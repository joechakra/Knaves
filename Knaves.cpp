// Knaves.cpp : Defines the entry point for the console application.
//
// This file can be built using MinGW  (gcc 4.6.2) and VS2010 console
// For MinGW the console commands to build are:
//    gcc -c -std=c++0x knaves.cpp
//    g++ -o knaves.exe knaves.o
//
//  For VS2010 the console commands to build are;
//  CL /EHsc knaves.cpp
// 
// Usage:
//   Knaves d4 B5
//
//
//
//The Compute function is responsible for the algorithm
//


#include <tchar.h>
#include <vector>
#include <deque>
#include <stack>
#include <algorithm>
#include <iostream>
#include <exception>
class myexception: public std::exception
{
public:
	myexception(std::string const& str):str_(str){}
	virtual const char* what() const throw()
	{
		return str_.c_str();
	}
	~myexception() throw(){}
private:
	std::string str_;
};
//Position is the chess board
struct KPos
{
	int x;
	int y;
	int Parent; //an index into an array that contains the position the knave came from
	KPos& operator=(KPos const& inp) 
	{
		//just an optimization. The default will work too.
		if (this != &inp)
		{
			x = inp.x;
			y = inp.y;
			Parent = inp.Parent;
		}
		return *this;
	}
};

const int MAX_POSITIONS = 8; //There are at most 8 positions that knave can move to in one move
struct KDist
{
	int cx;
	int cy;
};

KPos  operator+(KPos const& inp, KDist const& d)
{
	KPos res = {inp.x + d.cx, inp.y + d.cy};
	return res;
}
bool operator==(KPos const& f, KPos const& s)
{
	return f.x == s.x && f.y == s.y;
}
bool IsValidPos(KPos const& p)
{
	return p.x >= 0 && p.x <8 && p.y>=0 && p.y <8;
}
std::vector<KPos> ValidMoves(KPos const& inp)
{
	KDist const moves[MAX_POSITIONS] = {{-2,-1},{-2,1},{2,-1},{2,1},{-1,-2},{-1,2},{1,-2},{1,2}};
	std::vector<KPos> outp;
	for (int i=0; i<MAX_POSITIONS; ++i)
	{
		KPos newPos= inp + moves[i];
		if (IsValidPos(newPos))
		{
			outp.push_back(newPos);
		}
	}
	return outp;
}
template<class Iter1, class Iter2, class OutIter>
OutIter unordered_set_difference(Iter1 start1, Iter1 finish1,  Iter2 start, Iter2 finish, OutIter ostart)
{
	Iter1 curBegin=start1;
	while(curBegin!=finish1)
	{
		Iter1 it = std::find_first_of( curBegin,finish1,start, finish);
		while(curBegin != it) 
			*ostart++ = *curBegin++;
		curBegin = it==finish1 ? it : it+1;
	}
	return ostart;

}

std::ostream& operator<<(std::ostream& o, KPos const& pos)
{
	char c= 'A' + pos.x;
	return o << c << pos.y+1;
}
void PrintOut(KPos const& endPos, KPos const* seen, int curMax)
{
	std::stack<int> successMoves;
	int k=curMax;
	while (k!=0)
	{
		successMoves.push(k);
		k=seen[k].Parent;
	}

	while(!successMoves.empty())
	{
		int k = successMoves.top();
		successMoves.pop();
		std::cout << seen[k] << " ";
	}
	std::cout << endPos << std::endl;

}
////////////////////////////////////////////////////////////////
//Design:
//This implementation is based on Breadth First search
//There is a 'tobeseen' (T) queue containing the list of positions that 
//the program has reached from the given start position. 
//The seen list (S) contains the list of all positions such that:
//  x belongs to S =>  all y that are one hop away from x belong to (S U T)
// 
//The algorithm terminates when the end position is one of the valid 
//destinations from a position in the 'tobeseen' queue
// The  following notation is used below:
// Let T = Set-of-ToBeSeen
//     V = Set-of-ValidMoves
//     S = Set-Of-Seen
//     U is the notation for union
//
//The proof of correctness is given below. Proving optimality is more involved
//////////////////////////////////////////////////////////////////////////
int Compute(KPos const& startPos, KPos const& endPos, KPos* seen)
//Pre-Condition: startPos and endPos are 'valid' positions 
//seen is an array that has sufficient space to accommodate
//all the positions that Compute may traverse
{
	int curMax=0;
	std::deque<KPos> tobeseen;
	int totalseen=0;
	bool done = false;
	tobeseen.push_back(startPos);
	//Proof of Termination:
	// We assume that there is at least one path from any position to any other position.
	// Breadth-first search searches all possible positions that can be reached from startPos
	// Based on our assumption one of those positions reached will be endPos
	while(1)
	{
		KPos pos=tobeseen.front();
		tobeseen.pop_front();
		seen[curMax]= pos;
		std::vector<KPos> nextpositions=ValidMoves(pos);
		done=nextpositions.end() != std::find(nextpositions.begin(),nextpositions.end(),endPos);
		if (done) 
		{
			break;
		}
		// T <- T U (V - S)
		// which is implemented as
		// T.append(V-S-T)

		std::vector<KPos>::iterator finish = unordered_set_difference(  // V <- V-S
					nextpositions.begin(), 
					nextpositions.end(), 
					seen, 
					seen+curMax,
					nextpositions.begin() ); 

		finish  = unordered_set_difference(  // V <- V - T
			nextpositions.begin(),
			finish,
			tobeseen.begin(),
			tobeseen.end(), 
			nextpositions.begin());

		std::for_each(nextpositions.begin(),finish, //T.Append(V)
			[&] (KPos& pos) {
			pos.Parent = curMax; 
			tobeseen.push_back(pos); 
		} );


		++curMax;
	}
	return curMax;
}
KPos ConvertFromStr(_TCHAR* arg)
{
	std::basic_string<TCHAR> sarg(arg);
	_TCHAR const* err= _T("Invalid Argument ");
	std::basic_string<_TCHAR> msg(err);
	msg += sarg;
	myexception ex(msg);
	if (sarg.length() !=2)
	{
		throw ex;
	}
	KPos pos;
	pos.x = toupper(*arg) - 'A';
	pos.y = *++arg - '1';
	if (*++arg != '\0')
		throw ex;
	if (!IsValidPos(pos))
	{
		throw ex;
	}
	pos.Parent=0;
	return pos;
}

int _tmain(int argc, _TCHAR* argv[])
{
	if (argc!=3)
	{
		std::cout << "Usage example:" << argv[0] << " D3 D4" << std::endl;
		return 0;
	}
	try 
	{
		const int MAX_BOARD_POSITIONS=64; 
		KPos seen[MAX_BOARD_POSITIONS]; 
		//even if the breadth-first search covers ALL the positions on 
		//the board there are at most MAX_BOARD_POSITIONS;
		//hence 'seen' is of sufficient length
		KPos startPos=ConvertFromStr(argv[1]);
		KPos endPos=ConvertFromStr(argv[2]);
		int curMax = 0;
		if (! (startPos == endPos))
		{
			curMax = Compute(startPos,endPos,seen);
		}
		PrintOut(endPos, seen, curMax);
	}
	catch(std::exception& ex)
	{
		std::cout << ex.what() << std::endl;
	}
	return 0;
}

