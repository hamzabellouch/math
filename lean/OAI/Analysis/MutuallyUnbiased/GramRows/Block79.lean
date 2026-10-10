import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block6
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block16
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block17
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow7040 : Integer.Sparse Key := [(key2291, -1), (key2288, -1), (key2348, 2), (key2191, -1), (key2188, -1), (key2296, 2), (key2288, 2), (key2350, -1), (key2348, -1), (key2191, 2), (key2296, -1), (key2291, -1), (key2283, 1), (key2280, 1), (key2344, -2), (key2089, 1), (key2086, 1), (key2296, -2), (key2280, -2), (key2350, 1), (key2344, 1), (key2089, -2), (key2296, 1), (key2283, 1), (key2283, -1), (key2277, -1), (key2344, 1), (key2342, 1), (key2291, 1), (key2277, 1), (key2348, -1), (key2342, -1), (key2089, -1), (key2080, -1), (key2191, 1), (key2177, 1), (key2089, 1), (key2084, 1), (key2191, -1), (key2181, -1)]

theorem rawRowCheck7040 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form0 = rawRow7040 := by decide +kernel

def row7040 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

theorem rowCheck7040 : row7040 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7040 := by decide +kernel

theorem rowEval7040 (x : Key → ℝ) : Integer.Sparse.eval row7040 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck7040, Integer.Sparse.eval_collectBalanced, rawRowCheck7040]

def rawRow7041 : Integer.Sparse Key := [(key2288, -1), (key2348, -1), (key2291, 2), (key2288, -1), (key2348, -1), (key2188, 2), (key2350, 2), (key2191, -1), (key2296, -1), (key2291, 2), (key2191, -1), (key2296, -1), (key2280, 1), (key2344, 1), (key2283, -2), (key2280, 1), (key2344, 1), (key2086, -2), (key2350, -2), (key2089, 1), (key2296, 1), (key2283, -2), (key2089, 1), (key2296, 1), (key2177, -1), (key2344, -1), (key2181, 1), (key2283, 1), (key2080, 1), (key2348, 1), (key2084, -1), (key2291, -1), (key2177, -1), (key2344, -1), (key2080, 1), (key2348, 1), (key2181, 1), (key2283, 1), (key2084, -1), (key2291, -1)]

theorem rawRowCheck7041 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form0 = rawRow7041 := by decide +kernel

def row7041 : Integer.Sparse Key := [(key2080, 2), (key2084, -2), (key2086, -2), (key2089, 2), (key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2280, 2), (key2283, -2), (key2288, -2), (key2291, 2)]

theorem rowCheck7041 : row7041 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7041 := by decide +kernel

theorem rowEval7041 (x : Key → ℝ) : Integer.Sparse.eval row7041 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck7041, Integer.Sparse.eval_collectBalanced, rawRowCheck7041]

def rawRow7042 : Integer.Sparse Key := [(key2348, -1), (key2288, -1), (key2291, 2), (key2348, -1), (key2288, -1), (key2350, 2), (key2188, 2), (key2296, -1), (key2191, -1), (key2291, 2), (key2296, -1), (key2191, -1), (key2344, 1), (key2280, 1), (key2283, -2), (key2344, 1), (key2280, 1), (key2350, -2), (key2086, -2), (key2296, 1), (key2089, 1), (key2283, -2), (key2296, 1), (key2089, 1), (key2344, -1), (key2177, -1), (key2283, 1), (key2181, 1), (key2348, 1), (key2080, 1), (key2291, -1), (key2084, -1), (key2344, -1), (key2177, -1), (key2348, 1), (key2080, 1), (key2283, 1), (key2181, 1), (key2291, -1), (key2084, -1)]

theorem rawRowCheck7042 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form0 = rawRow7042 := by decide +kernel

def row7042 : Integer.Sparse Key := [(key2080, 2), (key2084, -2), (key2086, -2), (key2089, 2), (key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2280, 2), (key2283, -2), (key2288, -2), (key2291, 2)]

theorem rowCheck7042 : row7042 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7042 := by decide +kernel

theorem rowEval7042 (x : Key → ℝ) : Integer.Sparse.eval row7042 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck7042, Integer.Sparse.eval_collectBalanced, rawRowCheck7042]

def rawRow7043 : Integer.Sparse Key := [(key2291, -1), (key2348, -1), (key2288, 2), (key2296, -1), (key2350, -1), (key2191, 2), (key2348, 2), (key2188, -1), (key2288, -1), (key2296, 2), (key2191, -1), (key2291, -1), (key2283, 1), (key2344, 1), (key2280, -2), (key2296, 1), (key2350, 1), (key2089, -2), (key2344, -2), (key2086, 1), (key2280, 1), (key2296, -2), (key2089, 1), (key2283, 1), (key2181, -1), (key2342, -1), (key2177, 1), (key2277, 1), (key2084, 1), (key2342, 1), (key2080, -1), (key2277, -1), (key2191, -1), (key2348, -1), (key2089, 1), (key2344, 1), (key2191, 1), (key2291, 1), (key2089, -1), (key2283, -1)]

theorem rawRowCheck7043 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form0 = rawRow7043 := by decide +kernel

def row7043 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

theorem rowCheck7043 : row7043 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7043 := by decide +kernel

theorem rowEval7043 (x : Key → ℝ) : Integer.Sparse.eval row7043 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck7043, Integer.Sparse.eval_collectBalanced, rawRowCheck7043]

def rawRow7044 : Integer.Sparse Key := [(key2348, -1), (key2291, -1), (key2288, 2), (key2350, -1), (key2296, -1), (key2348, 2), (key2191, 2), (key2288, -1), (key2188, -1), (key2296, 2), (key2291, -1), (key2191, -1), (key2344, 1), (key2283, 1), (key2280, -2), (key2350, 1), (key2296, 1), (key2344, -2), (key2089, -2), (key2280, 1), (key2086, 1), (key2296, -2), (key2283, 1), (key2089, 1), (key2342, -1), (key2181, -1), (key2277, 1), (key2177, 1), (key2342, 1), (key2084, 1), (key2277, -1), (key2080, -1), (key2348, -1), (key2191, -1), (key2344, 1), (key2089, 1), (key2291, 1), (key2191, 1), (key2283, -1), (key2089, -1)]

theorem rawRowCheck7044 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form0 = rawRow7044 := by decide +kernel

def row7044 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

theorem rowCheck7044 : row7044 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7044 := by decide +kernel

theorem rowEval7044 (x : Key → ℝ) : Integer.Sparse.eval row7044 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck7044, Integer.Sparse.eval_collectBalanced, rawRowCheck7044]

def rawRow7045 : Integer.Sparse Key := [(key2296, -1), (key2296, -1), (key2350, 2), (key2191, -1), (key2191, -1), (key2291, 2), (key2291, 2), (key2348, -1), (key2348, -1), (key2188, 2), (key2288, -1), (key2288, -1), (key2296, 1), (key2296, 1), (key2350, -2), (key2089, 1), (key2089, 1), (key2283, -2), (key2283, -2), (key2344, 1), (key2344, 1), (key2086, -2), (key2280, 1), (key2280, 1), (key2291, -1), (key2291, -1), (key2348, 1), (key2348, 1), (key2283, 1), (key2283, 1), (key2344, -1), (key2344, -1), (key2084, -1), (key2084, -1), (key2181, 1), (key2181, 1), (key2080, 1), (key2080, 1), (key2177, -1), (key2177, -1)]

theorem rawRowCheck7045 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form0 = rawRow7045 := by decide +kernel

def row7045 : Integer.Sparse Key := [(key2080, 2), (key2084, -2), (key2086, -2), (key2089, 2), (key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2280, 2), (key2283, -2), (key2288, -2), (key2291, 2)]

theorem rowCheck7045 : row7045 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7045 := by decide +kernel

theorem rowEval7045 (x : Key → ℝ) : Integer.Sparse.eval row7045 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck7045, Integer.Sparse.eval_collectBalanced, rawRowCheck7045]

def rawRow7046 : Integer.Sparse Key := [(key2296, -1), (key2350, -1), (key2296, 2), (key2291, -1), (key2348, -1), (key2191, 2), (key2348, 2), (key2191, -1), (key2291, -1), (key2288, 2), (key2188, -1), (key2288, -1), (key2296, 1), (key2350, 1), (key2296, -2), (key2283, 1), (key2344, 1), (key2089, -2), (key2344, -2), (key2089, 1), (key2283, 1), (key2280, -2), (key2086, 1), (key2280, 1), (key2191, -1), (key2348, -1), (key2191, 1), (key2291, 1), (key2089, 1), (key2344, 1), (key2089, -1), (key2283, -1), (key2181, -1), (key2342, -1), (key2084, 1), (key2342, 1), (key2177, 1), (key2277, 1), (key2080, -1), (key2277, -1)]

theorem rawRowCheck7046 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form0 = rawRow7046 := by decide +kernel

def row7046 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

theorem rowCheck7046 : row7046 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7046 := by decide +kernel

theorem rowEval7046 (x : Key → ℝ) : Integer.Sparse.eval row7046 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck7046, Integer.Sparse.eval_collectBalanced, rawRowCheck7046]

def rawRow7047 : Integer.Sparse Key := [(key2350, -1), (key2296, -1), (key2296, 2), (key2348, -1), (key2291, -1), (key2348, 2), (key2191, 2), (key2291, -1), (key2191, -1), (key2288, 2), (key2288, -1), (key2188, -1), (key2350, 1), (key2296, 1), (key2296, -2), (key2344, 1), (key2283, 1), (key2344, -2), (key2089, -2), (key2283, 1), (key2089, 1), (key2280, -2), (key2280, 1), (key2086, 1), (key2348, -1), (key2191, -1), (key2291, 1), (key2191, 1), (key2344, 1), (key2089, 1), (key2283, -1), (key2089, -1), (key2342, -1), (key2181, -1), (key2342, 1), (key2084, 1), (key2277, 1), (key2177, 1), (key2277, -1), (key2080, -1)]

theorem rawRowCheck7047 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form0 = rawRow7047 := by decide +kernel

def row7047 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

theorem rowCheck7047 : row7047 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7047 := by decide +kernel

theorem rowEval7047 (x : Key → ℝ) : Integer.Sparse.eval row7047 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck7047, Integer.Sparse.eval_collectBalanced, rawRowCheck7047]

def rawRow7048 : Integer.Sparse Key := [(key739, -1), (key739, -1), (key740, 2), (key739, -1), (key739, -1), (key744, 2), (key744, 2), (key745, -1), (key745, -1), (key740, 2), (key745, -1), (key745, -1), (key819, 1), (key819, 1), (key820, -2), (key819, 1), (key819, 1), (key826, -2), (key826, -2), (key829, 1), (key829, 1), (key820, -2), (key829, 1), (key829, 1), (key903, -1), (key903, -1), (key904, 1), (key904, 1), (key909, 1), (key909, 1), (key912, -1), (key912, -1), (key903, -1), (key903, -1), (key909, 1), (key909, 1), (key904, 1), (key904, 1), (key912, -1), (key912, -1)]

theorem rawRowCheck7048 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form1 = rawRow7048 := by decide +kernel

def row7048 : Integer.Sparse Key := [(key739, -4), (key740, 4), (key744, 4), (key745, -4), (key819, 4), (key820, -4), (key826, -4), (key829, 4), (key903, -4), (key904, 4), (key909, 4), (key912, -4)]

theorem rowCheck7048 : row7048 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7048 := by decide +kernel

theorem rowEval7048 (x : Key → ℝ) : Integer.Sparse.eval row7048 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7048, Integer.Sparse.eval_collectBalanced, rawRowCheck7048]

def rawRow7049 : Integer.Sparse Key := [(key739, -1), (key740, -1), (key739, 2), (key744, -1), (key745, -1), (key739, 2), (key745, 2), (key739, -1), (key744, -1), (key745, 2), (key740, -1), (key745, -1), (key819, 1), (key820, 1), (key819, -2), (key826, 1), (key829, 1), (key819, -2), (key829, -2), (key819, 1), (key826, 1), (key829, -2), (key820, 1), (key829, 1), (key899, -1), (key904, -1), (key899, 1), (key903, 1), (key899, 1), (key912, 1), (key899, -1), (key909, -1), (key909, -1), (key919, -1), (key903, 1), (key919, 1), (key912, 1), (key919, 1), (key904, -1), (key919, -1)]

theorem rawRowCheck7049 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form1 = rawRow7049 := by decide +kernel

def row7049 : Integer.Sparse Key := [(key739, 2), (key740, -2), (key744, -2), (key745, 2), (key819, -2), (key820, 2), (key826, 2), (key829, -2), (key903, 2), (key904, -2), (key909, -2), (key912, 2)]

theorem rowCheck7049 : row7049 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7049 := by decide +kernel

theorem rowEval7049 (x : Key → ℝ) : Integer.Sparse.eval row7049 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7049, Integer.Sparse.eval_collectBalanced, rawRowCheck7049]

def rawRow7050 : Integer.Sparse Key := [(key740, -1), (key739, -1), (key739, 2), (key745, -1), (key744, -1), (key745, 2), (key739, 2), (key744, -1), (key739, -1), (key745, 2), (key745, -1), (key740, -1), (key820, 1), (key819, 1), (key819, -2), (key829, 1), (key826, 1), (key829, -2), (key819, -2), (key826, 1), (key819, 1), (key829, -2), (key829, 1), (key820, 1), (key904, -1), (key899, -1), (key903, 1), (key899, 1), (key912, 1), (key899, 1), (key909, -1), (key899, -1), (key919, -1), (key909, -1), (key919, 1), (key903, 1), (key919, 1), (key912, 1), (key919, -1), (key904, -1)]

theorem rawRowCheck7050 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form1 = rawRow7050 := by decide +kernel

def row7050 : Integer.Sparse Key := [(key739, 2), (key740, -2), (key744, -2), (key745, 2), (key819, -2), (key820, 2), (key826, 2), (key829, -2), (key903, 2), (key904, -2), (key909, -2), (key912, 2)]

theorem rowCheck7050 : row7050 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7050 := by decide +kernel

theorem rowEval7050 (x : Key → ℝ) : Integer.Sparse.eval row7050 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck7050, Integer.Sparse.eval_collectBalanced, rawRowCheck7050]

def rawRow7051 : Integer.Sparse Key := [(key744, -1), (key745, -1), (key745, 2), (key739, -1), (key740, -1), (key739, 2), (key745, 2), (key740, -1), (key745, -1), (key739, 2), (key739, -1), (key744, -1), (key826, 1), (key829, 1), (key829, -2), (key819, 1), (key820, 1), (key819, -2), (key829, -2), (key820, 1), (key829, 1), (key819, -2), (key819, 1), (key826, 1), (key909, -1), (key919, -1), (key912, 1), (key919, 1), (key903, 1), (key919, 1), (key904, -1), (key919, -1), (key899, -1), (key904, -1), (key899, 1), (key912, 1), (key899, 1), (key903, 1), (key899, -1), (key909, -1)]

theorem rawRowCheck7051 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form1 = rawRow7051 := by decide +kernel

def row7051 : Integer.Sparse Key := [(key739, 2), (key740, -2), (key744, -2), (key745, 2), (key819, -2), (key820, 2), (key826, 2), (key829, -2), (key903, 2), (key904, -2), (key909, -2), (key912, 2)]

theorem rowCheck7051 : row7051 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7051 := by decide +kernel

theorem rowEval7051 (x : Key → ℝ) : Integer.Sparse.eval row7051 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7051, Integer.Sparse.eval_collectBalanced, rawRowCheck7051]

def rawRow7052 : Integer.Sparse Key := [(key745, -1), (key744, -1), (key745, 2), (key740, -1), (key739, -1), (key745, 2), (key739, 2), (key745, -1), (key740, -1), (key739, 2), (key744, -1), (key739, -1), (key829, 1), (key826, 1), (key829, -2), (key820, 1), (key819, 1), (key829, -2), (key819, -2), (key829, 1), (key820, 1), (key819, -2), (key826, 1), (key819, 1), (key919, -1), (key909, -1), (key919, 1), (key912, 1), (key919, 1), (key903, 1), (key919, -1), (key904, -1), (key904, -1), (key899, -1), (key912, 1), (key899, 1), (key903, 1), (key899, 1), (key909, -1), (key899, -1)]

theorem rawRowCheck7052 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form1 = rawRow7052 := by decide +kernel

def row7052 : Integer.Sparse Key := [(key739, 2), (key740, -2), (key744, -2), (key745, 2), (key819, -2), (key820, 2), (key826, 2), (key829, -2), (key903, 2), (key904, -2), (key909, -2), (key912, 2)]

theorem rowCheck7052 : row7052 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7052 := by decide +kernel

theorem rowEval7052 (x : Key → ℝ) : Integer.Sparse.eval row7052 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck7052, Integer.Sparse.eval_collectBalanced, rawRowCheck7052]

def rawRow7053 : Integer.Sparse Key := [(key745, -1), (key745, -1), (key744, 2), (key745, -1), (key745, -1), (key740, 2), (key740, 2), (key739, -1), (key739, -1), (key744, 2), (key739, -1), (key739, -1), (key829, 1), (key829, 1), (key826, -2), (key829, 1), (key829, 1), (key820, -2), (key820, -2), (key819, 1), (key819, 1), (key826, -2), (key819, 1), (key819, 1), (key912, -1), (key912, -1), (key909, 1), (key909, 1), (key904, 1), (key904, 1), (key903, -1), (key903, -1), (key912, -1), (key912, -1), (key904, 1), (key904, 1), (key909, 1), (key909, 1), (key903, -1), (key903, -1)]

theorem rawRowCheck7053 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form1 = rawRow7053 := by decide +kernel

def row7053 : Integer.Sparse Key := [(key739, -4), (key740, 4), (key744, 4), (key745, -4), (key819, 4), (key820, -4), (key826, -4), (key829, 4), (key903, -4), (key904, 4), (key909, 4), (key912, -4)]

theorem rowCheck7053 : row7053 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7053 := by decide +kernel

theorem rowEval7053 (x : Key → ℝ) : Integer.Sparse.eval row7053 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck7053, Integer.Sparse.eval_collectBalanced, rawRowCheck7053]

def rawRow7054 : Integer.Sparse Key := [(key819, -1), (key819, -1), (key820, 2), (key899, -1), (key899, -1), (key903, 2), (key903, 2), (key904, -1), (key904, -1), (key961, 2), (key963, -1), (key963, -1), (key739, 1), (key739, 1), (key740, -2), (key899, 1), (key899, 1), (key909, -2), (key909, -2), (key912, 1), (key912, 1), (key961, -2), (key965, 1), (key965, 1), (key744, -1), (key744, -1), (key745, 1), (key745, 1), (key826, 1), (key826, 1), (key829, -1), (key829, -1), (key903, -1), (key903, -1), (key909, 1), (key909, 1), (key963, 1), (key963, 1), (key965, -1), (key965, -1)]

theorem rawRowCheck7054 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form1 = rawRow7054 := by decide +kernel

def row7054 : Integer.Sparse Key := [(key739, 2), (key740, -2), (key744, -2), (key745, 2), (key819, -2), (key820, 2), (key826, 2), (key829, -2), (key903, 2), (key904, -2), (key909, -2), (key912, 2)]

theorem rowCheck7054 : row7054 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7054 := by decide +kernel

theorem rowEval7054 (x : Key → ℝ) : Integer.Sparse.eval row7054 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7054, Integer.Sparse.eval_collectBalanced, rawRowCheck7054]

def rawRow7055 : Integer.Sparse Key := [(key819, -1), (key820, -1), (key819, 2), (key903, -1), (key904, -1), (key899, 2), (key904, 2), (key899, -1), (key903, -1), (key963, 2), (key961, -1), (key963, -1), (key739, 1), (key740, 1), (key739, -2), (key909, 1), (key912, 1), (key899, -2), (key912, -2), (key899, 1), (key909, 1), (key965, -2), (key961, 1), (key965, 1), (key739, -1), (key745, -1), (key739, 1), (key744, 1), (key819, 1), (key829, 1), (key819, -1), (key826, -1), (key909, -1), (key919, -1), (key903, 1), (key919, 1), (key965, 1), (key967, 1), (key963, -1), (key967, -1)]

theorem rawRowCheck7055 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form1 = rawRow7055 := by decide +kernel

def row7055 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

theorem rowCheck7055 : row7055 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7055 := by decide +kernel

theorem rowEval7055 (x : Key → ℝ) : Integer.Sparse.eval row7055 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7055, Integer.Sparse.eval_collectBalanced, rawRowCheck7055]

def rawRow7056 : Integer.Sparse Key := [(key820, -1), (key819, -1), (key819, 2), (key904, -1), (key903, -1), (key904, 2), (key899, 2), (key903, -1), (key899, -1), (key963, 2), (key963, -1), (key961, -1), (key740, 1), (key739, 1), (key739, -2), (key912, 1), (key909, 1), (key912, -2), (key899, -2), (key909, 1), (key899, 1), (key965, -2), (key965, 1), (key961, 1), (key745, -1), (key739, -1), (key744, 1), (key739, 1), (key829, 1), (key819, 1), (key826, -1), (key819, -1), (key919, -1), (key909, -1), (key919, 1), (key903, 1), (key967, 1), (key965, 1), (key967, -1), (key963, -1)]

theorem rawRowCheck7056 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form1 = rawRow7056 := by decide +kernel

def row7056 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

theorem rowCheck7056 : row7056 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7056 := by decide +kernel

theorem rowEval7056 (x : Key → ℝ) : Integer.Sparse.eval row7056 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck7056, Integer.Sparse.eval_collectBalanced, rawRowCheck7056]

def rawRow7057 : Integer.Sparse Key := [(key899, -1), (key899, -1), (key961, 2), (key819, -1), (key819, -1), (key903, 2), (key903, 2), (key963, -1), (key963, -1), (key820, 2), (key904, -1), (key904, -1), (key899, 1), (key899, 1), (key961, -2), (key739, 1), (key739, 1), (key909, -2), (key909, -2), (key965, 1), (key965, 1), (key740, -2), (key912, 1), (key912, 1), (key903, -1), (key903, -1), (key963, 1), (key963, 1), (key909, 1), (key909, 1), (key965, -1), (key965, -1), (key744, -1), (key744, -1), (key826, 1), (key826, 1), (key745, 1), (key745, 1), (key829, -1), (key829, -1)]

theorem rawRowCheck7057 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form1 = rawRow7057 := by decide +kernel

def row7057 : Integer.Sparse Key := [(key739, 2), (key740, -2), (key744, -2), (key745, 2), (key819, -2), (key820, 2), (key826, 2), (key829, -2), (key903, 2), (key904, -2), (key909, -2), (key912, 2)]

theorem rowCheck7057 : row7057 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7057 := by decide +kernel

theorem rowEval7057 (x : Key → ℝ) : Integer.Sparse.eval row7057 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7057, Integer.Sparse.eval_collectBalanced, rawRowCheck7057]

def rawRow7058 : Integer.Sparse Key := [(key899, -1), (key961, -1), (key899, 2), (key903, -1), (key963, -1), (key819, 2), (key963, 2), (key819, -1), (key903, -1), (key904, 2), (key820, -1), (key904, -1), (key899, 1), (key961, 1), (key899, -2), (key909, 1), (key965, 1), (key739, -2), (key965, -2), (key739, 1), (key909, 1), (key912, -2), (key740, 1), (key912, 1), (key819, -1), (key963, -1), (key819, 1), (key903, 1), (key739, 1), (key965, 1), (key739, -1), (key909, -1), (key826, -1), (key967, -1), (key744, 1), (key967, 1), (key829, 1), (key919, 1), (key745, -1), (key919, -1)]

theorem rawRowCheck7058 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form1 = rawRow7058 := by decide +kernel

def row7058 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

theorem rowCheck7058 : row7058 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7058 := by decide +kernel

theorem rowEval7058 (x : Key → ℝ) : Integer.Sparse.eval row7058 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7058, Integer.Sparse.eval_collectBalanced, rawRowCheck7058]

def rawRow7059 : Integer.Sparse Key := [(key961, -1), (key899, -1), (key899, 2), (key963, -1), (key903, -1), (key963, 2), (key819, 2), (key903, -1), (key819, -1), (key904, 2), (key904, -1), (key820, -1), (key961, 1), (key899, 1), (key899, -2), (key965, 1), (key909, 1), (key965, -2), (key739, -2), (key909, 1), (key739, 1), (key912, -2), (key912, 1), (key740, 1), (key963, -1), (key819, -1), (key903, 1), (key819, 1), (key965, 1), (key739, 1), (key909, -1), (key739, -1), (key967, -1), (key826, -1), (key967, 1), (key744, 1), (key919, 1), (key829, 1), (key919, -1), (key745, -1)]

theorem rawRowCheck7059 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form1 = rawRow7059 := by decide +kernel

def row7059 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

theorem rowCheck7059 : row7059 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7059 := by decide +kernel

theorem rowEval7059 (x : Key → ℝ) : Integer.Sparse.eval row7059 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7059, Integer.Sparse.eval_collectBalanced, rawRowCheck7059]

def rawRow7060 : Integer.Sparse Key := [(key903, -1), (key904, -1), (key963, 2), (key819, -1), (key820, -1), (key899, 2), (key904, 2), (key961, -1), (key963, -1), (key819, 2), (key899, -1), (key903, -1), (key909, 1), (key912, 1), (key965, -2), (key739, 1), (key740, 1), (key899, -2), (key912, -2), (key961, 1), (key965, 1), (key739, -2), (key899, 1), (key909, 1), (key909, -1), (key919, -1), (key965, 1), (key967, 1), (key903, 1), (key919, 1), (key963, -1), (key967, -1), (key739, -1), (key745, -1), (key819, 1), (key829, 1), (key739, 1), (key744, 1), (key819, -1), (key826, -1)]

theorem rawRowCheck7060 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form1 = rawRow7060 := by decide +kernel

def row7060 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

theorem rowCheck7060 : row7060 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7060 := by decide +kernel

theorem rowEval7060 (x : Key → ℝ) : Integer.Sparse.eval row7060 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7060, Integer.Sparse.eval_collectBalanced, rawRowCheck7060]

def rawRow7061 : Integer.Sparse Key := [(key904, -1), (key903, -1), (key963, 2), (key820, -1), (key819, -1), (key904, 2), (key899, 2), (key963, -1), (key961, -1), (key819, 2), (key903, -1), (key899, -1), (key912, 1), (key909, 1), (key965, -2), (key740, 1), (key739, 1), (key912, -2), (key899, -2), (key965, 1), (key961, 1), (key739, -2), (key909, 1), (key899, 1), (key919, -1), (key909, -1), (key967, 1), (key965, 1), (key919, 1), (key903, 1), (key967, -1), (key963, -1), (key745, -1), (key739, -1), (key829, 1), (key819, 1), (key744, 1), (key739, 1), (key826, -1), (key819, -1)]

theorem rawRowCheck7061 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form1 = rawRow7061 := by decide +kernel

def row7061 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

theorem rowCheck7061 : row7061 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7061 := by decide +kernel

theorem rowEval7061 (x : Key → ℝ) : Integer.Sparse.eval row7061 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck7061, Integer.Sparse.eval_collectBalanced, rawRowCheck7061]

def rawRow7062 : Integer.Sparse Key := [(key903, -1), (key963, -1), (key904, 2), (key899, -1), (key961, -1), (key819, 2), (key963, 2), (key820, -1), (key904, -1), (key899, 2), (key819, -1), (key903, -1), (key909, 1), (key965, 1), (key912, -2), (key899, 1), (key961, 1), (key739, -2), (key965, -2), (key740, 1), (key912, 1), (key899, -2), (key739, 1), (key909, 1), (key826, -1), (key967, -1), (key829, 1), (key919, 1), (key744, 1), (key967, 1), (key745, -1), (key919, -1), (key819, -1), (key963, -1), (key739, 1), (key965, 1), (key819, 1), (key903, 1), (key739, -1), (key909, -1)]

theorem rawRowCheck7062 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form1 = rawRow7062 := by decide +kernel

def row7062 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

theorem rowCheck7062 : row7062 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7062 := by decide +kernel

theorem rowEval7062 (x : Key → ℝ) : Integer.Sparse.eval row7062 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7062, Integer.Sparse.eval_collectBalanced, rawRowCheck7062]

def rawRow7063 : Integer.Sparse Key := [(key963, -1), (key903, -1), (key904, 2), (key961, -1), (key899, -1), (key963, 2), (key819, 2), (key904, -1), (key820, -1), (key899, 2), (key903, -1), (key819, -1), (key965, 1), (key909, 1), (key912, -2), (key961, 1), (key899, 1), (key965, -2), (key739, -2), (key912, 1), (key740, 1), (key899, -2), (key909, 1), (key739, 1), (key967, -1), (key826, -1), (key919, 1), (key829, 1), (key967, 1), (key744, 1), (key919, -1), (key745, -1), (key963, -1), (key819, -1), (key965, 1), (key739, 1), (key903, 1), (key819, 1), (key909, -1), (key739, -1)]

theorem rawRowCheck7063 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form1 = rawRow7063 := by decide +kernel

def row7063 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

theorem rowCheck7063 : row7063 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7063 := by decide +kernel

theorem rowEval7063 (x : Key → ℝ) : Integer.Sparse.eval row7063 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7063, Integer.Sparse.eval_collectBalanced, rawRowCheck7063]

def rawRow7064 : Integer.Sparse Key := [(key904, -1), (key963, -1), (key903, 2), (key904, -1), (key963, -1), (key820, 2), (key961, 2), (key819, -1), (key899, -1), (key903, 2), (key819, -1), (key899, -1), (key912, 1), (key965, 1), (key909, -2), (key912, 1), (key965, 1), (key740, -2), (key961, -2), (key739, 1), (key899, 1), (key909, -2), (key739, 1), (key899, 1), (key829, -1), (key965, -1), (key826, 1), (key909, 1), (key745, 1), (key963, 1), (key744, -1), (key903, -1), (key829, -1), (key965, -1), (key745, 1), (key963, 1), (key826, 1), (key909, 1), (key744, -1), (key903, -1)]

theorem rawRowCheck7064 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form1 = rawRow7064 := by decide +kernel

def row7064 : Integer.Sparse Key := [(key739, 2), (key740, -2), (key744, -2), (key745, 2), (key819, -2), (key820, 2), (key826, 2), (key829, -2), (key903, 2), (key904, -2), (key909, -2), (key912, 2)]

theorem rowCheck7064 : row7064 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7064 := by decide +kernel

theorem rowEval7064 (x : Key → ℝ) : Integer.Sparse.eval row7064 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck7064, Integer.Sparse.eval_collectBalanced, rawRowCheck7064]

def rawRow7065 : Integer.Sparse Key := [(key963, -1), (key904, -1), (key903, 2), (key963, -1), (key904, -1), (key961, 2), (key820, 2), (key899, -1), (key819, -1), (key903, 2), (key899, -1), (key819, -1), (key965, 1), (key912, 1), (key909, -2), (key965, 1), (key912, 1), (key961, -2), (key740, -2), (key899, 1), (key739, 1), (key909, -2), (key899, 1), (key739, 1), (key965, -1), (key829, -1), (key909, 1), (key826, 1), (key963, 1), (key745, 1), (key903, -1), (key744, -1), (key965, -1), (key829, -1), (key963, 1), (key745, 1), (key909, 1), (key826, 1), (key903, -1), (key744, -1)]

theorem rawRowCheck7065 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form1 = rawRow7065 := by decide +kernel

def row7065 : Integer.Sparse Key := [(key739, 2), (key740, -2), (key744, -2), (key745, 2), (key819, -2), (key820, 2), (key826, 2), (key829, -2), (key903, 2), (key904, -2), (key909, -2), (key912, 2)]

theorem rowCheck7065 : row7065 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7065 := by decide +kernel

theorem rowEval7065 (x : Key → ℝ) : Integer.Sparse.eval row7065 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7065, Integer.Sparse.eval_collectBalanced, rawRowCheck7065]

def rawRow7066 : Integer.Sparse Key := [(key826, -1), (key829, -1), (key829, 2), (key909, -1), (key912, -1), (key909, 2), (key919, 2), (key912, -1), (key919, -1), (key965, 2), (key965, -1), (key967, -1), (key744, 1), (key745, 1), (key745, -2), (key903, 1), (key904, 1), (key903, -2), (key919, -2), (key904, 1), (key919, 1), (key963, -2), (key963, 1), (key967, 1), (key739, -1), (key745, -1), (key740, 1), (key745, 1), (key819, 1), (key829, 1), (key820, -1), (key829, -1), (key899, -1), (key904, -1), (key899, 1), (key912, 1), (key961, 1), (key963, 1), (key961, -1), (key965, -1)]

theorem rawRowCheck7066 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form1 = rawRow7066 := by decide +kernel

def row7066 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

theorem rowCheck7066 : row7066 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7066 := by decide +kernel

theorem rowEval7066 (x : Key → ℝ) : Integer.Sparse.eval row7066 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7066, Integer.Sparse.eval_collectBalanced, rawRowCheck7066]

def rawRow7067 : Integer.Sparse Key := [(key829, -1), (key826, -1), (key829, 2), (key912, -1), (key909, -1), (key919, 2), (key909, 2), (key919, -1), (key912, -1), (key965, 2), (key967, -1), (key965, -1), (key745, 1), (key744, 1), (key745, -2), (key904, 1), (key903, 1), (key919, -2), (key903, -2), (key919, 1), (key904, 1), (key963, -2), (key967, 1), (key963, 1), (key745, -1), (key739, -1), (key745, 1), (key740, 1), (key829, 1), (key819, 1), (key829, -1), (key820, -1), (key904, -1), (key899, -1), (key912, 1), (key899, 1), (key963, 1), (key961, 1), (key965, -1), (key961, -1)]

theorem rawRowCheck7067 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form1 = rawRow7067 := by decide +kernel

def row7067 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

theorem rowCheck7067 : row7067 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7067 := by decide +kernel

theorem rowEval7067 (x : Key → ℝ) : Integer.Sparse.eval row7067 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck7067, Integer.Sparse.eval_collectBalanced, rawRowCheck7067]

def rawRow7068 : Integer.Sparse Key := [(key829, -1), (key829, -1), (key826, 2), (key919, -1), (key919, -1), (key912, 2), (key912, 2), (key909, -1), (key909, -1), (key967, 2), (key965, -1), (key965, -1), (key745, 1), (key745, 1), (key744, -2), (key919, 1), (key919, 1), (key904, -2), (key904, -2), (key903, 1), (key903, 1), (key967, -2), (key963, 1), (key963, 1), (key740, -1), (key740, -1), (key739, 1), (key739, 1), (key820, 1), (key820, 1), (key819, -1), (key819, -1), (key912, -1), (key912, -1), (key904, 1), (key904, 1), (key965, 1), (key965, 1), (key963, -1), (key963, -1)]

theorem rawRowCheck7068 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form1 = rawRow7068 := by decide +kernel

def row7068 : Integer.Sparse Key := [(key739, 2), (key740, -2), (key744, -2), (key745, 2), (key819, -2), (key820, 2), (key826, 2), (key829, -2), (key903, 2), (key904, -2), (key909, -2), (key912, 2)]

theorem rowCheck7068 : row7068 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7068 := by decide +kernel

theorem rowEval7068 (x : Key → ℝ) : Integer.Sparse.eval row7068 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck7068, Integer.Sparse.eval_collectBalanced, rawRowCheck7068]

def rawRow7069 : Integer.Sparse Key := [(key909, -1), (key912, -1), (key965, 2), (key826, -1), (key829, -1), (key909, 2), (key919, 2), (key965, -1), (key967, -1), (key829, 2), (key912, -1), (key919, -1), (key903, 1), (key904, 1), (key963, -2), (key744, 1), (key745, 1), (key903, -2), (key919, -2), (key963, 1), (key967, 1), (key745, -2), (key904, 1), (key919, 1), (key899, -1), (key904, -1), (key961, 1), (key963, 1), (key899, 1), (key912, 1), (key961, -1), (key965, -1), (key739, -1), (key745, -1), (key819, 1), (key829, 1), (key740, 1), (key745, 1), (key820, -1), (key829, -1)]

theorem rawRowCheck7069 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form1 = rawRow7069 := by decide +kernel

def row7069 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

theorem rowCheck7069 : row7069 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7069 := by decide +kernel

theorem rowEval7069 (x : Key → ℝ) : Integer.Sparse.eval row7069 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7069, Integer.Sparse.eval_collectBalanced, rawRowCheck7069]

def rawRow7070 : Integer.Sparse Key := [(key912, -1), (key909, -1), (key965, 2), (key829, -1), (key826, -1), (key919, 2), (key909, 2), (key967, -1), (key965, -1), (key829, 2), (key919, -1), (key912, -1), (key904, 1), (key903, 1), (key963, -2), (key745, 1), (key744, 1), (key919, -2), (key903, -2), (key967, 1), (key963, 1), (key745, -2), (key919, 1), (key904, 1), (key904, -1), (key899, -1), (key963, 1), (key961, 1), (key912, 1), (key899, 1), (key965, -1), (key961, -1), (key745, -1), (key739, -1), (key829, 1), (key819, 1), (key745, 1), (key740, 1), (key829, -1), (key820, -1)]

theorem rawRowCheck7070 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form1 = rawRow7070 := by decide +kernel

def row7070 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

theorem rowCheck7070 : row7070 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7070 := by decide +kernel

theorem rowEval7070 (x : Key → ℝ) : Integer.Sparse.eval row7070 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck7070, Integer.Sparse.eval_collectBalanced, rawRowCheck7070]

def rawRow7071 : Integer.Sparse Key := [(key909, -1), (key965, -1), (key912, 2), (key909, -1), (key965, -1), (key826, 2), (key967, 2), (key829, -1), (key919, -1), (key912, 2), (key829, -1), (key919, -1), (key903, 1), (key963, 1), (key904, -2), (key903, 1), (key963, 1), (key744, -2), (key967, -2), (key745, 1), (key919, 1), (key904, -2), (key745, 1), (key919, 1), (key819, -1), (key963, -1), (key820, 1), (key904, 1), (key739, 1), (key965, 1), (key740, -1), (key912, -1), (key819, -1), (key963, -1), (key739, 1), (key965, 1), (key820, 1), (key904, 1), (key740, -1), (key912, -1)]

theorem rawRowCheck7071 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form1 = rawRow7071 := by decide +kernel

def row7071 : Integer.Sparse Key := [(key739, 2), (key740, -2), (key744, -2), (key745, 2), (key819, -2), (key820, 2), (key826, 2), (key829, -2), (key903, 2), (key904, -2), (key909, -2), (key912, 2)]

theorem rowCheck7071 : row7071 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7071 := by decide +kernel

theorem rowEval7071 (x : Key → ℝ) : Integer.Sparse.eval row7071 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7071, Integer.Sparse.eval_collectBalanced, rawRowCheck7071]

def rawRow7072 : Integer.Sparse Key := [(key965, -1), (key909, -1), (key912, 2), (key965, -1), (key909, -1), (key967, 2), (key826, 2), (key919, -1), (key829, -1), (key912, 2), (key919, -1), (key829, -1), (key963, 1), (key903, 1), (key904, -2), (key963, 1), (key903, 1), (key967, -2), (key744, -2), (key919, 1), (key745, 1), (key904, -2), (key919, 1), (key745, 1), (key963, -1), (key819, -1), (key904, 1), (key820, 1), (key965, 1), (key739, 1), (key912, -1), (key740, -1), (key963, -1), (key819, -1), (key965, 1), (key739, 1), (key904, 1), (key820, 1), (key912, -1), (key740, -1)]

theorem rawRowCheck7072 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form1 = rawRow7072 := by decide +kernel

def row7072 : Integer.Sparse Key := [(key739, 2), (key740, -2), (key744, -2), (key745, 2), (key819, -2), (key820, 2), (key826, 2), (key829, -2), (key903, 2), (key904, -2), (key909, -2), (key912, 2)]

theorem rowCheck7072 : row7072 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7072 := by decide +kernel

theorem rowEval7072 (x : Key → ℝ) : Integer.Sparse.eval row7072 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7072, Integer.Sparse.eval_collectBalanced, rawRowCheck7072]

def rawRow7073 : Integer.Sparse Key := [(key912, -1), (key965, -1), (key909, 2), (key919, -1), (key967, -1), (key829, 2), (key965, 2), (key826, -1), (key909, -1), (key919, 2), (key829, -1), (key912, -1), (key904, 1), (key963, 1), (key903, -2), (key919, 1), (key967, 1), (key745, -2), (key963, -2), (key744, 1), (key903, 1), (key919, -2), (key745, 1), (key904, 1), (key820, -1), (key961, -1), (key819, 1), (key899, 1), (key740, 1), (key961, 1), (key739, -1), (key899, -1), (key829, -1), (key965, -1), (key745, 1), (key963, 1), (key829, 1), (key912, 1), (key745, -1), (key904, -1)]

theorem rawRowCheck7073 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form1 = rawRow7073 := by decide +kernel

def row7073 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

theorem rowCheck7073 : row7073 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7073 := by decide +kernel

theorem rowEval7073 (x : Key → ℝ) : Integer.Sparse.eval row7073 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck7073, Integer.Sparse.eval_collectBalanced, rawRowCheck7073]

def rawRow7074 : Integer.Sparse Key := [(key965, -1), (key912, -1), (key909, 2), (key967, -1), (key919, -1), (key965, 2), (key829, 2), (key909, -1), (key826, -1), (key919, 2), (key912, -1), (key829, -1), (key963, 1), (key904, 1), (key903, -2), (key967, 1), (key919, 1), (key963, -2), (key745, -2), (key903, 1), (key744, 1), (key919, -2), (key904, 1), (key745, 1), (key961, -1), (key820, -1), (key899, 1), (key819, 1), (key961, 1), (key740, 1), (key899, -1), (key739, -1), (key965, -1), (key829, -1), (key963, 1), (key745, 1), (key912, 1), (key829, 1), (key904, -1), (key745, -1)]

theorem rawRowCheck7074 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form1 = rawRow7074 := by decide +kernel

def row7074 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

theorem rowCheck7074 : row7074 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7074 := by decide +kernel

theorem rowEval7074 (x : Key → ℝ) : Integer.Sparse.eval row7074 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7074, Integer.Sparse.eval_collectBalanced, rawRowCheck7074]

def rawRow7075 : Integer.Sparse Key := [(key919, -1), (key919, -1), (key967, 2), (key829, -1), (key829, -1), (key912, 2), (key912, 2), (key965, -1), (key965, -1), (key826, 2), (key909, -1), (key909, -1), (key919, 1), (key919, 1), (key967, -2), (key745, 1), (key745, 1), (key904, -2), (key904, -2), (key963, 1), (key963, 1), (key744, -2), (key903, 1), (key903, 1), (key912, -1), (key912, -1), (key965, 1), (key965, 1), (key904, 1), (key904, 1), (key963, -1), (key963, -1), (key740, -1), (key740, -1), (key820, 1), (key820, 1), (key739, 1), (key739, 1), (key819, -1), (key819, -1)]

theorem rawRowCheck7075 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form1 = rawRow7075 := by decide +kernel

def row7075 : Integer.Sparse Key := [(key739, 2), (key740, -2), (key744, -2), (key745, 2), (key819, -2), (key820, 2), (key826, 2), (key829, -2), (key903, 2), (key904, -2), (key909, -2), (key912, 2)]

theorem rowCheck7075 : row7075 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7075 := by decide +kernel

theorem rowEval7075 (x : Key → ℝ) : Integer.Sparse.eval row7075 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck7075, Integer.Sparse.eval_collectBalanced, rawRowCheck7075]

def rawRow7076 : Integer.Sparse Key := [(key919, -1), (key967, -1), (key919, 2), (key912, -1), (key965, -1), (key829, 2), (key965, 2), (key829, -1), (key912, -1), (key909, 2), (key826, -1), (key909, -1), (key919, 1), (key967, 1), (key919, -2), (key904, 1), (key963, 1), (key745, -2), (key963, -2), (key745, 1), (key904, 1), (key903, -2), (key744, 1), (key903, 1), (key829, -1), (key965, -1), (key829, 1), (key912, 1), (key745, 1), (key963, 1), (key745, -1), (key904, -1), (key820, -1), (key961, -1), (key740, 1), (key961, 1), (key819, 1), (key899, 1), (key739, -1), (key899, -1)]

theorem rawRowCheck7076 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form1 = rawRow7076 := by decide +kernel

def row7076 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

theorem rowCheck7076 : row7076 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7076 := by decide +kernel

theorem rowEval7076 (x : Key → ℝ) : Integer.Sparse.eval row7076 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck7076, Integer.Sparse.eval_collectBalanced, rawRowCheck7076]

def rawRow7077 : Integer.Sparse Key := [(key967, -1), (key919, -1), (key919, 2), (key965, -1), (key912, -1), (key965, 2), (key829, 2), (key912, -1), (key829, -1), (key909, 2), (key909, -1), (key826, -1), (key967, 1), (key919, 1), (key919, -2), (key963, 1), (key904, 1), (key963, -2), (key745, -2), (key904, 1), (key745, 1), (key903, -2), (key903, 1), (key744, 1), (key965, -1), (key829, -1), (key912, 1), (key829, 1), (key963, 1), (key745, 1), (key904, -1), (key745, -1), (key961, -1), (key820, -1), (key961, 1), (key740, 1), (key899, 1), (key819, 1), (key899, -1), (key739, -1)]

theorem rawRowCheck7077 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form1 = rawRow7077 := by decide +kernel

def row7077 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

theorem rowCheck7077 : row7077 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7077 := by decide +kernel

theorem rowEval7077 (x : Key → ℝ) : Integer.Sparse.eval row7077 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7077, Integer.Sparse.eval_collectBalanced, rawRowCheck7077]

def rawRow7078 : Integer.Sparse Key := [(key2093, -1), (key2093, -1), (key2094, 2), (key2093, -1), (key2093, -1), (key2096, 2), (key2096, 2), (key2097, -1), (key2097, -1), (key2094, 2), (key2097, -1), (key2097, -1), (key2195, 1), (key2195, 1), (key2196, -2), (key2195, 1), (key2195, 1), (key2201, -2), (key2201, -2), (key2202, 1), (key2202, 1), (key2196, -2), (key2202, 1), (key2202, 1), (key2306, -1), (key2306, -1), (key2307, 1), (key2307, 1), (key2311, 1), (key2311, 1), (key2312, -1), (key2312, -1), (key2306, -1), (key2306, -1), (key2311, 1), (key2311, 1), (key2307, 1), (key2307, 1), (key2312, -1), (key2312, -1)]

theorem rawRowCheck7078 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form2 = rawRow7078 := by decide +kernel

def row7078 : Integer.Sparse Key := [(key2093, -4), (key2094, 4), (key2096, 4), (key2097, -4), (key2195, 4), (key2196, -4), (key2201, -4), (key2202, 4), (key2306, -4), (key2307, 4), (key2311, 4), (key2312, -4)]

theorem rowCheck7078 : row7078 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7078 := by decide +kernel

theorem rowEval7078 (x : Key → ℝ) : Integer.Sparse.eval row7078 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck7078, Integer.Sparse.eval_collectBalanced, rawRowCheck7078]

def rawRow7079 : Integer.Sparse Key := [(key2093, -1), (key2094, -1), (key2093, 2), (key2096, -1), (key2097, -1), (key2093, 2), (key2097, 2), (key2093, -1), (key2096, -1), (key2097, 2), (key2094, -1), (key2097, -1), (key2195, 1), (key2196, 1), (key2195, -2), (key2201, 1), (key2202, 1), (key2195, -2), (key2202, -2), (key2195, 1), (key2201, 1), (key2202, -2), (key2196, 1), (key2202, 1), (key2304, -1), (key2307, -1), (key2304, 1), (key2306, 1), (key2304, 1), (key2312, 1), (key2304, -1), (key2311, -1), (key2311, -1), (key2315, -1), (key2306, 1), (key2315, 1), (key2312, 1), (key2315, 1), (key2307, -1), (key2315, -1)]

theorem rawRowCheck7079 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form2 = rawRow7079 := by decide +kernel

def row7079 : Integer.Sparse Key := [(key2093, 2), (key2094, -2), (key2096, -2), (key2097, 2), (key2195, -2), (key2196, 2), (key2201, 2), (key2202, -2), (key2306, 2), (key2307, -2), (key2311, -2), (key2312, 2)]

theorem rowCheck7079 : row7079 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7079 := by decide +kernel

theorem rowEval7079 (x : Key → ℝ) : Integer.Sparse.eval row7079 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck7079, Integer.Sparse.eval_collectBalanced, rawRowCheck7079]

def rawRow7080 : Integer.Sparse Key := [(key2094, -1), (key2093, -1), (key2093, 2), (key2097, -1), (key2096, -1), (key2097, 2), (key2093, 2), (key2096, -1), (key2093, -1), (key2097, 2), (key2097, -1), (key2094, -1), (key2196, 1), (key2195, 1), (key2195, -2), (key2202, 1), (key2201, 1), (key2202, -2), (key2195, -2), (key2201, 1), (key2195, 1), (key2202, -2), (key2202, 1), (key2196, 1), (key2307, -1), (key2304, -1), (key2306, 1), (key2304, 1), (key2312, 1), (key2304, 1), (key2311, -1), (key2304, -1), (key2315, -1), (key2311, -1), (key2315, 1), (key2306, 1), (key2315, 1), (key2312, 1), (key2315, -1), (key2307, -1)]

theorem rawRowCheck7080 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form2 = rawRow7080 := by decide +kernel

def row7080 : Integer.Sparse Key := [(key2093, 2), (key2094, -2), (key2096, -2), (key2097, 2), (key2195, -2), (key2196, 2), (key2201, 2), (key2202, -2), (key2306, 2), (key2307, -2), (key2311, -2), (key2312, 2)]

theorem rowCheck7080 : row7080 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7080 := by decide +kernel

theorem rowEval7080 (x : Key → ℝ) : Integer.Sparse.eval row7080 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck7080, Integer.Sparse.eval_collectBalanced, rawRowCheck7080]

def rawRow7081 : Integer.Sparse Key := [(key2096, -1), (key2097, -1), (key2097, 2), (key2093, -1), (key2094, -1), (key2093, 2), (key2097, 2), (key2094, -1), (key2097, -1), (key2093, 2), (key2093, -1), (key2096, -1), (key2201, 1), (key2202, 1), (key2202, -2), (key2195, 1), (key2196, 1), (key2195, -2), (key2202, -2), (key2196, 1), (key2202, 1), (key2195, -2), (key2195, 1), (key2201, 1), (key2311, -1), (key2315, -1), (key2312, 1), (key2315, 1), (key2306, 1), (key2315, 1), (key2307, -1), (key2315, -1), (key2304, -1), (key2307, -1), (key2304, 1), (key2312, 1), (key2304, 1), (key2306, 1), (key2304, -1), (key2311, -1)]

theorem rawRowCheck7081 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form2 = rawRow7081 := by decide +kernel

def row7081 : Integer.Sparse Key := [(key2093, 2), (key2094, -2), (key2096, -2), (key2097, 2), (key2195, -2), (key2196, 2), (key2201, 2), (key2202, -2), (key2306, 2), (key2307, -2), (key2311, -2), (key2312, 2)]

theorem rowCheck7081 : row7081 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7081 := by decide +kernel

theorem rowEval7081 (x : Key → ℝ) : Integer.Sparse.eval row7081 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck7081, Integer.Sparse.eval_collectBalanced, rawRowCheck7081]

def rawRow7082 : Integer.Sparse Key := [(key2097, -1), (key2096, -1), (key2097, 2), (key2094, -1), (key2093, -1), (key2097, 2), (key2093, 2), (key2097, -1), (key2094, -1), (key2093, 2), (key2096, -1), (key2093, -1), (key2202, 1), (key2201, 1), (key2202, -2), (key2196, 1), (key2195, 1), (key2202, -2), (key2195, -2), (key2202, 1), (key2196, 1), (key2195, -2), (key2201, 1), (key2195, 1), (key2315, -1), (key2311, -1), (key2315, 1), (key2312, 1), (key2315, 1), (key2306, 1), (key2315, -1), (key2307, -1), (key2307, -1), (key2304, -1), (key2312, 1), (key2304, 1), (key2306, 1), (key2304, 1), (key2311, -1), (key2304, -1)]

theorem rawRowCheck7082 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form2 = rawRow7082 := by decide +kernel

def row7082 : Integer.Sparse Key := [(key2093, 2), (key2094, -2), (key2096, -2), (key2097, 2), (key2195, -2), (key2196, 2), (key2201, 2), (key2202, -2), (key2306, 2), (key2307, -2), (key2311, -2), (key2312, 2)]

theorem rowCheck7082 : row7082 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7082 := by decide +kernel

theorem rowEval7082 (x : Key → ℝ) : Integer.Sparse.eval row7082 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck7082, Integer.Sparse.eval_collectBalanced, rawRowCheck7082]

def rawRow7083 : Integer.Sparse Key := [(key2097, -1), (key2097, -1), (key2096, 2), (key2097, -1), (key2097, -1), (key2094, 2), (key2094, 2), (key2093, -1), (key2093, -1), (key2096, 2), (key2093, -1), (key2093, -1), (key2202, 1), (key2202, 1), (key2201, -2), (key2202, 1), (key2202, 1), (key2196, -2), (key2196, -2), (key2195, 1), (key2195, 1), (key2201, -2), (key2195, 1), (key2195, 1), (key2312, -1), (key2312, -1), (key2311, 1), (key2311, 1), (key2307, 1), (key2307, 1), (key2306, -1), (key2306, -1), (key2312, -1), (key2312, -1), (key2307, 1), (key2307, 1), (key2311, 1), (key2311, 1), (key2306, -1), (key2306, -1)]

theorem rawRowCheck7083 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form2 = rawRow7083 := by decide +kernel

def row7083 : Integer.Sparse Key := [(key2093, -4), (key2094, 4), (key2096, 4), (key2097, -4), (key2195, 4), (key2196, -4), (key2201, -4), (key2202, 4), (key2306, -4), (key2307, 4), (key2311, 4), (key2312, -4)]

theorem rowCheck7083 : row7083 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7083 := by decide +kernel

theorem rowEval7083 (x : Key → ℝ) : Integer.Sparse.eval row7083 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck7083, Integer.Sparse.eval_collectBalanced, rawRowCheck7083]

def rawRow7084 : Integer.Sparse Key := [(key2195, -1), (key2195, -1), (key2196, 2), (key2304, -1), (key2304, -1), (key2306, 2), (key2306, 2), (key2307, -1), (key2307, -1), (key2342, 2), (key2344, -1), (key2344, -1), (key2093, 1), (key2093, 1), (key2094, -2), (key2304, 1), (key2304, 1), (key2311, -2), (key2311, -2), (key2312, 1), (key2312, 1), (key2342, -2), (key2348, 1), (key2348, 1), (key2096, -1), (key2096, -1), (key2097, 1), (key2097, 1), (key2201, 1), (key2201, 1), (key2202, -1), (key2202, -1), (key2306, -1), (key2306, -1), (key2311, 1), (key2311, 1), (key2344, 1), (key2344, 1), (key2348, -1), (key2348, -1)]

theorem rawRowCheck7084 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form2 = rawRow7084 := by decide +kernel

def row7084 : Integer.Sparse Key := [(key2093, 2), (key2094, -2), (key2096, -2), (key2097, 2), (key2195, -2), (key2196, 2), (key2201, 2), (key2202, -2), (key2306, 2), (key2307, -2), (key2311, -2), (key2312, 2)]

theorem rowCheck7084 : row7084 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7084 := by decide +kernel

theorem rowEval7084 (x : Key → ℝ) : Integer.Sparse.eval row7084 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck7084, Integer.Sparse.eval_collectBalanced, rawRowCheck7084]

def rawRow7085 : Integer.Sparse Key := [(key2195, -1), (key2196, -1), (key2195, 2), (key2306, -1), (key2307, -1), (key2304, 2), (key2307, 2), (key2304, -1), (key2306, -1), (key2344, 2), (key2342, -1), (key2344, -1), (key2093, 1), (key2094, 1), (key2093, -2), (key2311, 1), (key2312, 1), (key2304, -2), (key2312, -2), (key2304, 1), (key2311, 1), (key2348, -2), (key2342, 1), (key2348, 1), (key2093, -1), (key2097, -1), (key2093, 1), (key2096, 1), (key2195, 1), (key2202, 1), (key2195, -1), (key2201, -1), (key2311, -1), (key2315, -1), (key2306, 1), (key2315, 1), (key2348, 1), (key2350, 1), (key2344, -1), (key2350, -1)]

theorem rawRowCheck7085 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form2 = rawRow7085 := by decide +kernel

def row7085 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

theorem rowCheck7085 : row7085 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7085 := by decide +kernel

theorem rowEval7085 (x : Key → ℝ) : Integer.Sparse.eval row7085 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck7085, Integer.Sparse.eval_collectBalanced, rawRowCheck7085]

def rawRow7086 : Integer.Sparse Key := [(key2196, -1), (key2195, -1), (key2195, 2), (key2307, -1), (key2306, -1), (key2307, 2), (key2304, 2), (key2306, -1), (key2304, -1), (key2344, 2), (key2344, -1), (key2342, -1), (key2094, 1), (key2093, 1), (key2093, -2), (key2312, 1), (key2311, 1), (key2312, -2), (key2304, -2), (key2311, 1), (key2304, 1), (key2348, -2), (key2348, 1), (key2342, 1), (key2097, -1), (key2093, -1), (key2096, 1), (key2093, 1), (key2202, 1), (key2195, 1), (key2201, -1), (key2195, -1), (key2315, -1), (key2311, -1), (key2315, 1), (key2306, 1), (key2350, 1), (key2348, 1), (key2350, -1), (key2344, -1)]

theorem rawRowCheck7086 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form2 = rawRow7086 := by decide +kernel

def row7086 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

theorem rowCheck7086 : row7086 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7086 := by decide +kernel

theorem rowEval7086 (x : Key → ℝ) : Integer.Sparse.eval row7086 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck7086, Integer.Sparse.eval_collectBalanced, rawRowCheck7086]

def rawRow7087 : Integer.Sparse Key := [(key2304, -1), (key2304, -1), (key2342, 2), (key2195, -1), (key2195, -1), (key2306, 2), (key2306, 2), (key2344, -1), (key2344, -1), (key2196, 2), (key2307, -1), (key2307, -1), (key2304, 1), (key2304, 1), (key2342, -2), (key2093, 1), (key2093, 1), (key2311, -2), (key2311, -2), (key2348, 1), (key2348, 1), (key2094, -2), (key2312, 1), (key2312, 1), (key2306, -1), (key2306, -1), (key2344, 1), (key2344, 1), (key2311, 1), (key2311, 1), (key2348, -1), (key2348, -1), (key2096, -1), (key2096, -1), (key2201, 1), (key2201, 1), (key2097, 1), (key2097, 1), (key2202, -1), (key2202, -1)]

theorem rawRowCheck7087 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form2 = rawRow7087 := by decide +kernel

def row7087 : Integer.Sparse Key := [(key2093, 2), (key2094, -2), (key2096, -2), (key2097, 2), (key2195, -2), (key2196, 2), (key2201, 2), (key2202, -2), (key2306, 2), (key2307, -2), (key2311, -2), (key2312, 2)]

theorem rowCheck7087 : row7087 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7087 := by decide +kernel

theorem rowEval7087 (x : Key → ℝ) : Integer.Sparse.eval row7087 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck7087, Integer.Sparse.eval_collectBalanced, rawRowCheck7087]

def rawRow7088 : Integer.Sparse Key := [(key2304, -1), (key2342, -1), (key2304, 2), (key2306, -1), (key2344, -1), (key2195, 2), (key2344, 2), (key2195, -1), (key2306, -1), (key2307, 2), (key2196, -1), (key2307, -1), (key2304, 1), (key2342, 1), (key2304, -2), (key2311, 1), (key2348, 1), (key2093, -2), (key2348, -2), (key2093, 1), (key2311, 1), (key2312, -2), (key2094, 1), (key2312, 1), (key2195, -1), (key2344, -1), (key2195, 1), (key2306, 1), (key2093, 1), (key2348, 1), (key2093, -1), (key2311, -1), (key2201, -1), (key2350, -1), (key2096, 1), (key2350, 1), (key2202, 1), (key2315, 1), (key2097, -1), (key2315, -1)]

theorem rawRowCheck7088 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form2 = rawRow7088 := by decide +kernel

def row7088 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

theorem rowCheck7088 : row7088 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7088 := by decide +kernel

theorem rowEval7088 (x : Key → ℝ) : Integer.Sparse.eval row7088 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck7088, Integer.Sparse.eval_collectBalanced, rawRowCheck7088]

def rawRow7089 : Integer.Sparse Key := [(key2342, -1), (key2304, -1), (key2304, 2), (key2344, -1), (key2306, -1), (key2344, 2), (key2195, 2), (key2306, -1), (key2195, -1), (key2307, 2), (key2307, -1), (key2196, -1), (key2342, 1), (key2304, 1), (key2304, -2), (key2348, 1), (key2311, 1), (key2348, -2), (key2093, -2), (key2311, 1), (key2093, 1), (key2312, -2), (key2312, 1), (key2094, 1), (key2344, -1), (key2195, -1), (key2306, 1), (key2195, 1), (key2348, 1), (key2093, 1), (key2311, -1), (key2093, -1), (key2350, -1), (key2201, -1), (key2350, 1), (key2096, 1), (key2315, 1), (key2202, 1), (key2315, -1), (key2097, -1)]

theorem rawRowCheck7089 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form2 = rawRow7089 := by decide +kernel

def row7089 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

theorem rowCheck7089 : row7089 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7089 := by decide +kernel

theorem rowEval7089 (x : Key → ℝ) : Integer.Sparse.eval row7089 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck7089, Integer.Sparse.eval_collectBalanced, rawRowCheck7089]

def rawRow7090 : Integer.Sparse Key := [(key2306, -1), (key2307, -1), (key2344, 2), (key2195, -1), (key2196, -1), (key2304, 2), (key2307, 2), (key2342, -1), (key2344, -1), (key2195, 2), (key2304, -1), (key2306, -1), (key2311, 1), (key2312, 1), (key2348, -2), (key2093, 1), (key2094, 1), (key2304, -2), (key2312, -2), (key2342, 1), (key2348, 1), (key2093, -2), (key2304, 1), (key2311, 1), (key2311, -1), (key2315, -1), (key2348, 1), (key2350, 1), (key2306, 1), (key2315, 1), (key2344, -1), (key2350, -1), (key2093, -1), (key2097, -1), (key2195, 1), (key2202, 1), (key2093, 1), (key2096, 1), (key2195, -1), (key2201, -1)]

theorem rawRowCheck7090 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form2 = rawRow7090 := by decide +kernel

def row7090 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

theorem rowCheck7090 : row7090 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7090 := by decide +kernel

theorem rowEval7090 (x : Key → ℝ) : Integer.Sparse.eval row7090 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck7090, Integer.Sparse.eval_collectBalanced, rawRowCheck7090]

def rawRow7091 : Integer.Sparse Key := [(key2307, -1), (key2306, -1), (key2344, 2), (key2196, -1), (key2195, -1), (key2307, 2), (key2304, 2), (key2344, -1), (key2342, -1), (key2195, 2), (key2306, -1), (key2304, -1), (key2312, 1), (key2311, 1), (key2348, -2), (key2094, 1), (key2093, 1), (key2312, -2), (key2304, -2), (key2348, 1), (key2342, 1), (key2093, -2), (key2311, 1), (key2304, 1), (key2315, -1), (key2311, -1), (key2350, 1), (key2348, 1), (key2315, 1), (key2306, 1), (key2350, -1), (key2344, -1), (key2097, -1), (key2093, -1), (key2202, 1), (key2195, 1), (key2096, 1), (key2093, 1), (key2201, -1), (key2195, -1)]

theorem rawRowCheck7091 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form2 = rawRow7091 := by decide +kernel

def row7091 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

theorem rowCheck7091 : row7091 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7091 := by decide +kernel

theorem rowEval7091 (x : Key → ℝ) : Integer.Sparse.eval row7091 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck7091, Integer.Sparse.eval_collectBalanced, rawRowCheck7091]

def rawRow7092 : Integer.Sparse Key := [(key2306, -1), (key2344, -1), (key2307, 2), (key2304, -1), (key2342, -1), (key2195, 2), (key2344, 2), (key2196, -1), (key2307, -1), (key2304, 2), (key2195, -1), (key2306, -1), (key2311, 1), (key2348, 1), (key2312, -2), (key2304, 1), (key2342, 1), (key2093, -2), (key2348, -2), (key2094, 1), (key2312, 1), (key2304, -2), (key2093, 1), (key2311, 1), (key2201, -1), (key2350, -1), (key2202, 1), (key2315, 1), (key2096, 1), (key2350, 1), (key2097, -1), (key2315, -1), (key2195, -1), (key2344, -1), (key2093, 1), (key2348, 1), (key2195, 1), (key2306, 1), (key2093, -1), (key2311, -1)]

theorem rawRowCheck7092 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form2 = rawRow7092 := by decide +kernel

def row7092 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

theorem rowCheck7092 : row7092 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7092 := by decide +kernel

theorem rowEval7092 (x : Key → ℝ) : Integer.Sparse.eval row7092 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck7092, Integer.Sparse.eval_collectBalanced, rawRowCheck7092]

def rawRow7093 : Integer.Sparse Key := [(key2344, -1), (key2306, -1), (key2307, 2), (key2342, -1), (key2304, -1), (key2344, 2), (key2195, 2), (key2307, -1), (key2196, -1), (key2304, 2), (key2306, -1), (key2195, -1), (key2348, 1), (key2311, 1), (key2312, -2), (key2342, 1), (key2304, 1), (key2348, -2), (key2093, -2), (key2312, 1), (key2094, 1), (key2304, -2), (key2311, 1), (key2093, 1), (key2350, -1), (key2201, -1), (key2315, 1), (key2202, 1), (key2350, 1), (key2096, 1), (key2315, -1), (key2097, -1), (key2344, -1), (key2195, -1), (key2348, 1), (key2093, 1), (key2306, 1), (key2195, 1), (key2311, -1), (key2093, -1)]

theorem rawRowCheck7093 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form2 = rawRow7093 := by decide +kernel

def row7093 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

theorem rowCheck7093 : row7093 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7093 := by decide +kernel

theorem rowEval7093 (x : Key → ℝ) : Integer.Sparse.eval row7093 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck7093, Integer.Sparse.eval_collectBalanced, rawRowCheck7093]

def rawRow7094 : Integer.Sparse Key := [(key2307, -1), (key2344, -1), (key2306, 2), (key2307, -1), (key2344, -1), (key2196, 2), (key2342, 2), (key2195, -1), (key2304, -1), (key2306, 2), (key2195, -1), (key2304, -1), (key2312, 1), (key2348, 1), (key2311, -2), (key2312, 1), (key2348, 1), (key2094, -2), (key2342, -2), (key2093, 1), (key2304, 1), (key2311, -2), (key2093, 1), (key2304, 1), (key2202, -1), (key2348, -1), (key2201, 1), (key2311, 1), (key2097, 1), (key2344, 1), (key2096, -1), (key2306, -1), (key2202, -1), (key2348, -1), (key2097, 1), (key2344, 1), (key2201, 1), (key2311, 1), (key2096, -1), (key2306, -1)]

theorem rawRowCheck7094 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form2 = rawRow7094 := by decide +kernel

def row7094 : Integer.Sparse Key := [(key2093, 2), (key2094, -2), (key2096, -2), (key2097, 2), (key2195, -2), (key2196, 2), (key2201, 2), (key2202, -2), (key2306, 2), (key2307, -2), (key2311, -2), (key2312, 2)]

theorem rowCheck7094 : row7094 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7094 := by decide +kernel

theorem rowEval7094 (x : Key → ℝ) : Integer.Sparse.eval row7094 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck7094, Integer.Sparse.eval_collectBalanced, rawRowCheck7094]

def rawRow7095 : Integer.Sparse Key := [(key2344, -1), (key2307, -1), (key2306, 2), (key2344, -1), (key2307, -1), (key2342, 2), (key2196, 2), (key2304, -1), (key2195, -1), (key2306, 2), (key2304, -1), (key2195, -1), (key2348, 1), (key2312, 1), (key2311, -2), (key2348, 1), (key2312, 1), (key2342, -2), (key2094, -2), (key2304, 1), (key2093, 1), (key2311, -2), (key2304, 1), (key2093, 1), (key2348, -1), (key2202, -1), (key2311, 1), (key2201, 1), (key2344, 1), (key2097, 1), (key2306, -1), (key2096, -1), (key2348, -1), (key2202, -1), (key2344, 1), (key2097, 1), (key2311, 1), (key2201, 1), (key2306, -1), (key2096, -1)]

theorem rawRowCheck7095 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form2 = rawRow7095 := by decide +kernel

def row7095 : Integer.Sparse Key := [(key2093, 2), (key2094, -2), (key2096, -2), (key2097, 2), (key2195, -2), (key2196, 2), (key2201, 2), (key2202, -2), (key2306, 2), (key2307, -2), (key2311, -2), (key2312, 2)]

theorem rowCheck7095 : row7095 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7095 := by decide +kernel

theorem rowEval7095 (x : Key → ℝ) : Integer.Sparse.eval row7095 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck7095, Integer.Sparse.eval_collectBalanced, rawRowCheck7095]

def rawRow7096 : Integer.Sparse Key := [(key2201, -1), (key2202, -1), (key2202, 2), (key2311, -1), (key2312, -1), (key2311, 2), (key2315, 2), (key2312, -1), (key2315, -1), (key2348, 2), (key2348, -1), (key2350, -1), (key2096, 1), (key2097, 1), (key2097, -2), (key2306, 1), (key2307, 1), (key2306, -2), (key2315, -2), (key2307, 1), (key2315, 1), (key2344, -2), (key2344, 1), (key2350, 1), (key2093, -1), (key2097, -1), (key2094, 1), (key2097, 1), (key2195, 1), (key2202, 1), (key2196, -1), (key2202, -1), (key2304, -1), (key2307, -1), (key2304, 1), (key2312, 1), (key2342, 1), (key2344, 1), (key2342, -1), (key2348, -1)]

theorem rawRowCheck7096 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form2 = rawRow7096 := by decide +kernel

def row7096 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

theorem rowCheck7096 : row7096 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7096 := by decide +kernel

theorem rowEval7096 (x : Key → ℝ) : Integer.Sparse.eval row7096 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck7096, Integer.Sparse.eval_collectBalanced, rawRowCheck7096]

def rawRow7097 : Integer.Sparse Key := [(key2202, -1), (key2201, -1), (key2202, 2), (key2312, -1), (key2311, -1), (key2315, 2), (key2311, 2), (key2315, -1), (key2312, -1), (key2348, 2), (key2350, -1), (key2348, -1), (key2097, 1), (key2096, 1), (key2097, -2), (key2307, 1), (key2306, 1), (key2315, -2), (key2306, -2), (key2315, 1), (key2307, 1), (key2344, -2), (key2350, 1), (key2344, 1), (key2097, -1), (key2093, -1), (key2097, 1), (key2094, 1), (key2202, 1), (key2195, 1), (key2202, -1), (key2196, -1), (key2307, -1), (key2304, -1), (key2312, 1), (key2304, 1), (key2344, 1), (key2342, 1), (key2348, -1), (key2342, -1)]

theorem rawRowCheck7097 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form2 = rawRow7097 := by decide +kernel

def row7097 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

theorem rowCheck7097 : row7097 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7097 := by decide +kernel

theorem rowEval7097 (x : Key → ℝ) : Integer.Sparse.eval row7097 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck7097, Integer.Sparse.eval_collectBalanced, rawRowCheck7097]

def rawRow7098 : Integer.Sparse Key := [(key2202, -1), (key2202, -1), (key2201, 2), (key2315, -1), (key2315, -1), (key2312, 2), (key2312, 2), (key2311, -1), (key2311, -1), (key2350, 2), (key2348, -1), (key2348, -1), (key2097, 1), (key2097, 1), (key2096, -2), (key2315, 1), (key2315, 1), (key2307, -2), (key2307, -2), (key2306, 1), (key2306, 1), (key2350, -2), (key2344, 1), (key2344, 1), (key2094, -1), (key2094, -1), (key2093, 1), (key2093, 1), (key2196, 1), (key2196, 1), (key2195, -1), (key2195, -1), (key2312, -1), (key2312, -1), (key2307, 1), (key2307, 1), (key2348, 1), (key2348, 1), (key2344, -1), (key2344, -1)]

theorem rawRowCheck7098 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form2 = rawRow7098 := by decide +kernel

def row7098 : Integer.Sparse Key := [(key2093, 2), (key2094, -2), (key2096, -2), (key2097, 2), (key2195, -2), (key2196, 2), (key2201, 2), (key2202, -2), (key2306, 2), (key2307, -2), (key2311, -2), (key2312, 2)]

theorem rowCheck7098 : row7098 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7098 := by decide +kernel

theorem rowEval7098 (x : Key → ℝ) : Integer.Sparse.eval row7098 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck7098, Integer.Sparse.eval_collectBalanced, rawRowCheck7098]

def rawRow7099 : Integer.Sparse Key := [(key2311, -1), (key2312, -1), (key2348, 2), (key2201, -1), (key2202, -1), (key2311, 2), (key2315, 2), (key2348, -1), (key2350, -1), (key2202, 2), (key2312, -1), (key2315, -1), (key2306, 1), (key2307, 1), (key2344, -2), (key2096, 1), (key2097, 1), (key2306, -2), (key2315, -2), (key2344, 1), (key2350, 1), (key2097, -2), (key2307, 1), (key2315, 1), (key2304, -1), (key2307, -1), (key2342, 1), (key2344, 1), (key2304, 1), (key2312, 1), (key2342, -1), (key2348, -1), (key2093, -1), (key2097, -1), (key2195, 1), (key2202, 1), (key2094, 1), (key2097, 1), (key2196, -1), (key2202, -1)]

theorem rawRowCheck7099 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form2 = rawRow7099 := by decide +kernel

def row7099 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

theorem rowCheck7099 : row7099 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7099 := by decide +kernel

theorem rowEval7099 (x : Key → ℝ) : Integer.Sparse.eval row7099 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck7099, Integer.Sparse.eval_collectBalanced, rawRowCheck7099]

def rawRow7100 : Integer.Sparse Key := [(key2312, -1), (key2311, -1), (key2348, 2), (key2202, -1), (key2201, -1), (key2315, 2), (key2311, 2), (key2350, -1), (key2348, -1), (key2202, 2), (key2315, -1), (key2312, -1), (key2307, 1), (key2306, 1), (key2344, -2), (key2097, 1), (key2096, 1), (key2315, -2), (key2306, -2), (key2350, 1), (key2344, 1), (key2097, -2), (key2315, 1), (key2307, 1), (key2307, -1), (key2304, -1), (key2344, 1), (key2342, 1), (key2312, 1), (key2304, 1), (key2348, -1), (key2342, -1), (key2097, -1), (key2093, -1), (key2202, 1), (key2195, 1), (key2097, 1), (key2094, 1), (key2202, -1), (key2196, -1)]

theorem rawRowCheck7100 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form2 = rawRow7100 := by decide +kernel

def row7100 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

theorem rowCheck7100 : row7100 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7100 := by decide +kernel

theorem rowEval7100 (x : Key → ℝ) : Integer.Sparse.eval row7100 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck7100, Integer.Sparse.eval_collectBalanced, rawRowCheck7100]

def rawRow7101 : Integer.Sparse Key := [(key2311, -1), (key2348, -1), (key2312, 2), (key2311, -1), (key2348, -1), (key2201, 2), (key2350, 2), (key2202, -1), (key2315, -1), (key2312, 2), (key2202, -1), (key2315, -1), (key2306, 1), (key2344, 1), (key2307, -2), (key2306, 1), (key2344, 1), (key2096, -2), (key2350, -2), (key2097, 1), (key2315, 1), (key2307, -2), (key2097, 1), (key2315, 1), (key2195, -1), (key2344, -1), (key2196, 1), (key2307, 1), (key2093, 1), (key2348, 1), (key2094, -1), (key2312, -1), (key2195, -1), (key2344, -1), (key2093, 1), (key2348, 1), (key2196, 1), (key2307, 1), (key2094, -1), (key2312, -1)]

theorem rawRowCheck7101 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form2 = rawRow7101 := by decide +kernel

def row7101 : Integer.Sparse Key := [(key2093, 2), (key2094, -2), (key2096, -2), (key2097, 2), (key2195, -2), (key2196, 2), (key2201, 2), (key2202, -2), (key2306, 2), (key2307, -2), (key2311, -2), (key2312, 2)]

theorem rowCheck7101 : row7101 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7101 := by decide +kernel

theorem rowEval7101 (x : Key → ℝ) : Integer.Sparse.eval row7101 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck7101, Integer.Sparse.eval_collectBalanced, rawRowCheck7101]

def rawRow7102 : Integer.Sparse Key := [(key2348, -1), (key2311, -1), (key2312, 2), (key2348, -1), (key2311, -1), (key2350, 2), (key2201, 2), (key2315, -1), (key2202, -1), (key2312, 2), (key2315, -1), (key2202, -1), (key2344, 1), (key2306, 1), (key2307, -2), (key2344, 1), (key2306, 1), (key2350, -2), (key2096, -2), (key2315, 1), (key2097, 1), (key2307, -2), (key2315, 1), (key2097, 1), (key2344, -1), (key2195, -1), (key2307, 1), (key2196, 1), (key2348, 1), (key2093, 1), (key2312, -1), (key2094, -1), (key2344, -1), (key2195, -1), (key2348, 1), (key2093, 1), (key2307, 1), (key2196, 1), (key2312, -1), (key2094, -1)]

theorem rawRowCheck7102 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form2 = rawRow7102 := by decide +kernel

def row7102 : Integer.Sparse Key := [(key2093, 2), (key2094, -2), (key2096, -2), (key2097, 2), (key2195, -2), (key2196, 2), (key2201, 2), (key2202, -2), (key2306, 2), (key2307, -2), (key2311, -2), (key2312, 2)]

theorem rowCheck7102 : row7102 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7102 := by decide +kernel

theorem rowEval7102 (x : Key → ℝ) : Integer.Sparse.eval row7102 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck7102, Integer.Sparse.eval_collectBalanced, rawRowCheck7102]

def rawRow7103 : Integer.Sparse Key := [(key2312, -1), (key2348, -1), (key2311, 2), (key2315, -1), (key2350, -1), (key2202, 2), (key2348, 2), (key2201, -1), (key2311, -1), (key2315, 2), (key2202, -1), (key2312, -1), (key2307, 1), (key2344, 1), (key2306, -2), (key2315, 1), (key2350, 1), (key2097, -2), (key2344, -2), (key2096, 1), (key2306, 1), (key2315, -2), (key2097, 1), (key2307, 1), (key2196, -1), (key2342, -1), (key2195, 1), (key2304, 1), (key2094, 1), (key2342, 1), (key2093, -1), (key2304, -1), (key2202, -1), (key2348, -1), (key2097, 1), (key2344, 1), (key2202, 1), (key2312, 1), (key2097, -1), (key2307, -1)]

theorem rawRowCheck7103 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form2 = rawRow7103 := by decide +kernel

def row7103 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

theorem rowCheck7103 : row7103 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7103 := by decide +kernel

theorem rowEval7103 (x : Key → ℝ) : Integer.Sparse.eval row7103 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck7103, Integer.Sparse.eval_collectBalanced, rawRowCheck7103]

def rawRow7104 : Integer.Sparse Key := [(key2348, -1), (key2312, -1), (key2311, 2), (key2350, -1), (key2315, -1), (key2348, 2), (key2202, 2), (key2311, -1), (key2201, -1), (key2315, 2), (key2312, -1), (key2202, -1), (key2344, 1), (key2307, 1), (key2306, -2), (key2350, 1), (key2315, 1), (key2344, -2), (key2097, -2), (key2306, 1), (key2096, 1), (key2315, -2), (key2307, 1), (key2097, 1), (key2342, -1), (key2196, -1), (key2304, 1), (key2195, 1), (key2342, 1), (key2094, 1), (key2304, -1), (key2093, -1), (key2348, -1), (key2202, -1), (key2344, 1), (key2097, 1), (key2312, 1), (key2202, 1), (key2307, -1), (key2097, -1)]

theorem rawRowCheck7104 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form2 = rawRow7104 := by decide +kernel

def row7104 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

theorem rowCheck7104 : row7104 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7104 := by decide +kernel

theorem rowEval7104 (x : Key → ℝ) : Integer.Sparse.eval row7104 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck7104, Integer.Sparse.eval_collectBalanced, rawRowCheck7104]

def rawRow7105 : Integer.Sparse Key := [(key2315, -1), (key2315, -1), (key2350, 2), (key2202, -1), (key2202, -1), (key2312, 2), (key2312, 2), (key2348, -1), (key2348, -1), (key2201, 2), (key2311, -1), (key2311, -1), (key2315, 1), (key2315, 1), (key2350, -2), (key2097, 1), (key2097, 1), (key2307, -2), (key2307, -2), (key2344, 1), (key2344, 1), (key2096, -2), (key2306, 1), (key2306, 1), (key2312, -1), (key2312, -1), (key2348, 1), (key2348, 1), (key2307, 1), (key2307, 1), (key2344, -1), (key2344, -1), (key2094, -1), (key2094, -1), (key2196, 1), (key2196, 1), (key2093, 1), (key2093, 1), (key2195, -1), (key2195, -1)]

theorem rawRowCheck7105 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form2 = rawRow7105 := by decide +kernel

def row7105 : Integer.Sparse Key := [(key2093, 2), (key2094, -2), (key2096, -2), (key2097, 2), (key2195, -2), (key2196, 2), (key2201, 2), (key2202, -2), (key2306, 2), (key2307, -2), (key2311, -2), (key2312, 2)]

theorem rowCheck7105 : row7105 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7105 := by decide +kernel

theorem rowEval7105 (x : Key → ℝ) : Integer.Sparse.eval row7105 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck7105, Integer.Sparse.eval_collectBalanced, rawRowCheck7105]

def rawRow7106 : Integer.Sparse Key := [(key2315, -1), (key2350, -1), (key2315, 2), (key2312, -1), (key2348, -1), (key2202, 2), (key2348, 2), (key2202, -1), (key2312, -1), (key2311, 2), (key2201, -1), (key2311, -1), (key2315, 1), (key2350, 1), (key2315, -2), (key2307, 1), (key2344, 1), (key2097, -2), (key2344, -2), (key2097, 1), (key2307, 1), (key2306, -2), (key2096, 1), (key2306, 1), (key2202, -1), (key2348, -1), (key2202, 1), (key2312, 1), (key2097, 1), (key2344, 1), (key2097, -1), (key2307, -1), (key2196, -1), (key2342, -1), (key2094, 1), (key2342, 1), (key2195, 1), (key2304, 1), (key2093, -1), (key2304, -1)]

theorem rawRowCheck7106 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form2 = rawRow7106 := by decide +kernel

def row7106 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

theorem rowCheck7106 : row7106 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7106 := by decide +kernel

theorem rowEval7106 (x : Key → ℝ) : Integer.Sparse.eval row7106 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck7106, Integer.Sparse.eval_collectBalanced, rawRowCheck7106]

def rawRow7107 : Integer.Sparse Key := [(key2350, -1), (key2315, -1), (key2315, 2), (key2348, -1), (key2312, -1), (key2348, 2), (key2202, 2), (key2312, -1), (key2202, -1), (key2311, 2), (key2311, -1), (key2201, -1), (key2350, 1), (key2315, 1), (key2315, -2), (key2344, 1), (key2307, 1), (key2344, -2), (key2097, -2), (key2307, 1), (key2097, 1), (key2306, -2), (key2306, 1), (key2096, 1), (key2348, -1), (key2202, -1), (key2312, 1), (key2202, 1), (key2344, 1), (key2097, 1), (key2307, -1), (key2097, -1), (key2342, -1), (key2196, -1), (key2342, 1), (key2094, 1), (key2304, 1), (key2195, 1), (key2304, -1), (key2093, -1)]

theorem rawRowCheck7107 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form2 = rawRow7107 := by decide +kernel

def row7107 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

theorem rowCheck7107 : row7107 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7107 := by decide +kernel

theorem rowEval7107 (x : Key → ℝ) : Integer.Sparse.eval row7107 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck7107, Integer.Sparse.eval_collectBalanced, rawRowCheck7107]

def rawRow7108 : Integer.Sparse Key := [(key717, -4), (key719, 2), (key719, 2), (key719, 2), (key719, 2), (key720, -4), (key894, 2), (key896, -1), (key896, -1), (key894, 2), (key917, -1), (key917, -1), (key896, -1), (key896, -1), (key917, -1), (key917, -1), (key920, 2), (key920, 2), (key949, -1), (key949, -1), (key950, 2), (key949, -1), (key949, -1), (key956, 2), (key956, 2), (key958, -1), (key958, -1), (key950, 2), (key958, -1), (key958, -1)]

theorem rawRowCheck7108 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form3 = rawRow7108 := by decide +kernel

def row7108 : Integer.Sparse Key := [(key717, -4), (key719, 8), (key720, -4), (key894, 4), (key896, -4), (key917, -4), (key920, 4), (key949, -4), (key950, 4), (key956, 4), (key958, -4)]

theorem rowCheck7108 : row7108 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7108 := by decide +kernel

theorem rowEval7108 (x : Key → ℝ) : Integer.Sparse.eval row7108 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7108, Integer.Sparse.eval_collectBalanced, rawRowCheck7108]

def rawRow7109 : Integer.Sparse Key := [(key719, -4), (key717, 2), (key719, 2), (key719, 2), (key720, 2), (key719, -4), (key896, 2), (key894, -1), (key896, -1), (key917, 2), (key894, -1), (key917, -1), (key917, -1), (key920, -1), (key896, -1), (key920, -1), (key896, 2), (key917, 2), (key949, -1), (key950, -1), (key949, 2), (key956, -1), (key958, -1), (key949, 2), (key958, 2), (key949, -1), (key956, -1), (key958, 2), (key950, -1), (key958, -1)]

theorem rawRowCheck7109 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form3 = rawRow7109 := by decide +kernel

def row7109 : Integer.Sparse Key := [(key717, 2), (key719, -4), (key720, 2), (key894, -2), (key896, 2), (key917, 2), (key920, -2), (key949, 2), (key950, -2), (key956, -2), (key958, 2)]

theorem rowCheck7109 : row7109 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7109 := by decide +kernel

theorem rowEval7109 (x : Key → ℝ) : Integer.Sparse.eval row7109 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7109, Integer.Sparse.eval_collectBalanced, rawRowCheck7109]

def rawRow7110 : Integer.Sparse Key := [(key719, -4), (key719, 2), (key717, 2), (key720, 2), (key719, 2), (key719, -4), (key896, 2), (key896, -1), (key894, -1), (key917, 2), (key917, -1), (key894, -1), (key920, -1), (key917, -1), (key920, -1), (key896, -1), (key917, 2), (key896, 2), (key950, -1), (key949, -1), (key949, 2), (key958, -1), (key956, -1), (key958, 2), (key949, 2), (key956, -1), (key949, -1), (key958, 2), (key958, -1), (key950, -1)]

theorem rawRowCheck7110 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form3 = rawRow7110 := by decide +kernel

def row7110 : Integer.Sparse Key := [(key717, 2), (key719, -4), (key720, 2), (key894, -2), (key896, 2), (key917, 2), (key920, -2), (key949, 2), (key950, -2), (key956, -2), (key958, 2)]

theorem rowCheck7110 : row7110 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7110 := by decide +kernel

theorem rowEval7110 (x : Key → ℝ) : Integer.Sparse.eval row7110 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck7110, Integer.Sparse.eval_collectBalanced, rawRowCheck7110]

def rawRow7111 : Integer.Sparse Key := [(key719, -4), (key719, 2), (key720, 2), (key717, 2), (key719, 2), (key719, -4), (key917, 2), (key917, -1), (key920, -1), (key896, 2), (key896, -1), (key920, -1), (key894, -1), (key896, -1), (key894, -1), (key917, -1), (key896, 2), (key917, 2), (key956, -1), (key958, -1), (key958, 2), (key949, -1), (key950, -1), (key949, 2), (key958, 2), (key950, -1), (key958, -1), (key949, 2), (key949, -1), (key956, -1)]

theorem rawRowCheck7111 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form3 = rawRow7111 := by decide +kernel

def row7111 : Integer.Sparse Key := [(key717, 2), (key719, -4), (key720, 2), (key894, -2), (key896, 2), (key917, 2), (key920, -2), (key949, 2), (key950, -2), (key956, -2), (key958, 2)]

theorem rowCheck7111 : row7111 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7111 := by decide +kernel

theorem rowEval7111 (x : Key → ℝ) : Integer.Sparse.eval row7111 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7111, Integer.Sparse.eval_collectBalanced, rawRowCheck7111]

def rawRow7112 : Integer.Sparse Key := [(key719, -4), (key720, 2), (key719, 2), (key719, 2), (key717, 2), (key719, -4), (key917, 2), (key920, -1), (key917, -1), (key896, 2), (key920, -1), (key896, -1), (key896, -1), (key894, -1), (key917, -1), (key894, -1), (key917, 2), (key896, 2), (key958, -1), (key956, -1), (key958, 2), (key950, -1), (key949, -1), (key958, 2), (key949, 2), (key958, -1), (key950, -1), (key949, 2), (key956, -1), (key949, -1)]

theorem rawRowCheck7112 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form3 = rawRow7112 := by decide +kernel

def row7112 : Integer.Sparse Key := [(key717, 2), (key719, -4), (key720, 2), (key894, -2), (key896, 2), (key917, 2), (key920, -2), (key949, 2), (key950, -2), (key956, -2), (key958, 2)]

theorem rowCheck7112 : row7112 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7112 := by decide +kernel

theorem rowEval7112 (x : Key → ℝ) : Integer.Sparse.eval row7112 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck7112, Integer.Sparse.eval_collectBalanced, rawRowCheck7112]

def rawRow7113 : Integer.Sparse Key := [(key720, -4), (key719, 2), (key719, 2), (key719, 2), (key719, 2), (key717, -4), (key920, 2), (key917, -1), (key917, -1), (key920, 2), (key896, -1), (key896, -1), (key917, -1), (key917, -1), (key896, -1), (key896, -1), (key894, 2), (key894, 2), (key958, -1), (key958, -1), (key956, 2), (key958, -1), (key958, -1), (key950, 2), (key950, 2), (key949, -1), (key949, -1), (key956, 2), (key949, -1), (key949, -1)]

theorem rawRowCheck7113 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form3 = rawRow7113 := by decide +kernel

def row7113 : Integer.Sparse Key := [(key717, -4), (key719, 8), (key720, -4), (key894, 4), (key896, -4), (key917, -4), (key920, 4), (key949, -4), (key950, 4), (key956, 4), (key958, -4)]

theorem rowCheck7113 : row7113 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7113 := by decide +kernel

theorem rowEval7113 (x : Key → ℝ) : Integer.Sparse.eval row7113 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck7113, Integer.Sparse.eval_collectBalanced, rawRowCheck7113]

def rawRow7114 : Integer.Sparse Key := [(key894, -4), (key896, 2), (key896, 2), (key949, 2), (key949, 2), (key950, -4), (key717, 2), (key719, -1), (key719, -1), (key894, 2), (key917, -1), (key917, -1), (key949, -1), (key949, -1), (key956, -1), (key956, -1), (key958, 2), (key958, 2), (key719, -1), (key719, -1), (key720, 2), (key896, -1), (key896, -1), (key917, 2), (key917, 2), (key920, -1), (key920, -1), (key950, 2), (key958, -1), (key958, -1)]

theorem rawRowCheck7114 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form3 = rawRow7114 := by decide +kernel

def row7114 : Integer.Sparse Key := [(key717, 2), (key719, -4), (key720, 2), (key894, -2), (key896, 2), (key917, 2), (key920, -2), (key949, 2), (key950, -2), (key956, -2), (key958, 2)]

theorem rowCheck7114 : row7114 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7114 := by decide +kernel

theorem rowEval7114 (x : Key → ℝ) : Integer.Sparse.eval row7114 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7114, Integer.Sparse.eval_collectBalanced, rawRowCheck7114]

def rawRow7115 : Integer.Sparse Key := [(key896, -4), (key894, 2), (key896, 2), (key949, 2), (key950, 2), (key949, -4), (key719, 2), (key717, -1), (key719, -1), (key917, 2), (key894, -1), (key917, -1), (key956, -1), (key958, -1), (key949, -1), (key958, -1), (key949, 2), (key956, 2), (key719, -1), (key720, -1), (key719, 2), (key917, -1), (key920, -1), (key896, 2), (key920, 2), (key896, -1), (key917, -1), (key958, 2), (key950, -1), (key958, -1)]

theorem rawRowCheck7115 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form3 = rawRow7115 := by decide +kernel

def row7115 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

theorem rowCheck7115 : row7115 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7115 := by decide +kernel

theorem rowEval7115 (x : Key → ℝ) : Integer.Sparse.eval row7115 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7115, Integer.Sparse.eval_collectBalanced, rawRowCheck7115]

def rawRow7116 : Integer.Sparse Key := [(key896, -4), (key896, 2), (key894, 2), (key950, 2), (key949, 2), (key949, -4), (key719, 2), (key719, -1), (key717, -1), (key917, 2), (key917, -1), (key894, -1), (key958, -1), (key956, -1), (key958, -1), (key949, -1), (key956, 2), (key949, 2), (key720, -1), (key719, -1), (key719, 2), (key920, -1), (key917, -1), (key920, 2), (key896, 2), (key917, -1), (key896, -1), (key958, 2), (key958, -1), (key950, -1)]

theorem rawRowCheck7116 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form3 = rawRow7116 := by decide +kernel

def row7116 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

theorem rowCheck7116 : row7116 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7116 := by decide +kernel

theorem rowEval7116 (x : Key → ℝ) : Integer.Sparse.eval row7116 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck7116, Integer.Sparse.eval_collectBalanced, rawRowCheck7116]

def rawRow7117 : Integer.Sparse Key := [(key894, -4), (key949, 2), (key949, 2), (key896, 2), (key896, 2), (key950, -4), (key894, 2), (key949, -1), (key949, -1), (key717, 2), (key956, -1), (key956, -1), (key719, -1), (key719, -1), (key917, -1), (key917, -1), (key958, 2), (key958, 2), (key896, -1), (key896, -1), (key950, 2), (key719, -1), (key719, -1), (key917, 2), (key917, 2), (key958, -1), (key958, -1), (key720, 2), (key920, -1), (key920, -1)]

theorem rawRowCheck7117 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form3 = rawRow7117 := by decide +kernel

def row7117 : Integer.Sparse Key := [(key717, 2), (key719, -4), (key720, 2), (key894, -2), (key896, 2), (key917, 2), (key920, -2), (key949, 2), (key950, -2), (key956, -2), (key958, 2)]

theorem rowCheck7117 : row7117 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7117 := by decide +kernel

theorem rowEval7117 (x : Key → ℝ) : Integer.Sparse.eval row7117 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7117, Integer.Sparse.eval_collectBalanced, rawRowCheck7117]

def rawRow7118 : Integer.Sparse Key := [(key949, -4), (key894, 2), (key949, 2), (key896, 2), (key950, 2), (key896, -4), (key949, 2), (key894, -1), (key949, -1), (key956, 2), (key717, -1), (key956, -1), (key917, -1), (key958, -1), (key719, -1), (key958, -1), (key719, 2), (key917, 2), (key896, -1), (key950, -1), (key896, 2), (key917, -1), (key958, -1), (key719, 2), (key958, 2), (key719, -1), (key917, -1), (key920, 2), (key720, -1), (key920, -1)]

theorem rawRowCheck7118 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form3 = rawRow7118 := by decide +kernel

def row7118 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

theorem rowCheck7118 : row7118 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7118 := by decide +kernel

theorem rowEval7118 (x : Key → ℝ) : Integer.Sparse.eval row7118 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7118, Integer.Sparse.eval_collectBalanced, rawRowCheck7118]

def rawRow7119 : Integer.Sparse Key := [(key949, -4), (key949, 2), (key894, 2), (key950, 2), (key896, 2), (key896, -4), (key949, 2), (key949, -1), (key894, -1), (key956, 2), (key956, -1), (key717, -1), (key958, -1), (key917, -1), (key958, -1), (key719, -1), (key917, 2), (key719, 2), (key950, -1), (key896, -1), (key896, 2), (key958, -1), (key917, -1), (key958, 2), (key719, 2), (key917, -1), (key719, -1), (key920, 2), (key920, -1), (key720, -1)]

theorem rawRowCheck7119 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form3 = rawRow7119 := by decide +kernel

def row7119 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

theorem rowCheck7119 : row7119 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7119 := by decide +kernel

theorem rowEval7119 (x : Key → ℝ) : Integer.Sparse.eval row7119 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7119, Integer.Sparse.eval_collectBalanced, rawRowCheck7119]

def rawRow7120 : Integer.Sparse Key := [(key896, -4), (key949, 2), (key950, 2), (key894, 2), (key896, 2), (key949, -4), (key917, 2), (key956, -1), (key958, -1), (key719, 2), (key949, -1), (key958, -1), (key717, -1), (key719, -1), (key894, -1), (key917, -1), (key949, 2), (key956, 2), (key917, -1), (key920, -1), (key958, 2), (key719, -1), (key720, -1), (key896, 2), (key920, 2), (key950, -1), (key958, -1), (key719, 2), (key896, -1), (key917, -1)]

theorem rawRowCheck7120 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form3 = rawRow7120 := by decide +kernel

def row7120 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

theorem rowCheck7120 : row7120 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7120 := by decide +kernel

theorem rowEval7120 (x : Key → ℝ) : Integer.Sparse.eval row7120 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7120, Integer.Sparse.eval_collectBalanced, rawRowCheck7120]

def rawRow7121 : Integer.Sparse Key := [(key896, -4), (key950, 2), (key949, 2), (key896, 2), (key894, 2), (key949, -4), (key917, 2), (key958, -1), (key956, -1), (key719, 2), (key958, -1), (key949, -1), (key719, -1), (key717, -1), (key917, -1), (key894, -1), (key956, 2), (key949, 2), (key920, -1), (key917, -1), (key958, 2), (key720, -1), (key719, -1), (key920, 2), (key896, 2), (key958, -1), (key950, -1), (key719, 2), (key917, -1), (key896, -1)]

theorem rawRowCheck7121 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form3 = rawRow7121 := by decide +kernel

def row7121 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

theorem rowCheck7121 : row7121 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7121 := by decide +kernel

theorem rowEval7121 (x : Key → ℝ) : Integer.Sparse.eval row7121 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck7121, Integer.Sparse.eval_collectBalanced, rawRowCheck7121]

def rawRow7122 : Integer.Sparse Key := [(key949, -4), (key896, 2), (key950, 2), (key894, 2), (key949, 2), (key896, -4), (key956, 2), (key917, -1), (key958, -1), (key949, 2), (key719, -1), (key958, -1), (key894, -1), (key949, -1), (key717, -1), (key956, -1), (key719, 2), (key917, 2), (key917, -1), (key958, -1), (key920, 2), (key896, -1), (key950, -1), (key719, 2), (key958, 2), (key720, -1), (key920, -1), (key896, 2), (key719, -1), (key917, -1)]

theorem rawRowCheck7122 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form3 = rawRow7122 := by decide +kernel

def row7122 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

theorem rowCheck7122 : row7122 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7122 := by decide +kernel

theorem rowEval7122 (x : Key → ℝ) : Integer.Sparse.eval row7122 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7122, Integer.Sparse.eval_collectBalanced, rawRowCheck7122]

def rawRow7123 : Integer.Sparse Key := [(key949, -4), (key950, 2), (key896, 2), (key949, 2), (key894, 2), (key896, -4), (key956, 2), (key958, -1), (key917, -1), (key949, 2), (key958, -1), (key719, -1), (key949, -1), (key894, -1), (key956, -1), (key717, -1), (key917, 2), (key719, 2), (key958, -1), (key917, -1), (key920, 2), (key950, -1), (key896, -1), (key958, 2), (key719, 2), (key920, -1), (key720, -1), (key896, 2), (key917, -1), (key719, -1)]

theorem rawRowCheck7123 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form3 = rawRow7123 := by decide +kernel

def row7123 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

theorem rowCheck7123 : row7123 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7123 := by decide +kernel

theorem rowEval7123 (x : Key → ℝ) : Integer.Sparse.eval row7123 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7123, Integer.Sparse.eval_collectBalanced, rawRowCheck7123]

def rawRow7124 : Integer.Sparse Key := [(key950, -4), (key896, 2), (key949, 2), (key896, 2), (key949, 2), (key894, -4), (key958, 2), (key917, -1), (key956, -1), (key958, 2), (key719, -1), (key949, -1), (key917, -1), (key956, -1), (key719, -1), (key949, -1), (key717, 2), (key894, 2), (key920, -1), (key958, -1), (key917, 2), (key920, -1), (key958, -1), (key720, 2), (key950, 2), (key719, -1), (key896, -1), (key917, 2), (key719, -1), (key896, -1)]

theorem rawRowCheck7124 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form3 = rawRow7124 := by decide +kernel

def row7124 : Integer.Sparse Key := [(key717, 2), (key719, -4), (key720, 2), (key894, -2), (key896, 2), (key917, 2), (key920, -2), (key949, 2), (key950, -2), (key956, -2), (key958, 2)]

theorem rowCheck7124 : row7124 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7124 := by decide +kernel

theorem rowEval7124 (x : Key → ℝ) : Integer.Sparse.eval row7124 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck7124, Integer.Sparse.eval_collectBalanced, rawRowCheck7124]

def rawRow7125 : Integer.Sparse Key := [(key950, -4), (key949, 2), (key896, 2), (key949, 2), (key896, 2), (key894, -4), (key958, 2), (key956, -1), (key917, -1), (key958, 2), (key949, -1), (key719, -1), (key956, -1), (key917, -1), (key949, -1), (key719, -1), (key894, 2), (key717, 2), (key958, -1), (key920, -1), (key917, 2), (key958, -1), (key920, -1), (key950, 2), (key720, 2), (key896, -1), (key719, -1), (key917, 2), (key896, -1), (key719, -1)]

theorem rawRowCheck7125 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form3 = rawRow7125 := by decide +kernel

def row7125 : Integer.Sparse Key := [(key717, 2), (key719, -4), (key720, 2), (key894, -2), (key896, 2), (key917, 2), (key920, -2), (key949, 2), (key950, -2), (key956, -2), (key958, 2)]

theorem rowCheck7125 : row7125 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7125 := by decide +kernel

theorem rowEval7125 (x : Key → ℝ) : Integer.Sparse.eval row7125 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7125, Integer.Sparse.eval_collectBalanced, rawRowCheck7125]

def rawRow7126 : Integer.Sparse Key := [(key917, -4), (key917, 2), (key920, 2), (key956, 2), (key958, 2), (key958, -4), (key719, 2), (key719, -1), (key720, -1), (key896, 2), (key896, -1), (key920, -1), (key949, -1), (key950, -1), (key949, -1), (key958, -1), (key950, 2), (key958, 2), (key717, -1), (key719, -1), (key719, 2), (key894, -1), (key896, -1), (key894, 2), (key917, 2), (key896, -1), (key917, -1), (key949, 2), (key949, -1), (key956, -1)]

theorem rawRowCheck7126 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form3 = rawRow7126 := by decide +kernel

def row7126 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

theorem rowCheck7126 : row7126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7126 := by decide +kernel

theorem rowEval7126 (x : Key → ℝ) : Integer.Sparse.eval row7126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7126, Integer.Sparse.eval_collectBalanced, rawRowCheck7126]

def rawRow7127 : Integer.Sparse Key := [(key917, -4), (key920, 2), (key917, 2), (key958, 2), (key956, 2), (key958, -4), (key719, 2), (key720, -1), (key719, -1), (key896, 2), (key920, -1), (key896, -1), (key950, -1), (key949, -1), (key958, -1), (key949, -1), (key958, 2), (key950, 2), (key719, -1), (key717, -1), (key719, 2), (key896, -1), (key894, -1), (key917, 2), (key894, 2), (key917, -1), (key896, -1), (key949, 2), (key956, -1), (key949, -1)]

theorem rawRowCheck7127 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form3 = rawRow7127 := by decide +kernel

def row7127 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

theorem rowCheck7127 : row7127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7127 := by decide +kernel

theorem rowEval7127 (x : Key → ℝ) : Integer.Sparse.eval row7127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck7127, Integer.Sparse.eval_collectBalanced, rawRowCheck7127]

def rawRow7128 : Integer.Sparse Key := [(key920, -4), (key917, 2), (key917, 2), (key958, 2), (key958, 2), (key956, -4), (key720, 2), (key719, -1), (key719, -1), (key920, 2), (key896, -1), (key896, -1), (key958, -1), (key958, -1), (key950, -1), (key950, -1), (key949, 2), (key949, 2), (key719, -1), (key719, -1), (key717, 2), (key917, -1), (key917, -1), (key896, 2), (key896, 2), (key894, -1), (key894, -1), (key956, 2), (key949, -1), (key949, -1)]

theorem rawRowCheck7128 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form3 = rawRow7128 := by decide +kernel

def row7128 : Integer.Sparse Key := [(key717, 2), (key719, -4), (key720, 2), (key894, -2), (key896, 2), (key917, 2), (key920, -2), (key949, 2), (key950, -2), (key956, -2), (key958, 2)]

theorem rowCheck7128 : row7128 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7128 := by decide +kernel

theorem rowEval7128 (x : Key → ℝ) : Integer.Sparse.eval row7128 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck7128, Integer.Sparse.eval_collectBalanced, rawRowCheck7128]

def rawRow7129 : Integer.Sparse Key := [(key917, -4), (key956, 2), (key958, 2), (key917, 2), (key920, 2), (key958, -4), (key896, 2), (key949, -1), (key950, -1), (key719, 2), (key949, -1), (key958, -1), (key719, -1), (key720, -1), (key896, -1), (key920, -1), (key950, 2), (key958, 2), (key894, -1), (key896, -1), (key949, 2), (key717, -1), (key719, -1), (key894, 2), (key917, 2), (key949, -1), (key956, -1), (key719, 2), (key896, -1), (key917, -1)]

theorem rawRowCheck7129 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form3 = rawRow7129 := by decide +kernel

def row7129 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

theorem rowCheck7129 : row7129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7129 := by decide +kernel

theorem rowEval7129 (x : Key → ℝ) : Integer.Sparse.eval row7129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7129, Integer.Sparse.eval_collectBalanced, rawRowCheck7129]

def rawRow7130 : Integer.Sparse Key := [(key917, -4), (key958, 2), (key956, 2), (key920, 2), (key917, 2), (key958, -4), (key896, 2), (key950, -1), (key949, -1), (key719, 2), (key958, -1), (key949, -1), (key720, -1), (key719, -1), (key920, -1), (key896, -1), (key958, 2), (key950, 2), (key896, -1), (key894, -1), (key949, 2), (key719, -1), (key717, -1), (key917, 2), (key894, 2), (key956, -1), (key949, -1), (key719, 2), (key917, -1), (key896, -1)]

theorem rawRowCheck7130 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form3 = rawRow7130 := by decide +kernel

def row7130 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

theorem rowCheck7130 : row7130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7130 := by decide +kernel

theorem rowEval7130 (x : Key → ℝ) : Integer.Sparse.eval row7130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck7130, Integer.Sparse.eval_collectBalanced, rawRowCheck7130]

def rawRow7131 : Integer.Sparse Key := [(key956, -4), (key917, 2), (key958, 2), (key917, 2), (key958, 2), (key920, -4), (key949, 2), (key896, -1), (key950, -1), (key949, 2), (key719, -1), (key958, -1), (key896, -1), (key950, -1), (key719, -1), (key958, -1), (key720, 2), (key920, 2), (key894, -1), (key949, -1), (key896, 2), (key894, -1), (key949, -1), (key717, 2), (key956, 2), (key719, -1), (key917, -1), (key896, 2), (key719, -1), (key917, -1)]

theorem rawRowCheck7131 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form3 = rawRow7131 := by decide +kernel

def row7131 : Integer.Sparse Key := [(key717, 2), (key719, -4), (key720, 2), (key894, -2), (key896, 2), (key917, 2), (key920, -2), (key949, 2), (key950, -2), (key956, -2), (key958, 2)]

theorem rowCheck7131 : row7131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7131 := by decide +kernel

theorem rowEval7131 (x : Key → ℝ) : Integer.Sparse.eval row7131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7131, Integer.Sparse.eval_collectBalanced, rawRowCheck7131]

def rawRow7132 : Integer.Sparse Key := [(key956, -4), (key958, 2), (key917, 2), (key958, 2), (key917, 2), (key920, -4), (key949, 2), (key950, -1), (key896, -1), (key949, 2), (key958, -1), (key719, -1), (key950, -1), (key896, -1), (key958, -1), (key719, -1), (key920, 2), (key720, 2), (key949, -1), (key894, -1), (key896, 2), (key949, -1), (key894, -1), (key956, 2), (key717, 2), (key917, -1), (key719, -1), (key896, 2), (key917, -1), (key719, -1)]

theorem rawRowCheck7132 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form3 = rawRow7132 := by decide +kernel

def row7132 : Integer.Sparse Key := [(key717, 2), (key719, -4), (key720, 2), (key894, -2), (key896, 2), (key917, 2), (key920, -2), (key949, 2), (key950, -2), (key956, -2), (key958, 2)]

theorem rowCheck7132 : row7132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7132 := by decide +kernel

theorem rowEval7132 (x : Key → ℝ) : Integer.Sparse.eval row7132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7132, Integer.Sparse.eval_collectBalanced, rawRowCheck7132]

def rawRow7133 : Integer.Sparse Key := [(key958, -4), (key917, 2), (key956, 2), (key920, 2), (key958, 2), (key917, -4), (key950, 2), (key896, -1), (key949, -1), (key958, 2), (key719, -1), (key949, -1), (key920, -1), (key958, -1), (key720, -1), (key950, -1), (key719, 2), (key896, 2), (key896, -1), (key949, -1), (key894, 2), (key917, -1), (key956, -1), (key719, 2), (key949, 2), (key717, -1), (key894, -1), (key917, 2), (key719, -1), (key896, -1)]

theorem rawRowCheck7133 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form3 = rawRow7133 := by decide +kernel

def row7133 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

theorem rowCheck7133 : row7133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7133 := by decide +kernel

theorem rowEval7133 (x : Key → ℝ) : Integer.Sparse.eval row7133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck7133, Integer.Sparse.eval_collectBalanced, rawRowCheck7133]

def rawRow7134 : Integer.Sparse Key := [(key958, -4), (key956, 2), (key917, 2), (key958, 2), (key920, 2), (key917, -4), (key950, 2), (key949, -1), (key896, -1), (key958, 2), (key949, -1), (key719, -1), (key958, -1), (key920, -1), (key950, -1), (key720, -1), (key896, 2), (key719, 2), (key949, -1), (key896, -1), (key894, 2), (key956, -1), (key917, -1), (key949, 2), (key719, 2), (key894, -1), (key717, -1), (key917, 2), (key896, -1), (key719, -1)]

theorem rawRowCheck7134 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form3 = rawRow7134 := by decide +kernel

def row7134 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

theorem rowCheck7134 : row7134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7134 := by decide +kernel

theorem rowEval7134 (x : Key → ℝ) : Integer.Sparse.eval row7134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7134, Integer.Sparse.eval_collectBalanced, rawRowCheck7134]

def rawRow7135 : Integer.Sparse Key := [(key920, -4), (key958, 2), (key958, 2), (key917, 2), (key917, 2), (key956, -4), (key920, 2), (key958, -1), (key958, -1), (key720, 2), (key950, -1), (key950, -1), (key719, -1), (key719, -1), (key896, -1), (key896, -1), (key949, 2), (key949, 2), (key917, -1), (key917, -1), (key956, 2), (key719, -1), (key719, -1), (key896, 2), (key896, 2), (key949, -1), (key949, -1), (key717, 2), (key894, -1), (key894, -1)]

theorem rawRowCheck7135 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form3 = rawRow7135 := by decide +kernel

def row7135 : Integer.Sparse Key := [(key717, 2), (key719, -4), (key720, 2), (key894, -2), (key896, 2), (key917, 2), (key920, -2), (key949, 2), (key950, -2), (key956, -2), (key958, 2)]

theorem rowCheck7135 : row7135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7135 := by decide +kernel

theorem rowEval7135 (x : Key → ℝ) : Integer.Sparse.eval row7135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck7135, Integer.Sparse.eval_collectBalanced, rawRowCheck7135]

def rawRow7136 : Integer.Sparse Key := [(key958, -4), (key920, 2), (key958, 2), (key917, 2), (key956, 2), (key917, -4), (key958, 2), (key920, -1), (key958, -1), (key950, 2), (key720, -1), (key950, -1), (key896, -1), (key949, -1), (key719, -1), (key949, -1), (key719, 2), (key896, 2), (key917, -1), (key956, -1), (key917, 2), (key896, -1), (key949, -1), (key719, 2), (key949, 2), (key719, -1), (key896, -1), (key894, 2), (key717, -1), (key894, -1)]

theorem rawRowCheck7136 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form3 = rawRow7136 := by decide +kernel

def row7136 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

theorem rowCheck7136 : row7136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7136 := by decide +kernel

theorem rowEval7136 (x : Key → ℝ) : Integer.Sparse.eval row7136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck7136, Integer.Sparse.eval_collectBalanced, rawRowCheck7136]

def rawRow7137 : Integer.Sparse Key := [(key958, -4), (key958, 2), (key920, 2), (key956, 2), (key917, 2), (key917, -4), (key958, 2), (key958, -1), (key920, -1), (key950, 2), (key950, -1), (key720, -1), (key949, -1), (key896, -1), (key949, -1), (key719, -1), (key896, 2), (key719, 2), (key956, -1), (key917, -1), (key917, 2), (key949, -1), (key896, -1), (key949, 2), (key719, 2), (key896, -1), (key719, -1), (key894, 2), (key894, -1), (key717, -1)]

theorem rawRowCheck7137 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form3 = rawRow7137 := by decide +kernel

def row7137 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

theorem rowCheck7137 : row7137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7137 := by decide +kernel

theorem rowEval7137 (x : Key → ℝ) : Integer.Sparse.eval row7137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7137, Integer.Sparse.eval_collectBalanced, rawRowCheck7137]

def rawRow7138 : Integer.Sparse Key := [(key2002, -4), (key2004, 2), (key2004, 2), (key2004, 2), (key2004, 2), (key2005, -4), (key2271, 2), (key2273, -1), (key2273, -1), (key2271, 2), (key2295, -1), (key2295, -1), (key2273, -1), (key2273, -1), (key2295, -1), (key2295, -1), (key2297, 2), (key2297, 2), (key2325, -1), (key2325, -1), (key2326, 2), (key2325, -1), (key2325, -1), (key2337, 2), (key2337, 2), (key2338, -1), (key2338, -1), (key2326, 2), (key2338, -1), (key2338, -1)]

theorem rawRowCheck7138 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form4 = rawRow7138 := by decide +kernel

def row7138 : Integer.Sparse Key := [(key2002, -4), (key2004, 8), (key2005, -4), (key2271, 4), (key2273, -4), (key2295, -4), (key2297, 4), (key2325, -4), (key2326, 4), (key2337, 4), (key2338, -4)]

theorem rowCheck7138 : row7138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7138 := by decide +kernel

theorem rowEval7138 (x : Key → ℝ) : Integer.Sparse.eval row7138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7138, Integer.Sparse.eval_collectBalanced, rawRowCheck7138]

def rawRow7139 : Integer.Sparse Key := [(key2004, -4), (key2002, 2), (key2004, 2), (key2004, 2), (key2005, 2), (key2004, -4), (key2273, 2), (key2271, -1), (key2273, -1), (key2295, 2), (key2271, -1), (key2295, -1), (key2295, -1), (key2297, -1), (key2273, -1), (key2297, -1), (key2273, 2), (key2295, 2), (key2325, -1), (key2326, -1), (key2325, 2), (key2337, -1), (key2338, -1), (key2325, 2), (key2338, 2), (key2325, -1), (key2337, -1), (key2338, 2), (key2326, -1), (key2338, -1)]

theorem rawRowCheck7139 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form4 = rawRow7139 := by decide +kernel

def row7139 : Integer.Sparse Key := [(key2002, 2), (key2004, -4), (key2005, 2), (key2271, -2), (key2273, 2), (key2295, 2), (key2297, -2), (key2325, 2), (key2326, -2), (key2337, -2), (key2338, 2)]

theorem rowCheck7139 : row7139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7139 := by decide +kernel

theorem rowEval7139 (x : Key → ℝ) : Integer.Sparse.eval row7139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7139, Integer.Sparse.eval_collectBalanced, rawRowCheck7139]

def rawRow7140 : Integer.Sparse Key := [(key2004, -4), (key2004, 2), (key2002, 2), (key2005, 2), (key2004, 2), (key2004, -4), (key2273, 2), (key2273, -1), (key2271, -1), (key2295, 2), (key2295, -1), (key2271, -1), (key2297, -1), (key2295, -1), (key2297, -1), (key2273, -1), (key2295, 2), (key2273, 2), (key2326, -1), (key2325, -1), (key2325, 2), (key2338, -1), (key2337, -1), (key2338, 2), (key2325, 2), (key2337, -1), (key2325, -1), (key2338, 2), (key2338, -1), (key2326, -1)]

theorem rawRowCheck7140 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form4 = rawRow7140 := by decide +kernel

def row7140 : Integer.Sparse Key := [(key2002, 2), (key2004, -4), (key2005, 2), (key2271, -2), (key2273, 2), (key2295, 2), (key2297, -2), (key2325, 2), (key2326, -2), (key2337, -2), (key2338, 2)]

theorem rowCheck7140 : row7140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7140 := by decide +kernel

theorem rowEval7140 (x : Key → ℝ) : Integer.Sparse.eval row7140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck7140, Integer.Sparse.eval_collectBalanced, rawRowCheck7140]

def rawRow7141 : Integer.Sparse Key := [(key2004, -4), (key2004, 2), (key2005, 2), (key2002, 2), (key2004, 2), (key2004, -4), (key2295, 2), (key2295, -1), (key2297, -1), (key2273, 2), (key2273, -1), (key2297, -1), (key2271, -1), (key2273, -1), (key2271, -1), (key2295, -1), (key2273, 2), (key2295, 2), (key2337, -1), (key2338, -1), (key2338, 2), (key2325, -1), (key2326, -1), (key2325, 2), (key2338, 2), (key2326, -1), (key2338, -1), (key2325, 2), (key2325, -1), (key2337, -1)]

theorem rawRowCheck7141 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form4 = rawRow7141 := by decide +kernel

def row7141 : Integer.Sparse Key := [(key2002, 2), (key2004, -4), (key2005, 2), (key2271, -2), (key2273, 2), (key2295, 2), (key2297, -2), (key2325, 2), (key2326, -2), (key2337, -2), (key2338, 2)]

theorem rowCheck7141 : row7141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7141 := by decide +kernel

theorem rowEval7141 (x : Key → ℝ) : Integer.Sparse.eval row7141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7141, Integer.Sparse.eval_collectBalanced, rawRowCheck7141]

def rawRow7142 : Integer.Sparse Key := [(key2004, -4), (key2005, 2), (key2004, 2), (key2004, 2), (key2002, 2), (key2004, -4), (key2295, 2), (key2297, -1), (key2295, -1), (key2273, 2), (key2297, -1), (key2273, -1), (key2273, -1), (key2271, -1), (key2295, -1), (key2271, -1), (key2295, 2), (key2273, 2), (key2338, -1), (key2337, -1), (key2338, 2), (key2326, -1), (key2325, -1), (key2338, 2), (key2325, 2), (key2338, -1), (key2326, -1), (key2325, 2), (key2337, -1), (key2325, -1)]

theorem rawRowCheck7142 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form4 = rawRow7142 := by decide +kernel

def row7142 : Integer.Sparse Key := [(key2002, 2), (key2004, -4), (key2005, 2), (key2271, -2), (key2273, 2), (key2295, 2), (key2297, -2), (key2325, 2), (key2326, -2), (key2337, -2), (key2338, 2)]

theorem rowCheck7142 : row7142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7142 := by decide +kernel

theorem rowEval7142 (x : Key → ℝ) : Integer.Sparse.eval row7142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck7142, Integer.Sparse.eval_collectBalanced, rawRowCheck7142]

def rawRow7143 : Integer.Sparse Key := [(key2005, -4), (key2004, 2), (key2004, 2), (key2004, 2), (key2004, 2), (key2002, -4), (key2297, 2), (key2295, -1), (key2295, -1), (key2297, 2), (key2273, -1), (key2273, -1), (key2295, -1), (key2295, -1), (key2273, -1), (key2273, -1), (key2271, 2), (key2271, 2), (key2338, -1), (key2338, -1), (key2337, 2), (key2338, -1), (key2338, -1), (key2326, 2), (key2326, 2), (key2325, -1), (key2325, -1), (key2337, 2), (key2325, -1), (key2325, -1)]

theorem rawRowCheck7143 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form4 = rawRow7143 := by decide +kernel

def row7143 : Integer.Sparse Key := [(key2002, -4), (key2004, 8), (key2005, -4), (key2271, 4), (key2273, -4), (key2295, -4), (key2297, 4), (key2325, -4), (key2326, 4), (key2337, 4), (key2338, -4)]

theorem rowCheck7143 : row7143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7143 := by decide +kernel

theorem rowEval7143 (x : Key → ℝ) : Integer.Sparse.eval row7143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck7143, Integer.Sparse.eval_collectBalanced, rawRowCheck7143]

def rawRow7144 : Integer.Sparse Key := [(key2271, -4), (key2273, 2), (key2273, 2), (key2325, 2), (key2325, 2), (key2326, -4), (key2002, 2), (key2004, -1), (key2004, -1), (key2271, 2), (key2295, -1), (key2295, -1), (key2325, -1), (key2325, -1), (key2337, -1), (key2337, -1), (key2338, 2), (key2338, 2), (key2004, -1), (key2004, -1), (key2005, 2), (key2273, -1), (key2273, -1), (key2295, 2), (key2295, 2), (key2297, -1), (key2297, -1), (key2326, 2), (key2338, -1), (key2338, -1)]

theorem rawRowCheck7144 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form4 = rawRow7144 := by decide +kernel

def row7144 : Integer.Sparse Key := [(key2002, 2), (key2004, -4), (key2005, 2), (key2271, -2), (key2273, 2), (key2295, 2), (key2297, -2), (key2325, 2), (key2326, -2), (key2337, -2), (key2338, 2)]

theorem rowCheck7144 : row7144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7144 := by decide +kernel

theorem rowEval7144 (x : Key → ℝ) : Integer.Sparse.eval row7144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7144, Integer.Sparse.eval_collectBalanced, rawRowCheck7144]

def rawRow7145 : Integer.Sparse Key := [(key2273, -4), (key2271, 2), (key2273, 2), (key2325, 2), (key2326, 2), (key2325, -4), (key2004, 2), (key2002, -1), (key2004, -1), (key2295, 2), (key2271, -1), (key2295, -1), (key2337, -1), (key2338, -1), (key2325, -1), (key2338, -1), (key2325, 2), (key2337, 2), (key2004, -1), (key2005, -1), (key2004, 2), (key2295, -1), (key2297, -1), (key2273, 2), (key2297, 2), (key2273, -1), (key2295, -1), (key2338, 2), (key2326, -1), (key2338, -1)]

theorem rawRowCheck7145 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form4 = rawRow7145 := by decide +kernel

def row7145 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

theorem rowCheck7145 : row7145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7145 := by decide +kernel

theorem rowEval7145 (x : Key → ℝ) : Integer.Sparse.eval row7145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7145, Integer.Sparse.eval_collectBalanced, rawRowCheck7145]

def rawRow7146 : Integer.Sparse Key := [(key2273, -4), (key2273, 2), (key2271, 2), (key2326, 2), (key2325, 2), (key2325, -4), (key2004, 2), (key2004, -1), (key2002, -1), (key2295, 2), (key2295, -1), (key2271, -1), (key2338, -1), (key2337, -1), (key2338, -1), (key2325, -1), (key2337, 2), (key2325, 2), (key2005, -1), (key2004, -1), (key2004, 2), (key2297, -1), (key2295, -1), (key2297, 2), (key2273, 2), (key2295, -1), (key2273, -1), (key2338, 2), (key2338, -1), (key2326, -1)]

theorem rawRowCheck7146 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form4 = rawRow7146 := by decide +kernel

def row7146 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

theorem rowCheck7146 : row7146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7146 := by decide +kernel

theorem rowEval7146 (x : Key → ℝ) : Integer.Sparse.eval row7146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck7146, Integer.Sparse.eval_collectBalanced, rawRowCheck7146]

def rawRow7147 : Integer.Sparse Key := [(key2271, -4), (key2325, 2), (key2325, 2), (key2273, 2), (key2273, 2), (key2326, -4), (key2271, 2), (key2325, -1), (key2325, -1), (key2002, 2), (key2337, -1), (key2337, -1), (key2004, -1), (key2004, -1), (key2295, -1), (key2295, -1), (key2338, 2), (key2338, 2), (key2273, -1), (key2273, -1), (key2326, 2), (key2004, -1), (key2004, -1), (key2295, 2), (key2295, 2), (key2338, -1), (key2338, -1), (key2005, 2), (key2297, -1), (key2297, -1)]

theorem rawRowCheck7147 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form4 = rawRow7147 := by decide +kernel

def row7147 : Integer.Sparse Key := [(key2002, 2), (key2004, -4), (key2005, 2), (key2271, -2), (key2273, 2), (key2295, 2), (key2297, -2), (key2325, 2), (key2326, -2), (key2337, -2), (key2338, 2)]

theorem rowCheck7147 : row7147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7147 := by decide +kernel

theorem rowEval7147 (x : Key → ℝ) : Integer.Sparse.eval row7147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7147, Integer.Sparse.eval_collectBalanced, rawRowCheck7147]

def rawRow7148 : Integer.Sparse Key := [(key2325, -4), (key2271, 2), (key2325, 2), (key2273, 2), (key2326, 2), (key2273, -4), (key2325, 2), (key2271, -1), (key2325, -1), (key2337, 2), (key2002, -1), (key2337, -1), (key2295, -1), (key2338, -1), (key2004, -1), (key2338, -1), (key2004, 2), (key2295, 2), (key2273, -1), (key2326, -1), (key2273, 2), (key2295, -1), (key2338, -1), (key2004, 2), (key2338, 2), (key2004, -1), (key2295, -1), (key2297, 2), (key2005, -1), (key2297, -1)]

theorem rawRowCheck7148 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form4 = rawRow7148 := by decide +kernel

def row7148 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

theorem rowCheck7148 : row7148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7148 := by decide +kernel

theorem rowEval7148 (x : Key → ℝ) : Integer.Sparse.eval row7148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7148, Integer.Sparse.eval_collectBalanced, rawRowCheck7148]

def rawRow7149 : Integer.Sparse Key := [(key2325, -4), (key2325, 2), (key2271, 2), (key2326, 2), (key2273, 2), (key2273, -4), (key2325, 2), (key2325, -1), (key2271, -1), (key2337, 2), (key2337, -1), (key2002, -1), (key2338, -1), (key2295, -1), (key2338, -1), (key2004, -1), (key2295, 2), (key2004, 2), (key2326, -1), (key2273, -1), (key2273, 2), (key2338, -1), (key2295, -1), (key2338, 2), (key2004, 2), (key2295, -1), (key2004, -1), (key2297, 2), (key2297, -1), (key2005, -1)]

theorem rawRowCheck7149 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form4 = rawRow7149 := by decide +kernel

def row7149 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

theorem rowCheck7149 : row7149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7149 := by decide +kernel

theorem rowEval7149 (x : Key → ℝ) : Integer.Sparse.eval row7149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7149, Integer.Sparse.eval_collectBalanced, rawRowCheck7149]

def rawRow7150 : Integer.Sparse Key := [(key2273, -4), (key2325, 2), (key2326, 2), (key2271, 2), (key2273, 2), (key2325, -4), (key2295, 2), (key2337, -1), (key2338, -1), (key2004, 2), (key2325, -1), (key2338, -1), (key2002, -1), (key2004, -1), (key2271, -1), (key2295, -1), (key2325, 2), (key2337, 2), (key2295, -1), (key2297, -1), (key2338, 2), (key2004, -1), (key2005, -1), (key2273, 2), (key2297, 2), (key2326, -1), (key2338, -1), (key2004, 2), (key2273, -1), (key2295, -1)]

theorem rawRowCheck7150 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form4 = rawRow7150 := by decide +kernel

def row7150 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

theorem rowCheck7150 : row7150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7150 := by decide +kernel

theorem rowEval7150 (x : Key → ℝ) : Integer.Sparse.eval row7150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7150, Integer.Sparse.eval_collectBalanced, rawRowCheck7150]

def rawRow7151 : Integer.Sparse Key := [(key2273, -4), (key2326, 2), (key2325, 2), (key2273, 2), (key2271, 2), (key2325, -4), (key2295, 2), (key2338, -1), (key2337, -1), (key2004, 2), (key2338, -1), (key2325, -1), (key2004, -1), (key2002, -1), (key2295, -1), (key2271, -1), (key2337, 2), (key2325, 2), (key2297, -1), (key2295, -1), (key2338, 2), (key2005, -1), (key2004, -1), (key2297, 2), (key2273, 2), (key2338, -1), (key2326, -1), (key2004, 2), (key2295, -1), (key2273, -1)]

theorem rawRowCheck7151 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form4 = rawRow7151 := by decide +kernel

def row7151 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

theorem rowCheck7151 : row7151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7151 := by decide +kernel

theorem rowEval7151 (x : Key → ℝ) : Integer.Sparse.eval row7151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck7151, Integer.Sparse.eval_collectBalanced, rawRowCheck7151]

def rawRow7152 : Integer.Sparse Key := [(key2325, -4), (key2273, 2), (key2326, 2), (key2271, 2), (key2325, 2), (key2273, -4), (key2337, 2), (key2295, -1), (key2338, -1), (key2325, 2), (key2004, -1), (key2338, -1), (key2271, -1), (key2325, -1), (key2002, -1), (key2337, -1), (key2004, 2), (key2295, 2), (key2295, -1), (key2338, -1), (key2297, 2), (key2273, -1), (key2326, -1), (key2004, 2), (key2338, 2), (key2005, -1), (key2297, -1), (key2273, 2), (key2004, -1), (key2295, -1)]

theorem rawRowCheck7152 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form4 = rawRow7152 := by decide +kernel

def row7152 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

theorem rowCheck7152 : row7152 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7152 := by decide +kernel

theorem rowEval7152 (x : Key → ℝ) : Integer.Sparse.eval row7152 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7152, Integer.Sparse.eval_collectBalanced, rawRowCheck7152]

def rawRow7153 : Integer.Sparse Key := [(key2325, -4), (key2326, 2), (key2273, 2), (key2325, 2), (key2271, 2), (key2273, -4), (key2337, 2), (key2338, -1), (key2295, -1), (key2325, 2), (key2338, -1), (key2004, -1), (key2325, -1), (key2271, -1), (key2337, -1), (key2002, -1), (key2295, 2), (key2004, 2), (key2338, -1), (key2295, -1), (key2297, 2), (key2326, -1), (key2273, -1), (key2338, 2), (key2004, 2), (key2297, -1), (key2005, -1), (key2273, 2), (key2295, -1), (key2004, -1)]

theorem rawRowCheck7153 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form4 = rawRow7153 := by decide +kernel

def row7153 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

theorem rowCheck7153 : row7153 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7153 := by decide +kernel

theorem rowEval7153 (x : Key → ℝ) : Integer.Sparse.eval row7153 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7153, Integer.Sparse.eval_collectBalanced, rawRowCheck7153]

def rawRow7154 : Integer.Sparse Key := [(key2326, -4), (key2273, 2), (key2325, 2), (key2273, 2), (key2325, 2), (key2271, -4), (key2338, 2), (key2295, -1), (key2337, -1), (key2338, 2), (key2004, -1), (key2325, -1), (key2295, -1), (key2337, -1), (key2004, -1), (key2325, -1), (key2002, 2), (key2271, 2), (key2297, -1), (key2338, -1), (key2295, 2), (key2297, -1), (key2338, -1), (key2005, 2), (key2326, 2), (key2004, -1), (key2273, -1), (key2295, 2), (key2004, -1), (key2273, -1)]

theorem rawRowCheck7154 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form4 = rawRow7154 := by decide +kernel

def row7154 : Integer.Sparse Key := [(key2002, 2), (key2004, -4), (key2005, 2), (key2271, -2), (key2273, 2), (key2295, 2), (key2297, -2), (key2325, 2), (key2326, -2), (key2337, -2), (key2338, 2)]

theorem rowCheck7154 : row7154 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7154 := by decide +kernel

theorem rowEval7154 (x : Key → ℝ) : Integer.Sparse.eval row7154 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck7154, Integer.Sparse.eval_collectBalanced, rawRowCheck7154]

def rawRow7155 : Integer.Sparse Key := [(key2326, -4), (key2325, 2), (key2273, 2), (key2325, 2), (key2273, 2), (key2271, -4), (key2338, 2), (key2337, -1), (key2295, -1), (key2338, 2), (key2325, -1), (key2004, -1), (key2337, -1), (key2295, -1), (key2325, -1), (key2004, -1), (key2271, 2), (key2002, 2), (key2338, -1), (key2297, -1), (key2295, 2), (key2338, -1), (key2297, -1), (key2326, 2), (key2005, 2), (key2273, -1), (key2004, -1), (key2295, 2), (key2273, -1), (key2004, -1)]

theorem rawRowCheck7155 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form4 = rawRow7155 := by decide +kernel

def row7155 : Integer.Sparse Key := [(key2002, 2), (key2004, -4), (key2005, 2), (key2271, -2), (key2273, 2), (key2295, 2), (key2297, -2), (key2325, 2), (key2326, -2), (key2337, -2), (key2338, 2)]

theorem rowCheck7155 : row7155 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7155 := by decide +kernel

theorem rowEval7155 (x : Key → ℝ) : Integer.Sparse.eval row7155 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7155, Integer.Sparse.eval_collectBalanced, rawRowCheck7155]

def rawRow7156 : Integer.Sparse Key := [(key2295, -4), (key2295, 2), (key2297, 2), (key2337, 2), (key2338, 2), (key2338, -4), (key2004, 2), (key2004, -1), (key2005, -1), (key2273, 2), (key2273, -1), (key2297, -1), (key2325, -1), (key2326, -1), (key2325, -1), (key2338, -1), (key2326, 2), (key2338, 2), (key2002, -1), (key2004, -1), (key2004, 2), (key2271, -1), (key2273, -1), (key2271, 2), (key2295, 2), (key2273, -1), (key2295, -1), (key2325, 2), (key2325, -1), (key2337, -1)]

theorem rawRowCheck7156 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form4 = rawRow7156 := by decide +kernel

def row7156 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

theorem rowCheck7156 : row7156 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7156 := by decide +kernel

theorem rowEval7156 (x : Key → ℝ) : Integer.Sparse.eval row7156 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7156, Integer.Sparse.eval_collectBalanced, rawRowCheck7156]

def rawRow7157 : Integer.Sparse Key := [(key2295, -4), (key2297, 2), (key2295, 2), (key2338, 2), (key2337, 2), (key2338, -4), (key2004, 2), (key2005, -1), (key2004, -1), (key2273, 2), (key2297, -1), (key2273, -1), (key2326, -1), (key2325, -1), (key2338, -1), (key2325, -1), (key2338, 2), (key2326, 2), (key2004, -1), (key2002, -1), (key2004, 2), (key2273, -1), (key2271, -1), (key2295, 2), (key2271, 2), (key2295, -1), (key2273, -1), (key2325, 2), (key2337, -1), (key2325, -1)]

theorem rawRowCheck7157 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form4 = rawRow7157 := by decide +kernel

def row7157 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

theorem rowCheck7157 : row7157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7157 := by decide +kernel

theorem rowEval7157 (x : Key → ℝ) : Integer.Sparse.eval row7157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck7157, Integer.Sparse.eval_collectBalanced, rawRowCheck7157]

def rawRow7158 : Integer.Sparse Key := [(key2297, -4), (key2295, 2), (key2295, 2), (key2338, 2), (key2338, 2), (key2337, -4), (key2005, 2), (key2004, -1), (key2004, -1), (key2297, 2), (key2273, -1), (key2273, -1), (key2338, -1), (key2338, -1), (key2326, -1), (key2326, -1), (key2325, 2), (key2325, 2), (key2004, -1), (key2004, -1), (key2002, 2), (key2295, -1), (key2295, -1), (key2273, 2), (key2273, 2), (key2271, -1), (key2271, -1), (key2337, 2), (key2325, -1), (key2325, -1)]

theorem rawRowCheck7158 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form4 = rawRow7158 := by decide +kernel

def row7158 : Integer.Sparse Key := [(key2002, 2), (key2004, -4), (key2005, 2), (key2271, -2), (key2273, 2), (key2295, 2), (key2297, -2), (key2325, 2), (key2326, -2), (key2337, -2), (key2338, 2)]

theorem rowCheck7158 : row7158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7158 := by decide +kernel

theorem rowEval7158 (x : Key → ℝ) : Integer.Sparse.eval row7158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck7158, Integer.Sparse.eval_collectBalanced, rawRowCheck7158]

def rawRow7159 : Integer.Sparse Key := [(key2295, -4), (key2337, 2), (key2338, 2), (key2295, 2), (key2297, 2), (key2338, -4), (key2273, 2), (key2325, -1), (key2326, -1), (key2004, 2), (key2325, -1), (key2338, -1), (key2004, -1), (key2005, -1), (key2273, -1), (key2297, -1), (key2326, 2), (key2338, 2), (key2271, -1), (key2273, -1), (key2325, 2), (key2002, -1), (key2004, -1), (key2271, 2), (key2295, 2), (key2325, -1), (key2337, -1), (key2004, 2), (key2273, -1), (key2295, -1)]

theorem rawRowCheck7159 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form4 = rawRow7159 := by decide +kernel

def row7159 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

theorem rowCheck7159 : row7159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7159 := by decide +kernel

theorem rowEval7159 (x : Key → ℝ) : Integer.Sparse.eval row7159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7159, Integer.Sparse.eval_collectBalanced, rawRowCheck7159]

def rawRow7160 : Integer.Sparse Key := [(key2295, -4), (key2338, 2), (key2337, 2), (key2297, 2), (key2295, 2), (key2338, -4), (key2273, 2), (key2326, -1), (key2325, -1), (key2004, 2), (key2338, -1), (key2325, -1), (key2005, -1), (key2004, -1), (key2297, -1), (key2273, -1), (key2338, 2), (key2326, 2), (key2273, -1), (key2271, -1), (key2325, 2), (key2004, -1), (key2002, -1), (key2295, 2), (key2271, 2), (key2337, -1), (key2325, -1), (key2004, 2), (key2295, -1), (key2273, -1)]

theorem rawRowCheck7160 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form4 = rawRow7160 := by decide +kernel

def row7160 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

theorem rowCheck7160 : row7160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7160 := by decide +kernel

theorem rowEval7160 (x : Key → ℝ) : Integer.Sparse.eval row7160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck7160, Integer.Sparse.eval_collectBalanced, rawRowCheck7160]

def rawRow7161 : Integer.Sparse Key := [(key2337, -4), (key2295, 2), (key2338, 2), (key2295, 2), (key2338, 2), (key2297, -4), (key2325, 2), (key2273, -1), (key2326, -1), (key2325, 2), (key2004, -1), (key2338, -1), (key2273, -1), (key2326, -1), (key2004, -1), (key2338, -1), (key2005, 2), (key2297, 2), (key2271, -1), (key2325, -1), (key2273, 2), (key2271, -1), (key2325, -1), (key2002, 2), (key2337, 2), (key2004, -1), (key2295, -1), (key2273, 2), (key2004, -1), (key2295, -1)]

theorem rawRowCheck7161 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form4 = rawRow7161 := by decide +kernel

def row7161 : Integer.Sparse Key := [(key2002, 2), (key2004, -4), (key2005, 2), (key2271, -2), (key2273, 2), (key2295, 2), (key2297, -2), (key2325, 2), (key2326, -2), (key2337, -2), (key2338, 2)]

theorem rowCheck7161 : row7161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7161 := by decide +kernel

theorem rowEval7161 (x : Key → ℝ) : Integer.Sparse.eval row7161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7161, Integer.Sparse.eval_collectBalanced, rawRowCheck7161]

def rawRow7162 : Integer.Sparse Key := [(key2337, -4), (key2338, 2), (key2295, 2), (key2338, 2), (key2295, 2), (key2297, -4), (key2325, 2), (key2326, -1), (key2273, -1), (key2325, 2), (key2338, -1), (key2004, -1), (key2326, -1), (key2273, -1), (key2338, -1), (key2004, -1), (key2297, 2), (key2005, 2), (key2325, -1), (key2271, -1), (key2273, 2), (key2325, -1), (key2271, -1), (key2337, 2), (key2002, 2), (key2295, -1), (key2004, -1), (key2273, 2), (key2295, -1), (key2004, -1)]

theorem rawRowCheck7162 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form4 = rawRow7162 := by decide +kernel

def row7162 : Integer.Sparse Key := [(key2002, 2), (key2004, -4), (key2005, 2), (key2271, -2), (key2273, 2), (key2295, 2), (key2297, -2), (key2325, 2), (key2326, -2), (key2337, -2), (key2338, 2)]

theorem rowCheck7162 : row7162 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7162 := by decide +kernel

theorem rowEval7162 (x : Key → ℝ) : Integer.Sparse.eval row7162 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7162, Integer.Sparse.eval_collectBalanced, rawRowCheck7162]

def rawRow7163 : Integer.Sparse Key := [(key2338, -4), (key2295, 2), (key2337, 2), (key2297, 2), (key2338, 2), (key2295, -4), (key2326, 2), (key2273, -1), (key2325, -1), (key2338, 2), (key2004, -1), (key2325, -1), (key2297, -1), (key2338, -1), (key2005, -1), (key2326, -1), (key2004, 2), (key2273, 2), (key2273, -1), (key2325, -1), (key2271, 2), (key2295, -1), (key2337, -1), (key2004, 2), (key2325, 2), (key2002, -1), (key2271, -1), (key2295, 2), (key2004, -1), (key2273, -1)]

theorem rawRowCheck7163 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form4 = rawRow7163 := by decide +kernel

def row7163 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

theorem rowCheck7163 : row7163 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7163 := by decide +kernel

theorem rowEval7163 (x : Key → ℝ) : Integer.Sparse.eval row7163 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck7163, Integer.Sparse.eval_collectBalanced, rawRowCheck7163]

def rawRow7164 : Integer.Sparse Key := [(key2338, -4), (key2337, 2), (key2295, 2), (key2338, 2), (key2297, 2), (key2295, -4), (key2326, 2), (key2325, -1), (key2273, -1), (key2338, 2), (key2325, -1), (key2004, -1), (key2338, -1), (key2297, -1), (key2326, -1), (key2005, -1), (key2273, 2), (key2004, 2), (key2325, -1), (key2273, -1), (key2271, 2), (key2337, -1), (key2295, -1), (key2325, 2), (key2004, 2), (key2271, -1), (key2002, -1), (key2295, 2), (key2273, -1), (key2004, -1)]

theorem rawRowCheck7164 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form4 = rawRow7164 := by decide +kernel

def row7164 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

theorem rowCheck7164 : row7164 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7164 := by decide +kernel

theorem rowEval7164 (x : Key → ℝ) : Integer.Sparse.eval row7164 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7164, Integer.Sparse.eval_collectBalanced, rawRowCheck7164]

def rawRow7165 : Integer.Sparse Key := [(key2297, -4), (key2338, 2), (key2338, 2), (key2295, 2), (key2295, 2), (key2337, -4), (key2297, 2), (key2338, -1), (key2338, -1), (key2005, 2), (key2326, -1), (key2326, -1), (key2004, -1), (key2004, -1), (key2273, -1), (key2273, -1), (key2325, 2), (key2325, 2), (key2295, -1), (key2295, -1), (key2337, 2), (key2004, -1), (key2004, -1), (key2273, 2), (key2273, 2), (key2325, -1), (key2325, -1), (key2002, 2), (key2271, -1), (key2271, -1)]

theorem rawRowCheck7165 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form4 = rawRow7165 := by decide +kernel

def row7165 : Integer.Sparse Key := [(key2002, 2), (key2004, -4), (key2005, 2), (key2271, -2), (key2273, 2), (key2295, 2), (key2297, -2), (key2325, 2), (key2326, -2), (key2337, -2), (key2338, 2)]

theorem rowCheck7165 : row7165 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7165 := by decide +kernel

theorem rowEval7165 (x : Key → ℝ) : Integer.Sparse.eval row7165 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck7165, Integer.Sparse.eval_collectBalanced, rawRowCheck7165]

def rawRow7166 : Integer.Sparse Key := [(key2338, -4), (key2297, 2), (key2338, 2), (key2295, 2), (key2337, 2), (key2295, -4), (key2338, 2), (key2297, -1), (key2338, -1), (key2326, 2), (key2005, -1), (key2326, -1), (key2273, -1), (key2325, -1), (key2004, -1), (key2325, -1), (key2004, 2), (key2273, 2), (key2295, -1), (key2337, -1), (key2295, 2), (key2273, -1), (key2325, -1), (key2004, 2), (key2325, 2), (key2004, -1), (key2273, -1), (key2271, 2), (key2002, -1), (key2271, -1)]

theorem rawRowCheck7166 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form4 = rawRow7166 := by decide +kernel

def row7166 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

theorem rowCheck7166 : row7166 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7166 := by decide +kernel

theorem rowEval7166 (x : Key → ℝ) : Integer.Sparse.eval row7166 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck7166, Integer.Sparse.eval_collectBalanced, rawRowCheck7166]

def rawRow7167 : Integer.Sparse Key := [(key2338, -4), (key2338, 2), (key2297, 2), (key2337, 2), (key2295, 2), (key2295, -4), (key2338, 2), (key2338, -1), (key2297, -1), (key2326, 2), (key2326, -1), (key2005, -1), (key2325, -1), (key2273, -1), (key2325, -1), (key2004, -1), (key2273, 2), (key2004, 2), (key2337, -1), (key2295, -1), (key2295, 2), (key2325, -1), (key2273, -1), (key2325, 2), (key2004, 2), (key2273, -1), (key2004, -1), (key2271, 2), (key2271, -1), (key2002, -1)]

theorem rawRowCheck7167 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form4 = rawRow7167 := by decide +kernel

def row7167 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

theorem rowCheck7167 : row7167 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7167 := by decide +kernel

theorem rowEval7167 (x : Key → ℝ) : Integer.Sparse.eval row7167 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7167, Integer.Sparse.eval_collectBalanced, rawRowCheck7167]

end MUB6.Certificate.GramRows

end OAI
