import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block6
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block16
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block17
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow17792 : Integer.Sparse Key := [(key2153, -1), (key2150, -1), (key2167, -1), (key2150, -1), (key2167, -1), (key2153, -1), (key2177, 2), (key2188, 2), (key2177, 2), (key2153, -1), (key2150, -1), (key2167, -1), (key2150, -1), (key2167, -1), (key2153, -1), (key2247, 2), (key2243, 2), (key2254, 2), (key2243, 2), (key2254, 2), (key2247, 2), (key2280, -1), (key2277, -1), (key2288, -1), (key2277, -1), (key2288, -1), (key2280, -1), (key2177, 2), (key2188, 2), (key2177, 2), (key2280, -1), (key2277, -1), (key2288, -1), (key2277, -1), (key2288, -1), (key2280, -1)]

theorem rawRowCheck17792 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form10 = rawRow17792 := by decide +kernel

def row17792 : Integer.Sparse Key := [(key2150, -4), (key2153, -4), (key2167, -4), (key2177, 8), (key2188, 4), (key2243, 4), (key2247, 4), (key2254, 4), (key2277, -4), (key2280, -4), (key2288, -4)]

theorem rowCheck17792 : row17792 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17792 := by decide +kernel

theorem rowEval17792 (x : Key → ℝ) : Integer.Sparse.eval row17792 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck17792, Integer.Sparse.eval_collectBalanced, rawRowCheck17792]

def rawRow17793 : Integer.Sparse Key := [(key2167, -1), (key2167, -1), (key2153, -1), (key2153, -1), (key2150, -1), (key2150, -1), (key2188, 2), (key2177, 2), (key2177, 2), (key2167, -1), (key2167, -1), (key2153, -1), (key2153, -1), (key2150, -1), (key2150, -1), (key2254, 2), (key2254, 2), (key2247, 2), (key2247, 2), (key2243, 2), (key2243, 2), (key2288, -1), (key2288, -1), (key2280, -1), (key2280, -1), (key2277, -1), (key2277, -1), (key2188, 2), (key2177, 2), (key2177, 2), (key2288, -1), (key2288, -1), (key2280, -1), (key2280, -1), (key2277, -1), (key2277, -1)]

theorem rawRowCheck17793 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form10 = rawRow17793 := by decide +kernel

def row17793 : Integer.Sparse Key := [(key2150, -4), (key2153, -4), (key2167, -4), (key2177, 8), (key2188, 4), (key2243, 4), (key2247, 4), (key2254, 4), (key2277, -4), (key2280, -4), (key2288, -4)]

theorem rowCheck17793 : row17793 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17793 := by decide +kernel

theorem rowEval17793 (x : Key → ℝ) : Integer.Sparse.eval row17793 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck17793, Integer.Sparse.eval_collectBalanced, rawRowCheck17793]

def rawRow17794 : Integer.Sparse Key := [(key2031, -1), (key2034, -1), (key2150, -1), (key2167, -1), (key2177, -1), (key2188, -1), (key2034, 2), (key2153, 2), (key2167, 2), (key2061, -1), (key2064, -1), (key2243, -1), (key2254, -1), (key2277, -1), (key2288, -1), (key2061, 2), (key2070, 2), (key2150, 2), (key2167, 2), (key2280, 2), (key2288, 2), (key2064, -1), (key2070, -1), (key2153, -1), (key2167, -1), (key2247, -1), (key2254, -1), (key2080, 2), (key2277, 2), (key2288, 2), (key2080, -1), (key2086, -1), (key2177, -1), (key2188, -1), (key2280, -1), (key2288, -1)]

theorem rawRowCheck17794 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form10 = rawRow17794 := by decide +kernel

def row17794 : Integer.Sparse Key := [(key2031, -1), (key2034, 1), (key2061, 1), (key2064, -2), (key2070, 1), (key2080, 1), (key2086, -1), (key2150, 1), (key2153, 1), (key2167, 2), (key2177, -2), (key2188, -2), (key2243, -1), (key2247, -1), (key2254, -2), (key2277, 1), (key2280, 1), (key2288, 2)]

theorem rowCheck17794 : row17794 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17794 := by decide +kernel

theorem rowEval17794 (x : Key → ℝ) : Integer.Sparse.eval row17794 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck17794, Integer.Sparse.eval_collectBalanced, rawRowCheck17794]

def rawRow17795 : Integer.Sparse Key := [(key2034, -1), (key2031, -1), (key2167, -1), (key2150, -1), (key2188, -1), (key2177, -1), (key2034, 2), (key2167, 2), (key2153, 2), (key2064, -1), (key2061, -1), (key2254, -1), (key2243, -1), (key2288, -1), (key2277, -1), (key2070, 2), (key2061, 2), (key2167, 2), (key2150, 2), (key2288, 2), (key2280, 2), (key2070, -1), (key2064, -1), (key2167, -1), (key2153, -1), (key2254, -1), (key2247, -1), (key2080, 2), (key2288, 2), (key2277, 2), (key2086, -1), (key2080, -1), (key2188, -1), (key2177, -1), (key2288, -1), (key2280, -1)]

theorem rawRowCheck17795 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form10 = rawRow17795 := by decide +kernel

def row17795 : Integer.Sparse Key := [(key2031, -1), (key2034, 1), (key2061, 1), (key2064, -2), (key2070, 1), (key2080, 1), (key2086, -1), (key2150, 1), (key2153, 1), (key2167, 2), (key2177, -2), (key2188, -2), (key2243, -1), (key2247, -1), (key2254, -2), (key2277, 1), (key2280, 1), (key2288, 2)]

theorem rowCheck17795 : row17795 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17795 := by decide +kernel

theorem rowEval17795 (x : Key → ℝ) : Integer.Sparse.eval row17795 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck17795, Integer.Sparse.eval_collectBalanced, rawRowCheck17795]

def rawRow17796 : Integer.Sparse Key := [(key2150, -1), (key2177, -1), (key2031, -1), (key2188, -1), (key2034, -1), (key2167, -1), (key2153, 2), (key2034, 2), (key2167, 2), (key2243, -1), (key2277, -1), (key2061, -1), (key2288, -1), (key2064, -1), (key2254, -1), (key2150, 2), (key2280, 2), (key2061, 2), (key2288, 2), (key2070, 2), (key2167, 2), (key2153, -1), (key2247, -1), (key2064, -1), (key2254, -1), (key2070, -1), (key2167, -1), (key2277, 2), (key2080, 2), (key2288, 2), (key2177, -1), (key2280, -1), (key2080, -1), (key2288, -1), (key2086, -1), (key2188, -1)]

theorem rawRowCheck17796 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form10 = rawRow17796 := by decide +kernel

def row17796 : Integer.Sparse Key := [(key2031, -1), (key2034, 1), (key2061, 1), (key2064, -2), (key2070, 1), (key2080, 1), (key2086, -1), (key2150, 1), (key2153, 1), (key2167, 2), (key2177, -2), (key2188, -2), (key2243, -1), (key2247, -1), (key2254, -2), (key2277, 1), (key2280, 1), (key2288, 2)]

theorem rowCheck17796 : row17796 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17796 := by decide +kernel

theorem rowEval17796 (x : Key → ℝ) : Integer.Sparse.eval row17796 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck17796, Integer.Sparse.eval_collectBalanced, rawRowCheck17796]

def rawRow17797 : Integer.Sparse Key := [(key2177, -1), (key2150, -1), (key2188, -1), (key2031, -1), (key2167, -1), (key2034, -1), (key2153, 2), (key2167, 2), (key2034, 2), (key2277, -1), (key2243, -1), (key2288, -1), (key2061, -1), (key2254, -1), (key2064, -1), (key2280, 2), (key2150, 2), (key2288, 2), (key2061, 2), (key2167, 2), (key2070, 2), (key2247, -1), (key2153, -1), (key2254, -1), (key2064, -1), (key2167, -1), (key2070, -1), (key2277, 2), (key2288, 2), (key2080, 2), (key2280, -1), (key2177, -1), (key2288, -1), (key2080, -1), (key2188, -1), (key2086, -1)]

theorem rawRowCheck17797 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form10 = rawRow17797 := by decide +kernel

def row17797 : Integer.Sparse Key := [(key2031, -1), (key2034, 1), (key2061, 1), (key2064, -2), (key2070, 1), (key2080, 1), (key2086, -1), (key2150, 1), (key2153, 1), (key2167, 2), (key2177, -2), (key2188, -2), (key2243, -1), (key2247, -1), (key2254, -2), (key2277, 1), (key2280, 1), (key2288, 2)]

theorem rowCheck17797 : row17797 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17797 := by decide +kernel

theorem rowEval17797 (x : Key → ℝ) : Integer.Sparse.eval row17797 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck17797, Integer.Sparse.eval_collectBalanced, rawRowCheck17797]

def rawRow17798 : Integer.Sparse Key := [(key2167, -1), (key2188, -1), (key2034, -1), (key2177, -1), (key2031, -1), (key2150, -1), (key2167, 2), (key2034, 2), (key2153, 2), (key2254, -1), (key2288, -1), (key2064, -1), (key2277, -1), (key2061, -1), (key2243, -1), (key2167, 2), (key2288, 2), (key2070, 2), (key2280, 2), (key2061, 2), (key2150, 2), (key2167, -1), (key2254, -1), (key2070, -1), (key2247, -1), (key2064, -1), (key2153, -1), (key2288, 2), (key2080, 2), (key2277, 2), (key2188, -1), (key2288, -1), (key2086, -1), (key2280, -1), (key2080, -1), (key2177, -1)]

theorem rawRowCheck17798 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form10 = rawRow17798 := by decide +kernel

def row17798 : Integer.Sparse Key := [(key2031, -1), (key2034, 1), (key2061, 1), (key2064, -2), (key2070, 1), (key2080, 1), (key2086, -1), (key2150, 1), (key2153, 1), (key2167, 2), (key2177, -2), (key2188, -2), (key2243, -1), (key2247, -1), (key2254, -2), (key2277, 1), (key2280, 1), (key2288, 2)]

theorem rowCheck17798 : row17798 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17798 := by decide +kernel

theorem rowEval17798 (x : Key → ℝ) : Integer.Sparse.eval row17798 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck17798, Integer.Sparse.eval_collectBalanced, rawRowCheck17798]

def rawRow17799 : Integer.Sparse Key := [(key2188, -1), (key2167, -1), (key2177, -1), (key2034, -1), (key2150, -1), (key2031, -1), (key2167, 2), (key2153, 2), (key2034, 2), (key2288, -1), (key2254, -1), (key2277, -1), (key2064, -1), (key2243, -1), (key2061, -1), (key2288, 2), (key2167, 2), (key2280, 2), (key2070, 2), (key2150, 2), (key2061, 2), (key2254, -1), (key2167, -1), (key2247, -1), (key2070, -1), (key2153, -1), (key2064, -1), (key2288, 2), (key2277, 2), (key2080, 2), (key2288, -1), (key2188, -1), (key2280, -1), (key2086, -1), (key2177, -1), (key2080, -1)]

theorem rawRowCheck17799 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form10 = rawRow17799 := by decide +kernel

def row17799 : Integer.Sparse Key := [(key2031, -1), (key2034, 1), (key2061, 1), (key2064, -2), (key2070, 1), (key2080, 1), (key2086, -1), (key2150, 1), (key2153, 1), (key2167, 2), (key2177, -2), (key2188, -2), (key2243, -1), (key2247, -1), (key2254, -2), (key2277, 1), (key2280, 1), (key2288, 2)]

theorem rowCheck17799 : row17799 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17799 := by decide +kernel

theorem rowEval17799 (x : Key → ℝ) : Integer.Sparse.eval row17799 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck17799, Integer.Sparse.eval_collectBalanced, rawRowCheck17799]

def rawRow17800 : Integer.Sparse Key := [(key2061, -1), (key2064, -1), (key2243, -1), (key2254, -1), (key2277, -1), (key2288, -1), (key2080, 2), (key2277, 2), (key2288, 2), (key2031, -1), (key2034, -1), (key2150, -1), (key2167, -1), (key2177, -1), (key2188, -1), (key2061, 2), (key2070, 2), (key2150, 2), (key2167, 2), (key2280, 2), (key2288, 2), (key2080, -1), (key2086, -1), (key2177, -1), (key2188, -1), (key2280, -1), (key2288, -1), (key2034, 2), (key2153, 2), (key2167, 2), (key2064, -1), (key2070, -1), (key2153, -1), (key2167, -1), (key2247, -1), (key2254, -1)]

theorem rawRowCheck17800 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form10 = rawRow17800 := by decide +kernel

def row17800 : Integer.Sparse Key := [(key2031, -1), (key2034, 1), (key2061, 1), (key2064, -2), (key2070, 1), (key2080, 1), (key2086, -1), (key2150, 1), (key2153, 1), (key2167, 2), (key2177, -2), (key2188, -2), (key2243, -1), (key2247, -1), (key2254, -2), (key2277, 1), (key2280, 1), (key2288, 2)]

theorem rowCheck17800 : row17800 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17800 := by decide +kernel

theorem rowEval17800 (x : Key → ℝ) : Integer.Sparse.eval row17800 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck17800, Integer.Sparse.eval_collectBalanced, rawRowCheck17800]

def rawRow17801 : Integer.Sparse Key := [(key2064, -1), (key2061, -1), (key2254, -1), (key2243, -1), (key2288, -1), (key2277, -1), (key2080, 2), (key2288, 2), (key2277, 2), (key2034, -1), (key2031, -1), (key2167, -1), (key2150, -1), (key2188, -1), (key2177, -1), (key2070, 2), (key2061, 2), (key2167, 2), (key2150, 2), (key2288, 2), (key2280, 2), (key2086, -1), (key2080, -1), (key2188, -1), (key2177, -1), (key2288, -1), (key2280, -1), (key2034, 2), (key2167, 2), (key2153, 2), (key2070, -1), (key2064, -1), (key2167, -1), (key2153, -1), (key2254, -1), (key2247, -1)]

theorem rawRowCheck17801 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form10 = rawRow17801 := by decide +kernel

def row17801 : Integer.Sparse Key := [(key2031, -1), (key2034, 1), (key2061, 1), (key2064, -2), (key2070, 1), (key2080, 1), (key2086, -1), (key2150, 1), (key2153, 1), (key2167, 2), (key2177, -2), (key2188, -2), (key2243, -1), (key2247, -1), (key2254, -2), (key2277, 1), (key2280, 1), (key2288, 2)]

theorem rowCheck17801 : row17801 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17801 := by decide +kernel

theorem rowEval17801 (x : Key → ℝ) : Integer.Sparse.eval row17801 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck17801, Integer.Sparse.eval_collectBalanced, rawRowCheck17801]

def rawRow17802 : Integer.Sparse Key := [(key2243, -1), (key2277, -1), (key2061, -1), (key2288, -1), (key2064, -1), (key2254, -1), (key2277, 2), (key2080, 2), (key2288, 2), (key2150, -1), (key2177, -1), (key2031, -1), (key2188, -1), (key2034, -1), (key2167, -1), (key2150, 2), (key2280, 2), (key2061, 2), (key2288, 2), (key2070, 2), (key2167, 2), (key2177, -1), (key2280, -1), (key2080, -1), (key2288, -1), (key2086, -1), (key2188, -1), (key2153, 2), (key2034, 2), (key2167, 2), (key2153, -1), (key2247, -1), (key2064, -1), (key2254, -1), (key2070, -1), (key2167, -1)]

theorem rawRowCheck17802 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form10 = rawRow17802 := by decide +kernel

def row17802 : Integer.Sparse Key := [(key2031, -1), (key2034, 1), (key2061, 1), (key2064, -2), (key2070, 1), (key2080, 1), (key2086, -1), (key2150, 1), (key2153, 1), (key2167, 2), (key2177, -2), (key2188, -2), (key2243, -1), (key2247, -1), (key2254, -2), (key2277, 1), (key2280, 1), (key2288, 2)]

theorem rowCheck17802 : row17802 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17802 := by decide +kernel

theorem rowEval17802 (x : Key → ℝ) : Integer.Sparse.eval row17802 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck17802, Integer.Sparse.eval_collectBalanced, rawRowCheck17802]

def rawRow17803 : Integer.Sparse Key := [(key2277, -1), (key2243, -1), (key2288, -1), (key2061, -1), (key2254, -1), (key2064, -1), (key2277, 2), (key2288, 2), (key2080, 2), (key2177, -1), (key2150, -1), (key2188, -1), (key2031, -1), (key2167, -1), (key2034, -1), (key2280, 2), (key2150, 2), (key2288, 2), (key2061, 2), (key2167, 2), (key2070, 2), (key2280, -1), (key2177, -1), (key2288, -1), (key2080, -1), (key2188, -1), (key2086, -1), (key2153, 2), (key2167, 2), (key2034, 2), (key2247, -1), (key2153, -1), (key2254, -1), (key2064, -1), (key2167, -1), (key2070, -1)]

theorem rawRowCheck17803 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form10 = rawRow17803 := by decide +kernel

def row17803 : Integer.Sparse Key := [(key2031, -1), (key2034, 1), (key2061, 1), (key2064, -2), (key2070, 1), (key2080, 1), (key2086, -1), (key2150, 1), (key2153, 1), (key2167, 2), (key2177, -2), (key2188, -2), (key2243, -1), (key2247, -1), (key2254, -2), (key2277, 1), (key2280, 1), (key2288, 2)]

theorem rowCheck17803 : row17803 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17803 := by decide +kernel

theorem rowEval17803 (x : Key → ℝ) : Integer.Sparse.eval row17803 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck17803, Integer.Sparse.eval_collectBalanced, rawRowCheck17803]

def rawRow17804 : Integer.Sparse Key := [(key2254, -1), (key2288, -1), (key2064, -1), (key2277, -1), (key2061, -1), (key2243, -1), (key2288, 2), (key2080, 2), (key2277, 2), (key2167, -1), (key2188, -1), (key2034, -1), (key2177, -1), (key2031, -1), (key2150, -1), (key2167, 2), (key2288, 2), (key2070, 2), (key2280, 2), (key2061, 2), (key2150, 2), (key2188, -1), (key2288, -1), (key2086, -1), (key2280, -1), (key2080, -1), (key2177, -1), (key2167, 2), (key2034, 2), (key2153, 2), (key2167, -1), (key2254, -1), (key2070, -1), (key2247, -1), (key2064, -1), (key2153, -1)]

theorem rawRowCheck17804 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form10 = rawRow17804 := by decide +kernel

def row17804 : Integer.Sparse Key := [(key2031, -1), (key2034, 1), (key2061, 1), (key2064, -2), (key2070, 1), (key2080, 1), (key2086, -1), (key2150, 1), (key2153, 1), (key2167, 2), (key2177, -2), (key2188, -2), (key2243, -1), (key2247, -1), (key2254, -2), (key2277, 1), (key2280, 1), (key2288, 2)]

theorem rowCheck17804 : row17804 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17804 := by decide +kernel

theorem rowEval17804 (x : Key → ℝ) : Integer.Sparse.eval row17804 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck17804, Integer.Sparse.eval_collectBalanced, rawRowCheck17804]

def rawRow17805 : Integer.Sparse Key := [(key2288, -1), (key2254, -1), (key2277, -1), (key2064, -1), (key2243, -1), (key2061, -1), (key2288, 2), (key2277, 2), (key2080, 2), (key2188, -1), (key2167, -1), (key2177, -1), (key2034, -1), (key2150, -1), (key2031, -1), (key2288, 2), (key2167, 2), (key2280, 2), (key2070, 2), (key2150, 2), (key2061, 2), (key2288, -1), (key2188, -1), (key2280, -1), (key2086, -1), (key2177, -1), (key2080, -1), (key2167, 2), (key2153, 2), (key2034, 2), (key2254, -1), (key2167, -1), (key2247, -1), (key2070, -1), (key2153, -1), (key2064, -1)]

theorem rawRowCheck17805 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form10 = rawRow17805 := by decide +kernel

def row17805 : Integer.Sparse Key := [(key2031, -1), (key2034, 1), (key2061, 1), (key2064, -2), (key2070, 1), (key2080, 1), (key2086, -1), (key2150, 1), (key2153, 1), (key2167, 2), (key2177, -2), (key2188, -2), (key2243, -1), (key2247, -1), (key2254, -2), (key2277, 1), (key2280, 1), (key2288, 2)]

theorem rowCheck17805 : row17805 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17805 := by decide +kernel

theorem rowEval17805 (x : Key → ℝ) : Integer.Sparse.eval row17805 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck17805, Integer.Sparse.eval_collectBalanced, rawRowCheck17805]

def rawRow17806 : Integer.Sparse Key := [(key2061, -1), (key2080, -1), (key2061, -1), (key2288, -1), (key2080, -1), (key2288, -1), (key2064, 2), (key2064, 2), (key2254, 2), (key2061, -1), (key2080, -1), (key2061, -1), (key2288, -1), (key2080, -1), (key2288, -1), (key2031, 2), (key2086, 2), (key2031, 2), (key2188, 2), (key2086, 2), (key2188, 2), (key2034, -1), (key2070, -1), (key2034, -1), (key2167, -1), (key2070, -1), (key2167, -1), (key2064, 2), (key2064, 2), (key2254, 2), (key2034, -1), (key2070, -1), (key2034, -1), (key2167, -1), (key2070, -1), (key2167, -1)]

theorem rawRowCheck17806 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form10 = rawRow17806 := by decide +kernel

def row17806 : Integer.Sparse Key := [(key2031, 4), (key2034, -4), (key2061, -4), (key2064, 8), (key2070, -4), (key2080, -4), (key2086, 4), (key2167, -4), (key2188, 4), (key2254, 4), (key2288, -4)]

theorem rowCheck17806 : row17806 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17806 := by decide +kernel

theorem rowEval17806 (x : Key → ℝ) : Integer.Sparse.eval row17806 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck17806, Integer.Sparse.eval_collectBalanced, rawRowCheck17806]

def rawRow17807 : Integer.Sparse Key := [(key2080, -1), (key2061, -1), (key2288, -1), (key2061, -1), (key2288, -1), (key2080, -1), (key2064, 2), (key2254, 2), (key2064, 2), (key2080, -1), (key2061, -1), (key2288, -1), (key2061, -1), (key2288, -1), (key2080, -1), (key2086, 2), (key2031, 2), (key2188, 2), (key2031, 2), (key2188, 2), (key2086, 2), (key2070, -1), (key2034, -1), (key2167, -1), (key2034, -1), (key2167, -1), (key2070, -1), (key2064, 2), (key2254, 2), (key2064, 2), (key2070, -1), (key2034, -1), (key2167, -1), (key2034, -1), (key2167, -1), (key2070, -1)]

theorem rawRowCheck17807 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form10 = rawRow17807 := by decide +kernel

def row17807 : Integer.Sparse Key := [(key2031, 4), (key2034, -4), (key2061, -4), (key2064, 8), (key2070, -4), (key2080, -4), (key2086, 4), (key2167, -4), (key2188, 4), (key2254, 4), (key2288, -4)]

theorem rowCheck17807 : row17807 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17807 := by decide +kernel

theorem rowEval17807 (x : Key → ℝ) : Integer.Sparse.eval row17807 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck17807, Integer.Sparse.eval_collectBalanced, rawRowCheck17807]

def rawRow17808 : Integer.Sparse Key := [(key2288, -1), (key2288, -1), (key2080, -1), (key2080, -1), (key2061, -1), (key2061, -1), (key2254, 2), (key2064, 2), (key2064, 2), (key2288, -1), (key2288, -1), (key2080, -1), (key2080, -1), (key2061, -1), (key2061, -1), (key2188, 2), (key2188, 2), (key2086, 2), (key2086, 2), (key2031, 2), (key2031, 2), (key2167, -1), (key2167, -1), (key2070, -1), (key2070, -1), (key2034, -1), (key2034, -1), (key2254, 2), (key2064, 2), (key2064, 2), (key2167, -1), (key2167, -1), (key2070, -1), (key2070, -1), (key2034, -1), (key2034, -1)]

theorem rawRowCheck17808 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form10 = rawRow17808 := by decide +kernel

def row17808 : Integer.Sparse Key := [(key2031, 4), (key2034, -4), (key2061, -4), (key2064, 8), (key2070, -4), (key2080, -4), (key2086, 4), (key2167, -4), (key2188, 4), (key2254, 4), (key2288, -4)]

theorem rowCheck17808 : row17808 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17808 := by decide +kernel

theorem rowEval17808 (x : Key → ℝ) : Integer.Sparse.eval row17808 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck17808, Integer.Sparse.eval_collectBalanced, rawRowCheck17808]

def rawRow17809 : Integer.Sparse Key := [(key361, -2), (key364, -2), (key364, -2), (key368, 6), (key361, -2), (key364, -2), (key364, -2), (key530, 2), (key534, 2), (key530, 2), (key634, 2), (key534, 2), (key634, 2), (key540, -2), (key540, -2), (key639, -2), (key368, 6), (key540, -2), (key540, -2), (key639, -2)]

theorem rawRowCheck17809 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form11 = rawRow17809 := by decide +kernel

def row17809 : Integer.Sparse Key := [(key361, -4), (key364, -8), (key368, 12), (key530, 4), (key534, 4), (key540, -8), (key634, 4), (key639, -4)]

theorem rowCheck17809 : row17809 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17809 := by decide +kernel

theorem rowEval17809 (x : Key → ℝ) : Integer.Sparse.eval row17809 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17809, Integer.Sparse.eval_collectBalanced, rawRowCheck17809]

def rawRow17810 : Integer.Sparse Key := [(key364, -2), (key361, -2), (key364, -2), (key368, 6), (key364, -2), (key361, -2), (key364, -2), (key534, 2), (key530, 2), (key634, 2), (key530, 2), (key634, 2), (key534, 2), (key540, -2), (key639, -2), (key540, -2), (key368, 6), (key540, -2), (key639, -2), (key540, -2)]

theorem rawRowCheck17810 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form11 = rawRow17810 := by decide +kernel

def row17810 : Integer.Sparse Key := [(key361, -4), (key364, -8), (key368, 12), (key530, 4), (key534, 4), (key540, -8), (key634, 4), (key639, -4)]

theorem rowCheck17810 : row17810 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17810 := by decide +kernel

theorem rowEval17810 (x : Key → ℝ) : Integer.Sparse.eval row17810 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck17810, Integer.Sparse.eval_collectBalanced, rawRowCheck17810]

def rawRow17811 : Integer.Sparse Key := [(key364, -2), (key364, -2), (key361, -2), (key368, 6), (key364, -2), (key364, -2), (key361, -2), (key634, 2), (key634, 2), (key534, 2), (key534, 2), (key530, 2), (key530, 2), (key639, -2), (key540, -2), (key540, -2), (key368, 6), (key639, -2), (key540, -2), (key540, -2)]

theorem rawRowCheck17811 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form11 = rawRow17811 := by decide +kernel

def row17811 : Integer.Sparse Key := [(key361, -4), (key364, -8), (key368, 12), (key530, 4), (key534, 4), (key540, -8), (key634, 4), (key639, -4)]

theorem rowCheck17811 : row17811 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17811 := by decide +kernel

theorem rowEval17811 (x : Key → ℝ) : Integer.Sparse.eval row17811 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck17811, Integer.Sparse.eval_collectBalanced, rawRowCheck17811]

def rawRow17812 : Integer.Sparse Key := [(key361, -2), (key364, -2), (key368, -2), (key364, 6), (key530, -2), (key534, -2), (key540, -2), (key361, 2), (key364, 2), (key530, 2), (key634, 2), (key540, 2), (key639, 2), (key364, -2), (key534, -2), (key634, -2), (key540, 6), (key368, -2), (key540, -2), (key639, -2)]

theorem rawRowCheck17812 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form11 = rawRow17812 := by decide +kernel

def row17812 : Integer.Sparse Key := [(key364, 4), (key368, -4), (key534, -4), (key540, 4)]

theorem rowCheck17812 : row17812 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17812 := by decide +kernel

theorem rowEval17812 (x : Key → ℝ) : Integer.Sparse.eval row17812 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17812, Integer.Sparse.eval_collectBalanced, rawRowCheck17812]

def rawRow17813 : Integer.Sparse Key := [(key364, -2), (key361, -2), (key368, -2), (key364, 6), (key534, -2), (key530, -2), (key540, -2), (key364, 2), (key361, 2), (key634, 2), (key530, 2), (key639, 2), (key540, 2), (key364, -2), (key634, -2), (key534, -2), (key540, 6), (key368, -2), (key639, -2), (key540, -2)]

theorem rawRowCheck17813 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form11 = rawRow17813 := by decide +kernel

def row17813 : Integer.Sparse Key := [(key364, 4), (key368, -4), (key534, -4), (key540, 4)]

theorem rowCheck17813 : row17813 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17813 := by decide +kernel

theorem rowEval17813 (x : Key → ℝ) : Integer.Sparse.eval row17813 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck17813, Integer.Sparse.eval_collectBalanced, rawRowCheck17813]

def rawRow17814 : Integer.Sparse Key := [(key361, -2), (key368, -2), (key364, -2), (key364, 6), (key530, -2), (key540, -2), (key534, -2), (key530, 2), (key540, 2), (key361, 2), (key639, 2), (key364, 2), (key634, 2), (key534, -2), (key364, -2), (key634, -2), (key540, 6), (key540, -2), (key368, -2), (key639, -2)]

theorem rawRowCheck17814 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form11 = rawRow17814 := by decide +kernel

def row17814 : Integer.Sparse Key := [(key364, 4), (key368, -4), (key534, -4), (key540, 4)]

theorem rowCheck17814 : row17814 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17814 := by decide +kernel

theorem rowEval17814 (x : Key → ℝ) : Integer.Sparse.eval row17814 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17814, Integer.Sparse.eval_collectBalanced, rawRowCheck17814]

def rawRow17815 : Integer.Sparse Key := [(key368, -2), (key361, -2), (key364, -2), (key364, 6), (key540, -2), (key530, -2), (key534, -2), (key540, 2), (key530, 2), (key639, 2), (key361, 2), (key634, 2), (key364, 2), (key534, -2), (key634, -2), (key364, -2), (key540, 6), (key540, -2), (key639, -2), (key368, -2)]

theorem rawRowCheck17815 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form11 = rawRow17815 := by decide +kernel

def row17815 : Integer.Sparse Key := [(key364, 4), (key368, -4), (key534, -4), (key540, 4)]

theorem rowCheck17815 : row17815 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17815 := by decide +kernel

theorem rowEval17815 (x : Key → ℝ) : Integer.Sparse.eval row17815 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17815, Integer.Sparse.eval_collectBalanced, rawRowCheck17815]

def rawRow17816 : Integer.Sparse Key := [(key364, -2), (key368, -2), (key361, -2), (key364, 6), (key534, -2), (key540, -2), (key530, -2), (key634, 2), (key639, 2), (key364, 2), (key540, 2), (key361, 2), (key530, 2), (key634, -2), (key364, -2), (key534, -2), (key540, 6), (key639, -2), (key368, -2), (key540, -2)]

theorem rawRowCheck17816 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form11 = rawRow17816 := by decide +kernel

def row17816 : Integer.Sparse Key := [(key364, 4), (key368, -4), (key534, -4), (key540, 4)]

theorem rowCheck17816 : row17816 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17816 := by decide +kernel

theorem rowEval17816 (x : Key → ℝ) : Integer.Sparse.eval row17816 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck17816, Integer.Sparse.eval_collectBalanced, rawRowCheck17816]

def rawRow17817 : Integer.Sparse Key := [(key368, -2), (key364, -2), (key361, -2), (key364, 6), (key540, -2), (key534, -2), (key530, -2), (key639, 2), (key634, 2), (key540, 2), (key364, 2), (key530, 2), (key361, 2), (key634, -2), (key534, -2), (key364, -2), (key540, 6), (key639, -2), (key540, -2), (key368, -2)]

theorem rawRowCheck17817 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form11 = rawRow17817 := by decide +kernel

def row17817 : Integer.Sparse Key := [(key364, 4), (key368, -4), (key534, -4), (key540, 4)]

theorem rowCheck17817 : row17817 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17817 := by decide +kernel

theorem rowEval17817 (x : Key → ℝ) : Integer.Sparse.eval row17817 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17817, Integer.Sparse.eval_collectBalanced, rawRowCheck17817]

def rawRow17818 : Integer.Sparse Key := [(key530, -2), (key534, -2), (key540, -2), (key540, 6), (key361, -2), (key364, -2), (key368, -2), (key361, 2), (key364, 2), (key530, 2), (key634, 2), (key540, 2), (key639, 2), (key368, -2), (key540, -2), (key639, -2), (key364, 6), (key364, -2), (key534, -2), (key634, -2)]

theorem rawRowCheck17818 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form11 = rawRow17818 := by decide +kernel

def row17818 : Integer.Sparse Key := [(key364, 4), (key368, -4), (key534, -4), (key540, 4)]

theorem rowCheck17818 : row17818 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17818 := by decide +kernel

theorem rowEval17818 (x : Key → ℝ) : Integer.Sparse.eval row17818 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17818, Integer.Sparse.eval_collectBalanced, rawRowCheck17818]

def rawRow17819 : Integer.Sparse Key := [(key534, -2), (key530, -2), (key540, -2), (key540, 6), (key364, -2), (key361, -2), (key368, -2), (key364, 2), (key361, 2), (key634, 2), (key530, 2), (key639, 2), (key540, 2), (key368, -2), (key639, -2), (key540, -2), (key364, 6), (key364, -2), (key634, -2), (key534, -2)]

theorem rawRowCheck17819 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form11 = rawRow17819 := by decide +kernel

def row17819 : Integer.Sparse Key := [(key364, 4), (key368, -4), (key534, -4), (key540, 4)]

theorem rowCheck17819 : row17819 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17819 := by decide +kernel

theorem rowEval17819 (x : Key → ℝ) : Integer.Sparse.eval row17819 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck17819, Integer.Sparse.eval_collectBalanced, rawRowCheck17819]

def rawRow17820 : Integer.Sparse Key := [(key530, -2), (key540, -2), (key534, -2), (key540, 6), (key361, -2), (key368, -2), (key364, -2), (key530, 2), (key540, 2), (key361, 2), (key639, 2), (key364, 2), (key634, 2), (key540, -2), (key368, -2), (key639, -2), (key364, 6), (key534, -2), (key364, -2), (key634, -2)]

theorem rawRowCheck17820 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form11 = rawRow17820 := by decide +kernel

def row17820 : Integer.Sparse Key := [(key364, 4), (key368, -4), (key534, -4), (key540, 4)]

theorem rowCheck17820 : row17820 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17820 := by decide +kernel

theorem rowEval17820 (x : Key → ℝ) : Integer.Sparse.eval row17820 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17820, Integer.Sparse.eval_collectBalanced, rawRowCheck17820]

def rawRow17821 : Integer.Sparse Key := [(key540, -2), (key530, -2), (key534, -2), (key540, 6), (key368, -2), (key361, -2), (key364, -2), (key540, 2), (key530, 2), (key639, 2), (key361, 2), (key634, 2), (key364, 2), (key540, -2), (key639, -2), (key368, -2), (key364, 6), (key534, -2), (key634, -2), (key364, -2)]

theorem rawRowCheck17821 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form11 = rawRow17821 := by decide +kernel

def row17821 : Integer.Sparse Key := [(key364, 4), (key368, -4), (key534, -4), (key540, 4)]

theorem rowCheck17821 : row17821 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17821 := by decide +kernel

theorem rowEval17821 (x : Key → ℝ) : Integer.Sparse.eval row17821 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17821, Integer.Sparse.eval_collectBalanced, rawRowCheck17821]

def rawRow17822 : Integer.Sparse Key := [(key534, -2), (key540, -2), (key530, -2), (key540, 6), (key364, -2), (key368, -2), (key361, -2), (key634, 2), (key639, 2), (key364, 2), (key540, 2), (key361, 2), (key530, 2), (key639, -2), (key368, -2), (key540, -2), (key364, 6), (key634, -2), (key364, -2), (key534, -2)]

theorem rawRowCheck17822 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form11 = rawRow17822 := by decide +kernel

def row17822 : Integer.Sparse Key := [(key364, 4), (key368, -4), (key534, -4), (key540, 4)]

theorem rowCheck17822 : row17822 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17822 := by decide +kernel

theorem rowEval17822 (x : Key → ℝ) : Integer.Sparse.eval row17822 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck17822, Integer.Sparse.eval_collectBalanced, rawRowCheck17822]

def rawRow17823 : Integer.Sparse Key := [(key540, -2), (key534, -2), (key530, -2), (key540, 6), (key368, -2), (key364, -2), (key361, -2), (key639, 2), (key634, 2), (key540, 2), (key364, 2), (key530, 2), (key361, 2), (key639, -2), (key540, -2), (key368, -2), (key364, 6), (key634, -2), (key534, -2), (key364, -2)]

theorem rawRowCheck17823 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form11 = rawRow17823 := by decide +kernel

def row17823 : Integer.Sparse Key := [(key364, 4), (key368, -4), (key534, -4), (key540, 4)]

theorem rowCheck17823 : row17823 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17823 := by decide +kernel

theorem rowEval17823 (x : Key → ℝ) : Integer.Sparse.eval row17823 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17823, Integer.Sparse.eval_collectBalanced, rawRowCheck17823]

def rawRow17824 : Integer.Sparse Key := [(key530, -2), (key540, -2), (key540, -2), (key534, 6), (key530, -2), (key540, -2), (key540, -2), (key361, 2), (key368, 2), (key361, 2), (key639, 2), (key368, 2), (key639, 2), (key364, -2), (key364, -2), (key634, -2), (key534, 6), (key364, -2), (key364, -2), (key634, -2)]

theorem rawRowCheck17824 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form11 = rawRow17824 := by decide +kernel

def row17824 : Integer.Sparse Key := [(key361, 4), (key364, -8), (key368, 4), (key530, -4), (key534, 12), (key540, -8), (key634, -4), (key639, 4)]

theorem rowCheck17824 : row17824 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17824 := by decide +kernel

theorem rowEval17824 (x : Key → ℝ) : Integer.Sparse.eval row17824 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17824, Integer.Sparse.eval_collectBalanced, rawRowCheck17824]

def rawRow17825 : Integer.Sparse Key := [(key540, -2), (key530, -2), (key540, -2), (key534, 6), (key540, -2), (key530, -2), (key540, -2), (key368, 2), (key361, 2), (key639, 2), (key361, 2), (key639, 2), (key368, 2), (key364, -2), (key634, -2), (key364, -2), (key534, 6), (key364, -2), (key634, -2), (key364, -2)]

theorem rawRowCheck17825 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form11 = rawRow17825 := by decide +kernel

def row17825 : Integer.Sparse Key := [(key361, 4), (key364, -8), (key368, 4), (key530, -4), (key534, 12), (key540, -8), (key634, -4), (key639, 4)]

theorem rowCheck17825 : row17825 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17825 := by decide +kernel

theorem rowEval17825 (x : Key → ℝ) : Integer.Sparse.eval row17825 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17825, Integer.Sparse.eval_collectBalanced, rawRowCheck17825]

def rawRow17826 : Integer.Sparse Key := [(key540, -2), (key540, -2), (key530, -2), (key534, 6), (key540, -2), (key540, -2), (key530, -2), (key639, 2), (key639, 2), (key368, 2), (key368, 2), (key361, 2), (key361, 2), (key634, -2), (key364, -2), (key364, -2), (key534, 6), (key634, -2), (key364, -2), (key364, -2)]

theorem rawRowCheck17826 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form11 = rawRow17826 := by decide +kernel

def row17826 : Integer.Sparse Key := [(key361, 4), (key364, -8), (key368, 4), (key530, -4), (key534, 12), (key540, -8), (key634, -4), (key639, 4)]

theorem rowCheck17826 : row17826 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17826 := by decide +kernel

theorem rowEval17826 (x : Key → ℝ) : Integer.Sparse.eval row17826 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17826, Integer.Sparse.eval_collectBalanced, rawRowCheck17826]

def rawRow17827 : Integer.Sparse Key := [(key1992, 2), (key1992, 2), (key1995, 2), (key2002, -2), (key2004, -2), (key2004, -2), (key1992, 2), (key1992, 2), (key1995, 2), (key2271, -1), (key2273, -1), (key2271, -1), (key2295, -1), (key2273, -1), (key2295, -1), (key2002, -2), (key2004, -2), (key2004, -2), (key2271, -1), (key2273, -1), (key2271, -1), (key2295, -1), (key2273, -1), (key2295, -1), (key2325, 4), (key2325, 4), (key2337, 4)]

theorem rawRowCheck17827 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form12 = rawRow17827 := by decide +kernel

def row17827 : Integer.Sparse Key := [(key1992, 8), (key1995, 4), (key2002, -4), (key2004, -8), (key2271, -4), (key2273, -4), (key2295, -4), (key2325, 8), (key2337, 4)]

theorem rowCheck17827 : row17827 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17827 := by decide +kernel

theorem rowEval17827 (x : Key → ℝ) : Integer.Sparse.eval row17827 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck17827, Integer.Sparse.eval_collectBalanced, rawRowCheck17827]

def rawRow17828 : Integer.Sparse Key := [(key1992, 2), (key1995, 2), (key1992, 2), (key2004, -2), (key2002, -2), (key2004, -2), (key1992, 2), (key1995, 2), (key1992, 2), (key2273, -1), (key2271, -1), (key2295, -1), (key2271, -1), (key2295, -1), (key2273, -1), (key2004, -2), (key2002, -2), (key2004, -2), (key2273, -1), (key2271, -1), (key2295, -1), (key2271, -1), (key2295, -1), (key2273, -1), (key2325, 4), (key2337, 4), (key2325, 4)]

theorem rawRowCheck17828 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form12 = rawRow17828 := by decide +kernel

def row17828 : Integer.Sparse Key := [(key1992, 8), (key1995, 4), (key2002, -4), (key2004, -8), (key2271, -4), (key2273, -4), (key2295, -4), (key2325, 8), (key2337, 4)]

theorem rowCheck17828 : row17828 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17828 := by decide +kernel

theorem rowEval17828 (x : Key → ℝ) : Integer.Sparse.eval row17828 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck17828, Integer.Sparse.eval_collectBalanced, rawRowCheck17828]

def rawRow17829 : Integer.Sparse Key := [(key1995, 2), (key1992, 2), (key1992, 2), (key2004, -2), (key2004, -2), (key2002, -2), (key1995, 2), (key1992, 2), (key1992, 2), (key2295, -1), (key2295, -1), (key2273, -1), (key2273, -1), (key2271, -1), (key2271, -1), (key2004, -2), (key2004, -2), (key2002, -2), (key2295, -1), (key2295, -1), (key2273, -1), (key2273, -1), (key2271, -1), (key2271, -1), (key2337, 4), (key2325, 4), (key2325, 4)]

theorem rawRowCheck17829 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form12 = rawRow17829 := by decide +kernel

def row17829 : Integer.Sparse Key := [(key1992, 8), (key1995, 4), (key2002, -4), (key2004, -8), (key2271, -4), (key2273, -4), (key2295, -4), (key2325, 8), (key2337, 4)]

theorem rowCheck17829 : row17829 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17829 := by decide +kernel

theorem rowEval17829 (x : Key → ℝ) : Integer.Sparse.eval row17829 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck17829, Integer.Sparse.eval_collectBalanced, rawRowCheck17829]

def rawRow17830 : Integer.Sparse Key := [(key1992, 2), (key2002, 2), (key2004, 2), (key1992, -2), (key1995, -2), (key2004, -2), (key2237, 2), (key2271, 2), (key2273, 2), (key1992, -1), (key1995, -1), (key2237, -1), (key2260, -1), (key2273, -1), (key2295, -1), (key2271, -2), (key2273, -2), (key2325, -2), (key2002, -1), (key2004, -1), (key2271, -1), (key2295, -1), (key2325, -1), (key2337, -1), (key2004, 4), (key2273, 4), (key2295, 4)]

theorem rawRowCheck17830 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form12 = rawRow17830 := by decide +kernel

def row17830 : Integer.Sparse Key := [(key1992, -1), (key1995, -3), (key2002, 1), (key2004, 3), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, 3), (key2295, 2), (key2325, -3), (key2337, -1)]

theorem rowCheck17830 : row17830 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17830 := by decide +kernel

theorem rowEval17830 (x : Key → ℝ) : Integer.Sparse.eval row17830 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck17830, Integer.Sparse.eval_collectBalanced, rawRowCheck17830]

def rawRow17831 : Integer.Sparse Key := [(key1992, 2), (key2004, 2), (key2002, 2), (key1995, -2), (key1992, -2), (key2004, -2), (key2237, 2), (key2273, 2), (key2271, 2), (key1995, -1), (key1992, -1), (key2260, -1), (key2237, -1), (key2295, -1), (key2273, -1), (key2273, -2), (key2271, -2), (key2325, -2), (key2004, -1), (key2002, -1), (key2295, -1), (key2271, -1), (key2337, -1), (key2325, -1), (key2004, 4), (key2295, 4), (key2273, 4)]

theorem rawRowCheck17831 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form12 = rawRow17831 := by decide +kernel

def row17831 : Integer.Sparse Key := [(key1992, -1), (key1995, -3), (key2002, 1), (key2004, 3), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, 3), (key2295, 2), (key2325, -3), (key2337, -1)]

theorem rowCheck17831 : row17831 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17831 := by decide +kernel

theorem rowEval17831 (x : Key → ℝ) : Integer.Sparse.eval row17831 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck17831, Integer.Sparse.eval_collectBalanced, rawRowCheck17831]

def rawRow17832 : Integer.Sparse Key := [(key2002, 2), (key1992, 2), (key2004, 2), (key1992, -2), (key2004, -2), (key1995, -2), (key2271, 2), (key2237, 2), (key2273, 2), (key2237, -1), (key2273, -1), (key1992, -1), (key2295, -1), (key1995, -1), (key2260, -1), (key2271, -2), (key2325, -2), (key2273, -2), (key2271, -1), (key2325, -1), (key2002, -1), (key2337, -1), (key2004, -1), (key2295, -1), (key2273, 4), (key2004, 4), (key2295, 4)]

theorem rawRowCheck17832 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form12 = rawRow17832 := by decide +kernel

def row17832 : Integer.Sparse Key := [(key1992, -1), (key1995, -3), (key2002, 1), (key2004, 3), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, 3), (key2295, 2), (key2325, -3), (key2337, -1)]

theorem rowCheck17832 : row17832 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17832 := by decide +kernel

theorem rowEval17832 (x : Key → ℝ) : Integer.Sparse.eval row17832 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck17832, Integer.Sparse.eval_collectBalanced, rawRowCheck17832]

def rawRow17833 : Integer.Sparse Key := [(key2002, 2), (key2004, 2), (key1992, 2), (key2004, -2), (key1992, -2), (key1995, -2), (key2271, 2), (key2273, 2), (key2237, 2), (key2273, -1), (key2237, -1), (key2295, -1), (key1992, -1), (key2260, -1), (key1995, -1), (key2325, -2), (key2271, -2), (key2273, -2), (key2325, -1), (key2271, -1), (key2337, -1), (key2002, -1), (key2295, -1), (key2004, -1), (key2273, 4), (key2295, 4), (key2004, 4)]

theorem rawRowCheck17833 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form12 = rawRow17833 := by decide +kernel

def row17833 : Integer.Sparse Key := [(key1992, -1), (key1995, -3), (key2002, 1), (key2004, 3), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, 3), (key2295, 2), (key2325, -3), (key2337, -1)]

theorem rowCheck17833 : row17833 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17833 := by decide +kernel

theorem rowEval17833 (x : Key → ℝ) : Integer.Sparse.eval row17833 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck17833, Integer.Sparse.eval_collectBalanced, rawRowCheck17833]

def rawRow17834 : Integer.Sparse Key := [(key2004, 2), (key1992, 2), (key2002, 2), (key1995, -2), (key2004, -2), (key1992, -2), (key2273, 2), (key2237, 2), (key2271, 2), (key2260, -1), (key2295, -1), (key1995, -1), (key2273, -1), (key1992, -1), (key2237, -1), (key2273, -2), (key2325, -2), (key2271, -2), (key2295, -1), (key2337, -1), (key2004, -1), (key2325, -1), (key2002, -1), (key2271, -1), (key2295, 4), (key2004, 4), (key2273, 4)]

theorem rawRowCheck17834 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form12 = rawRow17834 := by decide +kernel

def row17834 : Integer.Sparse Key := [(key1992, -1), (key1995, -3), (key2002, 1), (key2004, 3), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, 3), (key2295, 2), (key2325, -3), (key2337, -1)]

theorem rowCheck17834 : row17834 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17834 := by decide +kernel

theorem rowEval17834 (x : Key → ℝ) : Integer.Sparse.eval row17834 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck17834, Integer.Sparse.eval_collectBalanced, rawRowCheck17834]

def rawRow17835 : Integer.Sparse Key := [(key2004, 2), (key2002, 2), (key1992, 2), (key2004, -2), (key1995, -2), (key1992, -2), (key2273, 2), (key2271, 2), (key2237, 2), (key2295, -1), (key2260, -1), (key2273, -1), (key1995, -1), (key2237, -1), (key1992, -1), (key2325, -2), (key2273, -2), (key2271, -2), (key2337, -1), (key2295, -1), (key2325, -1), (key2004, -1), (key2271, -1), (key2002, -1), (key2295, 4), (key2273, 4), (key2004, 4)]

theorem rawRowCheck17835 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form12 = rawRow17835 := by decide +kernel

def row17835 : Integer.Sparse Key := [(key1992, -1), (key1995, -3), (key2002, 1), (key2004, 3), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, 3), (key2295, 2), (key2325, -3), (key2337, -1)]

theorem rowCheck17835 : row17835 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17835 := by decide +kernel

theorem rowEval17835 (x : Key → ℝ) : Integer.Sparse.eval row17835 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck17835, Integer.Sparse.eval_collectBalanced, rawRowCheck17835]

def rawRow17836 : Integer.Sparse Key := [(key2237, 2), (key2271, 2), (key2273, 2), (key2271, -2), (key2273, -2), (key2325, -2), (key1992, 2), (key2002, 2), (key2004, 2), (key2002, -1), (key2004, -1), (key2271, -1), (key2295, -1), (key2325, -1), (key2337, -1), (key1992, -2), (key1995, -2), (key2004, -2), (key1992, -1), (key1995, -1), (key2237, -1), (key2260, -1), (key2273, -1), (key2295, -1), (key2004, 4), (key2273, 4), (key2295, 4)]

theorem rawRowCheck17836 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form12 = rawRow17836 := by decide +kernel

def row17836 : Integer.Sparse Key := [(key1992, -1), (key1995, -3), (key2002, 1), (key2004, 3), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, 3), (key2295, 2), (key2325, -3), (key2337, -1)]

theorem rowCheck17836 : row17836 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17836 := by decide +kernel

theorem rowEval17836 (x : Key → ℝ) : Integer.Sparse.eval row17836 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck17836, Integer.Sparse.eval_collectBalanced, rawRowCheck17836]

def rawRow17837 : Integer.Sparse Key := [(key2237, 2), (key2273, 2), (key2271, 2), (key2273, -2), (key2271, -2), (key2325, -2), (key1992, 2), (key2004, 2), (key2002, 2), (key2004, -1), (key2002, -1), (key2295, -1), (key2271, -1), (key2337, -1), (key2325, -1), (key1995, -2), (key1992, -2), (key2004, -2), (key1995, -1), (key1992, -1), (key2260, -1), (key2237, -1), (key2295, -1), (key2273, -1), (key2004, 4), (key2295, 4), (key2273, 4)]

theorem rawRowCheck17837 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form12 = rawRow17837 := by decide +kernel

def row17837 : Integer.Sparse Key := [(key1992, -1), (key1995, -3), (key2002, 1), (key2004, 3), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, 3), (key2295, 2), (key2325, -3), (key2337, -1)]

theorem rowCheck17837 : row17837 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17837 := by decide +kernel

theorem rowEval17837 (x : Key → ℝ) : Integer.Sparse.eval row17837 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck17837, Integer.Sparse.eval_collectBalanced, rawRowCheck17837]

def rawRow17838 : Integer.Sparse Key := [(key2271, 2), (key2237, 2), (key2273, 2), (key2271, -2), (key2325, -2), (key2273, -2), (key2002, 2), (key1992, 2), (key2004, 2), (key2271, -1), (key2325, -1), (key2002, -1), (key2337, -1), (key2004, -1), (key2295, -1), (key1992, -2), (key2004, -2), (key1995, -2), (key2237, -1), (key2273, -1), (key1992, -1), (key2295, -1), (key1995, -1), (key2260, -1), (key2273, 4), (key2004, 4), (key2295, 4)]

theorem rawRowCheck17838 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form12 = rawRow17838 := by decide +kernel

def row17838 : Integer.Sparse Key := [(key1992, -1), (key1995, -3), (key2002, 1), (key2004, 3), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, 3), (key2295, 2), (key2325, -3), (key2337, -1)]

theorem rowCheck17838 : row17838 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17838 := by decide +kernel

theorem rowEval17838 (x : Key → ℝ) : Integer.Sparse.eval row17838 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck17838, Integer.Sparse.eval_collectBalanced, rawRowCheck17838]

def rawRow17839 : Integer.Sparse Key := [(key2271, 2), (key2273, 2), (key2237, 2), (key2325, -2), (key2271, -2), (key2273, -2), (key2002, 2), (key2004, 2), (key1992, 2), (key2325, -1), (key2271, -1), (key2337, -1), (key2002, -1), (key2295, -1), (key2004, -1), (key2004, -2), (key1992, -2), (key1995, -2), (key2273, -1), (key2237, -1), (key2295, -1), (key1992, -1), (key2260, -1), (key1995, -1), (key2273, 4), (key2295, 4), (key2004, 4)]

theorem rawRowCheck17839 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form12 = rawRow17839 := by decide +kernel

def row17839 : Integer.Sparse Key := [(key1992, -1), (key1995, -3), (key2002, 1), (key2004, 3), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, 3), (key2295, 2), (key2325, -3), (key2337, -1)]

theorem rowCheck17839 : row17839 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17839 := by decide +kernel

theorem rowEval17839 (x : Key → ℝ) : Integer.Sparse.eval row17839 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck17839, Integer.Sparse.eval_collectBalanced, rawRowCheck17839]

def rawRow17840 : Integer.Sparse Key := [(key2273, 2), (key2237, 2), (key2271, 2), (key2273, -2), (key2325, -2), (key2271, -2), (key2004, 2), (key1992, 2), (key2002, 2), (key2295, -1), (key2337, -1), (key2004, -1), (key2325, -1), (key2002, -1), (key2271, -1), (key1995, -2), (key2004, -2), (key1992, -2), (key2260, -1), (key2295, -1), (key1995, -1), (key2273, -1), (key1992, -1), (key2237, -1), (key2295, 4), (key2004, 4), (key2273, 4)]

theorem rawRowCheck17840 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form12 = rawRow17840 := by decide +kernel

def row17840 : Integer.Sparse Key := [(key1992, -1), (key1995, -3), (key2002, 1), (key2004, 3), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, 3), (key2295, 2), (key2325, -3), (key2337, -1)]

theorem rowCheck17840 : row17840 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17840 := by decide +kernel

theorem rowEval17840 (x : Key → ℝ) : Integer.Sparse.eval row17840 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck17840, Integer.Sparse.eval_collectBalanced, rawRowCheck17840]

def rawRow17841 : Integer.Sparse Key := [(key2273, 2), (key2271, 2), (key2237, 2), (key2325, -2), (key2273, -2), (key2271, -2), (key2004, 2), (key2002, 2), (key1992, 2), (key2337, -1), (key2295, -1), (key2325, -1), (key2004, -1), (key2271, -1), (key2002, -1), (key2004, -2), (key1995, -2), (key1992, -2), (key2295, -1), (key2260, -1), (key2273, -1), (key1995, -1), (key2237, -1), (key1992, -1), (key2295, 4), (key2273, 4), (key2004, 4)]

theorem rawRowCheck17841 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form12 = rawRow17841 := by decide +kernel

def row17841 : Integer.Sparse Key := [(key1992, -1), (key1995, -3), (key2002, 1), (key2004, 3), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, 3), (key2295, 2), (key2325, -3), (key2337, -1)]

theorem rowCheck17841 : row17841 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17841 := by decide +kernel

theorem rowEval17841 (x : Key → ℝ) : Integer.Sparse.eval row17841 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck17841, Integer.Sparse.eval_collectBalanced, rawRowCheck17841]

def rawRow17842 : Integer.Sparse Key := [(key2271, 2), (key2271, 2), (key2325, 2), (key2237, -2), (key2273, -2), (key2273, -2), (key2271, 2), (key2271, 2), (key2325, 2), (key1992, -1), (key2004, -1), (key1992, -1), (key2295, -1), (key2004, -1), (key2295, -1), (key2237, -2), (key2273, -2), (key2273, -2), (key1992, -1), (key2004, -1), (key1992, -1), (key2295, -1), (key2004, -1), (key2295, -1), (key1995, 4), (key1995, 4), (key2260, 4)]

theorem rawRowCheck17842 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form12 = rawRow17842 := by decide +kernel

def row17842 : Integer.Sparse Key := [(key1992, -4), (key1995, 8), (key2004, -4), (key2237, -4), (key2260, 4), (key2271, 8), (key2273, -8), (key2295, -4), (key2325, 4)]

theorem rowCheck17842 : row17842 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17842 := by decide +kernel

theorem rowEval17842 (x : Key → ℝ) : Integer.Sparse.eval row17842 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck17842, Integer.Sparse.eval_collectBalanced, rawRowCheck17842]

def rawRow17843 : Integer.Sparse Key := [(key2271, 2), (key2325, 2), (key2271, 2), (key2273, -2), (key2237, -2), (key2273, -2), (key2271, 2), (key2325, 2), (key2271, 2), (key2004, -1), (key1992, -1), (key2295, -1), (key1992, -1), (key2295, -1), (key2004, -1), (key2273, -2), (key2237, -2), (key2273, -2), (key2004, -1), (key1992, -1), (key2295, -1), (key1992, -1), (key2295, -1), (key2004, -1), (key1995, 4), (key2260, 4), (key1995, 4)]

theorem rawRowCheck17843 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form12 = rawRow17843 := by decide +kernel

def row17843 : Integer.Sparse Key := [(key1992, -4), (key1995, 8), (key2004, -4), (key2237, -4), (key2260, 4), (key2271, 8), (key2273, -8), (key2295, -4), (key2325, 4)]

theorem rowCheck17843 : row17843 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17843 := by decide +kernel

theorem rowEval17843 (x : Key → ℝ) : Integer.Sparse.eval row17843 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck17843, Integer.Sparse.eval_collectBalanced, rawRowCheck17843]

def rawRow17844 : Integer.Sparse Key := [(key2325, 2), (key2271, 2), (key2271, 2), (key2273, -2), (key2273, -2), (key2237, -2), (key2325, 2), (key2271, 2), (key2271, 2), (key2295, -1), (key2295, -1), (key2004, -1), (key2004, -1), (key1992, -1), (key1992, -1), (key2273, -2), (key2273, -2), (key2237, -2), (key2295, -1), (key2295, -1), (key2004, -1), (key2004, -1), (key1992, -1), (key1992, -1), (key2260, 4), (key1995, 4), (key1995, 4)]

theorem rawRowCheck17844 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form12 = rawRow17844 := by decide +kernel

def row17844 : Integer.Sparse Key := [(key1992, -4), (key1995, 8), (key2004, -4), (key2237, -4), (key2260, 4), (key2271, 8), (key2273, -8), (key2295, -4), (key2325, 4)]

theorem rowCheck17844 : row17844 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17844 := by decide +kernel

theorem rowEval17844 (x : Key → ℝ) : Integer.Sparse.eval row17844 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck17844, Integer.Sparse.eval_collectBalanced, rawRowCheck17844]

def rawRow17845 : Integer.Sparse Key := [(key2031, 2), (key2036, 2), (key2036, 2), (key2061, -1), (key2066, -1), (key2061, -1), (key2071, -1), (key2066, -1), (key2071, -1), (key2031, 2), (key2036, 2), (key2036, 2), (key2150, -1), (key2155, -1), (key2150, -1), (key2168, -1), (key2155, -1), (key2168, -1), (key2061, -1), (key2066, -1), (key2061, -1), (key2071, -1), (key2066, -1), (key2071, -1), (key2150, -1), (key2155, -1), (key2150, -1), (key2168, -1), (key2155, -1), (key2168, -1), (key2243, 2), (key2248, 2), (key2243, 2), (key2255, 2), (key2248, 2), (key2255, 2)]

theorem rawRowCheck17845 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form13 = rawRow17845 := by decide +kernel

def row17845 : Integer.Sparse Key := [(key2031, 4), (key2036, 8), (key2061, -4), (key2066, -4), (key2071, -4), (key2150, -4), (key2155, -4), (key2168, -4), (key2243, 4), (key2248, 4), (key2255, 4)]

theorem rowCheck17845 : row17845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17845 := by decide +kernel

theorem rowEval17845 (x : Key → ℝ) : Integer.Sparse.eval row17845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form13) x := by
  rw [rowCheck17845, Integer.Sparse.eval_collectBalanced, rawRowCheck17845]

def rawRow17846 : Integer.Sparse Key := [(key2036, 2), (key2031, 2), (key2036, 2), (key2066, -1), (key2061, -1), (key2071, -1), (key2061, -1), (key2071, -1), (key2066, -1), (key2036, 2), (key2031, 2), (key2036, 2), (key2155, -1), (key2150, -1), (key2168, -1), (key2150, -1), (key2168, -1), (key2155, -1), (key2066, -1), (key2061, -1), (key2071, -1), (key2061, -1), (key2071, -1), (key2066, -1), (key2155, -1), (key2150, -1), (key2168, -1), (key2150, -1), (key2168, -1), (key2155, -1), (key2248, 2), (key2243, 2), (key2255, 2), (key2243, 2), (key2255, 2), (key2248, 2)]

theorem rawRowCheck17846 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form13 = rawRow17846 := by decide +kernel

def row17846 : Integer.Sparse Key := [(key2031, 4), (key2036, 8), (key2061, -4), (key2066, -4), (key2071, -4), (key2150, -4), (key2155, -4), (key2168, -4), (key2243, 4), (key2248, 4), (key2255, 4)]

theorem rowCheck17846 : row17846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17846 := by decide +kernel

theorem rowEval17846 (x : Key → ℝ) : Integer.Sparse.eval row17846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck17846, Integer.Sparse.eval_collectBalanced, rawRowCheck17846]

def rawRow17847 : Integer.Sparse Key := [(key2036, 2), (key2036, 2), (key2031, 2), (key2071, -1), (key2071, -1), (key2066, -1), (key2066, -1), (key2061, -1), (key2061, -1), (key2036, 2), (key2036, 2), (key2031, 2), (key2168, -1), (key2168, -1), (key2155, -1), (key2155, -1), (key2150, -1), (key2150, -1), (key2071, -1), (key2071, -1), (key2066, -1), (key2066, -1), (key2061, -1), (key2061, -1), (key2168, -1), (key2168, -1), (key2155, -1), (key2155, -1), (key2150, -1), (key2150, -1), (key2255, 2), (key2255, 2), (key2248, 2), (key2248, 2), (key2243, 2), (key2243, 2)]

theorem rawRowCheck17847 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form13 = rawRow17847 := by decide +kernel

def row17847 : Integer.Sparse Key := [(key2031, 4), (key2036, 8), (key2061, -4), (key2066, -4), (key2071, -4), (key2150, -4), (key2155, -4), (key2168, -4), (key2243, 4), (key2248, 4), (key2255, 4)]

theorem rowCheck17847 : row17847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17847 := by decide +kernel

theorem rowEval17847 (x : Key → ℝ) : Integer.Sparse.eval row17847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck17847, Integer.Sparse.eval_collectBalanced, rawRowCheck17847]

def rawRow17848 : Integer.Sparse Key := [(key2061, 2), (key2066, 2), (key2093, 2), (key2031, -1), (key2036, -1), (key2061, -1), (key2071, -1), (key2093, -1), (key2096, -1), (key2150, 2), (key2155, 2), (key2195, 2), (key2031, -1), (key2036, -1), (key2150, -1), (key2168, -1), (key2195, -1), (key2201, -1), (key2150, -1), (key2155, -1), (key2243, -1), (key2248, -1), (key2304, -1), (key2306, -1), (key2061, -1), (key2066, -1), (key2243, -1), (key2255, -1), (key2304, -1), (key2311, -1), (key2061, 2), (key2071, 2), (key2150, 2), (key2168, 2), (key2306, 2), (key2311, 2)]

theorem rawRowCheck17848 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form13 = rawRow17848 := by decide +kernel

def row17848 : Integer.Sparse Key := [(key2031, -2), (key2036, -2), (key2061, 2), (key2066, 1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 2), (key2155, 1), (key2168, 1), (key2195, 1), (key2201, -1), (key2243, -2), (key2248, -1), (key2255, -1), (key2304, -2), (key2306, 1), (key2311, 1)]

theorem rowCheck17848 : row17848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17848 := by decide +kernel

theorem rowEval17848 (x : Key → ℝ) : Integer.Sparse.eval row17848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form13) x := by
  rw [rowCheck17848, Integer.Sparse.eval_collectBalanced, rawRowCheck17848]

def rawRow17849 : Integer.Sparse Key := [(key2066, 2), (key2061, 2), (key2093, 2), (key2036, -1), (key2031, -1), (key2071, -1), (key2061, -1), (key2096, -1), (key2093, -1), (key2155, 2), (key2150, 2), (key2195, 2), (key2036, -1), (key2031, -1), (key2168, -1), (key2150, -1), (key2201, -1), (key2195, -1), (key2155, -1), (key2150, -1), (key2248, -1), (key2243, -1), (key2306, -1), (key2304, -1), (key2066, -1), (key2061, -1), (key2255, -1), (key2243, -1), (key2311, -1), (key2304, -1), (key2071, 2), (key2061, 2), (key2168, 2), (key2150, 2), (key2311, 2), (key2306, 2)]

theorem rawRowCheck17849 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form13 = rawRow17849 := by decide +kernel

def row17849 : Integer.Sparse Key := [(key2031, -2), (key2036, -2), (key2061, 2), (key2066, 1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 2), (key2155, 1), (key2168, 1), (key2195, 1), (key2201, -1), (key2243, -2), (key2248, -1), (key2255, -1), (key2304, -2), (key2306, 1), (key2311, 1)]

theorem rowCheck17849 : row17849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17849 := by decide +kernel

theorem rowEval17849 (x : Key → ℝ) : Integer.Sparse.eval row17849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck17849, Integer.Sparse.eval_collectBalanced, rawRowCheck17849]

def rawRow17850 : Integer.Sparse Key := [(key2061, 2), (key2093, 2), (key2066, 2), (key2061, -1), (key2093, -1), (key2031, -1), (key2096, -1), (key2036, -1), (key2071, -1), (key2150, 2), (key2195, 2), (key2155, 2), (key2150, -1), (key2195, -1), (key2031, -1), (key2201, -1), (key2036, -1), (key2168, -1), (key2243, -1), (key2304, -1), (key2150, -1), (key2306, -1), (key2155, -1), (key2248, -1), (key2243, -1), (key2304, -1), (key2061, -1), (key2311, -1), (key2066, -1), (key2255, -1), (key2150, 2), (key2306, 2), (key2061, 2), (key2311, 2), (key2071, 2), (key2168, 2)]

theorem rawRowCheck17850 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form13 = rawRow17850 := by decide +kernel

def row17850 : Integer.Sparse Key := [(key2031, -2), (key2036, -2), (key2061, 2), (key2066, 1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 2), (key2155, 1), (key2168, 1), (key2195, 1), (key2201, -1), (key2243, -2), (key2248, -1), (key2255, -1), (key2304, -2), (key2306, 1), (key2311, 1)]

theorem rowCheck17850 : row17850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17850 := by decide +kernel

theorem rowEval17850 (x : Key → ℝ) : Integer.Sparse.eval row17850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form13) x := by
  rw [rowCheck17850, Integer.Sparse.eval_collectBalanced, rawRowCheck17850]

def rawRow17851 : Integer.Sparse Key := [(key2093, 2), (key2061, 2), (key2066, 2), (key2093, -1), (key2061, -1), (key2096, -1), (key2031, -1), (key2071, -1), (key2036, -1), (key2195, 2), (key2150, 2), (key2155, 2), (key2195, -1), (key2150, -1), (key2201, -1), (key2031, -1), (key2168, -1), (key2036, -1), (key2304, -1), (key2243, -1), (key2306, -1), (key2150, -1), (key2248, -1), (key2155, -1), (key2304, -1), (key2243, -1), (key2311, -1), (key2061, -1), (key2255, -1), (key2066, -1), (key2306, 2), (key2150, 2), (key2311, 2), (key2061, 2), (key2168, 2), (key2071, 2)]

theorem rawRowCheck17851 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form13 = rawRow17851 := by decide +kernel

def row17851 : Integer.Sparse Key := [(key2031, -2), (key2036, -2), (key2061, 2), (key2066, 1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 2), (key2155, 1), (key2168, 1), (key2195, 1), (key2201, -1), (key2243, -2), (key2248, -1), (key2255, -1), (key2304, -2), (key2306, 1), (key2311, 1)]

theorem rowCheck17851 : row17851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17851 := by decide +kernel

theorem rowEval17851 (x : Key → ℝ) : Integer.Sparse.eval row17851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck17851, Integer.Sparse.eval_collectBalanced, rawRowCheck17851]

def rawRow17852 : Integer.Sparse Key := [(key2066, 2), (key2093, 2), (key2061, 2), (key2071, -1), (key2096, -1), (key2036, -1), (key2093, -1), (key2031, -1), (key2061, -1), (key2155, 2), (key2195, 2), (key2150, 2), (key2168, -1), (key2201, -1), (key2036, -1), (key2195, -1), (key2031, -1), (key2150, -1), (key2248, -1), (key2306, -1), (key2155, -1), (key2304, -1), (key2150, -1), (key2243, -1), (key2255, -1), (key2311, -1), (key2066, -1), (key2304, -1), (key2061, -1), (key2243, -1), (key2168, 2), (key2311, 2), (key2071, 2), (key2306, 2), (key2061, 2), (key2150, 2)]

theorem rawRowCheck17852 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form13 = rawRow17852 := by decide +kernel

def row17852 : Integer.Sparse Key := [(key2031, -2), (key2036, -2), (key2061, 2), (key2066, 1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 2), (key2155, 1), (key2168, 1), (key2195, 1), (key2201, -1), (key2243, -2), (key2248, -1), (key2255, -1), (key2304, -2), (key2306, 1), (key2311, 1)]

theorem rowCheck17852 : row17852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17852 := by decide +kernel

theorem rowEval17852 (x : Key → ℝ) : Integer.Sparse.eval row17852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck17852, Integer.Sparse.eval_collectBalanced, rawRowCheck17852]

def rawRow17853 : Integer.Sparse Key := [(key2093, 2), (key2066, 2), (key2061, 2), (key2096, -1), (key2071, -1), (key2093, -1), (key2036, -1), (key2061, -1), (key2031, -1), (key2195, 2), (key2155, 2), (key2150, 2), (key2201, -1), (key2168, -1), (key2195, -1), (key2036, -1), (key2150, -1), (key2031, -1), (key2306, -1), (key2248, -1), (key2304, -1), (key2155, -1), (key2243, -1), (key2150, -1), (key2311, -1), (key2255, -1), (key2304, -1), (key2066, -1), (key2243, -1), (key2061, -1), (key2311, 2), (key2168, 2), (key2306, 2), (key2071, 2), (key2150, 2), (key2061, 2)]

theorem rawRowCheck17853 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form13 = rawRow17853 := by decide +kernel

def row17853 : Integer.Sparse Key := [(key2031, -2), (key2036, -2), (key2061, 2), (key2066, 1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 2), (key2155, 1), (key2168, 1), (key2195, 1), (key2201, -1), (key2243, -2), (key2248, -1), (key2255, -1), (key2304, -2), (key2306, 1), (key2311, 1)]

theorem rowCheck17853 : row17853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17853 := by decide +kernel

theorem rowEval17853 (x : Key → ℝ) : Integer.Sparse.eval row17853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck17853, Integer.Sparse.eval_collectBalanced, rawRowCheck17853]

def rawRow17854 : Integer.Sparse Key := [(key2150, 2), (key2155, 2), (key2195, 2), (key2150, -1), (key2155, -1), (key2243, -1), (key2248, -1), (key2304, -1), (key2306, -1), (key2061, 2), (key2066, 2), (key2093, 2), (key2061, -1), (key2066, -1), (key2243, -1), (key2255, -1), (key2304, -1), (key2311, -1), (key2031, -1), (key2036, -1), (key2061, -1), (key2071, -1), (key2093, -1), (key2096, -1), (key2031, -1), (key2036, -1), (key2150, -1), (key2168, -1), (key2195, -1), (key2201, -1), (key2061, 2), (key2071, 2), (key2150, 2), (key2168, 2), (key2306, 2), (key2311, 2)]

theorem rawRowCheck17854 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form13 = rawRow17854 := by decide +kernel

def row17854 : Integer.Sparse Key := [(key2031, -2), (key2036, -2), (key2061, 2), (key2066, 1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 2), (key2155, 1), (key2168, 1), (key2195, 1), (key2201, -1), (key2243, -2), (key2248, -1), (key2255, -1), (key2304, -2), (key2306, 1), (key2311, 1)]

theorem rowCheck17854 : row17854 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17854 := by decide +kernel

theorem rowEval17854 (x : Key → ℝ) : Integer.Sparse.eval row17854 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form13) x := by
  rw [rowCheck17854, Integer.Sparse.eval_collectBalanced, rawRowCheck17854]

def rawRow17855 : Integer.Sparse Key := [(key2155, 2), (key2150, 2), (key2195, 2), (key2155, -1), (key2150, -1), (key2248, -1), (key2243, -1), (key2306, -1), (key2304, -1), (key2066, 2), (key2061, 2), (key2093, 2), (key2066, -1), (key2061, -1), (key2255, -1), (key2243, -1), (key2311, -1), (key2304, -1), (key2036, -1), (key2031, -1), (key2071, -1), (key2061, -1), (key2096, -1), (key2093, -1), (key2036, -1), (key2031, -1), (key2168, -1), (key2150, -1), (key2201, -1), (key2195, -1), (key2071, 2), (key2061, 2), (key2168, 2), (key2150, 2), (key2311, 2), (key2306, 2)]

theorem rawRowCheck17855 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form13 = rawRow17855 := by decide +kernel

def row17855 : Integer.Sparse Key := [(key2031, -2), (key2036, -2), (key2061, 2), (key2066, 1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 2), (key2155, 1), (key2168, 1), (key2195, 1), (key2201, -1), (key2243, -2), (key2248, -1), (key2255, -1), (key2304, -2), (key2306, 1), (key2311, 1)]

theorem rowCheck17855 : row17855 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17855 := by decide +kernel

theorem rowEval17855 (x : Key → ℝ) : Integer.Sparse.eval row17855 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck17855, Integer.Sparse.eval_collectBalanced, rawRowCheck17855]

def rawRow17856 : Integer.Sparse Key := [(key2150, 2), (key2195, 2), (key2155, 2), (key2243, -1), (key2304, -1), (key2150, -1), (key2306, -1), (key2155, -1), (key2248, -1), (key2061, 2), (key2093, 2), (key2066, 2), (key2243, -1), (key2304, -1), (key2061, -1), (key2311, -1), (key2066, -1), (key2255, -1), (key2061, -1), (key2093, -1), (key2031, -1), (key2096, -1), (key2036, -1), (key2071, -1), (key2150, -1), (key2195, -1), (key2031, -1), (key2201, -1), (key2036, -1), (key2168, -1), (key2150, 2), (key2306, 2), (key2061, 2), (key2311, 2), (key2071, 2), (key2168, 2)]

theorem rawRowCheck17856 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form13 = rawRow17856 := by decide +kernel

def row17856 : Integer.Sparse Key := [(key2031, -2), (key2036, -2), (key2061, 2), (key2066, 1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 2), (key2155, 1), (key2168, 1), (key2195, 1), (key2201, -1), (key2243, -2), (key2248, -1), (key2255, -1), (key2304, -2), (key2306, 1), (key2311, 1)]

theorem rowCheck17856 : row17856 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17856 := by decide +kernel

theorem rowEval17856 (x : Key → ℝ) : Integer.Sparse.eval row17856 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form13) x := by
  rw [rowCheck17856, Integer.Sparse.eval_collectBalanced, rawRowCheck17856]

def rawRow17857 : Integer.Sparse Key := [(key2195, 2), (key2150, 2), (key2155, 2), (key2304, -1), (key2243, -1), (key2306, -1), (key2150, -1), (key2248, -1), (key2155, -1), (key2093, 2), (key2061, 2), (key2066, 2), (key2304, -1), (key2243, -1), (key2311, -1), (key2061, -1), (key2255, -1), (key2066, -1), (key2093, -1), (key2061, -1), (key2096, -1), (key2031, -1), (key2071, -1), (key2036, -1), (key2195, -1), (key2150, -1), (key2201, -1), (key2031, -1), (key2168, -1), (key2036, -1), (key2306, 2), (key2150, 2), (key2311, 2), (key2061, 2), (key2168, 2), (key2071, 2)]

theorem rawRowCheck17857 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form13 = rawRow17857 := by decide +kernel

def row17857 : Integer.Sparse Key := [(key2031, -2), (key2036, -2), (key2061, 2), (key2066, 1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 2), (key2155, 1), (key2168, 1), (key2195, 1), (key2201, -1), (key2243, -2), (key2248, -1), (key2255, -1), (key2304, -2), (key2306, 1), (key2311, 1)]

theorem rowCheck17857 : row17857 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17857 := by decide +kernel

theorem rowEval17857 (x : Key → ℝ) : Integer.Sparse.eval row17857 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck17857, Integer.Sparse.eval_collectBalanced, rawRowCheck17857]

def rawRow17858 : Integer.Sparse Key := [(key2155, 2), (key2195, 2), (key2150, 2), (key2248, -1), (key2306, -1), (key2155, -1), (key2304, -1), (key2150, -1), (key2243, -1), (key2066, 2), (key2093, 2), (key2061, 2), (key2255, -1), (key2311, -1), (key2066, -1), (key2304, -1), (key2061, -1), (key2243, -1), (key2071, -1), (key2096, -1), (key2036, -1), (key2093, -1), (key2031, -1), (key2061, -1), (key2168, -1), (key2201, -1), (key2036, -1), (key2195, -1), (key2031, -1), (key2150, -1), (key2168, 2), (key2311, 2), (key2071, 2), (key2306, 2), (key2061, 2), (key2150, 2)]

theorem rawRowCheck17858 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form13 = rawRow17858 := by decide +kernel

def row17858 : Integer.Sparse Key := [(key2031, -2), (key2036, -2), (key2061, 2), (key2066, 1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 2), (key2155, 1), (key2168, 1), (key2195, 1), (key2201, -1), (key2243, -2), (key2248, -1), (key2255, -1), (key2304, -2), (key2306, 1), (key2311, 1)]

theorem rowCheck17858 : row17858 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17858 := by decide +kernel

theorem rowEval17858 (x : Key → ℝ) : Integer.Sparse.eval row17858 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck17858, Integer.Sparse.eval_collectBalanced, rawRowCheck17858]

def rawRow17859 : Integer.Sparse Key := [(key2195, 2), (key2155, 2), (key2150, 2), (key2306, -1), (key2248, -1), (key2304, -1), (key2155, -1), (key2243, -1), (key2150, -1), (key2093, 2), (key2066, 2), (key2061, 2), (key2311, -1), (key2255, -1), (key2304, -1), (key2066, -1), (key2243, -1), (key2061, -1), (key2096, -1), (key2071, -1), (key2093, -1), (key2036, -1), (key2061, -1), (key2031, -1), (key2201, -1), (key2168, -1), (key2195, -1), (key2036, -1), (key2150, -1), (key2031, -1), (key2311, 2), (key2168, 2), (key2306, 2), (key2071, 2), (key2150, 2), (key2061, 2)]

theorem rawRowCheck17859 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form13 = rawRow17859 := by decide +kernel

def row17859 : Integer.Sparse Key := [(key2031, -2), (key2036, -2), (key2061, 2), (key2066, 1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 2), (key2155, 1), (key2168, 1), (key2195, 1), (key2201, -1), (key2243, -2), (key2248, -1), (key2255, -1), (key2304, -2), (key2306, 1), (key2311, 1)]

theorem rowCheck17859 : row17859 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17859 := by decide +kernel

theorem rowEval17859 (x : Key → ℝ) : Integer.Sparse.eval row17859 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck17859, Integer.Sparse.eval_collectBalanced, rawRowCheck17859]

def rawRow17860 : Integer.Sparse Key := [(key2243, 2), (key2304, 2), (key2304, 2), (key2150, -1), (key2195, -1), (key2150, -1), (key2306, -1), (key2195, -1), (key2306, -1), (key2243, 2), (key2304, 2), (key2304, 2), (key2061, -1), (key2093, -1), (key2061, -1), (key2311, -1), (key2093, -1), (key2311, -1), (key2150, -1), (key2195, -1), (key2150, -1), (key2306, -1), (key2195, -1), (key2306, -1), (key2061, -1), (key2093, -1), (key2061, -1), (key2311, -1), (key2093, -1), (key2311, -1), (key2031, 2), (key2096, 2), (key2031, 2), (key2201, 2), (key2096, 2), (key2201, 2)]

theorem rawRowCheck17860 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form13 = rawRow17860 := by decide +kernel

def row17860 : Integer.Sparse Key := [(key2031, 4), (key2061, -4), (key2093, -4), (key2096, 4), (key2150, -4), (key2195, -4), (key2201, 4), (key2243, 4), (key2304, 8), (key2306, -4), (key2311, -4)]

theorem rowCheck17860 : row17860 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17860 := by decide +kernel

theorem rowEval17860 (x : Key → ℝ) : Integer.Sparse.eval row17860 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form13) x := by
  rw [rowCheck17860, Integer.Sparse.eval_collectBalanced, rawRowCheck17860]

def rawRow17861 : Integer.Sparse Key := [(key2304, 2), (key2243, 2), (key2304, 2), (key2195, -1), (key2150, -1), (key2306, -1), (key2150, -1), (key2306, -1), (key2195, -1), (key2304, 2), (key2243, 2), (key2304, 2), (key2093, -1), (key2061, -1), (key2311, -1), (key2061, -1), (key2311, -1), (key2093, -1), (key2195, -1), (key2150, -1), (key2306, -1), (key2150, -1), (key2306, -1), (key2195, -1), (key2093, -1), (key2061, -1), (key2311, -1), (key2061, -1), (key2311, -1), (key2093, -1), (key2096, 2), (key2031, 2), (key2201, 2), (key2031, 2), (key2201, 2), (key2096, 2)]

theorem rawRowCheck17861 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form13 = rawRow17861 := by decide +kernel

def row17861 : Integer.Sparse Key := [(key2031, 4), (key2061, -4), (key2093, -4), (key2096, 4), (key2150, -4), (key2195, -4), (key2201, 4), (key2243, 4), (key2304, 8), (key2306, -4), (key2311, -4)]

theorem rowCheck17861 : row17861 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17861 := by decide +kernel

theorem rowEval17861 (x : Key → ℝ) : Integer.Sparse.eval row17861 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck17861, Integer.Sparse.eval_collectBalanced, rawRowCheck17861]

def rawRow17862 : Integer.Sparse Key := [(key2304, 2), (key2304, 2), (key2243, 2), (key2306, -1), (key2306, -1), (key2195, -1), (key2195, -1), (key2150, -1), (key2150, -1), (key2304, 2), (key2304, 2), (key2243, 2), (key2311, -1), (key2311, -1), (key2093, -1), (key2093, -1), (key2061, -1), (key2061, -1), (key2306, -1), (key2306, -1), (key2195, -1), (key2195, -1), (key2150, -1), (key2150, -1), (key2311, -1), (key2311, -1), (key2093, -1), (key2093, -1), (key2061, -1), (key2061, -1), (key2201, 2), (key2201, 2), (key2096, 2), (key2096, 2), (key2031, 2), (key2031, 2)]

theorem rawRowCheck17862 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form13 = rawRow17862 := by decide +kernel

def row17862 : Integer.Sparse Key := [(key2031, 4), (key2061, -4), (key2093, -4), (key2096, 4), (key2150, -4), (key2195, -4), (key2201, 4), (key2243, 4), (key2304, 8), (key2306, -4), (key2311, -4)]

theorem rowCheck17862 : row17862 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17862 := by decide +kernel

theorem rowEval17862 (x : Key → ℝ) : Integer.Sparse.eval row17862 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck17862, Integer.Sparse.eval_collectBalanced, rawRowCheck17862]

def rawRow17863 : Integer.Sparse Key := [(key2061, -1), (key2066, -1), (key2061, -1), (key2071, -1), (key2066, -1), (key2071, -1), (key2093, 2), (key2093, 2), (key2096, 2), (key2150, 1), (key2155, 1), (key2150, 1), (key2168, 1), (key2155, 1), (key2168, 1), (key2195, -2), (key2195, -2), (key2201, -2), (key2061, -1), (key2066, -1), (key2061, -1), (key2071, -1), (key2066, -1), (key2071, -1), (key2150, 1), (key2155, 1), (key2150, 1), (key2168, 1), (key2155, 1), (key2168, 1), (key2093, 2), (key2093, 2), (key2096, 2), (key2195, -2), (key2195, -2), (key2201, -2)]

theorem rawRowCheck17863 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form14 = rawRow17863 := by decide +kernel

def row17863 : Integer.Sparse Key := [(key2061, -4), (key2066, -4), (key2071, -4), (key2093, 8), (key2096, 4), (key2150, 4), (key2155, 4), (key2168, 4), (key2195, -8), (key2201, -4)]

theorem rowCheck17863 : row17863 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17863 := by decide +kernel

theorem rowEval17863 (x : Key → ℝ) : Integer.Sparse.eval row17863 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form14) x := by
  rw [rowCheck17863, Integer.Sparse.eval_collectBalanced, rawRowCheck17863]

def rawRow17864 : Integer.Sparse Key := [(key2066, -1), (key2061, -1), (key2071, -1), (key2061, -1), (key2071, -1), (key2066, -1), (key2093, 2), (key2096, 2), (key2093, 2), (key2155, 1), (key2150, 1), (key2168, 1), (key2150, 1), (key2168, 1), (key2155, 1), (key2195, -2), (key2201, -2), (key2195, -2), (key2066, -1), (key2061, -1), (key2071, -1), (key2061, -1), (key2071, -1), (key2066, -1), (key2155, 1), (key2150, 1), (key2168, 1), (key2150, 1), (key2168, 1), (key2155, 1), (key2093, 2), (key2096, 2), (key2093, 2), (key2195, -2), (key2201, -2), (key2195, -2)]

theorem rawRowCheck17864 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form14 = rawRow17864 := by decide +kernel

def row17864 : Integer.Sparse Key := [(key2061, -4), (key2066, -4), (key2071, -4), (key2093, 8), (key2096, 4), (key2150, 4), (key2155, 4), (key2168, 4), (key2195, -8), (key2201, -4)]

theorem rowCheck17864 : row17864 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17864 := by decide +kernel

theorem rowEval17864 (x : Key → ℝ) : Integer.Sparse.eval row17864 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck17864, Integer.Sparse.eval_collectBalanced, rawRowCheck17864]

def rawRow17865 : Integer.Sparse Key := [(key2071, -1), (key2071, -1), (key2066, -1), (key2066, -1), (key2061, -1), (key2061, -1), (key2096, 2), (key2093, 2), (key2093, 2), (key2168, 1), (key2168, 1), (key2155, 1), (key2155, 1), (key2150, 1), (key2150, 1), (key2201, -2), (key2195, -2), (key2195, -2), (key2071, -1), (key2071, -1), (key2066, -1), (key2066, -1), (key2061, -1), (key2061, -1), (key2168, 1), (key2168, 1), (key2155, 1), (key2155, 1), (key2150, 1), (key2150, 1), (key2096, 2), (key2093, 2), (key2093, 2), (key2201, -2), (key2195, -2), (key2195, -2)]

theorem rawRowCheck17865 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form14 = rawRow17865 := by decide +kernel

def row17865 : Integer.Sparse Key := [(key2061, -4), (key2066, -4), (key2071, -4), (key2093, 8), (key2096, 4), (key2150, 4), (key2155, 4), (key2168, 4), (key2195, -8), (key2201, -4)]

theorem rowCheck17865 : row17865 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17865 := by decide +kernel

theorem rowEval17865 (x : Key → ℝ) : Integer.Sparse.eval row17865 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck17865, Integer.Sparse.eval_collectBalanced, rawRowCheck17865]

def rawRow17866 : Integer.Sparse Key := [(key2031, -1), (key2036, -1), (key2061, -1), (key2071, -1), (key2093, -1), (key2096, -1), (key2036, 2), (key2066, 2), (key2071, 2), (key2031, 1), (key2036, 1), (key2150, 1), (key2168, 1), (key2195, 1), (key2201, 1), (key2036, -2), (key2155, -2), (key2168, -2), (key2150, -1), (key2155, -1), (key2243, -1), (key2248, -1), (key2304, -1), (key2306, -1), (key2061, 1), (key2066, 1), (key2243, 1), (key2255, 1), (key2304, 1), (key2311, 1), (key2195, 2), (key2304, 2), (key2306, 2), (key2093, -2), (key2304, -2), (key2311, -2)]

theorem rawRowCheck17866 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form14 = rawRow17866 := by decide +kernel

def row17866 : Integer.Sparse Key := [(key2066, 3), (key2071, 1), (key2093, -3), (key2096, -1), (key2155, -3), (key2168, -1), (key2195, 3), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

theorem rowCheck17866 : row17866 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17866 := by decide +kernel

theorem rowEval17866 (x : Key → ℝ) : Integer.Sparse.eval row17866 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form14) x := by
  rw [rowCheck17866, Integer.Sparse.eval_collectBalanced, rawRowCheck17866]

def rawRow17867 : Integer.Sparse Key := [(key2036, -1), (key2031, -1), (key2071, -1), (key2061, -1), (key2096, -1), (key2093, -1), (key2036, 2), (key2071, 2), (key2066, 2), (key2036, 1), (key2031, 1), (key2168, 1), (key2150, 1), (key2201, 1), (key2195, 1), (key2036, -2), (key2168, -2), (key2155, -2), (key2155, -1), (key2150, -1), (key2248, -1), (key2243, -1), (key2306, -1), (key2304, -1), (key2066, 1), (key2061, 1), (key2255, 1), (key2243, 1), (key2311, 1), (key2304, 1), (key2195, 2), (key2306, 2), (key2304, 2), (key2093, -2), (key2311, -2), (key2304, -2)]

theorem rawRowCheck17867 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form14 = rawRow17867 := by decide +kernel

def row17867 : Integer.Sparse Key := [(key2066, 3), (key2071, 1), (key2093, -3), (key2096, -1), (key2155, -3), (key2168, -1), (key2195, 3), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

theorem rowCheck17867 : row17867 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17867 := by decide +kernel

theorem rowEval17867 (x : Key → ℝ) : Integer.Sparse.eval row17867 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck17867, Integer.Sparse.eval_collectBalanced, rawRowCheck17867]

def rawRow17868 : Integer.Sparse Key := [(key2061, -1), (key2093, -1), (key2031, -1), (key2096, -1), (key2036, -1), (key2071, -1), (key2066, 2), (key2036, 2), (key2071, 2), (key2150, 1), (key2195, 1), (key2031, 1), (key2201, 1), (key2036, 1), (key2168, 1), (key2155, -2), (key2036, -2), (key2168, -2), (key2243, -1), (key2304, -1), (key2150, -1), (key2306, -1), (key2155, -1), (key2248, -1), (key2243, 1), (key2304, 1), (key2061, 1), (key2311, 1), (key2066, 1), (key2255, 1), (key2304, 2), (key2195, 2), (key2306, 2), (key2304, -2), (key2093, -2), (key2311, -2)]

theorem rawRowCheck17868 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form14 = rawRow17868 := by decide +kernel

def row17868 : Integer.Sparse Key := [(key2066, 3), (key2071, 1), (key2093, -3), (key2096, -1), (key2155, -3), (key2168, -1), (key2195, 3), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

theorem rowCheck17868 : row17868 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17868 := by decide +kernel

theorem rowEval17868 (x : Key → ℝ) : Integer.Sparse.eval row17868 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form14) x := by
  rw [rowCheck17868, Integer.Sparse.eval_collectBalanced, rawRowCheck17868]

def rawRow17869 : Integer.Sparse Key := [(key2093, -1), (key2061, -1), (key2096, -1), (key2031, -1), (key2071, -1), (key2036, -1), (key2066, 2), (key2071, 2), (key2036, 2), (key2195, 1), (key2150, 1), (key2201, 1), (key2031, 1), (key2168, 1), (key2036, 1), (key2155, -2), (key2168, -2), (key2036, -2), (key2304, -1), (key2243, -1), (key2306, -1), (key2150, -1), (key2248, -1), (key2155, -1), (key2304, 1), (key2243, 1), (key2311, 1), (key2061, 1), (key2255, 1), (key2066, 1), (key2304, 2), (key2306, 2), (key2195, 2), (key2304, -2), (key2311, -2), (key2093, -2)]

theorem rawRowCheck17869 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form14 = rawRow17869 := by decide +kernel

def row17869 : Integer.Sparse Key := [(key2066, 3), (key2071, 1), (key2093, -3), (key2096, -1), (key2155, -3), (key2168, -1), (key2195, 3), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

theorem rowCheck17869 : row17869 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17869 := by decide +kernel

theorem rowEval17869 (x : Key → ℝ) : Integer.Sparse.eval row17869 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck17869, Integer.Sparse.eval_collectBalanced, rawRowCheck17869]

def rawRow17870 : Integer.Sparse Key := [(key2071, -1), (key2096, -1), (key2036, -1), (key2093, -1), (key2031, -1), (key2061, -1), (key2071, 2), (key2036, 2), (key2066, 2), (key2168, 1), (key2201, 1), (key2036, 1), (key2195, 1), (key2031, 1), (key2150, 1), (key2168, -2), (key2036, -2), (key2155, -2), (key2248, -1), (key2306, -1), (key2155, -1), (key2304, -1), (key2150, -1), (key2243, -1), (key2255, 1), (key2311, 1), (key2066, 1), (key2304, 1), (key2061, 1), (key2243, 1), (key2306, 2), (key2195, 2), (key2304, 2), (key2311, -2), (key2093, -2), (key2304, -2)]

theorem rawRowCheck17870 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form14 = rawRow17870 := by decide +kernel

def row17870 : Integer.Sparse Key := [(key2066, 3), (key2071, 1), (key2093, -3), (key2096, -1), (key2155, -3), (key2168, -1), (key2195, 3), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

theorem rowCheck17870 : row17870 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17870 := by decide +kernel

theorem rowEval17870 (x : Key → ℝ) : Integer.Sparse.eval row17870 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck17870, Integer.Sparse.eval_collectBalanced, rawRowCheck17870]

def rawRow17871 : Integer.Sparse Key := [(key2096, -1), (key2071, -1), (key2093, -1), (key2036, -1), (key2061, -1), (key2031, -1), (key2071, 2), (key2066, 2), (key2036, 2), (key2201, 1), (key2168, 1), (key2195, 1), (key2036, 1), (key2150, 1), (key2031, 1), (key2168, -2), (key2155, -2), (key2036, -2), (key2306, -1), (key2248, -1), (key2304, -1), (key2155, -1), (key2243, -1), (key2150, -1), (key2311, 1), (key2255, 1), (key2304, 1), (key2066, 1), (key2243, 1), (key2061, 1), (key2306, 2), (key2304, 2), (key2195, 2), (key2311, -2), (key2304, -2), (key2093, -2)]

theorem rawRowCheck17871 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form14 = rawRow17871 := by decide +kernel

def row17871 : Integer.Sparse Key := [(key2066, 3), (key2071, 1), (key2093, -3), (key2096, -1), (key2155, -3), (key2168, -1), (key2195, 3), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

theorem rowCheck17871 : row17871 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17871 := by decide +kernel

theorem rowEval17871 (x : Key → ℝ) : Integer.Sparse.eval row17871 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck17871, Integer.Sparse.eval_collectBalanced, rawRowCheck17871]

def rawRow17872 : Integer.Sparse Key := [(key2150, -1), (key2155, -1), (key2243, -1), (key2248, -1), (key2304, -1), (key2306, -1), (key2195, 2), (key2304, 2), (key2306, 2), (key2061, 1), (key2066, 1), (key2243, 1), (key2255, 1), (key2304, 1), (key2311, 1), (key2093, -2), (key2304, -2), (key2311, -2), (key2031, -1), (key2036, -1), (key2061, -1), (key2071, -1), (key2093, -1), (key2096, -1), (key2031, 1), (key2036, 1), (key2150, 1), (key2168, 1), (key2195, 1), (key2201, 1), (key2036, 2), (key2066, 2), (key2071, 2), (key2036, -2), (key2155, -2), (key2168, -2)]

theorem rawRowCheck17872 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form14 = rawRow17872 := by decide +kernel

def row17872 : Integer.Sparse Key := [(key2066, 3), (key2071, 1), (key2093, -3), (key2096, -1), (key2155, -3), (key2168, -1), (key2195, 3), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

theorem rowCheck17872 : row17872 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17872 := by decide +kernel

theorem rowEval17872 (x : Key → ℝ) : Integer.Sparse.eval row17872 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form14) x := by
  rw [rowCheck17872, Integer.Sparse.eval_collectBalanced, rawRowCheck17872]

def rawRow17873 : Integer.Sparse Key := [(key2155, -1), (key2150, -1), (key2248, -1), (key2243, -1), (key2306, -1), (key2304, -1), (key2195, 2), (key2306, 2), (key2304, 2), (key2066, 1), (key2061, 1), (key2255, 1), (key2243, 1), (key2311, 1), (key2304, 1), (key2093, -2), (key2311, -2), (key2304, -2), (key2036, -1), (key2031, -1), (key2071, -1), (key2061, -1), (key2096, -1), (key2093, -1), (key2036, 1), (key2031, 1), (key2168, 1), (key2150, 1), (key2201, 1), (key2195, 1), (key2036, 2), (key2071, 2), (key2066, 2), (key2036, -2), (key2168, -2), (key2155, -2)]

theorem rawRowCheck17873 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form14 = rawRow17873 := by decide +kernel

def row17873 : Integer.Sparse Key := [(key2066, 3), (key2071, 1), (key2093, -3), (key2096, -1), (key2155, -3), (key2168, -1), (key2195, 3), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

theorem rowCheck17873 : row17873 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17873 := by decide +kernel

theorem rowEval17873 (x : Key → ℝ) : Integer.Sparse.eval row17873 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck17873, Integer.Sparse.eval_collectBalanced, rawRowCheck17873]

def rawRow17874 : Integer.Sparse Key := [(key2243, -1), (key2304, -1), (key2150, -1), (key2306, -1), (key2155, -1), (key2248, -1), (key2304, 2), (key2195, 2), (key2306, 2), (key2243, 1), (key2304, 1), (key2061, 1), (key2311, 1), (key2066, 1), (key2255, 1), (key2304, -2), (key2093, -2), (key2311, -2), (key2061, -1), (key2093, -1), (key2031, -1), (key2096, -1), (key2036, -1), (key2071, -1), (key2150, 1), (key2195, 1), (key2031, 1), (key2201, 1), (key2036, 1), (key2168, 1), (key2066, 2), (key2036, 2), (key2071, 2), (key2155, -2), (key2036, -2), (key2168, -2)]

theorem rawRowCheck17874 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form14 = rawRow17874 := by decide +kernel

def row17874 : Integer.Sparse Key := [(key2066, 3), (key2071, 1), (key2093, -3), (key2096, -1), (key2155, -3), (key2168, -1), (key2195, 3), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

theorem rowCheck17874 : row17874 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17874 := by decide +kernel

theorem rowEval17874 (x : Key → ℝ) : Integer.Sparse.eval row17874 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form14) x := by
  rw [rowCheck17874, Integer.Sparse.eval_collectBalanced, rawRowCheck17874]

def rawRow17875 : Integer.Sparse Key := [(key2304, -1), (key2243, -1), (key2306, -1), (key2150, -1), (key2248, -1), (key2155, -1), (key2304, 2), (key2306, 2), (key2195, 2), (key2304, 1), (key2243, 1), (key2311, 1), (key2061, 1), (key2255, 1), (key2066, 1), (key2304, -2), (key2311, -2), (key2093, -2), (key2093, -1), (key2061, -1), (key2096, -1), (key2031, -1), (key2071, -1), (key2036, -1), (key2195, 1), (key2150, 1), (key2201, 1), (key2031, 1), (key2168, 1), (key2036, 1), (key2066, 2), (key2071, 2), (key2036, 2), (key2155, -2), (key2168, -2), (key2036, -2)]

theorem rawRowCheck17875 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form14 = rawRow17875 := by decide +kernel

def row17875 : Integer.Sparse Key := [(key2066, 3), (key2071, 1), (key2093, -3), (key2096, -1), (key2155, -3), (key2168, -1), (key2195, 3), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

theorem rowCheck17875 : row17875 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17875 := by decide +kernel

theorem rowEval17875 (x : Key → ℝ) : Integer.Sparse.eval row17875 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck17875, Integer.Sparse.eval_collectBalanced, rawRowCheck17875]

def rawRow17876 : Integer.Sparse Key := [(key2248, -1), (key2306, -1), (key2155, -1), (key2304, -1), (key2150, -1), (key2243, -1), (key2306, 2), (key2195, 2), (key2304, 2), (key2255, 1), (key2311, 1), (key2066, 1), (key2304, 1), (key2061, 1), (key2243, 1), (key2311, -2), (key2093, -2), (key2304, -2), (key2071, -1), (key2096, -1), (key2036, -1), (key2093, -1), (key2031, -1), (key2061, -1), (key2168, 1), (key2201, 1), (key2036, 1), (key2195, 1), (key2031, 1), (key2150, 1), (key2071, 2), (key2036, 2), (key2066, 2), (key2168, -2), (key2036, -2), (key2155, -2)]

theorem rawRowCheck17876 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form14 = rawRow17876 := by decide +kernel

def row17876 : Integer.Sparse Key := [(key2066, 3), (key2071, 1), (key2093, -3), (key2096, -1), (key2155, -3), (key2168, -1), (key2195, 3), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

theorem rowCheck17876 : row17876 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17876 := by decide +kernel

theorem rowEval17876 (x : Key → ℝ) : Integer.Sparse.eval row17876 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck17876, Integer.Sparse.eval_collectBalanced, rawRowCheck17876]

def rawRow17877 : Integer.Sparse Key := [(key2306, -1), (key2248, -1), (key2304, -1), (key2155, -1), (key2243, -1), (key2150, -1), (key2306, 2), (key2304, 2), (key2195, 2), (key2311, 1), (key2255, 1), (key2304, 1), (key2066, 1), (key2243, 1), (key2061, 1), (key2311, -2), (key2304, -2), (key2093, -2), (key2096, -1), (key2071, -1), (key2093, -1), (key2036, -1), (key2061, -1), (key2031, -1), (key2201, 1), (key2168, 1), (key2195, 1), (key2036, 1), (key2150, 1), (key2031, 1), (key2071, 2), (key2066, 2), (key2036, 2), (key2168, -2), (key2155, -2), (key2036, -2)]

theorem rawRowCheck17877 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form14 = rawRow17877 := by decide +kernel

def row17877 : Integer.Sparse Key := [(key2066, 3), (key2071, 1), (key2093, -3), (key2096, -1), (key2155, -3), (key2168, -1), (key2195, 3), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

theorem rowCheck17877 : row17877 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17877 := by decide +kernel

theorem rowEval17877 (x : Key → ℝ) : Integer.Sparse.eval row17877 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck17877, Integer.Sparse.eval_collectBalanced, rawRowCheck17877]

def rawRow17878 : Integer.Sparse Key := [(key2150, -1), (key2195, -1), (key2150, -1), (key2306, -1), (key2195, -1), (key2306, -1), (key2155, 2), (key2155, 2), (key2248, 2), (key2061, 1), (key2093, 1), (key2061, 1), (key2311, 1), (key2093, 1), (key2311, 1), (key2066, -2), (key2066, -2), (key2255, -2), (key2150, -1), (key2195, -1), (key2150, -1), (key2306, -1), (key2195, -1), (key2306, -1), (key2061, 1), (key2093, 1), (key2061, 1), (key2311, 1), (key2093, 1), (key2311, 1), (key2155, 2), (key2155, 2), (key2248, 2), (key2066, -2), (key2066, -2), (key2255, -2)]

theorem rawRowCheck17878 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form14 = rawRow17878 := by decide +kernel

def row17878 : Integer.Sparse Key := [(key2061, 4), (key2066, -8), (key2093, 4), (key2150, -4), (key2155, 8), (key2195, -4), (key2248, 4), (key2255, -4), (key2306, -4), (key2311, 4)]

theorem rowCheck17878 : row17878 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17878 := by decide +kernel

theorem rowEval17878 (x : Key → ℝ) : Integer.Sparse.eval row17878 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form14) x := by
  rw [rowCheck17878, Integer.Sparse.eval_collectBalanced, rawRowCheck17878]

def rawRow17879 : Integer.Sparse Key := [(key2195, -1), (key2150, -1), (key2306, -1), (key2150, -1), (key2306, -1), (key2195, -1), (key2155, 2), (key2248, 2), (key2155, 2), (key2093, 1), (key2061, 1), (key2311, 1), (key2061, 1), (key2311, 1), (key2093, 1), (key2066, -2), (key2255, -2), (key2066, -2), (key2195, -1), (key2150, -1), (key2306, -1), (key2150, -1), (key2306, -1), (key2195, -1), (key2093, 1), (key2061, 1), (key2311, 1), (key2061, 1), (key2311, 1), (key2093, 1), (key2155, 2), (key2248, 2), (key2155, 2), (key2066, -2), (key2255, -2), (key2066, -2)]

theorem rawRowCheck17879 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form14 = rawRow17879 := by decide +kernel

def row17879 : Integer.Sparse Key := [(key2061, 4), (key2066, -8), (key2093, 4), (key2150, -4), (key2155, 8), (key2195, -4), (key2248, 4), (key2255, -4), (key2306, -4), (key2311, 4)]

theorem rowCheck17879 : row17879 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17879 := by decide +kernel

theorem rowEval17879 (x : Key → ℝ) : Integer.Sparse.eval row17879 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck17879, Integer.Sparse.eval_collectBalanced, rawRowCheck17879]

def rawRow17880 : Integer.Sparse Key := [(key2306, -1), (key2306, -1), (key2195, -1), (key2195, -1), (key2150, -1), (key2150, -1), (key2248, 2), (key2155, 2), (key2155, 2), (key2311, 1), (key2311, 1), (key2093, 1), (key2093, 1), (key2061, 1), (key2061, 1), (key2255, -2), (key2066, -2), (key2066, -2), (key2306, -1), (key2306, -1), (key2195, -1), (key2195, -1), (key2150, -1), (key2150, -1), (key2311, 1), (key2311, 1), (key2093, 1), (key2093, 1), (key2061, 1), (key2061, 1), (key2248, 2), (key2155, 2), (key2155, 2), (key2255, -2), (key2066, -2), (key2066, -2)]

theorem rawRowCheck17880 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form14 = rawRow17880 := by decide +kernel

def row17880 : Integer.Sparse Key := [(key2061, 4), (key2066, -8), (key2093, 4), (key2150, -4), (key2155, 8), (key2195, -4), (key2248, 4), (key2255, -4), (key2306, -4), (key2311, 4)]

theorem rowCheck17880 : row17880 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17880 := by decide +kernel

theorem rowEval17880 (x : Key → ℝ) : Integer.Sparse.eval row17880 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck17880, Integer.Sparse.eval_collectBalanced, rawRowCheck17880]

def rawRow17881 : Integer.Sparse Key := [(key2061, -1), (key2064, -1), (key2061, -1), (key2070, -1), (key2064, -1), (key2070, -1), (key2080, 2), (key2080, 2), (key2086, 2), (key2150, 1), (key2153, 1), (key2150, 1), (key2167, 1), (key2153, 1), (key2167, 1), (key2177, -2), (key2177, -2), (key2188, -2), (key2061, -1), (key2064, -1), (key2061, -1), (key2070, -1), (key2064, -1), (key2070, -1), (key2150, 1), (key2153, 1), (key2150, 1), (key2167, 1), (key2153, 1), (key2167, 1), (key2080, 2), (key2080, 2), (key2086, 2), (key2177, -2), (key2177, -2), (key2188, -2)]

theorem rawRowCheck17881 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form15 = rawRow17881 := by decide +kernel

def row17881 : Integer.Sparse Key := [(key2061, -4), (key2064, -4), (key2070, -4), (key2080, 8), (key2086, 4), (key2150, 4), (key2153, 4), (key2167, 4), (key2177, -8), (key2188, -4)]

theorem rowCheck17881 : row17881 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17881 := by decide +kernel

theorem rowEval17881 (x : Key → ℝ) : Integer.Sparse.eval row17881 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form15) x := by
  rw [rowCheck17881, Integer.Sparse.eval_collectBalanced, rawRowCheck17881]

def rawRow17882 : Integer.Sparse Key := [(key2064, -1), (key2061, -1), (key2070, -1), (key2061, -1), (key2070, -1), (key2064, -1), (key2080, 2), (key2086, 2), (key2080, 2), (key2153, 1), (key2150, 1), (key2167, 1), (key2150, 1), (key2167, 1), (key2153, 1), (key2177, -2), (key2188, -2), (key2177, -2), (key2064, -1), (key2061, -1), (key2070, -1), (key2061, -1), (key2070, -1), (key2064, -1), (key2153, 1), (key2150, 1), (key2167, 1), (key2150, 1), (key2167, 1), (key2153, 1), (key2080, 2), (key2086, 2), (key2080, 2), (key2177, -2), (key2188, -2), (key2177, -2)]

theorem rawRowCheck17882 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form15 = rawRow17882 := by decide +kernel

def row17882 : Integer.Sparse Key := [(key2061, -4), (key2064, -4), (key2070, -4), (key2080, 8), (key2086, 4), (key2150, 4), (key2153, 4), (key2167, 4), (key2177, -8), (key2188, -4)]

theorem rowCheck17882 : row17882 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17882 := by decide +kernel

theorem rowEval17882 (x : Key → ℝ) : Integer.Sparse.eval row17882 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck17882, Integer.Sparse.eval_collectBalanced, rawRowCheck17882]

def rawRow17883 : Integer.Sparse Key := [(key2070, -1), (key2070, -1), (key2064, -1), (key2064, -1), (key2061, -1), (key2061, -1), (key2086, 2), (key2080, 2), (key2080, 2), (key2167, 1), (key2167, 1), (key2153, 1), (key2153, 1), (key2150, 1), (key2150, 1), (key2188, -2), (key2177, -2), (key2177, -2), (key2070, -1), (key2070, -1), (key2064, -1), (key2064, -1), (key2061, -1), (key2061, -1), (key2167, 1), (key2167, 1), (key2153, 1), (key2153, 1), (key2150, 1), (key2150, 1), (key2086, 2), (key2080, 2), (key2080, 2), (key2188, -2), (key2177, -2), (key2177, -2)]

theorem rawRowCheck17883 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form15 = rawRow17883 := by decide +kernel

def row17883 : Integer.Sparse Key := [(key2061, -4), (key2064, -4), (key2070, -4), (key2080, 8), (key2086, 4), (key2150, 4), (key2153, 4), (key2167, 4), (key2177, -8), (key2188, -4)]

theorem rowCheck17883 : row17883 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17883 := by decide +kernel

theorem rowEval17883 (x : Key → ℝ) : Integer.Sparse.eval row17883 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck17883, Integer.Sparse.eval_collectBalanced, rawRowCheck17883]

def rawRow17884 : Integer.Sparse Key := [(key2031, -1), (key2034, -1), (key2061, -1), (key2070, -1), (key2080, -1), (key2086, -1), (key2034, 2), (key2064, 2), (key2070, 2), (key2031, 1), (key2034, 1), (key2150, 1), (key2167, 1), (key2177, 1), (key2188, 1), (key2034, -2), (key2153, -2), (key2167, -2), (key2150, -1), (key2153, -1), (key2243, -1), (key2247, -1), (key2277, -1), (key2280, -1), (key2061, 1), (key2064, 1), (key2243, 1), (key2254, 1), (key2277, 1), (key2288, 1), (key2177, 2), (key2277, 2), (key2280, 2), (key2080, -2), (key2277, -2), (key2288, -2)]

theorem rawRowCheck17884 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form15 = rawRow17884 := by decide +kernel

def row17884 : Integer.Sparse Key := [(key2064, 3), (key2070, 1), (key2080, -3), (key2086, -1), (key2153, -3), (key2167, -1), (key2177, 3), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

theorem rowCheck17884 : row17884 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17884 := by decide +kernel

theorem rowEval17884 (x : Key → ℝ) : Integer.Sparse.eval row17884 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form15) x := by
  rw [rowCheck17884, Integer.Sparse.eval_collectBalanced, rawRowCheck17884]

def rawRow17885 : Integer.Sparse Key := [(key2034, -1), (key2031, -1), (key2070, -1), (key2061, -1), (key2086, -1), (key2080, -1), (key2034, 2), (key2070, 2), (key2064, 2), (key2034, 1), (key2031, 1), (key2167, 1), (key2150, 1), (key2188, 1), (key2177, 1), (key2034, -2), (key2167, -2), (key2153, -2), (key2153, -1), (key2150, -1), (key2247, -1), (key2243, -1), (key2280, -1), (key2277, -1), (key2064, 1), (key2061, 1), (key2254, 1), (key2243, 1), (key2288, 1), (key2277, 1), (key2177, 2), (key2280, 2), (key2277, 2), (key2080, -2), (key2288, -2), (key2277, -2)]

theorem rawRowCheck17885 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form15 = rawRow17885 := by decide +kernel

def row17885 : Integer.Sparse Key := [(key2064, 3), (key2070, 1), (key2080, -3), (key2086, -1), (key2153, -3), (key2167, -1), (key2177, 3), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

theorem rowCheck17885 : row17885 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17885 := by decide +kernel

theorem rowEval17885 (x : Key → ℝ) : Integer.Sparse.eval row17885 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck17885, Integer.Sparse.eval_collectBalanced, rawRowCheck17885]

def rawRow17886 : Integer.Sparse Key := [(key2061, -1), (key2080, -1), (key2031, -1), (key2086, -1), (key2034, -1), (key2070, -1), (key2064, 2), (key2034, 2), (key2070, 2), (key2150, 1), (key2177, 1), (key2031, 1), (key2188, 1), (key2034, 1), (key2167, 1), (key2153, -2), (key2034, -2), (key2167, -2), (key2243, -1), (key2277, -1), (key2150, -1), (key2280, -1), (key2153, -1), (key2247, -1), (key2243, 1), (key2277, 1), (key2061, 1), (key2288, 1), (key2064, 1), (key2254, 1), (key2277, 2), (key2177, 2), (key2280, 2), (key2277, -2), (key2080, -2), (key2288, -2)]

theorem rawRowCheck17886 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form15 = rawRow17886 := by decide +kernel

def row17886 : Integer.Sparse Key := [(key2064, 3), (key2070, 1), (key2080, -3), (key2086, -1), (key2153, -3), (key2167, -1), (key2177, 3), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

theorem rowCheck17886 : row17886 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17886 := by decide +kernel

theorem rowEval17886 (x : Key → ℝ) : Integer.Sparse.eval row17886 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form15) x := by
  rw [rowCheck17886, Integer.Sparse.eval_collectBalanced, rawRowCheck17886]

def rawRow17887 : Integer.Sparse Key := [(key2080, -1), (key2061, -1), (key2086, -1), (key2031, -1), (key2070, -1), (key2034, -1), (key2064, 2), (key2070, 2), (key2034, 2), (key2177, 1), (key2150, 1), (key2188, 1), (key2031, 1), (key2167, 1), (key2034, 1), (key2153, -2), (key2167, -2), (key2034, -2), (key2277, -1), (key2243, -1), (key2280, -1), (key2150, -1), (key2247, -1), (key2153, -1), (key2277, 1), (key2243, 1), (key2288, 1), (key2061, 1), (key2254, 1), (key2064, 1), (key2277, 2), (key2280, 2), (key2177, 2), (key2277, -2), (key2288, -2), (key2080, -2)]

theorem rawRowCheck17887 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form15 = rawRow17887 := by decide +kernel

def row17887 : Integer.Sparse Key := [(key2064, 3), (key2070, 1), (key2080, -3), (key2086, -1), (key2153, -3), (key2167, -1), (key2177, 3), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

theorem rowCheck17887 : row17887 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17887 := by decide +kernel

theorem rowEval17887 (x : Key → ℝ) : Integer.Sparse.eval row17887 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck17887, Integer.Sparse.eval_collectBalanced, rawRowCheck17887]

def rawRow17888 : Integer.Sparse Key := [(key2070, -1), (key2086, -1), (key2034, -1), (key2080, -1), (key2031, -1), (key2061, -1), (key2070, 2), (key2034, 2), (key2064, 2), (key2167, 1), (key2188, 1), (key2034, 1), (key2177, 1), (key2031, 1), (key2150, 1), (key2167, -2), (key2034, -2), (key2153, -2), (key2247, -1), (key2280, -1), (key2153, -1), (key2277, -1), (key2150, -1), (key2243, -1), (key2254, 1), (key2288, 1), (key2064, 1), (key2277, 1), (key2061, 1), (key2243, 1), (key2280, 2), (key2177, 2), (key2277, 2), (key2288, -2), (key2080, -2), (key2277, -2)]

theorem rawRowCheck17888 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form15 = rawRow17888 := by decide +kernel

def row17888 : Integer.Sparse Key := [(key2064, 3), (key2070, 1), (key2080, -3), (key2086, -1), (key2153, -3), (key2167, -1), (key2177, 3), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

theorem rowCheck17888 : row17888 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17888 := by decide +kernel

theorem rowEval17888 (x : Key → ℝ) : Integer.Sparse.eval row17888 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck17888, Integer.Sparse.eval_collectBalanced, rawRowCheck17888]

def rawRow17889 : Integer.Sparse Key := [(key2086, -1), (key2070, -1), (key2080, -1), (key2034, -1), (key2061, -1), (key2031, -1), (key2070, 2), (key2064, 2), (key2034, 2), (key2188, 1), (key2167, 1), (key2177, 1), (key2034, 1), (key2150, 1), (key2031, 1), (key2167, -2), (key2153, -2), (key2034, -2), (key2280, -1), (key2247, -1), (key2277, -1), (key2153, -1), (key2243, -1), (key2150, -1), (key2288, 1), (key2254, 1), (key2277, 1), (key2064, 1), (key2243, 1), (key2061, 1), (key2280, 2), (key2277, 2), (key2177, 2), (key2288, -2), (key2277, -2), (key2080, -2)]

theorem rawRowCheck17889 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form15 = rawRow17889 := by decide +kernel

def row17889 : Integer.Sparse Key := [(key2064, 3), (key2070, 1), (key2080, -3), (key2086, -1), (key2153, -3), (key2167, -1), (key2177, 3), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

theorem rowCheck17889 : row17889 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17889 := by decide +kernel

theorem rowEval17889 (x : Key → ℝ) : Integer.Sparse.eval row17889 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck17889, Integer.Sparse.eval_collectBalanced, rawRowCheck17889]

def rawRow17890 : Integer.Sparse Key := [(key2150, -1), (key2153, -1), (key2243, -1), (key2247, -1), (key2277, -1), (key2280, -1), (key2177, 2), (key2277, 2), (key2280, 2), (key2061, 1), (key2064, 1), (key2243, 1), (key2254, 1), (key2277, 1), (key2288, 1), (key2080, -2), (key2277, -2), (key2288, -2), (key2031, -1), (key2034, -1), (key2061, -1), (key2070, -1), (key2080, -1), (key2086, -1), (key2031, 1), (key2034, 1), (key2150, 1), (key2167, 1), (key2177, 1), (key2188, 1), (key2034, 2), (key2064, 2), (key2070, 2), (key2034, -2), (key2153, -2), (key2167, -2)]

theorem rawRowCheck17890 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form15 = rawRow17890 := by decide +kernel

def row17890 : Integer.Sparse Key := [(key2064, 3), (key2070, 1), (key2080, -3), (key2086, -1), (key2153, -3), (key2167, -1), (key2177, 3), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

theorem rowCheck17890 : row17890 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17890 := by decide +kernel

theorem rowEval17890 (x : Key → ℝ) : Integer.Sparse.eval row17890 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form15) x := by
  rw [rowCheck17890, Integer.Sparse.eval_collectBalanced, rawRowCheck17890]

def rawRow17891 : Integer.Sparse Key := [(key2153, -1), (key2150, -1), (key2247, -1), (key2243, -1), (key2280, -1), (key2277, -1), (key2177, 2), (key2280, 2), (key2277, 2), (key2064, 1), (key2061, 1), (key2254, 1), (key2243, 1), (key2288, 1), (key2277, 1), (key2080, -2), (key2288, -2), (key2277, -2), (key2034, -1), (key2031, -1), (key2070, -1), (key2061, -1), (key2086, -1), (key2080, -1), (key2034, 1), (key2031, 1), (key2167, 1), (key2150, 1), (key2188, 1), (key2177, 1), (key2034, 2), (key2070, 2), (key2064, 2), (key2034, -2), (key2167, -2), (key2153, -2)]

theorem rawRowCheck17891 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form15 = rawRow17891 := by decide +kernel

def row17891 : Integer.Sparse Key := [(key2064, 3), (key2070, 1), (key2080, -3), (key2086, -1), (key2153, -3), (key2167, -1), (key2177, 3), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

theorem rowCheck17891 : row17891 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17891 := by decide +kernel

theorem rowEval17891 (x : Key → ℝ) : Integer.Sparse.eval row17891 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck17891, Integer.Sparse.eval_collectBalanced, rawRowCheck17891]

def rawRow17892 : Integer.Sparse Key := [(key2243, -1), (key2277, -1), (key2150, -1), (key2280, -1), (key2153, -1), (key2247, -1), (key2277, 2), (key2177, 2), (key2280, 2), (key2243, 1), (key2277, 1), (key2061, 1), (key2288, 1), (key2064, 1), (key2254, 1), (key2277, -2), (key2080, -2), (key2288, -2), (key2061, -1), (key2080, -1), (key2031, -1), (key2086, -1), (key2034, -1), (key2070, -1), (key2150, 1), (key2177, 1), (key2031, 1), (key2188, 1), (key2034, 1), (key2167, 1), (key2064, 2), (key2034, 2), (key2070, 2), (key2153, -2), (key2034, -2), (key2167, -2)]

theorem rawRowCheck17892 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form15 = rawRow17892 := by decide +kernel

def row17892 : Integer.Sparse Key := [(key2064, 3), (key2070, 1), (key2080, -3), (key2086, -1), (key2153, -3), (key2167, -1), (key2177, 3), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

theorem rowCheck17892 : row17892 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17892 := by decide +kernel

theorem rowEval17892 (x : Key → ℝ) : Integer.Sparse.eval row17892 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form15) x := by
  rw [rowCheck17892, Integer.Sparse.eval_collectBalanced, rawRowCheck17892]

def rawRow17893 : Integer.Sparse Key := [(key2277, -1), (key2243, -1), (key2280, -1), (key2150, -1), (key2247, -1), (key2153, -1), (key2277, 2), (key2280, 2), (key2177, 2), (key2277, 1), (key2243, 1), (key2288, 1), (key2061, 1), (key2254, 1), (key2064, 1), (key2277, -2), (key2288, -2), (key2080, -2), (key2080, -1), (key2061, -1), (key2086, -1), (key2031, -1), (key2070, -1), (key2034, -1), (key2177, 1), (key2150, 1), (key2188, 1), (key2031, 1), (key2167, 1), (key2034, 1), (key2064, 2), (key2070, 2), (key2034, 2), (key2153, -2), (key2167, -2), (key2034, -2)]

theorem rawRowCheck17893 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form15 = rawRow17893 := by decide +kernel

def row17893 : Integer.Sparse Key := [(key2064, 3), (key2070, 1), (key2080, -3), (key2086, -1), (key2153, -3), (key2167, -1), (key2177, 3), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

theorem rowCheck17893 : row17893 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17893 := by decide +kernel

theorem rowEval17893 (x : Key → ℝ) : Integer.Sparse.eval row17893 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck17893, Integer.Sparse.eval_collectBalanced, rawRowCheck17893]

def rawRow17894 : Integer.Sparse Key := [(key2247, -1), (key2280, -1), (key2153, -1), (key2277, -1), (key2150, -1), (key2243, -1), (key2280, 2), (key2177, 2), (key2277, 2), (key2254, 1), (key2288, 1), (key2064, 1), (key2277, 1), (key2061, 1), (key2243, 1), (key2288, -2), (key2080, -2), (key2277, -2), (key2070, -1), (key2086, -1), (key2034, -1), (key2080, -1), (key2031, -1), (key2061, -1), (key2167, 1), (key2188, 1), (key2034, 1), (key2177, 1), (key2031, 1), (key2150, 1), (key2070, 2), (key2034, 2), (key2064, 2), (key2167, -2), (key2034, -2), (key2153, -2)]

theorem rawRowCheck17894 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form15 = rawRow17894 := by decide +kernel

def row17894 : Integer.Sparse Key := [(key2064, 3), (key2070, 1), (key2080, -3), (key2086, -1), (key2153, -3), (key2167, -1), (key2177, 3), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

theorem rowCheck17894 : row17894 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17894 := by decide +kernel

theorem rowEval17894 (x : Key → ℝ) : Integer.Sparse.eval row17894 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck17894, Integer.Sparse.eval_collectBalanced, rawRowCheck17894]

def rawRow17895 : Integer.Sparse Key := [(key2280, -1), (key2247, -1), (key2277, -1), (key2153, -1), (key2243, -1), (key2150, -1), (key2280, 2), (key2277, 2), (key2177, 2), (key2288, 1), (key2254, 1), (key2277, 1), (key2064, 1), (key2243, 1), (key2061, 1), (key2288, -2), (key2277, -2), (key2080, -2), (key2086, -1), (key2070, -1), (key2080, -1), (key2034, -1), (key2061, -1), (key2031, -1), (key2188, 1), (key2167, 1), (key2177, 1), (key2034, 1), (key2150, 1), (key2031, 1), (key2070, 2), (key2064, 2), (key2034, 2), (key2167, -2), (key2153, -2), (key2034, -2)]

theorem rawRowCheck17895 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form15 = rawRow17895 := by decide +kernel

def row17895 : Integer.Sparse Key := [(key2064, 3), (key2070, 1), (key2080, -3), (key2086, -1), (key2153, -3), (key2167, -1), (key2177, 3), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

theorem rowCheck17895 : row17895 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17895 := by decide +kernel

theorem rowEval17895 (x : Key → ℝ) : Integer.Sparse.eval row17895 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck17895, Integer.Sparse.eval_collectBalanced, rawRowCheck17895]

def rawRow17896 : Integer.Sparse Key := [(key2150, -1), (key2177, -1), (key2150, -1), (key2280, -1), (key2177, -1), (key2280, -1), (key2153, 2), (key2153, 2), (key2247, 2), (key2061, 1), (key2080, 1), (key2061, 1), (key2288, 1), (key2080, 1), (key2288, 1), (key2064, -2), (key2064, -2), (key2254, -2), (key2150, -1), (key2177, -1), (key2150, -1), (key2280, -1), (key2177, -1), (key2280, -1), (key2061, 1), (key2080, 1), (key2061, 1), (key2288, 1), (key2080, 1), (key2288, 1), (key2153, 2), (key2153, 2), (key2247, 2), (key2064, -2), (key2064, -2), (key2254, -2)]

theorem rawRowCheck17896 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form15 = rawRow17896 := by decide +kernel

def row17896 : Integer.Sparse Key := [(key2061, 4), (key2064, -8), (key2080, 4), (key2150, -4), (key2153, 8), (key2177, -4), (key2247, 4), (key2254, -4), (key2280, -4), (key2288, 4)]

theorem rowCheck17896 : row17896 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17896 := by decide +kernel

theorem rowEval17896 (x : Key → ℝ) : Integer.Sparse.eval row17896 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form15) x := by
  rw [rowCheck17896, Integer.Sparse.eval_collectBalanced, rawRowCheck17896]

def rawRow17897 : Integer.Sparse Key := [(key2177, -1), (key2150, -1), (key2280, -1), (key2150, -1), (key2280, -1), (key2177, -1), (key2153, 2), (key2247, 2), (key2153, 2), (key2080, 1), (key2061, 1), (key2288, 1), (key2061, 1), (key2288, 1), (key2080, 1), (key2064, -2), (key2254, -2), (key2064, -2), (key2177, -1), (key2150, -1), (key2280, -1), (key2150, -1), (key2280, -1), (key2177, -1), (key2080, 1), (key2061, 1), (key2288, 1), (key2061, 1), (key2288, 1), (key2080, 1), (key2153, 2), (key2247, 2), (key2153, 2), (key2064, -2), (key2254, -2), (key2064, -2)]

theorem rawRowCheck17897 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form15 = rawRow17897 := by decide +kernel

def row17897 : Integer.Sparse Key := [(key2061, 4), (key2064, -8), (key2080, 4), (key2150, -4), (key2153, 8), (key2177, -4), (key2247, 4), (key2254, -4), (key2280, -4), (key2288, 4)]

theorem rowCheck17897 : row17897 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17897 := by decide +kernel

theorem rowEval17897 (x : Key → ℝ) : Integer.Sparse.eval row17897 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck17897, Integer.Sparse.eval_collectBalanced, rawRowCheck17897]

def rawRow17898 : Integer.Sparse Key := [(key2280, -1), (key2280, -1), (key2177, -1), (key2177, -1), (key2150, -1), (key2150, -1), (key2247, 2), (key2153, 2), (key2153, 2), (key2288, 1), (key2288, 1), (key2080, 1), (key2080, 1), (key2061, 1), (key2061, 1), (key2254, -2), (key2064, -2), (key2064, -2), (key2280, -1), (key2280, -1), (key2177, -1), (key2177, -1), (key2150, -1), (key2150, -1), (key2288, 1), (key2288, 1), (key2080, 1), (key2080, 1), (key2061, 1), (key2061, 1), (key2247, 2), (key2153, 2), (key2153, 2), (key2254, -2), (key2064, -2), (key2064, -2)]

theorem rawRowCheck17898 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form15 = rawRow17898 := by decide +kernel

def row17898 : Integer.Sparse Key := [(key2061, 4), (key2064, -8), (key2080, 4), (key2150, -4), (key2153, 8), (key2177, -4), (key2247, 4), (key2254, -4), (key2280, -4), (key2288, 4)]

theorem rowCheck17898 : row17898 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17898 := by decide +kernel

theorem rowEval17898 (x : Key → ℝ) : Integer.Sparse.eval row17898 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck17898, Integer.Sparse.eval_collectBalanced, rawRowCheck17898]

def rawRow17899 : Integer.Sparse Key := [(key2154, 2), (key2154, 2), (key2170, 2), (key2178, -1), (key2180, -1), (key2178, -1), (key2190, -1), (key2180, -1), (key2190, -1), (key2154, 2), (key2154, 2), (key2170, 2), (key2278, -1), (key2282, -1), (key2278, -1), (key2290, -1), (key2282, -1), (key2290, -1), (key2178, -1), (key2180, -1), (key2178, -1), (key2190, -1), (key2180, -1), (key2190, -1), (key2278, -1), (key2282, -1), (key2278, -1), (key2290, -1), (key2282, -1), (key2290, -1), (key2329, 2), (key2331, 2), (key2329, 2), (key2334, 2), (key2331, 2), (key2334, 2)]

theorem rawRowCheck17899 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form16 = rawRow17899 := by decide +kernel

def row17899 : Integer.Sparse Key := [(key2154, 8), (key2170, 4), (key2178, -4), (key2180, -4), (key2190, -4), (key2278, -4), (key2282, -4), (key2290, -4), (key2329, 4), (key2331, 4), (key2334, 4)]

theorem rowCheck17899 : row17899 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17899 := by decide +kernel

theorem rowEval17899 (x : Key → ℝ) : Integer.Sparse.eval row17899 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form16) x := by
  rw [rowCheck17899, Integer.Sparse.eval_collectBalanced, rawRowCheck17899]

def rawRow17900 : Integer.Sparse Key := [(key2154, 2), (key2170, 2), (key2154, 2), (key2180, -1), (key2178, -1), (key2190, -1), (key2178, -1), (key2190, -1), (key2180, -1), (key2154, 2), (key2170, 2), (key2154, 2), (key2282, -1), (key2278, -1), (key2290, -1), (key2278, -1), (key2290, -1), (key2282, -1), (key2180, -1), (key2178, -1), (key2190, -1), (key2178, -1), (key2190, -1), (key2180, -1), (key2282, -1), (key2278, -1), (key2290, -1), (key2278, -1), (key2290, -1), (key2282, -1), (key2331, 2), (key2329, 2), (key2334, 2), (key2329, 2), (key2334, 2), (key2331, 2)]

theorem rawRowCheck17900 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form16 = rawRow17900 := by decide +kernel

def row17900 : Integer.Sparse Key := [(key2154, 8), (key2170, 4), (key2178, -4), (key2180, -4), (key2190, -4), (key2278, -4), (key2282, -4), (key2290, -4), (key2329, 4), (key2331, 4), (key2334, 4)]

theorem rowCheck17900 : row17900 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17900 := by decide +kernel

theorem rowEval17900 (x : Key → ℝ) : Integer.Sparse.eval row17900 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form16) x := by
  rw [rowCheck17900, Integer.Sparse.eval_collectBalanced, rawRowCheck17900]

def rawRow17901 : Integer.Sparse Key := [(key2170, 2), (key2154, 2), (key2154, 2), (key2190, -1), (key2190, -1), (key2180, -1), (key2180, -1), (key2178, -1), (key2178, -1), (key2170, 2), (key2154, 2), (key2154, 2), (key2290, -1), (key2290, -1), (key2282, -1), (key2282, -1), (key2278, -1), (key2278, -1), (key2190, -1), (key2190, -1), (key2180, -1), (key2180, -1), (key2178, -1), (key2178, -1), (key2290, -1), (key2290, -1), (key2282, -1), (key2282, -1), (key2278, -1), (key2278, -1), (key2334, 2), (key2334, 2), (key2331, 2), (key2331, 2), (key2329, 2), (key2329, 2)]

theorem rawRowCheck17901 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form16 = rawRow17901 := by decide +kernel

def row17901 : Integer.Sparse Key := [(key2154, 8), (key2170, 4), (key2178, -4), (key2180, -4), (key2190, -4), (key2278, -4), (key2282, -4), (key2290, -4), (key2329, 4), (key2331, 4), (key2334, 4)]

theorem rowCheck17901 : row17901 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17901 := by decide +kernel

theorem rowEval17901 (x : Key → ℝ) : Integer.Sparse.eval row17901 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form16) x := by
  rw [rowCheck17901, Integer.Sparse.eval_collectBalanced, rawRowCheck17901]

def rawRow17902 : Integer.Sparse Key := [(key2035, 2), (key2178, 2), (key2190, 2), (key2035, -1), (key2038, -1), (key2154, -1), (key2170, -1), (key2180, -1), (key2190, -1), (key2065, 2), (key2278, 2), (key2290, 2), (key2065, -1), (key2073, -1), (key2154, -1), (key2170, -1), (key2282, -1), (key2290, -1), (key2081, -1), (key2083, -1), (key2278, -1), (key2290, -1), (key2329, -1), (key2334, -1), (key2081, -1), (key2088, -1), (key2178, -1), (key2190, -1), (key2331, -1), (key2334, -1), (key2083, 2), (key2088, 2), (key2180, 2), (key2190, 2), (key2282, 2), (key2290, 2)]

theorem rawRowCheck17902 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form16 = rawRow17902 := by decide +kernel

def row17902 : Integer.Sparse Key := [(key2035, 1), (key2038, -1), (key2065, 1), (key2073, -1), (key2081, -2), (key2083, 1), (key2088, 1), (key2154, -2), (key2170, -2), (key2178, 1), (key2180, 1), (key2190, 2), (key2278, 1), (key2282, 1), (key2290, 2), (key2329, -1), (key2331, -1), (key2334, -2)]

theorem rowCheck17902 : row17902 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17902 := by decide +kernel

theorem rowEval17902 (x : Key → ℝ) : Integer.Sparse.eval row17902 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form16) x := by
  rw [rowCheck17902, Integer.Sparse.eval_collectBalanced, rawRowCheck17902]

def rawRow17903 : Integer.Sparse Key := [(key2035, 2), (key2190, 2), (key2178, 2), (key2038, -1), (key2035, -1), (key2170, -1), (key2154, -1), (key2190, -1), (key2180, -1), (key2065, 2), (key2290, 2), (key2278, 2), (key2073, -1), (key2065, -1), (key2170, -1), (key2154, -1), (key2290, -1), (key2282, -1), (key2083, -1), (key2081, -1), (key2290, -1), (key2278, -1), (key2334, -1), (key2329, -1), (key2088, -1), (key2081, -1), (key2190, -1), (key2178, -1), (key2334, -1), (key2331, -1), (key2088, 2), (key2083, 2), (key2190, 2), (key2180, 2), (key2290, 2), (key2282, 2)]

theorem rawRowCheck17903 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form16 = rawRow17903 := by decide +kernel

def row17903 : Integer.Sparse Key := [(key2035, 1), (key2038, -1), (key2065, 1), (key2073, -1), (key2081, -2), (key2083, 1), (key2088, 1), (key2154, -2), (key2170, -2), (key2178, 1), (key2180, 1), (key2190, 2), (key2278, 1), (key2282, 1), (key2290, 2), (key2329, -1), (key2331, -1), (key2334, -2)]

theorem rowCheck17903 : row17903 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17903 := by decide +kernel

theorem rowEval17903 (x : Key → ℝ) : Integer.Sparse.eval row17903 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form16) x := by
  rw [rowCheck17903, Integer.Sparse.eval_collectBalanced, rawRowCheck17903]

def rawRow17904 : Integer.Sparse Key := [(key2178, 2), (key2035, 2), (key2190, 2), (key2154, -1), (key2180, -1), (key2035, -1), (key2190, -1), (key2038, -1), (key2170, -1), (key2278, 2), (key2065, 2), (key2290, 2), (key2154, -1), (key2282, -1), (key2065, -1), (key2290, -1), (key2073, -1), (key2170, -1), (key2278, -1), (key2329, -1), (key2081, -1), (key2334, -1), (key2083, -1), (key2290, -1), (key2178, -1), (key2331, -1), (key2081, -1), (key2334, -1), (key2088, -1), (key2190, -1), (key2180, 2), (key2282, 2), (key2083, 2), (key2290, 2), (key2088, 2), (key2190, 2)]

theorem rawRowCheck17904 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form16 = rawRow17904 := by decide +kernel

def row17904 : Integer.Sparse Key := [(key2035, 1), (key2038, -1), (key2065, 1), (key2073, -1), (key2081, -2), (key2083, 1), (key2088, 1), (key2154, -2), (key2170, -2), (key2178, 1), (key2180, 1), (key2190, 2), (key2278, 1), (key2282, 1), (key2290, 2), (key2329, -1), (key2331, -1), (key2334, -2)]

theorem rowCheck17904 : row17904 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17904 := by decide +kernel

theorem rowEval17904 (x : Key → ℝ) : Integer.Sparse.eval row17904 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form16) x := by
  rw [rowCheck17904, Integer.Sparse.eval_collectBalanced, rawRowCheck17904]

def rawRow17905 : Integer.Sparse Key := [(key2178, 2), (key2190, 2), (key2035, 2), (key2180, -1), (key2154, -1), (key2190, -1), (key2035, -1), (key2170, -1), (key2038, -1), (key2278, 2), (key2290, 2), (key2065, 2), (key2282, -1), (key2154, -1), (key2290, -1), (key2065, -1), (key2170, -1), (key2073, -1), (key2329, -1), (key2278, -1), (key2334, -1), (key2081, -1), (key2290, -1), (key2083, -1), (key2331, -1), (key2178, -1), (key2334, -1), (key2081, -1), (key2190, -1), (key2088, -1), (key2282, 2), (key2180, 2), (key2290, 2), (key2083, 2), (key2190, 2), (key2088, 2)]

theorem rawRowCheck17905 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form16 = rawRow17905 := by decide +kernel

def row17905 : Integer.Sparse Key := [(key2035, 1), (key2038, -1), (key2065, 1), (key2073, -1), (key2081, -2), (key2083, 1), (key2088, 1), (key2154, -2), (key2170, -2), (key2178, 1), (key2180, 1), (key2190, 2), (key2278, 1), (key2282, 1), (key2290, 2), (key2329, -1), (key2331, -1), (key2334, -2)]

theorem rowCheck17905 : row17905 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17905 := by decide +kernel

theorem rowEval17905 (x : Key → ℝ) : Integer.Sparse.eval row17905 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck17905, Integer.Sparse.eval_collectBalanced, rawRowCheck17905]

def rawRow17906 : Integer.Sparse Key := [(key2190, 2), (key2035, 2), (key2178, 2), (key2170, -1), (key2190, -1), (key2038, -1), (key2180, -1), (key2035, -1), (key2154, -1), (key2290, 2), (key2065, 2), (key2278, 2), (key2170, -1), (key2290, -1), (key2073, -1), (key2282, -1), (key2065, -1), (key2154, -1), (key2290, -1), (key2334, -1), (key2083, -1), (key2329, -1), (key2081, -1), (key2278, -1), (key2190, -1), (key2334, -1), (key2088, -1), (key2331, -1), (key2081, -1), (key2178, -1), (key2190, 2), (key2290, 2), (key2088, 2), (key2282, 2), (key2083, 2), (key2180, 2)]

theorem rawRowCheck17906 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form16 = rawRow17906 := by decide +kernel

def row17906 : Integer.Sparse Key := [(key2035, 1), (key2038, -1), (key2065, 1), (key2073, -1), (key2081, -2), (key2083, 1), (key2088, 1), (key2154, -2), (key2170, -2), (key2178, 1), (key2180, 1), (key2190, 2), (key2278, 1), (key2282, 1), (key2290, 2), (key2329, -1), (key2331, -1), (key2334, -2)]

theorem rowCheck17906 : row17906 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17906 := by decide +kernel

theorem rowEval17906 (x : Key → ℝ) : Integer.Sparse.eval row17906 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form16) x := by
  rw [rowCheck17906, Integer.Sparse.eval_collectBalanced, rawRowCheck17906]

def rawRow17907 : Integer.Sparse Key := [(key2190, 2), (key2178, 2), (key2035, 2), (key2190, -1), (key2170, -1), (key2180, -1), (key2038, -1), (key2154, -1), (key2035, -1), (key2290, 2), (key2278, 2), (key2065, 2), (key2290, -1), (key2170, -1), (key2282, -1), (key2073, -1), (key2154, -1), (key2065, -1), (key2334, -1), (key2290, -1), (key2329, -1), (key2083, -1), (key2278, -1), (key2081, -1), (key2334, -1), (key2190, -1), (key2331, -1), (key2088, -1), (key2178, -1), (key2081, -1), (key2290, 2), (key2190, 2), (key2282, 2), (key2088, 2), (key2180, 2), (key2083, 2)]

theorem rawRowCheck17907 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form16 = rawRow17907 := by decide +kernel

def row17907 : Integer.Sparse Key := [(key2035, 1), (key2038, -1), (key2065, 1), (key2073, -1), (key2081, -2), (key2083, 1), (key2088, 1), (key2154, -2), (key2170, -2), (key2178, 1), (key2180, 1), (key2190, 2), (key2278, 1), (key2282, 1), (key2290, 2), (key2329, -1), (key2331, -1), (key2334, -2)]

theorem rowCheck17907 : row17907 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17907 := by decide +kernel

theorem rowEval17907 (x : Key → ℝ) : Integer.Sparse.eval row17907 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck17907, Integer.Sparse.eval_collectBalanced, rawRowCheck17907]

def rawRow17908 : Integer.Sparse Key := [(key2065, 2), (key2278, 2), (key2290, 2), (key2081, -1), (key2083, -1), (key2278, -1), (key2290, -1), (key2329, -1), (key2334, -1), (key2035, 2), (key2178, 2), (key2190, 2), (key2081, -1), (key2088, -1), (key2178, -1), (key2190, -1), (key2331, -1), (key2334, -1), (key2035, -1), (key2038, -1), (key2154, -1), (key2170, -1), (key2180, -1), (key2190, -1), (key2065, -1), (key2073, -1), (key2154, -1), (key2170, -1), (key2282, -1), (key2290, -1), (key2083, 2), (key2088, 2), (key2180, 2), (key2190, 2), (key2282, 2), (key2290, 2)]

theorem rawRowCheck17908 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form16 = rawRow17908 := by decide +kernel

def row17908 : Integer.Sparse Key := [(key2035, 1), (key2038, -1), (key2065, 1), (key2073, -1), (key2081, -2), (key2083, 1), (key2088, 1), (key2154, -2), (key2170, -2), (key2178, 1), (key2180, 1), (key2190, 2), (key2278, 1), (key2282, 1), (key2290, 2), (key2329, -1), (key2331, -1), (key2334, -2)]

theorem rowCheck17908 : row17908 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17908 := by decide +kernel

theorem rowEval17908 (x : Key → ℝ) : Integer.Sparse.eval row17908 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form16) x := by
  rw [rowCheck17908, Integer.Sparse.eval_collectBalanced, rawRowCheck17908]

def rawRow17909 : Integer.Sparse Key := [(key2065, 2), (key2290, 2), (key2278, 2), (key2083, -1), (key2081, -1), (key2290, -1), (key2278, -1), (key2334, -1), (key2329, -1), (key2035, 2), (key2190, 2), (key2178, 2), (key2088, -1), (key2081, -1), (key2190, -1), (key2178, -1), (key2334, -1), (key2331, -1), (key2038, -1), (key2035, -1), (key2170, -1), (key2154, -1), (key2190, -1), (key2180, -1), (key2073, -1), (key2065, -1), (key2170, -1), (key2154, -1), (key2290, -1), (key2282, -1), (key2088, 2), (key2083, 2), (key2190, 2), (key2180, 2), (key2290, 2), (key2282, 2)]

theorem rawRowCheck17909 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form16 = rawRow17909 := by decide +kernel

def row17909 : Integer.Sparse Key := [(key2035, 1), (key2038, -1), (key2065, 1), (key2073, -1), (key2081, -2), (key2083, 1), (key2088, 1), (key2154, -2), (key2170, -2), (key2178, 1), (key2180, 1), (key2190, 2), (key2278, 1), (key2282, 1), (key2290, 2), (key2329, -1), (key2331, -1), (key2334, -2)]

theorem rowCheck17909 : row17909 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17909 := by decide +kernel

theorem rowEval17909 (x : Key → ℝ) : Integer.Sparse.eval row17909 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form16) x := by
  rw [rowCheck17909, Integer.Sparse.eval_collectBalanced, rawRowCheck17909]

def rawRow17910 : Integer.Sparse Key := [(key2278, 2), (key2065, 2), (key2290, 2), (key2278, -1), (key2329, -1), (key2081, -1), (key2334, -1), (key2083, -1), (key2290, -1), (key2178, 2), (key2035, 2), (key2190, 2), (key2178, -1), (key2331, -1), (key2081, -1), (key2334, -1), (key2088, -1), (key2190, -1), (key2154, -1), (key2180, -1), (key2035, -1), (key2190, -1), (key2038, -1), (key2170, -1), (key2154, -1), (key2282, -1), (key2065, -1), (key2290, -1), (key2073, -1), (key2170, -1), (key2180, 2), (key2282, 2), (key2083, 2), (key2290, 2), (key2088, 2), (key2190, 2)]

theorem rawRowCheck17910 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form16 = rawRow17910 := by decide +kernel

def row17910 : Integer.Sparse Key := [(key2035, 1), (key2038, -1), (key2065, 1), (key2073, -1), (key2081, -2), (key2083, 1), (key2088, 1), (key2154, -2), (key2170, -2), (key2178, 1), (key2180, 1), (key2190, 2), (key2278, 1), (key2282, 1), (key2290, 2), (key2329, -1), (key2331, -1), (key2334, -2)]

theorem rowCheck17910 : row17910 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17910 := by decide +kernel

theorem rowEval17910 (x : Key → ℝ) : Integer.Sparse.eval row17910 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form16) x := by
  rw [rowCheck17910, Integer.Sparse.eval_collectBalanced, rawRowCheck17910]

def rawRow17911 : Integer.Sparse Key := [(key2278, 2), (key2290, 2), (key2065, 2), (key2329, -1), (key2278, -1), (key2334, -1), (key2081, -1), (key2290, -1), (key2083, -1), (key2178, 2), (key2190, 2), (key2035, 2), (key2331, -1), (key2178, -1), (key2334, -1), (key2081, -1), (key2190, -1), (key2088, -1), (key2180, -1), (key2154, -1), (key2190, -1), (key2035, -1), (key2170, -1), (key2038, -1), (key2282, -1), (key2154, -1), (key2290, -1), (key2065, -1), (key2170, -1), (key2073, -1), (key2282, 2), (key2180, 2), (key2290, 2), (key2083, 2), (key2190, 2), (key2088, 2)]

theorem rawRowCheck17911 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form16 = rawRow17911 := by decide +kernel

def row17911 : Integer.Sparse Key := [(key2035, 1), (key2038, -1), (key2065, 1), (key2073, -1), (key2081, -2), (key2083, 1), (key2088, 1), (key2154, -2), (key2170, -2), (key2178, 1), (key2180, 1), (key2190, 2), (key2278, 1), (key2282, 1), (key2290, 2), (key2329, -1), (key2331, -1), (key2334, -2)]

theorem rowCheck17911 : row17911 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17911 := by decide +kernel

theorem rowEval17911 (x : Key → ℝ) : Integer.Sparse.eval row17911 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck17911, Integer.Sparse.eval_collectBalanced, rawRowCheck17911]

def rawRow17912 : Integer.Sparse Key := [(key2290, 2), (key2065, 2), (key2278, 2), (key2290, -1), (key2334, -1), (key2083, -1), (key2329, -1), (key2081, -1), (key2278, -1), (key2190, 2), (key2035, 2), (key2178, 2), (key2190, -1), (key2334, -1), (key2088, -1), (key2331, -1), (key2081, -1), (key2178, -1), (key2170, -1), (key2190, -1), (key2038, -1), (key2180, -1), (key2035, -1), (key2154, -1), (key2170, -1), (key2290, -1), (key2073, -1), (key2282, -1), (key2065, -1), (key2154, -1), (key2190, 2), (key2290, 2), (key2088, 2), (key2282, 2), (key2083, 2), (key2180, 2)]

theorem rawRowCheck17912 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form16 = rawRow17912 := by decide +kernel

def row17912 : Integer.Sparse Key := [(key2035, 1), (key2038, -1), (key2065, 1), (key2073, -1), (key2081, -2), (key2083, 1), (key2088, 1), (key2154, -2), (key2170, -2), (key2178, 1), (key2180, 1), (key2190, 2), (key2278, 1), (key2282, 1), (key2290, 2), (key2329, -1), (key2331, -1), (key2334, -2)]

theorem rowCheck17912 : row17912 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17912 := by decide +kernel

theorem rowEval17912 (x : Key → ℝ) : Integer.Sparse.eval row17912 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form16) x := by
  rw [rowCheck17912, Integer.Sparse.eval_collectBalanced, rawRowCheck17912]

def rawRow17913 : Integer.Sparse Key := [(key2290, 2), (key2278, 2), (key2065, 2), (key2334, -1), (key2290, -1), (key2329, -1), (key2083, -1), (key2278, -1), (key2081, -1), (key2190, 2), (key2178, 2), (key2035, 2), (key2334, -1), (key2190, -1), (key2331, -1), (key2088, -1), (key2178, -1), (key2081, -1), (key2190, -1), (key2170, -1), (key2180, -1), (key2038, -1), (key2154, -1), (key2035, -1), (key2290, -1), (key2170, -1), (key2282, -1), (key2073, -1), (key2154, -1), (key2065, -1), (key2290, 2), (key2190, 2), (key2282, 2), (key2088, 2), (key2180, 2), (key2083, 2)]

theorem rawRowCheck17913 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form16 = rawRow17913 := by decide +kernel

def row17913 : Integer.Sparse Key := [(key2035, 1), (key2038, -1), (key2065, 1), (key2073, -1), (key2081, -2), (key2083, 1), (key2088, 1), (key2154, -2), (key2170, -2), (key2178, 1), (key2180, 1), (key2190, 2), (key2278, 1), (key2282, 1), (key2290, 2), (key2329, -1), (key2331, -1), (key2334, -2)]

theorem rowCheck17913 : row17913 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17913 := by decide +kernel

theorem rowEval17913 (x : Key → ℝ) : Integer.Sparse.eval row17913 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck17913, Integer.Sparse.eval_collectBalanced, rawRowCheck17913]

def rawRow17914 : Integer.Sparse Key := [(key2081, 2), (key2081, 2), (key2334, 2), (key2065, -1), (key2083, -1), (key2065, -1), (key2290, -1), (key2083, -1), (key2290, -1), (key2081, 2), (key2081, 2), (key2334, 2), (key2035, -1), (key2088, -1), (key2035, -1), (key2190, -1), (key2088, -1), (key2190, -1), (key2065, -1), (key2083, -1), (key2065, -1), (key2290, -1), (key2083, -1), (key2290, -1), (key2035, -1), (key2088, -1), (key2035, -1), (key2190, -1), (key2088, -1), (key2190, -1), (key2038, 2), (key2073, 2), (key2038, 2), (key2170, 2), (key2073, 2), (key2170, 2)]

theorem rawRowCheck17914 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form16 = rawRow17914 := by decide +kernel

def row17914 : Integer.Sparse Key := [(key2035, -4), (key2038, 4), (key2065, -4), (key2073, 4), (key2081, 8), (key2083, -4), (key2088, -4), (key2170, 4), (key2190, -4), (key2290, -4), (key2334, 4)]

theorem rowCheck17914 : row17914 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17914 := by decide +kernel

theorem rowEval17914 (x : Key → ℝ) : Integer.Sparse.eval row17914 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form16) x := by
  rw [rowCheck17914, Integer.Sparse.eval_collectBalanced, rawRowCheck17914]

def rawRow17915 : Integer.Sparse Key := [(key2081, 2), (key2334, 2), (key2081, 2), (key2083, -1), (key2065, -1), (key2290, -1), (key2065, -1), (key2290, -1), (key2083, -1), (key2081, 2), (key2334, 2), (key2081, 2), (key2088, -1), (key2035, -1), (key2190, -1), (key2035, -1), (key2190, -1), (key2088, -1), (key2083, -1), (key2065, -1), (key2290, -1), (key2065, -1), (key2290, -1), (key2083, -1), (key2088, -1), (key2035, -1), (key2190, -1), (key2035, -1), (key2190, -1), (key2088, -1), (key2073, 2), (key2038, 2), (key2170, 2), (key2038, 2), (key2170, 2), (key2073, 2)]

theorem rawRowCheck17915 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form16 = rawRow17915 := by decide +kernel

def row17915 : Integer.Sparse Key := [(key2035, -4), (key2038, 4), (key2065, -4), (key2073, 4), (key2081, 8), (key2083, -4), (key2088, -4), (key2170, 4), (key2190, -4), (key2290, -4), (key2334, 4)]

theorem rowCheck17915 : row17915 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17915 := by decide +kernel

theorem rowEval17915 (x : Key → ℝ) : Integer.Sparse.eval row17915 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck17915, Integer.Sparse.eval_collectBalanced, rawRowCheck17915]

def rawRow17916 : Integer.Sparse Key := [(key2334, 2), (key2081, 2), (key2081, 2), (key2290, -1), (key2290, -1), (key2083, -1), (key2083, -1), (key2065, -1), (key2065, -1), (key2334, 2), (key2081, 2), (key2081, 2), (key2190, -1), (key2190, -1), (key2088, -1), (key2088, -1), (key2035, -1), (key2035, -1), (key2290, -1), (key2290, -1), (key2083, -1), (key2083, -1), (key2065, -1), (key2065, -1), (key2190, -1), (key2190, -1), (key2088, -1), (key2088, -1), (key2035, -1), (key2035, -1), (key2170, 2), (key2170, 2), (key2073, 2), (key2073, 2), (key2038, 2), (key2038, 2)]

theorem rawRowCheck17916 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form16 = rawRow17916 := by decide +kernel

def row17916 : Integer.Sparse Key := [(key2035, -4), (key2038, 4), (key2065, -4), (key2073, 4), (key2081, 8), (key2083, -4), (key2088, -4), (key2170, 4), (key2190, -4), (key2290, -4), (key2334, 4)]

theorem rowCheck17916 : row17916 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17916 := by decide +kernel

theorem rowEval17916 (x : Key → ℝ) : Integer.Sparse.eval row17916 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck17916, Integer.Sparse.eval_collectBalanced, rawRowCheck17916]

def rawRow17917 : Integer.Sparse Key := [(key777, 4), (key782, 4), (key782, 4), (key802, -2), (key807, -2), (key802, -2), (key821, -2), (key807, -2), (key821, -2), (key802, -2), (key807, -2), (key802, -2), (key821, -2), (key807, -2), (key821, -2), (key872, 4), (key905, 4), (key905, 4)]

theorem rawRowCheck17917 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form17 = rawRow17917 := by decide +kernel

def row17917 : Integer.Sparse Key := [(key777, 4), (key782, 8), (key802, -8), (key807, -8), (key821, -8), (key872, 4), (key905, 8)]

theorem rowCheck17917 : row17917 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17917 := by decide +kernel

theorem rowEval17917 (x : Key → ℝ) : Integer.Sparse.eval row17917 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17917, Integer.Sparse.eval_collectBalanced, rawRowCheck17917]

def rawRow17918 : Integer.Sparse Key := [(key782, 4), (key777, 4), (key782, 4), (key807, -2), (key802, -2), (key821, -2), (key802, -2), (key821, -2), (key807, -2), (key807, -2), (key802, -2), (key821, -2), (key802, -2), (key821, -2), (key807, -2), (key905, 4), (key872, 4), (key905, 4)]

theorem rawRowCheck17918 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form17 = rawRow17918 := by decide +kernel

def row17918 : Integer.Sparse Key := [(key777, 4), (key782, 8), (key802, -8), (key807, -8), (key821, -8), (key872, 4), (key905, 8)]

theorem rowCheck17918 : row17918 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17918 := by decide +kernel

theorem rowEval17918 (x : Key → ℝ) : Integer.Sparse.eval row17918 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17918, Integer.Sparse.eval_collectBalanced, rawRowCheck17918]

def rawRow17919 : Integer.Sparse Key := [(key782, 4), (key782, 4), (key777, 4), (key821, -2), (key821, -2), (key807, -2), (key807, -2), (key802, -2), (key802, -2), (key821, -2), (key821, -2), (key807, -2), (key807, -2), (key802, -2), (key802, -2), (key905, 4), (key905, 4), (key872, 4)]

theorem rawRowCheck17919 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form17 = rawRow17919 := by decide +kernel

def row17919 : Integer.Sparse Key := [(key777, 4), (key782, 8), (key802, -8), (key807, -8), (key821, -8), (key872, 4), (key905, 8)]

theorem rowCheck17919 : row17919 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17919 := by decide +kernel

theorem rowEval17919 (x : Key → ℝ) : Integer.Sparse.eval row17919 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17919, Integer.Sparse.eval_collectBalanced, rawRowCheck17919]

end MUB6.Certificate.GramRows

end OAI
