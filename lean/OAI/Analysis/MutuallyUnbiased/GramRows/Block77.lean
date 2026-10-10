import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
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

def rawRow6784 : Integer.Sparse Key := [(key2080, -1), (key2061, -1), (key2064, 2), (key2080, -1), (key2061, -1), (key2086, 2), (key2031, 2), (key2070, -1), (key2034, -1), (key2064, 2), (key2070, -1), (key2034, -1), (key2177, 1), (key2150, 1), (key2153, -2), (key2177, 1), (key2150, 1), (key2188, -2), (key2031, -2), (key2167, 1), (key2034, 1), (key2153, -2), (key2167, 1), (key2034, 1), (key2280, -1), (key2150, -1), (key2247, 1), (key2153, 1), (key2288, 1), (key2061, 1), (key2254, -1), (key2064, -1), (key2280, -1), (key2150, -1), (key2288, 1), (key2061, 1), (key2247, 1), (key2153, 1), (key2254, -1), (key2064, -1)]

theorem rawRowCheck6784 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block2.form2 = rawRow6784 := by decide +kernel

def row6784 : Integer.Sparse Key := [(key2064, 2), (key2070, -2), (key2080, -2), (key2086, 2), (key2153, -2), (key2167, 2), (key2177, 2), (key2188, -2), (key2247, 2), (key2254, -2), (key2280, -2), (key2288, 2)]

theorem rowCheck6784 : row6784 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6784 := by decide +kernel

theorem rowEval6784 (x : Key → ℝ) : Integer.Sparse.eval row6784 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6784, Integer.Sparse.eval_collectBalanced, rawRowCheck6784]

def rawRow6785 : Integer.Sparse Key := [(key2064, -1), (key2080, -1), (key2061, 2), (key2070, -1), (key2086, -1), (key2034, 2), (key2080, 2), (key2031, -1), (key2061, -1), (key2070, 2), (key2034, -1), (key2064, -1), (key2153, 1), (key2177, 1), (key2150, -2), (key2167, 1), (key2188, 1), (key2034, -2), (key2177, -2), (key2031, 1), (key2150, 1), (key2167, -2), (key2034, 1), (key2153, 1), (key2153, -1), (key2277, -1), (key2150, 1), (key2243, 1), (key2064, 1), (key2277, 1), (key2061, -1), (key2243, -1), (key2167, -1), (key2288, -1), (key2070, 1), (key2280, 1), (key2167, 1), (key2254, 1), (key2070, -1), (key2247, -1)]

theorem rawRowCheck6785 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block2.form2 = rawRow6785 := by decide +kernel

def row6785 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

theorem rowCheck6785 : row6785 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6785 := by decide +kernel

theorem rowEval6785 (x : Key → ℝ) : Integer.Sparse.eval row6785 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck6785, Integer.Sparse.eval_collectBalanced, rawRowCheck6785]

def rawRow6786 : Integer.Sparse Key := [(key2080, -1), (key2064, -1), (key2061, 2), (key2086, -1), (key2070, -1), (key2080, 2), (key2034, 2), (key2061, -1), (key2031, -1), (key2070, 2), (key2064, -1), (key2034, -1), (key2177, 1), (key2153, 1), (key2150, -2), (key2188, 1), (key2167, 1), (key2177, -2), (key2034, -2), (key2150, 1), (key2031, 1), (key2167, -2), (key2153, 1), (key2034, 1), (key2277, -1), (key2153, -1), (key2243, 1), (key2150, 1), (key2277, 1), (key2064, 1), (key2243, -1), (key2061, -1), (key2288, -1), (key2167, -1), (key2280, 1), (key2070, 1), (key2254, 1), (key2167, 1), (key2247, -1), (key2070, -1)]

theorem rawRowCheck6786 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block2.form2 = rawRow6786 := by decide +kernel

def row6786 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

theorem rowCheck6786 : row6786 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6786 := by decide +kernel

theorem rowEval6786 (x : Key → ℝ) : Integer.Sparse.eval row6786 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6786, Integer.Sparse.eval_collectBalanced, rawRowCheck6786]

def rawRow6787 : Integer.Sparse Key := [(key2070, -1), (key2070, -1), (key2086, 2), (key2034, -1), (key2034, -1), (key2064, 2), (key2064, 2), (key2080, -1), (key2080, -1), (key2031, 2), (key2061, -1), (key2061, -1), (key2167, 1), (key2167, 1), (key2188, -2), (key2034, 1), (key2034, 1), (key2153, -2), (key2153, -2), (key2177, 1), (key2177, 1), (key2031, -2), (key2150, 1), (key2150, 1), (key2254, -1), (key2254, -1), (key2288, 1), (key2288, 1), (key2247, 1), (key2247, 1), (key2280, -1), (key2280, -1), (key2064, -1), (key2064, -1), (key2153, 1), (key2153, 1), (key2061, 1), (key2061, 1), (key2150, -1), (key2150, -1)]

theorem rawRowCheck6787 : GramPolynomial.normalizedRow 0 ![1, -1, 1, -1, 0, 0] GramFunctions.Block2.form2 = rawRow6787 := by decide +kernel

def row6787 : Integer.Sparse Key := [(key2064, 2), (key2070, -2), (key2080, -2), (key2086, 2), (key2153, -2), (key2167, 2), (key2177, 2), (key2188, -2), (key2247, 2), (key2254, -2), (key2280, -2), (key2288, 2)]

theorem rowCheck6787 : row6787 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6787 := by decide +kernel

theorem rowEval6787 (x : Key → ℝ) : Integer.Sparse.eval row6787 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, -1, 0, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck6787, Integer.Sparse.eval_collectBalanced, rawRowCheck6787]

def rawRow6788 : Integer.Sparse Key := [(key2070, -1), (key2086, -1), (key2070, 2), (key2064, -1), (key2080, -1), (key2034, 2), (key2080, 2), (key2034, -1), (key2064, -1), (key2061, 2), (key2031, -1), (key2061, -1), (key2167, 1), (key2188, 1), (key2167, -2), (key2153, 1), (key2177, 1), (key2034, -2), (key2177, -2), (key2034, 1), (key2153, 1), (key2150, -2), (key2031, 1), (key2150, 1), (key2167, -1), (key2288, -1), (key2167, 1), (key2254, 1), (key2070, 1), (key2280, 1), (key2070, -1), (key2247, -1), (key2153, -1), (key2277, -1), (key2064, 1), (key2277, 1), (key2150, 1), (key2243, 1), (key2061, -1), (key2243, -1)]

theorem rawRowCheck6788 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -1, 0] GramFunctions.Block2.form2 = rawRow6788 := by decide +kernel

def row6788 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

theorem rowCheck6788 : row6788 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6788 := by decide +kernel

theorem rowEval6788 (x : Key → ℝ) : Integer.Sparse.eval row6788 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck6788, Integer.Sparse.eval_collectBalanced, rawRowCheck6788]

def rawRow6789 : Integer.Sparse Key := [(key2086, -1), (key2070, -1), (key2070, 2), (key2080, -1), (key2064, -1), (key2080, 2), (key2034, 2), (key2064, -1), (key2034, -1), (key2061, 2), (key2061, -1), (key2031, -1), (key2188, 1), (key2167, 1), (key2167, -2), (key2177, 1), (key2153, 1), (key2177, -2), (key2034, -2), (key2153, 1), (key2034, 1), (key2150, -2), (key2150, 1), (key2031, 1), (key2288, -1), (key2167, -1), (key2254, 1), (key2167, 1), (key2280, 1), (key2070, 1), (key2247, -1), (key2070, -1), (key2277, -1), (key2153, -1), (key2277, 1), (key2064, 1), (key2243, 1), (key2150, 1), (key2243, -1), (key2061, -1)]

theorem rawRowCheck6789 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 0, -1] GramFunctions.Block2.form2 = rawRow6789 := by decide +kernel

def row6789 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

theorem rowCheck6789 : row6789 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6789 := by decide +kernel

theorem rowEval6789 (x : Key → ℝ) : Integer.Sparse.eval row6789 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 0, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6789, Integer.Sparse.eval_collectBalanced, rawRowCheck6789]

def rawRow6790 : Integer.Sparse Key := [(key2150, -1), (key2153, -1), (key2177, 2), (key2150, -1), (key2153, -1), (key2243, 2), (key2247, 2), (key2277, -1), (key2280, -1), (key2177, 2), (key2277, -1), (key2280, -1), (key2061, 1), (key2064, 1), (key2080, -2), (key2061, 1), (key2064, 1), (key2243, -2), (key2254, -2), (key2277, 1), (key2288, 1), (key2080, -2), (key2277, 1), (key2288, 1), (key2061, -1), (key2070, -1), (key2080, 1), (key2086, 1), (key2150, 1), (key2167, 1), (key2177, -1), (key2188, -1), (key2061, -1), (key2070, -1), (key2150, 1), (key2167, 1), (key2080, 1), (key2086, 1), (key2177, -1), (key2188, -1)]

theorem rawRowCheck6790 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block2.form2 = rawRow6790 := by decide +kernel

def row6790 : Integer.Sparse Key := [(key2064, 2), (key2070, -2), (key2080, -2), (key2086, 2), (key2153, -2), (key2167, 2), (key2177, 2), (key2188, -2), (key2247, 2), (key2254, -2), (key2280, -2), (key2288, 2)]

theorem rowCheck6790 : row6790 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6790 := by decide +kernel

theorem rowEval6790 (x : Key → ℝ) : Integer.Sparse.eval row6790 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6790, Integer.Sparse.eval_collectBalanced, rawRowCheck6790]

def rawRow6791 : Integer.Sparse Key := [(key2153, -1), (key2150, -1), (key2177, 2), (key2153, -1), (key2150, -1), (key2247, 2), (key2243, 2), (key2280, -1), (key2277, -1), (key2177, 2), (key2280, -1), (key2277, -1), (key2064, 1), (key2061, 1), (key2080, -2), (key2064, 1), (key2061, 1), (key2254, -2), (key2243, -2), (key2288, 1), (key2277, 1), (key2080, -2), (key2288, 1), (key2277, 1), (key2070, -1), (key2061, -1), (key2086, 1), (key2080, 1), (key2167, 1), (key2150, 1), (key2188, -1), (key2177, -1), (key2070, -1), (key2061, -1), (key2167, 1), (key2150, 1), (key2086, 1), (key2080, 1), (key2188, -1), (key2177, -1)]

theorem rawRowCheck6791 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block2.form2 = rawRow6791 := by decide +kernel

def row6791 : Integer.Sparse Key := [(key2064, 2), (key2070, -2), (key2080, -2), (key2086, 2), (key2153, -2), (key2167, 2), (key2177, 2), (key2188, -2), (key2247, 2), (key2254, -2), (key2280, -2), (key2288, 2)]

theorem rowCheck6791 : row6791 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6791 := by decide +kernel

theorem rowEval6791 (x : Key → ℝ) : Integer.Sparse.eval row6791 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck6791, Integer.Sparse.eval_collectBalanced, rawRowCheck6791]

def rawRow6792 : Integer.Sparse Key := [(key2150, -1), (key2177, -1), (key2153, 2), (key2243, -1), (key2277, -1), (key2150, 2), (key2280, 2), (key2153, -1), (key2247, -1), (key2277, 2), (key2177, -1), (key2280, -1), (key2061, 1), (key2080, 1), (key2064, -2), (key2243, 1), (key2277, 1), (key2061, -2), (key2288, -2), (key2064, 1), (key2254, 1), (key2277, -2), (key2080, 1), (key2288, 1), (key2031, -1), (key2086, -1), (key2034, 1), (key2070, 1), (key2031, 1), (key2188, 1), (key2034, -1), (key2167, -1), (key2150, -1), (key2280, -1), (key2061, 1), (key2288, 1), (key2177, 1), (key2280, 1), (key2080, -1), (key2288, -1)]

theorem rawRowCheck6792 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block2.form2 = rawRow6792 := by decide +kernel

def row6792 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

theorem rowCheck6792 : row6792 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6792 := by decide +kernel

theorem rowEval6792 (x : Key → ℝ) : Integer.Sparse.eval row6792 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6792, Integer.Sparse.eval_collectBalanced, rawRowCheck6792]

def rawRow6793 : Integer.Sparse Key := [(key2177, -1), (key2150, -1), (key2153, 2), (key2277, -1), (key2243, -1), (key2280, 2), (key2150, 2), (key2247, -1), (key2153, -1), (key2277, 2), (key2280, -1), (key2177, -1), (key2080, 1), (key2061, 1), (key2064, -2), (key2277, 1), (key2243, 1), (key2288, -2), (key2061, -2), (key2254, 1), (key2064, 1), (key2277, -2), (key2288, 1), (key2080, 1), (key2086, -1), (key2031, -1), (key2070, 1), (key2034, 1), (key2188, 1), (key2031, 1), (key2167, -1), (key2034, -1), (key2280, -1), (key2150, -1), (key2288, 1), (key2061, 1), (key2280, 1), (key2177, 1), (key2288, -1), (key2080, -1)]

theorem rawRowCheck6793 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block2.form2 = rawRow6793 := by decide +kernel

def row6793 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

theorem rowCheck6793 : row6793 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6793 := by decide +kernel

theorem rowEval6793 (x : Key → ℝ) : Integer.Sparse.eval row6793 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6793, Integer.Sparse.eval_collectBalanced, rawRowCheck6793]

def rawRow6794 : Integer.Sparse Key := [(key2153, -1), (key2177, -1), (key2150, 2), (key2247, -1), (key2280, -1), (key2153, 2), (key2277, 2), (key2150, -1), (key2243, -1), (key2280, 2), (key2177, -1), (key2277, -1), (key2064, 1), (key2080, 1), (key2061, -2), (key2254, 1), (key2288, 1), (key2064, -2), (key2277, -2), (key2061, 1), (key2243, 1), (key2288, -2), (key2080, 1), (key2277, 1), (key2034, -1), (key2080, -1), (key2031, 1), (key2061, 1), (key2034, 1), (key2177, 1), (key2031, -1), (key2150, -1), (key2167, -1), (key2288, -1), (key2070, 1), (key2280, 1), (key2188, 1), (key2288, 1), (key2086, -1), (key2280, -1)]

theorem rawRowCheck6794 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block2.form2 = rawRow6794 := by decide +kernel

def row6794 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

theorem rowCheck6794 : row6794 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6794 := by decide +kernel

theorem rowEval6794 (x : Key → ℝ) : Integer.Sparse.eval row6794 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck6794, Integer.Sparse.eval_collectBalanced, rawRowCheck6794]

def rawRow6795 : Integer.Sparse Key := [(key2177, -1), (key2153, -1), (key2150, 2), (key2280, -1), (key2247, -1), (key2277, 2), (key2153, 2), (key2243, -1), (key2150, -1), (key2280, 2), (key2277, -1), (key2177, -1), (key2080, 1), (key2064, 1), (key2061, -2), (key2288, 1), (key2254, 1), (key2277, -2), (key2064, -2), (key2243, 1), (key2061, 1), (key2288, -2), (key2277, 1), (key2080, 1), (key2080, -1), (key2034, -1), (key2061, 1), (key2031, 1), (key2177, 1), (key2034, 1), (key2150, -1), (key2031, -1), (key2288, -1), (key2167, -1), (key2280, 1), (key2070, 1), (key2288, 1), (key2188, 1), (key2280, -1), (key2086, -1)]

theorem rawRowCheck6795 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block2.form2 = rawRow6795 := by decide +kernel

def row6795 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

theorem rowCheck6795 : row6795 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6795 := by decide +kernel

theorem rowEval6795 (x : Key → ℝ) : Integer.Sparse.eval row6795 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6795, Integer.Sparse.eval_collectBalanced, rawRowCheck6795]

def rawRow6796 : Integer.Sparse Key := [(key2243, -1), (key2277, -1), (key2277, 2), (key2150, -1), (key2177, -1), (key2150, 2), (key2280, 2), (key2177, -1), (key2280, -1), (key2153, 2), (key2153, -1), (key2247, -1), (key2243, 1), (key2277, 1), (key2277, -2), (key2061, 1), (key2080, 1), (key2061, -2), (key2288, -2), (key2080, 1), (key2288, 1), (key2064, -2), (key2064, 1), (key2254, 1), (key2150, -1), (key2280, -1), (key2177, 1), (key2280, 1), (key2061, 1), (key2288, 1), (key2080, -1), (key2288, -1), (key2031, -1), (key2086, -1), (key2031, 1), (key2188, 1), (key2034, 1), (key2070, 1), (key2034, -1), (key2167, -1)]

theorem rawRowCheck6796 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block2.form2 = rawRow6796 := by decide +kernel

def row6796 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

theorem rowCheck6796 : row6796 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6796 := by decide +kernel

theorem rowEval6796 (x : Key → ℝ) : Integer.Sparse.eval row6796 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6796, Integer.Sparse.eval_collectBalanced, rawRowCheck6796]

def rawRow6797 : Integer.Sparse Key := [(key2277, -1), (key2243, -1), (key2277, 2), (key2177, -1), (key2150, -1), (key2280, 2), (key2150, 2), (key2280, -1), (key2177, -1), (key2153, 2), (key2247, -1), (key2153, -1), (key2277, 1), (key2243, 1), (key2277, -2), (key2080, 1), (key2061, 1), (key2288, -2), (key2061, -2), (key2288, 1), (key2080, 1), (key2064, -2), (key2254, 1), (key2064, 1), (key2280, -1), (key2150, -1), (key2280, 1), (key2177, 1), (key2288, 1), (key2061, 1), (key2288, -1), (key2080, -1), (key2086, -1), (key2031, -1), (key2188, 1), (key2031, 1), (key2070, 1), (key2034, 1), (key2167, -1), (key2034, -1)]

theorem rawRowCheck6797 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block2.form2 = rawRow6797 := by decide +kernel

def row6797 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

theorem rowCheck6797 : row6797 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6797 := by decide +kernel

theorem rowEval6797 (x : Key → ℝ) : Integer.Sparse.eval row6797 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6797, Integer.Sparse.eval_collectBalanced, rawRowCheck6797]

def rawRow6798 : Integer.Sparse Key := [(key2277, -1), (key2277, -1), (key2243, 2), (key2280, -1), (key2280, -1), (key2177, 2), (key2177, 2), (key2150, -1), (key2150, -1), (key2247, 2), (key2153, -1), (key2153, -1), (key2277, 1), (key2277, 1), (key2243, -2), (key2288, 1), (key2288, 1), (key2080, -2), (key2080, -2), (key2061, 1), (key2061, 1), (key2254, -2), (key2064, 1), (key2064, 1), (key2177, -1), (key2177, -1), (key2150, 1), (key2150, 1), (key2080, 1), (key2080, 1), (key2061, -1), (key2061, -1), (key2188, -1), (key2188, -1), (key2086, 1), (key2086, 1), (key2167, 1), (key2167, 1), (key2070, -1), (key2070, -1)]

theorem rawRowCheck6798 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block2.form2 = rawRow6798 := by decide +kernel

def row6798 : Integer.Sparse Key := [(key2064, 2), (key2070, -2), (key2080, -2), (key2086, 2), (key2153, -2), (key2167, 2), (key2177, 2), (key2188, -2), (key2247, 2), (key2254, -2), (key2280, -2), (key2288, 2)]

theorem rowCheck6798 : row6798 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6798 := by decide +kernel

theorem rowEval6798 (x : Key → ℝ) : Integer.Sparse.eval row6798 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6798, Integer.Sparse.eval_collectBalanced, rawRowCheck6798]

def rawRow6799 : Integer.Sparse Key := [(key2247, -1), (key2280, -1), (key2280, 2), (key2153, -1), (key2177, -1), (key2153, 2), (key2277, 2), (key2177, -1), (key2277, -1), (key2150, 2), (key2150, -1), (key2243, -1), (key2254, 1), (key2288, 1), (key2288, -2), (key2064, 1), (key2080, 1), (key2064, -2), (key2277, -2), (key2080, 1), (key2277, 1), (key2061, -2), (key2061, 1), (key2243, 1), (key2167, -1), (key2288, -1), (key2188, 1), (key2288, 1), (key2070, 1), (key2280, 1), (key2086, -1), (key2280, -1), (key2034, -1), (key2080, -1), (key2034, 1), (key2177, 1), (key2031, 1), (key2061, 1), (key2031, -1), (key2150, -1)]

theorem rawRowCheck6799 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -1, 0] GramFunctions.Block2.form2 = rawRow6799 := by decide +kernel

def row6799 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

theorem rowCheck6799 : row6799 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6799 := by decide +kernel

theorem rowEval6799 (x : Key → ℝ) : Integer.Sparse.eval row6799 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck6799, Integer.Sparse.eval_collectBalanced, rawRowCheck6799]

def rawRow6800 : Integer.Sparse Key := [(key2280, -1), (key2247, -1), (key2280, 2), (key2177, -1), (key2153, -1), (key2277, 2), (key2153, 2), (key2277, -1), (key2177, -1), (key2150, 2), (key2243, -1), (key2150, -1), (key2288, 1), (key2254, 1), (key2288, -2), (key2080, 1), (key2064, 1), (key2277, -2), (key2064, -2), (key2277, 1), (key2080, 1), (key2061, -2), (key2243, 1), (key2061, 1), (key2288, -1), (key2167, -1), (key2288, 1), (key2188, 1), (key2280, 1), (key2070, 1), (key2280, -1), (key2086, -1), (key2080, -1), (key2034, -1), (key2177, 1), (key2034, 1), (key2061, 1), (key2031, 1), (key2150, -1), (key2031, -1)]

theorem rawRowCheck6800 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 0, -1] GramFunctions.Block2.form2 = rawRow6800 := by decide +kernel

def row6800 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

theorem rowCheck6800 : row6800 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6800 := by decide +kernel

theorem rowEval6800 (x : Key → ℝ) : Integer.Sparse.eval row6800 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 0, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6800, Integer.Sparse.eval_collectBalanced, rawRowCheck6800]

def rawRow6801 : Integer.Sparse Key := [(key2280, -1), (key2280, -1), (key2247, 2), (key2277, -1), (key2277, -1), (key2177, 2), (key2177, 2), (key2153, -1), (key2153, -1), (key2243, 2), (key2150, -1), (key2150, -1), (key2288, 1), (key2288, 1), (key2254, -2), (key2277, 1), (key2277, 1), (key2080, -2), (key2080, -2), (key2064, 1), (key2064, 1), (key2243, -2), (key2061, 1), (key2061, 1), (key2188, -1), (key2188, -1), (key2167, 1), (key2167, 1), (key2086, 1), (key2086, 1), (key2070, -1), (key2070, -1), (key2177, -1), (key2177, -1), (key2080, 1), (key2080, 1), (key2150, 1), (key2150, 1), (key2061, -1), (key2061, -1)]

theorem rawRowCheck6801 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -1, -1] GramFunctions.Block2.form2 = rawRow6801 := by decide +kernel

def row6801 : Integer.Sparse Key := [(key2064, 2), (key2070, -2), (key2080, -2), (key2086, 2), (key2153, -2), (key2167, 2), (key2177, 2), (key2188, -2), (key2247, 2), (key2254, -2), (key2280, -2), (key2288, 2)]

theorem rowCheck6801 : row6801 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6801 := by decide +kernel

theorem rowEval6801 (x : Key → ℝ) : Integer.Sparse.eval row6801 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -1, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6801, Integer.Sparse.eval_collectBalanced, rawRowCheck6801]

def rawRow6802 : Integer.Sparse Key := [(key2167, -1), (key2167, -1), (key2188, 2), (key2167, -1), (key2167, -1), (key2254, 2), (key2254, 2), (key2288, -1), (key2288, -1), (key2188, 2), (key2288, -1), (key2288, -1), (key2070, 1), (key2070, 1), (key2086, -2), (key2070, 1), (key2070, 1), (key2247, -2), (key2247, -2), (key2280, 1), (key2280, 1), (key2086, -2), (key2280, 1), (key2280, 1), (key2064, -1), (key2064, -1), (key2080, 1), (key2080, 1), (key2153, 1), (key2153, 1), (key2177, -1), (key2177, -1), (key2064, -1), (key2064, -1), (key2153, 1), (key2153, 1), (key2080, 1), (key2080, 1), (key2177, -1), (key2177, -1)]

theorem rawRowCheck6802 : GramPolynomial.normalizedRow 0 ![1, 1, -1, -1, 0, 0] GramFunctions.Block2.form2 = rawRow6802 := by decide +kernel

def row6802 : Integer.Sparse Key := [(key2064, -4), (key2070, 4), (key2080, 4), (key2086, -4), (key2153, 4), (key2167, -4), (key2177, -4), (key2188, 4), (key2247, -4), (key2254, 4), (key2280, 4), (key2288, -4)]

theorem rowCheck6802 : row6802 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6802 := by decide +kernel

theorem rowEval6802 (x : Key → ℝ) : Integer.Sparse.eval row6802 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, -1, 0, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck6802, Integer.Sparse.eval_collectBalanced, rawRowCheck6802]

def rawRow6803 : Integer.Sparse Key := [(key2167, -1), (key2188, -1), (key2167, 2), (key2254, -1), (key2288, -1), (key2167, 2), (key2288, 2), (key2167, -1), (key2254, -1), (key2288, 2), (key2188, -1), (key2288, -1), (key2070, 1), (key2086, 1), (key2070, -2), (key2247, 1), (key2280, 1), (key2070, -2), (key2280, -2), (key2070, 1), (key2247, 1), (key2280, -2), (key2086, 1), (key2280, 1), (key2034, -1), (key2080, -1), (key2034, 1), (key2064, 1), (key2034, 1), (key2177, 1), (key2034, -1), (key2153, -1), (key2153, -1), (key2277, -1), (key2064, 1), (key2277, 1), (key2177, 1), (key2277, 1), (key2080, -1), (key2277, -1)]

theorem rawRowCheck6803 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -1, 0] GramFunctions.Block2.form2 = rawRow6803 := by decide +kernel

def row6803 : Integer.Sparse Key := [(key2064, 2), (key2070, -2), (key2080, -2), (key2086, 2), (key2153, -2), (key2167, 2), (key2177, 2), (key2188, -2), (key2247, 2), (key2254, -2), (key2280, -2), (key2288, 2)]

theorem rowCheck6803 : row6803 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6803 := by decide +kernel

theorem rowEval6803 (x : Key → ℝ) : Integer.Sparse.eval row6803 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck6803, Integer.Sparse.eval_collectBalanced, rawRowCheck6803]

def rawRow6804 : Integer.Sparse Key := [(key2188, -1), (key2167, -1), (key2167, 2), (key2288, -1), (key2254, -1), (key2288, 2), (key2167, 2), (key2254, -1), (key2167, -1), (key2288, 2), (key2288, -1), (key2188, -1), (key2086, 1), (key2070, 1), (key2070, -2), (key2280, 1), (key2247, 1), (key2280, -2), (key2070, -2), (key2247, 1), (key2070, 1), (key2280, -2), (key2280, 1), (key2086, 1), (key2080, -1), (key2034, -1), (key2064, 1), (key2034, 1), (key2177, 1), (key2034, 1), (key2153, -1), (key2034, -1), (key2277, -1), (key2153, -1), (key2277, 1), (key2064, 1), (key2277, 1), (key2177, 1), (key2277, -1), (key2080, -1)]

theorem rawRowCheck6804 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 0, -1] GramFunctions.Block2.form2 = rawRow6804 := by decide +kernel

def row6804 : Integer.Sparse Key := [(key2064, 2), (key2070, -2), (key2080, -2), (key2086, 2), (key2153, -2), (key2167, 2), (key2177, 2), (key2188, -2), (key2247, 2), (key2254, -2), (key2280, -2), (key2288, 2)]

theorem rowCheck6804 : row6804 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6804 := by decide +kernel

theorem rowEval6804 (x : Key → ℝ) : Integer.Sparse.eval row6804 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 0, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6804, Integer.Sparse.eval_collectBalanced, rawRowCheck6804]

def rawRow6805 : Integer.Sparse Key := [(key2254, -1), (key2288, -1), (key2288, 2), (key2167, -1), (key2188, -1), (key2167, 2), (key2288, 2), (key2188, -1), (key2288, -1), (key2167, 2), (key2167, -1), (key2254, -1), (key2247, 1), (key2280, 1), (key2280, -2), (key2070, 1), (key2086, 1), (key2070, -2), (key2280, -2), (key2086, 1), (key2280, 1), (key2070, -2), (key2070, 1), (key2247, 1), (key2153, -1), (key2277, -1), (key2177, 1), (key2277, 1), (key2064, 1), (key2277, 1), (key2080, -1), (key2277, -1), (key2034, -1), (key2080, -1), (key2034, 1), (key2177, 1), (key2034, 1), (key2064, 1), (key2034, -1), (key2153, -1)]

theorem rawRowCheck6805 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -1, 0] GramFunctions.Block2.form2 = rawRow6805 := by decide +kernel

def row6805 : Integer.Sparse Key := [(key2064, 2), (key2070, -2), (key2080, -2), (key2086, 2), (key2153, -2), (key2167, 2), (key2177, 2), (key2188, -2), (key2247, 2), (key2254, -2), (key2280, -2), (key2288, 2)]

theorem rowCheck6805 : row6805 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6805 := by decide +kernel

theorem rowEval6805 (x : Key → ℝ) : Integer.Sparse.eval row6805 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck6805, Integer.Sparse.eval_collectBalanced, rawRowCheck6805]

def rawRow6806 : Integer.Sparse Key := [(key2288, -1), (key2254, -1), (key2288, 2), (key2188, -1), (key2167, -1), (key2288, 2), (key2167, 2), (key2288, -1), (key2188, -1), (key2167, 2), (key2254, -1), (key2167, -1), (key2280, 1), (key2247, 1), (key2280, -2), (key2086, 1), (key2070, 1), (key2280, -2), (key2070, -2), (key2280, 1), (key2086, 1), (key2070, -2), (key2247, 1), (key2070, 1), (key2277, -1), (key2153, -1), (key2277, 1), (key2177, 1), (key2277, 1), (key2064, 1), (key2277, -1), (key2080, -1), (key2080, -1), (key2034, -1), (key2177, 1), (key2034, 1), (key2064, 1), (key2034, 1), (key2153, -1), (key2034, -1)]

theorem rawRowCheck6806 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 0, -1] GramFunctions.Block2.form2 = rawRow6806 := by decide +kernel

def row6806 : Integer.Sparse Key := [(key2064, 2), (key2070, -2), (key2080, -2), (key2086, 2), (key2153, -2), (key2167, 2), (key2177, 2), (key2188, -2), (key2247, 2), (key2254, -2), (key2280, -2), (key2288, 2)]

theorem rowCheck6806 : row6806 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6806 := by decide +kernel

theorem rowEval6806 (x : Key → ℝ) : Integer.Sparse.eval row6806 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 0, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6806, Integer.Sparse.eval_collectBalanced, rawRowCheck6806]

def rawRow6807 : Integer.Sparse Key := [(key2288, -1), (key2288, -1), (key2254, 2), (key2288, -1), (key2288, -1), (key2188, 2), (key2188, 2), (key2167, -1), (key2167, -1), (key2254, 2), (key2167, -1), (key2167, -1), (key2280, 1), (key2280, 1), (key2247, -2), (key2280, 1), (key2280, 1), (key2086, -2), (key2086, -2), (key2070, 1), (key2070, 1), (key2247, -2), (key2070, 1), (key2070, 1), (key2177, -1), (key2177, -1), (key2153, 1), (key2153, 1), (key2080, 1), (key2080, 1), (key2064, -1), (key2064, -1), (key2177, -1), (key2177, -1), (key2080, 1), (key2080, 1), (key2153, 1), (key2153, 1), (key2064, -1), (key2064, -1)]

theorem rawRowCheck6807 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -1, -1] GramFunctions.Block2.form2 = rawRow6807 := by decide +kernel

def row6807 : Integer.Sparse Key := [(key2064, -4), (key2070, 4), (key2080, 4), (key2086, -4), (key2153, 4), (key2167, -4), (key2177, -4), (key2188, 4), (key2247, -4), (key2254, 4), (key2280, 4), (key2288, -4)]

theorem rowCheck6807 : row6807 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6807 := by decide +kernel

theorem rowEval6807 (x : Key → ℝ) : Integer.Sparse.eval row6807 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -1, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6807, Integer.Sparse.eval_collectBalanced, rawRowCheck6807]

def rawRow6808 : Integer.Sparse Key := [(key66, -4), (key66, 2), (key67, 2), (key78, 2), (key80, 2), (key80, -4), (key708, 2), (key708, -1), (key711, -1), (key862, 2), (key862, -1), (key887, -1), (key894, -1), (key896, -1), (key894, -1), (key917, -1), (key896, 2), (key917, 2), (key717, -1), (key719, -1), (key719, 2), (key894, -1), (key896, -1), (key894, 2), (key917, 2), (key896, -1), (key917, -1), (key949, 2), (key949, -1), (key956, -1)]

theorem rawRowCheck6808 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block2.form3 = rawRow6808 := by decide +kernel

def row6808 : Integer.Sparse Key := [(key66, -2), (key67, 2), (key78, 2), (key80, -2), (key708, 1), (key711, -1), (key717, -1), (key719, 1), (key862, 1), (key887, -1), (key894, -1), (key896, -1), (key917, 2), (key949, 1), (key956, -1)]

theorem rowCheck6808 : row6808 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6808 := by decide +kernel

theorem rowEval6808 (x : Key → ℝ) : Integer.Sparse.eval row6808 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6808, Integer.Sparse.eval_collectBalanced, rawRowCheck6808]

def rawRow6809 : Integer.Sparse Key := [(key66, -4), (key67, 2), (key66, 2), (key80, 2), (key78, 2), (key80, -4), (key708, 2), (key711, -1), (key708, -1), (key862, 2), (key887, -1), (key862, -1), (key896, -1), (key894, -1), (key917, -1), (key894, -1), (key917, 2), (key896, 2), (key719, -1), (key717, -1), (key719, 2), (key896, -1), (key894, -1), (key917, 2), (key894, 2), (key917, -1), (key896, -1), (key949, 2), (key956, -1), (key949, -1)]

theorem rawRowCheck6809 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block2.form3 = rawRow6809 := by decide +kernel

def row6809 : Integer.Sparse Key := [(key66, -2), (key67, 2), (key78, 2), (key80, -2), (key708, 1), (key711, -1), (key717, -1), (key719, 1), (key862, 1), (key887, -1), (key894, -1), (key896, -1), (key917, 2), (key949, 1), (key956, -1)]

theorem rowCheck6809 : row6809 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6809 := by decide +kernel

theorem rowEval6809 (x : Key → ℝ) : Integer.Sparse.eval row6809 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6809, Integer.Sparse.eval_collectBalanced, rawRowCheck6809]

def rawRow6810 : Integer.Sparse Key := [(key67, -4), (key66, 2), (key66, 2), (key80, 2), (key80, 2), (key78, -4), (key711, 2), (key708, -1), (key708, -1), (key887, 2), (key862, -1), (key862, -1), (key917, -1), (key917, -1), (key896, -1), (key896, -1), (key894, 2), (key894, 2), (key719, -1), (key719, -1), (key717, 2), (key917, -1), (key917, -1), (key896, 2), (key896, 2), (key894, -1), (key894, -1), (key956, 2), (key949, -1), (key949, -1)]

theorem rawRowCheck6810 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block2.form3 = rawRow6810 := by decide +kernel

def row6810 : Integer.Sparse Key := [(key66, 4), (key67, -4), (key78, -4), (key80, 4), (key708, -2), (key711, 2), (key717, 2), (key719, -2), (key862, -2), (key887, 2), (key894, 2), (key896, 2), (key917, -4), (key949, -2), (key956, 2)]

theorem rowCheck6810 : row6810 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6810 := by decide +kernel

theorem rowEval6810 (x : Key → ℝ) : Integer.Sparse.eval row6810 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6810, Integer.Sparse.eval_collectBalanced, rawRowCheck6810]

def rawRow6811 : Integer.Sparse Key := [(key66, -4), (key78, 2), (key80, 2), (key66, 2), (key67, 2), (key80, -4), (key862, 2), (key894, -1), (key896, -1), (key708, 2), (key894, -1), (key917, -1), (key708, -1), (key711, -1), (key862, -1), (key887, -1), (key896, 2), (key917, 2), (key894, -1), (key896, -1), (key949, 2), (key717, -1), (key719, -1), (key894, 2), (key917, 2), (key949, -1), (key956, -1), (key719, 2), (key896, -1), (key917, -1)]

theorem rawRowCheck6811 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block2.form3 = rawRow6811 := by decide +kernel

def row6811 : Integer.Sparse Key := [(key66, -2), (key67, 2), (key78, 2), (key80, -2), (key708, 1), (key711, -1), (key717, -1), (key719, 1), (key862, 1), (key887, -1), (key894, -1), (key896, -1), (key917, 2), (key949, 1), (key956, -1)]

theorem rowCheck6811 : row6811 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6811 := by decide +kernel

theorem rowEval6811 (x : Key → ℝ) : Integer.Sparse.eval row6811 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6811, Integer.Sparse.eval_collectBalanced, rawRowCheck6811]

def rawRow6812 : Integer.Sparse Key := [(key66, -4), (key80, 2), (key78, 2), (key67, 2), (key66, 2), (key80, -4), (key862, 2), (key896, -1), (key894, -1), (key708, 2), (key917, -1), (key894, -1), (key711, -1), (key708, -1), (key887, -1), (key862, -1), (key917, 2), (key896, 2), (key896, -1), (key894, -1), (key949, 2), (key719, -1), (key717, -1), (key917, 2), (key894, 2), (key956, -1), (key949, -1), (key719, 2), (key917, -1), (key896, -1)]

theorem rawRowCheck6812 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block2.form3 = rawRow6812 := by decide +kernel

def row6812 : Integer.Sparse Key := [(key66, -2), (key67, 2), (key78, 2), (key80, -2), (key708, 1), (key711, -1), (key717, -1), (key719, 1), (key862, 1), (key887, -1), (key894, -1), (key896, -1), (key917, 2), (key949, 1), (key956, -1)]

theorem rowCheck6812 : row6812 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6812 := by decide +kernel

theorem rowEval6812 (x : Key → ℝ) : Integer.Sparse.eval row6812 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6812, Integer.Sparse.eval_collectBalanced, rawRowCheck6812]

def rawRow6813 : Integer.Sparse Key := [(key78, -4), (key66, 2), (key80, 2), (key66, 2), (key80, 2), (key67, -4), (key894, 2), (key862, -1), (key896, -1), (key894, 2), (key708, -1), (key917, -1), (key862, -1), (key896, -1), (key708, -1), (key917, -1), (key711, 2), (key887, 2), (key894, -1), (key949, -1), (key896, 2), (key894, -1), (key949, -1), (key717, 2), (key956, 2), (key719, -1), (key917, -1), (key896, 2), (key719, -1), (key917, -1)]

theorem rawRowCheck6813 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block2.form3 = rawRow6813 := by decide +kernel

def row6813 : Integer.Sparse Key := [(key66, 4), (key67, -4), (key78, -4), (key80, 4), (key708, -2), (key711, 2), (key717, 2), (key719, -2), (key862, -2), (key887, 2), (key894, 2), (key896, 2), (key917, -4), (key949, -2), (key956, 2)]

theorem rowCheck6813 : row6813 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6813 := by decide +kernel

theorem rowEval6813 (x : Key → ℝ) : Integer.Sparse.eval row6813 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6813, Integer.Sparse.eval_collectBalanced, rawRowCheck6813]

def rawRow6814 : Integer.Sparse Key := [(key78, -4), (key80, 2), (key66, 2), (key80, 2), (key66, 2), (key67, -4), (key894, 2), (key896, -1), (key862, -1), (key894, 2), (key917, -1), (key708, -1), (key896, -1), (key862, -1), (key917, -1), (key708, -1), (key887, 2), (key711, 2), (key949, -1), (key894, -1), (key896, 2), (key949, -1), (key894, -1), (key956, 2), (key717, 2), (key917, -1), (key719, -1), (key896, 2), (key917, -1), (key719, -1)]

theorem rawRowCheck6814 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block2.form3 = rawRow6814 := by decide +kernel

def row6814 : Integer.Sparse Key := [(key66, 4), (key67, -4), (key78, -4), (key80, 4), (key708, -2), (key711, 2), (key717, 2), (key719, -2), (key862, -2), (key887, 2), (key894, 2), (key896, 2), (key917, -4), (key949, -2), (key956, 2)]

theorem rowCheck6814 : row6814 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6814 := by decide +kernel

theorem rowEval6814 (x : Key → ℝ) : Integer.Sparse.eval row6814 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6814, Integer.Sparse.eval_collectBalanced, rawRowCheck6814]

def rawRow6815 : Integer.Sparse Key := [(key80, -4), (key66, 2), (key78, 2), (key67, 2), (key80, 2), (key66, -4), (key896, 2), (key862, -1), (key894, -1), (key917, 2), (key708, -1), (key894, -1), (key887, -1), (key917, -1), (key711, -1), (key896, -1), (key708, 2), (key862, 2), (key896, -1), (key949, -1), (key894, 2), (key917, -1), (key956, -1), (key719, 2), (key949, 2), (key717, -1), (key894, -1), (key917, 2), (key719, -1), (key896, -1)]

theorem rawRowCheck6815 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block2.form3 = rawRow6815 := by decide +kernel

def row6815 : Integer.Sparse Key := [(key66, -2), (key67, 2), (key78, 2), (key80, -2), (key708, 1), (key711, -1), (key717, -1), (key719, 1), (key862, 1), (key887, -1), (key894, -1), (key896, -1), (key917, 2), (key949, 1), (key956, -1)]

theorem rowCheck6815 : row6815 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6815 := by decide +kernel

theorem rowEval6815 (x : Key → ℝ) : Integer.Sparse.eval row6815 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6815, Integer.Sparse.eval_collectBalanced, rawRowCheck6815]

def rawRow6816 : Integer.Sparse Key := [(key80, -4), (key78, 2), (key66, 2), (key80, 2), (key67, 2), (key66, -4), (key896, 2), (key894, -1), (key862, -1), (key917, 2), (key894, -1), (key708, -1), (key917, -1), (key887, -1), (key896, -1), (key711, -1), (key862, 2), (key708, 2), (key949, -1), (key896, -1), (key894, 2), (key956, -1), (key917, -1), (key949, 2), (key719, 2), (key894, -1), (key717, -1), (key917, 2), (key896, -1), (key719, -1)]

theorem rawRowCheck6816 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block2.form3 = rawRow6816 := by decide +kernel

def row6816 : Integer.Sparse Key := [(key66, -2), (key67, 2), (key78, 2), (key80, -2), (key708, 1), (key711, -1), (key717, -1), (key719, 1), (key862, 1), (key887, -1), (key894, -1), (key896, -1), (key917, 2), (key949, 1), (key956, -1)]

theorem rowCheck6816 : row6816 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6816 := by decide +kernel

theorem rowEval6816 (x : Key → ℝ) : Integer.Sparse.eval row6816 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6816, Integer.Sparse.eval_collectBalanced, rawRowCheck6816]

def rawRow6817 : Integer.Sparse Key := [(key67, -4), (key80, 2), (key80, 2), (key66, 2), (key66, 2), (key78, -4), (key887, 2), (key917, -1), (key917, -1), (key711, 2), (key896, -1), (key896, -1), (key708, -1), (key708, -1), (key862, -1), (key862, -1), (key894, 2), (key894, 2), (key917, -1), (key917, -1), (key956, 2), (key719, -1), (key719, -1), (key896, 2), (key896, 2), (key949, -1), (key949, -1), (key717, 2), (key894, -1), (key894, -1)]

theorem rawRowCheck6817 : GramPolynomial.normalizedRow 0 ![1, -1, 1, -1, 0, 0] GramFunctions.Block2.form3 = rawRow6817 := by decide +kernel

def row6817 : Integer.Sparse Key := [(key66, 4), (key67, -4), (key78, -4), (key80, 4), (key708, -2), (key711, 2), (key717, 2), (key719, -2), (key862, -2), (key887, 2), (key894, 2), (key896, 2), (key917, -4), (key949, -2), (key956, 2)]

theorem rowCheck6817 : row6817 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6817 := by decide +kernel

theorem rowEval6817 (x : Key → ℝ) : Integer.Sparse.eval row6817 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, -1, 0, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6817, Integer.Sparse.eval_collectBalanced, rawRowCheck6817]

def rawRow6818 : Integer.Sparse Key := [(key80, -4), (key67, 2), (key80, 2), (key66, 2), (key78, 2), (key66, -4), (key917, 2), (key887, -1), (key917, -1), (key896, 2), (key711, -1), (key896, -1), (key862, -1), (key894, -1), (key708, -1), (key894, -1), (key708, 2), (key862, 2), (key917, -1), (key956, -1), (key917, 2), (key896, -1), (key949, -1), (key719, 2), (key949, 2), (key719, -1), (key896, -1), (key894, 2), (key717, -1), (key894, -1)]

theorem rawRowCheck6818 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -1, 0] GramFunctions.Block2.form3 = rawRow6818 := by decide +kernel

def row6818 : Integer.Sparse Key := [(key66, -2), (key67, 2), (key78, 2), (key80, -2), (key708, 1), (key711, -1), (key717, -1), (key719, 1), (key862, 1), (key887, -1), (key894, -1), (key896, -1), (key917, 2), (key949, 1), (key956, -1)]

theorem rowCheck6818 : row6818 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6818 := by decide +kernel

theorem rowEval6818 (x : Key → ℝ) : Integer.Sparse.eval row6818 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6818, Integer.Sparse.eval_collectBalanced, rawRowCheck6818]

def rawRow6819 : Integer.Sparse Key := [(key80, -4), (key80, 2), (key67, 2), (key78, 2), (key66, 2), (key66, -4), (key917, 2), (key917, -1), (key887, -1), (key896, 2), (key896, -1), (key711, -1), (key894, -1), (key862, -1), (key894, -1), (key708, -1), (key862, 2), (key708, 2), (key956, -1), (key917, -1), (key917, 2), (key949, -1), (key896, -1), (key949, 2), (key719, 2), (key896, -1), (key719, -1), (key894, 2), (key894, -1), (key717, -1)]

theorem rawRowCheck6819 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 0, -1] GramFunctions.Block2.form3 = rawRow6819 := by decide +kernel

def row6819 : Integer.Sparse Key := [(key66, -2), (key67, 2), (key78, 2), (key80, -2), (key708, 1), (key711, -1), (key717, -1), (key719, 1), (key862, 1), (key887, -1), (key894, -1), (key896, -1), (key917, 2), (key949, 1), (key956, -1)]

theorem rowCheck6819 : row6819 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6819 := by decide +kernel

theorem rowEval6819 (x : Key → ℝ) : Integer.Sparse.eval row6819 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 0, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6819, Integer.Sparse.eval_collectBalanced, rawRowCheck6819]

def rawRow6820 : Integer.Sparse Key := [(key131, -4), (key141, 2), (key143, 2), (key141, 2), (key143, 2), (key160, -4), (key66, 2), (key78, -1), (key80, -1), (key708, 2), (key894, -1), (key917, -1), (key717, -1), (key719, -1), (key894, -1), (key917, -1), (key949, 2), (key956, 2), (key708, -1), (key711, -1), (key719, 2), (key708, -1), (key711, -1), (key862, 2), (key887, 2), (key896, -1), (key917, -1), (key719, 2), (key896, -1), (key917, -1)]

theorem rawRowCheck6820 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block2.form3 = rawRow6820 := by decide +kernel

def row6820 : Integer.Sparse Key := [(key66, 2), (key78, -1), (key80, -1), (key131, -4), (key141, 4), (key143, 4), (key160, -4), (key711, -2), (key717, -1), (key719, 3), (key862, 2), (key887, 2), (key894, -2), (key896, -2), (key917, -4), (key949, 2), (key956, 2)]

theorem rowCheck6820 : row6820 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6820 := by decide +kernel

theorem rowEval6820 (x : Key → ℝ) : Integer.Sparse.eval row6820 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6820, Integer.Sparse.eval_collectBalanced, rawRowCheck6820]

def rawRow6821 : Integer.Sparse Key := [(key131, -4), (key143, 2), (key141, 2), (key143, 2), (key141, 2), (key160, -4), (key66, 2), (key80, -1), (key78, -1), (key708, 2), (key917, -1), (key894, -1), (key719, -1), (key717, -1), (key917, -1), (key894, -1), (key956, 2), (key949, 2), (key711, -1), (key708, -1), (key719, 2), (key711, -1), (key708, -1), (key887, 2), (key862, 2), (key917, -1), (key896, -1), (key719, 2), (key917, -1), (key896, -1)]

theorem rawRowCheck6821 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block2.form3 = rawRow6821 := by decide +kernel

def row6821 : Integer.Sparse Key := [(key66, 2), (key78, -1), (key80, -1), (key131, -4), (key141, 4), (key143, 4), (key160, -4), (key711, -2), (key717, -1), (key719, 3), (key862, 2), (key887, 2), (key894, -2), (key896, -2), (key917, -4), (key949, 2), (key956, 2)]

theorem rowCheck6821 : row6821 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6821 := by decide +kernel

theorem rowEval6821 (x : Key → ℝ) : Integer.Sparse.eval row6821 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6821, Integer.Sparse.eval_collectBalanced, rawRowCheck6821]

def rawRow6822 : Integer.Sparse Key := [(key141, -4), (key131, 2), (key143, 2), (key141, 2), (key160, 2), (key143, -4), (key78, 2), (key66, -1), (key80, -1), (key894, 2), (key708, -1), (key917, -1), (key894, -1), (key949, -1), (key717, -1), (key956, -1), (key719, 2), (key917, 2), (key708, -1), (key719, -1), (key711, 2), (key862, -1), (key896, -1), (key708, 2), (key917, 2), (key711, -1), (key887, -1), (key896, 2), (key719, -1), (key917, -1)]

theorem rawRowCheck6822 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block2.form3 = rawRow6822 := by decide +kernel

def row6822 : Integer.Sparse Key := [(key66, -1), (key78, 2), (key80, -1), (key131, 2), (key141, -2), (key143, -2), (key160, 2), (key711, 1), (key717, -1), (key862, -1), (key887, -1), (key894, 1), (key896, 1), (key917, 2), (key949, -1), (key956, -1)]

theorem rowCheck6822 : row6822 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6822 := by decide +kernel

theorem rowEval6822 (x : Key → ℝ) : Integer.Sparse.eval row6822 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6822, Integer.Sparse.eval_collectBalanced, rawRowCheck6822]

def rawRow6823 : Integer.Sparse Key := [(key141, -4), (key143, 2), (key131, 2), (key160, 2), (key141, 2), (key143, -4), (key78, 2), (key80, -1), (key66, -1), (key894, 2), (key917, -1), (key708, -1), (key949, -1), (key894, -1), (key956, -1), (key717, -1), (key917, 2), (key719, 2), (key719, -1), (key708, -1), (key711, 2), (key896, -1), (key862, -1), (key917, 2), (key708, 2), (key887, -1), (key711, -1), (key896, 2), (key917, -1), (key719, -1)]

theorem rawRowCheck6823 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block2.form3 = rawRow6823 := by decide +kernel

def row6823 : Integer.Sparse Key := [(key66, -1), (key78, 2), (key80, -1), (key131, 2), (key141, -2), (key143, -2), (key160, 2), (key711, 1), (key717, -1), (key862, -1), (key887, -1), (key894, 1), (key896, 1), (key917, 2), (key949, -1), (key956, -1)]

theorem rowCheck6823 : row6823 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6823 := by decide +kernel

theorem rowEval6823 (x : Key → ℝ) : Integer.Sparse.eval row6823 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6823, Integer.Sparse.eval_collectBalanced, rawRowCheck6823]

def rawRow6824 : Integer.Sparse Key := [(key143, -4), (key131, 2), (key141, 2), (key143, 2), (key160, 2), (key141, -4), (key80, 2), (key66, -1), (key78, -1), (key917, 2), (key708, -1), (key894, -1), (key917, -1), (key956, -1), (key719, -1), (key949, -1), (key717, 2), (key894, 2), (key711, -1), (key719, -1), (key708, 2), (key887, -1), (key917, -1), (key711, 2), (key896, 2), (key708, -1), (key862, -1), (key917, 2), (key719, -1), (key896, -1)]

theorem rawRowCheck6824 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block2.form3 = rawRow6824 := by decide +kernel

def row6824 : Integer.Sparse Key := [(key66, -1), (key78, -1), (key80, 2), (key131, 2), (key141, -2), (key143, -2), (key160, 2), (key711, 1), (key717, 2), (key719, -3), (key862, -1), (key887, -1), (key894, 1), (key896, 1), (key917, 2), (key949, -1), (key956, -1)]

theorem rowCheck6824 : row6824 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6824 := by decide +kernel

theorem rowEval6824 (x : Key → ℝ) : Integer.Sparse.eval row6824 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6824, Integer.Sparse.eval_collectBalanced, rawRowCheck6824]

def rawRow6825 : Integer.Sparse Key := [(key143, -4), (key141, 2), (key131, 2), (key160, 2), (key143, 2), (key141, -4), (key80, 2), (key78, -1), (key66, -1), (key917, 2), (key894, -1), (key708, -1), (key956, -1), (key917, -1), (key949, -1), (key719, -1), (key894, 2), (key717, 2), (key719, -1), (key711, -1), (key708, 2), (key917, -1), (key887, -1), (key896, 2), (key711, 2), (key862, -1), (key708, -1), (key917, 2), (key896, -1), (key719, -1)]

theorem rawRowCheck6825 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block2.form3 = rawRow6825 := by decide +kernel

def row6825 : Integer.Sparse Key := [(key66, -1), (key78, -1), (key80, 2), (key131, 2), (key141, -2), (key143, -2), (key160, 2), (key711, 1), (key717, 2), (key719, -3), (key862, -1), (key887, -1), (key894, 1), (key896, 1), (key917, 2), (key949, -1), (key956, -1)]

theorem rowCheck6825 : row6825 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6825 := by decide +kernel

theorem rowEval6825 (x : Key → ℝ) : Integer.Sparse.eval row6825 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6825, Integer.Sparse.eval_collectBalanced, rawRowCheck6825]

def rawRow6826 : Integer.Sparse Key := [(key141, -4), (key141, 2), (key160, 2), (key131, 2), (key143, 2), (key143, -4), (key141, 2), (key141, -1), (key160, -1), (key78, 2), (key717, -1), (key956, -1), (key708, -1), (key719, -1), (key708, -1), (key917, -1), (key719, 2), (key917, 2), (key862, -1), (key896, -1), (key896, 2), (key708, -1), (key719, -1), (key708, 2), (key917, 2), (key719, -1), (key917, -1), (key711, 2), (key711, -1), (key887, -1)]

theorem rawRowCheck6826 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block2.form3 = rawRow6826 := by decide +kernel

def row6826 : Integer.Sparse Key := [(key78, 2), (key131, 2), (key141, -1), (key143, -2), (key160, 1), (key708, -1), (key711, 1), (key717, -1), (key719, -1), (key862, -1), (key887, -1), (key896, 1), (key917, 2), (key956, -1)]

theorem rowCheck6826 : row6826 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6826 := by decide +kernel

theorem rowEval6826 (x : Key → ℝ) : Integer.Sparse.eval row6826 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6826, Integer.Sparse.eval_collectBalanced, rawRowCheck6826]

def rawRow6827 : Integer.Sparse Key := [(key141, -4), (key160, 2), (key141, 2), (key143, 2), (key131, 2), (key143, -4), (key141, 2), (key160, -1), (key141, -1), (key78, 2), (key956, -1), (key717, -1), (key719, -1), (key708, -1), (key917, -1), (key708, -1), (key917, 2), (key719, 2), (key896, -1), (key862, -1), (key896, 2), (key719, -1), (key708, -1), (key917, 2), (key708, 2), (key917, -1), (key719, -1), (key711, 2), (key887, -1), (key711, -1)]

theorem rawRowCheck6827 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block2.form3 = rawRow6827 := by decide +kernel

def row6827 : Integer.Sparse Key := [(key78, 2), (key131, 2), (key141, -1), (key143, -2), (key160, 1), (key708, -1), (key711, 1), (key717, -1), (key719, -1), (key862, -1), (key887, -1), (key896, 1), (key917, 2), (key956, -1)]

theorem rowCheck6827 : row6827 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6827 := by decide +kernel

theorem rowEval6827 (x : Key → ℝ) : Integer.Sparse.eval row6827 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6827, Integer.Sparse.eval_collectBalanced, rawRowCheck6827]

def rawRow6828 : Integer.Sparse Key := [(key160, -4), (key141, 2), (key141, 2), (key143, 2), (key143, 2), (key131, -4), (key160, 2), (key141, -1), (key141, -1), (key191, 2), (key78, -1), (key717, -1), (key917, -1), (key917, -1), (key719, -1), (key719, -1), (key708, 2), (key708, 2), (key896, -1), (key896, -1), (key862, 2), (key917, -1), (key917, -1), (key719, 2), (key719, 2), (key708, -1), (key708, -1), (key887, 2), (key711, -1), (key711, -1)]

theorem rawRowCheck6828 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block2.form3 = rawRow6828 := by decide +kernel

def row6828 : Integer.Sparse Key := [(key78, -1), (key131, -4), (key141, 2), (key143, 4), (key160, -2), (key191, 2), (key708, 2), (key711, -2), (key717, -1), (key719, 2), (key862, 2), (key887, 2), (key896, -2), (key917, -4)]

theorem rowCheck6828 : row6828 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6828 := by decide +kernel

theorem rowEval6828 (x : Key → ℝ) : Integer.Sparse.eval row6828 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6828, Integer.Sparse.eval_collectBalanced, rawRowCheck6828]

def rawRow6829 : Integer.Sparse Key := [(key143, -4), (key143, 2), (key160, 2), (key131, 2), (key141, 2), (key141, -4), (key183, 2), (key183, -1), (key191, -1), (key80, 2), (key80, -1), (key160, -1), (key66, -1), (key78, -1), (key708, -1), (key894, -1), (key717, 2), (key894, 2), (key887, -1), (key917, -1), (key917, 2), (key711, -1), (key719, -1), (key711, 2), (key896, 2), (key719, -1), (key896, -1), (key708, 2), (key708, -1), (key862, -1)]

theorem rawRowCheck6829 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -1, 0] GramFunctions.Block2.form3 = rawRow6829 := by decide +kernel

def row6829 : Integer.Sparse Key := [(key66, -1), (key78, -1), (key80, 1), (key131, 2), (key141, -2), (key143, -2), (key160, 1), (key183, 1), (key191, -1), (key711, 1), (key717, 2), (key719, -2), (key862, -1), (key887, -1), (key894, 1), (key896, 1), (key917, 1)]

theorem rowCheck6829 : row6829 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6829 := by decide +kernel

theorem rowEval6829 (x : Key → ℝ) : Integer.Sparse.eval row6829 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6829, Integer.Sparse.eval_collectBalanced, rawRowCheck6829]

def rawRow6830 : Integer.Sparse Key := [(key143, -4), (key160, 2), (key143, 2), (key141, 2), (key131, 2), (key141, -4), (key183, 2), (key191, -1), (key183, -1), (key80, 2), (key160, -1), (key80, -1), (key78, -1), (key66, -1), (key894, -1), (key708, -1), (key894, 2), (key717, 2), (key917, -1), (key887, -1), (key917, 2), (key719, -1), (key711, -1), (key896, 2), (key711, 2), (key896, -1), (key719, -1), (key708, 2), (key862, -1), (key708, -1)]

theorem rawRowCheck6830 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 0, -1] GramFunctions.Block2.form3 = rawRow6830 := by decide +kernel

def row6830 : Integer.Sparse Key := [(key66, -1), (key78, -1), (key80, 1), (key131, 2), (key141, -2), (key143, -2), (key160, 1), (key183, 1), (key191, -1), (key711, 1), (key717, 2), (key719, -2), (key862, -1), (key887, -1), (key894, 1), (key896, 1), (key917, 1)]

theorem rowCheck6830 : row6830 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6830 := by decide +kernel

theorem rowEval6830 (x : Key → ℝ) : Integer.Sparse.eval row6830 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 0, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6830, Integer.Sparse.eval_collectBalanced, rawRowCheck6830]

def rawRow6831 : Integer.Sparse Key := [(key160, -4), (key143, 2), (key143, 2), (key141, 2), (key141, 2), (key131, -4), (key191, 2), (key183, -1), (key183, -1), (key160, 2), (key80, -1), (key80, -1), (key141, -1), (key141, -1), (key78, -1), (key717, -1), (key708, 2), (key708, 2), (key917, -1), (key917, -1), (key887, 2), (key896, -1), (key896, -1), (key719, 2), (key719, 2), (key711, -1), (key711, -1), (key862, 2), (key708, -1), (key708, -1)]

theorem rawRowCheck6831 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -1, -1] GramFunctions.Block2.form3 = rawRow6831 := by decide +kernel

def row6831 : Integer.Sparse Key := [(key78, -1), (key80, -2), (key131, -4), (key141, 2), (key143, 4), (key160, -2), (key183, -2), (key191, 2), (key708, 2), (key711, -2), (key717, -1), (key719, 4), (key862, 2), (key887, 2), (key896, -2), (key917, -2)]

theorem rowCheck6831 : row6831 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6831 := by decide +kernel

theorem rowEval6831 (x : Key → ℝ) : Integer.Sparse.eval row6831 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -1, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6831, Integer.Sparse.eval_collectBalanced, rawRowCheck6831]

def rawRow6832 : Integer.Sparse Key := [(key178, -4), (key183, 2), (key183, 2), (key183, 2), (key183, 2), (key191, -4), (key67, 2), (key80, -1), (key80, -1), (key67, 2), (key143, -1), (key143, -1), (key80, -1), (key80, -1), (key143, -1), (key143, -1), (key160, 2), (key160, 2), (key66, -1), (key66, -1), (key78, 2), (key708, -1), (key708, -1), (key862, 2), (key862, 2), (key894, -1), (key894, -1), (key717, 2), (key894, -1), (key894, -1)]

theorem rawRowCheck6832 : GramPolynomial.normalizedRow 0 ![1, 1, -1, -1, 0, 0] GramFunctions.Block2.form3 = rawRow6832 := by decide +kernel

def row6832 : Integer.Sparse Key := [(key66, -2), (key67, 4), (key78, 2), (key80, -4), (key143, -4), (key160, 4), (key178, -4), (key183, 8), (key191, -4), (key708, -2), (key717, 2), (key862, 4), (key894, -4)]

theorem rowCheck6832 : row6832 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6832 := by decide +kernel

theorem rowEval6832 (x : Key → ℝ) : Integer.Sparse.eval row6832 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, -1, 0, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6832, Integer.Sparse.eval_collectBalanced, rawRowCheck6832]

def rawRow6833 : Integer.Sparse Key := [(key183, -4), (key178, 2), (key183, 2), (key183, 2), (key191, 2), (key183, -4), (key80, 2), (key67, -1), (key80, -1), (key143, 2), (key67, -1), (key143, -1), (key143, -1), (key160, -1), (key80, -1), (key160, -1), (key80, 2), (key143, 2), (key66, -1), (key78, -1), (key66, 2), (key862, -1), (key894, -1), (key708, 2), (key894, 2), (key708, -1), (key862, -1), (key894, 2), (key717, -1), (key894, -1)]

theorem rawRowCheck6833 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -1, 0] GramFunctions.Block2.form3 = rawRow6833 := by decide +kernel

def row6833 : Integer.Sparse Key := [(key66, 1), (key67, -2), (key78, -1), (key80, 2), (key143, 2), (key160, -2), (key178, 2), (key183, -4), (key191, 2), (key708, 1), (key717, -1), (key862, -2), (key894, 2)]

theorem rowCheck6833 : row6833 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6833 := by decide +kernel

theorem rowEval6833 (x : Key → ℝ) : Integer.Sparse.eval row6833 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6833, Integer.Sparse.eval_collectBalanced, rawRowCheck6833]

def rawRow6834 : Integer.Sparse Key := [(key183, -4), (key183, 2), (key178, 2), (key191, 2), (key183, 2), (key183, -4), (key80, 2), (key80, -1), (key67, -1), (key143, 2), (key143, -1), (key67, -1), (key160, -1), (key143, -1), (key160, -1), (key80, -1), (key143, 2), (key80, 2), (key78, -1), (key66, -1), (key66, 2), (key894, -1), (key862, -1), (key894, 2), (key708, 2), (key862, -1), (key708, -1), (key894, 2), (key894, -1), (key717, -1)]

theorem rawRowCheck6834 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 0, -1] GramFunctions.Block2.form3 = rawRow6834 := by decide +kernel

def row6834 : Integer.Sparse Key := [(key66, 1), (key67, -2), (key78, -1), (key80, 2), (key143, 2), (key160, -2), (key178, 2), (key183, -4), (key191, 2), (key708, 1), (key717, -1), (key862, -2), (key894, 2)]

theorem rowCheck6834 : row6834 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6834 := by decide +kernel

theorem rowEval6834 (x : Key → ℝ) : Integer.Sparse.eval row6834 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 0, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6834, Integer.Sparse.eval_collectBalanced, rawRowCheck6834]

def rawRow6835 : Integer.Sparse Key := [(key183, -4), (key183, 2), (key191, 2), (key178, 2), (key183, 2), (key183, -4), (key143, 2), (key143, -1), (key160, -1), (key80, 2), (key80, -1), (key160, -1), (key67, -1), (key80, -1), (key67, -1), (key143, -1), (key80, 2), (key143, 2), (key131, -1), (key141, -1), (key141, 2), (key66, -1), (key78, -1), (key708, 2), (key894, 2), (key717, -1), (key894, -1), (key708, 2), (key708, -1), (key862, -1)]

theorem rawRowCheck6835 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -1, 0] GramFunctions.Block2.form3 = rawRow6835 := by decide +kernel

def row6835 : Integer.Sparse Key := [(key66, -1), (key67, -2), (key78, -1), (key80, 2), (key131, -1), (key141, 1), (key143, 2), (key160, -2), (key178, 2), (key183, -4), (key191, 2), (key708, 3), (key717, -1), (key862, -1), (key894, 1)]

theorem rowCheck6835 : row6835 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6835 := by decide +kernel

theorem rowEval6835 (x : Key → ℝ) : Integer.Sparse.eval row6835 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6835, Integer.Sparse.eval_collectBalanced, rawRowCheck6835]

def rawRow6836 : Integer.Sparse Key := [(key183, -4), (key191, 2), (key183, 2), (key183, 2), (key178, 2), (key183, -4), (key143, 2), (key160, -1), (key143, -1), (key80, 2), (key160, -1), (key80, -1), (key80, -1), (key67, -1), (key143, -1), (key67, -1), (key143, 2), (key80, 2), (key141, -1), (key131, -1), (key141, 2), (key78, -1), (key66, -1), (key894, 2), (key708, 2), (key894, -1), (key717, -1), (key708, 2), (key862, -1), (key708, -1)]

theorem rawRowCheck6836 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 0, -1] GramFunctions.Block2.form3 = rawRow6836 := by decide +kernel

def row6836 : Integer.Sparse Key := [(key66, -1), (key67, -2), (key78, -1), (key80, 2), (key131, -1), (key141, 1), (key143, 2), (key160, -2), (key178, 2), (key183, -4), (key191, 2), (key708, 3), (key717, -1), (key862, -1), (key894, 1)]

theorem rowCheck6836 : row6836 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6836 := by decide +kernel

theorem rowEval6836 (x : Key → ℝ) : Integer.Sparse.eval row6836 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 0, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6836, Integer.Sparse.eval_collectBalanced, rawRowCheck6836]

def rawRow6837 : Integer.Sparse Key := [(key191, -4), (key183, 2), (key183, 2), (key183, 2), (key183, 2), (key178, -4), (key160, 2), (key143, -1), (key143, -1), (key160, 2), (key80, -1), (key80, -1), (key143, -1), (key143, -1), (key80, -1), (key80, -1), (key67, 2), (key67, 2), (key141, -1), (key141, -1), (key131, 2), (key141, -1), (key141, -1), (key78, 2), (key717, 2), (key708, -1), (key708, -1), (key862, 2), (key708, -1), (key708, -1)]

theorem rawRowCheck6837 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -1, -1] GramFunctions.Block2.form3 = rawRow6837 := by decide +kernel

def row6837 : Integer.Sparse Key := [(key67, 4), (key78, 2), (key80, -4), (key131, 2), (key141, -4), (key143, -4), (key160, 4), (key178, -4), (key183, 8), (key191, -4), (key708, -4), (key717, 2), (key862, 2)]

theorem rowCheck6837 : row6837 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6837 := by decide +kernel

theorem rowEval6837 (x : Key → ℝ) : Integer.Sparse.eval row6837 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -1, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6837, Integer.Sparse.eval_collectBalanced, rawRowCheck6837]

def rawRow6838 : Integer.Sparse Key := [(key1992, -4), (key1992, 2), (key1995, 2), (key2002, 2), (key2004, 2), (key2004, -4), (key1992, 2), (key1992, -1), (key1995, -1), (key2237, 2), (key2237, -1), (key2260, -1), (key2271, -1), (key2273, -1), (key2271, -1), (key2295, -1), (key2273, 2), (key2295, 2), (key2002, -1), (key2004, -1), (key2004, 2), (key2271, -1), (key2273, -1), (key2271, 2), (key2295, 2), (key2273, -1), (key2295, -1), (key2325, 2), (key2325, -1), (key2337, -1)]

theorem rawRowCheck6838 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block2.form4 = rawRow6838 := by decide +kernel

def row6838 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

theorem rowCheck6838 : row6838 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6838 := by decide +kernel

theorem rowEval6838 (x : Key → ℝ) : Integer.Sparse.eval row6838 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6838, Integer.Sparse.eval_collectBalanced, rawRowCheck6838]

def rawRow6839 : Integer.Sparse Key := [(key1992, -4), (key1995, 2), (key1992, 2), (key2004, 2), (key2002, 2), (key2004, -4), (key1992, 2), (key1995, -1), (key1992, -1), (key2237, 2), (key2260, -1), (key2237, -1), (key2273, -1), (key2271, -1), (key2295, -1), (key2271, -1), (key2295, 2), (key2273, 2), (key2004, -1), (key2002, -1), (key2004, 2), (key2273, -1), (key2271, -1), (key2295, 2), (key2271, 2), (key2295, -1), (key2273, -1), (key2325, 2), (key2337, -1), (key2325, -1)]

theorem rawRowCheck6839 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block2.form4 = rawRow6839 := by decide +kernel

def row6839 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

theorem rowCheck6839 : row6839 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6839 := by decide +kernel

theorem rowEval6839 (x : Key → ℝ) : Integer.Sparse.eval row6839 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6839, Integer.Sparse.eval_collectBalanced, rawRowCheck6839]

def rawRow6840 : Integer.Sparse Key := [(key1995, -4), (key1992, 2), (key1992, 2), (key2004, 2), (key2004, 2), (key2002, -4), (key1995, 2), (key1992, -1), (key1992, -1), (key2260, 2), (key2237, -1), (key2237, -1), (key2295, -1), (key2295, -1), (key2273, -1), (key2273, -1), (key2271, 2), (key2271, 2), (key2004, -1), (key2004, -1), (key2002, 2), (key2295, -1), (key2295, -1), (key2273, 2), (key2273, 2), (key2271, -1), (key2271, -1), (key2337, 2), (key2325, -1), (key2325, -1)]

theorem rawRowCheck6840 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block2.form4 = rawRow6840 := by decide +kernel

def row6840 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, 2), (key2271, 2), (key2273, 2), (key2295, -4), (key2325, -2), (key2337, 2)]

theorem rowCheck6840 : row6840 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6840 := by decide +kernel

theorem rowEval6840 (x : Key → ℝ) : Integer.Sparse.eval row6840 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6840, Integer.Sparse.eval_collectBalanced, rawRowCheck6840]

def rawRow6841 : Integer.Sparse Key := [(key1992, -4), (key2002, 2), (key2004, 2), (key1992, 2), (key1995, 2), (key2004, -4), (key2237, 2), (key2271, -1), (key2273, -1), (key1992, 2), (key2271, -1), (key2295, -1), (key1992, -1), (key1995, -1), (key2237, -1), (key2260, -1), (key2273, 2), (key2295, 2), (key2271, -1), (key2273, -1), (key2325, 2), (key2002, -1), (key2004, -1), (key2271, 2), (key2295, 2), (key2325, -1), (key2337, -1), (key2004, 2), (key2273, -1), (key2295, -1)]

theorem rawRowCheck6841 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block2.form4 = rawRow6841 := by decide +kernel

def row6841 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

theorem rowCheck6841 : row6841 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6841 := by decide +kernel

theorem rowEval6841 (x : Key → ℝ) : Integer.Sparse.eval row6841 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6841, Integer.Sparse.eval_collectBalanced, rawRowCheck6841]

def rawRow6842 : Integer.Sparse Key := [(key1992, -4), (key2004, 2), (key2002, 2), (key1995, 2), (key1992, 2), (key2004, -4), (key2237, 2), (key2273, -1), (key2271, -1), (key1992, 2), (key2295, -1), (key2271, -1), (key1995, -1), (key1992, -1), (key2260, -1), (key2237, -1), (key2295, 2), (key2273, 2), (key2273, -1), (key2271, -1), (key2325, 2), (key2004, -1), (key2002, -1), (key2295, 2), (key2271, 2), (key2337, -1), (key2325, -1), (key2004, 2), (key2295, -1), (key2273, -1)]

theorem rawRowCheck6842 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block2.form4 = rawRow6842 := by decide +kernel

def row6842 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

theorem rowCheck6842 : row6842 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6842 := by decide +kernel

theorem rowEval6842 (x : Key → ℝ) : Integer.Sparse.eval row6842 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6842, Integer.Sparse.eval_collectBalanced, rawRowCheck6842]

def rawRow6843 : Integer.Sparse Key := [(key2002, -4), (key1992, 2), (key2004, 2), (key1992, 2), (key2004, 2), (key1995, -4), (key2271, 2), (key2237, -1), (key2273, -1), (key2271, 2), (key1992, -1), (key2295, -1), (key2237, -1), (key2273, -1), (key1992, -1), (key2295, -1), (key1995, 2), (key2260, 2), (key2271, -1), (key2325, -1), (key2273, 2), (key2271, -1), (key2325, -1), (key2002, 2), (key2337, 2), (key2004, -1), (key2295, -1), (key2273, 2), (key2004, -1), (key2295, -1)]

theorem rawRowCheck6843 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block2.form4 = rawRow6843 := by decide +kernel

def row6843 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, 2), (key2271, 2), (key2273, 2), (key2295, -4), (key2325, -2), (key2337, 2)]

theorem rowCheck6843 : row6843 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6843 := by decide +kernel

theorem rowEval6843 (x : Key → ℝ) : Integer.Sparse.eval row6843 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6843, Integer.Sparse.eval_collectBalanced, rawRowCheck6843]

def rawRow6844 : Integer.Sparse Key := [(key2002, -4), (key2004, 2), (key1992, 2), (key2004, 2), (key1992, 2), (key1995, -4), (key2271, 2), (key2273, -1), (key2237, -1), (key2271, 2), (key2295, -1), (key1992, -1), (key2273, -1), (key2237, -1), (key2295, -1), (key1992, -1), (key2260, 2), (key1995, 2), (key2325, -1), (key2271, -1), (key2273, 2), (key2325, -1), (key2271, -1), (key2337, 2), (key2002, 2), (key2295, -1), (key2004, -1), (key2273, 2), (key2295, -1), (key2004, -1)]

theorem rawRowCheck6844 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block2.form4 = rawRow6844 := by decide +kernel

def row6844 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, 2), (key2271, 2), (key2273, 2), (key2295, -4), (key2325, -2), (key2337, 2)]

theorem rowCheck6844 : row6844 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6844 := by decide +kernel

theorem rowEval6844 (x : Key → ℝ) : Integer.Sparse.eval row6844 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6844, Integer.Sparse.eval_collectBalanced, rawRowCheck6844]

def rawRow6845 : Integer.Sparse Key := [(key2004, -4), (key1992, 2), (key2002, 2), (key1995, 2), (key2004, 2), (key1992, -4), (key2273, 2), (key2237, -1), (key2271, -1), (key2295, 2), (key1992, -1), (key2271, -1), (key2260, -1), (key2295, -1), (key1995, -1), (key2273, -1), (key1992, 2), (key2237, 2), (key2273, -1), (key2325, -1), (key2271, 2), (key2295, -1), (key2337, -1), (key2004, 2), (key2325, 2), (key2002, -1), (key2271, -1), (key2295, 2), (key2004, -1), (key2273, -1)]

theorem rawRowCheck6845 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block2.form4 = rawRow6845 := by decide +kernel

def row6845 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

theorem rowCheck6845 : row6845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6845 := by decide +kernel

theorem rowEval6845 (x : Key → ℝ) : Integer.Sparse.eval row6845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6845, Integer.Sparse.eval_collectBalanced, rawRowCheck6845]

def rawRow6846 : Integer.Sparse Key := [(key2004, -4), (key2002, 2), (key1992, 2), (key2004, 2), (key1995, 2), (key1992, -4), (key2273, 2), (key2271, -1), (key2237, -1), (key2295, 2), (key2271, -1), (key1992, -1), (key2295, -1), (key2260, -1), (key2273, -1), (key1995, -1), (key2237, 2), (key1992, 2), (key2325, -1), (key2273, -1), (key2271, 2), (key2337, -1), (key2295, -1), (key2325, 2), (key2004, 2), (key2271, -1), (key2002, -1), (key2295, 2), (key2273, -1), (key2004, -1)]

theorem rawRowCheck6846 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block2.form4 = rawRow6846 := by decide +kernel

def row6846 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

theorem rowCheck6846 : row6846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6846 := by decide +kernel

theorem rowEval6846 (x : Key → ℝ) : Integer.Sparse.eval row6846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6846, Integer.Sparse.eval_collectBalanced, rawRowCheck6846]

def rawRow6847 : Integer.Sparse Key := [(key1995, -4), (key2004, 2), (key2004, 2), (key1992, 2), (key1992, 2), (key2002, -4), (key2260, 2), (key2295, -1), (key2295, -1), (key1995, 2), (key2273, -1), (key2273, -1), (key1992, -1), (key1992, -1), (key2237, -1), (key2237, -1), (key2271, 2), (key2271, 2), (key2295, -1), (key2295, -1), (key2337, 2), (key2004, -1), (key2004, -1), (key2273, 2), (key2273, 2), (key2325, -1), (key2325, -1), (key2002, 2), (key2271, -1), (key2271, -1)]

theorem rawRowCheck6847 : GramPolynomial.normalizedRow 0 ![1, -1, 1, -1, 0, 0] GramFunctions.Block2.form4 = rawRow6847 := by decide +kernel

def row6847 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, 2), (key2271, 2), (key2273, 2), (key2295, -4), (key2325, -2), (key2337, 2)]

theorem rowCheck6847 : row6847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6847 := by decide +kernel

theorem rowEval6847 (x : Key → ℝ) : Integer.Sparse.eval row6847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, -1, 0, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6847, Integer.Sparse.eval_collectBalanced, rawRowCheck6847]

def rawRow6848 : Integer.Sparse Key := [(key2004, -4), (key1995, 2), (key2004, 2), (key1992, 2), (key2002, 2), (key1992, -4), (key2295, 2), (key2260, -1), (key2295, -1), (key2273, 2), (key1995, -1), (key2273, -1), (key2237, -1), (key2271, -1), (key1992, -1), (key2271, -1), (key1992, 2), (key2237, 2), (key2295, -1), (key2337, -1), (key2295, 2), (key2273, -1), (key2325, -1), (key2004, 2), (key2325, 2), (key2004, -1), (key2273, -1), (key2271, 2), (key2002, -1), (key2271, -1)]

theorem rawRowCheck6848 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -1, 0] GramFunctions.Block2.form4 = rawRow6848 := by decide +kernel

def row6848 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

theorem rowCheck6848 : row6848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6848 := by decide +kernel

theorem rowEval6848 (x : Key → ℝ) : Integer.Sparse.eval row6848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6848, Integer.Sparse.eval_collectBalanced, rawRowCheck6848]

def rawRow6849 : Integer.Sparse Key := [(key2004, -4), (key2004, 2), (key1995, 2), (key2002, 2), (key1992, 2), (key1992, -4), (key2295, 2), (key2295, -1), (key2260, -1), (key2273, 2), (key2273, -1), (key1995, -1), (key2271, -1), (key2237, -1), (key2271, -1), (key1992, -1), (key2237, 2), (key1992, 2), (key2337, -1), (key2295, -1), (key2295, 2), (key2325, -1), (key2273, -1), (key2325, 2), (key2004, 2), (key2273, -1), (key2004, -1), (key2271, 2), (key2271, -1), (key2002, -1)]

theorem rawRowCheck6849 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 0, -1] GramFunctions.Block2.form4 = rawRow6849 := by decide +kernel

def row6849 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

theorem rowCheck6849 : row6849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6849 := by decide +kernel

theorem rowEval6849 (x : Key → ℝ) : Integer.Sparse.eval row6849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 0, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6849, Integer.Sparse.eval_collectBalanced, rawRowCheck6849]

def rawRow6850 : Integer.Sparse Key := [(key2237, -4), (key2271, 2), (key2273, 2), (key2271, 2), (key2273, 2), (key2325, -4), (key1992, 2), (key2002, -1), (key2004, -1), (key1992, 2), (key2271, -1), (key2295, -1), (key2002, -1), (key2004, -1), (key2271, -1), (key2295, -1), (key2325, 2), (key2337, 2), (key1992, -1), (key1995, -1), (key2004, 2), (key1992, -1), (key1995, -1), (key2237, 2), (key2260, 2), (key2273, -1), (key2295, -1), (key2004, 2), (key2273, -1), (key2295, -1)]

theorem rawRowCheck6850 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block2.form4 = rawRow6850 := by decide +kernel

def row6850 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, 2), (key2271, 2), (key2273, 2), (key2295, -4), (key2325, -2), (key2337, 2)]

theorem rowCheck6850 : row6850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6850 := by decide +kernel

theorem rowEval6850 (x : Key → ℝ) : Integer.Sparse.eval row6850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6850, Integer.Sparse.eval_collectBalanced, rawRowCheck6850]

def rawRow6851 : Integer.Sparse Key := [(key2237, -4), (key2273, 2), (key2271, 2), (key2273, 2), (key2271, 2), (key2325, -4), (key1992, 2), (key2004, -1), (key2002, -1), (key1992, 2), (key2295, -1), (key2271, -1), (key2004, -1), (key2002, -1), (key2295, -1), (key2271, -1), (key2337, 2), (key2325, 2), (key1995, -1), (key1992, -1), (key2004, 2), (key1995, -1), (key1992, -1), (key2260, 2), (key2237, 2), (key2295, -1), (key2273, -1), (key2004, 2), (key2295, -1), (key2273, -1)]

theorem rawRowCheck6851 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block2.form4 = rawRow6851 := by decide +kernel

def row6851 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, 2), (key2271, 2), (key2273, 2), (key2295, -4), (key2325, -2), (key2337, 2)]

theorem rowCheck6851 : row6851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6851 := by decide +kernel

theorem rowEval6851 (x : Key → ℝ) : Integer.Sparse.eval row6851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6851, Integer.Sparse.eval_collectBalanced, rawRowCheck6851]

def rawRow6852 : Integer.Sparse Key := [(key2271, -4), (key2237, 2), (key2273, 2), (key2271, 2), (key2325, 2), (key2273, -4), (key2002, 2), (key1992, -1), (key2004, -1), (key2271, 2), (key1992, -1), (key2295, -1), (key2271, -1), (key2325, -1), (key2002, -1), (key2337, -1), (key2004, 2), (key2295, 2), (key1992, -1), (key2004, -1), (key1995, 2), (key2237, -1), (key2273, -1), (key1992, 2), (key2295, 2), (key1995, -1), (key2260, -1), (key2273, 2), (key2004, -1), (key2295, -1)]

theorem rawRowCheck6852 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block2.form4 = rawRow6852 := by decide +kernel

def row6852 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

theorem rowCheck6852 : row6852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6852 := by decide +kernel

theorem rowEval6852 (x : Key → ℝ) : Integer.Sparse.eval row6852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6852, Integer.Sparse.eval_collectBalanced, rawRowCheck6852]

def rawRow6853 : Integer.Sparse Key := [(key2271, -4), (key2273, 2), (key2237, 2), (key2325, 2), (key2271, 2), (key2273, -4), (key2002, 2), (key2004, -1), (key1992, -1), (key2271, 2), (key2295, -1), (key1992, -1), (key2325, -1), (key2271, -1), (key2337, -1), (key2002, -1), (key2295, 2), (key2004, 2), (key2004, -1), (key1992, -1), (key1995, 2), (key2273, -1), (key2237, -1), (key2295, 2), (key1992, 2), (key2260, -1), (key1995, -1), (key2273, 2), (key2295, -1), (key2004, -1)]

theorem rawRowCheck6853 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block2.form4 = rawRow6853 := by decide +kernel

def row6853 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

theorem rowCheck6853 : row6853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6853 := by decide +kernel

theorem rowEval6853 (x : Key → ℝ) : Integer.Sparse.eval row6853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6853, Integer.Sparse.eval_collectBalanced, rawRowCheck6853]

def rawRow6854 : Integer.Sparse Key := [(key2273, -4), (key2237, 2), (key2271, 2), (key2273, 2), (key2325, 2), (key2271, -4), (key2004, 2), (key1992, -1), (key2002, -1), (key2295, 2), (key1992, -1), (key2271, -1), (key2295, -1), (key2337, -1), (key2004, -1), (key2325, -1), (key2002, 2), (key2271, 2), (key1995, -1), (key2004, -1), (key1992, 2), (key2260, -1), (key2295, -1), (key1995, 2), (key2273, 2), (key1992, -1), (key2237, -1), (key2295, 2), (key2004, -1), (key2273, -1)]

theorem rawRowCheck6854 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block2.form4 = rawRow6854 := by decide +kernel

def row6854 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

theorem rowCheck6854 : row6854 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6854 := by decide +kernel

theorem rowEval6854 (x : Key → ℝ) : Integer.Sparse.eval row6854 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6854, Integer.Sparse.eval_collectBalanced, rawRowCheck6854]

def rawRow6855 : Integer.Sparse Key := [(key2273, -4), (key2271, 2), (key2237, 2), (key2325, 2), (key2273, 2), (key2271, -4), (key2004, 2), (key2002, -1), (key1992, -1), (key2295, 2), (key2271, -1), (key1992, -1), (key2337, -1), (key2295, -1), (key2325, -1), (key2004, -1), (key2271, 2), (key2002, 2), (key2004, -1), (key1995, -1), (key1992, 2), (key2295, -1), (key2260, -1), (key2273, 2), (key1995, 2), (key2237, -1), (key1992, -1), (key2295, 2), (key2273, -1), (key2004, -1)]

theorem rawRowCheck6855 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block2.form4 = rawRow6855 := by decide +kernel

def row6855 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

theorem rowCheck6855 : row6855 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6855 := by decide +kernel

theorem rowEval6855 (x : Key → ℝ) : Integer.Sparse.eval row6855 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6855, Integer.Sparse.eval_collectBalanced, rawRowCheck6855]

def rawRow6856 : Integer.Sparse Key := [(key2271, -4), (key2271, 2), (key2325, 2), (key2237, 2), (key2273, 2), (key2273, -4), (key2271, 2), (key2271, -1), (key2325, -1), (key2002, 2), (key2002, -1), (key2337, -1), (key1992, -1), (key2004, -1), (key1992, -1), (key2295, -1), (key2004, 2), (key2295, 2), (key2237, -1), (key2273, -1), (key2273, 2), (key1992, -1), (key2004, -1), (key1992, 2), (key2295, 2), (key2004, -1), (key2295, -1), (key1995, 2), (key1995, -1), (key2260, -1)]

theorem rawRowCheck6856 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block2.form4 = rawRow6856 := by decide +kernel

def row6856 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

theorem rowCheck6856 : row6856 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6856 := by decide +kernel

theorem rowEval6856 (x : Key → ℝ) : Integer.Sparse.eval row6856 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6856, Integer.Sparse.eval_collectBalanced, rawRowCheck6856]

def rawRow6857 : Integer.Sparse Key := [(key2271, -4), (key2325, 2), (key2271, 2), (key2273, 2), (key2237, 2), (key2273, -4), (key2271, 2), (key2325, -1), (key2271, -1), (key2002, 2), (key2337, -1), (key2002, -1), (key2004, -1), (key1992, -1), (key2295, -1), (key1992, -1), (key2295, 2), (key2004, 2), (key2273, -1), (key2237, -1), (key2273, 2), (key2004, -1), (key1992, -1), (key2295, 2), (key1992, 2), (key2295, -1), (key2004, -1), (key1995, 2), (key2260, -1), (key1995, -1)]

theorem rawRowCheck6857 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block2.form4 = rawRow6857 := by decide +kernel

def row6857 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

theorem rowCheck6857 : row6857 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6857 := by decide +kernel

theorem rowEval6857 (x : Key → ℝ) : Integer.Sparse.eval row6857 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6857, Integer.Sparse.eval_collectBalanced, rawRowCheck6857]

def rawRow6858 : Integer.Sparse Key := [(key2325, -4), (key2271, 2), (key2271, 2), (key2273, 2), (key2273, 2), (key2237, -4), (key2325, 2), (key2271, -1), (key2271, -1), (key2337, 2), (key2002, -1), (key2002, -1), (key2295, -1), (key2295, -1), (key2004, -1), (key2004, -1), (key1992, 2), (key1992, 2), (key2273, -1), (key2273, -1), (key2237, 2), (key2295, -1), (key2295, -1), (key2004, 2), (key2004, 2), (key1992, -1), (key1992, -1), (key2260, 2), (key1995, -1), (key1995, -1)]

theorem rawRowCheck6858 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block2.form4 = rawRow6858 := by decide +kernel

def row6858 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, 2), (key2271, 2), (key2273, 2), (key2295, -4), (key2325, -2), (key2337, 2)]

theorem rowCheck6858 : row6858 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6858 := by decide +kernel

theorem rowEval6858 (x : Key → ℝ) : Integer.Sparse.eval row6858 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6858, Integer.Sparse.eval_collectBalanced, rawRowCheck6858]

def rawRow6859 : Integer.Sparse Key := [(key2273, -4), (key2273, 2), (key2325, 2), (key2237, 2), (key2271, 2), (key2271, -4), (key2295, 2), (key2295, -1), (key2337, -1), (key2004, 2), (key2004, -1), (key2325, -1), (key1992, -1), (key2002, -1), (key1992, -1), (key2271, -1), (key2002, 2), (key2271, 2), (key2260, -1), (key2295, -1), (key2295, 2), (key1995, -1), (key2004, -1), (key1995, 2), (key2273, 2), (key2004, -1), (key2273, -1), (key1992, 2), (key1992, -1), (key2237, -1)]

theorem rawRowCheck6859 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -1, 0] GramFunctions.Block2.form4 = rawRow6859 := by decide +kernel

def row6859 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

theorem rowCheck6859 : row6859 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6859 := by decide +kernel

theorem rowEval6859 (x : Key → ℝ) : Integer.Sparse.eval row6859 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6859, Integer.Sparse.eval_collectBalanced, rawRowCheck6859]

def rawRow6860 : Integer.Sparse Key := [(key2273, -4), (key2325, 2), (key2273, 2), (key2271, 2), (key2237, 2), (key2271, -4), (key2295, 2), (key2337, -1), (key2295, -1), (key2004, 2), (key2325, -1), (key2004, -1), (key2002, -1), (key1992, -1), (key2271, -1), (key1992, -1), (key2271, 2), (key2002, 2), (key2295, -1), (key2260, -1), (key2295, 2), (key2004, -1), (key1995, -1), (key2273, 2), (key1995, 2), (key2273, -1), (key2004, -1), (key1992, 2), (key2237, -1), (key1992, -1)]

theorem rawRowCheck6860 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 0, -1] GramFunctions.Block2.form4 = rawRow6860 := by decide +kernel

def row6860 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

theorem rowCheck6860 : row6860 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6860 := by decide +kernel

theorem rowEval6860 (x : Key → ℝ) : Integer.Sparse.eval row6860 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 0, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6860, Integer.Sparse.eval_collectBalanced, rawRowCheck6860]

def rawRow6861 : Integer.Sparse Key := [(key2325, -4), (key2273, 2), (key2273, 2), (key2271, 2), (key2271, 2), (key2237, -4), (key2337, 2), (key2295, -1), (key2295, -1), (key2325, 2), (key2004, -1), (key2004, -1), (key2271, -1), (key2271, -1), (key2002, -1), (key2002, -1), (key1992, 2), (key1992, 2), (key2295, -1), (key2295, -1), (key2260, 2), (key2273, -1), (key2273, -1), (key2004, 2), (key2004, 2), (key1995, -1), (key1995, -1), (key2237, 2), (key1992, -1), (key1992, -1)]

theorem rawRowCheck6861 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -1, -1] GramFunctions.Block2.form4 = rawRow6861 := by decide +kernel

def row6861 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, 2), (key2271, 2), (key2273, 2), (key2295, -4), (key2325, -2), (key2337, 2)]

theorem rowCheck6861 : row6861 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6861 := by decide +kernel

theorem rowEval6861 (x : Key → ℝ) : Integer.Sparse.eval row6861 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -1, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6861, Integer.Sparse.eval_collectBalanced, rawRowCheck6861]

def rawRow6862 : Integer.Sparse Key := [(key2260, -4), (key2295, 2), (key2295, 2), (key2295, 2), (key2295, 2), (key2337, -4), (key1995, 2), (key2004, -1), (key2004, -1), (key1995, 2), (key2273, -1), (key2273, -1), (key2004, -1), (key2004, -1), (key2273, -1), (key2273, -1), (key2325, 2), (key2325, 2), (key1992, -1), (key1992, -1), (key2002, 2), (key1992, -1), (key1992, -1), (key2237, 2), (key2237, 2), (key2271, -1), (key2271, -1), (key2002, 2), (key2271, -1), (key2271, -1)]

theorem rawRowCheck6862 : GramPolynomial.normalizedRow 0 ![1, 1, -1, -1, 0, 0] GramFunctions.Block2.form4 = rawRow6862 := by decide +kernel

def row6862 : Integer.Sparse Key := [(key1992, -4), (key1995, 4), (key2002, 4), (key2004, -4), (key2237, 4), (key2260, -4), (key2271, -4), (key2273, -4), (key2295, 8), (key2325, 4), (key2337, -4)]

theorem rowCheck6862 : row6862 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6862 := by decide +kernel

theorem rowEval6862 (x : Key → ℝ) : Integer.Sparse.eval row6862 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, -1, 0, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6862, Integer.Sparse.eval_collectBalanced, rawRowCheck6862]

def rawRow6863 : Integer.Sparse Key := [(key2295, -4), (key2260, 2), (key2295, 2), (key2295, 2), (key2337, 2), (key2295, -4), (key2004, 2), (key1995, -1), (key2004, -1), (key2273, 2), (key1995, -1), (key2273, -1), (key2273, -1), (key2325, -1), (key2004, -1), (key2325, -1), (key2004, 2), (key2273, 2), (key1992, -1), (key2002, -1), (key1992, 2), (key2237, -1), (key2271, -1), (key1992, 2), (key2271, 2), (key1992, -1), (key2237, -1), (key2271, 2), (key2002, -1), (key2271, -1)]

theorem rawRowCheck6863 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -1, 0] GramFunctions.Block2.form4 = rawRow6863 := by decide +kernel

def row6863 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, 2), (key2271, 2), (key2273, 2), (key2295, -4), (key2325, -2), (key2337, 2)]

theorem rowCheck6863 : row6863 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6863 := by decide +kernel

theorem rowEval6863 (x : Key → ℝ) : Integer.Sparse.eval row6863 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6863, Integer.Sparse.eval_collectBalanced, rawRowCheck6863]

def rawRow6864 : Integer.Sparse Key := [(key2295, -4), (key2295, 2), (key2260, 2), (key2337, 2), (key2295, 2), (key2295, -4), (key2004, 2), (key2004, -1), (key1995, -1), (key2273, 2), (key2273, -1), (key1995, -1), (key2325, -1), (key2273, -1), (key2325, -1), (key2004, -1), (key2273, 2), (key2004, 2), (key2002, -1), (key1992, -1), (key1992, 2), (key2271, -1), (key2237, -1), (key2271, 2), (key1992, 2), (key2237, -1), (key1992, -1), (key2271, 2), (key2271, -1), (key2002, -1)]

theorem rawRowCheck6864 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 0, -1] GramFunctions.Block2.form4 = rawRow6864 := by decide +kernel

def row6864 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, 2), (key2271, 2), (key2273, 2), (key2295, -4), (key2325, -2), (key2337, 2)]

theorem rowCheck6864 : row6864 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6864 := by decide +kernel

theorem rowEval6864 (x : Key → ℝ) : Integer.Sparse.eval row6864 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 0, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6864, Integer.Sparse.eval_collectBalanced, rawRowCheck6864]

def rawRow6865 : Integer.Sparse Key := [(key2295, -4), (key2295, 2), (key2337, 2), (key2260, 2), (key2295, 2), (key2295, -4), (key2273, 2), (key2273, -1), (key2325, -1), (key2004, 2), (key2004, -1), (key2325, -1), (key1995, -1), (key2004, -1), (key1995, -1), (key2273, -1), (key2004, 2), (key2273, 2), (key2237, -1), (key2271, -1), (key2271, 2), (key1992, -1), (key2002, -1), (key1992, 2), (key2271, 2), (key2002, -1), (key2271, -1), (key1992, 2), (key1992, -1), (key2237, -1)]

theorem rawRowCheck6865 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -1, 0] GramFunctions.Block2.form4 = rawRow6865 := by decide +kernel

def row6865 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, 2), (key2271, 2), (key2273, 2), (key2295, -4), (key2325, -2), (key2337, 2)]

theorem rowCheck6865 : row6865 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6865 := by decide +kernel

theorem rowEval6865 (x : Key → ℝ) : Integer.Sparse.eval row6865 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6865, Integer.Sparse.eval_collectBalanced, rawRowCheck6865]

def rawRow6866 : Integer.Sparse Key := [(key2295, -4), (key2337, 2), (key2295, 2), (key2295, 2), (key2260, 2), (key2295, -4), (key2273, 2), (key2325, -1), (key2273, -1), (key2004, 2), (key2325, -1), (key2004, -1), (key2004, -1), (key1995, -1), (key2273, -1), (key1995, -1), (key2273, 2), (key2004, 2), (key2271, -1), (key2237, -1), (key2271, 2), (key2002, -1), (key1992, -1), (key2271, 2), (key1992, 2), (key2271, -1), (key2002, -1), (key1992, 2), (key2237, -1), (key1992, -1)]

theorem rawRowCheck6866 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 0, -1] GramFunctions.Block2.form4 = rawRow6866 := by decide +kernel

def row6866 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, 2), (key2271, 2), (key2273, 2), (key2295, -4), (key2325, -2), (key2337, 2)]

theorem rowCheck6866 : row6866 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6866 := by decide +kernel

theorem rowEval6866 (x : Key → ℝ) : Integer.Sparse.eval row6866 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 0, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6866, Integer.Sparse.eval_collectBalanced, rawRowCheck6866]

def rawRow6867 : Integer.Sparse Key := [(key2337, -4), (key2295, 2), (key2295, 2), (key2295, 2), (key2295, 2), (key2260, -4), (key2325, 2), (key2273, -1), (key2273, -1), (key2325, 2), (key2004, -1), (key2004, -1), (key2273, -1), (key2273, -1), (key2004, -1), (key2004, -1), (key1995, 2), (key1995, 2), (key2271, -1), (key2271, -1), (key2237, 2), (key2271, -1), (key2271, -1), (key2002, 2), (key2002, 2), (key1992, -1), (key1992, -1), (key2237, 2), (key1992, -1), (key1992, -1)]

theorem rawRowCheck6867 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -1, -1] GramFunctions.Block2.form4 = rawRow6867 := by decide +kernel

def row6867 : Integer.Sparse Key := [(key1992, -4), (key1995, 4), (key2002, 4), (key2004, -4), (key2237, 4), (key2260, -4), (key2271, -4), (key2273, -4), (key2295, 8), (key2325, 4), (key2337, -4)]

theorem rowCheck6867 : row6867 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6867 := by decide +kernel

theorem rowEval6867 (x : Key → ℝ) : Integer.Sparse.eval row6867 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -1, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6867, Integer.Sparse.eval_collectBalanced, rawRowCheck6867]

def rawRow6868 : Integer.Sparse Key := [(key2035, -2), (key2035, 1), (key2038, 1), (key2154, -2), (key2154, 1), (key2170, 1), (key2178, 1), (key2180, 1), (key2178, 1), (key2190, 1), (key2180, -2), (key2190, -2), (key2065, 2), (key2065, -1), (key2073, -1), (key2154, 2), (key2154, -1), (key2170, -1), (key2278, -1), (key2282, -1), (key2278, -1), (key2290, -1), (key2282, 2), (key2290, 2), (key2081, -1), (key2083, -1), (key2081, 1), (key2088, 1), (key2178, -1), (key2180, -1), (key2180, 1), (key2190, 1), (key2278, 1), (key2282, 1), (key2282, -1), (key2290, -1), (key2329, 1), (key2334, 1), (key2331, -1), (key2334, -1)]

theorem rawRowCheck6868 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block2.form5 = rawRow6868 := by decide +kernel

def row6868 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

theorem rowCheck6868 : row6868 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6868 := by decide +kernel

theorem rowEval6868 (x : Key → ℝ) : Integer.Sparse.eval row6868 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6868, Integer.Sparse.eval_collectBalanced, rawRowCheck6868]

def rawRow6869 : Integer.Sparse Key := [(key2035, -2), (key2038, 1), (key2035, 1), (key2154, -2), (key2170, 1), (key2154, 1), (key2180, 1), (key2178, 1), (key2190, 1), (key2178, 1), (key2190, -2), (key2180, -2), (key2065, 2), (key2073, -1), (key2065, -1), (key2154, 2), (key2170, -1), (key2154, -1), (key2282, -1), (key2278, -1), (key2290, -1), (key2278, -1), (key2290, 2), (key2282, 2), (key2083, -1), (key2081, -1), (key2088, 1), (key2081, 1), (key2180, -1), (key2178, -1), (key2190, 1), (key2180, 1), (key2282, 1), (key2278, 1), (key2290, -1), (key2282, -1), (key2334, 1), (key2329, 1), (key2334, -1), (key2331, -1)]

theorem rawRowCheck6869 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block2.form5 = rawRow6869 := by decide +kernel

def row6869 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

theorem rowCheck6869 : row6869 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6869 := by decide +kernel

theorem rowEval6869 (x : Key → ℝ) : Integer.Sparse.eval row6869 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6869, Integer.Sparse.eval_collectBalanced, rawRowCheck6869]

def rawRow6870 : Integer.Sparse Key := [(key2038, -2), (key2035, 1), (key2035, 1), (key2170, -2), (key2154, 1), (key2154, 1), (key2190, 1), (key2190, 1), (key2180, 1), (key2180, 1), (key2178, -2), (key2178, -2), (key2073, 2), (key2065, -1), (key2065, -1), (key2170, 2), (key2154, -1), (key2154, -1), (key2290, -1), (key2290, -1), (key2282, -1), (key2282, -1), (key2278, 2), (key2278, 2), (key2088, -1), (key2088, -1), (key2083, 1), (key2083, 1), (key2190, -1), (key2190, -1), (key2178, 1), (key2178, 1), (key2290, 1), (key2290, 1), (key2278, -1), (key2278, -1), (key2331, 1), (key2331, 1), (key2329, -1), (key2329, -1)]

theorem rawRowCheck6870 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block2.form5 = rawRow6870 := by decide +kernel

def row6870 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2065, -2), (key2073, 2), (key2083, 2), (key2088, -2), (key2178, -2), (key2180, 2), (key2278, 2), (key2282, -2), (key2329, -2), (key2331, 2)]

theorem rowCheck6870 : row6870 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6870 := by decide +kernel

theorem rowEval6870 (x : Key → ℝ) : Integer.Sparse.eval row6870 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6870, Integer.Sparse.eval_collectBalanced, rawRowCheck6870]

def rawRow6871 : Integer.Sparse Key := [(key2154, -2), (key2178, 1), (key2180, 1), (key2035, -2), (key2178, 1), (key2190, 1), (key2035, 1), (key2038, 1), (key2154, 1), (key2170, 1), (key2180, -2), (key2190, -2), (key2154, 2), (key2278, -1), (key2282, -1), (key2065, 2), (key2278, -1), (key2290, -1), (key2065, -1), (key2073, -1), (key2154, -1), (key2170, -1), (key2282, 2), (key2290, 2), (key2178, -1), (key2180, -1), (key2278, 1), (key2282, 1), (key2081, -1), (key2083, -1), (key2329, 1), (key2334, 1), (key2081, 1), (key2088, 1), (key2331, -1), (key2334, -1), (key2180, 1), (key2190, 1), (key2282, -1), (key2290, -1)]

theorem rawRowCheck6871 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block2.form5 = rawRow6871 := by decide +kernel

def row6871 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

theorem rowCheck6871 : row6871 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6871 := by decide +kernel

theorem rowEval6871 (x : Key → ℝ) : Integer.Sparse.eval row6871 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6871, Integer.Sparse.eval_collectBalanced, rawRowCheck6871]

def rawRow6872 : Integer.Sparse Key := [(key2154, -2), (key2180, 1), (key2178, 1), (key2035, -2), (key2190, 1), (key2178, 1), (key2038, 1), (key2035, 1), (key2170, 1), (key2154, 1), (key2190, -2), (key2180, -2), (key2154, 2), (key2282, -1), (key2278, -1), (key2065, 2), (key2290, -1), (key2278, -1), (key2073, -1), (key2065, -1), (key2170, -1), (key2154, -1), (key2290, 2), (key2282, 2), (key2180, -1), (key2178, -1), (key2282, 1), (key2278, 1), (key2083, -1), (key2081, -1), (key2334, 1), (key2329, 1), (key2088, 1), (key2081, 1), (key2334, -1), (key2331, -1), (key2190, 1), (key2180, 1), (key2290, -1), (key2282, -1)]

theorem rawRowCheck6872 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block2.form5 = rawRow6872 := by decide +kernel

def row6872 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

theorem rowCheck6872 : row6872 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6872 := by decide +kernel

theorem rowEval6872 (x : Key → ℝ) : Integer.Sparse.eval row6872 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6872, Integer.Sparse.eval_collectBalanced, rawRowCheck6872]

def rawRow6873 : Integer.Sparse Key := [(key2178, -2), (key2154, 1), (key2180, 1), (key2178, -2), (key2035, 1), (key2190, 1), (key2154, 1), (key2180, 1), (key2035, 1), (key2190, 1), (key2038, -2), (key2170, -2), (key2278, 2), (key2154, -1), (key2282, -1), (key2278, 2), (key2065, -1), (key2290, -1), (key2154, -1), (key2282, -1), (key2065, -1), (key2290, -1), (key2073, 2), (key2170, 2), (key2278, -1), (key2329, -1), (key2178, 1), (key2331, 1), (key2278, -1), (key2329, -1), (key2083, 1), (key2290, 1), (key2178, 1), (key2331, 1), (key2088, -1), (key2190, -1), (key2083, 1), (key2290, 1), (key2088, -1), (key2190, -1)]

theorem rawRowCheck6873 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block2.form5 = rawRow6873 := by decide +kernel

def row6873 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2065, -2), (key2073, 2), (key2083, 2), (key2088, -2), (key2178, -2), (key2180, 2), (key2278, 2), (key2282, -2), (key2329, -2), (key2331, 2)]

theorem rowCheck6873 : row6873 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6873 := by decide +kernel

theorem rowEval6873 (x : Key → ℝ) : Integer.Sparse.eval row6873 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6873, Integer.Sparse.eval_collectBalanced, rawRowCheck6873]

def rawRow6874 : Integer.Sparse Key := [(key2178, -2), (key2180, 1), (key2154, 1), (key2178, -2), (key2190, 1), (key2035, 1), (key2180, 1), (key2154, 1), (key2190, 1), (key2035, 1), (key2170, -2), (key2038, -2), (key2278, 2), (key2282, -1), (key2154, -1), (key2278, 2), (key2290, -1), (key2065, -1), (key2282, -1), (key2154, -1), (key2290, -1), (key2065, -1), (key2170, 2), (key2073, 2), (key2329, -1), (key2278, -1), (key2331, 1), (key2178, 1), (key2329, -1), (key2278, -1), (key2290, 1), (key2083, 1), (key2331, 1), (key2178, 1), (key2190, -1), (key2088, -1), (key2290, 1), (key2083, 1), (key2190, -1), (key2088, -1)]

theorem rawRowCheck6874 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block2.form5 = rawRow6874 := by decide +kernel

def row6874 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2065, -2), (key2073, 2), (key2083, 2), (key2088, -2), (key2178, -2), (key2180, 2), (key2278, 2), (key2282, -2), (key2329, -2), (key2331, 2)]

theorem rowCheck6874 : row6874 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6874 := by decide +kernel

theorem rowEval6874 (x : Key → ℝ) : Integer.Sparse.eval row6874 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6874, Integer.Sparse.eval_collectBalanced, rawRowCheck6874]

def rawRow6875 : Integer.Sparse Key := [(key2180, -2), (key2154, 1), (key2178, 1), (key2190, -2), (key2035, 1), (key2178, 1), (key2170, 1), (key2190, 1), (key2038, 1), (key2180, 1), (key2035, -2), (key2154, -2), (key2282, 2), (key2154, -1), (key2278, -1), (key2290, 2), (key2065, -1), (key2278, -1), (key2170, -1), (key2290, -1), (key2073, -1), (key2282, -1), (key2065, 2), (key2154, 2), (key2282, -1), (key2331, -1), (key2180, 1), (key2329, 1), (key2290, -1), (key2334, -1), (key2081, 1), (key2278, 1), (key2190, 1), (key2334, 1), (key2081, -1), (key2178, -1), (key2088, 1), (key2282, 1), (key2083, -1), (key2180, -1)]

theorem rawRowCheck6875 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block2.form5 = rawRow6875 := by decide +kernel

def row6875 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

theorem rowCheck6875 : row6875 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6875 := by decide +kernel

theorem rowEval6875 (x : Key → ℝ) : Integer.Sparse.eval row6875 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6875, Integer.Sparse.eval_collectBalanced, rawRowCheck6875]

def rawRow6876 : Integer.Sparse Key := [(key2180, -2), (key2178, 1), (key2154, 1), (key2190, -2), (key2178, 1), (key2035, 1), (key2190, 1), (key2170, 1), (key2180, 1), (key2038, 1), (key2154, -2), (key2035, -2), (key2282, 2), (key2278, -1), (key2154, -1), (key2290, 2), (key2278, -1), (key2065, -1), (key2290, -1), (key2170, -1), (key2282, -1), (key2073, -1), (key2154, 2), (key2065, 2), (key2331, -1), (key2282, -1), (key2329, 1), (key2180, 1), (key2334, -1), (key2290, -1), (key2278, 1), (key2081, 1), (key2334, 1), (key2190, 1), (key2178, -1), (key2081, -1), (key2282, 1), (key2088, 1), (key2180, -1), (key2083, -1)]

theorem rawRowCheck6876 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block2.form5 = rawRow6876 := by decide +kernel

def row6876 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

theorem rowCheck6876 : row6876 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6876 := by decide +kernel

theorem rowEval6876 (x : Key → ℝ) : Integer.Sparse.eval row6876 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6876, Integer.Sparse.eval_collectBalanced, rawRowCheck6876]

def rawRow6877 : Integer.Sparse Key := [(key2170, -2), (key2190, 1), (key2190, 1), (key2038, -2), (key2180, 1), (key2180, 1), (key2035, 1), (key2035, 1), (key2154, 1), (key2154, 1), (key2178, -2), (key2178, -2), (key2170, 2), (key2290, -1), (key2290, -1), (key2073, 2), (key2282, -1), (key2282, -1), (key2065, -1), (key2065, -1), (key2154, -1), (key2154, -1), (key2278, 2), (key2278, 2), (key2190, -1), (key2190, -1), (key2290, 1), (key2290, 1), (key2088, -1), (key2088, -1), (key2331, 1), (key2331, 1), (key2083, 1), (key2083, 1), (key2329, -1), (key2329, -1), (key2178, 1), (key2178, 1), (key2278, -1), (key2278, -1)]

theorem rawRowCheck6877 : GramPolynomial.normalizedRow 0 ![1, -1, 1, -1, 0, 0] GramFunctions.Block2.form5 = rawRow6877 := by decide +kernel

def row6877 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2065, -2), (key2073, 2), (key2083, 2), (key2088, -2), (key2178, -2), (key2180, 2), (key2278, 2), (key2282, -2), (key2329, -2), (key2331, 2)]

theorem rowCheck6877 : row6877 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6877 := by decide +kernel

theorem rowEval6877 (x : Key → ℝ) : Integer.Sparse.eval row6877 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, -1, 0, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6877, Integer.Sparse.eval_collectBalanced, rawRowCheck6877]

def rawRow6878 : Integer.Sparse Key := [(key2190, -2), (key2170, 1), (key2190, 1), (key2180, -2), (key2038, 1), (key2180, 1), (key2154, 1), (key2178, 1), (key2035, 1), (key2178, 1), (key2035, -2), (key2154, -2), (key2290, 2), (key2170, -1), (key2290, -1), (key2282, 2), (key2073, -1), (key2282, -1), (key2154, -1), (key2278, -1), (key2065, -1), (key2278, -1), (key2065, 2), (key2154, 2), (key2290, -1), (key2334, -1), (key2190, 1), (key2334, 1), (key2282, -1), (key2331, -1), (key2088, 1), (key2282, 1), (key2180, 1), (key2329, 1), (key2083, -1), (key2180, -1), (key2081, 1), (key2278, 1), (key2081, -1), (key2178, -1)]

theorem rawRowCheck6878 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -1, 0] GramFunctions.Block2.form5 = rawRow6878 := by decide +kernel

def row6878 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

theorem rowCheck6878 : row6878 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6878 := by decide +kernel

theorem rowEval6878 (x : Key → ℝ) : Integer.Sparse.eval row6878 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -1, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6878, Integer.Sparse.eval_collectBalanced, rawRowCheck6878]

def rawRow6879 : Integer.Sparse Key := [(key2190, -2), (key2190, 1), (key2170, 1), (key2180, -2), (key2180, 1), (key2038, 1), (key2178, 1), (key2154, 1), (key2178, 1), (key2035, 1), (key2154, -2), (key2035, -2), (key2290, 2), (key2290, -1), (key2170, -1), (key2282, 2), (key2282, -1), (key2073, -1), (key2278, -1), (key2154, -1), (key2278, -1), (key2065, -1), (key2154, 2), (key2065, 2), (key2334, -1), (key2290, -1), (key2334, 1), (key2190, 1), (key2331, -1), (key2282, -1), (key2282, 1), (key2088, 1), (key2329, 1), (key2180, 1), (key2180, -1), (key2083, -1), (key2278, 1), (key2081, 1), (key2178, -1), (key2081, -1)]

theorem rawRowCheck6879 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 0, -1] GramFunctions.Block2.form5 = rawRow6879 := by decide +kernel

def row6879 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

theorem rowCheck6879 : row6879 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6879 := by decide +kernel

theorem rowEval6879 (x : Key → ℝ) : Integer.Sparse.eval row6879 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 0, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6879, Integer.Sparse.eval_collectBalanced, rawRowCheck6879]

def rawRow6880 : Integer.Sparse Key := [(key2065, -2), (key2081, 1), (key2083, 1), (key2065, -2), (key2278, 1), (key2290, 1), (key2081, 1), (key2083, 1), (key2278, 1), (key2290, 1), (key2329, -2), (key2334, -2), (key2035, 2), (key2081, -1), (key2088, -1), (key2035, 2), (key2178, -1), (key2190, -1), (key2081, -1), (key2088, -1), (key2178, -1), (key2190, -1), (key2331, 2), (key2334, 2), (key2035, -1), (key2038, -1), (key2065, 1), (key2073, 1), (key2035, -1), (key2038, -1), (key2180, 1), (key2190, 1), (key2065, 1), (key2073, 1), (key2282, -1), (key2290, -1), (key2180, 1), (key2190, 1), (key2282, -1), (key2290, -1)]

theorem rawRowCheck6880 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block2.form5 = rawRow6880 := by decide +kernel

def row6880 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2065, -2), (key2073, 2), (key2083, 2), (key2088, -2), (key2178, -2), (key2180, 2), (key2278, 2), (key2282, -2), (key2329, -2), (key2331, 2)]

theorem rowCheck6880 : row6880 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6880 := by decide +kernel

theorem rowEval6880 (x : Key → ℝ) : Integer.Sparse.eval row6880 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6880, Integer.Sparse.eval_collectBalanced, rawRowCheck6880]

def rawRow6881 : Integer.Sparse Key := [(key2065, -2), (key2083, 1), (key2081, 1), (key2065, -2), (key2290, 1), (key2278, 1), (key2083, 1), (key2081, 1), (key2290, 1), (key2278, 1), (key2334, -2), (key2329, -2), (key2035, 2), (key2088, -1), (key2081, -1), (key2035, 2), (key2190, -1), (key2178, -1), (key2088, -1), (key2081, -1), (key2190, -1), (key2178, -1), (key2334, 2), (key2331, 2), (key2038, -1), (key2035, -1), (key2073, 1), (key2065, 1), (key2038, -1), (key2035, -1), (key2190, 1), (key2180, 1), (key2073, 1), (key2065, 1), (key2290, -1), (key2282, -1), (key2190, 1), (key2180, 1), (key2290, -1), (key2282, -1)]

theorem rawRowCheck6881 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block2.form5 = rawRow6881 := by decide +kernel

def row6881 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2065, -2), (key2073, 2), (key2083, 2), (key2088, -2), (key2178, -2), (key2180, 2), (key2278, 2), (key2282, -2), (key2329, -2), (key2331, 2)]

theorem rowCheck6881 : row6881 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6881 := by decide +kernel

theorem rowEval6881 (x : Key → ℝ) : Integer.Sparse.eval row6881 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6881, Integer.Sparse.eval_collectBalanced, rawRowCheck6881]

def rawRow6882 : Integer.Sparse Key := [(key2081, -2), (key2065, 1), (key2083, 1), (key2278, -2), (key2065, 1), (key2290, 1), (key2278, 1), (key2329, 1), (key2081, 1), (key2334, 1), (key2083, -2), (key2290, -2), (key2081, 2), (key2035, -1), (key2088, -1), (key2178, 2), (key2035, -1), (key2190, -1), (key2178, -1), (key2331, -1), (key2081, -1), (key2334, -1), (key2088, 2), (key2190, 2), (key2065, -1), (key2083, -1), (key2035, 1), (key2088, 1), (key2154, -1), (key2180, -1), (key2038, 1), (key2170, 1), (key2154, 1), (key2282, 1), (key2073, -1), (key2170, -1), (key2083, 1), (key2290, 1), (key2088, -1), (key2190, -1)]

theorem rawRowCheck6882 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block2.form5 = rawRow6882 := by decide +kernel

def row6882 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

theorem rowCheck6882 : row6882 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6882 := by decide +kernel

theorem rowEval6882 (x : Key → ℝ) : Integer.Sparse.eval row6882 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6882, Integer.Sparse.eval_collectBalanced, rawRowCheck6882]

def rawRow6883 : Integer.Sparse Key := [(key2081, -2), (key2083, 1), (key2065, 1), (key2278, -2), (key2290, 1), (key2065, 1), (key2329, 1), (key2278, 1), (key2334, 1), (key2081, 1), (key2290, -2), (key2083, -2), (key2081, 2), (key2088, -1), (key2035, -1), (key2178, 2), (key2190, -1), (key2035, -1), (key2331, -1), (key2178, -1), (key2334, -1), (key2081, -1), (key2190, 2), (key2088, 2), (key2083, -1), (key2065, -1), (key2088, 1), (key2035, 1), (key2180, -1), (key2154, -1), (key2170, 1), (key2038, 1), (key2282, 1), (key2154, 1), (key2170, -1), (key2073, -1), (key2290, 1), (key2083, 1), (key2190, -1), (key2088, -1)]

theorem rawRowCheck6883 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block2.form5 = rawRow6883 := by decide +kernel

def row6883 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

theorem rowCheck6883 : row6883 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6883 := by decide +kernel

theorem rowEval6883 (x : Key → ℝ) : Integer.Sparse.eval row6883 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6883, Integer.Sparse.eval_collectBalanced, rawRowCheck6883]

def rawRow6884 : Integer.Sparse Key := [(key2083, -2), (key2065, 1), (key2081, 1), (key2290, -2), (key2065, 1), (key2278, 1), (key2290, 1), (key2334, 1), (key2083, 1), (key2329, 1), (key2081, -2), (key2278, -2), (key2088, 2), (key2035, -1), (key2081, -1), (key2190, 2), (key2035, -1), (key2178, -1), (key2190, -1), (key2334, -1), (key2088, -1), (key2331, -1), (key2081, 2), (key2178, 2), (key2073, -1), (key2088, -1), (key2038, 1), (key2083, 1), (key2170, -1), (key2190, -1), (key2035, 1), (key2154, 1), (key2170, 1), (key2290, 1), (key2065, -1), (key2154, -1), (key2088, 1), (key2282, 1), (key2083, -1), (key2180, -1)]

theorem rawRowCheck6884 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block2.form5 = rawRow6884 := by decide +kernel

def row6884 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

theorem rowCheck6884 : row6884 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6884 := by decide +kernel

theorem rowEval6884 (x : Key → ℝ) : Integer.Sparse.eval row6884 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6884, Integer.Sparse.eval_collectBalanced, rawRowCheck6884]

def rawRow6885 : Integer.Sparse Key := [(key2083, -2), (key2081, 1), (key2065, 1), (key2290, -2), (key2278, 1), (key2065, 1), (key2334, 1), (key2290, 1), (key2329, 1), (key2083, 1), (key2278, -2), (key2081, -2), (key2088, 2), (key2081, -1), (key2035, -1), (key2190, 2), (key2178, -1), (key2035, -1), (key2334, -1), (key2190, -1), (key2331, -1), (key2088, -1), (key2178, 2), (key2081, 2), (key2088, -1), (key2073, -1), (key2083, 1), (key2038, 1), (key2190, -1), (key2170, -1), (key2154, 1), (key2035, 1), (key2290, 1), (key2170, 1), (key2154, -1), (key2065, -1), (key2282, 1), (key2088, 1), (key2180, -1), (key2083, -1)]

theorem rawRowCheck6885 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block2.form5 = rawRow6885 := by decide +kernel

def row6885 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

theorem rowCheck6885 : row6885 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6885 := by decide +kernel

theorem rowEval6885 (x : Key → ℝ) : Integer.Sparse.eval row6885 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6885, Integer.Sparse.eval_collectBalanced, rawRowCheck6885]

def rawRow6886 : Integer.Sparse Key := [(key2278, -2), (key2278, 1), (key2329, 1), (key2081, -2), (key2081, 1), (key2334, 1), (key2065, 1), (key2083, 1), (key2065, 1), (key2290, 1), (key2083, -2), (key2290, -2), (key2178, 2), (key2178, -1), (key2331, -1), (key2081, 2), (key2081, -1), (key2334, -1), (key2035, -1), (key2088, -1), (key2035, -1), (key2190, -1), (key2088, 2), (key2190, 2), (key2154, -1), (key2180, -1), (key2154, 1), (key2282, 1), (key2065, -1), (key2083, -1), (key2083, 1), (key2290, 1), (key2035, 1), (key2088, 1), (key2088, -1), (key2190, -1), (key2038, 1), (key2170, 1), (key2073, -1), (key2170, -1)]

theorem rawRowCheck6886 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block2.form5 = rawRow6886 := by decide +kernel

def row6886 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

theorem rowCheck6886 : row6886 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6886 := by decide +kernel

theorem rowEval6886 (x : Key → ℝ) : Integer.Sparse.eval row6886 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6886, Integer.Sparse.eval_collectBalanced, rawRowCheck6886]

def rawRow6887 : Integer.Sparse Key := [(key2278, -2), (key2329, 1), (key2278, 1), (key2081, -2), (key2334, 1), (key2081, 1), (key2083, 1), (key2065, 1), (key2290, 1), (key2065, 1), (key2290, -2), (key2083, -2), (key2178, 2), (key2331, -1), (key2178, -1), (key2081, 2), (key2334, -1), (key2081, -1), (key2088, -1), (key2035, -1), (key2190, -1), (key2035, -1), (key2190, 2), (key2088, 2), (key2180, -1), (key2154, -1), (key2282, 1), (key2154, 1), (key2083, -1), (key2065, -1), (key2290, 1), (key2083, 1), (key2088, 1), (key2035, 1), (key2190, -1), (key2088, -1), (key2170, 1), (key2038, 1), (key2170, -1), (key2073, -1)]

theorem rawRowCheck6887 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block2.form5 = rawRow6887 := by decide +kernel

def row6887 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

theorem rowCheck6887 : row6887 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6887 := by decide +kernel

theorem rowEval6887 (x : Key → ℝ) : Integer.Sparse.eval row6887 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6887, Integer.Sparse.eval_collectBalanced, rawRowCheck6887]

def rawRow6888 : Integer.Sparse Key := [(key2329, -2), (key2278, 1), (key2278, 1), (key2334, -2), (key2081, 1), (key2081, 1), (key2290, 1), (key2290, 1), (key2083, 1), (key2083, 1), (key2065, -2), (key2065, -2), (key2331, 2), (key2178, -1), (key2178, -1), (key2334, 2), (key2081, -1), (key2081, -1), (key2190, -1), (key2190, -1), (key2088, -1), (key2088, -1), (key2035, 2), (key2035, 2), (key2282, -1), (key2282, -1), (key2180, 1), (key2180, 1), (key2290, -1), (key2290, -1), (key2065, 1), (key2065, 1), (key2190, 1), (key2190, 1), (key2035, -1), (key2035, -1), (key2073, 1), (key2073, 1), (key2038, -1), (key2038, -1)]

theorem rawRowCheck6888 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block2.form5 = rawRow6888 := by decide +kernel

def row6888 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2065, -2), (key2073, 2), (key2083, 2), (key2088, -2), (key2178, -2), (key2180, 2), (key2278, 2), (key2282, -2), (key2329, -2), (key2331, 2)]

theorem rowCheck6888 : row6888 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6888 := by decide +kernel

theorem rowEval6888 (x : Key → ℝ) : Integer.Sparse.eval row6888 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6888, Integer.Sparse.eval_collectBalanced, rawRowCheck6888]

def rawRow6889 : Integer.Sparse Key := [(key2290, -2), (key2290, 1), (key2334, 1), (key2083, -2), (key2083, 1), (key2329, 1), (key2065, 1), (key2081, 1), (key2065, 1), (key2278, 1), (key2081, -2), (key2278, -2), (key2190, 2), (key2190, -1), (key2334, -1), (key2088, 2), (key2088, -1), (key2331, -1), (key2035, -1), (key2081, -1), (key2035, -1), (key2178, -1), (key2081, 2), (key2178, 2), (key2170, -1), (key2190, -1), (key2170, 1), (key2290, 1), (key2073, -1), (key2088, -1), (key2088, 1), (key2282, 1), (key2038, 1), (key2083, 1), (key2083, -1), (key2180, -1), (key2035, 1), (key2154, 1), (key2065, -1), (key2154, -1)]

theorem rawRowCheck6889 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -1, 0] GramFunctions.Block2.form5 = rawRow6889 := by decide +kernel

def row6889 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

theorem rowCheck6889 : row6889 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6889 := by decide +kernel

theorem rowEval6889 (x : Key → ℝ) : Integer.Sparse.eval row6889 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -1, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6889, Integer.Sparse.eval_collectBalanced, rawRowCheck6889]

def rawRow6890 : Integer.Sparse Key := [(key2290, -2), (key2334, 1), (key2290, 1), (key2083, -2), (key2329, 1), (key2083, 1), (key2081, 1), (key2065, 1), (key2278, 1), (key2065, 1), (key2278, -2), (key2081, -2), (key2190, 2), (key2334, -1), (key2190, -1), (key2088, 2), (key2331, -1), (key2088, -1), (key2081, -1), (key2035, -1), (key2178, -1), (key2035, -1), (key2178, 2), (key2081, 2), (key2190, -1), (key2170, -1), (key2290, 1), (key2170, 1), (key2088, -1), (key2073, -1), (key2282, 1), (key2088, 1), (key2083, 1), (key2038, 1), (key2180, -1), (key2083, -1), (key2154, 1), (key2035, 1), (key2154, -1), (key2065, -1)]

theorem rawRowCheck6890 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 0, -1] GramFunctions.Block2.form5 = rawRow6890 := by decide +kernel

def row6890 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

theorem rowCheck6890 : row6890 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6890 := by decide +kernel

theorem rowEval6890 (x : Key → ℝ) : Integer.Sparse.eval row6890 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 0, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6890, Integer.Sparse.eval_collectBalanced, rawRowCheck6890]

def rawRow6891 : Integer.Sparse Key := [(key2334, -2), (key2290, 1), (key2290, 1), (key2329, -2), (key2083, 1), (key2083, 1), (key2278, 1), (key2278, 1), (key2081, 1), (key2081, 1), (key2065, -2), (key2065, -2), (key2334, 2), (key2190, -1), (key2190, -1), (key2331, 2), (key2088, -1), (key2088, -1), (key2178, -1), (key2178, -1), (key2081, -1), (key2081, -1), (key2035, 2), (key2035, 2), (key2290, -1), (key2290, -1), (key2190, 1), (key2190, 1), (key2282, -1), (key2282, -1), (key2073, 1), (key2073, 1), (key2180, 1), (key2180, 1), (key2038, -1), (key2038, -1), (key2065, 1), (key2065, 1), (key2035, -1), (key2035, -1)]

theorem rawRowCheck6891 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -1, -1] GramFunctions.Block2.form5 = rawRow6891 := by decide +kernel

def row6891 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2065, -2), (key2073, 2), (key2083, 2), (key2088, -2), (key2178, -2), (key2180, 2), (key2278, 2), (key2282, -2), (key2329, -2), (key2331, 2)]

theorem rowCheck6891 : row6891 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6891 := by decide +kernel

theorem rowEval6891 (x : Key → ℝ) : Integer.Sparse.eval row6891 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -1, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6891, Integer.Sparse.eval_collectBalanced, rawRowCheck6891]

def rawRow6892 : Integer.Sparse Key := [(key2073, -2), (key2088, 1), (key2088, 1), (key2073, -2), (key2282, 1), (key2282, 1), (key2088, 1), (key2088, 1), (key2282, 1), (key2282, 1), (key2331, -2), (key2331, -2), (key2038, 2), (key2083, -1), (key2083, -1), (key2038, 2), (key2180, -1), (key2180, -1), (key2083, -1), (key2083, -1), (key2180, -1), (key2180, -1), (key2329, 2), (key2329, 2), (key2035, -1), (key2035, -1), (key2065, 1), (key2065, 1), (key2035, -1), (key2035, -1), (key2178, 1), (key2178, 1), (key2065, 1), (key2065, 1), (key2278, -1), (key2278, -1), (key2178, 1), (key2178, 1), (key2278, -1), (key2278, -1)]

theorem rawRowCheck6892 : GramPolynomial.normalizedRow 0 ![1, 1, -1, -1, 0, 0] GramFunctions.Block2.form5 = rawRow6892 := by decide +kernel

def row6892 : Integer.Sparse Key := [(key2035, -4), (key2038, 4), (key2065, 4), (key2073, -4), (key2083, -4), (key2088, 4), (key2178, 4), (key2180, -4), (key2278, -4), (key2282, 4), (key2329, 4), (key2331, -4)]

theorem rowCheck6892 : row6892 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6892 := by decide +kernel

theorem rowEval6892 (x : Key → ℝ) : Integer.Sparse.eval row6892 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, -1, 0, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6892, Integer.Sparse.eval_collectBalanced, rawRowCheck6892]

def rawRow6893 : Integer.Sparse Key := [(key2088, -2), (key2073, 1), (key2088, 1), (key2282, -2), (key2073, 1), (key2282, 1), (key2282, 1), (key2331, 1), (key2088, 1), (key2331, 1), (key2088, -2), (key2282, -2), (key2083, 2), (key2038, -1), (key2083, -1), (key2180, 2), (key2038, -1), (key2180, -1), (key2180, -1), (key2329, -1), (key2083, -1), (key2329, -1), (key2083, 2), (key2180, 2), (key2065, -1), (key2081, -1), (key2035, 1), (key2081, 1), (key2154, -1), (key2178, -1), (key2035, 1), (key2154, 1), (key2154, 1), (key2278, 1), (key2065, -1), (key2154, -1), (key2081, 1), (key2278, 1), (key2081, -1), (key2178, -1)]

theorem rawRowCheck6893 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -1, 0] GramFunctions.Block2.form5 = rawRow6893 := by decide +kernel

def row6893 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2065, -2), (key2073, 2), (key2083, 2), (key2088, -2), (key2178, -2), (key2180, 2), (key2278, 2), (key2282, -2), (key2329, -2), (key2331, 2)]

theorem rowCheck6893 : row6893 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6893 := by decide +kernel

theorem rowEval6893 (x : Key → ℝ) : Integer.Sparse.eval row6893 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -1, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6893, Integer.Sparse.eval_collectBalanced, rawRowCheck6893]

def rawRow6894 : Integer.Sparse Key := [(key2088, -2), (key2088, 1), (key2073, 1), (key2282, -2), (key2282, 1), (key2073, 1), (key2331, 1), (key2282, 1), (key2331, 1), (key2088, 1), (key2282, -2), (key2088, -2), (key2083, 2), (key2083, -1), (key2038, -1), (key2180, 2), (key2180, -1), (key2038, -1), (key2329, -1), (key2180, -1), (key2329, -1), (key2083, -1), (key2180, 2), (key2083, 2), (key2081, -1), (key2065, -1), (key2081, 1), (key2035, 1), (key2178, -1), (key2154, -1), (key2154, 1), (key2035, 1), (key2278, 1), (key2154, 1), (key2154, -1), (key2065, -1), (key2278, 1), (key2081, 1), (key2178, -1), (key2081, -1)]

theorem rawRowCheck6894 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 0, -1] GramFunctions.Block2.form5 = rawRow6894 := by decide +kernel

def row6894 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2065, -2), (key2073, 2), (key2083, 2), (key2088, -2), (key2178, -2), (key2180, 2), (key2278, 2), (key2282, -2), (key2329, -2), (key2331, 2)]

theorem rowCheck6894 : row6894 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6894 := by decide +kernel

theorem rowEval6894 (x : Key → ℝ) : Integer.Sparse.eval row6894 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 0, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6894, Integer.Sparse.eval_collectBalanced, rawRowCheck6894]

def rawRow6895 : Integer.Sparse Key := [(key2282, -2), (key2282, 1), (key2331, 1), (key2088, -2), (key2088, 1), (key2331, 1), (key2073, 1), (key2088, 1), (key2073, 1), (key2282, 1), (key2088, -2), (key2282, -2), (key2180, 2), (key2180, -1), (key2329, -1), (key2083, 2), (key2083, -1), (key2329, -1), (key2038, -1), (key2083, -1), (key2038, -1), (key2180, -1), (key2083, 2), (key2180, 2), (key2154, -1), (key2178, -1), (key2154, 1), (key2278, 1), (key2065, -1), (key2081, -1), (key2081, 1), (key2278, 1), (key2035, 1), (key2081, 1), (key2081, -1), (key2178, -1), (key2035, 1), (key2154, 1), (key2065, -1), (key2154, -1)]

theorem rawRowCheck6895 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -1, 0] GramFunctions.Block2.form5 = rawRow6895 := by decide +kernel

def row6895 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2065, -2), (key2073, 2), (key2083, 2), (key2088, -2), (key2178, -2), (key2180, 2), (key2278, 2), (key2282, -2), (key2329, -2), (key2331, 2)]

theorem rowCheck6895 : row6895 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6895 := by decide +kernel

theorem rowEval6895 (x : Key → ℝ) : Integer.Sparse.eval row6895 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -1, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6895, Integer.Sparse.eval_collectBalanced, rawRowCheck6895]

def rawRow6896 : Integer.Sparse Key := [(key2282, -2), (key2331, 1), (key2282, 1), (key2088, -2), (key2331, 1), (key2088, 1), (key2088, 1), (key2073, 1), (key2282, 1), (key2073, 1), (key2282, -2), (key2088, -2), (key2180, 2), (key2329, -1), (key2180, -1), (key2083, 2), (key2329, -1), (key2083, -1), (key2083, -1), (key2038, -1), (key2180, -1), (key2038, -1), (key2180, 2), (key2083, 2), (key2178, -1), (key2154, -1), (key2278, 1), (key2154, 1), (key2081, -1), (key2065, -1), (key2278, 1), (key2081, 1), (key2081, 1), (key2035, 1), (key2178, -1), (key2081, -1), (key2154, 1), (key2035, 1), (key2154, -1), (key2065, -1)]

theorem rawRowCheck6896 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 0, -1] GramFunctions.Block2.form5 = rawRow6896 := by decide +kernel

def row6896 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2065, -2), (key2073, 2), (key2083, 2), (key2088, -2), (key2178, -2), (key2180, 2), (key2278, 2), (key2282, -2), (key2329, -2), (key2331, 2)]

theorem rowCheck6896 : row6896 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6896 := by decide +kernel

theorem rowEval6896 (x : Key → ℝ) : Integer.Sparse.eval row6896 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 0, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6896, Integer.Sparse.eval_collectBalanced, rawRowCheck6896]

def rawRow6897 : Integer.Sparse Key := [(key2331, -2), (key2282, 1), (key2282, 1), (key2331, -2), (key2088, 1), (key2088, 1), (key2282, 1), (key2282, 1), (key2088, 1), (key2088, 1), (key2073, -2), (key2073, -2), (key2329, 2), (key2180, -1), (key2180, -1), (key2329, 2), (key2083, -1), (key2083, -1), (key2180, -1), (key2180, -1), (key2083, -1), (key2083, -1), (key2038, 2), (key2038, 2), (key2278, -1), (key2278, -1), (key2178, 1), (key2178, 1), (key2278, -1), (key2278, -1), (key2065, 1), (key2065, 1), (key2178, 1), (key2178, 1), (key2035, -1), (key2035, -1), (key2065, 1), (key2065, 1), (key2035, -1), (key2035, -1)]

theorem rawRowCheck6897 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -1, -1] GramFunctions.Block2.form5 = rawRow6897 := by decide +kernel

def row6897 : Integer.Sparse Key := [(key2035, -4), (key2038, 4), (key2065, 4), (key2073, -4), (key2083, -4), (key2088, 4), (key2178, 4), (key2180, -4), (key2278, -4), (key2282, 4), (key2329, 4), (key2331, -4)]

theorem rowCheck6897 : row6897 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6897 := by decide +kernel

theorem rowEval6897 (x : Key → ℝ) : Integer.Sparse.eval row6897 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -1, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6897, Integer.Sparse.eval_collectBalanced, rawRowCheck6897]

def rawRow6898 : Integer.Sparse Key := [(key725, -1), (key726, -1), (key726, 2), (key728, -1), (key729, -1), (key728, 2), (key735, 2), (key729, -1), (key735, -1), (key739, 2), (key739, -1), (key744, -1), (key725, 1), (key726, 1), (key726, -2), (key794, 1), (key795, 1), (key794, -2), (key813, -2), (key795, 1), (key813, 1), (key819, -2), (key819, 1), (key826, 1), (key728, -1), (key735, -1), (key729, 1), (key735, 1), (key794, 1), (key813, 1), (key795, -1), (key813, -1), (key864, -1), (key869, -1), (key864, 1), (key878, 1), (key899, 1), (key903, 1), (key899, -1), (key909, -1)]

theorem rawRowCheck6898 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block2.form6 = rawRow6898 := by decide +kernel

def row6898 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

theorem rowCheck6898 : row6898 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6898 := by decide +kernel

theorem rowEval6898 (x : Key → ℝ) : Integer.Sparse.eval row6898 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6898, Integer.Sparse.eval_collectBalanced, rawRowCheck6898]

def rawRow6899 : Integer.Sparse Key := [(key726, -1), (key725, -1), (key726, 2), (key729, -1), (key728, -1), (key735, 2), (key728, 2), (key735, -1), (key729, -1), (key739, 2), (key744, -1), (key739, -1), (key726, 1), (key725, 1), (key726, -2), (key795, 1), (key794, 1), (key813, -2), (key794, -2), (key813, 1), (key795, 1), (key819, -2), (key826, 1), (key819, 1), (key735, -1), (key728, -1), (key735, 1), (key729, 1), (key813, 1), (key794, 1), (key813, -1), (key795, -1), (key869, -1), (key864, -1), (key878, 1), (key864, 1), (key903, 1), (key899, 1), (key909, -1), (key899, -1)]

theorem rawRowCheck6899 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block2.form6 = rawRow6899 := by decide +kernel

def row6899 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

theorem rowCheck6899 : row6899 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6899 := by decide +kernel

theorem rowEval6899 (x : Key → ℝ) : Integer.Sparse.eval row6899 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6899, Integer.Sparse.eval_collectBalanced, rawRowCheck6899]

def rawRow6900 : Integer.Sparse Key := [(key726, -1), (key726, -1), (key725, 2), (key735, -1), (key735, -1), (key729, 2), (key729, 2), (key728, -1), (key728, -1), (key744, 2), (key739, -1), (key739, -1), (key726, 1), (key726, 1), (key725, -2), (key813, 1), (key813, 1), (key795, -2), (key795, -2), (key794, 1), (key794, 1), (key826, -2), (key819, 1), (key819, 1), (key729, -1), (key729, -1), (key728, 1), (key728, 1), (key795, 1), (key795, 1), (key794, -1), (key794, -1), (key878, -1), (key878, -1), (key869, 1), (key869, 1), (key909, 1), (key909, 1), (key903, -1), (key903, -1)]

theorem rawRowCheck6900 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block2.form6 = rawRow6900 := by decide +kernel

def row6900 : Integer.Sparse Key := [(key729, 2), (key735, -2), (key739, -2), (key744, 2), (key795, -2), (key813, 2), (key819, 2), (key826, -2), (key869, 2), (key878, -2), (key903, -2), (key909, 2)]

theorem rowCheck6900 : row6900 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6900 := by decide +kernel

theorem rowEval6900 (x : Key → ℝ) : Integer.Sparse.eval row6900 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6900, Integer.Sparse.eval_collectBalanced, rawRowCheck6900]

def rawRow6901 : Integer.Sparse Key := [(key728, -1), (key729, -1), (key739, 2), (key725, -1), (key726, -1), (key728, 2), (key735, 2), (key739, -1), (key744, -1), (key726, 2), (key729, -1), (key735, -1), (key794, 1), (key795, 1), (key819, -2), (key725, 1), (key726, 1), (key794, -2), (key813, -2), (key819, 1), (key826, 1), (key726, -2), (key795, 1), (key813, 1), (key864, -1), (key869, -1), (key899, 1), (key903, 1), (key864, 1), (key878, 1), (key899, -1), (key909, -1), (key728, -1), (key735, -1), (key794, 1), (key813, 1), (key729, 1), (key735, 1), (key795, -1), (key813, -1)]

theorem rawRowCheck6901 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block2.form6 = rawRow6901 := by decide +kernel

def row6901 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

theorem rowCheck6901 : row6901 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6901 := by decide +kernel

theorem rowEval6901 (x : Key → ℝ) : Integer.Sparse.eval row6901 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6901, Integer.Sparse.eval_collectBalanced, rawRowCheck6901]

def rawRow6902 : Integer.Sparse Key := [(key729, -1), (key728, -1), (key739, 2), (key726, -1), (key725, -1), (key735, 2), (key728, 2), (key744, -1), (key739, -1), (key726, 2), (key735, -1), (key729, -1), (key795, 1), (key794, 1), (key819, -2), (key726, 1), (key725, 1), (key813, -2), (key794, -2), (key826, 1), (key819, 1), (key726, -2), (key813, 1), (key795, 1), (key869, -1), (key864, -1), (key903, 1), (key899, 1), (key878, 1), (key864, 1), (key909, -1), (key899, -1), (key735, -1), (key728, -1), (key813, 1), (key794, 1), (key735, 1), (key729, 1), (key813, -1), (key795, -1)]

theorem rawRowCheck6902 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block2.form6 = rawRow6902 := by decide +kernel

def row6902 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

theorem rowCheck6902 : row6902 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6902 := by decide +kernel

theorem rowEval6902 (x : Key → ℝ) : Integer.Sparse.eval row6902 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6902, Integer.Sparse.eval_collectBalanced, rawRowCheck6902]

def rawRow6903 : Integer.Sparse Key := [(key728, -1), (key739, -1), (key729, 2), (key728, -1), (key739, -1), (key725, 2), (key744, 2), (key726, -1), (key735, -1), (key729, 2), (key726, -1), (key735, -1), (key794, 1), (key819, 1), (key795, -2), (key794, 1), (key819, 1), (key725, -2), (key826, -2), (key726, 1), (key813, 1), (key795, -2), (key726, 1), (key813, 1), (key794, -1), (key903, -1), (key795, 1), (key869, 1), (key728, 1), (key909, 1), (key729, -1), (key878, -1), (key794, -1), (key903, -1), (key728, 1), (key909, 1), (key795, 1), (key869, 1), (key729, -1), (key878, -1)]

theorem rawRowCheck6903 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block2.form6 = rawRow6903 := by decide +kernel

def row6903 : Integer.Sparse Key := [(key729, 2), (key735, -2), (key739, -2), (key744, 2), (key795, -2), (key813, 2), (key819, 2), (key826, -2), (key869, 2), (key878, -2), (key903, -2), (key909, 2)]

theorem rowCheck6903 : row6903 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6903 := by decide +kernel

theorem rowEval6903 (x : Key → ℝ) : Integer.Sparse.eval row6903 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6903, Integer.Sparse.eval_collectBalanced, rawRowCheck6903]

def rawRow6904 : Integer.Sparse Key := [(key739, -1), (key728, -1), (key729, 2), (key739, -1), (key728, -1), (key744, 2), (key725, 2), (key735, -1), (key726, -1), (key729, 2), (key735, -1), (key726, -1), (key819, 1), (key794, 1), (key795, -2), (key819, 1), (key794, 1), (key826, -2), (key725, -2), (key813, 1), (key726, 1), (key795, -2), (key813, 1), (key726, 1), (key903, -1), (key794, -1), (key869, 1), (key795, 1), (key909, 1), (key728, 1), (key878, -1), (key729, -1), (key903, -1), (key794, -1), (key909, 1), (key728, 1), (key869, 1), (key795, 1), (key878, -1), (key729, -1)]

theorem rawRowCheck6904 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block2.form6 = rawRow6904 := by decide +kernel

def row6904 : Integer.Sparse Key := [(key729, 2), (key735, -2), (key739, -2), (key744, 2), (key795, -2), (key813, 2), (key819, 2), (key826, -2), (key869, 2), (key878, -2), (key903, -2), (key909, 2)]

theorem rowCheck6904 : row6904 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6904 := by decide +kernel

theorem rowEval6904 (x : Key → ℝ) : Integer.Sparse.eval row6904 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6904, Integer.Sparse.eval_collectBalanced, rawRowCheck6904]

def rawRow6905 : Integer.Sparse Key := [(key729, -1), (key739, -1), (key728, 2), (key735, -1), (key744, -1), (key726, 2), (key739, 2), (key725, -1), (key728, -1), (key735, 2), (key726, -1), (key729, -1), (key795, 1), (key819, 1), (key794, -2), (key813, 1), (key826, 1), (key726, -2), (key819, -2), (key725, 1), (key794, 1), (key813, -2), (key726, 1), (key795, 1), (key795, -1), (key899, -1), (key794, 1), (key864, 1), (key729, 1), (key899, 1), (key728, -1), (key864, -1), (key813, -1), (key909, -1), (key735, 1), (key903, 1), (key813, 1), (key878, 1), (key735, -1), (key869, -1)]

theorem rawRowCheck6905 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block2.form6 = rawRow6905 := by decide +kernel

def row6905 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

theorem rowCheck6905 : row6905 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6905 := by decide +kernel

theorem rowEval6905 (x : Key → ℝ) : Integer.Sparse.eval row6905 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6905, Integer.Sparse.eval_collectBalanced, rawRowCheck6905]

def rawRow6906 : Integer.Sparse Key := [(key739, -1), (key729, -1), (key728, 2), (key744, -1), (key735, -1), (key739, 2), (key726, 2), (key728, -1), (key725, -1), (key735, 2), (key729, -1), (key726, -1), (key819, 1), (key795, 1), (key794, -2), (key826, 1), (key813, 1), (key819, -2), (key726, -2), (key794, 1), (key725, 1), (key813, -2), (key795, 1), (key726, 1), (key899, -1), (key795, -1), (key864, 1), (key794, 1), (key899, 1), (key729, 1), (key864, -1), (key728, -1), (key909, -1), (key813, -1), (key903, 1), (key735, 1), (key878, 1), (key813, 1), (key869, -1), (key735, -1)]

theorem rawRowCheck6906 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block2.form6 = rawRow6906 := by decide +kernel

def row6906 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

theorem rowCheck6906 : row6906 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6906 := by decide +kernel

theorem rowEval6906 (x : Key → ℝ) : Integer.Sparse.eval row6906 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6906, Integer.Sparse.eval_collectBalanced, rawRowCheck6906]

def rawRow6907 : Integer.Sparse Key := [(key735, -1), (key735, -1), (key744, 2), (key726, -1), (key726, -1), (key729, 2), (key729, 2), (key739, -1), (key739, -1), (key725, 2), (key728, -1), (key728, -1), (key813, 1), (key813, 1), (key826, -2), (key726, 1), (key726, 1), (key795, -2), (key795, -2), (key819, 1), (key819, 1), (key725, -2), (key794, 1), (key794, 1), (key878, -1), (key878, -1), (key909, 1), (key909, 1), (key869, 1), (key869, 1), (key903, -1), (key903, -1), (key729, -1), (key729, -1), (key795, 1), (key795, 1), (key728, 1), (key728, 1), (key794, -1), (key794, -1)]

theorem rawRowCheck6907 : GramPolynomial.normalizedRow 0 ![1, -1, 1, -1, 0, 0] GramFunctions.Block2.form6 = rawRow6907 := by decide +kernel

def row6907 : Integer.Sparse Key := [(key729, 2), (key735, -2), (key739, -2), (key744, 2), (key795, -2), (key813, 2), (key819, 2), (key826, -2), (key869, 2), (key878, -2), (key903, -2), (key909, 2)]

theorem rowCheck6907 : row6907 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6907 := by decide +kernel

theorem rowEval6907 (x : Key → ℝ) : Integer.Sparse.eval row6907 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, -1, 0, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6907, Integer.Sparse.eval_collectBalanced, rawRowCheck6907]

def rawRow6908 : Integer.Sparse Key := [(key735, -1), (key744, -1), (key735, 2), (key729, -1), (key739, -1), (key726, 2), (key739, 2), (key726, -1), (key729, -1), (key728, 2), (key725, -1), (key728, -1), (key813, 1), (key826, 1), (key813, -2), (key795, 1), (key819, 1), (key726, -2), (key819, -2), (key726, 1), (key795, 1), (key794, -2), (key725, 1), (key794, 1), (key813, -1), (key909, -1), (key813, 1), (key878, 1), (key735, 1), (key903, 1), (key735, -1), (key869, -1), (key795, -1), (key899, -1), (key729, 1), (key899, 1), (key794, 1), (key864, 1), (key728, -1), (key864, -1)]

theorem rawRowCheck6908 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -1, 0] GramFunctions.Block2.form6 = rawRow6908 := by decide +kernel

def row6908 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

theorem rowCheck6908 : row6908 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6908 := by decide +kernel

theorem rowEval6908 (x : Key → ℝ) : Integer.Sparse.eval row6908 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6908, Integer.Sparse.eval_collectBalanced, rawRowCheck6908]

def rawRow6909 : Integer.Sparse Key := [(key744, -1), (key735, -1), (key735, 2), (key739, -1), (key729, -1), (key739, 2), (key726, 2), (key729, -1), (key726, -1), (key728, 2), (key728, -1), (key725, -1), (key826, 1), (key813, 1), (key813, -2), (key819, 1), (key795, 1), (key819, -2), (key726, -2), (key795, 1), (key726, 1), (key794, -2), (key794, 1), (key725, 1), (key909, -1), (key813, -1), (key878, 1), (key813, 1), (key903, 1), (key735, 1), (key869, -1), (key735, -1), (key899, -1), (key795, -1), (key899, 1), (key729, 1), (key864, 1), (key794, 1), (key864, -1), (key728, -1)]

theorem rawRowCheck6909 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 0, -1] GramFunctions.Block2.form6 = rawRow6909 := by decide +kernel

def row6909 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

theorem rowCheck6909 : row6909 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6909 := by decide +kernel

theorem rowEval6909 (x : Key → ℝ) : Integer.Sparse.eval row6909 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 0, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6909, Integer.Sparse.eval_collectBalanced, rawRowCheck6909]

def rawRow6910 : Integer.Sparse Key := [(key794, -1), (key795, -1), (key819, 2), (key794, -1), (key795, -1), (key864, 2), (key869, 2), (key899, -1), (key903, -1), (key819, 2), (key899, -1), (key903, -1), (key728, 1), (key729, 1), (key739, -2), (key728, 1), (key729, 1), (key864, -2), (key878, -2), (key899, 1), (key909, 1), (key739, -2), (key899, 1), (key909, 1), (key728, -1), (key735, -1), (key739, 1), (key744, 1), (key794, 1), (key813, 1), (key819, -1), (key826, -1), (key728, -1), (key735, -1), (key794, 1), (key813, 1), (key739, 1), (key744, 1), (key819, -1), (key826, -1)]

theorem rawRowCheck6910 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block2.form6 = rawRow6910 := by decide +kernel

def row6910 : Integer.Sparse Key := [(key729, 2), (key735, -2), (key739, -2), (key744, 2), (key795, -2), (key813, 2), (key819, 2), (key826, -2), (key869, 2), (key878, -2), (key903, -2), (key909, 2)]

theorem rowCheck6910 : row6910 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6910 := by decide +kernel

theorem rowEval6910 (x : Key → ℝ) : Integer.Sparse.eval row6910 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6910, Integer.Sparse.eval_collectBalanced, rawRowCheck6910]

def rawRow6911 : Integer.Sparse Key := [(key795, -1), (key794, -1), (key819, 2), (key795, -1), (key794, -1), (key869, 2), (key864, 2), (key903, -1), (key899, -1), (key819, 2), (key903, -1), (key899, -1), (key729, 1), (key728, 1), (key739, -2), (key729, 1), (key728, 1), (key878, -2), (key864, -2), (key909, 1), (key899, 1), (key739, -2), (key909, 1), (key899, 1), (key735, -1), (key728, -1), (key744, 1), (key739, 1), (key813, 1), (key794, 1), (key826, -1), (key819, -1), (key735, -1), (key728, -1), (key813, 1), (key794, 1), (key744, 1), (key739, 1), (key826, -1), (key819, -1)]

theorem rawRowCheck6911 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block2.form6 = rawRow6911 := by decide +kernel

def row6911 : Integer.Sparse Key := [(key729, 2), (key735, -2), (key739, -2), (key744, 2), (key795, -2), (key813, 2), (key819, 2), (key826, -2), (key869, 2), (key878, -2), (key903, -2), (key909, 2)]

theorem rowCheck6911 : row6911 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6911 := by decide +kernel

theorem rowEval6911 (x : Key → ℝ) : Integer.Sparse.eval row6911 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6911, Integer.Sparse.eval_collectBalanced, rawRowCheck6911]

end MUB6.Certificate.GramRows

end OAI
