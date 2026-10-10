import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
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

def rawRow17664 : Integer.Sparse Key := [(key2301, -2), (key2301, -2), (key2233, -2), (key2238, 6), (key2301, -2), (key2301, -2), (key2233, -2), (key2314, 2), (key2314, 2), (key2008, 2), (key2008, 2), (key1988, 2), (key1988, 2), (key2258, -2), (key1993, -2), (key1993, -2), (key2238, 6), (key2258, -2), (key1993, -2), (key1993, -2)]

theorem rawRowCheck17664 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form2 = rawRow17664 := by decide +kernel

def row17664 : Integer.Sparse Key := [(key1988, 4), (key1993, -8), (key2008, 4), (key2233, -4), (key2238, 12), (key2258, -4), (key2301, -8), (key2314, 4)]

theorem rowCheck17664 : row17664 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17664 := by decide +kernel

theorem rowEval17664 (x : Key → ℝ) : Integer.Sparse.eval row17664 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17664, Integer.Sparse.eval_collectBalanced, rawRowCheck17664]

def rawRow17665 : Integer.Sparse Key := [(key2030, 6), (key2060, -2), (key2060, -2), (key2068, -2), (key2030, 6), (key2149, -2), (key2149, -2), (key2165, -2), (key2060, -2), (key2060, -2), (key2068, -2), (key2149, -2), (key2149, -2), (key2165, -2), (key2242, 2), (key2245, 2), (key2242, 2), (key2252, 2), (key2245, 2), (key2252, 2)]

theorem rawRowCheck17665 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form3 = rawRow17665 := by decide +kernel

def row17665 : Integer.Sparse Key := [(key2030, 12), (key2060, -8), (key2068, -4), (key2149, -8), (key2165, -4), (key2242, 4), (key2245, 4), (key2252, 4)]

theorem rowCheck17665 : row17665 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17665 := by decide +kernel

theorem rowEval17665 (x : Key → ℝ) : Integer.Sparse.eval row17665 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17665, Integer.Sparse.eval_collectBalanced, rawRowCheck17665]

def rawRow17666 : Integer.Sparse Key := [(key2030, 6), (key2060, -2), (key2068, -2), (key2060, -2), (key2030, 6), (key2149, -2), (key2165, -2), (key2149, -2), (key2060, -2), (key2068, -2), (key2060, -2), (key2149, -2), (key2165, -2), (key2149, -2), (key2245, 2), (key2242, 2), (key2252, 2), (key2242, 2), (key2252, 2), (key2245, 2)]

theorem rawRowCheck17666 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form3 = rawRow17666 := by decide +kernel

def row17666 : Integer.Sparse Key := [(key2030, 12), (key2060, -8), (key2068, -4), (key2149, -8), (key2165, -4), (key2242, 4), (key2245, 4), (key2252, 4)]

theorem rowCheck17666 : row17666 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17666 := by decide +kernel

theorem rowEval17666 (x : Key → ℝ) : Integer.Sparse.eval row17666 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck17666, Integer.Sparse.eval_collectBalanced, rawRowCheck17666]

def rawRow17667 : Integer.Sparse Key := [(key2030, 6), (key2068, -2), (key2060, -2), (key2060, -2), (key2030, 6), (key2165, -2), (key2149, -2), (key2149, -2), (key2068, -2), (key2060, -2), (key2060, -2), (key2165, -2), (key2149, -2), (key2149, -2), (key2252, 2), (key2252, 2), (key2245, 2), (key2245, 2), (key2242, 2), (key2242, 2)]

theorem rawRowCheck17667 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form3 = rawRow17667 := by decide +kernel

def row17667 : Integer.Sparse Key := [(key2030, 12), (key2060, -8), (key2068, -4), (key2149, -8), (key2165, -4), (key2242, 4), (key2245, 4), (key2252, 4)]

theorem rowCheck17667 : row17667 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17667 := by decide +kernel

theorem rowEval17667 (x : Key → ℝ) : Integer.Sparse.eval row17667 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck17667, Integer.Sparse.eval_collectBalanced, rawRowCheck17667]

def rawRow17668 : Integer.Sparse Key := [(key2060, 6), (key2030, -2), (key2060, -2), (key2068, -2), (key2149, 6), (key2030, -2), (key2149, -2), (key2165, -2), (key2149, -2), (key2242, -2), (key2245, -2), (key2060, -2), (key2242, -2), (key2252, -2), (key2060, 2), (key2068, 2), (key2149, 2), (key2165, 2), (key2245, 2), (key2252, 2)]

theorem rawRowCheck17668 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form3 = rawRow17668 := by decide +kernel

def row17668 : Integer.Sparse Key := [(key2030, -4), (key2060, 4), (key2149, 4), (key2242, -4)]

theorem rowCheck17668 : row17668 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17668 := by decide +kernel

theorem rowEval17668 (x : Key → ℝ) : Integer.Sparse.eval row17668 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17668, Integer.Sparse.eval_collectBalanced, rawRowCheck17668]

def rawRow17669 : Integer.Sparse Key := [(key2060, 6), (key2030, -2), (key2068, -2), (key2060, -2), (key2149, 6), (key2030, -2), (key2165, -2), (key2149, -2), (key2149, -2), (key2245, -2), (key2242, -2), (key2060, -2), (key2252, -2), (key2242, -2), (key2068, 2), (key2060, 2), (key2165, 2), (key2149, 2), (key2252, 2), (key2245, 2)]

theorem rawRowCheck17669 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form3 = rawRow17669 := by decide +kernel

def row17669 : Integer.Sparse Key := [(key2030, -4), (key2060, 4), (key2149, 4), (key2242, -4)]

theorem rowCheck17669 : row17669 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17669 := by decide +kernel

theorem rowEval17669 (x : Key → ℝ) : Integer.Sparse.eval row17669 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck17669, Integer.Sparse.eval_collectBalanced, rawRowCheck17669]

def rawRow17670 : Integer.Sparse Key := [(key2060, 6), (key2060, -2), (key2030, -2), (key2068, -2), (key2149, 6), (key2149, -2), (key2030, -2), (key2165, -2), (key2242, -2), (key2149, -2), (key2245, -2), (key2242, -2), (key2060, -2), (key2252, -2), (key2149, 2), (key2245, 2), (key2060, 2), (key2252, 2), (key2068, 2), (key2165, 2)]

theorem rawRowCheck17670 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form3 = rawRow17670 := by decide +kernel

def row17670 : Integer.Sparse Key := [(key2030, -4), (key2060, 4), (key2149, 4), (key2242, -4)]

theorem rowCheck17670 : row17670 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17670 := by decide +kernel

theorem rowEval17670 (x : Key → ℝ) : Integer.Sparse.eval row17670 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17670, Integer.Sparse.eval_collectBalanced, rawRowCheck17670]

def rawRow17671 : Integer.Sparse Key := [(key2060, 6), (key2060, -2), (key2068, -2), (key2030, -2), (key2149, 6), (key2149, -2), (key2165, -2), (key2030, -2), (key2242, -2), (key2245, -2), (key2149, -2), (key2242, -2), (key2252, -2), (key2060, -2), (key2245, 2), (key2149, 2), (key2252, 2), (key2060, 2), (key2165, 2), (key2068, 2)]

theorem rawRowCheck17671 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form3 = rawRow17671 := by decide +kernel

def row17671 : Integer.Sparse Key := [(key2030, -4), (key2060, 4), (key2149, 4), (key2242, -4)]

theorem rowCheck17671 : row17671 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17671 := by decide +kernel

theorem rowEval17671 (x : Key → ℝ) : Integer.Sparse.eval row17671 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17671, Integer.Sparse.eval_collectBalanced, rawRowCheck17671]

def rawRow17672 : Integer.Sparse Key := [(key2060, 6), (key2068, -2), (key2030, -2), (key2060, -2), (key2149, 6), (key2165, -2), (key2030, -2), (key2149, -2), (key2245, -2), (key2149, -2), (key2242, -2), (key2252, -2), (key2060, -2), (key2242, -2), (key2165, 2), (key2252, 2), (key2068, 2), (key2245, 2), (key2060, 2), (key2149, 2)]

theorem rawRowCheck17672 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form3 = rawRow17672 := by decide +kernel

def row17672 : Integer.Sparse Key := [(key2030, -4), (key2060, 4), (key2149, 4), (key2242, -4)]

theorem rowCheck17672 : row17672 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17672 := by decide +kernel

theorem rowEval17672 (x : Key → ℝ) : Integer.Sparse.eval row17672 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck17672, Integer.Sparse.eval_collectBalanced, rawRowCheck17672]

def rawRow17673 : Integer.Sparse Key := [(key2060, 6), (key2068, -2), (key2060, -2), (key2030, -2), (key2149, 6), (key2165, -2), (key2149, -2), (key2030, -2), (key2245, -2), (key2242, -2), (key2149, -2), (key2252, -2), (key2242, -2), (key2060, -2), (key2252, 2), (key2165, 2), (key2245, 2), (key2068, 2), (key2149, 2), (key2060, 2)]

theorem rawRowCheck17673 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form3 = rawRow17673 := by decide +kernel

def row17673 : Integer.Sparse Key := [(key2030, -4), (key2060, 4), (key2149, 4), (key2242, -4)]

theorem rowCheck17673 : row17673 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17673 := by decide +kernel

theorem rowEval17673 (x : Key → ℝ) : Integer.Sparse.eval row17673 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17673, Integer.Sparse.eval_collectBalanced, rawRowCheck17673]

def rawRow17674 : Integer.Sparse Key := [(key2149, 6), (key2149, -2), (key2242, -2), (key2245, -2), (key2060, 6), (key2060, -2), (key2242, -2), (key2252, -2), (key2030, -2), (key2060, -2), (key2068, -2), (key2030, -2), (key2149, -2), (key2165, -2), (key2060, 2), (key2068, 2), (key2149, 2), (key2165, 2), (key2245, 2), (key2252, 2)]

theorem rawRowCheck17674 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form3 = rawRow17674 := by decide +kernel

def row17674 : Integer.Sparse Key := [(key2030, -4), (key2060, 4), (key2149, 4), (key2242, -4)]

theorem rowCheck17674 : row17674 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17674 := by decide +kernel

theorem rowEval17674 (x : Key → ℝ) : Integer.Sparse.eval row17674 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17674, Integer.Sparse.eval_collectBalanced, rawRowCheck17674]

def rawRow17675 : Integer.Sparse Key := [(key2149, 6), (key2149, -2), (key2245, -2), (key2242, -2), (key2060, 6), (key2060, -2), (key2252, -2), (key2242, -2), (key2030, -2), (key2068, -2), (key2060, -2), (key2030, -2), (key2165, -2), (key2149, -2), (key2068, 2), (key2060, 2), (key2165, 2), (key2149, 2), (key2252, 2), (key2245, 2)]

theorem rawRowCheck17675 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form3 = rawRow17675 := by decide +kernel

def row17675 : Integer.Sparse Key := [(key2030, -4), (key2060, 4), (key2149, 4), (key2242, -4)]

theorem rowCheck17675 : row17675 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17675 := by decide +kernel

theorem rowEval17675 (x : Key → ℝ) : Integer.Sparse.eval row17675 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck17675, Integer.Sparse.eval_collectBalanced, rawRowCheck17675]

def rawRow17676 : Integer.Sparse Key := [(key2149, 6), (key2242, -2), (key2149, -2), (key2245, -2), (key2060, 6), (key2242, -2), (key2060, -2), (key2252, -2), (key2060, -2), (key2030, -2), (key2068, -2), (key2149, -2), (key2030, -2), (key2165, -2), (key2149, 2), (key2245, 2), (key2060, 2), (key2252, 2), (key2068, 2), (key2165, 2)]

theorem rawRowCheck17676 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form3 = rawRow17676 := by decide +kernel

def row17676 : Integer.Sparse Key := [(key2030, -4), (key2060, 4), (key2149, 4), (key2242, -4)]

theorem rowCheck17676 : row17676 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17676 := by decide +kernel

theorem rowEval17676 (x : Key → ℝ) : Integer.Sparse.eval row17676 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17676, Integer.Sparse.eval_collectBalanced, rawRowCheck17676]

def rawRow17677 : Integer.Sparse Key := [(key2149, 6), (key2242, -2), (key2245, -2), (key2149, -2), (key2060, 6), (key2242, -2), (key2252, -2), (key2060, -2), (key2060, -2), (key2068, -2), (key2030, -2), (key2149, -2), (key2165, -2), (key2030, -2), (key2245, 2), (key2149, 2), (key2252, 2), (key2060, 2), (key2165, 2), (key2068, 2)]

theorem rawRowCheck17677 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form3 = rawRow17677 := by decide +kernel

def row17677 : Integer.Sparse Key := [(key2030, -4), (key2060, 4), (key2149, 4), (key2242, -4)]

theorem rowCheck17677 : row17677 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17677 := by decide +kernel

theorem rowEval17677 (x : Key → ℝ) : Integer.Sparse.eval row17677 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17677, Integer.Sparse.eval_collectBalanced, rawRowCheck17677]

def rawRow17678 : Integer.Sparse Key := [(key2149, 6), (key2245, -2), (key2149, -2), (key2242, -2), (key2060, 6), (key2252, -2), (key2060, -2), (key2242, -2), (key2068, -2), (key2030, -2), (key2060, -2), (key2165, -2), (key2030, -2), (key2149, -2), (key2165, 2), (key2252, 2), (key2068, 2), (key2245, 2), (key2060, 2), (key2149, 2)]

theorem rawRowCheck17678 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form3 = rawRow17678 := by decide +kernel

def row17678 : Integer.Sparse Key := [(key2030, -4), (key2060, 4), (key2149, 4), (key2242, -4)]

theorem rowCheck17678 : row17678 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17678 := by decide +kernel

theorem rowEval17678 (x : Key → ℝ) : Integer.Sparse.eval row17678 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck17678, Integer.Sparse.eval_collectBalanced, rawRowCheck17678]

def rawRow17679 : Integer.Sparse Key := [(key2149, 6), (key2245, -2), (key2242, -2), (key2149, -2), (key2060, 6), (key2252, -2), (key2242, -2), (key2060, -2), (key2068, -2), (key2060, -2), (key2030, -2), (key2165, -2), (key2149, -2), (key2030, -2), (key2252, 2), (key2165, 2), (key2245, 2), (key2068, 2), (key2149, 2), (key2060, 2)]

theorem rawRowCheck17679 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form3 = rawRow17679 := by decide +kernel

def row17679 : Integer.Sparse Key := [(key2030, -4), (key2060, 4), (key2149, 4), (key2242, -4)]

theorem rowCheck17679 : row17679 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17679 := by decide +kernel

theorem rowEval17679 (x : Key → ℝ) : Integer.Sparse.eval row17679 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17679, Integer.Sparse.eval_collectBalanced, rawRowCheck17679]

def rawRow17680 : Integer.Sparse Key := [(key2242, 6), (key2149, -2), (key2149, -2), (key2245, -2), (key2242, 6), (key2060, -2), (key2060, -2), (key2252, -2), (key2149, -2), (key2149, -2), (key2245, -2), (key2060, -2), (key2060, -2), (key2252, -2), (key2030, 2), (key2068, 2), (key2030, 2), (key2165, 2), (key2068, 2), (key2165, 2)]

theorem rawRowCheck17680 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form3 = rawRow17680 := by decide +kernel

def row17680 : Integer.Sparse Key := [(key2030, 4), (key2060, -8), (key2068, 4), (key2149, -8), (key2165, 4), (key2242, 12), (key2245, -4), (key2252, -4)]

theorem rowCheck17680 : row17680 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17680 := by decide +kernel

theorem rowEval17680 (x : Key → ℝ) : Integer.Sparse.eval row17680 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17680, Integer.Sparse.eval_collectBalanced, rawRowCheck17680]

def rawRow17681 : Integer.Sparse Key := [(key2242, 6), (key2149, -2), (key2245, -2), (key2149, -2), (key2242, 6), (key2060, -2), (key2252, -2), (key2060, -2), (key2149, -2), (key2245, -2), (key2149, -2), (key2060, -2), (key2252, -2), (key2060, -2), (key2068, 2), (key2030, 2), (key2165, 2), (key2030, 2), (key2165, 2), (key2068, 2)]

theorem rawRowCheck17681 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form3 = rawRow17681 := by decide +kernel

def row17681 : Integer.Sparse Key := [(key2030, 4), (key2060, -8), (key2068, 4), (key2149, -8), (key2165, 4), (key2242, 12), (key2245, -4), (key2252, -4)]

theorem rowCheck17681 : row17681 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17681 := by decide +kernel

theorem rowEval17681 (x : Key → ℝ) : Integer.Sparse.eval row17681 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17681, Integer.Sparse.eval_collectBalanced, rawRowCheck17681]

def rawRow17682 : Integer.Sparse Key := [(key2242, 6), (key2245, -2), (key2149, -2), (key2149, -2), (key2242, 6), (key2252, -2), (key2060, -2), (key2060, -2), (key2245, -2), (key2149, -2), (key2149, -2), (key2252, -2), (key2060, -2), (key2060, -2), (key2165, 2), (key2165, 2), (key2068, 2), (key2068, 2), (key2030, 2), (key2030, 2)]

theorem rawRowCheck17682 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form3 = rawRow17682 := by decide +kernel

def row17682 : Integer.Sparse Key := [(key2030, 4), (key2060, -8), (key2068, 4), (key2149, -8), (key2165, 4), (key2242, 12), (key2245, -4), (key2252, -4)]

theorem rowCheck17682 : row17682 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17682 := by decide +kernel

theorem rowEval17682 (x : Key → ℝ) : Integer.Sparse.eval row17682 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17682, Integer.Sparse.eval_collectBalanced, rawRowCheck17682]

def rawRow17683 : Integer.Sparse Key := [(key704, -2), (key707, -2), (key707, -2), (key716, 6), (key704, -2), (key707, -2), (key707, -2), (key858, 2), (key861, 2), (key858, 2), (key884, 2), (key861, 2), (key884, 2), (key893, -2), (key893, -2), (key915, -2), (key716, 6), (key893, -2), (key893, -2), (key915, -2)]

theorem rawRowCheck17683 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form4 = rawRow17683 := by decide +kernel

def row17683 : Integer.Sparse Key := [(key704, -4), (key707, -8), (key716, 12), (key858, 4), (key861, 4), (key884, 4), (key893, -8), (key915, -4)]

theorem rowCheck17683 : row17683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17683 := by decide +kernel

theorem rowEval17683 (x : Key → ℝ) : Integer.Sparse.eval row17683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17683, Integer.Sparse.eval_collectBalanced, rawRowCheck17683]

def rawRow17684 : Integer.Sparse Key := [(key707, -2), (key704, -2), (key707, -2), (key716, 6), (key707, -2), (key704, -2), (key707, -2), (key861, 2), (key858, 2), (key884, 2), (key858, 2), (key884, 2), (key861, 2), (key893, -2), (key915, -2), (key893, -2), (key716, 6), (key893, -2), (key915, -2), (key893, -2)]

theorem rawRowCheck17684 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form4 = rawRow17684 := by decide +kernel

def row17684 : Integer.Sparse Key := [(key704, -4), (key707, -8), (key716, 12), (key858, 4), (key861, 4), (key884, 4), (key893, -8), (key915, -4)]

theorem rowCheck17684 : row17684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17684 := by decide +kernel

theorem rowEval17684 (x : Key → ℝ) : Integer.Sparse.eval row17684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17684, Integer.Sparse.eval_collectBalanced, rawRowCheck17684]

def rawRow17685 : Integer.Sparse Key := [(key707, -2), (key707, -2), (key704, -2), (key716, 6), (key707, -2), (key707, -2), (key704, -2), (key884, 2), (key884, 2), (key861, 2), (key861, 2), (key858, 2), (key858, 2), (key915, -2), (key893, -2), (key893, -2), (key716, 6), (key915, -2), (key893, -2), (key893, -2)]

theorem rawRowCheck17685 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form4 = rawRow17685 := by decide +kernel

def row17685 : Integer.Sparse Key := [(key704, -4), (key707, -8), (key716, 12), (key858, 4), (key861, 4), (key884, 4), (key893, -8), (key915, -4)]

theorem rowCheck17685 : row17685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17685 := by decide +kernel

theorem rowEval17685 (x : Key → ℝ) : Integer.Sparse.eval row17685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17685, Integer.Sparse.eval_collectBalanced, rawRowCheck17685]

def rawRow17686 : Integer.Sparse Key := [(key704, -2), (key707, -2), (key716, -2), (key707, 6), (key858, -2), (key861, -2), (key893, -2), (key704, 2), (key707, 2), (key858, 2), (key884, 2), (key893, 2), (key915, 2), (key707, -2), (key861, -2), (key884, -2), (key893, 6), (key716, -2), (key893, -2), (key915, -2)]

theorem rawRowCheck17686 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form4 = rawRow17686 := by decide +kernel

def row17686 : Integer.Sparse Key := [(key707, 4), (key716, -4), (key861, -4), (key893, 4)]

theorem rowCheck17686 : row17686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17686 := by decide +kernel

theorem rowEval17686 (x : Key → ℝ) : Integer.Sparse.eval row17686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17686, Integer.Sparse.eval_collectBalanced, rawRowCheck17686]

def rawRow17687 : Integer.Sparse Key := [(key707, -2), (key704, -2), (key716, -2), (key707, 6), (key861, -2), (key858, -2), (key893, -2), (key707, 2), (key704, 2), (key884, 2), (key858, 2), (key915, 2), (key893, 2), (key707, -2), (key884, -2), (key861, -2), (key893, 6), (key716, -2), (key915, -2), (key893, -2)]

theorem rawRowCheck17687 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form4 = rawRow17687 := by decide +kernel

def row17687 : Integer.Sparse Key := [(key707, 4), (key716, -4), (key861, -4), (key893, 4)]

theorem rowCheck17687 : row17687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17687 := by decide +kernel

theorem rowEval17687 (x : Key → ℝ) : Integer.Sparse.eval row17687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17687, Integer.Sparse.eval_collectBalanced, rawRowCheck17687]

def rawRow17688 : Integer.Sparse Key := [(key704, -2), (key716, -2), (key707, -2), (key707, 6), (key858, -2), (key893, -2), (key861, -2), (key858, 2), (key893, 2), (key704, 2), (key915, 2), (key707, 2), (key884, 2), (key861, -2), (key707, -2), (key884, -2), (key893, 6), (key893, -2), (key716, -2), (key915, -2)]

theorem rawRowCheck17688 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form4 = rawRow17688 := by decide +kernel

def row17688 : Integer.Sparse Key := [(key707, 4), (key716, -4), (key861, -4), (key893, 4)]

theorem rowCheck17688 : row17688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17688 := by decide +kernel

theorem rowEval17688 (x : Key → ℝ) : Integer.Sparse.eval row17688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17688, Integer.Sparse.eval_collectBalanced, rawRowCheck17688]

def rawRow17689 : Integer.Sparse Key := [(key716, -2), (key704, -2), (key707, -2), (key707, 6), (key893, -2), (key858, -2), (key861, -2), (key893, 2), (key858, 2), (key915, 2), (key704, 2), (key884, 2), (key707, 2), (key861, -2), (key884, -2), (key707, -2), (key893, 6), (key893, -2), (key915, -2), (key716, -2)]

theorem rawRowCheck17689 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form4 = rawRow17689 := by decide +kernel

def row17689 : Integer.Sparse Key := [(key707, 4), (key716, -4), (key861, -4), (key893, 4)]

theorem rowCheck17689 : row17689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17689 := by decide +kernel

theorem rowEval17689 (x : Key → ℝ) : Integer.Sparse.eval row17689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17689, Integer.Sparse.eval_collectBalanced, rawRowCheck17689]

def rawRow17690 : Integer.Sparse Key := [(key707, -2), (key716, -2), (key704, -2), (key707, 6), (key861, -2), (key893, -2), (key858, -2), (key884, 2), (key915, 2), (key707, 2), (key893, 2), (key704, 2), (key858, 2), (key884, -2), (key707, -2), (key861, -2), (key893, 6), (key915, -2), (key716, -2), (key893, -2)]

theorem rawRowCheck17690 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form4 = rawRow17690 := by decide +kernel

def row17690 : Integer.Sparse Key := [(key707, 4), (key716, -4), (key861, -4), (key893, 4)]

theorem rowCheck17690 : row17690 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17690 := by decide +kernel

theorem rowEval17690 (x : Key → ℝ) : Integer.Sparse.eval row17690 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17690, Integer.Sparse.eval_collectBalanced, rawRowCheck17690]

def rawRow17691 : Integer.Sparse Key := [(key716, -2), (key707, -2), (key704, -2), (key707, 6), (key893, -2), (key861, -2), (key858, -2), (key915, 2), (key884, 2), (key893, 2), (key707, 2), (key858, 2), (key704, 2), (key884, -2), (key861, -2), (key707, -2), (key893, 6), (key915, -2), (key893, -2), (key716, -2)]

theorem rawRowCheck17691 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form4 = rawRow17691 := by decide +kernel

def row17691 : Integer.Sparse Key := [(key707, 4), (key716, -4), (key861, -4), (key893, 4)]

theorem rowCheck17691 : row17691 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17691 := by decide +kernel

theorem rowEval17691 (x : Key → ℝ) : Integer.Sparse.eval row17691 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17691, Integer.Sparse.eval_collectBalanced, rawRowCheck17691]

def rawRow17692 : Integer.Sparse Key := [(key858, -2), (key861, -2), (key893, -2), (key893, 6), (key704, -2), (key707, -2), (key716, -2), (key704, 2), (key707, 2), (key858, 2), (key884, 2), (key893, 2), (key915, 2), (key716, -2), (key893, -2), (key915, -2), (key707, 6), (key707, -2), (key861, -2), (key884, -2)]

theorem rawRowCheck17692 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form4 = rawRow17692 := by decide +kernel

def row17692 : Integer.Sparse Key := [(key707, 4), (key716, -4), (key861, -4), (key893, 4)]

theorem rowCheck17692 : row17692 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17692 := by decide +kernel

theorem rowEval17692 (x : Key → ℝ) : Integer.Sparse.eval row17692 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17692, Integer.Sparse.eval_collectBalanced, rawRowCheck17692]

def rawRow17693 : Integer.Sparse Key := [(key861, -2), (key858, -2), (key893, -2), (key893, 6), (key707, -2), (key704, -2), (key716, -2), (key707, 2), (key704, 2), (key884, 2), (key858, 2), (key915, 2), (key893, 2), (key716, -2), (key915, -2), (key893, -2), (key707, 6), (key707, -2), (key884, -2), (key861, -2)]

theorem rawRowCheck17693 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form4 = rawRow17693 := by decide +kernel

def row17693 : Integer.Sparse Key := [(key707, 4), (key716, -4), (key861, -4), (key893, 4)]

theorem rowCheck17693 : row17693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17693 := by decide +kernel

theorem rowEval17693 (x : Key → ℝ) : Integer.Sparse.eval row17693 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17693, Integer.Sparse.eval_collectBalanced, rawRowCheck17693]

def rawRow17694 : Integer.Sparse Key := [(key858, -2), (key893, -2), (key861, -2), (key893, 6), (key704, -2), (key716, -2), (key707, -2), (key858, 2), (key893, 2), (key704, 2), (key915, 2), (key707, 2), (key884, 2), (key893, -2), (key716, -2), (key915, -2), (key707, 6), (key861, -2), (key707, -2), (key884, -2)]

theorem rawRowCheck17694 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form4 = rawRow17694 := by decide +kernel

def row17694 : Integer.Sparse Key := [(key707, 4), (key716, -4), (key861, -4), (key893, 4)]

theorem rowCheck17694 : row17694 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17694 := by decide +kernel

theorem rowEval17694 (x : Key → ℝ) : Integer.Sparse.eval row17694 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17694, Integer.Sparse.eval_collectBalanced, rawRowCheck17694]

def rawRow17695 : Integer.Sparse Key := [(key893, -2), (key858, -2), (key861, -2), (key893, 6), (key716, -2), (key704, -2), (key707, -2), (key893, 2), (key858, 2), (key915, 2), (key704, 2), (key884, 2), (key707, 2), (key893, -2), (key915, -2), (key716, -2), (key707, 6), (key861, -2), (key884, -2), (key707, -2)]

theorem rawRowCheck17695 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form4 = rawRow17695 := by decide +kernel

def row17695 : Integer.Sparse Key := [(key707, 4), (key716, -4), (key861, -4), (key893, 4)]

theorem rowCheck17695 : row17695 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17695 := by decide +kernel

theorem rowEval17695 (x : Key → ℝ) : Integer.Sparse.eval row17695 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17695, Integer.Sparse.eval_collectBalanced, rawRowCheck17695]

def rawRow17696 : Integer.Sparse Key := [(key861, -2), (key893, -2), (key858, -2), (key893, 6), (key707, -2), (key716, -2), (key704, -2), (key884, 2), (key915, 2), (key707, 2), (key893, 2), (key704, 2), (key858, 2), (key915, -2), (key716, -2), (key893, -2), (key707, 6), (key884, -2), (key707, -2), (key861, -2)]

theorem rawRowCheck17696 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form4 = rawRow17696 := by decide +kernel

def row17696 : Integer.Sparse Key := [(key707, 4), (key716, -4), (key861, -4), (key893, 4)]

theorem rowCheck17696 : row17696 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17696 := by decide +kernel

theorem rowEval17696 (x : Key → ℝ) : Integer.Sparse.eval row17696 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17696, Integer.Sparse.eval_collectBalanced, rawRowCheck17696]

def rawRow17697 : Integer.Sparse Key := [(key893, -2), (key861, -2), (key858, -2), (key893, 6), (key716, -2), (key707, -2), (key704, -2), (key915, 2), (key884, 2), (key893, 2), (key707, 2), (key858, 2), (key704, 2), (key915, -2), (key893, -2), (key716, -2), (key707, 6), (key884, -2), (key861, -2), (key707, -2)]

theorem rawRowCheck17697 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form4 = rawRow17697 := by decide +kernel

def row17697 : Integer.Sparse Key := [(key707, 4), (key716, -4), (key861, -4), (key893, 4)]

theorem rowCheck17697 : row17697 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17697 := by decide +kernel

theorem rowEval17697 (x : Key → ℝ) : Integer.Sparse.eval row17697 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17697, Integer.Sparse.eval_collectBalanced, rawRowCheck17697]

def rawRow17698 : Integer.Sparse Key := [(key858, -2), (key893, -2), (key893, -2), (key861, 6), (key858, -2), (key893, -2), (key893, -2), (key704, 2), (key716, 2), (key704, 2), (key915, 2), (key716, 2), (key915, 2), (key707, -2), (key707, -2), (key884, -2), (key861, 6), (key707, -2), (key707, -2), (key884, -2)]

theorem rawRowCheck17698 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form4 = rawRow17698 := by decide +kernel

def row17698 : Integer.Sparse Key := [(key704, 4), (key707, -8), (key716, 4), (key858, -4), (key861, 12), (key884, -4), (key893, -8), (key915, 4)]

theorem rowCheck17698 : row17698 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17698 := by decide +kernel

theorem rowEval17698 (x : Key → ℝ) : Integer.Sparse.eval row17698 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17698, Integer.Sparse.eval_collectBalanced, rawRowCheck17698]

def rawRow17699 : Integer.Sparse Key := [(key893, -2), (key858, -2), (key893, -2), (key861, 6), (key893, -2), (key858, -2), (key893, -2), (key716, 2), (key704, 2), (key915, 2), (key704, 2), (key915, 2), (key716, 2), (key707, -2), (key884, -2), (key707, -2), (key861, 6), (key707, -2), (key884, -2), (key707, -2)]

theorem rawRowCheck17699 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form4 = rawRow17699 := by decide +kernel

def row17699 : Integer.Sparse Key := [(key704, 4), (key707, -8), (key716, 4), (key858, -4), (key861, 12), (key884, -4), (key893, -8), (key915, 4)]

theorem rowCheck17699 : row17699 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17699 := by decide +kernel

theorem rowEval17699 (x : Key → ℝ) : Integer.Sparse.eval row17699 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17699, Integer.Sparse.eval_collectBalanced, rawRowCheck17699]

def rawRow17700 : Integer.Sparse Key := [(key893, -2), (key893, -2), (key858, -2), (key861, 6), (key893, -2), (key893, -2), (key858, -2), (key915, 2), (key915, 2), (key716, 2), (key716, 2), (key704, 2), (key704, 2), (key884, -2), (key707, -2), (key707, -2), (key861, 6), (key884, -2), (key707, -2), (key707, -2)]

theorem rawRowCheck17700 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form4 = rawRow17700 := by decide +kernel

def row17700 : Integer.Sparse Key := [(key704, 4), (key707, -8), (key716, 4), (key858, -4), (key861, 12), (key884, -4), (key893, -8), (key915, 4)]

theorem rowCheck17700 : row17700 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17700 := by decide +kernel

theorem rowEval17700 (x : Key → ℝ) : Integer.Sparse.eval row17700 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17700, Integer.Sparse.eval_collectBalanced, rawRowCheck17700]

def rawRow17701 : Integer.Sparse Key := [(key862, 4), (key862, 4), (key887, 4), (key894, -2), (key896, -2), (key894, -2), (key917, -2), (key896, -2), (key917, -2), (key894, -2), (key896, -2), (key894, -2), (key917, -2), (key896, -2), (key917, -2), (key949, 4), (key949, 4), (key956, 4)]

theorem rawRowCheck17701 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form5 = rawRow17701 := by decide +kernel

def row17701 : Integer.Sparse Key := [(key862, 8), (key887, 4), (key894, -8), (key896, -8), (key917, -8), (key949, 8), (key956, 4)]

theorem rowCheck17701 : row17701 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17701 := by decide +kernel

theorem rowEval17701 (x : Key → ℝ) : Integer.Sparse.eval row17701 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17701, Integer.Sparse.eval_collectBalanced, rawRowCheck17701]

def rawRow17702 : Integer.Sparse Key := [(key862, 4), (key887, 4), (key862, 4), (key896, -2), (key894, -2), (key917, -2), (key894, -2), (key917, -2), (key896, -2), (key896, -2), (key894, -2), (key917, -2), (key894, -2), (key917, -2), (key896, -2), (key949, 4), (key956, 4), (key949, 4)]

theorem rawRowCheck17702 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form5 = rawRow17702 := by decide +kernel

def row17702 : Integer.Sparse Key := [(key862, 8), (key887, 4), (key894, -8), (key896, -8), (key917, -8), (key949, 8), (key956, 4)]

theorem rowCheck17702 : row17702 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17702 := by decide +kernel

theorem rowEval17702 (x : Key → ℝ) : Integer.Sparse.eval row17702 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17702, Integer.Sparse.eval_collectBalanced, rawRowCheck17702]

def rawRow17703 : Integer.Sparse Key := [(key887, 4), (key862, 4), (key862, 4), (key917, -2), (key917, -2), (key896, -2), (key896, -2), (key894, -2), (key894, -2), (key917, -2), (key917, -2), (key896, -2), (key896, -2), (key894, -2), (key894, -2), (key956, 4), (key949, 4), (key949, 4)]

theorem rawRowCheck17703 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form5 = rawRow17703 := by decide +kernel

def row17703 : Integer.Sparse Key := [(key862, 8), (key887, 4), (key894, -8), (key896, -8), (key917, -8), (key949, 8), (key956, 4)]

theorem rowCheck17703 : row17703 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17703 := by decide +kernel

theorem rowEval17703 (x : Key → ℝ) : Integer.Sparse.eval row17703 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17703, Integer.Sparse.eval_collectBalanced, rawRowCheck17703]

def rawRow17704 : Integer.Sparse Key := [(key708, 4), (key894, 4), (key917, 4), (key708, -2), (key711, -2), (key862, -2), (key887, -2), (key896, -2), (key917, -2), (key717, -2), (key719, -2), (key894, -2), (key917, -2), (key949, -2), (key956, -2), (key719, 4), (key896, 4), (key917, 4)]

theorem rawRowCheck17704 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form5 = rawRow17704 := by decide +kernel

def row17704 : Integer.Sparse Key := [(key708, 2), (key711, -2), (key717, -2), (key719, 2), (key862, -2), (key887, -2), (key894, 2), (key896, 2), (key917, 4), (key949, -2), (key956, -2)]

theorem rowCheck17704 : row17704 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17704 := by decide +kernel

theorem rowEval17704 (x : Key → ℝ) : Integer.Sparse.eval row17704 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17704, Integer.Sparse.eval_collectBalanced, rawRowCheck17704]

def rawRow17705 : Integer.Sparse Key := [(key708, 4), (key917, 4), (key894, 4), (key711, -2), (key708, -2), (key887, -2), (key862, -2), (key917, -2), (key896, -2), (key719, -2), (key717, -2), (key917, -2), (key894, -2), (key956, -2), (key949, -2), (key719, 4), (key917, 4), (key896, 4)]

theorem rawRowCheck17705 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form5 = rawRow17705 := by decide +kernel

def row17705 : Integer.Sparse Key := [(key708, 2), (key711, -2), (key717, -2), (key719, 2), (key862, -2), (key887, -2), (key894, 2), (key896, 2), (key917, 4), (key949, -2), (key956, -2)]

theorem rowCheck17705 : row17705 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17705 := by decide +kernel

theorem rowEval17705 (x : Key → ℝ) : Integer.Sparse.eval row17705 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17705, Integer.Sparse.eval_collectBalanced, rawRowCheck17705]

def rawRow17706 : Integer.Sparse Key := [(key894, 4), (key708, 4), (key917, 4), (key862, -2), (key896, -2), (key708, -2), (key917, -2), (key711, -2), (key887, -2), (key894, -2), (key949, -2), (key717, -2), (key956, -2), (key719, -2), (key917, -2), (key896, 4), (key719, 4), (key917, 4)]

theorem rawRowCheck17706 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form5 = rawRow17706 := by decide +kernel

def row17706 : Integer.Sparse Key := [(key708, 2), (key711, -2), (key717, -2), (key719, 2), (key862, -2), (key887, -2), (key894, 2), (key896, 2), (key917, 4), (key949, -2), (key956, -2)]

theorem rowCheck17706 : row17706 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17706 := by decide +kernel

theorem rowEval17706 (x : Key → ℝ) : Integer.Sparse.eval row17706 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17706, Integer.Sparse.eval_collectBalanced, rawRowCheck17706]

def rawRow17707 : Integer.Sparse Key := [(key894, 4), (key917, 4), (key708, 4), (key896, -2), (key862, -2), (key917, -2), (key708, -2), (key887, -2), (key711, -2), (key949, -2), (key894, -2), (key956, -2), (key717, -2), (key917, -2), (key719, -2), (key896, 4), (key917, 4), (key719, 4)]

theorem rawRowCheck17707 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form5 = rawRow17707 := by decide +kernel

def row17707 : Integer.Sparse Key := [(key708, 2), (key711, -2), (key717, -2), (key719, 2), (key862, -2), (key887, -2), (key894, 2), (key896, 2), (key917, 4), (key949, -2), (key956, -2)]

theorem rowCheck17707 : row17707 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17707 := by decide +kernel

theorem rowEval17707 (x : Key → ℝ) : Integer.Sparse.eval row17707 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17707, Integer.Sparse.eval_collectBalanced, rawRowCheck17707]

def rawRow17708 : Integer.Sparse Key := [(key917, 4), (key708, 4), (key894, 4), (key887, -2), (key917, -2), (key711, -2), (key896, -2), (key708, -2), (key862, -2), (key917, -2), (key956, -2), (key719, -2), (key949, -2), (key717, -2), (key894, -2), (key917, 4), (key719, 4), (key896, 4)]

theorem rawRowCheck17708 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form5 = rawRow17708 := by decide +kernel

def row17708 : Integer.Sparse Key := [(key708, 2), (key711, -2), (key717, -2), (key719, 2), (key862, -2), (key887, -2), (key894, 2), (key896, 2), (key917, 4), (key949, -2), (key956, -2)]

theorem rowCheck17708 : row17708 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17708 := by decide +kernel

theorem rowEval17708 (x : Key → ℝ) : Integer.Sparse.eval row17708 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17708, Integer.Sparse.eval_collectBalanced, rawRowCheck17708]

def rawRow17709 : Integer.Sparse Key := [(key917, 4), (key894, 4), (key708, 4), (key917, -2), (key887, -2), (key896, -2), (key711, -2), (key862, -2), (key708, -2), (key956, -2), (key917, -2), (key949, -2), (key719, -2), (key894, -2), (key717, -2), (key917, 4), (key896, 4), (key719, 4)]

theorem rawRowCheck17709 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form5 = rawRow17709 := by decide +kernel

def row17709 : Integer.Sparse Key := [(key708, 2), (key711, -2), (key717, -2), (key719, 2), (key862, -2), (key887, -2), (key894, 2), (key896, 2), (key917, 4), (key949, -2), (key956, -2)]

theorem rowCheck17709 : row17709 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17709 := by decide +kernel

theorem rowEval17709 (x : Key → ℝ) : Integer.Sparse.eval row17709 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17709, Integer.Sparse.eval_collectBalanced, rawRowCheck17709]

def rawRow17710 : Integer.Sparse Key := [(key708, 4), (key894, 4), (key917, 4), (key717, -2), (key719, -2), (key894, -2), (key917, -2), (key949, -2), (key956, -2), (key708, -2), (key711, -2), (key862, -2), (key887, -2), (key896, -2), (key917, -2), (key719, 4), (key896, 4), (key917, 4)]

theorem rawRowCheck17710 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form5 = rawRow17710 := by decide +kernel

def row17710 : Integer.Sparse Key := [(key708, 2), (key711, -2), (key717, -2), (key719, 2), (key862, -2), (key887, -2), (key894, 2), (key896, 2), (key917, 4), (key949, -2), (key956, -2)]

theorem rowCheck17710 : row17710 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17710 := by decide +kernel

theorem rowEval17710 (x : Key → ℝ) : Integer.Sparse.eval row17710 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17710, Integer.Sparse.eval_collectBalanced, rawRowCheck17710]

def rawRow17711 : Integer.Sparse Key := [(key708, 4), (key917, 4), (key894, 4), (key719, -2), (key717, -2), (key917, -2), (key894, -2), (key956, -2), (key949, -2), (key711, -2), (key708, -2), (key887, -2), (key862, -2), (key917, -2), (key896, -2), (key719, 4), (key917, 4), (key896, 4)]

theorem rawRowCheck17711 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form5 = rawRow17711 := by decide +kernel

def row17711 : Integer.Sparse Key := [(key708, 2), (key711, -2), (key717, -2), (key719, 2), (key862, -2), (key887, -2), (key894, 2), (key896, 2), (key917, 4), (key949, -2), (key956, -2)]

theorem rowCheck17711 : row17711 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17711 := by decide +kernel

theorem rowEval17711 (x : Key → ℝ) : Integer.Sparse.eval row17711 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17711, Integer.Sparse.eval_collectBalanced, rawRowCheck17711]

def rawRow17712 : Integer.Sparse Key := [(key894, 4), (key708, 4), (key917, 4), (key894, -2), (key949, -2), (key717, -2), (key956, -2), (key719, -2), (key917, -2), (key862, -2), (key896, -2), (key708, -2), (key917, -2), (key711, -2), (key887, -2), (key896, 4), (key719, 4), (key917, 4)]

theorem rawRowCheck17712 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form5 = rawRow17712 := by decide +kernel

def row17712 : Integer.Sparse Key := [(key708, 2), (key711, -2), (key717, -2), (key719, 2), (key862, -2), (key887, -2), (key894, 2), (key896, 2), (key917, 4), (key949, -2), (key956, -2)]

theorem rowCheck17712 : row17712 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17712 := by decide +kernel

theorem rowEval17712 (x : Key → ℝ) : Integer.Sparse.eval row17712 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17712, Integer.Sparse.eval_collectBalanced, rawRowCheck17712]

def rawRow17713 : Integer.Sparse Key := [(key894, 4), (key917, 4), (key708, 4), (key949, -2), (key894, -2), (key956, -2), (key717, -2), (key917, -2), (key719, -2), (key896, -2), (key862, -2), (key917, -2), (key708, -2), (key887, -2), (key711, -2), (key896, 4), (key917, 4), (key719, 4)]

theorem rawRowCheck17713 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form5 = rawRow17713 := by decide +kernel

def row17713 : Integer.Sparse Key := [(key708, 2), (key711, -2), (key717, -2), (key719, 2), (key862, -2), (key887, -2), (key894, 2), (key896, 2), (key917, 4), (key949, -2), (key956, -2)]

theorem rowCheck17713 : row17713 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17713 := by decide +kernel

theorem rowEval17713 (x : Key → ℝ) : Integer.Sparse.eval row17713 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17713, Integer.Sparse.eval_collectBalanced, rawRowCheck17713]

def rawRow17714 : Integer.Sparse Key := [(key917, 4), (key708, 4), (key894, 4), (key917, -2), (key956, -2), (key719, -2), (key949, -2), (key717, -2), (key894, -2), (key887, -2), (key917, -2), (key711, -2), (key896, -2), (key708, -2), (key862, -2), (key917, 4), (key719, 4), (key896, 4)]

theorem rawRowCheck17714 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form5 = rawRow17714 := by decide +kernel

def row17714 : Integer.Sparse Key := [(key708, 2), (key711, -2), (key717, -2), (key719, 2), (key862, -2), (key887, -2), (key894, 2), (key896, 2), (key917, 4), (key949, -2), (key956, -2)]

theorem rowCheck17714 : row17714 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17714 := by decide +kernel

theorem rowEval17714 (x : Key → ℝ) : Integer.Sparse.eval row17714 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17714, Integer.Sparse.eval_collectBalanced, rawRowCheck17714]

def rawRow17715 : Integer.Sparse Key := [(key917, 4), (key894, 4), (key708, 4), (key956, -2), (key917, -2), (key949, -2), (key719, -2), (key894, -2), (key717, -2), (key917, -2), (key887, -2), (key896, -2), (key711, -2), (key862, -2), (key708, -2), (key917, 4), (key896, 4), (key719, 4)]

theorem rawRowCheck17715 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form5 = rawRow17715 := by decide +kernel

def row17715 : Integer.Sparse Key := [(key708, 2), (key711, -2), (key717, -2), (key719, 2), (key862, -2), (key887, -2), (key894, 2), (key896, 2), (key917, 4), (key949, -2), (key956, -2)]

theorem rowCheck17715 : row17715 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17715 := by decide +kernel

theorem rowEval17715 (x : Key → ℝ) : Integer.Sparse.eval row17715 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17715, Integer.Sparse.eval_collectBalanced, rawRowCheck17715]

def rawRow17716 : Integer.Sparse Key := [(key78, 4), (key717, 4), (key956, 4), (key708, -2), (key719, -2), (key708, -2), (key917, -2), (key719, -2), (key917, -2), (key708, -2), (key719, -2), (key708, -2), (key917, -2), (key719, -2), (key917, -2), (key711, 4), (key711, 4), (key887, 4)]

theorem rawRowCheck17716 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form5 = rawRow17716 := by decide +kernel

def row17716 : Integer.Sparse Key := [(key78, 4), (key708, -8), (key711, 8), (key717, 4), (key719, -8), (key887, 4), (key917, -8), (key956, 4)]

theorem rowCheck17716 : row17716 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17716 := by decide +kernel

theorem rowEval17716 (x : Key → ℝ) : Integer.Sparse.eval row17716 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17716, Integer.Sparse.eval_collectBalanced, rawRowCheck17716]

def rawRow17717 : Integer.Sparse Key := [(key78, 4), (key956, 4), (key717, 4), (key719, -2), (key708, -2), (key917, -2), (key708, -2), (key917, -2), (key719, -2), (key719, -2), (key708, -2), (key917, -2), (key708, -2), (key917, -2), (key719, -2), (key711, 4), (key887, 4), (key711, 4)]

theorem rawRowCheck17717 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form5 = rawRow17717 := by decide +kernel

def row17717 : Integer.Sparse Key := [(key78, 4), (key708, -8), (key711, 8), (key717, 4), (key719, -8), (key887, 4), (key917, -8), (key956, 4)]

theorem rowCheck17717 : row17717 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17717 := by decide +kernel

theorem rowEval17717 (x : Key → ℝ) : Integer.Sparse.eval row17717 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17717, Integer.Sparse.eval_collectBalanced, rawRowCheck17717]

def rawRow17718 : Integer.Sparse Key := [(key191, 4), (key78, 4), (key717, 4), (key917, -2), (key917, -2), (key719, -2), (key719, -2), (key708, -2), (key708, -2), (key917, -2), (key917, -2), (key719, -2), (key719, -2), (key708, -2), (key708, -2), (key887, 4), (key711, 4), (key711, 4)]

theorem rawRowCheck17718 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form5 = rawRow17718 := by decide +kernel

def row17718 : Integer.Sparse Key := [(key78, 4), (key191, 4), (key708, -8), (key711, 8), (key717, 4), (key719, -8), (key887, 4), (key917, -8)]

theorem rowCheck17718 : row17718 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17718 := by decide +kernel

theorem rowEval17718 (x : Key → ℝ) : Integer.Sparse.eval row17718 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17718, Integer.Sparse.eval_collectBalanced, rawRowCheck17718]

def rawRow17719 : Integer.Sparse Key := [(key2150, -1), (key2155, -1), (key2150, -1), (key2168, -1), (key2155, -1), (key2168, -1), (key2195, 2), (key2195, 2), (key2201, 2), (key2150, -1), (key2155, -1), (key2150, -1), (key2168, -1), (key2155, -1), (key2168, -1), (key2243, 2), (key2248, 2), (key2243, 2), (key2255, 2), (key2248, 2), (key2255, 2), (key2304, -1), (key2306, -1), (key2304, -1), (key2311, -1), (key2306, -1), (key2311, -1), (key2195, 2), (key2195, 2), (key2201, 2), (key2304, -1), (key2306, -1), (key2304, -1), (key2311, -1), (key2306, -1), (key2311, -1)]

theorem rawRowCheck17719 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form6 = rawRow17719 := by decide +kernel

def row17719 : Integer.Sparse Key := [(key2150, -4), (key2155, -4), (key2168, -4), (key2195, 8), (key2201, 4), (key2243, 4), (key2248, 4), (key2255, 4), (key2304, -4), (key2306, -4), (key2311, -4)]

theorem rowCheck17719 : row17719 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17719 := by decide +kernel

theorem rowEval17719 (x : Key → ℝ) : Integer.Sparse.eval row17719 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17719, Integer.Sparse.eval_collectBalanced, rawRowCheck17719]

def rawRow17720 : Integer.Sparse Key := [(key2155, -1), (key2150, -1), (key2168, -1), (key2150, -1), (key2168, -1), (key2155, -1), (key2195, 2), (key2201, 2), (key2195, 2), (key2155, -1), (key2150, -1), (key2168, -1), (key2150, -1), (key2168, -1), (key2155, -1), (key2248, 2), (key2243, 2), (key2255, 2), (key2243, 2), (key2255, 2), (key2248, 2), (key2306, -1), (key2304, -1), (key2311, -1), (key2304, -1), (key2311, -1), (key2306, -1), (key2195, 2), (key2201, 2), (key2195, 2), (key2306, -1), (key2304, -1), (key2311, -1), (key2304, -1), (key2311, -1), (key2306, -1)]

theorem rawRowCheck17720 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form6 = rawRow17720 := by decide +kernel

def row17720 : Integer.Sparse Key := [(key2150, -4), (key2155, -4), (key2168, -4), (key2195, 8), (key2201, 4), (key2243, 4), (key2248, 4), (key2255, 4), (key2304, -4), (key2306, -4), (key2311, -4)]

theorem rowCheck17720 : row17720 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17720 := by decide +kernel

theorem rowEval17720 (x : Key → ℝ) : Integer.Sparse.eval row17720 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck17720, Integer.Sparse.eval_collectBalanced, rawRowCheck17720]

def rawRow17721 : Integer.Sparse Key := [(key2168, -1), (key2168, -1), (key2155, -1), (key2155, -1), (key2150, -1), (key2150, -1), (key2201, 2), (key2195, 2), (key2195, 2), (key2168, -1), (key2168, -1), (key2155, -1), (key2155, -1), (key2150, -1), (key2150, -1), (key2255, 2), (key2255, 2), (key2248, 2), (key2248, 2), (key2243, 2), (key2243, 2), (key2311, -1), (key2311, -1), (key2306, -1), (key2306, -1), (key2304, -1), (key2304, -1), (key2201, 2), (key2195, 2), (key2195, 2), (key2311, -1), (key2311, -1), (key2306, -1), (key2306, -1), (key2304, -1), (key2304, -1)]

theorem rawRowCheck17721 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form6 = rawRow17721 := by decide +kernel

def row17721 : Integer.Sparse Key := [(key2150, -4), (key2155, -4), (key2168, -4), (key2195, 8), (key2201, 4), (key2243, 4), (key2248, 4), (key2255, 4), (key2304, -4), (key2306, -4), (key2311, -4)]

theorem rowCheck17721 : row17721 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17721 := by decide +kernel

theorem rowEval17721 (x : Key → ℝ) : Integer.Sparse.eval row17721 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck17721, Integer.Sparse.eval_collectBalanced, rawRowCheck17721]

def rawRow17722 : Integer.Sparse Key := [(key2031, -1), (key2036, -1), (key2150, -1), (key2168, -1), (key2195, -1), (key2201, -1), (key2036, 2), (key2155, 2), (key2168, 2), (key2061, -1), (key2066, -1), (key2243, -1), (key2255, -1), (key2304, -1), (key2311, -1), (key2061, 2), (key2071, 2), (key2150, 2), (key2168, 2), (key2306, 2), (key2311, 2), (key2066, -1), (key2071, -1), (key2155, -1), (key2168, -1), (key2248, -1), (key2255, -1), (key2093, 2), (key2304, 2), (key2311, 2), (key2093, -1), (key2096, -1), (key2195, -1), (key2201, -1), (key2306, -1), (key2311, -1)]

theorem rawRowCheck17722 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form6 = rawRow17722 := by decide +kernel

def row17722 : Integer.Sparse Key := [(key2031, -1), (key2036, 1), (key2061, 1), (key2066, -2), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 1), (key2155, 1), (key2168, 2), (key2195, -2), (key2201, -2), (key2243, -1), (key2248, -1), (key2255, -2), (key2304, 1), (key2306, 1), (key2311, 2)]

theorem rowCheck17722 : row17722 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17722 := by decide +kernel

theorem rowEval17722 (x : Key → ℝ) : Integer.Sparse.eval row17722 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17722, Integer.Sparse.eval_collectBalanced, rawRowCheck17722]

def rawRow17723 : Integer.Sparse Key := [(key2036, -1), (key2031, -1), (key2168, -1), (key2150, -1), (key2201, -1), (key2195, -1), (key2036, 2), (key2168, 2), (key2155, 2), (key2066, -1), (key2061, -1), (key2255, -1), (key2243, -1), (key2311, -1), (key2304, -1), (key2071, 2), (key2061, 2), (key2168, 2), (key2150, 2), (key2311, 2), (key2306, 2), (key2071, -1), (key2066, -1), (key2168, -1), (key2155, -1), (key2255, -1), (key2248, -1), (key2093, 2), (key2311, 2), (key2304, 2), (key2096, -1), (key2093, -1), (key2201, -1), (key2195, -1), (key2311, -1), (key2306, -1)]

theorem rawRowCheck17723 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form6 = rawRow17723 := by decide +kernel

def row17723 : Integer.Sparse Key := [(key2031, -1), (key2036, 1), (key2061, 1), (key2066, -2), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 1), (key2155, 1), (key2168, 2), (key2195, -2), (key2201, -2), (key2243, -1), (key2248, -1), (key2255, -2), (key2304, 1), (key2306, 1), (key2311, 2)]

theorem rowCheck17723 : row17723 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17723 := by decide +kernel

theorem rowEval17723 (x : Key → ℝ) : Integer.Sparse.eval row17723 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck17723, Integer.Sparse.eval_collectBalanced, rawRowCheck17723]

def rawRow17724 : Integer.Sparse Key := [(key2150, -1), (key2195, -1), (key2031, -1), (key2201, -1), (key2036, -1), (key2168, -1), (key2155, 2), (key2036, 2), (key2168, 2), (key2243, -1), (key2304, -1), (key2061, -1), (key2311, -1), (key2066, -1), (key2255, -1), (key2150, 2), (key2306, 2), (key2061, 2), (key2311, 2), (key2071, 2), (key2168, 2), (key2155, -1), (key2248, -1), (key2066, -1), (key2255, -1), (key2071, -1), (key2168, -1), (key2304, 2), (key2093, 2), (key2311, 2), (key2195, -1), (key2306, -1), (key2093, -1), (key2311, -1), (key2096, -1), (key2201, -1)]

theorem rawRowCheck17724 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form6 = rawRow17724 := by decide +kernel

def row17724 : Integer.Sparse Key := [(key2031, -1), (key2036, 1), (key2061, 1), (key2066, -2), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 1), (key2155, 1), (key2168, 2), (key2195, -2), (key2201, -2), (key2243, -1), (key2248, -1), (key2255, -2), (key2304, 1), (key2306, 1), (key2311, 2)]

theorem rowCheck17724 : row17724 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17724 := by decide +kernel

theorem rowEval17724 (x : Key → ℝ) : Integer.Sparse.eval row17724 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17724, Integer.Sparse.eval_collectBalanced, rawRowCheck17724]

def rawRow17725 : Integer.Sparse Key := [(key2195, -1), (key2150, -1), (key2201, -1), (key2031, -1), (key2168, -1), (key2036, -1), (key2155, 2), (key2168, 2), (key2036, 2), (key2304, -1), (key2243, -1), (key2311, -1), (key2061, -1), (key2255, -1), (key2066, -1), (key2306, 2), (key2150, 2), (key2311, 2), (key2061, 2), (key2168, 2), (key2071, 2), (key2248, -1), (key2155, -1), (key2255, -1), (key2066, -1), (key2168, -1), (key2071, -1), (key2304, 2), (key2311, 2), (key2093, 2), (key2306, -1), (key2195, -1), (key2311, -1), (key2093, -1), (key2201, -1), (key2096, -1)]

theorem rawRowCheck17725 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form6 = rawRow17725 := by decide +kernel

def row17725 : Integer.Sparse Key := [(key2031, -1), (key2036, 1), (key2061, 1), (key2066, -2), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 1), (key2155, 1), (key2168, 2), (key2195, -2), (key2201, -2), (key2243, -1), (key2248, -1), (key2255, -2), (key2304, 1), (key2306, 1), (key2311, 2)]

theorem rowCheck17725 : row17725 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17725 := by decide +kernel

theorem rowEval17725 (x : Key → ℝ) : Integer.Sparse.eval row17725 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17725, Integer.Sparse.eval_collectBalanced, rawRowCheck17725]

def rawRow17726 : Integer.Sparse Key := [(key2168, -1), (key2201, -1), (key2036, -1), (key2195, -1), (key2031, -1), (key2150, -1), (key2168, 2), (key2036, 2), (key2155, 2), (key2255, -1), (key2311, -1), (key2066, -1), (key2304, -1), (key2061, -1), (key2243, -1), (key2168, 2), (key2311, 2), (key2071, 2), (key2306, 2), (key2061, 2), (key2150, 2), (key2168, -1), (key2255, -1), (key2071, -1), (key2248, -1), (key2066, -1), (key2155, -1), (key2311, 2), (key2093, 2), (key2304, 2), (key2201, -1), (key2311, -1), (key2096, -1), (key2306, -1), (key2093, -1), (key2195, -1)]

theorem rawRowCheck17726 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form6 = rawRow17726 := by decide +kernel

def row17726 : Integer.Sparse Key := [(key2031, -1), (key2036, 1), (key2061, 1), (key2066, -2), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 1), (key2155, 1), (key2168, 2), (key2195, -2), (key2201, -2), (key2243, -1), (key2248, -1), (key2255, -2), (key2304, 1), (key2306, 1), (key2311, 2)]

theorem rowCheck17726 : row17726 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17726 := by decide +kernel

theorem rowEval17726 (x : Key → ℝ) : Integer.Sparse.eval row17726 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck17726, Integer.Sparse.eval_collectBalanced, rawRowCheck17726]

def rawRow17727 : Integer.Sparse Key := [(key2201, -1), (key2168, -1), (key2195, -1), (key2036, -1), (key2150, -1), (key2031, -1), (key2168, 2), (key2155, 2), (key2036, 2), (key2311, -1), (key2255, -1), (key2304, -1), (key2066, -1), (key2243, -1), (key2061, -1), (key2311, 2), (key2168, 2), (key2306, 2), (key2071, 2), (key2150, 2), (key2061, 2), (key2255, -1), (key2168, -1), (key2248, -1), (key2071, -1), (key2155, -1), (key2066, -1), (key2311, 2), (key2304, 2), (key2093, 2), (key2311, -1), (key2201, -1), (key2306, -1), (key2096, -1), (key2195, -1), (key2093, -1)]

theorem rawRowCheck17727 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form6 = rawRow17727 := by decide +kernel

def row17727 : Integer.Sparse Key := [(key2031, -1), (key2036, 1), (key2061, 1), (key2066, -2), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 1), (key2155, 1), (key2168, 2), (key2195, -2), (key2201, -2), (key2243, -1), (key2248, -1), (key2255, -2), (key2304, 1), (key2306, 1), (key2311, 2)]

theorem rowCheck17727 : row17727 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17727 := by decide +kernel

theorem rowEval17727 (x : Key → ℝ) : Integer.Sparse.eval row17727 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17727, Integer.Sparse.eval_collectBalanced, rawRowCheck17727]

def rawRow17728 : Integer.Sparse Key := [(key2061, -1), (key2066, -1), (key2243, -1), (key2255, -1), (key2304, -1), (key2311, -1), (key2093, 2), (key2304, 2), (key2311, 2), (key2031, -1), (key2036, -1), (key2150, -1), (key2168, -1), (key2195, -1), (key2201, -1), (key2061, 2), (key2071, 2), (key2150, 2), (key2168, 2), (key2306, 2), (key2311, 2), (key2093, -1), (key2096, -1), (key2195, -1), (key2201, -1), (key2306, -1), (key2311, -1), (key2036, 2), (key2155, 2), (key2168, 2), (key2066, -1), (key2071, -1), (key2155, -1), (key2168, -1), (key2248, -1), (key2255, -1)]

theorem rawRowCheck17728 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form6 = rawRow17728 := by decide +kernel

def row17728 : Integer.Sparse Key := [(key2031, -1), (key2036, 1), (key2061, 1), (key2066, -2), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 1), (key2155, 1), (key2168, 2), (key2195, -2), (key2201, -2), (key2243, -1), (key2248, -1), (key2255, -2), (key2304, 1), (key2306, 1), (key2311, 2)]

theorem rowCheck17728 : row17728 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17728 := by decide +kernel

theorem rowEval17728 (x : Key → ℝ) : Integer.Sparse.eval row17728 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17728, Integer.Sparse.eval_collectBalanced, rawRowCheck17728]

def rawRow17729 : Integer.Sparse Key := [(key2066, -1), (key2061, -1), (key2255, -1), (key2243, -1), (key2311, -1), (key2304, -1), (key2093, 2), (key2311, 2), (key2304, 2), (key2036, -1), (key2031, -1), (key2168, -1), (key2150, -1), (key2201, -1), (key2195, -1), (key2071, 2), (key2061, 2), (key2168, 2), (key2150, 2), (key2311, 2), (key2306, 2), (key2096, -1), (key2093, -1), (key2201, -1), (key2195, -1), (key2311, -1), (key2306, -1), (key2036, 2), (key2168, 2), (key2155, 2), (key2071, -1), (key2066, -1), (key2168, -1), (key2155, -1), (key2255, -1), (key2248, -1)]

theorem rawRowCheck17729 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form6 = rawRow17729 := by decide +kernel

def row17729 : Integer.Sparse Key := [(key2031, -1), (key2036, 1), (key2061, 1), (key2066, -2), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 1), (key2155, 1), (key2168, 2), (key2195, -2), (key2201, -2), (key2243, -1), (key2248, -1), (key2255, -2), (key2304, 1), (key2306, 1), (key2311, 2)]

theorem rowCheck17729 : row17729 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17729 := by decide +kernel

theorem rowEval17729 (x : Key → ℝ) : Integer.Sparse.eval row17729 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck17729, Integer.Sparse.eval_collectBalanced, rawRowCheck17729]

def rawRow17730 : Integer.Sparse Key := [(key2243, -1), (key2304, -1), (key2061, -1), (key2311, -1), (key2066, -1), (key2255, -1), (key2304, 2), (key2093, 2), (key2311, 2), (key2150, -1), (key2195, -1), (key2031, -1), (key2201, -1), (key2036, -1), (key2168, -1), (key2150, 2), (key2306, 2), (key2061, 2), (key2311, 2), (key2071, 2), (key2168, 2), (key2195, -1), (key2306, -1), (key2093, -1), (key2311, -1), (key2096, -1), (key2201, -1), (key2155, 2), (key2036, 2), (key2168, 2), (key2155, -1), (key2248, -1), (key2066, -1), (key2255, -1), (key2071, -1), (key2168, -1)]

theorem rawRowCheck17730 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form6 = rawRow17730 := by decide +kernel

def row17730 : Integer.Sparse Key := [(key2031, -1), (key2036, 1), (key2061, 1), (key2066, -2), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 1), (key2155, 1), (key2168, 2), (key2195, -2), (key2201, -2), (key2243, -1), (key2248, -1), (key2255, -2), (key2304, 1), (key2306, 1), (key2311, 2)]

theorem rowCheck17730 : row17730 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17730 := by decide +kernel

theorem rowEval17730 (x : Key → ℝ) : Integer.Sparse.eval row17730 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17730, Integer.Sparse.eval_collectBalanced, rawRowCheck17730]

def rawRow17731 : Integer.Sparse Key := [(key2304, -1), (key2243, -1), (key2311, -1), (key2061, -1), (key2255, -1), (key2066, -1), (key2304, 2), (key2311, 2), (key2093, 2), (key2195, -1), (key2150, -1), (key2201, -1), (key2031, -1), (key2168, -1), (key2036, -1), (key2306, 2), (key2150, 2), (key2311, 2), (key2061, 2), (key2168, 2), (key2071, 2), (key2306, -1), (key2195, -1), (key2311, -1), (key2093, -1), (key2201, -1), (key2096, -1), (key2155, 2), (key2168, 2), (key2036, 2), (key2248, -1), (key2155, -1), (key2255, -1), (key2066, -1), (key2168, -1), (key2071, -1)]

theorem rawRowCheck17731 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form6 = rawRow17731 := by decide +kernel

def row17731 : Integer.Sparse Key := [(key2031, -1), (key2036, 1), (key2061, 1), (key2066, -2), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 1), (key2155, 1), (key2168, 2), (key2195, -2), (key2201, -2), (key2243, -1), (key2248, -1), (key2255, -2), (key2304, 1), (key2306, 1), (key2311, 2)]

theorem rowCheck17731 : row17731 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17731 := by decide +kernel

theorem rowEval17731 (x : Key → ℝ) : Integer.Sparse.eval row17731 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17731, Integer.Sparse.eval_collectBalanced, rawRowCheck17731]

def rawRow17732 : Integer.Sparse Key := [(key2255, -1), (key2311, -1), (key2066, -1), (key2304, -1), (key2061, -1), (key2243, -1), (key2311, 2), (key2093, 2), (key2304, 2), (key2168, -1), (key2201, -1), (key2036, -1), (key2195, -1), (key2031, -1), (key2150, -1), (key2168, 2), (key2311, 2), (key2071, 2), (key2306, 2), (key2061, 2), (key2150, 2), (key2201, -1), (key2311, -1), (key2096, -1), (key2306, -1), (key2093, -1), (key2195, -1), (key2168, 2), (key2036, 2), (key2155, 2), (key2168, -1), (key2255, -1), (key2071, -1), (key2248, -1), (key2066, -1), (key2155, -1)]

theorem rawRowCheck17732 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form6 = rawRow17732 := by decide +kernel

def row17732 : Integer.Sparse Key := [(key2031, -1), (key2036, 1), (key2061, 1), (key2066, -2), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 1), (key2155, 1), (key2168, 2), (key2195, -2), (key2201, -2), (key2243, -1), (key2248, -1), (key2255, -2), (key2304, 1), (key2306, 1), (key2311, 2)]

theorem rowCheck17732 : row17732 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17732 := by decide +kernel

theorem rowEval17732 (x : Key → ℝ) : Integer.Sparse.eval row17732 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck17732, Integer.Sparse.eval_collectBalanced, rawRowCheck17732]

def rawRow17733 : Integer.Sparse Key := [(key2311, -1), (key2255, -1), (key2304, -1), (key2066, -1), (key2243, -1), (key2061, -1), (key2311, 2), (key2304, 2), (key2093, 2), (key2201, -1), (key2168, -1), (key2195, -1), (key2036, -1), (key2150, -1), (key2031, -1), (key2311, 2), (key2168, 2), (key2306, 2), (key2071, 2), (key2150, 2), (key2061, 2), (key2311, -1), (key2201, -1), (key2306, -1), (key2096, -1), (key2195, -1), (key2093, -1), (key2168, 2), (key2155, 2), (key2036, 2), (key2255, -1), (key2168, -1), (key2248, -1), (key2071, -1), (key2155, -1), (key2066, -1)]

theorem rawRowCheck17733 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form6 = rawRow17733 := by decide +kernel

def row17733 : Integer.Sparse Key := [(key2031, -1), (key2036, 1), (key2061, 1), (key2066, -2), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, 1), (key2155, 1), (key2168, 2), (key2195, -2), (key2201, -2), (key2243, -1), (key2248, -1), (key2255, -2), (key2304, 1), (key2306, 1), (key2311, 2)]

theorem rowCheck17733 : row17733 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17733 := by decide +kernel

theorem rowEval17733 (x : Key → ℝ) : Integer.Sparse.eval row17733 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17733, Integer.Sparse.eval_collectBalanced, rawRowCheck17733]

def rawRow17734 : Integer.Sparse Key := [(key2061, -1), (key2093, -1), (key2061, -1), (key2311, -1), (key2093, -1), (key2311, -1), (key2066, 2), (key2066, 2), (key2255, 2), (key2061, -1), (key2093, -1), (key2061, -1), (key2311, -1), (key2093, -1), (key2311, -1), (key2031, 2), (key2096, 2), (key2031, 2), (key2201, 2), (key2096, 2), (key2201, 2), (key2036, -1), (key2071, -1), (key2036, -1), (key2168, -1), (key2071, -1), (key2168, -1), (key2066, 2), (key2066, 2), (key2255, 2), (key2036, -1), (key2071, -1), (key2036, -1), (key2168, -1), (key2071, -1), (key2168, -1)]

theorem rawRowCheck17734 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form6 = rawRow17734 := by decide +kernel

def row17734 : Integer.Sparse Key := [(key2031, 4), (key2036, -4), (key2061, -4), (key2066, 8), (key2071, -4), (key2093, -4), (key2096, 4), (key2168, -4), (key2201, 4), (key2255, 4), (key2311, -4)]

theorem rowCheck17734 : row17734 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17734 := by decide +kernel

theorem rowEval17734 (x : Key → ℝ) : Integer.Sparse.eval row17734 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17734, Integer.Sparse.eval_collectBalanced, rawRowCheck17734]

def rawRow17735 : Integer.Sparse Key := [(key2093, -1), (key2061, -1), (key2311, -1), (key2061, -1), (key2311, -1), (key2093, -1), (key2066, 2), (key2255, 2), (key2066, 2), (key2093, -1), (key2061, -1), (key2311, -1), (key2061, -1), (key2311, -1), (key2093, -1), (key2096, 2), (key2031, 2), (key2201, 2), (key2031, 2), (key2201, 2), (key2096, 2), (key2071, -1), (key2036, -1), (key2168, -1), (key2036, -1), (key2168, -1), (key2071, -1), (key2066, 2), (key2255, 2), (key2066, 2), (key2071, -1), (key2036, -1), (key2168, -1), (key2036, -1), (key2168, -1), (key2071, -1)]

theorem rawRowCheck17735 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form6 = rawRow17735 := by decide +kernel

def row17735 : Integer.Sparse Key := [(key2031, 4), (key2036, -4), (key2061, -4), (key2066, 8), (key2071, -4), (key2093, -4), (key2096, 4), (key2168, -4), (key2201, 4), (key2255, 4), (key2311, -4)]

theorem rowCheck17735 : row17735 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17735 := by decide +kernel

theorem rowEval17735 (x : Key → ℝ) : Integer.Sparse.eval row17735 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17735, Integer.Sparse.eval_collectBalanced, rawRowCheck17735]

def rawRow17736 : Integer.Sparse Key := [(key2311, -1), (key2311, -1), (key2093, -1), (key2093, -1), (key2061, -1), (key2061, -1), (key2255, 2), (key2066, 2), (key2066, 2), (key2311, -1), (key2311, -1), (key2093, -1), (key2093, -1), (key2061, -1), (key2061, -1), (key2201, 2), (key2201, 2), (key2096, 2), (key2096, 2), (key2031, 2), (key2031, 2), (key2168, -1), (key2168, -1), (key2071, -1), (key2071, -1), (key2036, -1), (key2036, -1), (key2255, 2), (key2066, 2), (key2066, 2), (key2168, -1), (key2168, -1), (key2071, -1), (key2071, -1), (key2036, -1), (key2036, -1)]

theorem rawRowCheck17736 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form6 = rawRow17736 := by decide +kernel

def row17736 : Integer.Sparse Key := [(key2031, 4), (key2036, -4), (key2061, -4), (key2066, 8), (key2071, -4), (key2093, -4), (key2096, 4), (key2168, -4), (key2201, 4), (key2255, 4), (key2311, -4)]

theorem rowCheck17736 : row17736 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17736 := by decide +kernel

theorem rowEval17736 (x : Key → ℝ) : Integer.Sparse.eval row17736 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17736, Integer.Sparse.eval_collectBalanced, rawRowCheck17736]

def rawRow17737 : Integer.Sparse Key := [(key2116, 4), (key2116, 4), (key2121, 4), (key2158, -4), (key2161, -4), (key2161, -4), (key2158, -4), (key2161, -4), (key2161, -4), (key2250, 12)]

theorem rawRowCheck17737 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form7 = rawRow17737 := by decide +kernel

def row17737 : Integer.Sparse Key := [(key2116, 8), (key2121, 4), (key2158, -8), (key2161, -16), (key2250, 12)]

theorem rowCheck17737 : row17737 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17737 := by decide +kernel

theorem rowEval17737 (x : Key → ℝ) : Integer.Sparse.eval row17737 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17737, Integer.Sparse.eval_collectBalanced, rawRowCheck17737]

def rawRow17738 : Integer.Sparse Key := [(key2116, 4), (key2121, 4), (key2116, 4), (key2161, -4), (key2158, -4), (key2161, -4), (key2161, -4), (key2158, -4), (key2161, -4), (key2250, 12)]

theorem rawRowCheck17738 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form7 = rawRow17738 := by decide +kernel

def row17738 : Integer.Sparse Key := [(key2116, 8), (key2121, 4), (key2158, -8), (key2161, -16), (key2250, 12)]

theorem rowCheck17738 : row17738 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17738 := by decide +kernel

theorem rowEval17738 (x : Key → ℝ) : Integer.Sparse.eval row17738 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17738, Integer.Sparse.eval_collectBalanced, rawRowCheck17738]

def rawRow17739 : Integer.Sparse Key := [(key2121, 4), (key2116, 4), (key2116, 4), (key2161, -4), (key2161, -4), (key2158, -4), (key2161, -4), (key2161, -4), (key2158, -4), (key2250, 12)]

theorem rawRowCheck17739 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form7 = rawRow17739 := by decide +kernel

def row17739 : Integer.Sparse Key := [(key2116, 8), (key2121, 4), (key2158, -8), (key2161, -16), (key2250, 12)]

theorem rowCheck17739 : row17739 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17739 := by decide +kernel

theorem rowEval17739 (x : Key → ℝ) : Integer.Sparse.eval row17739 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17739, Integer.Sparse.eval_collectBalanced, rawRowCheck17739]

def rawRow17740 : Integer.Sparse Key := [(key2116, 4), (key2158, 4), (key2161, 4), (key2116, -4), (key2121, -4), (key2161, -4), (key2158, -4), (key2161, -4), (key2250, -4), (key2161, 12)]

theorem rawRowCheck17740 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form7 = rawRow17740 := by decide +kernel

def row17740 : Integer.Sparse Key := [(key2121, -4), (key2161, 8), (key2250, -4)]

theorem rowCheck17740 : row17740 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17740 := by decide +kernel

theorem rowEval17740 (x : Key → ℝ) : Integer.Sparse.eval row17740 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17740, Integer.Sparse.eval_collectBalanced, rawRowCheck17740]

def rawRow17741 : Integer.Sparse Key := [(key2116, 4), (key2161, 4), (key2158, 4), (key2121, -4), (key2116, -4), (key2161, -4), (key2161, -4), (key2158, -4), (key2250, -4), (key2161, 12)]

theorem rawRowCheck17741 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form7 = rawRow17741 := by decide +kernel

def row17741 : Integer.Sparse Key := [(key2121, -4), (key2161, 8), (key2250, -4)]

theorem rowCheck17741 : row17741 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17741 := by decide +kernel

theorem rowEval17741 (x : Key → ℝ) : Integer.Sparse.eval row17741 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17741, Integer.Sparse.eval_collectBalanced, rawRowCheck17741]

def rawRow17742 : Integer.Sparse Key := [(key2158, 4), (key2116, 4), (key2161, 4), (key2116, -4), (key2161, -4), (key2121, -4), (key2158, -4), (key2250, -4), (key2161, -4), (key2161, 12)]

theorem rawRowCheck17742 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form7 = rawRow17742 := by decide +kernel

def row17742 : Integer.Sparse Key := [(key2121, -4), (key2161, 8), (key2250, -4)]

theorem rowCheck17742 : row17742 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17742 := by decide +kernel

theorem rowEval17742 (x : Key → ℝ) : Integer.Sparse.eval row17742 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17742, Integer.Sparse.eval_collectBalanced, rawRowCheck17742]

def rawRow17743 : Integer.Sparse Key := [(key2158, 4), (key2161, 4), (key2116, 4), (key2161, -4), (key2116, -4), (key2121, -4), (key2250, -4), (key2158, -4), (key2161, -4), (key2161, 12)]

theorem rawRowCheck17743 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form7 = rawRow17743 := by decide +kernel

def row17743 : Integer.Sparse Key := [(key2121, -4), (key2161, 8), (key2250, -4)]

theorem rowCheck17743 : row17743 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17743 := by decide +kernel

theorem rowEval17743 (x : Key → ℝ) : Integer.Sparse.eval row17743 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17743, Integer.Sparse.eval_collectBalanced, rawRowCheck17743]

def rawRow17744 : Integer.Sparse Key := [(key2161, 4), (key2116, 4), (key2158, 4), (key2121, -4), (key2161, -4), (key2116, -4), (key2161, -4), (key2250, -4), (key2158, -4), (key2161, 12)]

theorem rawRowCheck17744 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form7 = rawRow17744 := by decide +kernel

def row17744 : Integer.Sparse Key := [(key2121, -4), (key2161, 8), (key2250, -4)]

theorem rowCheck17744 : row17744 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17744 := by decide +kernel

theorem rowEval17744 (x : Key → ℝ) : Integer.Sparse.eval row17744 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17744, Integer.Sparse.eval_collectBalanced, rawRowCheck17744]

def rawRow17745 : Integer.Sparse Key := [(key2161, 4), (key2158, 4), (key2116, 4), (key2161, -4), (key2121, -4), (key2116, -4), (key2250, -4), (key2161, -4), (key2158, -4), (key2161, 12)]

theorem rawRowCheck17745 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form7 = rawRow17745 := by decide +kernel

def row17745 : Integer.Sparse Key := [(key2121, -4), (key2161, 8), (key2250, -4)]

theorem rowCheck17745 : row17745 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17745 := by decide +kernel

theorem rowEval17745 (x : Key → ℝ) : Integer.Sparse.eval row17745 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17745, Integer.Sparse.eval_collectBalanced, rawRowCheck17745]

def rawRow17746 : Integer.Sparse Key := [(key2116, 4), (key2158, 4), (key2161, 4), (key2158, -4), (key2161, -4), (key2250, -4), (key2116, -4), (key2121, -4), (key2161, -4), (key2161, 12)]

theorem rawRowCheck17746 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form7 = rawRow17746 := by decide +kernel

def row17746 : Integer.Sparse Key := [(key2121, -4), (key2161, 8), (key2250, -4)]

theorem rowCheck17746 : row17746 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17746 := by decide +kernel

theorem rowEval17746 (x : Key → ℝ) : Integer.Sparse.eval row17746 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17746, Integer.Sparse.eval_collectBalanced, rawRowCheck17746]

def rawRow17747 : Integer.Sparse Key := [(key2116, 4), (key2161, 4), (key2158, 4), (key2161, -4), (key2158, -4), (key2250, -4), (key2121, -4), (key2116, -4), (key2161, -4), (key2161, 12)]

theorem rawRowCheck17747 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form7 = rawRow17747 := by decide +kernel

def row17747 : Integer.Sparse Key := [(key2121, -4), (key2161, 8), (key2250, -4)]

theorem rowCheck17747 : row17747 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17747 := by decide +kernel

theorem rowEval17747 (x : Key → ℝ) : Integer.Sparse.eval row17747 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17747, Integer.Sparse.eval_collectBalanced, rawRowCheck17747]

def rawRow17748 : Integer.Sparse Key := [(key2158, 4), (key2116, 4), (key2161, 4), (key2158, -4), (key2250, -4), (key2161, -4), (key2116, -4), (key2161, -4), (key2121, -4), (key2161, 12)]

theorem rawRowCheck17748 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form7 = rawRow17748 := by decide +kernel

def row17748 : Integer.Sparse Key := [(key2121, -4), (key2161, 8), (key2250, -4)]

theorem rowCheck17748 : row17748 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17748 := by decide +kernel

theorem rowEval17748 (x : Key → ℝ) : Integer.Sparse.eval row17748 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17748, Integer.Sparse.eval_collectBalanced, rawRowCheck17748]

def rawRow17749 : Integer.Sparse Key := [(key2158, 4), (key2161, 4), (key2116, 4), (key2250, -4), (key2158, -4), (key2161, -4), (key2161, -4), (key2116, -4), (key2121, -4), (key2161, 12)]

theorem rawRowCheck17749 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form7 = rawRow17749 := by decide +kernel

def row17749 : Integer.Sparse Key := [(key2121, -4), (key2161, 8), (key2250, -4)]

theorem rowCheck17749 : row17749 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17749 := by decide +kernel

theorem rowEval17749 (x : Key → ℝ) : Integer.Sparse.eval row17749 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17749, Integer.Sparse.eval_collectBalanced, rawRowCheck17749]

def rawRow17750 : Integer.Sparse Key := [(key2161, 4), (key2116, 4), (key2158, 4), (key2161, -4), (key2250, -4), (key2158, -4), (key2121, -4), (key2161, -4), (key2116, -4), (key2161, 12)]

theorem rawRowCheck17750 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form7 = rawRow17750 := by decide +kernel

def row17750 : Integer.Sparse Key := [(key2121, -4), (key2161, 8), (key2250, -4)]

theorem rowCheck17750 : row17750 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17750 := by decide +kernel

theorem rowEval17750 (x : Key → ℝ) : Integer.Sparse.eval row17750 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17750, Integer.Sparse.eval_collectBalanced, rawRowCheck17750]

def rawRow17751 : Integer.Sparse Key := [(key2161, 4), (key2158, 4), (key2116, 4), (key2250, -4), (key2161, -4), (key2158, -4), (key2161, -4), (key2121, -4), (key2116, -4), (key2161, 12)]

theorem rawRowCheck17751 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form7 = rawRow17751 := by decide +kernel

def row17751 : Integer.Sparse Key := [(key2121, -4), (key2161, 8), (key2250, -4)]

theorem rowCheck17751 : row17751 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17751 := by decide +kernel

theorem rowEval17751 (x : Key → ℝ) : Integer.Sparse.eval row17751 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17751, Integer.Sparse.eval_collectBalanced, rawRowCheck17751]

def rawRow17752 : Integer.Sparse Key := [(key2158, 4), (key2158, 4), (key2250, 4), (key2116, -4), (key2161, -4), (key2161, -4), (key2116, -4), (key2161, -4), (key2161, -4), (key2121, 12)]

theorem rawRowCheck17752 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form7 = rawRow17752 := by decide +kernel

def row17752 : Integer.Sparse Key := [(key2116, -8), (key2121, 12), (key2158, 8), (key2161, -16), (key2250, 4)]

theorem rowCheck17752 : row17752 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17752 := by decide +kernel

theorem rowEval17752 (x : Key → ℝ) : Integer.Sparse.eval row17752 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17752, Integer.Sparse.eval_collectBalanced, rawRowCheck17752]

def rawRow17753 : Integer.Sparse Key := [(key2158, 4), (key2250, 4), (key2158, 4), (key2161, -4), (key2116, -4), (key2161, -4), (key2161, -4), (key2116, -4), (key2161, -4), (key2121, 12)]

theorem rawRowCheck17753 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form7 = rawRow17753 := by decide +kernel

def row17753 : Integer.Sparse Key := [(key2116, -8), (key2121, 12), (key2158, 8), (key2161, -16), (key2250, 4)]

theorem rowCheck17753 : row17753 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17753 := by decide +kernel

theorem rowEval17753 (x : Key → ℝ) : Integer.Sparse.eval row17753 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17753, Integer.Sparse.eval_collectBalanced, rawRowCheck17753]

def rawRow17754 : Integer.Sparse Key := [(key2250, 4), (key2158, 4), (key2158, 4), (key2161, -4), (key2161, -4), (key2116, -4), (key2161, -4), (key2161, -4), (key2116, -4), (key2121, 12)]

theorem rawRowCheck17754 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form7 = rawRow17754 := by decide +kernel

def row17754 : Integer.Sparse Key := [(key2116, -8), (key2121, 12), (key2158, 8), (key2161, -16), (key2250, 4)]

theorem rowCheck17754 : row17754 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17754 := by decide +kernel

theorem rowEval17754 (x : Key → ℝ) : Integer.Sparse.eval row17754 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17754, Integer.Sparse.eval_collectBalanced, rawRowCheck17754]

def rawRow17755 : Integer.Sparse Key := [(key1988, -2), (key1991, -2), (key1991, -2), (key2001, 6), (key1988, -2), (key1991, -2), (key1991, -2), (key2233, 2), (key2236, 2), (key2233, 2), (key2257, 2), (key2236, 2), (key2257, 2), (key2270, -2), (key2270, -2), (key2293, -2), (key2001, 6), (key2270, -2), (key2270, -2), (key2293, -2)]

theorem rawRowCheck17755 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form8 = rawRow17755 := by decide +kernel

def row17755 : Integer.Sparse Key := [(key1988, -4), (key1991, -8), (key2001, 12), (key2233, 4), (key2236, 4), (key2257, 4), (key2270, -8), (key2293, -4)]

theorem rowCheck17755 : row17755 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17755 := by decide +kernel

theorem rowEval17755 (x : Key → ℝ) : Integer.Sparse.eval row17755 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17755, Integer.Sparse.eval_collectBalanced, rawRowCheck17755]

def rawRow17756 : Integer.Sparse Key := [(key1991, -2), (key1988, -2), (key1991, -2), (key2001, 6), (key1991, -2), (key1988, -2), (key1991, -2), (key2236, 2), (key2233, 2), (key2257, 2), (key2233, 2), (key2257, 2), (key2236, 2), (key2270, -2), (key2293, -2), (key2270, -2), (key2001, 6), (key2270, -2), (key2293, -2), (key2270, -2)]

theorem rawRowCheck17756 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form8 = rawRow17756 := by decide +kernel

def row17756 : Integer.Sparse Key := [(key1988, -4), (key1991, -8), (key2001, 12), (key2233, 4), (key2236, 4), (key2257, 4), (key2270, -8), (key2293, -4)]

theorem rowCheck17756 : row17756 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17756 := by decide +kernel

theorem rowEval17756 (x : Key → ℝ) : Integer.Sparse.eval row17756 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck17756, Integer.Sparse.eval_collectBalanced, rawRowCheck17756]

def rawRow17757 : Integer.Sparse Key := [(key1991, -2), (key1991, -2), (key1988, -2), (key2001, 6), (key1991, -2), (key1991, -2), (key1988, -2), (key2257, 2), (key2257, 2), (key2236, 2), (key2236, 2), (key2233, 2), (key2233, 2), (key2293, -2), (key2270, -2), (key2270, -2), (key2001, 6), (key2293, -2), (key2270, -2), (key2270, -2)]

theorem rawRowCheck17757 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form8 = rawRow17757 := by decide +kernel

def row17757 : Integer.Sparse Key := [(key1988, -4), (key1991, -8), (key2001, 12), (key2233, 4), (key2236, 4), (key2257, 4), (key2270, -8), (key2293, -4)]

theorem rowCheck17757 : row17757 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17757 := by decide +kernel

theorem rowEval17757 (x : Key → ℝ) : Integer.Sparse.eval row17757 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck17757, Integer.Sparse.eval_collectBalanced, rawRowCheck17757]

def rawRow17758 : Integer.Sparse Key := [(key1988, -2), (key1991, -2), (key2001, -2), (key1991, 6), (key2233, -2), (key2236, -2), (key2270, -2), (key1988, 2), (key1991, 2), (key2233, 2), (key2257, 2), (key2270, 2), (key2293, 2), (key1991, -2), (key2236, -2), (key2257, -2), (key2270, 6), (key2001, -2), (key2270, -2), (key2293, -2)]

theorem rawRowCheck17758 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form8 = rawRow17758 := by decide +kernel

def row17758 : Integer.Sparse Key := [(key1991, 4), (key2001, -4), (key2236, -4), (key2270, 4)]

theorem rowCheck17758 : row17758 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17758 := by decide +kernel

theorem rowEval17758 (x : Key → ℝ) : Integer.Sparse.eval row17758 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17758, Integer.Sparse.eval_collectBalanced, rawRowCheck17758]

def rawRow17759 : Integer.Sparse Key := [(key1991, -2), (key1988, -2), (key2001, -2), (key1991, 6), (key2236, -2), (key2233, -2), (key2270, -2), (key1991, 2), (key1988, 2), (key2257, 2), (key2233, 2), (key2293, 2), (key2270, 2), (key1991, -2), (key2257, -2), (key2236, -2), (key2270, 6), (key2001, -2), (key2293, -2), (key2270, -2)]

theorem rawRowCheck17759 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form8 = rawRow17759 := by decide +kernel

def row17759 : Integer.Sparse Key := [(key1991, 4), (key2001, -4), (key2236, -4), (key2270, 4)]

theorem rowCheck17759 : row17759 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17759 := by decide +kernel

theorem rowEval17759 (x : Key → ℝ) : Integer.Sparse.eval row17759 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck17759, Integer.Sparse.eval_collectBalanced, rawRowCheck17759]

def rawRow17760 : Integer.Sparse Key := [(key1988, -2), (key2001, -2), (key1991, -2), (key1991, 6), (key2233, -2), (key2270, -2), (key2236, -2), (key2233, 2), (key2270, 2), (key1988, 2), (key2293, 2), (key1991, 2), (key2257, 2), (key2236, -2), (key1991, -2), (key2257, -2), (key2270, 6), (key2270, -2), (key2001, -2), (key2293, -2)]

theorem rawRowCheck17760 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form8 = rawRow17760 := by decide +kernel

def row17760 : Integer.Sparse Key := [(key1991, 4), (key2001, -4), (key2236, -4), (key2270, 4)]

theorem rowCheck17760 : row17760 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17760 := by decide +kernel

theorem rowEval17760 (x : Key → ℝ) : Integer.Sparse.eval row17760 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17760, Integer.Sparse.eval_collectBalanced, rawRowCheck17760]

def rawRow17761 : Integer.Sparse Key := [(key2001, -2), (key1988, -2), (key1991, -2), (key1991, 6), (key2270, -2), (key2233, -2), (key2236, -2), (key2270, 2), (key2233, 2), (key2293, 2), (key1988, 2), (key2257, 2), (key1991, 2), (key2236, -2), (key2257, -2), (key1991, -2), (key2270, 6), (key2270, -2), (key2293, -2), (key2001, -2)]

theorem rawRowCheck17761 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form8 = rawRow17761 := by decide +kernel

def row17761 : Integer.Sparse Key := [(key1991, 4), (key2001, -4), (key2236, -4), (key2270, 4)]

theorem rowCheck17761 : row17761 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17761 := by decide +kernel

theorem rowEval17761 (x : Key → ℝ) : Integer.Sparse.eval row17761 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17761, Integer.Sparse.eval_collectBalanced, rawRowCheck17761]

def rawRow17762 : Integer.Sparse Key := [(key1991, -2), (key2001, -2), (key1988, -2), (key1991, 6), (key2236, -2), (key2270, -2), (key2233, -2), (key2257, 2), (key2293, 2), (key1991, 2), (key2270, 2), (key1988, 2), (key2233, 2), (key2257, -2), (key1991, -2), (key2236, -2), (key2270, 6), (key2293, -2), (key2001, -2), (key2270, -2)]

theorem rawRowCheck17762 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form8 = rawRow17762 := by decide +kernel

def row17762 : Integer.Sparse Key := [(key1991, 4), (key2001, -4), (key2236, -4), (key2270, 4)]

theorem rowCheck17762 : row17762 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17762 := by decide +kernel

theorem rowEval17762 (x : Key → ℝ) : Integer.Sparse.eval row17762 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck17762, Integer.Sparse.eval_collectBalanced, rawRowCheck17762]

def rawRow17763 : Integer.Sparse Key := [(key2001, -2), (key1991, -2), (key1988, -2), (key1991, 6), (key2270, -2), (key2236, -2), (key2233, -2), (key2293, 2), (key2257, 2), (key2270, 2), (key1991, 2), (key2233, 2), (key1988, 2), (key2257, -2), (key2236, -2), (key1991, -2), (key2270, 6), (key2293, -2), (key2270, -2), (key2001, -2)]

theorem rawRowCheck17763 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form8 = rawRow17763 := by decide +kernel

def row17763 : Integer.Sparse Key := [(key1991, 4), (key2001, -4), (key2236, -4), (key2270, 4)]

theorem rowCheck17763 : row17763 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17763 := by decide +kernel

theorem rowEval17763 (x : Key → ℝ) : Integer.Sparse.eval row17763 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17763, Integer.Sparse.eval_collectBalanced, rawRowCheck17763]

def rawRow17764 : Integer.Sparse Key := [(key2233, -2), (key2236, -2), (key2270, -2), (key2270, 6), (key1988, -2), (key1991, -2), (key2001, -2), (key1988, 2), (key1991, 2), (key2233, 2), (key2257, 2), (key2270, 2), (key2293, 2), (key2001, -2), (key2270, -2), (key2293, -2), (key1991, 6), (key1991, -2), (key2236, -2), (key2257, -2)]

theorem rawRowCheck17764 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form8 = rawRow17764 := by decide +kernel

def row17764 : Integer.Sparse Key := [(key1991, 4), (key2001, -4), (key2236, -4), (key2270, 4)]

theorem rowCheck17764 : row17764 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17764 := by decide +kernel

theorem rowEval17764 (x : Key → ℝ) : Integer.Sparse.eval row17764 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17764, Integer.Sparse.eval_collectBalanced, rawRowCheck17764]

def rawRow17765 : Integer.Sparse Key := [(key2236, -2), (key2233, -2), (key2270, -2), (key2270, 6), (key1991, -2), (key1988, -2), (key2001, -2), (key1991, 2), (key1988, 2), (key2257, 2), (key2233, 2), (key2293, 2), (key2270, 2), (key2001, -2), (key2293, -2), (key2270, -2), (key1991, 6), (key1991, -2), (key2257, -2), (key2236, -2)]

theorem rawRowCheck17765 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form8 = rawRow17765 := by decide +kernel

def row17765 : Integer.Sparse Key := [(key1991, 4), (key2001, -4), (key2236, -4), (key2270, 4)]

theorem rowCheck17765 : row17765 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17765 := by decide +kernel

theorem rowEval17765 (x : Key → ℝ) : Integer.Sparse.eval row17765 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck17765, Integer.Sparse.eval_collectBalanced, rawRowCheck17765]

def rawRow17766 : Integer.Sparse Key := [(key2233, -2), (key2270, -2), (key2236, -2), (key2270, 6), (key1988, -2), (key2001, -2), (key1991, -2), (key2233, 2), (key2270, 2), (key1988, 2), (key2293, 2), (key1991, 2), (key2257, 2), (key2270, -2), (key2001, -2), (key2293, -2), (key1991, 6), (key2236, -2), (key1991, -2), (key2257, -2)]

theorem rawRowCheck17766 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form8 = rawRow17766 := by decide +kernel

def row17766 : Integer.Sparse Key := [(key1991, 4), (key2001, -4), (key2236, -4), (key2270, 4)]

theorem rowCheck17766 : row17766 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17766 := by decide +kernel

theorem rowEval17766 (x : Key → ℝ) : Integer.Sparse.eval row17766 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17766, Integer.Sparse.eval_collectBalanced, rawRowCheck17766]

def rawRow17767 : Integer.Sparse Key := [(key2270, -2), (key2233, -2), (key2236, -2), (key2270, 6), (key2001, -2), (key1988, -2), (key1991, -2), (key2270, 2), (key2233, 2), (key2293, 2), (key1988, 2), (key2257, 2), (key1991, 2), (key2270, -2), (key2293, -2), (key2001, -2), (key1991, 6), (key2236, -2), (key2257, -2), (key1991, -2)]

theorem rawRowCheck17767 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form8 = rawRow17767 := by decide +kernel

def row17767 : Integer.Sparse Key := [(key1991, 4), (key2001, -4), (key2236, -4), (key2270, 4)]

theorem rowCheck17767 : row17767 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17767 := by decide +kernel

theorem rowEval17767 (x : Key → ℝ) : Integer.Sparse.eval row17767 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17767, Integer.Sparse.eval_collectBalanced, rawRowCheck17767]

def rawRow17768 : Integer.Sparse Key := [(key2236, -2), (key2270, -2), (key2233, -2), (key2270, 6), (key1991, -2), (key2001, -2), (key1988, -2), (key2257, 2), (key2293, 2), (key1991, 2), (key2270, 2), (key1988, 2), (key2233, 2), (key2293, -2), (key2001, -2), (key2270, -2), (key1991, 6), (key2257, -2), (key1991, -2), (key2236, -2)]

theorem rawRowCheck17768 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form8 = rawRow17768 := by decide +kernel

def row17768 : Integer.Sparse Key := [(key1991, 4), (key2001, -4), (key2236, -4), (key2270, 4)]

theorem rowCheck17768 : row17768 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17768 := by decide +kernel

theorem rowEval17768 (x : Key → ℝ) : Integer.Sparse.eval row17768 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck17768, Integer.Sparse.eval_collectBalanced, rawRowCheck17768]

def rawRow17769 : Integer.Sparse Key := [(key2270, -2), (key2236, -2), (key2233, -2), (key2270, 6), (key2001, -2), (key1991, -2), (key1988, -2), (key2293, 2), (key2257, 2), (key2270, 2), (key1991, 2), (key2233, 2), (key1988, 2), (key2293, -2), (key2270, -2), (key2001, -2), (key1991, 6), (key2257, -2), (key2236, -2), (key1991, -2)]

theorem rawRowCheck17769 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form8 = rawRow17769 := by decide +kernel

def row17769 : Integer.Sparse Key := [(key1991, 4), (key2001, -4), (key2236, -4), (key2270, 4)]

theorem rowCheck17769 : row17769 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17769 := by decide +kernel

theorem rowEval17769 (x : Key → ℝ) : Integer.Sparse.eval row17769 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17769, Integer.Sparse.eval_collectBalanced, rawRowCheck17769]

def rawRow17770 : Integer.Sparse Key := [(key2233, -2), (key2270, -2), (key2270, -2), (key2236, 6), (key2233, -2), (key2270, -2), (key2270, -2), (key1988, 2), (key2001, 2), (key1988, 2), (key2293, 2), (key2001, 2), (key2293, 2), (key1991, -2), (key1991, -2), (key2257, -2), (key2236, 6), (key1991, -2), (key1991, -2), (key2257, -2)]

theorem rawRowCheck17770 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form8 = rawRow17770 := by decide +kernel

def row17770 : Integer.Sparse Key := [(key1988, 4), (key1991, -8), (key2001, 4), (key2233, -4), (key2236, 12), (key2257, -4), (key2270, -8), (key2293, 4)]

theorem rowCheck17770 : row17770 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17770 := by decide +kernel

theorem rowEval17770 (x : Key → ℝ) : Integer.Sparse.eval row17770 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17770, Integer.Sparse.eval_collectBalanced, rawRowCheck17770]

def rawRow17771 : Integer.Sparse Key := [(key2270, -2), (key2233, -2), (key2270, -2), (key2236, 6), (key2270, -2), (key2233, -2), (key2270, -2), (key2001, 2), (key1988, 2), (key2293, 2), (key1988, 2), (key2293, 2), (key2001, 2), (key1991, -2), (key2257, -2), (key1991, -2), (key2236, 6), (key1991, -2), (key2257, -2), (key1991, -2)]

theorem rawRowCheck17771 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form8 = rawRow17771 := by decide +kernel

def row17771 : Integer.Sparse Key := [(key1988, 4), (key1991, -8), (key2001, 4), (key2233, -4), (key2236, 12), (key2257, -4), (key2270, -8), (key2293, 4)]

theorem rowCheck17771 : row17771 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17771 := by decide +kernel

theorem rowEval17771 (x : Key → ℝ) : Integer.Sparse.eval row17771 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17771, Integer.Sparse.eval_collectBalanced, rawRowCheck17771]

def rawRow17772 : Integer.Sparse Key := [(key2270, -2), (key2270, -2), (key2233, -2), (key2236, 6), (key2270, -2), (key2270, -2), (key2233, -2), (key2293, 2), (key2293, 2), (key2001, 2), (key2001, 2), (key1988, 2), (key1988, 2), (key2257, -2), (key1991, -2), (key1991, -2), (key2236, 6), (key2257, -2), (key1991, -2), (key1991, -2)]

theorem rawRowCheck17772 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form8 = rawRow17772 := by decide +kernel

def row17772 : Integer.Sparse Key := [(key1988, 4), (key1991, -8), (key2001, 4), (key2233, -4), (key2236, 12), (key2257, -4), (key2270, -8), (key2293, 4)]

theorem rowCheck17772 : row17772 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17772 := by decide +kernel

theorem rowEval17772 (x : Key → ℝ) : Integer.Sparse.eval row17772 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17772, Integer.Sparse.eval_collectBalanced, rawRowCheck17772]

def rawRow17773 : Integer.Sparse Key := [(key772, 4), (key772, 4), (key780, 4), (key799, -4), (key805, -4), (key805, -4), (key799, -4), (key805, -4), (key805, -4), (key874, 12)]

theorem rawRowCheck17773 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form9 = rawRow17773 := by decide +kernel

def row17773 : Integer.Sparse Key := [(key772, 8), (key780, 4), (key799, -8), (key805, -16), (key874, 12)]

theorem rowCheck17773 : row17773 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17773 := by decide +kernel

theorem rowEval17773 (x : Key → ℝ) : Integer.Sparse.eval row17773 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17773, Integer.Sparse.eval_collectBalanced, rawRowCheck17773]

def rawRow17774 : Integer.Sparse Key := [(key772, 4), (key780, 4), (key772, 4), (key805, -4), (key799, -4), (key805, -4), (key805, -4), (key799, -4), (key805, -4), (key874, 12)]

theorem rawRowCheck17774 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form9 = rawRow17774 := by decide +kernel

def row17774 : Integer.Sparse Key := [(key772, 8), (key780, 4), (key799, -8), (key805, -16), (key874, 12)]

theorem rowCheck17774 : row17774 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17774 := by decide +kernel

theorem rowEval17774 (x : Key → ℝ) : Integer.Sparse.eval row17774 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17774, Integer.Sparse.eval_collectBalanced, rawRowCheck17774]

def rawRow17775 : Integer.Sparse Key := [(key780, 4), (key772, 4), (key772, 4), (key805, -4), (key805, -4), (key799, -4), (key805, -4), (key805, -4), (key799, -4), (key874, 12)]

theorem rawRowCheck17775 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form9 = rawRow17775 := by decide +kernel

def row17775 : Integer.Sparse Key := [(key772, 8), (key780, 4), (key799, -8), (key805, -16), (key874, 12)]

theorem rowCheck17775 : row17775 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17775 := by decide +kernel

theorem rowEval17775 (x : Key → ℝ) : Integer.Sparse.eval row17775 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17775, Integer.Sparse.eval_collectBalanced, rawRowCheck17775]

def rawRow17776 : Integer.Sparse Key := [(key772, 4), (key799, 4), (key805, 4), (key772, -4), (key780, -4), (key805, -4), (key799, -4), (key805, -4), (key874, -4), (key805, 12)]

theorem rawRowCheck17776 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form9 = rawRow17776 := by decide +kernel

def row17776 : Integer.Sparse Key := [(key780, -4), (key805, 8), (key874, -4)]

theorem rowCheck17776 : row17776 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17776 := by decide +kernel

theorem rowEval17776 (x : Key → ℝ) : Integer.Sparse.eval row17776 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17776, Integer.Sparse.eval_collectBalanced, rawRowCheck17776]

def rawRow17777 : Integer.Sparse Key := [(key772, 4), (key805, 4), (key799, 4), (key780, -4), (key772, -4), (key805, -4), (key805, -4), (key799, -4), (key874, -4), (key805, 12)]

theorem rawRowCheck17777 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form9 = rawRow17777 := by decide +kernel

def row17777 : Integer.Sparse Key := [(key780, -4), (key805, 8), (key874, -4)]

theorem rowCheck17777 : row17777 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17777 := by decide +kernel

theorem rowEval17777 (x : Key → ℝ) : Integer.Sparse.eval row17777 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17777, Integer.Sparse.eval_collectBalanced, rawRowCheck17777]

def rawRow17778 : Integer.Sparse Key := [(key799, 4), (key772, 4), (key805, 4), (key772, -4), (key805, -4), (key780, -4), (key799, -4), (key874, -4), (key805, -4), (key805, 12)]

theorem rawRowCheck17778 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form9 = rawRow17778 := by decide +kernel

def row17778 : Integer.Sparse Key := [(key780, -4), (key805, 8), (key874, -4)]

theorem rowCheck17778 : row17778 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17778 := by decide +kernel

theorem rowEval17778 (x : Key → ℝ) : Integer.Sparse.eval row17778 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17778, Integer.Sparse.eval_collectBalanced, rawRowCheck17778]

def rawRow17779 : Integer.Sparse Key := [(key799, 4), (key805, 4), (key772, 4), (key805, -4), (key772, -4), (key780, -4), (key874, -4), (key799, -4), (key805, -4), (key805, 12)]

theorem rawRowCheck17779 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form9 = rawRow17779 := by decide +kernel

def row17779 : Integer.Sparse Key := [(key780, -4), (key805, 8), (key874, -4)]

theorem rowCheck17779 : row17779 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17779 := by decide +kernel

theorem rowEval17779 (x : Key → ℝ) : Integer.Sparse.eval row17779 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17779, Integer.Sparse.eval_collectBalanced, rawRowCheck17779]

def rawRow17780 : Integer.Sparse Key := [(key805, 4), (key772, 4), (key799, 4), (key780, -4), (key805, -4), (key772, -4), (key805, -4), (key874, -4), (key799, -4), (key805, 12)]

theorem rawRowCheck17780 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form9 = rawRow17780 := by decide +kernel

def row17780 : Integer.Sparse Key := [(key780, -4), (key805, 8), (key874, -4)]

theorem rowCheck17780 : row17780 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17780 := by decide +kernel

theorem rowEval17780 (x : Key → ℝ) : Integer.Sparse.eval row17780 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17780, Integer.Sparse.eval_collectBalanced, rawRowCheck17780]

def rawRow17781 : Integer.Sparse Key := [(key805, 4), (key799, 4), (key772, 4), (key805, -4), (key780, -4), (key772, -4), (key874, -4), (key805, -4), (key799, -4), (key805, 12)]

theorem rawRowCheck17781 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form9 = rawRow17781 := by decide +kernel

def row17781 : Integer.Sparse Key := [(key780, -4), (key805, 8), (key874, -4)]

theorem rowCheck17781 : row17781 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17781 := by decide +kernel

theorem rowEval17781 (x : Key → ℝ) : Integer.Sparse.eval row17781 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17781, Integer.Sparse.eval_collectBalanced, rawRowCheck17781]

def rawRow17782 : Integer.Sparse Key := [(key772, 4), (key799, 4), (key805, 4), (key799, -4), (key805, -4), (key874, -4), (key772, -4), (key780, -4), (key805, -4), (key805, 12)]

theorem rawRowCheck17782 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form9 = rawRow17782 := by decide +kernel

def row17782 : Integer.Sparse Key := [(key780, -4), (key805, 8), (key874, -4)]

theorem rowCheck17782 : row17782 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17782 := by decide +kernel

theorem rowEval17782 (x : Key → ℝ) : Integer.Sparse.eval row17782 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17782, Integer.Sparse.eval_collectBalanced, rawRowCheck17782]

def rawRow17783 : Integer.Sparse Key := [(key772, 4), (key805, 4), (key799, 4), (key805, -4), (key799, -4), (key874, -4), (key780, -4), (key772, -4), (key805, -4), (key805, 12)]

theorem rawRowCheck17783 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form9 = rawRow17783 := by decide +kernel

def row17783 : Integer.Sparse Key := [(key780, -4), (key805, 8), (key874, -4)]

theorem rowCheck17783 : row17783 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17783 := by decide +kernel

theorem rowEval17783 (x : Key → ℝ) : Integer.Sparse.eval row17783 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17783, Integer.Sparse.eval_collectBalanced, rawRowCheck17783]

def rawRow17784 : Integer.Sparse Key := [(key799, 4), (key772, 4), (key805, 4), (key799, -4), (key874, -4), (key805, -4), (key772, -4), (key805, -4), (key780, -4), (key805, 12)]

theorem rawRowCheck17784 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form9 = rawRow17784 := by decide +kernel

def row17784 : Integer.Sparse Key := [(key780, -4), (key805, 8), (key874, -4)]

theorem rowCheck17784 : row17784 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17784 := by decide +kernel

theorem rowEval17784 (x : Key → ℝ) : Integer.Sparse.eval row17784 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17784, Integer.Sparse.eval_collectBalanced, rawRowCheck17784]

def rawRow17785 : Integer.Sparse Key := [(key799, 4), (key805, 4), (key772, 4), (key874, -4), (key799, -4), (key805, -4), (key805, -4), (key772, -4), (key780, -4), (key805, 12)]

theorem rawRowCheck17785 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form9 = rawRow17785 := by decide +kernel

def row17785 : Integer.Sparse Key := [(key780, -4), (key805, 8), (key874, -4)]

theorem rowCheck17785 : row17785 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17785 := by decide +kernel

theorem rowEval17785 (x : Key → ℝ) : Integer.Sparse.eval row17785 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17785, Integer.Sparse.eval_collectBalanced, rawRowCheck17785]

def rawRow17786 : Integer.Sparse Key := [(key805, 4), (key772, 4), (key799, 4), (key805, -4), (key874, -4), (key799, -4), (key780, -4), (key805, -4), (key772, -4), (key805, 12)]

theorem rawRowCheck17786 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form9 = rawRow17786 := by decide +kernel

def row17786 : Integer.Sparse Key := [(key780, -4), (key805, 8), (key874, -4)]

theorem rowCheck17786 : row17786 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17786 := by decide +kernel

theorem rowEval17786 (x : Key → ℝ) : Integer.Sparse.eval row17786 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17786, Integer.Sparse.eval_collectBalanced, rawRowCheck17786]

def rawRow17787 : Integer.Sparse Key := [(key805, 4), (key799, 4), (key772, 4), (key874, -4), (key805, -4), (key799, -4), (key805, -4), (key780, -4), (key772, -4), (key805, 12)]

theorem rawRowCheck17787 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form9 = rawRow17787 := by decide +kernel

def row17787 : Integer.Sparse Key := [(key780, -4), (key805, 8), (key874, -4)]

theorem rowCheck17787 : row17787 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17787 := by decide +kernel

theorem rowEval17787 (x : Key → ℝ) : Integer.Sparse.eval row17787 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17787, Integer.Sparse.eval_collectBalanced, rawRowCheck17787]

def rawRow17788 : Integer.Sparse Key := [(key799, 4), (key799, 4), (key874, 4), (key772, -4), (key805, -4), (key805, -4), (key772, -4), (key805, -4), (key805, -4), (key780, 12)]

theorem rawRowCheck17788 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form9 = rawRow17788 := by decide +kernel

def row17788 : Integer.Sparse Key := [(key772, -8), (key780, 12), (key799, 8), (key805, -16), (key874, 4)]

theorem rowCheck17788 : row17788 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17788 := by decide +kernel

theorem rowEval17788 (x : Key → ℝ) : Integer.Sparse.eval row17788 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17788, Integer.Sparse.eval_collectBalanced, rawRowCheck17788]

def rawRow17789 : Integer.Sparse Key := [(key799, 4), (key874, 4), (key799, 4), (key805, -4), (key772, -4), (key805, -4), (key805, -4), (key772, -4), (key805, -4), (key780, 12)]

theorem rawRowCheck17789 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form9 = rawRow17789 := by decide +kernel

def row17789 : Integer.Sparse Key := [(key772, -8), (key780, 12), (key799, 8), (key805, -16), (key874, 4)]

theorem rowCheck17789 : row17789 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17789 := by decide +kernel

theorem rowEval17789 (x : Key → ℝ) : Integer.Sparse.eval row17789 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17789, Integer.Sparse.eval_collectBalanced, rawRowCheck17789]

def rawRow17790 : Integer.Sparse Key := [(key874, 4), (key799, 4), (key799, 4), (key805, -4), (key805, -4), (key772, -4), (key805, -4), (key805, -4), (key772, -4), (key780, 12)]

theorem rawRowCheck17790 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form9 = rawRow17790 := by decide +kernel

def row17790 : Integer.Sparse Key := [(key772, -8), (key780, 12), (key799, 8), (key805, -16), (key874, 4)]

theorem rowCheck17790 : row17790 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17790 := by decide +kernel

theorem rowEval17790 (x : Key → ℝ) : Integer.Sparse.eval row17790 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17790, Integer.Sparse.eval_collectBalanced, rawRowCheck17790]

def rawRow17791 : Integer.Sparse Key := [(key2150, -1), (key2153, -1), (key2150, -1), (key2167, -1), (key2153, -1), (key2167, -1), (key2177, 2), (key2177, 2), (key2188, 2), (key2150, -1), (key2153, -1), (key2150, -1), (key2167, -1), (key2153, -1), (key2167, -1), (key2243, 2), (key2247, 2), (key2243, 2), (key2254, 2), (key2247, 2), (key2254, 2), (key2277, -1), (key2280, -1), (key2277, -1), (key2288, -1), (key2280, -1), (key2288, -1), (key2177, 2), (key2177, 2), (key2188, 2), (key2277, -1), (key2280, -1), (key2277, -1), (key2288, -1), (key2280, -1), (key2288, -1)]

theorem rawRowCheck17791 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form10 = rawRow17791 := by decide +kernel

def row17791 : Integer.Sparse Key := [(key2150, -4), (key2153, -4), (key2167, -4), (key2177, 8), (key2188, 4), (key2243, 4), (key2247, 4), (key2254, 4), (key2277, -4), (key2280, -4), (key2288, -4)]

theorem rowCheck17791 : row17791 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17791 := by decide +kernel

theorem rowEval17791 (x : Key → ℝ) : Integer.Sparse.eval row17791 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck17791, Integer.Sparse.eval_collectBalanced, rawRowCheck17791]

end MUB6.Certificate.GramRows

end OAI
