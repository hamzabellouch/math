import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
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

def rawRow16768 : Integer.Sparse Key := [(key2059, 6), (key2067, -2), (key2029, -2), (key2059, -2), (key2148, 6), (key2164, -2), (key2029, -2), (key2148, -2), (key2244, -2), (key2148, -2), (key2241, -2), (key2251, -2), (key2059, -2), (key2241, -2), (key2164, 2), (key2251, 2), (key2067, 2), (key2244, 2), (key2059, 2), (key2148, 2)]

theorem rawRowCheck16768 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form3 = rawRow16768 := by decide +kernel

def row16768 : Integer.Sparse Key := [(key2029, -4), (key2059, 4), (key2148, 4), (key2241, -4)]

theorem rowCheck16768 : row16768 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16768 := by decide +kernel

theorem rowEval16768 (x : Key → ℝ) : Integer.Sparse.eval row16768 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck16768, Integer.Sparse.eval_collectBalanced, rawRowCheck16768]

def rawRow16769 : Integer.Sparse Key := [(key2059, 6), (key2067, -2), (key2059, -2), (key2029, -2), (key2148, 6), (key2164, -2), (key2148, -2), (key2029, -2), (key2244, -2), (key2241, -2), (key2148, -2), (key2251, -2), (key2241, -2), (key2059, -2), (key2251, 2), (key2164, 2), (key2244, 2), (key2067, 2), (key2148, 2), (key2059, 2)]

theorem rawRowCheck16769 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form3 = rawRow16769 := by decide +kernel

def row16769 : Integer.Sparse Key := [(key2029, -4), (key2059, 4), (key2148, 4), (key2241, -4)]

theorem rowCheck16769 : row16769 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16769 := by decide +kernel

theorem rowEval16769 (x : Key → ℝ) : Integer.Sparse.eval row16769 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck16769, Integer.Sparse.eval_collectBalanced, rawRowCheck16769]

def rawRow16770 : Integer.Sparse Key := [(key2148, 6), (key2148, -2), (key2241, -2), (key2244, -2), (key2059, 6), (key2059, -2), (key2241, -2), (key2251, -2), (key2029, -2), (key2059, -2), (key2067, -2), (key2029, -2), (key2148, -2), (key2164, -2), (key2059, 2), (key2067, 2), (key2148, 2), (key2164, 2), (key2244, 2), (key2251, 2)]

theorem rawRowCheck16770 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form3 = rawRow16770 := by decide +kernel

def row16770 : Integer.Sparse Key := [(key2029, -4), (key2059, 4), (key2148, 4), (key2241, -4)]

theorem rowCheck16770 : row16770 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16770 := by decide +kernel

theorem rowEval16770 (x : Key → ℝ) : Integer.Sparse.eval row16770 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck16770, Integer.Sparse.eval_collectBalanced, rawRowCheck16770]

def rawRow16771 : Integer.Sparse Key := [(key2148, 6), (key2148, -2), (key2244, -2), (key2241, -2), (key2059, 6), (key2059, -2), (key2251, -2), (key2241, -2), (key2029, -2), (key2067, -2), (key2059, -2), (key2029, -2), (key2164, -2), (key2148, -2), (key2067, 2), (key2059, 2), (key2164, 2), (key2148, 2), (key2251, 2), (key2244, 2)]

theorem rawRowCheck16771 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form3 = rawRow16771 := by decide +kernel

def row16771 : Integer.Sparse Key := [(key2029, -4), (key2059, 4), (key2148, 4), (key2241, -4)]

theorem rowCheck16771 : row16771 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16771 := by decide +kernel

theorem rowEval16771 (x : Key → ℝ) : Integer.Sparse.eval row16771 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck16771, Integer.Sparse.eval_collectBalanced, rawRowCheck16771]

def rawRow16772 : Integer.Sparse Key := [(key2148, 6), (key2241, -2), (key2148, -2), (key2244, -2), (key2059, 6), (key2241, -2), (key2059, -2), (key2251, -2), (key2059, -2), (key2029, -2), (key2067, -2), (key2148, -2), (key2029, -2), (key2164, -2), (key2148, 2), (key2244, 2), (key2059, 2), (key2251, 2), (key2067, 2), (key2164, 2)]

theorem rawRowCheck16772 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form3 = rawRow16772 := by decide +kernel

def row16772 : Integer.Sparse Key := [(key2029, -4), (key2059, 4), (key2148, 4), (key2241, -4)]

theorem rowCheck16772 : row16772 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16772 := by decide +kernel

theorem rowEval16772 (x : Key → ℝ) : Integer.Sparse.eval row16772 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck16772, Integer.Sparse.eval_collectBalanced, rawRowCheck16772]

def rawRow16773 : Integer.Sparse Key := [(key2148, 6), (key2241, -2), (key2244, -2), (key2148, -2), (key2059, 6), (key2241, -2), (key2251, -2), (key2059, -2), (key2059, -2), (key2067, -2), (key2029, -2), (key2148, -2), (key2164, -2), (key2029, -2), (key2244, 2), (key2148, 2), (key2251, 2), (key2059, 2), (key2164, 2), (key2067, 2)]

theorem rawRowCheck16773 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form3 = rawRow16773 := by decide +kernel

def row16773 : Integer.Sparse Key := [(key2029, -4), (key2059, 4), (key2148, 4), (key2241, -4)]

theorem rowCheck16773 : row16773 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16773 := by decide +kernel

theorem rowEval16773 (x : Key → ℝ) : Integer.Sparse.eval row16773 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck16773, Integer.Sparse.eval_collectBalanced, rawRowCheck16773]

def rawRow16774 : Integer.Sparse Key := [(key2148, 6), (key2244, -2), (key2148, -2), (key2241, -2), (key2059, 6), (key2251, -2), (key2059, -2), (key2241, -2), (key2067, -2), (key2029, -2), (key2059, -2), (key2164, -2), (key2029, -2), (key2148, -2), (key2164, 2), (key2251, 2), (key2067, 2), (key2244, 2), (key2059, 2), (key2148, 2)]

theorem rawRowCheck16774 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form3 = rawRow16774 := by decide +kernel

def row16774 : Integer.Sparse Key := [(key2029, -4), (key2059, 4), (key2148, 4), (key2241, -4)]

theorem rowCheck16774 : row16774 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16774 := by decide +kernel

theorem rowEval16774 (x : Key → ℝ) : Integer.Sparse.eval row16774 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck16774, Integer.Sparse.eval_collectBalanced, rawRowCheck16774]

def rawRow16775 : Integer.Sparse Key := [(key2148, 6), (key2244, -2), (key2241, -2), (key2148, -2), (key2059, 6), (key2251, -2), (key2241, -2), (key2059, -2), (key2067, -2), (key2059, -2), (key2029, -2), (key2164, -2), (key2148, -2), (key2029, -2), (key2251, 2), (key2164, 2), (key2244, 2), (key2067, 2), (key2148, 2), (key2059, 2)]

theorem rawRowCheck16775 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form3 = rawRow16775 := by decide +kernel

def row16775 : Integer.Sparse Key := [(key2029, -4), (key2059, 4), (key2148, 4), (key2241, -4)]

theorem rowCheck16775 : row16775 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16775 := by decide +kernel

theorem rowEval16775 (x : Key → ℝ) : Integer.Sparse.eval row16775 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck16775, Integer.Sparse.eval_collectBalanced, rawRowCheck16775]

def rawRow16776 : Integer.Sparse Key := [(key2241, 6), (key2148, -2), (key2148, -2), (key2244, -2), (key2241, 6), (key2059, -2), (key2059, -2), (key2251, -2), (key2148, -2), (key2148, -2), (key2244, -2), (key2059, -2), (key2059, -2), (key2251, -2), (key2029, 2), (key2067, 2), (key2029, 2), (key2164, 2), (key2067, 2), (key2164, 2)]

theorem rawRowCheck16776 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form3 = rawRow16776 := by decide +kernel

def row16776 : Integer.Sparse Key := [(key2029, 4), (key2059, -8), (key2067, 4), (key2148, -8), (key2164, 4), (key2241, 12), (key2244, -4), (key2251, -4)]

theorem rowCheck16776 : row16776 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16776 := by decide +kernel

theorem rowEval16776 (x : Key → ℝ) : Integer.Sparse.eval row16776 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck16776, Integer.Sparse.eval_collectBalanced, rawRowCheck16776]

def rawRow16777 : Integer.Sparse Key := [(key2241, 6), (key2148, -2), (key2244, -2), (key2148, -2), (key2241, 6), (key2059, -2), (key2251, -2), (key2059, -2), (key2148, -2), (key2244, -2), (key2148, -2), (key2059, -2), (key2251, -2), (key2059, -2), (key2067, 2), (key2029, 2), (key2164, 2), (key2029, 2), (key2164, 2), (key2067, 2)]

theorem rawRowCheck16777 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form3 = rawRow16777 := by decide +kernel

def row16777 : Integer.Sparse Key := [(key2029, 4), (key2059, -8), (key2067, 4), (key2148, -8), (key2164, 4), (key2241, 12), (key2244, -4), (key2251, -4)]

theorem rowCheck16777 : row16777 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16777 := by decide +kernel

theorem rowEval16777 (x : Key → ℝ) : Integer.Sparse.eval row16777 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck16777, Integer.Sparse.eval_collectBalanced, rawRowCheck16777]

def rawRow16778 : Integer.Sparse Key := [(key2241, 6), (key2244, -2), (key2148, -2), (key2148, -2), (key2241, 6), (key2251, -2), (key2059, -2), (key2059, -2), (key2244, -2), (key2148, -2), (key2148, -2), (key2251, -2), (key2059, -2), (key2059, -2), (key2164, 2), (key2164, 2), (key2067, 2), (key2067, 2), (key2029, 2), (key2029, 2)]

theorem rawRowCheck16778 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form3 = rawRow16778 := by decide +kernel

def row16778 : Integer.Sparse Key := [(key2029, 4), (key2059, -8), (key2067, 4), (key2148, -8), (key2164, 4), (key2241, 12), (key2244, -4), (key2251, -4)]

theorem rowCheck16778 : row16778 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16778 := by decide +kernel

theorem rowEval16778 (x : Key → ℝ) : Integer.Sparse.eval row16778 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck16778, Integer.Sparse.eval_collectBalanced, rawRowCheck16778]

def rawRow16779 : Integer.Sparse Key := [(key703, -2), (key706, -2), (key706, -2), (key715, 6), (key703, -2), (key706, -2), (key706, -2), (key857, 2), (key860, 2), (key857, 2), (key883, 2), (key860, 2), (key883, 2), (key892, -2), (key892, -2), (key914, -2), (key715, 6), (key892, -2), (key892, -2), (key914, -2)]

theorem rawRowCheck16779 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form4 = rawRow16779 := by decide +kernel

def row16779 : Integer.Sparse Key := [(key703, -4), (key706, -8), (key715, 12), (key857, 4), (key860, 4), (key883, 4), (key892, -8), (key914, -4)]

theorem rowCheck16779 : row16779 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16779 := by decide +kernel

theorem rowEval16779 (x : Key → ℝ) : Integer.Sparse.eval row16779 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck16779, Integer.Sparse.eval_collectBalanced, rawRowCheck16779]

def rawRow16780 : Integer.Sparse Key := [(key706, -2), (key703, -2), (key706, -2), (key715, 6), (key706, -2), (key703, -2), (key706, -2), (key860, 2), (key857, 2), (key883, 2), (key857, 2), (key883, 2), (key860, 2), (key892, -2), (key914, -2), (key892, -2), (key715, 6), (key892, -2), (key914, -2), (key892, -2)]

theorem rawRowCheck16780 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form4 = rawRow16780 := by decide +kernel

def row16780 : Integer.Sparse Key := [(key703, -4), (key706, -8), (key715, 12), (key857, 4), (key860, 4), (key883, 4), (key892, -8), (key914, -4)]

theorem rowCheck16780 : row16780 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16780 := by decide +kernel

theorem rowEval16780 (x : Key → ℝ) : Integer.Sparse.eval row16780 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck16780, Integer.Sparse.eval_collectBalanced, rawRowCheck16780]

def rawRow16781 : Integer.Sparse Key := [(key706, -2), (key706, -2), (key703, -2), (key715, 6), (key706, -2), (key706, -2), (key703, -2), (key883, 2), (key883, 2), (key860, 2), (key860, 2), (key857, 2), (key857, 2), (key914, -2), (key892, -2), (key892, -2), (key715, 6), (key914, -2), (key892, -2), (key892, -2)]

theorem rawRowCheck16781 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form4 = rawRow16781 := by decide +kernel

def row16781 : Integer.Sparse Key := [(key703, -4), (key706, -8), (key715, 12), (key857, 4), (key860, 4), (key883, 4), (key892, -8), (key914, -4)]

theorem rowCheck16781 : row16781 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16781 := by decide +kernel

theorem rowEval16781 (x : Key → ℝ) : Integer.Sparse.eval row16781 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck16781, Integer.Sparse.eval_collectBalanced, rawRowCheck16781]

def rawRow16782 : Integer.Sparse Key := [(key703, -2), (key706, -2), (key715, -2), (key706, 6), (key857, -2), (key860, -2), (key892, -2), (key703, 2), (key706, 2), (key857, 2), (key883, 2), (key892, 2), (key914, 2), (key706, -2), (key860, -2), (key883, -2), (key892, 6), (key715, -2), (key892, -2), (key914, -2)]

theorem rawRowCheck16782 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form4 = rawRow16782 := by decide +kernel

def row16782 : Integer.Sparse Key := [(key706, 4), (key715, -4), (key860, -4), (key892, 4)]

theorem rowCheck16782 : row16782 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16782 := by decide +kernel

theorem rowEval16782 (x : Key → ℝ) : Integer.Sparse.eval row16782 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck16782, Integer.Sparse.eval_collectBalanced, rawRowCheck16782]

def rawRow16783 : Integer.Sparse Key := [(key706, -2), (key703, -2), (key715, -2), (key706, 6), (key860, -2), (key857, -2), (key892, -2), (key706, 2), (key703, 2), (key883, 2), (key857, 2), (key914, 2), (key892, 2), (key706, -2), (key883, -2), (key860, -2), (key892, 6), (key715, -2), (key914, -2), (key892, -2)]

theorem rawRowCheck16783 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form4 = rawRow16783 := by decide +kernel

def row16783 : Integer.Sparse Key := [(key706, 4), (key715, -4), (key860, -4), (key892, 4)]

theorem rowCheck16783 : row16783 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16783 := by decide +kernel

theorem rowEval16783 (x : Key → ℝ) : Integer.Sparse.eval row16783 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck16783, Integer.Sparse.eval_collectBalanced, rawRowCheck16783]

def rawRow16784 : Integer.Sparse Key := [(key703, -2), (key715, -2), (key706, -2), (key706, 6), (key857, -2), (key892, -2), (key860, -2), (key857, 2), (key892, 2), (key703, 2), (key914, 2), (key706, 2), (key883, 2), (key860, -2), (key706, -2), (key883, -2), (key892, 6), (key892, -2), (key715, -2), (key914, -2)]

theorem rawRowCheck16784 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form4 = rawRow16784 := by decide +kernel

def row16784 : Integer.Sparse Key := [(key706, 4), (key715, -4), (key860, -4), (key892, 4)]

theorem rowCheck16784 : row16784 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16784 := by decide +kernel

theorem rowEval16784 (x : Key → ℝ) : Integer.Sparse.eval row16784 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck16784, Integer.Sparse.eval_collectBalanced, rawRowCheck16784]

def rawRow16785 : Integer.Sparse Key := [(key715, -2), (key703, -2), (key706, -2), (key706, 6), (key892, -2), (key857, -2), (key860, -2), (key892, 2), (key857, 2), (key914, 2), (key703, 2), (key883, 2), (key706, 2), (key860, -2), (key883, -2), (key706, -2), (key892, 6), (key892, -2), (key914, -2), (key715, -2)]

theorem rawRowCheck16785 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form4 = rawRow16785 := by decide +kernel

def row16785 : Integer.Sparse Key := [(key706, 4), (key715, -4), (key860, -4), (key892, 4)]

theorem rowCheck16785 : row16785 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16785 := by decide +kernel

theorem rowEval16785 (x : Key → ℝ) : Integer.Sparse.eval row16785 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck16785, Integer.Sparse.eval_collectBalanced, rawRowCheck16785]

def rawRow16786 : Integer.Sparse Key := [(key706, -2), (key715, -2), (key703, -2), (key706, 6), (key860, -2), (key892, -2), (key857, -2), (key883, 2), (key914, 2), (key706, 2), (key892, 2), (key703, 2), (key857, 2), (key883, -2), (key706, -2), (key860, -2), (key892, 6), (key914, -2), (key715, -2), (key892, -2)]

theorem rawRowCheck16786 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form4 = rawRow16786 := by decide +kernel

def row16786 : Integer.Sparse Key := [(key706, 4), (key715, -4), (key860, -4), (key892, 4)]

theorem rowCheck16786 : row16786 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16786 := by decide +kernel

theorem rowEval16786 (x : Key → ℝ) : Integer.Sparse.eval row16786 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck16786, Integer.Sparse.eval_collectBalanced, rawRowCheck16786]

def rawRow16787 : Integer.Sparse Key := [(key715, -2), (key706, -2), (key703, -2), (key706, 6), (key892, -2), (key860, -2), (key857, -2), (key914, 2), (key883, 2), (key892, 2), (key706, 2), (key857, 2), (key703, 2), (key883, -2), (key860, -2), (key706, -2), (key892, 6), (key914, -2), (key892, -2), (key715, -2)]

theorem rawRowCheck16787 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form4 = rawRow16787 := by decide +kernel

def row16787 : Integer.Sparse Key := [(key706, 4), (key715, -4), (key860, -4), (key892, 4)]

theorem rowCheck16787 : row16787 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16787 := by decide +kernel

theorem rowEval16787 (x : Key → ℝ) : Integer.Sparse.eval row16787 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck16787, Integer.Sparse.eval_collectBalanced, rawRowCheck16787]

def rawRow16788 : Integer.Sparse Key := [(key857, -2), (key860, -2), (key892, -2), (key892, 6), (key703, -2), (key706, -2), (key715, -2), (key703, 2), (key706, 2), (key857, 2), (key883, 2), (key892, 2), (key914, 2), (key715, -2), (key892, -2), (key914, -2), (key706, 6), (key706, -2), (key860, -2), (key883, -2)]

theorem rawRowCheck16788 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form4 = rawRow16788 := by decide +kernel

def row16788 : Integer.Sparse Key := [(key706, 4), (key715, -4), (key860, -4), (key892, 4)]

theorem rowCheck16788 : row16788 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16788 := by decide +kernel

theorem rowEval16788 (x : Key → ℝ) : Integer.Sparse.eval row16788 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck16788, Integer.Sparse.eval_collectBalanced, rawRowCheck16788]

def rawRow16789 : Integer.Sparse Key := [(key860, -2), (key857, -2), (key892, -2), (key892, 6), (key706, -2), (key703, -2), (key715, -2), (key706, 2), (key703, 2), (key883, 2), (key857, 2), (key914, 2), (key892, 2), (key715, -2), (key914, -2), (key892, -2), (key706, 6), (key706, -2), (key883, -2), (key860, -2)]

theorem rawRowCheck16789 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form4 = rawRow16789 := by decide +kernel

def row16789 : Integer.Sparse Key := [(key706, 4), (key715, -4), (key860, -4), (key892, 4)]

theorem rowCheck16789 : row16789 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16789 := by decide +kernel

theorem rowEval16789 (x : Key → ℝ) : Integer.Sparse.eval row16789 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck16789, Integer.Sparse.eval_collectBalanced, rawRowCheck16789]

def rawRow16790 : Integer.Sparse Key := [(key857, -2), (key892, -2), (key860, -2), (key892, 6), (key703, -2), (key715, -2), (key706, -2), (key857, 2), (key892, 2), (key703, 2), (key914, 2), (key706, 2), (key883, 2), (key892, -2), (key715, -2), (key914, -2), (key706, 6), (key860, -2), (key706, -2), (key883, -2)]

theorem rawRowCheck16790 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form4 = rawRow16790 := by decide +kernel

def row16790 : Integer.Sparse Key := [(key706, 4), (key715, -4), (key860, -4), (key892, 4)]

theorem rowCheck16790 : row16790 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16790 := by decide +kernel

theorem rowEval16790 (x : Key → ℝ) : Integer.Sparse.eval row16790 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck16790, Integer.Sparse.eval_collectBalanced, rawRowCheck16790]

def rawRow16791 : Integer.Sparse Key := [(key892, -2), (key857, -2), (key860, -2), (key892, 6), (key715, -2), (key703, -2), (key706, -2), (key892, 2), (key857, 2), (key914, 2), (key703, 2), (key883, 2), (key706, 2), (key892, -2), (key914, -2), (key715, -2), (key706, 6), (key860, -2), (key883, -2), (key706, -2)]

theorem rawRowCheck16791 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form4 = rawRow16791 := by decide +kernel

def row16791 : Integer.Sparse Key := [(key706, 4), (key715, -4), (key860, -4), (key892, 4)]

theorem rowCheck16791 : row16791 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16791 := by decide +kernel

theorem rowEval16791 (x : Key → ℝ) : Integer.Sparse.eval row16791 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck16791, Integer.Sparse.eval_collectBalanced, rawRowCheck16791]

def rawRow16792 : Integer.Sparse Key := [(key860, -2), (key892, -2), (key857, -2), (key892, 6), (key706, -2), (key715, -2), (key703, -2), (key883, 2), (key914, 2), (key706, 2), (key892, 2), (key703, 2), (key857, 2), (key914, -2), (key715, -2), (key892, -2), (key706, 6), (key883, -2), (key706, -2), (key860, -2)]

theorem rawRowCheck16792 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form4 = rawRow16792 := by decide +kernel

def row16792 : Integer.Sparse Key := [(key706, 4), (key715, -4), (key860, -4), (key892, 4)]

theorem rowCheck16792 : row16792 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16792 := by decide +kernel

theorem rowEval16792 (x : Key → ℝ) : Integer.Sparse.eval row16792 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck16792, Integer.Sparse.eval_collectBalanced, rawRowCheck16792]

def rawRow16793 : Integer.Sparse Key := [(key892, -2), (key860, -2), (key857, -2), (key892, 6), (key715, -2), (key706, -2), (key703, -2), (key914, 2), (key883, 2), (key892, 2), (key706, 2), (key857, 2), (key703, 2), (key914, -2), (key892, -2), (key715, -2), (key706, 6), (key883, -2), (key860, -2), (key706, -2)]

theorem rawRowCheck16793 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form4 = rawRow16793 := by decide +kernel

def row16793 : Integer.Sparse Key := [(key706, 4), (key715, -4), (key860, -4), (key892, 4)]

theorem rowCheck16793 : row16793 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16793 := by decide +kernel

theorem rowEval16793 (x : Key → ℝ) : Integer.Sparse.eval row16793 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck16793, Integer.Sparse.eval_collectBalanced, rawRowCheck16793]

def rawRow16794 : Integer.Sparse Key := [(key857, -2), (key892, -2), (key892, -2), (key860, 6), (key857, -2), (key892, -2), (key892, -2), (key703, 2), (key715, 2), (key703, 2), (key914, 2), (key715, 2), (key914, 2), (key706, -2), (key706, -2), (key883, -2), (key860, 6), (key706, -2), (key706, -2), (key883, -2)]

theorem rawRowCheck16794 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form4 = rawRow16794 := by decide +kernel

def row16794 : Integer.Sparse Key := [(key703, 4), (key706, -8), (key715, 4), (key857, -4), (key860, 12), (key883, -4), (key892, -8), (key914, 4)]

theorem rowCheck16794 : row16794 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16794 := by decide +kernel

theorem rowEval16794 (x : Key → ℝ) : Integer.Sparse.eval row16794 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck16794, Integer.Sparse.eval_collectBalanced, rawRowCheck16794]

def rawRow16795 : Integer.Sparse Key := [(key892, -2), (key857, -2), (key892, -2), (key860, 6), (key892, -2), (key857, -2), (key892, -2), (key715, 2), (key703, 2), (key914, 2), (key703, 2), (key914, 2), (key715, 2), (key706, -2), (key883, -2), (key706, -2), (key860, 6), (key706, -2), (key883, -2), (key706, -2)]

theorem rawRowCheck16795 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form4 = rawRow16795 := by decide +kernel

def row16795 : Integer.Sparse Key := [(key703, 4), (key706, -8), (key715, 4), (key857, -4), (key860, 12), (key883, -4), (key892, -8), (key914, 4)]

theorem rowCheck16795 : row16795 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16795 := by decide +kernel

theorem rowEval16795 (x : Key → ℝ) : Integer.Sparse.eval row16795 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck16795, Integer.Sparse.eval_collectBalanced, rawRowCheck16795]

def rawRow16796 : Integer.Sparse Key := [(key892, -2), (key892, -2), (key857, -2), (key860, 6), (key892, -2), (key892, -2), (key857, -2), (key914, 2), (key914, 2), (key715, 2), (key715, 2), (key703, 2), (key703, 2), (key883, -2), (key706, -2), (key706, -2), (key860, 6), (key883, -2), (key706, -2), (key706, -2)]

theorem rawRowCheck16796 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form4 = rawRow16796 := by decide +kernel

def row16796 : Integer.Sparse Key := [(key703, 4), (key706, -8), (key715, 4), (key857, -4), (key860, 12), (key883, -4), (key892, -8), (key914, 4)]

theorem rowCheck16796 : row16796 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16796 := by decide +kernel

theorem rowEval16796 (x : Key → ℝ) : Integer.Sparse.eval row16796 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck16796, Integer.Sparse.eval_collectBalanced, rawRowCheck16796]

def rawRow16797 : Integer.Sparse Key := [(key859, 4), (key859, 4), (key886, 4), (key891, -2), (key895, -2), (key891, -2), (key916, -2), (key895, -2), (key916, -2), (key891, -2), (key895, -2), (key891, -2), (key916, -2), (key895, -2), (key916, -2), (key948, 4), (key948, 4), (key955, 4)]

theorem rawRowCheck16797 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form5 = rawRow16797 := by decide +kernel

def row16797 : Integer.Sparse Key := [(key859, 8), (key886, 4), (key891, -8), (key895, -8), (key916, -8), (key948, 8), (key955, 4)]

theorem rowCheck16797 : row16797 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16797 := by decide +kernel

theorem rowEval16797 (x : Key → ℝ) : Integer.Sparse.eval row16797 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck16797, Integer.Sparse.eval_collectBalanced, rawRowCheck16797]

def rawRow16798 : Integer.Sparse Key := [(key859, 4), (key886, 4), (key859, 4), (key895, -2), (key891, -2), (key916, -2), (key891, -2), (key916, -2), (key895, -2), (key895, -2), (key891, -2), (key916, -2), (key891, -2), (key916, -2), (key895, -2), (key948, 4), (key955, 4), (key948, 4)]

theorem rawRowCheck16798 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form5 = rawRow16798 := by decide +kernel

def row16798 : Integer.Sparse Key := [(key859, 8), (key886, 4), (key891, -8), (key895, -8), (key916, -8), (key948, 8), (key955, 4)]

theorem rowCheck16798 : row16798 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16798 := by decide +kernel

theorem rowEval16798 (x : Key → ℝ) : Integer.Sparse.eval row16798 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck16798, Integer.Sparse.eval_collectBalanced, rawRowCheck16798]

def rawRow16799 : Integer.Sparse Key := [(key886, 4), (key859, 4), (key859, 4), (key916, -2), (key916, -2), (key895, -2), (key895, -2), (key891, -2), (key891, -2), (key916, -2), (key916, -2), (key895, -2), (key895, -2), (key891, -2), (key891, -2), (key955, 4), (key948, 4), (key948, 4)]

theorem rawRowCheck16799 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form5 = rawRow16799 := by decide +kernel

def row16799 : Integer.Sparse Key := [(key859, 8), (key886, 4), (key891, -8), (key895, -8), (key916, -8), (key948, 8), (key955, 4)]

theorem rowCheck16799 : row16799 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16799 := by decide +kernel

theorem rowEval16799 (x : Key → ℝ) : Integer.Sparse.eval row16799 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck16799, Integer.Sparse.eval_collectBalanced, rawRowCheck16799]

def rawRow16800 : Integer.Sparse Key := [(key705, 4), (key891, 4), (key916, 4), (key705, -2), (key710, -2), (key859, -2), (key886, -2), (key895, -2), (key916, -2), (key714, -2), (key718, -2), (key891, -2), (key916, -2), (key948, -2), (key955, -2), (key718, 4), (key895, 4), (key916, 4)]

theorem rawRowCheck16800 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form5 = rawRow16800 := by decide +kernel

def row16800 : Integer.Sparse Key := [(key705, 2), (key710, -2), (key714, -2), (key718, 2), (key859, -2), (key886, -2), (key891, 2), (key895, 2), (key916, 4), (key948, -2), (key955, -2)]

theorem rowCheck16800 : row16800 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16800 := by decide +kernel

theorem rowEval16800 (x : Key → ℝ) : Integer.Sparse.eval row16800 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck16800, Integer.Sparse.eval_collectBalanced, rawRowCheck16800]

def rawRow16801 : Integer.Sparse Key := [(key705, 4), (key916, 4), (key891, 4), (key710, -2), (key705, -2), (key886, -2), (key859, -2), (key916, -2), (key895, -2), (key718, -2), (key714, -2), (key916, -2), (key891, -2), (key955, -2), (key948, -2), (key718, 4), (key916, 4), (key895, 4)]

theorem rawRowCheck16801 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form5 = rawRow16801 := by decide +kernel

def row16801 : Integer.Sparse Key := [(key705, 2), (key710, -2), (key714, -2), (key718, 2), (key859, -2), (key886, -2), (key891, 2), (key895, 2), (key916, 4), (key948, -2), (key955, -2)]

theorem rowCheck16801 : row16801 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16801 := by decide +kernel

theorem rowEval16801 (x : Key → ℝ) : Integer.Sparse.eval row16801 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck16801, Integer.Sparse.eval_collectBalanced, rawRowCheck16801]

def rawRow16802 : Integer.Sparse Key := [(key891, 4), (key705, 4), (key916, 4), (key859, -2), (key895, -2), (key705, -2), (key916, -2), (key710, -2), (key886, -2), (key891, -2), (key948, -2), (key714, -2), (key955, -2), (key718, -2), (key916, -2), (key895, 4), (key718, 4), (key916, 4)]

theorem rawRowCheck16802 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form5 = rawRow16802 := by decide +kernel

def row16802 : Integer.Sparse Key := [(key705, 2), (key710, -2), (key714, -2), (key718, 2), (key859, -2), (key886, -2), (key891, 2), (key895, 2), (key916, 4), (key948, -2), (key955, -2)]

theorem rowCheck16802 : row16802 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16802 := by decide +kernel

theorem rowEval16802 (x : Key → ℝ) : Integer.Sparse.eval row16802 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck16802, Integer.Sparse.eval_collectBalanced, rawRowCheck16802]

def rawRow16803 : Integer.Sparse Key := [(key891, 4), (key916, 4), (key705, 4), (key895, -2), (key859, -2), (key916, -2), (key705, -2), (key886, -2), (key710, -2), (key948, -2), (key891, -2), (key955, -2), (key714, -2), (key916, -2), (key718, -2), (key895, 4), (key916, 4), (key718, 4)]

theorem rawRowCheck16803 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form5 = rawRow16803 := by decide +kernel

def row16803 : Integer.Sparse Key := [(key705, 2), (key710, -2), (key714, -2), (key718, 2), (key859, -2), (key886, -2), (key891, 2), (key895, 2), (key916, 4), (key948, -2), (key955, -2)]

theorem rowCheck16803 : row16803 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16803 := by decide +kernel

theorem rowEval16803 (x : Key → ℝ) : Integer.Sparse.eval row16803 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck16803, Integer.Sparse.eval_collectBalanced, rawRowCheck16803]

def rawRow16804 : Integer.Sparse Key := [(key916, 4), (key705, 4), (key891, 4), (key886, -2), (key916, -2), (key710, -2), (key895, -2), (key705, -2), (key859, -2), (key916, -2), (key955, -2), (key718, -2), (key948, -2), (key714, -2), (key891, -2), (key916, 4), (key718, 4), (key895, 4)]

theorem rawRowCheck16804 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form5 = rawRow16804 := by decide +kernel

def row16804 : Integer.Sparse Key := [(key705, 2), (key710, -2), (key714, -2), (key718, 2), (key859, -2), (key886, -2), (key891, 2), (key895, 2), (key916, 4), (key948, -2), (key955, -2)]

theorem rowCheck16804 : row16804 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16804 := by decide +kernel

theorem rowEval16804 (x : Key → ℝ) : Integer.Sparse.eval row16804 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck16804, Integer.Sparse.eval_collectBalanced, rawRowCheck16804]

def rawRow16805 : Integer.Sparse Key := [(key916, 4), (key891, 4), (key705, 4), (key916, -2), (key886, -2), (key895, -2), (key710, -2), (key859, -2), (key705, -2), (key955, -2), (key916, -2), (key948, -2), (key718, -2), (key891, -2), (key714, -2), (key916, 4), (key895, 4), (key718, 4)]

theorem rawRowCheck16805 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form5 = rawRow16805 := by decide +kernel

def row16805 : Integer.Sparse Key := [(key705, 2), (key710, -2), (key714, -2), (key718, 2), (key859, -2), (key886, -2), (key891, 2), (key895, 2), (key916, 4), (key948, -2), (key955, -2)]

theorem rowCheck16805 : row16805 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16805 := by decide +kernel

theorem rowEval16805 (x : Key → ℝ) : Integer.Sparse.eval row16805 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck16805, Integer.Sparse.eval_collectBalanced, rawRowCheck16805]

def rawRow16806 : Integer.Sparse Key := [(key705, 4), (key891, 4), (key916, 4), (key714, -2), (key718, -2), (key891, -2), (key916, -2), (key948, -2), (key955, -2), (key705, -2), (key710, -2), (key859, -2), (key886, -2), (key895, -2), (key916, -2), (key718, 4), (key895, 4), (key916, 4)]

theorem rawRowCheck16806 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form5 = rawRow16806 := by decide +kernel

def row16806 : Integer.Sparse Key := [(key705, 2), (key710, -2), (key714, -2), (key718, 2), (key859, -2), (key886, -2), (key891, 2), (key895, 2), (key916, 4), (key948, -2), (key955, -2)]

theorem rowCheck16806 : row16806 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16806 := by decide +kernel

theorem rowEval16806 (x : Key → ℝ) : Integer.Sparse.eval row16806 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck16806, Integer.Sparse.eval_collectBalanced, rawRowCheck16806]

def rawRow16807 : Integer.Sparse Key := [(key705, 4), (key916, 4), (key891, 4), (key718, -2), (key714, -2), (key916, -2), (key891, -2), (key955, -2), (key948, -2), (key710, -2), (key705, -2), (key886, -2), (key859, -2), (key916, -2), (key895, -2), (key718, 4), (key916, 4), (key895, 4)]

theorem rawRowCheck16807 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form5 = rawRow16807 := by decide +kernel

def row16807 : Integer.Sparse Key := [(key705, 2), (key710, -2), (key714, -2), (key718, 2), (key859, -2), (key886, -2), (key891, 2), (key895, 2), (key916, 4), (key948, -2), (key955, -2)]

theorem rowCheck16807 : row16807 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16807 := by decide +kernel

theorem rowEval16807 (x : Key → ℝ) : Integer.Sparse.eval row16807 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck16807, Integer.Sparse.eval_collectBalanced, rawRowCheck16807]

def rawRow16808 : Integer.Sparse Key := [(key891, 4), (key705, 4), (key916, 4), (key891, -2), (key948, -2), (key714, -2), (key955, -2), (key718, -2), (key916, -2), (key859, -2), (key895, -2), (key705, -2), (key916, -2), (key710, -2), (key886, -2), (key895, 4), (key718, 4), (key916, 4)]

theorem rawRowCheck16808 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form5 = rawRow16808 := by decide +kernel

def row16808 : Integer.Sparse Key := [(key705, 2), (key710, -2), (key714, -2), (key718, 2), (key859, -2), (key886, -2), (key891, 2), (key895, 2), (key916, 4), (key948, -2), (key955, -2)]

theorem rowCheck16808 : row16808 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16808 := by decide +kernel

theorem rowEval16808 (x : Key → ℝ) : Integer.Sparse.eval row16808 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck16808, Integer.Sparse.eval_collectBalanced, rawRowCheck16808]

def rawRow16809 : Integer.Sparse Key := [(key891, 4), (key916, 4), (key705, 4), (key948, -2), (key891, -2), (key955, -2), (key714, -2), (key916, -2), (key718, -2), (key895, -2), (key859, -2), (key916, -2), (key705, -2), (key886, -2), (key710, -2), (key895, 4), (key916, 4), (key718, 4)]

theorem rawRowCheck16809 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form5 = rawRow16809 := by decide +kernel

def row16809 : Integer.Sparse Key := [(key705, 2), (key710, -2), (key714, -2), (key718, 2), (key859, -2), (key886, -2), (key891, 2), (key895, 2), (key916, 4), (key948, -2), (key955, -2)]

theorem rowCheck16809 : row16809 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16809 := by decide +kernel

theorem rowEval16809 (x : Key → ℝ) : Integer.Sparse.eval row16809 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck16809, Integer.Sparse.eval_collectBalanced, rawRowCheck16809]

def rawRow16810 : Integer.Sparse Key := [(key916, 4), (key705, 4), (key891, 4), (key916, -2), (key955, -2), (key718, -2), (key948, -2), (key714, -2), (key891, -2), (key886, -2), (key916, -2), (key710, -2), (key895, -2), (key705, -2), (key859, -2), (key916, 4), (key718, 4), (key895, 4)]

theorem rawRowCheck16810 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form5 = rawRow16810 := by decide +kernel

def row16810 : Integer.Sparse Key := [(key705, 2), (key710, -2), (key714, -2), (key718, 2), (key859, -2), (key886, -2), (key891, 2), (key895, 2), (key916, 4), (key948, -2), (key955, -2)]

theorem rowCheck16810 : row16810 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16810 := by decide +kernel

theorem rowEval16810 (x : Key → ℝ) : Integer.Sparse.eval row16810 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck16810, Integer.Sparse.eval_collectBalanced, rawRowCheck16810]

def rawRow16811 : Integer.Sparse Key := [(key916, 4), (key891, 4), (key705, 4), (key955, -2), (key916, -2), (key948, -2), (key718, -2), (key891, -2), (key714, -2), (key916, -2), (key886, -2), (key895, -2), (key710, -2), (key859, -2), (key705, -2), (key916, 4), (key895, 4), (key718, 4)]

theorem rawRowCheck16811 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form5 = rawRow16811 := by decide +kernel

def row16811 : Integer.Sparse Key := [(key705, 2), (key710, -2), (key714, -2), (key718, 2), (key859, -2), (key886, -2), (key891, 2), (key895, 2), (key916, 4), (key948, -2), (key955, -2)]

theorem rowCheck16811 : row16811 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16811 := by decide +kernel

theorem rowEval16811 (x : Key → ℝ) : Integer.Sparse.eval row16811 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck16811, Integer.Sparse.eval_collectBalanced, rawRowCheck16811]

def rawRow16812 : Integer.Sparse Key := [(key714, 4), (key714, 4), (key955, 4), (key705, -2), (key718, -2), (key705, -2), (key916, -2), (key718, -2), (key916, -2), (key705, -2), (key718, -2), (key705, -2), (key916, -2), (key718, -2), (key916, -2), (key710, 4), (key710, 4), (key886, 4)]

theorem rawRowCheck16812 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form5 = rawRow16812 := by decide +kernel

def row16812 : Integer.Sparse Key := [(key705, -8), (key710, 8), (key714, 8), (key718, -8), (key886, 4), (key916, -8), (key955, 4)]

theorem rowCheck16812 : row16812 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16812 := by decide +kernel

theorem rowEval16812 (x : Key → ℝ) : Integer.Sparse.eval row16812 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck16812, Integer.Sparse.eval_collectBalanced, rawRowCheck16812]

def rawRow16813 : Integer.Sparse Key := [(key714, 4), (key955, 4), (key714, 4), (key718, -2), (key705, -2), (key916, -2), (key705, -2), (key916, -2), (key718, -2), (key718, -2), (key705, -2), (key916, -2), (key705, -2), (key916, -2), (key718, -2), (key710, 4), (key886, 4), (key710, 4)]

theorem rawRowCheck16813 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form5 = rawRow16813 := by decide +kernel

def row16813 : Integer.Sparse Key := [(key705, -8), (key710, 8), (key714, 8), (key718, -8), (key886, 4), (key916, -8), (key955, 4)]

theorem rowCheck16813 : row16813 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16813 := by decide +kernel

theorem rowEval16813 (x : Key → ℝ) : Integer.Sparse.eval row16813 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck16813, Integer.Sparse.eval_collectBalanced, rawRowCheck16813]

def rawRow16814 : Integer.Sparse Key := [(key955, 4), (key714, 4), (key714, 4), (key916, -2), (key916, -2), (key718, -2), (key718, -2), (key705, -2), (key705, -2), (key916, -2), (key916, -2), (key718, -2), (key718, -2), (key705, -2), (key705, -2), (key886, 4), (key710, 4), (key710, 4)]

theorem rawRowCheck16814 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form5 = rawRow16814 := by decide +kernel

def row16814 : Integer.Sparse Key := [(key705, -8), (key710, 8), (key714, 8), (key718, -8), (key886, 4), (key916, -8), (key955, 4)]

theorem rowCheck16814 : row16814 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16814 := by decide +kernel

theorem rowEval16814 (x : Key → ℝ) : Integer.Sparse.eval row16814 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck16814, Integer.Sparse.eval_collectBalanced, rawRowCheck16814]

def rawRow16815 : Integer.Sparse Key := [(key2146, -1), (key2152, -1), (key2146, -1), (key2166, -1), (key2152, -1), (key2166, -1), (key2194, 2), (key2194, 2), (key2200, 2), (key2146, -1), (key2152, -1), (key2146, -1), (key2166, -1), (key2152, -1), (key2166, -1), (key2239, 2), (key2246, 2), (key2239, 2), (key2253, 2), (key2246, 2), (key2253, 2), (key2303, -1), (key2305, -1), (key2303, -1), (key2310, -1), (key2305, -1), (key2310, -1), (key2194, 2), (key2194, 2), (key2200, 2), (key2303, -1), (key2305, -1), (key2303, -1), (key2310, -1), (key2305, -1), (key2310, -1)]

theorem rawRowCheck16815 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form6 = rawRow16815 := by decide +kernel

def row16815 : Integer.Sparse Key := [(key2146, -4), (key2152, -4), (key2166, -4), (key2194, 8), (key2200, 4), (key2239, 4), (key2246, 4), (key2253, 4), (key2303, -4), (key2305, -4), (key2310, -4)]

theorem rowCheck16815 : row16815 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16815 := by decide +kernel

theorem rowEval16815 (x : Key → ℝ) : Integer.Sparse.eval row16815 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form6) x := by
  rw [rowCheck16815, Integer.Sparse.eval_collectBalanced, rawRowCheck16815]

def rawRow16816 : Integer.Sparse Key := [(key2152, -1), (key2146, -1), (key2166, -1), (key2146, -1), (key2166, -1), (key2152, -1), (key2194, 2), (key2200, 2), (key2194, 2), (key2152, -1), (key2146, -1), (key2166, -1), (key2146, -1), (key2166, -1), (key2152, -1), (key2246, 2), (key2239, 2), (key2253, 2), (key2239, 2), (key2253, 2), (key2246, 2), (key2305, -1), (key2303, -1), (key2310, -1), (key2303, -1), (key2310, -1), (key2305, -1), (key2194, 2), (key2200, 2), (key2194, 2), (key2305, -1), (key2303, -1), (key2310, -1), (key2303, -1), (key2310, -1), (key2305, -1)]

theorem rawRowCheck16816 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form6 = rawRow16816 := by decide +kernel

def row16816 : Integer.Sparse Key := [(key2146, -4), (key2152, -4), (key2166, -4), (key2194, 8), (key2200, 4), (key2239, 4), (key2246, 4), (key2253, 4), (key2303, -4), (key2305, -4), (key2310, -4)]

theorem rowCheck16816 : row16816 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16816 := by decide +kernel

theorem rowEval16816 (x : Key → ℝ) : Integer.Sparse.eval row16816 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck16816, Integer.Sparse.eval_collectBalanced, rawRowCheck16816]

def rawRow16817 : Integer.Sparse Key := [(key2166, -1), (key2166, -1), (key2152, -1), (key2152, -1), (key2146, -1), (key2146, -1), (key2200, 2), (key2194, 2), (key2194, 2), (key2166, -1), (key2166, -1), (key2152, -1), (key2152, -1), (key2146, -1), (key2146, -1), (key2253, 2), (key2253, 2), (key2246, 2), (key2246, 2), (key2239, 2), (key2239, 2), (key2310, -1), (key2310, -1), (key2305, -1), (key2305, -1), (key2303, -1), (key2303, -1), (key2200, 2), (key2194, 2), (key2194, 2), (key2310, -1), (key2310, -1), (key2305, -1), (key2305, -1), (key2303, -1), (key2303, -1)]

theorem rawRowCheck16817 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form6 = rawRow16817 := by decide +kernel

def row16817 : Integer.Sparse Key := [(key2146, -4), (key2152, -4), (key2166, -4), (key2194, 8), (key2200, 4), (key2239, 4), (key2246, 4), (key2253, 4), (key2303, -4), (key2305, -4), (key2310, -4)]

theorem rowCheck16817 : row16817 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16817 := by decide +kernel

theorem rowEval16817 (x : Key → ℝ) : Integer.Sparse.eval row16817 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck16817, Integer.Sparse.eval_collectBalanced, rawRowCheck16817]

def rawRow16818 : Integer.Sparse Key := [(key2027, -1), (key2033, -1), (key2146, -1), (key2166, -1), (key2194, -1), (key2200, -1), (key2033, 2), (key2152, 2), (key2166, 2), (key2057, -1), (key2063, -1), (key2239, -1), (key2253, -1), (key2303, -1), (key2310, -1), (key2057, 2), (key2069, 2), (key2146, 2), (key2166, 2), (key2305, 2), (key2310, 2), (key2063, -1), (key2069, -1), (key2152, -1), (key2166, -1), (key2246, -1), (key2253, -1), (key2092, 2), (key2303, 2), (key2310, 2), (key2092, -1), (key2095, -1), (key2194, -1), (key2200, -1), (key2305, -1), (key2310, -1)]

theorem rawRowCheck16818 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form6 = rawRow16818 := by decide +kernel

def row16818 : Integer.Sparse Key := [(key2027, -1), (key2033, 1), (key2057, 1), (key2063, -2), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 1), (key2152, 1), (key2166, 2), (key2194, -2), (key2200, -2), (key2239, -1), (key2246, -1), (key2253, -2), (key2303, 1), (key2305, 1), (key2310, 2)]

theorem rowCheck16818 : row16818 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16818 := by decide +kernel

theorem rowEval16818 (x : Key → ℝ) : Integer.Sparse.eval row16818 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form6) x := by
  rw [rowCheck16818, Integer.Sparse.eval_collectBalanced, rawRowCheck16818]

def rawRow16819 : Integer.Sparse Key := [(key2033, -1), (key2027, -1), (key2166, -1), (key2146, -1), (key2200, -1), (key2194, -1), (key2033, 2), (key2166, 2), (key2152, 2), (key2063, -1), (key2057, -1), (key2253, -1), (key2239, -1), (key2310, -1), (key2303, -1), (key2069, 2), (key2057, 2), (key2166, 2), (key2146, 2), (key2310, 2), (key2305, 2), (key2069, -1), (key2063, -1), (key2166, -1), (key2152, -1), (key2253, -1), (key2246, -1), (key2092, 2), (key2310, 2), (key2303, 2), (key2095, -1), (key2092, -1), (key2200, -1), (key2194, -1), (key2310, -1), (key2305, -1)]

theorem rawRowCheck16819 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form6 = rawRow16819 := by decide +kernel

def row16819 : Integer.Sparse Key := [(key2027, -1), (key2033, 1), (key2057, 1), (key2063, -2), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 1), (key2152, 1), (key2166, 2), (key2194, -2), (key2200, -2), (key2239, -1), (key2246, -1), (key2253, -2), (key2303, 1), (key2305, 1), (key2310, 2)]

theorem rowCheck16819 : row16819 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16819 := by decide +kernel

theorem rowEval16819 (x : Key → ℝ) : Integer.Sparse.eval row16819 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck16819, Integer.Sparse.eval_collectBalanced, rawRowCheck16819]

def rawRow16820 : Integer.Sparse Key := [(key2146, -1), (key2194, -1), (key2027, -1), (key2200, -1), (key2033, -1), (key2166, -1), (key2152, 2), (key2033, 2), (key2166, 2), (key2239, -1), (key2303, -1), (key2057, -1), (key2310, -1), (key2063, -1), (key2253, -1), (key2146, 2), (key2305, 2), (key2057, 2), (key2310, 2), (key2069, 2), (key2166, 2), (key2152, -1), (key2246, -1), (key2063, -1), (key2253, -1), (key2069, -1), (key2166, -1), (key2303, 2), (key2092, 2), (key2310, 2), (key2194, -1), (key2305, -1), (key2092, -1), (key2310, -1), (key2095, -1), (key2200, -1)]

theorem rawRowCheck16820 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form6 = rawRow16820 := by decide +kernel

def row16820 : Integer.Sparse Key := [(key2027, -1), (key2033, 1), (key2057, 1), (key2063, -2), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 1), (key2152, 1), (key2166, 2), (key2194, -2), (key2200, -2), (key2239, -1), (key2246, -1), (key2253, -2), (key2303, 1), (key2305, 1), (key2310, 2)]

theorem rowCheck16820 : row16820 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16820 := by decide +kernel

theorem rowEval16820 (x : Key → ℝ) : Integer.Sparse.eval row16820 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form6) x := by
  rw [rowCheck16820, Integer.Sparse.eval_collectBalanced, rawRowCheck16820]

def rawRow16821 : Integer.Sparse Key := [(key2194, -1), (key2146, -1), (key2200, -1), (key2027, -1), (key2166, -1), (key2033, -1), (key2152, 2), (key2166, 2), (key2033, 2), (key2303, -1), (key2239, -1), (key2310, -1), (key2057, -1), (key2253, -1), (key2063, -1), (key2305, 2), (key2146, 2), (key2310, 2), (key2057, 2), (key2166, 2), (key2069, 2), (key2246, -1), (key2152, -1), (key2253, -1), (key2063, -1), (key2166, -1), (key2069, -1), (key2303, 2), (key2310, 2), (key2092, 2), (key2305, -1), (key2194, -1), (key2310, -1), (key2092, -1), (key2200, -1), (key2095, -1)]

theorem rawRowCheck16821 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form6 = rawRow16821 := by decide +kernel

def row16821 : Integer.Sparse Key := [(key2027, -1), (key2033, 1), (key2057, 1), (key2063, -2), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 1), (key2152, 1), (key2166, 2), (key2194, -2), (key2200, -2), (key2239, -1), (key2246, -1), (key2253, -2), (key2303, 1), (key2305, 1), (key2310, 2)]

theorem rowCheck16821 : row16821 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16821 := by decide +kernel

theorem rowEval16821 (x : Key → ℝ) : Integer.Sparse.eval row16821 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck16821, Integer.Sparse.eval_collectBalanced, rawRowCheck16821]

def rawRow16822 : Integer.Sparse Key := [(key2166, -1), (key2200, -1), (key2033, -1), (key2194, -1), (key2027, -1), (key2146, -1), (key2166, 2), (key2033, 2), (key2152, 2), (key2253, -1), (key2310, -1), (key2063, -1), (key2303, -1), (key2057, -1), (key2239, -1), (key2166, 2), (key2310, 2), (key2069, 2), (key2305, 2), (key2057, 2), (key2146, 2), (key2166, -1), (key2253, -1), (key2069, -1), (key2246, -1), (key2063, -1), (key2152, -1), (key2310, 2), (key2092, 2), (key2303, 2), (key2200, -1), (key2310, -1), (key2095, -1), (key2305, -1), (key2092, -1), (key2194, -1)]

theorem rawRowCheck16822 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form6 = rawRow16822 := by decide +kernel

def row16822 : Integer.Sparse Key := [(key2027, -1), (key2033, 1), (key2057, 1), (key2063, -2), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 1), (key2152, 1), (key2166, 2), (key2194, -2), (key2200, -2), (key2239, -1), (key2246, -1), (key2253, -2), (key2303, 1), (key2305, 1), (key2310, 2)]

theorem rowCheck16822 : row16822 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16822 := by decide +kernel

theorem rowEval16822 (x : Key → ℝ) : Integer.Sparse.eval row16822 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck16822, Integer.Sparse.eval_collectBalanced, rawRowCheck16822]

def rawRow16823 : Integer.Sparse Key := [(key2200, -1), (key2166, -1), (key2194, -1), (key2033, -1), (key2146, -1), (key2027, -1), (key2166, 2), (key2152, 2), (key2033, 2), (key2310, -1), (key2253, -1), (key2303, -1), (key2063, -1), (key2239, -1), (key2057, -1), (key2310, 2), (key2166, 2), (key2305, 2), (key2069, 2), (key2146, 2), (key2057, 2), (key2253, -1), (key2166, -1), (key2246, -1), (key2069, -1), (key2152, -1), (key2063, -1), (key2310, 2), (key2303, 2), (key2092, 2), (key2310, -1), (key2200, -1), (key2305, -1), (key2095, -1), (key2194, -1), (key2092, -1)]

theorem rawRowCheck16823 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form6 = rawRow16823 := by decide +kernel

def row16823 : Integer.Sparse Key := [(key2027, -1), (key2033, 1), (key2057, 1), (key2063, -2), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 1), (key2152, 1), (key2166, 2), (key2194, -2), (key2200, -2), (key2239, -1), (key2246, -1), (key2253, -2), (key2303, 1), (key2305, 1), (key2310, 2)]

theorem rowCheck16823 : row16823 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16823 := by decide +kernel

theorem rowEval16823 (x : Key → ℝ) : Integer.Sparse.eval row16823 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck16823, Integer.Sparse.eval_collectBalanced, rawRowCheck16823]

def rawRow16824 : Integer.Sparse Key := [(key2057, -1), (key2063, -1), (key2239, -1), (key2253, -1), (key2303, -1), (key2310, -1), (key2092, 2), (key2303, 2), (key2310, 2), (key2027, -1), (key2033, -1), (key2146, -1), (key2166, -1), (key2194, -1), (key2200, -1), (key2057, 2), (key2069, 2), (key2146, 2), (key2166, 2), (key2305, 2), (key2310, 2), (key2092, -1), (key2095, -1), (key2194, -1), (key2200, -1), (key2305, -1), (key2310, -1), (key2033, 2), (key2152, 2), (key2166, 2), (key2063, -1), (key2069, -1), (key2152, -1), (key2166, -1), (key2246, -1), (key2253, -1)]

theorem rawRowCheck16824 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form6 = rawRow16824 := by decide +kernel

def row16824 : Integer.Sparse Key := [(key2027, -1), (key2033, 1), (key2057, 1), (key2063, -2), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 1), (key2152, 1), (key2166, 2), (key2194, -2), (key2200, -2), (key2239, -1), (key2246, -1), (key2253, -2), (key2303, 1), (key2305, 1), (key2310, 2)]

theorem rowCheck16824 : row16824 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16824 := by decide +kernel

theorem rowEval16824 (x : Key → ℝ) : Integer.Sparse.eval row16824 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form6) x := by
  rw [rowCheck16824, Integer.Sparse.eval_collectBalanced, rawRowCheck16824]

def rawRow16825 : Integer.Sparse Key := [(key2063, -1), (key2057, -1), (key2253, -1), (key2239, -1), (key2310, -1), (key2303, -1), (key2092, 2), (key2310, 2), (key2303, 2), (key2033, -1), (key2027, -1), (key2166, -1), (key2146, -1), (key2200, -1), (key2194, -1), (key2069, 2), (key2057, 2), (key2166, 2), (key2146, 2), (key2310, 2), (key2305, 2), (key2095, -1), (key2092, -1), (key2200, -1), (key2194, -1), (key2310, -1), (key2305, -1), (key2033, 2), (key2166, 2), (key2152, 2), (key2069, -1), (key2063, -1), (key2166, -1), (key2152, -1), (key2253, -1), (key2246, -1)]

theorem rawRowCheck16825 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form6 = rawRow16825 := by decide +kernel

def row16825 : Integer.Sparse Key := [(key2027, -1), (key2033, 1), (key2057, 1), (key2063, -2), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 1), (key2152, 1), (key2166, 2), (key2194, -2), (key2200, -2), (key2239, -1), (key2246, -1), (key2253, -2), (key2303, 1), (key2305, 1), (key2310, 2)]

theorem rowCheck16825 : row16825 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16825 := by decide +kernel

theorem rowEval16825 (x : Key → ℝ) : Integer.Sparse.eval row16825 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck16825, Integer.Sparse.eval_collectBalanced, rawRowCheck16825]

def rawRow16826 : Integer.Sparse Key := [(key2239, -1), (key2303, -1), (key2057, -1), (key2310, -1), (key2063, -1), (key2253, -1), (key2303, 2), (key2092, 2), (key2310, 2), (key2146, -1), (key2194, -1), (key2027, -1), (key2200, -1), (key2033, -1), (key2166, -1), (key2146, 2), (key2305, 2), (key2057, 2), (key2310, 2), (key2069, 2), (key2166, 2), (key2194, -1), (key2305, -1), (key2092, -1), (key2310, -1), (key2095, -1), (key2200, -1), (key2152, 2), (key2033, 2), (key2166, 2), (key2152, -1), (key2246, -1), (key2063, -1), (key2253, -1), (key2069, -1), (key2166, -1)]

theorem rawRowCheck16826 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form6 = rawRow16826 := by decide +kernel

def row16826 : Integer.Sparse Key := [(key2027, -1), (key2033, 1), (key2057, 1), (key2063, -2), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 1), (key2152, 1), (key2166, 2), (key2194, -2), (key2200, -2), (key2239, -1), (key2246, -1), (key2253, -2), (key2303, 1), (key2305, 1), (key2310, 2)]

theorem rowCheck16826 : row16826 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16826 := by decide +kernel

theorem rowEval16826 (x : Key → ℝ) : Integer.Sparse.eval row16826 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form6) x := by
  rw [rowCheck16826, Integer.Sparse.eval_collectBalanced, rawRowCheck16826]

def rawRow16827 : Integer.Sparse Key := [(key2303, -1), (key2239, -1), (key2310, -1), (key2057, -1), (key2253, -1), (key2063, -1), (key2303, 2), (key2310, 2), (key2092, 2), (key2194, -1), (key2146, -1), (key2200, -1), (key2027, -1), (key2166, -1), (key2033, -1), (key2305, 2), (key2146, 2), (key2310, 2), (key2057, 2), (key2166, 2), (key2069, 2), (key2305, -1), (key2194, -1), (key2310, -1), (key2092, -1), (key2200, -1), (key2095, -1), (key2152, 2), (key2166, 2), (key2033, 2), (key2246, -1), (key2152, -1), (key2253, -1), (key2063, -1), (key2166, -1), (key2069, -1)]

theorem rawRowCheck16827 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form6 = rawRow16827 := by decide +kernel

def row16827 : Integer.Sparse Key := [(key2027, -1), (key2033, 1), (key2057, 1), (key2063, -2), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 1), (key2152, 1), (key2166, 2), (key2194, -2), (key2200, -2), (key2239, -1), (key2246, -1), (key2253, -2), (key2303, 1), (key2305, 1), (key2310, 2)]

theorem rowCheck16827 : row16827 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16827 := by decide +kernel

theorem rowEval16827 (x : Key → ℝ) : Integer.Sparse.eval row16827 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck16827, Integer.Sparse.eval_collectBalanced, rawRowCheck16827]

def rawRow16828 : Integer.Sparse Key := [(key2253, -1), (key2310, -1), (key2063, -1), (key2303, -1), (key2057, -1), (key2239, -1), (key2310, 2), (key2092, 2), (key2303, 2), (key2166, -1), (key2200, -1), (key2033, -1), (key2194, -1), (key2027, -1), (key2146, -1), (key2166, 2), (key2310, 2), (key2069, 2), (key2305, 2), (key2057, 2), (key2146, 2), (key2200, -1), (key2310, -1), (key2095, -1), (key2305, -1), (key2092, -1), (key2194, -1), (key2166, 2), (key2033, 2), (key2152, 2), (key2166, -1), (key2253, -1), (key2069, -1), (key2246, -1), (key2063, -1), (key2152, -1)]

theorem rawRowCheck16828 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form6 = rawRow16828 := by decide +kernel

def row16828 : Integer.Sparse Key := [(key2027, -1), (key2033, 1), (key2057, 1), (key2063, -2), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 1), (key2152, 1), (key2166, 2), (key2194, -2), (key2200, -2), (key2239, -1), (key2246, -1), (key2253, -2), (key2303, 1), (key2305, 1), (key2310, 2)]

theorem rowCheck16828 : row16828 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16828 := by decide +kernel

theorem rowEval16828 (x : Key → ℝ) : Integer.Sparse.eval row16828 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck16828, Integer.Sparse.eval_collectBalanced, rawRowCheck16828]

def rawRow16829 : Integer.Sparse Key := [(key2310, -1), (key2253, -1), (key2303, -1), (key2063, -1), (key2239, -1), (key2057, -1), (key2310, 2), (key2303, 2), (key2092, 2), (key2200, -1), (key2166, -1), (key2194, -1), (key2033, -1), (key2146, -1), (key2027, -1), (key2310, 2), (key2166, 2), (key2305, 2), (key2069, 2), (key2146, 2), (key2057, 2), (key2310, -1), (key2200, -1), (key2305, -1), (key2095, -1), (key2194, -1), (key2092, -1), (key2166, 2), (key2152, 2), (key2033, 2), (key2253, -1), (key2166, -1), (key2246, -1), (key2069, -1), (key2152, -1), (key2063, -1)]

theorem rawRowCheck16829 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form6 = rawRow16829 := by decide +kernel

def row16829 : Integer.Sparse Key := [(key2027, -1), (key2033, 1), (key2057, 1), (key2063, -2), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 1), (key2152, 1), (key2166, 2), (key2194, -2), (key2200, -2), (key2239, -1), (key2246, -1), (key2253, -2), (key2303, 1), (key2305, 1), (key2310, 2)]

theorem rowCheck16829 : row16829 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16829 := by decide +kernel

theorem rowEval16829 (x : Key → ℝ) : Integer.Sparse.eval row16829 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck16829, Integer.Sparse.eval_collectBalanced, rawRowCheck16829]

def rawRow16830 : Integer.Sparse Key := [(key2057, -1), (key2092, -1), (key2057, -1), (key2310, -1), (key2092, -1), (key2310, -1), (key2063, 2), (key2063, 2), (key2253, 2), (key2057, -1), (key2092, -1), (key2057, -1), (key2310, -1), (key2092, -1), (key2310, -1), (key2027, 2), (key2095, 2), (key2027, 2), (key2200, 2), (key2095, 2), (key2200, 2), (key2033, -1), (key2069, -1), (key2033, -1), (key2166, -1), (key2069, -1), (key2166, -1), (key2063, 2), (key2063, 2), (key2253, 2), (key2033, -1), (key2069, -1), (key2033, -1), (key2166, -1), (key2069, -1), (key2166, -1)]

theorem rawRowCheck16830 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form6 = rawRow16830 := by decide +kernel

def row16830 : Integer.Sparse Key := [(key2027, 4), (key2033, -4), (key2057, -4), (key2063, 8), (key2069, -4), (key2092, -4), (key2095, 4), (key2166, -4), (key2200, 4), (key2253, 4), (key2310, -4)]

theorem rowCheck16830 : row16830 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16830 := by decide +kernel

theorem rowEval16830 (x : Key → ℝ) : Integer.Sparse.eval row16830 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form6) x := by
  rw [rowCheck16830, Integer.Sparse.eval_collectBalanced, rawRowCheck16830]

def rawRow16831 : Integer.Sparse Key := [(key2092, -1), (key2057, -1), (key2310, -1), (key2057, -1), (key2310, -1), (key2092, -1), (key2063, 2), (key2253, 2), (key2063, 2), (key2092, -1), (key2057, -1), (key2310, -1), (key2057, -1), (key2310, -1), (key2092, -1), (key2095, 2), (key2027, 2), (key2200, 2), (key2027, 2), (key2200, 2), (key2095, 2), (key2069, -1), (key2033, -1), (key2166, -1), (key2033, -1), (key2166, -1), (key2069, -1), (key2063, 2), (key2253, 2), (key2063, 2), (key2069, -1), (key2033, -1), (key2166, -1), (key2033, -1), (key2166, -1), (key2069, -1)]

theorem rawRowCheck16831 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form6 = rawRow16831 := by decide +kernel

def row16831 : Integer.Sparse Key := [(key2027, 4), (key2033, -4), (key2057, -4), (key2063, 8), (key2069, -4), (key2092, -4), (key2095, 4), (key2166, -4), (key2200, 4), (key2253, 4), (key2310, -4)]

theorem rowCheck16831 : row16831 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16831 := by decide +kernel

theorem rowEval16831 (x : Key → ℝ) : Integer.Sparse.eval row16831 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck16831, Integer.Sparse.eval_collectBalanced, rawRowCheck16831]

def rawRow16832 : Integer.Sparse Key := [(key2310, -1), (key2310, -1), (key2092, -1), (key2092, -1), (key2057, -1), (key2057, -1), (key2253, 2), (key2063, 2), (key2063, 2), (key2310, -1), (key2310, -1), (key2092, -1), (key2092, -1), (key2057, -1), (key2057, -1), (key2200, 2), (key2200, 2), (key2095, 2), (key2095, 2), (key2027, 2), (key2027, 2), (key2166, -1), (key2166, -1), (key2069, -1), (key2069, -1), (key2033, -1), (key2033, -1), (key2253, 2), (key2063, 2), (key2063, 2), (key2166, -1), (key2166, -1), (key2069, -1), (key2069, -1), (key2033, -1), (key2033, -1)]

theorem rawRowCheck16832 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form6 = rawRow16832 := by decide +kernel

def row16832 : Integer.Sparse Key := [(key2027, 4), (key2033, -4), (key2057, -4), (key2063, 8), (key2069, -4), (key2092, -4), (key2095, 4), (key2166, -4), (key2200, 4), (key2253, 4), (key2310, -4)]

theorem rowCheck16832 : row16832 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16832 := by decide +kernel

theorem rowEval16832 (x : Key → ℝ) : Integer.Sparse.eval row16832 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck16832, Integer.Sparse.eval_collectBalanced, rawRowCheck16832]

def rawRow16833 : Integer.Sparse Key := [(key2115, 4), (key2115, 4), (key2120, 4), (key2157, -4), (key2160, -4), (key2160, -4), (key2157, -4), (key2160, -4), (key2160, -4), (key2249, 12)]

theorem rawRowCheck16833 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form7 = rawRow16833 := by decide +kernel

def row16833 : Integer.Sparse Key := [(key2115, 8), (key2120, 4), (key2157, -8), (key2160, -16), (key2249, 12)]

theorem rowCheck16833 : row16833 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16833 := by decide +kernel

theorem rowEval16833 (x : Key → ℝ) : Integer.Sparse.eval row16833 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck16833, Integer.Sparse.eval_collectBalanced, rawRowCheck16833]

def rawRow16834 : Integer.Sparse Key := [(key2115, 4), (key2120, 4), (key2115, 4), (key2160, -4), (key2157, -4), (key2160, -4), (key2160, -4), (key2157, -4), (key2160, -4), (key2249, 12)]

theorem rawRowCheck16834 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form7 = rawRow16834 := by decide +kernel

def row16834 : Integer.Sparse Key := [(key2115, 8), (key2120, 4), (key2157, -8), (key2160, -16), (key2249, 12)]

theorem rowCheck16834 : row16834 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16834 := by decide +kernel

theorem rowEval16834 (x : Key → ℝ) : Integer.Sparse.eval row16834 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck16834, Integer.Sparse.eval_collectBalanced, rawRowCheck16834]

def rawRow16835 : Integer.Sparse Key := [(key2120, 4), (key2115, 4), (key2115, 4), (key2160, -4), (key2160, -4), (key2157, -4), (key2160, -4), (key2160, -4), (key2157, -4), (key2249, 12)]

theorem rawRowCheck16835 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form7 = rawRow16835 := by decide +kernel

def row16835 : Integer.Sparse Key := [(key2115, 8), (key2120, 4), (key2157, -8), (key2160, -16), (key2249, 12)]

theorem rowCheck16835 : row16835 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16835 := by decide +kernel

theorem rowEval16835 (x : Key → ℝ) : Integer.Sparse.eval row16835 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck16835, Integer.Sparse.eval_collectBalanced, rawRowCheck16835]

def rawRow16836 : Integer.Sparse Key := [(key2115, 4), (key2157, 4), (key2160, 4), (key2115, -4), (key2120, -4), (key2160, -4), (key2157, -4), (key2160, -4), (key2249, -4), (key2160, 12)]

theorem rawRowCheck16836 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form7 = rawRow16836 := by decide +kernel

def row16836 : Integer.Sparse Key := [(key2120, -4), (key2160, 8), (key2249, -4)]

theorem rowCheck16836 : row16836 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16836 := by decide +kernel

theorem rowEval16836 (x : Key → ℝ) : Integer.Sparse.eval row16836 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck16836, Integer.Sparse.eval_collectBalanced, rawRowCheck16836]

def rawRow16837 : Integer.Sparse Key := [(key2115, 4), (key2160, 4), (key2157, 4), (key2120, -4), (key2115, -4), (key2160, -4), (key2160, -4), (key2157, -4), (key2249, -4), (key2160, 12)]

theorem rawRowCheck16837 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form7 = rawRow16837 := by decide +kernel

def row16837 : Integer.Sparse Key := [(key2120, -4), (key2160, 8), (key2249, -4)]

theorem rowCheck16837 : row16837 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16837 := by decide +kernel

theorem rowEval16837 (x : Key → ℝ) : Integer.Sparse.eval row16837 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck16837, Integer.Sparse.eval_collectBalanced, rawRowCheck16837]

def rawRow16838 : Integer.Sparse Key := [(key2157, 4), (key2115, 4), (key2160, 4), (key2115, -4), (key2160, -4), (key2120, -4), (key2157, -4), (key2249, -4), (key2160, -4), (key2160, 12)]

theorem rawRowCheck16838 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form7 = rawRow16838 := by decide +kernel

def row16838 : Integer.Sparse Key := [(key2120, -4), (key2160, 8), (key2249, -4)]

theorem rowCheck16838 : row16838 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16838 := by decide +kernel

theorem rowEval16838 (x : Key → ℝ) : Integer.Sparse.eval row16838 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck16838, Integer.Sparse.eval_collectBalanced, rawRowCheck16838]

def rawRow16839 : Integer.Sparse Key := [(key2157, 4), (key2160, 4), (key2115, 4), (key2160, -4), (key2115, -4), (key2120, -4), (key2249, -4), (key2157, -4), (key2160, -4), (key2160, 12)]

theorem rawRowCheck16839 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form7 = rawRow16839 := by decide +kernel

def row16839 : Integer.Sparse Key := [(key2120, -4), (key2160, 8), (key2249, -4)]

theorem rowCheck16839 : row16839 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16839 := by decide +kernel

theorem rowEval16839 (x : Key → ℝ) : Integer.Sparse.eval row16839 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck16839, Integer.Sparse.eval_collectBalanced, rawRowCheck16839]

def rawRow16840 : Integer.Sparse Key := [(key2160, 4), (key2115, 4), (key2157, 4), (key2120, -4), (key2160, -4), (key2115, -4), (key2160, -4), (key2249, -4), (key2157, -4), (key2160, 12)]

theorem rawRowCheck16840 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form7 = rawRow16840 := by decide +kernel

def row16840 : Integer.Sparse Key := [(key2120, -4), (key2160, 8), (key2249, -4)]

theorem rowCheck16840 : row16840 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16840 := by decide +kernel

theorem rowEval16840 (x : Key → ℝ) : Integer.Sparse.eval row16840 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck16840, Integer.Sparse.eval_collectBalanced, rawRowCheck16840]

def rawRow16841 : Integer.Sparse Key := [(key2160, 4), (key2157, 4), (key2115, 4), (key2160, -4), (key2120, -4), (key2115, -4), (key2249, -4), (key2160, -4), (key2157, -4), (key2160, 12)]

theorem rawRowCheck16841 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form7 = rawRow16841 := by decide +kernel

def row16841 : Integer.Sparse Key := [(key2120, -4), (key2160, 8), (key2249, -4)]

theorem rowCheck16841 : row16841 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16841 := by decide +kernel

theorem rowEval16841 (x : Key → ℝ) : Integer.Sparse.eval row16841 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck16841, Integer.Sparse.eval_collectBalanced, rawRowCheck16841]

def rawRow16842 : Integer.Sparse Key := [(key2115, 4), (key2157, 4), (key2160, 4), (key2157, -4), (key2160, -4), (key2249, -4), (key2115, -4), (key2120, -4), (key2160, -4), (key2160, 12)]

theorem rawRowCheck16842 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form7 = rawRow16842 := by decide +kernel

def row16842 : Integer.Sparse Key := [(key2120, -4), (key2160, 8), (key2249, -4)]

theorem rowCheck16842 : row16842 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16842 := by decide +kernel

theorem rowEval16842 (x : Key → ℝ) : Integer.Sparse.eval row16842 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck16842, Integer.Sparse.eval_collectBalanced, rawRowCheck16842]

def rawRow16843 : Integer.Sparse Key := [(key2115, 4), (key2160, 4), (key2157, 4), (key2160, -4), (key2157, -4), (key2249, -4), (key2120, -4), (key2115, -4), (key2160, -4), (key2160, 12)]

theorem rawRowCheck16843 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form7 = rawRow16843 := by decide +kernel

def row16843 : Integer.Sparse Key := [(key2120, -4), (key2160, 8), (key2249, -4)]

theorem rowCheck16843 : row16843 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16843 := by decide +kernel

theorem rowEval16843 (x : Key → ℝ) : Integer.Sparse.eval row16843 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck16843, Integer.Sparse.eval_collectBalanced, rawRowCheck16843]

def rawRow16844 : Integer.Sparse Key := [(key2157, 4), (key2115, 4), (key2160, 4), (key2157, -4), (key2249, -4), (key2160, -4), (key2115, -4), (key2160, -4), (key2120, -4), (key2160, 12)]

theorem rawRowCheck16844 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form7 = rawRow16844 := by decide +kernel

def row16844 : Integer.Sparse Key := [(key2120, -4), (key2160, 8), (key2249, -4)]

theorem rowCheck16844 : row16844 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16844 := by decide +kernel

theorem rowEval16844 (x : Key → ℝ) : Integer.Sparse.eval row16844 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck16844, Integer.Sparse.eval_collectBalanced, rawRowCheck16844]

def rawRow16845 : Integer.Sparse Key := [(key2157, 4), (key2160, 4), (key2115, 4), (key2249, -4), (key2157, -4), (key2160, -4), (key2160, -4), (key2115, -4), (key2120, -4), (key2160, 12)]

theorem rawRowCheck16845 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form7 = rawRow16845 := by decide +kernel

def row16845 : Integer.Sparse Key := [(key2120, -4), (key2160, 8), (key2249, -4)]

theorem rowCheck16845 : row16845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16845 := by decide +kernel

theorem rowEval16845 (x : Key → ℝ) : Integer.Sparse.eval row16845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck16845, Integer.Sparse.eval_collectBalanced, rawRowCheck16845]

def rawRow16846 : Integer.Sparse Key := [(key2160, 4), (key2115, 4), (key2157, 4), (key2160, -4), (key2249, -4), (key2157, -4), (key2120, -4), (key2160, -4), (key2115, -4), (key2160, 12)]

theorem rawRowCheck16846 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form7 = rawRow16846 := by decide +kernel

def row16846 : Integer.Sparse Key := [(key2120, -4), (key2160, 8), (key2249, -4)]

theorem rowCheck16846 : row16846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16846 := by decide +kernel

theorem rowEval16846 (x : Key → ℝ) : Integer.Sparse.eval row16846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck16846, Integer.Sparse.eval_collectBalanced, rawRowCheck16846]

def rawRow16847 : Integer.Sparse Key := [(key2160, 4), (key2157, 4), (key2115, 4), (key2249, -4), (key2160, -4), (key2157, -4), (key2160, -4), (key2120, -4), (key2115, -4), (key2160, 12)]

theorem rawRowCheck16847 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form7 = rawRow16847 := by decide +kernel

def row16847 : Integer.Sparse Key := [(key2120, -4), (key2160, 8), (key2249, -4)]

theorem rowCheck16847 : row16847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16847 := by decide +kernel

theorem rowEval16847 (x : Key → ℝ) : Integer.Sparse.eval row16847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck16847, Integer.Sparse.eval_collectBalanced, rawRowCheck16847]

def rawRow16848 : Integer.Sparse Key := [(key2157, 4), (key2157, 4), (key2249, 4), (key2115, -4), (key2160, -4), (key2160, -4), (key2115, -4), (key2160, -4), (key2160, -4), (key2120, 12)]

theorem rawRowCheck16848 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form7 = rawRow16848 := by decide +kernel

def row16848 : Integer.Sparse Key := [(key2115, -8), (key2120, 12), (key2157, 8), (key2160, -16), (key2249, 4)]

theorem rowCheck16848 : row16848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16848 := by decide +kernel

theorem rowEval16848 (x : Key → ℝ) : Integer.Sparse.eval row16848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck16848, Integer.Sparse.eval_collectBalanced, rawRowCheck16848]

def rawRow16849 : Integer.Sparse Key := [(key2157, 4), (key2249, 4), (key2157, 4), (key2160, -4), (key2115, -4), (key2160, -4), (key2160, -4), (key2115, -4), (key2160, -4), (key2120, 12)]

theorem rawRowCheck16849 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form7 = rawRow16849 := by decide +kernel

def row16849 : Integer.Sparse Key := [(key2115, -8), (key2120, 12), (key2157, 8), (key2160, -16), (key2249, 4)]

theorem rowCheck16849 : row16849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16849 := by decide +kernel

theorem rowEval16849 (x : Key → ℝ) : Integer.Sparse.eval row16849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck16849, Integer.Sparse.eval_collectBalanced, rawRowCheck16849]

def rawRow16850 : Integer.Sparse Key := [(key2249, 4), (key2157, 4), (key2157, 4), (key2160, -4), (key2160, -4), (key2115, -4), (key2160, -4), (key2160, -4), (key2115, -4), (key2120, 12)]

theorem rawRowCheck16850 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form7 = rawRow16850 := by decide +kernel

def row16850 : Integer.Sparse Key := [(key2115, -8), (key2120, 12), (key2157, 8), (key2160, -16), (key2249, 4)]

theorem rowCheck16850 : row16850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16850 := by decide +kernel

theorem rowEval16850 (x : Key → ℝ) : Integer.Sparse.eval row16850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck16850, Integer.Sparse.eval_collectBalanced, rawRowCheck16850]

def rawRow16851 : Integer.Sparse Key := [(key1987, -2), (key1990, -2), (key1990, -2), (key2000, 6), (key1987, -2), (key1990, -2), (key1990, -2), (key2232, 2), (key2235, 2), (key2232, 2), (key2256, 2), (key2235, 2), (key2256, 2), (key2269, -2), (key2269, -2), (key2292, -2), (key2000, 6), (key2269, -2), (key2269, -2), (key2292, -2)]

theorem rawRowCheck16851 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form8 = rawRow16851 := by decide +kernel

def row16851 : Integer.Sparse Key := [(key1987, -4), (key1990, -8), (key2000, 12), (key2232, 4), (key2235, 4), (key2256, 4), (key2269, -8), (key2292, -4)]

theorem rowCheck16851 : row16851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16851 := by decide +kernel

theorem rowEval16851 (x : Key → ℝ) : Integer.Sparse.eval row16851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck16851, Integer.Sparse.eval_collectBalanced, rawRowCheck16851]

def rawRow16852 : Integer.Sparse Key := [(key1990, -2), (key1987, -2), (key1990, -2), (key2000, 6), (key1990, -2), (key1987, -2), (key1990, -2), (key2235, 2), (key2232, 2), (key2256, 2), (key2232, 2), (key2256, 2), (key2235, 2), (key2269, -2), (key2292, -2), (key2269, -2), (key2000, 6), (key2269, -2), (key2292, -2), (key2269, -2)]

theorem rawRowCheck16852 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form8 = rawRow16852 := by decide +kernel

def row16852 : Integer.Sparse Key := [(key1987, -4), (key1990, -8), (key2000, 12), (key2232, 4), (key2235, 4), (key2256, 4), (key2269, -8), (key2292, -4)]

theorem rowCheck16852 : row16852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16852 := by decide +kernel

theorem rowEval16852 (x : Key → ℝ) : Integer.Sparse.eval row16852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck16852, Integer.Sparse.eval_collectBalanced, rawRowCheck16852]

def rawRow16853 : Integer.Sparse Key := [(key1990, -2), (key1990, -2), (key1987, -2), (key2000, 6), (key1990, -2), (key1990, -2), (key1987, -2), (key2256, 2), (key2256, 2), (key2235, 2), (key2235, 2), (key2232, 2), (key2232, 2), (key2292, -2), (key2269, -2), (key2269, -2), (key2000, 6), (key2292, -2), (key2269, -2), (key2269, -2)]

theorem rawRowCheck16853 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form8 = rawRow16853 := by decide +kernel

def row16853 : Integer.Sparse Key := [(key1987, -4), (key1990, -8), (key2000, 12), (key2232, 4), (key2235, 4), (key2256, 4), (key2269, -8), (key2292, -4)]

theorem rowCheck16853 : row16853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16853 := by decide +kernel

theorem rowEval16853 (x : Key → ℝ) : Integer.Sparse.eval row16853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck16853, Integer.Sparse.eval_collectBalanced, rawRowCheck16853]

def rawRow16854 : Integer.Sparse Key := [(key1987, -2), (key1990, -2), (key2000, -2), (key1990, 6), (key2232, -2), (key2235, -2), (key2269, -2), (key1987, 2), (key1990, 2), (key2232, 2), (key2256, 2), (key2269, 2), (key2292, 2), (key1990, -2), (key2235, -2), (key2256, -2), (key2269, 6), (key2000, -2), (key2269, -2), (key2292, -2)]

theorem rawRowCheck16854 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form8 = rawRow16854 := by decide +kernel

def row16854 : Integer.Sparse Key := [(key1990, 4), (key2000, -4), (key2235, -4), (key2269, 4)]

theorem rowCheck16854 : row16854 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16854 := by decide +kernel

theorem rowEval16854 (x : Key → ℝ) : Integer.Sparse.eval row16854 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck16854, Integer.Sparse.eval_collectBalanced, rawRowCheck16854]

def rawRow16855 : Integer.Sparse Key := [(key1990, -2), (key1987, -2), (key2000, -2), (key1990, 6), (key2235, -2), (key2232, -2), (key2269, -2), (key1990, 2), (key1987, 2), (key2256, 2), (key2232, 2), (key2292, 2), (key2269, 2), (key1990, -2), (key2256, -2), (key2235, -2), (key2269, 6), (key2000, -2), (key2292, -2), (key2269, -2)]

theorem rawRowCheck16855 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form8 = rawRow16855 := by decide +kernel

def row16855 : Integer.Sparse Key := [(key1990, 4), (key2000, -4), (key2235, -4), (key2269, 4)]

theorem rowCheck16855 : row16855 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16855 := by decide +kernel

theorem rowEval16855 (x : Key → ℝ) : Integer.Sparse.eval row16855 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck16855, Integer.Sparse.eval_collectBalanced, rawRowCheck16855]

def rawRow16856 : Integer.Sparse Key := [(key1987, -2), (key2000, -2), (key1990, -2), (key1990, 6), (key2232, -2), (key2269, -2), (key2235, -2), (key2232, 2), (key2269, 2), (key1987, 2), (key2292, 2), (key1990, 2), (key2256, 2), (key2235, -2), (key1990, -2), (key2256, -2), (key2269, 6), (key2269, -2), (key2000, -2), (key2292, -2)]

theorem rawRowCheck16856 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form8 = rawRow16856 := by decide +kernel

def row16856 : Integer.Sparse Key := [(key1990, 4), (key2000, -4), (key2235, -4), (key2269, 4)]

theorem rowCheck16856 : row16856 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16856 := by decide +kernel

theorem rowEval16856 (x : Key → ℝ) : Integer.Sparse.eval row16856 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck16856, Integer.Sparse.eval_collectBalanced, rawRowCheck16856]

def rawRow16857 : Integer.Sparse Key := [(key2000, -2), (key1987, -2), (key1990, -2), (key1990, 6), (key2269, -2), (key2232, -2), (key2235, -2), (key2269, 2), (key2232, 2), (key2292, 2), (key1987, 2), (key2256, 2), (key1990, 2), (key2235, -2), (key2256, -2), (key1990, -2), (key2269, 6), (key2269, -2), (key2292, -2), (key2000, -2)]

theorem rawRowCheck16857 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form8 = rawRow16857 := by decide +kernel

def row16857 : Integer.Sparse Key := [(key1990, 4), (key2000, -4), (key2235, -4), (key2269, 4)]

theorem rowCheck16857 : row16857 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16857 := by decide +kernel

theorem rowEval16857 (x : Key → ℝ) : Integer.Sparse.eval row16857 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck16857, Integer.Sparse.eval_collectBalanced, rawRowCheck16857]

def rawRow16858 : Integer.Sparse Key := [(key1990, -2), (key2000, -2), (key1987, -2), (key1990, 6), (key2235, -2), (key2269, -2), (key2232, -2), (key2256, 2), (key2292, 2), (key1990, 2), (key2269, 2), (key1987, 2), (key2232, 2), (key2256, -2), (key1990, -2), (key2235, -2), (key2269, 6), (key2292, -2), (key2000, -2), (key2269, -2)]

theorem rawRowCheck16858 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form8 = rawRow16858 := by decide +kernel

def row16858 : Integer.Sparse Key := [(key1990, 4), (key2000, -4), (key2235, -4), (key2269, 4)]

theorem rowCheck16858 : row16858 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16858 := by decide +kernel

theorem rowEval16858 (x : Key → ℝ) : Integer.Sparse.eval row16858 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck16858, Integer.Sparse.eval_collectBalanced, rawRowCheck16858]

def rawRow16859 : Integer.Sparse Key := [(key2000, -2), (key1990, -2), (key1987, -2), (key1990, 6), (key2269, -2), (key2235, -2), (key2232, -2), (key2292, 2), (key2256, 2), (key2269, 2), (key1990, 2), (key2232, 2), (key1987, 2), (key2256, -2), (key2235, -2), (key1990, -2), (key2269, 6), (key2292, -2), (key2269, -2), (key2000, -2)]

theorem rawRowCheck16859 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form8 = rawRow16859 := by decide +kernel

def row16859 : Integer.Sparse Key := [(key1990, 4), (key2000, -4), (key2235, -4), (key2269, 4)]

theorem rowCheck16859 : row16859 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16859 := by decide +kernel

theorem rowEval16859 (x : Key → ℝ) : Integer.Sparse.eval row16859 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck16859, Integer.Sparse.eval_collectBalanced, rawRowCheck16859]

def rawRow16860 : Integer.Sparse Key := [(key2232, -2), (key2235, -2), (key2269, -2), (key2269, 6), (key1987, -2), (key1990, -2), (key2000, -2), (key1987, 2), (key1990, 2), (key2232, 2), (key2256, 2), (key2269, 2), (key2292, 2), (key2000, -2), (key2269, -2), (key2292, -2), (key1990, 6), (key1990, -2), (key2235, -2), (key2256, -2)]

theorem rawRowCheck16860 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form8 = rawRow16860 := by decide +kernel

def row16860 : Integer.Sparse Key := [(key1990, 4), (key2000, -4), (key2235, -4), (key2269, 4)]

theorem rowCheck16860 : row16860 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16860 := by decide +kernel

theorem rowEval16860 (x : Key → ℝ) : Integer.Sparse.eval row16860 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck16860, Integer.Sparse.eval_collectBalanced, rawRowCheck16860]

def rawRow16861 : Integer.Sparse Key := [(key2235, -2), (key2232, -2), (key2269, -2), (key2269, 6), (key1990, -2), (key1987, -2), (key2000, -2), (key1990, 2), (key1987, 2), (key2256, 2), (key2232, 2), (key2292, 2), (key2269, 2), (key2000, -2), (key2292, -2), (key2269, -2), (key1990, 6), (key1990, -2), (key2256, -2), (key2235, -2)]

theorem rawRowCheck16861 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form8 = rawRow16861 := by decide +kernel

def row16861 : Integer.Sparse Key := [(key1990, 4), (key2000, -4), (key2235, -4), (key2269, 4)]

theorem rowCheck16861 : row16861 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16861 := by decide +kernel

theorem rowEval16861 (x : Key → ℝ) : Integer.Sparse.eval row16861 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck16861, Integer.Sparse.eval_collectBalanced, rawRowCheck16861]

def rawRow16862 : Integer.Sparse Key := [(key2232, -2), (key2269, -2), (key2235, -2), (key2269, 6), (key1987, -2), (key2000, -2), (key1990, -2), (key2232, 2), (key2269, 2), (key1987, 2), (key2292, 2), (key1990, 2), (key2256, 2), (key2269, -2), (key2000, -2), (key2292, -2), (key1990, 6), (key2235, -2), (key1990, -2), (key2256, -2)]

theorem rawRowCheck16862 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form8 = rawRow16862 := by decide +kernel

def row16862 : Integer.Sparse Key := [(key1990, 4), (key2000, -4), (key2235, -4), (key2269, 4)]

theorem rowCheck16862 : row16862 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16862 := by decide +kernel

theorem rowEval16862 (x : Key → ℝ) : Integer.Sparse.eval row16862 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck16862, Integer.Sparse.eval_collectBalanced, rawRowCheck16862]

def rawRow16863 : Integer.Sparse Key := [(key2269, -2), (key2232, -2), (key2235, -2), (key2269, 6), (key2000, -2), (key1987, -2), (key1990, -2), (key2269, 2), (key2232, 2), (key2292, 2), (key1987, 2), (key2256, 2), (key1990, 2), (key2269, -2), (key2292, -2), (key2000, -2), (key1990, 6), (key2235, -2), (key2256, -2), (key1990, -2)]

theorem rawRowCheck16863 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form8 = rawRow16863 := by decide +kernel

def row16863 : Integer.Sparse Key := [(key1990, 4), (key2000, -4), (key2235, -4), (key2269, 4)]

theorem rowCheck16863 : row16863 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16863 := by decide +kernel

theorem rowEval16863 (x : Key → ℝ) : Integer.Sparse.eval row16863 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck16863, Integer.Sparse.eval_collectBalanced, rawRowCheck16863]

def rawRow16864 : Integer.Sparse Key := [(key2235, -2), (key2269, -2), (key2232, -2), (key2269, 6), (key1990, -2), (key2000, -2), (key1987, -2), (key2256, 2), (key2292, 2), (key1990, 2), (key2269, 2), (key1987, 2), (key2232, 2), (key2292, -2), (key2000, -2), (key2269, -2), (key1990, 6), (key2256, -2), (key1990, -2), (key2235, -2)]

theorem rawRowCheck16864 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form8 = rawRow16864 := by decide +kernel

def row16864 : Integer.Sparse Key := [(key1990, 4), (key2000, -4), (key2235, -4), (key2269, 4)]

theorem rowCheck16864 : row16864 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16864 := by decide +kernel

theorem rowEval16864 (x : Key → ℝ) : Integer.Sparse.eval row16864 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck16864, Integer.Sparse.eval_collectBalanced, rawRowCheck16864]

def rawRow16865 : Integer.Sparse Key := [(key2269, -2), (key2235, -2), (key2232, -2), (key2269, 6), (key2000, -2), (key1990, -2), (key1987, -2), (key2292, 2), (key2256, 2), (key2269, 2), (key1990, 2), (key2232, 2), (key1987, 2), (key2292, -2), (key2269, -2), (key2000, -2), (key1990, 6), (key2256, -2), (key2235, -2), (key1990, -2)]

theorem rawRowCheck16865 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form8 = rawRow16865 := by decide +kernel

def row16865 : Integer.Sparse Key := [(key1990, 4), (key2000, -4), (key2235, -4), (key2269, 4)]

theorem rowCheck16865 : row16865 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16865 := by decide +kernel

theorem rowEval16865 (x : Key → ℝ) : Integer.Sparse.eval row16865 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck16865, Integer.Sparse.eval_collectBalanced, rawRowCheck16865]

def rawRow16866 : Integer.Sparse Key := [(key2232, -2), (key2269, -2), (key2269, -2), (key2235, 6), (key2232, -2), (key2269, -2), (key2269, -2), (key1987, 2), (key2000, 2), (key1987, 2), (key2292, 2), (key2000, 2), (key2292, 2), (key1990, -2), (key1990, -2), (key2256, -2), (key2235, 6), (key1990, -2), (key1990, -2), (key2256, -2)]

theorem rawRowCheck16866 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form8 = rawRow16866 := by decide +kernel

def row16866 : Integer.Sparse Key := [(key1987, 4), (key1990, -8), (key2000, 4), (key2232, -4), (key2235, 12), (key2256, -4), (key2269, -8), (key2292, 4)]

theorem rowCheck16866 : row16866 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16866 := by decide +kernel

theorem rowEval16866 (x : Key → ℝ) : Integer.Sparse.eval row16866 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck16866, Integer.Sparse.eval_collectBalanced, rawRowCheck16866]

def rawRow16867 : Integer.Sparse Key := [(key2269, -2), (key2232, -2), (key2269, -2), (key2235, 6), (key2269, -2), (key2232, -2), (key2269, -2), (key2000, 2), (key1987, 2), (key2292, 2), (key1987, 2), (key2292, 2), (key2000, 2), (key1990, -2), (key2256, -2), (key1990, -2), (key2235, 6), (key1990, -2), (key2256, -2), (key1990, -2)]

theorem rawRowCheck16867 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form8 = rawRow16867 := by decide +kernel

def row16867 : Integer.Sparse Key := [(key1987, 4), (key1990, -8), (key2000, 4), (key2232, -4), (key2235, 12), (key2256, -4), (key2269, -8), (key2292, 4)]

theorem rowCheck16867 : row16867 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16867 := by decide +kernel

theorem rowEval16867 (x : Key → ℝ) : Integer.Sparse.eval row16867 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck16867, Integer.Sparse.eval_collectBalanced, rawRowCheck16867]

def rawRow16868 : Integer.Sparse Key := [(key2269, -2), (key2269, -2), (key2232, -2), (key2235, 6), (key2269, -2), (key2269, -2), (key2232, -2), (key2292, 2), (key2292, 2), (key2000, 2), (key2000, 2), (key1987, 2), (key1987, 2), (key2256, -2), (key1990, -2), (key1990, -2), (key2235, 6), (key2256, -2), (key1990, -2), (key1990, -2)]

theorem rawRowCheck16868 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form8 = rawRow16868 := by decide +kernel

def row16868 : Integer.Sparse Key := [(key1987, 4), (key1990, -8), (key2000, 4), (key2232, -4), (key2235, 12), (key2256, -4), (key2269, -8), (key2292, 4)]

theorem rowCheck16868 : row16868 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16868 := by decide +kernel

theorem rowEval16868 (x : Key → ℝ) : Integer.Sparse.eval row16868 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck16868, Integer.Sparse.eval_collectBalanced, rawRowCheck16868]

def rawRow16869 : Integer.Sparse Key := [(key771, 4), (key771, 4), (key779, 4), (key798, -4), (key804, -4), (key804, -4), (key798, -4), (key804, -4), (key804, -4), (key873, 12)]

theorem rawRowCheck16869 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form9 = rawRow16869 := by decide +kernel

def row16869 : Integer.Sparse Key := [(key771, 8), (key779, 4), (key798, -8), (key804, -16), (key873, 12)]

theorem rowCheck16869 : row16869 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16869 := by decide +kernel

theorem rowEval16869 (x : Key → ℝ) : Integer.Sparse.eval row16869 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck16869, Integer.Sparse.eval_collectBalanced, rawRowCheck16869]

def rawRow16870 : Integer.Sparse Key := [(key771, 4), (key779, 4), (key771, 4), (key804, -4), (key798, -4), (key804, -4), (key804, -4), (key798, -4), (key804, -4), (key873, 12)]

theorem rawRowCheck16870 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form9 = rawRow16870 := by decide +kernel

def row16870 : Integer.Sparse Key := [(key771, 8), (key779, 4), (key798, -8), (key804, -16), (key873, 12)]

theorem rowCheck16870 : row16870 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16870 := by decide +kernel

theorem rowEval16870 (x : Key → ℝ) : Integer.Sparse.eval row16870 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck16870, Integer.Sparse.eval_collectBalanced, rawRowCheck16870]

def rawRow16871 : Integer.Sparse Key := [(key779, 4), (key771, 4), (key771, 4), (key804, -4), (key804, -4), (key798, -4), (key804, -4), (key804, -4), (key798, -4), (key873, 12)]

theorem rawRowCheck16871 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form9 = rawRow16871 := by decide +kernel

def row16871 : Integer.Sparse Key := [(key771, 8), (key779, 4), (key798, -8), (key804, -16), (key873, 12)]

theorem rowCheck16871 : row16871 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16871 := by decide +kernel

theorem rowEval16871 (x : Key → ℝ) : Integer.Sparse.eval row16871 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck16871, Integer.Sparse.eval_collectBalanced, rawRowCheck16871]

def rawRow16872 : Integer.Sparse Key := [(key771, 4), (key798, 4), (key804, 4), (key771, -4), (key779, -4), (key804, -4), (key798, -4), (key804, -4), (key873, -4), (key804, 12)]

theorem rawRowCheck16872 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form9 = rawRow16872 := by decide +kernel

def row16872 : Integer.Sparse Key := [(key779, -4), (key804, 8), (key873, -4)]

theorem rowCheck16872 : row16872 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16872 := by decide +kernel

theorem rowEval16872 (x : Key → ℝ) : Integer.Sparse.eval row16872 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck16872, Integer.Sparse.eval_collectBalanced, rawRowCheck16872]

def rawRow16873 : Integer.Sparse Key := [(key771, 4), (key804, 4), (key798, 4), (key779, -4), (key771, -4), (key804, -4), (key804, -4), (key798, -4), (key873, -4), (key804, 12)]

theorem rawRowCheck16873 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form9 = rawRow16873 := by decide +kernel

def row16873 : Integer.Sparse Key := [(key779, -4), (key804, 8), (key873, -4)]

theorem rowCheck16873 : row16873 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16873 := by decide +kernel

theorem rowEval16873 (x : Key → ℝ) : Integer.Sparse.eval row16873 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck16873, Integer.Sparse.eval_collectBalanced, rawRowCheck16873]

def rawRow16874 : Integer.Sparse Key := [(key798, 4), (key771, 4), (key804, 4), (key771, -4), (key804, -4), (key779, -4), (key798, -4), (key873, -4), (key804, -4), (key804, 12)]

theorem rawRowCheck16874 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form9 = rawRow16874 := by decide +kernel

def row16874 : Integer.Sparse Key := [(key779, -4), (key804, 8), (key873, -4)]

theorem rowCheck16874 : row16874 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16874 := by decide +kernel

theorem rowEval16874 (x : Key → ℝ) : Integer.Sparse.eval row16874 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck16874, Integer.Sparse.eval_collectBalanced, rawRowCheck16874]

def rawRow16875 : Integer.Sparse Key := [(key798, 4), (key804, 4), (key771, 4), (key804, -4), (key771, -4), (key779, -4), (key873, -4), (key798, -4), (key804, -4), (key804, 12)]

theorem rawRowCheck16875 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form9 = rawRow16875 := by decide +kernel

def row16875 : Integer.Sparse Key := [(key779, -4), (key804, 8), (key873, -4)]

theorem rowCheck16875 : row16875 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16875 := by decide +kernel

theorem rowEval16875 (x : Key → ℝ) : Integer.Sparse.eval row16875 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck16875, Integer.Sparse.eval_collectBalanced, rawRowCheck16875]

def rawRow16876 : Integer.Sparse Key := [(key804, 4), (key771, 4), (key798, 4), (key779, -4), (key804, -4), (key771, -4), (key804, -4), (key873, -4), (key798, -4), (key804, 12)]

theorem rawRowCheck16876 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form9 = rawRow16876 := by decide +kernel

def row16876 : Integer.Sparse Key := [(key779, -4), (key804, 8), (key873, -4)]

theorem rowCheck16876 : row16876 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16876 := by decide +kernel

theorem rowEval16876 (x : Key → ℝ) : Integer.Sparse.eval row16876 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck16876, Integer.Sparse.eval_collectBalanced, rawRowCheck16876]

def rawRow16877 : Integer.Sparse Key := [(key804, 4), (key798, 4), (key771, 4), (key804, -4), (key779, -4), (key771, -4), (key873, -4), (key804, -4), (key798, -4), (key804, 12)]

theorem rawRowCheck16877 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form9 = rawRow16877 := by decide +kernel

def row16877 : Integer.Sparse Key := [(key779, -4), (key804, 8), (key873, -4)]

theorem rowCheck16877 : row16877 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16877 := by decide +kernel

theorem rowEval16877 (x : Key → ℝ) : Integer.Sparse.eval row16877 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck16877, Integer.Sparse.eval_collectBalanced, rawRowCheck16877]

def rawRow16878 : Integer.Sparse Key := [(key771, 4), (key798, 4), (key804, 4), (key798, -4), (key804, -4), (key873, -4), (key771, -4), (key779, -4), (key804, -4), (key804, 12)]

theorem rawRowCheck16878 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form9 = rawRow16878 := by decide +kernel

def row16878 : Integer.Sparse Key := [(key779, -4), (key804, 8), (key873, -4)]

theorem rowCheck16878 : row16878 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16878 := by decide +kernel

theorem rowEval16878 (x : Key → ℝ) : Integer.Sparse.eval row16878 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck16878, Integer.Sparse.eval_collectBalanced, rawRowCheck16878]

def rawRow16879 : Integer.Sparse Key := [(key771, 4), (key804, 4), (key798, 4), (key804, -4), (key798, -4), (key873, -4), (key779, -4), (key771, -4), (key804, -4), (key804, 12)]

theorem rawRowCheck16879 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form9 = rawRow16879 := by decide +kernel

def row16879 : Integer.Sparse Key := [(key779, -4), (key804, 8), (key873, -4)]

theorem rowCheck16879 : row16879 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16879 := by decide +kernel

theorem rowEval16879 (x : Key → ℝ) : Integer.Sparse.eval row16879 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck16879, Integer.Sparse.eval_collectBalanced, rawRowCheck16879]

def rawRow16880 : Integer.Sparse Key := [(key798, 4), (key771, 4), (key804, 4), (key798, -4), (key873, -4), (key804, -4), (key771, -4), (key804, -4), (key779, -4), (key804, 12)]

theorem rawRowCheck16880 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form9 = rawRow16880 := by decide +kernel

def row16880 : Integer.Sparse Key := [(key779, -4), (key804, 8), (key873, -4)]

theorem rowCheck16880 : row16880 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16880 := by decide +kernel

theorem rowEval16880 (x : Key → ℝ) : Integer.Sparse.eval row16880 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck16880, Integer.Sparse.eval_collectBalanced, rawRowCheck16880]

def rawRow16881 : Integer.Sparse Key := [(key798, 4), (key804, 4), (key771, 4), (key873, -4), (key798, -4), (key804, -4), (key804, -4), (key771, -4), (key779, -4), (key804, 12)]

theorem rawRowCheck16881 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form9 = rawRow16881 := by decide +kernel

def row16881 : Integer.Sparse Key := [(key779, -4), (key804, 8), (key873, -4)]

theorem rowCheck16881 : row16881 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16881 := by decide +kernel

theorem rowEval16881 (x : Key → ℝ) : Integer.Sparse.eval row16881 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck16881, Integer.Sparse.eval_collectBalanced, rawRowCheck16881]

def rawRow16882 : Integer.Sparse Key := [(key804, 4), (key771, 4), (key798, 4), (key804, -4), (key873, -4), (key798, -4), (key779, -4), (key804, -4), (key771, -4), (key804, 12)]

theorem rawRowCheck16882 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form9 = rawRow16882 := by decide +kernel

def row16882 : Integer.Sparse Key := [(key779, -4), (key804, 8), (key873, -4)]

theorem rowCheck16882 : row16882 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16882 := by decide +kernel

theorem rowEval16882 (x : Key → ℝ) : Integer.Sparse.eval row16882 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck16882, Integer.Sparse.eval_collectBalanced, rawRowCheck16882]

def rawRow16883 : Integer.Sparse Key := [(key804, 4), (key798, 4), (key771, 4), (key873, -4), (key804, -4), (key798, -4), (key804, -4), (key779, -4), (key771, -4), (key804, 12)]

theorem rawRowCheck16883 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form9 = rawRow16883 := by decide +kernel

def row16883 : Integer.Sparse Key := [(key779, -4), (key804, 8), (key873, -4)]

theorem rowCheck16883 : row16883 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16883 := by decide +kernel

theorem rowEval16883 (x : Key → ℝ) : Integer.Sparse.eval row16883 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck16883, Integer.Sparse.eval_collectBalanced, rawRowCheck16883]

def rawRow16884 : Integer.Sparse Key := [(key798, 4), (key798, 4), (key873, 4), (key771, -4), (key804, -4), (key804, -4), (key771, -4), (key804, -4), (key804, -4), (key779, 12)]

theorem rawRowCheck16884 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form9 = rawRow16884 := by decide +kernel

def row16884 : Integer.Sparse Key := [(key771, -8), (key779, 12), (key798, 8), (key804, -16), (key873, 4)]

theorem rowCheck16884 : row16884 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16884 := by decide +kernel

theorem rowEval16884 (x : Key → ℝ) : Integer.Sparse.eval row16884 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck16884, Integer.Sparse.eval_collectBalanced, rawRowCheck16884]

def rawRow16885 : Integer.Sparse Key := [(key798, 4), (key873, 4), (key798, 4), (key804, -4), (key771, -4), (key804, -4), (key804, -4), (key771, -4), (key804, -4), (key779, 12)]

theorem rawRowCheck16885 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form9 = rawRow16885 := by decide +kernel

def row16885 : Integer.Sparse Key := [(key771, -8), (key779, 12), (key798, 8), (key804, -16), (key873, 4)]

theorem rowCheck16885 : row16885 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16885 := by decide +kernel

theorem rowEval16885 (x : Key → ℝ) : Integer.Sparse.eval row16885 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck16885, Integer.Sparse.eval_collectBalanced, rawRowCheck16885]

def rawRow16886 : Integer.Sparse Key := [(key873, 4), (key798, 4), (key798, 4), (key804, -4), (key804, -4), (key771, -4), (key804, -4), (key804, -4), (key771, -4), (key779, 12)]

theorem rawRowCheck16886 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form9 = rawRow16886 := by decide +kernel

def row16886 : Integer.Sparse Key := [(key771, -8), (key779, 12), (key798, 8), (key804, -16), (key873, 4)]

theorem rowCheck16886 : row16886 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16886 := by decide +kernel

theorem rowEval16886 (x : Key → ℝ) : Integer.Sparse.eval row16886 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck16886, Integer.Sparse.eval_collectBalanced, rawRowCheck16886]

def rawRow16887 : Integer.Sparse Key := [(key2147, -1), (key2152, -1), (key2147, -1), (key2166, -1), (key2152, -1), (key2166, -1), (key2176, 2), (key2176, 2), (key2187, 2), (key2147, -1), (key2152, -1), (key2147, -1), (key2166, -1), (key2152, -1), (key2166, -1), (key2240, 2), (key2246, 2), (key2240, 2), (key2253, 2), (key2246, 2), (key2253, 2), (key2276, -1), (key2279, -1), (key2276, -1), (key2287, -1), (key2279, -1), (key2287, -1), (key2176, 2), (key2176, 2), (key2187, 2), (key2276, -1), (key2279, -1), (key2276, -1), (key2287, -1), (key2279, -1), (key2287, -1)]

theorem rawRowCheck16887 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form10 = rawRow16887 := by decide +kernel

def row16887 : Integer.Sparse Key := [(key2147, -4), (key2152, -4), (key2166, -4), (key2176, 8), (key2187, 4), (key2240, 4), (key2246, 4), (key2253, 4), (key2276, -4), (key2279, -4), (key2287, -4)]

theorem rowCheck16887 : row16887 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16887 := by decide +kernel

theorem rowEval16887 (x : Key → ℝ) : Integer.Sparse.eval row16887 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form10) x := by
  rw [rowCheck16887, Integer.Sparse.eval_collectBalanced, rawRowCheck16887]

def rawRow16888 : Integer.Sparse Key := [(key2152, -1), (key2147, -1), (key2166, -1), (key2147, -1), (key2166, -1), (key2152, -1), (key2176, 2), (key2187, 2), (key2176, 2), (key2152, -1), (key2147, -1), (key2166, -1), (key2147, -1), (key2166, -1), (key2152, -1), (key2246, 2), (key2240, 2), (key2253, 2), (key2240, 2), (key2253, 2), (key2246, 2), (key2279, -1), (key2276, -1), (key2287, -1), (key2276, -1), (key2287, -1), (key2279, -1), (key2176, 2), (key2187, 2), (key2176, 2), (key2279, -1), (key2276, -1), (key2287, -1), (key2276, -1), (key2287, -1), (key2279, -1)]

theorem rawRowCheck16888 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form10 = rawRow16888 := by decide +kernel

def row16888 : Integer.Sparse Key := [(key2147, -4), (key2152, -4), (key2166, -4), (key2176, 8), (key2187, 4), (key2240, 4), (key2246, 4), (key2253, 4), (key2276, -4), (key2279, -4), (key2287, -4)]

theorem rowCheck16888 : row16888 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16888 := by decide +kernel

theorem rowEval16888 (x : Key → ℝ) : Integer.Sparse.eval row16888 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck16888, Integer.Sparse.eval_collectBalanced, rawRowCheck16888]

def rawRow16889 : Integer.Sparse Key := [(key2166, -1), (key2166, -1), (key2152, -1), (key2152, -1), (key2147, -1), (key2147, -1), (key2187, 2), (key2176, 2), (key2176, 2), (key2166, -1), (key2166, -1), (key2152, -1), (key2152, -1), (key2147, -1), (key2147, -1), (key2253, 2), (key2253, 2), (key2246, 2), (key2246, 2), (key2240, 2), (key2240, 2), (key2287, -1), (key2287, -1), (key2279, -1), (key2279, -1), (key2276, -1), (key2276, -1), (key2187, 2), (key2176, 2), (key2176, 2), (key2287, -1), (key2287, -1), (key2279, -1), (key2279, -1), (key2276, -1), (key2276, -1)]

theorem rawRowCheck16889 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form10 = rawRow16889 := by decide +kernel

def row16889 : Integer.Sparse Key := [(key2147, -4), (key2152, -4), (key2166, -4), (key2176, 8), (key2187, 4), (key2240, 4), (key2246, 4), (key2253, 4), (key2276, -4), (key2279, -4), (key2287, -4)]

theorem rowCheck16889 : row16889 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16889 := by decide +kernel

theorem rowEval16889 (x : Key → ℝ) : Integer.Sparse.eval row16889 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck16889, Integer.Sparse.eval_collectBalanced, rawRowCheck16889]

def rawRow16890 : Integer.Sparse Key := [(key2028, -1), (key2033, -1), (key2147, -1), (key2166, -1), (key2176, -1), (key2187, -1), (key2033, 2), (key2152, 2), (key2166, 2), (key2058, -1), (key2063, -1), (key2240, -1), (key2253, -1), (key2276, -1), (key2287, -1), (key2058, 2), (key2069, 2), (key2147, 2), (key2166, 2), (key2279, 2), (key2287, 2), (key2063, -1), (key2069, -1), (key2152, -1), (key2166, -1), (key2246, -1), (key2253, -1), (key2079, 2), (key2276, 2), (key2287, 2), (key2079, -1), (key2085, -1), (key2176, -1), (key2187, -1), (key2279, -1), (key2287, -1)]

theorem rawRowCheck16890 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form10 = rawRow16890 := by decide +kernel

def row16890 : Integer.Sparse Key := [(key2028, -1), (key2033, 1), (key2058, 1), (key2063, -2), (key2069, 1), (key2079, 1), (key2085, -1), (key2147, 1), (key2152, 1), (key2166, 2), (key2176, -2), (key2187, -2), (key2240, -1), (key2246, -1), (key2253, -2), (key2276, 1), (key2279, 1), (key2287, 2)]

theorem rowCheck16890 : row16890 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16890 := by decide +kernel

theorem rowEval16890 (x : Key → ℝ) : Integer.Sparse.eval row16890 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form10) x := by
  rw [rowCheck16890, Integer.Sparse.eval_collectBalanced, rawRowCheck16890]

def rawRow16891 : Integer.Sparse Key := [(key2033, -1), (key2028, -1), (key2166, -1), (key2147, -1), (key2187, -1), (key2176, -1), (key2033, 2), (key2166, 2), (key2152, 2), (key2063, -1), (key2058, -1), (key2253, -1), (key2240, -1), (key2287, -1), (key2276, -1), (key2069, 2), (key2058, 2), (key2166, 2), (key2147, 2), (key2287, 2), (key2279, 2), (key2069, -1), (key2063, -1), (key2166, -1), (key2152, -1), (key2253, -1), (key2246, -1), (key2079, 2), (key2287, 2), (key2276, 2), (key2085, -1), (key2079, -1), (key2187, -1), (key2176, -1), (key2287, -1), (key2279, -1)]

theorem rawRowCheck16891 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form10 = rawRow16891 := by decide +kernel

def row16891 : Integer.Sparse Key := [(key2028, -1), (key2033, 1), (key2058, 1), (key2063, -2), (key2069, 1), (key2079, 1), (key2085, -1), (key2147, 1), (key2152, 1), (key2166, 2), (key2176, -2), (key2187, -2), (key2240, -1), (key2246, -1), (key2253, -2), (key2276, 1), (key2279, 1), (key2287, 2)]

theorem rowCheck16891 : row16891 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16891 := by decide +kernel

theorem rowEval16891 (x : Key → ℝ) : Integer.Sparse.eval row16891 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck16891, Integer.Sparse.eval_collectBalanced, rawRowCheck16891]

def rawRow16892 : Integer.Sparse Key := [(key2147, -1), (key2176, -1), (key2028, -1), (key2187, -1), (key2033, -1), (key2166, -1), (key2152, 2), (key2033, 2), (key2166, 2), (key2240, -1), (key2276, -1), (key2058, -1), (key2287, -1), (key2063, -1), (key2253, -1), (key2147, 2), (key2279, 2), (key2058, 2), (key2287, 2), (key2069, 2), (key2166, 2), (key2152, -1), (key2246, -1), (key2063, -1), (key2253, -1), (key2069, -1), (key2166, -1), (key2276, 2), (key2079, 2), (key2287, 2), (key2176, -1), (key2279, -1), (key2079, -1), (key2287, -1), (key2085, -1), (key2187, -1)]

theorem rawRowCheck16892 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form10 = rawRow16892 := by decide +kernel

def row16892 : Integer.Sparse Key := [(key2028, -1), (key2033, 1), (key2058, 1), (key2063, -2), (key2069, 1), (key2079, 1), (key2085, -1), (key2147, 1), (key2152, 1), (key2166, 2), (key2176, -2), (key2187, -2), (key2240, -1), (key2246, -1), (key2253, -2), (key2276, 1), (key2279, 1), (key2287, 2)]

theorem rowCheck16892 : row16892 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16892 := by decide +kernel

theorem rowEval16892 (x : Key → ℝ) : Integer.Sparse.eval row16892 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form10) x := by
  rw [rowCheck16892, Integer.Sparse.eval_collectBalanced, rawRowCheck16892]

def rawRow16893 : Integer.Sparse Key := [(key2176, -1), (key2147, -1), (key2187, -1), (key2028, -1), (key2166, -1), (key2033, -1), (key2152, 2), (key2166, 2), (key2033, 2), (key2276, -1), (key2240, -1), (key2287, -1), (key2058, -1), (key2253, -1), (key2063, -1), (key2279, 2), (key2147, 2), (key2287, 2), (key2058, 2), (key2166, 2), (key2069, 2), (key2246, -1), (key2152, -1), (key2253, -1), (key2063, -1), (key2166, -1), (key2069, -1), (key2276, 2), (key2287, 2), (key2079, 2), (key2279, -1), (key2176, -1), (key2287, -1), (key2079, -1), (key2187, -1), (key2085, -1)]

theorem rawRowCheck16893 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form10 = rawRow16893 := by decide +kernel

def row16893 : Integer.Sparse Key := [(key2028, -1), (key2033, 1), (key2058, 1), (key2063, -2), (key2069, 1), (key2079, 1), (key2085, -1), (key2147, 1), (key2152, 1), (key2166, 2), (key2176, -2), (key2187, -2), (key2240, -1), (key2246, -1), (key2253, -2), (key2276, 1), (key2279, 1), (key2287, 2)]

theorem rowCheck16893 : row16893 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16893 := by decide +kernel

theorem rowEval16893 (x : Key → ℝ) : Integer.Sparse.eval row16893 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck16893, Integer.Sparse.eval_collectBalanced, rawRowCheck16893]

def rawRow16894 : Integer.Sparse Key := [(key2166, -1), (key2187, -1), (key2033, -1), (key2176, -1), (key2028, -1), (key2147, -1), (key2166, 2), (key2033, 2), (key2152, 2), (key2253, -1), (key2287, -1), (key2063, -1), (key2276, -1), (key2058, -1), (key2240, -1), (key2166, 2), (key2287, 2), (key2069, 2), (key2279, 2), (key2058, 2), (key2147, 2), (key2166, -1), (key2253, -1), (key2069, -1), (key2246, -1), (key2063, -1), (key2152, -1), (key2287, 2), (key2079, 2), (key2276, 2), (key2187, -1), (key2287, -1), (key2085, -1), (key2279, -1), (key2079, -1), (key2176, -1)]

theorem rawRowCheck16894 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form10 = rawRow16894 := by decide +kernel

def row16894 : Integer.Sparse Key := [(key2028, -1), (key2033, 1), (key2058, 1), (key2063, -2), (key2069, 1), (key2079, 1), (key2085, -1), (key2147, 1), (key2152, 1), (key2166, 2), (key2176, -2), (key2187, -2), (key2240, -1), (key2246, -1), (key2253, -2), (key2276, 1), (key2279, 1), (key2287, 2)]

theorem rowCheck16894 : row16894 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16894 := by decide +kernel

theorem rowEval16894 (x : Key → ℝ) : Integer.Sparse.eval row16894 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck16894, Integer.Sparse.eval_collectBalanced, rawRowCheck16894]

def rawRow16895 : Integer.Sparse Key := [(key2187, -1), (key2166, -1), (key2176, -1), (key2033, -1), (key2147, -1), (key2028, -1), (key2166, 2), (key2152, 2), (key2033, 2), (key2287, -1), (key2253, -1), (key2276, -1), (key2063, -1), (key2240, -1), (key2058, -1), (key2287, 2), (key2166, 2), (key2279, 2), (key2069, 2), (key2147, 2), (key2058, 2), (key2253, -1), (key2166, -1), (key2246, -1), (key2069, -1), (key2152, -1), (key2063, -1), (key2287, 2), (key2276, 2), (key2079, 2), (key2287, -1), (key2187, -1), (key2279, -1), (key2085, -1), (key2176, -1), (key2079, -1)]

theorem rawRowCheck16895 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form10 = rawRow16895 := by decide +kernel

def row16895 : Integer.Sparse Key := [(key2028, -1), (key2033, 1), (key2058, 1), (key2063, -2), (key2069, 1), (key2079, 1), (key2085, -1), (key2147, 1), (key2152, 1), (key2166, 2), (key2176, -2), (key2187, -2), (key2240, -1), (key2246, -1), (key2253, -2), (key2276, 1), (key2279, 1), (key2287, 2)]

theorem rowCheck16895 : row16895 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16895 := by decide +kernel

theorem rowEval16895 (x : Key → ℝ) : Integer.Sparse.eval row16895 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck16895, Integer.Sparse.eval_collectBalanced, rawRowCheck16895]

end MUB6.Certificate.GramRows

end OAI
