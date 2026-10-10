import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow13056 : Integer.Sparse Key := [(key1371, 1), (key1367, 1), (key1380, 1), (key1367, 1), (key1380, 1), (key1371, 1), (key1497, 1), (key1493, 1), (key1520, 1), (key1493, 1), (key1520, 1), (key1497, 1), (key1729, 1), (key1719, 1), (key1748, 1), (key1719, 1), (key1748, 1), (key1729, 1), (key1871, 1), (key1866, 1), (key1881, 1), (key1866, 1), (key1881, 1), (key1871, 1), (key1367, -2), (key1376, -2), (key1367, -2), (key1493, -2), (key1515, -2), (key1493, -2), (key1725, -2), (key1719, -2), (key1743, -2), (key1719, -2), (key1743, -2), (key1725, -2)]

theorem rawRowCheck13056 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form21 = rawRow13056 := by decide +kernel

def row13056 : Integer.Sparse Key := [(key1367, -2), (key1371, 2), (key1376, -2), (key1380, 2), (key1493, -2), (key1497, 2), (key1515, -2), (key1520, 2), (key1719, -2), (key1725, -4), (key1729, 2), (key1743, -4), (key1748, 2), (key1866, 2), (key1871, 2), (key1881, 2)]

theorem rowCheck13056 : row13056 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13056 := by decide +kernel

theorem rowEval13056 (x : Key → ℝ) : Integer.Sparse.eval row13056 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck13056, Integer.Sparse.eval_collectBalanced, rawRowCheck13056]

def rawRow13057 : Integer.Sparse Key := [(key1380, 1), (key1380, 1), (key1371, 1), (key1371, 1), (key1367, 1), (key1367, 1), (key1520, 1), (key1520, 1), (key1497, 1), (key1497, 1), (key1493, 1), (key1493, 1), (key1748, 1), (key1748, 1), (key1729, 1), (key1729, 1), (key1719, 1), (key1719, 1), (key1881, 1), (key1881, 1), (key1871, 1), (key1871, 1), (key1866, 1), (key1866, 1), (key1376, -2), (key1367, -2), (key1367, -2), (key1515, -2), (key1493, -2), (key1493, -2), (key1743, -2), (key1743, -2), (key1725, -2), (key1725, -2), (key1719, -2), (key1719, -2)]

theorem rawRowCheck13057 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form21 = rawRow13057 := by decide +kernel

def row13057 : Integer.Sparse Key := [(key1367, -2), (key1371, 2), (key1376, -2), (key1380, 2), (key1493, -2), (key1497, 2), (key1515, -2), (key1520, 2), (key1719, -2), (key1725, -4), (key1729, 2), (key1743, -4), (key1748, 2), (key1866, 2), (key1871, 2), (key1881, 2)]

theorem rowCheck13057 : row13057 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13057 := by decide +kernel

theorem rowEval13057 (x : Key → ℝ) : Integer.Sparse.eval row13057 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck13057, Integer.Sparse.eval_collectBalanced, rawRowCheck13057]

def rawRow13058 : Integer.Sparse Key := [(key1493, 1), (key1497, 1), (key1719, 1), (key1729, 1), (key1866, 1), (key1871, 1), (key1367, 1), (key1371, 1), (key1719, 1), (key1748, 1), (key1866, 1), (key1881, 1), (key1367, 1), (key1380, 1), (key1493, 1), (key1520, 1), (key1871, 1), (key1881, 1), (key1371, 1), (key1380, 1), (key1497, 1), (key1520, 1), (key1729, 1), (key1748, 1), (key1493, -2), (key1719, -2), (key1725, -2), (key1367, -2), (key1719, -2), (key1743, -2), (key1367, -2), (key1376, -2), (key1493, -2), (key1515, -2), (key1725, -2), (key1743, -2)]

theorem rawRowCheck13058 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form21 = rawRow13058 := by decide +kernel

def row13058 : Integer.Sparse Key := [(key1367, -2), (key1371, 2), (key1376, -2), (key1380, 2), (key1493, -2), (key1497, 2), (key1515, -2), (key1520, 2), (key1719, -2), (key1725, -4), (key1729, 2), (key1743, -4), (key1748, 2), (key1866, 2), (key1871, 2), (key1881, 2)]

theorem rowCheck13058 : row13058 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13058 := by decide +kernel

theorem rowEval13058 (x : Key → ℝ) : Integer.Sparse.eval row13058 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form21) x := by
  rw [rowCheck13058, Integer.Sparse.eval_collectBalanced, rawRowCheck13058]

def rawRow13059 : Integer.Sparse Key := [(key1497, 1), (key1493, 1), (key1729, 1), (key1719, 1), (key1871, 1), (key1866, 1), (key1371, 1), (key1367, 1), (key1748, 1), (key1719, 1), (key1881, 1), (key1866, 1), (key1380, 1), (key1367, 1), (key1520, 1), (key1493, 1), (key1881, 1), (key1871, 1), (key1380, 1), (key1371, 1), (key1520, 1), (key1497, 1), (key1748, 1), (key1729, 1), (key1493, -2), (key1725, -2), (key1719, -2), (key1367, -2), (key1743, -2), (key1719, -2), (key1376, -2), (key1367, -2), (key1515, -2), (key1493, -2), (key1743, -2), (key1725, -2)]

theorem rawRowCheck13059 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form21 = rawRow13059 := by decide +kernel

def row13059 : Integer.Sparse Key := [(key1367, -2), (key1371, 2), (key1376, -2), (key1380, 2), (key1493, -2), (key1497, 2), (key1515, -2), (key1520, 2), (key1719, -2), (key1725, -4), (key1729, 2), (key1743, -4), (key1748, 2), (key1866, 2), (key1871, 2), (key1881, 2)]

theorem rowCheck13059 : row13059 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13059 := by decide +kernel

theorem rowEval13059 (x : Key → ℝ) : Integer.Sparse.eval row13059 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck13059, Integer.Sparse.eval_collectBalanced, rawRowCheck13059]

def rawRow13060 : Integer.Sparse Key := [(key1719, 1), (key1866, 1), (key1493, 1), (key1871, 1), (key1497, 1), (key1729, 1), (key1719, 1), (key1866, 1), (key1367, 1), (key1881, 1), (key1371, 1), (key1748, 1), (key1493, 1), (key1871, 1), (key1367, 1), (key1881, 1), (key1380, 1), (key1520, 1), (key1497, 1), (key1729, 1), (key1371, 1), (key1748, 1), (key1380, 1), (key1520, 1), (key1719, -2), (key1493, -2), (key1725, -2), (key1719, -2), (key1367, -2), (key1743, -2), (key1493, -2), (key1725, -2), (key1367, -2), (key1743, -2), (key1376, -2), (key1515, -2)]

theorem rawRowCheck13060 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form21 = rawRow13060 := by decide +kernel

def row13060 : Integer.Sparse Key := [(key1367, -2), (key1371, 2), (key1376, -2), (key1380, 2), (key1493, -2), (key1497, 2), (key1515, -2), (key1520, 2), (key1719, -2), (key1725, -4), (key1729, 2), (key1743, -4), (key1748, 2), (key1866, 2), (key1871, 2), (key1881, 2)]

theorem rowCheck13060 : row13060 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13060 := by decide +kernel

theorem rowEval13060 (x : Key → ℝ) : Integer.Sparse.eval row13060 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form21) x := by
  rw [rowCheck13060, Integer.Sparse.eval_collectBalanced, rawRowCheck13060]

def rawRow13061 : Integer.Sparse Key := [(key1866, 1), (key1719, 1), (key1871, 1), (key1493, 1), (key1729, 1), (key1497, 1), (key1866, 1), (key1719, 1), (key1881, 1), (key1367, 1), (key1748, 1), (key1371, 1), (key1871, 1), (key1493, 1), (key1881, 1), (key1367, 1), (key1520, 1), (key1380, 1), (key1729, 1), (key1497, 1), (key1748, 1), (key1371, 1), (key1520, 1), (key1380, 1), (key1719, -2), (key1725, -2), (key1493, -2), (key1719, -2), (key1743, -2), (key1367, -2), (key1725, -2), (key1493, -2), (key1743, -2), (key1367, -2), (key1515, -2), (key1376, -2)]

theorem rawRowCheck13061 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form21 = rawRow13061 := by decide +kernel

def row13061 : Integer.Sparse Key := [(key1367, -2), (key1371, 2), (key1376, -2), (key1380, 2), (key1493, -2), (key1497, 2), (key1515, -2), (key1520, 2), (key1719, -2), (key1725, -4), (key1729, 2), (key1743, -4), (key1748, 2), (key1866, 2), (key1871, 2), (key1881, 2)]

theorem rowCheck13061 : row13061 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13061 := by decide +kernel

theorem rowEval13061 (x : Key → ℝ) : Integer.Sparse.eval row13061 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form21) x := by
  rw [rowCheck13061, Integer.Sparse.eval_collectBalanced, rawRowCheck13061]

def rawRow13062 : Integer.Sparse Key := [(key1729, 1), (key1871, 1), (key1497, 1), (key1866, 1), (key1493, 1), (key1719, 1), (key1748, 1), (key1881, 1), (key1371, 1), (key1866, 1), (key1367, 1), (key1719, 1), (key1520, 1), (key1881, 1), (key1380, 1), (key1871, 1), (key1367, 1), (key1493, 1), (key1520, 1), (key1748, 1), (key1380, 1), (key1729, 1), (key1371, 1), (key1497, 1), (key1725, -2), (key1493, -2), (key1719, -2), (key1743, -2), (key1367, -2), (key1719, -2), (key1515, -2), (key1743, -2), (key1376, -2), (key1725, -2), (key1367, -2), (key1493, -2)]

theorem rawRowCheck13062 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form21 = rawRow13062 := by decide +kernel

def row13062 : Integer.Sparse Key := [(key1367, -2), (key1371, 2), (key1376, -2), (key1380, 2), (key1493, -2), (key1497, 2), (key1515, -2), (key1520, 2), (key1719, -2), (key1725, -4), (key1729, 2), (key1743, -4), (key1748, 2), (key1866, 2), (key1871, 2), (key1881, 2)]

theorem rowCheck13062 : row13062 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13062 := by decide +kernel

theorem rowEval13062 (x : Key → ℝ) : Integer.Sparse.eval row13062 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck13062, Integer.Sparse.eval_collectBalanced, rawRowCheck13062]

def rawRow13063 : Integer.Sparse Key := [(key1871, 1), (key1729, 1), (key1866, 1), (key1497, 1), (key1719, 1), (key1493, 1), (key1881, 1), (key1748, 1), (key1866, 1), (key1371, 1), (key1719, 1), (key1367, 1), (key1881, 1), (key1520, 1), (key1871, 1), (key1380, 1), (key1493, 1), (key1367, 1), (key1748, 1), (key1520, 1), (key1729, 1), (key1380, 1), (key1497, 1), (key1371, 1), (key1725, -2), (key1719, -2), (key1493, -2), (key1743, -2), (key1719, -2), (key1367, -2), (key1743, -2), (key1515, -2), (key1725, -2), (key1376, -2), (key1493, -2), (key1367, -2)]

theorem rawRowCheck13063 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form21 = rawRow13063 := by decide +kernel

def row13063 : Integer.Sparse Key := [(key1367, -2), (key1371, 2), (key1376, -2), (key1380, 2), (key1493, -2), (key1497, 2), (key1515, -2), (key1520, 2), (key1719, -2), (key1725, -4), (key1729, 2), (key1743, -4), (key1748, 2), (key1866, 2), (key1871, 2), (key1881, 2)]

theorem rowCheck13063 : row13063 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13063 := by decide +kernel

theorem rowEval13063 (x : Key → ℝ) : Integer.Sparse.eval row13063 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form21) x := by
  rw [rowCheck13063, Integer.Sparse.eval_collectBalanced, rawRowCheck13063]

def rawRow13064 : Integer.Sparse Key := [(key1520, 1), (key1520, 1), (key1748, 1), (key1748, 1), (key1881, 1), (key1881, 1), (key1380, 1), (key1380, 1), (key1729, 1), (key1729, 1), (key1871, 1), (key1871, 1), (key1371, 1), (key1371, 1), (key1497, 1), (key1497, 1), (key1866, 1), (key1866, 1), (key1367, 1), (key1367, 1), (key1493, 1), (key1493, 1), (key1719, 1), (key1719, 1), (key1515, -2), (key1743, -2), (key1743, -2), (key1376, -2), (key1725, -2), (key1725, -2), (key1367, -2), (key1367, -2), (key1493, -2), (key1493, -2), (key1719, -2), (key1719, -2)]

theorem rawRowCheck13064 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form21 = rawRow13064 := by decide +kernel

def row13064 : Integer.Sparse Key := [(key1367, -2), (key1371, 2), (key1376, -2), (key1380, 2), (key1493, -2), (key1497, 2), (key1515, -2), (key1520, 2), (key1719, -2), (key1725, -4), (key1729, 2), (key1743, -4), (key1748, 2), (key1866, 2), (key1871, 2), (key1881, 2)]

theorem rowCheck13064 : row13064 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13064 := by decide +kernel

theorem rowEval13064 (x : Key → ℝ) : Integer.Sparse.eval row13064 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck13064, Integer.Sparse.eval_collectBalanced, rawRowCheck13064]

def rawRow13065 : Integer.Sparse Key := [(key1748, 1), (key1881, 1), (key1520, 1), (key1881, 1), (key1520, 1), (key1748, 1), (key1729, 1), (key1871, 1), (key1380, 1), (key1871, 1), (key1380, 1), (key1729, 1), (key1497, 1), (key1866, 1), (key1371, 1), (key1866, 1), (key1371, 1), (key1497, 1), (key1493, 1), (key1719, 1), (key1367, 1), (key1719, 1), (key1367, 1), (key1493, 1), (key1743, -2), (key1515, -2), (key1743, -2), (key1725, -2), (key1376, -2), (key1725, -2), (key1493, -2), (key1719, -2), (key1367, -2), (key1719, -2), (key1367, -2), (key1493, -2)]

theorem rawRowCheck13065 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form21 = rawRow13065 := by decide +kernel

def row13065 : Integer.Sparse Key := [(key1367, -2), (key1371, 2), (key1376, -2), (key1380, 2), (key1493, -2), (key1497, 2), (key1515, -2), (key1520, 2), (key1719, -2), (key1725, -4), (key1729, 2), (key1743, -4), (key1748, 2), (key1866, 2), (key1871, 2), (key1881, 2)]

theorem rowCheck13065 : row13065 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13065 := by decide +kernel

theorem rowEval13065 (x : Key → ℝ) : Integer.Sparse.eval row13065 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck13065, Integer.Sparse.eval_collectBalanced, rawRowCheck13065]

def rawRow13066 : Integer.Sparse Key := [(key1881, 1), (key1748, 1), (key1881, 1), (key1520, 1), (key1748, 1), (key1520, 1), (key1871, 1), (key1729, 1), (key1871, 1), (key1380, 1), (key1729, 1), (key1380, 1), (key1866, 1), (key1497, 1), (key1866, 1), (key1371, 1), (key1497, 1), (key1371, 1), (key1719, 1), (key1493, 1), (key1719, 1), (key1367, 1), (key1493, 1), (key1367, 1), (key1743, -2), (key1743, -2), (key1515, -2), (key1725, -2), (key1725, -2), (key1376, -2), (key1719, -2), (key1493, -2), (key1719, -2), (key1367, -2), (key1493, -2), (key1367, -2)]

theorem rawRowCheck13066 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form21 = rawRow13066 := by decide +kernel

def row13066 : Integer.Sparse Key := [(key1367, -2), (key1371, 2), (key1376, -2), (key1380, 2), (key1493, -2), (key1497, 2), (key1515, -2), (key1520, 2), (key1719, -2), (key1725, -4), (key1729, 2), (key1743, -4), (key1748, 2), (key1866, 2), (key1871, 2), (key1881, 2)]

theorem rowCheck13066 : row13066 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13066 := by decide +kernel

theorem rowEval13066 (x : Key → ℝ) : Integer.Sparse.eval row13066 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form21) x := by
  rw [rowCheck13066, Integer.Sparse.eval_collectBalanced, rawRowCheck13066]

def rawRow13067 : Integer.Sparse Key := [(key1367, -2), (key1367, -2), (key1371, -2), (key1719, -2), (key1719, -2), (key1743, -2), (key1743, -2), (key1748, -2), (key1748, -2), (key1866, -2), (key1881, -2), (key1881, -2), (key1367, 1), (key1367, 1), (key1376, 1), (key1376, 1), (key1380, 1), (key1380, 1), (key1493, 1), (key1493, 1), (key1515, 1), (key1515, 1), (key1520, 1), (key1520, 1), (key1725, 1), (key1725, 1), (key1743, 1), (key1743, 1), (key1759, 1), (key1759, 1), (key1871, 1), (key1871, 1), (key1881, 1), (key1881, 1), (key1889, 1), (key1889, 1)]

theorem rawRowCheck13067 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form22 = rawRow13067 := by decide +kernel

def row13067 : Integer.Sparse Key := [(key1367, -2), (key1371, -2), (key1376, 2), (key1380, 2), (key1493, 2), (key1515, 2), (key1520, 2), (key1719, -4), (key1725, 2), (key1743, -2), (key1748, -4), (key1759, 2), (key1866, -2), (key1871, 2), (key1881, -2), (key1889, 2)]

theorem rowCheck13067 : row13067 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13067 := by decide +kernel

theorem rowEval13067 (x : Key → ℝ) : Integer.Sparse.eval row13067 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form22) x := by
  rw [rowCheck13067, Integer.Sparse.eval_collectBalanced, rawRowCheck13067]

def rawRow13068 : Integer.Sparse Key := [(key1367, -2), (key1371, -2), (key1367, -2), (key1743, -2), (key1748, -2), (key1719, -2), (key1748, -2), (key1719, -2), (key1743, -2), (key1881, -2), (key1866, -2), (key1881, -2), (key1376, 1), (key1380, 1), (key1367, 1), (key1380, 1), (key1367, 1), (key1376, 1), (key1515, 1), (key1520, 1), (key1493, 1), (key1520, 1), (key1493, 1), (key1515, 1), (key1743, 1), (key1759, 1), (key1725, 1), (key1759, 1), (key1725, 1), (key1743, 1), (key1881, 1), (key1889, 1), (key1871, 1), (key1889, 1), (key1871, 1), (key1881, 1)]

theorem rawRowCheck13068 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form22 = rawRow13068 := by decide +kernel

def row13068 : Integer.Sparse Key := [(key1367, -2), (key1371, -2), (key1376, 2), (key1380, 2), (key1493, 2), (key1515, 2), (key1520, 2), (key1719, -4), (key1725, 2), (key1743, -2), (key1748, -4), (key1759, 2), (key1866, -2), (key1871, 2), (key1881, -2), (key1889, 2)]

theorem rowCheck13068 : row13068 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13068 := by decide +kernel

theorem rowEval13068 (x : Key → ℝ) : Integer.Sparse.eval row13068 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form22) x := by
  rw [rowCheck13068, Integer.Sparse.eval_collectBalanced, rawRowCheck13068]

def rawRow13069 : Integer.Sparse Key := [(key1371, -2), (key1367, -2), (key1367, -2), (key1748, -2), (key1743, -2), (key1748, -2), (key1719, -2), (key1743, -2), (key1719, -2), (key1881, -2), (key1881, -2), (key1866, -2), (key1380, 1), (key1376, 1), (key1380, 1), (key1367, 1), (key1376, 1), (key1367, 1), (key1520, 1), (key1515, 1), (key1520, 1), (key1493, 1), (key1515, 1), (key1493, 1), (key1759, 1), (key1743, 1), (key1759, 1), (key1725, 1), (key1743, 1), (key1725, 1), (key1889, 1), (key1881, 1), (key1889, 1), (key1871, 1), (key1881, 1), (key1871, 1)]

theorem rawRowCheck13069 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form22 = rawRow13069 := by decide +kernel

def row13069 : Integer.Sparse Key := [(key1367, -2), (key1371, -2), (key1376, 2), (key1380, 2), (key1493, 2), (key1515, 2), (key1520, 2), (key1719, -4), (key1725, 2), (key1743, -2), (key1748, -4), (key1759, 2), (key1866, -2), (key1871, 2), (key1881, -2), (key1889, 2)]

theorem rowCheck13069 : row13069 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13069 := by decide +kernel

theorem rowEval13069 (x : Key → ℝ) : Integer.Sparse.eval row13069 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck13069, Integer.Sparse.eval_collectBalanced, rawRowCheck13069]

def rawRow13070 : Integer.Sparse Key := [(key1719, -2), (key1719, -2), (key1866, -2), (key1367, -2), (key1367, -2), (key1743, -2), (key1743, -2), (key1881, -2), (key1881, -2), (key1371, -2), (key1748, -2), (key1748, -2), (key1493, 1), (key1493, 1), (key1725, 1), (key1725, 1), (key1871, 1), (key1871, 1), (key1367, 1), (key1367, 1), (key1743, 1), (key1743, 1), (key1881, 1), (key1881, 1), (key1376, 1), (key1376, 1), (key1515, 1), (key1515, 1), (key1889, 1), (key1889, 1), (key1380, 1), (key1380, 1), (key1520, 1), (key1520, 1), (key1759, 1), (key1759, 1)]

theorem rawRowCheck13070 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form22 = rawRow13070 := by decide +kernel

def row13070 : Integer.Sparse Key := [(key1367, -2), (key1371, -2), (key1376, 2), (key1380, 2), (key1493, 2), (key1515, 2), (key1520, 2), (key1719, -4), (key1725, 2), (key1743, -2), (key1748, -4), (key1759, 2), (key1866, -2), (key1871, 2), (key1881, -2), (key1889, 2)]

theorem rowCheck13070 : row13070 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13070 := by decide +kernel

theorem rowEval13070 (x : Key → ℝ) : Integer.Sparse.eval row13070 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form22) x := by
  rw [rowCheck13070, Integer.Sparse.eval_collectBalanced, rawRowCheck13070]

def rawRow13071 : Integer.Sparse Key := [(key1719, -2), (key1866, -2), (key1719, -2), (key1743, -2), (key1881, -2), (key1367, -2), (key1881, -2), (key1367, -2), (key1743, -2), (key1748, -2), (key1371, -2), (key1748, -2), (key1725, 1), (key1871, 1), (key1493, 1), (key1871, 1), (key1493, 1), (key1725, 1), (key1743, 1), (key1881, 1), (key1367, 1), (key1881, 1), (key1367, 1), (key1743, 1), (key1515, 1), (key1889, 1), (key1376, 1), (key1889, 1), (key1376, 1), (key1515, 1), (key1520, 1), (key1759, 1), (key1380, 1), (key1759, 1), (key1380, 1), (key1520, 1)]

theorem rawRowCheck13071 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form22 = rawRow13071 := by decide +kernel

def row13071 : Integer.Sparse Key := [(key1367, -2), (key1371, -2), (key1376, 2), (key1380, 2), (key1493, 2), (key1515, 2), (key1520, 2), (key1719, -4), (key1725, 2), (key1743, -2), (key1748, -4), (key1759, 2), (key1866, -2), (key1871, 2), (key1881, -2), (key1889, 2)]

theorem rowCheck13071 : row13071 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13071 := by decide +kernel

theorem rowEval13071 (x : Key → ℝ) : Integer.Sparse.eval row13071 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form22) x := by
  rw [rowCheck13071, Integer.Sparse.eval_collectBalanced, rawRowCheck13071]

def rawRow13072 : Integer.Sparse Key := [(key1866, -2), (key1719, -2), (key1719, -2), (key1881, -2), (key1743, -2), (key1881, -2), (key1367, -2), (key1743, -2), (key1367, -2), (key1748, -2), (key1748, -2), (key1371, -2), (key1871, 1), (key1725, 1), (key1871, 1), (key1493, 1), (key1725, 1), (key1493, 1), (key1881, 1), (key1743, 1), (key1881, 1), (key1367, 1), (key1743, 1), (key1367, 1), (key1889, 1), (key1515, 1), (key1889, 1), (key1376, 1), (key1515, 1), (key1376, 1), (key1759, 1), (key1520, 1), (key1759, 1), (key1380, 1), (key1520, 1), (key1380, 1)]

theorem rawRowCheck13072 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form22 = rawRow13072 := by decide +kernel

def row13072 : Integer.Sparse Key := [(key1367, -2), (key1371, -2), (key1376, 2), (key1380, 2), (key1493, 2), (key1515, 2), (key1520, 2), (key1719, -4), (key1725, 2), (key1743, -2), (key1748, -4), (key1759, 2), (key1866, -2), (key1871, 2), (key1881, -2), (key1889, 2)]

theorem rowCheck13072 : row13072 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13072 := by decide +kernel

theorem rowEval13072 (x : Key → ℝ) : Integer.Sparse.eval row13072 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form22) x := by
  rw [rowCheck13072, Integer.Sparse.eval_collectBalanced, rawRowCheck13072]

def rawRow13073 : Integer.Sparse Key := [(key1743, -2), (key1748, -2), (key1881, -2), (key1367, -2), (key1371, -2), (key1719, -2), (key1748, -2), (key1866, -2), (key1881, -2), (key1367, -2), (key1719, -2), (key1743, -2), (key1515, 1), (key1520, 1), (key1743, 1), (key1759, 1), (key1881, 1), (key1889, 1), (key1376, 1), (key1380, 1), (key1725, 1), (key1759, 1), (key1871, 1), (key1889, 1), (key1367, 1), (key1380, 1), (key1493, 1), (key1520, 1), (key1871, 1), (key1881, 1), (key1367, 1), (key1376, 1), (key1493, 1), (key1515, 1), (key1725, 1), (key1743, 1)]

theorem rawRowCheck13073 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form22 = rawRow13073 := by decide +kernel

def row13073 : Integer.Sparse Key := [(key1367, -2), (key1371, -2), (key1376, 2), (key1380, 2), (key1493, 2), (key1515, 2), (key1520, 2), (key1719, -4), (key1725, 2), (key1743, -2), (key1748, -4), (key1759, 2), (key1866, -2), (key1871, 2), (key1881, -2), (key1889, 2)]

theorem rowCheck13073 : row13073 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13073 := by decide +kernel

theorem rowEval13073 (x : Key → ℝ) : Integer.Sparse.eval row13073 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form22) x := by
  rw [rowCheck13073, Integer.Sparse.eval_collectBalanced, rawRowCheck13073]

def rawRow13074 : Integer.Sparse Key := [(key1748, -2), (key1743, -2), (key1881, -2), (key1371, -2), (key1367, -2), (key1748, -2), (key1719, -2), (key1881, -2), (key1866, -2), (key1367, -2), (key1743, -2), (key1719, -2), (key1520, 1), (key1515, 1), (key1759, 1), (key1743, 1), (key1889, 1), (key1881, 1), (key1380, 1), (key1376, 1), (key1759, 1), (key1725, 1), (key1889, 1), (key1871, 1), (key1380, 1), (key1367, 1), (key1520, 1), (key1493, 1), (key1881, 1), (key1871, 1), (key1376, 1), (key1367, 1), (key1515, 1), (key1493, 1), (key1743, 1), (key1725, 1)]

theorem rawRowCheck13074 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form22 = rawRow13074 := by decide +kernel

def row13074 : Integer.Sparse Key := [(key1367, -2), (key1371, -2), (key1376, 2), (key1380, 2), (key1493, 2), (key1515, 2), (key1520, 2), (key1719, -4), (key1725, 2), (key1743, -2), (key1748, -4), (key1759, 2), (key1866, -2), (key1871, 2), (key1881, -2), (key1889, 2)]

theorem rowCheck13074 : row13074 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13074 := by decide +kernel

theorem rowEval13074 (x : Key → ℝ) : Integer.Sparse.eval row13074 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck13074, Integer.Sparse.eval_collectBalanced, rawRowCheck13074]

def rawRow13075 : Integer.Sparse Key := [(key1743, -2), (key1881, -2), (key1748, -2), (key1719, -2), (key1866, -2), (key1367, -2), (key1881, -2), (key1371, -2), (key1748, -2), (key1719, -2), (key1367, -2), (key1743, -2), (key1743, 1), (key1881, 1), (key1515, 1), (key1889, 1), (key1520, 1), (key1759, 1), (key1725, 1), (key1871, 1), (key1376, 1), (key1889, 1), (key1380, 1), (key1759, 1), (key1493, 1), (key1871, 1), (key1367, 1), (key1881, 1), (key1380, 1), (key1520, 1), (key1493, 1), (key1725, 1), (key1367, 1), (key1743, 1), (key1376, 1), (key1515, 1)]

theorem rawRowCheck13075 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form22 = rawRow13075 := by decide +kernel

def row13075 : Integer.Sparse Key := [(key1367, -2), (key1371, -2), (key1376, 2), (key1380, 2), (key1493, 2), (key1515, 2), (key1520, 2), (key1719, -4), (key1725, 2), (key1743, -2), (key1748, -4), (key1759, 2), (key1866, -2), (key1871, 2), (key1881, -2), (key1889, 2)]

theorem rowCheck13075 : row13075 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13075 := by decide +kernel

theorem rowEval13075 (x : Key → ℝ) : Integer.Sparse.eval row13075 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form22) x := by
  rw [rowCheck13075, Integer.Sparse.eval_collectBalanced, rawRowCheck13075]

def rawRow13076 : Integer.Sparse Key := [(key1881, -2), (key1743, -2), (key1748, -2), (key1866, -2), (key1719, -2), (key1881, -2), (key1367, -2), (key1748, -2), (key1371, -2), (key1719, -2), (key1743, -2), (key1367, -2), (key1881, 1), (key1743, 1), (key1889, 1), (key1515, 1), (key1759, 1), (key1520, 1), (key1871, 1), (key1725, 1), (key1889, 1), (key1376, 1), (key1759, 1), (key1380, 1), (key1871, 1), (key1493, 1), (key1881, 1), (key1367, 1), (key1520, 1), (key1380, 1), (key1725, 1), (key1493, 1), (key1743, 1), (key1367, 1), (key1515, 1), (key1376, 1)]

theorem rawRowCheck13076 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form22 = rawRow13076 := by decide +kernel

def row13076 : Integer.Sparse Key := [(key1367, -2), (key1371, -2), (key1376, 2), (key1380, 2), (key1493, 2), (key1515, 2), (key1520, 2), (key1719, -4), (key1725, 2), (key1743, -2), (key1748, -4), (key1759, 2), (key1866, -2), (key1871, 2), (key1881, -2), (key1889, 2)]

theorem rowCheck13076 : row13076 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13076 := by decide +kernel

theorem rowEval13076 (x : Key → ℝ) : Integer.Sparse.eval row13076 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form22) x := by
  rw [rowCheck13076, Integer.Sparse.eval_collectBalanced, rawRowCheck13076]

def rawRow13077 : Integer.Sparse Key := [(key1748, -2), (key1881, -2), (key1743, -2), (key1748, -2), (key1881, -2), (key1371, -2), (key1866, -2), (key1367, -2), (key1719, -2), (key1743, -2), (key1367, -2), (key1719, -2), (key1759, 1), (key1889, 1), (key1520, 1), (key1881, 1), (key1515, 1), (key1743, 1), (key1759, 1), (key1889, 1), (key1380, 1), (key1871, 1), (key1376, 1), (key1725, 1), (key1520, 1), (key1881, 1), (key1380, 1), (key1871, 1), (key1367, 1), (key1493, 1), (key1515, 1), (key1743, 1), (key1376, 1), (key1725, 1), (key1367, 1), (key1493, 1)]

theorem rawRowCheck13077 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form22 = rawRow13077 := by decide +kernel

def row13077 : Integer.Sparse Key := [(key1367, -2), (key1371, -2), (key1376, 2), (key1380, 2), (key1493, 2), (key1515, 2), (key1520, 2), (key1719, -4), (key1725, 2), (key1743, -2), (key1748, -4), (key1759, 2), (key1866, -2), (key1871, 2), (key1881, -2), (key1889, 2)]

theorem rowCheck13077 : row13077 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13077 := by decide +kernel

theorem rowEval13077 (x : Key → ℝ) : Integer.Sparse.eval row13077 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck13077, Integer.Sparse.eval_collectBalanced, rawRowCheck13077]

def rawRow13078 : Integer.Sparse Key := [(key1881, -2), (key1748, -2), (key1743, -2), (key1881, -2), (key1748, -2), (key1866, -2), (key1371, -2), (key1719, -2), (key1367, -2), (key1743, -2), (key1719, -2), (key1367, -2), (key1889, 1), (key1759, 1), (key1881, 1), (key1520, 1), (key1743, 1), (key1515, 1), (key1889, 1), (key1759, 1), (key1871, 1), (key1380, 1), (key1725, 1), (key1376, 1), (key1881, 1), (key1520, 1), (key1871, 1), (key1380, 1), (key1493, 1), (key1367, 1), (key1743, 1), (key1515, 1), (key1725, 1), (key1376, 1), (key1493, 1), (key1367, 1)]

theorem rawRowCheck13078 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form22 = rawRow13078 := by decide +kernel

def row13078 : Integer.Sparse Key := [(key1367, -2), (key1371, -2), (key1376, 2), (key1380, 2), (key1493, 2), (key1515, 2), (key1520, 2), (key1719, -4), (key1725, 2), (key1743, -2), (key1748, -4), (key1759, 2), (key1866, -2), (key1871, 2), (key1881, -2), (key1889, 2)]

theorem rowCheck13078 : row13078 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13078 := by decide +kernel

theorem rowEval13078 (x : Key → ℝ) : Integer.Sparse.eval row13078 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form22) x := by
  rw [rowCheck13078, Integer.Sparse.eval_collectBalanced, rawRowCheck13078]

def rawRow13079 : Integer.Sparse Key := [(key1376, -2), (key1380, -2), (key1380, -2), (key1725, -2), (key1729, -2), (key1725, -2), (key1759, -2), (key1729, -2), (key1759, -2), (key1871, -2), (key1871, -2), (key1889, -2), (key1367, 1), (key1371, 1), (key1367, 1), (key1380, 1), (key1371, 1), (key1380, 1), (key1493, 1), (key1497, 1), (key1493, 1), (key1520, 1), (key1497, 1), (key1520, 1), (key1719, 1), (key1729, 1), (key1719, 1), (key1748, 1), (key1729, 1), (key1748, 1), (key1866, 1), (key1871, 1), (key1866, 1), (key1881, 1), (key1871, 1), (key1881, 1)]

theorem rawRowCheck13079 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form22 = rawRow13079 := by decide +kernel

def row13079 : Integer.Sparse Key := [(key1367, 2), (key1371, 2), (key1376, -2), (key1380, -2), (key1493, 2), (key1497, 2), (key1520, 2), (key1719, 2), (key1725, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1866, 2), (key1871, -2), (key1881, 2), (key1889, -2)]

theorem rowCheck13079 : row13079 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13079 := by decide +kernel

theorem rowEval13079 (x : Key → ℝ) : Integer.Sparse.eval row13079 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form22) x := by
  rw [rowCheck13079, Integer.Sparse.eval_collectBalanced, rawRowCheck13079]

def rawRow13080 : Integer.Sparse Key := [(key1380, -2), (key1376, -2), (key1380, -2), (key1729, -2), (key1725, -2), (key1759, -2), (key1725, -2), (key1759, -2), (key1729, -2), (key1871, -2), (key1889, -2), (key1871, -2), (key1371, 1), (key1367, 1), (key1380, 1), (key1367, 1), (key1380, 1), (key1371, 1), (key1497, 1), (key1493, 1), (key1520, 1), (key1493, 1), (key1520, 1), (key1497, 1), (key1729, 1), (key1719, 1), (key1748, 1), (key1719, 1), (key1748, 1), (key1729, 1), (key1871, 1), (key1866, 1), (key1881, 1), (key1866, 1), (key1881, 1), (key1871, 1)]

theorem rawRowCheck13080 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form22 = rawRow13080 := by decide +kernel

def row13080 : Integer.Sparse Key := [(key1367, 2), (key1371, 2), (key1376, -2), (key1380, -2), (key1493, 2), (key1497, 2), (key1520, 2), (key1719, 2), (key1725, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1866, 2), (key1871, -2), (key1881, 2), (key1889, -2)]

theorem rowCheck13080 : row13080 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13080 := by decide +kernel

theorem rowEval13080 (x : Key → ℝ) : Integer.Sparse.eval row13080 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck13080, Integer.Sparse.eval_collectBalanced, rawRowCheck13080]

def rawRow13081 : Integer.Sparse Key := [(key1380, -2), (key1380, -2), (key1376, -2), (key1759, -2), (key1759, -2), (key1729, -2), (key1729, -2), (key1725, -2), (key1725, -2), (key1889, -2), (key1871, -2), (key1871, -2), (key1380, 1), (key1380, 1), (key1371, 1), (key1371, 1), (key1367, 1), (key1367, 1), (key1520, 1), (key1520, 1), (key1497, 1), (key1497, 1), (key1493, 1), (key1493, 1), (key1748, 1), (key1748, 1), (key1729, 1), (key1729, 1), (key1719, 1), (key1719, 1), (key1881, 1), (key1881, 1), (key1871, 1), (key1871, 1), (key1866, 1), (key1866, 1)]

theorem rawRowCheck13081 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form22 = rawRow13081 := by decide +kernel

def row13081 : Integer.Sparse Key := [(key1367, 2), (key1371, 2), (key1376, -2), (key1380, -2), (key1493, 2), (key1497, 2), (key1520, 2), (key1719, 2), (key1725, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1866, 2), (key1871, -2), (key1881, 2), (key1889, -2)]

theorem rowCheck13081 : row13081 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13081 := by decide +kernel

theorem rowEval13081 (x : Key → ℝ) : Integer.Sparse.eval row13081 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck13081, Integer.Sparse.eval_collectBalanced, rawRowCheck13081]

def rawRow13082 : Integer.Sparse Key := [(key1725, -2), (key1729, -2), (key1871, -2), (key1376, -2), (key1380, -2), (key1725, -2), (key1759, -2), (key1871, -2), (key1889, -2), (key1380, -2), (key1729, -2), (key1759, -2), (key1493, 1), (key1497, 1), (key1719, 1), (key1729, 1), (key1866, 1), (key1871, 1), (key1367, 1), (key1371, 1), (key1719, 1), (key1748, 1), (key1866, 1), (key1881, 1), (key1367, 1), (key1380, 1), (key1493, 1), (key1520, 1), (key1871, 1), (key1881, 1), (key1371, 1), (key1380, 1), (key1497, 1), (key1520, 1), (key1729, 1), (key1748, 1)]

theorem rawRowCheck13082 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form22 = rawRow13082 := by decide +kernel

def row13082 : Integer.Sparse Key := [(key1367, 2), (key1371, 2), (key1376, -2), (key1380, -2), (key1493, 2), (key1497, 2), (key1520, 2), (key1719, 2), (key1725, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1866, 2), (key1871, -2), (key1881, 2), (key1889, -2)]

theorem rowCheck13082 : row13082 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13082 := by decide +kernel

theorem rowEval13082 (x : Key → ℝ) : Integer.Sparse.eval row13082 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form22) x := by
  rw [rowCheck13082, Integer.Sparse.eval_collectBalanced, rawRowCheck13082]

def rawRow13083 : Integer.Sparse Key := [(key1729, -2), (key1725, -2), (key1871, -2), (key1380, -2), (key1376, -2), (key1759, -2), (key1725, -2), (key1889, -2), (key1871, -2), (key1380, -2), (key1759, -2), (key1729, -2), (key1497, 1), (key1493, 1), (key1729, 1), (key1719, 1), (key1871, 1), (key1866, 1), (key1371, 1), (key1367, 1), (key1748, 1), (key1719, 1), (key1881, 1), (key1866, 1), (key1380, 1), (key1367, 1), (key1520, 1), (key1493, 1), (key1881, 1), (key1871, 1), (key1380, 1), (key1371, 1), (key1520, 1), (key1497, 1), (key1748, 1), (key1729, 1)]

theorem rawRowCheck13083 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form22 = rawRow13083 := by decide +kernel

def row13083 : Integer.Sparse Key := [(key1367, 2), (key1371, 2), (key1376, -2), (key1380, -2), (key1493, 2), (key1497, 2), (key1520, 2), (key1719, 2), (key1725, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1866, 2), (key1871, -2), (key1881, 2), (key1889, -2)]

theorem rowCheck13083 : row13083 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13083 := by decide +kernel

theorem rowEval13083 (x : Key → ℝ) : Integer.Sparse.eval row13083 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck13083, Integer.Sparse.eval_collectBalanced, rawRowCheck13083]

def rawRow13084 : Integer.Sparse Key := [(key1725, -2), (key1871, -2), (key1729, -2), (key1725, -2), (key1871, -2), (key1376, -2), (key1889, -2), (key1380, -2), (key1759, -2), (key1729, -2), (key1380, -2), (key1759, -2), (key1719, 1), (key1866, 1), (key1493, 1), (key1871, 1), (key1497, 1), (key1729, 1), (key1719, 1), (key1866, 1), (key1367, 1), (key1881, 1), (key1371, 1), (key1748, 1), (key1493, 1), (key1871, 1), (key1367, 1), (key1881, 1), (key1380, 1), (key1520, 1), (key1497, 1), (key1729, 1), (key1371, 1), (key1748, 1), (key1380, 1), (key1520, 1)]

theorem rawRowCheck13084 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form22 = rawRow13084 := by decide +kernel

def row13084 : Integer.Sparse Key := [(key1367, 2), (key1371, 2), (key1376, -2), (key1380, -2), (key1493, 2), (key1497, 2), (key1520, 2), (key1719, 2), (key1725, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1866, 2), (key1871, -2), (key1881, 2), (key1889, -2)]

theorem rowCheck13084 : row13084 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13084 := by decide +kernel

theorem rowEval13084 (x : Key → ℝ) : Integer.Sparse.eval row13084 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form22) x := by
  rw [rowCheck13084, Integer.Sparse.eval_collectBalanced, rawRowCheck13084]

def rawRow13085 : Integer.Sparse Key := [(key1871, -2), (key1725, -2), (key1729, -2), (key1871, -2), (key1725, -2), (key1889, -2), (key1376, -2), (key1759, -2), (key1380, -2), (key1729, -2), (key1759, -2), (key1380, -2), (key1866, 1), (key1719, 1), (key1871, 1), (key1493, 1), (key1729, 1), (key1497, 1), (key1866, 1), (key1719, 1), (key1881, 1), (key1367, 1), (key1748, 1), (key1371, 1), (key1871, 1), (key1493, 1), (key1881, 1), (key1367, 1), (key1520, 1), (key1380, 1), (key1729, 1), (key1497, 1), (key1748, 1), (key1371, 1), (key1520, 1), (key1380, 1)]

theorem rawRowCheck13085 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form22 = rawRow13085 := by decide +kernel

def row13085 : Integer.Sparse Key := [(key1367, 2), (key1371, 2), (key1376, -2), (key1380, -2), (key1493, 2), (key1497, 2), (key1520, 2), (key1719, 2), (key1725, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1866, 2), (key1871, -2), (key1881, 2), (key1889, -2)]

theorem rowCheck13085 : row13085 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13085 := by decide +kernel

theorem rowEval13085 (x : Key → ℝ) : Integer.Sparse.eval row13085 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form22) x := by
  rw [rowCheck13085, Integer.Sparse.eval_collectBalanced, rawRowCheck13085]

def rawRow13086 : Integer.Sparse Key := [(key1729, -2), (key1871, -2), (key1725, -2), (key1759, -2), (key1889, -2), (key1380, -2), (key1871, -2), (key1376, -2), (key1725, -2), (key1759, -2), (key1380, -2), (key1729, -2), (key1729, 1), (key1871, 1), (key1497, 1), (key1866, 1), (key1493, 1), (key1719, 1), (key1748, 1), (key1881, 1), (key1371, 1), (key1866, 1), (key1367, 1), (key1719, 1), (key1520, 1), (key1881, 1), (key1380, 1), (key1871, 1), (key1367, 1), (key1493, 1), (key1520, 1), (key1748, 1), (key1380, 1), (key1729, 1), (key1371, 1), (key1497, 1)]

theorem rawRowCheck13086 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form22 = rawRow13086 := by decide +kernel

def row13086 : Integer.Sparse Key := [(key1367, 2), (key1371, 2), (key1376, -2), (key1380, -2), (key1493, 2), (key1497, 2), (key1520, 2), (key1719, 2), (key1725, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1866, 2), (key1871, -2), (key1881, 2), (key1889, -2)]

theorem rowCheck13086 : row13086 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13086 := by decide +kernel

theorem rowEval13086 (x : Key → ℝ) : Integer.Sparse.eval row13086 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck13086, Integer.Sparse.eval_collectBalanced, rawRowCheck13086]

def rawRow13087 : Integer.Sparse Key := [(key1871, -2), (key1729, -2), (key1725, -2), (key1889, -2), (key1759, -2), (key1871, -2), (key1380, -2), (key1725, -2), (key1376, -2), (key1759, -2), (key1729, -2), (key1380, -2), (key1871, 1), (key1729, 1), (key1866, 1), (key1497, 1), (key1719, 1), (key1493, 1), (key1881, 1), (key1748, 1), (key1866, 1), (key1371, 1), (key1719, 1), (key1367, 1), (key1881, 1), (key1520, 1), (key1871, 1), (key1380, 1), (key1493, 1), (key1367, 1), (key1748, 1), (key1520, 1), (key1729, 1), (key1380, 1), (key1497, 1), (key1371, 1)]

theorem rawRowCheck13087 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form22 = rawRow13087 := by decide +kernel

def row13087 : Integer.Sparse Key := [(key1367, 2), (key1371, 2), (key1376, -2), (key1380, -2), (key1493, 2), (key1497, 2), (key1520, 2), (key1719, 2), (key1725, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1866, 2), (key1871, -2), (key1881, 2), (key1889, -2)]

theorem rowCheck13087 : row13087 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13087 := by decide +kernel

theorem rowEval13087 (x : Key → ℝ) : Integer.Sparse.eval row13087 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form22) x := by
  rw [rowCheck13087, Integer.Sparse.eval_collectBalanced, rawRowCheck13087]

def rawRow13088 : Integer.Sparse Key := [(key1759, -2), (key1759, -2), (key1889, -2), (key1380, -2), (key1380, -2), (key1729, -2), (key1729, -2), (key1871, -2), (key1871, -2), (key1376, -2), (key1725, -2), (key1725, -2), (key1520, 1), (key1520, 1), (key1748, 1), (key1748, 1), (key1881, 1), (key1881, 1), (key1380, 1), (key1380, 1), (key1729, 1), (key1729, 1), (key1871, 1), (key1871, 1), (key1371, 1), (key1371, 1), (key1497, 1), (key1497, 1), (key1866, 1), (key1866, 1), (key1367, 1), (key1367, 1), (key1493, 1), (key1493, 1), (key1719, 1), (key1719, 1)]

theorem rawRowCheck13088 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form22 = rawRow13088 := by decide +kernel

def row13088 : Integer.Sparse Key := [(key1367, 2), (key1371, 2), (key1376, -2), (key1380, -2), (key1493, 2), (key1497, 2), (key1520, 2), (key1719, 2), (key1725, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1866, 2), (key1871, -2), (key1881, 2), (key1889, -2)]

theorem rowCheck13088 : row13088 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13088 := by decide +kernel

theorem rowEval13088 (x : Key → ℝ) : Integer.Sparse.eval row13088 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck13088, Integer.Sparse.eval_collectBalanced, rawRowCheck13088]

def rawRow13089 : Integer.Sparse Key := [(key1759, -2), (key1889, -2), (key1759, -2), (key1729, -2), (key1871, -2), (key1380, -2), (key1871, -2), (key1380, -2), (key1729, -2), (key1725, -2), (key1376, -2), (key1725, -2), (key1748, 1), (key1881, 1), (key1520, 1), (key1881, 1), (key1520, 1), (key1748, 1), (key1729, 1), (key1871, 1), (key1380, 1), (key1871, 1), (key1380, 1), (key1729, 1), (key1497, 1), (key1866, 1), (key1371, 1), (key1866, 1), (key1371, 1), (key1497, 1), (key1493, 1), (key1719, 1), (key1367, 1), (key1719, 1), (key1367, 1), (key1493, 1)]

theorem rawRowCheck13089 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form22 = rawRow13089 := by decide +kernel

def row13089 : Integer.Sparse Key := [(key1367, 2), (key1371, 2), (key1376, -2), (key1380, -2), (key1493, 2), (key1497, 2), (key1520, 2), (key1719, 2), (key1725, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1866, 2), (key1871, -2), (key1881, 2), (key1889, -2)]

theorem rowCheck13089 : row13089 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13089 := by decide +kernel

theorem rowEval13089 (x : Key → ℝ) : Integer.Sparse.eval row13089 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck13089, Integer.Sparse.eval_collectBalanced, rawRowCheck13089]

def rawRow13090 : Integer.Sparse Key := [(key1889, -2), (key1759, -2), (key1759, -2), (key1871, -2), (key1729, -2), (key1871, -2), (key1380, -2), (key1729, -2), (key1380, -2), (key1725, -2), (key1725, -2), (key1376, -2), (key1881, 1), (key1748, 1), (key1881, 1), (key1520, 1), (key1748, 1), (key1520, 1), (key1871, 1), (key1729, 1), (key1871, 1), (key1380, 1), (key1729, 1), (key1380, 1), (key1866, 1), (key1497, 1), (key1866, 1), (key1371, 1), (key1497, 1), (key1371, 1), (key1719, 1), (key1493, 1), (key1719, 1), (key1367, 1), (key1493, 1), (key1367, 1)]

theorem rawRowCheck13090 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form22 = rawRow13090 := by decide +kernel

def row13090 : Integer.Sparse Key := [(key1367, 2), (key1371, 2), (key1376, -2), (key1380, -2), (key1493, 2), (key1497, 2), (key1520, 2), (key1719, 2), (key1725, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1866, 2), (key1871, -2), (key1881, 2), (key1889, -2)]

theorem rowCheck13090 : row13090 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13090 := by decide +kernel

theorem rowEval13090 (x : Key → ℝ) : Integer.Sparse.eval row13090 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form22) x := by
  rw [rowCheck13090, Integer.Sparse.eval_collectBalanced, rawRowCheck13090]

def rawRow13091 : Integer.Sparse Key := [(key1703, -4), (key1707, -4), (key1707, -4), (key1856, -4), (key1856, -4), (key1858, -4), (key1280, 2), (key1284, 2), (key1284, 2), (key1703, 2), (key1757, 2), (key1757, 2), (key1856, 2), (key1856, 2), (key1887, 2), (key1887, 2), (key1890, 2), (key1890, 2)]

theorem rawRowCheck13091 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form23 = rawRow13091 := by decide +kernel

def row13091 : Integer.Sparse Key := [(key1280, 2), (key1284, 4), (key1703, -2), (key1707, -8), (key1757, 4), (key1856, -4), (key1858, -4), (key1887, 4), (key1890, 4)]

theorem rowCheck13091 : row13091 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13091 := by decide +kernel

theorem rowEval13091 (x : Key → ℝ) : Integer.Sparse.eval row13091 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form23) x := by
  rw [rowCheck13091, Integer.Sparse.eval_collectBalanced, rawRowCheck13091]

def rawRow13092 : Integer.Sparse Key := [(key1707, -4), (key1703, -4), (key1707, -4), (key1856, -4), (key1858, -4), (key1856, -4), (key1284, 2), (key1280, 2), (key1284, 2), (key1757, 2), (key1703, 2), (key1757, 2), (key1887, 2), (key1890, 2), (key1856, 2), (key1890, 2), (key1856, 2), (key1887, 2)]

theorem rawRowCheck13092 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form23 = rawRow13092 := by decide +kernel

def row13092 : Integer.Sparse Key := [(key1280, 2), (key1284, 4), (key1703, -2), (key1707, -8), (key1757, 4), (key1856, -4), (key1858, -4), (key1887, 4), (key1890, 4)]

theorem rowCheck13092 : row13092 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13092 := by decide +kernel

theorem rowEval13092 (x : Key → ℝ) : Integer.Sparse.eval row13092 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form23) x := by
  rw [rowCheck13092, Integer.Sparse.eval_collectBalanced, rawRowCheck13092]

def rawRow13093 : Integer.Sparse Key := [(key1707, -4), (key1707, -4), (key1703, -4), (key1858, -4), (key1856, -4), (key1856, -4), (key1284, 2), (key1284, 2), (key1280, 2), (key1757, 2), (key1757, 2), (key1703, 2), (key1890, 2), (key1887, 2), (key1890, 2), (key1856, 2), (key1887, 2), (key1856, 2)]

theorem rawRowCheck13093 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form23 = rawRow13093 := by decide +kernel

def row13093 : Integer.Sparse Key := [(key1280, 2), (key1284, 4), (key1703, -2), (key1707, -8), (key1757, 4), (key1856, -4), (key1858, -4), (key1887, 4), (key1890, 4)]

theorem rowCheck13093 : row13093 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13093 := by decide +kernel

theorem rowEval13093 (x : Key → ℝ) : Integer.Sparse.eval row13093 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form23) x := by
  rw [rowCheck13093, Integer.Sparse.eval_collectBalanced, rawRowCheck13093]

def rawRow13094 : Integer.Sparse Key := [(key1703, -4), (key1856, -4), (key1856, -4), (key1707, -4), (key1707, -4), (key1858, -4), (key1703, 2), (key1856, 2), (key1856, 2), (key1280, 2), (key1887, 2), (key1887, 2), (key1284, 2), (key1284, 2), (key1757, 2), (key1757, 2), (key1890, 2), (key1890, 2)]

theorem rawRowCheck13094 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form23 = rawRow13094 := by decide +kernel

def row13094 : Integer.Sparse Key := [(key1280, 2), (key1284, 4), (key1703, -2), (key1707, -8), (key1757, 4), (key1856, -4), (key1858, -4), (key1887, 4), (key1890, 4)]

theorem rowCheck13094 : row13094 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13094 := by decide +kernel

theorem rowEval13094 (x : Key → ℝ) : Integer.Sparse.eval row13094 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form23) x := by
  rw [rowCheck13094, Integer.Sparse.eval_collectBalanced, rawRowCheck13094]

def rawRow13095 : Integer.Sparse Key := [(key1856, -4), (key1703, -4), (key1856, -4), (key1707, -4), (key1858, -4), (key1707, -4), (key1856, 2), (key1703, 2), (key1856, 2), (key1887, 2), (key1280, 2), (key1887, 2), (key1757, 2), (key1890, 2), (key1284, 2), (key1890, 2), (key1284, 2), (key1757, 2)]

theorem rawRowCheck13095 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form23 = rawRow13095 := by decide +kernel

def row13095 : Integer.Sparse Key := [(key1280, 2), (key1284, 4), (key1703, -2), (key1707, -8), (key1757, 4), (key1856, -4), (key1858, -4), (key1887, 4), (key1890, 4)]

theorem rowCheck13095 : row13095 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13095 := by decide +kernel

theorem rowEval13095 (x : Key → ℝ) : Integer.Sparse.eval row13095 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form23) x := by
  rw [rowCheck13095, Integer.Sparse.eval_collectBalanced, rawRowCheck13095]

def rawRow13096 : Integer.Sparse Key := [(key1856, -4), (key1856, -4), (key1703, -4), (key1858, -4), (key1707, -4), (key1707, -4), (key1856, 2), (key1856, 2), (key1703, 2), (key1887, 2), (key1887, 2), (key1280, 2), (key1890, 2), (key1757, 2), (key1890, 2), (key1284, 2), (key1757, 2), (key1284, 2)]

theorem rawRowCheck13096 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form23 = rawRow13096 := by decide +kernel

def row13096 : Integer.Sparse Key := [(key1280, 2), (key1284, 4), (key1703, -2), (key1707, -8), (key1757, 4), (key1856, -4), (key1858, -4), (key1887, 4), (key1890, 4)]

theorem rowCheck13096 : row13096 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13096 := by decide +kernel

theorem rowEval13096 (x : Key → ℝ) : Integer.Sparse.eval row13096 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form23) x := by
  rw [rowCheck13096, Integer.Sparse.eval_collectBalanced, rawRowCheck13096]

def rawRow13097 : Integer.Sparse Key := [(key1707, -4), (key1856, -4), (key1858, -4), (key1703, -4), (key1707, -4), (key1856, -4), (key1757, 2), (key1887, 2), (key1890, 2), (key1284, 2), (key1856, 2), (key1890, 2), (key1280, 2), (key1284, 2), (key1703, 2), (key1757, 2), (key1856, 2), (key1887, 2)]

theorem rawRowCheck13097 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form23 = rawRow13097 := by decide +kernel

def row13097 : Integer.Sparse Key := [(key1280, 2), (key1284, 4), (key1703, -2), (key1707, -8), (key1757, 4), (key1856, -4), (key1858, -4), (key1887, 4), (key1890, 4)]

theorem rowCheck13097 : row13097 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13097 := by decide +kernel

theorem rowEval13097 (x : Key → ℝ) : Integer.Sparse.eval row13097 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form23) x := by
  rw [rowCheck13097, Integer.Sparse.eval_collectBalanced, rawRowCheck13097]

def rawRow13098 : Integer.Sparse Key := [(key1707, -4), (key1858, -4), (key1856, -4), (key1707, -4), (key1703, -4), (key1856, -4), (key1757, 2), (key1890, 2), (key1887, 2), (key1284, 2), (key1890, 2), (key1856, 2), (key1284, 2), (key1280, 2), (key1757, 2), (key1703, 2), (key1887, 2), (key1856, 2)]

theorem rawRowCheck13098 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form23 = rawRow13098 := by decide +kernel

def row13098 : Integer.Sparse Key := [(key1280, 2), (key1284, 4), (key1703, -2), (key1707, -8), (key1757, 4), (key1856, -4), (key1858, -4), (key1887, 4), (key1890, 4)]

theorem rowCheck13098 : row13098 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13098 := by decide +kernel

theorem rowEval13098 (x : Key → ℝ) : Integer.Sparse.eval row13098 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form23) x := by
  rw [rowCheck13098, Integer.Sparse.eval_collectBalanced, rawRowCheck13098]

def rawRow13099 : Integer.Sparse Key := [(key1856, -4), (key1707, -4), (key1858, -4), (key1703, -4), (key1856, -4), (key1707, -4), (key1887, 2), (key1757, 2), (key1890, 2), (key1856, 2), (key1284, 2), (key1890, 2), (key1703, 2), (key1856, 2), (key1280, 2), (key1887, 2), (key1284, 2), (key1757, 2)]

theorem rawRowCheck13099 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form23 = rawRow13099 := by decide +kernel

def row13099 : Integer.Sparse Key := [(key1280, 2), (key1284, 4), (key1703, -2), (key1707, -8), (key1757, 4), (key1856, -4), (key1858, -4), (key1887, 4), (key1890, 4)]

theorem rowCheck13099 : row13099 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13099 := by decide +kernel

theorem rowEval13099 (x : Key → ℝ) : Integer.Sparse.eval row13099 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form23) x := by
  rw [rowCheck13099, Integer.Sparse.eval_collectBalanced, rawRowCheck13099]

def rawRow13100 : Integer.Sparse Key := [(key1856, -4), (key1858, -4), (key1707, -4), (key1856, -4), (key1703, -4), (key1707, -4), (key1887, 2), (key1890, 2), (key1757, 2), (key1856, 2), (key1890, 2), (key1284, 2), (key1856, 2), (key1703, 2), (key1887, 2), (key1280, 2), (key1757, 2), (key1284, 2)]

theorem rawRowCheck13100 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form23 = rawRow13100 := by decide +kernel

def row13100 : Integer.Sparse Key := [(key1280, 2), (key1284, 4), (key1703, -2), (key1707, -8), (key1757, 4), (key1856, -4), (key1858, -4), (key1887, 4), (key1890, 4)]

theorem rowCheck13100 : row13100 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13100 := by decide +kernel

theorem rowEval13100 (x : Key → ℝ) : Integer.Sparse.eval row13100 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form23) x := by
  rw [rowCheck13100, Integer.Sparse.eval_collectBalanced, rawRowCheck13100]

def rawRow13101 : Integer.Sparse Key := [(key1858, -4), (key1707, -4), (key1856, -4), (key1707, -4), (key1856, -4), (key1703, -4), (key1890, 2), (key1757, 2), (key1887, 2), (key1890, 2), (key1284, 2), (key1856, 2), (key1757, 2), (key1887, 2), (key1284, 2), (key1856, 2), (key1280, 2), (key1703, 2)]

theorem rawRowCheck13101 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form23 = rawRow13101 := by decide +kernel

def row13101 : Integer.Sparse Key := [(key1280, 2), (key1284, 4), (key1703, -2), (key1707, -8), (key1757, 4), (key1856, -4), (key1858, -4), (key1887, 4), (key1890, 4)]

theorem rowCheck13101 : row13101 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13101 := by decide +kernel

theorem rowEval13101 (x : Key → ℝ) : Integer.Sparse.eval row13101 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form23) x := by
  rw [rowCheck13101, Integer.Sparse.eval_collectBalanced, rawRowCheck13101]

def rawRow13102 : Integer.Sparse Key := [(key1858, -4), (key1856, -4), (key1707, -4), (key1856, -4), (key1707, -4), (key1703, -4), (key1890, 2), (key1887, 2), (key1757, 2), (key1890, 2), (key1856, 2), (key1284, 2), (key1887, 2), (key1757, 2), (key1856, 2), (key1284, 2), (key1703, 2), (key1280, 2)]

theorem rawRowCheck13102 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form23 = rawRow13102 := by decide +kernel

def row13102 : Integer.Sparse Key := [(key1280, 2), (key1284, 4), (key1703, -2), (key1707, -8), (key1757, 4), (key1856, -4), (key1858, -4), (key1887, 4), (key1890, 4)]

theorem rowCheck13102 : row13102 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13102 := by decide +kernel

theorem rowEval13102 (x : Key → ℝ) : Integer.Sparse.eval row13102 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form23) x := by
  rw [rowCheck13102, Integer.Sparse.eval_collectBalanced, rawRowCheck13102]

def rawRow13103 : Integer.Sparse Key := [(key1757, -4), (key1757, -4), (key1760, -4), (key1887, -4), (key1890, -4), (key1890, -4), (key1284, 2), (key1284, 2), (key1286, 2), (key1707, 2), (key1707, 2), (key1760, 2), (key1856, 2), (key1858, 2), (key1856, 2), (key1890, 2), (key1858, 2), (key1890, 2)]

theorem rawRowCheck13103 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form23 = rawRow13103 := by decide +kernel

def row13103 : Integer.Sparse Key := [(key1284, 4), (key1286, 2), (key1707, 4), (key1757, -8), (key1760, -2), (key1856, 4), (key1858, 4), (key1887, -4), (key1890, -4)]

theorem rowCheck13103 : row13103 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13103 := by decide +kernel

theorem rowEval13103 (x : Key → ℝ) : Integer.Sparse.eval row13103 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form23) x := by
  rw [rowCheck13103, Integer.Sparse.eval_collectBalanced, rawRowCheck13103]

def rawRow13104 : Integer.Sparse Key := [(key1757, -4), (key1760, -4), (key1757, -4), (key1890, -4), (key1887, -4), (key1890, -4), (key1284, 2), (key1286, 2), (key1284, 2), (key1707, 2), (key1760, 2), (key1707, 2), (key1858, 2), (key1856, 2), (key1890, 2), (key1856, 2), (key1890, 2), (key1858, 2)]

theorem rawRowCheck13104 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form23 = rawRow13104 := by decide +kernel

def row13104 : Integer.Sparse Key := [(key1284, 4), (key1286, 2), (key1707, 4), (key1757, -8), (key1760, -2), (key1856, 4), (key1858, 4), (key1887, -4), (key1890, -4)]

theorem rowCheck13104 : row13104 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13104 := by decide +kernel

theorem rowEval13104 (x : Key → ℝ) : Integer.Sparse.eval row13104 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form23) x := by
  rw [rowCheck13104, Integer.Sparse.eval_collectBalanced, rawRowCheck13104]

def rawRow13105 : Integer.Sparse Key := [(key1760, -4), (key1757, -4), (key1757, -4), (key1890, -4), (key1890, -4), (key1887, -4), (key1286, 2), (key1284, 2), (key1284, 2), (key1760, 2), (key1707, 2), (key1707, 2), (key1890, 2), (key1890, 2), (key1858, 2), (key1858, 2), (key1856, 2), (key1856, 2)]

theorem rawRowCheck13105 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form23 = rawRow13105 := by decide +kernel

def row13105 : Integer.Sparse Key := [(key1284, 4), (key1286, 2), (key1707, 4), (key1757, -8), (key1760, -2), (key1856, 4), (key1858, 4), (key1887, -4), (key1890, -4)]

theorem rowCheck13105 : row13105 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13105 := by decide +kernel

theorem rowEval13105 (x : Key → ℝ) : Integer.Sparse.eval row13105 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form23) x := by
  rw [rowCheck13105, Integer.Sparse.eval_collectBalanced, rawRowCheck13105]

def rawRow13106 : Integer.Sparse Key := [(key1757, -4), (key1887, -4), (key1890, -4), (key1757, -4), (key1760, -4), (key1890, -4), (key1707, 2), (key1856, 2), (key1858, 2), (key1284, 2), (key1856, 2), (key1890, 2), (key1284, 2), (key1286, 2), (key1707, 2), (key1760, 2), (key1858, 2), (key1890, 2)]

theorem rawRowCheck13106 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form23 = rawRow13106 := by decide +kernel

def row13106 : Integer.Sparse Key := [(key1284, 4), (key1286, 2), (key1707, 4), (key1757, -8), (key1760, -2), (key1856, 4), (key1858, 4), (key1887, -4), (key1890, -4)]

theorem rowCheck13106 : row13106 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13106 := by decide +kernel

theorem rowEval13106 (x : Key → ℝ) : Integer.Sparse.eval row13106 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form23) x := by
  rw [rowCheck13106, Integer.Sparse.eval_collectBalanced, rawRowCheck13106]

def rawRow13107 : Integer.Sparse Key := [(key1757, -4), (key1890, -4), (key1887, -4), (key1760, -4), (key1757, -4), (key1890, -4), (key1707, 2), (key1858, 2), (key1856, 2), (key1284, 2), (key1890, 2), (key1856, 2), (key1286, 2), (key1284, 2), (key1760, 2), (key1707, 2), (key1890, 2), (key1858, 2)]

theorem rawRowCheck13107 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form23 = rawRow13107 := by decide +kernel

def row13107 : Integer.Sparse Key := [(key1284, 4), (key1286, 2), (key1707, 4), (key1757, -8), (key1760, -2), (key1856, 4), (key1858, 4), (key1887, -4), (key1890, -4)]

theorem rowCheck13107 : row13107 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13107 := by decide +kernel

theorem rowEval13107 (x : Key → ℝ) : Integer.Sparse.eval row13107 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form23) x := by
  rw [rowCheck13107, Integer.Sparse.eval_collectBalanced, rawRowCheck13107]

def rawRow13108 : Integer.Sparse Key := [(key1887, -4), (key1757, -4), (key1890, -4), (key1757, -4), (key1890, -4), (key1760, -4), (key1856, 2), (key1707, 2), (key1858, 2), (key1856, 2), (key1284, 2), (key1890, 2), (key1707, 2), (key1858, 2), (key1284, 2), (key1890, 2), (key1286, 2), (key1760, 2)]

theorem rawRowCheck13108 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form23 = rawRow13108 := by decide +kernel

def row13108 : Integer.Sparse Key := [(key1284, 4), (key1286, 2), (key1707, 4), (key1757, -8), (key1760, -2), (key1856, 4), (key1858, 4), (key1887, -4), (key1890, -4)]

theorem rowCheck13108 : row13108 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13108 := by decide +kernel

theorem rowEval13108 (x : Key → ℝ) : Integer.Sparse.eval row13108 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form23) x := by
  rw [rowCheck13108, Integer.Sparse.eval_collectBalanced, rawRowCheck13108]

def rawRow13109 : Integer.Sparse Key := [(key1887, -4), (key1890, -4), (key1757, -4), (key1890, -4), (key1757, -4), (key1760, -4), (key1856, 2), (key1858, 2), (key1707, 2), (key1856, 2), (key1890, 2), (key1284, 2), (key1858, 2), (key1707, 2), (key1890, 2), (key1284, 2), (key1760, 2), (key1286, 2)]

theorem rawRowCheck13109 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form23 = rawRow13109 := by decide +kernel

def row13109 : Integer.Sparse Key := [(key1284, 4), (key1286, 2), (key1707, 4), (key1757, -8), (key1760, -2), (key1856, 4), (key1858, 4), (key1887, -4), (key1890, -4)]

theorem rowCheck13109 : row13109 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13109 := by decide +kernel

theorem rowEval13109 (x : Key → ℝ) : Integer.Sparse.eval row13109 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form23) x := by
  rw [rowCheck13109, Integer.Sparse.eval_collectBalanced, rawRowCheck13109]

def rawRow13110 : Integer.Sparse Key := [(key1890, -4), (key1757, -4), (key1887, -4), (key1760, -4), (key1890, -4), (key1757, -4), (key1858, 2), (key1707, 2), (key1856, 2), (key1890, 2), (key1284, 2), (key1856, 2), (key1760, 2), (key1890, 2), (key1286, 2), (key1858, 2), (key1284, 2), (key1707, 2)]

theorem rawRowCheck13110 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form23 = rawRow13110 := by decide +kernel

def row13110 : Integer.Sparse Key := [(key1284, 4), (key1286, 2), (key1707, 4), (key1757, -8), (key1760, -2), (key1856, 4), (key1858, 4), (key1887, -4), (key1890, -4)]

theorem rowCheck13110 : row13110 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13110 := by decide +kernel

theorem rowEval13110 (x : Key → ℝ) : Integer.Sparse.eval row13110 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form23) x := by
  rw [rowCheck13110, Integer.Sparse.eval_collectBalanced, rawRowCheck13110]

def rawRow13111 : Integer.Sparse Key := [(key1890, -4), (key1887, -4), (key1757, -4), (key1890, -4), (key1760, -4), (key1757, -4), (key1858, 2), (key1856, 2), (key1707, 2), (key1890, 2), (key1856, 2), (key1284, 2), (key1890, 2), (key1760, 2), (key1858, 2), (key1286, 2), (key1707, 2), (key1284, 2)]

theorem rawRowCheck13111 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form23 = rawRow13111 := by decide +kernel

def row13111 : Integer.Sparse Key := [(key1284, 4), (key1286, 2), (key1707, 4), (key1757, -8), (key1760, -2), (key1856, 4), (key1858, 4), (key1887, -4), (key1890, -4)]

theorem rowCheck13111 : row13111 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13111 := by decide +kernel

theorem rowEval13111 (x : Key → ℝ) : Integer.Sparse.eval row13111 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form23) x := by
  rw [rowCheck13111, Integer.Sparse.eval_collectBalanced, rawRowCheck13111]

def rawRow13112 : Integer.Sparse Key := [(key1760, -4), (key1890, -4), (key1890, -4), (key1757, -4), (key1757, -4), (key1887, -4), (key1760, 2), (key1890, 2), (key1890, 2), (key1286, 2), (key1858, 2), (key1858, 2), (key1284, 2), (key1284, 2), (key1707, 2), (key1707, 2), (key1856, 2), (key1856, 2)]

theorem rawRowCheck13112 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form23 = rawRow13112 := by decide +kernel

def row13112 : Integer.Sparse Key := [(key1284, 4), (key1286, 2), (key1707, 4), (key1757, -8), (key1760, -2), (key1856, 4), (key1858, 4), (key1887, -4), (key1890, -4)]

theorem rowCheck13112 : row13112 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13112 := by decide +kernel

theorem rowEval13112 (x : Key → ℝ) : Integer.Sparse.eval row13112 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form23) x := by
  rw [rowCheck13112, Integer.Sparse.eval_collectBalanced, rawRowCheck13112]

def rawRow13113 : Integer.Sparse Key := [(key1890, -4), (key1760, -4), (key1890, -4), (key1757, -4), (key1887, -4), (key1757, -4), (key1890, 2), (key1760, 2), (key1890, 2), (key1858, 2), (key1286, 2), (key1858, 2), (key1707, 2), (key1856, 2), (key1284, 2), (key1856, 2), (key1284, 2), (key1707, 2)]

theorem rawRowCheck13113 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form23 = rawRow13113 := by decide +kernel

def row13113 : Integer.Sparse Key := [(key1284, 4), (key1286, 2), (key1707, 4), (key1757, -8), (key1760, -2), (key1856, 4), (key1858, 4), (key1887, -4), (key1890, -4)]

theorem rowCheck13113 : row13113 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13113 := by decide +kernel

theorem rowEval13113 (x : Key → ℝ) : Integer.Sparse.eval row13113 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form23) x := by
  rw [rowCheck13113, Integer.Sparse.eval_collectBalanced, rawRowCheck13113]

def rawRow13114 : Integer.Sparse Key := [(key1890, -4), (key1890, -4), (key1760, -4), (key1887, -4), (key1757, -4), (key1757, -4), (key1890, 2), (key1890, 2), (key1760, 2), (key1858, 2), (key1858, 2), (key1286, 2), (key1856, 2), (key1707, 2), (key1856, 2), (key1284, 2), (key1707, 2), (key1284, 2)]

theorem rawRowCheck13114 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form23 = rawRow13114 := by decide +kernel

def row13114 : Integer.Sparse Key := [(key1284, 4), (key1286, 2), (key1707, 4), (key1757, -8), (key1760, -2), (key1856, 4), (key1858, 4), (key1887, -4), (key1890, -4)]

theorem rowCheck13114 : row13114 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13114 := by decide +kernel

theorem rowEval13114 (x : Key → ℝ) : Integer.Sparse.eval row13114 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form23) x := by
  rw [rowCheck13114, Integer.Sparse.eval_collectBalanced, rawRowCheck13114]

def rawRow13115 : Integer.Sparse Key := [(key524, -24), (key296, 6), (key524, 6), (key555, 6), (key555, 6)]

theorem rawRowCheck13115 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form24 = rawRow13115 := by decide +kernel

def row13115 : Integer.Sparse Key := [(key296, 6), (key524, -18), (key555, 12)]

theorem rowCheck13115 : row13115 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13115 := by decide +kernel

theorem rowEval13115 (x : Key → ℝ) : Integer.Sparse.eval row13115 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form24) x := by
  rw [rowCheck13115, Integer.Sparse.eval_collectBalanced, rawRowCheck13115]

def rawRow13116 : Integer.Sparse Key := [(key524, -24), (key296, 6), (key555, 6), (key524, 6), (key555, 6)]

theorem rawRowCheck13116 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form24 = rawRow13116 := by decide +kernel

def row13116 : Integer.Sparse Key := [(key296, 6), (key524, -18), (key555, 12)]

theorem rowCheck13116 : row13116 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13116 := by decide +kernel

theorem rowEval13116 (x : Key → ℝ) : Integer.Sparse.eval row13116 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form24) x := by
  rw [rowCheck13116, Integer.Sparse.eval_collectBalanced, rawRowCheck13116]

def rawRow13117 : Integer.Sparse Key := [(key524, -24), (key296, 6), (key555, 6), (key555, 6), (key524, 6)]

theorem rawRowCheck13117 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form24 = rawRow13117 := by decide +kernel

def row13117 : Integer.Sparse Key := [(key296, 6), (key524, -18), (key555, 12)]

theorem rowCheck13117 : row13117 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13117 := by decide +kernel

theorem rowEval13117 (x : Key → ℝ) : Integer.Sparse.eval row13117 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form24) x := by
  rw [rowCheck13117, Integer.Sparse.eval_collectBalanced, rawRowCheck13117]

def rawRow13118 : Integer.Sparse Key := [(key524, -24), (key524, 6), (key296, 6), (key555, 6), (key555, 6)]

theorem rawRowCheck13118 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form24 = rawRow13118 := by decide +kernel

def row13118 : Integer.Sparse Key := [(key296, 6), (key524, -18), (key555, 12)]

theorem rowCheck13118 : row13118 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13118 := by decide +kernel

theorem rowEval13118 (x : Key → ℝ) : Integer.Sparse.eval row13118 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form24) x := by
  rw [rowCheck13118, Integer.Sparse.eval_collectBalanced, rawRowCheck13118]

def rawRow13119 : Integer.Sparse Key := [(key524, -24), (key524, 6), (key555, 6), (key296, 6), (key555, 6)]

theorem rawRowCheck13119 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form24 = rawRow13119 := by decide +kernel

def row13119 : Integer.Sparse Key := [(key296, 6), (key524, -18), (key555, 12)]

theorem rowCheck13119 : row13119 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13119 := by decide +kernel

theorem rowEval13119 (x : Key → ℝ) : Integer.Sparse.eval row13119 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form24) x := by
  rw [rowCheck13119, Integer.Sparse.eval_collectBalanced, rawRowCheck13119]

def rawRow13120 : Integer.Sparse Key := [(key524, -24), (key524, 6), (key555, 6), (key555, 6), (key296, 6)]

theorem rawRowCheck13120 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form24 = rawRow13120 := by decide +kernel

def row13120 : Integer.Sparse Key := [(key296, 6), (key524, -18), (key555, 12)]

theorem rowCheck13120 : row13120 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13120 := by decide +kernel

theorem rowEval13120 (x : Key → ℝ) : Integer.Sparse.eval row13120 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form24) x := by
  rw [rowCheck13120, Integer.Sparse.eval_collectBalanced, rawRowCheck13120]

def rawRow13121 : Integer.Sparse Key := [(key524, -24), (key555, 6), (key296, 6), (key524, 6), (key555, 6)]

theorem rawRowCheck13121 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form24 = rawRow13121 := by decide +kernel

def row13121 : Integer.Sparse Key := [(key296, 6), (key524, -18), (key555, 12)]

theorem rowCheck13121 : row13121 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13121 := by decide +kernel

theorem rowEval13121 (x : Key → ℝ) : Integer.Sparse.eval row13121 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form24) x := by
  rw [rowCheck13121, Integer.Sparse.eval_collectBalanced, rawRowCheck13121]

def rawRow13122 : Integer.Sparse Key := [(key524, -24), (key555, 6), (key296, 6), (key555, 6), (key524, 6)]

theorem rawRowCheck13122 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form24 = rawRow13122 := by decide +kernel

def row13122 : Integer.Sparse Key := [(key296, 6), (key524, -18), (key555, 12)]

theorem rowCheck13122 : row13122 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13122 := by decide +kernel

theorem rowEval13122 (x : Key → ℝ) : Integer.Sparse.eval row13122 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form24) x := by
  rw [rowCheck13122, Integer.Sparse.eval_collectBalanced, rawRowCheck13122]

def rawRow13123 : Integer.Sparse Key := [(key524, -24), (key555, 6), (key524, 6), (key296, 6), (key555, 6)]

theorem rawRowCheck13123 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form24 = rawRow13123 := by decide +kernel

def row13123 : Integer.Sparse Key := [(key296, 6), (key524, -18), (key555, 12)]

theorem rowCheck13123 : row13123 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13123 := by decide +kernel

theorem rowEval13123 (x : Key → ℝ) : Integer.Sparse.eval row13123 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form24) x := by
  rw [rowCheck13123, Integer.Sparse.eval_collectBalanced, rawRowCheck13123]

def rawRow13124 : Integer.Sparse Key := [(key524, -24), (key555, 6), (key524, 6), (key555, 6), (key296, 6)]

theorem rawRowCheck13124 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form24 = rawRow13124 := by decide +kernel

def row13124 : Integer.Sparse Key := [(key296, 6), (key524, -18), (key555, 12)]

theorem rowCheck13124 : row13124 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13124 := by decide +kernel

theorem rowEval13124 (x : Key → ℝ) : Integer.Sparse.eval row13124 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form24) x := by
  rw [rowCheck13124, Integer.Sparse.eval_collectBalanced, rawRowCheck13124]

def rawRow13125 : Integer.Sparse Key := [(key524, -24), (key555, 6), (key555, 6), (key296, 6), (key524, 6)]

theorem rawRowCheck13125 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form24 = rawRow13125 := by decide +kernel

def row13125 : Integer.Sparse Key := [(key296, 6), (key524, -18), (key555, 12)]

theorem rowCheck13125 : row13125 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13125 := by decide +kernel

theorem rowEval13125 (x : Key → ℝ) : Integer.Sparse.eval row13125 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form24) x := by
  rw [rowCheck13125, Integer.Sparse.eval_collectBalanced, rawRowCheck13125]

def rawRow13126 : Integer.Sparse Key := [(key524, -24), (key555, 6), (key555, 6), (key524, 6), (key296, 6)]

theorem rawRowCheck13126 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form24 = rawRow13126 := by decide +kernel

def row13126 : Integer.Sparse Key := [(key296, 6), (key524, -18), (key555, 12)]

theorem rowCheck13126 : row13126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13126 := by decide +kernel

theorem rowEval13126 (x : Key → ℝ) : Integer.Sparse.eval row13126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form24) x := by
  rw [rowCheck13126, Integer.Sparse.eval_collectBalanced, rawRowCheck13126]

def rawRow13127 : Integer.Sparse Key := [(key555, -24), (key296, 6), (key524, 6), (key524, 6), (key555, 6)]

theorem rawRowCheck13127 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form24 = rawRow13127 := by decide +kernel

def row13127 : Integer.Sparse Key := [(key296, 6), (key524, 12), (key555, -18)]

theorem rowCheck13127 : row13127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13127 := by decide +kernel

theorem rowEval13127 (x : Key → ℝ) : Integer.Sparse.eval row13127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form24) x := by
  rw [rowCheck13127, Integer.Sparse.eval_collectBalanced, rawRowCheck13127]

def rawRow13128 : Integer.Sparse Key := [(key555, -24), (key296, 6), (key524, 6), (key555, 6), (key524, 6)]

theorem rawRowCheck13128 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form24 = rawRow13128 := by decide +kernel

def row13128 : Integer.Sparse Key := [(key296, 6), (key524, 12), (key555, -18)]

theorem rowCheck13128 : row13128 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13128 := by decide +kernel

theorem rowEval13128 (x : Key → ℝ) : Integer.Sparse.eval row13128 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form24) x := by
  rw [rowCheck13128, Integer.Sparse.eval_collectBalanced, rawRowCheck13128]

def rawRow13129 : Integer.Sparse Key := [(key555, -24), (key296, 6), (key555, 6), (key524, 6), (key524, 6)]

theorem rawRowCheck13129 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form24 = rawRow13129 := by decide +kernel

def row13129 : Integer.Sparse Key := [(key296, 6), (key524, 12), (key555, -18)]

theorem rowCheck13129 : row13129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13129 := by decide +kernel

theorem rowEval13129 (x : Key → ℝ) : Integer.Sparse.eval row13129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form24) x := by
  rw [rowCheck13129, Integer.Sparse.eval_collectBalanced, rawRowCheck13129]

def rawRow13130 : Integer.Sparse Key := [(key555, -24), (key524, 6), (key296, 6), (key524, 6), (key555, 6)]

theorem rawRowCheck13130 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form24 = rawRow13130 := by decide +kernel

def row13130 : Integer.Sparse Key := [(key296, 6), (key524, 12), (key555, -18)]

theorem rowCheck13130 : row13130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13130 := by decide +kernel

theorem rowEval13130 (x : Key → ℝ) : Integer.Sparse.eval row13130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form24) x := by
  rw [rowCheck13130, Integer.Sparse.eval_collectBalanced, rawRowCheck13130]

def rawRow13131 : Integer.Sparse Key := [(key555, -24), (key524, 6), (key296, 6), (key555, 6), (key524, 6)]

theorem rawRowCheck13131 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form24 = rawRow13131 := by decide +kernel

def row13131 : Integer.Sparse Key := [(key296, 6), (key524, 12), (key555, -18)]

theorem rowCheck13131 : row13131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13131 := by decide +kernel

theorem rowEval13131 (x : Key → ℝ) : Integer.Sparse.eval row13131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form24) x := by
  rw [rowCheck13131, Integer.Sparse.eval_collectBalanced, rawRowCheck13131]

def rawRow13132 : Integer.Sparse Key := [(key555, -24), (key524, 6), (key524, 6), (key296, 6), (key555, 6)]

theorem rawRowCheck13132 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form24 = rawRow13132 := by decide +kernel

def row13132 : Integer.Sparse Key := [(key296, 6), (key524, 12), (key555, -18)]

theorem rowCheck13132 : row13132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13132 := by decide +kernel

theorem rowEval13132 (x : Key → ℝ) : Integer.Sparse.eval row13132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form24) x := by
  rw [rowCheck13132, Integer.Sparse.eval_collectBalanced, rawRowCheck13132]

def rawRow13133 : Integer.Sparse Key := [(key555, -24), (key524, 6), (key524, 6), (key555, 6), (key296, 6)]

theorem rawRowCheck13133 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form24 = rawRow13133 := by decide +kernel

def row13133 : Integer.Sparse Key := [(key296, 6), (key524, 12), (key555, -18)]

theorem rowCheck13133 : row13133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13133 := by decide +kernel

theorem rowEval13133 (x : Key → ℝ) : Integer.Sparse.eval row13133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form24) x := by
  rw [rowCheck13133, Integer.Sparse.eval_collectBalanced, rawRowCheck13133]

def rawRow13134 : Integer.Sparse Key := [(key555, -24), (key524, 6), (key555, 6), (key296, 6), (key524, 6)]

theorem rawRowCheck13134 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form24 = rawRow13134 := by decide +kernel

def row13134 : Integer.Sparse Key := [(key296, 6), (key524, 12), (key555, -18)]

theorem rowCheck13134 : row13134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13134 := by decide +kernel

theorem rowEval13134 (x : Key → ℝ) : Integer.Sparse.eval row13134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form24) x := by
  rw [rowCheck13134, Integer.Sparse.eval_collectBalanced, rawRowCheck13134]

def rawRow13135 : Integer.Sparse Key := [(key555, -24), (key524, 6), (key555, 6), (key524, 6), (key296, 6)]

theorem rawRowCheck13135 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form24 = rawRow13135 := by decide +kernel

def row13135 : Integer.Sparse Key := [(key296, 6), (key524, 12), (key555, -18)]

theorem rowCheck13135 : row13135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13135 := by decide +kernel

theorem rowEval13135 (x : Key → ℝ) : Integer.Sparse.eval row13135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form24) x := by
  rw [rowCheck13135, Integer.Sparse.eval_collectBalanced, rawRowCheck13135]

def rawRow13136 : Integer.Sparse Key := [(key555, -24), (key555, 6), (key296, 6), (key524, 6), (key524, 6)]

theorem rawRowCheck13136 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form24 = rawRow13136 := by decide +kernel

def row13136 : Integer.Sparse Key := [(key296, 6), (key524, 12), (key555, -18)]

theorem rowCheck13136 : row13136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13136 := by decide +kernel

theorem rowEval13136 (x : Key → ℝ) : Integer.Sparse.eval row13136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form24) x := by
  rw [rowCheck13136, Integer.Sparse.eval_collectBalanced, rawRowCheck13136]

def rawRow13137 : Integer.Sparse Key := [(key555, -24), (key555, 6), (key524, 6), (key296, 6), (key524, 6)]

theorem rawRowCheck13137 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form24 = rawRow13137 := by decide +kernel

def row13137 : Integer.Sparse Key := [(key296, 6), (key524, 12), (key555, -18)]

theorem rowCheck13137 : row13137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13137 := by decide +kernel

theorem rowEval13137 (x : Key → ℝ) : Integer.Sparse.eval row13137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form24) x := by
  rw [rowCheck13137, Integer.Sparse.eval_collectBalanced, rawRowCheck13137]

def rawRow13138 : Integer.Sparse Key := [(key555, -24), (key555, 6), (key524, 6), (key524, 6), (key296, 6)]

theorem rawRowCheck13138 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form24 = rawRow13138 := by decide +kernel

def row13138 : Integer.Sparse Key := [(key296, 6), (key524, 12), (key555, -18)]

theorem rowCheck13138 : row13138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13138 := by decide +kernel

theorem rowEval13138 (x : Key → ℝ) : Integer.Sparse.eval row13138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form24) x := by
  rw [rowCheck13138, Integer.Sparse.eval_collectBalanced, rawRowCheck13138]

def rawRow13139 : Integer.Sparse Key := [(key1508, 6), (key1508, 6), (key1521, 6), (key1882, 6), (key1510, -6), (key1510, -6), (key1521, -6), (key1749, -6)]

theorem rawRowCheck13139 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form25 = rawRow13139 := by decide +kernel

def row13139 : Integer.Sparse Key := [(key1508, 12), (key1510, -12), (key1749, -6), (key1882, 6)]

theorem rowCheck13139 : row13139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13139 := by decide +kernel

theorem rowEval13139 (x : Key → ℝ) : Integer.Sparse.eval row13139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form25) x := by
  rw [rowCheck13139, Integer.Sparse.eval_collectBalanced, rawRowCheck13139]

def rawRow13140 : Integer.Sparse Key := [(key1508, 6), (key1521, 6), (key1508, 6), (key1882, 6), (key1510, -6), (key1521, -6), (key1510, -6), (key1749, -6)]

theorem rawRowCheck13140 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form25 = rawRow13140 := by decide +kernel

def row13140 : Integer.Sparse Key := [(key1508, 12), (key1510, -12), (key1749, -6), (key1882, 6)]

theorem rowCheck13140 : row13140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13140 := by decide +kernel

theorem rowEval13140 (x : Key → ℝ) : Integer.Sparse.eval row13140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form25) x := by
  rw [rowCheck13140, Integer.Sparse.eval_collectBalanced, rawRowCheck13140]

def rawRow13141 : Integer.Sparse Key := [(key1521, 6), (key1508, 6), (key1508, 6), (key1882, 6), (key1521, -6), (key1510, -6), (key1510, -6), (key1749, -6)]

theorem rawRowCheck13141 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form25 = rawRow13141 := by decide +kernel

def row13141 : Integer.Sparse Key := [(key1508, 12), (key1510, -12), (key1749, -6), (key1882, 6)]

theorem rowCheck13141 : row13141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13141 := by decide +kernel

theorem rowEval13141 (x : Key → ℝ) : Integer.Sparse.eval row13141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form25) x := by
  rw [rowCheck13141, Integer.Sparse.eval_collectBalanced, rawRowCheck13141]

def rawRow13142 : Integer.Sparse Key := [(key1508, 6), (key1508, 6), (key1882, 6), (key1521, 6), (key1510, -6), (key1510, -6), (key1749, -6), (key1521, -6)]

theorem rawRowCheck13142 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form25 = rawRow13142 := by decide +kernel

def row13142 : Integer.Sparse Key := [(key1508, 12), (key1510, -12), (key1749, -6), (key1882, 6)]

theorem rowCheck13142 : row13142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13142 := by decide +kernel

theorem rowEval13142 (x : Key → ℝ) : Integer.Sparse.eval row13142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form25) x := by
  rw [rowCheck13142, Integer.Sparse.eval_collectBalanced, rawRowCheck13142]

def rawRow13143 : Integer.Sparse Key := [(key1508, 6), (key1882, 6), (key1508, 6), (key1521, 6), (key1510, -6), (key1749, -6), (key1510, -6), (key1521, -6)]

theorem rawRowCheck13143 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form25 = rawRow13143 := by decide +kernel

def row13143 : Integer.Sparse Key := [(key1508, 12), (key1510, -12), (key1749, -6), (key1882, 6)]

theorem rowCheck13143 : row13143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13143 := by decide +kernel

theorem rowEval13143 (x : Key → ℝ) : Integer.Sparse.eval row13143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form25) x := by
  rw [rowCheck13143, Integer.Sparse.eval_collectBalanced, rawRowCheck13143]

def rawRow13144 : Integer.Sparse Key := [(key1882, 6), (key1508, 6), (key1508, 6), (key1521, 6), (key1749, -6), (key1510, -6), (key1510, -6), (key1521, -6)]

theorem rawRowCheck13144 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form25 = rawRow13144 := by decide +kernel

def row13144 : Integer.Sparse Key := [(key1508, 12), (key1510, -12), (key1749, -6), (key1882, 6)]

theorem rowCheck13144 : row13144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13144 := by decide +kernel

theorem rowEval13144 (x : Key → ℝ) : Integer.Sparse.eval row13144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form25) x := by
  rw [rowCheck13144, Integer.Sparse.eval_collectBalanced, rawRowCheck13144]

def rawRow13145 : Integer.Sparse Key := [(key1508, 6), (key1521, 6), (key1882, 6), (key1508, 6), (key1510, -6), (key1521, -6), (key1749, -6), (key1510, -6)]

theorem rawRowCheck13145 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form25 = rawRow13145 := by decide +kernel

def row13145 : Integer.Sparse Key := [(key1508, 12), (key1510, -12), (key1749, -6), (key1882, 6)]

theorem rowCheck13145 : row13145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13145 := by decide +kernel

theorem rowEval13145 (x : Key → ℝ) : Integer.Sparse.eval row13145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form25) x := by
  rw [rowCheck13145, Integer.Sparse.eval_collectBalanced, rawRowCheck13145]

def rawRow13146 : Integer.Sparse Key := [(key1521, 6), (key1508, 6), (key1882, 6), (key1508, 6), (key1521, -6), (key1510, -6), (key1749, -6), (key1510, -6)]

theorem rawRowCheck13146 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form25 = rawRow13146 := by decide +kernel

def row13146 : Integer.Sparse Key := [(key1508, 12), (key1510, -12), (key1749, -6), (key1882, 6)]

theorem rowCheck13146 : row13146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13146 := by decide +kernel

theorem rowEval13146 (x : Key → ℝ) : Integer.Sparse.eval row13146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form25) x := by
  rw [rowCheck13146, Integer.Sparse.eval_collectBalanced, rawRowCheck13146]

def rawRow13147 : Integer.Sparse Key := [(key1508, 6), (key1882, 6), (key1521, 6), (key1508, 6), (key1510, -6), (key1749, -6), (key1521, -6), (key1510, -6)]

theorem rawRowCheck13147 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form25 = rawRow13147 := by decide +kernel

def row13147 : Integer.Sparse Key := [(key1508, 12), (key1510, -12), (key1749, -6), (key1882, 6)]

theorem rowCheck13147 : row13147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13147 := by decide +kernel

theorem rowEval13147 (x : Key → ℝ) : Integer.Sparse.eval row13147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form25) x := by
  rw [rowCheck13147, Integer.Sparse.eval_collectBalanced, rawRowCheck13147]

def rawRow13148 : Integer.Sparse Key := [(key1882, 6), (key1508, 6), (key1521, 6), (key1508, 6), (key1749, -6), (key1510, -6), (key1521, -6), (key1510, -6)]

theorem rawRowCheck13148 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form25 = rawRow13148 := by decide +kernel

def row13148 : Integer.Sparse Key := [(key1508, 12), (key1510, -12), (key1749, -6), (key1882, 6)]

theorem rowCheck13148 : row13148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13148 := by decide +kernel

theorem rowEval13148 (x : Key → ℝ) : Integer.Sparse.eval row13148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form25) x := by
  rw [rowCheck13148, Integer.Sparse.eval_collectBalanced, rawRowCheck13148]

def rawRow13149 : Integer.Sparse Key := [(key1521, 6), (key1882, 6), (key1508, 6), (key1508, 6), (key1521, -6), (key1749, -6), (key1510, -6), (key1510, -6)]

theorem rawRowCheck13149 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form25 = rawRow13149 := by decide +kernel

def row13149 : Integer.Sparse Key := [(key1508, 12), (key1510, -12), (key1749, -6), (key1882, 6)]

theorem rowCheck13149 : row13149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13149 := by decide +kernel

theorem rowEval13149 (x : Key → ℝ) : Integer.Sparse.eval row13149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form25) x := by
  rw [rowCheck13149, Integer.Sparse.eval_collectBalanced, rawRowCheck13149]

def rawRow13150 : Integer.Sparse Key := [(key1882, 6), (key1521, 6), (key1508, 6), (key1508, 6), (key1749, -6), (key1521, -6), (key1510, -6), (key1510, -6)]

theorem rawRowCheck13150 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form25 = rawRow13150 := by decide +kernel

def row13150 : Integer.Sparse Key := [(key1508, 12), (key1510, -12), (key1749, -6), (key1882, 6)]

theorem rowCheck13150 : row13150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13150 := by decide +kernel

theorem rowEval13150 (x : Key → ℝ) : Integer.Sparse.eval row13150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form25) x := by
  rw [rowCheck13150, Integer.Sparse.eval_collectBalanced, rawRowCheck13150]

def rawRow13151 : Integer.Sparse Key := [(key1504, 6), (key1510, 6), (key1510, 6), (key1876, 6), (key1504, -6), (key1508, -6), (key1508, -6), (key1737, -6)]

theorem rawRowCheck13151 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form25 = rawRow13151 := by decide +kernel

def row13151 : Integer.Sparse Key := [(key1508, -12), (key1510, 12), (key1737, -6), (key1876, 6)]

theorem rowCheck13151 : row13151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13151 := by decide +kernel

theorem rowEval13151 (x : Key → ℝ) : Integer.Sparse.eval row13151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form25) x := by
  rw [rowCheck13151, Integer.Sparse.eval_collectBalanced, rawRowCheck13151]

def rawRow13152 : Integer.Sparse Key := [(key1510, 6), (key1504, 6), (key1510, 6), (key1876, 6), (key1508, -6), (key1504, -6), (key1508, -6), (key1737, -6)]

theorem rawRowCheck13152 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form25 = rawRow13152 := by decide +kernel

def row13152 : Integer.Sparse Key := [(key1508, -12), (key1510, 12), (key1737, -6), (key1876, 6)]

theorem rowCheck13152 : row13152 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13152 := by decide +kernel

theorem rowEval13152 (x : Key → ℝ) : Integer.Sparse.eval row13152 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form25) x := by
  rw [rowCheck13152, Integer.Sparse.eval_collectBalanced, rawRowCheck13152]

def rawRow13153 : Integer.Sparse Key := [(key1510, 6), (key1510, 6), (key1504, 6), (key1876, 6), (key1508, -6), (key1508, -6), (key1504, -6), (key1737, -6)]

theorem rawRowCheck13153 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form25 = rawRow13153 := by decide +kernel

def row13153 : Integer.Sparse Key := [(key1508, -12), (key1510, 12), (key1737, -6), (key1876, 6)]

theorem rowCheck13153 : row13153 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13153 := by decide +kernel

theorem rowEval13153 (x : Key → ℝ) : Integer.Sparse.eval row13153 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form25) x := by
  rw [rowCheck13153, Integer.Sparse.eval_collectBalanced, rawRowCheck13153]

def rawRow13154 : Integer.Sparse Key := [(key1504, 6), (key1510, 6), (key1876, 6), (key1510, 6), (key1504, -6), (key1508, -6), (key1737, -6), (key1508, -6)]

theorem rawRowCheck13154 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form25 = rawRow13154 := by decide +kernel

def row13154 : Integer.Sparse Key := [(key1508, -12), (key1510, 12), (key1737, -6), (key1876, 6)]

theorem rowCheck13154 : row13154 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13154 := by decide +kernel

theorem rowEval13154 (x : Key → ℝ) : Integer.Sparse.eval row13154 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form25) x := by
  rw [rowCheck13154, Integer.Sparse.eval_collectBalanced, rawRowCheck13154]

def rawRow13155 : Integer.Sparse Key := [(key1510, 6), (key1504, 6), (key1876, 6), (key1510, 6), (key1508, -6), (key1504, -6), (key1737, -6), (key1508, -6)]

theorem rawRowCheck13155 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form25 = rawRow13155 := by decide +kernel

def row13155 : Integer.Sparse Key := [(key1508, -12), (key1510, 12), (key1737, -6), (key1876, 6)]

theorem rowCheck13155 : row13155 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13155 := by decide +kernel

theorem rowEval13155 (x : Key → ℝ) : Integer.Sparse.eval row13155 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form25) x := by
  rw [rowCheck13155, Integer.Sparse.eval_collectBalanced, rawRowCheck13155]

def rawRow13156 : Integer.Sparse Key := [(key1504, 6), (key1876, 6), (key1510, 6), (key1510, 6), (key1504, -6), (key1737, -6), (key1508, -6), (key1508, -6)]

theorem rawRowCheck13156 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form25 = rawRow13156 := by decide +kernel

def row13156 : Integer.Sparse Key := [(key1508, -12), (key1510, 12), (key1737, -6), (key1876, 6)]

theorem rowCheck13156 : row13156 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13156 := by decide +kernel

theorem rowEval13156 (x : Key → ℝ) : Integer.Sparse.eval row13156 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form25) x := by
  rw [rowCheck13156, Integer.Sparse.eval_collectBalanced, rawRowCheck13156]

def rawRow13157 : Integer.Sparse Key := [(key1876, 6), (key1504, 6), (key1510, 6), (key1510, 6), (key1737, -6), (key1504, -6), (key1508, -6), (key1508, -6)]

theorem rawRowCheck13157 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form25 = rawRow13157 := by decide +kernel

def row13157 : Integer.Sparse Key := [(key1508, -12), (key1510, 12), (key1737, -6), (key1876, 6)]

theorem rowCheck13157 : row13157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13157 := by decide +kernel

theorem rowEval13157 (x : Key → ℝ) : Integer.Sparse.eval row13157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form25) x := by
  rw [rowCheck13157, Integer.Sparse.eval_collectBalanced, rawRowCheck13157]

def rawRow13158 : Integer.Sparse Key := [(key1510, 6), (key1876, 6), (key1504, 6), (key1510, 6), (key1508, -6), (key1737, -6), (key1504, -6), (key1508, -6)]

theorem rawRowCheck13158 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form25 = rawRow13158 := by decide +kernel

def row13158 : Integer.Sparse Key := [(key1508, -12), (key1510, 12), (key1737, -6), (key1876, 6)]

theorem rowCheck13158 : row13158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13158 := by decide +kernel

theorem rowEval13158 (x : Key → ℝ) : Integer.Sparse.eval row13158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form25) x := by
  rw [rowCheck13158, Integer.Sparse.eval_collectBalanced, rawRowCheck13158]

def rawRow13159 : Integer.Sparse Key := [(key1876, 6), (key1510, 6), (key1504, 6), (key1510, 6), (key1737, -6), (key1508, -6), (key1504, -6), (key1508, -6)]

theorem rawRowCheck13159 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form25 = rawRow13159 := by decide +kernel

def row13159 : Integer.Sparse Key := [(key1508, -12), (key1510, 12), (key1737, -6), (key1876, 6)]

theorem rowCheck13159 : row13159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13159 := by decide +kernel

theorem rowEval13159 (x : Key → ℝ) : Integer.Sparse.eval row13159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form25) x := by
  rw [rowCheck13159, Integer.Sparse.eval_collectBalanced, rawRowCheck13159]

def rawRow13160 : Integer.Sparse Key := [(key1510, 6), (key1510, 6), (key1876, 6), (key1504, 6), (key1508, -6), (key1508, -6), (key1737, -6), (key1504, -6)]

theorem rawRowCheck13160 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form25 = rawRow13160 := by decide +kernel

def row13160 : Integer.Sparse Key := [(key1508, -12), (key1510, 12), (key1737, -6), (key1876, 6)]

theorem rowCheck13160 : row13160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13160 := by decide +kernel

theorem rowEval13160 (x : Key → ℝ) : Integer.Sparse.eval row13160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form25) x := by
  rw [rowCheck13160, Integer.Sparse.eval_collectBalanced, rawRowCheck13160]

def rawRow13161 : Integer.Sparse Key := [(key1510, 6), (key1876, 6), (key1510, 6), (key1504, 6), (key1508, -6), (key1737, -6), (key1508, -6), (key1504, -6)]

theorem rawRowCheck13161 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form25 = rawRow13161 := by decide +kernel

def row13161 : Integer.Sparse Key := [(key1508, -12), (key1510, 12), (key1737, -6), (key1876, 6)]

theorem rowCheck13161 : row13161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13161 := by decide +kernel

theorem rowEval13161 (x : Key → ℝ) : Integer.Sparse.eval row13161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form25) x := by
  rw [rowCheck13161, Integer.Sparse.eval_collectBalanced, rawRowCheck13161]

def rawRow13162 : Integer.Sparse Key := [(key1876, 6), (key1510, 6), (key1510, 6), (key1504, 6), (key1737, -6), (key1508, -6), (key1508, -6), (key1504, -6)]

theorem rawRowCheck13162 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form25 = rawRow13162 := by decide +kernel

def row13162 : Integer.Sparse Key := [(key1508, -12), (key1510, 12), (key1737, -6), (key1876, 6)]

theorem rowCheck13162 : row13162 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13162 := by decide +kernel

theorem rowEval13162 (x : Key → ℝ) : Integer.Sparse.eval row13162 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form25) x := by
  rw [rowCheck13162, Integer.Sparse.eval_collectBalanced, rawRowCheck13162]

def rawRow13163 : Integer.Sparse Key := [(key291, 2), (key294, 2), (key294, 2), (key518, 2), (key553, 2), (key553, 2), (key631, 2), (key631, 2), (key647, 2), (key647, 2), (key650, 2), (key650, 2), (key294, -2), (key294, -2), (key298, -2), (key522, -2), (key522, -2), (key553, -2), (key553, -2), (key561, -2), (key561, -2), (key632, -2), (key650, -2), (key650, -2)]

theorem rawRowCheck13163 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form26 = rawRow13163 := by decide +kernel

def row13163 : Integer.Sparse Key := [(key291, 2), (key298, -2), (key518, 2), (key522, -4), (key561, -4), (key631, 4), (key632, -2), (key647, 4)]

theorem rowCheck13163 : row13163 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13163 := by decide +kernel

theorem rowEval13163 (x : Key → ℝ) : Integer.Sparse.eval row13163 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form26) x := by
  rw [rowCheck13163, Integer.Sparse.eval_collectBalanced, rawRowCheck13163]

def rawRow13164 : Integer.Sparse Key := [(key294, 2), (key291, 2), (key294, 2), (key553, 2), (key518, 2), (key553, 2), (key647, 2), (key650, 2), (key631, 2), (key650, 2), (key631, 2), (key647, 2), (key294, -2), (key298, -2), (key294, -2), (key553, -2), (key561, -2), (key522, -2), (key561, -2), (key522, -2), (key553, -2), (key650, -2), (key632, -2), (key650, -2)]

theorem rawRowCheck13164 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form26 = rawRow13164 := by decide +kernel

def row13164 : Integer.Sparse Key := [(key291, 2), (key298, -2), (key518, 2), (key522, -4), (key561, -4), (key631, 4), (key632, -2), (key647, 4)]

theorem rowCheck13164 : row13164 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13164 := by decide +kernel

theorem rowEval13164 (x : Key → ℝ) : Integer.Sparse.eval row13164 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form26) x := by
  rw [rowCheck13164, Integer.Sparse.eval_collectBalanced, rawRowCheck13164]

def rawRow13165 : Integer.Sparse Key := [(key294, 2), (key294, 2), (key291, 2), (key553, 2), (key553, 2), (key518, 2), (key650, 2), (key647, 2), (key650, 2), (key631, 2), (key647, 2), (key631, 2), (key298, -2), (key294, -2), (key294, -2), (key561, -2), (key553, -2), (key561, -2), (key522, -2), (key553, -2), (key522, -2), (key650, -2), (key650, -2), (key632, -2)]

theorem rawRowCheck13165 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form26 = rawRow13165 := by decide +kernel

def row13165 : Integer.Sparse Key := [(key291, 2), (key298, -2), (key518, 2), (key522, -4), (key561, -4), (key631, 4), (key632, -2), (key647, 4)]

theorem rowCheck13165 : row13165 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13165 := by decide +kernel

theorem rowEval13165 (x : Key → ℝ) : Integer.Sparse.eval row13165 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form26) x := by
  rw [rowCheck13165, Integer.Sparse.eval_collectBalanced, rawRowCheck13165]

def rawRow13166 : Integer.Sparse Key := [(key518, 2), (key553, 2), (key553, 2), (key291, 2), (key647, 2), (key647, 2), (key294, 2), (key294, 2), (key553, 2), (key553, 2), (key650, 2), (key650, 2), (key522, -2), (key522, -2), (key632, -2), (key294, -2), (key294, -2), (key553, -2), (key553, -2), (key650, -2), (key650, -2), (key298, -2), (key561, -2), (key561, -2)]

theorem rawRowCheck13166 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form26 = rawRow13166 := by decide +kernel

def row13166 : Integer.Sparse Key := [(key291, 2), (key298, -2), (key518, 2), (key522, -4), (key553, 4), (key561, -4), (key632, -2), (key647, 4)]

theorem rowCheck13166 : row13166 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13166 := by decide +kernel

theorem rowEval13166 (x : Key → ℝ) : Integer.Sparse.eval row13166 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form26) x := by
  rw [rowCheck13166, Integer.Sparse.eval_collectBalanced, rawRowCheck13166]

def rawRow13167 : Integer.Sparse Key := [(key553, 2), (key518, 2), (key553, 2), (key647, 2), (key291, 2), (key647, 2), (key553, 2), (key650, 2), (key294, 2), (key650, 2), (key294, 2), (key553, 2), (key522, -2), (key632, -2), (key522, -2), (key553, -2), (key650, -2), (key294, -2), (key650, -2), (key294, -2), (key553, -2), (key561, -2), (key298, -2), (key561, -2)]

theorem rawRowCheck13167 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form26 = rawRow13167 := by decide +kernel

def row13167 : Integer.Sparse Key := [(key291, 2), (key298, -2), (key518, 2), (key522, -4), (key553, 4), (key561, -4), (key632, -2), (key647, 4)]

theorem rowCheck13167 : row13167 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13167 := by decide +kernel

theorem rowEval13167 (x : Key → ℝ) : Integer.Sparse.eval row13167 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form26) x := by
  rw [rowCheck13167, Integer.Sparse.eval_collectBalanced, rawRowCheck13167]

def rawRow13168 : Integer.Sparse Key := [(key553, 2), (key553, 2), (key518, 2), (key647, 2), (key647, 2), (key291, 2), (key650, 2), (key553, 2), (key650, 2), (key294, 2), (key553, 2), (key294, 2), (key632, -2), (key522, -2), (key522, -2), (key650, -2), (key553, -2), (key650, -2), (key294, -2), (key553, -2), (key294, -2), (key561, -2), (key561, -2), (key298, -2)]

theorem rawRowCheck13168 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form26 = rawRow13168 := by decide +kernel

def row13168 : Integer.Sparse Key := [(key291, 2), (key298, -2), (key518, 2), (key522, -4), (key553, 4), (key561, -4), (key632, -2), (key647, 4)]

theorem rowCheck13168 : row13168 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13168 := by decide +kernel

theorem rowEval13168 (x : Key → ℝ) : Integer.Sparse.eval row13168 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form26) x := by
  rw [rowCheck13168, Integer.Sparse.eval_collectBalanced, rawRowCheck13168]

def rawRow13169 : Integer.Sparse Key := [(key631, 2), (key647, 2), (key650, 2), (key294, 2), (key553, 2), (key650, 2), (key291, 2), (key294, 2), (key518, 2), (key553, 2), (key631, 2), (key647, 2), (key553, -2), (key561, -2), (key650, -2), (key294, -2), (key298, -2), (key522, -2), (key561, -2), (key632, -2), (key650, -2), (key294, -2), (key522, -2), (key553, -2)]

theorem rawRowCheck13169 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form26 = rawRow13169 := by decide +kernel

def row13169 : Integer.Sparse Key := [(key291, 2), (key298, -2), (key518, 2), (key522, -4), (key561, -4), (key631, 4), (key632, -2), (key647, 4)]

theorem rowCheck13169 : row13169 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13169 := by decide +kernel

theorem rowEval13169 (x : Key → ℝ) : Integer.Sparse.eval row13169 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form26) x := by
  rw [rowCheck13169, Integer.Sparse.eval_collectBalanced, rawRowCheck13169]

def rawRow13170 : Integer.Sparse Key := [(key631, 2), (key650, 2), (key647, 2), (key294, 2), (key650, 2), (key553, 2), (key294, 2), (key291, 2), (key553, 2), (key518, 2), (key647, 2), (key631, 2), (key561, -2), (key553, -2), (key650, -2), (key298, -2), (key294, -2), (key561, -2), (key522, -2), (key650, -2), (key632, -2), (key294, -2), (key553, -2), (key522, -2)]

theorem rawRowCheck13170 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form26 = rawRow13170 := by decide +kernel

def row13170 : Integer.Sparse Key := [(key291, 2), (key298, -2), (key518, 2), (key522, -4), (key561, -4), (key631, 4), (key632, -2), (key647, 4)]

theorem rowCheck13170 : row13170 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13170 := by decide +kernel

theorem rowEval13170 (x : Key → ℝ) : Integer.Sparse.eval row13170 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form26) x := by
  rw [rowCheck13170, Integer.Sparse.eval_collectBalanced, rawRowCheck13170]

def rawRow13171 : Integer.Sparse Key := [(key647, 2), (key631, 2), (key650, 2), (key553, 2), (key294, 2), (key650, 2), (key518, 2), (key553, 2), (key291, 2), (key647, 2), (key294, 2), (key553, 2), (key553, -2), (key650, -2), (key561, -2), (key522, -2), (key632, -2), (key294, -2), (key650, -2), (key298, -2), (key561, -2), (key522, -2), (key294, -2), (key553, -2)]

theorem rawRowCheck13171 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form26 = rawRow13171 := by decide +kernel

def row13171 : Integer.Sparse Key := [(key291, 2), (key298, -2), (key518, 2), (key522, -4), (key553, 2), (key561, -4), (key631, 2), (key632, -2), (key647, 4)]

theorem rowCheck13171 : row13171 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13171 := by decide +kernel

theorem rowEval13171 (x : Key → ℝ) : Integer.Sparse.eval row13171 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form26) x := by
  rw [rowCheck13171, Integer.Sparse.eval_collectBalanced, rawRowCheck13171]

def rawRow13172 : Integer.Sparse Key := [(key647, 2), (key650, 2), (key631, 2), (key553, 2), (key650, 2), (key294, 2), (key553, 2), (key518, 2), (key647, 2), (key291, 2), (key553, 2), (key294, 2), (key650, -2), (key553, -2), (key561, -2), (key632, -2), (key522, -2), (key650, -2), (key294, -2), (key561, -2), (key298, -2), (key522, -2), (key553, -2), (key294, -2)]

theorem rawRowCheck13172 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form26 = rawRow13172 := by decide +kernel

def row13172 : Integer.Sparse Key := [(key291, 2), (key298, -2), (key518, 2), (key522, -4), (key553, 2), (key561, -4), (key631, 2), (key632, -2), (key647, 4)]

theorem rowCheck13172 : row13172 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13172 := by decide +kernel

theorem rowEval13172 (x : Key → ℝ) : Integer.Sparse.eval row13172 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form26) x := by
  rw [rowCheck13172, Integer.Sparse.eval_collectBalanced, rawRowCheck13172]

def rawRow13173 : Integer.Sparse Key := [(key650, 2), (key631, 2), (key647, 2), (key650, 2), (key294, 2), (key553, 2), (key631, 2), (key647, 2), (key294, 2), (key553, 2), (key291, 2), (key518, 2), (key561, -2), (key650, -2), (key553, -2), (key561, -2), (key650, -2), (key298, -2), (key632, -2), (key294, -2), (key522, -2), (key553, -2), (key294, -2), (key522, -2)]

theorem rawRowCheck13173 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form26 = rawRow13173 := by decide +kernel

def row13173 : Integer.Sparse Key := [(key291, 2), (key298, -2), (key518, 2), (key522, -4), (key561, -4), (key631, 4), (key632, -2), (key647, 4)]

theorem rowCheck13173 : row13173 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13173 := by decide +kernel

theorem rowEval13173 (x : Key → ℝ) : Integer.Sparse.eval row13173 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form26) x := by
  rw [rowCheck13173, Integer.Sparse.eval_collectBalanced, rawRowCheck13173]

def rawRow13174 : Integer.Sparse Key := [(key650, 2), (key647, 2), (key631, 2), (key650, 2), (key553, 2), (key294, 2), (key647, 2), (key631, 2), (key553, 2), (key294, 2), (key518, 2), (key291, 2), (key650, -2), (key561, -2), (key553, -2), (key650, -2), (key561, -2), (key632, -2), (key298, -2), (key522, -2), (key294, -2), (key553, -2), (key522, -2), (key294, -2)]

theorem rawRowCheck13174 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form26 = rawRow13174 := by decide +kernel

def row13174 : Integer.Sparse Key := [(key291, 2), (key298, -2), (key518, 2), (key522, -4), (key561, -4), (key631, 4), (key632, -2), (key647, 4)]

theorem rowCheck13174 : row13174 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13174 := by decide +kernel

theorem rowEval13174 (x : Key → ℝ) : Integer.Sparse.eval row13174 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form26) x := by
  rw [rowCheck13174, Integer.Sparse.eval_collectBalanced, rawRowCheck13174]

def rawRow13175 : Integer.Sparse Key := [(key294, 2), (key294, 2), (key298, 2), (key522, 2), (key522, 2), (key632, 2), (key553, 2), (key561, 2), (key553, 2), (key650, 2), (key561, 2), (key650, 2), (key291, -2), (key294, -2), (key294, -2), (key518, -2), (key522, -2), (key518, -2), (key553, -2), (key522, -2), (key553, -2), (key631, -2), (key631, -2), (key647, -2)]

theorem rawRowCheck13175 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form26 = rawRow13175 := by decide +kernel

def row13175 : Integer.Sparse Key := [(key291, -2), (key298, 2), (key518, -4), (key561, 4), (key631, -4), (key632, 2), (key647, -2), (key650, 4)]

theorem rowCheck13175 : row13175 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13175 := by decide +kernel

theorem rowEval13175 (x : Key → ℝ) : Integer.Sparse.eval row13175 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form26) x := by
  rw [rowCheck13175, Integer.Sparse.eval_collectBalanced, rawRowCheck13175]

def rawRow13176 : Integer.Sparse Key := [(key294, 2), (key298, 2), (key294, 2), (key522, 2), (key632, 2), (key522, 2), (key561, 2), (key553, 2), (key650, 2), (key553, 2), (key650, 2), (key561, 2), (key294, -2), (key291, -2), (key294, -2), (key522, -2), (key518, -2), (key553, -2), (key518, -2), (key553, -2), (key522, -2), (key631, -2), (key647, -2), (key631, -2)]

theorem rawRowCheck13176 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form26 = rawRow13176 := by decide +kernel

def row13176 : Integer.Sparse Key := [(key291, -2), (key298, 2), (key518, -4), (key561, 4), (key631, -4), (key632, 2), (key647, -2), (key650, 4)]

theorem rowCheck13176 : row13176 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13176 := by decide +kernel

theorem rowEval13176 (x : Key → ℝ) : Integer.Sparse.eval row13176 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form26) x := by
  rw [rowCheck13176, Integer.Sparse.eval_collectBalanced, rawRowCheck13176]

def rawRow13177 : Integer.Sparse Key := [(key298, 2), (key294, 2), (key294, 2), (key632, 2), (key522, 2), (key522, 2), (key650, 2), (key650, 2), (key561, 2), (key561, 2), (key553, 2), (key553, 2), (key294, -2), (key294, -2), (key291, -2), (key553, -2), (key553, -2), (key522, -2), (key522, -2), (key518, -2), (key518, -2), (key647, -2), (key631, -2), (key631, -2)]

theorem rawRowCheck13177 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form26 = rawRow13177 := by decide +kernel

def row13177 : Integer.Sparse Key := [(key291, -2), (key298, 2), (key518, -4), (key561, 4), (key631, -4), (key632, 2), (key647, -2), (key650, 4)]

theorem rowCheck13177 : row13177 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13177 := by decide +kernel

theorem rowEval13177 (x : Key → ℝ) : Integer.Sparse.eval row13177 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form26) x := by
  rw [rowCheck13177, Integer.Sparse.eval_collectBalanced, rawRowCheck13177]

def rawRow13178 : Integer.Sparse Key := [(key522, 2), (key553, 2), (key561, 2), (key294, 2), (key553, 2), (key650, 2), (key294, 2), (key298, 2), (key522, 2), (key632, 2), (key561, 2), (key650, 2), (key518, -2), (key522, -2), (key553, -2), (key291, -2), (key294, -2), (key518, -2), (key553, -2), (key631, -2), (key647, -2), (key294, -2), (key522, -2), (key553, -2)]

theorem rawRowCheck13178 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form26 = rawRow13178 := by decide +kernel

def row13178 : Integer.Sparse Key := [(key291, -2), (key298, 2), (key518, -4), (key553, -2), (key561, 4), (key631, -2), (key632, 2), (key647, -2), (key650, 4)]

theorem rowCheck13178 : row13178 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13178 := by decide +kernel

theorem rowEval13178 (x : Key → ℝ) : Integer.Sparse.eval row13178 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form26) x := by
  rw [rowCheck13178, Integer.Sparse.eval_collectBalanced, rawRowCheck13178]

def rawRow13179 : Integer.Sparse Key := [(key522, 2), (key561, 2), (key553, 2), (key294, 2), (key650, 2), (key553, 2), (key298, 2), (key294, 2), (key632, 2), (key522, 2), (key650, 2), (key561, 2), (key522, -2), (key518, -2), (key553, -2), (key294, -2), (key291, -2), (key553, -2), (key518, -2), (key647, -2), (key631, -2), (key294, -2), (key553, -2), (key522, -2)]

theorem rawRowCheck13179 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form26 = rawRow13179 := by decide +kernel

def row13179 : Integer.Sparse Key := [(key291, -2), (key298, 2), (key518, -4), (key553, -2), (key561, 4), (key631, -2), (key632, 2), (key647, -2), (key650, 4)]

theorem rowCheck13179 : row13179 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13179 := by decide +kernel

theorem rowEval13179 (x : Key → ℝ) : Integer.Sparse.eval row13179 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form26) x := by
  rw [rowCheck13179, Integer.Sparse.eval_collectBalanced, rawRowCheck13179]

def rawRow13180 : Integer.Sparse Key := [(key553, 2), (key522, 2), (key561, 2), (key553, 2), (key294, 2), (key650, 2), (key522, 2), (key561, 2), (key294, 2), (key650, 2), (key298, 2), (key632, 2), (key518, -2), (key553, -2), (key522, -2), (key518, -2), (key553, -2), (key291, -2), (key647, -2), (key294, -2), (key553, -2), (key522, -2), (key294, -2), (key553, -2)]

theorem rawRowCheck13180 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form26 = rawRow13180 := by decide +kernel

def row13180 : Integer.Sparse Key := [(key291, -2), (key298, 2), (key518, -4), (key553, -4), (key561, 4), (key632, 2), (key647, -2), (key650, 4)]

theorem rowCheck13180 : row13180 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13180 := by decide +kernel

theorem rowEval13180 (x : Key → ℝ) : Integer.Sparse.eval row13180 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form26) x := by
  rw [rowCheck13180, Integer.Sparse.eval_collectBalanced, rawRowCheck13180]

def rawRow13181 : Integer.Sparse Key := [(key553, 2), (key561, 2), (key522, 2), (key553, 2), (key650, 2), (key294, 2), (key561, 2), (key522, 2), (key650, 2), (key294, 2), (key632, 2), (key298, 2), (key553, -2), (key518, -2), (key522, -2), (key553, -2), (key518, -2), (key647, -2), (key291, -2), (key553, -2), (key294, -2), (key522, -2), (key553, -2), (key294, -2)]

theorem rawRowCheck13181 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form26 = rawRow13181 := by decide +kernel

def row13181 : Integer.Sparse Key := [(key291, -2), (key298, 2), (key518, -4), (key553, -4), (key561, 4), (key632, 2), (key647, -2), (key650, 4)]

theorem rowCheck13181 : row13181 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13181 := by decide +kernel

theorem rowEval13181 (x : Key → ℝ) : Integer.Sparse.eval row13181 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form26) x := by
  rw [rowCheck13181, Integer.Sparse.eval_collectBalanced, rawRowCheck13181]

def rawRow13182 : Integer.Sparse Key := [(key561, 2), (key522, 2), (key553, 2), (key650, 2), (key294, 2), (key553, 2), (key632, 2), (key650, 2), (key298, 2), (key561, 2), (key294, 2), (key522, 2), (key522, -2), (key553, -2), (key518, -2), (key631, -2), (key647, -2), (key294, -2), (key553, -2), (key291, -2), (key518, -2), (key553, -2), (key294, -2), (key522, -2)]

theorem rawRowCheck13182 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form26 = rawRow13182 := by decide +kernel

def row13182 : Integer.Sparse Key := [(key291, -2), (key298, 2), (key518, -4), (key553, -2), (key561, 4), (key631, -2), (key632, 2), (key647, -2), (key650, 4)]

theorem rowCheck13182 : row13182 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13182 := by decide +kernel

theorem rowEval13182 (x : Key → ℝ) : Integer.Sparse.eval row13182 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form26) x := by
  rw [rowCheck13182, Integer.Sparse.eval_collectBalanced, rawRowCheck13182]

def rawRow13183 : Integer.Sparse Key := [(key561, 2), (key553, 2), (key522, 2), (key650, 2), (key553, 2), (key294, 2), (key650, 2), (key632, 2), (key561, 2), (key298, 2), (key522, 2), (key294, 2), (key553, -2), (key522, -2), (key518, -2), (key647, -2), (key631, -2), (key553, -2), (key294, -2), (key518, -2), (key291, -2), (key553, -2), (key522, -2), (key294, -2)]

theorem rawRowCheck13183 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form26 = rawRow13183 := by decide +kernel

def row13183 : Integer.Sparse Key := [(key291, -2), (key298, 2), (key518, -4), (key553, -2), (key561, 4), (key631, -2), (key632, 2), (key647, -2), (key650, 4)]

theorem rowCheck13183 : row13183 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13183 := by decide +kernel

theorem rowEval13183 (x : Key → ℝ) : Integer.Sparse.eval row13183 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form26) x := by
  rw [rowCheck13183, Integer.Sparse.eval_collectBalanced, rawRowCheck13183]

end MUB6.Certificate.GramRows

end OAI
