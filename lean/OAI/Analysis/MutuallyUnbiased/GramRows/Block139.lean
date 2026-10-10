import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow14720 : Integer.Sparse Key := [(key622, 4), (key622, 4), (key230, 4), (key622, -2), (key502, -2), (key622, -2), (key230, -2), (key502, -2), (key230, -2), (key618, -2), (key496, -2), (key618, -2), (key224, -2), (key496, -2), (key224, -2), (key496, 4), (key496, 4), (key224, 4)]

theorem rawRowCheck14720 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form5 = rawRow14720 := by decide +kernel

def row14720 : Integer.Sparse Key := [(key496, 4), (key502, -4), (key618, -4), (key622, 4)]

theorem rowCheck14720 : row14720 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14720 := by decide +kernel

theorem rowEval14720 (x : Key → ℝ) : Integer.Sparse.eval row14720 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck14720, Integer.Sparse.eval_collectBalanced, rawRowCheck14720]

def rawRow14721 : Integer.Sparse Key := [(key1484, -1), (key1490, -1), (key1484, -1), (key1513, -1), (key1490, -1), (key1513, -1), (key1490, 2), (key1490, 2), (key1513, 2), (key1710, -1), (key1716, -1), (key1710, -1), (key1741, -1), (key1716, -1), (key1741, -1), (key1710, 2), (key1723, 2), (key1710, 2), (key1741, 2), (key1723, 2), (key1741, 2), (key1716, -1), (key1723, -1), (key1716, -1), (key1741, -1), (key1723, -1), (key1741, -1), (key1937, 2), (key1937, 2), (key1949, 2), (key1937, -1), (key1940, -1), (key1937, -1), (key1949, -1), (key1940, -1), (key1949, -1)]

theorem rawRowCheck14721 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form6 = rawRow14721 := by decide +kernel

def row14721 : Integer.Sparse Key := [(key1484, -2), (key1490, 2), (key1710, 2), (key1716, -4), (key1723, 2), (key1937, 2), (key1940, -2)]

theorem rowCheck14721 : row14721 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14721 := by decide +kernel

theorem rowEval14721 (x : Key → ℝ) : Integer.Sparse.eval row14721 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form6) x := by
  rw [rowCheck14721, Integer.Sparse.eval_collectBalanced, rawRowCheck14721]

def rawRow14722 : Integer.Sparse Key := [(key1490, -1), (key1484, -1), (key1513, -1), (key1484, -1), (key1513, -1), (key1490, -1), (key1490, 2), (key1513, 2), (key1490, 2), (key1716, -1), (key1710, -1), (key1741, -1), (key1710, -1), (key1741, -1), (key1716, -1), (key1723, 2), (key1710, 2), (key1741, 2), (key1710, 2), (key1741, 2), (key1723, 2), (key1723, -1), (key1716, -1), (key1741, -1), (key1716, -1), (key1741, -1), (key1723, -1), (key1937, 2), (key1949, 2), (key1937, 2), (key1940, -1), (key1937, -1), (key1949, -1), (key1937, -1), (key1949, -1), (key1940, -1)]

theorem rawRowCheck14722 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form6 = rawRow14722 := by decide +kernel

def row14722 : Integer.Sparse Key := [(key1484, -2), (key1490, 2), (key1710, 2), (key1716, -4), (key1723, 2), (key1937, 2), (key1940, -2)]

theorem rowCheck14722 : row14722 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14722 := by decide +kernel

theorem rowEval14722 (x : Key → ℝ) : Integer.Sparse.eval row14722 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14722, Integer.Sparse.eval_collectBalanced, rawRowCheck14722]

def rawRow14723 : Integer.Sparse Key := [(key1513, -1), (key1513, -1), (key1490, -1), (key1490, -1), (key1484, -1), (key1484, -1), (key1513, 2), (key1490, 2), (key1490, 2), (key1741, -1), (key1741, -1), (key1716, -1), (key1716, -1), (key1710, -1), (key1710, -1), (key1741, 2), (key1741, 2), (key1723, 2), (key1723, 2), (key1710, 2), (key1710, 2), (key1741, -1), (key1741, -1), (key1723, -1), (key1723, -1), (key1716, -1), (key1716, -1), (key1949, 2), (key1937, 2), (key1937, 2), (key1949, -1), (key1949, -1), (key1940, -1), (key1940, -1), (key1937, -1), (key1937, -1)]

theorem rawRowCheck14723 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form6 = rawRow14723 := by decide +kernel

def row14723 : Integer.Sparse Key := [(key1484, -2), (key1490, 2), (key1710, 2), (key1716, -4), (key1723, 2), (key1937, 2), (key1940, -2)]

theorem rowCheck14723 : row14723 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14723 := by decide +kernel

theorem rowEval14723 (x : Key → ℝ) : Integer.Sparse.eval row14723 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14723, Integer.Sparse.eval_collectBalanced, rawRowCheck14723]

def rawRow14724 : Integer.Sparse Key := [(key1490, -1), (key1490, -1), (key1490, -1), (key1490, -1), (key1490, -1), (key1490, -1), (key1484, 2), (key1484, 2), (key1484, 2), (key1723, -1), (key1723, -1), (key1723, -1), (key1723, -1), (key1723, -1), (key1723, -1), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1710, -1), (key1710, -1), (key1710, -1), (key1710, -1), (key1710, -1), (key1710, -1), (key1940, 2), (key1940, 2), (key1940, 2), (key1937, -1), (key1937, -1), (key1937, -1), (key1937, -1), (key1937, -1), (key1937, -1)]

theorem rawRowCheck14724 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form6 = rawRow14724 := by decide +kernel

def row14724 : Integer.Sparse Key := [(key1484, 6), (key1490, -6), (key1710, -6), (key1716, 12), (key1723, -6), (key1937, -6), (key1940, 6)]

theorem rowCheck14724 : row14724 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14724 := by decide +kernel

theorem rowEval14724 (x : Key → ℝ) : Integer.Sparse.eval row14724 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14724, Integer.Sparse.eval_collectBalanced, rawRowCheck14724]

def rawRow14725 : Integer.Sparse Key := [(key1710, -1), (key1716, -1), (key1710, -1), (key1741, -1), (key1716, -1), (key1741, -1), (key1937, 2), (key1937, 2), (key1949, 2), (key1484, -1), (key1490, -1), (key1484, -1), (key1513, -1), (key1490, -1), (key1513, -1), (key1710, 2), (key1723, 2), (key1710, 2), (key1741, 2), (key1723, 2), (key1741, 2), (key1937, -1), (key1940, -1), (key1937, -1), (key1949, -1), (key1940, -1), (key1949, -1), (key1490, 2), (key1490, 2), (key1513, 2), (key1716, -1), (key1723, -1), (key1716, -1), (key1741, -1), (key1723, -1), (key1741, -1)]

theorem rawRowCheck14725 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form6 = rawRow14725 := by decide +kernel

def row14725 : Integer.Sparse Key := [(key1484, -2), (key1490, 2), (key1710, 2), (key1716, -4), (key1723, 2), (key1937, 2), (key1940, -2)]

theorem rowCheck14725 : row14725 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14725 := by decide +kernel

theorem rowEval14725 (x : Key → ℝ) : Integer.Sparse.eval row14725 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form6) x := by
  rw [rowCheck14725, Integer.Sparse.eval_collectBalanced, rawRowCheck14725]

def rawRow14726 : Integer.Sparse Key := [(key1716, -1), (key1710, -1), (key1741, -1), (key1710, -1), (key1741, -1), (key1716, -1), (key1937, 2), (key1949, 2), (key1937, 2), (key1490, -1), (key1484, -1), (key1513, -1), (key1484, -1), (key1513, -1), (key1490, -1), (key1723, 2), (key1710, 2), (key1741, 2), (key1710, 2), (key1741, 2), (key1723, 2), (key1940, -1), (key1937, -1), (key1949, -1), (key1937, -1), (key1949, -1), (key1940, -1), (key1490, 2), (key1513, 2), (key1490, 2), (key1723, -1), (key1716, -1), (key1741, -1), (key1716, -1), (key1741, -1), (key1723, -1)]

theorem rawRowCheck14726 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form6 = rawRow14726 := by decide +kernel

def row14726 : Integer.Sparse Key := [(key1484, -2), (key1490, 2), (key1710, 2), (key1716, -4), (key1723, 2), (key1937, 2), (key1940, -2)]

theorem rowCheck14726 : row14726 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14726 := by decide +kernel

theorem rowEval14726 (x : Key → ℝ) : Integer.Sparse.eval row14726 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14726, Integer.Sparse.eval_collectBalanced, rawRowCheck14726]

def rawRow14727 : Integer.Sparse Key := [(key1741, -1), (key1741, -1), (key1716, -1), (key1716, -1), (key1710, -1), (key1710, -1), (key1949, 2), (key1937, 2), (key1937, 2), (key1513, -1), (key1513, -1), (key1490, -1), (key1490, -1), (key1484, -1), (key1484, -1), (key1741, 2), (key1741, 2), (key1723, 2), (key1723, 2), (key1710, 2), (key1710, 2), (key1949, -1), (key1949, -1), (key1940, -1), (key1940, -1), (key1937, -1), (key1937, -1), (key1513, 2), (key1490, 2), (key1490, 2), (key1741, -1), (key1741, -1), (key1723, -1), (key1723, -1), (key1716, -1), (key1716, -1)]

theorem rawRowCheck14727 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form6 = rawRow14727 := by decide +kernel

def row14727 : Integer.Sparse Key := [(key1484, -2), (key1490, 2), (key1710, 2), (key1716, -4), (key1723, 2), (key1937, 2), (key1940, -2)]

theorem rowCheck14727 : row14727 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14727 := by decide +kernel

theorem rowEval14727 (x : Key → ℝ) : Integer.Sparse.eval row14727 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14727, Integer.Sparse.eval_collectBalanced, rawRowCheck14727]

def rawRow14728 : Integer.Sparse Key := [(key1358, -1), (key1364, -1), (key1710, -1), (key1741, -1), (key1937, -1), (key1949, -1), (key1364, 2), (key1716, 2), (key1741, 2), (key1358, -1), (key1364, -1), (key1710, -1), (key1741, -1), (key1937, -1), (key1949, -1), (key1358, 2), (key1374, 2), (key1484, 2), (key1513, 2), (key1940, 2), (key1949, 2), (key1364, -1), (key1374, -1), (key1490, -1), (key1513, -1), (key1723, -1), (key1741, -1), (key1364, 2), (key1716, 2), (key1741, 2), (key1364, -1), (key1374, -1), (key1490, -1), (key1513, -1), (key1723, -1), (key1741, -1)]

theorem rawRowCheck14728 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form6 = rawRow14728 := by decide +kernel

def row14728 : Integer.Sparse Key := [(key1484, 2), (key1490, -2), (key1710, -2), (key1716, 4), (key1723, -2), (key1937, -2), (key1940, 2)]

theorem rowCheck14728 : row14728 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14728 := by decide +kernel

theorem rowEval14728 (x : Key → ℝ) : Integer.Sparse.eval row14728 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form6) x := by
  rw [rowCheck14728, Integer.Sparse.eval_collectBalanced, rawRowCheck14728]

def rawRow14729 : Integer.Sparse Key := [(key1364, -1), (key1358, -1), (key1741, -1), (key1710, -1), (key1949, -1), (key1937, -1), (key1364, 2), (key1741, 2), (key1716, 2), (key1364, -1), (key1358, -1), (key1741, -1), (key1710, -1), (key1949, -1), (key1937, -1), (key1374, 2), (key1358, 2), (key1513, 2), (key1484, 2), (key1949, 2), (key1940, 2), (key1374, -1), (key1364, -1), (key1513, -1), (key1490, -1), (key1741, -1), (key1723, -1), (key1364, 2), (key1741, 2), (key1716, 2), (key1374, -1), (key1364, -1), (key1513, -1), (key1490, -1), (key1741, -1), (key1723, -1)]

theorem rawRowCheck14729 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form6 = rawRow14729 := by decide +kernel

def row14729 : Integer.Sparse Key := [(key1484, 2), (key1490, -2), (key1710, -2), (key1716, 4), (key1723, -2), (key1937, -2), (key1940, 2)]

theorem rowCheck14729 : row14729 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14729 := by decide +kernel

theorem rowEval14729 (x : Key → ℝ) : Integer.Sparse.eval row14729 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14729, Integer.Sparse.eval_collectBalanced, rawRowCheck14729]

def rawRow14730 : Integer.Sparse Key := [(key1710, -1), (key1937, -1), (key1358, -1), (key1949, -1), (key1364, -1), (key1741, -1), (key1716, 2), (key1364, 2), (key1741, 2), (key1710, -1), (key1937, -1), (key1358, -1), (key1949, -1), (key1364, -1), (key1741, -1), (key1484, 2), (key1940, 2), (key1358, 2), (key1949, 2), (key1374, 2), (key1513, 2), (key1490, -1), (key1723, -1), (key1364, -1), (key1741, -1), (key1374, -1), (key1513, -1), (key1716, 2), (key1364, 2), (key1741, 2), (key1490, -1), (key1723, -1), (key1364, -1), (key1741, -1), (key1374, -1), (key1513, -1)]

theorem rawRowCheck14730 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form6 = rawRow14730 := by decide +kernel

def row14730 : Integer.Sparse Key := [(key1484, 2), (key1490, -2), (key1710, -2), (key1716, 4), (key1723, -2), (key1937, -2), (key1940, 2)]

theorem rowCheck14730 : row14730 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14730 := by decide +kernel

theorem rowEval14730 (x : Key → ℝ) : Integer.Sparse.eval row14730 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form6) x := by
  rw [rowCheck14730, Integer.Sparse.eval_collectBalanced, rawRowCheck14730]

def rawRow14731 : Integer.Sparse Key := [(key1937, -1), (key1710, -1), (key1949, -1), (key1358, -1), (key1741, -1), (key1364, -1), (key1716, 2), (key1741, 2), (key1364, 2), (key1937, -1), (key1710, -1), (key1949, -1), (key1358, -1), (key1741, -1), (key1364, -1), (key1940, 2), (key1484, 2), (key1949, 2), (key1358, 2), (key1513, 2), (key1374, 2), (key1723, -1), (key1490, -1), (key1741, -1), (key1364, -1), (key1513, -1), (key1374, -1), (key1716, 2), (key1741, 2), (key1364, 2), (key1723, -1), (key1490, -1), (key1741, -1), (key1364, -1), (key1513, -1), (key1374, -1)]

theorem rawRowCheck14731 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form6 = rawRow14731 := by decide +kernel

def row14731 : Integer.Sparse Key := [(key1484, 2), (key1490, -2), (key1710, -2), (key1716, 4), (key1723, -2), (key1937, -2), (key1940, 2)]

theorem rowCheck14731 : row14731 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14731 := by decide +kernel

theorem rowEval14731 (x : Key → ℝ) : Integer.Sparse.eval row14731 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck14731, Integer.Sparse.eval_collectBalanced, rawRowCheck14731]

def rawRow14732 : Integer.Sparse Key := [(key1741, -1), (key1949, -1), (key1364, -1), (key1937, -1), (key1358, -1), (key1710, -1), (key1741, 2), (key1364, 2), (key1716, 2), (key1741, -1), (key1949, -1), (key1364, -1), (key1937, -1), (key1358, -1), (key1710, -1), (key1513, 2), (key1949, 2), (key1374, 2), (key1940, 2), (key1358, 2), (key1484, 2), (key1513, -1), (key1741, -1), (key1374, -1), (key1723, -1), (key1364, -1), (key1490, -1), (key1741, 2), (key1364, 2), (key1716, 2), (key1513, -1), (key1741, -1), (key1374, -1), (key1723, -1), (key1364, -1), (key1490, -1)]

theorem rawRowCheck14732 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form6 = rawRow14732 := by decide +kernel

def row14732 : Integer.Sparse Key := [(key1484, 2), (key1490, -2), (key1710, -2), (key1716, 4), (key1723, -2), (key1937, -2), (key1940, 2)]

theorem rowCheck14732 : row14732 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14732 := by decide +kernel

theorem rowEval14732 (x : Key → ℝ) : Integer.Sparse.eval row14732 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14732, Integer.Sparse.eval_collectBalanced, rawRowCheck14732]

def rawRow14733 : Integer.Sparse Key := [(key1949, -1), (key1741, -1), (key1937, -1), (key1364, -1), (key1710, -1), (key1358, -1), (key1741, 2), (key1716, 2), (key1364, 2), (key1949, -1), (key1741, -1), (key1937, -1), (key1364, -1), (key1710, -1), (key1358, -1), (key1949, 2), (key1513, 2), (key1940, 2), (key1374, 2), (key1484, 2), (key1358, 2), (key1741, -1), (key1513, -1), (key1723, -1), (key1374, -1), (key1490, -1), (key1364, -1), (key1741, 2), (key1716, 2), (key1364, 2), (key1741, -1), (key1513, -1), (key1723, -1), (key1374, -1), (key1490, -1), (key1364, -1)]

theorem rawRowCheck14733 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form6 = rawRow14733 := by decide +kernel

def row14733 : Integer.Sparse Key := [(key1484, 2), (key1490, -2), (key1710, -2), (key1716, 4), (key1723, -2), (key1937, -2), (key1940, 2)]

theorem rowCheck14733 : row14733 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14733 := by decide +kernel

theorem rowEval14733 (x : Key → ℝ) : Integer.Sparse.eval row14733 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck14733, Integer.Sparse.eval_collectBalanced, rawRowCheck14733]

def rawRow14734 : Integer.Sparse Key := [(key1364, -1), (key1364, -1), (key1716, -1), (key1716, -1), (key1937, -1), (key1937, -1), (key1358, 2), (key1710, 2), (key1710, 2), (key1374, -1), (key1374, -1), (key1723, -1), (key1723, -1), (key1940, -1), (key1940, -1), (key1364, 2), (key1364, 2), (key1490, 2), (key1490, 2), (key1937, 2), (key1937, 2), (key1358, -1), (key1358, -1), (key1484, -1), (key1484, -1), (key1710, -1), (key1710, -1), (key1374, 2), (key1723, 2), (key1723, 2), (key1364, -1), (key1364, -1), (key1490, -1), (key1490, -1), (key1716, -1), (key1716, -1)]

theorem rawRowCheck14734 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form6 = rawRow14734 := by decide +kernel

def row14734 : Integer.Sparse Key := [(key1484, -2), (key1490, 2), (key1710, 2), (key1716, -4), (key1723, 2), (key1937, 2), (key1940, -2)]

theorem rowCheck14734 : row14734 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14734 := by decide +kernel

theorem rowEval14734 (x : Key → ℝ) : Integer.Sparse.eval row14734 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14734, Integer.Sparse.eval_collectBalanced, rawRowCheck14734]

def rawRow14735 : Integer.Sparse Key := [(key1716, -1), (key1937, -1), (key1364, -1), (key1937, -1), (key1364, -1), (key1716, -1), (key1710, 2), (key1358, 2), (key1710, 2), (key1723, -1), (key1940, -1), (key1374, -1), (key1940, -1), (key1374, -1), (key1723, -1), (key1490, 2), (key1937, 2), (key1364, 2), (key1937, 2), (key1364, 2), (key1490, 2), (key1484, -1), (key1710, -1), (key1358, -1), (key1710, -1), (key1358, -1), (key1484, -1), (key1723, 2), (key1374, 2), (key1723, 2), (key1490, -1), (key1716, -1), (key1364, -1), (key1716, -1), (key1364, -1), (key1490, -1)]

theorem rawRowCheck14735 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form6 = rawRow14735 := by decide +kernel

def row14735 : Integer.Sparse Key := [(key1484, -2), (key1490, 2), (key1710, 2), (key1716, -4), (key1723, 2), (key1937, 2), (key1940, -2)]

theorem rowCheck14735 : row14735 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14735 := by decide +kernel

theorem rowEval14735 (x : Key → ℝ) : Integer.Sparse.eval row14735 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14735, Integer.Sparse.eval_collectBalanced, rawRowCheck14735]

def rawRow14736 : Integer.Sparse Key := [(key1937, -1), (key1716, -1), (key1937, -1), (key1364, -1), (key1716, -1), (key1364, -1), (key1710, 2), (key1710, 2), (key1358, 2), (key1940, -1), (key1723, -1), (key1940, -1), (key1374, -1), (key1723, -1), (key1374, -1), (key1937, 2), (key1490, 2), (key1937, 2), (key1364, 2), (key1490, 2), (key1364, 2), (key1710, -1), (key1484, -1), (key1710, -1), (key1358, -1), (key1484, -1), (key1358, -1), (key1723, 2), (key1723, 2), (key1374, 2), (key1716, -1), (key1490, -1), (key1716, -1), (key1364, -1), (key1490, -1), (key1364, -1)]

theorem rawRowCheck14736 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form6 = rawRow14736 := by decide +kernel

def row14736 : Integer.Sparse Key := [(key1484, -2), (key1490, 2), (key1710, 2), (key1716, -4), (key1723, 2), (key1937, 2), (key1940, -2)]

theorem rowCheck14736 : row14736 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14736 := by decide +kernel

theorem rowEval14736 (x : Key → ℝ) : Integer.Sparse.eval row14736 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck14736, Integer.Sparse.eval_collectBalanced, rawRowCheck14736]

def rawRow14737 : Integer.Sparse Key := [(key1723, -1), (key1723, -1), (key1723, -1), (key1723, -1), (key1723, -1), (key1723, -1), (key1940, 2), (key1940, 2), (key1940, 2), (key1490, -1), (key1490, -1), (key1490, -1), (key1490, -1), (key1490, -1), (key1490, -1), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1937, -1), (key1937, -1), (key1937, -1), (key1937, -1), (key1937, -1), (key1937, -1), (key1484, 2), (key1484, 2), (key1484, 2), (key1710, -1), (key1710, -1), (key1710, -1), (key1710, -1), (key1710, -1), (key1710, -1)]

theorem rawRowCheck14737 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form6 = rawRow14737 := by decide +kernel

def row14737 : Integer.Sparse Key := [(key1484, 6), (key1490, -6), (key1710, -6), (key1716, 12), (key1723, -6), (key1937, -6), (key1940, 6)]

theorem rowCheck14737 : row14737 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14737 := by decide +kernel

theorem rowEval14737 (x : Key → ℝ) : Integer.Sparse.eval row14737 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14737, Integer.Sparse.eval_collectBalanced, rawRowCheck14737]

def rawRow14738 : Integer.Sparse Key := [(key1374, -1), (key1374, -1), (key1723, -1), (key1723, -1), (key1940, -1), (key1940, -1), (key1374, 2), (key1723, 2), (key1723, 2), (key1364, -1), (key1364, -1), (key1716, -1), (key1716, -1), (key1937, -1), (key1937, -1), (key1364, 2), (key1364, 2), (key1490, 2), (key1490, 2), (key1937, 2), (key1937, 2), (key1364, -1), (key1364, -1), (key1490, -1), (key1490, -1), (key1716, -1), (key1716, -1), (key1358, 2), (key1710, 2), (key1710, 2), (key1358, -1), (key1358, -1), (key1484, -1), (key1484, -1), (key1710, -1), (key1710, -1)]

theorem rawRowCheck14738 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form6 = rawRow14738 := by decide +kernel

def row14738 : Integer.Sparse Key := [(key1484, -2), (key1490, 2), (key1710, 2), (key1716, -4), (key1723, 2), (key1937, 2), (key1940, -2)]

theorem rowCheck14738 : row14738 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14738 := by decide +kernel

theorem rowEval14738 (x : Key → ℝ) : Integer.Sparse.eval row14738 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14738, Integer.Sparse.eval_collectBalanced, rawRowCheck14738]

def rawRow14739 : Integer.Sparse Key := [(key1723, -1), (key1940, -1), (key1374, -1), (key1940, -1), (key1374, -1), (key1723, -1), (key1723, 2), (key1374, 2), (key1723, 2), (key1716, -1), (key1937, -1), (key1364, -1), (key1937, -1), (key1364, -1), (key1716, -1), (key1490, 2), (key1937, 2), (key1364, 2), (key1937, 2), (key1364, 2), (key1490, 2), (key1490, -1), (key1716, -1), (key1364, -1), (key1716, -1), (key1364, -1), (key1490, -1), (key1710, 2), (key1358, 2), (key1710, 2), (key1484, -1), (key1710, -1), (key1358, -1), (key1710, -1), (key1358, -1), (key1484, -1)]

theorem rawRowCheck14739 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form6 = rawRow14739 := by decide +kernel

def row14739 : Integer.Sparse Key := [(key1484, -2), (key1490, 2), (key1710, 2), (key1716, -4), (key1723, 2), (key1937, 2), (key1940, -2)]

theorem rowCheck14739 : row14739 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14739 := by decide +kernel

theorem rowEval14739 (x : Key → ℝ) : Integer.Sparse.eval row14739 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14739, Integer.Sparse.eval_collectBalanced, rawRowCheck14739]

def rawRow14740 : Integer.Sparse Key := [(key1940, -1), (key1723, -1), (key1940, -1), (key1374, -1), (key1723, -1), (key1374, -1), (key1723, 2), (key1723, 2), (key1374, 2), (key1937, -1), (key1716, -1), (key1937, -1), (key1364, -1), (key1716, -1), (key1364, -1), (key1937, 2), (key1490, 2), (key1937, 2), (key1364, 2), (key1490, 2), (key1364, 2), (key1716, -1), (key1490, -1), (key1716, -1), (key1364, -1), (key1490, -1), (key1364, -1), (key1710, 2), (key1710, 2), (key1358, 2), (key1710, -1), (key1484, -1), (key1710, -1), (key1358, -1), (key1484, -1), (key1358, -1)]

theorem rawRowCheck14740 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form6 = rawRow14740 := by decide +kernel

def row14740 : Integer.Sparse Key := [(key1484, -2), (key1490, 2), (key1710, 2), (key1716, -4), (key1723, 2), (key1937, 2), (key1940, -2)]

theorem rowCheck14740 : row14740 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14740 := by decide +kernel

theorem rowEval14740 (x : Key → ℝ) : Integer.Sparse.eval row14740 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck14740, Integer.Sparse.eval_collectBalanced, rawRowCheck14740]

def rawRow14741 : Integer.Sparse Key := [(key1501, 4), (key1501, 4), (key1506, 4), (key1501, -4), (key1506, -4), (key1506, -4), (key1733, -4), (key1735, -4), (key1735, -4), (key1735, 12)]

theorem rawRowCheck14741 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form7 = rawRow14741 := by decide +kernel

def row14741 : Integer.Sparse Key := [(key1501, 4), (key1506, -4), (key1733, -4), (key1735, 4)]

theorem rowCheck14741 : row14741 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14741 := by decide +kernel

theorem rowEval14741 (x : Key → ℝ) : Integer.Sparse.eval row14741 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck14741, Integer.Sparse.eval_collectBalanced, rawRowCheck14741]

def rawRow14742 : Integer.Sparse Key := [(key1501, 4), (key1506, 4), (key1501, 4), (key1506, -4), (key1501, -4), (key1506, -4), (key1735, -4), (key1733, -4), (key1735, -4), (key1735, 12)]

theorem rawRowCheck14742 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form7 = rawRow14742 := by decide +kernel

def row14742 : Integer.Sparse Key := [(key1501, 4), (key1506, -4), (key1733, -4), (key1735, 4)]

theorem rowCheck14742 : row14742 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14742 := by decide +kernel

theorem rowEval14742 (x : Key → ℝ) : Integer.Sparse.eval row14742 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14742, Integer.Sparse.eval_collectBalanced, rawRowCheck14742]

def rawRow14743 : Integer.Sparse Key := [(key1506, 4), (key1501, 4), (key1501, 4), (key1506, -4), (key1506, -4), (key1501, -4), (key1735, -4), (key1735, -4), (key1733, -4), (key1735, 12)]

theorem rawRowCheck14743 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form7 = rawRow14743 := by decide +kernel

def row14743 : Integer.Sparse Key := [(key1501, 4), (key1506, -4), (key1733, -4), (key1735, 4)]

theorem rowCheck14743 : row14743 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14743 := by decide +kernel

theorem rowEval14743 (x : Key → ℝ) : Integer.Sparse.eval row14743 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14743, Integer.Sparse.eval_collectBalanced, rawRowCheck14743]

def rawRow14744 : Integer.Sparse Key := [(key1506, 4), (key1506, 4), (key1506, 4), (key1501, -4), (key1501, -4), (key1501, -4), (key1735, -4), (key1735, -4), (key1735, -4), (key1733, 12)]

theorem rawRowCheck14744 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form7 = rawRow14744 := by decide +kernel

def row14744 : Integer.Sparse Key := [(key1501, -12), (key1506, 12), (key1733, 12), (key1735, -12)]

theorem rowCheck14744 : row14744 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14744 := by decide +kernel

theorem rowEval14744 (x : Key → ℝ) : Integer.Sparse.eval row14744 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14744, Integer.Sparse.eval_collectBalanced, rawRowCheck14744]

def rawRow14745 : Integer.Sparse Key := [(key1501, 4), (key1501, 4), (key1506, 4), (key1733, -4), (key1735, -4), (key1735, -4), (key1501, -4), (key1506, -4), (key1506, -4), (key1735, 12)]

theorem rawRowCheck14745 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form7 = rawRow14745 := by decide +kernel

def row14745 : Integer.Sparse Key := [(key1501, 4), (key1506, -4), (key1733, -4), (key1735, 4)]

theorem rowCheck14745 : row14745 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14745 := by decide +kernel

theorem rowEval14745 (x : Key → ℝ) : Integer.Sparse.eval row14745 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck14745, Integer.Sparse.eval_collectBalanced, rawRowCheck14745]

def rawRow14746 : Integer.Sparse Key := [(key1501, 4), (key1506, 4), (key1501, 4), (key1735, -4), (key1733, -4), (key1735, -4), (key1506, -4), (key1501, -4), (key1506, -4), (key1735, 12)]

theorem rawRowCheck14746 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form7 = rawRow14746 := by decide +kernel

def row14746 : Integer.Sparse Key := [(key1501, 4), (key1506, -4), (key1733, -4), (key1735, 4)]

theorem rowCheck14746 : row14746 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14746 := by decide +kernel

theorem rowEval14746 (x : Key → ℝ) : Integer.Sparse.eval row14746 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14746, Integer.Sparse.eval_collectBalanced, rawRowCheck14746]

def rawRow14747 : Integer.Sparse Key := [(key1506, 4), (key1501, 4), (key1501, 4), (key1735, -4), (key1735, -4), (key1733, -4), (key1506, -4), (key1506, -4), (key1501, -4), (key1735, 12)]

theorem rawRowCheck14747 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form7 = rawRow14747 := by decide +kernel

def row14747 : Integer.Sparse Key := [(key1501, 4), (key1506, -4), (key1733, -4), (key1735, 4)]

theorem rowCheck14747 : row14747 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14747 := by decide +kernel

theorem rowEval14747 (x : Key → ℝ) : Integer.Sparse.eval row14747 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14747, Integer.Sparse.eval_collectBalanced, rawRowCheck14747]

def rawRow14748 : Integer.Sparse Key := [(key1501, 4), (key1733, 4), (key1735, 4), (key1501, -4), (key1506, -4), (key1735, -4), (key1501, -4), (key1506, -4), (key1735, -4), (key1506, 12)]

theorem rawRowCheck14748 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form7 = rawRow14748 := by decide +kernel

def row14748 : Integer.Sparse Key := [(key1501, -4), (key1506, 4), (key1733, 4), (key1735, -4)]

theorem rowCheck14748 : row14748 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14748 := by decide +kernel

theorem rowEval14748 (x : Key → ℝ) : Integer.Sparse.eval row14748 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck14748, Integer.Sparse.eval_collectBalanced, rawRowCheck14748]

def rawRow14749 : Integer.Sparse Key := [(key1501, 4), (key1735, 4), (key1733, 4), (key1506, -4), (key1501, -4), (key1735, -4), (key1506, -4), (key1501, -4), (key1735, -4), (key1506, 12)]

theorem rawRowCheck14749 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form7 = rawRow14749 := by decide +kernel

def row14749 : Integer.Sparse Key := [(key1501, -4), (key1506, 4), (key1733, 4), (key1735, -4)]

theorem rowCheck14749 : row14749 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14749 := by decide +kernel

theorem rowEval14749 (x : Key → ℝ) : Integer.Sparse.eval row14749 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14749, Integer.Sparse.eval_collectBalanced, rawRowCheck14749]

def rawRow14750 : Integer.Sparse Key := [(key1733, 4), (key1501, 4), (key1735, 4), (key1501, -4), (key1735, -4), (key1506, -4), (key1501, -4), (key1735, -4), (key1506, -4), (key1506, 12)]

theorem rawRowCheck14750 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form7 = rawRow14750 := by decide +kernel

def row14750 : Integer.Sparse Key := [(key1501, -4), (key1506, 4), (key1733, 4), (key1735, -4)]

theorem rowCheck14750 : row14750 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14750 := by decide +kernel

theorem rowEval14750 (x : Key → ℝ) : Integer.Sparse.eval row14750 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck14750, Integer.Sparse.eval_collectBalanced, rawRowCheck14750]

def rawRow14751 : Integer.Sparse Key := [(key1733, 4), (key1735, 4), (key1501, 4), (key1735, -4), (key1501, -4), (key1506, -4), (key1735, -4), (key1501, -4), (key1506, -4), (key1506, 12)]

theorem rawRowCheck14751 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form7 = rawRow14751 := by decide +kernel

def row14751 : Integer.Sparse Key := [(key1501, -4), (key1506, 4), (key1733, 4), (key1735, -4)]

theorem rowCheck14751 : row14751 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14751 := by decide +kernel

theorem rowEval14751 (x : Key → ℝ) : Integer.Sparse.eval row14751 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck14751, Integer.Sparse.eval_collectBalanced, rawRowCheck14751]

def rawRow14752 : Integer.Sparse Key := [(key1735, 4), (key1501, 4), (key1733, 4), (key1506, -4), (key1735, -4), (key1501, -4), (key1506, -4), (key1735, -4), (key1501, -4), (key1506, 12)]

theorem rawRowCheck14752 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form7 = rawRow14752 := by decide +kernel

def row14752 : Integer.Sparse Key := [(key1501, -4), (key1506, 4), (key1733, 4), (key1735, -4)]

theorem rowCheck14752 : row14752 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14752 := by decide +kernel

theorem rowEval14752 (x : Key → ℝ) : Integer.Sparse.eval row14752 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14752, Integer.Sparse.eval_collectBalanced, rawRowCheck14752]

def rawRow14753 : Integer.Sparse Key := [(key1735, 4), (key1733, 4), (key1501, 4), (key1735, -4), (key1506, -4), (key1501, -4), (key1735, -4), (key1506, -4), (key1501, -4), (key1506, 12)]

theorem rawRowCheck14753 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form7 = rawRow14753 := by decide +kernel

def row14753 : Integer.Sparse Key := [(key1501, -4), (key1506, 4), (key1733, 4), (key1735, -4)]

theorem rowCheck14753 : row14753 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14753 := by decide +kernel

theorem rowEval14753 (x : Key → ℝ) : Integer.Sparse.eval row14753 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck14753, Integer.Sparse.eval_collectBalanced, rawRowCheck14753]

def rawRow14754 : Integer.Sparse Key := [(key1506, 4), (key1735, 4), (key1735, 4), (key1501, -4), (key1501, -4), (key1733, -4), (key1506, -4), (key1506, -4), (key1735, -4), (key1501, 12)]

theorem rawRowCheck14754 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form7 = rawRow14754 := by decide +kernel

def row14754 : Integer.Sparse Key := [(key1501, 4), (key1506, -4), (key1733, -4), (key1735, 4)]

theorem rowCheck14754 : row14754 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14754 := by decide +kernel

theorem rowEval14754 (x : Key → ℝ) : Integer.Sparse.eval row14754 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14754, Integer.Sparse.eval_collectBalanced, rawRowCheck14754]

def rawRow14755 : Integer.Sparse Key := [(key1735, 4), (key1506, 4), (key1735, 4), (key1501, -4), (key1733, -4), (key1501, -4), (key1506, -4), (key1735, -4), (key1506, -4), (key1501, 12)]

theorem rawRowCheck14755 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form7 = rawRow14755 := by decide +kernel

def row14755 : Integer.Sparse Key := [(key1501, 4), (key1506, -4), (key1733, -4), (key1735, 4)]

theorem rowCheck14755 : row14755 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14755 := by decide +kernel

theorem rowEval14755 (x : Key → ℝ) : Integer.Sparse.eval row14755 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14755, Integer.Sparse.eval_collectBalanced, rawRowCheck14755]

def rawRow14756 : Integer.Sparse Key := [(key1735, 4), (key1735, 4), (key1506, 4), (key1733, -4), (key1501, -4), (key1501, -4), (key1735, -4), (key1506, -4), (key1506, -4), (key1501, 12)]

theorem rawRowCheck14756 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form7 = rawRow14756 := by decide +kernel

def row14756 : Integer.Sparse Key := [(key1501, 4), (key1506, -4), (key1733, -4), (key1735, 4)]

theorem rowCheck14756 : row14756 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14756 := by decide +kernel

theorem rowEval14756 (x : Key → ℝ) : Integer.Sparse.eval row14756 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck14756, Integer.Sparse.eval_collectBalanced, rawRowCheck14756]

def rawRow14757 : Integer.Sparse Key := [(key1506, 4), (key1506, 4), (key1506, 4), (key1735, -4), (key1735, -4), (key1735, -4), (key1501, -4), (key1501, -4), (key1501, -4), (key1733, 12)]

theorem rawRowCheck14757 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form7 = rawRow14757 := by decide +kernel

def row14757 : Integer.Sparse Key := [(key1501, -12), (key1506, 12), (key1733, 12), (key1735, -12)]

theorem rowCheck14757 : row14757 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14757 := by decide +kernel

theorem rowEval14757 (x : Key → ℝ) : Integer.Sparse.eval row14757 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14757, Integer.Sparse.eval_collectBalanced, rawRowCheck14757]

def rawRow14758 : Integer.Sparse Key := [(key1506, 4), (key1735, 4), (key1735, 4), (key1506, -4), (key1506, -4), (key1735, -4), (key1501, -4), (key1501, -4), (key1733, -4), (key1501, 12)]

theorem rawRowCheck14758 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form7 = rawRow14758 := by decide +kernel

def row14758 : Integer.Sparse Key := [(key1501, 4), (key1506, -4), (key1733, -4), (key1735, 4)]

theorem rowCheck14758 : row14758 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14758 := by decide +kernel

theorem rowEval14758 (x : Key → ℝ) : Integer.Sparse.eval row14758 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14758, Integer.Sparse.eval_collectBalanced, rawRowCheck14758]

def rawRow14759 : Integer.Sparse Key := [(key1735, 4), (key1506, 4), (key1735, 4), (key1506, -4), (key1735, -4), (key1506, -4), (key1501, -4), (key1733, -4), (key1501, -4), (key1501, 12)]

theorem rawRowCheck14759 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form7 = rawRow14759 := by decide +kernel

def row14759 : Integer.Sparse Key := [(key1501, 4), (key1506, -4), (key1733, -4), (key1735, 4)]

theorem rowCheck14759 : row14759 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14759 := by decide +kernel

theorem rowEval14759 (x : Key → ℝ) : Integer.Sparse.eval row14759 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14759, Integer.Sparse.eval_collectBalanced, rawRowCheck14759]

def rawRow14760 : Integer.Sparse Key := [(key1735, 4), (key1735, 4), (key1506, 4), (key1735, -4), (key1506, -4), (key1506, -4), (key1733, -4), (key1501, -4), (key1501, -4), (key1501, 12)]

theorem rawRowCheck14760 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form7 = rawRow14760 := by decide +kernel

def row14760 : Integer.Sparse Key := [(key1501, 4), (key1506, -4), (key1733, -4), (key1735, 4)]

theorem rowCheck14760 : row14760 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14760 := by decide +kernel

theorem rowEval14760 (x : Key → ℝ) : Integer.Sparse.eval row14760 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck14760, Integer.Sparse.eval_collectBalanced, rawRowCheck14760]

def rawRow14761 : Integer.Sparse Key := [(key1274, -2), (key1278, -2), (key1278, -2), (key1278, 6), (key1697, -2), (key1701, -2), (key1701, -2), (key1697, 2), (key1701, 2), (key1697, 2), (key1751, 2), (key1701, 2), (key1751, 2), (key1701, -2), (key1701, -2), (key1751, -2), (key1852, 6), (key1852, -2), (key1852, -2), (key1884, -2)]

theorem rawRowCheck14761 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form8 = rawRow14761 := by decide +kernel

def row14761 : Integer.Sparse Key := [(key1274, -2), (key1278, 2), (key1697, 2), (key1701, -4), (key1751, 2), (key1852, 2), (key1884, -2)]

theorem rowCheck14761 : row14761 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14761 := by decide +kernel

theorem rowEval14761 (x : Key → ℝ) : Integer.Sparse.eval row14761 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck14761, Integer.Sparse.eval_collectBalanced, rawRowCheck14761]

def rawRow14762 : Integer.Sparse Key := [(key1278, -2), (key1274, -2), (key1278, -2), (key1278, 6), (key1701, -2), (key1697, -2), (key1701, -2), (key1701, 2), (key1697, 2), (key1751, 2), (key1697, 2), (key1751, 2), (key1701, 2), (key1701, -2), (key1751, -2), (key1701, -2), (key1852, 6), (key1852, -2), (key1884, -2), (key1852, -2)]

theorem rawRowCheck14762 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form8 = rawRow14762 := by decide +kernel

def row14762 : Integer.Sparse Key := [(key1274, -2), (key1278, 2), (key1697, 2), (key1701, -4), (key1751, 2), (key1852, 2), (key1884, -2)]

theorem rowCheck14762 : row14762 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14762 := by decide +kernel

theorem rowEval14762 (x : Key → ℝ) : Integer.Sparse.eval row14762 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14762, Integer.Sparse.eval_collectBalanced, rawRowCheck14762]

def rawRow14763 : Integer.Sparse Key := [(key1278, -2), (key1278, -2), (key1274, -2), (key1278, 6), (key1701, -2), (key1701, -2), (key1697, -2), (key1751, 2), (key1751, 2), (key1701, 2), (key1701, 2), (key1697, 2), (key1697, 2), (key1751, -2), (key1701, -2), (key1701, -2), (key1852, 6), (key1884, -2), (key1852, -2), (key1852, -2)]

theorem rawRowCheck14763 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form8 = rawRow14763 := by decide +kernel

def row14763 : Integer.Sparse Key := [(key1274, -2), (key1278, 2), (key1697, 2), (key1701, -4), (key1751, 2), (key1852, 2), (key1884, -2)]

theorem rowCheck14763 : row14763 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14763 := by decide +kernel

theorem rowEval14763 (x : Key → ℝ) : Integer.Sparse.eval row14763 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14763, Integer.Sparse.eval_collectBalanced, rawRowCheck14763]

def rawRow14764 : Integer.Sparse Key := [(key1278, -2), (key1278, -2), (key1278, -2), (key1274, 6), (key1751, -2), (key1751, -2), (key1751, -2), (key1701, 2), (key1701, 2), (key1701, 2), (key1701, 2), (key1701, 2), (key1701, 2), (key1697, -2), (key1697, -2), (key1697, -2), (key1884, 6), (key1852, -2), (key1852, -2), (key1852, -2)]

theorem rawRowCheck14764 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form8 = rawRow14764 := by decide +kernel

def row14764 : Integer.Sparse Key := [(key1274, 6), (key1278, -6), (key1697, -6), (key1701, 12), (key1751, -6), (key1852, -6), (key1884, 6)]

theorem rowCheck14764 : row14764 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14764 := by decide +kernel

theorem rowEval14764 (x : Key → ℝ) : Integer.Sparse.eval row14764 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14764, Integer.Sparse.eval_collectBalanced, rawRowCheck14764]

def rawRow14765 : Integer.Sparse Key := [(key1697, -2), (key1701, -2), (key1701, -2), (key1852, 6), (key1274, -2), (key1278, -2), (key1278, -2), (key1697, 2), (key1701, 2), (key1697, 2), (key1751, 2), (key1701, 2), (key1751, 2), (key1852, -2), (key1852, -2), (key1884, -2), (key1278, 6), (key1701, -2), (key1701, -2), (key1751, -2)]

theorem rawRowCheck14765 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form8 = rawRow14765 := by decide +kernel

def row14765 : Integer.Sparse Key := [(key1274, -2), (key1278, 2), (key1697, 2), (key1701, -4), (key1751, 2), (key1852, 2), (key1884, -2)]

theorem rowCheck14765 : row14765 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14765 := by decide +kernel

theorem rowEval14765 (x : Key → ℝ) : Integer.Sparse.eval row14765 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck14765, Integer.Sparse.eval_collectBalanced, rawRowCheck14765]

def rawRow14766 : Integer.Sparse Key := [(key1701, -2), (key1697, -2), (key1701, -2), (key1852, 6), (key1278, -2), (key1274, -2), (key1278, -2), (key1701, 2), (key1697, 2), (key1751, 2), (key1697, 2), (key1751, 2), (key1701, 2), (key1852, -2), (key1884, -2), (key1852, -2), (key1278, 6), (key1701, -2), (key1751, -2), (key1701, -2)]

theorem rawRowCheck14766 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form8 = rawRow14766 := by decide +kernel

def row14766 : Integer.Sparse Key := [(key1274, -2), (key1278, 2), (key1697, 2), (key1701, -4), (key1751, 2), (key1852, 2), (key1884, -2)]

theorem rowCheck14766 : row14766 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14766 := by decide +kernel

theorem rowEval14766 (x : Key → ℝ) : Integer.Sparse.eval row14766 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14766, Integer.Sparse.eval_collectBalanced, rawRowCheck14766]

def rawRow14767 : Integer.Sparse Key := [(key1701, -2), (key1701, -2), (key1697, -2), (key1852, 6), (key1278, -2), (key1278, -2), (key1274, -2), (key1751, 2), (key1751, 2), (key1701, 2), (key1701, 2), (key1697, 2), (key1697, 2), (key1884, -2), (key1852, -2), (key1852, -2), (key1278, 6), (key1751, -2), (key1701, -2), (key1701, -2)]

theorem rawRowCheck14767 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form8 = rawRow14767 := by decide +kernel

def row14767 : Integer.Sparse Key := [(key1274, -2), (key1278, 2), (key1697, 2), (key1701, -4), (key1751, 2), (key1852, 2), (key1884, -2)]

theorem rowCheck14767 : row14767 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14767 := by decide +kernel

theorem rowEval14767 (x : Key → ℝ) : Integer.Sparse.eval row14767 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14767, Integer.Sparse.eval_collectBalanced, rawRowCheck14767]

def rawRow14768 : Integer.Sparse Key := [(key1697, -2), (key1701, -2), (key1852, -2), (key1701, 6), (key1697, -2), (key1701, -2), (key1852, -2), (key1274, 2), (key1278, 2), (key1697, 2), (key1751, 2), (key1852, 2), (key1884, 2), (key1278, -2), (key1701, -2), (key1751, -2), (key1701, 6), (key1278, -2), (key1701, -2), (key1751, -2)]

theorem rawRowCheck14768 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form8 = rawRow14768 := by decide +kernel

def row14768 : Integer.Sparse Key := [(key1274, 2), (key1278, -2), (key1697, -2), (key1701, 4), (key1751, -2), (key1852, -2), (key1884, 2)]

theorem rowCheck14768 : row14768 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14768 := by decide +kernel

theorem rowEval14768 (x : Key → ℝ) : Integer.Sparse.eval row14768 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck14768, Integer.Sparse.eval_collectBalanced, rawRowCheck14768]

def rawRow14769 : Integer.Sparse Key := [(key1701, -2), (key1697, -2), (key1852, -2), (key1701, 6), (key1701, -2), (key1697, -2), (key1852, -2), (key1278, 2), (key1274, 2), (key1751, 2), (key1697, 2), (key1884, 2), (key1852, 2), (key1278, -2), (key1751, -2), (key1701, -2), (key1701, 6), (key1278, -2), (key1751, -2), (key1701, -2)]

theorem rawRowCheck14769 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form8 = rawRow14769 := by decide +kernel

def row14769 : Integer.Sparse Key := [(key1274, 2), (key1278, -2), (key1697, -2), (key1701, 4), (key1751, -2), (key1852, -2), (key1884, 2)]

theorem rowCheck14769 : row14769 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14769 := by decide +kernel

theorem rowEval14769 (x : Key → ℝ) : Integer.Sparse.eval row14769 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14769, Integer.Sparse.eval_collectBalanced, rawRowCheck14769]

def rawRow14770 : Integer.Sparse Key := [(key1697, -2), (key1852, -2), (key1701, -2), (key1701, 6), (key1697, -2), (key1852, -2), (key1701, -2), (key1697, 2), (key1852, 2), (key1274, 2), (key1884, 2), (key1278, 2), (key1751, 2), (key1701, -2), (key1278, -2), (key1751, -2), (key1701, 6), (key1701, -2), (key1278, -2), (key1751, -2)]

theorem rawRowCheck14770 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form8 = rawRow14770 := by decide +kernel

def row14770 : Integer.Sparse Key := [(key1274, 2), (key1278, -2), (key1697, -2), (key1701, 4), (key1751, -2), (key1852, -2), (key1884, 2)]

theorem rowCheck14770 : row14770 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14770 := by decide +kernel

theorem rowEval14770 (x : Key → ℝ) : Integer.Sparse.eval row14770 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck14770, Integer.Sparse.eval_collectBalanced, rawRowCheck14770]

def rawRow14771 : Integer.Sparse Key := [(key1852, -2), (key1697, -2), (key1701, -2), (key1701, 6), (key1852, -2), (key1697, -2), (key1701, -2), (key1852, 2), (key1697, 2), (key1884, 2), (key1274, 2), (key1751, 2), (key1278, 2), (key1701, -2), (key1751, -2), (key1278, -2), (key1701, 6), (key1701, -2), (key1751, -2), (key1278, -2)]

theorem rawRowCheck14771 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form8 = rawRow14771 := by decide +kernel

def row14771 : Integer.Sparse Key := [(key1274, 2), (key1278, -2), (key1697, -2), (key1701, 4), (key1751, -2), (key1852, -2), (key1884, 2)]

theorem rowCheck14771 : row14771 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14771 := by decide +kernel

theorem rowEval14771 (x : Key → ℝ) : Integer.Sparse.eval row14771 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck14771, Integer.Sparse.eval_collectBalanced, rawRowCheck14771]

def rawRow14772 : Integer.Sparse Key := [(key1701, -2), (key1852, -2), (key1697, -2), (key1701, 6), (key1701, -2), (key1852, -2), (key1697, -2), (key1751, 2), (key1884, 2), (key1278, 2), (key1852, 2), (key1274, 2), (key1697, 2), (key1751, -2), (key1278, -2), (key1701, -2), (key1701, 6), (key1751, -2), (key1278, -2), (key1701, -2)]

theorem rawRowCheck14772 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form8 = rawRow14772 := by decide +kernel

def row14772 : Integer.Sparse Key := [(key1274, 2), (key1278, -2), (key1697, -2), (key1701, 4), (key1751, -2), (key1852, -2), (key1884, 2)]

theorem rowCheck14772 : row14772 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14772 := by decide +kernel

theorem rowEval14772 (x : Key → ℝ) : Integer.Sparse.eval row14772 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14772, Integer.Sparse.eval_collectBalanced, rawRowCheck14772]

def rawRow14773 : Integer.Sparse Key := [(key1852, -2), (key1701, -2), (key1697, -2), (key1701, 6), (key1852, -2), (key1701, -2), (key1697, -2), (key1884, 2), (key1751, 2), (key1852, 2), (key1278, 2), (key1697, 2), (key1274, 2), (key1751, -2), (key1701, -2), (key1278, -2), (key1701, 6), (key1751, -2), (key1701, -2), (key1278, -2)]

theorem rawRowCheck14773 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form8 = rawRow14773 := by decide +kernel

def row14773 : Integer.Sparse Key := [(key1274, 2), (key1278, -2), (key1697, -2), (key1701, 4), (key1751, -2), (key1852, -2), (key1884, 2)]

theorem rowCheck14773 : row14773 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14773 := by decide +kernel

theorem rowEval14773 (x : Key → ℝ) : Integer.Sparse.eval row14773 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck14773, Integer.Sparse.eval_collectBalanced, rawRowCheck14773]

def rawRow14774 : Integer.Sparse Key := [(key1701, -2), (key1701, -2), (key1852, -2), (key1697, 6), (key1751, -2), (key1751, -2), (key1884, -2), (key1278, 2), (key1278, 2), (key1701, 2), (key1701, 2), (key1852, 2), (key1852, 2), (key1274, -2), (key1697, -2), (key1697, -2), (key1751, 6), (key1278, -2), (key1701, -2), (key1701, -2)]

theorem rawRowCheck14774 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form8 = rawRow14774 := by decide +kernel

def row14774 : Integer.Sparse Key := [(key1274, -2), (key1278, 2), (key1697, 2), (key1701, -4), (key1751, 2), (key1852, 2), (key1884, -2)]

theorem rowCheck14774 : row14774 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14774 := by decide +kernel

theorem rowEval14774 (x : Key → ℝ) : Integer.Sparse.eval row14774 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14774, Integer.Sparse.eval_collectBalanced, rawRowCheck14774]

def rawRow14775 : Integer.Sparse Key := [(key1701, -2), (key1852, -2), (key1701, -2), (key1697, 6), (key1751, -2), (key1884, -2), (key1751, -2), (key1701, 2), (key1852, 2), (key1278, 2), (key1852, 2), (key1278, 2), (key1701, 2), (key1697, -2), (key1274, -2), (key1697, -2), (key1751, 6), (key1701, -2), (key1278, -2), (key1701, -2)]

theorem rawRowCheck14775 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form8 = rawRow14775 := by decide +kernel

def row14775 : Integer.Sparse Key := [(key1274, -2), (key1278, 2), (key1697, 2), (key1701, -4), (key1751, 2), (key1852, 2), (key1884, -2)]

theorem rowCheck14775 : row14775 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14775 := by decide +kernel

theorem rowEval14775 (x : Key → ℝ) : Integer.Sparse.eval row14775 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14775, Integer.Sparse.eval_collectBalanced, rawRowCheck14775]

def rawRow14776 : Integer.Sparse Key := [(key1852, -2), (key1701, -2), (key1701, -2), (key1697, 6), (key1884, -2), (key1751, -2), (key1751, -2), (key1852, 2), (key1701, 2), (key1852, 2), (key1278, 2), (key1701, 2), (key1278, 2), (key1697, -2), (key1697, -2), (key1274, -2), (key1751, 6), (key1701, -2), (key1701, -2), (key1278, -2)]

theorem rawRowCheck14776 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form8 = rawRow14776 := by decide +kernel

def row14776 : Integer.Sparse Key := [(key1274, -2), (key1278, 2), (key1697, 2), (key1701, -4), (key1751, 2), (key1852, 2), (key1884, -2)]

theorem rowCheck14776 : row14776 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14776 := by decide +kernel

theorem rowEval14776 (x : Key → ℝ) : Integer.Sparse.eval row14776 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck14776, Integer.Sparse.eval_collectBalanced, rawRowCheck14776]

def rawRow14777 : Integer.Sparse Key := [(key1751, -2), (key1751, -2), (key1751, -2), (key1884, 6), (key1278, -2), (key1278, -2), (key1278, -2), (key1701, 2), (key1701, 2), (key1701, 2), (key1701, 2), (key1701, 2), (key1701, 2), (key1852, -2), (key1852, -2), (key1852, -2), (key1274, 6), (key1697, -2), (key1697, -2), (key1697, -2)]

theorem rawRowCheck14777 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form8 = rawRow14777 := by decide +kernel

def row14777 : Integer.Sparse Key := [(key1274, 6), (key1278, -6), (key1697, -6), (key1701, 12), (key1751, -6), (key1852, -6), (key1884, 6)]

theorem rowCheck14777 : row14777 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14777 := by decide +kernel

theorem rowEval14777 (x : Key → ℝ) : Integer.Sparse.eval row14777 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14777, Integer.Sparse.eval_collectBalanced, rawRowCheck14777]

def rawRow14778 : Integer.Sparse Key := [(key1751, -2), (key1751, -2), (key1884, -2), (key1751, 6), (key1701, -2), (key1701, -2), (key1852, -2), (key1278, 2), (key1278, 2), (key1701, 2), (key1701, 2), (key1852, 2), (key1852, 2), (key1278, -2), (key1701, -2), (key1701, -2), (key1697, 6), (key1274, -2), (key1697, -2), (key1697, -2)]

theorem rawRowCheck14778 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form8 = rawRow14778 := by decide +kernel

def row14778 : Integer.Sparse Key := [(key1274, -2), (key1278, 2), (key1697, 2), (key1701, -4), (key1751, 2), (key1852, 2), (key1884, -2)]

theorem rowCheck14778 : row14778 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14778 := by decide +kernel

theorem rowEval14778 (x : Key → ℝ) : Integer.Sparse.eval row14778 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14778, Integer.Sparse.eval_collectBalanced, rawRowCheck14778]

def rawRow14779 : Integer.Sparse Key := [(key1751, -2), (key1884, -2), (key1751, -2), (key1751, 6), (key1701, -2), (key1852, -2), (key1701, -2), (key1701, 2), (key1852, 2), (key1278, 2), (key1852, 2), (key1278, 2), (key1701, 2), (key1701, -2), (key1278, -2), (key1701, -2), (key1697, 6), (key1697, -2), (key1274, -2), (key1697, -2)]

theorem rawRowCheck14779 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form8 = rawRow14779 := by decide +kernel

def row14779 : Integer.Sparse Key := [(key1274, -2), (key1278, 2), (key1697, 2), (key1701, -4), (key1751, 2), (key1852, 2), (key1884, -2)]

theorem rowCheck14779 : row14779 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14779 := by decide +kernel

theorem rowEval14779 (x : Key → ℝ) : Integer.Sparse.eval row14779 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14779, Integer.Sparse.eval_collectBalanced, rawRowCheck14779]

def rawRow14780 : Integer.Sparse Key := [(key1884, -2), (key1751, -2), (key1751, -2), (key1751, 6), (key1852, -2), (key1701, -2), (key1701, -2), (key1852, 2), (key1701, 2), (key1852, 2), (key1278, 2), (key1701, 2), (key1278, 2), (key1701, -2), (key1701, -2), (key1278, -2), (key1697, 6), (key1697, -2), (key1697, -2), (key1274, -2)]

theorem rawRowCheck14780 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form8 = rawRow14780 := by decide +kernel

def row14780 : Integer.Sparse Key := [(key1274, -2), (key1278, 2), (key1697, 2), (key1701, -4), (key1751, 2), (key1852, 2), (key1884, -2)]

theorem rowCheck14780 : row14780 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14780 := by decide +kernel

theorem rowEval14780 (x : Key → ℝ) : Integer.Sparse.eval row14780 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck14780, Integer.Sparse.eval_collectBalanced, rawRowCheck14780]

def rawRow14781 : Integer.Sparse Key := [(key358, 4), (key358, 4), (key363, 4), (key358, -4), (key363, -4), (key363, -4), (key528, -4), (key532, -4), (key532, -4), (key532, 12)]

theorem rawRowCheck14781 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form9 = rawRow14781 := by decide +kernel

def row14781 : Integer.Sparse Key := [(key358, 4), (key363, -4), (key528, -4), (key532, 4)]

theorem rowCheck14781 : row14781 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14781 := by decide +kernel

theorem rowEval14781 (x : Key → ℝ) : Integer.Sparse.eval row14781 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14781, Integer.Sparse.eval_collectBalanced, rawRowCheck14781]

def rawRow14782 : Integer.Sparse Key := [(key358, 4), (key363, 4), (key358, 4), (key363, -4), (key358, -4), (key363, -4), (key532, -4), (key528, -4), (key532, -4), (key532, 12)]

theorem rawRowCheck14782 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form9 = rawRow14782 := by decide +kernel

def row14782 : Integer.Sparse Key := [(key358, 4), (key363, -4), (key528, -4), (key532, 4)]

theorem rowCheck14782 : row14782 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14782 := by decide +kernel

theorem rowEval14782 (x : Key → ℝ) : Integer.Sparse.eval row14782 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14782, Integer.Sparse.eval_collectBalanced, rawRowCheck14782]

def rawRow14783 : Integer.Sparse Key := [(key363, 4), (key358, 4), (key358, 4), (key363, -4), (key363, -4), (key358, -4), (key532, -4), (key532, -4), (key528, -4), (key532, 12)]

theorem rawRowCheck14783 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form9 = rawRow14783 := by decide +kernel

def row14783 : Integer.Sparse Key := [(key358, 4), (key363, -4), (key528, -4), (key532, 4)]

theorem rowCheck14783 : row14783 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14783 := by decide +kernel

theorem rowEval14783 (x : Key → ℝ) : Integer.Sparse.eval row14783 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14783, Integer.Sparse.eval_collectBalanced, rawRowCheck14783]

def rawRow14784 : Integer.Sparse Key := [(key363, 4), (key363, 4), (key363, 4), (key358, -4), (key358, -4), (key358, -4), (key532, -4), (key532, -4), (key532, -4), (key528, 12)]

theorem rawRowCheck14784 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form9 = rawRow14784 := by decide +kernel

def row14784 : Integer.Sparse Key := [(key358, -12), (key363, 12), (key528, 12), (key532, -12)]

theorem rowCheck14784 : row14784 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14784 := by decide +kernel

theorem rowEval14784 (x : Key → ℝ) : Integer.Sparse.eval row14784 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14784, Integer.Sparse.eval_collectBalanced, rawRowCheck14784]

def rawRow14785 : Integer.Sparse Key := [(key358, 4), (key358, 4), (key363, 4), (key528, -4), (key532, -4), (key532, -4), (key358, -4), (key363, -4), (key363, -4), (key532, 12)]

theorem rawRowCheck14785 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form9 = rawRow14785 := by decide +kernel

def row14785 : Integer.Sparse Key := [(key358, 4), (key363, -4), (key528, -4), (key532, 4)]

theorem rowCheck14785 : row14785 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14785 := by decide +kernel

theorem rowEval14785 (x : Key → ℝ) : Integer.Sparse.eval row14785 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14785, Integer.Sparse.eval_collectBalanced, rawRowCheck14785]

def rawRow14786 : Integer.Sparse Key := [(key358, 4), (key363, 4), (key358, 4), (key532, -4), (key528, -4), (key532, -4), (key363, -4), (key358, -4), (key363, -4), (key532, 12)]

theorem rawRowCheck14786 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form9 = rawRow14786 := by decide +kernel

def row14786 : Integer.Sparse Key := [(key358, 4), (key363, -4), (key528, -4), (key532, 4)]

theorem rowCheck14786 : row14786 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14786 := by decide +kernel

theorem rowEval14786 (x : Key → ℝ) : Integer.Sparse.eval row14786 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14786, Integer.Sparse.eval_collectBalanced, rawRowCheck14786]

def rawRow14787 : Integer.Sparse Key := [(key363, 4), (key358, 4), (key358, 4), (key532, -4), (key532, -4), (key528, -4), (key363, -4), (key363, -4), (key358, -4), (key532, 12)]

theorem rawRowCheck14787 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form9 = rawRow14787 := by decide +kernel

def row14787 : Integer.Sparse Key := [(key358, 4), (key363, -4), (key528, -4), (key532, 4)]

theorem rowCheck14787 : row14787 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14787 := by decide +kernel

theorem rowEval14787 (x : Key → ℝ) : Integer.Sparse.eval row14787 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14787, Integer.Sparse.eval_collectBalanced, rawRowCheck14787]

def rawRow14788 : Integer.Sparse Key := [(key358, 4), (key528, 4), (key532, 4), (key358, -4), (key363, -4), (key532, -4), (key358, -4), (key363, -4), (key532, -4), (key363, 12)]

theorem rawRowCheck14788 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form9 = rawRow14788 := by decide +kernel

def row14788 : Integer.Sparse Key := [(key358, -4), (key363, 4), (key528, 4), (key532, -4)]

theorem rowCheck14788 : row14788 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14788 := by decide +kernel

theorem rowEval14788 (x : Key → ℝ) : Integer.Sparse.eval row14788 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14788, Integer.Sparse.eval_collectBalanced, rawRowCheck14788]

def rawRow14789 : Integer.Sparse Key := [(key358, 4), (key532, 4), (key528, 4), (key363, -4), (key358, -4), (key532, -4), (key363, -4), (key358, -4), (key532, -4), (key363, 12)]

theorem rawRowCheck14789 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form9 = rawRow14789 := by decide +kernel

def row14789 : Integer.Sparse Key := [(key358, -4), (key363, 4), (key528, 4), (key532, -4)]

theorem rowCheck14789 : row14789 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14789 := by decide +kernel

theorem rowEval14789 (x : Key → ℝ) : Integer.Sparse.eval row14789 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14789, Integer.Sparse.eval_collectBalanced, rawRowCheck14789]

def rawRow14790 : Integer.Sparse Key := [(key528, 4), (key358, 4), (key532, 4), (key358, -4), (key532, -4), (key363, -4), (key358, -4), (key532, -4), (key363, -4), (key363, 12)]

theorem rawRowCheck14790 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form9 = rawRow14790 := by decide +kernel

def row14790 : Integer.Sparse Key := [(key358, -4), (key363, 4), (key528, 4), (key532, -4)]

theorem rowCheck14790 : row14790 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14790 := by decide +kernel

theorem rowEval14790 (x : Key → ℝ) : Integer.Sparse.eval row14790 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14790, Integer.Sparse.eval_collectBalanced, rawRowCheck14790]

def rawRow14791 : Integer.Sparse Key := [(key528, 4), (key532, 4), (key358, 4), (key532, -4), (key358, -4), (key363, -4), (key532, -4), (key358, -4), (key363, -4), (key363, 12)]

theorem rawRowCheck14791 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form9 = rawRow14791 := by decide +kernel

def row14791 : Integer.Sparse Key := [(key358, -4), (key363, 4), (key528, 4), (key532, -4)]

theorem rowCheck14791 : row14791 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14791 := by decide +kernel

theorem rowEval14791 (x : Key → ℝ) : Integer.Sparse.eval row14791 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14791, Integer.Sparse.eval_collectBalanced, rawRowCheck14791]

def rawRow14792 : Integer.Sparse Key := [(key532, 4), (key358, 4), (key528, 4), (key363, -4), (key532, -4), (key358, -4), (key363, -4), (key532, -4), (key358, -4), (key363, 12)]

theorem rawRowCheck14792 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form9 = rawRow14792 := by decide +kernel

def row14792 : Integer.Sparse Key := [(key358, -4), (key363, 4), (key528, 4), (key532, -4)]

theorem rowCheck14792 : row14792 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14792 := by decide +kernel

theorem rowEval14792 (x : Key → ℝ) : Integer.Sparse.eval row14792 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14792, Integer.Sparse.eval_collectBalanced, rawRowCheck14792]

def rawRow14793 : Integer.Sparse Key := [(key532, 4), (key528, 4), (key358, 4), (key532, -4), (key363, -4), (key358, -4), (key532, -4), (key363, -4), (key358, -4), (key363, 12)]

theorem rawRowCheck14793 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form9 = rawRow14793 := by decide +kernel

def row14793 : Integer.Sparse Key := [(key358, -4), (key363, 4), (key528, 4), (key532, -4)]

theorem rowCheck14793 : row14793 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14793 := by decide +kernel

theorem rowEval14793 (x : Key → ℝ) : Integer.Sparse.eval row14793 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14793, Integer.Sparse.eval_collectBalanced, rawRowCheck14793]

def rawRow14794 : Integer.Sparse Key := [(key363, 4), (key532, 4), (key532, 4), (key358, -4), (key358, -4), (key528, -4), (key363, -4), (key363, -4), (key532, -4), (key358, 12)]

theorem rawRowCheck14794 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form9 = rawRow14794 := by decide +kernel

def row14794 : Integer.Sparse Key := [(key358, 4), (key363, -4), (key528, -4), (key532, 4)]

theorem rowCheck14794 : row14794 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14794 := by decide +kernel

theorem rowEval14794 (x : Key → ℝ) : Integer.Sparse.eval row14794 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14794, Integer.Sparse.eval_collectBalanced, rawRowCheck14794]

def rawRow14795 : Integer.Sparse Key := [(key532, 4), (key363, 4), (key532, 4), (key358, -4), (key528, -4), (key358, -4), (key363, -4), (key532, -4), (key363, -4), (key358, 12)]

theorem rawRowCheck14795 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form9 = rawRow14795 := by decide +kernel

def row14795 : Integer.Sparse Key := [(key358, 4), (key363, -4), (key528, -4), (key532, 4)]

theorem rowCheck14795 : row14795 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14795 := by decide +kernel

theorem rowEval14795 (x : Key → ℝ) : Integer.Sparse.eval row14795 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14795, Integer.Sparse.eval_collectBalanced, rawRowCheck14795]

def rawRow14796 : Integer.Sparse Key := [(key532, 4), (key532, 4), (key363, 4), (key528, -4), (key358, -4), (key358, -4), (key532, -4), (key363, -4), (key363, -4), (key358, 12)]

theorem rawRowCheck14796 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form9 = rawRow14796 := by decide +kernel

def row14796 : Integer.Sparse Key := [(key358, 4), (key363, -4), (key528, -4), (key532, 4)]

theorem rowCheck14796 : row14796 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14796 := by decide +kernel

theorem rowEval14796 (x : Key → ℝ) : Integer.Sparse.eval row14796 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14796, Integer.Sparse.eval_collectBalanced, rawRowCheck14796]

def rawRow14797 : Integer.Sparse Key := [(key363, 4), (key363, 4), (key363, 4), (key532, -4), (key532, -4), (key532, -4), (key358, -4), (key358, -4), (key358, -4), (key528, 12)]

theorem rawRowCheck14797 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form9 = rawRow14797 := by decide +kernel

def row14797 : Integer.Sparse Key := [(key358, -12), (key363, 12), (key528, 12), (key532, -12)]

theorem rowCheck14797 : row14797 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14797 := by decide +kernel

theorem rowEval14797 (x : Key → ℝ) : Integer.Sparse.eval row14797 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14797, Integer.Sparse.eval_collectBalanced, rawRowCheck14797]

def rawRow14798 : Integer.Sparse Key := [(key363, 4), (key532, 4), (key532, 4), (key363, -4), (key363, -4), (key532, -4), (key358, -4), (key358, -4), (key528, -4), (key358, 12)]

theorem rawRowCheck14798 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form9 = rawRow14798 := by decide +kernel

def row14798 : Integer.Sparse Key := [(key358, 4), (key363, -4), (key528, -4), (key532, 4)]

theorem rowCheck14798 : row14798 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14798 := by decide +kernel

theorem rowEval14798 (x : Key → ℝ) : Integer.Sparse.eval row14798 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14798, Integer.Sparse.eval_collectBalanced, rawRowCheck14798]

def rawRow14799 : Integer.Sparse Key := [(key532, 4), (key363, 4), (key532, 4), (key363, -4), (key532, -4), (key363, -4), (key358, -4), (key528, -4), (key358, -4), (key358, 12)]

theorem rawRowCheck14799 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form9 = rawRow14799 := by decide +kernel

def row14799 : Integer.Sparse Key := [(key358, 4), (key363, -4), (key528, -4), (key532, 4)]

theorem rowCheck14799 : row14799 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14799 := by decide +kernel

theorem rowEval14799 (x : Key → ℝ) : Integer.Sparse.eval row14799 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14799, Integer.Sparse.eval_collectBalanced, rawRowCheck14799]

def rawRow14800 : Integer.Sparse Key := [(key532, 4), (key532, 4), (key363, 4), (key532, -4), (key363, -4), (key363, -4), (key528, -4), (key358, -4), (key358, -4), (key358, 12)]

theorem rawRowCheck14800 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form9 = rawRow14800 := by decide +kernel

def row14800 : Integer.Sparse Key := [(key358, 4), (key363, -4), (key528, -4), (key532, 4)]

theorem rowCheck14800 : row14800 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14800 := by decide +kernel

theorem rowEval14800 (x : Key → ℝ) : Integer.Sparse.eval row14800 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14800, Integer.Sparse.eval_collectBalanced, rawRowCheck14800]

def rawRow14801 : Integer.Sparse Key := [(key1485, -1), (key1490, -1), (key1485, -1), (key1513, -1), (key1490, -1), (key1513, -1), (key1490, 2), (key1490, 2), (key1513, 2), (key1711, -1), (key1716, -1), (key1711, -1), (key1741, -1), (key1716, -1), (key1741, -1), (key1711, 2), (key1723, 2), (key1711, 2), (key1741, 2), (key1723, 2), (key1741, 2), (key1716, -1), (key1723, -1), (key1716, -1), (key1741, -1), (key1723, -1), (key1741, -1), (key1861, 2), (key1861, 2), (key1877, 2), (key1861, -1), (key1867, -1), (key1861, -1), (key1877, -1), (key1867, -1), (key1877, -1)]

theorem rawRowCheck14801 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form10 = rawRow14801 := by decide +kernel

def row14801 : Integer.Sparse Key := [(key1485, -2), (key1490, 2), (key1711, 2), (key1716, -4), (key1723, 2), (key1861, 2), (key1867, -2)]

theorem rowCheck14801 : row14801 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14801 := by decide +kernel

theorem rowEval14801 (x : Key → ℝ) : Integer.Sparse.eval row14801 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form10) x := by
  rw [rowCheck14801, Integer.Sparse.eval_collectBalanced, rawRowCheck14801]

def rawRow14802 : Integer.Sparse Key := [(key1490, -1), (key1485, -1), (key1513, -1), (key1485, -1), (key1513, -1), (key1490, -1), (key1490, 2), (key1513, 2), (key1490, 2), (key1716, -1), (key1711, -1), (key1741, -1), (key1711, -1), (key1741, -1), (key1716, -1), (key1723, 2), (key1711, 2), (key1741, 2), (key1711, 2), (key1741, 2), (key1723, 2), (key1723, -1), (key1716, -1), (key1741, -1), (key1716, -1), (key1741, -1), (key1723, -1), (key1861, 2), (key1877, 2), (key1861, 2), (key1867, -1), (key1861, -1), (key1877, -1), (key1861, -1), (key1877, -1), (key1867, -1)]

theorem rawRowCheck14802 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form10 = rawRow14802 := by decide +kernel

def row14802 : Integer.Sparse Key := [(key1485, -2), (key1490, 2), (key1711, 2), (key1716, -4), (key1723, 2), (key1861, 2), (key1867, -2)]

theorem rowCheck14802 : row14802 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14802 := by decide +kernel

theorem rowEval14802 (x : Key → ℝ) : Integer.Sparse.eval row14802 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck14802, Integer.Sparse.eval_collectBalanced, rawRowCheck14802]

def rawRow14803 : Integer.Sparse Key := [(key1513, -1), (key1513, -1), (key1490, -1), (key1490, -1), (key1485, -1), (key1485, -1), (key1513, 2), (key1490, 2), (key1490, 2), (key1741, -1), (key1741, -1), (key1716, -1), (key1716, -1), (key1711, -1), (key1711, -1), (key1741, 2), (key1741, 2), (key1723, 2), (key1723, 2), (key1711, 2), (key1711, 2), (key1741, -1), (key1741, -1), (key1723, -1), (key1723, -1), (key1716, -1), (key1716, -1), (key1877, 2), (key1861, 2), (key1861, 2), (key1877, -1), (key1877, -1), (key1867, -1), (key1867, -1), (key1861, -1), (key1861, -1)]

theorem rawRowCheck14803 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form10 = rawRow14803 := by decide +kernel

def row14803 : Integer.Sparse Key := [(key1485, -2), (key1490, 2), (key1711, 2), (key1716, -4), (key1723, 2), (key1861, 2), (key1867, -2)]

theorem rowCheck14803 : row14803 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14803 := by decide +kernel

theorem rowEval14803 (x : Key → ℝ) : Integer.Sparse.eval row14803 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck14803, Integer.Sparse.eval_collectBalanced, rawRowCheck14803]

def rawRow14804 : Integer.Sparse Key := [(key1490, -1), (key1490, -1), (key1490, -1), (key1490, -1), (key1490, -1), (key1490, -1), (key1485, 2), (key1485, 2), (key1485, 2), (key1723, -1), (key1723, -1), (key1723, -1), (key1723, -1), (key1723, -1), (key1723, -1), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1711, -1), (key1711, -1), (key1711, -1), (key1711, -1), (key1711, -1), (key1711, -1), (key1867, 2), (key1867, 2), (key1867, 2), (key1861, -1), (key1861, -1), (key1861, -1), (key1861, -1), (key1861, -1), (key1861, -1)]

theorem rawRowCheck14804 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form10 = rawRow14804 := by decide +kernel

def row14804 : Integer.Sparse Key := [(key1485, 6), (key1490, -6), (key1711, -6), (key1716, 12), (key1723, -6), (key1861, -6), (key1867, 6)]

theorem rowCheck14804 : row14804 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14804 := by decide +kernel

theorem rowEval14804 (x : Key → ℝ) : Integer.Sparse.eval row14804 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck14804, Integer.Sparse.eval_collectBalanced, rawRowCheck14804]

def rawRow14805 : Integer.Sparse Key := [(key1711, -1), (key1716, -1), (key1711, -1), (key1741, -1), (key1716, -1), (key1741, -1), (key1861, 2), (key1861, 2), (key1877, 2), (key1485, -1), (key1490, -1), (key1485, -1), (key1513, -1), (key1490, -1), (key1513, -1), (key1711, 2), (key1723, 2), (key1711, 2), (key1741, 2), (key1723, 2), (key1741, 2), (key1861, -1), (key1867, -1), (key1861, -1), (key1877, -1), (key1867, -1), (key1877, -1), (key1490, 2), (key1490, 2), (key1513, 2), (key1716, -1), (key1723, -1), (key1716, -1), (key1741, -1), (key1723, -1), (key1741, -1)]

theorem rawRowCheck14805 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form10 = rawRow14805 := by decide +kernel

def row14805 : Integer.Sparse Key := [(key1485, -2), (key1490, 2), (key1711, 2), (key1716, -4), (key1723, 2), (key1861, 2), (key1867, -2)]

theorem rowCheck14805 : row14805 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14805 := by decide +kernel

theorem rowEval14805 (x : Key → ℝ) : Integer.Sparse.eval row14805 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form10) x := by
  rw [rowCheck14805, Integer.Sparse.eval_collectBalanced, rawRowCheck14805]

def rawRow14806 : Integer.Sparse Key := [(key1716, -1), (key1711, -1), (key1741, -1), (key1711, -1), (key1741, -1), (key1716, -1), (key1861, 2), (key1877, 2), (key1861, 2), (key1490, -1), (key1485, -1), (key1513, -1), (key1485, -1), (key1513, -1), (key1490, -1), (key1723, 2), (key1711, 2), (key1741, 2), (key1711, 2), (key1741, 2), (key1723, 2), (key1867, -1), (key1861, -1), (key1877, -1), (key1861, -1), (key1877, -1), (key1867, -1), (key1490, 2), (key1513, 2), (key1490, 2), (key1723, -1), (key1716, -1), (key1741, -1), (key1716, -1), (key1741, -1), (key1723, -1)]

theorem rawRowCheck14806 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form10 = rawRow14806 := by decide +kernel

def row14806 : Integer.Sparse Key := [(key1485, -2), (key1490, 2), (key1711, 2), (key1716, -4), (key1723, 2), (key1861, 2), (key1867, -2)]

theorem rowCheck14806 : row14806 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14806 := by decide +kernel

theorem rowEval14806 (x : Key → ℝ) : Integer.Sparse.eval row14806 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck14806, Integer.Sparse.eval_collectBalanced, rawRowCheck14806]

def rawRow14807 : Integer.Sparse Key := [(key1741, -1), (key1741, -1), (key1716, -1), (key1716, -1), (key1711, -1), (key1711, -1), (key1877, 2), (key1861, 2), (key1861, 2), (key1513, -1), (key1513, -1), (key1490, -1), (key1490, -1), (key1485, -1), (key1485, -1), (key1741, 2), (key1741, 2), (key1723, 2), (key1723, 2), (key1711, 2), (key1711, 2), (key1877, -1), (key1877, -1), (key1867, -1), (key1867, -1), (key1861, -1), (key1861, -1), (key1513, 2), (key1490, 2), (key1490, 2), (key1741, -1), (key1741, -1), (key1723, -1), (key1723, -1), (key1716, -1), (key1716, -1)]

theorem rawRowCheck14807 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form10 = rawRow14807 := by decide +kernel

def row14807 : Integer.Sparse Key := [(key1485, -2), (key1490, 2), (key1711, 2), (key1716, -4), (key1723, 2), (key1861, 2), (key1867, -2)]

theorem rowCheck14807 : row14807 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14807 := by decide +kernel

theorem rowEval14807 (x : Key → ℝ) : Integer.Sparse.eval row14807 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck14807, Integer.Sparse.eval_collectBalanced, rawRowCheck14807]

def rawRow14808 : Integer.Sparse Key := [(key1359, -1), (key1364, -1), (key1711, -1), (key1741, -1), (key1861, -1), (key1877, -1), (key1364, 2), (key1716, 2), (key1741, 2), (key1359, -1), (key1364, -1), (key1711, -1), (key1741, -1), (key1861, -1), (key1877, -1), (key1359, 2), (key1374, 2), (key1485, 2), (key1513, 2), (key1867, 2), (key1877, 2), (key1364, -1), (key1374, -1), (key1490, -1), (key1513, -1), (key1723, -1), (key1741, -1), (key1364, 2), (key1716, 2), (key1741, 2), (key1364, -1), (key1374, -1), (key1490, -1), (key1513, -1), (key1723, -1), (key1741, -1)]

theorem rawRowCheck14808 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form10 = rawRow14808 := by decide +kernel

def row14808 : Integer.Sparse Key := [(key1485, 2), (key1490, -2), (key1711, -2), (key1716, 4), (key1723, -2), (key1861, -2), (key1867, 2)]

theorem rowCheck14808 : row14808 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14808 := by decide +kernel

theorem rowEval14808 (x : Key → ℝ) : Integer.Sparse.eval row14808 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form10) x := by
  rw [rowCheck14808, Integer.Sparse.eval_collectBalanced, rawRowCheck14808]

def rawRow14809 : Integer.Sparse Key := [(key1364, -1), (key1359, -1), (key1741, -1), (key1711, -1), (key1877, -1), (key1861, -1), (key1364, 2), (key1741, 2), (key1716, 2), (key1364, -1), (key1359, -1), (key1741, -1), (key1711, -1), (key1877, -1), (key1861, -1), (key1374, 2), (key1359, 2), (key1513, 2), (key1485, 2), (key1877, 2), (key1867, 2), (key1374, -1), (key1364, -1), (key1513, -1), (key1490, -1), (key1741, -1), (key1723, -1), (key1364, 2), (key1741, 2), (key1716, 2), (key1374, -1), (key1364, -1), (key1513, -1), (key1490, -1), (key1741, -1), (key1723, -1)]

theorem rawRowCheck14809 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form10 = rawRow14809 := by decide +kernel

def row14809 : Integer.Sparse Key := [(key1485, 2), (key1490, -2), (key1711, -2), (key1716, 4), (key1723, -2), (key1861, -2), (key1867, 2)]

theorem rowCheck14809 : row14809 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14809 := by decide +kernel

theorem rowEval14809 (x : Key → ℝ) : Integer.Sparse.eval row14809 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck14809, Integer.Sparse.eval_collectBalanced, rawRowCheck14809]

def rawRow14810 : Integer.Sparse Key := [(key1711, -1), (key1861, -1), (key1359, -1), (key1877, -1), (key1364, -1), (key1741, -1), (key1716, 2), (key1364, 2), (key1741, 2), (key1711, -1), (key1861, -1), (key1359, -1), (key1877, -1), (key1364, -1), (key1741, -1), (key1485, 2), (key1867, 2), (key1359, 2), (key1877, 2), (key1374, 2), (key1513, 2), (key1490, -1), (key1723, -1), (key1364, -1), (key1741, -1), (key1374, -1), (key1513, -1), (key1716, 2), (key1364, 2), (key1741, 2), (key1490, -1), (key1723, -1), (key1364, -1), (key1741, -1), (key1374, -1), (key1513, -1)]

theorem rawRowCheck14810 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form10 = rawRow14810 := by decide +kernel

def row14810 : Integer.Sparse Key := [(key1485, 2), (key1490, -2), (key1711, -2), (key1716, 4), (key1723, -2), (key1861, -2), (key1867, 2)]

theorem rowCheck14810 : row14810 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14810 := by decide +kernel

theorem rowEval14810 (x : Key → ℝ) : Integer.Sparse.eval row14810 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form10) x := by
  rw [rowCheck14810, Integer.Sparse.eval_collectBalanced, rawRowCheck14810]

def rawRow14811 : Integer.Sparse Key := [(key1861, -1), (key1711, -1), (key1877, -1), (key1359, -1), (key1741, -1), (key1364, -1), (key1716, 2), (key1741, 2), (key1364, 2), (key1861, -1), (key1711, -1), (key1877, -1), (key1359, -1), (key1741, -1), (key1364, -1), (key1867, 2), (key1485, 2), (key1877, 2), (key1359, 2), (key1513, 2), (key1374, 2), (key1723, -1), (key1490, -1), (key1741, -1), (key1364, -1), (key1513, -1), (key1374, -1), (key1716, 2), (key1741, 2), (key1364, 2), (key1723, -1), (key1490, -1), (key1741, -1), (key1364, -1), (key1513, -1), (key1374, -1)]

theorem rawRowCheck14811 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form10 = rawRow14811 := by decide +kernel

def row14811 : Integer.Sparse Key := [(key1485, 2), (key1490, -2), (key1711, -2), (key1716, 4), (key1723, -2), (key1861, -2), (key1867, 2)]

theorem rowCheck14811 : row14811 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14811 := by decide +kernel

theorem rowEval14811 (x : Key → ℝ) : Integer.Sparse.eval row14811 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form10) x := by
  rw [rowCheck14811, Integer.Sparse.eval_collectBalanced, rawRowCheck14811]

def rawRow14812 : Integer.Sparse Key := [(key1741, -1), (key1877, -1), (key1364, -1), (key1861, -1), (key1359, -1), (key1711, -1), (key1741, 2), (key1364, 2), (key1716, 2), (key1741, -1), (key1877, -1), (key1364, -1), (key1861, -1), (key1359, -1), (key1711, -1), (key1513, 2), (key1877, 2), (key1374, 2), (key1867, 2), (key1359, 2), (key1485, 2), (key1513, -1), (key1741, -1), (key1374, -1), (key1723, -1), (key1364, -1), (key1490, -1), (key1741, 2), (key1364, 2), (key1716, 2), (key1513, -1), (key1741, -1), (key1374, -1), (key1723, -1), (key1364, -1), (key1490, -1)]

theorem rawRowCheck14812 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form10 = rawRow14812 := by decide +kernel

def row14812 : Integer.Sparse Key := [(key1485, 2), (key1490, -2), (key1711, -2), (key1716, 4), (key1723, -2), (key1861, -2), (key1867, 2)]

theorem rowCheck14812 : row14812 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14812 := by decide +kernel

theorem rowEval14812 (x : Key → ℝ) : Integer.Sparse.eval row14812 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck14812, Integer.Sparse.eval_collectBalanced, rawRowCheck14812]

def rawRow14813 : Integer.Sparse Key := [(key1877, -1), (key1741, -1), (key1861, -1), (key1364, -1), (key1711, -1), (key1359, -1), (key1741, 2), (key1716, 2), (key1364, 2), (key1877, -1), (key1741, -1), (key1861, -1), (key1364, -1), (key1711, -1), (key1359, -1), (key1877, 2), (key1513, 2), (key1867, 2), (key1374, 2), (key1485, 2), (key1359, 2), (key1741, -1), (key1513, -1), (key1723, -1), (key1374, -1), (key1490, -1), (key1364, -1), (key1741, 2), (key1716, 2), (key1364, 2), (key1741, -1), (key1513, -1), (key1723, -1), (key1374, -1), (key1490, -1), (key1364, -1)]

theorem rawRowCheck14813 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form10 = rawRow14813 := by decide +kernel

def row14813 : Integer.Sparse Key := [(key1485, 2), (key1490, -2), (key1711, -2), (key1716, 4), (key1723, -2), (key1861, -2), (key1867, 2)]

theorem rowCheck14813 : row14813 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14813 := by decide +kernel

theorem rowEval14813 (x : Key → ℝ) : Integer.Sparse.eval row14813 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form10) x := by
  rw [rowCheck14813, Integer.Sparse.eval_collectBalanced, rawRowCheck14813]

def rawRow14814 : Integer.Sparse Key := [(key1364, -1), (key1364, -1), (key1716, -1), (key1716, -1), (key1861, -1), (key1861, -1), (key1359, 2), (key1711, 2), (key1711, 2), (key1374, -1), (key1374, -1), (key1723, -1), (key1723, -1), (key1867, -1), (key1867, -1), (key1364, 2), (key1364, 2), (key1490, 2), (key1490, 2), (key1861, 2), (key1861, 2), (key1359, -1), (key1359, -1), (key1485, -1), (key1485, -1), (key1711, -1), (key1711, -1), (key1374, 2), (key1723, 2), (key1723, 2), (key1364, -1), (key1364, -1), (key1490, -1), (key1490, -1), (key1716, -1), (key1716, -1)]

theorem rawRowCheck14814 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form10 = rawRow14814 := by decide +kernel

def row14814 : Integer.Sparse Key := [(key1485, -2), (key1490, 2), (key1711, 2), (key1716, -4), (key1723, 2), (key1861, 2), (key1867, -2)]

theorem rowCheck14814 : row14814 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14814 := by decide +kernel

theorem rowEval14814 (x : Key → ℝ) : Integer.Sparse.eval row14814 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck14814, Integer.Sparse.eval_collectBalanced, rawRowCheck14814]

def rawRow14815 : Integer.Sparse Key := [(key1716, -1), (key1861, -1), (key1364, -1), (key1861, -1), (key1364, -1), (key1716, -1), (key1711, 2), (key1359, 2), (key1711, 2), (key1723, -1), (key1867, -1), (key1374, -1), (key1867, -1), (key1374, -1), (key1723, -1), (key1490, 2), (key1861, 2), (key1364, 2), (key1861, 2), (key1364, 2), (key1490, 2), (key1485, -1), (key1711, -1), (key1359, -1), (key1711, -1), (key1359, -1), (key1485, -1), (key1723, 2), (key1374, 2), (key1723, 2), (key1490, -1), (key1716, -1), (key1364, -1), (key1716, -1), (key1364, -1), (key1490, -1)]

theorem rawRowCheck14815 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form10 = rawRow14815 := by decide +kernel

def row14815 : Integer.Sparse Key := [(key1485, -2), (key1490, 2), (key1711, 2), (key1716, -4), (key1723, 2), (key1861, 2), (key1867, -2)]

theorem rowCheck14815 : row14815 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14815 := by decide +kernel

theorem rowEval14815 (x : Key → ℝ) : Integer.Sparse.eval row14815 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck14815, Integer.Sparse.eval_collectBalanced, rawRowCheck14815]

def rawRow14816 : Integer.Sparse Key := [(key1861, -1), (key1716, -1), (key1861, -1), (key1364, -1), (key1716, -1), (key1364, -1), (key1711, 2), (key1711, 2), (key1359, 2), (key1867, -1), (key1723, -1), (key1867, -1), (key1374, -1), (key1723, -1), (key1374, -1), (key1861, 2), (key1490, 2), (key1861, 2), (key1364, 2), (key1490, 2), (key1364, 2), (key1711, -1), (key1485, -1), (key1711, -1), (key1359, -1), (key1485, -1), (key1359, -1), (key1723, 2), (key1723, 2), (key1374, 2), (key1716, -1), (key1490, -1), (key1716, -1), (key1364, -1), (key1490, -1), (key1364, -1)]

theorem rawRowCheck14816 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form10 = rawRow14816 := by decide +kernel

def row14816 : Integer.Sparse Key := [(key1485, -2), (key1490, 2), (key1711, 2), (key1716, -4), (key1723, 2), (key1861, 2), (key1867, -2)]

theorem rowCheck14816 : row14816 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14816 := by decide +kernel

theorem rowEval14816 (x : Key → ℝ) : Integer.Sparse.eval row14816 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form10) x := by
  rw [rowCheck14816, Integer.Sparse.eval_collectBalanced, rawRowCheck14816]

def rawRow14817 : Integer.Sparse Key := [(key1723, -1), (key1723, -1), (key1723, -1), (key1723, -1), (key1723, -1), (key1723, -1), (key1867, 2), (key1867, 2), (key1867, 2), (key1490, -1), (key1490, -1), (key1490, -1), (key1490, -1), (key1490, -1), (key1490, -1), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1861, -1), (key1861, -1), (key1861, -1), (key1861, -1), (key1861, -1), (key1861, -1), (key1485, 2), (key1485, 2), (key1485, 2), (key1711, -1), (key1711, -1), (key1711, -1), (key1711, -1), (key1711, -1), (key1711, -1)]

theorem rawRowCheck14817 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form10 = rawRow14817 := by decide +kernel

def row14817 : Integer.Sparse Key := [(key1485, 6), (key1490, -6), (key1711, -6), (key1716, 12), (key1723, -6), (key1861, -6), (key1867, 6)]

theorem rowCheck14817 : row14817 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14817 := by decide +kernel

theorem rowEval14817 (x : Key → ℝ) : Integer.Sparse.eval row14817 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck14817, Integer.Sparse.eval_collectBalanced, rawRowCheck14817]

def rawRow14818 : Integer.Sparse Key := [(key1374, -1), (key1374, -1), (key1723, -1), (key1723, -1), (key1867, -1), (key1867, -1), (key1374, 2), (key1723, 2), (key1723, 2), (key1364, -1), (key1364, -1), (key1716, -1), (key1716, -1), (key1861, -1), (key1861, -1), (key1364, 2), (key1364, 2), (key1490, 2), (key1490, 2), (key1861, 2), (key1861, 2), (key1364, -1), (key1364, -1), (key1490, -1), (key1490, -1), (key1716, -1), (key1716, -1), (key1359, 2), (key1711, 2), (key1711, 2), (key1359, -1), (key1359, -1), (key1485, -1), (key1485, -1), (key1711, -1), (key1711, -1)]

theorem rawRowCheck14818 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form10 = rawRow14818 := by decide +kernel

def row14818 : Integer.Sparse Key := [(key1485, -2), (key1490, 2), (key1711, 2), (key1716, -4), (key1723, 2), (key1861, 2), (key1867, -2)]

theorem rowCheck14818 : row14818 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14818 := by decide +kernel

theorem rowEval14818 (x : Key → ℝ) : Integer.Sparse.eval row14818 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck14818, Integer.Sparse.eval_collectBalanced, rawRowCheck14818]

def rawRow14819 : Integer.Sparse Key := [(key1723, -1), (key1867, -1), (key1374, -1), (key1867, -1), (key1374, -1), (key1723, -1), (key1723, 2), (key1374, 2), (key1723, 2), (key1716, -1), (key1861, -1), (key1364, -1), (key1861, -1), (key1364, -1), (key1716, -1), (key1490, 2), (key1861, 2), (key1364, 2), (key1861, 2), (key1364, 2), (key1490, 2), (key1490, -1), (key1716, -1), (key1364, -1), (key1716, -1), (key1364, -1), (key1490, -1), (key1711, 2), (key1359, 2), (key1711, 2), (key1485, -1), (key1711, -1), (key1359, -1), (key1711, -1), (key1359, -1), (key1485, -1)]

theorem rawRowCheck14819 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form10 = rawRow14819 := by decide +kernel

def row14819 : Integer.Sparse Key := [(key1485, -2), (key1490, 2), (key1711, 2), (key1716, -4), (key1723, 2), (key1861, 2), (key1867, -2)]

theorem rowCheck14819 : row14819 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14819 := by decide +kernel

theorem rowEval14819 (x : Key → ℝ) : Integer.Sparse.eval row14819 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck14819, Integer.Sparse.eval_collectBalanced, rawRowCheck14819]

def rawRow14820 : Integer.Sparse Key := [(key1867, -1), (key1723, -1), (key1867, -1), (key1374, -1), (key1723, -1), (key1374, -1), (key1723, 2), (key1723, 2), (key1374, 2), (key1861, -1), (key1716, -1), (key1861, -1), (key1364, -1), (key1716, -1), (key1364, -1), (key1861, 2), (key1490, 2), (key1861, 2), (key1364, 2), (key1490, 2), (key1364, 2), (key1716, -1), (key1490, -1), (key1716, -1), (key1364, -1), (key1490, -1), (key1364, -1), (key1711, 2), (key1711, 2), (key1359, 2), (key1711, -1), (key1485, -1), (key1711, -1), (key1359, -1), (key1485, -1), (key1359, -1)]

theorem rawRowCheck14820 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form10 = rawRow14820 := by decide +kernel

def row14820 : Integer.Sparse Key := [(key1485, -2), (key1490, 2), (key1711, 2), (key1716, -4), (key1723, 2), (key1861, 2), (key1867, -2)]

theorem rowCheck14820 : row14820 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14820 := by decide +kernel

theorem rowEval14820 (x : Key → ℝ) : Integer.Sparse.eval row14820 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form10) x := by
  rw [rowCheck14820, Integer.Sparse.eval_collectBalanced, rawRowCheck14820]

def rawRow14821 : Integer.Sparse Key := [(key288, -2), (key289, -2), (key289, -2), (key289, 6), (key513, -2), (key515, -2), (key515, -2), (key513, 2), (key515, 2), (key513, 2), (key547, 2), (key515, 2), (key547, 2), (key515, -2), (key515, -2), (key547, -2), (key670, 6), (key670, -2), (key670, -2), (key680, -2)]

theorem rawRowCheck14821 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form11 = rawRow14821 := by decide +kernel

def row14821 : Integer.Sparse Key := [(key288, -2), (key289, 2), (key513, 2), (key515, -4), (key547, 2), (key670, 2), (key680, -2)]

theorem rowCheck14821 : row14821 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14821 := by decide +kernel

theorem rowEval14821 (x : Key → ℝ) : Integer.Sparse.eval row14821 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form11) x := by
  rw [rowCheck14821, Integer.Sparse.eval_collectBalanced, rawRowCheck14821]

def rawRow14822 : Integer.Sparse Key := [(key289, -2), (key288, -2), (key289, -2), (key289, 6), (key515, -2), (key513, -2), (key515, -2), (key515, 2), (key513, 2), (key547, 2), (key513, 2), (key547, 2), (key515, 2), (key515, -2), (key547, -2), (key515, -2), (key670, 6), (key670, -2), (key680, -2), (key670, -2)]

theorem rawRowCheck14822 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form11 = rawRow14822 := by decide +kernel

def row14822 : Integer.Sparse Key := [(key288, -2), (key289, 2), (key513, 2), (key515, -4), (key547, 2), (key670, 2), (key680, -2)]

theorem rowCheck14822 : row14822 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14822 := by decide +kernel

theorem rowEval14822 (x : Key → ℝ) : Integer.Sparse.eval row14822 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck14822, Integer.Sparse.eval_collectBalanced, rawRowCheck14822]

def rawRow14823 : Integer.Sparse Key := [(key289, -2), (key289, -2), (key288, -2), (key289, 6), (key515, -2), (key515, -2), (key513, -2), (key547, 2), (key547, 2), (key515, 2), (key515, 2), (key513, 2), (key513, 2), (key547, -2), (key515, -2), (key515, -2), (key670, 6), (key680, -2), (key670, -2), (key670, -2)]

theorem rawRowCheck14823 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form11 = rawRow14823 := by decide +kernel

def row14823 : Integer.Sparse Key := [(key288, -2), (key289, 2), (key513, 2), (key515, -4), (key547, 2), (key670, 2), (key680, -2)]

theorem rowCheck14823 : row14823 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14823 := by decide +kernel

theorem rowEval14823 (x : Key → ℝ) : Integer.Sparse.eval row14823 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck14823, Integer.Sparse.eval_collectBalanced, rawRowCheck14823]

def rawRow14824 : Integer.Sparse Key := [(key289, -2), (key289, -2), (key289, -2), (key288, 6), (key547, -2), (key547, -2), (key547, -2), (key515, 2), (key515, 2), (key515, 2), (key515, 2), (key515, 2), (key515, 2), (key513, -2), (key513, -2), (key513, -2), (key680, 6), (key670, -2), (key670, -2), (key670, -2)]

theorem rawRowCheck14824 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form11 = rawRow14824 := by decide +kernel

def row14824 : Integer.Sparse Key := [(key288, 6), (key289, -6), (key513, -6), (key515, 12), (key547, -6), (key670, -6), (key680, 6)]

theorem rowCheck14824 : row14824 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14824 := by decide +kernel

theorem rowEval14824 (x : Key → ℝ) : Integer.Sparse.eval row14824 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck14824, Integer.Sparse.eval_collectBalanced, rawRowCheck14824]

def rawRow14825 : Integer.Sparse Key := [(key513, -2), (key515, -2), (key515, -2), (key547, 6), (key288, -2), (key289, -2), (key289, -2), (key513, 2), (key515, 2), (key513, 2), (key547, 2), (key515, 2), (key547, 2), (key670, -2), (key670, -2), (key680, -2), (key289, 6), (key515, -2), (key515, -2), (key547, -2)]

theorem rawRowCheck14825 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form11 = rawRow14825 := by decide +kernel

def row14825 : Integer.Sparse Key := [(key288, -2), (key289, 2), (key513, 2), (key515, -4), (key547, 8), (key670, -4), (key680, -2)]

theorem rowCheck14825 : row14825 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14825 := by decide +kernel

theorem rowEval14825 (x : Key → ℝ) : Integer.Sparse.eval row14825 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form11) x := by
  rw [rowCheck14825, Integer.Sparse.eval_collectBalanced, rawRowCheck14825]

def rawRow14826 : Integer.Sparse Key := [(key515, -2), (key513, -2), (key515, -2), (key547, 6), (key289, -2), (key288, -2), (key289, -2), (key515, 2), (key513, 2), (key547, 2), (key513, 2), (key547, 2), (key515, 2), (key670, -2), (key680, -2), (key670, -2), (key289, 6), (key515, -2), (key547, -2), (key515, -2)]

theorem rawRowCheck14826 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form11 = rawRow14826 := by decide +kernel

def row14826 : Integer.Sparse Key := [(key288, -2), (key289, 2), (key513, 2), (key515, -4), (key547, 8), (key670, -4), (key680, -2)]

theorem rowCheck14826 : row14826 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14826 := by decide +kernel

theorem rowEval14826 (x : Key → ℝ) : Integer.Sparse.eval row14826 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck14826, Integer.Sparse.eval_collectBalanced, rawRowCheck14826]

def rawRow14827 : Integer.Sparse Key := [(key515, -2), (key515, -2), (key513, -2), (key547, 6), (key289, -2), (key289, -2), (key288, -2), (key547, 2), (key547, 2), (key515, 2), (key515, 2), (key513, 2), (key513, 2), (key680, -2), (key670, -2), (key670, -2), (key289, 6), (key547, -2), (key515, -2), (key515, -2)]

theorem rawRowCheck14827 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form11 = rawRow14827 := by decide +kernel

def row14827 : Integer.Sparse Key := [(key288, -2), (key289, 2), (key513, 2), (key515, -4), (key547, 8), (key670, -4), (key680, -2)]

theorem rowCheck14827 : row14827 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14827 := by decide +kernel

theorem rowEval14827 (x : Key → ℝ) : Integer.Sparse.eval row14827 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck14827, Integer.Sparse.eval_collectBalanced, rawRowCheck14827]

def rawRow14828 : Integer.Sparse Key := [(key513, -2), (key515, -2), (key547, -2), (key515, 6), (key513, -2), (key515, -2), (key547, -2), (key288, 2), (key289, 2), (key513, 2), (key547, 2), (key670, 2), (key680, 2), (key289, -2), (key515, -2), (key547, -2), (key515, 6), (key289, -2), (key515, -2), (key547, -2)]

theorem rawRowCheck14828 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form11 = rawRow14828 := by decide +kernel

def row14828 : Integer.Sparse Key := [(key288, 2), (key289, -2), (key513, -2), (key515, 4), (key547, -6), (key670, 2), (key680, 2)]

theorem rowCheck14828 : row14828 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14828 := by decide +kernel

theorem rowEval14828 (x : Key → ℝ) : Integer.Sparse.eval row14828 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form11) x := by
  rw [rowCheck14828, Integer.Sparse.eval_collectBalanced, rawRowCheck14828]

def rawRow14829 : Integer.Sparse Key := [(key515, -2), (key513, -2), (key547, -2), (key515, 6), (key515, -2), (key513, -2), (key547, -2), (key289, 2), (key288, 2), (key547, 2), (key513, 2), (key680, 2), (key670, 2), (key289, -2), (key547, -2), (key515, -2), (key515, 6), (key289, -2), (key547, -2), (key515, -2)]

theorem rawRowCheck14829 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form11 = rawRow14829 := by decide +kernel

def row14829 : Integer.Sparse Key := [(key288, 2), (key289, -2), (key513, -2), (key515, 4), (key547, -6), (key670, 2), (key680, 2)]

theorem rowCheck14829 : row14829 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14829 := by decide +kernel

theorem rowEval14829 (x : Key → ℝ) : Integer.Sparse.eval row14829 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck14829, Integer.Sparse.eval_collectBalanced, rawRowCheck14829]

def rawRow14830 : Integer.Sparse Key := [(key513, -2), (key547, -2), (key515, -2), (key515, 6), (key513, -2), (key547, -2), (key515, -2), (key513, 2), (key547, 2), (key288, 2), (key680, 2), (key289, 2), (key547, 2), (key515, -2), (key289, -2), (key547, -2), (key515, 6), (key515, -2), (key289, -2), (key547, -2)]

theorem rawRowCheck14830 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form11 = rawRow14830 := by decide +kernel

def row14830 : Integer.Sparse Key := [(key288, 2), (key289, -2), (key513, -2), (key515, 4), (key547, -4), (key680, 2)]

theorem rowCheck14830 : row14830 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14830 := by decide +kernel

theorem rowEval14830 (x : Key → ℝ) : Integer.Sparse.eval row14830 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form11) x := by
  rw [rowCheck14830, Integer.Sparse.eval_collectBalanced, rawRowCheck14830]

def rawRow14831 : Integer.Sparse Key := [(key547, -2), (key513, -2), (key515, -2), (key515, 6), (key547, -2), (key513, -2), (key515, -2), (key547, 2), (key513, 2), (key680, 2), (key288, 2), (key547, 2), (key289, 2), (key515, -2), (key547, -2), (key289, -2), (key515, 6), (key515, -2), (key547, -2), (key289, -2)]

theorem rawRowCheck14831 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form11 = rawRow14831 := by decide +kernel

def row14831 : Integer.Sparse Key := [(key288, 2), (key289, -2), (key513, -2), (key515, 4), (key547, -4), (key680, 2)]

theorem rowCheck14831 : row14831 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14831 := by decide +kernel

theorem rowEval14831 (x : Key → ℝ) : Integer.Sparse.eval row14831 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form11) x := by
  rw [rowCheck14831, Integer.Sparse.eval_collectBalanced, rawRowCheck14831]

def rawRow14832 : Integer.Sparse Key := [(key515, -2), (key547, -2), (key513, -2), (key515, 6), (key515, -2), (key547, -2), (key513, -2), (key670, 2), (key680, 2), (key289, 2), (key547, 2), (key288, 2), (key513, 2), (key547, -2), (key289, -2), (key515, -2), (key515, 6), (key547, -2), (key289, -2), (key515, -2)]

theorem rawRowCheck14832 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form11 = rawRow14832 := by decide +kernel

def row14832 : Integer.Sparse Key := [(key288, 2), (key289, -2), (key513, -2), (key515, 4), (key547, -6), (key670, 2), (key680, 2)]

theorem rowCheck14832 : row14832 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14832 := by decide +kernel

theorem rowEval14832 (x : Key → ℝ) : Integer.Sparse.eval row14832 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck14832, Integer.Sparse.eval_collectBalanced, rawRowCheck14832]

def rawRow14833 : Integer.Sparse Key := [(key547, -2), (key515, -2), (key513, -2), (key515, 6), (key547, -2), (key515, -2), (key513, -2), (key680, 2), (key670, 2), (key547, 2), (key289, 2), (key513, 2), (key288, 2), (key547, -2), (key515, -2), (key289, -2), (key515, 6), (key547, -2), (key515, -2), (key289, -2)]

theorem rawRowCheck14833 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form11 = rawRow14833 := by decide +kernel

def row14833 : Integer.Sparse Key := [(key288, 2), (key289, -2), (key513, -2), (key515, 4), (key547, -6), (key670, 2), (key680, 2)]

theorem rowCheck14833 : row14833 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14833 := by decide +kernel

theorem rowEval14833 (x : Key → ℝ) : Integer.Sparse.eval row14833 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form11) x := by
  rw [rowCheck14833, Integer.Sparse.eval_collectBalanced, rawRowCheck14833]

def rawRow14834 : Integer.Sparse Key := [(key515, -2), (key515, -2), (key547, -2), (key513, 6), (key670, -2), (key670, -2), (key680, -2), (key289, 2), (key289, 2), (key515, 2), (key515, 2), (key547, 2), (key547, 2), (key288, -2), (key513, -2), (key513, -2), (key547, 6), (key289, -2), (key515, -2), (key515, -2)]

theorem rawRowCheck14834 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form11 = rawRow14834 := by decide +kernel

def row14834 : Integer.Sparse Key := [(key288, -2), (key289, 2), (key513, 2), (key515, -4), (key547, 8), (key670, -4), (key680, -2)]

theorem rowCheck14834 : row14834 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14834 := by decide +kernel

theorem rowEval14834 (x : Key → ℝ) : Integer.Sparse.eval row14834 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck14834, Integer.Sparse.eval_collectBalanced, rawRowCheck14834]

def rawRow14835 : Integer.Sparse Key := [(key515, -2), (key547, -2), (key515, -2), (key513, 6), (key670, -2), (key680, -2), (key670, -2), (key515, 2), (key547, 2), (key289, 2), (key547, 2), (key289, 2), (key515, 2), (key513, -2), (key288, -2), (key513, -2), (key547, 6), (key515, -2), (key289, -2), (key515, -2)]

theorem rawRowCheck14835 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form11 = rawRow14835 := by decide +kernel

def row14835 : Integer.Sparse Key := [(key288, -2), (key289, 2), (key513, 2), (key515, -4), (key547, 8), (key670, -4), (key680, -2)]

theorem rowCheck14835 : row14835 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14835 := by decide +kernel

theorem rowEval14835 (x : Key → ℝ) : Integer.Sparse.eval row14835 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck14835, Integer.Sparse.eval_collectBalanced, rawRowCheck14835]

def rawRow14836 : Integer.Sparse Key := [(key547, -2), (key515, -2), (key515, -2), (key513, 6), (key680, -2), (key670, -2), (key670, -2), (key547, 2), (key515, 2), (key547, 2), (key289, 2), (key515, 2), (key289, 2), (key513, -2), (key513, -2), (key288, -2), (key547, 6), (key515, -2), (key515, -2), (key289, -2)]

theorem rawRowCheck14836 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form11 = rawRow14836 := by decide +kernel

def row14836 : Integer.Sparse Key := [(key288, -2), (key289, 2), (key513, 2), (key515, -4), (key547, 8), (key670, -4), (key680, -2)]

theorem rowCheck14836 : row14836 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14836 := by decide +kernel

theorem rowEval14836 (x : Key → ℝ) : Integer.Sparse.eval row14836 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form11) x := by
  rw [rowCheck14836, Integer.Sparse.eval_collectBalanced, rawRowCheck14836]

def rawRow14837 : Integer.Sparse Key := [(key670, -2), (key670, -2), (key670, -2), (key680, 6), (key289, -2), (key289, -2), (key289, -2), (key515, 2), (key515, 2), (key515, 2), (key515, 2), (key515, 2), (key515, 2), (key547, -2), (key547, -2), (key547, -2), (key288, 6), (key513, -2), (key513, -2), (key513, -2)]

theorem rawRowCheck14837 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form11 = rawRow14837 := by decide +kernel

def row14837 : Integer.Sparse Key := [(key288, 6), (key289, -6), (key513, -6), (key515, 12), (key547, -6), (key670, -6), (key680, 6)]

theorem rowCheck14837 : row14837 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14837 := by decide +kernel

theorem rowEval14837 (x : Key → ℝ) : Integer.Sparse.eval row14837 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck14837, Integer.Sparse.eval_collectBalanced, rawRowCheck14837]

def rawRow14838 : Integer.Sparse Key := [(key670, -2), (key670, -2), (key680, -2), (key670, 6), (key515, -2), (key515, -2), (key547, -2), (key289, 2), (key289, 2), (key515, 2), (key515, 2), (key547, 2), (key547, 2), (key289, -2), (key515, -2), (key515, -2), (key513, 6), (key288, -2), (key513, -2), (key513, -2)]

theorem rawRowCheck14838 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form11 = rawRow14838 := by decide +kernel

def row14838 : Integer.Sparse Key := [(key288, -2), (key289, 2), (key513, 2), (key515, -4), (key547, 2), (key670, 2), (key680, -2)]

theorem rowCheck14838 : row14838 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14838 := by decide +kernel

theorem rowEval14838 (x : Key → ℝ) : Integer.Sparse.eval row14838 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck14838, Integer.Sparse.eval_collectBalanced, rawRowCheck14838]

def rawRow14839 : Integer.Sparse Key := [(key670, -2), (key680, -2), (key670, -2), (key670, 6), (key515, -2), (key547, -2), (key515, -2), (key515, 2), (key547, 2), (key289, 2), (key547, 2), (key289, 2), (key515, 2), (key515, -2), (key289, -2), (key515, -2), (key513, 6), (key513, -2), (key288, -2), (key513, -2)]

theorem rawRowCheck14839 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form11 = rawRow14839 := by decide +kernel

def row14839 : Integer.Sparse Key := [(key288, -2), (key289, 2), (key513, 2), (key515, -4), (key547, 2), (key670, 2), (key680, -2)]

theorem rowCheck14839 : row14839 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14839 := by decide +kernel

theorem rowEval14839 (x : Key → ℝ) : Integer.Sparse.eval row14839 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck14839, Integer.Sparse.eval_collectBalanced, rawRowCheck14839]

def rawRow14840 : Integer.Sparse Key := [(key680, -2), (key670, -2), (key670, -2), (key670, 6), (key547, -2), (key515, -2), (key515, -2), (key547, 2), (key515, 2), (key547, 2), (key289, 2), (key515, 2), (key289, 2), (key515, -2), (key515, -2), (key289, -2), (key513, 6), (key513, -2), (key513, -2), (key288, -2)]

theorem rawRowCheck14840 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form11 = rawRow14840 := by decide +kernel

def row14840 : Integer.Sparse Key := [(key288, -2), (key289, 2), (key513, 2), (key515, -4), (key547, 2), (key670, 2), (key680, -2)]

theorem rowCheck14840 : row14840 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14840 := by decide +kernel

theorem rowEval14840 (x : Key → ℝ) : Integer.Sparse.eval row14840 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form11) x := by
  rw [rowCheck14840, Integer.Sparse.eval_collectBalanced, rawRowCheck14840]

def rawRow14841 : Integer.Sparse Key := [(key2457, 4), (key2521, 4), (key2521, 4), (key2460, -2), (key2460, -2), (key2521, -2), (key2521, -2), (key2525, -2), (key2525, -2), (key2532, -2), (key2532, -2), (key2562, -2), (key2562, -2), (key2564, -2), (key2564, -2), (key2533, 4), (key2564, 4), (key2564, 4)]

theorem rawRowCheck14841 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form0 = rawRow14841 := by decide +kernel

def row14841 : Integer.Sparse Key := [(key2457, 4), (key2460, -4), (key2521, 4), (key2525, -4), (key2532, -4), (key2533, 4), (key2562, -4), (key2564, 4)]

theorem rowCheck14841 : row14841 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14841 := by decide +kernel

theorem rowEval14841 (x : Key → ℝ) : Integer.Sparse.eval row14841 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14841, Integer.Sparse.eval_collectBalanced, rawRowCheck14841]

def rawRow14842 : Integer.Sparse Key := [(key2521, 4), (key2457, 4), (key2521, 4), (key2521, -2), (key2525, -2), (key2460, -2), (key2525, -2), (key2460, -2), (key2521, -2), (key2562, -2), (key2564, -2), (key2532, -2), (key2564, -2), (key2532, -2), (key2562, -2), (key2564, 4), (key2533, 4), (key2564, 4)]

theorem rawRowCheck14842 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form0 = rawRow14842 := by decide +kernel

def row14842 : Integer.Sparse Key := [(key2457, 4), (key2460, -4), (key2521, 4), (key2525, -4), (key2532, -4), (key2533, 4), (key2562, -4), (key2564, 4)]

theorem rowCheck14842 : row14842 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14842 := by decide +kernel

theorem rowEval14842 (x : Key → ℝ) : Integer.Sparse.eval row14842 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14842, Integer.Sparse.eval_collectBalanced, rawRowCheck14842]

def rawRow14843 : Integer.Sparse Key := [(key2521, 4), (key2521, 4), (key2457, 4), (key2525, -2), (key2521, -2), (key2525, -2), (key2460, -2), (key2521, -2), (key2460, -2), (key2564, -2), (key2562, -2), (key2564, -2), (key2532, -2), (key2562, -2), (key2532, -2), (key2564, 4), (key2564, 4), (key2533, 4)]

theorem rawRowCheck14843 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form0 = rawRow14843 := by decide +kernel

def row14843 : Integer.Sparse Key := [(key2457, 4), (key2460, -4), (key2521, 4), (key2525, -4), (key2532, -4), (key2533, 4), (key2562, -4), (key2564, 4)]

theorem rowCheck14843 : row14843 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14843 := by decide +kernel

theorem rowEval14843 (x : Key → ℝ) : Integer.Sparse.eval row14843 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14843, Integer.Sparse.eval_collectBalanced, rawRowCheck14843]

def rawRow14844 : Integer.Sparse Key := [(key2460, 4), (key2460, 4), (key2525, 4), (key2457, -2), (key2460, -2), (key2457, -2), (key2521, -2), (key2460, -2), (key2521, -2), (key2532, -2), (key2533, -2), (key2532, -2), (key2564, -2), (key2533, -2), (key2564, -2), (key2532, 4), (key2532, 4), (key2562, 4)]

theorem rawRowCheck14844 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form0 = rawRow14844 := by decide +kernel

def row14844 : Integer.Sparse Key := [(key2457, -4), (key2460, 4), (key2521, -4), (key2525, 4), (key2532, 4), (key2533, -4), (key2562, 4), (key2564, -4)]

theorem rowCheck14844 : row14844 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14844 := by decide +kernel

theorem rowEval14844 (x : Key → ℝ) : Integer.Sparse.eval row14844 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14844, Integer.Sparse.eval_collectBalanced, rawRowCheck14844]

def rawRow14845 : Integer.Sparse Key := [(key2460, 4), (key2525, 4), (key2460, 4), (key2460, -2), (key2457, -2), (key2521, -2), (key2457, -2), (key2521, -2), (key2460, -2), (key2533, -2), (key2532, -2), (key2564, -2), (key2532, -2), (key2564, -2), (key2533, -2), (key2532, 4), (key2562, 4), (key2532, 4)]

theorem rawRowCheck14845 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form0 = rawRow14845 := by decide +kernel

def row14845 : Integer.Sparse Key := [(key2457, -4), (key2460, 4), (key2521, -4), (key2525, 4), (key2532, 4), (key2533, -4), (key2562, 4), (key2564, -4)]

theorem rowCheck14845 : row14845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14845 := by decide +kernel

theorem rowEval14845 (x : Key → ℝ) : Integer.Sparse.eval row14845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14845, Integer.Sparse.eval_collectBalanced, rawRowCheck14845]

def rawRow14846 : Integer.Sparse Key := [(key2525, 4), (key2460, 4), (key2460, 4), (key2521, -2), (key2521, -2), (key2460, -2), (key2460, -2), (key2457, -2), (key2457, -2), (key2564, -2), (key2564, -2), (key2533, -2), (key2533, -2), (key2532, -2), (key2532, -2), (key2562, 4), (key2532, 4), (key2532, 4)]

theorem rawRowCheck14846 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form0 = rawRow14846 := by decide +kernel

def row14846 : Integer.Sparse Key := [(key2457, -4), (key2460, 4), (key2521, -4), (key2525, 4), (key2532, 4), (key2533, -4), (key2562, 4), (key2564, -4)]

theorem rowCheck14846 : row14846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14846 := by decide +kernel

theorem rowEval14846 (x : Key → ℝ) : Integer.Sparse.eval row14846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14846, Integer.Sparse.eval_collectBalanced, rawRowCheck14846]

def rawRow14847 : Integer.Sparse Key := [(key2457, 4), (key2521, 4), (key2521, 4), (key2532, -2), (key2532, -2), (key2562, -2), (key2562, -2), (key2564, -2), (key2564, -2), (key2460, -2), (key2460, -2), (key2521, -2), (key2521, -2), (key2525, -2), (key2525, -2), (key2533, 4), (key2564, 4), (key2564, 4)]

theorem rawRowCheck14847 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form0 = rawRow14847 := by decide +kernel

def row14847 : Integer.Sparse Key := [(key2457, 4), (key2460, -4), (key2521, 4), (key2525, -4), (key2532, -4), (key2533, 4), (key2562, -4), (key2564, 4)]

theorem rowCheck14847 : row14847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14847 := by decide +kernel

theorem rowEval14847 (x : Key → ℝ) : Integer.Sparse.eval row14847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14847, Integer.Sparse.eval_collectBalanced, rawRowCheck14847]

end MUB6.Certificate.GramRows

end OAI
