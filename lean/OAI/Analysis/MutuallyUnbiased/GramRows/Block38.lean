import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block24

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow1792 : Integer.Sparse Key := [(key2370, -2), (key2376, -2), (key2376, -2), (key2370, 1), (key2376, 1), (key2370, 1), (key2388, 1), (key2376, 1), (key2388, 1), (key2398, 2), (key2404, 2), (key2404, 2), (key2398, -1), (key2404, -1), (key2398, -1), (key2435, -1), (key2404, -1), (key2435, -1), (key2464, -1), (key2470, -1), (key2464, -1), (key2478, -1), (key2470, -1), (key2478, -1), (key2464, 1), (key2470, 1), (key2464, 1), (key2501, 1), (key2470, 1), (key2501, 1)]

theorem rawRowCheck1792 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form2 = rawRow1792 := by decide +kernel

def row1792 : Integer.Sparse Key := [(key2376, -2), (key2388, 2), (key2404, 2), (key2435, -2), (key2478, -2), (key2501, 2)]

theorem rowCheck1792 : row1792 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1792 := by decide +kernel

theorem rowEval1792 (x : Key → ℝ) : Integer.Sparse.eval row1792 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck1792, Integer.Sparse.eval_collectBalanced, rawRowCheck1792]

def rawRow1793 : Integer.Sparse Key := [(key2376, -2), (key2370, -2), (key2376, -2), (key2376, 1), (key2370, 1), (key2388, 1), (key2370, 1), (key2388, 1), (key2376, 1), (key2404, 2), (key2398, 2), (key2404, 2), (key2404, -1), (key2398, -1), (key2435, -1), (key2398, -1), (key2435, -1), (key2404, -1), (key2470, -1), (key2464, -1), (key2478, -1), (key2464, -1), (key2478, -1), (key2470, -1), (key2470, 1), (key2464, 1), (key2501, 1), (key2464, 1), (key2501, 1), (key2470, 1)]

theorem rawRowCheck1793 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form2 = rawRow1793 := by decide +kernel

def row1793 : Integer.Sparse Key := [(key2376, -2), (key2388, 2), (key2404, 2), (key2435, -2), (key2478, -2), (key2501, 2)]

theorem rowCheck1793 : row1793 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1793 := by decide +kernel

theorem rowEval1793 (x : Key → ℝ) : Integer.Sparse.eval row1793 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1793, Integer.Sparse.eval_collectBalanced, rawRowCheck1793]

def rawRow1794 : Integer.Sparse Key := [(key2376, -2), (key2376, -2), (key2370, -2), (key2388, 1), (key2388, 1), (key2376, 1), (key2376, 1), (key2370, 1), (key2370, 1), (key2404, 2), (key2404, 2), (key2398, 2), (key2435, -1), (key2435, -1), (key2404, -1), (key2404, -1), (key2398, -1), (key2398, -1), (key2478, -1), (key2478, -1), (key2470, -1), (key2470, -1), (key2464, -1), (key2464, -1), (key2501, 1), (key2501, 1), (key2470, 1), (key2470, 1), (key2464, 1), (key2464, 1)]

theorem rawRowCheck1794 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form2 = rawRow1794 := by decide +kernel

def row1794 : Integer.Sparse Key := [(key2376, -2), (key2388, 2), (key2404, 2), (key2435, -2), (key2478, -2), (key2501, 2)]

theorem rowCheck1794 : row1794 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1794 := by decide +kernel

theorem rowEval1794 (x : Key → ℝ) : Integer.Sparse.eval row1794 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1794, Integer.Sparse.eval_collectBalanced, rawRowCheck1794]

def rawRow1795 : Integer.Sparse Key := [(key2388, -2), (key2388, -2), (key2388, -2), (key2376, 1), (key2376, 1), (key2376, 1), (key2376, 1), (key2376, 1), (key2376, 1), (key2435, 2), (key2435, 2), (key2435, 2), (key2404, -1), (key2404, -1), (key2404, -1), (key2404, -1), (key2404, -1), (key2404, -1), (key2501, -1), (key2501, -1), (key2501, -1), (key2501, -1), (key2501, -1), (key2501, -1), (key2478, 1), (key2478, 1), (key2478, 1), (key2478, 1), (key2478, 1), (key2478, 1)]

theorem rawRowCheck1795 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form2 = rawRow1795 := by decide +kernel

def row1795 : Integer.Sparse Key := [(key2376, 6), (key2388, -6), (key2404, -6), (key2435, 6), (key2478, 6), (key2501, -6)]

theorem rowCheck1795 : row1795 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1795 := by decide +kernel

theorem rowEval1795 (x : Key → ℝ) : Integer.Sparse.eval row1795 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1795, Integer.Sparse.eval_collectBalanced, rawRowCheck1795]

def rawRow1796 : Integer.Sparse Key := [(key2762, -2), (key2768, -2), (key2768, -2), (key2839, 1), (key2845, 1), (key2839, 1), (key2916, 1), (key2845, 1), (key2916, 1), (key2583, 2), (key2589, 2), (key2589, 2), (key2839, -1), (key2845, -1), (key2839, -1), (key3019, -1), (key2845, -1), (key3019, -1), (key2370, -1), (key2376, -1), (key2370, -1), (key2388, -1), (key2376, -1), (key2388, -1), (key2398, 1), (key2404, 1), (key2398, 1), (key2435, 1), (key2404, 1), (key2435, 1)]

theorem rawRowCheck1796 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form2 = rawRow1796 := by decide +kernel

def row1796 : Integer.Sparse Key := [(key2370, -2), (key2376, -2), (key2388, -2), (key2398, 2), (key2404, 2), (key2435, 2), (key2583, 2), (key2589, 4), (key2762, -2), (key2768, -4), (key2916, 2), (key3019, -2)]

theorem rowCheck1796 : row1796 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1796 := by decide +kernel

theorem rowEval1796 (x : Key → ℝ) : Integer.Sparse.eval row1796 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck1796, Integer.Sparse.eval_collectBalanced, rawRowCheck1796]

def rawRow1797 : Integer.Sparse Key := [(key2768, -2), (key2762, -2), (key2768, -2), (key2845, 1), (key2839, 1), (key2916, 1), (key2839, 1), (key2916, 1), (key2845, 1), (key2589, 2), (key2583, 2), (key2589, 2), (key2845, -1), (key2839, -1), (key3019, -1), (key2839, -1), (key3019, -1), (key2845, -1), (key2376, -1), (key2370, -1), (key2388, -1), (key2370, -1), (key2388, -1), (key2376, -1), (key2404, 1), (key2398, 1), (key2435, 1), (key2398, 1), (key2435, 1), (key2404, 1)]

theorem rawRowCheck1797 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form2 = rawRow1797 := by decide +kernel

def row1797 : Integer.Sparse Key := [(key2370, -2), (key2376, -2), (key2388, -2), (key2398, 2), (key2404, 2), (key2435, 2), (key2583, 2), (key2589, 4), (key2762, -2), (key2768, -4), (key2916, 2), (key3019, -2)]

theorem rowCheck1797 : row1797 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1797 := by decide +kernel

theorem rowEval1797 (x : Key → ℝ) : Integer.Sparse.eval row1797 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1797, Integer.Sparse.eval_collectBalanced, rawRowCheck1797]

def rawRow1798 : Integer.Sparse Key := [(key2768, -2), (key2768, -2), (key2762, -2), (key2916, 1), (key2916, 1), (key2845, 1), (key2845, 1), (key2839, 1), (key2839, 1), (key2589, 2), (key2589, 2), (key2583, 2), (key3019, -1), (key3019, -1), (key2845, -1), (key2845, -1), (key2839, -1), (key2839, -1), (key2388, -1), (key2388, -1), (key2376, -1), (key2376, -1), (key2370, -1), (key2370, -1), (key2435, 1), (key2435, 1), (key2404, 1), (key2404, 1), (key2398, 1), (key2398, 1)]

theorem rawRowCheck1798 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form2 = rawRow1798 := by decide +kernel

def row1798 : Integer.Sparse Key := [(key2370, -2), (key2376, -2), (key2388, -2), (key2398, 2), (key2404, 2), (key2435, 2), (key2583, 2), (key2589, 4), (key2762, -2), (key2768, -4), (key2916, 2), (key3019, -2)]

theorem rowCheck1798 : row1798 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1798 := by decide +kernel

theorem rowEval1798 (x : Key → ℝ) : Integer.Sparse.eval row1798 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1798, Integer.Sparse.eval_collectBalanced, rawRowCheck1798]

def rawRow1799 : Integer.Sparse Key := [(key2916, -2), (key2916, -2), (key2925, -2), (key2768, 1), (key2768, 1), (key2845, 1), (key2845, 1), (key2876, 1), (key2876, 1), (key3019, 2), (key3019, 2), (key3028, 2), (key2589, -1), (key2589, -1), (key2845, -1), (key2845, -1), (key2876, -1), (key2876, -1), (key3005, -1), (key3005, -1), (key3019, -1), (key3019, -1), (key3028, -1), (key3028, -1), (key2604, 1), (key2604, 1), (key2916, 1), (key2916, 1), (key2925, 1), (key2925, 1)]

theorem rawRowCheck1799 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form2 = rawRow1799 := by decide +kernel

def row1799 : Integer.Sparse Key := [(key2589, -2), (key2604, 2), (key2768, 2), (key2916, -2), (key3005, -2), (key3019, 2)]

theorem rowCheck1799 : row1799 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1799 := by decide +kernel

theorem rowEval1799 (x : Key → ℝ) : Integer.Sparse.eval row1799 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1799, Integer.Sparse.eval_collectBalanced, rawRowCheck1799]

def rawRow1800 : Integer.Sparse Key := [(key2916, -2), (key2925, -2), (key2916, -2), (key2845, 1), (key2876, 1), (key2768, 1), (key2876, 1), (key2768, 1), (key2845, 1), (key3019, 2), (key3028, 2), (key3019, 2), (key2845, -1), (key2876, -1), (key2589, -1), (key2876, -1), (key2589, -1), (key2845, -1), (key3019, -1), (key3028, -1), (key3005, -1), (key3028, -1), (key3005, -1), (key3019, -1), (key2916, 1), (key2925, 1), (key2604, 1), (key2925, 1), (key2604, 1), (key2916, 1)]

theorem rawRowCheck1800 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form2 = rawRow1800 := by decide +kernel

def row1800 : Integer.Sparse Key := [(key2589, -2), (key2604, 2), (key2768, 2), (key2916, -2), (key3005, -2), (key3019, 2)]

theorem rowCheck1800 : row1800 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1800 := by decide +kernel

theorem rowEval1800 (x : Key → ℝ) : Integer.Sparse.eval row1800 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1800, Integer.Sparse.eval_collectBalanced, rawRowCheck1800]

def rawRow1801 : Integer.Sparse Key := [(key2925, -2), (key2916, -2), (key2916, -2), (key2876, 1), (key2845, 1), (key2876, 1), (key2768, 1), (key2845, 1), (key2768, 1), (key3028, 2), (key3019, 2), (key3019, 2), (key2876, -1), (key2845, -1), (key2876, -1), (key2589, -1), (key2845, -1), (key2589, -1), (key3028, -1), (key3019, -1), (key3028, -1), (key3005, -1), (key3019, -1), (key3005, -1), (key2925, 1), (key2916, 1), (key2925, 1), (key2604, 1), (key2916, 1), (key2604, 1)]

theorem rawRowCheck1801 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form2 = rawRow1801 := by decide +kernel

def row1801 : Integer.Sparse Key := [(key2589, -2), (key2604, 2), (key2768, 2), (key2916, -2), (key3005, -2), (key3019, 2)]

theorem rowCheck1801 : row1801 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1801 := by decide +kernel

theorem rowEval1801 (x : Key → ℝ) : Integer.Sparse.eval row1801 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form2) x := by
  rw [rowCheck1801, Integer.Sparse.eval_collectBalanced, rawRowCheck1801]

def rawRow1802 : Integer.Sparse Key := [(key3005, -2), (key3005, -2), (key3005, -2), (key3019, 1), (key3019, 1), (key3019, 1), (key3019, 1), (key3019, 1), (key3019, 1), (key2604, 2), (key2604, 2), (key2604, 2), (key2916, -1), (key2916, -1), (key2916, -1), (key2916, -1), (key2916, -1), (key2916, -1), (key2589, -1), (key2589, -1), (key2589, -1), (key2589, -1), (key2589, -1), (key2589, -1), (key2768, 1), (key2768, 1), (key2768, 1), (key2768, 1), (key2768, 1), (key2768, 1)]

theorem rawRowCheck1802 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form2 = rawRow1802 := by decide +kernel

def row1802 : Integer.Sparse Key := [(key2589, -6), (key2604, 6), (key2768, 6), (key2916, -6), (key3005, -6), (key3019, 6)]

theorem rowCheck1802 : row1802 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1802 := by decide +kernel

theorem rowEval1802 (x : Key → ℝ) : Integer.Sparse.eval row1802 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1802, Integer.Sparse.eval_collectBalanced, rawRowCheck1802]

def rawRow1803 : Integer.Sparse Key := [(key3019, -2), (key3019, -2), (key3028, -2), (key3005, 1), (key3005, 1), (key3019, 1), (key3019, 1), (key3028, 1), (key3028, 1), (key2916, 2), (key2916, 2), (key2925, 2), (key2604, -1), (key2604, -1), (key2916, -1), (key2916, -1), (key2925, -1), (key2925, -1), (key2768, -1), (key2768, -1), (key2845, -1), (key2845, -1), (key2876, -1), (key2876, -1), (key2589, 1), (key2589, 1), (key2845, 1), (key2845, 1), (key2876, 1), (key2876, 1)]

theorem rawRowCheck1803 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form2 = rawRow1803 := by decide +kernel

def row1803 : Integer.Sparse Key := [(key2589, 2), (key2604, -2), (key2768, -2), (key2916, 2), (key3005, 2), (key3019, -2)]

theorem rowCheck1803 : row1803 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1803 := by decide +kernel

theorem rowEval1803 (x : Key → ℝ) : Integer.Sparse.eval row1803 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1803, Integer.Sparse.eval_collectBalanced, rawRowCheck1803]

def rawRow1804 : Integer.Sparse Key := [(key3019, -2), (key3028, -2), (key3019, -2), (key3019, 1), (key3028, 1), (key3005, 1), (key3028, 1), (key3005, 1), (key3019, 1), (key2916, 2), (key2925, 2), (key2916, 2), (key2916, -1), (key2925, -1), (key2604, -1), (key2925, -1), (key2604, -1), (key2916, -1), (key2845, -1), (key2876, -1), (key2768, -1), (key2876, -1), (key2768, -1), (key2845, -1), (key2845, 1), (key2876, 1), (key2589, 1), (key2876, 1), (key2589, 1), (key2845, 1)]

theorem rawRowCheck1804 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form2 = rawRow1804 := by decide +kernel

def row1804 : Integer.Sparse Key := [(key2589, 2), (key2604, -2), (key2768, -2), (key2916, 2), (key3005, 2), (key3019, -2)]

theorem rowCheck1804 : row1804 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1804 := by decide +kernel

theorem rowEval1804 (x : Key → ℝ) : Integer.Sparse.eval row1804 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1804, Integer.Sparse.eval_collectBalanced, rawRowCheck1804]

def rawRow1805 : Integer.Sparse Key := [(key3028, -2), (key3019, -2), (key3019, -2), (key3028, 1), (key3019, 1), (key3028, 1), (key3005, 1), (key3019, 1), (key3005, 1), (key2925, 2), (key2916, 2), (key2916, 2), (key2925, -1), (key2916, -1), (key2925, -1), (key2604, -1), (key2916, -1), (key2604, -1), (key2876, -1), (key2845, -1), (key2876, -1), (key2768, -1), (key2845, -1), (key2768, -1), (key2876, 1), (key2845, 1), (key2876, 1), (key2589, 1), (key2845, 1), (key2589, 1)]

theorem rawRowCheck1805 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form2 = rawRow1805 := by decide +kernel

def row1805 : Integer.Sparse Key := [(key2589, 2), (key2604, -2), (key2768, -2), (key2916, 2), (key3005, 2), (key3019, -2)]

theorem rowCheck1805 : row1805 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1805 := by decide +kernel

theorem rowEval1805 (x : Key → ℝ) : Integer.Sparse.eval row1805 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form2) x := by
  rw [rowCheck1805, Integer.Sparse.eval_collectBalanced, rawRowCheck1805]

def rawRow1806 : Integer.Sparse Key := [(key971, -2), (key979, -2), (key979, -2), (key979, 6), (key1085, 2), (key1093, 2), (key1093, 2), (key1093, -2), (key1093, -2), (key1228, -2), (key1164, -6), (key1164, 2), (key1164, 2), (key1245, 2)]

theorem rawRowCheck1806 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form3 = rawRow1806 := by decide +kernel

def row1806 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1164, -2), (key1228, -2), (key1245, 2)]

theorem rowCheck1806 : row1806 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1806 := by decide +kernel

theorem rowEval1806 (x : Key → ℝ) : Integer.Sparse.eval row1806 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1806, Integer.Sparse.eval_collectBalanced, rawRowCheck1806]

def rawRow1807 : Integer.Sparse Key := [(key979, -2), (key971, -2), (key979, -2), (key979, 6), (key1093, 2), (key1085, 2), (key1093, 2), (key1093, -2), (key1228, -2), (key1093, -2), (key1164, -6), (key1164, 2), (key1245, 2), (key1164, 2)]

theorem rawRowCheck1807 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form3 = rawRow1807 := by decide +kernel

def row1807 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1164, -2), (key1228, -2), (key1245, 2)]

theorem rowCheck1807 : row1807 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1807 := by decide +kernel

theorem rowEval1807 (x : Key → ℝ) : Integer.Sparse.eval row1807 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1807, Integer.Sparse.eval_collectBalanced, rawRowCheck1807]

def rawRow1808 : Integer.Sparse Key := [(key979, -2), (key979, -2), (key971, -2), (key979, 6), (key1093, 2), (key1093, 2), (key1085, 2), (key1228, -2), (key1093, -2), (key1093, -2), (key1164, -6), (key1245, 2), (key1164, 2), (key1164, 2)]

theorem rawRowCheck1808 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form3 = rawRow1808 := by decide +kernel

def row1808 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1164, -2), (key1228, -2), (key1245, 2)]

theorem rowCheck1808 : row1808 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1808 := by decide +kernel

theorem rowEval1808 (x : Key → ℝ) : Integer.Sparse.eval row1808 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1808, Integer.Sparse.eval_collectBalanced, rawRowCheck1808]

def rawRow1809 : Integer.Sparse Key := [(key979, -2), (key979, -2), (key979, -2), (key971, 6), (key1228, 2), (key1228, 2), (key1228, 2), (key1085, -2), (key1085, -2), (key1085, -2), (key1245, -6), (key1164, 2), (key1164, 2), (key1164, 2)]

theorem rawRowCheck1809 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form3 = rawRow1809 := by decide +kernel

def row1809 : Integer.Sparse Key := [(key971, 6), (key979, -6), (key1085, -6), (key1164, 6), (key1228, 6), (key1245, -6)]

theorem rowCheck1809 : row1809 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1809 := by decide +kernel

theorem rowEval1809 (x : Key → ℝ) : Integer.Sparse.eval row1809 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1809, Integer.Sparse.eval_collectBalanced, rawRowCheck1809]

def rawRow1810 : Integer.Sparse Key := [(key1085, -2), (key1093, -2), (key1093, -2), (key1164, 6), (key971, 2), (key979, 2), (key979, 2), (key1164, -2), (key1164, -2), (key1245, -2), (key979, -6), (key1093, 2), (key1093, 2), (key1228, 2)]

theorem rawRowCheck1810 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form3 = rawRow1810 := by decide +kernel

def row1810 : Integer.Sparse Key := [(key971, 2), (key979, -2), (key1085, -2), (key1164, 2), (key1228, 2), (key1245, -2)]

theorem rowCheck1810 : row1810 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1810 := by decide +kernel

theorem rowEval1810 (x : Key → ℝ) : Integer.Sparse.eval row1810 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1810, Integer.Sparse.eval_collectBalanced, rawRowCheck1810]

def rawRow1811 : Integer.Sparse Key := [(key1093, -2), (key1085, -2), (key1093, -2), (key1164, 6), (key979, 2), (key971, 2), (key979, 2), (key1164, -2), (key1245, -2), (key1164, -2), (key979, -6), (key1093, 2), (key1228, 2), (key1093, 2)]

theorem rawRowCheck1811 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form3 = rawRow1811 := by decide +kernel

def row1811 : Integer.Sparse Key := [(key971, 2), (key979, -2), (key1085, -2), (key1164, 2), (key1228, 2), (key1245, -2)]

theorem rowCheck1811 : row1811 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1811 := by decide +kernel

theorem rowEval1811 (x : Key → ℝ) : Integer.Sparse.eval row1811 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1811, Integer.Sparse.eval_collectBalanced, rawRowCheck1811]

def rawRow1812 : Integer.Sparse Key := [(key1093, -2), (key1093, -2), (key1085, -2), (key1164, 6), (key979, 2), (key979, 2), (key971, 2), (key1245, -2), (key1164, -2), (key1164, -2), (key979, -6), (key1228, 2), (key1093, 2), (key1093, 2)]

theorem rawRowCheck1812 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form3 = rawRow1812 := by decide +kernel

def row1812 : Integer.Sparse Key := [(key971, 2), (key979, -2), (key1085, -2), (key1164, 2), (key1228, 2), (key1245, -2)]

theorem rowCheck1812 : row1812 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1812 := by decide +kernel

theorem rowEval1812 (x : Key → ℝ) : Integer.Sparse.eval row1812 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1812, Integer.Sparse.eval_collectBalanced, rawRowCheck1812]

def rawRow1813 : Integer.Sparse Key := [(key1093, -2), (key1093, -2), (key1164, -2), (key1085, 6), (key1228, 2), (key1228, 2), (key1245, 2), (key971, -2), (key1085, -2), (key1085, -2), (key1228, -6), (key979, 2), (key1093, 2), (key1093, 2)]

theorem rawRowCheck1813 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form3 = rawRow1813 := by decide +kernel

def row1813 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1164, -2), (key1228, -2), (key1245, 2)]

theorem rowCheck1813 : row1813 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1813 := by decide +kernel

theorem rowEval1813 (x : Key → ℝ) : Integer.Sparse.eval row1813 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1813, Integer.Sparse.eval_collectBalanced, rawRowCheck1813]

def rawRow1814 : Integer.Sparse Key := [(key1093, -2), (key1164, -2), (key1093, -2), (key1085, 6), (key1228, 2), (key1245, 2), (key1228, 2), (key1085, -2), (key971, -2), (key1085, -2), (key1228, -6), (key1093, 2), (key979, 2), (key1093, 2)]

theorem rawRowCheck1814 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form3 = rawRow1814 := by decide +kernel

def row1814 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1164, -2), (key1228, -2), (key1245, 2)]

theorem rowCheck1814 : row1814 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1814 := by decide +kernel

theorem rowEval1814 (x : Key → ℝ) : Integer.Sparse.eval row1814 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1814, Integer.Sparse.eval_collectBalanced, rawRowCheck1814]

def rawRow1815 : Integer.Sparse Key := [(key1164, -2), (key1093, -2), (key1093, -2), (key1085, 6), (key1245, 2), (key1228, 2), (key1228, 2), (key1085, -2), (key1085, -2), (key971, -2), (key1228, -6), (key1093, 2), (key1093, 2), (key979, 2)]

theorem rawRowCheck1815 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form3 = rawRow1815 := by decide +kernel

def row1815 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1164, -2), (key1228, -2), (key1245, 2)]

theorem rowCheck1815 : row1815 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1815 := by decide +kernel

theorem rowEval1815 (x : Key → ℝ) : Integer.Sparse.eval row1815 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form3) x := by
  rw [rowCheck1815, Integer.Sparse.eval_collectBalanced, rawRowCheck1815]

def rawRow1816 : Integer.Sparse Key := [(key1228, -2), (key1228, -2), (key1228, -2), (key1245, 6), (key979, 2), (key979, 2), (key979, 2), (key1164, -2), (key1164, -2), (key1164, -2), (key971, -6), (key1085, 2), (key1085, 2), (key1085, 2)]

theorem rawRowCheck1816 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form3 = rawRow1816 := by decide +kernel

def row1816 : Integer.Sparse Key := [(key971, -6), (key979, 6), (key1085, 6), (key1164, -6), (key1228, -6), (key1245, 6)]

theorem rowCheck1816 : row1816 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1816 := by decide +kernel

theorem rowEval1816 (x : Key → ℝ) : Integer.Sparse.eval row1816 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1816, Integer.Sparse.eval_collectBalanced, rawRowCheck1816]

def rawRow1817 : Integer.Sparse Key := [(key1228, -2), (key1228, -2), (key1245, -2), (key1228, 6), (key1093, 2), (key1093, 2), (key1164, 2), (key979, -2), (key1093, -2), (key1093, -2), (key1085, -6), (key971, 2), (key1085, 2), (key1085, 2)]

theorem rawRowCheck1817 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form3 = rawRow1817 := by decide +kernel

def row1817 : Integer.Sparse Key := [(key971, 2), (key979, -2), (key1085, -2), (key1164, 2), (key1228, 2), (key1245, -2)]

theorem rowCheck1817 : row1817 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1817 := by decide +kernel

theorem rowEval1817 (x : Key → ℝ) : Integer.Sparse.eval row1817 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1817, Integer.Sparse.eval_collectBalanced, rawRowCheck1817]

def rawRow1818 : Integer.Sparse Key := [(key1228, -2), (key1245, -2), (key1228, -2), (key1228, 6), (key1093, 2), (key1164, 2), (key1093, 2), (key1093, -2), (key979, -2), (key1093, -2), (key1085, -6), (key1085, 2), (key971, 2), (key1085, 2)]

theorem rawRowCheck1818 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form3 = rawRow1818 := by decide +kernel

def row1818 : Integer.Sparse Key := [(key971, 2), (key979, -2), (key1085, -2), (key1164, 2), (key1228, 2), (key1245, -2)]

theorem rowCheck1818 : row1818 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1818 := by decide +kernel

theorem rowEval1818 (x : Key → ℝ) : Integer.Sparse.eval row1818 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1818, Integer.Sparse.eval_collectBalanced, rawRowCheck1818]

def rawRow1819 : Integer.Sparse Key := [(key1245, -2), (key1228, -2), (key1228, -2), (key1228, 6), (key1164, 2), (key1093, 2), (key1093, 2), (key1093, -2), (key1093, -2), (key979, -2), (key1085, -6), (key1085, 2), (key1085, 2), (key971, 2)]

theorem rawRowCheck1819 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form3 = rawRow1819 := by decide +kernel

def row1819 : Integer.Sparse Key := [(key971, 2), (key979, -2), (key1085, -2), (key1164, 2), (key1228, 2), (key1245, -2)]

theorem rowCheck1819 : row1819 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1819 := by decide +kernel

theorem rowEval1819 (x : Key → ℝ) : Integer.Sparse.eval row1819 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form3) x := by
  rw [rowCheck1819, Integer.Sparse.eval_collectBalanced, rawRowCheck1819]

def rawRow1820 : Integer.Sparse Key := [(key2372, -6), (key2372, 2), (key2372, 2), (key2385, 2), (key2400, 6), (key2400, -2), (key2400, -2), (key2432, -2), (key2466, -2), (key2466, -2), (key2475, -2), (key2466, 2), (key2466, 2), (key2498, 2)]

theorem rawRowCheck1820 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form4 = rawRow1820 := by decide +kernel

def row1820 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 2), (key2432, -2), (key2475, -2), (key2498, 2)]

theorem rowCheck1820 : row1820 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1820 := by decide +kernel

theorem rowEval1820 (x : Key → ℝ) : Integer.Sparse.eval row1820 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1820, Integer.Sparse.eval_collectBalanced, rawRowCheck1820]

def rawRow1821 : Integer.Sparse Key := [(key2372, -6), (key2372, 2), (key2385, 2), (key2372, 2), (key2400, 6), (key2400, -2), (key2432, -2), (key2400, -2), (key2466, -2), (key2475, -2), (key2466, -2), (key2466, 2), (key2498, 2), (key2466, 2)]

theorem rawRowCheck1821 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form4 = rawRow1821 := by decide +kernel

def row1821 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 2), (key2432, -2), (key2475, -2), (key2498, 2)]

theorem rowCheck1821 : row1821 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1821 := by decide +kernel

theorem rowEval1821 (x : Key → ℝ) : Integer.Sparse.eval row1821 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1821, Integer.Sparse.eval_collectBalanced, rawRowCheck1821]

def rawRow1822 : Integer.Sparse Key := [(key2372, -6), (key2385, 2), (key2372, 2), (key2372, 2), (key2400, 6), (key2432, -2), (key2400, -2), (key2400, -2), (key2475, -2), (key2466, -2), (key2466, -2), (key2498, 2), (key2466, 2), (key2466, 2)]

theorem rawRowCheck1822 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form4 = rawRow1822 := by decide +kernel

def row1822 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 2), (key2432, -2), (key2475, -2), (key2498, 2)]

theorem rowCheck1822 : row1822 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1822 := by decide +kernel

theorem rowEval1822 (x : Key → ℝ) : Integer.Sparse.eval row1822 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1822, Integer.Sparse.eval_collectBalanced, rawRowCheck1822]

def rawRow1823 : Integer.Sparse Key := [(key2385, -6), (key2372, 2), (key2372, 2), (key2372, 2), (key2432, 6), (key2400, -2), (key2400, -2), (key2400, -2), (key2498, -2), (key2498, -2), (key2498, -2), (key2475, 2), (key2475, 2), (key2475, 2)]

theorem rawRowCheck1823 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form4 = rawRow1823 := by decide +kernel

def row1823 : Integer.Sparse Key := [(key2372, 6), (key2385, -6), (key2400, -6), (key2432, 6), (key2475, 6), (key2498, -6)]

theorem rowCheck1823 : row1823 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1823 := by decide +kernel

theorem rowEval1823 (x : Key → ℝ) : Integer.Sparse.eval row1823 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1823, Integer.Sparse.eval_collectBalanced, rawRowCheck1823]

def rawRow1824 : Integer.Sparse Key := [(key2400, -6), (key2466, 2), (key2466, 2), (key2475, 2), (key2372, 6), (key2466, -2), (key2466, -2), (key2498, -2), (key2372, -2), (key2372, -2), (key2385, -2), (key2400, 2), (key2400, 2), (key2432, 2)]

theorem rawRowCheck1824 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form4 = rawRow1824 := by decide +kernel

def row1824 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, -2), (key2432, 2), (key2475, 2), (key2498, -2)]

theorem rowCheck1824 : row1824 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1824 := by decide +kernel

theorem rowEval1824 (x : Key → ℝ) : Integer.Sparse.eval row1824 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1824, Integer.Sparse.eval_collectBalanced, rawRowCheck1824]

def rawRow1825 : Integer.Sparse Key := [(key2400, -6), (key2466, 2), (key2475, 2), (key2466, 2), (key2372, 6), (key2466, -2), (key2498, -2), (key2466, -2), (key2372, -2), (key2385, -2), (key2372, -2), (key2400, 2), (key2432, 2), (key2400, 2)]

theorem rawRowCheck1825 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form4 = rawRow1825 := by decide +kernel

def row1825 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, -2), (key2432, 2), (key2475, 2), (key2498, -2)]

theorem rowCheck1825 : row1825 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1825 := by decide +kernel

theorem rowEval1825 (x : Key → ℝ) : Integer.Sparse.eval row1825 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1825, Integer.Sparse.eval_collectBalanced, rawRowCheck1825]

def rawRow1826 : Integer.Sparse Key := [(key2400, -6), (key2475, 2), (key2466, 2), (key2466, 2), (key2372, 6), (key2498, -2), (key2466, -2), (key2466, -2), (key2385, -2), (key2372, -2), (key2372, -2), (key2432, 2), (key2400, 2), (key2400, 2)]

theorem rawRowCheck1826 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form4 = rawRow1826 := by decide +kernel

def row1826 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, -2), (key2432, 2), (key2475, 2), (key2498, -2)]

theorem rowCheck1826 : row1826 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1826 := by decide +kernel

theorem rowEval1826 (x : Key → ℝ) : Integer.Sparse.eval row1826 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1826, Integer.Sparse.eval_collectBalanced, rawRowCheck1826]

def rawRow1827 : Integer.Sparse Key := [(key2475, -6), (key2400, 2), (key2466, 2), (key2466, 2), (key2498, 6), (key2372, -2), (key2466, -2), (key2466, -2), (key2432, -2), (key2498, -2), (key2498, -2), (key2385, 2), (key2475, 2), (key2475, 2)]

theorem rawRowCheck1827 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form4 = rawRow1827 := by decide +kernel

def row1827 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 2), (key2432, -2), (key2475, -2), (key2498, 2)]

theorem rowCheck1827 : row1827 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1827 := by decide +kernel

theorem rowEval1827 (x : Key → ℝ) : Integer.Sparse.eval row1827 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1827, Integer.Sparse.eval_collectBalanced, rawRowCheck1827]

def rawRow1828 : Integer.Sparse Key := [(key2475, -6), (key2466, 2), (key2400, 2), (key2466, 2), (key2498, 6), (key2466, -2), (key2372, -2), (key2466, -2), (key2498, -2), (key2432, -2), (key2498, -2), (key2475, 2), (key2385, 2), (key2475, 2)]

theorem rawRowCheck1828 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form4 = rawRow1828 := by decide +kernel

def row1828 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 2), (key2432, -2), (key2475, -2), (key2498, 2)]

theorem rowCheck1828 : row1828 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1828 := by decide +kernel

theorem rowEval1828 (x : Key → ℝ) : Integer.Sparse.eval row1828 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1828, Integer.Sparse.eval_collectBalanced, rawRowCheck1828]

def rawRow1829 : Integer.Sparse Key := [(key2475, -6), (key2466, 2), (key2466, 2), (key2400, 2), (key2498, 6), (key2466, -2), (key2466, -2), (key2372, -2), (key2498, -2), (key2498, -2), (key2432, -2), (key2475, 2), (key2475, 2), (key2385, 2)]

theorem rawRowCheck1829 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form4 = rawRow1829 := by decide +kernel

def row1829 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 2), (key2432, -2), (key2475, -2), (key2498, 2)]

theorem rowCheck1829 : row1829 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1829 := by decide +kernel

theorem rowEval1829 (x : Key → ℝ) : Integer.Sparse.eval row1829 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form4) x := by
  rw [rowCheck1829, Integer.Sparse.eval_collectBalanced, rawRowCheck1829]

def rawRow1830 : Integer.Sparse Key := [(key2432, -6), (key2498, 2), (key2498, 2), (key2498, 2), (key2385, 6), (key2475, -2), (key2475, -2), (key2475, -2), (key2372, -2), (key2372, -2), (key2372, -2), (key2400, 2), (key2400, 2), (key2400, 2)]

theorem rawRowCheck1830 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form4 = rawRow1830 := by decide +kernel

def row1830 : Integer.Sparse Key := [(key2372, -6), (key2385, 6), (key2400, 6), (key2432, -6), (key2475, -6), (key2498, 6)]

theorem rowCheck1830 : row1830 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1830 := by decide +kernel

theorem rowEval1830 (x : Key → ℝ) : Integer.Sparse.eval row1830 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1830, Integer.Sparse.eval_collectBalanced, rawRowCheck1830]

def rawRow1831 : Integer.Sparse Key := [(key2498, -6), (key2432, 2), (key2498, 2), (key2498, 2), (key2475, 6), (key2385, -2), (key2475, -2), (key2475, -2), (key2400, -2), (key2466, -2), (key2466, -2), (key2372, 2), (key2466, 2), (key2466, 2)]

theorem rawRowCheck1831 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form4 = rawRow1831 := by decide +kernel

def row1831 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, -2), (key2432, 2), (key2475, 2), (key2498, -2)]

theorem rowCheck1831 : row1831 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1831 := by decide +kernel

theorem rowEval1831 (x : Key → ℝ) : Integer.Sparse.eval row1831 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1831, Integer.Sparse.eval_collectBalanced, rawRowCheck1831]

def rawRow1832 : Integer.Sparse Key := [(key2498, -6), (key2498, 2), (key2432, 2), (key2498, 2), (key2475, 6), (key2475, -2), (key2385, -2), (key2475, -2), (key2466, -2), (key2400, -2), (key2466, -2), (key2466, 2), (key2372, 2), (key2466, 2)]

theorem rawRowCheck1832 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form4 = rawRow1832 := by decide +kernel

def row1832 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, -2), (key2432, 2), (key2475, 2), (key2498, -2)]

theorem rowCheck1832 : row1832 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1832 := by decide +kernel

theorem rowEval1832 (x : Key → ℝ) : Integer.Sparse.eval row1832 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1832, Integer.Sparse.eval_collectBalanced, rawRowCheck1832]

def rawRow1833 : Integer.Sparse Key := [(key2498, -6), (key2498, 2), (key2498, 2), (key2432, 2), (key2475, 6), (key2475, -2), (key2475, -2), (key2385, -2), (key2466, -2), (key2466, -2), (key2400, -2), (key2466, 2), (key2466, 2), (key2372, 2)]

theorem rawRowCheck1833 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form4 = rawRow1833 := by decide +kernel

def row1833 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, -2), (key2432, 2), (key2475, 2), (key2498, -2)]

theorem rowCheck1833 : row1833 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1833 := by decide +kernel

theorem rowEval1833 (x : Key → ℝ) : Integer.Sparse.eval row1833 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form4) x := by
  rw [rowCheck1833, Integer.Sparse.eval_collectBalanced, rawRowCheck1833]

def rawRow1834 : Integer.Sparse Key := [(key1526, -1), (key1534, -1), (key1526, -1), (key1894, -1), (key1534, -1), (key1894, -1), (key1534, 2), (key1534, 2), (key1894, 2), (key1604, 1), (key1612, 1), (key1604, 1), (key1916, 1), (key1612, 1), (key1916, 1), (key1612, -1), (key1679, -1), (key1612, -1), (key1916, -1), (key1679, -1), (key1916, -1), (key1640, -2), (key1640, -2), (key1930, -2), (key1640, 1), (key1693, 1), (key1640, 1), (key1930, 1), (key1693, 1), (key1930, 1)]

theorem rawRowCheck1834 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form5 = rawRow1834 := by decide +kernel

def row1834 : Integer.Sparse Key := [(key1526, -2), (key1534, 2), (key1604, 2), (key1640, -2), (key1679, -2), (key1693, 2)]

theorem rowCheck1834 : row1834 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1834 := by decide +kernel

theorem rowEval1834 (x : Key → ℝ) : Integer.Sparse.eval row1834 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form5) x := by
  rw [rowCheck1834, Integer.Sparse.eval_collectBalanced, rawRowCheck1834]

def rawRow1835 : Integer.Sparse Key := [(key1534, -1), (key1526, -1), (key1894, -1), (key1526, -1), (key1894, -1), (key1534, -1), (key1534, 2), (key1894, 2), (key1534, 2), (key1612, 1), (key1604, 1), (key1916, 1), (key1604, 1), (key1916, 1), (key1612, 1), (key1679, -1), (key1612, -1), (key1916, -1), (key1612, -1), (key1916, -1), (key1679, -1), (key1640, -2), (key1930, -2), (key1640, -2), (key1693, 1), (key1640, 1), (key1930, 1), (key1640, 1), (key1930, 1), (key1693, 1)]

theorem rawRowCheck1835 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form5 = rawRow1835 := by decide +kernel

def row1835 : Integer.Sparse Key := [(key1526, -2), (key1534, 2), (key1604, 2), (key1640, -2), (key1679, -2), (key1693, 2)]

theorem rowCheck1835 : row1835 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1835 := by decide +kernel

theorem rowEval1835 (x : Key → ℝ) : Integer.Sparse.eval row1835 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1835, Integer.Sparse.eval_collectBalanced, rawRowCheck1835]

def rawRow1836 : Integer.Sparse Key := [(key1894, -1), (key1894, -1), (key1534, -1), (key1534, -1), (key1526, -1), (key1526, -1), (key1894, 2), (key1534, 2), (key1534, 2), (key1916, 1), (key1916, 1), (key1612, 1), (key1612, 1), (key1604, 1), (key1604, 1), (key1916, -1), (key1916, -1), (key1679, -1), (key1679, -1), (key1612, -1), (key1612, -1), (key1930, -2), (key1640, -2), (key1640, -2), (key1930, 1), (key1930, 1), (key1693, 1), (key1693, 1), (key1640, 1), (key1640, 1)]

theorem rawRowCheck1836 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form5 = rawRow1836 := by decide +kernel

def row1836 : Integer.Sparse Key := [(key1526, -2), (key1534, 2), (key1604, 2), (key1640, -2), (key1679, -2), (key1693, 2)]

theorem rowCheck1836 : row1836 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1836 := by decide +kernel

theorem rowEval1836 (x : Key → ℝ) : Integer.Sparse.eval row1836 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1836, Integer.Sparse.eval_collectBalanced, rawRowCheck1836]

def rawRow1837 : Integer.Sparse Key := [(key1534, -1), (key1534, -1), (key1534, -1), (key1534, -1), (key1534, -1), (key1534, -1), (key1526, 2), (key1526, 2), (key1526, 2), (key1679, 1), (key1679, 1), (key1679, 1), (key1679, 1), (key1679, 1), (key1679, 1), (key1604, -1), (key1604, -1), (key1604, -1), (key1604, -1), (key1604, -1), (key1604, -1), (key1693, -2), (key1693, -2), (key1693, -2), (key1640, 1), (key1640, 1), (key1640, 1), (key1640, 1), (key1640, 1), (key1640, 1)]

theorem rawRowCheck1837 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form5 = rawRow1837 := by decide +kernel

def row1837 : Integer.Sparse Key := [(key1526, 6), (key1534, -6), (key1604, -6), (key1640, 6), (key1679, 6), (key1693, -6)]

theorem rowCheck1837 : row1837 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1837 := by decide +kernel

theorem rowEval1837 (x : Key → ℝ) : Integer.Sparse.eval row1837 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1837, Integer.Sparse.eval_collectBalanced, rawRowCheck1837]

def rawRow1838 : Integer.Sparse Key := [(key1604, -1), (key1612, -1), (key1604, -1), (key1916, -1), (key1612, -1), (key1916, -1), (key1640, 2), (key1640, 2), (key1930, 2), (key1526, 1), (key1534, 1), (key1526, 1), (key1894, 1), (key1534, 1), (key1894, 1), (key1640, -1), (key1693, -1), (key1640, -1), (key1930, -1), (key1693, -1), (key1930, -1), (key1534, -2), (key1534, -2), (key1894, -2), (key1612, 1), (key1679, 1), (key1612, 1), (key1916, 1), (key1679, 1), (key1916, 1)]

theorem rawRowCheck1838 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form5 = rawRow1838 := by decide +kernel

def row1838 : Integer.Sparse Key := [(key1526, 2), (key1534, -2), (key1604, -2), (key1640, 2), (key1679, 2), (key1693, -2)]

theorem rowCheck1838 : row1838 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1838 := by decide +kernel

theorem rowEval1838 (x : Key → ℝ) : Integer.Sparse.eval row1838 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form5) x := by
  rw [rowCheck1838, Integer.Sparse.eval_collectBalanced, rawRowCheck1838]

def rawRow1839 : Integer.Sparse Key := [(key1612, -1), (key1604, -1), (key1916, -1), (key1604, -1), (key1916, -1), (key1612, -1), (key1640, 2), (key1930, 2), (key1640, 2), (key1534, 1), (key1526, 1), (key1894, 1), (key1526, 1), (key1894, 1), (key1534, 1), (key1693, -1), (key1640, -1), (key1930, -1), (key1640, -1), (key1930, -1), (key1693, -1), (key1534, -2), (key1894, -2), (key1534, -2), (key1679, 1), (key1612, 1), (key1916, 1), (key1612, 1), (key1916, 1), (key1679, 1)]

theorem rawRowCheck1839 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form5 = rawRow1839 := by decide +kernel

def row1839 : Integer.Sparse Key := [(key1526, 2), (key1534, -2), (key1604, -2), (key1640, 2), (key1679, 2), (key1693, -2)]

theorem rowCheck1839 : row1839 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1839 := by decide +kernel

theorem rowEval1839 (x : Key → ℝ) : Integer.Sparse.eval row1839 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1839, Integer.Sparse.eval_collectBalanced, rawRowCheck1839]

def rawRow1840 : Integer.Sparse Key := [(key1916, -1), (key1916, -1), (key1612, -1), (key1612, -1), (key1604, -1), (key1604, -1), (key1930, 2), (key1640, 2), (key1640, 2), (key1894, 1), (key1894, 1), (key1534, 1), (key1534, 1), (key1526, 1), (key1526, 1), (key1930, -1), (key1930, -1), (key1693, -1), (key1693, -1), (key1640, -1), (key1640, -1), (key1894, -2), (key1534, -2), (key1534, -2), (key1916, 1), (key1916, 1), (key1679, 1), (key1679, 1), (key1612, 1), (key1612, 1)]

theorem rawRowCheck1840 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form5 = rawRow1840 := by decide +kernel

def row1840 : Integer.Sparse Key := [(key1526, 2), (key1534, -2), (key1604, -2), (key1640, 2), (key1679, 2), (key1693, -2)]

theorem rowCheck1840 : row1840 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1840 := by decide +kernel

theorem rowEval1840 (x : Key → ℝ) : Integer.Sparse.eval row1840 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1840, Integer.Sparse.eval_collectBalanced, rawRowCheck1840]

def rawRow1841 : Integer.Sparse Key := [(key1259, -1), (key1259, -1), (key1612, -1), (key1612, -1), (key1640, -1), (key1640, -1), (key1251, 2), (key1604, 2), (key1604, 2), (key1271, 1), (key1271, 1), (key1679, 1), (key1679, 1), (key1693, 1), (key1693, 1), (key1251, -1), (key1251, -1), (key1526, -1), (key1526, -1), (key1604, -1), (key1604, -1), (key1271, -2), (key1679, -2), (key1679, -2), (key1259, 1), (key1259, 1), (key1534, 1), (key1534, 1), (key1612, 1), (key1612, 1)]

theorem rawRowCheck1841 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form5 = rawRow1841 := by decide +kernel

def row1841 : Integer.Sparse Key := [(key1526, -2), (key1534, 2), (key1604, 2), (key1640, -2), (key1679, -2), (key1693, 2)]

theorem rowCheck1841 : row1841 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1841 := by decide +kernel

theorem rowEval1841 (x : Key → ℝ) : Integer.Sparse.eval row1841 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1841, Integer.Sparse.eval_collectBalanced, rawRowCheck1841]

def rawRow1842 : Integer.Sparse Key := [(key1612, -1), (key1640, -1), (key1259, -1), (key1640, -1), (key1259, -1), (key1612, -1), (key1604, 2), (key1251, 2), (key1604, 2), (key1679, 1), (key1693, 1), (key1271, 1), (key1693, 1), (key1271, 1), (key1679, 1), (key1526, -1), (key1604, -1), (key1251, -1), (key1604, -1), (key1251, -1), (key1526, -1), (key1679, -2), (key1271, -2), (key1679, -2), (key1534, 1), (key1612, 1), (key1259, 1), (key1612, 1), (key1259, 1), (key1534, 1)]

theorem rawRowCheck1842 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form5 = rawRow1842 := by decide +kernel

def row1842 : Integer.Sparse Key := [(key1526, -2), (key1534, 2), (key1604, 2), (key1640, -2), (key1679, -2), (key1693, 2)]

theorem rowCheck1842 : row1842 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1842 := by decide +kernel

theorem rowEval1842 (x : Key → ℝ) : Integer.Sparse.eval row1842 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1842, Integer.Sparse.eval_collectBalanced, rawRowCheck1842]

def rawRow1843 : Integer.Sparse Key := [(key1640, -1), (key1612, -1), (key1640, -1), (key1259, -1), (key1612, -1), (key1259, -1), (key1604, 2), (key1604, 2), (key1251, 2), (key1693, 1), (key1679, 1), (key1693, 1), (key1271, 1), (key1679, 1), (key1271, 1), (key1604, -1), (key1526, -1), (key1604, -1), (key1251, -1), (key1526, -1), (key1251, -1), (key1679, -2), (key1679, -2), (key1271, -2), (key1612, 1), (key1534, 1), (key1612, 1), (key1259, 1), (key1534, 1), (key1259, 1)]

theorem rawRowCheck1843 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form5 = rawRow1843 := by decide +kernel

def row1843 : Integer.Sparse Key := [(key1526, -2), (key1534, 2), (key1604, 2), (key1640, -2), (key1679, -2), (key1693, 2)]

theorem rowCheck1843 : row1843 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1843 := by decide +kernel

theorem rowEval1843 (x : Key → ℝ) : Integer.Sparse.eval row1843 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form5) x := by
  rw [rowCheck1843, Integer.Sparse.eval_collectBalanced, rawRowCheck1843]

def rawRow1844 : Integer.Sparse Key := [(key1679, -1), (key1679, -1), (key1679, -1), (key1679, -1), (key1679, -1), (key1679, -1), (key1693, 2), (key1693, 2), (key1693, 2), (key1534, 1), (key1534, 1), (key1534, 1), (key1534, 1), (key1534, 1), (key1534, 1), (key1640, -1), (key1640, -1), (key1640, -1), (key1640, -1), (key1640, -1), (key1640, -1), (key1526, -2), (key1526, -2), (key1526, -2), (key1604, 1), (key1604, 1), (key1604, 1), (key1604, 1), (key1604, 1), (key1604, 1)]

theorem rawRowCheck1844 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form5 = rawRow1844 := by decide +kernel

def row1844 : Integer.Sparse Key := [(key1526, -6), (key1534, 6), (key1604, 6), (key1640, -6), (key1679, -6), (key1693, 6)]

theorem rowCheck1844 : row1844 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1844 := by decide +kernel

theorem rowEval1844 (x : Key → ℝ) : Integer.Sparse.eval row1844 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1844, Integer.Sparse.eval_collectBalanced, rawRowCheck1844]

def rawRow1845 : Integer.Sparse Key := [(key1271, -1), (key1271, -1), (key1679, -1), (key1679, -1), (key1693, -1), (key1693, -1), (key1271, 2), (key1679, 2), (key1679, 2), (key1259, 1), (key1259, 1), (key1612, 1), (key1612, 1), (key1640, 1), (key1640, 1), (key1259, -1), (key1259, -1), (key1534, -1), (key1534, -1), (key1612, -1), (key1612, -1), (key1251, -2), (key1604, -2), (key1604, -2), (key1251, 1), (key1251, 1), (key1526, 1), (key1526, 1), (key1604, 1), (key1604, 1)]

theorem rawRowCheck1845 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form5 = rawRow1845 := by decide +kernel

def row1845 : Integer.Sparse Key := [(key1526, 2), (key1534, -2), (key1604, -2), (key1640, 2), (key1679, 2), (key1693, -2)]

theorem rowCheck1845 : row1845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1845 := by decide +kernel

theorem rowEval1845 (x : Key → ℝ) : Integer.Sparse.eval row1845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1845, Integer.Sparse.eval_collectBalanced, rawRowCheck1845]

def rawRow1846 : Integer.Sparse Key := [(key1679, -1), (key1693, -1), (key1271, -1), (key1693, -1), (key1271, -1), (key1679, -1), (key1679, 2), (key1271, 2), (key1679, 2), (key1612, 1), (key1640, 1), (key1259, 1), (key1640, 1), (key1259, 1), (key1612, 1), (key1534, -1), (key1612, -1), (key1259, -1), (key1612, -1), (key1259, -1), (key1534, -1), (key1604, -2), (key1251, -2), (key1604, -2), (key1526, 1), (key1604, 1), (key1251, 1), (key1604, 1), (key1251, 1), (key1526, 1)]

theorem rawRowCheck1846 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form5 = rawRow1846 := by decide +kernel

def row1846 : Integer.Sparse Key := [(key1526, 2), (key1534, -2), (key1604, -2), (key1640, 2), (key1679, 2), (key1693, -2)]

theorem rowCheck1846 : row1846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1846 := by decide +kernel

theorem rowEval1846 (x : Key → ℝ) : Integer.Sparse.eval row1846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1846, Integer.Sparse.eval_collectBalanced, rawRowCheck1846]

def rawRow1847 : Integer.Sparse Key := [(key1693, -1), (key1679, -1), (key1693, -1), (key1271, -1), (key1679, -1), (key1271, -1), (key1679, 2), (key1679, 2), (key1271, 2), (key1640, 1), (key1612, 1), (key1640, 1), (key1259, 1), (key1612, 1), (key1259, 1), (key1612, -1), (key1534, -1), (key1612, -1), (key1259, -1), (key1534, -1), (key1259, -1), (key1604, -2), (key1604, -2), (key1251, -2), (key1604, 1), (key1526, 1), (key1604, 1), (key1251, 1), (key1526, 1), (key1251, 1)]

theorem rawRowCheck1847 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form5 = rawRow1847 := by decide +kernel

def row1847 : Integer.Sparse Key := [(key1526, 2), (key1534, -2), (key1604, -2), (key1640, 2), (key1679, 2), (key1693, -2)]

theorem rowCheck1847 : row1847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1847 := by decide +kernel

theorem rowEval1847 (x : Key → ℝ) : Integer.Sparse.eval row1847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form5) x := by
  rw [rowCheck1847, Integer.Sparse.eval_collectBalanced, rawRowCheck1847]

def rawRow1848 : Integer.Sparse Key := [(key2414, -2), (key2426, -2), (key2426, -2), (key2419, 2), (key2426, 2), (key2426, 2), (key2487, 2), (key2494, 2), (key2494, 2), (key2494, -6), (key2572, -2), (key2573, -2), (key2573, -2), (key2573, 6)]

theorem rawRowCheck1848 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form6 = rawRow1848 := by decide +kernel

def row1848 : Integer.Sparse Key := [(key2414, -2), (key2419, 2), (key2487, 2), (key2494, -2), (key2572, -2), (key2573, 2)]

theorem rowCheck1848 : row1848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1848 := by decide +kernel

theorem rowEval1848 (x : Key → ℝ) : Integer.Sparse.eval row1848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1848, Integer.Sparse.eval_collectBalanced, rawRowCheck1848]

def rawRow1849 : Integer.Sparse Key := [(key2426, -2), (key2414, -2), (key2426, -2), (key2426, 2), (key2419, 2), (key2426, 2), (key2494, 2), (key2487, 2), (key2494, 2), (key2494, -6), (key2573, -2), (key2572, -2), (key2573, -2), (key2573, 6)]

theorem rawRowCheck1849 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form6 = rawRow1849 := by decide +kernel

def row1849 : Integer.Sparse Key := [(key2414, -2), (key2419, 2), (key2487, 2), (key2494, -2), (key2572, -2), (key2573, 2)]

theorem rowCheck1849 : row1849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1849 := by decide +kernel

theorem rowEval1849 (x : Key → ℝ) : Integer.Sparse.eval row1849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1849, Integer.Sparse.eval_collectBalanced, rawRowCheck1849]

def rawRow1850 : Integer.Sparse Key := [(key2426, -2), (key2426, -2), (key2414, -2), (key2426, 2), (key2426, 2), (key2419, 2), (key2494, 2), (key2494, 2), (key2487, 2), (key2494, -6), (key2573, -2), (key2573, -2), (key2572, -2), (key2573, 6)]

theorem rawRowCheck1850 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form6 = rawRow1850 := by decide +kernel

def row1850 : Integer.Sparse Key := [(key2414, -2), (key2419, 2), (key2487, 2), (key2494, -2), (key2572, -2), (key2573, 2)]

theorem rowCheck1850 : row1850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1850 := by decide +kernel

theorem rowEval1850 (x : Key → ℝ) : Integer.Sparse.eval row1850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1850, Integer.Sparse.eval_collectBalanced, rawRowCheck1850]

def rawRow1851 : Integer.Sparse Key := [(key2419, -2), (key2419, -2), (key2419, -2), (key2414, 2), (key2414, 2), (key2414, 2), (key2494, 2), (key2494, 2), (key2494, 2), (key2487, -6), (key2573, -2), (key2573, -2), (key2573, -2), (key2572, 6)]

theorem rawRowCheck1851 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form6 = rawRow1851 := by decide +kernel

def row1851 : Integer.Sparse Key := [(key2414, 6), (key2419, -6), (key2487, -6), (key2494, 6), (key2572, 6), (key2573, -6)]

theorem rowCheck1851 : row1851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1851 := by decide +kernel

theorem rowEval1851 (x : Key → ℝ) : Integer.Sparse.eval row1851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1851, Integer.Sparse.eval_collectBalanced, rawRowCheck1851]

def rawRow1852 : Integer.Sparse Key := [(key3120, -2), (key3141, -2), (key3141, -2), (key3130, 2), (key3144, 2), (key3144, 2), (key2414, 2), (key2426, 2), (key2426, 2), (key2573, -6), (key2419, -2), (key2426, -2), (key2426, -2), (key2494, 6)]

theorem rawRowCheck1852 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form6 = rawRow1852 := by decide +kernel

def row1852 : Integer.Sparse Key := [(key2414, 2), (key2419, -2), (key2494, 6), (key2573, -6), (key3120, -2), (key3130, 2), (key3141, -4), (key3144, 4)]

theorem rowCheck1852 : row1852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1852 := by decide +kernel

theorem rowEval1852 (x : Key → ℝ) : Integer.Sparse.eval row1852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1852, Integer.Sparse.eval_collectBalanced, rawRowCheck1852]

def rawRow1853 : Integer.Sparse Key := [(key3141, -2), (key3120, -2), (key3141, -2), (key3144, 2), (key3130, 2), (key3144, 2), (key2426, 2), (key2414, 2), (key2426, 2), (key2573, -6), (key2426, -2), (key2419, -2), (key2426, -2), (key2494, 6)]

theorem rawRowCheck1853 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form6 = rawRow1853 := by decide +kernel

def row1853 : Integer.Sparse Key := [(key2414, 2), (key2419, -2), (key2494, 6), (key2573, -6), (key3120, -2), (key3130, 2), (key3141, -4), (key3144, 4)]

theorem rowCheck1853 : row1853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1853 := by decide +kernel

theorem rowEval1853 (x : Key → ℝ) : Integer.Sparse.eval row1853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1853, Integer.Sparse.eval_collectBalanced, rawRowCheck1853]

def rawRow1854 : Integer.Sparse Key := [(key3141, -2), (key3141, -2), (key3120, -2), (key3144, 2), (key3144, 2), (key3130, 2), (key2426, 2), (key2426, 2), (key2414, 2), (key2573, -6), (key2426, -2), (key2426, -2), (key2419, -2), (key2494, 6)]

theorem rawRowCheck1854 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form6 = rawRow1854 := by decide +kernel

def row1854 : Integer.Sparse Key := [(key2414, 2), (key2419, -2), (key2494, 6), (key2573, -6), (key3120, -2), (key3130, 2), (key3141, -4), (key3144, 4)]

theorem rowCheck1854 : row1854 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1854 := by decide +kernel

theorem rowEval1854 (x : Key → ℝ) : Integer.Sparse.eval row1854 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1854, Integer.Sparse.eval_collectBalanced, rawRowCheck1854]

def rawRow1855 : Integer.Sparse Key := [(key3038, -2), (key3038, -2), (key3130, -2), (key3033, 2), (key3033, 2), (key3120, 2), (key3043, 2), (key3043, 2), (key3144, 2), (key2414, -6), (key2426, -2), (key2426, -2), (key2494, -2), (key2419, 6)]

theorem rawRowCheck1855 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form6 = rawRow1855 := by decide +kernel

def row1855 : Integer.Sparse Key := [(key2414, -6), (key2419, 6), (key2426, -4), (key2494, -2), (key3033, 4), (key3038, -4), (key3043, 4), (key3120, 2), (key3130, -2), (key3144, 2)]

theorem rowCheck1855 : row1855 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1855 := by decide +kernel

theorem rowEval1855 (x : Key → ℝ) : Integer.Sparse.eval row1855 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1855, Integer.Sparse.eval_collectBalanced, rawRowCheck1855]

def rawRow1856 : Integer.Sparse Key := [(key3038, -2), (key3130, -2), (key3038, -2), (key3033, 2), (key3120, 2), (key3033, 2), (key3043, 2), (key3144, 2), (key3043, 2), (key3033, -6), (key2426, -2), (key2494, -2), (key2426, -2), (key2419, 6)]

theorem rawRowCheck1856 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form6 = rawRow1856 := by decide +kernel

def row1856 : Integer.Sparse Key := [(key2419, 6), (key2426, -4), (key2494, -2), (key3033, -2), (key3038, -4), (key3043, 4), (key3120, 2), (key3130, -2), (key3144, 2)]

theorem rowCheck1856 : row1856 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1856 := by decide +kernel

theorem rowEval1856 (x : Key → ℝ) : Integer.Sparse.eval row1856 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1856, Integer.Sparse.eval_collectBalanced, rawRowCheck1856]

def rawRow1857 : Integer.Sparse Key := [(key3130, -2), (key3038, -2), (key3038, -2), (key3120, 2), (key3033, 2), (key3033, 2), (key3144, 2), (key3043, 2), (key3043, 2), (key3033, -6), (key2494, -2), (key2426, -2), (key2426, -2), (key2419, 6)]

theorem rawRowCheck1857 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form6 = rawRow1857 := by decide +kernel

def row1857 : Integer.Sparse Key := [(key2419, 6), (key2426, -4), (key2494, -2), (key3033, -2), (key3038, -4), (key3043, 4), (key3120, 2), (key3130, -2), (key3144, 2)]

theorem rowCheck1857 : row1857 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1857 := by decide +kernel

theorem rowEval1857 (x : Key → ℝ) : Integer.Sparse.eval row1857 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form6) x := by
  rw [rowCheck1857, Integer.Sparse.eval_collectBalanced, rawRowCheck1857]

def rawRow1858 : Integer.Sparse Key := [(key3141, -2), (key3141, -2), (key3141, -2), (key3144, 2), (key3144, 2), (key3144, 2), (key3038, 2), (key3038, 2), (key3038, 2), (key3130, -6), (key2414, -2), (key2414, -2), (key2414, -2), (key2487, 6)]

theorem rawRowCheck1858 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form6 = rawRow1858 := by decide +kernel

def row1858 : Integer.Sparse Key := [(key2414, -6), (key2487, 6), (key3038, 6), (key3130, -6), (key3141, -6), (key3144, 6)]

theorem rowCheck1858 : row1858 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1858 := by decide +kernel

theorem rowEval1858 (x : Key → ℝ) : Integer.Sparse.eval row1858 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1858, Integer.Sparse.eval_collectBalanced, rawRowCheck1858]

def rawRow1859 : Integer.Sparse Key := [(key3043, -2), (key3043, -2), (key3144, -2), (key3043, 2), (key3043, 2), (key3141, 2), (key3038, 2), (key3038, 2), (key3130, 2), (key3038, -6), (key3033, -2), (key3033, -2), (key3120, -2), (key2414, 6)]

theorem rawRowCheck1859 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form6 = rawRow1859 := by decide +kernel

def row1859 : Integer.Sparse Key := [(key2414, 6), (key3033, -4), (key3038, -2), (key3120, -2), (key3130, 2), (key3141, 2), (key3144, -2)]

theorem rowCheck1859 : row1859 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1859 := by decide +kernel

theorem rowEval1859 (x : Key → ℝ) : Integer.Sparse.eval row1859 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1859, Integer.Sparse.eval_collectBalanced, rawRowCheck1859]

def rawRow1860 : Integer.Sparse Key := [(key3043, -2), (key3144, -2), (key3043, -2), (key3043, 2), (key3141, 2), (key3043, 2), (key3038, 2), (key3130, 2), (key3038, 2), (key3038, -6), (key3033, -2), (key3120, -2), (key3033, -2), (key3033, 6)]

theorem rawRowCheck1860 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form6 = rawRow1860 := by decide +kernel

def row1860 : Integer.Sparse Key := [(key3033, 2), (key3038, -2), (key3120, -2), (key3130, 2), (key3141, 2), (key3144, -2)]

theorem rowCheck1860 : row1860 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1860 := by decide +kernel

theorem rowEval1860 (x : Key → ℝ) : Integer.Sparse.eval row1860 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1860, Integer.Sparse.eval_collectBalanced, rawRowCheck1860]

def rawRow1861 : Integer.Sparse Key := [(key3144, -2), (key3043, -2), (key3043, -2), (key3141, 2), (key3043, 2), (key3043, 2), (key3130, 2), (key3038, 2), (key3038, 2), (key3038, -6), (key3120, -2), (key3033, -2), (key3033, -2), (key3033, 6)]

theorem rawRowCheck1861 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form6 = rawRow1861 := by decide +kernel

def row1861 : Integer.Sparse Key := [(key3033, 2), (key3038, -2), (key3120, -2), (key3130, 2), (key3141, 2), (key3144, -2)]

theorem rowCheck1861 : row1861 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1861 := by decide +kernel

theorem rowEval1861 (x : Key → ℝ) : Integer.Sparse.eval row1861 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form6) x := by
  rw [rowCheck1861, Integer.Sparse.eval_collectBalanced, rawRowCheck1861]

def rawRow1862 : Integer.Sparse Key := [(key1251, -2), (key1259, -2), (key1259, -2), (key1251, 1), (key1259, 1), (key1251, 1), (key1271, 1), (key1259, 1), (key1271, 1), (key1526, 2), (key1534, 2), (key1534, 2), (key1526, -1), (key1534, -1), (key1526, -1), (key1894, -1), (key1534, -1), (key1894, -1), (key1604, -1), (key1612, -1), (key1604, -1), (key1679, -1), (key1612, -1), (key1679, -1), (key1604, 1), (key1612, 1), (key1604, 1), (key1916, 1), (key1612, 1), (key1916, 1)]

theorem rawRowCheck1862 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form7 = rawRow1862 := by decide +kernel

def row1862 : Integer.Sparse Key := [(key1259, -2), (key1271, 2), (key1534, 2), (key1679, -2), (key1894, -2), (key1916, 2)]

theorem rowCheck1862 : row1862 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1862 := by decide +kernel

theorem rowEval1862 (x : Key → ℝ) : Integer.Sparse.eval row1862 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form7) x := by
  rw [rowCheck1862, Integer.Sparse.eval_collectBalanced, rawRowCheck1862]

def rawRow1863 : Integer.Sparse Key := [(key1259, -2), (key1251, -2), (key1259, -2), (key1259, 1), (key1251, 1), (key1271, 1), (key1251, 1), (key1271, 1), (key1259, 1), (key1534, 2), (key1526, 2), (key1534, 2), (key1534, -1), (key1526, -1), (key1894, -1), (key1526, -1), (key1894, -1), (key1534, -1), (key1612, -1), (key1604, -1), (key1679, -1), (key1604, -1), (key1679, -1), (key1612, -1), (key1612, 1), (key1604, 1), (key1916, 1), (key1604, 1), (key1916, 1), (key1612, 1)]

theorem rawRowCheck1863 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form7 = rawRow1863 := by decide +kernel

def row1863 : Integer.Sparse Key := [(key1259, -2), (key1271, 2), (key1534, 2), (key1679, -2), (key1894, -2), (key1916, 2)]

theorem rowCheck1863 : row1863 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1863 := by decide +kernel

theorem rowEval1863 (x : Key → ℝ) : Integer.Sparse.eval row1863 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1863, Integer.Sparse.eval_collectBalanced, rawRowCheck1863]

def rawRow1864 : Integer.Sparse Key := [(key1259, -2), (key1259, -2), (key1251, -2), (key1271, 1), (key1271, 1), (key1259, 1), (key1259, 1), (key1251, 1), (key1251, 1), (key1534, 2), (key1534, 2), (key1526, 2), (key1894, -1), (key1894, -1), (key1534, -1), (key1534, -1), (key1526, -1), (key1526, -1), (key1679, -1), (key1679, -1), (key1612, -1), (key1612, -1), (key1604, -1), (key1604, -1), (key1916, 1), (key1916, 1), (key1612, 1), (key1612, 1), (key1604, 1), (key1604, 1)]

theorem rawRowCheck1864 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form7 = rawRow1864 := by decide +kernel

def row1864 : Integer.Sparse Key := [(key1259, -2), (key1271, 2), (key1534, 2), (key1679, -2), (key1894, -2), (key1916, 2)]

theorem rowCheck1864 : row1864 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1864 := by decide +kernel

theorem rowEval1864 (x : Key → ℝ) : Integer.Sparse.eval row1864 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1864, Integer.Sparse.eval_collectBalanced, rawRowCheck1864]

def rawRow1865 : Integer.Sparse Key := [(key1271, -2), (key1271, -2), (key1271, -2), (key1259, 1), (key1259, 1), (key1259, 1), (key1259, 1), (key1259, 1), (key1259, 1), (key1894, 2), (key1894, 2), (key1894, 2), (key1534, -1), (key1534, -1), (key1534, -1), (key1534, -1), (key1534, -1), (key1534, -1), (key1916, -1), (key1916, -1), (key1916, -1), (key1916, -1), (key1916, -1), (key1916, -1), (key1679, 1), (key1679, 1), (key1679, 1), (key1679, 1), (key1679, 1), (key1679, 1)]

theorem rawRowCheck1865 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form7 = rawRow1865 := by decide +kernel

def row1865 : Integer.Sparse Key := [(key1259, 6), (key1271, -6), (key1534, -6), (key1679, 6), (key1894, 6), (key1916, -6)]

theorem rowCheck1865 : row1865 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1865 := by decide +kernel

theorem rowEval1865 (x : Key → ℝ) : Integer.Sparse.eval row1865 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1865, Integer.Sparse.eval_collectBalanced, rawRowCheck1865]

def rawRow1866 : Integer.Sparse Key := [(key1526, -2), (key1534, -2), (key1534, -2), (key1604, 1), (key1612, 1), (key1604, 1), (key1679, 1), (key1612, 1), (key1679, 1), (key1251, 2), (key1259, 2), (key1259, 2), (key1604, -1), (key1612, -1), (key1604, -1), (key1916, -1), (key1612, -1), (key1916, -1), (key1251, -1), (key1259, -1), (key1251, -1), (key1271, -1), (key1259, -1), (key1271, -1), (key1526, 1), (key1534, 1), (key1526, 1), (key1894, 1), (key1534, 1), (key1894, 1)]

theorem rawRowCheck1866 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form7 = rawRow1866 := by decide +kernel

def row1866 : Integer.Sparse Key := [(key1259, 2), (key1271, -2), (key1534, -2), (key1679, 2), (key1894, 2), (key1916, -2)]

theorem rowCheck1866 : row1866 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1866 := by decide +kernel

theorem rowEval1866 (x : Key → ℝ) : Integer.Sparse.eval row1866 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form7) x := by
  rw [rowCheck1866, Integer.Sparse.eval_collectBalanced, rawRowCheck1866]

def rawRow1867 : Integer.Sparse Key := [(key1534, -2), (key1526, -2), (key1534, -2), (key1612, 1), (key1604, 1), (key1679, 1), (key1604, 1), (key1679, 1), (key1612, 1), (key1259, 2), (key1251, 2), (key1259, 2), (key1612, -1), (key1604, -1), (key1916, -1), (key1604, -1), (key1916, -1), (key1612, -1), (key1259, -1), (key1251, -1), (key1271, -1), (key1251, -1), (key1271, -1), (key1259, -1), (key1534, 1), (key1526, 1), (key1894, 1), (key1526, 1), (key1894, 1), (key1534, 1)]

theorem rawRowCheck1867 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form7 = rawRow1867 := by decide +kernel

def row1867 : Integer.Sparse Key := [(key1259, 2), (key1271, -2), (key1534, -2), (key1679, 2), (key1894, 2), (key1916, -2)]

theorem rowCheck1867 : row1867 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1867 := by decide +kernel

theorem rowEval1867 (x : Key → ℝ) : Integer.Sparse.eval row1867 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1867, Integer.Sparse.eval_collectBalanced, rawRowCheck1867]

def rawRow1868 : Integer.Sparse Key := [(key1534, -2), (key1534, -2), (key1526, -2), (key1679, 1), (key1679, 1), (key1612, 1), (key1612, 1), (key1604, 1), (key1604, 1), (key1259, 2), (key1259, 2), (key1251, 2), (key1916, -1), (key1916, -1), (key1612, -1), (key1612, -1), (key1604, -1), (key1604, -1), (key1271, -1), (key1271, -1), (key1259, -1), (key1259, -1), (key1251, -1), (key1251, -1), (key1894, 1), (key1894, 1), (key1534, 1), (key1534, 1), (key1526, 1), (key1526, 1)]

theorem rawRowCheck1868 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form7 = rawRow1868 := by decide +kernel

def row1868 : Integer.Sparse Key := [(key1259, 2), (key1271, -2), (key1534, -2), (key1679, 2), (key1894, 2), (key1916, -2)]

theorem rowCheck1868 : row1868 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1868 := by decide +kernel

theorem rowEval1868 (x : Key → ℝ) : Integer.Sparse.eval row1868 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1868, Integer.Sparse.eval_collectBalanced, rawRowCheck1868]

def rawRow1869 : Integer.Sparse Key := [(key1679, -2), (key1679, -2), (key1693, -2), (key1534, 1), (key1534, 1), (key1612, 1), (key1612, 1), (key1640, 1), (key1640, 1), (key1916, 2), (key1916, 2), (key1930, 2), (key1259, -1), (key1259, -1), (key1612, -1), (key1612, -1), (key1640, -1), (key1640, -1), (key1894, -1), (key1894, -1), (key1916, -1), (key1916, -1), (key1930, -1), (key1930, -1), (key1271, 1), (key1271, 1), (key1679, 1), (key1679, 1), (key1693, 1), (key1693, 1)]

theorem rawRowCheck1869 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form7 = rawRow1869 := by decide +kernel

def row1869 : Integer.Sparse Key := [(key1259, -2), (key1271, 2), (key1534, 2), (key1679, -2), (key1894, -2), (key1916, 2)]

theorem rowCheck1869 : row1869 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1869 := by decide +kernel

theorem rowEval1869 (x : Key → ℝ) : Integer.Sparse.eval row1869 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1869, Integer.Sparse.eval_collectBalanced, rawRowCheck1869]

def rawRow1870 : Integer.Sparse Key := [(key1679, -2), (key1693, -2), (key1679, -2), (key1612, 1), (key1640, 1), (key1534, 1), (key1640, 1), (key1534, 1), (key1612, 1), (key1916, 2), (key1930, 2), (key1916, 2), (key1612, -1), (key1640, -1), (key1259, -1), (key1640, -1), (key1259, -1), (key1612, -1), (key1916, -1), (key1930, -1), (key1894, -1), (key1930, -1), (key1894, -1), (key1916, -1), (key1679, 1), (key1693, 1), (key1271, 1), (key1693, 1), (key1271, 1), (key1679, 1)]

theorem rawRowCheck1870 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form7 = rawRow1870 := by decide +kernel

def row1870 : Integer.Sparse Key := [(key1259, -2), (key1271, 2), (key1534, 2), (key1679, -2), (key1894, -2), (key1916, 2)]

theorem rowCheck1870 : row1870 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1870 := by decide +kernel

theorem rowEval1870 (x : Key → ℝ) : Integer.Sparse.eval row1870 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1870, Integer.Sparse.eval_collectBalanced, rawRowCheck1870]

def rawRow1871 : Integer.Sparse Key := [(key1693, -2), (key1679, -2), (key1679, -2), (key1640, 1), (key1612, 1), (key1640, 1), (key1534, 1), (key1612, 1), (key1534, 1), (key1930, 2), (key1916, 2), (key1916, 2), (key1640, -1), (key1612, -1), (key1640, -1), (key1259, -1), (key1612, -1), (key1259, -1), (key1930, -1), (key1916, -1), (key1930, -1), (key1894, -1), (key1916, -1), (key1894, -1), (key1693, 1), (key1679, 1), (key1693, 1), (key1271, 1), (key1679, 1), (key1271, 1)]

theorem rawRowCheck1871 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form7 = rawRow1871 := by decide +kernel

def row1871 : Integer.Sparse Key := [(key1259, -2), (key1271, 2), (key1534, 2), (key1679, -2), (key1894, -2), (key1916, 2)]

theorem rowCheck1871 : row1871 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1871 := by decide +kernel

theorem rowEval1871 (x : Key → ℝ) : Integer.Sparse.eval row1871 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form7) x := by
  rw [rowCheck1871, Integer.Sparse.eval_collectBalanced, rawRowCheck1871]

def rawRow1872 : Integer.Sparse Key := [(key1894, -2), (key1894, -2), (key1894, -2), (key1916, 1), (key1916, 1), (key1916, 1), (key1916, 1), (key1916, 1), (key1916, 1), (key1271, 2), (key1271, 2), (key1271, 2), (key1679, -1), (key1679, -1), (key1679, -1), (key1679, -1), (key1679, -1), (key1679, -1), (key1259, -1), (key1259, -1), (key1259, -1), (key1259, -1), (key1259, -1), (key1259, -1), (key1534, 1), (key1534, 1), (key1534, 1), (key1534, 1), (key1534, 1), (key1534, 1)]

theorem rawRowCheck1872 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form7 = rawRow1872 := by decide +kernel

def row1872 : Integer.Sparse Key := [(key1259, -6), (key1271, 6), (key1534, 6), (key1679, -6), (key1894, -6), (key1916, 6)]

theorem rowCheck1872 : row1872 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1872 := by decide +kernel

theorem rowEval1872 (x : Key → ℝ) : Integer.Sparse.eval row1872 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1872, Integer.Sparse.eval_collectBalanced, rawRowCheck1872]

def rawRow1873 : Integer.Sparse Key := [(key1916, -2), (key1916, -2), (key1930, -2), (key1894, 1), (key1894, 1), (key1916, 1), (key1916, 1), (key1930, 1), (key1930, 1), (key1679, 2), (key1679, 2), (key1693, 2), (key1271, -1), (key1271, -1), (key1679, -1), (key1679, -1), (key1693, -1), (key1693, -1), (key1534, -1), (key1534, -1), (key1612, -1), (key1612, -1), (key1640, -1), (key1640, -1), (key1259, 1), (key1259, 1), (key1612, 1), (key1612, 1), (key1640, 1), (key1640, 1)]

theorem rawRowCheck1873 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form7 = rawRow1873 := by decide +kernel

def row1873 : Integer.Sparse Key := [(key1259, 2), (key1271, -2), (key1534, -2), (key1679, 2), (key1894, 2), (key1916, -2)]

theorem rowCheck1873 : row1873 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1873 := by decide +kernel

theorem rowEval1873 (x : Key → ℝ) : Integer.Sparse.eval row1873 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1873, Integer.Sparse.eval_collectBalanced, rawRowCheck1873]

def rawRow1874 : Integer.Sparse Key := [(key1916, -2), (key1930, -2), (key1916, -2), (key1916, 1), (key1930, 1), (key1894, 1), (key1930, 1), (key1894, 1), (key1916, 1), (key1679, 2), (key1693, 2), (key1679, 2), (key1679, -1), (key1693, -1), (key1271, -1), (key1693, -1), (key1271, -1), (key1679, -1), (key1612, -1), (key1640, -1), (key1534, -1), (key1640, -1), (key1534, -1), (key1612, -1), (key1612, 1), (key1640, 1), (key1259, 1), (key1640, 1), (key1259, 1), (key1612, 1)]

theorem rawRowCheck1874 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form7 = rawRow1874 := by decide +kernel

def row1874 : Integer.Sparse Key := [(key1259, 2), (key1271, -2), (key1534, -2), (key1679, 2), (key1894, 2), (key1916, -2)]

theorem rowCheck1874 : row1874 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1874 := by decide +kernel

theorem rowEval1874 (x : Key → ℝ) : Integer.Sparse.eval row1874 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1874, Integer.Sparse.eval_collectBalanced, rawRowCheck1874]

def rawRow1875 : Integer.Sparse Key := [(key1930, -2), (key1916, -2), (key1916, -2), (key1930, 1), (key1916, 1), (key1930, 1), (key1894, 1), (key1916, 1), (key1894, 1), (key1693, 2), (key1679, 2), (key1679, 2), (key1693, -1), (key1679, -1), (key1693, -1), (key1271, -1), (key1679, -1), (key1271, -1), (key1640, -1), (key1612, -1), (key1640, -1), (key1534, -1), (key1612, -1), (key1534, -1), (key1640, 1), (key1612, 1), (key1640, 1), (key1259, 1), (key1612, 1), (key1259, 1)]

theorem rawRowCheck1875 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form7 = rawRow1875 := by decide +kernel

def row1875 : Integer.Sparse Key := [(key1259, 2), (key1271, -2), (key1534, -2), (key1679, 2), (key1894, 2), (key1916, -2)]

theorem rowCheck1875 : row1875 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1875 := by decide +kernel

theorem rowEval1875 (x : Key → ℝ) : Integer.Sparse.eval row1875 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form7) x := by
  rw [rowCheck1875, Integer.Sparse.eval_collectBalanced, rawRowCheck1875]

def rawRow1876 : Integer.Sparse Key := [(key972, -2), (key978, -2), (key978, -2), (key978, 6), (key1086, 2), (key1092, 2), (key1092, 2), (key1092, -2), (key1092, -2), (key1227, -2), (key1163, -6), (key1163, 2), (key1163, 2), (key1244, 2)]

theorem rawRowCheck1876 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form8 = rawRow1876 := by decide +kernel

def row1876 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1163, -2), (key1227, -2), (key1244, 2)]

theorem rowCheck1876 : row1876 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1876 := by decide +kernel

theorem rowEval1876 (x : Key → ℝ) : Integer.Sparse.eval row1876 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form8) x := by
  rw [rowCheck1876, Integer.Sparse.eval_collectBalanced, rawRowCheck1876]

def rawRow1877 : Integer.Sparse Key := [(key978, -2), (key972, -2), (key978, -2), (key978, 6), (key1092, 2), (key1086, 2), (key1092, 2), (key1092, -2), (key1227, -2), (key1092, -2), (key1163, -6), (key1163, 2), (key1244, 2), (key1163, 2)]

theorem rawRowCheck1877 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form8 = rawRow1877 := by decide +kernel

def row1877 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1163, -2), (key1227, -2), (key1244, 2)]

theorem rowCheck1877 : row1877 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1877 := by decide +kernel

theorem rowEval1877 (x : Key → ℝ) : Integer.Sparse.eval row1877 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1877, Integer.Sparse.eval_collectBalanced, rawRowCheck1877]

def rawRow1878 : Integer.Sparse Key := [(key978, -2), (key978, -2), (key972, -2), (key978, 6), (key1092, 2), (key1092, 2), (key1086, 2), (key1227, -2), (key1092, -2), (key1092, -2), (key1163, -6), (key1244, 2), (key1163, 2), (key1163, 2)]

theorem rawRowCheck1878 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form8 = rawRow1878 := by decide +kernel

def row1878 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1163, -2), (key1227, -2), (key1244, 2)]

theorem rowCheck1878 : row1878 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1878 := by decide +kernel

theorem rowEval1878 (x : Key → ℝ) : Integer.Sparse.eval row1878 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1878, Integer.Sparse.eval_collectBalanced, rawRowCheck1878]

def rawRow1879 : Integer.Sparse Key := [(key978, -2), (key978, -2), (key978, -2), (key972, 6), (key1227, 2), (key1227, 2), (key1227, 2), (key1086, -2), (key1086, -2), (key1086, -2), (key1244, -6), (key1163, 2), (key1163, 2), (key1163, 2)]

theorem rawRowCheck1879 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form8 = rawRow1879 := by decide +kernel

def row1879 : Integer.Sparse Key := [(key972, 6), (key978, -6), (key1086, -6), (key1163, 6), (key1227, 6), (key1244, -6)]

theorem rowCheck1879 : row1879 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1879 := by decide +kernel

theorem rowEval1879 (x : Key → ℝ) : Integer.Sparse.eval row1879 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1879, Integer.Sparse.eval_collectBalanced, rawRowCheck1879]

def rawRow1880 : Integer.Sparse Key := [(key1086, -2), (key1092, -2), (key1092, -2), (key1163, 6), (key972, 2), (key978, 2), (key978, 2), (key1163, -2), (key1163, -2), (key1244, -2), (key978, -6), (key1092, 2), (key1092, 2), (key1227, 2)]

theorem rawRowCheck1880 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form8 = rawRow1880 := by decide +kernel

def row1880 : Integer.Sparse Key := [(key972, 2), (key978, -2), (key1086, -2), (key1163, 2), (key1227, 2), (key1244, -2)]

theorem rowCheck1880 : row1880 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1880 := by decide +kernel

theorem rowEval1880 (x : Key → ℝ) : Integer.Sparse.eval row1880 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form8) x := by
  rw [rowCheck1880, Integer.Sparse.eval_collectBalanced, rawRowCheck1880]

def rawRow1881 : Integer.Sparse Key := [(key1092, -2), (key1086, -2), (key1092, -2), (key1163, 6), (key978, 2), (key972, 2), (key978, 2), (key1163, -2), (key1244, -2), (key1163, -2), (key978, -6), (key1092, 2), (key1227, 2), (key1092, 2)]

theorem rawRowCheck1881 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form8 = rawRow1881 := by decide +kernel

def row1881 : Integer.Sparse Key := [(key972, 2), (key978, -2), (key1086, -2), (key1163, 2), (key1227, 2), (key1244, -2)]

theorem rowCheck1881 : row1881 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1881 := by decide +kernel

theorem rowEval1881 (x : Key → ℝ) : Integer.Sparse.eval row1881 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1881, Integer.Sparse.eval_collectBalanced, rawRowCheck1881]

def rawRow1882 : Integer.Sparse Key := [(key1092, -2), (key1092, -2), (key1086, -2), (key1163, 6), (key978, 2), (key978, 2), (key972, 2), (key1244, -2), (key1163, -2), (key1163, -2), (key978, -6), (key1227, 2), (key1092, 2), (key1092, 2)]

theorem rawRowCheck1882 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form8 = rawRow1882 := by decide +kernel

def row1882 : Integer.Sparse Key := [(key972, 2), (key978, -2), (key1086, -2), (key1163, 2), (key1227, 2), (key1244, -2)]

theorem rowCheck1882 : row1882 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1882 := by decide +kernel

theorem rowEval1882 (x : Key → ℝ) : Integer.Sparse.eval row1882 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1882, Integer.Sparse.eval_collectBalanced, rawRowCheck1882]

def rawRow1883 : Integer.Sparse Key := [(key1092, -2), (key1092, -2), (key1163, -2), (key1086, 6), (key1227, 2), (key1227, 2), (key1244, 2), (key972, -2), (key1086, -2), (key1086, -2), (key1227, -6), (key978, 2), (key1092, 2), (key1092, 2)]

theorem rawRowCheck1883 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form8 = rawRow1883 := by decide +kernel

def row1883 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1163, -2), (key1227, -2), (key1244, 2)]

theorem rowCheck1883 : row1883 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1883 := by decide +kernel

theorem rowEval1883 (x : Key → ℝ) : Integer.Sparse.eval row1883 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1883, Integer.Sparse.eval_collectBalanced, rawRowCheck1883]

def rawRow1884 : Integer.Sparse Key := [(key1092, -2), (key1163, -2), (key1092, -2), (key1086, 6), (key1227, 2), (key1244, 2), (key1227, 2), (key1086, -2), (key972, -2), (key1086, -2), (key1227, -6), (key1092, 2), (key978, 2), (key1092, 2)]

theorem rawRowCheck1884 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form8 = rawRow1884 := by decide +kernel

def row1884 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1163, -2), (key1227, -2), (key1244, 2)]

theorem rowCheck1884 : row1884 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1884 := by decide +kernel

theorem rowEval1884 (x : Key → ℝ) : Integer.Sparse.eval row1884 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1884, Integer.Sparse.eval_collectBalanced, rawRowCheck1884]

def rawRow1885 : Integer.Sparse Key := [(key1163, -2), (key1092, -2), (key1092, -2), (key1086, 6), (key1244, 2), (key1227, 2), (key1227, 2), (key1086, -2), (key1086, -2), (key972, -2), (key1227, -6), (key1092, 2), (key1092, 2), (key978, 2)]

theorem rawRowCheck1885 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form8 = rawRow1885 := by decide +kernel

def row1885 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1163, -2), (key1227, -2), (key1244, 2)]

theorem rowCheck1885 : row1885 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1885 := by decide +kernel

theorem rowEval1885 (x : Key → ℝ) : Integer.Sparse.eval row1885 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form8) x := by
  rw [rowCheck1885, Integer.Sparse.eval_collectBalanced, rawRowCheck1885]

def rawRow1886 : Integer.Sparse Key := [(key1227, -2), (key1227, -2), (key1227, -2), (key1244, 6), (key978, 2), (key978, 2), (key978, 2), (key1163, -2), (key1163, -2), (key1163, -2), (key972, -6), (key1086, 2), (key1086, 2), (key1086, 2)]

theorem rawRowCheck1886 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form8 = rawRow1886 := by decide +kernel

def row1886 : Integer.Sparse Key := [(key972, -6), (key978, 6), (key1086, 6), (key1163, -6), (key1227, -6), (key1244, 6)]

theorem rowCheck1886 : row1886 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1886 := by decide +kernel

theorem rowEval1886 (x : Key → ℝ) : Integer.Sparse.eval row1886 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1886, Integer.Sparse.eval_collectBalanced, rawRowCheck1886]

def rawRow1887 : Integer.Sparse Key := [(key1227, -2), (key1227, -2), (key1244, -2), (key1227, 6), (key1092, 2), (key1092, 2), (key1163, 2), (key978, -2), (key1092, -2), (key1092, -2), (key1086, -6), (key972, 2), (key1086, 2), (key1086, 2)]

theorem rawRowCheck1887 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form8 = rawRow1887 := by decide +kernel

def row1887 : Integer.Sparse Key := [(key972, 2), (key978, -2), (key1086, -2), (key1163, 2), (key1227, 2), (key1244, -2)]

theorem rowCheck1887 : row1887 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1887 := by decide +kernel

theorem rowEval1887 (x : Key → ℝ) : Integer.Sparse.eval row1887 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1887, Integer.Sparse.eval_collectBalanced, rawRowCheck1887]

def rawRow1888 : Integer.Sparse Key := [(key1227, -2), (key1244, -2), (key1227, -2), (key1227, 6), (key1092, 2), (key1163, 2), (key1092, 2), (key1092, -2), (key978, -2), (key1092, -2), (key1086, -6), (key1086, 2), (key972, 2), (key1086, 2)]

theorem rawRowCheck1888 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form8 = rawRow1888 := by decide +kernel

def row1888 : Integer.Sparse Key := [(key972, 2), (key978, -2), (key1086, -2), (key1163, 2), (key1227, 2), (key1244, -2)]

theorem rowCheck1888 : row1888 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1888 := by decide +kernel

theorem rowEval1888 (x : Key → ℝ) : Integer.Sparse.eval row1888 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1888, Integer.Sparse.eval_collectBalanced, rawRowCheck1888]

def rawRow1889 : Integer.Sparse Key := [(key1244, -2), (key1227, -2), (key1227, -2), (key1227, 6), (key1163, 2), (key1092, 2), (key1092, 2), (key1092, -2), (key1092, -2), (key978, -2), (key1086, -6), (key1086, 2), (key1086, 2), (key972, 2)]

theorem rawRowCheck1889 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form8 = rawRow1889 := by decide +kernel

def row1889 : Integer.Sparse Key := [(key972, 2), (key978, -2), (key1086, -2), (key1163, 2), (key1227, 2), (key1244, -2)]

theorem rowCheck1889 : row1889 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1889 := by decide +kernel

theorem rowEval1889 (x : Key → ℝ) : Integer.Sparse.eval row1889 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form8) x := by
  rw [rowCheck1889, Integer.Sparse.eval_collectBalanced, rawRowCheck1889]

def rawRow1890 : Integer.Sparse Key := [(key2374, -2), (key2374, -2), (key2391, -2), (key2374, 1), (key2380, 1), (key2374, 1), (key2391, 1), (key2380, 1), (key2391, 1), (key2468, 2), (key2468, 2), (key2481, 2), (key2468, -1), (key2481, -1), (key2468, -1), (key2505, -1), (key2481, -1), (key2505, -1), (key2535, -1), (key2537, -1), (key2535, -1), (key2542, -1), (key2537, -1), (key2542, -1), (key2535, 1), (key2542, 1), (key2535, 1), (key2553, 1), (key2542, 1), (key2553, 1)]

theorem rawRowCheck1890 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form9 = rawRow1890 := by decide +kernel

def row1890 : Integer.Sparse Key := [(key2374, -2), (key2380, 2), (key2468, 2), (key2505, -2), (key2537, -2), (key2553, 2)]

theorem rowCheck1890 : row1890 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1890 := by decide +kernel

theorem rowEval1890 (x : Key → ℝ) : Integer.Sparse.eval row1890 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form9) x := by
  rw [rowCheck1890, Integer.Sparse.eval_collectBalanced, rawRowCheck1890]

def rawRow1891 : Integer.Sparse Key := [(key2374, -2), (key2391, -2), (key2374, -2), (key2380, 1), (key2374, 1), (key2391, 1), (key2374, 1), (key2391, 1), (key2380, 1), (key2468, 2), (key2481, 2), (key2468, 2), (key2481, -1), (key2468, -1), (key2505, -1), (key2468, -1), (key2505, -1), (key2481, -1), (key2537, -1), (key2535, -1), (key2542, -1), (key2535, -1), (key2542, -1), (key2537, -1), (key2542, 1), (key2535, 1), (key2553, 1), (key2535, 1), (key2553, 1), (key2542, 1)]

theorem rawRowCheck1891 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form9 = rawRow1891 := by decide +kernel

def row1891 : Integer.Sparse Key := [(key2374, -2), (key2380, 2), (key2468, 2), (key2505, -2), (key2537, -2), (key2553, 2)]

theorem rowCheck1891 : row1891 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1891 := by decide +kernel

theorem rowEval1891 (x : Key → ℝ) : Integer.Sparse.eval row1891 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck1891, Integer.Sparse.eval_collectBalanced, rawRowCheck1891]

def rawRow1892 : Integer.Sparse Key := [(key2391, -2), (key2374, -2), (key2374, -2), (key2391, 1), (key2391, 1), (key2380, 1), (key2380, 1), (key2374, 1), (key2374, 1), (key2481, 2), (key2468, 2), (key2468, 2), (key2505, -1), (key2505, -1), (key2481, -1), (key2481, -1), (key2468, -1), (key2468, -1), (key2542, -1), (key2542, -1), (key2537, -1), (key2537, -1), (key2535, -1), (key2535, -1), (key2553, 1), (key2553, 1), (key2542, 1), (key2542, 1), (key2535, 1), (key2535, 1)]

theorem rawRowCheck1892 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form9 = rawRow1892 := by decide +kernel

def row1892 : Integer.Sparse Key := [(key2374, -2), (key2380, 2), (key2468, 2), (key2505, -2), (key2537, -2), (key2553, 2)]

theorem rowCheck1892 : row1892 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1892 := by decide +kernel

theorem rowEval1892 (x : Key → ℝ) : Integer.Sparse.eval row1892 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck1892, Integer.Sparse.eval_collectBalanced, rawRowCheck1892]

def rawRow1893 : Integer.Sparse Key := [(key2380, -2), (key2380, -2), (key2380, -2), (key2374, 1), (key2374, 1), (key2374, 1), (key2374, 1), (key2374, 1), (key2374, 1), (key2505, 2), (key2505, 2), (key2505, 2), (key2468, -1), (key2468, -1), (key2468, -1), (key2468, -1), (key2468, -1), (key2468, -1), (key2553, -1), (key2553, -1), (key2553, -1), (key2553, -1), (key2553, -1), (key2553, -1), (key2537, 1), (key2537, 1), (key2537, 1), (key2537, 1), (key2537, 1), (key2537, 1)]

theorem rawRowCheck1893 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form9 = rawRow1893 := by decide +kernel

def row1893 : Integer.Sparse Key := [(key2374, 6), (key2380, -6), (key2468, -6), (key2505, 6), (key2537, 6), (key2553, -6)]

theorem rowCheck1893 : row1893 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1893 := by decide +kernel

theorem rowEval1893 (x : Key → ℝ) : Integer.Sparse.eval row1893 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck1893, Integer.Sparse.eval_collectBalanced, rawRowCheck1893]

def rawRow1894 : Integer.Sparse Key := [(key2847, -2), (key2847, -2), (key2917, -2), (key2878, 1), (key2884, 1), (key2878, 1), (key2926, 1), (key2884, 1), (key2926, 1), (key2374, 2), (key2374, 2), (key2391, 2), (key2535, -1), (key2542, -1), (key2535, -1), (key2553, -1), (key2542, -1), (key2553, -1), (key2374, -1), (key2380, -1), (key2374, -1), (key2391, -1), (key2380, -1), (key2391, -1), (key2468, 1), (key2481, 1), (key2468, 1), (key2505, 1), (key2481, 1), (key2505, 1)]

theorem rawRowCheck1894 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form9 = rawRow1894 := by decide +kernel

def row1894 : Integer.Sparse Key := [(key2374, 2), (key2380, -2), (key2468, 2), (key2481, 2), (key2505, 2), (key2535, -2), (key2542, -2), (key2553, -2), (key2847, -4), (key2878, 2), (key2884, 2), (key2917, -2), (key2926, 2)]

theorem rowCheck1894 : row1894 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1894 := by decide +kernel

theorem rowEval1894 (x : Key → ℝ) : Integer.Sparse.eval row1894 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form9) x := by
  rw [rowCheck1894, Integer.Sparse.eval_collectBalanced, rawRowCheck1894]

def rawRow1895 : Integer.Sparse Key := [(key2847, -2), (key2917, -2), (key2847, -2), (key2884, 1), (key2878, 1), (key2926, 1), (key2878, 1), (key2926, 1), (key2884, 1), (key2374, 2), (key2391, 2), (key2374, 2), (key2542, -1), (key2535, -1), (key2553, -1), (key2535, -1), (key2553, -1), (key2542, -1), (key2380, -1), (key2374, -1), (key2391, -1), (key2374, -1), (key2391, -1), (key2380, -1), (key2481, 1), (key2468, 1), (key2505, 1), (key2468, 1), (key2505, 1), (key2481, 1)]

theorem rawRowCheck1895 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form9 = rawRow1895 := by decide +kernel

def row1895 : Integer.Sparse Key := [(key2374, 2), (key2380, -2), (key2468, 2), (key2481, 2), (key2505, 2), (key2535, -2), (key2542, -2), (key2553, -2), (key2847, -4), (key2878, 2), (key2884, 2), (key2917, -2), (key2926, 2)]

theorem rowCheck1895 : row1895 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1895 := by decide +kernel

theorem rowEval1895 (x : Key → ℝ) : Integer.Sparse.eval row1895 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck1895, Integer.Sparse.eval_collectBalanced, rawRowCheck1895]

def rawRow1896 : Integer.Sparse Key := [(key2917, -2), (key2847, -2), (key2847, -2), (key2926, 1), (key2926, 1), (key2884, 1), (key2884, 1), (key2878, 1), (key2878, 1), (key2391, 2), (key2374, 2), (key2374, 2), (key2553, -1), (key2553, -1), (key2542, -1), (key2542, -1), (key2535, -1), (key2535, -1), (key2391, -1), (key2391, -1), (key2380, -1), (key2380, -1), (key2374, -1), (key2374, -1), (key2505, 1), (key2505, 1), (key2481, 1), (key2481, 1), (key2468, 1), (key2468, 1)]

theorem rawRowCheck1896 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form9 = rawRow1896 := by decide +kernel

def row1896 : Integer.Sparse Key := [(key2374, 2), (key2380, -2), (key2468, 2), (key2481, 2), (key2505, 2), (key2535, -2), (key2542, -2), (key2553, -2), (key2847, -4), (key2878, 2), (key2884, 2), (key2917, -2), (key2926, 2)]

theorem rowCheck1896 : row1896 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1896 := by decide +kernel

theorem rowEval1896 (x : Key → ℝ) : Integer.Sparse.eval row1896 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck1896, Integer.Sparse.eval_collectBalanced, rawRowCheck1896]

def rawRow1897 : Integer.Sparse Key := [(key2775, -2), (key2884, -2), (key2884, -2), (key2770, 1), (key2770, 1), (key2847, 1), (key2847, 1), (key2878, 1), (key2878, 1), (key3006, 2), (key3029, 2), (key3029, 2), (key2591, -1), (key2591, -1), (key2770, -1), (key2770, -1), (key2878, -1), (key2878, -1), (key2439, -1), (key2439, -1), (key2505, -1), (key2505, -1), (key2553, -1), (key2553, -1), (key2380, 1), (key2380, 1), (key2408, 1), (key2408, 1), (key2537, 1), (key2537, 1)]

theorem rawRowCheck1897 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form9 = rawRow1897 := by decide +kernel

def row1897 : Integer.Sparse Key := [(key2380, 2), (key2408, 2), (key2439, -2), (key2505, -2), (key2537, 2), (key2553, -2), (key2591, -2), (key2775, -2), (key2847, 2), (key2884, -4), (key3006, 2), (key3029, 4)]

theorem rowCheck1897 : row1897 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1897 := by decide +kernel

theorem rowEval1897 (x : Key → ℝ) : Integer.Sparse.eval row1897 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck1897, Integer.Sparse.eval_collectBalanced, rawRowCheck1897]

def rawRow1898 : Integer.Sparse Key := [(key2884, -2), (key2775, -2), (key2884, -2), (key2847, 1), (key2878, 1), (key2770, 1), (key2878, 1), (key2770, 1), (key2847, 1), (key3029, 2), (key3006, 2), (key3029, 2), (key2770, -1), (key2878, -1), (key2591, -1), (key2878, -1), (key2591, -1), (key2770, -1), (key2505, -1), (key2553, -1), (key2439, -1), (key2553, -1), (key2439, -1), (key2505, -1), (key2408, 1), (key2537, 1), (key2380, 1), (key2537, 1), (key2380, 1), (key2408, 1)]

theorem rawRowCheck1898 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form9 = rawRow1898 := by decide +kernel

def row1898 : Integer.Sparse Key := [(key2380, 2), (key2408, 2), (key2439, -2), (key2505, -2), (key2537, 2), (key2553, -2), (key2591, -2), (key2775, -2), (key2847, 2), (key2884, -4), (key3006, 2), (key3029, 4)]

theorem rowCheck1898 : row1898 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1898 := by decide +kernel

theorem rowEval1898 (x : Key → ℝ) : Integer.Sparse.eval row1898 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck1898, Integer.Sparse.eval_collectBalanced, rawRowCheck1898]

def rawRow1899 : Integer.Sparse Key := [(key2884, -2), (key2884, -2), (key2775, -2), (key2878, 1), (key2847, 1), (key2878, 1), (key2770, 1), (key2847, 1), (key2770, 1), (key3029, 2), (key3029, 2), (key3006, 2), (key2878, -1), (key2770, -1), (key2878, -1), (key2591, -1), (key2770, -1), (key2591, -1), (key2553, -1), (key2505, -1), (key2553, -1), (key2439, -1), (key2505, -1), (key2439, -1), (key2537, 1), (key2408, 1), (key2537, 1), (key2380, 1), (key2408, 1), (key2380, 1)]

theorem rawRowCheck1899 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form9 = rawRow1899 := by decide +kernel

def row1899 : Integer.Sparse Key := [(key2380, 2), (key2408, 2), (key2439, -2), (key2505, -2), (key2537, 2), (key2553, -2), (key2591, -2), (key2775, -2), (key2847, 2), (key2884, -4), (key3006, 2), (key3029, 4)]

theorem rowCheck1899 : row1899 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1899 := by decide +kernel

theorem rowEval1899 (x : Key → ℝ) : Integer.Sparse.eval row1899 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form9) x := by
  rw [rowCheck1899, Integer.Sparse.eval_collectBalanced, rawRowCheck1899]

def rawRow1900 : Integer.Sparse Key := [(key3020, -2), (key3020, -2), (key3020, -2), (key3029, 1), (key3029, 1), (key3029, 1), (key3029, 1), (key3029, 1), (key3029, 1), (key2596, 2), (key2596, 2), (key2596, 2), (key2884, -1), (key2884, -1), (key2884, -1), (key2884, -1), (key2884, -1), (key2884, -1), (key2591, -1), (key2591, -1), (key2591, -1), (key2591, -1), (key2591, -1), (key2591, -1), (key2847, 1), (key2847, 1), (key2847, 1), (key2847, 1), (key2847, 1), (key2847, 1)]

theorem rawRowCheck1900 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form9 = rawRow1900 := by decide +kernel

def row1900 : Integer.Sparse Key := [(key2591, -6), (key2596, 6), (key2847, 6), (key2884, -6), (key3020, -6), (key3029, 6)]

theorem rowCheck1900 : row1900 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1900 := by decide +kernel

theorem rowEval1900 (x : Key → ℝ) : Integer.Sparse.eval row1900 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck1900, Integer.Sparse.eval_collectBalanced, rawRowCheck1900]

def rawRow1901 : Integer.Sparse Key := [(key3006, -2), (key3029, -2), (key3029, -2), (key3006, 1), (key3006, 1), (key3020, 1), (key3020, 1), (key3029, 1), (key3029, 1), (key2775, 2), (key2884, 2), (key2884, 2), (key2596, -1), (key2596, -1), (key2775, -1), (key2775, -1), (key2884, -1), (key2884, -1), (key2770, -1), (key2770, -1), (key2847, -1), (key2847, -1), (key2878, -1), (key2878, -1), (key2591, 1), (key2591, 1), (key2770, 1), (key2770, 1), (key2878, 1), (key2878, 1)]

theorem rawRowCheck1901 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form9 = rawRow1901 := by decide +kernel

def row1901 : Integer.Sparse Key := [(key2591, 2), (key2596, -2), (key2847, -2), (key2884, 2), (key3020, 2), (key3029, -2)]

theorem rowCheck1901 : row1901 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1901 := by decide +kernel

theorem rowEval1901 (x : Key → ℝ) : Integer.Sparse.eval row1901 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck1901, Integer.Sparse.eval_collectBalanced, rawRowCheck1901]

def rawRow1902 : Integer.Sparse Key := [(key3029, -2), (key3006, -2), (key3029, -2), (key3020, 1), (key3029, 1), (key3006, 1), (key3029, 1), (key3006, 1), (key3020, 1), (key2884, 2), (key2775, 2), (key2884, 2), (key2775, -1), (key2884, -1), (key2596, -1), (key2884, -1), (key2596, -1), (key2775, -1), (key2847, -1), (key2878, -1), (key2770, -1), (key2878, -1), (key2770, -1), (key2847, -1), (key2770, 1), (key2878, 1), (key2591, 1), (key2878, 1), (key2591, 1), (key2770, 1)]

theorem rawRowCheck1902 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form9 = rawRow1902 := by decide +kernel

def row1902 : Integer.Sparse Key := [(key2591, 2), (key2596, -2), (key2847, -2), (key2884, 2), (key3020, 2), (key3029, -2)]

theorem rowCheck1902 : row1902 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1902 := by decide +kernel

theorem rowEval1902 (x : Key → ℝ) : Integer.Sparse.eval row1902 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck1902, Integer.Sparse.eval_collectBalanced, rawRowCheck1902]

def rawRow1903 : Integer.Sparse Key := [(key3029, -2), (key3029, -2), (key3006, -2), (key3029, 1), (key3020, 1), (key3029, 1), (key3006, 1), (key3020, 1), (key3006, 1), (key2884, 2), (key2884, 2), (key2775, 2), (key2884, -1), (key2775, -1), (key2884, -1), (key2596, -1), (key2775, -1), (key2596, -1), (key2878, -1), (key2847, -1), (key2878, -1), (key2770, -1), (key2847, -1), (key2770, -1), (key2878, 1), (key2770, 1), (key2878, 1), (key2591, 1), (key2770, 1), (key2591, 1)]

theorem rawRowCheck1903 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form9 = rawRow1903 := by decide +kernel

def row1903 : Integer.Sparse Key := [(key2591, 2), (key2596, -2), (key2847, -2), (key2884, 2), (key3020, 2), (key3029, -2)]

theorem rowCheck1903 : row1903 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1903 := by decide +kernel

theorem rowEval1903 (x : Key → ℝ) : Integer.Sparse.eval row1903 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form9) x := by
  rw [rowCheck1903, Integer.Sparse.eval_collectBalanced, rawRowCheck1903]

def rawRow1904 : Integer.Sparse Key := [(key2353, -2), (key2359, -2), (key2359, -2), (key2359, 6), (key2448, 2), (key2454, 2), (key2454, 2), (key2454, -2), (key2454, -2), (key2515, -2), (key2566, -6), (key2566, 2), (key2566, 2), (key2578, 2)]

theorem rawRowCheck1904 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form10 = rawRow1904 := by decide +kernel

def row1904 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2515, -2), (key2566, -2), (key2578, 2)]

theorem rowCheck1904 : row1904 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1904 := by decide +kernel

theorem rowEval1904 (x : Key → ℝ) : Integer.Sparse.eval row1904 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form10) x := by
  rw [rowCheck1904, Integer.Sparse.eval_collectBalanced, rawRowCheck1904]

def rawRow1905 : Integer.Sparse Key := [(key2359, -2), (key2353, -2), (key2359, -2), (key2359, 6), (key2454, 2), (key2448, 2), (key2454, 2), (key2454, -2), (key2515, -2), (key2454, -2), (key2566, -6), (key2566, 2), (key2578, 2), (key2566, 2)]

theorem rawRowCheck1905 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form10 = rawRow1905 := by decide +kernel

def row1905 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2515, -2), (key2566, -2), (key2578, 2)]

theorem rowCheck1905 : row1905 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1905 := by decide +kernel

theorem rowEval1905 (x : Key → ℝ) : Integer.Sparse.eval row1905 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck1905, Integer.Sparse.eval_collectBalanced, rawRowCheck1905]

def rawRow1906 : Integer.Sparse Key := [(key2359, -2), (key2359, -2), (key2353, -2), (key2359, 6), (key2454, 2), (key2454, 2), (key2448, 2), (key2515, -2), (key2454, -2), (key2454, -2), (key2566, -6), (key2578, 2), (key2566, 2), (key2566, 2)]

theorem rawRowCheck1906 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form10 = rawRow1906 := by decide +kernel

def row1906 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2515, -2), (key2566, -2), (key2578, 2)]

theorem rowCheck1906 : row1906 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1906 := by decide +kernel

theorem rowEval1906 (x : Key → ℝ) : Integer.Sparse.eval row1906 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck1906, Integer.Sparse.eval_collectBalanced, rawRowCheck1906]

def rawRow1907 : Integer.Sparse Key := [(key2359, -2), (key2359, -2), (key2359, -2), (key2353, 6), (key2515, 2), (key2515, 2), (key2515, 2), (key2448, -2), (key2448, -2), (key2448, -2), (key2578, -6), (key2566, 2), (key2566, 2), (key2566, 2)]

theorem rawRowCheck1907 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form10 = rawRow1907 := by decide +kernel

def row1907 : Integer.Sparse Key := [(key2353, 6), (key2359, -6), (key2448, -6), (key2515, 6), (key2566, 6), (key2578, -6)]

theorem rowCheck1907 : row1907 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1907 := by decide +kernel

theorem rowEval1907 (x : Key → ℝ) : Integer.Sparse.eval row1907 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck1907, Integer.Sparse.eval_collectBalanced, rawRowCheck1907]

def rawRow1908 : Integer.Sparse Key := [(key2448, -2), (key2454, -2), (key2454, -2), (key2515, 6), (key2353, 2), (key2359, 2), (key2359, 2), (key2566, -2), (key2566, -2), (key2578, -2), (key2359, -6), (key2454, 2), (key2454, 2), (key2515, 2)]

theorem rawRowCheck1908 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form10 = rawRow1908 := by decide +kernel

def row1908 : Integer.Sparse Key := [(key2353, 2), (key2359, -2), (key2448, -2), (key2515, 8), (key2566, -4), (key2578, -2)]

theorem rowCheck1908 : row1908 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1908 := by decide +kernel

theorem rowEval1908 (x : Key → ℝ) : Integer.Sparse.eval row1908 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form10) x := by
  rw [rowCheck1908, Integer.Sparse.eval_collectBalanced, rawRowCheck1908]

def rawRow1909 : Integer.Sparse Key := [(key2454, -2), (key2448, -2), (key2454, -2), (key2515, 6), (key2359, 2), (key2353, 2), (key2359, 2), (key2566, -2), (key2578, -2), (key2566, -2), (key2359, -6), (key2454, 2), (key2515, 2), (key2454, 2)]

theorem rawRowCheck1909 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form10 = rawRow1909 := by decide +kernel

def row1909 : Integer.Sparse Key := [(key2353, 2), (key2359, -2), (key2448, -2), (key2515, 8), (key2566, -4), (key2578, -2)]

theorem rowCheck1909 : row1909 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1909 := by decide +kernel

theorem rowEval1909 (x : Key → ℝ) : Integer.Sparse.eval row1909 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck1909, Integer.Sparse.eval_collectBalanced, rawRowCheck1909]

def rawRow1910 : Integer.Sparse Key := [(key2454, -2), (key2454, -2), (key2448, -2), (key2515, 6), (key2359, 2), (key2359, 2), (key2353, 2), (key2578, -2), (key2566, -2), (key2566, -2), (key2359, -6), (key2515, 2), (key2454, 2), (key2454, 2)]

theorem rawRowCheck1910 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form10 = rawRow1910 := by decide +kernel

def row1910 : Integer.Sparse Key := [(key2353, 2), (key2359, -2), (key2448, -2), (key2515, 8), (key2566, -4), (key2578, -2)]

theorem rowCheck1910 : row1910 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1910 := by decide +kernel

theorem rowEval1910 (x : Key → ℝ) : Integer.Sparse.eval row1910 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck1910, Integer.Sparse.eval_collectBalanced, rawRowCheck1910]

def rawRow1911 : Integer.Sparse Key := [(key2454, -2), (key2454, -2), (key2515, -2), (key2448, 6), (key2566, 2), (key2566, 2), (key2578, 2), (key2353, -2), (key2448, -2), (key2448, -2), (key2515, -6), (key2359, 2), (key2454, 2), (key2454, 2)]

theorem rawRowCheck1911 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form10 = rawRow1911 := by decide +kernel

def row1911 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2515, -8), (key2566, 4), (key2578, 2)]

theorem rowCheck1911 : row1911 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1911 := by decide +kernel

theorem rowEval1911 (x : Key → ℝ) : Integer.Sparse.eval row1911 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck1911, Integer.Sparse.eval_collectBalanced, rawRowCheck1911]

def rawRow1912 : Integer.Sparse Key := [(key2454, -2), (key2515, -2), (key2454, -2), (key2448, 6), (key2566, 2), (key2578, 2), (key2566, 2), (key2448, -2), (key2353, -2), (key2448, -2), (key2515, -6), (key2454, 2), (key2359, 2), (key2454, 2)]

theorem rawRowCheck1912 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form10 = rawRow1912 := by decide +kernel

def row1912 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2515, -8), (key2566, 4), (key2578, 2)]

theorem rowCheck1912 : row1912 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1912 := by decide +kernel

theorem rowEval1912 (x : Key → ℝ) : Integer.Sparse.eval row1912 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck1912, Integer.Sparse.eval_collectBalanced, rawRowCheck1912]

def rawRow1913 : Integer.Sparse Key := [(key2515, -2), (key2454, -2), (key2454, -2), (key2448, 6), (key2578, 2), (key2566, 2), (key2566, 2), (key2448, -2), (key2448, -2), (key2353, -2), (key2515, -6), (key2454, 2), (key2454, 2), (key2359, 2)]

theorem rawRowCheck1913 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form10 = rawRow1913 := by decide +kernel

def row1913 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2515, -8), (key2566, 4), (key2578, 2)]

theorem rowCheck1913 : row1913 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1913 := by decide +kernel

theorem rowEval1913 (x : Key → ℝ) : Integer.Sparse.eval row1913 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form10) x := by
  rw [rowCheck1913, Integer.Sparse.eval_collectBalanced, rawRowCheck1913]

def rawRow1914 : Integer.Sparse Key := [(key2566, -2), (key2566, -2), (key2566, -2), (key2578, 6), (key2359, 2), (key2359, 2), (key2359, 2), (key2515, -2), (key2515, -2), (key2515, -2), (key2353, -6), (key2448, 2), (key2448, 2), (key2448, 2)]

theorem rawRowCheck1914 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form10 = rawRow1914 := by decide +kernel

def row1914 : Integer.Sparse Key := [(key2353, -6), (key2359, 6), (key2448, 6), (key2515, -6), (key2566, -6), (key2578, 6)]

theorem rowCheck1914 : row1914 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1914 := by decide +kernel

theorem rowEval1914 (x : Key → ℝ) : Integer.Sparse.eval row1914 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck1914, Integer.Sparse.eval_collectBalanced, rawRowCheck1914]

def rawRow1915 : Integer.Sparse Key := [(key2566, -2), (key2566, -2), (key2578, -2), (key2566, 6), (key2454, 2), (key2454, 2), (key2515, 2), (key2359, -2), (key2454, -2), (key2454, -2), (key2448, -6), (key2353, 2), (key2448, 2), (key2448, 2)]

theorem rawRowCheck1915 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form10 = rawRow1915 := by decide +kernel

def row1915 : Integer.Sparse Key := [(key2353, 2), (key2359, -2), (key2448, -2), (key2515, 2), (key2566, 2), (key2578, -2)]

theorem rowCheck1915 : row1915 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1915 := by decide +kernel

theorem rowEval1915 (x : Key → ℝ) : Integer.Sparse.eval row1915 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck1915, Integer.Sparse.eval_collectBalanced, rawRowCheck1915]

def rawRow1916 : Integer.Sparse Key := [(key2566, -2), (key2578, -2), (key2566, -2), (key2566, 6), (key2454, 2), (key2515, 2), (key2454, 2), (key2454, -2), (key2359, -2), (key2454, -2), (key2448, -6), (key2448, 2), (key2353, 2), (key2448, 2)]

theorem rawRowCheck1916 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form10 = rawRow1916 := by decide +kernel

def row1916 : Integer.Sparse Key := [(key2353, 2), (key2359, -2), (key2448, -2), (key2515, 2), (key2566, 2), (key2578, -2)]

theorem rowCheck1916 : row1916 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1916 := by decide +kernel

theorem rowEval1916 (x : Key → ℝ) : Integer.Sparse.eval row1916 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck1916, Integer.Sparse.eval_collectBalanced, rawRowCheck1916]

def rawRow1917 : Integer.Sparse Key := [(key2578, -2), (key2566, -2), (key2566, -2), (key2566, 6), (key2515, 2), (key2454, 2), (key2454, 2), (key2454, -2), (key2454, -2), (key2359, -2), (key2448, -6), (key2448, 2), (key2448, 2), (key2353, 2)]

theorem rawRowCheck1917 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form10 = rawRow1917 := by decide +kernel

def row1917 : Integer.Sparse Key := [(key2353, 2), (key2359, -2), (key2448, -2), (key2515, 2), (key2566, 2), (key2578, -2)]

theorem rowCheck1917 : row1917 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1917 := by decide +kernel

theorem rowEval1917 (x : Key → ℝ) : Integer.Sparse.eval row1917 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form10) x := by
  rw [rowCheck1917, Integer.Sparse.eval_collectBalanced, rawRowCheck1917]

def rawRow1918 : Integer.Sparse Key := [(key2770, -2), (key2770, -2), (key2932, -2), (key2770, 1), (key2773, 1), (key2770, 1), (key2932, 1), (key2773, 1), (key2932, 1), (key2847, 2), (key2847, 2), (key2969, 2), (key2847, -1), (key2890, -1), (key2847, -1), (key2969, -1), (key2890, -1), (key2969, -1), (key2878, -1), (key2881, -1), (key2878, -1), (key2990, -1), (key2881, -1), (key2990, -1), (key2878, 1), (key2911, 1), (key2878, 1), (key2990, 1), (key2911, 1), (key2990, 1)]

theorem rawRowCheck1918 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form0 = rawRow1918 := by decide +kernel

def row1918 : Integer.Sparse Key := [(key2770, -2), (key2773, 2), (key2847, 2), (key2881, -2), (key2890, -2), (key2911, 2)]

theorem rowCheck1918 : row1918 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1918 := by decide +kernel

theorem rowEval1918 (x : Key → ℝ) : Integer.Sparse.eval row1918 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1918, Integer.Sparse.eval_collectBalanced, rawRowCheck1918]

def rawRow1919 : Integer.Sparse Key := [(key2770, -2), (key2932, -2), (key2770, -2), (key2773, 1), (key2770, 1), (key2932, 1), (key2770, 1), (key2932, 1), (key2773, 1), (key2847, 2), (key2969, 2), (key2847, 2), (key2890, -1), (key2847, -1), (key2969, -1), (key2847, -1), (key2969, -1), (key2890, -1), (key2881, -1), (key2878, -1), (key2990, -1), (key2878, -1), (key2990, -1), (key2881, -1), (key2911, 1), (key2878, 1), (key2990, 1), (key2878, 1), (key2990, 1), (key2911, 1)]

theorem rawRowCheck1919 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form0 = rawRow1919 := by decide +kernel

def row1919 : Integer.Sparse Key := [(key2770, -2), (key2773, 2), (key2847, 2), (key2881, -2), (key2890, -2), (key2911, 2)]

theorem rowCheck1919 : row1919 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1919 := by decide +kernel

theorem rowEval1919 (x : Key → ℝ) : Integer.Sparse.eval row1919 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1919, Integer.Sparse.eval_collectBalanced, rawRowCheck1919]

end MUB6.Certificate.GramRows

end OAI
