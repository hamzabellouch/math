import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block6
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block16
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block17
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow7168 : Integer.Sparse Key := [(key2178, -2), (key2180, 1), (key2180, 1), (key2178, -2), (key2190, 1), (key2190, 1), (key2180, 1), (key2180, 1), (key2190, 1), (key2190, 1), (key2192, -2), (key2192, -2), (key2278, 2), (key2282, -1), (key2282, -1), (key2278, 2), (key2290, -1), (key2290, -1), (key2282, -1), (key2282, -1), (key2290, -1), (key2290, -1), (key2298, 2), (key2298, 2), (key2329, -1), (key2329, -1), (key2331, 1), (key2331, 1), (key2329, -1), (key2329, -1), (key2335, 1), (key2335, 1), (key2331, 1), (key2331, 1), (key2339, -1), (key2339, -1), (key2335, 1), (key2335, 1), (key2339, -1), (key2339, -1)]

theorem rawRowCheck7168 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form5 = rawRow7168 := by decide +kernel

def row7168 : Integer.Sparse Key := [(key2178, -4), (key2180, 4), (key2190, 4), (key2192, -4), (key2278, 4), (key2282, -4), (key2290, -4), (key2298, 4), (key2329, -4), (key2331, 4), (key2335, 4), (key2339, -4)]

theorem rowCheck7168 : row7168 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7168 := by decide +kernel

theorem rowEval7168 (x : Key → ℝ) : Integer.Sparse.eval row7168 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck7168, Integer.Sparse.eval_collectBalanced, rawRowCheck7168]

def rawRow7169 : Integer.Sparse Key := [(key2180, -2), (key2178, 1), (key2180, 1), (key2190, -2), (key2178, 1), (key2190, 1), (key2190, 1), (key2192, 1), (key2180, 1), (key2192, 1), (key2180, -2), (key2190, -2), (key2282, 2), (key2278, -1), (key2282, -1), (key2290, 2), (key2278, -1), (key2290, -1), (key2290, -1), (key2298, -1), (key2282, -1), (key2298, -1), (key2282, 2), (key2290, 2), (key2331, -1), (key2332, -1), (key2329, 1), (key2332, 1), (key2334, -1), (key2335, -1), (key2329, 1), (key2334, 1), (key2334, 1), (key2339, 1), (key2331, -1), (key2334, -1), (key2332, 1), (key2339, 1), (key2332, -1), (key2335, -1)]

theorem rawRowCheck7169 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form5 = rawRow7169 := by decide +kernel

def row7169 : Integer.Sparse Key := [(key2178, 2), (key2180, -2), (key2190, -2), (key2192, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2331, -2), (key2335, -2), (key2339, 2)]

theorem rowCheck7169 : row7169 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7169 := by decide +kernel

theorem rowEval7169 (x : Key → ℝ) : Integer.Sparse.eval row7169 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck7169, Integer.Sparse.eval_collectBalanced, rawRowCheck7169]

def rawRow7170 : Integer.Sparse Key := [(key2180, -2), (key2180, 1), (key2178, 1), (key2190, -2), (key2190, 1), (key2178, 1), (key2192, 1), (key2190, 1), (key2192, 1), (key2180, 1), (key2190, -2), (key2180, -2), (key2282, 2), (key2282, -1), (key2278, -1), (key2290, 2), (key2290, -1), (key2278, -1), (key2298, -1), (key2290, -1), (key2298, -1), (key2282, -1), (key2290, 2), (key2282, 2), (key2332, -1), (key2331, -1), (key2332, 1), (key2329, 1), (key2335, -1), (key2334, -1), (key2334, 1), (key2329, 1), (key2339, 1), (key2334, 1), (key2334, -1), (key2331, -1), (key2339, 1), (key2332, 1), (key2335, -1), (key2332, -1)]

theorem rawRowCheck7170 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form5 = rawRow7170 := by decide +kernel

def row7170 : Integer.Sparse Key := [(key2178, 2), (key2180, -2), (key2190, -2), (key2192, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2331, -2), (key2335, -2), (key2339, 2)]

theorem rowCheck7170 : row7170 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7170 := by decide +kernel

theorem rowEval7170 (x : Key → ℝ) : Integer.Sparse.eval row7170 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck7170, Integer.Sparse.eval_collectBalanced, rawRowCheck7170]

def rawRow7171 : Integer.Sparse Key := [(key2190, -2), (key2190, 1), (key2192, 1), (key2180, -2), (key2180, 1), (key2192, 1), (key2178, 1), (key2180, 1), (key2178, 1), (key2190, 1), (key2180, -2), (key2190, -2), (key2290, 2), (key2290, -1), (key2298, -1), (key2282, 2), (key2282, -1), (key2298, -1), (key2278, -1), (key2282, -1), (key2278, -1), (key2290, -1), (key2282, 2), (key2290, 2), (key2334, -1), (key2335, -1), (key2334, 1), (key2339, 1), (key2331, -1), (key2332, -1), (key2332, 1), (key2339, 1), (key2329, 1), (key2332, 1), (key2332, -1), (key2335, -1), (key2329, 1), (key2334, 1), (key2331, -1), (key2334, -1)]

theorem rawRowCheck7171 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form5 = rawRow7171 := by decide +kernel

def row7171 : Integer.Sparse Key := [(key2178, 2), (key2180, -2), (key2190, -2), (key2192, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2331, -2), (key2335, -2), (key2339, 2)]

theorem rowCheck7171 : row7171 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7171 := by decide +kernel

theorem rowEval7171 (x : Key → ℝ) : Integer.Sparse.eval row7171 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck7171, Integer.Sparse.eval_collectBalanced, rawRowCheck7171]

def rawRow7172 : Integer.Sparse Key := [(key2190, -2), (key2192, 1), (key2190, 1), (key2180, -2), (key2192, 1), (key2180, 1), (key2180, 1), (key2178, 1), (key2190, 1), (key2178, 1), (key2190, -2), (key2180, -2), (key2290, 2), (key2298, -1), (key2290, -1), (key2282, 2), (key2298, -1), (key2282, -1), (key2282, -1), (key2278, -1), (key2290, -1), (key2278, -1), (key2290, 2), (key2282, 2), (key2335, -1), (key2334, -1), (key2339, 1), (key2334, 1), (key2332, -1), (key2331, -1), (key2339, 1), (key2332, 1), (key2332, 1), (key2329, 1), (key2335, -1), (key2332, -1), (key2334, 1), (key2329, 1), (key2334, -1), (key2331, -1)]

theorem rawRowCheck7172 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form5 = rawRow7172 := by decide +kernel

def row7172 : Integer.Sparse Key := [(key2178, 2), (key2180, -2), (key2190, -2), (key2192, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2331, -2), (key2335, -2), (key2339, 2)]

theorem rowCheck7172 : row7172 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7172 := by decide +kernel

theorem rowEval7172 (x : Key → ℝ) : Integer.Sparse.eval row7172 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck7172, Integer.Sparse.eval_collectBalanced, rawRowCheck7172]

def rawRow7173 : Integer.Sparse Key := [(key2192, -2), (key2190, 1), (key2190, 1), (key2192, -2), (key2180, 1), (key2180, 1), (key2190, 1), (key2190, 1), (key2180, 1), (key2180, 1), (key2178, -2), (key2178, -2), (key2298, 2), (key2290, -1), (key2290, -1), (key2298, 2), (key2282, -1), (key2282, -1), (key2290, -1), (key2290, -1), (key2282, -1), (key2282, -1), (key2278, 2), (key2278, 2), (key2339, -1), (key2339, -1), (key2335, 1), (key2335, 1), (key2339, -1), (key2339, -1), (key2331, 1), (key2331, 1), (key2335, 1), (key2335, 1), (key2329, -1), (key2329, -1), (key2331, 1), (key2331, 1), (key2329, -1), (key2329, -1)]

theorem rawRowCheck7173 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form5 = rawRow7173 := by decide +kernel

def row7173 : Integer.Sparse Key := [(key2178, -4), (key2180, 4), (key2190, 4), (key2192, -4), (key2278, 4), (key2282, -4), (key2290, -4), (key2298, 4), (key2329, -4), (key2331, 4), (key2335, 4), (key2339, -4)]

theorem rowCheck7173 : row7173 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7173 := by decide +kernel

theorem rowEval7173 (x : Key → ℝ) : Integer.Sparse.eval row7173 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck7173, Integer.Sparse.eval_collectBalanced, rawRowCheck7173]

def rawRow7174 : Integer.Sparse Key := [(key2081, -2), (key2083, 1), (key2083, 1), (key2278, -2), (key2290, 1), (key2290, 1), (key2329, 1), (key2329, 1), (key2334, 1), (key2334, 1), (key2335, -2), (key2335, -2), (key2081, 2), (key2088, -1), (key2088, -1), (key2178, 2), (key2190, -1), (key2190, -1), (key2331, -1), (key2331, -1), (key2334, -1), (key2334, -1), (key2339, 2), (key2339, 2), (key2083, -1), (key2083, -1), (key2088, 1), (key2088, 1), (key2180, -1), (key2180, -1), (key2192, 1), (key2192, 1), (key2282, 1), (key2282, 1), (key2298, -1), (key2298, -1), (key2335, 1), (key2335, 1), (key2339, -1), (key2339, -1)]

theorem rawRowCheck7174 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form5 = rawRow7174 := by decide +kernel

def row7174 : Integer.Sparse Key := [(key2178, 2), (key2180, -2), (key2190, -2), (key2192, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2331, -2), (key2335, -2), (key2339, 2)]

theorem rowCheck7174 : row7174 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7174 := by decide +kernel

theorem rowEval7174 (x : Key → ℝ) : Integer.Sparse.eval row7174 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck7174, Integer.Sparse.eval_collectBalanced, rawRowCheck7174]

def rawRow7175 : Integer.Sparse Key := [(key2083, -2), (key2081, 1), (key2083, 1), (key2290, -2), (key2278, 1), (key2290, 1), (key2334, 1), (key2335, 1), (key2329, 1), (key2335, 1), (key2329, -2), (key2334, -2), (key2088, 2), (key2081, -1), (key2088, -1), (key2190, 2), (key2178, -1), (key2190, -1), (key2334, -1), (key2339, -1), (key2331, -1), (key2339, -1), (key2331, 2), (key2334, 2), (key2088, -1), (key2090, -1), (key2083, 1), (key2090, 1), (key2190, -1), (key2192, -1), (key2180, 1), (key2190, 1), (key2290, 1), (key2298, 1), (key2282, -1), (key2290, -1), (key2332, 1), (key2339, 1), (key2332, -1), (key2335, -1)]

theorem rawRowCheck7175 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form5 = rawRow7175 := by decide +kernel

def row7175 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

theorem rowCheck7175 : row7175 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7175 := by decide +kernel

theorem rowEval7175 (x : Key → ℝ) : Integer.Sparse.eval row7175 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck7175, Integer.Sparse.eval_collectBalanced, rawRowCheck7175]

def rawRow7176 : Integer.Sparse Key := [(key2083, -2), (key2083, 1), (key2081, 1), (key2290, -2), (key2290, 1), (key2278, 1), (key2335, 1), (key2334, 1), (key2335, 1), (key2329, 1), (key2334, -2), (key2329, -2), (key2088, 2), (key2088, -1), (key2081, -1), (key2190, 2), (key2190, -1), (key2178, -1), (key2339, -1), (key2334, -1), (key2339, -1), (key2331, -1), (key2334, 2), (key2331, 2), (key2090, -1), (key2088, -1), (key2090, 1), (key2083, 1), (key2192, -1), (key2190, -1), (key2190, 1), (key2180, 1), (key2298, 1), (key2290, 1), (key2290, -1), (key2282, -1), (key2339, 1), (key2332, 1), (key2335, -1), (key2332, -1)]

theorem rawRowCheck7176 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form5 = rawRow7176 := by decide +kernel

def row7176 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

theorem rowCheck7176 : row7176 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7176 := by decide +kernel

theorem rowEval7176 (x : Key → ℝ) : Integer.Sparse.eval row7176 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck7176, Integer.Sparse.eval_collectBalanced, rawRowCheck7176]

def rawRow7177 : Integer.Sparse Key := [(key2278, -2), (key2329, 1), (key2329, 1), (key2081, -2), (key2334, 1), (key2334, 1), (key2083, 1), (key2083, 1), (key2290, 1), (key2290, 1), (key2335, -2), (key2335, -2), (key2178, 2), (key2331, -1), (key2331, -1), (key2081, 2), (key2334, -1), (key2334, -1), (key2088, -1), (key2088, -1), (key2190, -1), (key2190, -1), (key2339, 2), (key2339, 2), (key2180, -1), (key2180, -1), (key2282, 1), (key2282, 1), (key2083, -1), (key2083, -1), (key2335, 1), (key2335, 1), (key2088, 1), (key2088, 1), (key2339, -1), (key2339, -1), (key2192, 1), (key2192, 1), (key2298, -1), (key2298, -1)]

theorem rawRowCheck7177 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form5 = rawRow7177 := by decide +kernel

def row7177 : Integer.Sparse Key := [(key2178, 2), (key2180, -2), (key2190, -2), (key2192, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2331, -2), (key2335, -2), (key2339, 2)]

theorem rowCheck7177 : row7177 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7177 := by decide +kernel

theorem rowEval7177 (x : Key → ℝ) : Integer.Sparse.eval row7177 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck7177, Integer.Sparse.eval_collectBalanced, rawRowCheck7177]

def rawRow7178 : Integer.Sparse Key := [(key2329, -2), (key2278, 1), (key2329, 1), (key2334, -2), (key2081, 1), (key2334, 1), (key2290, 1), (key2335, 1), (key2083, 1), (key2335, 1), (key2083, -2), (key2290, -2), (key2331, 2), (key2178, -1), (key2331, -1), (key2334, 2), (key2081, -1), (key2334, -1), (key2190, -1), (key2339, -1), (key2088, -1), (key2339, -1), (key2088, 2), (key2190, 2), (key2282, -1), (key2332, -1), (key2180, 1), (key2332, 1), (key2290, -1), (key2335, -1), (key2083, 1), (key2290, 1), (key2190, 1), (key2339, 1), (key2088, -1), (key2190, -1), (key2090, 1), (key2298, 1), (key2090, -1), (key2192, -1)]

theorem rawRowCheck7178 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form5 = rawRow7178 := by decide +kernel

def row7178 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

theorem rowCheck7178 : row7178 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7178 := by decide +kernel

theorem rowEval7178 (x : Key → ℝ) : Integer.Sparse.eval row7178 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck7178, Integer.Sparse.eval_collectBalanced, rawRowCheck7178]

def rawRow7179 : Integer.Sparse Key := [(key2329, -2), (key2329, 1), (key2278, 1), (key2334, -2), (key2334, 1), (key2081, 1), (key2335, 1), (key2290, 1), (key2335, 1), (key2083, 1), (key2290, -2), (key2083, -2), (key2331, 2), (key2331, -1), (key2178, -1), (key2334, 2), (key2334, -1), (key2081, -1), (key2339, -1), (key2190, -1), (key2339, -1), (key2088, -1), (key2190, 2), (key2088, 2), (key2332, -1), (key2282, -1), (key2332, 1), (key2180, 1), (key2335, -1), (key2290, -1), (key2290, 1), (key2083, 1), (key2339, 1), (key2190, 1), (key2190, -1), (key2088, -1), (key2298, 1), (key2090, 1), (key2192, -1), (key2090, -1)]

theorem rawRowCheck7179 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form5 = rawRow7179 := by decide +kernel

def row7179 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

theorem rowCheck7179 : row7179 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7179 := by decide +kernel

theorem rowEval7179 (x : Key → ℝ) : Integer.Sparse.eval row7179 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck7179, Integer.Sparse.eval_collectBalanced, rawRowCheck7179]

def rawRow7180 : Integer.Sparse Key := [(key2290, -2), (key2334, 1), (key2335, 1), (key2083, -2), (key2329, 1), (key2335, 1), (key2081, 1), (key2083, 1), (key2278, 1), (key2290, 1), (key2329, -2), (key2334, -2), (key2190, 2), (key2334, -1), (key2339, -1), (key2088, 2), (key2331, -1), (key2339, -1), (key2081, -1), (key2088, -1), (key2178, -1), (key2190, -1), (key2331, 2), (key2334, 2), (key2190, -1), (key2192, -1), (key2290, 1), (key2298, 1), (key2088, -1), (key2090, -1), (key2332, 1), (key2339, 1), (key2083, 1), (key2090, 1), (key2332, -1), (key2335, -1), (key2180, 1), (key2190, 1), (key2282, -1), (key2290, -1)]

theorem rawRowCheck7180 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form5 = rawRow7180 := by decide +kernel

def row7180 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

theorem rowCheck7180 : row7180 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7180 := by decide +kernel

theorem rowEval7180 (x : Key → ℝ) : Integer.Sparse.eval row7180 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck7180, Integer.Sparse.eval_collectBalanced, rawRowCheck7180]

def rawRow7181 : Integer.Sparse Key := [(key2290, -2), (key2335, 1), (key2334, 1), (key2083, -2), (key2335, 1), (key2329, 1), (key2083, 1), (key2081, 1), (key2290, 1), (key2278, 1), (key2334, -2), (key2329, -2), (key2190, 2), (key2339, -1), (key2334, -1), (key2088, 2), (key2339, -1), (key2331, -1), (key2088, -1), (key2081, -1), (key2190, -1), (key2178, -1), (key2334, 2), (key2331, 2), (key2192, -1), (key2190, -1), (key2298, 1), (key2290, 1), (key2090, -1), (key2088, -1), (key2339, 1), (key2332, 1), (key2090, 1), (key2083, 1), (key2335, -1), (key2332, -1), (key2190, 1), (key2180, 1), (key2290, -1), (key2282, -1)]

theorem rawRowCheck7181 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form5 = rawRow7181 := by decide +kernel

def row7181 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

theorem rowCheck7181 : row7181 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7181 := by decide +kernel

theorem rowEval7181 (x : Key → ℝ) : Integer.Sparse.eval row7181 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck7181, Integer.Sparse.eval_collectBalanced, rawRowCheck7181]

def rawRow7182 : Integer.Sparse Key := [(key2334, -2), (key2290, 1), (key2335, 1), (key2329, -2), (key2083, 1), (key2335, 1), (key2278, 1), (key2329, 1), (key2081, 1), (key2334, 1), (key2083, -2), (key2290, -2), (key2334, 2), (key2190, -1), (key2339, -1), (key2331, 2), (key2088, -1), (key2339, -1), (key2178, -1), (key2331, -1), (key2081, -1), (key2334, -1), (key2088, 2), (key2190, 2), (key2290, -1), (key2335, -1), (key2190, 1), (key2339, 1), (key2282, -1), (key2332, -1), (key2090, 1), (key2298, 1), (key2180, 1), (key2332, 1), (key2090, -1), (key2192, -1), (key2083, 1), (key2290, 1), (key2088, -1), (key2190, -1)]

theorem rawRowCheck7182 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form5 = rawRow7182 := by decide +kernel

def row7182 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

theorem rowCheck7182 : row7182 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7182 := by decide +kernel

theorem rowEval7182 (x : Key → ℝ) : Integer.Sparse.eval row7182 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck7182, Integer.Sparse.eval_collectBalanced, rawRowCheck7182]

def rawRow7183 : Integer.Sparse Key := [(key2334, -2), (key2335, 1), (key2290, 1), (key2329, -2), (key2335, 1), (key2083, 1), (key2329, 1), (key2278, 1), (key2334, 1), (key2081, 1), (key2290, -2), (key2083, -2), (key2334, 2), (key2339, -1), (key2190, -1), (key2331, 2), (key2339, -1), (key2088, -1), (key2331, -1), (key2178, -1), (key2334, -1), (key2081, -1), (key2190, 2), (key2088, 2), (key2335, -1), (key2290, -1), (key2339, 1), (key2190, 1), (key2332, -1), (key2282, -1), (key2298, 1), (key2090, 1), (key2332, 1), (key2180, 1), (key2192, -1), (key2090, -1), (key2290, 1), (key2083, 1), (key2190, -1), (key2088, -1)]

theorem rawRowCheck7183 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form5 = rawRow7183 := by decide +kernel

def row7183 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

theorem rowCheck7183 : row7183 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7183 := by decide +kernel

theorem rowEval7183 (x : Key → ℝ) : Integer.Sparse.eval row7183 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck7183, Integer.Sparse.eval_collectBalanced, rawRowCheck7183]

def rawRow7184 : Integer.Sparse Key := [(key2335, -2), (key2290, 1), (key2334, 1), (key2335, -2), (key2083, 1), (key2329, 1), (key2290, 1), (key2334, 1), (key2083, 1), (key2329, 1), (key2081, -2), (key2278, -2), (key2339, 2), (key2190, -1), (key2334, -1), (key2339, 2), (key2088, -1), (key2331, -1), (key2190, -1), (key2334, -1), (key2088, -1), (key2331, -1), (key2081, 2), (key2178, 2), (key2298, -1), (key2339, -1), (key2192, 1), (key2335, 1), (key2298, -1), (key2339, -1), (key2088, 1), (key2282, 1), (key2192, 1), (key2335, 1), (key2083, -1), (key2180, -1), (key2088, 1), (key2282, 1), (key2083, -1), (key2180, -1)]

theorem rawRowCheck7184 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form5 = rawRow7184 := by decide +kernel

def row7184 : Integer.Sparse Key := [(key2178, 2), (key2180, -2), (key2190, -2), (key2192, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2331, -2), (key2335, -2), (key2339, 2)]

theorem rowCheck7184 : row7184 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7184 := by decide +kernel

theorem rowEval7184 (x : Key → ℝ) : Integer.Sparse.eval row7184 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck7184, Integer.Sparse.eval_collectBalanced, rawRowCheck7184]

def rawRow7185 : Integer.Sparse Key := [(key2335, -2), (key2334, 1), (key2290, 1), (key2335, -2), (key2329, 1), (key2083, 1), (key2334, 1), (key2290, 1), (key2329, 1), (key2083, 1), (key2278, -2), (key2081, -2), (key2339, 2), (key2334, -1), (key2190, -1), (key2339, 2), (key2331, -1), (key2088, -1), (key2334, -1), (key2190, -1), (key2331, -1), (key2088, -1), (key2178, 2), (key2081, 2), (key2339, -1), (key2298, -1), (key2335, 1), (key2192, 1), (key2339, -1), (key2298, -1), (key2282, 1), (key2088, 1), (key2335, 1), (key2192, 1), (key2180, -1), (key2083, -1), (key2282, 1), (key2088, 1), (key2180, -1), (key2083, -1)]

theorem rawRowCheck7185 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form5 = rawRow7185 := by decide +kernel

def row7185 : Integer.Sparse Key := [(key2178, 2), (key2180, -2), (key2190, -2), (key2192, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2331, -2), (key2335, -2), (key2339, 2)]

theorem rowCheck7185 : row7185 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7185 := by decide +kernel

theorem rowEval7185 (x : Key → ℝ) : Integer.Sparse.eval row7185 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck7185, Integer.Sparse.eval_collectBalanced, rawRowCheck7185]

def rawRow7186 : Integer.Sparse Key := [(key2088, -2), (key2088, 1), (key2090, 1), (key2282, -2), (key2282, 1), (key2298, 1), (key2331, 1), (key2332, 1), (key2331, 1), (key2339, 1), (key2332, -2), (key2339, -2), (key2083, 2), (key2083, -1), (key2090, -1), (key2180, 2), (key2180, -1), (key2192, -1), (key2329, -1), (key2332, -1), (key2329, -1), (key2335, -1), (key2332, 2), (key2335, 2), (key2081, -1), (key2083, -1), (key2081, 1), (key2088, 1), (key2178, -1), (key2180, -1), (key2180, 1), (key2190, 1), (key2278, 1), (key2282, 1), (key2282, -1), (key2290, -1), (key2329, 1), (key2334, 1), (key2331, -1), (key2334, -1)]

theorem rawRowCheck7186 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form5 = rawRow7186 := by decide +kernel

def row7186 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

theorem rowCheck7186 : row7186 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7186 := by decide +kernel

theorem rowEval7186 (x : Key → ℝ) : Integer.Sparse.eval row7186 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck7186, Integer.Sparse.eval_collectBalanced, rawRowCheck7186]

def rawRow7187 : Integer.Sparse Key := [(key2088, -2), (key2090, 1), (key2088, 1), (key2282, -2), (key2298, 1), (key2282, 1), (key2332, 1), (key2331, 1), (key2339, 1), (key2331, 1), (key2339, -2), (key2332, -2), (key2083, 2), (key2090, -1), (key2083, -1), (key2180, 2), (key2192, -1), (key2180, -1), (key2332, -1), (key2329, -1), (key2335, -1), (key2329, -1), (key2335, 2), (key2332, 2), (key2083, -1), (key2081, -1), (key2088, 1), (key2081, 1), (key2180, -1), (key2178, -1), (key2190, 1), (key2180, 1), (key2282, 1), (key2278, 1), (key2290, -1), (key2282, -1), (key2334, 1), (key2329, 1), (key2334, -1), (key2331, -1)]

theorem rawRowCheck7187 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form5 = rawRow7187 := by decide +kernel

def row7187 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

theorem rowCheck7187 : row7187 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7187 := by decide +kernel

theorem rowEval7187 (x : Key → ℝ) : Integer.Sparse.eval row7187 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck7187, Integer.Sparse.eval_collectBalanced, rawRowCheck7187]

def rawRow7188 : Integer.Sparse Key := [(key2090, -2), (key2088, 1), (key2088, 1), (key2298, -2), (key2282, 1), (key2282, 1), (key2339, 1), (key2339, 1), (key2332, 1), (key2332, 1), (key2331, -2), (key2331, -2), (key2090, 2), (key2083, -1), (key2083, -1), (key2192, 2), (key2180, -1), (key2180, -1), (key2335, -1), (key2335, -1), (key2332, -1), (key2332, -1), (key2329, 2), (key2329, 2), (key2088, -1), (key2088, -1), (key2083, 1), (key2083, 1), (key2190, -1), (key2190, -1), (key2178, 1), (key2178, 1), (key2290, 1), (key2290, 1), (key2278, -1), (key2278, -1), (key2331, 1), (key2331, 1), (key2329, -1), (key2329, -1)]

theorem rawRowCheck7188 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form5 = rawRow7188 := by decide +kernel

def row7188 : Integer.Sparse Key := [(key2178, 2), (key2180, -2), (key2190, -2), (key2192, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2331, -2), (key2335, -2), (key2339, 2)]

theorem rowCheck7188 : row7188 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7188 := by decide +kernel

theorem rowEval7188 (x : Key → ℝ) : Integer.Sparse.eval row7188 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck7188, Integer.Sparse.eval_collectBalanced, rawRowCheck7188]

def rawRow7189 : Integer.Sparse Key := [(key2282, -2), (key2331, 1), (key2332, 1), (key2088, -2), (key2331, 1), (key2339, 1), (key2088, 1), (key2090, 1), (key2282, 1), (key2298, 1), (key2332, -2), (key2339, -2), (key2180, 2), (key2329, -1), (key2332, -1), (key2083, 2), (key2329, -1), (key2335, -1), (key2083, -1), (key2090, -1), (key2180, -1), (key2192, -1), (key2332, 2), (key2335, 2), (key2178, -1), (key2180, -1), (key2278, 1), (key2282, 1), (key2081, -1), (key2083, -1), (key2329, 1), (key2334, 1), (key2081, 1), (key2088, 1), (key2331, -1), (key2334, -1), (key2180, 1), (key2190, 1), (key2282, -1), (key2290, -1)]

theorem rawRowCheck7189 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form5 = rawRow7189 := by decide +kernel

def row7189 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

theorem rowCheck7189 : row7189 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7189 := by decide +kernel

theorem rowEval7189 (x : Key → ℝ) : Integer.Sparse.eval row7189 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck7189, Integer.Sparse.eval_collectBalanced, rawRowCheck7189]

def rawRow7190 : Integer.Sparse Key := [(key2282, -2), (key2332, 1), (key2331, 1), (key2088, -2), (key2339, 1), (key2331, 1), (key2090, 1), (key2088, 1), (key2298, 1), (key2282, 1), (key2339, -2), (key2332, -2), (key2180, 2), (key2332, -1), (key2329, -1), (key2083, 2), (key2335, -1), (key2329, -1), (key2090, -1), (key2083, -1), (key2192, -1), (key2180, -1), (key2335, 2), (key2332, 2), (key2180, -1), (key2178, -1), (key2282, 1), (key2278, 1), (key2083, -1), (key2081, -1), (key2334, 1), (key2329, 1), (key2088, 1), (key2081, 1), (key2334, -1), (key2331, -1), (key2190, 1), (key2180, 1), (key2290, -1), (key2282, -1)]

theorem rawRowCheck7190 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form5 = rawRow7190 := by decide +kernel

def row7190 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

theorem rowCheck7190 : row7190 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7190 := by decide +kernel

theorem rowEval7190 (x : Key → ℝ) : Integer.Sparse.eval row7190 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck7190, Integer.Sparse.eval_collectBalanced, rawRowCheck7190]

def rawRow7191 : Integer.Sparse Key := [(key2331, -2), (key2282, 1), (key2332, 1), (key2331, -2), (key2088, 1), (key2339, 1), (key2282, 1), (key2332, 1), (key2088, 1), (key2339, 1), (key2090, -2), (key2298, -2), (key2329, 2), (key2180, -1), (key2332, -1), (key2329, 2), (key2083, -1), (key2335, -1), (key2180, -1), (key2332, -1), (key2083, -1), (key2335, -1), (key2090, 2), (key2192, 2), (key2278, -1), (key2329, -1), (key2178, 1), (key2331, 1), (key2278, -1), (key2329, -1), (key2083, 1), (key2290, 1), (key2178, 1), (key2331, 1), (key2088, -1), (key2190, -1), (key2083, 1), (key2290, 1), (key2088, -1), (key2190, -1)]

theorem rawRowCheck7191 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form5 = rawRow7191 := by decide +kernel

def row7191 : Integer.Sparse Key := [(key2178, 2), (key2180, -2), (key2190, -2), (key2192, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2331, -2), (key2335, -2), (key2339, 2)]

theorem rowCheck7191 : row7191 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7191 := by decide +kernel

theorem rowEval7191 (x : Key → ℝ) : Integer.Sparse.eval row7191 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck7191, Integer.Sparse.eval_collectBalanced, rawRowCheck7191]

def rawRow7192 : Integer.Sparse Key := [(key2331, -2), (key2332, 1), (key2282, 1), (key2331, -2), (key2339, 1), (key2088, 1), (key2332, 1), (key2282, 1), (key2339, 1), (key2088, 1), (key2298, -2), (key2090, -2), (key2329, 2), (key2332, -1), (key2180, -1), (key2329, 2), (key2335, -1), (key2083, -1), (key2332, -1), (key2180, -1), (key2335, -1), (key2083, -1), (key2192, 2), (key2090, 2), (key2329, -1), (key2278, -1), (key2331, 1), (key2178, 1), (key2329, -1), (key2278, -1), (key2290, 1), (key2083, 1), (key2331, 1), (key2178, 1), (key2190, -1), (key2088, -1), (key2290, 1), (key2083, 1), (key2190, -1), (key2088, -1)]

theorem rawRowCheck7192 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form5 = rawRow7192 := by decide +kernel

def row7192 : Integer.Sparse Key := [(key2178, 2), (key2180, -2), (key2190, -2), (key2192, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2331, -2), (key2335, -2), (key2339, 2)]

theorem rowCheck7192 : row7192 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7192 := by decide +kernel

theorem rowEval7192 (x : Key → ℝ) : Integer.Sparse.eval row7192 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck7192, Integer.Sparse.eval_collectBalanced, rawRowCheck7192]

def rawRow7193 : Integer.Sparse Key := [(key2332, -2), (key2282, 1), (key2331, 1), (key2339, -2), (key2088, 1), (key2331, 1), (key2298, 1), (key2339, 1), (key2090, 1), (key2332, 1), (key2088, -2), (key2282, -2), (key2332, 2), (key2180, -1), (key2329, -1), (key2335, 2), (key2083, -1), (key2329, -1), (key2192, -1), (key2335, -1), (key2090, -1), (key2332, -1), (key2083, 2), (key2180, 2), (key2282, -1), (key2331, -1), (key2180, 1), (key2329, 1), (key2290, -1), (key2334, -1), (key2081, 1), (key2278, 1), (key2190, 1), (key2334, 1), (key2081, -1), (key2178, -1), (key2088, 1), (key2282, 1), (key2083, -1), (key2180, -1)]

theorem rawRowCheck7193 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form5 = rawRow7193 := by decide +kernel

def row7193 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

theorem rowCheck7193 : row7193 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7193 := by decide +kernel

theorem rowEval7193 (x : Key → ℝ) : Integer.Sparse.eval row7193 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck7193, Integer.Sparse.eval_collectBalanced, rawRowCheck7193]

def rawRow7194 : Integer.Sparse Key := [(key2332, -2), (key2331, 1), (key2282, 1), (key2339, -2), (key2331, 1), (key2088, 1), (key2339, 1), (key2298, 1), (key2332, 1), (key2090, 1), (key2282, -2), (key2088, -2), (key2332, 2), (key2329, -1), (key2180, -1), (key2335, 2), (key2329, -1), (key2083, -1), (key2335, -1), (key2192, -1), (key2332, -1), (key2090, -1), (key2180, 2), (key2083, 2), (key2331, -1), (key2282, -1), (key2329, 1), (key2180, 1), (key2334, -1), (key2290, -1), (key2278, 1), (key2081, 1), (key2334, 1), (key2190, 1), (key2178, -1), (key2081, -1), (key2282, 1), (key2088, 1), (key2180, -1), (key2083, -1)]

theorem rawRowCheck7194 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form5 = rawRow7194 := by decide +kernel

def row7194 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

theorem rowCheck7194 : row7194 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7194 := by decide +kernel

theorem rowEval7194 (x : Key → ℝ) : Integer.Sparse.eval row7194 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck7194, Integer.Sparse.eval_collectBalanced, rawRowCheck7194]

def rawRow7195 : Integer.Sparse Key := [(key2298, -2), (key2339, 1), (key2339, 1), (key2090, -2), (key2332, 1), (key2332, 1), (key2088, 1), (key2088, 1), (key2282, 1), (key2282, 1), (key2331, -2), (key2331, -2), (key2192, 2), (key2335, -1), (key2335, -1), (key2090, 2), (key2332, -1), (key2332, -1), (key2083, -1), (key2083, -1), (key2180, -1), (key2180, -1), (key2329, 2), (key2329, 2), (key2190, -1), (key2190, -1), (key2290, 1), (key2290, 1), (key2088, -1), (key2088, -1), (key2331, 1), (key2331, 1), (key2083, 1), (key2083, 1), (key2329, -1), (key2329, -1), (key2178, 1), (key2178, 1), (key2278, -1), (key2278, -1)]

theorem rawRowCheck7195 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form5 = rawRow7195 := by decide +kernel

def row7195 : Integer.Sparse Key := [(key2178, 2), (key2180, -2), (key2190, -2), (key2192, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2331, -2), (key2335, -2), (key2339, 2)]

theorem rowCheck7195 : row7195 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7195 := by decide +kernel

theorem rowEval7195 (x : Key → ℝ) : Integer.Sparse.eval row7195 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck7195, Integer.Sparse.eval_collectBalanced, rawRowCheck7195]

def rawRow7196 : Integer.Sparse Key := [(key2339, -2), (key2298, 1), (key2339, 1), (key2332, -2), (key2090, 1), (key2332, 1), (key2282, 1), (key2331, 1), (key2088, 1), (key2331, 1), (key2088, -2), (key2282, -2), (key2335, 2), (key2192, -1), (key2335, -1), (key2332, 2), (key2090, -1), (key2332, -1), (key2180, -1), (key2329, -1), (key2083, -1), (key2329, -1), (key2083, 2), (key2180, 2), (key2290, -1), (key2334, -1), (key2190, 1), (key2334, 1), (key2282, -1), (key2331, -1), (key2088, 1), (key2282, 1), (key2180, 1), (key2329, 1), (key2083, -1), (key2180, -1), (key2081, 1), (key2278, 1), (key2081, -1), (key2178, -1)]

theorem rawRowCheck7196 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form5 = rawRow7196 := by decide +kernel

def row7196 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

theorem rowCheck7196 : row7196 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7196 := by decide +kernel

theorem rowEval7196 (x : Key → ℝ) : Integer.Sparse.eval row7196 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck7196, Integer.Sparse.eval_collectBalanced, rawRowCheck7196]

def rawRow7197 : Integer.Sparse Key := [(key2339, -2), (key2339, 1), (key2298, 1), (key2332, -2), (key2332, 1), (key2090, 1), (key2331, 1), (key2282, 1), (key2331, 1), (key2088, 1), (key2282, -2), (key2088, -2), (key2335, 2), (key2335, -1), (key2192, -1), (key2332, 2), (key2332, -1), (key2090, -1), (key2329, -1), (key2180, -1), (key2329, -1), (key2083, -1), (key2180, 2), (key2083, 2), (key2334, -1), (key2290, -1), (key2334, 1), (key2190, 1), (key2331, -1), (key2282, -1), (key2282, 1), (key2088, 1), (key2329, 1), (key2180, 1), (key2180, -1), (key2083, -1), (key2278, 1), (key2081, 1), (key2178, -1), (key2081, -1)]

theorem rawRowCheck7197 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form5 = rawRow7197 := by decide +kernel

def row7197 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

theorem rowCheck7197 : row7197 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7197 := by decide +kernel

theorem rowEval7197 (x : Key → ℝ) : Integer.Sparse.eval row7197 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck7197, Integer.Sparse.eval_collectBalanced, rawRowCheck7197]

def rawRow7198 : Integer.Sparse Key := [(key748, -1), (key748, -1), (key749, 2), (key748, -1), (key748, -1), (key752, 2), (key752, 2), (key753, -1), (key753, -1), (key749, 2), (key753, -1), (key753, -1), (key832, 1), (key832, 1), (key833, -2), (key832, 1), (key832, 1), (key841, -2), (key841, -2), (key842, 1), (key842, 1), (key833, -2), (key842, 1), (key842, 1), (key929, -1), (key929, -1), (key930, 1), (key930, 1), (key936, 1), (key936, 1), (key937, -1), (key937, -1), (key929, -1), (key929, -1), (key936, 1), (key936, 1), (key930, 1), (key930, 1), (key937, -1), (key937, -1)]

theorem rawRowCheck7198 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form6 = rawRow7198 := by decide +kernel

def row7198 : Integer.Sparse Key := [(key748, -4), (key749, 4), (key752, 4), (key753, -4), (key832, 4), (key833, -4), (key841, -4), (key842, 4), (key929, -4), (key930, 4), (key936, 4), (key937, -4)]

theorem rowCheck7198 : row7198 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7198 := by decide +kernel

theorem rowEval7198 (x : Key → ℝ) : Integer.Sparse.eval row7198 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck7198, Integer.Sparse.eval_collectBalanced, rawRowCheck7198]

def rawRow7199 : Integer.Sparse Key := [(key748, -1), (key749, -1), (key748, 2), (key752, -1), (key753, -1), (key748, 2), (key753, 2), (key748, -1), (key752, -1), (key753, 2), (key749, -1), (key753, -1), (key832, 1), (key833, 1), (key832, -2), (key841, 1), (key842, 1), (key832, -2), (key842, -2), (key832, 1), (key841, 1), (key842, -2), (key833, 1), (key842, 1), (key926, -1), (key930, -1), (key926, 1), (key929, 1), (key926, 1), (key937, 1), (key926, -1), (key936, -1), (key936, -1), (key941, -1), (key929, 1), (key941, 1), (key937, 1), (key941, 1), (key930, -1), (key941, -1)]

theorem rawRowCheck7199 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form6 = rawRow7199 := by decide +kernel

def row7199 : Integer.Sparse Key := [(key748, 2), (key749, -2), (key752, -2), (key753, 2), (key832, -2), (key833, 2), (key841, 2), (key842, -2), (key929, 2), (key930, -2), (key936, -2), (key937, 2)]

theorem rowCheck7199 : row7199 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7199 := by decide +kernel

theorem rowEval7199 (x : Key → ℝ) : Integer.Sparse.eval row7199 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck7199, Integer.Sparse.eval_collectBalanced, rawRowCheck7199]

def rawRow7200 : Integer.Sparse Key := [(key749, -1), (key748, -1), (key748, 2), (key753, -1), (key752, -1), (key753, 2), (key748, 2), (key752, -1), (key748, -1), (key753, 2), (key753, -1), (key749, -1), (key833, 1), (key832, 1), (key832, -2), (key842, 1), (key841, 1), (key842, -2), (key832, -2), (key841, 1), (key832, 1), (key842, -2), (key842, 1), (key833, 1), (key930, -1), (key926, -1), (key929, 1), (key926, 1), (key937, 1), (key926, 1), (key936, -1), (key926, -1), (key941, -1), (key936, -1), (key941, 1), (key929, 1), (key941, 1), (key937, 1), (key941, -1), (key930, -1)]

theorem rawRowCheck7200 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form6 = rawRow7200 := by decide +kernel

def row7200 : Integer.Sparse Key := [(key748, 2), (key749, -2), (key752, -2), (key753, 2), (key832, -2), (key833, 2), (key841, 2), (key842, -2), (key929, 2), (key930, -2), (key936, -2), (key937, 2)]

theorem rowCheck7200 : row7200 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7200 := by decide +kernel

theorem rowEval7200 (x : Key → ℝ) : Integer.Sparse.eval row7200 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck7200, Integer.Sparse.eval_collectBalanced, rawRowCheck7200]

def rawRow7201 : Integer.Sparse Key := [(key752, -1), (key753, -1), (key753, 2), (key748, -1), (key749, -1), (key748, 2), (key753, 2), (key749, -1), (key753, -1), (key748, 2), (key748, -1), (key752, -1), (key841, 1), (key842, 1), (key842, -2), (key832, 1), (key833, 1), (key832, -2), (key842, -2), (key833, 1), (key842, 1), (key832, -2), (key832, 1), (key841, 1), (key936, -1), (key941, -1), (key937, 1), (key941, 1), (key929, 1), (key941, 1), (key930, -1), (key941, -1), (key926, -1), (key930, -1), (key926, 1), (key937, 1), (key926, 1), (key929, 1), (key926, -1), (key936, -1)]

theorem rawRowCheck7201 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form6 = rawRow7201 := by decide +kernel

def row7201 : Integer.Sparse Key := [(key748, 2), (key749, -2), (key752, -2), (key753, 2), (key832, -2), (key833, 2), (key841, 2), (key842, -2), (key929, 2), (key930, -2), (key936, -2), (key937, 2)]

theorem rowCheck7201 : row7201 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7201 := by decide +kernel

theorem rowEval7201 (x : Key → ℝ) : Integer.Sparse.eval row7201 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck7201, Integer.Sparse.eval_collectBalanced, rawRowCheck7201]

def rawRow7202 : Integer.Sparse Key := [(key753, -1), (key752, -1), (key753, 2), (key749, -1), (key748, -1), (key753, 2), (key748, 2), (key753, -1), (key749, -1), (key748, 2), (key752, -1), (key748, -1), (key842, 1), (key841, 1), (key842, -2), (key833, 1), (key832, 1), (key842, -2), (key832, -2), (key842, 1), (key833, 1), (key832, -2), (key841, 1), (key832, 1), (key941, -1), (key936, -1), (key941, 1), (key937, 1), (key941, 1), (key929, 1), (key941, -1), (key930, -1), (key930, -1), (key926, -1), (key937, 1), (key926, 1), (key929, 1), (key926, 1), (key936, -1), (key926, -1)]

theorem rawRowCheck7202 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form6 = rawRow7202 := by decide +kernel

def row7202 : Integer.Sparse Key := [(key748, 2), (key749, -2), (key752, -2), (key753, 2), (key832, -2), (key833, 2), (key841, 2), (key842, -2), (key929, 2), (key930, -2), (key936, -2), (key937, 2)]

theorem rowCheck7202 : row7202 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7202 := by decide +kernel

theorem rowEval7202 (x : Key → ℝ) : Integer.Sparse.eval row7202 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck7202, Integer.Sparse.eval_collectBalanced, rawRowCheck7202]

def rawRow7203 : Integer.Sparse Key := [(key753, -1), (key753, -1), (key752, 2), (key753, -1), (key753, -1), (key749, 2), (key749, 2), (key748, -1), (key748, -1), (key752, 2), (key748, -1), (key748, -1), (key842, 1), (key842, 1), (key841, -2), (key842, 1), (key842, 1), (key833, -2), (key833, -2), (key832, 1), (key832, 1), (key841, -2), (key832, 1), (key832, 1), (key937, -1), (key937, -1), (key936, 1), (key936, 1), (key930, 1), (key930, 1), (key929, -1), (key929, -1), (key937, -1), (key937, -1), (key930, 1), (key930, 1), (key936, 1), (key936, 1), (key929, -1), (key929, -1)]

theorem rawRowCheck7203 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form6 = rawRow7203 := by decide +kernel

def row7203 : Integer.Sparse Key := [(key748, -4), (key749, 4), (key752, 4), (key753, -4), (key832, 4), (key833, -4), (key841, -4), (key842, 4), (key929, -4), (key930, 4), (key936, 4), (key937, -4)]

theorem rowCheck7203 : row7203 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7203 := by decide +kernel

theorem rowEval7203 (x : Key → ℝ) : Integer.Sparse.eval row7203 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck7203, Integer.Sparse.eval_collectBalanced, rawRowCheck7203]

def rawRow7204 : Integer.Sparse Key := [(key832, -1), (key832, -1), (key833, 2), (key926, -1), (key926, -1), (key929, 2), (key929, 2), (key930, -1), (key930, -1), (key961, 2), (key963, -1), (key963, -1), (key748, 1), (key748, 1), (key749, -2), (key926, 1), (key926, 1), (key936, -2), (key936, -2), (key937, 1), (key937, 1), (key961, -2), (key965, 1), (key965, 1), (key752, -1), (key752, -1), (key753, 1), (key753, 1), (key841, 1), (key841, 1), (key842, -1), (key842, -1), (key929, -1), (key929, -1), (key936, 1), (key936, 1), (key963, 1), (key963, 1), (key965, -1), (key965, -1)]

theorem rawRowCheck7204 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form6 = rawRow7204 := by decide +kernel

def row7204 : Integer.Sparse Key := [(key748, 2), (key749, -2), (key752, -2), (key753, 2), (key832, -2), (key833, 2), (key841, 2), (key842, -2), (key929, 2), (key930, -2), (key936, -2), (key937, 2)]

theorem rowCheck7204 : row7204 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7204 := by decide +kernel

theorem rowEval7204 (x : Key → ℝ) : Integer.Sparse.eval row7204 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck7204, Integer.Sparse.eval_collectBalanced, rawRowCheck7204]

def rawRow7205 : Integer.Sparse Key := [(key832, -1), (key833, -1), (key832, 2), (key929, -1), (key930, -1), (key926, 2), (key930, 2), (key926, -1), (key929, -1), (key963, 2), (key961, -1), (key963, -1), (key748, 1), (key749, 1), (key748, -2), (key936, 1), (key937, 1), (key926, -2), (key937, -2), (key926, 1), (key936, 1), (key965, -2), (key961, 1), (key965, 1), (key748, -1), (key753, -1), (key748, 1), (key752, 1), (key832, 1), (key842, 1), (key832, -1), (key841, -1), (key936, -1), (key941, -1), (key929, 1), (key941, 1), (key965, 1), (key967, 1), (key963, -1), (key967, -1)]

theorem rawRowCheck7205 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form6 = rawRow7205 := by decide +kernel

def row7205 : Integer.Sparse Key := [(key748, -1), (key749, 1), (key752, 1), (key753, -1), (key832, 1), (key833, -1), (key841, -1), (key842, 1), (key929, -1), (key930, 1), (key936, 1), (key937, -1)]

theorem rowCheck7205 : row7205 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7205 := by decide +kernel

theorem rowEval7205 (x : Key → ℝ) : Integer.Sparse.eval row7205 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck7205, Integer.Sparse.eval_collectBalanced, rawRowCheck7205]

def rawRow7206 : Integer.Sparse Key := [(key833, -1), (key832, -1), (key832, 2), (key930, -1), (key929, -1), (key930, 2), (key926, 2), (key929, -1), (key926, -1), (key963, 2), (key963, -1), (key961, -1), (key749, 1), (key748, 1), (key748, -2), (key937, 1), (key936, 1), (key937, -2), (key926, -2), (key936, 1), (key926, 1), (key965, -2), (key965, 1), (key961, 1), (key753, -1), (key748, -1), (key752, 1), (key748, 1), (key842, 1), (key832, 1), (key841, -1), (key832, -1), (key941, -1), (key936, -1), (key941, 1), (key929, 1), (key967, 1), (key965, 1), (key967, -1), (key963, -1)]

theorem rawRowCheck7206 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form6 = rawRow7206 := by decide +kernel

def row7206 : Integer.Sparse Key := [(key748, -1), (key749, 1), (key752, 1), (key753, -1), (key832, 1), (key833, -1), (key841, -1), (key842, 1), (key929, -1), (key930, 1), (key936, 1), (key937, -1)]

theorem rowCheck7206 : row7206 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7206 := by decide +kernel

theorem rowEval7206 (x : Key → ℝ) : Integer.Sparse.eval row7206 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck7206, Integer.Sparse.eval_collectBalanced, rawRowCheck7206]

def rawRow7207 : Integer.Sparse Key := [(key926, -1), (key926, -1), (key961, 2), (key832, -1), (key832, -1), (key929, 2), (key929, 2), (key963, -1), (key963, -1), (key833, 2), (key930, -1), (key930, -1), (key926, 1), (key926, 1), (key961, -2), (key748, 1), (key748, 1), (key936, -2), (key936, -2), (key965, 1), (key965, 1), (key749, -2), (key937, 1), (key937, 1), (key929, -1), (key929, -1), (key963, 1), (key963, 1), (key936, 1), (key936, 1), (key965, -1), (key965, -1), (key752, -1), (key752, -1), (key841, 1), (key841, 1), (key753, 1), (key753, 1), (key842, -1), (key842, -1)]

theorem rawRowCheck7207 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form6 = rawRow7207 := by decide +kernel

def row7207 : Integer.Sparse Key := [(key748, 2), (key749, -2), (key752, -2), (key753, 2), (key832, -2), (key833, 2), (key841, 2), (key842, -2), (key929, 2), (key930, -2), (key936, -2), (key937, 2)]

theorem rowCheck7207 : row7207 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7207 := by decide +kernel

theorem rowEval7207 (x : Key → ℝ) : Integer.Sparse.eval row7207 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck7207, Integer.Sparse.eval_collectBalanced, rawRowCheck7207]

def rawRow7208 : Integer.Sparse Key := [(key926, -1), (key961, -1), (key926, 2), (key929, -1), (key963, -1), (key832, 2), (key963, 2), (key832, -1), (key929, -1), (key930, 2), (key833, -1), (key930, -1), (key926, 1), (key961, 1), (key926, -2), (key936, 1), (key965, 1), (key748, -2), (key965, -2), (key748, 1), (key936, 1), (key937, -2), (key749, 1), (key937, 1), (key832, -1), (key963, -1), (key832, 1), (key929, 1), (key748, 1), (key965, 1), (key748, -1), (key936, -1), (key841, -1), (key967, -1), (key752, 1), (key967, 1), (key842, 1), (key941, 1), (key753, -1), (key941, -1)]

theorem rawRowCheck7208 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form6 = rawRow7208 := by decide +kernel

def row7208 : Integer.Sparse Key := [(key748, -1), (key749, 1), (key752, 1), (key753, -1), (key832, 1), (key833, -1), (key841, -1), (key842, 1), (key929, -1), (key930, 1), (key936, 1), (key937, -1)]

theorem rowCheck7208 : row7208 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7208 := by decide +kernel

theorem rowEval7208 (x : Key → ℝ) : Integer.Sparse.eval row7208 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck7208, Integer.Sparse.eval_collectBalanced, rawRowCheck7208]

def rawRow7209 : Integer.Sparse Key := [(key961, -1), (key926, -1), (key926, 2), (key963, -1), (key929, -1), (key963, 2), (key832, 2), (key929, -1), (key832, -1), (key930, 2), (key930, -1), (key833, -1), (key961, 1), (key926, 1), (key926, -2), (key965, 1), (key936, 1), (key965, -2), (key748, -2), (key936, 1), (key748, 1), (key937, -2), (key937, 1), (key749, 1), (key963, -1), (key832, -1), (key929, 1), (key832, 1), (key965, 1), (key748, 1), (key936, -1), (key748, -1), (key967, -1), (key841, -1), (key967, 1), (key752, 1), (key941, 1), (key842, 1), (key941, -1), (key753, -1)]

theorem rawRowCheck7209 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form6 = rawRow7209 := by decide +kernel

def row7209 : Integer.Sparse Key := [(key748, -1), (key749, 1), (key752, 1), (key753, -1), (key832, 1), (key833, -1), (key841, -1), (key842, 1), (key929, -1), (key930, 1), (key936, 1), (key937, -1)]

theorem rowCheck7209 : row7209 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7209 := by decide +kernel

theorem rowEval7209 (x : Key → ℝ) : Integer.Sparse.eval row7209 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck7209, Integer.Sparse.eval_collectBalanced, rawRowCheck7209]

def rawRow7210 : Integer.Sparse Key := [(key929, -1), (key930, -1), (key963, 2), (key832, -1), (key833, -1), (key926, 2), (key930, 2), (key961, -1), (key963, -1), (key832, 2), (key926, -1), (key929, -1), (key936, 1), (key937, 1), (key965, -2), (key748, 1), (key749, 1), (key926, -2), (key937, -2), (key961, 1), (key965, 1), (key748, -2), (key926, 1), (key936, 1), (key936, -1), (key941, -1), (key965, 1), (key967, 1), (key929, 1), (key941, 1), (key963, -1), (key967, -1), (key748, -1), (key753, -1), (key832, 1), (key842, 1), (key748, 1), (key752, 1), (key832, -1), (key841, -1)]

theorem rawRowCheck7210 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form6 = rawRow7210 := by decide +kernel

def row7210 : Integer.Sparse Key := [(key748, -1), (key749, 1), (key752, 1), (key753, -1), (key832, 1), (key833, -1), (key841, -1), (key842, 1), (key929, -1), (key930, 1), (key936, 1), (key937, -1)]

theorem rowCheck7210 : row7210 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7210 := by decide +kernel

theorem rowEval7210 (x : Key → ℝ) : Integer.Sparse.eval row7210 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck7210, Integer.Sparse.eval_collectBalanced, rawRowCheck7210]

def rawRow7211 : Integer.Sparse Key := [(key930, -1), (key929, -1), (key963, 2), (key833, -1), (key832, -1), (key930, 2), (key926, 2), (key963, -1), (key961, -1), (key832, 2), (key929, -1), (key926, -1), (key937, 1), (key936, 1), (key965, -2), (key749, 1), (key748, 1), (key937, -2), (key926, -2), (key965, 1), (key961, 1), (key748, -2), (key936, 1), (key926, 1), (key941, -1), (key936, -1), (key967, 1), (key965, 1), (key941, 1), (key929, 1), (key967, -1), (key963, -1), (key753, -1), (key748, -1), (key842, 1), (key832, 1), (key752, 1), (key748, 1), (key841, -1), (key832, -1)]

theorem rawRowCheck7211 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form6 = rawRow7211 := by decide +kernel

def row7211 : Integer.Sparse Key := [(key748, -1), (key749, 1), (key752, 1), (key753, -1), (key832, 1), (key833, -1), (key841, -1), (key842, 1), (key929, -1), (key930, 1), (key936, 1), (key937, -1)]

theorem rowCheck7211 : row7211 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7211 := by decide +kernel

theorem rowEval7211 (x : Key → ℝ) : Integer.Sparse.eval row7211 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck7211, Integer.Sparse.eval_collectBalanced, rawRowCheck7211]

def rawRow7212 : Integer.Sparse Key := [(key929, -1), (key963, -1), (key930, 2), (key926, -1), (key961, -1), (key832, 2), (key963, 2), (key833, -1), (key930, -1), (key926, 2), (key832, -1), (key929, -1), (key936, 1), (key965, 1), (key937, -2), (key926, 1), (key961, 1), (key748, -2), (key965, -2), (key749, 1), (key937, 1), (key926, -2), (key748, 1), (key936, 1), (key841, -1), (key967, -1), (key842, 1), (key941, 1), (key752, 1), (key967, 1), (key753, -1), (key941, -1), (key832, -1), (key963, -1), (key748, 1), (key965, 1), (key832, 1), (key929, 1), (key748, -1), (key936, -1)]

theorem rawRowCheck7212 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form6 = rawRow7212 := by decide +kernel

def row7212 : Integer.Sparse Key := [(key748, -1), (key749, 1), (key752, 1), (key753, -1), (key832, 1), (key833, -1), (key841, -1), (key842, 1), (key929, -1), (key930, 1), (key936, 1), (key937, -1)]

theorem rowCheck7212 : row7212 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7212 := by decide +kernel

theorem rowEval7212 (x : Key → ℝ) : Integer.Sparse.eval row7212 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck7212, Integer.Sparse.eval_collectBalanced, rawRowCheck7212]

def rawRow7213 : Integer.Sparse Key := [(key963, -1), (key929, -1), (key930, 2), (key961, -1), (key926, -1), (key963, 2), (key832, 2), (key930, -1), (key833, -1), (key926, 2), (key929, -1), (key832, -1), (key965, 1), (key936, 1), (key937, -2), (key961, 1), (key926, 1), (key965, -2), (key748, -2), (key937, 1), (key749, 1), (key926, -2), (key936, 1), (key748, 1), (key967, -1), (key841, -1), (key941, 1), (key842, 1), (key967, 1), (key752, 1), (key941, -1), (key753, -1), (key963, -1), (key832, -1), (key965, 1), (key748, 1), (key929, 1), (key832, 1), (key936, -1), (key748, -1)]

theorem rawRowCheck7213 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form6 = rawRow7213 := by decide +kernel

def row7213 : Integer.Sparse Key := [(key748, -1), (key749, 1), (key752, 1), (key753, -1), (key832, 1), (key833, -1), (key841, -1), (key842, 1), (key929, -1), (key930, 1), (key936, 1), (key937, -1)]

theorem rowCheck7213 : row7213 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7213 := by decide +kernel

theorem rowEval7213 (x : Key → ℝ) : Integer.Sparse.eval row7213 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck7213, Integer.Sparse.eval_collectBalanced, rawRowCheck7213]

def rawRow7214 : Integer.Sparse Key := [(key930, -1), (key963, -1), (key929, 2), (key930, -1), (key963, -1), (key833, 2), (key961, 2), (key832, -1), (key926, -1), (key929, 2), (key832, -1), (key926, -1), (key937, 1), (key965, 1), (key936, -2), (key937, 1), (key965, 1), (key749, -2), (key961, -2), (key748, 1), (key926, 1), (key936, -2), (key748, 1), (key926, 1), (key842, -1), (key965, -1), (key841, 1), (key936, 1), (key753, 1), (key963, 1), (key752, -1), (key929, -1), (key842, -1), (key965, -1), (key753, 1), (key963, 1), (key841, 1), (key936, 1), (key752, -1), (key929, -1)]

theorem rawRowCheck7214 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form6 = rawRow7214 := by decide +kernel

def row7214 : Integer.Sparse Key := [(key748, 2), (key749, -2), (key752, -2), (key753, 2), (key832, -2), (key833, 2), (key841, 2), (key842, -2), (key929, 2), (key930, -2), (key936, -2), (key937, 2)]

theorem rowCheck7214 : row7214 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7214 := by decide +kernel

theorem rowEval7214 (x : Key → ℝ) : Integer.Sparse.eval row7214 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck7214, Integer.Sparse.eval_collectBalanced, rawRowCheck7214]

def rawRow7215 : Integer.Sparse Key := [(key963, -1), (key930, -1), (key929, 2), (key963, -1), (key930, -1), (key961, 2), (key833, 2), (key926, -1), (key832, -1), (key929, 2), (key926, -1), (key832, -1), (key965, 1), (key937, 1), (key936, -2), (key965, 1), (key937, 1), (key961, -2), (key749, -2), (key926, 1), (key748, 1), (key936, -2), (key926, 1), (key748, 1), (key965, -1), (key842, -1), (key936, 1), (key841, 1), (key963, 1), (key753, 1), (key929, -1), (key752, -1), (key965, -1), (key842, -1), (key963, 1), (key753, 1), (key936, 1), (key841, 1), (key929, -1), (key752, -1)]

theorem rawRowCheck7215 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form6 = rawRow7215 := by decide +kernel

def row7215 : Integer.Sparse Key := [(key748, 2), (key749, -2), (key752, -2), (key753, 2), (key832, -2), (key833, 2), (key841, 2), (key842, -2), (key929, 2), (key930, -2), (key936, -2), (key937, 2)]

theorem rowCheck7215 : row7215 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7215 := by decide +kernel

theorem rowEval7215 (x : Key → ℝ) : Integer.Sparse.eval row7215 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck7215, Integer.Sparse.eval_collectBalanced, rawRowCheck7215]

def rawRow7216 : Integer.Sparse Key := [(key841, -1), (key842, -1), (key842, 2), (key936, -1), (key937, -1), (key936, 2), (key941, 2), (key937, -1), (key941, -1), (key965, 2), (key965, -1), (key967, -1), (key752, 1), (key753, 1), (key753, -2), (key929, 1), (key930, 1), (key929, -2), (key941, -2), (key930, 1), (key941, 1), (key963, -2), (key963, 1), (key967, 1), (key748, -1), (key753, -1), (key749, 1), (key753, 1), (key832, 1), (key842, 1), (key833, -1), (key842, -1), (key926, -1), (key930, -1), (key926, 1), (key937, 1), (key961, 1), (key963, 1), (key961, -1), (key965, -1)]

theorem rawRowCheck7216 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form6 = rawRow7216 := by decide +kernel

def row7216 : Integer.Sparse Key := [(key748, -1), (key749, 1), (key752, 1), (key753, -1), (key832, 1), (key833, -1), (key841, -1), (key842, 1), (key929, -1), (key930, 1), (key936, 1), (key937, -1)]

theorem rowCheck7216 : row7216 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7216 := by decide +kernel

theorem rowEval7216 (x : Key → ℝ) : Integer.Sparse.eval row7216 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck7216, Integer.Sparse.eval_collectBalanced, rawRowCheck7216]

def rawRow7217 : Integer.Sparse Key := [(key842, -1), (key841, -1), (key842, 2), (key937, -1), (key936, -1), (key941, 2), (key936, 2), (key941, -1), (key937, -1), (key965, 2), (key967, -1), (key965, -1), (key753, 1), (key752, 1), (key753, -2), (key930, 1), (key929, 1), (key941, -2), (key929, -2), (key941, 1), (key930, 1), (key963, -2), (key967, 1), (key963, 1), (key753, -1), (key748, -1), (key753, 1), (key749, 1), (key842, 1), (key832, 1), (key842, -1), (key833, -1), (key930, -1), (key926, -1), (key937, 1), (key926, 1), (key963, 1), (key961, 1), (key965, -1), (key961, -1)]

theorem rawRowCheck7217 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form6 = rawRow7217 := by decide +kernel

def row7217 : Integer.Sparse Key := [(key748, -1), (key749, 1), (key752, 1), (key753, -1), (key832, 1), (key833, -1), (key841, -1), (key842, 1), (key929, -1), (key930, 1), (key936, 1), (key937, -1)]

theorem rowCheck7217 : row7217 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7217 := by decide +kernel

theorem rowEval7217 (x : Key → ℝ) : Integer.Sparse.eval row7217 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck7217, Integer.Sparse.eval_collectBalanced, rawRowCheck7217]

def rawRow7218 : Integer.Sparse Key := [(key842, -1), (key842, -1), (key841, 2), (key941, -1), (key941, -1), (key937, 2), (key937, 2), (key936, -1), (key936, -1), (key967, 2), (key965, -1), (key965, -1), (key753, 1), (key753, 1), (key752, -2), (key941, 1), (key941, 1), (key930, -2), (key930, -2), (key929, 1), (key929, 1), (key967, -2), (key963, 1), (key963, 1), (key749, -1), (key749, -1), (key748, 1), (key748, 1), (key833, 1), (key833, 1), (key832, -1), (key832, -1), (key937, -1), (key937, -1), (key930, 1), (key930, 1), (key965, 1), (key965, 1), (key963, -1), (key963, -1)]

theorem rawRowCheck7218 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form6 = rawRow7218 := by decide +kernel

def row7218 : Integer.Sparse Key := [(key748, 2), (key749, -2), (key752, -2), (key753, 2), (key832, -2), (key833, 2), (key841, 2), (key842, -2), (key929, 2), (key930, -2), (key936, -2), (key937, 2)]

theorem rowCheck7218 : row7218 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7218 := by decide +kernel

theorem rowEval7218 (x : Key → ℝ) : Integer.Sparse.eval row7218 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck7218, Integer.Sparse.eval_collectBalanced, rawRowCheck7218]

def rawRow7219 : Integer.Sparse Key := [(key936, -1), (key937, -1), (key965, 2), (key841, -1), (key842, -1), (key936, 2), (key941, 2), (key965, -1), (key967, -1), (key842, 2), (key937, -1), (key941, -1), (key929, 1), (key930, 1), (key963, -2), (key752, 1), (key753, 1), (key929, -2), (key941, -2), (key963, 1), (key967, 1), (key753, -2), (key930, 1), (key941, 1), (key926, -1), (key930, -1), (key961, 1), (key963, 1), (key926, 1), (key937, 1), (key961, -1), (key965, -1), (key748, -1), (key753, -1), (key832, 1), (key842, 1), (key749, 1), (key753, 1), (key833, -1), (key842, -1)]

theorem rawRowCheck7219 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form6 = rawRow7219 := by decide +kernel

def row7219 : Integer.Sparse Key := [(key748, -1), (key749, 1), (key752, 1), (key753, -1), (key832, 1), (key833, -1), (key841, -1), (key842, 1), (key929, -1), (key930, 1), (key936, 1), (key937, -1)]

theorem rowCheck7219 : row7219 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7219 := by decide +kernel

theorem rowEval7219 (x : Key → ℝ) : Integer.Sparse.eval row7219 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck7219, Integer.Sparse.eval_collectBalanced, rawRowCheck7219]

def rawRow7220 : Integer.Sparse Key := [(key937, -1), (key936, -1), (key965, 2), (key842, -1), (key841, -1), (key941, 2), (key936, 2), (key967, -1), (key965, -1), (key842, 2), (key941, -1), (key937, -1), (key930, 1), (key929, 1), (key963, -2), (key753, 1), (key752, 1), (key941, -2), (key929, -2), (key967, 1), (key963, 1), (key753, -2), (key941, 1), (key930, 1), (key930, -1), (key926, -1), (key963, 1), (key961, 1), (key937, 1), (key926, 1), (key965, -1), (key961, -1), (key753, -1), (key748, -1), (key842, 1), (key832, 1), (key753, 1), (key749, 1), (key842, -1), (key833, -1)]

theorem rawRowCheck7220 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form6 = rawRow7220 := by decide +kernel

def row7220 : Integer.Sparse Key := [(key748, -1), (key749, 1), (key752, 1), (key753, -1), (key832, 1), (key833, -1), (key841, -1), (key842, 1), (key929, -1), (key930, 1), (key936, 1), (key937, -1)]

theorem rowCheck7220 : row7220 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7220 := by decide +kernel

theorem rowEval7220 (x : Key → ℝ) : Integer.Sparse.eval row7220 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck7220, Integer.Sparse.eval_collectBalanced, rawRowCheck7220]

def rawRow7221 : Integer.Sparse Key := [(key936, -1), (key965, -1), (key937, 2), (key936, -1), (key965, -1), (key841, 2), (key967, 2), (key842, -1), (key941, -1), (key937, 2), (key842, -1), (key941, -1), (key929, 1), (key963, 1), (key930, -2), (key929, 1), (key963, 1), (key752, -2), (key967, -2), (key753, 1), (key941, 1), (key930, -2), (key753, 1), (key941, 1), (key832, -1), (key963, -1), (key833, 1), (key930, 1), (key748, 1), (key965, 1), (key749, -1), (key937, -1), (key832, -1), (key963, -1), (key748, 1), (key965, 1), (key833, 1), (key930, 1), (key749, -1), (key937, -1)]

theorem rawRowCheck7221 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form6 = rawRow7221 := by decide +kernel

def row7221 : Integer.Sparse Key := [(key748, 2), (key749, -2), (key752, -2), (key753, 2), (key832, -2), (key833, 2), (key841, 2), (key842, -2), (key929, 2), (key930, -2), (key936, -2), (key937, 2)]

theorem rowCheck7221 : row7221 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7221 := by decide +kernel

theorem rowEval7221 (x : Key → ℝ) : Integer.Sparse.eval row7221 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck7221, Integer.Sparse.eval_collectBalanced, rawRowCheck7221]

def rawRow7222 : Integer.Sparse Key := [(key965, -1), (key936, -1), (key937, 2), (key965, -1), (key936, -1), (key967, 2), (key841, 2), (key941, -1), (key842, -1), (key937, 2), (key941, -1), (key842, -1), (key963, 1), (key929, 1), (key930, -2), (key963, 1), (key929, 1), (key967, -2), (key752, -2), (key941, 1), (key753, 1), (key930, -2), (key941, 1), (key753, 1), (key963, -1), (key832, -1), (key930, 1), (key833, 1), (key965, 1), (key748, 1), (key937, -1), (key749, -1), (key963, -1), (key832, -1), (key965, 1), (key748, 1), (key930, 1), (key833, 1), (key937, -1), (key749, -1)]

theorem rawRowCheck7222 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form6 = rawRow7222 := by decide +kernel

def row7222 : Integer.Sparse Key := [(key748, 2), (key749, -2), (key752, -2), (key753, 2), (key832, -2), (key833, 2), (key841, 2), (key842, -2), (key929, 2), (key930, -2), (key936, -2), (key937, 2)]

theorem rowCheck7222 : row7222 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7222 := by decide +kernel

theorem rowEval7222 (x : Key → ℝ) : Integer.Sparse.eval row7222 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck7222, Integer.Sparse.eval_collectBalanced, rawRowCheck7222]

def rawRow7223 : Integer.Sparse Key := [(key937, -1), (key965, -1), (key936, 2), (key941, -1), (key967, -1), (key842, 2), (key965, 2), (key841, -1), (key936, -1), (key941, 2), (key842, -1), (key937, -1), (key930, 1), (key963, 1), (key929, -2), (key941, 1), (key967, 1), (key753, -2), (key963, -2), (key752, 1), (key929, 1), (key941, -2), (key753, 1), (key930, 1), (key833, -1), (key961, -1), (key832, 1), (key926, 1), (key749, 1), (key961, 1), (key748, -1), (key926, -1), (key842, -1), (key965, -1), (key753, 1), (key963, 1), (key842, 1), (key937, 1), (key753, -1), (key930, -1)]

theorem rawRowCheck7223 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form6 = rawRow7223 := by decide +kernel

def row7223 : Integer.Sparse Key := [(key748, -1), (key749, 1), (key752, 1), (key753, -1), (key832, 1), (key833, -1), (key841, -1), (key842, 1), (key929, -1), (key930, 1), (key936, 1), (key937, -1)]

theorem rowCheck7223 : row7223 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7223 := by decide +kernel

theorem rowEval7223 (x : Key → ℝ) : Integer.Sparse.eval row7223 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck7223, Integer.Sparse.eval_collectBalanced, rawRowCheck7223]

def rawRow7224 : Integer.Sparse Key := [(key965, -1), (key937, -1), (key936, 2), (key967, -1), (key941, -1), (key965, 2), (key842, 2), (key936, -1), (key841, -1), (key941, 2), (key937, -1), (key842, -1), (key963, 1), (key930, 1), (key929, -2), (key967, 1), (key941, 1), (key963, -2), (key753, -2), (key929, 1), (key752, 1), (key941, -2), (key930, 1), (key753, 1), (key961, -1), (key833, -1), (key926, 1), (key832, 1), (key961, 1), (key749, 1), (key926, -1), (key748, -1), (key965, -1), (key842, -1), (key963, 1), (key753, 1), (key937, 1), (key842, 1), (key930, -1), (key753, -1)]

theorem rawRowCheck7224 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form6 = rawRow7224 := by decide +kernel

def row7224 : Integer.Sparse Key := [(key748, -1), (key749, 1), (key752, 1), (key753, -1), (key832, 1), (key833, -1), (key841, -1), (key842, 1), (key929, -1), (key930, 1), (key936, 1), (key937, -1)]

theorem rowCheck7224 : row7224 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7224 := by decide +kernel

theorem rowEval7224 (x : Key → ℝ) : Integer.Sparse.eval row7224 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck7224, Integer.Sparse.eval_collectBalanced, rawRowCheck7224]

def rawRow7225 : Integer.Sparse Key := [(key941, -1), (key941, -1), (key967, 2), (key842, -1), (key842, -1), (key937, 2), (key937, 2), (key965, -1), (key965, -1), (key841, 2), (key936, -1), (key936, -1), (key941, 1), (key941, 1), (key967, -2), (key753, 1), (key753, 1), (key930, -2), (key930, -2), (key963, 1), (key963, 1), (key752, -2), (key929, 1), (key929, 1), (key937, -1), (key937, -1), (key965, 1), (key965, 1), (key930, 1), (key930, 1), (key963, -1), (key963, -1), (key749, -1), (key749, -1), (key833, 1), (key833, 1), (key748, 1), (key748, 1), (key832, -1), (key832, -1)]

theorem rawRowCheck7225 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form6 = rawRow7225 := by decide +kernel

def row7225 : Integer.Sparse Key := [(key748, 2), (key749, -2), (key752, -2), (key753, 2), (key832, -2), (key833, 2), (key841, 2), (key842, -2), (key929, 2), (key930, -2), (key936, -2), (key937, 2)]

theorem rowCheck7225 : row7225 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7225 := by decide +kernel

theorem rowEval7225 (x : Key → ℝ) : Integer.Sparse.eval row7225 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck7225, Integer.Sparse.eval_collectBalanced, rawRowCheck7225]

def rawRow7226 : Integer.Sparse Key := [(key941, -1), (key967, -1), (key941, 2), (key937, -1), (key965, -1), (key842, 2), (key965, 2), (key842, -1), (key937, -1), (key936, 2), (key841, -1), (key936, -1), (key941, 1), (key967, 1), (key941, -2), (key930, 1), (key963, 1), (key753, -2), (key963, -2), (key753, 1), (key930, 1), (key929, -2), (key752, 1), (key929, 1), (key842, -1), (key965, -1), (key842, 1), (key937, 1), (key753, 1), (key963, 1), (key753, -1), (key930, -1), (key833, -1), (key961, -1), (key749, 1), (key961, 1), (key832, 1), (key926, 1), (key748, -1), (key926, -1)]

theorem rawRowCheck7226 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form6 = rawRow7226 := by decide +kernel

def row7226 : Integer.Sparse Key := [(key748, -1), (key749, 1), (key752, 1), (key753, -1), (key832, 1), (key833, -1), (key841, -1), (key842, 1), (key929, -1), (key930, 1), (key936, 1), (key937, -1)]

theorem rowCheck7226 : row7226 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7226 := by decide +kernel

theorem rowEval7226 (x : Key → ℝ) : Integer.Sparse.eval row7226 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck7226, Integer.Sparse.eval_collectBalanced, rawRowCheck7226]

def rawRow7227 : Integer.Sparse Key := [(key967, -1), (key941, -1), (key941, 2), (key965, -1), (key937, -1), (key965, 2), (key842, 2), (key937, -1), (key842, -1), (key936, 2), (key936, -1), (key841, -1), (key967, 1), (key941, 1), (key941, -2), (key963, 1), (key930, 1), (key963, -2), (key753, -2), (key930, 1), (key753, 1), (key929, -2), (key929, 1), (key752, 1), (key965, -1), (key842, -1), (key937, 1), (key842, 1), (key963, 1), (key753, 1), (key930, -1), (key753, -1), (key961, -1), (key833, -1), (key961, 1), (key749, 1), (key926, 1), (key832, 1), (key926, -1), (key748, -1)]

theorem rawRowCheck7227 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form6 = rawRow7227 := by decide +kernel

def row7227 : Integer.Sparse Key := [(key748, -1), (key749, 1), (key752, 1), (key753, -1), (key832, 1), (key833, -1), (key841, -1), (key842, 1), (key929, -1), (key930, 1), (key936, 1), (key937, -1)]

theorem rowCheck7227 : row7227 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7227 := by decide +kernel

theorem rowEval7227 (x : Key → ℝ) : Integer.Sparse.eval row7227 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck7227, Integer.Sparse.eval_collectBalanced, rawRowCheck7227]

def rawRow7228 : Integer.Sparse Key := [(key2177, 1), (key2177, 1), (key2181, -2), (key2177, 1), (key2177, 1), (key2188, -2), (key2188, -2), (key2191, 1), (key2191, 1), (key2181, -2), (key2191, 1), (key2191, 1), (key2277, -1), (key2277, -1), (key2283, 1), (key2283, 1), (key2277, -1), (key2277, -1), (key2288, 1), (key2288, 1), (key2288, 1), (key2288, 1), (key2296, -1), (key2296, -1), (key2283, 1), (key2283, 1), (key2296, -1), (key2296, -1), (key2342, 2), (key2344, -1), (key2344, -1), (key2342, 2), (key2348, -1), (key2348, -1), (key2344, -1), (key2344, -1), (key2348, -1), (key2348, -1), (key2350, 2), (key2350, 2)]

theorem rawRowCheck7228 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form7 = rawRow7228 := by decide +kernel

def row7228 : Integer.Sparse Key := [(key2177, 4), (key2181, -4), (key2188, -4), (key2191, 4), (key2277, -4), (key2283, 4), (key2288, 4), (key2296, -4), (key2342, 4), (key2344, -4), (key2348, -4), (key2350, 4)]

theorem rowCheck7228 : row7228 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7228 := by decide +kernel

theorem rowEval7228 (x : Key → ℝ) : Integer.Sparse.eval row7228 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form7) x := by
  rw [rowCheck7228, Integer.Sparse.eval_collectBalanced, rawRowCheck7228]

def rawRow7229 : Integer.Sparse Key := [(key2177, 1), (key2181, 1), (key2177, -2), (key2188, 1), (key2191, 1), (key2177, -2), (key2191, -2), (key2177, 1), (key2188, 1), (key2191, -2), (key2181, 1), (key2191, 1), (key2280, -1), (key2283, -1), (key2277, 1), (key2280, 1), (key2288, -1), (key2291, -1), (key2277, 1), (key2291, 1), (key2280, 1), (key2296, 1), (key2280, -1), (key2288, -1), (key2291, 1), (key2296, 1), (key2283, -1), (key2291, -1), (key2344, 2), (key2342, -1), (key2344, -1), (key2348, 2), (key2342, -1), (key2348, -1), (key2348, -1), (key2350, -1), (key2344, -1), (key2350, -1), (key2344, 2), (key2348, 2)]

theorem rawRowCheck7229 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form7 = rawRow7229 := by decide +kernel

def row7229 : Integer.Sparse Key := [(key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2277, 2), (key2283, -2), (key2288, -2), (key2296, 2), (key2342, -2), (key2344, 2), (key2348, 2), (key2350, -2)]

theorem rowCheck7229 : row7229 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7229 := by decide +kernel

theorem rowEval7229 (x : Key → ℝ) : Integer.Sparse.eval row7229 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form7) x := by
  rw [rowCheck7229, Integer.Sparse.eval_collectBalanced, rawRowCheck7229]

def rawRow7230 : Integer.Sparse Key := [(key2181, 1), (key2177, 1), (key2177, -2), (key2191, 1), (key2188, 1), (key2191, -2), (key2177, -2), (key2188, 1), (key2177, 1), (key2191, -2), (key2191, 1), (key2181, 1), (key2283, -1), (key2280, -1), (key2280, 1), (key2277, 1), (key2291, -1), (key2288, -1), (key2291, 1), (key2277, 1), (key2296, 1), (key2280, 1), (key2288, -1), (key2280, -1), (key2296, 1), (key2291, 1), (key2291, -1), (key2283, -1), (key2344, 2), (key2344, -1), (key2342, -1), (key2348, 2), (key2348, -1), (key2342, -1), (key2350, -1), (key2348, -1), (key2350, -1), (key2344, -1), (key2348, 2), (key2344, 2)]

theorem rawRowCheck7230 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form7 = rawRow7230 := by decide +kernel

def row7230 : Integer.Sparse Key := [(key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2277, 2), (key2283, -2), (key2288, -2), (key2296, 2), (key2342, -2), (key2344, 2), (key2348, 2), (key2350, -2)]

theorem rowCheck7230 : row7230 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7230 := by decide +kernel

theorem rowEval7230 (x : Key → ℝ) : Integer.Sparse.eval row7230 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck7230, Integer.Sparse.eval_collectBalanced, rawRowCheck7230]

def rawRow7231 : Integer.Sparse Key := [(key2188, 1), (key2191, 1), (key2191, -2), (key2177, 1), (key2181, 1), (key2177, -2), (key2191, -2), (key2181, 1), (key2191, 1), (key2177, -2), (key2177, 1), (key2188, 1), (key2288, -1), (key2291, -1), (key2291, 1), (key2296, 1), (key2280, -1), (key2283, -1), (key2280, 1), (key2296, 1), (key2277, 1), (key2291, 1), (key2283, -1), (key2291, -1), (key2277, 1), (key2280, 1), (key2280, -1), (key2288, -1), (key2348, 2), (key2348, -1), (key2350, -1), (key2344, 2), (key2344, -1), (key2350, -1), (key2342, -1), (key2344, -1), (key2342, -1), (key2348, -1), (key2344, 2), (key2348, 2)]

theorem rawRowCheck7231 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form7 = rawRow7231 := by decide +kernel

def row7231 : Integer.Sparse Key := [(key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2277, 2), (key2283, -2), (key2288, -2), (key2296, 2), (key2342, -2), (key2344, 2), (key2348, 2), (key2350, -2)]

theorem rowCheck7231 : row7231 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7231 := by decide +kernel

theorem rowEval7231 (x : Key → ℝ) : Integer.Sparse.eval row7231 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form7) x := by
  rw [rowCheck7231, Integer.Sparse.eval_collectBalanced, rawRowCheck7231]

def rawRow7232 : Integer.Sparse Key := [(key2191, 1), (key2188, 1), (key2191, -2), (key2181, 1), (key2177, 1), (key2191, -2), (key2177, -2), (key2191, 1), (key2181, 1), (key2177, -2), (key2188, 1), (key2177, 1), (key2291, -1), (key2288, -1), (key2296, 1), (key2291, 1), (key2283, -1), (key2280, -1), (key2296, 1), (key2280, 1), (key2291, 1), (key2277, 1), (key2291, -1), (key2283, -1), (key2280, 1), (key2277, 1), (key2288, -1), (key2280, -1), (key2348, 2), (key2350, -1), (key2348, -1), (key2344, 2), (key2350, -1), (key2344, -1), (key2344, -1), (key2342, -1), (key2348, -1), (key2342, -1), (key2348, 2), (key2344, 2)]

theorem rawRowCheck7232 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form7 = rawRow7232 := by decide +kernel

def row7232 : Integer.Sparse Key := [(key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2277, 2), (key2283, -2), (key2288, -2), (key2296, 2), (key2342, -2), (key2344, 2), (key2348, 2), (key2350, -2)]

theorem rowCheck7232 : row7232 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7232 := by decide +kernel

theorem rowEval7232 (x : Key → ℝ) : Integer.Sparse.eval row7232 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck7232, Integer.Sparse.eval_collectBalanced, rawRowCheck7232]

def rawRow7233 : Integer.Sparse Key := [(key2191, 1), (key2191, 1), (key2188, -2), (key2191, 1), (key2191, 1), (key2181, -2), (key2181, -2), (key2177, 1), (key2177, 1), (key2188, -2), (key2177, 1), (key2177, 1), (key2296, -1), (key2296, -1), (key2288, 1), (key2288, 1), (key2296, -1), (key2296, -1), (key2283, 1), (key2283, 1), (key2283, 1), (key2283, 1), (key2277, -1), (key2277, -1), (key2288, 1), (key2288, 1), (key2277, -1), (key2277, -1), (key2350, 2), (key2348, -1), (key2348, -1), (key2350, 2), (key2344, -1), (key2344, -1), (key2348, -1), (key2348, -1), (key2344, -1), (key2344, -1), (key2342, 2), (key2342, 2)]

theorem rawRowCheck7233 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form7 = rawRow7233 := by decide +kernel

def row7233 : Integer.Sparse Key := [(key2177, 4), (key2181, -4), (key2188, -4), (key2191, 4), (key2277, -4), (key2283, 4), (key2288, 4), (key2296, -4), (key2342, 4), (key2344, -4), (key2348, -4), (key2350, 4)]

theorem rowCheck7233 : row7233 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7233 := by decide +kernel

theorem rowEval7233 (x : Key → ℝ) : Integer.Sparse.eval row7233 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck7233, Integer.Sparse.eval_collectBalanced, rawRowCheck7233]

def rawRow7234 : Integer.Sparse Key := [(key2080, 1), (key2080, 1), (key2084, -2), (key2277, 1), (key2277, 1), (key2288, -2), (key2288, -2), (key2291, 1), (key2291, 1), (key2342, -2), (key2348, 1), (key2348, 1), (key2080, -1), (key2080, -1), (key2089, 1), (key2089, 1), (key2177, -1), (key2177, -1), (key2188, 1), (key2188, 1), (key2288, 1), (key2288, 1), (key2296, -1), (key2296, -1), (key2344, 1), (key2344, 1), (key2350, -1), (key2350, -1), (key2084, 2), (key2089, -1), (key2089, -1), (key2181, 2), (key2191, -1), (key2191, -1), (key2283, -1), (key2283, -1), (key2291, -1), (key2291, -1), (key2296, 2), (key2296, 2)]

theorem rawRowCheck7234 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form7 = rawRow7234 := by decide +kernel

def row7234 : Integer.Sparse Key := [(key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2277, 2), (key2283, -2), (key2288, -2), (key2296, 2), (key2342, -2), (key2344, 2), (key2348, 2), (key2350, -2)]

theorem rowCheck7234 : row7234 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7234 := by decide +kernel

theorem rowEval7234 (x : Key → ℝ) : Integer.Sparse.eval row7234 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form7) x := by
  rw [rowCheck7234, Integer.Sparse.eval_collectBalanced, rawRowCheck7234]

def rawRow7235 : Integer.Sparse Key := [(key2080, 1), (key2084, 1), (key2080, -2), (key2288, 1), (key2291, 1), (key2277, -2), (key2291, -2), (key2277, 1), (key2288, 1), (key2348, -2), (key2342, 1), (key2348, 1), (key2086, -1), (key2089, -1), (key2080, 1), (key2086, 1), (key2188, -1), (key2191, -1), (key2177, 1), (key2191, 1), (key2280, 1), (key2296, 1), (key2280, -1), (key2288, -1), (key2348, 1), (key2350, 1), (key2344, -1), (key2348, -1), (key2089, 2), (key2084, -1), (key2089, -1), (key2191, 2), (key2181, -1), (key2191, -1), (key2291, -1), (key2296, -1), (key2283, -1), (key2296, -1), (key2283, 2), (key2291, 2)]

theorem rawRowCheck7235 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form7 = rawRow7235 := by decide +kernel

def row7235 : Integer.Sparse Key := [(key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2277, -1), (key2283, 1), (key2288, 1), (key2296, -1), (key2342, 1), (key2344, -1), (key2348, -1), (key2350, 1)]

theorem rowCheck7235 : row7235 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7235 := by decide +kernel

theorem rowEval7235 (x : Key → ℝ) : Integer.Sparse.eval row7235 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form7) x := by
  rw [rowCheck7235, Integer.Sparse.eval_collectBalanced, rawRowCheck7235]

def rawRow7236 : Integer.Sparse Key := [(key2084, 1), (key2080, 1), (key2080, -2), (key2291, 1), (key2288, 1), (key2291, -2), (key2277, -2), (key2288, 1), (key2277, 1), (key2348, -2), (key2348, 1), (key2342, 1), (key2089, -1), (key2086, -1), (key2086, 1), (key2080, 1), (key2191, -1), (key2188, -1), (key2191, 1), (key2177, 1), (key2296, 1), (key2280, 1), (key2288, -1), (key2280, -1), (key2350, 1), (key2348, 1), (key2348, -1), (key2344, -1), (key2089, 2), (key2089, -1), (key2084, -1), (key2191, 2), (key2191, -1), (key2181, -1), (key2296, -1), (key2291, -1), (key2296, -1), (key2283, -1), (key2291, 2), (key2283, 2)]

theorem rawRowCheck7236 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form7 = rawRow7236 := by decide +kernel

def row7236 : Integer.Sparse Key := [(key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2277, -1), (key2283, 1), (key2288, 1), (key2296, -1), (key2342, 1), (key2344, -1), (key2348, -1), (key2350, 1)]

theorem rowCheck7236 : row7236 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7236 := by decide +kernel

theorem rowEval7236 (x : Key → ℝ) : Integer.Sparse.eval row7236 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck7236, Integer.Sparse.eval_collectBalanced, rawRowCheck7236]

def rawRow7237 : Integer.Sparse Key := [(key2277, 1), (key2277, 1), (key2342, -2), (key2080, 1), (key2080, 1), (key2288, -2), (key2288, -2), (key2348, 1), (key2348, 1), (key2084, -2), (key2291, 1), (key2291, 1), (key2177, -1), (key2177, -1), (key2344, 1), (key2344, 1), (key2080, -1), (key2080, -1), (key2288, 1), (key2288, 1), (key2188, 1), (key2188, 1), (key2350, -1), (key2350, -1), (key2089, 1), (key2089, 1), (key2296, -1), (key2296, -1), (key2181, 2), (key2283, -1), (key2283, -1), (key2084, 2), (key2291, -1), (key2291, -1), (key2089, -1), (key2089, -1), (key2191, -1), (key2191, -1), (key2296, 2), (key2296, 2)]

theorem rawRowCheck7237 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form7 = rawRow7237 := by decide +kernel

def row7237 : Integer.Sparse Key := [(key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2277, 2), (key2283, -2), (key2288, -2), (key2296, 2), (key2342, -2), (key2344, 2), (key2348, 2), (key2350, -2)]

theorem rowCheck7237 : row7237 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7237 := by decide +kernel

theorem rowEval7237 (x : Key → ℝ) : Integer.Sparse.eval row7237 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form7) x := by
  rw [rowCheck7237, Integer.Sparse.eval_collectBalanced, rawRowCheck7237]

def rawRow7238 : Integer.Sparse Key := [(key2277, 1), (key2342, 1), (key2277, -2), (key2288, 1), (key2348, 1), (key2080, -2), (key2348, -2), (key2080, 1), (key2288, 1), (key2291, -2), (key2084, 1), (key2291, 1), (key2280, -1), (key2344, -1), (key2177, 1), (key2280, 1), (key2288, -1), (key2348, -1), (key2080, 1), (key2348, 1), (key2086, 1), (key2350, 1), (key2086, -1), (key2188, -1), (key2191, 1), (key2296, 1), (key2089, -1), (key2191, -1), (key2283, 2), (key2181, -1), (key2283, -1), (key2291, 2), (key2084, -1), (key2291, -1), (key2191, -1), (key2296, -1), (key2089, -1), (key2296, -1), (key2089, 2), (key2191, 2)]

theorem rawRowCheck7238 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form7 = rawRow7238 := by decide +kernel

def row7238 : Integer.Sparse Key := [(key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2277, -1), (key2283, 1), (key2288, 1), (key2296, -1), (key2342, 1), (key2344, -1), (key2348, -1), (key2350, 1)]

theorem rowCheck7238 : row7238 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7238 := by decide +kernel

theorem rowEval7238 (x : Key → ℝ) : Integer.Sparse.eval row7238 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form7) x := by
  rw [rowCheck7238, Integer.Sparse.eval_collectBalanced, rawRowCheck7238]

def rawRow7239 : Integer.Sparse Key := [(key2342, 1), (key2277, 1), (key2277, -2), (key2348, 1), (key2288, 1), (key2348, -2), (key2080, -2), (key2288, 1), (key2080, 1), (key2291, -2), (key2291, 1), (key2084, 1), (key2344, -1), (key2280, -1), (key2280, 1), (key2177, 1), (key2348, -1), (key2288, -1), (key2348, 1), (key2080, 1), (key2350, 1), (key2086, 1), (key2188, -1), (key2086, -1), (key2296, 1), (key2191, 1), (key2191, -1), (key2089, -1), (key2283, 2), (key2283, -1), (key2181, -1), (key2291, 2), (key2291, -1), (key2084, -1), (key2296, -1), (key2191, -1), (key2296, -1), (key2089, -1), (key2191, 2), (key2089, 2)]

theorem rawRowCheck7239 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form7 = rawRow7239 := by decide +kernel

def row7239 : Integer.Sparse Key := [(key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2277, -1), (key2283, 1), (key2288, 1), (key2296, -1), (key2342, 1), (key2344, -1), (key2348, -1), (key2350, 1)]

theorem rowCheck7239 : row7239 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7239 := by decide +kernel

theorem rowEval7239 (x : Key → ℝ) : Integer.Sparse.eval row7239 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form7) x := by
  rw [rowCheck7239, Integer.Sparse.eval_collectBalanced, rawRowCheck7239]

def rawRow7240 : Integer.Sparse Key := [(key2288, 1), (key2291, 1), (key2348, -2), (key2080, 1), (key2084, 1), (key2277, -2), (key2291, -2), (key2342, 1), (key2348, 1), (key2080, -2), (key2277, 1), (key2288, 1), (key2188, -1), (key2191, -1), (key2348, 1), (key2350, 1), (key2086, -1), (key2089, -1), (key2280, 1), (key2296, 1), (key2177, 1), (key2191, 1), (key2344, -1), (key2348, -1), (key2080, 1), (key2086, 1), (key2280, -1), (key2288, -1), (key2191, 2), (key2291, -1), (key2296, -1), (key2089, 2), (key2283, -1), (key2296, -1), (key2084, -1), (key2089, -1), (key2181, -1), (key2191, -1), (key2283, 2), (key2291, 2)]

theorem rawRowCheck7240 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form7 = rawRow7240 := by decide +kernel

def row7240 : Integer.Sparse Key := [(key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2277, -1), (key2283, 1), (key2288, 1), (key2296, -1), (key2342, 1), (key2344, -1), (key2348, -1), (key2350, 1)]

theorem rowCheck7240 : row7240 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7240 := by decide +kernel

theorem rowEval7240 (x : Key → ℝ) : Integer.Sparse.eval row7240 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form7) x := by
  rw [rowCheck7240, Integer.Sparse.eval_collectBalanced, rawRowCheck7240]

def rawRow7241 : Integer.Sparse Key := [(key2291, 1), (key2288, 1), (key2348, -2), (key2084, 1), (key2080, 1), (key2291, -2), (key2277, -2), (key2348, 1), (key2342, 1), (key2080, -2), (key2288, 1), (key2277, 1), (key2191, -1), (key2188, -1), (key2350, 1), (key2348, 1), (key2089, -1), (key2086, -1), (key2296, 1), (key2280, 1), (key2191, 1), (key2177, 1), (key2348, -1), (key2344, -1), (key2086, 1), (key2080, 1), (key2288, -1), (key2280, -1), (key2191, 2), (key2296, -1), (key2291, -1), (key2089, 2), (key2296, -1), (key2283, -1), (key2089, -1), (key2084, -1), (key2191, -1), (key2181, -1), (key2291, 2), (key2283, 2)]

theorem rawRowCheck7241 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form7 = rawRow7241 := by decide +kernel

def row7241 : Integer.Sparse Key := [(key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2277, -1), (key2283, 1), (key2288, 1), (key2296, -1), (key2342, 1), (key2344, -1), (key2348, -1), (key2350, 1)]

theorem rowCheck7241 : row7241 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7241 := by decide +kernel

theorem rowEval7241 (x : Key → ℝ) : Integer.Sparse.eval row7241 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck7241, Integer.Sparse.eval_collectBalanced, rawRowCheck7241]

def rawRow7242 : Integer.Sparse Key := [(key2288, 1), (key2348, 1), (key2291, -2), (key2277, 1), (key2342, 1), (key2080, -2), (key2348, -2), (key2084, 1), (key2291, 1), (key2277, -2), (key2080, 1), (key2288, 1), (key2288, -1), (key2348, -1), (key2191, 1), (key2296, 1), (key2280, -1), (key2344, -1), (key2086, 1), (key2350, 1), (key2080, 1), (key2348, 1), (key2089, -1), (key2191, -1), (key2177, 1), (key2280, 1), (key2086, -1), (key2188, -1), (key2291, 2), (key2191, -1), (key2296, -1), (key2283, 2), (key2089, -1), (key2296, -1), (key2181, -1), (key2283, -1), (key2084, -1), (key2291, -1), (key2089, 2), (key2191, 2)]

theorem rawRowCheck7242 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form7 = rawRow7242 := by decide +kernel

def row7242 : Integer.Sparse Key := [(key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2277, -1), (key2283, 1), (key2288, 1), (key2296, -1), (key2342, 1), (key2344, -1), (key2348, -1), (key2350, 1)]

theorem rowCheck7242 : row7242 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7242 := by decide +kernel

theorem rowEval7242 (x : Key → ℝ) : Integer.Sparse.eval row7242 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form7) x := by
  rw [rowCheck7242, Integer.Sparse.eval_collectBalanced, rawRowCheck7242]

def rawRow7243 : Integer.Sparse Key := [(key2348, 1), (key2288, 1), (key2291, -2), (key2342, 1), (key2277, 1), (key2348, -2), (key2080, -2), (key2291, 1), (key2084, 1), (key2277, -2), (key2288, 1), (key2080, 1), (key2348, -1), (key2288, -1), (key2296, 1), (key2191, 1), (key2344, -1), (key2280, -1), (key2350, 1), (key2086, 1), (key2348, 1), (key2080, 1), (key2191, -1), (key2089, -1), (key2280, 1), (key2177, 1), (key2188, -1), (key2086, -1), (key2291, 2), (key2296, -1), (key2191, -1), (key2283, 2), (key2296, -1), (key2089, -1), (key2283, -1), (key2181, -1), (key2291, -1), (key2084, -1), (key2191, 2), (key2089, 2)]

theorem rawRowCheck7243 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form7 = rawRow7243 := by decide +kernel

def row7243 : Integer.Sparse Key := [(key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2277, -1), (key2283, 1), (key2288, 1), (key2296, -1), (key2342, 1), (key2344, -1), (key2348, -1), (key2350, 1)]

theorem rowCheck7243 : row7243 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7243 := by decide +kernel

theorem rowEval7243 (x : Key → ℝ) : Integer.Sparse.eval row7243 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form7) x := by
  rw [rowCheck7243, Integer.Sparse.eval_collectBalanced, rawRowCheck7243]

def rawRow7244 : Integer.Sparse Key := [(key2291, 1), (key2348, 1), (key2288, -2), (key2291, 1), (key2348, 1), (key2084, -2), (key2342, -2), (key2080, 1), (key2277, 1), (key2288, -2), (key2080, 1), (key2277, 1), (key2296, -1), (key2350, -1), (key2188, 1), (key2288, 1), (key2296, -1), (key2350, -1), (key2089, 1), (key2344, 1), (key2089, 1), (key2344, 1), (key2080, -1), (key2177, -1), (key2188, 1), (key2288, 1), (key2080, -1), (key2177, -1), (key2296, 2), (key2191, -1), (key2291, -1), (key2296, 2), (key2089, -1), (key2283, -1), (key2191, -1), (key2291, -1), (key2089, -1), (key2283, -1), (key2084, 2), (key2181, 2)]

theorem rawRowCheck7244 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form7 = rawRow7244 := by decide +kernel

def row7244 : Integer.Sparse Key := [(key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2277, 2), (key2283, -2), (key2288, -2), (key2296, 2), (key2342, -2), (key2344, 2), (key2348, 2), (key2350, -2)]

theorem rowCheck7244 : row7244 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7244 := by decide +kernel

theorem rowEval7244 (x : Key → ℝ) : Integer.Sparse.eval row7244 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck7244, Integer.Sparse.eval_collectBalanced, rawRowCheck7244]

def rawRow7245 : Integer.Sparse Key := [(key2348, 1), (key2291, 1), (key2288, -2), (key2348, 1), (key2291, 1), (key2342, -2), (key2084, -2), (key2277, 1), (key2080, 1), (key2288, -2), (key2277, 1), (key2080, 1), (key2350, -1), (key2296, -1), (key2288, 1), (key2188, 1), (key2350, -1), (key2296, -1), (key2344, 1), (key2089, 1), (key2344, 1), (key2089, 1), (key2177, -1), (key2080, -1), (key2288, 1), (key2188, 1), (key2177, -1), (key2080, -1), (key2296, 2), (key2291, -1), (key2191, -1), (key2296, 2), (key2283, -1), (key2089, -1), (key2291, -1), (key2191, -1), (key2283, -1), (key2089, -1), (key2181, 2), (key2084, 2)]

theorem rawRowCheck7245 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form7 = rawRow7245 := by decide +kernel

def row7245 : Integer.Sparse Key := [(key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2277, 2), (key2283, -2), (key2288, -2), (key2296, 2), (key2342, -2), (key2344, 2), (key2348, 2), (key2350, -2)]

theorem rowCheck7245 : row7245 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7245 := by decide +kernel

theorem rowEval7245 (x : Key → ℝ) : Integer.Sparse.eval row7245 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form7) x := by
  rw [rowCheck7245, Integer.Sparse.eval_collectBalanced, rawRowCheck7245]

def rawRow7246 : Integer.Sparse Key := [(key2086, 1), (key2089, 1), (key2089, -2), (key2280, 1), (key2283, 1), (key2280, -2), (key2296, -2), (key2283, 1), (key2296, 1), (key2344, -2), (key2344, 1), (key2350, 1), (key2080, -1), (key2084, -1), (key2084, 1), (key2089, 1), (key2177, -1), (key2181, -1), (key2177, 1), (key2191, 1), (key2277, 1), (key2291, 1), (key2283, -1), (key2291, -1), (key2342, 1), (key2344, 1), (key2344, -1), (key2348, -1), (key2080, 2), (key2080, -1), (key2086, -1), (key2177, 2), (key2177, -1), (key2188, -1), (key2277, -1), (key2280, -1), (key2277, -1), (key2288, -1), (key2280, 2), (key2288, 2)]

theorem rawRowCheck7246 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form7 = rawRow7246 := by decide +kernel

def row7246 : Integer.Sparse Key := [(key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2277, -1), (key2283, 1), (key2288, 1), (key2296, -1), (key2342, 1), (key2344, -1), (key2348, -1), (key2350, 1)]

theorem rowCheck7246 : row7246 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7246 := by decide +kernel

theorem rowEval7246 (x : Key → ℝ) : Integer.Sparse.eval row7246 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form7) x := by
  rw [rowCheck7246, Integer.Sparse.eval_collectBalanced, rawRowCheck7246]

def rawRow7247 : Integer.Sparse Key := [(key2089, 1), (key2086, 1), (key2089, -2), (key2283, 1), (key2280, 1), (key2296, -2), (key2280, -2), (key2296, 1), (key2283, 1), (key2344, -2), (key2350, 1), (key2344, 1), (key2084, -1), (key2080, -1), (key2089, 1), (key2084, 1), (key2181, -1), (key2177, -1), (key2191, 1), (key2177, 1), (key2291, 1), (key2277, 1), (key2291, -1), (key2283, -1), (key2344, 1), (key2342, 1), (key2348, -1), (key2344, -1), (key2080, 2), (key2086, -1), (key2080, -1), (key2177, 2), (key2188, -1), (key2177, -1), (key2280, -1), (key2277, -1), (key2288, -1), (key2277, -1), (key2288, 2), (key2280, 2)]

theorem rawRowCheck7247 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form7 = rawRow7247 := by decide +kernel

def row7247 : Integer.Sparse Key := [(key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2277, -1), (key2283, 1), (key2288, 1), (key2296, -1), (key2342, 1), (key2344, -1), (key2348, -1), (key2350, 1)]

theorem rowCheck7247 : row7247 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7247 := by decide +kernel

theorem rowEval7247 (x : Key → ℝ) : Integer.Sparse.eval row7247 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck7247, Integer.Sparse.eval_collectBalanced, rawRowCheck7247]

def rawRow7248 : Integer.Sparse Key := [(key2089, 1), (key2089, 1), (key2086, -2), (key2296, 1), (key2296, 1), (key2283, -2), (key2283, -2), (key2280, 1), (key2280, 1), (key2350, -2), (key2344, 1), (key2344, 1), (key2089, -1), (key2089, -1), (key2080, 1), (key2080, 1), (key2191, -1), (key2191, -1), (key2181, 1), (key2181, 1), (key2283, 1), (key2283, 1), (key2277, -1), (key2277, -1), (key2348, 1), (key2348, 1), (key2342, -1), (key2342, -1), (key2086, 2), (key2080, -1), (key2080, -1), (key2188, 2), (key2177, -1), (key2177, -1), (key2288, -1), (key2288, -1), (key2280, -1), (key2280, -1), (key2277, 2), (key2277, 2)]

theorem rawRowCheck7248 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form7 = rawRow7248 := by decide +kernel

def row7248 : Integer.Sparse Key := [(key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2277, 2), (key2283, -2), (key2288, -2), (key2296, 2), (key2342, -2), (key2344, 2), (key2348, 2), (key2350, -2)]

theorem rowCheck7248 : row7248 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7248 := by decide +kernel

theorem rowEval7248 (x : Key → ℝ) : Integer.Sparse.eval row7248 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck7248, Integer.Sparse.eval_collectBalanced, rawRowCheck7248]

def rawRow7249 : Integer.Sparse Key := [(key2280, 1), (key2283, 1), (key2344, -2), (key2086, 1), (key2089, 1), (key2280, -2), (key2296, -2), (key2344, 1), (key2350, 1), (key2089, -2), (key2283, 1), (key2296, 1), (key2177, -1), (key2181, -1), (key2342, 1), (key2344, 1), (key2080, -1), (key2084, -1), (key2277, 1), (key2291, 1), (key2177, 1), (key2191, 1), (key2344, -1), (key2348, -1), (key2084, 1), (key2089, 1), (key2283, -1), (key2291, -1), (key2177, 2), (key2277, -1), (key2280, -1), (key2080, 2), (key2277, -1), (key2288, -1), (key2080, -1), (key2086, -1), (key2177, -1), (key2188, -1), (key2280, 2), (key2288, 2)]

theorem rawRowCheck7249 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form7 = rawRow7249 := by decide +kernel

def row7249 : Integer.Sparse Key := [(key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2277, -1), (key2283, 1), (key2288, 1), (key2296, -1), (key2342, 1), (key2344, -1), (key2348, -1), (key2350, 1)]

theorem rowCheck7249 : row7249 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7249 := by decide +kernel

theorem rowEval7249 (x : Key → ℝ) : Integer.Sparse.eval row7249 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form7) x := by
  rw [rowCheck7249, Integer.Sparse.eval_collectBalanced, rawRowCheck7249]

def rawRow7250 : Integer.Sparse Key := [(key2283, 1), (key2280, 1), (key2344, -2), (key2089, 1), (key2086, 1), (key2296, -2), (key2280, -2), (key2350, 1), (key2344, 1), (key2089, -2), (key2296, 1), (key2283, 1), (key2181, -1), (key2177, -1), (key2344, 1), (key2342, 1), (key2084, -1), (key2080, -1), (key2291, 1), (key2277, 1), (key2191, 1), (key2177, 1), (key2348, -1), (key2344, -1), (key2089, 1), (key2084, 1), (key2291, -1), (key2283, -1), (key2177, 2), (key2280, -1), (key2277, -1), (key2080, 2), (key2288, -1), (key2277, -1), (key2086, -1), (key2080, -1), (key2188, -1), (key2177, -1), (key2288, 2), (key2280, 2)]

theorem rawRowCheck7250 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form7 = rawRow7250 := by decide +kernel

def row7250 : Integer.Sparse Key := [(key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2277, -1), (key2283, 1), (key2288, 1), (key2296, -1), (key2342, 1), (key2344, -1), (key2348, -1), (key2350, 1)]

theorem rowCheck7250 : row7250 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7250 := by decide +kernel

theorem rowEval7250 (x : Key → ℝ) : Integer.Sparse.eval row7250 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck7250, Integer.Sparse.eval_collectBalanced, rawRowCheck7250]

def rawRow7251 : Integer.Sparse Key := [(key2280, 1), (key2344, 1), (key2283, -2), (key2280, 1), (key2344, 1), (key2086, -2), (key2350, -2), (key2089, 1), (key2296, 1), (key2283, -2), (key2089, 1), (key2296, 1), (key2277, -1), (key2342, -1), (key2181, 1), (key2283, 1), (key2277, -1), (key2342, -1), (key2080, 1), (key2348, 1), (key2080, 1), (key2348, 1), (key2089, -1), (key2191, -1), (key2181, 1), (key2283, 1), (key2089, -1), (key2191, -1), (key2277, 2), (key2177, -1), (key2280, -1), (key2277, 2), (key2080, -1), (key2288, -1), (key2177, -1), (key2280, -1), (key2080, -1), (key2288, -1), (key2086, 2), (key2188, 2)]

theorem rawRowCheck7251 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form7 = rawRow7251 := by decide +kernel

def row7251 : Integer.Sparse Key := [(key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2277, 2), (key2283, -2), (key2288, -2), (key2296, 2), (key2342, -2), (key2344, 2), (key2348, 2), (key2350, -2)]

theorem rowCheck7251 : row7251 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7251 := by decide +kernel

theorem rowEval7251 (x : Key → ℝ) : Integer.Sparse.eval row7251 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form7) x := by
  rw [rowCheck7251, Integer.Sparse.eval_collectBalanced, rawRowCheck7251]

def rawRow7252 : Integer.Sparse Key := [(key2344, 1), (key2280, 1), (key2283, -2), (key2344, 1), (key2280, 1), (key2350, -2), (key2086, -2), (key2296, 1), (key2089, 1), (key2283, -2), (key2296, 1), (key2089, 1), (key2342, -1), (key2277, -1), (key2283, 1), (key2181, 1), (key2342, -1), (key2277, -1), (key2348, 1), (key2080, 1), (key2348, 1), (key2080, 1), (key2191, -1), (key2089, -1), (key2283, 1), (key2181, 1), (key2191, -1), (key2089, -1), (key2277, 2), (key2280, -1), (key2177, -1), (key2277, 2), (key2288, -1), (key2080, -1), (key2280, -1), (key2177, -1), (key2288, -1), (key2080, -1), (key2188, 2), (key2086, 2)]

theorem rawRowCheck7252 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form7 = rawRow7252 := by decide +kernel

def row7252 : Integer.Sparse Key := [(key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2277, 2), (key2283, -2), (key2288, -2), (key2296, 2), (key2342, -2), (key2344, 2), (key2348, 2), (key2350, -2)]

theorem rowCheck7252 : row7252 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7252 := by decide +kernel

theorem rowEval7252 (x : Key → ℝ) : Integer.Sparse.eval row7252 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form7) x := by
  rw [rowCheck7252, Integer.Sparse.eval_collectBalanced, rawRowCheck7252]

def rawRow7253 : Integer.Sparse Key := [(key2283, 1), (key2344, 1), (key2280, -2), (key2296, 1), (key2350, 1), (key2089, -2), (key2344, -2), (key2086, 1), (key2280, 1), (key2296, -2), (key2089, 1), (key2283, 1), (key2283, -1), (key2344, -1), (key2177, 1), (key2277, 1), (key2291, -1), (key2348, -1), (key2084, 1), (key2342, 1), (key2089, 1), (key2344, 1), (key2080, -1), (key2177, -1), (key2191, 1), (key2291, 1), (key2084, -1), (key2181, -1), (key2280, 2), (key2177, -1), (key2277, -1), (key2288, 2), (key2080, -1), (key2277, -1), (key2188, -1), (key2288, -1), (key2086, -1), (key2280, -1), (key2080, 2), (key2177, 2)]

theorem rawRowCheck7253 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form7 = rawRow7253 := by decide +kernel

def row7253 : Integer.Sparse Key := [(key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2277, -1), (key2283, 1), (key2288, 1), (key2296, -1), (key2342, 1), (key2344, -1), (key2348, -1), (key2350, 1)]

theorem rowCheck7253 : row7253 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7253 := by decide +kernel

theorem rowEval7253 (x : Key → ℝ) : Integer.Sparse.eval row7253 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck7253, Integer.Sparse.eval_collectBalanced, rawRowCheck7253]

def rawRow7254 : Integer.Sparse Key := [(key2344, 1), (key2283, 1), (key2280, -2), (key2350, 1), (key2296, 1), (key2344, -2), (key2089, -2), (key2280, 1), (key2086, 1), (key2296, -2), (key2283, 1), (key2089, 1), (key2344, -1), (key2283, -1), (key2277, 1), (key2177, 1), (key2348, -1), (key2291, -1), (key2342, 1), (key2084, 1), (key2344, 1), (key2089, 1), (key2177, -1), (key2080, -1), (key2291, 1), (key2191, 1), (key2181, -1), (key2084, -1), (key2280, 2), (key2277, -1), (key2177, -1), (key2288, 2), (key2277, -1), (key2080, -1), (key2288, -1), (key2188, -1), (key2280, -1), (key2086, -1), (key2177, 2), (key2080, 2)]

theorem rawRowCheck7254 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form7 = rawRow7254 := by decide +kernel

def row7254 : Integer.Sparse Key := [(key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2277, -1), (key2283, 1), (key2288, 1), (key2296, -1), (key2342, 1), (key2344, -1), (key2348, -1), (key2350, 1)]

theorem rowCheck7254 : row7254 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7254 := by decide +kernel

theorem rowEval7254 (x : Key → ℝ) : Integer.Sparse.eval row7254 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form7) x := by
  rw [rowCheck7254, Integer.Sparse.eval_collectBalanced, rawRowCheck7254]

def rawRow7255 : Integer.Sparse Key := [(key2296, 1), (key2296, 1), (key2350, -2), (key2089, 1), (key2089, 1), (key2283, -2), (key2283, -2), (key2344, 1), (key2344, 1), (key2086, -2), (key2280, 1), (key2280, 1), (key2191, -1), (key2191, -1), (key2348, 1), (key2348, 1), (key2089, -1), (key2089, -1), (key2283, 1), (key2283, 1), (key2181, 1), (key2181, 1), (key2342, -1), (key2342, -1), (key2080, 1), (key2080, 1), (key2277, -1), (key2277, -1), (key2188, 2), (key2288, -1), (key2288, -1), (key2086, 2), (key2280, -1), (key2280, -1), (key2080, -1), (key2080, -1), (key2177, -1), (key2177, -1), (key2277, 2), (key2277, 2)]

theorem rawRowCheck7255 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form7 = rawRow7255 := by decide +kernel

def row7255 : Integer.Sparse Key := [(key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2277, 2), (key2283, -2), (key2288, -2), (key2296, 2), (key2342, -2), (key2344, 2), (key2348, 2), (key2350, -2)]

theorem rowCheck7255 : row7255 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7255 := by decide +kernel

theorem rowEval7255 (x : Key → ℝ) : Integer.Sparse.eval row7255 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck7255, Integer.Sparse.eval_collectBalanced, rawRowCheck7255]

def rawRow7256 : Integer.Sparse Key := [(key2296, 1), (key2350, 1), (key2296, -2), (key2283, 1), (key2344, 1), (key2089, -2), (key2344, -2), (key2089, 1), (key2283, 1), (key2280, -2), (key2086, 1), (key2280, 1), (key2291, -1), (key2348, -1), (key2191, 1), (key2291, 1), (key2283, -1), (key2344, -1), (key2089, 1), (key2344, 1), (key2084, 1), (key2342, 1), (key2084, -1), (key2181, -1), (key2177, 1), (key2277, 1), (key2080, -1), (key2177, -1), (key2288, 2), (key2188, -1), (key2288, -1), (key2280, 2), (key2086, -1), (key2280, -1), (key2177, -1), (key2277, -1), (key2080, -1), (key2277, -1), (key2080, 2), (key2177, 2)]

theorem rawRowCheck7256 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form7 = rawRow7256 := by decide +kernel

def row7256 : Integer.Sparse Key := [(key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2277, -1), (key2283, 1), (key2288, 1), (key2296, -1), (key2342, 1), (key2344, -1), (key2348, -1), (key2350, 1)]

theorem rowCheck7256 : row7256 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7256 := by decide +kernel

theorem rowEval7256 (x : Key → ℝ) : Integer.Sparse.eval row7256 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck7256, Integer.Sparse.eval_collectBalanced, rawRowCheck7256]

def rawRow7257 : Integer.Sparse Key := [(key2350, 1), (key2296, 1), (key2296, -2), (key2344, 1), (key2283, 1), (key2344, -2), (key2089, -2), (key2283, 1), (key2089, 1), (key2280, -2), (key2280, 1), (key2086, 1), (key2348, -1), (key2291, -1), (key2291, 1), (key2191, 1), (key2344, -1), (key2283, -1), (key2344, 1), (key2089, 1), (key2342, 1), (key2084, 1), (key2181, -1), (key2084, -1), (key2277, 1), (key2177, 1), (key2177, -1), (key2080, -1), (key2288, 2), (key2288, -1), (key2188, -1), (key2280, 2), (key2280, -1), (key2086, -1), (key2277, -1), (key2177, -1), (key2277, -1), (key2080, -1), (key2177, 2), (key2080, 2)]

theorem rawRowCheck7257 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form7 = rawRow7257 := by decide +kernel

def row7257 : Integer.Sparse Key := [(key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2277, -1), (key2283, 1), (key2288, 1), (key2296, -1), (key2342, 1), (key2344, -1), (key2348, -1), (key2350, 1)]

theorem rowCheck7257 : row7257 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7257 := by decide +kernel

theorem rowEval7257 (x : Key → ℝ) : Integer.Sparse.eval row7257 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form7) x := by
  rw [rowCheck7257, Integer.Sparse.eval_collectBalanced, rawRowCheck7257]

def rawRow7258 : Integer.Sparse Key := [(key2081, -2), (key2083, 1), (key2083, 1), (key2081, -2), (key2088, 1), (key2088, 1), (key2083, 1), (key2083, 1), (key2088, 1), (key2088, 1), (key2090, -2), (key2090, -2), (key2278, 2), (key2282, -1), (key2282, -1), (key2278, 2), (key2290, -1), (key2290, -1), (key2282, -1), (key2282, -1), (key2290, -1), (key2290, -1), (key2298, 2), (key2298, 2), (key2329, -1), (key2329, -1), (key2332, 1), (key2332, 1), (key2329, -1), (key2329, -1), (key2334, 1), (key2334, 1), (key2334, 1), (key2334, 1), (key2339, -1), (key2339, -1), (key2332, 1), (key2332, 1), (key2339, -1), (key2339, -1)]

theorem rawRowCheck7258 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form8 = rawRow7258 := by decide +kernel

def row7258 : Integer.Sparse Key := [(key2081, -4), (key2083, 4), (key2088, 4), (key2090, -4), (key2278, 4), (key2282, -4), (key2290, -4), (key2298, 4), (key2329, -4), (key2332, 4), (key2334, 4), (key2339, -4)]

theorem rowCheck7258 : row7258 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7258 := by decide +kernel

theorem rowEval7258 (x : Key → ℝ) : Integer.Sparse.eval row7258 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck7258, Integer.Sparse.eval_collectBalanced, rawRowCheck7258]

def rawRow7259 : Integer.Sparse Key := [(key2083, -2), (key2081, 1), (key2083, 1), (key2088, -2), (key2081, 1), (key2088, 1), (key2088, 1), (key2090, 1), (key2083, 1), (key2090, 1), (key2083, -2), (key2088, -2), (key2282, 2), (key2278, -1), (key2282, -1), (key2290, 2), (key2278, -1), (key2290, -1), (key2290, -1), (key2298, -1), (key2282, -1), (key2298, -1), (key2282, 2), (key2290, 2), (key2331, -1), (key2332, -1), (key2329, 1), (key2331, 1), (key2334, -1), (key2335, -1), (key2329, 1), (key2335, 1), (key2331, 1), (key2339, 1), (key2331, -1), (key2334, -1), (key2335, 1), (key2339, 1), (key2332, -1), (key2335, -1)]

theorem rawRowCheck7259 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form8 = rawRow7259 := by decide +kernel

def row7259 : Integer.Sparse Key := [(key2081, 2), (key2083, -2), (key2088, -2), (key2090, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2332, -2), (key2334, -2), (key2339, 2)]

theorem rowCheck7259 : row7259 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7259 := by decide +kernel

theorem rowEval7259 (x : Key → ℝ) : Integer.Sparse.eval row7259 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck7259, Integer.Sparse.eval_collectBalanced, rawRowCheck7259]

def rawRow7260 : Integer.Sparse Key := [(key2083, -2), (key2083, 1), (key2081, 1), (key2088, -2), (key2088, 1), (key2081, 1), (key2090, 1), (key2088, 1), (key2090, 1), (key2083, 1), (key2088, -2), (key2083, -2), (key2282, 2), (key2282, -1), (key2278, -1), (key2290, 2), (key2290, -1), (key2278, -1), (key2298, -1), (key2290, -1), (key2298, -1), (key2282, -1), (key2290, 2), (key2282, 2), (key2332, -1), (key2331, -1), (key2331, 1), (key2329, 1), (key2335, -1), (key2334, -1), (key2335, 1), (key2329, 1), (key2339, 1), (key2331, 1), (key2334, -1), (key2331, -1), (key2339, 1), (key2335, 1), (key2335, -1), (key2332, -1)]

theorem rawRowCheck7260 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form8 = rawRow7260 := by decide +kernel

def row7260 : Integer.Sparse Key := [(key2081, 2), (key2083, -2), (key2088, -2), (key2090, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2332, -2), (key2334, -2), (key2339, 2)]

theorem rowCheck7260 : row7260 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7260 := by decide +kernel

theorem rowEval7260 (x : Key → ℝ) : Integer.Sparse.eval row7260 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form8) x := by
  rw [rowCheck7260, Integer.Sparse.eval_collectBalanced, rawRowCheck7260]

def rawRow7261 : Integer.Sparse Key := [(key2088, -2), (key2088, 1), (key2090, 1), (key2083, -2), (key2083, 1), (key2090, 1), (key2081, 1), (key2083, 1), (key2081, 1), (key2088, 1), (key2083, -2), (key2088, -2), (key2290, 2), (key2290, -1), (key2298, -1), (key2282, 2), (key2282, -1), (key2298, -1), (key2278, -1), (key2282, -1), (key2278, -1), (key2290, -1), (key2282, 2), (key2290, 2), (key2334, -1), (key2335, -1), (key2335, 1), (key2339, 1), (key2331, -1), (key2332, -1), (key2331, 1), (key2339, 1), (key2329, 1), (key2335, 1), (key2332, -1), (key2335, -1), (key2329, 1), (key2331, 1), (key2331, -1), (key2334, -1)]

theorem rawRowCheck7261 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form8 = rawRow7261 := by decide +kernel

def row7261 : Integer.Sparse Key := [(key2081, 2), (key2083, -2), (key2088, -2), (key2090, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2332, -2), (key2334, -2), (key2339, 2)]

theorem rowCheck7261 : row7261 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7261 := by decide +kernel

theorem rowEval7261 (x : Key → ℝ) : Integer.Sparse.eval row7261 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck7261, Integer.Sparse.eval_collectBalanced, rawRowCheck7261]

def rawRow7262 : Integer.Sparse Key := [(key2088, -2), (key2090, 1), (key2088, 1), (key2083, -2), (key2090, 1), (key2083, 1), (key2083, 1), (key2081, 1), (key2088, 1), (key2081, 1), (key2088, -2), (key2083, -2), (key2290, 2), (key2298, -1), (key2290, -1), (key2282, 2), (key2298, -1), (key2282, -1), (key2282, -1), (key2278, -1), (key2290, -1), (key2278, -1), (key2290, 2), (key2282, 2), (key2335, -1), (key2334, -1), (key2339, 1), (key2335, 1), (key2332, -1), (key2331, -1), (key2339, 1), (key2331, 1), (key2335, 1), (key2329, 1), (key2335, -1), (key2332, -1), (key2331, 1), (key2329, 1), (key2334, -1), (key2331, -1)]

theorem rawRowCheck7262 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form8 = rawRow7262 := by decide +kernel

def row7262 : Integer.Sparse Key := [(key2081, 2), (key2083, -2), (key2088, -2), (key2090, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2332, -2), (key2334, -2), (key2339, 2)]

theorem rowCheck7262 : row7262 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7262 := by decide +kernel

theorem rowEval7262 (x : Key → ℝ) : Integer.Sparse.eval row7262 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form8) x := by
  rw [rowCheck7262, Integer.Sparse.eval_collectBalanced, rawRowCheck7262]

def rawRow7263 : Integer.Sparse Key := [(key2090, -2), (key2088, 1), (key2088, 1), (key2090, -2), (key2083, 1), (key2083, 1), (key2088, 1), (key2088, 1), (key2083, 1), (key2083, 1), (key2081, -2), (key2081, -2), (key2298, 2), (key2290, -1), (key2290, -1), (key2298, 2), (key2282, -1), (key2282, -1), (key2290, -1), (key2290, -1), (key2282, -1), (key2282, -1), (key2278, 2), (key2278, 2), (key2339, -1), (key2339, -1), (key2334, 1), (key2334, 1), (key2339, -1), (key2339, -1), (key2332, 1), (key2332, 1), (key2332, 1), (key2332, 1), (key2329, -1), (key2329, -1), (key2334, 1), (key2334, 1), (key2329, -1), (key2329, -1)]

theorem rawRowCheck7263 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form8 = rawRow7263 := by decide +kernel

def row7263 : Integer.Sparse Key := [(key2081, -4), (key2083, 4), (key2088, 4), (key2090, -4), (key2278, 4), (key2282, -4), (key2290, -4), (key2298, 4), (key2329, -4), (key2332, 4), (key2334, 4), (key2339, -4)]

theorem rowCheck7263 : row7263 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7263 := by decide +kernel

theorem rowEval7263 (x : Key → ℝ) : Integer.Sparse.eval row7263 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form8) x := by
  rw [rowCheck7263, Integer.Sparse.eval_collectBalanced, rawRowCheck7263]

def rawRow7264 : Integer.Sparse Key := [(key2178, -2), (key2180, 1), (key2180, 1), (key2278, -2), (key2282, 1), (key2282, 1), (key2329, 1), (key2329, 1), (key2331, 1), (key2331, 1), (key2332, -2), (key2332, -2), (key2081, 2), (key2088, -1), (key2088, -1), (key2178, 2), (key2190, -1), (key2190, -1), (key2331, -1), (key2331, -1), (key2334, -1), (key2334, -1), (key2339, 2), (key2339, 2), (key2083, -1), (key2083, -1), (key2090, 1), (key2090, 1), (key2180, -1), (key2180, -1), (key2190, 1), (key2190, 1), (key2290, 1), (key2290, 1), (key2298, -1), (key2298, -1), (key2332, 1), (key2332, 1), (key2339, -1), (key2339, -1)]

theorem rawRowCheck7264 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form8 = rawRow7264 := by decide +kernel

def row7264 : Integer.Sparse Key := [(key2081, 2), (key2083, -2), (key2088, -2), (key2090, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2332, -2), (key2334, -2), (key2339, 2)]

theorem rowCheck7264 : row7264 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7264 := by decide +kernel

theorem rowEval7264 (x : Key → ℝ) : Integer.Sparse.eval row7264 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck7264, Integer.Sparse.eval_collectBalanced, rawRowCheck7264]

def rawRow7265 : Integer.Sparse Key := [(key2180, -2), (key2178, 1), (key2180, 1), (key2282, -2), (key2278, 1), (key2282, 1), (key2331, 1), (key2332, 1), (key2329, 1), (key2332, 1), (key2329, -2), (key2331, -2), (key2088, 2), (key2081, -1), (key2088, -1), (key2190, 2), (key2178, -1), (key2190, -1), (key2334, -1), (key2339, -1), (key2331, -1), (key2339, -1), (key2331, 2), (key2334, 2), (key2088, -1), (key2090, -1), (key2083, 1), (key2088, 1), (key2190, -1), (key2192, -1), (key2180, 1), (key2192, 1), (key2282, 1), (key2298, 1), (key2282, -1), (key2290, -1), (key2335, 1), (key2339, 1), (key2332, -1), (key2335, -1)]

theorem rawRowCheck7265 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form8 = rawRow7265 := by decide +kernel

def row7265 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

theorem rowCheck7265 : row7265 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7265 := by decide +kernel

theorem rowEval7265 (x : Key → ℝ) : Integer.Sparse.eval row7265 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck7265, Integer.Sparse.eval_collectBalanced, rawRowCheck7265]

def rawRow7266 : Integer.Sparse Key := [(key2180, -2), (key2180, 1), (key2178, 1), (key2282, -2), (key2282, 1), (key2278, 1), (key2332, 1), (key2331, 1), (key2332, 1), (key2329, 1), (key2331, -2), (key2329, -2), (key2088, 2), (key2088, -1), (key2081, -1), (key2190, 2), (key2190, -1), (key2178, -1), (key2339, -1), (key2334, -1), (key2339, -1), (key2331, -1), (key2334, 2), (key2331, 2), (key2090, -1), (key2088, -1), (key2088, 1), (key2083, 1), (key2192, -1), (key2190, -1), (key2192, 1), (key2180, 1), (key2298, 1), (key2282, 1), (key2290, -1), (key2282, -1), (key2339, 1), (key2335, 1), (key2335, -1), (key2332, -1)]

theorem rawRowCheck7266 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form8 = rawRow7266 := by decide +kernel

def row7266 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

theorem rowCheck7266 : row7266 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7266 := by decide +kernel

theorem rowEval7266 (x : Key → ℝ) : Integer.Sparse.eval row7266 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form8) x := by
  rw [rowCheck7266, Integer.Sparse.eval_collectBalanced, rawRowCheck7266]

def rawRow7267 : Integer.Sparse Key := [(key2278, -2), (key2329, 1), (key2329, 1), (key2178, -2), (key2331, 1), (key2331, 1), (key2180, 1), (key2180, 1), (key2282, 1), (key2282, 1), (key2332, -2), (key2332, -2), (key2178, 2), (key2331, -1), (key2331, -1), (key2081, 2), (key2334, -1), (key2334, -1), (key2088, -1), (key2088, -1), (key2190, -1), (key2190, -1), (key2339, 2), (key2339, 2), (key2180, -1), (key2180, -1), (key2332, 1), (key2332, 1), (key2083, -1), (key2083, -1), (key2290, 1), (key2290, 1), (key2190, 1), (key2190, 1), (key2339, -1), (key2339, -1), (key2090, 1), (key2090, 1), (key2298, -1), (key2298, -1)]

theorem rawRowCheck7267 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form8 = rawRow7267 := by decide +kernel

def row7267 : Integer.Sparse Key := [(key2081, 2), (key2083, -2), (key2088, -2), (key2090, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2332, -2), (key2334, -2), (key2339, 2)]

theorem rowCheck7267 : row7267 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7267 := by decide +kernel

theorem rowEval7267 (x : Key → ℝ) : Integer.Sparse.eval row7267 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck7267, Integer.Sparse.eval_collectBalanced, rawRowCheck7267]

def rawRow7268 : Integer.Sparse Key := [(key2329, -2), (key2278, 1), (key2329, 1), (key2331, -2), (key2178, 1), (key2331, 1), (key2282, 1), (key2332, 1), (key2180, 1), (key2332, 1), (key2180, -2), (key2282, -2), (key2331, 2), (key2178, -1), (key2331, -1), (key2334, 2), (key2081, -1), (key2334, -1), (key2190, -1), (key2339, -1), (key2088, -1), (key2339, -1), (key2088, 2), (key2190, 2), (key2282, -1), (key2332, -1), (key2180, 1), (key2282, 1), (key2290, -1), (key2335, -1), (key2083, 1), (key2335, 1), (key2088, 1), (key2339, 1), (key2088, -1), (key2190, -1), (key2192, 1), (key2298, 1), (key2090, -1), (key2192, -1)]

theorem rawRowCheck7268 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form8 = rawRow7268 := by decide +kernel

def row7268 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

theorem rowCheck7268 : row7268 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7268 := by decide +kernel

theorem rowEval7268 (x : Key → ℝ) : Integer.Sparse.eval row7268 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck7268, Integer.Sparse.eval_collectBalanced, rawRowCheck7268]

def rawRow7269 : Integer.Sparse Key := [(key2329, -2), (key2329, 1), (key2278, 1), (key2331, -2), (key2331, 1), (key2178, 1), (key2332, 1), (key2282, 1), (key2332, 1), (key2180, 1), (key2282, -2), (key2180, -2), (key2331, 2), (key2331, -1), (key2178, -1), (key2334, 2), (key2334, -1), (key2081, -1), (key2339, -1), (key2190, -1), (key2339, -1), (key2088, -1), (key2190, 2), (key2088, 2), (key2332, -1), (key2282, -1), (key2282, 1), (key2180, 1), (key2335, -1), (key2290, -1), (key2335, 1), (key2083, 1), (key2339, 1), (key2088, 1), (key2190, -1), (key2088, -1), (key2298, 1), (key2192, 1), (key2192, -1), (key2090, -1)]

theorem rawRowCheck7269 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form8 = rawRow7269 := by decide +kernel

def row7269 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

theorem rowCheck7269 : row7269 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7269 := by decide +kernel

theorem rowEval7269 (x : Key → ℝ) : Integer.Sparse.eval row7269 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form8) x := by
  rw [rowCheck7269, Integer.Sparse.eval_collectBalanced, rawRowCheck7269]

def rawRow7270 : Integer.Sparse Key := [(key2282, -2), (key2331, 1), (key2332, 1), (key2180, -2), (key2329, 1), (key2332, 1), (key2178, 1), (key2180, 1), (key2278, 1), (key2282, 1), (key2329, -2), (key2331, -2), (key2190, 2), (key2334, -1), (key2339, -1), (key2088, 2), (key2331, -1), (key2339, -1), (key2081, -1), (key2088, -1), (key2178, -1), (key2190, -1), (key2331, 2), (key2334, 2), (key2190, -1), (key2192, -1), (key2335, 1), (key2339, 1), (key2088, -1), (key2090, -1), (key2282, 1), (key2298, 1), (key2180, 1), (key2192, 1), (key2332, -1), (key2335, -1), (key2083, 1), (key2088, 1), (key2282, -1), (key2290, -1)]

theorem rawRowCheck7270 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form8 = rawRow7270 := by decide +kernel

def row7270 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

theorem rowCheck7270 : row7270 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7270 := by decide +kernel

theorem rowEval7270 (x : Key → ℝ) : Integer.Sparse.eval row7270 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck7270, Integer.Sparse.eval_collectBalanced, rawRowCheck7270]

def rawRow7271 : Integer.Sparse Key := [(key2282, -2), (key2332, 1), (key2331, 1), (key2180, -2), (key2332, 1), (key2329, 1), (key2180, 1), (key2178, 1), (key2282, 1), (key2278, 1), (key2331, -2), (key2329, -2), (key2190, 2), (key2339, -1), (key2334, -1), (key2088, 2), (key2339, -1), (key2331, -1), (key2088, -1), (key2081, -1), (key2190, -1), (key2178, -1), (key2334, 2), (key2331, 2), (key2192, -1), (key2190, -1), (key2339, 1), (key2335, 1), (key2090, -1), (key2088, -1), (key2298, 1), (key2282, 1), (key2192, 1), (key2180, 1), (key2335, -1), (key2332, -1), (key2088, 1), (key2083, 1), (key2290, -1), (key2282, -1)]

theorem rawRowCheck7271 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form8 = rawRow7271 := by decide +kernel

def row7271 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

theorem rowCheck7271 : row7271 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7271 := by decide +kernel

theorem rowEval7271 (x : Key → ℝ) : Integer.Sparse.eval row7271 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form8) x := by
  rw [rowCheck7271, Integer.Sparse.eval_collectBalanced, rawRowCheck7271]

def rawRow7272 : Integer.Sparse Key := [(key2331, -2), (key2282, 1), (key2332, 1), (key2329, -2), (key2180, 1), (key2332, 1), (key2278, 1), (key2329, 1), (key2178, 1), (key2331, 1), (key2180, -2), (key2282, -2), (key2334, 2), (key2190, -1), (key2339, -1), (key2331, 2), (key2088, -1), (key2339, -1), (key2178, -1), (key2331, -1), (key2081, -1), (key2334, -1), (key2088, 2), (key2190, 2), (key2290, -1), (key2335, -1), (key2192, 1), (key2298, 1), (key2282, -1), (key2332, -1), (key2088, 1), (key2339, 1), (key2083, 1), (key2335, 1), (key2090, -1), (key2192, -1), (key2180, 1), (key2282, 1), (key2088, -1), (key2190, -1)]

theorem rawRowCheck7272 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form8 = rawRow7272 := by decide +kernel

def row7272 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

theorem rowCheck7272 : row7272 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7272 := by decide +kernel

theorem rowEval7272 (x : Key → ℝ) : Integer.Sparse.eval row7272 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck7272, Integer.Sparse.eval_collectBalanced, rawRowCheck7272]

def rawRow7273 : Integer.Sparse Key := [(key2331, -2), (key2332, 1), (key2282, 1), (key2329, -2), (key2332, 1), (key2180, 1), (key2329, 1), (key2278, 1), (key2331, 1), (key2178, 1), (key2282, -2), (key2180, -2), (key2334, 2), (key2339, -1), (key2190, -1), (key2331, 2), (key2339, -1), (key2088, -1), (key2331, -1), (key2178, -1), (key2334, -1), (key2081, -1), (key2190, 2), (key2088, 2), (key2335, -1), (key2290, -1), (key2298, 1), (key2192, 1), (key2332, -1), (key2282, -1), (key2339, 1), (key2088, 1), (key2335, 1), (key2083, 1), (key2192, -1), (key2090, -1), (key2282, 1), (key2180, 1), (key2190, -1), (key2088, -1)]

theorem rawRowCheck7273 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form8 = rawRow7273 := by decide +kernel

def row7273 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

theorem rowCheck7273 : row7273 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7273 := by decide +kernel

theorem rowEval7273 (x : Key → ℝ) : Integer.Sparse.eval row7273 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form8) x := by
  rw [rowCheck7273, Integer.Sparse.eval_collectBalanced, rawRowCheck7273]

def rawRow7274 : Integer.Sparse Key := [(key2332, -2), (key2282, 1), (key2331, 1), (key2332, -2), (key2180, 1), (key2329, 1), (key2282, 1), (key2331, 1), (key2180, 1), (key2329, 1), (key2178, -2), (key2278, -2), (key2339, 2), (key2190, -1), (key2334, -1), (key2339, 2), (key2088, -1), (key2331, -1), (key2190, -1), (key2334, -1), (key2088, -1), (key2331, -1), (key2081, 2), (key2178, 2), (key2298, -1), (key2339, -1), (key2190, 1), (key2290, 1), (key2298, -1), (key2339, -1), (key2090, 1), (key2332, 1), (key2090, 1), (key2332, 1), (key2083, -1), (key2180, -1), (key2190, 1), (key2290, 1), (key2083, -1), (key2180, -1)]

theorem rawRowCheck7274 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form8 = rawRow7274 := by decide +kernel

def row7274 : Integer.Sparse Key := [(key2081, 2), (key2083, -2), (key2088, -2), (key2090, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2332, -2), (key2334, -2), (key2339, 2)]

theorem rowCheck7274 : row7274 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7274 := by decide +kernel

theorem rowEval7274 (x : Key → ℝ) : Integer.Sparse.eval row7274 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form8) x := by
  rw [rowCheck7274, Integer.Sparse.eval_collectBalanced, rawRowCheck7274]

def rawRow7275 : Integer.Sparse Key := [(key2332, -2), (key2331, 1), (key2282, 1), (key2332, -2), (key2329, 1), (key2180, 1), (key2331, 1), (key2282, 1), (key2329, 1), (key2180, 1), (key2278, -2), (key2178, -2), (key2339, 2), (key2334, -1), (key2190, -1), (key2339, 2), (key2331, -1), (key2088, -1), (key2334, -1), (key2190, -1), (key2331, -1), (key2088, -1), (key2178, 2), (key2081, 2), (key2339, -1), (key2298, -1), (key2290, 1), (key2190, 1), (key2339, -1), (key2298, -1), (key2332, 1), (key2090, 1), (key2332, 1), (key2090, 1), (key2180, -1), (key2083, -1), (key2290, 1), (key2190, 1), (key2180, -1), (key2083, -1)]

theorem rawRowCheck7275 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form8 = rawRow7275 := by decide +kernel

def row7275 : Integer.Sparse Key := [(key2081, 2), (key2083, -2), (key2088, -2), (key2090, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2332, -2), (key2334, -2), (key2339, 2)]

theorem rowCheck7275 : row7275 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7275 := by decide +kernel

theorem rowEval7275 (x : Key → ℝ) : Integer.Sparse.eval row7275 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form8) x := by
  rw [rowCheck7275, Integer.Sparse.eval_collectBalanced, rawRowCheck7275]

def rawRow7276 : Integer.Sparse Key := [(key2190, -2), (key2190, 1), (key2192, 1), (key2290, -2), (key2290, 1), (key2298, 1), (key2334, 1), (key2335, 1), (key2334, 1), (key2339, 1), (key2335, -2), (key2339, -2), (key2083, 2), (key2083, -1), (key2090, -1), (key2180, 2), (key2180, -1), (key2192, -1), (key2329, -1), (key2332, -1), (key2329, -1), (key2335, -1), (key2332, 2), (key2335, 2), (key2081, -1), (key2083, -1), (key2083, 1), (key2088, 1), (key2178, -1), (key2180, -1), (key2178, 1), (key2190, 1), (key2278, 1), (key2290, 1), (key2282, -1), (key2290, -1), (key2329, 1), (key2331, 1), (key2331, -1), (key2334, -1)]

theorem rawRowCheck7276 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form8 = rawRow7276 := by decide +kernel

def row7276 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

theorem rowCheck7276 : row7276 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7276 := by decide +kernel

theorem rowEval7276 (x : Key → ℝ) : Integer.Sparse.eval row7276 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck7276, Integer.Sparse.eval_collectBalanced, rawRowCheck7276]

def rawRow7277 : Integer.Sparse Key := [(key2190, -2), (key2192, 1), (key2190, 1), (key2290, -2), (key2298, 1), (key2290, 1), (key2335, 1), (key2334, 1), (key2339, 1), (key2334, 1), (key2339, -2), (key2335, -2), (key2083, 2), (key2090, -1), (key2083, -1), (key2180, 2), (key2192, -1), (key2180, -1), (key2332, -1), (key2329, -1), (key2335, -1), (key2329, -1), (key2335, 2), (key2332, 2), (key2083, -1), (key2081, -1), (key2088, 1), (key2083, 1), (key2180, -1), (key2178, -1), (key2190, 1), (key2178, 1), (key2290, 1), (key2278, 1), (key2290, -1), (key2282, -1), (key2331, 1), (key2329, 1), (key2334, -1), (key2331, -1)]

theorem rawRowCheck7277 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form8 = rawRow7277 := by decide +kernel

def row7277 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

theorem rowCheck7277 : row7277 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7277 := by decide +kernel

theorem rowEval7277 (x : Key → ℝ) : Integer.Sparse.eval row7277 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form8) x := by
  rw [rowCheck7277, Integer.Sparse.eval_collectBalanced, rawRowCheck7277]

def rawRow7278 : Integer.Sparse Key := [(key2192, -2), (key2190, 1), (key2190, 1), (key2298, -2), (key2290, 1), (key2290, 1), (key2339, 1), (key2339, 1), (key2335, 1), (key2335, 1), (key2334, -2), (key2334, -2), (key2090, 2), (key2083, -1), (key2083, -1), (key2192, 2), (key2180, -1), (key2180, -1), (key2335, -1), (key2335, -1), (key2332, -1), (key2332, -1), (key2329, 2), (key2329, 2), (key2088, -1), (key2088, -1), (key2081, 1), (key2081, 1), (key2190, -1), (key2190, -1), (key2180, 1), (key2180, 1), (key2282, 1), (key2282, 1), (key2278, -1), (key2278, -1), (key2334, 1), (key2334, 1), (key2329, -1), (key2329, -1)]

theorem rawRowCheck7278 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form8 = rawRow7278 := by decide +kernel

def row7278 : Integer.Sparse Key := [(key2081, 2), (key2083, -2), (key2088, -2), (key2090, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2332, -2), (key2334, -2), (key2339, 2)]

theorem rowCheck7278 : row7278 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7278 := by decide +kernel

theorem rowEval7278 (x : Key → ℝ) : Integer.Sparse.eval row7278 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form8) x := by
  rw [rowCheck7278, Integer.Sparse.eval_collectBalanced, rawRowCheck7278]

def rawRow7279 : Integer.Sparse Key := [(key2290, -2), (key2334, 1), (key2335, 1), (key2190, -2), (key2334, 1), (key2339, 1), (key2190, 1), (key2192, 1), (key2290, 1), (key2298, 1), (key2335, -2), (key2339, -2), (key2180, 2), (key2329, -1), (key2332, -1), (key2083, 2), (key2329, -1), (key2335, -1), (key2083, -1), (key2090, -1), (key2180, -1), (key2192, -1), (key2332, 2), (key2335, 2), (key2178, -1), (key2180, -1), (key2329, 1), (key2331, 1), (key2081, -1), (key2083, -1), (key2278, 1), (key2290, 1), (key2178, 1), (key2190, 1), (key2331, -1), (key2334, -1), (key2083, 1), (key2088, 1), (key2282, -1), (key2290, -1)]

theorem rawRowCheck7279 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form8 = rawRow7279 := by decide +kernel

def row7279 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

theorem rowCheck7279 : row7279 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7279 := by decide +kernel

theorem rowEval7279 (x : Key → ℝ) : Integer.Sparse.eval row7279 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck7279, Integer.Sparse.eval_collectBalanced, rawRowCheck7279]

def rawRow7280 : Integer.Sparse Key := [(key2290, -2), (key2335, 1), (key2334, 1), (key2190, -2), (key2339, 1), (key2334, 1), (key2192, 1), (key2190, 1), (key2298, 1), (key2290, 1), (key2339, -2), (key2335, -2), (key2180, 2), (key2332, -1), (key2329, -1), (key2083, 2), (key2335, -1), (key2329, -1), (key2090, -1), (key2083, -1), (key2192, -1), (key2180, -1), (key2335, 2), (key2332, 2), (key2180, -1), (key2178, -1), (key2331, 1), (key2329, 1), (key2083, -1), (key2081, -1), (key2290, 1), (key2278, 1), (key2190, 1), (key2178, 1), (key2334, -1), (key2331, -1), (key2088, 1), (key2083, 1), (key2290, -1), (key2282, -1)]

theorem rawRowCheck7280 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form8 = rawRow7280 := by decide +kernel

def row7280 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

theorem rowCheck7280 : row7280 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7280 := by decide +kernel

theorem rowEval7280 (x : Key → ℝ) : Integer.Sparse.eval row7280 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form8) x := by
  rw [rowCheck7280, Integer.Sparse.eval_collectBalanced, rawRowCheck7280]

def rawRow7281 : Integer.Sparse Key := [(key2334, -2), (key2290, 1), (key2335, 1), (key2334, -2), (key2190, 1), (key2339, 1), (key2290, 1), (key2335, 1), (key2190, 1), (key2339, 1), (key2192, -2), (key2298, -2), (key2329, 2), (key2180, -1), (key2332, -1), (key2329, 2), (key2083, -1), (key2335, -1), (key2180, -1), (key2332, -1), (key2083, -1), (key2335, -1), (key2090, 2), (key2192, 2), (key2278, -1), (key2329, -1), (key2180, 1), (key2282, 1), (key2278, -1), (key2329, -1), (key2081, 1), (key2334, 1), (key2081, 1), (key2334, 1), (key2088, -1), (key2190, -1), (key2180, 1), (key2282, 1), (key2088, -1), (key2190, -1)]

theorem rawRowCheck7281 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form8 = rawRow7281 := by decide +kernel

def row7281 : Integer.Sparse Key := [(key2081, 2), (key2083, -2), (key2088, -2), (key2090, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2332, -2), (key2334, -2), (key2339, 2)]

theorem rowCheck7281 : row7281 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7281 := by decide +kernel

theorem rowEval7281 (x : Key → ℝ) : Integer.Sparse.eval row7281 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck7281, Integer.Sparse.eval_collectBalanced, rawRowCheck7281]

def rawRow7282 : Integer.Sparse Key := [(key2334, -2), (key2335, 1), (key2290, 1), (key2334, -2), (key2339, 1), (key2190, 1), (key2335, 1), (key2290, 1), (key2339, 1), (key2190, 1), (key2298, -2), (key2192, -2), (key2329, 2), (key2332, -1), (key2180, -1), (key2329, 2), (key2335, -1), (key2083, -1), (key2332, -1), (key2180, -1), (key2335, -1), (key2083, -1), (key2192, 2), (key2090, 2), (key2329, -1), (key2278, -1), (key2282, 1), (key2180, 1), (key2329, -1), (key2278, -1), (key2334, 1), (key2081, 1), (key2334, 1), (key2081, 1), (key2190, -1), (key2088, -1), (key2282, 1), (key2180, 1), (key2190, -1), (key2088, -1)]

theorem rawRowCheck7282 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form8 = rawRow7282 := by decide +kernel

def row7282 : Integer.Sparse Key := [(key2081, 2), (key2083, -2), (key2088, -2), (key2090, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2332, -2), (key2334, -2), (key2339, 2)]

theorem rowCheck7282 : row7282 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7282 := by decide +kernel

theorem rowEval7282 (x : Key → ℝ) : Integer.Sparse.eval row7282 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form8) x := by
  rw [rowCheck7282, Integer.Sparse.eval_collectBalanced, rawRowCheck7282]

def rawRow7283 : Integer.Sparse Key := [(key2335, -2), (key2290, 1), (key2334, 1), (key2339, -2), (key2190, 1), (key2334, 1), (key2298, 1), (key2339, 1), (key2192, 1), (key2335, 1), (key2190, -2), (key2290, -2), (key2332, 2), (key2180, -1), (key2329, -1), (key2335, 2), (key2083, -1), (key2329, -1), (key2192, -1), (key2335, -1), (key2090, -1), (key2332, -1), (key2083, 2), (key2180, 2), (key2282, -1), (key2331, -1), (key2178, 1), (key2278, 1), (key2290, -1), (key2334, -1), (key2083, 1), (key2329, 1), (key2088, 1), (key2331, 1), (key2081, -1), (key2178, -1), (key2190, 1), (key2290, 1), (key2083, -1), (key2180, -1)]

theorem rawRowCheck7283 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form8 = rawRow7283 := by decide +kernel

def row7283 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

theorem rowCheck7283 : row7283 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7283 := by decide +kernel

theorem rowEval7283 (x : Key → ℝ) : Integer.Sparse.eval row7283 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form8) x := by
  rw [rowCheck7283, Integer.Sparse.eval_collectBalanced, rawRowCheck7283]

def rawRow7284 : Integer.Sparse Key := [(key2335, -2), (key2334, 1), (key2290, 1), (key2339, -2), (key2334, 1), (key2190, 1), (key2339, 1), (key2298, 1), (key2335, 1), (key2192, 1), (key2290, -2), (key2190, -2), (key2332, 2), (key2329, -1), (key2180, -1), (key2335, 2), (key2329, -1), (key2083, -1), (key2335, -1), (key2192, -1), (key2332, -1), (key2090, -1), (key2180, 2), (key2083, 2), (key2331, -1), (key2282, -1), (key2278, 1), (key2178, 1), (key2334, -1), (key2290, -1), (key2329, 1), (key2083, 1), (key2331, 1), (key2088, 1), (key2178, -1), (key2081, -1), (key2290, 1), (key2190, 1), (key2180, -1), (key2083, -1)]

theorem rawRowCheck7284 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form8 = rawRow7284 := by decide +kernel

def row7284 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

theorem rowCheck7284 : row7284 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7284 := by decide +kernel

theorem rowEval7284 (x : Key → ℝ) : Integer.Sparse.eval row7284 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form8) x := by
  rw [rowCheck7284, Integer.Sparse.eval_collectBalanced, rawRowCheck7284]

def rawRow7285 : Integer.Sparse Key := [(key2298, -2), (key2339, 1), (key2339, 1), (key2192, -2), (key2335, 1), (key2335, 1), (key2190, 1), (key2190, 1), (key2290, 1), (key2290, 1), (key2334, -2), (key2334, -2), (key2192, 2), (key2335, -1), (key2335, -1), (key2090, 2), (key2332, -1), (key2332, -1), (key2083, -1), (key2083, -1), (key2180, -1), (key2180, -1), (key2329, 2), (key2329, 2), (key2190, -1), (key2190, -1), (key2334, 1), (key2334, 1), (key2088, -1), (key2088, -1), (key2282, 1), (key2282, 1), (key2180, 1), (key2180, 1), (key2329, -1), (key2329, -1), (key2081, 1), (key2081, 1), (key2278, -1), (key2278, -1)]

theorem rawRowCheck7285 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form8 = rawRow7285 := by decide +kernel

def row7285 : Integer.Sparse Key := [(key2081, 2), (key2083, -2), (key2088, -2), (key2090, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2332, -2), (key2334, -2), (key2339, 2)]

theorem rowCheck7285 : row7285 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7285 := by decide +kernel

theorem rowEval7285 (x : Key → ℝ) : Integer.Sparse.eval row7285 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form8) x := by
  rw [rowCheck7285, Integer.Sparse.eval_collectBalanced, rawRowCheck7285]

def rawRow7286 : Integer.Sparse Key := [(key2339, -2), (key2298, 1), (key2339, 1), (key2335, -2), (key2192, 1), (key2335, 1), (key2290, 1), (key2334, 1), (key2190, 1), (key2334, 1), (key2190, -2), (key2290, -2), (key2335, 2), (key2192, -1), (key2335, -1), (key2332, 2), (key2090, -1), (key2332, -1), (key2180, -1), (key2329, -1), (key2083, -1), (key2329, -1), (key2083, 2), (key2180, 2), (key2290, -1), (key2334, -1), (key2190, 1), (key2290, 1), (key2282, -1), (key2331, -1), (key2088, 1), (key2331, 1), (key2083, 1), (key2329, 1), (key2083, -1), (key2180, -1), (key2178, 1), (key2278, 1), (key2081, -1), (key2178, -1)]

theorem rawRowCheck7286 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form8 = rawRow7286 := by decide +kernel

def row7286 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

theorem rowCheck7286 : row7286 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7286 := by decide +kernel

theorem rowEval7286 (x : Key → ℝ) : Integer.Sparse.eval row7286 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form8) x := by
  rw [rowCheck7286, Integer.Sparse.eval_collectBalanced, rawRowCheck7286]

def rawRow7287 : Integer.Sparse Key := [(key2339, -2), (key2339, 1), (key2298, 1), (key2335, -2), (key2335, 1), (key2192, 1), (key2334, 1), (key2290, 1), (key2334, 1), (key2190, 1), (key2290, -2), (key2190, -2), (key2335, 2), (key2335, -1), (key2192, -1), (key2332, 2), (key2332, -1), (key2090, -1), (key2329, -1), (key2180, -1), (key2329, -1), (key2083, -1), (key2180, 2), (key2083, 2), (key2334, -1), (key2290, -1), (key2290, 1), (key2190, 1), (key2331, -1), (key2282, -1), (key2331, 1), (key2088, 1), (key2329, 1), (key2083, 1), (key2180, -1), (key2083, -1), (key2278, 1), (key2178, 1), (key2178, -1), (key2081, -1)]

theorem rawRowCheck7287 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form8 = rawRow7287 := by decide +kernel

def row7287 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

theorem rowCheck7287 : row7287 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7287 := by decide +kernel

theorem rowEval7287 (x : Key → ℝ) : Integer.Sparse.eval row7287 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form8) x := by
  rw [rowCheck7287, Integer.Sparse.eval_collectBalanced, rawRowCheck7287]

def rawRow7288 : Integer.Sparse Key := [(key822, 1), (key822, 1), (key823, -2), (key822, 1), (key822, 1), (key827, -2), (key827, -2), (key828, 1), (key828, 1), (key823, -2), (key828, 1), (key828, 1), (key906, -2), (key906, -2), (key910, 1), (key910, 1), (key911, 1), (key911, 1), (key910, 1), (key910, 1), (key918, -2), (key911, 1), (key911, 1), (key918, -2), (key952, 4), (key953, -2), (key953, -2), (key953, -2), (key953, -2), (key957, 4)]

theorem rawRowCheck7288 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form9 = rawRow7288 := by decide +kernel

def row7288 : Integer.Sparse Key := [(key822, 4), (key823, -4), (key827, -4), (key828, 4), (key906, -4), (key910, 4), (key911, 4), (key918, -4), (key952, 4), (key953, -8), (key957, 4)]

theorem rowCheck7288 : row7288 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7288 := by decide +kernel

theorem rowEval7288 (x : Key → ℝ) : Integer.Sparse.eval row7288 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7288, Integer.Sparse.eval_collectBalanced, rawRowCheck7288]

def rawRow7289 : Integer.Sparse Key := [(key822, 1), (key823, 1), (key822, -2), (key827, 1), (key828, 1), (key822, -2), (key828, -2), (key822, 1), (key827, 1), (key828, -2), (key823, 1), (key828, 1), (key910, -2), (key911, -2), (key906, 1), (key911, 1), (key906, 1), (key910, 1), (key910, 1), (key918, 1), (key910, -2), (key911, 1), (key918, 1), (key911, -2), (key953, 4), (key952, -2), (key953, -2), (key953, -2), (key957, -2), (key953, 4)]

theorem rawRowCheck7289 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form9 = rawRow7289 := by decide +kernel

def row7289 : Integer.Sparse Key := [(key822, -2), (key823, 2), (key827, 2), (key828, -2), (key906, 2), (key910, -2), (key911, -2), (key918, 2), (key952, -2), (key953, 4), (key957, -2)]

theorem rowCheck7289 : row7289 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7289 := by decide +kernel

theorem rowEval7289 (x : Key → ℝ) : Integer.Sparse.eval row7289 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7289, Integer.Sparse.eval_collectBalanced, rawRowCheck7289]

def rawRow7290 : Integer.Sparse Key := [(key823, 1), (key822, 1), (key822, -2), (key828, 1), (key827, 1), (key828, -2), (key822, -2), (key827, 1), (key822, 1), (key828, -2), (key828, 1), (key823, 1), (key911, -2), (key910, -2), (key911, 1), (key906, 1), (key910, 1), (key906, 1), (key918, 1), (key910, 1), (key910, -2), (key918, 1), (key911, 1), (key911, -2), (key953, 4), (key953, -2), (key952, -2), (key957, -2), (key953, -2), (key953, 4)]

theorem rawRowCheck7290 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form9 = rawRow7290 := by decide +kernel

def row7290 : Integer.Sparse Key := [(key822, -2), (key823, 2), (key827, 2), (key828, -2), (key906, 2), (key910, -2), (key911, -2), (key918, 2), (key952, -2), (key953, 4), (key957, -2)]

theorem rowCheck7290 : row7290 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7290 := by decide +kernel

theorem rowEval7290 (x : Key → ℝ) : Integer.Sparse.eval row7290 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7290, Integer.Sparse.eval_collectBalanced, rawRowCheck7290]

def rawRow7291 : Integer.Sparse Key := [(key827, 1), (key828, 1), (key828, -2), (key822, 1), (key823, 1), (key822, -2), (key828, -2), (key823, 1), (key828, 1), (key822, -2), (key822, 1), (key827, 1), (key910, -2), (key911, -2), (key910, 1), (key918, 1), (key911, 1), (key918, 1), (key906, 1), (key911, 1), (key911, -2), (key906, 1), (key910, 1), (key910, -2), (key953, 4), (key953, -2), (key957, -2), (key952, -2), (key953, -2), (key953, 4)]

theorem rawRowCheck7291 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form9 = rawRow7291 := by decide +kernel

def row7291 : Integer.Sparse Key := [(key822, -2), (key823, 2), (key827, 2), (key828, -2), (key906, 2), (key910, -2), (key911, -2), (key918, 2), (key952, -2), (key953, 4), (key957, -2)]

theorem rowCheck7291 : row7291 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7291 := by decide +kernel

theorem rowEval7291 (x : Key → ℝ) : Integer.Sparse.eval row7291 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7291, Integer.Sparse.eval_collectBalanced, rawRowCheck7291]

def rawRow7292 : Integer.Sparse Key := [(key828, 1), (key827, 1), (key828, -2), (key823, 1), (key822, 1), (key828, -2), (key822, -2), (key828, 1), (key823, 1), (key822, -2), (key827, 1), (key822, 1), (key911, -2), (key910, -2), (key918, 1), (key910, 1), (key918, 1), (key911, 1), (key911, 1), (key906, 1), (key911, -2), (key910, 1), (key906, 1), (key910, -2), (key953, 4), (key957, -2), (key953, -2), (key953, -2), (key952, -2), (key953, 4)]

theorem rawRowCheck7292 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form9 = rawRow7292 := by decide +kernel

def row7292 : Integer.Sparse Key := [(key822, -2), (key823, 2), (key827, 2), (key828, -2), (key906, 2), (key910, -2), (key911, -2), (key918, 2), (key952, -2), (key953, 4), (key957, -2)]

theorem rowCheck7292 : row7292 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7292 := by decide +kernel

theorem rowEval7292 (x : Key → ℝ) : Integer.Sparse.eval row7292 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7292, Integer.Sparse.eval_collectBalanced, rawRowCheck7292]

def rawRow7293 : Integer.Sparse Key := [(key828, 1), (key828, 1), (key827, -2), (key828, 1), (key828, 1), (key823, -2), (key823, -2), (key822, 1), (key822, 1), (key827, -2), (key822, 1), (key822, 1), (key918, -2), (key918, -2), (key911, 1), (key911, 1), (key910, 1), (key910, 1), (key911, 1), (key911, 1), (key906, -2), (key910, 1), (key910, 1), (key906, -2), (key957, 4), (key953, -2), (key953, -2), (key953, -2), (key953, -2), (key952, 4)]

theorem rawRowCheck7293 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form9 = rawRow7293 := by decide +kernel

def row7293 : Integer.Sparse Key := [(key822, 4), (key823, -4), (key827, -4), (key828, 4), (key906, -4), (key910, 4), (key911, 4), (key918, -4), (key952, 4), (key953, -8), (key957, 4)]

theorem rowCheck7293 : row7293 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7293 := by decide +kernel

theorem rowEval7293 (x : Key → ℝ) : Integer.Sparse.eval row7293 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7293, Integer.Sparse.eval_collectBalanced, rawRowCheck7293]

def rawRow7294 : Integer.Sparse Key := [(key822, 1), (key822, 1), (key823, -2), (key906, 1), (key906, 1), (key910, -2), (key910, -2), (key911, 1), (key911, 1), (key952, -2), (key953, 1), (key953, 1), (key822, -2), (key822, -2), (key827, 1), (key827, 1), (key828, 1), (key828, 1), (key910, 1), (key910, 1), (key918, -2), (key953, 1), (key953, 1), (key957, -2), (key823, 4), (key828, -2), (key828, -2), (key911, -2), (key911, -2), (key918, 4)]

theorem rawRowCheck7294 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form9 = rawRow7294 := by decide +kernel

def row7294 : Integer.Sparse Key := [(key822, -2), (key823, 2), (key827, 2), (key828, -2), (key906, 2), (key910, -2), (key911, -2), (key918, 2), (key952, -2), (key953, 4), (key957, -2)]

theorem rowCheck7294 : row7294 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7294 := by decide +kernel

theorem rowEval7294 (x : Key → ℝ) : Integer.Sparse.eval row7294 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7294, Integer.Sparse.eval_collectBalanced, rawRowCheck7294]

def rawRow7295 : Integer.Sparse Key := [(key822, 1), (key823, 1), (key822, -2), (key910, 1), (key911, 1), (key906, -2), (key911, -2), (key906, 1), (key910, 1), (key953, -2), (key952, 1), (key953, 1), (key827, -2), (key828, -2), (key822, 1), (key828, 1), (key822, 1), (key827, 1), (key910, 1), (key918, 1), (key910, -2), (key953, 1), (key957, 1), (key953, -2), (key828, 4), (key823, -2), (key828, -2), (key911, -2), (key918, -2), (key911, 4)]

theorem rawRowCheck7295 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form9 = rawRow7295 := by decide +kernel

def row7295 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

theorem rowCheck7295 : row7295 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7295 := by decide +kernel

theorem rowEval7295 (x : Key → ℝ) : Integer.Sparse.eval row7295 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7295, Integer.Sparse.eval_collectBalanced, rawRowCheck7295]

end MUB6.Certificate.GramRows

end OAI
