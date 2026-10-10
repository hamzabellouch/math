import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block24

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow2176 : Integer.Sparse Key := [(key994, -2), (key999, -2), (key999, -2), (key1013, 6), (key1029, 2), (key1034, 2), (key1034, 2), (key1121, -2), (key1121, -2), (key1197, -2), (key1069, -6), (key1148, 2), (key1148, 2), (key1210, 2)]

theorem rawRowCheck2176 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form3 = rawRow2176 := by decide +kernel

def row2176 : Integer.Sparse Key := [(key994, -2), (key999, -4), (key1013, 6), (key1029, 2), (key1034, 4), (key1069, -6), (key1121, -4), (key1148, 4), (key1197, -2), (key1210, 2)]

theorem rowCheck2176 : row2176 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2176 := by decide +kernel

theorem rowEval2176 (x : Key → ℝ) : Integer.Sparse.eval row2176 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2176, Integer.Sparse.eval_collectBalanced, rawRowCheck2176]

def rawRow2177 : Integer.Sparse Key := [(key999, -2), (key994, -2), (key999, -2), (key1013, 6), (key1034, 2), (key1029, 2), (key1034, 2), (key1121, -2), (key1197, -2), (key1121, -2), (key1069, -6), (key1148, 2), (key1210, 2), (key1148, 2)]

theorem rawRowCheck2177 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form3 = rawRow2177 := by decide +kernel

def row2177 : Integer.Sparse Key := [(key994, -2), (key999, -4), (key1013, 6), (key1029, 2), (key1034, 4), (key1069, -6), (key1121, -4), (key1148, 4), (key1197, -2), (key1210, 2)]

theorem rowCheck2177 : row2177 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2177 := by decide +kernel

theorem rowEval2177 (x : Key → ℝ) : Integer.Sparse.eval row2177 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2177, Integer.Sparse.eval_collectBalanced, rawRowCheck2177]

def rawRow2178 : Integer.Sparse Key := [(key999, -2), (key999, -2), (key994, -2), (key1013, 6), (key1034, 2), (key1034, 2), (key1029, 2), (key1197, -2), (key1121, -2), (key1121, -2), (key1069, -6), (key1210, 2), (key1148, 2), (key1148, 2)]

theorem rawRowCheck2178 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form3 = rawRow2178 := by decide +kernel

def row2178 : Integer.Sparse Key := [(key994, -2), (key999, -4), (key1013, 6), (key1029, 2), (key1034, 4), (key1069, -6), (key1121, -4), (key1148, 4), (key1197, -2), (key1210, 2)]

theorem rowCheck2178 : row2178 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2178 := by decide +kernel

theorem rowEval2178 (x : Key → ℝ) : Integer.Sparse.eval row2178 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2178, Integer.Sparse.eval_collectBalanced, rawRowCheck2178]

def rawRow2179 : Integer.Sparse Key := [(key994, -2), (key999, -2), (key1013, -2), (key999, 6), (key1107, 2), (key1112, 2), (key1121, 2), (key1034, -2), (key1112, -2), (key1191, -2), (key1148, -6), (key1069, 2), (key1148, 2), (key1210, 2)]

theorem rawRowCheck2179 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block1.form3 = rawRow2179 := by decide +kernel

def row2179 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1034, -2), (key1069, 2), (key1107, 2), (key1121, 2), (key1148, -4), (key1191, -2), (key1210, 2)]

theorem rowCheck2179 : row2179 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2179 := by decide +kernel

theorem rowEval2179 (x : Key → ℝ) : Integer.Sparse.eval row2179 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2179, Integer.Sparse.eval_collectBalanced, rawRowCheck2179]

def rawRow2180 : Integer.Sparse Key := [(key999, -2), (key994, -2), (key1013, -2), (key999, 6), (key1112, 2), (key1107, 2), (key1121, 2), (key1034, -2), (key1191, -2), (key1112, -2), (key1148, -6), (key1069, 2), (key1210, 2), (key1148, 2)]

theorem rawRowCheck2180 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block1.form3 = rawRow2180 := by decide +kernel

def row2180 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1034, -2), (key1069, 2), (key1107, 2), (key1121, 2), (key1148, -4), (key1191, -2), (key1210, 2)]

theorem rowCheck2180 : row2180 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2180 := by decide +kernel

theorem rowEval2180 (x : Key → ℝ) : Integer.Sparse.eval row2180 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2180, Integer.Sparse.eval_collectBalanced, rawRowCheck2180]

def rawRow2181 : Integer.Sparse Key := [(key994, -2), (key1013, -2), (key999, -2), (key999, 6), (key1107, 2), (key1121, 2), (key1112, 2), (key1112, -2), (key1034, -2), (key1191, -2), (key1148, -6), (key1148, 2), (key1069, 2), (key1210, 2)]

theorem rawRowCheck2181 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block1.form3 = rawRow2181 := by decide +kernel

def row2181 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1034, -2), (key1069, 2), (key1107, 2), (key1121, 2), (key1148, -4), (key1191, -2), (key1210, 2)]

theorem rowCheck2181 : row2181 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2181 := by decide +kernel

theorem rowEval2181 (x : Key → ℝ) : Integer.Sparse.eval row2181 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2181, Integer.Sparse.eval_collectBalanced, rawRowCheck2181]

def rawRow2182 : Integer.Sparse Key := [(key1013, -2), (key994, -2), (key999, -2), (key999, 6), (key1121, 2), (key1107, 2), (key1112, 2), (key1112, -2), (key1191, -2), (key1034, -2), (key1148, -6), (key1148, 2), (key1210, 2), (key1069, 2)]

theorem rawRowCheck2182 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block1.form3 = rawRow2182 := by decide +kernel

def row2182 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1034, -2), (key1069, 2), (key1107, 2), (key1121, 2), (key1148, -4), (key1191, -2), (key1210, 2)]

theorem rowCheck2182 : row2182 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2182 := by decide +kernel

theorem rowEval2182 (x : Key → ℝ) : Integer.Sparse.eval row2182 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2182, Integer.Sparse.eval_collectBalanced, rawRowCheck2182]

def rawRow2183 : Integer.Sparse Key := [(key999, -2), (key1013, -2), (key994, -2), (key999, 6), (key1112, 2), (key1121, 2), (key1107, 2), (key1191, -2), (key1034, -2), (key1112, -2), (key1148, -6), (key1210, 2), (key1069, 2), (key1148, 2)]

theorem rawRowCheck2183 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block1.form3 = rawRow2183 := by decide +kernel

def row2183 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1034, -2), (key1069, 2), (key1107, 2), (key1121, 2), (key1148, -4), (key1191, -2), (key1210, 2)]

theorem rowCheck2183 : row2183 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2183 := by decide +kernel

theorem rowEval2183 (x : Key → ℝ) : Integer.Sparse.eval row2183 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2183, Integer.Sparse.eval_collectBalanced, rawRowCheck2183]

def rawRow2184 : Integer.Sparse Key := [(key1013, -2), (key999, -2), (key994, -2), (key999, 6), (key1121, 2), (key1112, 2), (key1107, 2), (key1191, -2), (key1112, -2), (key1034, -2), (key1148, -6), (key1210, 2), (key1148, 2), (key1069, 2)]

theorem rawRowCheck2184 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block1.form3 = rawRow2184 := by decide +kernel

def row2184 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1034, -2), (key1069, 2), (key1107, 2), (key1121, 2), (key1148, -4), (key1191, -2), (key1210, 2)]

theorem rowCheck2184 : row2184 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2184 := by decide +kernel

theorem rowEval2184 (x : Key → ℝ) : Integer.Sparse.eval row2184 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2184, Integer.Sparse.eval_collectBalanced, rawRowCheck2184]

def rawRow2185 : Integer.Sparse Key := [(key1029, -2), (key1034, -2), (key1034, -2), (key1069, 6), (key994, 2), (key999, 2), (key999, 2), (key1148, -2), (key1148, -2), (key1210, -2), (key1013, -6), (key1121, 2), (key1121, 2), (key1197, 2)]

theorem rawRowCheck2185 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form3 = rawRow2185 := by decide +kernel

def row2185 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1013, -6), (key1029, -2), (key1034, -4), (key1069, 6), (key1121, 4), (key1148, -4), (key1197, 2), (key1210, -2)]

theorem rowCheck2185 : row2185 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2185 := by decide +kernel

theorem rowEval2185 (x : Key → ℝ) : Integer.Sparse.eval row2185 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2185, Integer.Sparse.eval_collectBalanced, rawRowCheck2185]

def rawRow2186 : Integer.Sparse Key := [(key1034, -2), (key1029, -2), (key1034, -2), (key1069, 6), (key999, 2), (key994, 2), (key999, 2), (key1148, -2), (key1210, -2), (key1148, -2), (key1013, -6), (key1121, 2), (key1197, 2), (key1121, 2)]

theorem rawRowCheck2186 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form3 = rawRow2186 := by decide +kernel

def row2186 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1013, -6), (key1029, -2), (key1034, -4), (key1069, 6), (key1121, 4), (key1148, -4), (key1197, 2), (key1210, -2)]

theorem rowCheck2186 : row2186 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2186 := by decide +kernel

theorem rowEval2186 (x : Key → ℝ) : Integer.Sparse.eval row2186 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2186, Integer.Sparse.eval_collectBalanced, rawRowCheck2186]

def rawRow2187 : Integer.Sparse Key := [(key1034, -2), (key1034, -2), (key1029, -2), (key1069, 6), (key999, 2), (key999, 2), (key994, 2), (key1210, -2), (key1148, -2), (key1148, -2), (key1013, -6), (key1197, 2), (key1121, 2), (key1121, 2)]

theorem rawRowCheck2187 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form3 = rawRow2187 := by decide +kernel

def row2187 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1013, -6), (key1029, -2), (key1034, -4), (key1069, 6), (key1121, 4), (key1148, -4), (key1197, 2), (key1210, -2)]

theorem rowCheck2187 : row2187 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2187 := by decide +kernel

theorem rowEval2187 (x : Key → ℝ) : Integer.Sparse.eval row2187 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2187, Integer.Sparse.eval_collectBalanced, rawRowCheck2187]

def rawRow2188 : Integer.Sparse Key := [(key1029, -2), (key1034, -2), (key1069, -2), (key1034, 6), (key1107, 2), (key1112, 2), (key1148, 2), (key999, -2), (key1112, -2), (key1191, -2), (key1121, -6), (key1013, 2), (key1121, 2), (key1197, 2)]

theorem rawRowCheck2188 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form3 = rawRow2188 := by decide +kernel

def row2188 : Integer.Sparse Key := [(key999, -2), (key1013, 2), (key1029, -2), (key1034, 4), (key1069, -2), (key1107, 2), (key1121, -4), (key1148, 2), (key1191, -2), (key1197, 2)]

theorem rowCheck2188 : row2188 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2188 := by decide +kernel

theorem rowEval2188 (x : Key → ℝ) : Integer.Sparse.eval row2188 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2188, Integer.Sparse.eval_collectBalanced, rawRowCheck2188]

def rawRow2189 : Integer.Sparse Key := [(key1034, -2), (key1029, -2), (key1069, -2), (key1034, 6), (key1112, 2), (key1107, 2), (key1148, 2), (key999, -2), (key1191, -2), (key1112, -2), (key1121, -6), (key1013, 2), (key1197, 2), (key1121, 2)]

theorem rawRowCheck2189 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form3 = rawRow2189 := by decide +kernel

def row2189 : Integer.Sparse Key := [(key999, -2), (key1013, 2), (key1029, -2), (key1034, 4), (key1069, -2), (key1107, 2), (key1121, -4), (key1148, 2), (key1191, -2), (key1197, 2)]

theorem rowCheck2189 : row2189 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2189 := by decide +kernel

theorem rowEval2189 (x : Key → ℝ) : Integer.Sparse.eval row2189 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2189, Integer.Sparse.eval_collectBalanced, rawRowCheck2189]

def rawRow2190 : Integer.Sparse Key := [(key1029, -2), (key1069, -2), (key1034, -2), (key1034, 6), (key1107, 2), (key1148, 2), (key1112, 2), (key1112, -2), (key999, -2), (key1191, -2), (key1121, -6), (key1121, 2), (key1013, 2), (key1197, 2)]

theorem rawRowCheck2190 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form3 = rawRow2190 := by decide +kernel

def row2190 : Integer.Sparse Key := [(key999, -2), (key1013, 2), (key1029, -2), (key1034, 4), (key1069, -2), (key1107, 2), (key1121, -4), (key1148, 2), (key1191, -2), (key1197, 2)]

theorem rowCheck2190 : row2190 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2190 := by decide +kernel

theorem rowEval2190 (x : Key → ℝ) : Integer.Sparse.eval row2190 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2190, Integer.Sparse.eval_collectBalanced, rawRowCheck2190]

def rawRow2191 : Integer.Sparse Key := [(key1069, -2), (key1029, -2), (key1034, -2), (key1034, 6), (key1148, 2), (key1107, 2), (key1112, 2), (key1112, -2), (key1191, -2), (key999, -2), (key1121, -6), (key1121, 2), (key1197, 2), (key1013, 2)]

theorem rawRowCheck2191 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form3 = rawRow2191 := by decide +kernel

def row2191 : Integer.Sparse Key := [(key999, -2), (key1013, 2), (key1029, -2), (key1034, 4), (key1069, -2), (key1107, 2), (key1121, -4), (key1148, 2), (key1191, -2), (key1197, 2)]

theorem rowCheck2191 : row2191 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2191 := by decide +kernel

theorem rowEval2191 (x : Key → ℝ) : Integer.Sparse.eval row2191 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck2191, Integer.Sparse.eval_collectBalanced, rawRowCheck2191]

def rawRow2192 : Integer.Sparse Key := [(key1034, -2), (key1069, -2), (key1029, -2), (key1034, 6), (key1112, 2), (key1148, 2), (key1107, 2), (key1191, -2), (key999, -2), (key1112, -2), (key1121, -6), (key1197, 2), (key1013, 2), (key1121, 2)]

theorem rawRowCheck2192 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form3 = rawRow2192 := by decide +kernel

def row2192 : Integer.Sparse Key := [(key999, -2), (key1013, 2), (key1029, -2), (key1034, 4), (key1069, -2), (key1107, 2), (key1121, -4), (key1148, 2), (key1191, -2), (key1197, 2)]

theorem rowCheck2192 : row2192 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2192 := by decide +kernel

theorem rowEval2192 (x : Key → ℝ) : Integer.Sparse.eval row2192 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2192, Integer.Sparse.eval_collectBalanced, rawRowCheck2192]

def rawRow2193 : Integer.Sparse Key := [(key1069, -2), (key1034, -2), (key1029, -2), (key1034, 6), (key1148, 2), (key1112, 2), (key1107, 2), (key1191, -2), (key1112, -2), (key999, -2), (key1121, -6), (key1197, 2), (key1121, 2), (key1013, 2)]

theorem rawRowCheck2193 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form3 = rawRow2193 := by decide +kernel

def row2193 : Integer.Sparse Key := [(key999, -2), (key1013, 2), (key1029, -2), (key1034, 4), (key1069, -2), (key1107, 2), (key1121, -4), (key1148, 2), (key1191, -2), (key1197, 2)]

theorem rowCheck2193 : row2193 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2193 := by decide +kernel

theorem rowEval2193 (x : Key → ℝ) : Integer.Sparse.eval row2193 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck2193, Integer.Sparse.eval_collectBalanced, rawRowCheck2193]

def rawRow2194 : Integer.Sparse Key := [(key1107, -2), (key1112, -2), (key1121, -2), (key1148, 6), (key994, 2), (key999, 2), (key1013, 2), (key1069, -2), (key1148, -2), (key1210, -2), (key999, -6), (key1034, 2), (key1112, 2), (key1191, 2)]

theorem rawRowCheck2194 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block1.form3 = rawRow2194 := by decide +kernel

def row2194 : Integer.Sparse Key := [(key994, 2), (key999, -4), (key1013, 2), (key1034, 2), (key1069, -2), (key1107, -2), (key1121, -2), (key1148, 4), (key1191, 2), (key1210, -2)]

theorem rowCheck2194 : row2194 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2194 := by decide +kernel

theorem rowEval2194 (x : Key → ℝ) : Integer.Sparse.eval row2194 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2194, Integer.Sparse.eval_collectBalanced, rawRowCheck2194]

def rawRow2195 : Integer.Sparse Key := [(key1112, -2), (key1107, -2), (key1121, -2), (key1148, 6), (key999, 2), (key994, 2), (key1013, 2), (key1069, -2), (key1210, -2), (key1148, -2), (key999, -6), (key1034, 2), (key1191, 2), (key1112, 2)]

theorem rawRowCheck2195 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block1.form3 = rawRow2195 := by decide +kernel

def row2195 : Integer.Sparse Key := [(key994, 2), (key999, -4), (key1013, 2), (key1034, 2), (key1069, -2), (key1107, -2), (key1121, -2), (key1148, 4), (key1191, 2), (key1210, -2)]

theorem rowCheck2195 : row2195 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2195 := by decide +kernel

theorem rowEval2195 (x : Key → ℝ) : Integer.Sparse.eval row2195 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2195, Integer.Sparse.eval_collectBalanced, rawRowCheck2195]

def rawRow2196 : Integer.Sparse Key := [(key1107, -2), (key1121, -2), (key1112, -2), (key1148, 6), (key994, 2), (key1013, 2), (key999, 2), (key1148, -2), (key1069, -2), (key1210, -2), (key999, -6), (key1112, 2), (key1034, 2), (key1191, 2)]

theorem rawRowCheck2196 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block1.form3 = rawRow2196 := by decide +kernel

def row2196 : Integer.Sparse Key := [(key994, 2), (key999, -4), (key1013, 2), (key1034, 2), (key1069, -2), (key1107, -2), (key1121, -2), (key1148, 4), (key1191, 2), (key1210, -2)]

theorem rowCheck2196 : row2196 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2196 := by decide +kernel

theorem rowEval2196 (x : Key → ℝ) : Integer.Sparse.eval row2196 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2196, Integer.Sparse.eval_collectBalanced, rawRowCheck2196]

def rawRow2197 : Integer.Sparse Key := [(key1121, -2), (key1107, -2), (key1112, -2), (key1148, 6), (key1013, 2), (key994, 2), (key999, 2), (key1148, -2), (key1210, -2), (key1069, -2), (key999, -6), (key1112, 2), (key1191, 2), (key1034, 2)]

theorem rawRowCheck2197 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block1.form3 = rawRow2197 := by decide +kernel

def row2197 : Integer.Sparse Key := [(key994, 2), (key999, -4), (key1013, 2), (key1034, 2), (key1069, -2), (key1107, -2), (key1121, -2), (key1148, 4), (key1191, 2), (key1210, -2)]

theorem rowCheck2197 : row2197 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2197 := by decide +kernel

theorem rowEval2197 (x : Key → ℝ) : Integer.Sparse.eval row2197 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2197, Integer.Sparse.eval_collectBalanced, rawRowCheck2197]

def rawRow2198 : Integer.Sparse Key := [(key1112, -2), (key1121, -2), (key1107, -2), (key1148, 6), (key999, 2), (key1013, 2), (key994, 2), (key1210, -2), (key1069, -2), (key1148, -2), (key999, -6), (key1191, 2), (key1034, 2), (key1112, 2)]

theorem rawRowCheck2198 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block1.form3 = rawRow2198 := by decide +kernel

def row2198 : Integer.Sparse Key := [(key994, 2), (key999, -4), (key1013, 2), (key1034, 2), (key1069, -2), (key1107, -2), (key1121, -2), (key1148, 4), (key1191, 2), (key1210, -2)]

theorem rowCheck2198 : row2198 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2198 := by decide +kernel

theorem rowEval2198 (x : Key → ℝ) : Integer.Sparse.eval row2198 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2198, Integer.Sparse.eval_collectBalanced, rawRowCheck2198]

def rawRow2199 : Integer.Sparse Key := [(key1121, -2), (key1112, -2), (key1107, -2), (key1148, 6), (key1013, 2), (key999, 2), (key994, 2), (key1210, -2), (key1148, -2), (key1069, -2), (key999, -6), (key1191, 2), (key1112, 2), (key1034, 2)]

theorem rawRowCheck2199 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block1.form3 = rawRow2199 := by decide +kernel

def row2199 : Integer.Sparse Key := [(key994, 2), (key999, -4), (key1013, 2), (key1034, 2), (key1069, -2), (key1107, -2), (key1121, -2), (key1148, 4), (key1191, 2), (key1210, -2)]

theorem rowCheck2199 : row2199 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2199 := by decide +kernel

theorem rowEval2199 (x : Key → ℝ) : Integer.Sparse.eval row2199 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2199, Integer.Sparse.eval_collectBalanced, rawRowCheck2199]

def rawRow2200 : Integer.Sparse Key := [(key1107, -2), (key1112, -2), (key1148, -2), (key1121, 6), (key1029, 2), (key1034, 2), (key1069, 2), (key1013, -2), (key1121, -2), (key1197, -2), (key1034, -6), (key999, 2), (key1112, 2), (key1191, 2)]

theorem rawRowCheck2200 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form3 = rawRow2200 := by decide +kernel

def row2200 : Integer.Sparse Key := [(key999, 2), (key1013, -2), (key1029, 2), (key1034, -4), (key1069, 2), (key1107, -2), (key1121, 4), (key1148, -2), (key1191, 2), (key1197, -2)]

theorem rowCheck2200 : row2200 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2200 := by decide +kernel

theorem rowEval2200 (x : Key → ℝ) : Integer.Sparse.eval row2200 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2200, Integer.Sparse.eval_collectBalanced, rawRowCheck2200]

def rawRow2201 : Integer.Sparse Key := [(key1112, -2), (key1107, -2), (key1148, -2), (key1121, 6), (key1034, 2), (key1029, 2), (key1069, 2), (key1013, -2), (key1197, -2), (key1121, -2), (key1034, -6), (key999, 2), (key1191, 2), (key1112, 2)]

theorem rawRowCheck2201 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form3 = rawRow2201 := by decide +kernel

def row2201 : Integer.Sparse Key := [(key999, 2), (key1013, -2), (key1029, 2), (key1034, -4), (key1069, 2), (key1107, -2), (key1121, 4), (key1148, -2), (key1191, 2), (key1197, -2)]

theorem rowCheck2201 : row2201 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2201 := by decide +kernel

theorem rowEval2201 (x : Key → ℝ) : Integer.Sparse.eval row2201 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2201, Integer.Sparse.eval_collectBalanced, rawRowCheck2201]

def rawRow2202 : Integer.Sparse Key := [(key1107, -2), (key1148, -2), (key1112, -2), (key1121, 6), (key1029, 2), (key1069, 2), (key1034, 2), (key1121, -2), (key1013, -2), (key1197, -2), (key1034, -6), (key1112, 2), (key999, 2), (key1191, 2)]

theorem rawRowCheck2202 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form3 = rawRow2202 := by decide +kernel

def row2202 : Integer.Sparse Key := [(key999, 2), (key1013, -2), (key1029, 2), (key1034, -4), (key1069, 2), (key1107, -2), (key1121, 4), (key1148, -2), (key1191, 2), (key1197, -2)]

theorem rowCheck2202 : row2202 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2202 := by decide +kernel

theorem rowEval2202 (x : Key → ℝ) : Integer.Sparse.eval row2202 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2202, Integer.Sparse.eval_collectBalanced, rawRowCheck2202]

def rawRow2203 : Integer.Sparse Key := [(key1148, -2), (key1107, -2), (key1112, -2), (key1121, 6), (key1069, 2), (key1029, 2), (key1034, 2), (key1121, -2), (key1197, -2), (key1013, -2), (key1034, -6), (key1112, 2), (key1191, 2), (key999, 2)]

theorem rawRowCheck2203 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form3 = rawRow2203 := by decide +kernel

def row2203 : Integer.Sparse Key := [(key999, 2), (key1013, -2), (key1029, 2), (key1034, -4), (key1069, 2), (key1107, -2), (key1121, 4), (key1148, -2), (key1191, 2), (key1197, -2)]

theorem rowCheck2203 : row2203 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2203 := by decide +kernel

theorem rowEval2203 (x : Key → ℝ) : Integer.Sparse.eval row2203 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck2203, Integer.Sparse.eval_collectBalanced, rawRowCheck2203]

def rawRow2204 : Integer.Sparse Key := [(key1112, -2), (key1148, -2), (key1107, -2), (key1121, 6), (key1034, 2), (key1069, 2), (key1029, 2), (key1197, -2), (key1013, -2), (key1121, -2), (key1034, -6), (key1191, 2), (key999, 2), (key1112, 2)]

theorem rawRowCheck2204 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form3 = rawRow2204 := by decide +kernel

def row2204 : Integer.Sparse Key := [(key999, 2), (key1013, -2), (key1029, 2), (key1034, -4), (key1069, 2), (key1107, -2), (key1121, 4), (key1148, -2), (key1191, 2), (key1197, -2)]

theorem rowCheck2204 : row2204 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2204 := by decide +kernel

theorem rowEval2204 (x : Key → ℝ) : Integer.Sparse.eval row2204 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2204, Integer.Sparse.eval_collectBalanced, rawRowCheck2204]

def rawRow2205 : Integer.Sparse Key := [(key1148, -2), (key1112, -2), (key1107, -2), (key1121, 6), (key1069, 2), (key1034, 2), (key1029, 2), (key1197, -2), (key1121, -2), (key1013, -2), (key1034, -6), (key1191, 2), (key1112, 2), (key999, 2)]

theorem rawRowCheck2205 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form3 = rawRow2205 := by decide +kernel

def row2205 : Integer.Sparse Key := [(key999, 2), (key1013, -2), (key1029, 2), (key1034, -4), (key1069, 2), (key1107, -2), (key1121, 4), (key1148, -2), (key1191, 2), (key1197, -2)]

theorem rowCheck2205 : row2205 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2205 := by decide +kernel

theorem rowEval2205 (x : Key → ℝ) : Integer.Sparse.eval row2205 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck2205, Integer.Sparse.eval_collectBalanced, rawRowCheck2205]

def rawRow2206 : Integer.Sparse Key := [(key2607, -6), (key2623, 2), (key2623, 2), (key2634, 2), (key2662, 6), (key2697, -2), (key2697, -2), (key2720, -2), (key2777, -2), (key2777, -2), (key2788, -2), (key2800, 2), (key2800, 2), (key2823, 2)]

theorem rawRowCheck2206 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form4 = rawRow2206 := by decide +kernel

def row2206 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2662, 6), (key2697, -4), (key2720, -2), (key2777, -4), (key2788, -2), (key2800, 4), (key2823, 2)]

theorem rowCheck2206 : row2206 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2206 := by decide +kernel

theorem rowEval2206 (x : Key → ℝ) : Integer.Sparse.eval row2206 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2206, Integer.Sparse.eval_collectBalanced, rawRowCheck2206]

def rawRow2207 : Integer.Sparse Key := [(key2607, -6), (key2623, 2), (key2634, 2), (key2623, 2), (key2662, 6), (key2697, -2), (key2720, -2), (key2697, -2), (key2777, -2), (key2788, -2), (key2777, -2), (key2800, 2), (key2823, 2), (key2800, 2)]

theorem rawRowCheck2207 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form4 = rawRow2207 := by decide +kernel

def row2207 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2662, 6), (key2697, -4), (key2720, -2), (key2777, -4), (key2788, -2), (key2800, 4), (key2823, 2)]

theorem rowCheck2207 : row2207 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2207 := by decide +kernel

theorem rowEval2207 (x : Key → ℝ) : Integer.Sparse.eval row2207 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2207, Integer.Sparse.eval_collectBalanced, rawRowCheck2207]

def rawRow2208 : Integer.Sparse Key := [(key2607, -6), (key2634, 2), (key2623, 2), (key2623, 2), (key2662, 6), (key2720, -2), (key2697, -2), (key2697, -2), (key2788, -2), (key2777, -2), (key2777, -2), (key2823, 2), (key2800, 2), (key2800, 2)]

theorem rawRowCheck2208 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form4 = rawRow2208 := by decide +kernel

def row2208 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2662, 6), (key2697, -4), (key2720, -2), (key2777, -4), (key2788, -2), (key2800, 4), (key2823, 2)]

theorem rowCheck2208 : row2208 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2208 := by decide +kernel

theorem rowEval2208 (x : Key → ℝ) : Integer.Sparse.eval row2208 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2208, Integer.Sparse.eval_collectBalanced, rawRowCheck2208]

def rawRow2209 : Integer.Sparse Key := [(key2623, -6), (key2607, 2), (key2623, 2), (key2634, 2), (key2697, 6), (key2662, -2), (key2697, -2), (key2720, -2), (key2800, -2), (key2850, -2), (key2854, -2), (key2777, 2), (key2850, 2), (key2864, 2)]

theorem rawRowCheck2209 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block1.form4 = rawRow2209 := by decide +kernel

def row2209 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, -2), (key2697, 4), (key2720, -2), (key2777, 2), (key2800, -2), (key2854, -2), (key2864, 2)]

theorem rowCheck2209 : row2209 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2209 := by decide +kernel

theorem rowEval2209 (x : Key → ℝ) : Integer.Sparse.eval row2209 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2209, Integer.Sparse.eval_collectBalanced, rawRowCheck2209]

def rawRow2210 : Integer.Sparse Key := [(key2623, -6), (key2607, 2), (key2634, 2), (key2623, 2), (key2697, 6), (key2662, -2), (key2720, -2), (key2697, -2), (key2800, -2), (key2854, -2), (key2850, -2), (key2777, 2), (key2864, 2), (key2850, 2)]

theorem rawRowCheck2210 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block1.form4 = rawRow2210 := by decide +kernel

def row2210 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, -2), (key2697, 4), (key2720, -2), (key2777, 2), (key2800, -2), (key2854, -2), (key2864, 2)]

theorem rowCheck2210 : row2210 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2210 := by decide +kernel

theorem rowEval2210 (x : Key → ℝ) : Integer.Sparse.eval row2210 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2210, Integer.Sparse.eval_collectBalanced, rawRowCheck2210]

def rawRow2211 : Integer.Sparse Key := [(key2623, -6), (key2623, 2), (key2607, 2), (key2634, 2), (key2697, 6), (key2697, -2), (key2662, -2), (key2720, -2), (key2850, -2), (key2800, -2), (key2854, -2), (key2850, 2), (key2777, 2), (key2864, 2)]

theorem rawRowCheck2211 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block1.form4 = rawRow2211 := by decide +kernel

def row2211 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, -2), (key2697, 4), (key2720, -2), (key2777, 2), (key2800, -2), (key2854, -2), (key2864, 2)]

theorem rowCheck2211 : row2211 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2211 := by decide +kernel

theorem rowEval2211 (x : Key → ℝ) : Integer.Sparse.eval row2211 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2211, Integer.Sparse.eval_collectBalanced, rawRowCheck2211]

def rawRow2212 : Integer.Sparse Key := [(key2623, -6), (key2623, 2), (key2634, 2), (key2607, 2), (key2697, 6), (key2697, -2), (key2720, -2), (key2662, -2), (key2850, -2), (key2854, -2), (key2800, -2), (key2850, 2), (key2864, 2), (key2777, 2)]

theorem rawRowCheck2212 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block1.form4 = rawRow2212 := by decide +kernel

def row2212 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, -2), (key2697, 4), (key2720, -2), (key2777, 2), (key2800, -2), (key2854, -2), (key2864, 2)]

theorem rowCheck2212 : row2212 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2212 := by decide +kernel

theorem rowEval2212 (x : Key → ℝ) : Integer.Sparse.eval row2212 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2212, Integer.Sparse.eval_collectBalanced, rawRowCheck2212]

def rawRow2213 : Integer.Sparse Key := [(key2623, -6), (key2634, 2), (key2607, 2), (key2623, 2), (key2697, 6), (key2720, -2), (key2662, -2), (key2697, -2), (key2854, -2), (key2800, -2), (key2850, -2), (key2864, 2), (key2777, 2), (key2850, 2)]

theorem rawRowCheck2213 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block1.form4 = rawRow2213 := by decide +kernel

def row2213 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, -2), (key2697, 4), (key2720, -2), (key2777, 2), (key2800, -2), (key2854, -2), (key2864, 2)]

theorem rowCheck2213 : row2213 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2213 := by decide +kernel

theorem rowEval2213 (x : Key → ℝ) : Integer.Sparse.eval row2213 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2213, Integer.Sparse.eval_collectBalanced, rawRowCheck2213]

def rawRow2214 : Integer.Sparse Key := [(key2623, -6), (key2634, 2), (key2623, 2), (key2607, 2), (key2697, 6), (key2720, -2), (key2697, -2), (key2662, -2), (key2854, -2), (key2850, -2), (key2800, -2), (key2864, 2), (key2850, 2), (key2777, 2)]

theorem rawRowCheck2214 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block1.form4 = rawRow2214 := by decide +kernel

def row2214 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, -2), (key2697, 4), (key2720, -2), (key2777, 2), (key2800, -2), (key2854, -2), (key2864, 2)]

theorem rowCheck2214 : row2214 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2214 := by decide +kernel

theorem rowEval2214 (x : Key → ℝ) : Integer.Sparse.eval row2214 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2214, Integer.Sparse.eval_collectBalanced, rawRowCheck2214]

def rawRow2215 : Integer.Sparse Key := [(key2662, -6), (key2777, 2), (key2777, 2), (key2788, 2), (key2607, 6), (key2800, -2), (key2800, -2), (key2823, -2), (key2623, -2), (key2623, -2), (key2634, -2), (key2697, 2), (key2697, 2), (key2720, 2)]

theorem rawRowCheck2215 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form4 = rawRow2215 := by decide +kernel

def row2215 : Integer.Sparse Key := [(key2607, 6), (key2623, -4), (key2634, -2), (key2662, -6), (key2697, 4), (key2720, 2), (key2777, 4), (key2788, 2), (key2800, -4), (key2823, -2)]

theorem rowCheck2215 : row2215 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2215 := by decide +kernel

theorem rowEval2215 (x : Key → ℝ) : Integer.Sparse.eval row2215 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2215, Integer.Sparse.eval_collectBalanced, rawRowCheck2215]

def rawRow2216 : Integer.Sparse Key := [(key2662, -6), (key2777, 2), (key2788, 2), (key2777, 2), (key2607, 6), (key2800, -2), (key2823, -2), (key2800, -2), (key2623, -2), (key2634, -2), (key2623, -2), (key2697, 2), (key2720, 2), (key2697, 2)]

theorem rawRowCheck2216 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form4 = rawRow2216 := by decide +kernel

def row2216 : Integer.Sparse Key := [(key2607, 6), (key2623, -4), (key2634, -2), (key2662, -6), (key2697, 4), (key2720, 2), (key2777, 4), (key2788, 2), (key2800, -4), (key2823, -2)]

theorem rowCheck2216 : row2216 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2216 := by decide +kernel

theorem rowEval2216 (x : Key → ℝ) : Integer.Sparse.eval row2216 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2216, Integer.Sparse.eval_collectBalanced, rawRowCheck2216]

def rawRow2217 : Integer.Sparse Key := [(key2662, -6), (key2788, 2), (key2777, 2), (key2777, 2), (key2607, 6), (key2823, -2), (key2800, -2), (key2800, -2), (key2634, -2), (key2623, -2), (key2623, -2), (key2720, 2), (key2697, 2), (key2697, 2)]

theorem rawRowCheck2217 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form4 = rawRow2217 := by decide +kernel

def row2217 : Integer.Sparse Key := [(key2607, 6), (key2623, -4), (key2634, -2), (key2662, -6), (key2697, 4), (key2720, 2), (key2777, 4), (key2788, 2), (key2800, -4), (key2823, -2)]

theorem rowCheck2217 : row2217 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2217 := by decide +kernel

theorem rowEval2217 (x : Key → ℝ) : Integer.Sparse.eval row2217 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2217, Integer.Sparse.eval_collectBalanced, rawRowCheck2217]

def rawRow2218 : Integer.Sparse Key := [(key2777, -6), (key2662, 2), (key2777, 2), (key2788, 2), (key2800, 6), (key2607, -2), (key2800, -2), (key2823, -2), (key2697, -2), (key2850, -2), (key2854, -2), (key2623, 2), (key2850, 2), (key2864, 2)]

theorem rawRowCheck2218 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form4 = rawRow2218 := by decide +kernel

def row2218 : Integer.Sparse Key := [(key2607, -2), (key2623, 2), (key2662, 2), (key2697, -2), (key2777, -4), (key2788, 2), (key2800, 4), (key2823, -2), (key2854, -2), (key2864, 2)]

theorem rowCheck2218 : row2218 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2218 := by decide +kernel

theorem rowEval2218 (x : Key → ℝ) : Integer.Sparse.eval row2218 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2218, Integer.Sparse.eval_collectBalanced, rawRowCheck2218]

def rawRow2219 : Integer.Sparse Key := [(key2777, -6), (key2662, 2), (key2788, 2), (key2777, 2), (key2800, 6), (key2607, -2), (key2823, -2), (key2800, -2), (key2697, -2), (key2854, -2), (key2850, -2), (key2623, 2), (key2864, 2), (key2850, 2)]

theorem rawRowCheck2219 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form4 = rawRow2219 := by decide +kernel

def row2219 : Integer.Sparse Key := [(key2607, -2), (key2623, 2), (key2662, 2), (key2697, -2), (key2777, -4), (key2788, 2), (key2800, 4), (key2823, -2), (key2854, -2), (key2864, 2)]

theorem rowCheck2219 : row2219 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2219 := by decide +kernel

theorem rowEval2219 (x : Key → ℝ) : Integer.Sparse.eval row2219 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2219, Integer.Sparse.eval_collectBalanced, rawRowCheck2219]

def rawRow2220 : Integer.Sparse Key := [(key2777, -6), (key2777, 2), (key2662, 2), (key2788, 2), (key2800, 6), (key2800, -2), (key2607, -2), (key2823, -2), (key2850, -2), (key2697, -2), (key2854, -2), (key2850, 2), (key2623, 2), (key2864, 2)]

theorem rawRowCheck2220 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form4 = rawRow2220 := by decide +kernel

def row2220 : Integer.Sparse Key := [(key2607, -2), (key2623, 2), (key2662, 2), (key2697, -2), (key2777, -4), (key2788, 2), (key2800, 4), (key2823, -2), (key2854, -2), (key2864, 2)]

theorem rowCheck2220 : row2220 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2220 := by decide +kernel

theorem rowEval2220 (x : Key → ℝ) : Integer.Sparse.eval row2220 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2220, Integer.Sparse.eval_collectBalanced, rawRowCheck2220]

def rawRow2221 : Integer.Sparse Key := [(key2777, -6), (key2777, 2), (key2788, 2), (key2662, 2), (key2800, 6), (key2800, -2), (key2823, -2), (key2607, -2), (key2850, -2), (key2854, -2), (key2697, -2), (key2850, 2), (key2864, 2), (key2623, 2)]

theorem rawRowCheck2221 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form4 = rawRow2221 := by decide +kernel

def row2221 : Integer.Sparse Key := [(key2607, -2), (key2623, 2), (key2662, 2), (key2697, -2), (key2777, -4), (key2788, 2), (key2800, 4), (key2823, -2), (key2854, -2), (key2864, 2)]

theorem rowCheck2221 : row2221 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2221 := by decide +kernel

theorem rowEval2221 (x : Key → ℝ) : Integer.Sparse.eval row2221 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck2221, Integer.Sparse.eval_collectBalanced, rawRowCheck2221]

def rawRow2222 : Integer.Sparse Key := [(key2777, -6), (key2788, 2), (key2662, 2), (key2777, 2), (key2800, 6), (key2823, -2), (key2607, -2), (key2800, -2), (key2854, -2), (key2697, -2), (key2850, -2), (key2864, 2), (key2623, 2), (key2850, 2)]

theorem rawRowCheck2222 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form4 = rawRow2222 := by decide +kernel

def row2222 : Integer.Sparse Key := [(key2607, -2), (key2623, 2), (key2662, 2), (key2697, -2), (key2777, -4), (key2788, 2), (key2800, 4), (key2823, -2), (key2854, -2), (key2864, 2)]

theorem rowCheck2222 : row2222 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2222 := by decide +kernel

theorem rowEval2222 (x : Key → ℝ) : Integer.Sparse.eval row2222 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2222, Integer.Sparse.eval_collectBalanced, rawRowCheck2222]

def rawRow2223 : Integer.Sparse Key := [(key2777, -6), (key2788, 2), (key2777, 2), (key2662, 2), (key2800, 6), (key2823, -2), (key2800, -2), (key2607, -2), (key2854, -2), (key2850, -2), (key2697, -2), (key2864, 2), (key2850, 2), (key2623, 2)]

theorem rawRowCheck2223 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form4 = rawRow2223 := by decide +kernel

def row2223 : Integer.Sparse Key := [(key2607, -2), (key2623, 2), (key2662, 2), (key2697, -2), (key2777, -4), (key2788, 2), (key2800, 4), (key2823, -2), (key2854, -2), (key2864, 2)]

theorem rowCheck2223 : row2223 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2223 := by decide +kernel

theorem rowEval2223 (x : Key → ℝ) : Integer.Sparse.eval row2223 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck2223, Integer.Sparse.eval_collectBalanced, rawRowCheck2223]

def rawRow2224 : Integer.Sparse Key := [(key2697, -6), (key2800, 2), (key2850, 2), (key2854, 2), (key2623, 6), (key2777, -2), (key2850, -2), (key2864, -2), (key2607, -2), (key2623, -2), (key2634, -2), (key2662, 2), (key2697, 2), (key2720, 2)]

theorem rawRowCheck2224 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block1.form4 = rawRow2224 := by decide +kernel

def row2224 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, 2), (key2697, -4), (key2720, 2), (key2777, -2), (key2800, 2), (key2854, 2), (key2864, -2)]

theorem rowCheck2224 : row2224 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2224 := by decide +kernel

theorem rowEval2224 (x : Key → ℝ) : Integer.Sparse.eval row2224 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2224, Integer.Sparse.eval_collectBalanced, rawRowCheck2224]

def rawRow2225 : Integer.Sparse Key := [(key2697, -6), (key2800, 2), (key2854, 2), (key2850, 2), (key2623, 6), (key2777, -2), (key2864, -2), (key2850, -2), (key2607, -2), (key2634, -2), (key2623, -2), (key2662, 2), (key2720, 2), (key2697, 2)]

theorem rawRowCheck2225 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block1.form4 = rawRow2225 := by decide +kernel

def row2225 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, 2), (key2697, -4), (key2720, 2), (key2777, -2), (key2800, 2), (key2854, 2), (key2864, -2)]

theorem rowCheck2225 : row2225 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2225 := by decide +kernel

theorem rowEval2225 (x : Key → ℝ) : Integer.Sparse.eval row2225 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2225, Integer.Sparse.eval_collectBalanced, rawRowCheck2225]

def rawRow2226 : Integer.Sparse Key := [(key2697, -6), (key2850, 2), (key2800, 2), (key2854, 2), (key2623, 6), (key2850, -2), (key2777, -2), (key2864, -2), (key2623, -2), (key2607, -2), (key2634, -2), (key2697, 2), (key2662, 2), (key2720, 2)]

theorem rawRowCheck2226 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block1.form4 = rawRow2226 := by decide +kernel

def row2226 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, 2), (key2697, -4), (key2720, 2), (key2777, -2), (key2800, 2), (key2854, 2), (key2864, -2)]

theorem rowCheck2226 : row2226 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2226 := by decide +kernel

theorem rowEval2226 (x : Key → ℝ) : Integer.Sparse.eval row2226 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2226, Integer.Sparse.eval_collectBalanced, rawRowCheck2226]

def rawRow2227 : Integer.Sparse Key := [(key2697, -6), (key2850, 2), (key2854, 2), (key2800, 2), (key2623, 6), (key2850, -2), (key2864, -2), (key2777, -2), (key2623, -2), (key2634, -2), (key2607, -2), (key2697, 2), (key2720, 2), (key2662, 2)]

theorem rawRowCheck2227 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block1.form4 = rawRow2227 := by decide +kernel

def row2227 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, 2), (key2697, -4), (key2720, 2), (key2777, -2), (key2800, 2), (key2854, 2), (key2864, -2)]

theorem rowCheck2227 : row2227 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2227 := by decide +kernel

theorem rowEval2227 (x : Key → ℝ) : Integer.Sparse.eval row2227 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2227, Integer.Sparse.eval_collectBalanced, rawRowCheck2227]

def rawRow2228 : Integer.Sparse Key := [(key2697, -6), (key2854, 2), (key2800, 2), (key2850, 2), (key2623, 6), (key2864, -2), (key2777, -2), (key2850, -2), (key2634, -2), (key2607, -2), (key2623, -2), (key2720, 2), (key2662, 2), (key2697, 2)]

theorem rawRowCheck2228 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block1.form4 = rawRow2228 := by decide +kernel

def row2228 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, 2), (key2697, -4), (key2720, 2), (key2777, -2), (key2800, 2), (key2854, 2), (key2864, -2)]

theorem rowCheck2228 : row2228 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2228 := by decide +kernel

theorem rowEval2228 (x : Key → ℝ) : Integer.Sparse.eval row2228 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2228, Integer.Sparse.eval_collectBalanced, rawRowCheck2228]

def rawRow2229 : Integer.Sparse Key := [(key2697, -6), (key2854, 2), (key2850, 2), (key2800, 2), (key2623, 6), (key2864, -2), (key2850, -2), (key2777, -2), (key2634, -2), (key2623, -2), (key2607, -2), (key2720, 2), (key2697, 2), (key2662, 2)]

theorem rawRowCheck2229 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block1.form4 = rawRow2229 := by decide +kernel

def row2229 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, 2), (key2697, -4), (key2720, 2), (key2777, -2), (key2800, 2), (key2854, 2), (key2864, -2)]

theorem rowCheck2229 : row2229 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2229 := by decide +kernel

theorem rowEval2229 (x : Key → ℝ) : Integer.Sparse.eval row2229 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2229, Integer.Sparse.eval_collectBalanced, rawRowCheck2229]

def rawRow2230 : Integer.Sparse Key := [(key2800, -6), (key2697, 2), (key2850, 2), (key2854, 2), (key2777, 6), (key2623, -2), (key2850, -2), (key2864, -2), (key2662, -2), (key2777, -2), (key2788, -2), (key2607, 2), (key2800, 2), (key2823, 2)]

theorem rawRowCheck2230 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form4 = rawRow2230 := by decide +kernel

def row2230 : Integer.Sparse Key := [(key2607, 2), (key2623, -2), (key2662, -2), (key2697, 2), (key2777, 4), (key2788, -2), (key2800, -4), (key2823, 2), (key2854, 2), (key2864, -2)]

theorem rowCheck2230 : row2230 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2230 := by decide +kernel

theorem rowEval2230 (x : Key → ℝ) : Integer.Sparse.eval row2230 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2230, Integer.Sparse.eval_collectBalanced, rawRowCheck2230]

def rawRow2231 : Integer.Sparse Key := [(key2800, -6), (key2697, 2), (key2854, 2), (key2850, 2), (key2777, 6), (key2623, -2), (key2864, -2), (key2850, -2), (key2662, -2), (key2788, -2), (key2777, -2), (key2607, 2), (key2823, 2), (key2800, 2)]

theorem rawRowCheck2231 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form4 = rawRow2231 := by decide +kernel

def row2231 : Integer.Sparse Key := [(key2607, 2), (key2623, -2), (key2662, -2), (key2697, 2), (key2777, 4), (key2788, -2), (key2800, -4), (key2823, 2), (key2854, 2), (key2864, -2)]

theorem rowCheck2231 : row2231 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2231 := by decide +kernel

theorem rowEval2231 (x : Key → ℝ) : Integer.Sparse.eval row2231 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2231, Integer.Sparse.eval_collectBalanced, rawRowCheck2231]

def rawRow2232 : Integer.Sparse Key := [(key2800, -6), (key2850, 2), (key2697, 2), (key2854, 2), (key2777, 6), (key2850, -2), (key2623, -2), (key2864, -2), (key2777, -2), (key2662, -2), (key2788, -2), (key2800, 2), (key2607, 2), (key2823, 2)]

theorem rawRowCheck2232 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form4 = rawRow2232 := by decide +kernel

def row2232 : Integer.Sparse Key := [(key2607, 2), (key2623, -2), (key2662, -2), (key2697, 2), (key2777, 4), (key2788, -2), (key2800, -4), (key2823, 2), (key2854, 2), (key2864, -2)]

theorem rowCheck2232 : row2232 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2232 := by decide +kernel

theorem rowEval2232 (x : Key → ℝ) : Integer.Sparse.eval row2232 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2232, Integer.Sparse.eval_collectBalanced, rawRowCheck2232]

def rawRow2233 : Integer.Sparse Key := [(key2800, -6), (key2850, 2), (key2854, 2), (key2697, 2), (key2777, 6), (key2850, -2), (key2864, -2), (key2623, -2), (key2777, -2), (key2788, -2), (key2662, -2), (key2800, 2), (key2823, 2), (key2607, 2)]

theorem rawRowCheck2233 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form4 = rawRow2233 := by decide +kernel

def row2233 : Integer.Sparse Key := [(key2607, 2), (key2623, -2), (key2662, -2), (key2697, 2), (key2777, 4), (key2788, -2), (key2800, -4), (key2823, 2), (key2854, 2), (key2864, -2)]

theorem rowCheck2233 : row2233 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2233 := by decide +kernel

theorem rowEval2233 (x : Key → ℝ) : Integer.Sparse.eval row2233 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck2233, Integer.Sparse.eval_collectBalanced, rawRowCheck2233]

def rawRow2234 : Integer.Sparse Key := [(key2800, -6), (key2854, 2), (key2697, 2), (key2850, 2), (key2777, 6), (key2864, -2), (key2623, -2), (key2850, -2), (key2788, -2), (key2662, -2), (key2777, -2), (key2823, 2), (key2607, 2), (key2800, 2)]

theorem rawRowCheck2234 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form4 = rawRow2234 := by decide +kernel

def row2234 : Integer.Sparse Key := [(key2607, 2), (key2623, -2), (key2662, -2), (key2697, 2), (key2777, 4), (key2788, -2), (key2800, -4), (key2823, 2), (key2854, 2), (key2864, -2)]

theorem rowCheck2234 : row2234 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2234 := by decide +kernel

theorem rowEval2234 (x : Key → ℝ) : Integer.Sparse.eval row2234 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2234, Integer.Sparse.eval_collectBalanced, rawRowCheck2234]

def rawRow2235 : Integer.Sparse Key := [(key2800, -6), (key2854, 2), (key2850, 2), (key2697, 2), (key2777, 6), (key2864, -2), (key2850, -2), (key2623, -2), (key2788, -2), (key2777, -2), (key2662, -2), (key2823, 2), (key2800, 2), (key2607, 2)]

theorem rawRowCheck2235 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form4 = rawRow2235 := by decide +kernel

def row2235 : Integer.Sparse Key := [(key2607, 2), (key2623, -2), (key2662, -2), (key2697, 2), (key2777, 4), (key2788, -2), (key2800, -4), (key2823, 2), (key2854, 2), (key2864, -2)]

theorem rowCheck2235 : row2235 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2235 := by decide +kernel

theorem rowEval2235 (x : Key → ℝ) : Integer.Sparse.eval row2235 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck2235, Integer.Sparse.eval_collectBalanced, rawRowCheck2235]

def rawRow2236 : Integer.Sparse Key := [(key1542, -1), (key1547, -1), (key1542, -1), (key1773, -1), (key1547, -1), (key1773, -1), (key1555, 2), (key1555, 2), (key1779, 2), (key1569, 1), (key1574, 1), (key1569, 1), (key1789, 1), (key1574, 1), (key1789, 1), (key1623, -1), (key1658, -1), (key1623, -1), (key1816, -1), (key1658, -1), (key1816, -1), (key1592, -2), (key1592, -2), (key1797, -2), (key1632, 1), (key1666, 1), (key1632, 1), (key1824, 1), (key1666, 1), (key1824, 1)]

theorem rawRowCheck2236 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form5 = rawRow2236 := by decide +kernel

def row2236 : Integer.Sparse Key := [(key1542, -2), (key1547, -2), (key1555, 4), (key1569, 2), (key1574, 2), (key1592, -4), (key1623, -2), (key1632, 2), (key1658, -2), (key1666, 2), (key1773, -2), (key1779, 2), (key1789, 2), (key1797, -2), (key1816, -2), (key1824, 2)]

theorem rowCheck2236 : row2236 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2236 := by decide +kernel

theorem rowEval2236 (x : Key → ℝ) : Integer.Sparse.eval row2236 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2236, Integer.Sparse.eval_collectBalanced, rawRowCheck2236]

def rawRow2237 : Integer.Sparse Key := [(key1547, -1), (key1542, -1), (key1773, -1), (key1542, -1), (key1773, -1), (key1547, -1), (key1555, 2), (key1779, 2), (key1555, 2), (key1574, 1), (key1569, 1), (key1789, 1), (key1569, 1), (key1789, 1), (key1574, 1), (key1658, -1), (key1623, -1), (key1816, -1), (key1623, -1), (key1816, -1), (key1658, -1), (key1592, -2), (key1797, -2), (key1592, -2), (key1666, 1), (key1632, 1), (key1824, 1), (key1632, 1), (key1824, 1), (key1666, 1)]

theorem rawRowCheck2237 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form5 = rawRow2237 := by decide +kernel

def row2237 : Integer.Sparse Key := [(key1542, -2), (key1547, -2), (key1555, 4), (key1569, 2), (key1574, 2), (key1592, -4), (key1623, -2), (key1632, 2), (key1658, -2), (key1666, 2), (key1773, -2), (key1779, 2), (key1789, 2), (key1797, -2), (key1816, -2), (key1824, 2)]

theorem rowCheck2237 : row2237 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2237 := by decide +kernel

theorem rowEval2237 (x : Key → ℝ) : Integer.Sparse.eval row2237 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2237, Integer.Sparse.eval_collectBalanced, rawRowCheck2237]

def rawRow2238 : Integer.Sparse Key := [(key1773, -1), (key1773, -1), (key1547, -1), (key1547, -1), (key1542, -1), (key1542, -1), (key1779, 2), (key1555, 2), (key1555, 2), (key1789, 1), (key1789, 1), (key1574, 1), (key1574, 1), (key1569, 1), (key1569, 1), (key1816, -1), (key1816, -1), (key1658, -1), (key1658, -1), (key1623, -1), (key1623, -1), (key1797, -2), (key1592, -2), (key1592, -2), (key1824, 1), (key1824, 1), (key1666, 1), (key1666, 1), (key1632, 1), (key1632, 1)]

theorem rawRowCheck2238 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form5 = rawRow2238 := by decide +kernel

def row2238 : Integer.Sparse Key := [(key1542, -2), (key1547, -2), (key1555, 4), (key1569, 2), (key1574, 2), (key1592, -4), (key1623, -2), (key1632, 2), (key1658, -2), (key1666, 2), (key1773, -2), (key1779, 2), (key1789, 2), (key1797, -2), (key1816, -2), (key1824, 2)]

theorem rowCheck2238 : row2238 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2238 := by decide +kernel

theorem rowEval2238 (x : Key → ℝ) : Integer.Sparse.eval row2238 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2238, Integer.Sparse.eval_collectBalanced, rawRowCheck2238]

def rawRow2239 : Integer.Sparse Key := [(key1387, -1), (key1392, -1), (key1542, -1), (key1773, -1), (key1555, -1), (key1779, -1), (key1392, 2), (key1547, 2), (key1773, 2), (key1420, 1), (key1425, 1), (key1618, 1), (key1814, 1), (key1623, 1), (key1816, 1), (key1425, -1), (key1456, -1), (key1574, -1), (key1789, -1), (key1656, -1), (key1814, -1), (key1443, -2), (key1632, -2), (key1824, -2), (key1443, 1), (key1465, 1), (key1592, 1), (key1797, 1), (key1666, 1), (key1824, 1)]

theorem rawRowCheck2239 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block1.form5 = rawRow2239 := by decide +kernel

def row2239 : Integer.Sparse Key := [(key1387, -1), (key1392, 1), (key1420, 1), (key1443, -1), (key1456, -1), (key1465, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1574, -1), (key1592, 1), (key1618, 1), (key1623, 1), (key1632, -2), (key1656, -1), (key1666, 1), (key1773, 1), (key1779, -1), (key1789, -1), (key1797, 1), (key1816, 1), (key1824, -1)]

theorem rowCheck2239 : row2239 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2239 := by decide +kernel

theorem rowEval2239 (x : Key → ℝ) : Integer.Sparse.eval row2239 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2239, Integer.Sparse.eval_collectBalanced, rawRowCheck2239]

def rawRow2240 : Integer.Sparse Key := [(key1392, -1), (key1387, -1), (key1773, -1), (key1542, -1), (key1779, -1), (key1555, -1), (key1392, 2), (key1773, 2), (key1547, 2), (key1425, 1), (key1420, 1), (key1814, 1), (key1618, 1), (key1816, 1), (key1623, 1), (key1456, -1), (key1425, -1), (key1789, -1), (key1574, -1), (key1814, -1), (key1656, -1), (key1443, -2), (key1824, -2), (key1632, -2), (key1465, 1), (key1443, 1), (key1797, 1), (key1592, 1), (key1824, 1), (key1666, 1)]

theorem rawRowCheck2240 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block1.form5 = rawRow2240 := by decide +kernel

def row2240 : Integer.Sparse Key := [(key1387, -1), (key1392, 1), (key1420, 1), (key1443, -1), (key1456, -1), (key1465, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1574, -1), (key1592, 1), (key1618, 1), (key1623, 1), (key1632, -2), (key1656, -1), (key1666, 1), (key1773, 1), (key1779, -1), (key1789, -1), (key1797, 1), (key1816, 1), (key1824, -1)]

theorem rowCheck2240 : row2240 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2240 := by decide +kernel

theorem rowEval2240 (x : Key → ℝ) : Integer.Sparse.eval row2240 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2240, Integer.Sparse.eval_collectBalanced, rawRowCheck2240]

def rawRow2241 : Integer.Sparse Key := [(key1542, -1), (key1555, -1), (key1387, -1), (key1779, -1), (key1392, -1), (key1773, -1), (key1547, 2), (key1392, 2), (key1773, 2), (key1618, 1), (key1623, 1), (key1420, 1), (key1816, 1), (key1425, 1), (key1814, 1), (key1574, -1), (key1656, -1), (key1425, -1), (key1814, -1), (key1456, -1), (key1789, -1), (key1632, -2), (key1443, -2), (key1824, -2), (key1592, 1), (key1666, 1), (key1443, 1), (key1824, 1), (key1465, 1), (key1797, 1)]

theorem rawRowCheck2241 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block1.form5 = rawRow2241 := by decide +kernel

def row2241 : Integer.Sparse Key := [(key1387, -1), (key1392, 1), (key1420, 1), (key1443, -1), (key1456, -1), (key1465, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1574, -1), (key1592, 1), (key1618, 1), (key1623, 1), (key1632, -2), (key1656, -1), (key1666, 1), (key1773, 1), (key1779, -1), (key1789, -1), (key1797, 1), (key1816, 1), (key1824, -1)]

theorem rowCheck2241 : row2241 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2241 := by decide +kernel

theorem rowEval2241 (x : Key → ℝ) : Integer.Sparse.eval row2241 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2241, Integer.Sparse.eval_collectBalanced, rawRowCheck2241]

def rawRow2242 : Integer.Sparse Key := [(key1555, -1), (key1542, -1), (key1779, -1), (key1387, -1), (key1773, -1), (key1392, -1), (key1547, 2), (key1773, 2), (key1392, 2), (key1623, 1), (key1618, 1), (key1816, 1), (key1420, 1), (key1814, 1), (key1425, 1), (key1656, -1), (key1574, -1), (key1814, -1), (key1425, -1), (key1789, -1), (key1456, -1), (key1632, -2), (key1824, -2), (key1443, -2), (key1666, 1), (key1592, 1), (key1824, 1), (key1443, 1), (key1797, 1), (key1465, 1)]

theorem rawRowCheck2242 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block1.form5 = rawRow2242 := by decide +kernel

def row2242 : Integer.Sparse Key := [(key1387, -1), (key1392, 1), (key1420, 1), (key1443, -1), (key1456, -1), (key1465, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1574, -1), (key1592, 1), (key1618, 1), (key1623, 1), (key1632, -2), (key1656, -1), (key1666, 1), (key1773, 1), (key1779, -1), (key1789, -1), (key1797, 1), (key1816, 1), (key1824, -1)]

theorem rowCheck2242 : row2242 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2242 := by decide +kernel

theorem rowEval2242 (x : Key → ℝ) : Integer.Sparse.eval row2242 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2242, Integer.Sparse.eval_collectBalanced, rawRowCheck2242]

def rawRow2243 : Integer.Sparse Key := [(key1773, -1), (key1779, -1), (key1392, -1), (key1555, -1), (key1387, -1), (key1542, -1), (key1773, 2), (key1392, 2), (key1547, 2), (key1814, 1), (key1816, 1), (key1425, 1), (key1623, 1), (key1420, 1), (key1618, 1), (key1789, -1), (key1814, -1), (key1456, -1), (key1656, -1), (key1425, -1), (key1574, -1), (key1824, -2), (key1443, -2), (key1632, -2), (key1797, 1), (key1824, 1), (key1465, 1), (key1666, 1), (key1443, 1), (key1592, 1)]

theorem rawRowCheck2243 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block1.form5 = rawRow2243 := by decide +kernel

def row2243 : Integer.Sparse Key := [(key1387, -1), (key1392, 1), (key1420, 1), (key1443, -1), (key1456, -1), (key1465, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1574, -1), (key1592, 1), (key1618, 1), (key1623, 1), (key1632, -2), (key1656, -1), (key1666, 1), (key1773, 1), (key1779, -1), (key1789, -1), (key1797, 1), (key1816, 1), (key1824, -1)]

theorem rowCheck2243 : row2243 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2243 := by decide +kernel

theorem rowEval2243 (x : Key → ℝ) : Integer.Sparse.eval row2243 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2243, Integer.Sparse.eval_collectBalanced, rawRowCheck2243]

def rawRow2244 : Integer.Sparse Key := [(key1779, -1), (key1773, -1), (key1555, -1), (key1392, -1), (key1542, -1), (key1387, -1), (key1773, 2), (key1547, 2), (key1392, 2), (key1816, 1), (key1814, 1), (key1623, 1), (key1425, 1), (key1618, 1), (key1420, 1), (key1814, -1), (key1789, -1), (key1656, -1), (key1456, -1), (key1574, -1), (key1425, -1), (key1824, -2), (key1632, -2), (key1443, -2), (key1824, 1), (key1797, 1), (key1666, 1), (key1465, 1), (key1592, 1), (key1443, 1)]

theorem rawRowCheck2244 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block1.form5 = rawRow2244 := by decide +kernel

def row2244 : Integer.Sparse Key := [(key1387, -1), (key1392, 1), (key1420, 1), (key1443, -1), (key1456, -1), (key1465, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1574, -1), (key1592, 1), (key1618, 1), (key1623, 1), (key1632, -2), (key1656, -1), (key1666, 1), (key1773, 1), (key1779, -1), (key1789, -1), (key1797, 1), (key1816, 1), (key1824, -1)]

theorem rowCheck2244 : row2244 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2244 := by decide +kernel

theorem rowEval2244 (x : Key → ℝ) : Integer.Sparse.eval row2244 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2244, Integer.Sparse.eval_collectBalanced, rawRowCheck2244]

def rawRow2245 : Integer.Sparse Key := [(key1569, -1), (key1574, -1), (key1569, -1), (key1789, -1), (key1574, -1), (key1789, -1), (key1592, 2), (key1592, 2), (key1797, 2), (key1542, 1), (key1547, 1), (key1542, 1), (key1773, 1), (key1547, 1), (key1773, 1), (key1632, -1), (key1666, -1), (key1632, -1), (key1824, -1), (key1666, -1), (key1824, -1), (key1555, -2), (key1555, -2), (key1779, -2), (key1623, 1), (key1658, 1), (key1623, 1), (key1816, 1), (key1658, 1), (key1816, 1)]

theorem rawRowCheck2245 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form5 = rawRow2245 := by decide +kernel

def row2245 : Integer.Sparse Key := [(key1542, 2), (key1547, 2), (key1555, -4), (key1569, -2), (key1574, -2), (key1592, 4), (key1623, 2), (key1632, -2), (key1658, 2), (key1666, -2), (key1773, 2), (key1779, -2), (key1789, -2), (key1797, 2), (key1816, 2), (key1824, -2)]

theorem rowCheck2245 : row2245 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2245 := by decide +kernel

theorem rowEval2245 (x : Key → ℝ) : Integer.Sparse.eval row2245 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2245, Integer.Sparse.eval_collectBalanced, rawRowCheck2245]

def rawRow2246 : Integer.Sparse Key := [(key1574, -1), (key1569, -1), (key1789, -1), (key1569, -1), (key1789, -1), (key1574, -1), (key1592, 2), (key1797, 2), (key1592, 2), (key1547, 1), (key1542, 1), (key1773, 1), (key1542, 1), (key1773, 1), (key1547, 1), (key1666, -1), (key1632, -1), (key1824, -1), (key1632, -1), (key1824, -1), (key1666, -1), (key1555, -2), (key1779, -2), (key1555, -2), (key1658, 1), (key1623, 1), (key1816, 1), (key1623, 1), (key1816, 1), (key1658, 1)]

theorem rawRowCheck2246 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form5 = rawRow2246 := by decide +kernel

def row2246 : Integer.Sparse Key := [(key1542, 2), (key1547, 2), (key1555, -4), (key1569, -2), (key1574, -2), (key1592, 4), (key1623, 2), (key1632, -2), (key1658, 2), (key1666, -2), (key1773, 2), (key1779, -2), (key1789, -2), (key1797, 2), (key1816, 2), (key1824, -2)]

theorem rowCheck2246 : row2246 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2246 := by decide +kernel

theorem rowEval2246 (x : Key → ℝ) : Integer.Sparse.eval row2246 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2246, Integer.Sparse.eval_collectBalanced, rawRowCheck2246]

def rawRow2247 : Integer.Sparse Key := [(key1789, -1), (key1789, -1), (key1574, -1), (key1574, -1), (key1569, -1), (key1569, -1), (key1797, 2), (key1592, 2), (key1592, 2), (key1773, 1), (key1773, 1), (key1547, 1), (key1547, 1), (key1542, 1), (key1542, 1), (key1824, -1), (key1824, -1), (key1666, -1), (key1666, -1), (key1632, -1), (key1632, -1), (key1779, -2), (key1555, -2), (key1555, -2), (key1816, 1), (key1816, 1), (key1658, 1), (key1658, 1), (key1623, 1), (key1623, 1)]

theorem rawRowCheck2247 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form5 = rawRow2247 := by decide +kernel

def row2247 : Integer.Sparse Key := [(key1542, 2), (key1547, 2), (key1555, -4), (key1569, -2), (key1574, -2), (key1592, 4), (key1623, 2), (key1632, -2), (key1658, 2), (key1666, -2), (key1773, 2), (key1779, -2), (key1789, -2), (key1797, 2), (key1816, 2), (key1824, -2)]

theorem rowCheck2247 : row2247 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2247 := by decide +kernel

theorem rowEval2247 (x : Key → ℝ) : Integer.Sparse.eval row2247 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2247, Integer.Sparse.eval_collectBalanced, rawRowCheck2247]

def rawRow2248 : Integer.Sparse Key := [(key1292, -1), (key1297, -1), (key1569, -1), (key1789, -1), (key1592, -1), (key1797, -1), (key1297, 2), (key1574, 2), (key1789, 2), (key1312, 1), (key1317, 1), (key1618, 1), (key1814, 1), (key1632, 1), (key1824, 1), (key1317, -1), (key1338, -1), (key1547, -1), (key1773, -1), (key1656, -1), (key1814, -1), (key1325, -2), (key1623, -2), (key1816, -2), (key1325, 1), (key1344, 1), (key1555, 1), (key1779, 1), (key1658, 1), (key1816, 1)]

theorem rawRowCheck2248 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form5 = rawRow2248 := by decide +kernel

def row2248 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1325, -1), (key1338, -1), (key1344, 1), (key1547, -1), (key1555, 1), (key1569, -1), (key1574, 2), (key1592, -1), (key1618, 1), (key1623, -2), (key1632, 1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1789, 1), (key1797, -1), (key1816, -1), (key1824, 1)]

theorem rowCheck2248 : row2248 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2248 := by decide +kernel

theorem rowEval2248 (x : Key → ℝ) : Integer.Sparse.eval row2248 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2248, Integer.Sparse.eval_collectBalanced, rawRowCheck2248]

def rawRow2249 : Integer.Sparse Key := [(key1297, -1), (key1292, -1), (key1789, -1), (key1569, -1), (key1797, -1), (key1592, -1), (key1297, 2), (key1789, 2), (key1574, 2), (key1317, 1), (key1312, 1), (key1814, 1), (key1618, 1), (key1824, 1), (key1632, 1), (key1338, -1), (key1317, -1), (key1773, -1), (key1547, -1), (key1814, -1), (key1656, -1), (key1325, -2), (key1816, -2), (key1623, -2), (key1344, 1), (key1325, 1), (key1779, 1), (key1555, 1), (key1816, 1), (key1658, 1)]

theorem rawRowCheck2249 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form5 = rawRow2249 := by decide +kernel

def row2249 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1325, -1), (key1338, -1), (key1344, 1), (key1547, -1), (key1555, 1), (key1569, -1), (key1574, 2), (key1592, -1), (key1618, 1), (key1623, -2), (key1632, 1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1789, 1), (key1797, -1), (key1816, -1), (key1824, 1)]

theorem rowCheck2249 : row2249 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2249 := by decide +kernel

theorem rowEval2249 (x : Key → ℝ) : Integer.Sparse.eval row2249 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2249, Integer.Sparse.eval_collectBalanced, rawRowCheck2249]

def rawRow2250 : Integer.Sparse Key := [(key1569, -1), (key1592, -1), (key1292, -1), (key1797, -1), (key1297, -1), (key1789, -1), (key1574, 2), (key1297, 2), (key1789, 2), (key1618, 1), (key1632, 1), (key1312, 1), (key1824, 1), (key1317, 1), (key1814, 1), (key1547, -1), (key1656, -1), (key1317, -1), (key1814, -1), (key1338, -1), (key1773, -1), (key1623, -2), (key1325, -2), (key1816, -2), (key1555, 1), (key1658, 1), (key1325, 1), (key1816, 1), (key1344, 1), (key1779, 1)]

theorem rawRowCheck2250 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form5 = rawRow2250 := by decide +kernel

def row2250 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1325, -1), (key1338, -1), (key1344, 1), (key1547, -1), (key1555, 1), (key1569, -1), (key1574, 2), (key1592, -1), (key1618, 1), (key1623, -2), (key1632, 1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1789, 1), (key1797, -1), (key1816, -1), (key1824, 1)]

theorem rowCheck2250 : row2250 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2250 := by decide +kernel

theorem rowEval2250 (x : Key → ℝ) : Integer.Sparse.eval row2250 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2250, Integer.Sparse.eval_collectBalanced, rawRowCheck2250]

def rawRow2251 : Integer.Sparse Key := [(key1592, -1), (key1569, -1), (key1797, -1), (key1292, -1), (key1789, -1), (key1297, -1), (key1574, 2), (key1789, 2), (key1297, 2), (key1632, 1), (key1618, 1), (key1824, 1), (key1312, 1), (key1814, 1), (key1317, 1), (key1656, -1), (key1547, -1), (key1814, -1), (key1317, -1), (key1773, -1), (key1338, -1), (key1623, -2), (key1816, -2), (key1325, -2), (key1658, 1), (key1555, 1), (key1816, 1), (key1325, 1), (key1779, 1), (key1344, 1)]

theorem rawRowCheck2251 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form5 = rawRow2251 := by decide +kernel

def row2251 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1325, -1), (key1338, -1), (key1344, 1), (key1547, -1), (key1555, 1), (key1569, -1), (key1574, 2), (key1592, -1), (key1618, 1), (key1623, -2), (key1632, 1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1789, 1), (key1797, -1), (key1816, -1), (key1824, 1)]

theorem rowCheck2251 : row2251 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2251 := by decide +kernel

theorem rowEval2251 (x : Key → ℝ) : Integer.Sparse.eval row2251 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck2251, Integer.Sparse.eval_collectBalanced, rawRowCheck2251]

def rawRow2252 : Integer.Sparse Key := [(key1789, -1), (key1797, -1), (key1297, -1), (key1592, -1), (key1292, -1), (key1569, -1), (key1789, 2), (key1297, 2), (key1574, 2), (key1814, 1), (key1824, 1), (key1317, 1), (key1632, 1), (key1312, 1), (key1618, 1), (key1773, -1), (key1814, -1), (key1338, -1), (key1656, -1), (key1317, -1), (key1547, -1), (key1816, -2), (key1325, -2), (key1623, -2), (key1779, 1), (key1816, 1), (key1344, 1), (key1658, 1), (key1325, 1), (key1555, 1)]

theorem rawRowCheck2252 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form5 = rawRow2252 := by decide +kernel

def row2252 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1325, -1), (key1338, -1), (key1344, 1), (key1547, -1), (key1555, 1), (key1569, -1), (key1574, 2), (key1592, -1), (key1618, 1), (key1623, -2), (key1632, 1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1789, 1), (key1797, -1), (key1816, -1), (key1824, 1)]

theorem rowCheck2252 : row2252 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2252 := by decide +kernel

theorem rowEval2252 (x : Key → ℝ) : Integer.Sparse.eval row2252 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2252, Integer.Sparse.eval_collectBalanced, rawRowCheck2252]

def rawRow2253 : Integer.Sparse Key := [(key1797, -1), (key1789, -1), (key1592, -1), (key1297, -1), (key1569, -1), (key1292, -1), (key1789, 2), (key1574, 2), (key1297, 2), (key1824, 1), (key1814, 1), (key1632, 1), (key1317, 1), (key1618, 1), (key1312, 1), (key1814, -1), (key1773, -1), (key1656, -1), (key1338, -1), (key1547, -1), (key1317, -1), (key1816, -2), (key1623, -2), (key1325, -2), (key1816, 1), (key1779, 1), (key1658, 1), (key1344, 1), (key1555, 1), (key1325, 1)]

theorem rawRowCheck2253 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form5 = rawRow2253 := by decide +kernel

def row2253 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1325, -1), (key1338, -1), (key1344, 1), (key1547, -1), (key1555, 1), (key1569, -1), (key1574, 2), (key1592, -1), (key1618, 1), (key1623, -2), (key1632, 1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1789, 1), (key1797, -1), (key1816, -1), (key1824, 1)]

theorem rowCheck2253 : row2253 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2253 := by decide +kernel

theorem rowEval2253 (x : Key → ℝ) : Integer.Sparse.eval row2253 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck2253, Integer.Sparse.eval_collectBalanced, rawRowCheck2253]

def rawRow2254 : Integer.Sparse Key := [(key1420, -1), (key1425, -1), (key1618, -1), (key1814, -1), (key1623, -1), (key1816, -1), (key1443, 2), (key1632, 2), (key1824, 2), (key1387, 1), (key1392, 1), (key1542, 1), (key1773, 1), (key1555, 1), (key1779, 1), (key1443, -1), (key1465, -1), (key1592, -1), (key1797, -1), (key1666, -1), (key1824, -1), (key1392, -2), (key1547, -2), (key1773, -2), (key1425, 1), (key1456, 1), (key1574, 1), (key1789, 1), (key1656, 1), (key1814, 1)]

theorem rawRowCheck2254 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block1.form5 = rawRow2254 := by decide +kernel

def row2254 : Integer.Sparse Key := [(key1387, 1), (key1392, -1), (key1420, -1), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -2), (key1555, 1), (key1574, 1), (key1592, -1), (key1618, -1), (key1623, -1), (key1632, 2), (key1656, 1), (key1666, -1), (key1773, -1), (key1779, 1), (key1789, 1), (key1797, -1), (key1816, -1), (key1824, 1)]

theorem rowCheck2254 : row2254 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2254 := by decide +kernel

theorem rowEval2254 (x : Key → ℝ) : Integer.Sparse.eval row2254 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2254, Integer.Sparse.eval_collectBalanced, rawRowCheck2254]

def rawRow2255 : Integer.Sparse Key := [(key1425, -1), (key1420, -1), (key1814, -1), (key1618, -1), (key1816, -1), (key1623, -1), (key1443, 2), (key1824, 2), (key1632, 2), (key1392, 1), (key1387, 1), (key1773, 1), (key1542, 1), (key1779, 1), (key1555, 1), (key1465, -1), (key1443, -1), (key1797, -1), (key1592, -1), (key1824, -1), (key1666, -1), (key1392, -2), (key1773, -2), (key1547, -2), (key1456, 1), (key1425, 1), (key1789, 1), (key1574, 1), (key1814, 1), (key1656, 1)]

theorem rawRowCheck2255 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block1.form5 = rawRow2255 := by decide +kernel

def row2255 : Integer.Sparse Key := [(key1387, 1), (key1392, -1), (key1420, -1), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -2), (key1555, 1), (key1574, 1), (key1592, -1), (key1618, -1), (key1623, -1), (key1632, 2), (key1656, 1), (key1666, -1), (key1773, -1), (key1779, 1), (key1789, 1), (key1797, -1), (key1816, -1), (key1824, 1)]

theorem rowCheck2255 : row2255 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2255 := by decide +kernel

theorem rowEval2255 (x : Key → ℝ) : Integer.Sparse.eval row2255 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2255, Integer.Sparse.eval_collectBalanced, rawRowCheck2255]

def rawRow2256 : Integer.Sparse Key := [(key1618, -1), (key1623, -1), (key1420, -1), (key1816, -1), (key1425, -1), (key1814, -1), (key1632, 2), (key1443, 2), (key1824, 2), (key1542, 1), (key1555, 1), (key1387, 1), (key1779, 1), (key1392, 1), (key1773, 1), (key1592, -1), (key1666, -1), (key1443, -1), (key1824, -1), (key1465, -1), (key1797, -1), (key1547, -2), (key1392, -2), (key1773, -2), (key1574, 1), (key1656, 1), (key1425, 1), (key1814, 1), (key1456, 1), (key1789, 1)]

theorem rawRowCheck2256 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block1.form5 = rawRow2256 := by decide +kernel

def row2256 : Integer.Sparse Key := [(key1387, 1), (key1392, -1), (key1420, -1), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -2), (key1555, 1), (key1574, 1), (key1592, -1), (key1618, -1), (key1623, -1), (key1632, 2), (key1656, 1), (key1666, -1), (key1773, -1), (key1779, 1), (key1789, 1), (key1797, -1), (key1816, -1), (key1824, 1)]

theorem rowCheck2256 : row2256 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2256 := by decide +kernel

theorem rowEval2256 (x : Key → ℝ) : Integer.Sparse.eval row2256 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2256, Integer.Sparse.eval_collectBalanced, rawRowCheck2256]

def rawRow2257 : Integer.Sparse Key := [(key1623, -1), (key1618, -1), (key1816, -1), (key1420, -1), (key1814, -1), (key1425, -1), (key1632, 2), (key1824, 2), (key1443, 2), (key1555, 1), (key1542, 1), (key1779, 1), (key1387, 1), (key1773, 1), (key1392, 1), (key1666, -1), (key1592, -1), (key1824, -1), (key1443, -1), (key1797, -1), (key1465, -1), (key1547, -2), (key1773, -2), (key1392, -2), (key1656, 1), (key1574, 1), (key1814, 1), (key1425, 1), (key1789, 1), (key1456, 1)]

theorem rawRowCheck2257 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block1.form5 = rawRow2257 := by decide +kernel

def row2257 : Integer.Sparse Key := [(key1387, 1), (key1392, -1), (key1420, -1), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -2), (key1555, 1), (key1574, 1), (key1592, -1), (key1618, -1), (key1623, -1), (key1632, 2), (key1656, 1), (key1666, -1), (key1773, -1), (key1779, 1), (key1789, 1), (key1797, -1), (key1816, -1), (key1824, 1)]

theorem rowCheck2257 : row2257 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2257 := by decide +kernel

theorem rowEval2257 (x : Key → ℝ) : Integer.Sparse.eval row2257 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2257, Integer.Sparse.eval_collectBalanced, rawRowCheck2257]

def rawRow2258 : Integer.Sparse Key := [(key1814, -1), (key1816, -1), (key1425, -1), (key1623, -1), (key1420, -1), (key1618, -1), (key1824, 2), (key1443, 2), (key1632, 2), (key1773, 1), (key1779, 1), (key1392, 1), (key1555, 1), (key1387, 1), (key1542, 1), (key1797, -1), (key1824, -1), (key1465, -1), (key1666, -1), (key1443, -1), (key1592, -1), (key1773, -2), (key1392, -2), (key1547, -2), (key1789, 1), (key1814, 1), (key1456, 1), (key1656, 1), (key1425, 1), (key1574, 1)]

theorem rawRowCheck2258 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block1.form5 = rawRow2258 := by decide +kernel

def row2258 : Integer.Sparse Key := [(key1387, 1), (key1392, -1), (key1420, -1), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -2), (key1555, 1), (key1574, 1), (key1592, -1), (key1618, -1), (key1623, -1), (key1632, 2), (key1656, 1), (key1666, -1), (key1773, -1), (key1779, 1), (key1789, 1), (key1797, -1), (key1816, -1), (key1824, 1)]

theorem rowCheck2258 : row2258 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2258 := by decide +kernel

theorem rowEval2258 (x : Key → ℝ) : Integer.Sparse.eval row2258 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2258, Integer.Sparse.eval_collectBalanced, rawRowCheck2258]

def rawRow2259 : Integer.Sparse Key := [(key1816, -1), (key1814, -1), (key1623, -1), (key1425, -1), (key1618, -1), (key1420, -1), (key1824, 2), (key1632, 2), (key1443, 2), (key1779, 1), (key1773, 1), (key1555, 1), (key1392, 1), (key1542, 1), (key1387, 1), (key1824, -1), (key1797, -1), (key1666, -1), (key1465, -1), (key1592, -1), (key1443, -1), (key1773, -2), (key1547, -2), (key1392, -2), (key1814, 1), (key1789, 1), (key1656, 1), (key1456, 1), (key1574, 1), (key1425, 1)]

theorem rawRowCheck2259 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block1.form5 = rawRow2259 := by decide +kernel

def row2259 : Integer.Sparse Key := [(key1387, 1), (key1392, -1), (key1420, -1), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -2), (key1555, 1), (key1574, 1), (key1592, -1), (key1618, -1), (key1623, -1), (key1632, 2), (key1656, 1), (key1666, -1), (key1773, -1), (key1779, 1), (key1789, 1), (key1797, -1), (key1816, -1), (key1824, 1)]

theorem rowCheck2259 : row2259 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2259 := by decide +kernel

theorem rowEval2259 (x : Key → ℝ) : Integer.Sparse.eval row2259 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2259, Integer.Sparse.eval_collectBalanced, rawRowCheck2259]

def rawRow2260 : Integer.Sparse Key := [(key1312, -1), (key1317, -1), (key1618, -1), (key1814, -1), (key1632, -1), (key1824, -1), (key1325, 2), (key1623, 2), (key1816, 2), (key1292, 1), (key1297, 1), (key1569, 1), (key1789, 1), (key1592, 1), (key1797, 1), (key1325, -1), (key1344, -1), (key1555, -1), (key1779, -1), (key1658, -1), (key1816, -1), (key1297, -2), (key1574, -2), (key1789, -2), (key1317, 1), (key1338, 1), (key1547, 1), (key1773, 1), (key1656, 1), (key1814, 1)]

theorem rawRowCheck2260 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form5 = rawRow2260 := by decide +kernel

def row2260 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1325, 1), (key1338, 1), (key1344, -1), (key1547, 1), (key1555, -1), (key1569, 1), (key1574, -2), (key1592, 1), (key1618, -1), (key1623, 2), (key1632, -1), (key1656, 1), (key1658, -1), (key1773, 1), (key1779, -1), (key1789, -1), (key1797, 1), (key1816, 1), (key1824, -1)]

theorem rowCheck2260 : row2260 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2260 := by decide +kernel

theorem rowEval2260 (x : Key → ℝ) : Integer.Sparse.eval row2260 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2260, Integer.Sparse.eval_collectBalanced, rawRowCheck2260]

def rawRow2261 : Integer.Sparse Key := [(key1317, -1), (key1312, -1), (key1814, -1), (key1618, -1), (key1824, -1), (key1632, -1), (key1325, 2), (key1816, 2), (key1623, 2), (key1297, 1), (key1292, 1), (key1789, 1), (key1569, 1), (key1797, 1), (key1592, 1), (key1344, -1), (key1325, -1), (key1779, -1), (key1555, -1), (key1816, -1), (key1658, -1), (key1297, -2), (key1789, -2), (key1574, -2), (key1338, 1), (key1317, 1), (key1773, 1), (key1547, 1), (key1814, 1), (key1656, 1)]

theorem rawRowCheck2261 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form5 = rawRow2261 := by decide +kernel

def row2261 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1325, 1), (key1338, 1), (key1344, -1), (key1547, 1), (key1555, -1), (key1569, 1), (key1574, -2), (key1592, 1), (key1618, -1), (key1623, 2), (key1632, -1), (key1656, 1), (key1658, -1), (key1773, 1), (key1779, -1), (key1789, -1), (key1797, 1), (key1816, 1), (key1824, -1)]

theorem rowCheck2261 : row2261 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2261 := by decide +kernel

theorem rowEval2261 (x : Key → ℝ) : Integer.Sparse.eval row2261 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2261, Integer.Sparse.eval_collectBalanced, rawRowCheck2261]

def rawRow2262 : Integer.Sparse Key := [(key1618, -1), (key1632, -1), (key1312, -1), (key1824, -1), (key1317, -1), (key1814, -1), (key1623, 2), (key1325, 2), (key1816, 2), (key1569, 1), (key1592, 1), (key1292, 1), (key1797, 1), (key1297, 1), (key1789, 1), (key1555, -1), (key1658, -1), (key1325, -1), (key1816, -1), (key1344, -1), (key1779, -1), (key1574, -2), (key1297, -2), (key1789, -2), (key1547, 1), (key1656, 1), (key1317, 1), (key1814, 1), (key1338, 1), (key1773, 1)]

theorem rawRowCheck2262 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form5 = rawRow2262 := by decide +kernel

def row2262 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1325, 1), (key1338, 1), (key1344, -1), (key1547, 1), (key1555, -1), (key1569, 1), (key1574, -2), (key1592, 1), (key1618, -1), (key1623, 2), (key1632, -1), (key1656, 1), (key1658, -1), (key1773, 1), (key1779, -1), (key1789, -1), (key1797, 1), (key1816, 1), (key1824, -1)]

theorem rowCheck2262 : row2262 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2262 := by decide +kernel

theorem rowEval2262 (x : Key → ℝ) : Integer.Sparse.eval row2262 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2262, Integer.Sparse.eval_collectBalanced, rawRowCheck2262]

def rawRow2263 : Integer.Sparse Key := [(key1632, -1), (key1618, -1), (key1824, -1), (key1312, -1), (key1814, -1), (key1317, -1), (key1623, 2), (key1816, 2), (key1325, 2), (key1592, 1), (key1569, 1), (key1797, 1), (key1292, 1), (key1789, 1), (key1297, 1), (key1658, -1), (key1555, -1), (key1816, -1), (key1325, -1), (key1779, -1), (key1344, -1), (key1574, -2), (key1789, -2), (key1297, -2), (key1656, 1), (key1547, 1), (key1814, 1), (key1317, 1), (key1773, 1), (key1338, 1)]

theorem rawRowCheck2263 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form5 = rawRow2263 := by decide +kernel

def row2263 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1325, 1), (key1338, 1), (key1344, -1), (key1547, 1), (key1555, -1), (key1569, 1), (key1574, -2), (key1592, 1), (key1618, -1), (key1623, 2), (key1632, -1), (key1656, 1), (key1658, -1), (key1773, 1), (key1779, -1), (key1789, -1), (key1797, 1), (key1816, 1), (key1824, -1)]

theorem rowCheck2263 : row2263 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2263 := by decide +kernel

theorem rowEval2263 (x : Key → ℝ) : Integer.Sparse.eval row2263 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck2263, Integer.Sparse.eval_collectBalanced, rawRowCheck2263]

def rawRow2264 : Integer.Sparse Key := [(key1814, -1), (key1824, -1), (key1317, -1), (key1632, -1), (key1312, -1), (key1618, -1), (key1816, 2), (key1325, 2), (key1623, 2), (key1789, 1), (key1797, 1), (key1297, 1), (key1592, 1), (key1292, 1), (key1569, 1), (key1779, -1), (key1816, -1), (key1344, -1), (key1658, -1), (key1325, -1), (key1555, -1), (key1789, -2), (key1297, -2), (key1574, -2), (key1773, 1), (key1814, 1), (key1338, 1), (key1656, 1), (key1317, 1), (key1547, 1)]

theorem rawRowCheck2264 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form5 = rawRow2264 := by decide +kernel

def row2264 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1325, 1), (key1338, 1), (key1344, -1), (key1547, 1), (key1555, -1), (key1569, 1), (key1574, -2), (key1592, 1), (key1618, -1), (key1623, 2), (key1632, -1), (key1656, 1), (key1658, -1), (key1773, 1), (key1779, -1), (key1789, -1), (key1797, 1), (key1816, 1), (key1824, -1)]

theorem rowCheck2264 : row2264 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2264 := by decide +kernel

theorem rowEval2264 (x : Key → ℝ) : Integer.Sparse.eval row2264 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2264, Integer.Sparse.eval_collectBalanced, rawRowCheck2264]

def rawRow2265 : Integer.Sparse Key := [(key1824, -1), (key1814, -1), (key1632, -1), (key1317, -1), (key1618, -1), (key1312, -1), (key1816, 2), (key1623, 2), (key1325, 2), (key1797, 1), (key1789, 1), (key1592, 1), (key1297, 1), (key1569, 1), (key1292, 1), (key1816, -1), (key1779, -1), (key1658, -1), (key1344, -1), (key1555, -1), (key1325, -1), (key1789, -2), (key1574, -2), (key1297, -2), (key1814, 1), (key1773, 1), (key1656, 1), (key1338, 1), (key1547, 1), (key1317, 1)]

theorem rawRowCheck2265 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form5 = rawRow2265 := by decide +kernel

def row2265 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1325, 1), (key1338, 1), (key1344, -1), (key1547, 1), (key1555, -1), (key1569, 1), (key1574, -2), (key1592, 1), (key1618, -1), (key1623, 2), (key1632, -1), (key1656, 1), (key1658, -1), (key1773, 1), (key1779, -1), (key1789, -1), (key1797, 1), (key1816, 1), (key1824, -1)]

theorem rowCheck2265 : row2265 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2265 := by decide +kernel

theorem rowEval2265 (x : Key → ℝ) : Integer.Sparse.eval row2265 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck2265, Integer.Sparse.eval_collectBalanced, rawRowCheck2265]

def rawRow2266 : Integer.Sparse Key := [(key3062, -2), (key3071, -2), (key3071, -2), (key3067, 2), (key3073, 2), (key3073, 2), (key3097, 2), (key3108, 2), (key3108, 2), (key3135, -6), (key3104, -2), (key3111, -2), (key3111, -2), (key3137, 6)]

theorem rawRowCheck2266 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form6 = rawRow2266 := by decide +kernel

def row2266 : Integer.Sparse Key := [(key3062, -2), (key3067, 2), (key3071, -4), (key3073, 4), (key3097, 2), (key3104, -2), (key3108, 4), (key3111, -4), (key3135, -6), (key3137, 6)]

theorem rowCheck2266 : row2266 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2266 := by decide +kernel

theorem rowEval2266 (x : Key → ℝ) : Integer.Sparse.eval row2266 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2266, Integer.Sparse.eval_collectBalanced, rawRowCheck2266]

def rawRow2267 : Integer.Sparse Key := [(key3071, -2), (key3062, -2), (key3071, -2), (key3073, 2), (key3067, 2), (key3073, 2), (key3108, 2), (key3097, 2), (key3108, 2), (key3135, -6), (key3111, -2), (key3104, -2), (key3111, -2), (key3137, 6)]

theorem rawRowCheck2267 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form6 = rawRow2267 := by decide +kernel

def row2267 : Integer.Sparse Key := [(key3062, -2), (key3067, 2), (key3071, -4), (key3073, 4), (key3097, 2), (key3104, -2), (key3108, 4), (key3111, -4), (key3135, -6), (key3137, 6)]

theorem rowCheck2267 : row2267 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2267 := by decide +kernel

theorem rowEval2267 (x : Key → ℝ) : Integer.Sparse.eval row2267 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2267, Integer.Sparse.eval_collectBalanced, rawRowCheck2267]

def rawRow2268 : Integer.Sparse Key := [(key3071, -2), (key3071, -2), (key3062, -2), (key3073, 2), (key3073, 2), (key3067, 2), (key3108, 2), (key3108, 2), (key3097, 2), (key3135, -6), (key3111, -2), (key3111, -2), (key3104, -2), (key3137, 6)]

theorem rawRowCheck2268 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form6 = rawRow2268 := by decide +kernel

def row2268 : Integer.Sparse Key := [(key3062, -2), (key3067, 2), (key3071, -4), (key3073, 4), (key3097, 2), (key3104, -2), (key3108, 4), (key3111, -4), (key3135, -6), (key3137, 6)]

theorem rowCheck2268 : row2268 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2268 := by decide +kernel

theorem rowEval2268 (x : Key → ℝ) : Integer.Sparse.eval row2268 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2268, Integer.Sparse.eval_collectBalanced, rawRowCheck2268]

def rawRow2269 : Integer.Sparse Key := [(key3048, -2), (key3056, -2), (key3073, -2), (key3052, 2), (key3056, 2), (key3071, 2), (key3097, 2), (key3108, 2), (key3135, 2), (key3108, -6), (key3104, -2), (key3111, -2), (key3137, -2), (key3111, 6)]

theorem rawRowCheck2269 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block1.form6 = rawRow2269 := by decide +kernel

def row2269 : Integer.Sparse Key := [(key3048, -2), (key3052, 2), (key3071, 2), (key3073, -2), (key3097, 2), (key3104, -2), (key3108, -4), (key3111, 4), (key3135, 2), (key3137, -2)]

theorem rowCheck2269 : row2269 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2269 := by decide +kernel

theorem rowEval2269 (x : Key → ℝ) : Integer.Sparse.eval row2269 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2269, Integer.Sparse.eval_collectBalanced, rawRowCheck2269]

def rawRow2270 : Integer.Sparse Key := [(key3056, -2), (key3048, -2), (key3073, -2), (key3056, 2), (key3052, 2), (key3071, 2), (key3108, 2), (key3097, 2), (key3135, 2), (key3108, -6), (key3111, -2), (key3104, -2), (key3137, -2), (key3111, 6)]

theorem rawRowCheck2270 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block1.form6 = rawRow2270 := by decide +kernel

def row2270 : Integer.Sparse Key := [(key3048, -2), (key3052, 2), (key3071, 2), (key3073, -2), (key3097, 2), (key3104, -2), (key3108, -4), (key3111, 4), (key3135, 2), (key3137, -2)]

theorem rowCheck2270 : row2270 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2270 := by decide +kernel

theorem rowEval2270 (x : Key → ℝ) : Integer.Sparse.eval row2270 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2270, Integer.Sparse.eval_collectBalanced, rawRowCheck2270]

def rawRow2271 : Integer.Sparse Key := [(key3048, -2), (key3073, -2), (key3056, -2), (key3052, 2), (key3071, 2), (key3056, 2), (key3097, 2), (key3135, 2), (key3108, 2), (key3108, -6), (key3104, -2), (key3137, -2), (key3111, -2), (key3111, 6)]

theorem rawRowCheck2271 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block1.form6 = rawRow2271 := by decide +kernel

def row2271 : Integer.Sparse Key := [(key3048, -2), (key3052, 2), (key3071, 2), (key3073, -2), (key3097, 2), (key3104, -2), (key3108, -4), (key3111, 4), (key3135, 2), (key3137, -2)]

theorem rowCheck2271 : row2271 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2271 := by decide +kernel

theorem rowEval2271 (x : Key → ℝ) : Integer.Sparse.eval row2271 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2271, Integer.Sparse.eval_collectBalanced, rawRowCheck2271]

def rawRow2272 : Integer.Sparse Key := [(key3073, -2), (key3048, -2), (key3056, -2), (key3071, 2), (key3052, 2), (key3056, 2), (key3135, 2), (key3097, 2), (key3108, 2), (key3108, -6), (key3137, -2), (key3104, -2), (key3111, -2), (key3111, 6)]

theorem rawRowCheck2272 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block1.form6 = rawRow2272 := by decide +kernel

def row2272 : Integer.Sparse Key := [(key3048, -2), (key3052, 2), (key3071, 2), (key3073, -2), (key3097, 2), (key3104, -2), (key3108, -4), (key3111, 4), (key3135, 2), (key3137, -2)]

theorem rowCheck2272 : row2272 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2272 := by decide +kernel

theorem rowEval2272 (x : Key → ℝ) : Integer.Sparse.eval row2272 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2272, Integer.Sparse.eval_collectBalanced, rawRowCheck2272]

def rawRow2273 : Integer.Sparse Key := [(key3056, -2), (key3073, -2), (key3048, -2), (key3056, 2), (key3071, 2), (key3052, 2), (key3108, 2), (key3135, 2), (key3097, 2), (key3108, -6), (key3111, -2), (key3137, -2), (key3104, -2), (key3111, 6)]

theorem rawRowCheck2273 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block1.form6 = rawRow2273 := by decide +kernel

def row2273 : Integer.Sparse Key := [(key3048, -2), (key3052, 2), (key3071, 2), (key3073, -2), (key3097, 2), (key3104, -2), (key3108, -4), (key3111, 4), (key3135, 2), (key3137, -2)]

theorem rowCheck2273 : row2273 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2273 := by decide +kernel

theorem rowEval2273 (x : Key → ℝ) : Integer.Sparse.eval row2273 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2273, Integer.Sparse.eval_collectBalanced, rawRowCheck2273]

def rawRow2274 : Integer.Sparse Key := [(key3073, -2), (key3056, -2), (key3048, -2), (key3071, 2), (key3056, 2), (key3052, 2), (key3135, 2), (key3108, 2), (key3097, 2), (key3108, -6), (key3137, -2), (key3111, -2), (key3104, -2), (key3111, 6)]

theorem rawRowCheck2274 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block1.form6 = rawRow2274 := by decide +kernel

def row2274 : Integer.Sparse Key := [(key3048, -2), (key3052, 2), (key3071, 2), (key3073, -2), (key3097, 2), (key3104, -2), (key3108, -4), (key3111, 4), (key3135, 2), (key3137, -2)]

theorem rowCheck2274 : row2274 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2274 := by decide +kernel

theorem rowEval2274 (x : Key → ℝ) : Integer.Sparse.eval row2274 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2274, Integer.Sparse.eval_collectBalanced, rawRowCheck2274]

def rawRow2275 : Integer.Sparse Key := [(key3097, -2), (key3108, -2), (key3108, -2), (key3104, 2), (key3111, 2), (key3111, 2), (key3062, 2), (key3071, 2), (key3071, 2), (key3137, -6), (key3067, -2), (key3073, -2), (key3073, -2), (key3135, 6)]

theorem rawRowCheck2275 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form6 = rawRow2275 := by decide +kernel

def row2275 : Integer.Sparse Key := [(key3062, 2), (key3067, -2), (key3071, 4), (key3073, -4), (key3097, -2), (key3104, 2), (key3108, -4), (key3111, 4), (key3135, 6), (key3137, -6)]

theorem rowCheck2275 : row2275 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2275 := by decide +kernel

theorem rowEval2275 (x : Key → ℝ) : Integer.Sparse.eval row2275 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2275, Integer.Sparse.eval_collectBalanced, rawRowCheck2275]

def rawRow2276 : Integer.Sparse Key := [(key3108, -2), (key3097, -2), (key3108, -2), (key3111, 2), (key3104, 2), (key3111, 2), (key3071, 2), (key3062, 2), (key3071, 2), (key3137, -6), (key3073, -2), (key3067, -2), (key3073, -2), (key3135, 6)]

theorem rawRowCheck2276 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form6 = rawRow2276 := by decide +kernel

def row2276 : Integer.Sparse Key := [(key3062, 2), (key3067, -2), (key3071, 4), (key3073, -4), (key3097, -2), (key3104, 2), (key3108, -4), (key3111, 4), (key3135, 6), (key3137, -6)]

theorem rowCheck2276 : row2276 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2276 := by decide +kernel

theorem rowEval2276 (x : Key → ℝ) : Integer.Sparse.eval row2276 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2276, Integer.Sparse.eval_collectBalanced, rawRowCheck2276]

def rawRow2277 : Integer.Sparse Key := [(key3108, -2), (key3108, -2), (key3097, -2), (key3111, 2), (key3111, 2), (key3104, 2), (key3071, 2), (key3071, 2), (key3062, 2), (key3137, -6), (key3073, -2), (key3073, -2), (key3067, -2), (key3135, 6)]

theorem rawRowCheck2277 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form6 = rawRow2277 := by decide +kernel

def row2277 : Integer.Sparse Key := [(key3062, 2), (key3067, -2), (key3071, 4), (key3073, -4), (key3097, -2), (key3104, 2), (key3108, -4), (key3111, 4), (key3135, 6), (key3137, -6)]

theorem rowCheck2277 : row2277 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2277 := by decide +kernel

theorem rowEval2277 (x : Key → ℝ) : Integer.Sparse.eval row2277 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2277, Integer.Sparse.eval_collectBalanced, rawRowCheck2277]

def rawRow2278 : Integer.Sparse Key := [(key3048, -2), (key3056, -2), (key3111, -2), (key3052, 2), (key3056, 2), (key3108, 2), (key3062, 2), (key3071, 2), (key3137, 2), (key3071, -6), (key3067, -2), (key3073, -2), (key3135, -2), (key3073, 6)]

theorem rawRowCheck2278 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form6 = rawRow2278 := by decide +kernel

def row2278 : Integer.Sparse Key := [(key3048, -2), (key3052, 2), (key3062, 2), (key3067, -2), (key3071, -4), (key3073, 4), (key3108, 2), (key3111, -2), (key3135, -2), (key3137, 2)]

theorem rowCheck2278 : row2278 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2278 := by decide +kernel

theorem rowEval2278 (x : Key → ℝ) : Integer.Sparse.eval row2278 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2278, Integer.Sparse.eval_collectBalanced, rawRowCheck2278]

def rawRow2279 : Integer.Sparse Key := [(key3056, -2), (key3048, -2), (key3111, -2), (key3056, 2), (key3052, 2), (key3108, 2), (key3071, 2), (key3062, 2), (key3137, 2), (key3071, -6), (key3073, -2), (key3067, -2), (key3135, -2), (key3073, 6)]

theorem rawRowCheck2279 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form6 = rawRow2279 := by decide +kernel

def row2279 : Integer.Sparse Key := [(key3048, -2), (key3052, 2), (key3062, 2), (key3067, -2), (key3071, -4), (key3073, 4), (key3108, 2), (key3111, -2), (key3135, -2), (key3137, 2)]

theorem rowCheck2279 : row2279 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2279 := by decide +kernel

theorem rowEval2279 (x : Key → ℝ) : Integer.Sparse.eval row2279 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2279, Integer.Sparse.eval_collectBalanced, rawRowCheck2279]

def rawRow2280 : Integer.Sparse Key := [(key3048, -2), (key3111, -2), (key3056, -2), (key3052, 2), (key3108, 2), (key3056, 2), (key3062, 2), (key3137, 2), (key3071, 2), (key3071, -6), (key3067, -2), (key3135, -2), (key3073, -2), (key3073, 6)]

theorem rawRowCheck2280 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form6 = rawRow2280 := by decide +kernel

def row2280 : Integer.Sparse Key := [(key3048, -2), (key3052, 2), (key3062, 2), (key3067, -2), (key3071, -4), (key3073, 4), (key3108, 2), (key3111, -2), (key3135, -2), (key3137, 2)]

theorem rowCheck2280 : row2280 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2280 := by decide +kernel

theorem rowEval2280 (x : Key → ℝ) : Integer.Sparse.eval row2280 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2280, Integer.Sparse.eval_collectBalanced, rawRowCheck2280]

def rawRow2281 : Integer.Sparse Key := [(key3111, -2), (key3048, -2), (key3056, -2), (key3108, 2), (key3052, 2), (key3056, 2), (key3137, 2), (key3062, 2), (key3071, 2), (key3071, -6), (key3135, -2), (key3067, -2), (key3073, -2), (key3073, 6)]

theorem rawRowCheck2281 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form6 = rawRow2281 := by decide +kernel

def row2281 : Integer.Sparse Key := [(key3048, -2), (key3052, 2), (key3062, 2), (key3067, -2), (key3071, -4), (key3073, 4), (key3108, 2), (key3111, -2), (key3135, -2), (key3137, 2)]

theorem rowCheck2281 : row2281 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2281 := by decide +kernel

theorem rowEval2281 (x : Key → ℝ) : Integer.Sparse.eval row2281 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck2281, Integer.Sparse.eval_collectBalanced, rawRowCheck2281]

def rawRow2282 : Integer.Sparse Key := [(key3056, -2), (key3111, -2), (key3048, -2), (key3056, 2), (key3108, 2), (key3052, 2), (key3071, 2), (key3137, 2), (key3062, 2), (key3071, -6), (key3073, -2), (key3135, -2), (key3067, -2), (key3073, 6)]

theorem rawRowCheck2282 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form6 = rawRow2282 := by decide +kernel

def row2282 : Integer.Sparse Key := [(key3048, -2), (key3052, 2), (key3062, 2), (key3067, -2), (key3071, -4), (key3073, 4), (key3108, 2), (key3111, -2), (key3135, -2), (key3137, 2)]

theorem rowCheck2282 : row2282 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2282 := by decide +kernel

theorem rowEval2282 (x : Key → ℝ) : Integer.Sparse.eval row2282 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2282, Integer.Sparse.eval_collectBalanced, rawRowCheck2282]

def rawRow2283 : Integer.Sparse Key := [(key3111, -2), (key3056, -2), (key3048, -2), (key3108, 2), (key3056, 2), (key3052, 2), (key3137, 2), (key3071, 2), (key3062, 2), (key3071, -6), (key3135, -2), (key3073, -2), (key3067, -2), (key3073, 6)]

theorem rawRowCheck2283 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form6 = rawRow2283 := by decide +kernel

def row2283 : Integer.Sparse Key := [(key3048, -2), (key3052, 2), (key3062, 2), (key3067, -2), (key3071, -4), (key3073, 4), (key3108, 2), (key3111, -2), (key3135, -2), (key3137, 2)]

theorem rowCheck2283 : row2283 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2283 := by decide +kernel

theorem rowEval2283 (x : Key → ℝ) : Integer.Sparse.eval row2283 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck2283, Integer.Sparse.eval_collectBalanced, rawRowCheck2283]

def rawRow2284 : Integer.Sparse Key := [(key3097, -2), (key3108, -2), (key3135, -2), (key3104, 2), (key3111, 2), (key3137, 2), (key3048, 2), (key3056, 2), (key3073, 2), (key3111, -6), (key3052, -2), (key3056, -2), (key3071, -2), (key3108, 6)]

theorem rawRowCheck2284 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block1.form6 = rawRow2284 := by decide +kernel

def row2284 : Integer.Sparse Key := [(key3048, 2), (key3052, -2), (key3071, -2), (key3073, 2), (key3097, -2), (key3104, 2), (key3108, 4), (key3111, -4), (key3135, -2), (key3137, 2)]

theorem rowCheck2284 : row2284 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2284 := by decide +kernel

theorem rowEval2284 (x : Key → ℝ) : Integer.Sparse.eval row2284 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2284, Integer.Sparse.eval_collectBalanced, rawRowCheck2284]

def rawRow2285 : Integer.Sparse Key := [(key3108, -2), (key3097, -2), (key3135, -2), (key3111, 2), (key3104, 2), (key3137, 2), (key3056, 2), (key3048, 2), (key3073, 2), (key3111, -6), (key3056, -2), (key3052, -2), (key3071, -2), (key3108, 6)]

theorem rawRowCheck2285 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block1.form6 = rawRow2285 := by decide +kernel

def row2285 : Integer.Sparse Key := [(key3048, 2), (key3052, -2), (key3071, -2), (key3073, 2), (key3097, -2), (key3104, 2), (key3108, 4), (key3111, -4), (key3135, -2), (key3137, 2)]

theorem rowCheck2285 : row2285 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2285 := by decide +kernel

theorem rowEval2285 (x : Key → ℝ) : Integer.Sparse.eval row2285 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2285, Integer.Sparse.eval_collectBalanced, rawRowCheck2285]

def rawRow2286 : Integer.Sparse Key := [(key3097, -2), (key3135, -2), (key3108, -2), (key3104, 2), (key3137, 2), (key3111, 2), (key3048, 2), (key3073, 2), (key3056, 2), (key3111, -6), (key3052, -2), (key3071, -2), (key3056, -2), (key3108, 6)]

theorem rawRowCheck2286 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block1.form6 = rawRow2286 := by decide +kernel

def row2286 : Integer.Sparse Key := [(key3048, 2), (key3052, -2), (key3071, -2), (key3073, 2), (key3097, -2), (key3104, 2), (key3108, 4), (key3111, -4), (key3135, -2), (key3137, 2)]

theorem rowCheck2286 : row2286 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2286 := by decide +kernel

theorem rowEval2286 (x : Key → ℝ) : Integer.Sparse.eval row2286 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2286, Integer.Sparse.eval_collectBalanced, rawRowCheck2286]

def rawRow2287 : Integer.Sparse Key := [(key3135, -2), (key3097, -2), (key3108, -2), (key3137, 2), (key3104, 2), (key3111, 2), (key3073, 2), (key3048, 2), (key3056, 2), (key3111, -6), (key3071, -2), (key3052, -2), (key3056, -2), (key3108, 6)]

theorem rawRowCheck2287 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block1.form6 = rawRow2287 := by decide +kernel

def row2287 : Integer.Sparse Key := [(key3048, 2), (key3052, -2), (key3071, -2), (key3073, 2), (key3097, -2), (key3104, 2), (key3108, 4), (key3111, -4), (key3135, -2), (key3137, 2)]

theorem rowCheck2287 : row2287 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2287 := by decide +kernel

theorem rowEval2287 (x : Key → ℝ) : Integer.Sparse.eval row2287 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2287, Integer.Sparse.eval_collectBalanced, rawRowCheck2287]

def rawRow2288 : Integer.Sparse Key := [(key3108, -2), (key3135, -2), (key3097, -2), (key3111, 2), (key3137, 2), (key3104, 2), (key3056, 2), (key3073, 2), (key3048, 2), (key3111, -6), (key3056, -2), (key3071, -2), (key3052, -2), (key3108, 6)]

theorem rawRowCheck2288 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block1.form6 = rawRow2288 := by decide +kernel

def row2288 : Integer.Sparse Key := [(key3048, 2), (key3052, -2), (key3071, -2), (key3073, 2), (key3097, -2), (key3104, 2), (key3108, 4), (key3111, -4), (key3135, -2), (key3137, 2)]

theorem rowCheck2288 : row2288 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2288 := by decide +kernel

theorem rowEval2288 (x : Key → ℝ) : Integer.Sparse.eval row2288 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2288, Integer.Sparse.eval_collectBalanced, rawRowCheck2288]

def rawRow2289 : Integer.Sparse Key := [(key3135, -2), (key3108, -2), (key3097, -2), (key3137, 2), (key3111, 2), (key3104, 2), (key3073, 2), (key3056, 2), (key3048, 2), (key3111, -6), (key3071, -2), (key3056, -2), (key3052, -2), (key3108, 6)]

theorem rawRowCheck2289 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block1.form6 = rawRow2289 := by decide +kernel

def row2289 : Integer.Sparse Key := [(key3048, 2), (key3052, -2), (key3071, -2), (key3073, 2), (key3097, -2), (key3104, 2), (key3108, 4), (key3111, -4), (key3135, -2), (key3137, 2)]

theorem rowCheck2289 : row2289 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2289 := by decide +kernel

theorem rowEval2289 (x : Key → ℝ) : Integer.Sparse.eval row2289 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2289, Integer.Sparse.eval_collectBalanced, rawRowCheck2289]

def rawRow2290 : Integer.Sparse Key := [(key3062, -2), (key3071, -2), (key3137, -2), (key3067, 2), (key3073, 2), (key3135, 2), (key3048, 2), (key3056, 2), (key3111, 2), (key3073, -6), (key3052, -2), (key3056, -2), (key3108, -2), (key3071, 6)]

theorem rawRowCheck2290 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form6 = rawRow2290 := by decide +kernel

def row2290 : Integer.Sparse Key := [(key3048, 2), (key3052, -2), (key3062, -2), (key3067, 2), (key3071, 4), (key3073, -4), (key3108, -2), (key3111, 2), (key3135, 2), (key3137, -2)]

theorem rowCheck2290 : row2290 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2290 := by decide +kernel

theorem rowEval2290 (x : Key → ℝ) : Integer.Sparse.eval row2290 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2290, Integer.Sparse.eval_collectBalanced, rawRowCheck2290]

def rawRow2291 : Integer.Sparse Key := [(key3071, -2), (key3062, -2), (key3137, -2), (key3073, 2), (key3067, 2), (key3135, 2), (key3056, 2), (key3048, 2), (key3111, 2), (key3073, -6), (key3056, -2), (key3052, -2), (key3108, -2), (key3071, 6)]

theorem rawRowCheck2291 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form6 = rawRow2291 := by decide +kernel

def row2291 : Integer.Sparse Key := [(key3048, 2), (key3052, -2), (key3062, -2), (key3067, 2), (key3071, 4), (key3073, -4), (key3108, -2), (key3111, 2), (key3135, 2), (key3137, -2)]

theorem rowCheck2291 : row2291 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2291 := by decide +kernel

theorem rowEval2291 (x : Key → ℝ) : Integer.Sparse.eval row2291 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2291, Integer.Sparse.eval_collectBalanced, rawRowCheck2291]

def rawRow2292 : Integer.Sparse Key := [(key3062, -2), (key3137, -2), (key3071, -2), (key3067, 2), (key3135, 2), (key3073, 2), (key3048, 2), (key3111, 2), (key3056, 2), (key3073, -6), (key3052, -2), (key3108, -2), (key3056, -2), (key3071, 6)]

theorem rawRowCheck2292 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form6 = rawRow2292 := by decide +kernel

def row2292 : Integer.Sparse Key := [(key3048, 2), (key3052, -2), (key3062, -2), (key3067, 2), (key3071, 4), (key3073, -4), (key3108, -2), (key3111, 2), (key3135, 2), (key3137, -2)]

theorem rowCheck2292 : row2292 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2292 := by decide +kernel

theorem rowEval2292 (x : Key → ℝ) : Integer.Sparse.eval row2292 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2292, Integer.Sparse.eval_collectBalanced, rawRowCheck2292]

def rawRow2293 : Integer.Sparse Key := [(key3137, -2), (key3062, -2), (key3071, -2), (key3135, 2), (key3067, 2), (key3073, 2), (key3111, 2), (key3048, 2), (key3056, 2), (key3073, -6), (key3108, -2), (key3052, -2), (key3056, -2), (key3071, 6)]

theorem rawRowCheck2293 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form6 = rawRow2293 := by decide +kernel

def row2293 : Integer.Sparse Key := [(key3048, 2), (key3052, -2), (key3062, -2), (key3067, 2), (key3071, 4), (key3073, -4), (key3108, -2), (key3111, 2), (key3135, 2), (key3137, -2)]

theorem rowCheck2293 : row2293 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2293 := by decide +kernel

theorem rowEval2293 (x : Key → ℝ) : Integer.Sparse.eval row2293 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck2293, Integer.Sparse.eval_collectBalanced, rawRowCheck2293]

def rawRow2294 : Integer.Sparse Key := [(key3071, -2), (key3137, -2), (key3062, -2), (key3073, 2), (key3135, 2), (key3067, 2), (key3056, 2), (key3111, 2), (key3048, 2), (key3073, -6), (key3056, -2), (key3108, -2), (key3052, -2), (key3071, 6)]

theorem rawRowCheck2294 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form6 = rawRow2294 := by decide +kernel

def row2294 : Integer.Sparse Key := [(key3048, 2), (key3052, -2), (key3062, -2), (key3067, 2), (key3071, 4), (key3073, -4), (key3108, -2), (key3111, 2), (key3135, 2), (key3137, -2)]

theorem rowCheck2294 : row2294 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2294 := by decide +kernel

theorem rowEval2294 (x : Key → ℝ) : Integer.Sparse.eval row2294 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2294, Integer.Sparse.eval_collectBalanced, rawRowCheck2294]

def rawRow2295 : Integer.Sparse Key := [(key3137, -2), (key3071, -2), (key3062, -2), (key3135, 2), (key3073, 2), (key3067, 2), (key3111, 2), (key3056, 2), (key3048, 2), (key3073, -6), (key3108, -2), (key3056, -2), (key3052, -2), (key3071, 6)]

theorem rawRowCheck2295 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form6 = rawRow2295 := by decide +kernel

def row2295 : Integer.Sparse Key := [(key3048, 2), (key3052, -2), (key3062, -2), (key3067, 2), (key3071, 4), (key3073, -4), (key3108, -2), (key3111, 2), (key3135, 2), (key3137, -2)]

theorem rowCheck2295 : row2295 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2295 := by decide +kernel

theorem rowEval2295 (x : Key → ℝ) : Integer.Sparse.eval row2295 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck2295, Integer.Sparse.eval_collectBalanced, rawRowCheck2295]

def rawRow2296 : Integer.Sparse Key := [(key1292, -2), (key1297, -2), (key1297, -2), (key1312, 1), (key1317, 1), (key1312, 1), (key1338, 1), (key1317, 1), (key1338, 1), (key1387, 2), (key1392, 2), (key1392, 2), (key1542, -1), (key1547, -1), (key1542, -1), (key1773, -1), (key1547, -1), (key1773, -1), (key1420, -1), (key1425, -1), (key1420, -1), (key1456, -1), (key1425, -1), (key1456, -1), (key1569, 1), (key1574, 1), (key1569, 1), (key1789, 1), (key1574, 1), (key1789, 1)]

theorem rawRowCheck2296 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form7 = rawRow2296 := by decide +kernel

def row2296 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1387, 2), (key1392, 4), (key1420, -2), (key1425, -2), (key1456, -2), (key1542, -2), (key1547, -2), (key1569, 2), (key1574, 2), (key1773, -2), (key1789, 2)]

theorem rowCheck2296 : row2296 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2296 := by decide +kernel

theorem rowEval2296 (x : Key → ℝ) : Integer.Sparse.eval row2296 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck2296, Integer.Sparse.eval_collectBalanced, rawRowCheck2296]

def rawRow2297 : Integer.Sparse Key := [(key1297, -2), (key1292, -2), (key1297, -2), (key1317, 1), (key1312, 1), (key1338, 1), (key1312, 1), (key1338, 1), (key1317, 1), (key1392, 2), (key1387, 2), (key1392, 2), (key1547, -1), (key1542, -1), (key1773, -1), (key1542, -1), (key1773, -1), (key1547, -1), (key1425, -1), (key1420, -1), (key1456, -1), (key1420, -1), (key1456, -1), (key1425, -1), (key1574, 1), (key1569, 1), (key1789, 1), (key1569, 1), (key1789, 1), (key1574, 1)]

theorem rawRowCheck2297 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form7 = rawRow2297 := by decide +kernel

def row2297 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1387, 2), (key1392, 4), (key1420, -2), (key1425, -2), (key1456, -2), (key1542, -2), (key1547, -2), (key1569, 2), (key1574, 2), (key1773, -2), (key1789, 2)]

theorem rowCheck2297 : row2297 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2297 := by decide +kernel

theorem rowEval2297 (x : Key → ℝ) : Integer.Sparse.eval row2297 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2297, Integer.Sparse.eval_collectBalanced, rawRowCheck2297]

def rawRow2298 : Integer.Sparse Key := [(key1297, -2), (key1297, -2), (key1292, -2), (key1338, 1), (key1338, 1), (key1317, 1), (key1317, 1), (key1312, 1), (key1312, 1), (key1392, 2), (key1392, 2), (key1387, 2), (key1773, -1), (key1773, -1), (key1547, -1), (key1547, -1), (key1542, -1), (key1542, -1), (key1456, -1), (key1456, -1), (key1425, -1), (key1425, -1), (key1420, -1), (key1420, -1), (key1789, 1), (key1789, 1), (key1574, 1), (key1574, 1), (key1569, 1), (key1569, 1)]

theorem rawRowCheck2298 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form7 = rawRow2298 := by decide +kernel

def row2298 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1387, 2), (key1392, 4), (key1420, -2), (key1425, -2), (key1456, -2), (key1542, -2), (key1547, -2), (key1569, 2), (key1574, 2), (key1773, -2), (key1789, 2)]

theorem rowCheck2298 : row2298 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2298 := by decide +kernel

theorem rowEval2298 (x : Key → ℝ) : Integer.Sparse.eval row2298 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2298, Integer.Sparse.eval_collectBalanced, rawRowCheck2298]

def rawRow2299 : Integer.Sparse Key := [(key1312, -2), (key1317, -2), (key1325, -2), (key1292, 1), (key1297, 1), (key1312, 1), (key1338, 1), (key1325, 1), (key1344, 1), (key1542, 2), (key1547, 2), (key1555, 2), (key1387, -1), (key1392, -1), (key1542, -1), (key1773, -1), (key1555, -1), (key1779, -1), (key1569, -1), (key1574, -1), (key1618, -1), (key1656, -1), (key1623, -1), (key1658, -1), (key1420, 1), (key1425, 1), (key1618, 1), (key1814, 1), (key1623, 1), (key1816, 1)]

theorem rawRowCheck2299 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block1.form7 = rawRow2299 := by decide +kernel

def row2299 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, -1), (key1392, -1), (key1420, 1), (key1425, 1), (key1542, 1), (key1547, 2), (key1555, 1), (key1569, -1), (key1574, -1), (key1656, -1), (key1658, -1), (key1773, -1), (key1779, -1), (key1814, 1), (key1816, 1)]

theorem rowCheck2299 : row2299 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2299 := by decide +kernel

theorem rowEval2299 (x : Key → ℝ) : Integer.Sparse.eval row2299 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck2299, Integer.Sparse.eval_collectBalanced, rawRowCheck2299]

def rawRow2300 : Integer.Sparse Key := [(key1317, -2), (key1312, -2), (key1325, -2), (key1297, 1), (key1292, 1), (key1338, 1), (key1312, 1), (key1344, 1), (key1325, 1), (key1547, 2), (key1542, 2), (key1555, 2), (key1392, -1), (key1387, -1), (key1773, -1), (key1542, -1), (key1779, -1), (key1555, -1), (key1574, -1), (key1569, -1), (key1656, -1), (key1618, -1), (key1658, -1), (key1623, -1), (key1425, 1), (key1420, 1), (key1814, 1), (key1618, 1), (key1816, 1), (key1623, 1)]

theorem rawRowCheck2300 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block1.form7 = rawRow2300 := by decide +kernel

def row2300 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, -1), (key1392, -1), (key1420, 1), (key1425, 1), (key1542, 1), (key1547, 2), (key1555, 1), (key1569, -1), (key1574, -1), (key1656, -1), (key1658, -1), (key1773, -1), (key1779, -1), (key1814, 1), (key1816, 1)]

theorem rowCheck2300 : row2300 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2300 := by decide +kernel

theorem rowEval2300 (x : Key → ℝ) : Integer.Sparse.eval row2300 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2300, Integer.Sparse.eval_collectBalanced, rawRowCheck2300]

def rawRow2301 : Integer.Sparse Key := [(key1312, -2), (key1325, -2), (key1317, -2), (key1312, 1), (key1325, 1), (key1292, 1), (key1344, 1), (key1297, 1), (key1338, 1), (key1542, 2), (key1555, 2), (key1547, 2), (key1542, -1), (key1555, -1), (key1387, -1), (key1779, -1), (key1392, -1), (key1773, -1), (key1618, -1), (key1623, -1), (key1569, -1), (key1658, -1), (key1574, -1), (key1656, -1), (key1618, 1), (key1623, 1), (key1420, 1), (key1816, 1), (key1425, 1), (key1814, 1)]

theorem rawRowCheck2301 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block1.form7 = rawRow2301 := by decide +kernel

def row2301 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, -1), (key1392, -1), (key1420, 1), (key1425, 1), (key1542, 1), (key1547, 2), (key1555, 1), (key1569, -1), (key1574, -1), (key1656, -1), (key1658, -1), (key1773, -1), (key1779, -1), (key1814, 1), (key1816, 1)]

theorem rowCheck2301 : row2301 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2301 := by decide +kernel

theorem rowEval2301 (x : Key → ℝ) : Integer.Sparse.eval row2301 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck2301, Integer.Sparse.eval_collectBalanced, rawRowCheck2301]

def rawRow2302 : Integer.Sparse Key := [(key1325, -2), (key1312, -2), (key1317, -2), (key1325, 1), (key1312, 1), (key1344, 1), (key1292, 1), (key1338, 1), (key1297, 1), (key1555, 2), (key1542, 2), (key1547, 2), (key1555, -1), (key1542, -1), (key1779, -1), (key1387, -1), (key1773, -1), (key1392, -1), (key1623, -1), (key1618, -1), (key1658, -1), (key1569, -1), (key1656, -1), (key1574, -1), (key1623, 1), (key1618, 1), (key1816, 1), (key1420, 1), (key1814, 1), (key1425, 1)]

theorem rawRowCheck2302 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block1.form7 = rawRow2302 := by decide +kernel

def row2302 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, -1), (key1392, -1), (key1420, 1), (key1425, 1), (key1542, 1), (key1547, 2), (key1555, 1), (key1569, -1), (key1574, -1), (key1656, -1), (key1658, -1), (key1773, -1), (key1779, -1), (key1814, 1), (key1816, 1)]

theorem rowCheck2302 : row2302 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2302 := by decide +kernel

theorem rowEval2302 (x : Key → ℝ) : Integer.Sparse.eval row2302 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck2302, Integer.Sparse.eval_collectBalanced, rawRowCheck2302]

def rawRow2303 : Integer.Sparse Key := [(key1317, -2), (key1325, -2), (key1312, -2), (key1338, 1), (key1344, 1), (key1297, 1), (key1325, 1), (key1292, 1), (key1312, 1), (key1547, 2), (key1555, 2), (key1542, 2), (key1773, -1), (key1779, -1), (key1392, -1), (key1555, -1), (key1387, -1), (key1542, -1), (key1656, -1), (key1658, -1), (key1574, -1), (key1623, -1), (key1569, -1), (key1618, -1), (key1814, 1), (key1816, 1), (key1425, 1), (key1623, 1), (key1420, 1), (key1618, 1)]

theorem rawRowCheck2303 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block1.form7 = rawRow2303 := by decide +kernel

def row2303 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, -1), (key1392, -1), (key1420, 1), (key1425, 1), (key1542, 1), (key1547, 2), (key1555, 1), (key1569, -1), (key1574, -1), (key1656, -1), (key1658, -1), (key1773, -1), (key1779, -1), (key1814, 1), (key1816, 1)]

theorem rowCheck2303 : row2303 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2303 := by decide +kernel

theorem rowEval2303 (x : Key → ℝ) : Integer.Sparse.eval row2303 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2303, Integer.Sparse.eval_collectBalanced, rawRowCheck2303]

end MUB6.Certificate.GramRows

end OAI
