import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block24

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow1152 : Integer.Sparse Key := [(key3102, -6), (key3126, 2), (key3102, 2), (key3102, 2), (key3065, 6), (key3124, -2), (key3065, -2), (key3065, -2), (key3063, -2), (key3049, -2), (key3049, -2), (key3098, 2), (key3049, 2), (key3049, 2)]

theorem rawRowCheck1152 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -1, -1] GramFunctions.Block1.form4 = rawRow1152 := by decide +kernel

def row1152 : Integer.Sparse Key := [(key3063, -2), (key3065, 2), (key3098, 2), (key3102, -2), (key3124, -2), (key3126, 2)]

theorem rowCheck1152 : row1152 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1152 := by decide +kernel

theorem rowEval1152 (x : Key → ℝ) : Integer.Sparse.eval row1152 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -1, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1152, Integer.Sparse.eval_collectBalanced, rawRowCheck1152]

def rawRow1153 : Integer.Sparse Key := [(key3126, -6), (key3102, 2), (key3102, 2), (key3102, 2), (key3124, 6), (key3065, -2), (key3065, -2), (key3065, -2), (key3098, -2), (key3098, -2), (key3098, -2), (key3063, 2), (key3063, 2), (key3063, 2)]

theorem rawRowCheck1153 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -1, -1] GramFunctions.Block1.form4 = rawRow1153 := by decide +kernel

def row1153 : Integer.Sparse Key := [(key3063, 6), (key3065, -6), (key3098, -6), (key3102, 6), (key3124, 6), (key3126, -6)]

theorem rowCheck1153 : row1153 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1153 := by decide +kernel

theorem rowEval1153 (x : Key → ℝ) : Integer.Sparse.eval row1153 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -1, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1153, Integer.Sparse.eval_collectBalanced, rawRowCheck1153]

def rawRow1154 : Integer.Sparse Key := [(key1405, -1), (key1414, -1), (key1405, -1), (key1910, -1), (key1414, -1), (key1910, -1), (key1410, 2), (key1410, 2), (key1908, 2), (key1433, 1), (key1439, 1), (key1433, 1), (key1925, 1), (key1439, 1), (key1925, 1), (key1410, -1), (key1477, -1), (key1410, -1), (key1908, -1), (key1477, -1), (key1908, -1), (key1439, -2), (key1439, -2), (key1925, -2), (key1414, 1), (key1479, 1), (key1414, 1), (key1910, 1), (key1479, 1), (key1910, 1)]

theorem rawRowCheck1154 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, -1, 2] GramFunctions.Block1.form5 = rawRow1154 := by decide +kernel

def row1154 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1433, 2), (key1439, -2), (key1477, -2), (key1479, 2)]

theorem rowCheck1154 : row1154 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1154 := by decide +kernel

theorem rowEval1154 (x : Key → ℝ) : Integer.Sparse.eval row1154 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, -1, 2] GramFunctions.Block1.form5) x := by
  rw [rowCheck1154, Integer.Sparse.eval_collectBalanced, rawRowCheck1154]

def rawRow1155 : Integer.Sparse Key := [(key1414, -1), (key1405, -1), (key1910, -1), (key1405, -1), (key1910, -1), (key1414, -1), (key1410, 2), (key1908, 2), (key1410, 2), (key1439, 1), (key1433, 1), (key1925, 1), (key1433, 1), (key1925, 1), (key1439, 1), (key1477, -1), (key1410, -1), (key1908, -1), (key1410, -1), (key1908, -1), (key1477, -1), (key1439, -2), (key1925, -2), (key1439, -2), (key1479, 1), (key1414, 1), (key1910, 1), (key1414, 1), (key1910, 1), (key1479, 1)]

theorem rawRowCheck1155 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, 2, -1] GramFunctions.Block1.form5 = rawRow1155 := by decide +kernel

def row1155 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1433, 2), (key1439, -2), (key1477, -2), (key1479, 2)]

theorem rowCheck1155 : row1155 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1155 := by decide +kernel

theorem rowEval1155 (x : Key → ℝ) : Integer.Sparse.eval row1155 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, 2, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1155, Integer.Sparse.eval_collectBalanced, rawRowCheck1155]

def rawRow1156 : Integer.Sparse Key := [(key1910, -1), (key1910, -1), (key1414, -1), (key1414, -1), (key1405, -1), (key1405, -1), (key1908, 2), (key1410, 2), (key1410, 2), (key1925, 1), (key1925, 1), (key1439, 1), (key1439, 1), (key1433, 1), (key1433, 1), (key1908, -1), (key1908, -1), (key1477, -1), (key1477, -1), (key1410, -1), (key1410, -1), (key1925, -2), (key1439, -2), (key1439, -2), (key1910, 1), (key1910, 1), (key1479, 1), (key1479, 1), (key1414, 1), (key1414, 1)]

theorem rawRowCheck1156 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -1, -1] GramFunctions.Block1.form5 = rawRow1156 := by decide +kernel

def row1156 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1433, 2), (key1439, -2), (key1477, -2), (key1479, 2)]

theorem rowCheck1156 : row1156 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1156 := by decide +kernel

theorem rowEval1156 (x : Key → ℝ) : Integer.Sparse.eval row1156 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -1, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1156, Integer.Sparse.eval_collectBalanced, rawRowCheck1156]

def rawRow1157 : Integer.Sparse Key := [(key1410, -1), (key1414, -1), (key1410, -1), (key1588, -1), (key1414, -1), (key1588, -1), (key1405, 2), (key1405, 2), (key1582, 2), (key1477, 1), (key1479, 1), (key1477, 1), (key1688, 1), (key1479, 1), (key1688, 1), (key1405, -1), (key1433, -1), (key1405, -1), (key1582, -1), (key1433, -1), (key1582, -1), (key1479, -2), (key1479, -2), (key1688, -2), (key1414, 1), (key1439, 1), (key1414, 1), (key1588, 1), (key1439, 1), (key1588, 1)]

theorem rawRowCheck1157 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, -1, 0] GramFunctions.Block1.form5 = rawRow1157 := by decide +kernel

def row1157 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1433, -2), (key1439, 2), (key1477, 2), (key1479, -2)]

theorem rowCheck1157 : row1157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1157 := by decide +kernel

theorem rowEval1157 (x : Key → ℝ) : Integer.Sparse.eval row1157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, -1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1157, Integer.Sparse.eval_collectBalanced, rawRowCheck1157]

def rawRow1158 : Integer.Sparse Key := [(key1414, -1), (key1410, -1), (key1588, -1), (key1410, -1), (key1588, -1), (key1414, -1), (key1405, 2), (key1582, 2), (key1405, 2), (key1479, 1), (key1477, 1), (key1688, 1), (key1477, 1), (key1688, 1), (key1479, 1), (key1433, -1), (key1405, -1), (key1582, -1), (key1405, -1), (key1582, -1), (key1433, -1), (key1479, -2), (key1688, -2), (key1479, -2), (key1439, 1), (key1414, 1), (key1588, 1), (key1414, 1), (key1588, 1), (key1439, 1)]

theorem rawRowCheck1158 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, 0, -1] GramFunctions.Block1.form5 = rawRow1158 := by decide +kernel

def row1158 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1433, -2), (key1439, 2), (key1477, 2), (key1479, -2)]

theorem rowCheck1158 : row1158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1158 := by decide +kernel

theorem rowEval1158 (x : Key → ℝ) : Integer.Sparse.eval row1158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, 0, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1158, Integer.Sparse.eval_collectBalanced, rawRowCheck1158]

def rawRow1159 : Integer.Sparse Key := [(key1588, -1), (key1588, -1), (key1414, -1), (key1414, -1), (key1410, -1), (key1410, -1), (key1582, 2), (key1405, 2), (key1405, 2), (key1688, 1), (key1688, 1), (key1479, 1), (key1479, 1), (key1477, 1), (key1477, 1), (key1582, -1), (key1582, -1), (key1433, -1), (key1433, -1), (key1405, -1), (key1405, -1), (key1688, -2), (key1479, -2), (key1479, -2), (key1588, 1), (key1588, 1), (key1439, 1), (key1439, 1), (key1414, 1), (key1414, 1)]

theorem rawRowCheck1159 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -1, -1] GramFunctions.Block1.form5 = rawRow1159 := by decide +kernel

def row1159 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1433, -2), (key1439, 2), (key1477, 2), (key1479, -2)]

theorem rowCheck1159 : row1159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1159 := by decide +kernel

theorem rowEval1159 (x : Key → ℝ) : Integer.Sparse.eval row1159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -1, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1159, Integer.Sparse.eval_collectBalanced, rawRowCheck1159]

def rawRow1160 : Integer.Sparse Key := [(key1433, -1), (key1439, -1), (key1433, -1), (key1925, -1), (key1439, -1), (key1925, -1), (key1439, 2), (key1439, 2), (key1925, 2), (key1405, 1), (key1414, 1), (key1405, 1), (key1910, 1), (key1414, 1), (key1910, 1), (key1414, -1), (key1479, -1), (key1414, -1), (key1910, -1), (key1479, -1), (key1910, -1), (key1410, -2), (key1410, -2), (key1908, -2), (key1410, 1), (key1477, 1), (key1410, 1), (key1908, 1), (key1477, 1), (key1908, 1)]

theorem rawRowCheck1160 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, -1, 2] GramFunctions.Block1.form5 = rawRow1160 := by decide +kernel

def row1160 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1433, -2), (key1439, 2), (key1477, 2), (key1479, -2)]

theorem rowCheck1160 : row1160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1160 := by decide +kernel

theorem rowEval1160 (x : Key → ℝ) : Integer.Sparse.eval row1160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, -1, 2] GramFunctions.Block1.form5) x := by
  rw [rowCheck1160, Integer.Sparse.eval_collectBalanced, rawRowCheck1160]

def rawRow1161 : Integer.Sparse Key := [(key1439, -1), (key1433, -1), (key1925, -1), (key1433, -1), (key1925, -1), (key1439, -1), (key1439, 2), (key1925, 2), (key1439, 2), (key1414, 1), (key1405, 1), (key1910, 1), (key1405, 1), (key1910, 1), (key1414, 1), (key1479, -1), (key1414, -1), (key1910, -1), (key1414, -1), (key1910, -1), (key1479, -1), (key1410, -2), (key1908, -2), (key1410, -2), (key1477, 1), (key1410, 1), (key1908, 1), (key1410, 1), (key1908, 1), (key1477, 1)]

theorem rawRowCheck1161 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, 2, -1] GramFunctions.Block1.form5 = rawRow1161 := by decide +kernel

def row1161 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1433, -2), (key1439, 2), (key1477, 2), (key1479, -2)]

theorem rowCheck1161 : row1161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1161 := by decide +kernel

theorem rowEval1161 (x : Key → ℝ) : Integer.Sparse.eval row1161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, 2, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1161, Integer.Sparse.eval_collectBalanced, rawRowCheck1161]

def rawRow1162 : Integer.Sparse Key := [(key1925, -1), (key1925, -1), (key1439, -1), (key1439, -1), (key1433, -1), (key1433, -1), (key1925, 2), (key1439, 2), (key1439, 2), (key1910, 1), (key1910, 1), (key1414, 1), (key1414, 1), (key1405, 1), (key1405, 1), (key1910, -1), (key1910, -1), (key1479, -1), (key1479, -1), (key1414, -1), (key1414, -1), (key1908, -2), (key1410, -2), (key1410, -2), (key1908, 1), (key1908, 1), (key1477, 1), (key1477, 1), (key1410, 1), (key1410, 1)]

theorem rawRowCheck1162 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -1, -1] GramFunctions.Block1.form5 = rawRow1162 := by decide +kernel

def row1162 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1433, -2), (key1439, 2), (key1477, 2), (key1479, -2)]

theorem rowCheck1162 : row1162 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1162 := by decide +kernel

theorem rowEval1162 (x : Key → ℝ) : Integer.Sparse.eval row1162 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -1, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1162, Integer.Sparse.eval_collectBalanced, rawRowCheck1162]

def rawRow1163 : Integer.Sparse Key := [(key1439, -1), (key1439, -1), (key1439, -1), (key1439, -1), (key1439, -1), (key1439, -1), (key1433, 2), (key1433, 2), (key1433, 2), (key1479, 1), (key1479, 1), (key1479, 1), (key1479, 1), (key1479, 1), (key1479, 1), (key1405, -1), (key1405, -1), (key1405, -1), (key1405, -1), (key1405, -1), (key1405, -1), (key1477, -2), (key1477, -2), (key1477, -2), (key1410, 1), (key1410, 1), (key1410, 1), (key1410, 1), (key1410, 1), (key1410, 1)]

theorem rawRowCheck1163 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -1, -1] GramFunctions.Block1.form5 = rawRow1163 := by decide +kernel

def row1163 : Integer.Sparse Key := [(key1405, -6), (key1410, 6), (key1433, 6), (key1439, -6), (key1477, -6), (key1479, 6)]

theorem rowCheck1163 : row1163 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1163 := by decide +kernel

theorem rowEval1163 (x : Key → ℝ) : Integer.Sparse.eval row1163 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -1, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1163, Integer.Sparse.eval_collectBalanced, rawRowCheck1163]

def rawRow1164 : Integer.Sparse Key := [(key1477, -1), (key1479, -1), (key1477, -1), (key1688, -1), (key1479, -1), (key1688, -1), (key1479, 2), (key1479, 2), (key1688, 2), (key1410, 1), (key1414, 1), (key1410, 1), (key1588, 1), (key1414, 1), (key1588, 1), (key1414, -1), (key1439, -1), (key1414, -1), (key1588, -1), (key1439, -1), (key1588, -1), (key1405, -2), (key1405, -2), (key1582, -2), (key1405, 1), (key1433, 1), (key1405, 1), (key1582, 1), (key1433, 1), (key1582, 1)]

theorem rawRowCheck1164 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, -1, 0] GramFunctions.Block1.form5 = rawRow1164 := by decide +kernel

def row1164 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1433, 2), (key1439, -2), (key1477, -2), (key1479, 2)]

theorem rowCheck1164 : row1164 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1164 := by decide +kernel

theorem rowEval1164 (x : Key → ℝ) : Integer.Sparse.eval row1164 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, -1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1164, Integer.Sparse.eval_collectBalanced, rawRowCheck1164]

def rawRow1165 : Integer.Sparse Key := [(key1479, -1), (key1477, -1), (key1688, -1), (key1477, -1), (key1688, -1), (key1479, -1), (key1479, 2), (key1688, 2), (key1479, 2), (key1414, 1), (key1410, 1), (key1588, 1), (key1410, 1), (key1588, 1), (key1414, 1), (key1439, -1), (key1414, -1), (key1588, -1), (key1414, -1), (key1588, -1), (key1439, -1), (key1405, -2), (key1582, -2), (key1405, -2), (key1433, 1), (key1405, 1), (key1582, 1), (key1405, 1), (key1582, 1), (key1433, 1)]

theorem rawRowCheck1165 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, 0, -1] GramFunctions.Block1.form5 = rawRow1165 := by decide +kernel

def row1165 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1433, 2), (key1439, -2), (key1477, -2), (key1479, 2)]

theorem rowCheck1165 : row1165 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1165 := by decide +kernel

theorem rowEval1165 (x : Key → ℝ) : Integer.Sparse.eval row1165 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, 0, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1165, Integer.Sparse.eval_collectBalanced, rawRowCheck1165]

def rawRow1166 : Integer.Sparse Key := [(key1688, -1), (key1688, -1), (key1479, -1), (key1479, -1), (key1477, -1), (key1477, -1), (key1688, 2), (key1479, 2), (key1479, 2), (key1588, 1), (key1588, 1), (key1414, 1), (key1414, 1), (key1410, 1), (key1410, 1), (key1588, -1), (key1588, -1), (key1439, -1), (key1439, -1), (key1414, -1), (key1414, -1), (key1582, -2), (key1405, -2), (key1405, -2), (key1582, 1), (key1582, 1), (key1433, 1), (key1433, 1), (key1405, 1), (key1405, 1)]

theorem rawRowCheck1166 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -1, -1] GramFunctions.Block1.form5 = rawRow1166 := by decide +kernel

def row1166 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1433, 2), (key1439, -2), (key1477, -2), (key1479, 2)]

theorem rowCheck1166 : row1166 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1166 := by decide +kernel

theorem rowEval1166 (x : Key → ℝ) : Integer.Sparse.eval row1166 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -1, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1166, Integer.Sparse.eval_collectBalanced, rawRowCheck1166]

def rawRow1167 : Integer.Sparse Key := [(key1479, -1), (key1479, -1), (key1479, -1), (key1479, -1), (key1479, -1), (key1479, -1), (key1477, 2), (key1477, 2), (key1477, 2), (key1439, 1), (key1439, 1), (key1439, 1), (key1439, 1), (key1439, 1), (key1439, 1), (key1410, -1), (key1410, -1), (key1410, -1), (key1410, -1), (key1410, -1), (key1410, -1), (key1433, -2), (key1433, -2), (key1433, -2), (key1405, 1), (key1405, 1), (key1405, 1), (key1405, 1), (key1405, 1), (key1405, 1)]

theorem rawRowCheck1167 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -1, -1] GramFunctions.Block1.form5 = rawRow1167 := by decide +kernel

def row1167 : Integer.Sparse Key := [(key1405, 6), (key1410, -6), (key1433, -6), (key1439, 6), (key1477, 6), (key1479, -6)]

theorem rowCheck1167 : row1167 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1167 := by decide +kernel

theorem rowEval1167 (x : Key → ℝ) : Integer.Sparse.eval row1167 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -1, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1167, Integer.Sparse.eval_collectBalanced, rawRowCheck1167]

def rawRow1168 : Integer.Sparse Key := [(key3081, -2), (key3093, -2), (key3093, -2), (key3083, 2), (key3089, 2), (key3089, 2), (key3086, 2), (key3114, 2), (key3114, 2), (key3089, -6), (key3092, -2), (key3114, -2), (key3114, -2), (key3093, 6)]

theorem rawRowCheck1168 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, -1, 2] GramFunctions.Block1.form6 = rawRow1168 := by decide +kernel

def row1168 : Integer.Sparse Key := [(key3081, -2), (key3083, 2), (key3086, 2), (key3089, -2), (key3092, -2), (key3093, 2)]

theorem rowCheck1168 : row1168 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1168 := by decide +kernel

theorem rowEval1168 (x : Key → ℝ) : Integer.Sparse.eval row1168 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, -1, 2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1168, Integer.Sparse.eval_collectBalanced, rawRowCheck1168]

def rawRow1169 : Integer.Sparse Key := [(key3093, -2), (key3081, -2), (key3093, -2), (key3089, 2), (key3083, 2), (key3089, 2), (key3114, 2), (key3086, 2), (key3114, 2), (key3089, -6), (key3114, -2), (key3092, -2), (key3114, -2), (key3093, 6)]

theorem rawRowCheck1169 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, 2, -1] GramFunctions.Block1.form6 = rawRow1169 := by decide +kernel

def row1169 : Integer.Sparse Key := [(key3081, -2), (key3083, 2), (key3086, 2), (key3089, -2), (key3092, -2), (key3093, 2)]

theorem rowCheck1169 : row1169 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1169 := by decide +kernel

theorem rowEval1169 (x : Key → ℝ) : Integer.Sparse.eval row1169 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, 2, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1169, Integer.Sparse.eval_collectBalanced, rawRowCheck1169]

def rawRow1170 : Integer.Sparse Key := [(key3093, -2), (key3093, -2), (key3081, -2), (key3089, 2), (key3089, 2), (key3083, 2), (key3114, 2), (key3114, 2), (key3086, 2), (key3089, -6), (key3114, -2), (key3114, -2), (key3092, -2), (key3093, 6)]

theorem rawRowCheck1170 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -1, -1] GramFunctions.Block1.form6 = rawRow1170 := by decide +kernel

def row1170 : Integer.Sparse Key := [(key3081, -2), (key3083, 2), (key3086, 2), (key3089, -2), (key3092, -2), (key3093, 2)]

theorem rowCheck1170 : row1170 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1170 := by decide +kernel

theorem rowEval1170 (x : Key → ℝ) : Integer.Sparse.eval row1170 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -1, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1170, Integer.Sparse.eval_collectBalanced, rawRowCheck1170]

def rawRow1171 : Integer.Sparse Key := [(key3083, -2), (key3089, -2), (key3089, -2), (key3081, 2), (key3086, 2), (key3086, 2), (key3089, 2), (key3114, 2), (key3114, 2), (key3086, -6), (key3093, -2), (key3114, -2), (key3114, -2), (key3092, 6)]

theorem rawRowCheck1171 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, -1, 0] GramFunctions.Block1.form6 = rawRow1171 := by decide +kernel

def row1171 : Integer.Sparse Key := [(key3081, 2), (key3083, -2), (key3086, -2), (key3089, -2), (key3092, 6), (key3093, -2)]

theorem rowCheck1171 : row1171 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1171 := by decide +kernel

theorem rowEval1171 (x : Key → ℝ) : Integer.Sparse.eval row1171 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, -1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1171, Integer.Sparse.eval_collectBalanced, rawRowCheck1171]

def rawRow1172 : Integer.Sparse Key := [(key3089, -2), (key3083, -2), (key3089, -2), (key3086, 2), (key3081, 2), (key3086, 2), (key3114, 2), (key3089, 2), (key3114, 2), (key3086, -6), (key3114, -2), (key3093, -2), (key3114, -2), (key3092, 6)]

theorem rawRowCheck1172 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, 0, -1] GramFunctions.Block1.form6 = rawRow1172 := by decide +kernel

def row1172 : Integer.Sparse Key := [(key3081, 2), (key3083, -2), (key3086, -2), (key3089, -2), (key3092, 6), (key3093, -2)]

theorem rowCheck1172 : row1172 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1172 := by decide +kernel

theorem rowEval1172 (x : Key → ℝ) : Integer.Sparse.eval row1172 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, 0, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1172, Integer.Sparse.eval_collectBalanced, rawRowCheck1172]

def rawRow1173 : Integer.Sparse Key := [(key3089, -2), (key3089, -2), (key3083, -2), (key3086, 2), (key3086, 2), (key3081, 2), (key3114, 2), (key3114, 2), (key3089, 2), (key3086, -6), (key3114, -2), (key3114, -2), (key3093, -2), (key3092, 6)]

theorem rawRowCheck1173 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -1, -1] GramFunctions.Block1.form6 = rawRow1173 := by decide +kernel

def row1173 : Integer.Sparse Key := [(key3081, 2), (key3083, -2), (key3086, -2), (key3089, -2), (key3092, 6), (key3093, -2)]

theorem rowCheck1173 : row1173 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1173 := by decide +kernel

theorem rowEval1173 (x : Key → ℝ) : Integer.Sparse.eval row1173 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -1, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1173, Integer.Sparse.eval_collectBalanced, rawRowCheck1173]

def rawRow1174 : Integer.Sparse Key := [(key3086, -2), (key3114, -2), (key3114, -2), (key3089, 2), (key3114, 2), (key3114, 2), (key3081, 2), (key3093, 2), (key3093, 2), (key3093, -6), (key3083, -2), (key3089, -2), (key3089, -2), (key3089, 6)]

theorem rawRowCheck1174 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, -1, 2] GramFunctions.Block1.form6 = rawRow1174 := by decide +kernel

def row1174 : Integer.Sparse Key := [(key3081, 2), (key3083, -2), (key3086, -2), (key3089, 4), (key3093, -2)]

theorem rowCheck1174 : row1174 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1174 := by decide +kernel

theorem rowEval1174 (x : Key → ℝ) : Integer.Sparse.eval row1174 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, -1, 2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1174, Integer.Sparse.eval_collectBalanced, rawRowCheck1174]

def rawRow1175 : Integer.Sparse Key := [(key3114, -2), (key3086, -2), (key3114, -2), (key3114, 2), (key3089, 2), (key3114, 2), (key3093, 2), (key3081, 2), (key3093, 2), (key3093, -6), (key3089, -2), (key3083, -2), (key3089, -2), (key3089, 6)]

theorem rawRowCheck1175 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, 2, -1] GramFunctions.Block1.form6 = rawRow1175 := by decide +kernel

def row1175 : Integer.Sparse Key := [(key3081, 2), (key3083, -2), (key3086, -2), (key3089, 4), (key3093, -2)]

theorem rowCheck1175 : row1175 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1175 := by decide +kernel

theorem rowEval1175 (x : Key → ℝ) : Integer.Sparse.eval row1175 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, 2, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1175, Integer.Sparse.eval_collectBalanced, rawRowCheck1175]

def rawRow1176 : Integer.Sparse Key := [(key3114, -2), (key3114, -2), (key3086, -2), (key3114, 2), (key3114, 2), (key3089, 2), (key3093, 2), (key3093, 2), (key3081, 2), (key3093, -6), (key3089, -2), (key3089, -2), (key3083, -2), (key3089, 6)]

theorem rawRowCheck1176 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -1, -1] GramFunctions.Block1.form6 = rawRow1176 := by decide +kernel

def row1176 : Integer.Sparse Key := [(key3081, 2), (key3083, -2), (key3086, -2), (key3089, 4), (key3093, -2)]

theorem rowCheck1176 : row1176 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1176 := by decide +kernel

theorem rowEval1176 (x : Key → ℝ) : Integer.Sparse.eval row1176 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -1, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1176, Integer.Sparse.eval_collectBalanced, rawRowCheck1176]

def rawRow1177 : Integer.Sparse Key := [(key3089, -2), (key3089, -2), (key3089, -2), (key3086, 2), (key3086, 2), (key3086, 2), (key3093, 2), (key3093, 2), (key3093, 2), (key3081, -6), (key3089, -2), (key3089, -2), (key3089, -2), (key3083, 6)]

theorem rawRowCheck1177 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -1, -1] GramFunctions.Block1.form6 = rawRow1177 := by decide +kernel

def row1177 : Integer.Sparse Key := [(key3081, -6), (key3083, 6), (key3086, 6), (key3089, -12), (key3093, 6)]

theorem rowCheck1177 : row1177 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1177 := by decide +kernel

theorem rowEval1177 (x : Key → ℝ) : Integer.Sparse.eval row1177 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -1, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1177, Integer.Sparse.eval_collectBalanced, rawRowCheck1177]

def rawRow1178 : Integer.Sparse Key := [(key3092, -2), (key3114, -2), (key3114, -2), (key3093, 2), (key3114, 2), (key3114, 2), (key3083, 2), (key3089, 2), (key3089, 2), (key3089, -6), (key3081, -2), (key3086, -2), (key3086, -2), (key3086, 6)]

theorem rawRowCheck1178 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, -1, 0] GramFunctions.Block1.form6 = rawRow1178 := by decide +kernel

def row1178 : Integer.Sparse Key := [(key3081, -2), (key3083, 2), (key3086, 2), (key3089, -2), (key3092, -2), (key3093, 2)]

theorem rowCheck1178 : row1178 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1178 := by decide +kernel

theorem rowEval1178 (x : Key → ℝ) : Integer.Sparse.eval row1178 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, -1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1178, Integer.Sparse.eval_collectBalanced, rawRowCheck1178]

def rawRow1179 : Integer.Sparse Key := [(key3114, -2), (key3092, -2), (key3114, -2), (key3114, 2), (key3093, 2), (key3114, 2), (key3089, 2), (key3083, 2), (key3089, 2), (key3089, -6), (key3086, -2), (key3081, -2), (key3086, -2), (key3086, 6)]

theorem rawRowCheck1179 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, 0, -1] GramFunctions.Block1.form6 = rawRow1179 := by decide +kernel

def row1179 : Integer.Sparse Key := [(key3081, -2), (key3083, 2), (key3086, 2), (key3089, -2), (key3092, -2), (key3093, 2)]

theorem rowCheck1179 : row1179 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1179 := by decide +kernel

theorem rowEval1179 (x : Key → ℝ) : Integer.Sparse.eval row1179 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, 0, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1179, Integer.Sparse.eval_collectBalanced, rawRowCheck1179]

def rawRow1180 : Integer.Sparse Key := [(key3114, -2), (key3114, -2), (key3092, -2), (key3114, 2), (key3114, 2), (key3093, 2), (key3089, 2), (key3089, 2), (key3083, 2), (key3089, -6), (key3086, -2), (key3086, -2), (key3081, -2), (key3086, 6)]

theorem rawRowCheck1180 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -1, -1] GramFunctions.Block1.form6 = rawRow1180 := by decide +kernel

def row1180 : Integer.Sparse Key := [(key3081, -2), (key3083, 2), (key3086, 2), (key3089, -2), (key3092, -2), (key3093, 2)]

theorem rowCheck1180 : row1180 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1180 := by decide +kernel

theorem rowEval1180 (x : Key → ℝ) : Integer.Sparse.eval row1180 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -1, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1180, Integer.Sparse.eval_collectBalanced, rawRowCheck1180]

def rawRow1181 : Integer.Sparse Key := [(key3093, -2), (key3093, -2), (key3093, -2), (key3092, 2), (key3092, 2), (key3092, 2), (key3089, 2), (key3089, 2), (key3089, 2), (key3083, -6), (key3086, -2), (key3086, -2), (key3086, -2), (key3081, 6)]

theorem rawRowCheck1181 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -1, -1] GramFunctions.Block1.form6 = rawRow1181 := by decide +kernel

def row1181 : Integer.Sparse Key := [(key3081, 6), (key3083, -6), (key3086, -6), (key3089, 6), (key3092, 6), (key3093, -6)]

theorem rowCheck1181 : row1181 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1181 := by decide +kernel

theorem rowEval1181 (x : Key → ℝ) : Integer.Sparse.eval row1181 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -1, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1181, Integer.Sparse.eval_collectBalanced, rawRowCheck1181]

def rawRow1182 : Integer.Sparse Key := [(key1424, -2), (key1424, -2), (key1448, -2), (key1455, 1), (key1458, 1), (key1455, 1), (key1467, 1), (key1458, 1), (key1467, 1), (key1573, 2), (key1573, 2), (key1597, 2), (key1655, -1), (key1660, -1), (key1655, -1), (key1668, -1), (key1660, -1), (key1668, -1), (key1788, -1), (key1791, -1), (key1788, -1), (key1799, -1), (key1791, -1), (key1799, -1), (key1813, 1), (key1818, 1), (key1813, 1), (key1826, 1), (key1818, 1), (key1826, 1)]

theorem rawRowCheck1182 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block1.form0 = rawRow1182 := by decide +kernel

def row1182 : Integer.Sparse Key := [(key1424, -4), (key1448, -2), (key1455, 2), (key1458, 2), (key1467, 2), (key1573, 4), (key1597, 2), (key1655, -2), (key1660, -2), (key1668, -2), (key1788, -2), (key1791, -2), (key1799, -2), (key1813, 2), (key1818, 2), (key1826, 2)]

theorem rowCheck1182 : row1182 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1182 := by decide +kernel

theorem rowEval1182 (x : Key → ℝ) : Integer.Sparse.eval row1182 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck1182, Integer.Sparse.eval_collectBalanced, rawRowCheck1182]

def rawRow1183 : Integer.Sparse Key := [(key1424, -2), (key1448, -2), (key1424, -2), (key1458, 1), (key1455, 1), (key1467, 1), (key1455, 1), (key1467, 1), (key1458, 1), (key1573, 2), (key1597, 2), (key1573, 2), (key1660, -1), (key1655, -1), (key1668, -1), (key1655, -1), (key1668, -1), (key1660, -1), (key1791, -1), (key1788, -1), (key1799, -1), (key1788, -1), (key1799, -1), (key1791, -1), (key1818, 1), (key1813, 1), (key1826, 1), (key1813, 1), (key1826, 1), (key1818, 1)]

theorem rawRowCheck1183 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block1.form0 = rawRow1183 := by decide +kernel

def row1183 : Integer.Sparse Key := [(key1424, -4), (key1448, -2), (key1455, 2), (key1458, 2), (key1467, 2), (key1573, 4), (key1597, 2), (key1655, -2), (key1660, -2), (key1668, -2), (key1788, -2), (key1791, -2), (key1799, -2), (key1813, 2), (key1818, 2), (key1826, 2)]

theorem rowCheck1183 : row1183 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1183 := by decide +kernel

theorem rowEval1183 (x : Key → ℝ) : Integer.Sparse.eval row1183 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1183, Integer.Sparse.eval_collectBalanced, rawRowCheck1183]

def rawRow1184 : Integer.Sparse Key := [(key1448, -2), (key1424, -2), (key1424, -2), (key1467, 1), (key1467, 1), (key1458, 1), (key1458, 1), (key1455, 1), (key1455, 1), (key1597, 2), (key1573, 2), (key1573, 2), (key1668, -1), (key1668, -1), (key1660, -1), (key1660, -1), (key1655, -1), (key1655, -1), (key1799, -1), (key1799, -1), (key1791, -1), (key1791, -1), (key1788, -1), (key1788, -1), (key1826, 1), (key1826, 1), (key1818, 1), (key1818, 1), (key1813, 1), (key1813, 1)]

theorem rawRowCheck1184 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block1.form0 = rawRow1184 := by decide +kernel

def row1184 : Integer.Sparse Key := [(key1424, -4), (key1448, -2), (key1455, 2), (key1458, 2), (key1467, 2), (key1573, 4), (key1597, 2), (key1655, -2), (key1660, -2), (key1668, -2), (key1788, -2), (key1791, -2), (key1799, -2), (key1813, 2), (key1818, 2), (key1826, 2)]

theorem rowCheck1184 : row1184 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1184 := by decide +kernel

theorem rowEval1184 (x : Key → ℝ) : Integer.Sparse.eval row1184 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1184, Integer.Sparse.eval_collectBalanced, rawRowCheck1184]

def rawRow1185 : Integer.Sparse Key := [(key1391, -2), (key1455, -2), (key1467, -2), (key1391, 1), (key1398, 1), (key1424, 1), (key1448, 1), (key1458, 1), (key1467, 1), (key1546, 2), (key1655, 2), (key1668, 2), (key1546, -1), (key1560, -1), (key1573, -1), (key1597, -1), (key1660, -1), (key1668, -1), (key1772, -1), (key1775, -1), (key1813, -1), (key1826, -1), (key1840, -1), (key1845, -1), (key1772, 1), (key1781, 1), (key1788, 1), (key1799, 1), (key1842, 1), (key1845, 1)]

theorem rawRowCheck1185 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block1.form0 = rawRow1185 := by decide +kernel

def row1185 : Integer.Sparse Key := [(key1391, -1), (key1398, 1), (key1424, 1), (key1448, 1), (key1455, -2), (key1458, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, -1), (key1597, -1), (key1655, 2), (key1660, -1), (key1668, 1), (key1775, -1), (key1781, 1), (key1788, 1), (key1799, 1), (key1813, -1), (key1826, -1), (key1840, -1), (key1842, 1)]

theorem rowCheck1185 : row1185 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1185 := by decide +kernel

theorem rowEval1185 (x : Key → ℝ) : Integer.Sparse.eval row1185 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck1185, Integer.Sparse.eval_collectBalanced, rawRowCheck1185]

def rawRow1186 : Integer.Sparse Key := [(key1391, -2), (key1467, -2), (key1455, -2), (key1398, 1), (key1391, 1), (key1448, 1), (key1424, 1), (key1467, 1), (key1458, 1), (key1546, 2), (key1668, 2), (key1655, 2), (key1560, -1), (key1546, -1), (key1597, -1), (key1573, -1), (key1668, -1), (key1660, -1), (key1775, -1), (key1772, -1), (key1826, -1), (key1813, -1), (key1845, -1), (key1840, -1), (key1781, 1), (key1772, 1), (key1799, 1), (key1788, 1), (key1845, 1), (key1842, 1)]

theorem rawRowCheck1186 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block1.form0 = rawRow1186 := by decide +kernel

def row1186 : Integer.Sparse Key := [(key1391, -1), (key1398, 1), (key1424, 1), (key1448, 1), (key1455, -2), (key1458, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, -1), (key1597, -1), (key1655, 2), (key1660, -1), (key1668, 1), (key1775, -1), (key1781, 1), (key1788, 1), (key1799, 1), (key1813, -1), (key1826, -1), (key1840, -1), (key1842, 1)]

theorem rowCheck1186 : row1186 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1186 := by decide +kernel

theorem rowEval1186 (x : Key → ℝ) : Integer.Sparse.eval row1186 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1186, Integer.Sparse.eval_collectBalanced, rawRowCheck1186]

def rawRow1187 : Integer.Sparse Key := [(key1455, -2), (key1391, -2), (key1467, -2), (key1424, 1), (key1458, 1), (key1391, 1), (key1467, 1), (key1398, 1), (key1448, 1), (key1655, 2), (key1546, 2), (key1668, 2), (key1573, -1), (key1660, -1), (key1546, -1), (key1668, -1), (key1560, -1), (key1597, -1), (key1813, -1), (key1840, -1), (key1772, -1), (key1845, -1), (key1775, -1), (key1826, -1), (key1788, 1), (key1842, 1), (key1772, 1), (key1845, 1), (key1781, 1), (key1799, 1)]

theorem rawRowCheck1187 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block1.form0 = rawRow1187 := by decide +kernel

def row1187 : Integer.Sparse Key := [(key1391, -1), (key1398, 1), (key1424, 1), (key1448, 1), (key1455, -2), (key1458, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, -1), (key1597, -1), (key1655, 2), (key1660, -1), (key1668, 1), (key1775, -1), (key1781, 1), (key1788, 1), (key1799, 1), (key1813, -1), (key1826, -1), (key1840, -1), (key1842, 1)]

theorem rowCheck1187 : row1187 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1187 := by decide +kernel

theorem rowEval1187 (x : Key → ℝ) : Integer.Sparse.eval row1187 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck1187, Integer.Sparse.eval_collectBalanced, rawRowCheck1187]

def rawRow1188 : Integer.Sparse Key := [(key1455, -2), (key1467, -2), (key1391, -2), (key1458, 1), (key1424, 1), (key1467, 1), (key1391, 1), (key1448, 1), (key1398, 1), (key1655, 2), (key1668, 2), (key1546, 2), (key1660, -1), (key1573, -1), (key1668, -1), (key1546, -1), (key1597, -1), (key1560, -1), (key1840, -1), (key1813, -1), (key1845, -1), (key1772, -1), (key1826, -1), (key1775, -1), (key1842, 1), (key1788, 1), (key1845, 1), (key1772, 1), (key1799, 1), (key1781, 1)]

theorem rawRowCheck1188 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block1.form0 = rawRow1188 := by decide +kernel

def row1188 : Integer.Sparse Key := [(key1391, -1), (key1398, 1), (key1424, 1), (key1448, 1), (key1455, -2), (key1458, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, -1), (key1597, -1), (key1655, 2), (key1660, -1), (key1668, 1), (key1775, -1), (key1781, 1), (key1788, 1), (key1799, 1), (key1813, -1), (key1826, -1), (key1840, -1), (key1842, 1)]

theorem rowCheck1188 : row1188 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1188 := by decide +kernel

theorem rowEval1188 (x : Key → ℝ) : Integer.Sparse.eval row1188 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1188, Integer.Sparse.eval_collectBalanced, rawRowCheck1188]

def rawRow1189 : Integer.Sparse Key := [(key1467, -2), (key1391, -2), (key1455, -2), (key1448, 1), (key1467, 1), (key1398, 1), (key1458, 1), (key1391, 1), (key1424, 1), (key1668, 2), (key1546, 2), (key1655, 2), (key1597, -1), (key1668, -1), (key1560, -1), (key1660, -1), (key1546, -1), (key1573, -1), (key1826, -1), (key1845, -1), (key1775, -1), (key1840, -1), (key1772, -1), (key1813, -1), (key1799, 1), (key1845, 1), (key1781, 1), (key1842, 1), (key1772, 1), (key1788, 1)]

theorem rawRowCheck1189 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block1.form0 = rawRow1189 := by decide +kernel

def row1189 : Integer.Sparse Key := [(key1391, -1), (key1398, 1), (key1424, 1), (key1448, 1), (key1455, -2), (key1458, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, -1), (key1597, -1), (key1655, 2), (key1660, -1), (key1668, 1), (key1775, -1), (key1781, 1), (key1788, 1), (key1799, 1), (key1813, -1), (key1826, -1), (key1840, -1), (key1842, 1)]

theorem rowCheck1189 : row1189 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1189 := by decide +kernel

theorem rowEval1189 (x : Key → ℝ) : Integer.Sparse.eval row1189 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1189, Integer.Sparse.eval_collectBalanced, rawRowCheck1189]

def rawRow1190 : Integer.Sparse Key := [(key1467, -2), (key1455, -2), (key1391, -2), (key1467, 1), (key1448, 1), (key1458, 1), (key1398, 1), (key1424, 1), (key1391, 1), (key1668, 2), (key1655, 2), (key1546, 2), (key1668, -1), (key1597, -1), (key1660, -1), (key1560, -1), (key1573, -1), (key1546, -1), (key1845, -1), (key1826, -1), (key1840, -1), (key1775, -1), (key1813, -1), (key1772, -1), (key1845, 1), (key1799, 1), (key1842, 1), (key1781, 1), (key1788, 1), (key1772, 1)]

theorem rawRowCheck1190 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block1.form0 = rawRow1190 := by decide +kernel

def row1190 : Integer.Sparse Key := [(key1391, -1), (key1398, 1), (key1424, 1), (key1448, 1), (key1455, -2), (key1458, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, -1), (key1597, -1), (key1655, 2), (key1660, -1), (key1668, 1), (key1775, -1), (key1781, 1), (key1788, 1), (key1799, 1), (key1813, -1), (key1826, -1), (key1840, -1), (key1842, 1)]

theorem rowCheck1190 : row1190 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1190 := by decide +kernel

theorem rowEval1190 (x : Key → ℝ) : Integer.Sparse.eval row1190 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1190, Integer.Sparse.eval_collectBalanced, rawRowCheck1190]

def rawRow1191 : Integer.Sparse Key := [(key1573, -2), (key1573, -2), (key1597, -2), (key1788, 1), (key1791, 1), (key1788, 1), (key1799, 1), (key1791, 1), (key1799, 1), (key1424, 2), (key1424, 2), (key1448, 2), (key1813, -1), (key1818, -1), (key1813, -1), (key1826, -1), (key1818, -1), (key1826, -1), (key1455, -1), (key1458, -1), (key1455, -1), (key1467, -1), (key1458, -1), (key1467, -1), (key1655, 1), (key1660, 1), (key1655, 1), (key1668, 1), (key1660, 1), (key1668, 1)]

theorem rawRowCheck1191 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block1.form0 = rawRow1191 := by decide +kernel

def row1191 : Integer.Sparse Key := [(key1424, 4), (key1448, 2), (key1455, -2), (key1458, -2), (key1467, -2), (key1573, -4), (key1597, -2), (key1655, 2), (key1660, 2), (key1668, 2), (key1788, 2), (key1791, 2), (key1799, 2), (key1813, -2), (key1818, -2), (key1826, -2)]

theorem rowCheck1191 : row1191 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1191 := by decide +kernel

theorem rowEval1191 (x : Key → ℝ) : Integer.Sparse.eval row1191 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck1191, Integer.Sparse.eval_collectBalanced, rawRowCheck1191]

def rawRow1192 : Integer.Sparse Key := [(key1573, -2), (key1597, -2), (key1573, -2), (key1791, 1), (key1788, 1), (key1799, 1), (key1788, 1), (key1799, 1), (key1791, 1), (key1424, 2), (key1448, 2), (key1424, 2), (key1818, -1), (key1813, -1), (key1826, -1), (key1813, -1), (key1826, -1), (key1818, -1), (key1458, -1), (key1455, -1), (key1467, -1), (key1455, -1), (key1467, -1), (key1458, -1), (key1660, 1), (key1655, 1), (key1668, 1), (key1655, 1), (key1668, 1), (key1660, 1)]

theorem rawRowCheck1192 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block1.form0 = rawRow1192 := by decide +kernel

def row1192 : Integer.Sparse Key := [(key1424, 4), (key1448, 2), (key1455, -2), (key1458, -2), (key1467, -2), (key1573, -4), (key1597, -2), (key1655, 2), (key1660, 2), (key1668, 2), (key1788, 2), (key1791, 2), (key1799, 2), (key1813, -2), (key1818, -2), (key1826, -2)]

theorem rowCheck1192 : row1192 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1192 := by decide +kernel

theorem rowEval1192 (x : Key → ℝ) : Integer.Sparse.eval row1192 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1192, Integer.Sparse.eval_collectBalanced, rawRowCheck1192]

def rawRow1193 : Integer.Sparse Key := [(key1597, -2), (key1573, -2), (key1573, -2), (key1799, 1), (key1799, 1), (key1791, 1), (key1791, 1), (key1788, 1), (key1788, 1), (key1448, 2), (key1424, 2), (key1424, 2), (key1826, -1), (key1826, -1), (key1818, -1), (key1818, -1), (key1813, -1), (key1813, -1), (key1467, -1), (key1467, -1), (key1458, -1), (key1458, -1), (key1455, -1), (key1455, -1), (key1668, 1), (key1668, 1), (key1660, 1), (key1660, 1), (key1655, 1), (key1655, 1)]

theorem rawRowCheck1193 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block1.form0 = rawRow1193 := by decide +kernel

def row1193 : Integer.Sparse Key := [(key1424, 4), (key1448, 2), (key1455, -2), (key1458, -2), (key1467, -2), (key1573, -4), (key1597, -2), (key1655, 2), (key1660, 2), (key1668, 2), (key1788, 2), (key1791, 2), (key1799, 2), (key1813, -2), (key1818, -2), (key1826, -2)]

theorem rowCheck1193 : row1193 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1193 := by decide +kernel

theorem rowEval1193 (x : Key → ℝ) : Integer.Sparse.eval row1193 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1193, Integer.Sparse.eval_collectBalanced, rawRowCheck1193]

def rawRow1194 : Integer.Sparse Key := [(key1546, -2), (key1655, -2), (key1668, -2), (key1772, 1), (key1775, 1), (key1813, 1), (key1826, 1), (key1840, 1), (key1845, 1), (key1391, 2), (key1455, 2), (key1467, 2), (key1772, -1), (key1781, -1), (key1788, -1), (key1799, -1), (key1842, -1), (key1845, -1), (key1391, -1), (key1398, -1), (key1424, -1), (key1448, -1), (key1458, -1), (key1467, -1), (key1546, 1), (key1560, 1), (key1573, 1), (key1597, 1), (key1660, 1), (key1668, 1)]

theorem rawRowCheck1194 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block1.form0 = rawRow1194 := by decide +kernel

def row1194 : Integer.Sparse Key := [(key1391, 1), (key1398, -1), (key1424, -1), (key1448, -1), (key1455, 2), (key1458, -1), (key1467, 1), (key1546, -1), (key1560, 1), (key1573, 1), (key1597, 1), (key1655, -2), (key1660, 1), (key1668, -1), (key1775, 1), (key1781, -1), (key1788, -1), (key1799, -1), (key1813, 1), (key1826, 1), (key1840, 1), (key1842, -1)]

theorem rowCheck1194 : row1194 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1194 := by decide +kernel

theorem rowEval1194 (x : Key → ℝ) : Integer.Sparse.eval row1194 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck1194, Integer.Sparse.eval_collectBalanced, rawRowCheck1194]

def rawRow1195 : Integer.Sparse Key := [(key1546, -2), (key1668, -2), (key1655, -2), (key1775, 1), (key1772, 1), (key1826, 1), (key1813, 1), (key1845, 1), (key1840, 1), (key1391, 2), (key1467, 2), (key1455, 2), (key1781, -1), (key1772, -1), (key1799, -1), (key1788, -1), (key1845, -1), (key1842, -1), (key1398, -1), (key1391, -1), (key1448, -1), (key1424, -1), (key1467, -1), (key1458, -1), (key1560, 1), (key1546, 1), (key1597, 1), (key1573, 1), (key1668, 1), (key1660, 1)]

theorem rawRowCheck1195 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block1.form0 = rawRow1195 := by decide +kernel

def row1195 : Integer.Sparse Key := [(key1391, 1), (key1398, -1), (key1424, -1), (key1448, -1), (key1455, 2), (key1458, -1), (key1467, 1), (key1546, -1), (key1560, 1), (key1573, 1), (key1597, 1), (key1655, -2), (key1660, 1), (key1668, -1), (key1775, 1), (key1781, -1), (key1788, -1), (key1799, -1), (key1813, 1), (key1826, 1), (key1840, 1), (key1842, -1)]

theorem rowCheck1195 : row1195 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1195 := by decide +kernel

theorem rowEval1195 (x : Key → ℝ) : Integer.Sparse.eval row1195 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1195, Integer.Sparse.eval_collectBalanced, rawRowCheck1195]

def rawRow1196 : Integer.Sparse Key := [(key1655, -2), (key1546, -2), (key1668, -2), (key1813, 1), (key1840, 1), (key1772, 1), (key1845, 1), (key1775, 1), (key1826, 1), (key1455, 2), (key1391, 2), (key1467, 2), (key1788, -1), (key1842, -1), (key1772, -1), (key1845, -1), (key1781, -1), (key1799, -1), (key1424, -1), (key1458, -1), (key1391, -1), (key1467, -1), (key1398, -1), (key1448, -1), (key1573, 1), (key1660, 1), (key1546, 1), (key1668, 1), (key1560, 1), (key1597, 1)]

theorem rawRowCheck1196 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block1.form0 = rawRow1196 := by decide +kernel

def row1196 : Integer.Sparse Key := [(key1391, 1), (key1398, -1), (key1424, -1), (key1448, -1), (key1455, 2), (key1458, -1), (key1467, 1), (key1546, -1), (key1560, 1), (key1573, 1), (key1597, 1), (key1655, -2), (key1660, 1), (key1668, -1), (key1775, 1), (key1781, -1), (key1788, -1), (key1799, -1), (key1813, 1), (key1826, 1), (key1840, 1), (key1842, -1)]

theorem rowCheck1196 : row1196 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1196 := by decide +kernel

theorem rowEval1196 (x : Key → ℝ) : Integer.Sparse.eval row1196 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck1196, Integer.Sparse.eval_collectBalanced, rawRowCheck1196]

def rawRow1197 : Integer.Sparse Key := [(key1655, -2), (key1668, -2), (key1546, -2), (key1840, 1), (key1813, 1), (key1845, 1), (key1772, 1), (key1826, 1), (key1775, 1), (key1455, 2), (key1467, 2), (key1391, 2), (key1842, -1), (key1788, -1), (key1845, -1), (key1772, -1), (key1799, -1), (key1781, -1), (key1458, -1), (key1424, -1), (key1467, -1), (key1391, -1), (key1448, -1), (key1398, -1), (key1660, 1), (key1573, 1), (key1668, 1), (key1546, 1), (key1597, 1), (key1560, 1)]

theorem rawRowCheck1197 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block1.form0 = rawRow1197 := by decide +kernel

def row1197 : Integer.Sparse Key := [(key1391, 1), (key1398, -1), (key1424, -1), (key1448, -1), (key1455, 2), (key1458, -1), (key1467, 1), (key1546, -1), (key1560, 1), (key1573, 1), (key1597, 1), (key1655, -2), (key1660, 1), (key1668, -1), (key1775, 1), (key1781, -1), (key1788, -1), (key1799, -1), (key1813, 1), (key1826, 1), (key1840, 1), (key1842, -1)]

theorem rowCheck1197 : row1197 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1197 := by decide +kernel

theorem rowEval1197 (x : Key → ℝ) : Integer.Sparse.eval row1197 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1197, Integer.Sparse.eval_collectBalanced, rawRowCheck1197]

def rawRow1198 : Integer.Sparse Key := [(key1668, -2), (key1546, -2), (key1655, -2), (key1826, 1), (key1845, 1), (key1775, 1), (key1840, 1), (key1772, 1), (key1813, 1), (key1467, 2), (key1391, 2), (key1455, 2), (key1799, -1), (key1845, -1), (key1781, -1), (key1842, -1), (key1772, -1), (key1788, -1), (key1448, -1), (key1467, -1), (key1398, -1), (key1458, -1), (key1391, -1), (key1424, -1), (key1597, 1), (key1668, 1), (key1560, 1), (key1660, 1), (key1546, 1), (key1573, 1)]

theorem rawRowCheck1198 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block1.form0 = rawRow1198 := by decide +kernel

def row1198 : Integer.Sparse Key := [(key1391, 1), (key1398, -1), (key1424, -1), (key1448, -1), (key1455, 2), (key1458, -1), (key1467, 1), (key1546, -1), (key1560, 1), (key1573, 1), (key1597, 1), (key1655, -2), (key1660, 1), (key1668, -1), (key1775, 1), (key1781, -1), (key1788, -1), (key1799, -1), (key1813, 1), (key1826, 1), (key1840, 1), (key1842, -1)]

theorem rowCheck1198 : row1198 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1198 := by decide +kernel

theorem rowEval1198 (x : Key → ℝ) : Integer.Sparse.eval row1198 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1198, Integer.Sparse.eval_collectBalanced, rawRowCheck1198]

def rawRow1199 : Integer.Sparse Key := [(key1668, -2), (key1655, -2), (key1546, -2), (key1845, 1), (key1826, 1), (key1840, 1), (key1775, 1), (key1813, 1), (key1772, 1), (key1467, 2), (key1455, 2), (key1391, 2), (key1845, -1), (key1799, -1), (key1842, -1), (key1781, -1), (key1788, -1), (key1772, -1), (key1467, -1), (key1448, -1), (key1458, -1), (key1398, -1), (key1424, -1), (key1391, -1), (key1668, 1), (key1597, 1), (key1660, 1), (key1560, 1), (key1573, 1), (key1546, 1)]

theorem rawRowCheck1199 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block1.form0 = rawRow1199 := by decide +kernel

def row1199 : Integer.Sparse Key := [(key1391, 1), (key1398, -1), (key1424, -1), (key1448, -1), (key1455, 2), (key1458, -1), (key1467, 1), (key1546, -1), (key1560, 1), (key1573, 1), (key1597, 1), (key1655, -2), (key1660, 1), (key1668, -1), (key1775, 1), (key1781, -1), (key1788, -1), (key1799, -1), (key1813, 1), (key1826, 1), (key1840, 1), (key1842, -1)]

theorem rowCheck1199 : row1199 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1199 := by decide +kernel

theorem rowEval1199 (x : Key → ℝ) : Integer.Sparse.eval row1199 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1199, Integer.Sparse.eval_collectBalanced, rawRowCheck1199]

def rawRow1200 : Integer.Sparse Key := [(key238, -6), (key250, 2), (key250, 2), (key259, 2), (key304, 6), (key318, -2), (key318, -2), (key327, -2), (key387, -2), (key387, -2), (key396, -2), (key408, 2), (key408, 2), (key417, 2)]

theorem rawRowCheck1200 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block1.form1 = rawRow1200 := by decide +kernel

def row1200 : Integer.Sparse Key := [(key238, -6), (key250, 4), (key259, 2), (key304, 6), (key318, -4), (key327, -2), (key387, -4), (key396, -2), (key408, 4), (key417, 2)]

theorem rowCheck1200 : row1200 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1200 := by decide +kernel

theorem rowEval1200 (x : Key → ℝ) : Integer.Sparse.eval row1200 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck1200, Integer.Sparse.eval_collectBalanced, rawRowCheck1200]

def rawRow1201 : Integer.Sparse Key := [(key238, -6), (key250, 2), (key259, 2), (key250, 2), (key304, 6), (key318, -2), (key327, -2), (key318, -2), (key387, -2), (key396, -2), (key387, -2), (key408, 2), (key417, 2), (key408, 2)]

theorem rawRowCheck1201 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block1.form1 = rawRow1201 := by decide +kernel

def row1201 : Integer.Sparse Key := [(key238, -6), (key250, 4), (key259, 2), (key304, 6), (key318, -4), (key327, -2), (key387, -4), (key396, -2), (key408, 4), (key417, 2)]

theorem rowCheck1201 : row1201 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1201 := by decide +kernel

theorem rowEval1201 (x : Key → ℝ) : Integer.Sparse.eval row1201 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1201, Integer.Sparse.eval_collectBalanced, rawRowCheck1201]

def rawRow1202 : Integer.Sparse Key := [(key238, -6), (key259, 2), (key250, 2), (key250, 2), (key304, 6), (key327, -2), (key318, -2), (key318, -2), (key396, -2), (key387, -2), (key387, -2), (key417, 2), (key408, 2), (key408, 2)]

theorem rawRowCheck1202 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block1.form1 = rawRow1202 := by decide +kernel

def row1202 : Integer.Sparse Key := [(key238, -6), (key250, 4), (key259, 2), (key304, 6), (key318, -4), (key327, -2), (key387, -4), (key396, -2), (key408, 4), (key417, 2)]

theorem rowCheck1202 : row1202 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1202 := by decide +kernel

theorem rowEval1202 (x : Key → ℝ) : Integer.Sparse.eval row1202 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1202, Integer.Sparse.eval_collectBalanced, rawRowCheck1202]

def rawRow1203 : Integer.Sparse Key := [(key250, -6), (key238, 2), (key250, 2), (key259, 2), (key318, 6), (key304, -2), (key318, -2), (key327, -2), (key408, -2), (key437, -2), (key441, -2), (key387, 2), (key437, 2), (key449, 2)]

theorem rawRowCheck1203 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block1.form1 = rawRow1203 := by decide +kernel

def row1203 : Integer.Sparse Key := [(key238, 2), (key250, -4), (key259, 2), (key304, -2), (key318, 4), (key327, -2), (key387, 2), (key408, -2), (key441, -2), (key449, 2)]

theorem rowCheck1203 : row1203 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1203 := by decide +kernel

theorem rowEval1203 (x : Key → ℝ) : Integer.Sparse.eval row1203 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck1203, Integer.Sparse.eval_collectBalanced, rawRowCheck1203]

def rawRow1204 : Integer.Sparse Key := [(key250, -6), (key238, 2), (key259, 2), (key250, 2), (key318, 6), (key304, -2), (key327, -2), (key318, -2), (key408, -2), (key441, -2), (key437, -2), (key387, 2), (key449, 2), (key437, 2)]

theorem rawRowCheck1204 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block1.form1 = rawRow1204 := by decide +kernel

def row1204 : Integer.Sparse Key := [(key238, 2), (key250, -4), (key259, 2), (key304, -2), (key318, 4), (key327, -2), (key387, 2), (key408, -2), (key441, -2), (key449, 2)]

theorem rowCheck1204 : row1204 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1204 := by decide +kernel

theorem rowEval1204 (x : Key → ℝ) : Integer.Sparse.eval row1204 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1204, Integer.Sparse.eval_collectBalanced, rawRowCheck1204]

def rawRow1205 : Integer.Sparse Key := [(key250, -6), (key250, 2), (key238, 2), (key259, 2), (key318, 6), (key318, -2), (key304, -2), (key327, -2), (key437, -2), (key408, -2), (key441, -2), (key437, 2), (key387, 2), (key449, 2)]

theorem rawRowCheck1205 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block1.form1 = rawRow1205 := by decide +kernel

def row1205 : Integer.Sparse Key := [(key238, 2), (key250, -4), (key259, 2), (key304, -2), (key318, 4), (key327, -2), (key387, 2), (key408, -2), (key441, -2), (key449, 2)]

theorem rowCheck1205 : row1205 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1205 := by decide +kernel

theorem rowEval1205 (x : Key → ℝ) : Integer.Sparse.eval row1205 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck1205, Integer.Sparse.eval_collectBalanced, rawRowCheck1205]

def rawRow1206 : Integer.Sparse Key := [(key250, -6), (key250, 2), (key259, 2), (key238, 2), (key318, 6), (key318, -2), (key327, -2), (key304, -2), (key437, -2), (key441, -2), (key408, -2), (key437, 2), (key449, 2), (key387, 2)]

theorem rawRowCheck1206 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block1.form1 = rawRow1206 := by decide +kernel

def row1206 : Integer.Sparse Key := [(key238, 2), (key250, -4), (key259, 2), (key304, -2), (key318, 4), (key327, -2), (key387, 2), (key408, -2), (key441, -2), (key449, 2)]

theorem rowCheck1206 : row1206 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1206 := by decide +kernel

theorem rowEval1206 (x : Key → ℝ) : Integer.Sparse.eval row1206 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1206, Integer.Sparse.eval_collectBalanced, rawRowCheck1206]

def rawRow1207 : Integer.Sparse Key := [(key250, -6), (key259, 2), (key238, 2), (key250, 2), (key318, 6), (key327, -2), (key304, -2), (key318, -2), (key441, -2), (key408, -2), (key437, -2), (key449, 2), (key387, 2), (key437, 2)]

theorem rawRowCheck1207 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block1.form1 = rawRow1207 := by decide +kernel

def row1207 : Integer.Sparse Key := [(key238, 2), (key250, -4), (key259, 2), (key304, -2), (key318, 4), (key327, -2), (key387, 2), (key408, -2), (key441, -2), (key449, 2)]

theorem rowCheck1207 : row1207 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1207 := by decide +kernel

theorem rowEval1207 (x : Key → ℝ) : Integer.Sparse.eval row1207 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1207, Integer.Sparse.eval_collectBalanced, rawRowCheck1207]

def rawRow1208 : Integer.Sparse Key := [(key250, -6), (key259, 2), (key250, 2), (key238, 2), (key318, 6), (key327, -2), (key318, -2), (key304, -2), (key441, -2), (key437, -2), (key408, -2), (key449, 2), (key437, 2), (key387, 2)]

theorem rawRowCheck1208 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block1.form1 = rawRow1208 := by decide +kernel

def row1208 : Integer.Sparse Key := [(key238, 2), (key250, -4), (key259, 2), (key304, -2), (key318, 4), (key327, -2), (key387, 2), (key408, -2), (key441, -2), (key449, 2)]

theorem rowCheck1208 : row1208 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1208 := by decide +kernel

theorem rowEval1208 (x : Key → ℝ) : Integer.Sparse.eval row1208 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1208, Integer.Sparse.eval_collectBalanced, rawRowCheck1208]

def rawRow1209 : Integer.Sparse Key := [(key304, -6), (key387, 2), (key387, 2), (key396, 2), (key238, 6), (key408, -2), (key408, -2), (key417, -2), (key250, -2), (key250, -2), (key259, -2), (key318, 2), (key318, 2), (key327, 2)]

theorem rawRowCheck1209 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block1.form1 = rawRow1209 := by decide +kernel

def row1209 : Integer.Sparse Key := [(key238, 6), (key250, -4), (key259, -2), (key304, -6), (key318, 4), (key327, 2), (key387, 4), (key396, 2), (key408, -4), (key417, -2)]

theorem rowCheck1209 : row1209 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1209 := by decide +kernel

theorem rowEval1209 (x : Key → ℝ) : Integer.Sparse.eval row1209 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck1209, Integer.Sparse.eval_collectBalanced, rawRowCheck1209]

def rawRow1210 : Integer.Sparse Key := [(key304, -6), (key387, 2), (key396, 2), (key387, 2), (key238, 6), (key408, -2), (key417, -2), (key408, -2), (key250, -2), (key259, -2), (key250, -2), (key318, 2), (key327, 2), (key318, 2)]

theorem rawRowCheck1210 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block1.form1 = rawRow1210 := by decide +kernel

def row1210 : Integer.Sparse Key := [(key238, 6), (key250, -4), (key259, -2), (key304, -6), (key318, 4), (key327, 2), (key387, 4), (key396, 2), (key408, -4), (key417, -2)]

theorem rowCheck1210 : row1210 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1210 := by decide +kernel

theorem rowEval1210 (x : Key → ℝ) : Integer.Sparse.eval row1210 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1210, Integer.Sparse.eval_collectBalanced, rawRowCheck1210]

def rawRow1211 : Integer.Sparse Key := [(key304, -6), (key396, 2), (key387, 2), (key387, 2), (key238, 6), (key417, -2), (key408, -2), (key408, -2), (key259, -2), (key250, -2), (key250, -2), (key327, 2), (key318, 2), (key318, 2)]

theorem rawRowCheck1211 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block1.form1 = rawRow1211 := by decide +kernel

def row1211 : Integer.Sparse Key := [(key238, 6), (key250, -4), (key259, -2), (key304, -6), (key318, 4), (key327, 2), (key387, 4), (key396, 2), (key408, -4), (key417, -2)]

theorem rowCheck1211 : row1211 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1211 := by decide +kernel

theorem rowEval1211 (x : Key → ℝ) : Integer.Sparse.eval row1211 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1211, Integer.Sparse.eval_collectBalanced, rawRowCheck1211]

def rawRow1212 : Integer.Sparse Key := [(key318, -6), (key408, 2), (key437, 2), (key441, 2), (key250, 6), (key387, -2), (key437, -2), (key449, -2), (key238, -2), (key250, -2), (key259, -2), (key304, 2), (key318, 2), (key327, 2)]

theorem rawRowCheck1212 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block1.form1 = rawRow1212 := by decide +kernel

def row1212 : Integer.Sparse Key := [(key238, -2), (key250, 4), (key259, -2), (key304, 2), (key318, -4), (key327, 2), (key387, -2), (key408, 2), (key441, 2), (key449, -2)]

theorem rowCheck1212 : row1212 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1212 := by decide +kernel

theorem rowEval1212 (x : Key → ℝ) : Integer.Sparse.eval row1212 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck1212, Integer.Sparse.eval_collectBalanced, rawRowCheck1212]

def rawRow1213 : Integer.Sparse Key := [(key318, -6), (key408, 2), (key441, 2), (key437, 2), (key250, 6), (key387, -2), (key449, -2), (key437, -2), (key238, -2), (key259, -2), (key250, -2), (key304, 2), (key327, 2), (key318, 2)]

theorem rawRowCheck1213 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block1.form1 = rawRow1213 := by decide +kernel

def row1213 : Integer.Sparse Key := [(key238, -2), (key250, 4), (key259, -2), (key304, 2), (key318, -4), (key327, 2), (key387, -2), (key408, 2), (key441, 2), (key449, -2)]

theorem rowCheck1213 : row1213 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1213 := by decide +kernel

theorem rowEval1213 (x : Key → ℝ) : Integer.Sparse.eval row1213 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1213, Integer.Sparse.eval_collectBalanced, rawRowCheck1213]

def rawRow1214 : Integer.Sparse Key := [(key318, -6), (key437, 2), (key408, 2), (key441, 2), (key250, 6), (key437, -2), (key387, -2), (key449, -2), (key250, -2), (key238, -2), (key259, -2), (key318, 2), (key304, 2), (key327, 2)]

theorem rawRowCheck1214 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block1.form1 = rawRow1214 := by decide +kernel

def row1214 : Integer.Sparse Key := [(key238, -2), (key250, 4), (key259, -2), (key304, 2), (key318, -4), (key327, 2), (key387, -2), (key408, 2), (key441, 2), (key449, -2)]

theorem rowCheck1214 : row1214 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1214 := by decide +kernel

theorem rowEval1214 (x : Key → ℝ) : Integer.Sparse.eval row1214 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck1214, Integer.Sparse.eval_collectBalanced, rawRowCheck1214]

def rawRow1215 : Integer.Sparse Key := [(key318, -6), (key437, 2), (key441, 2), (key408, 2), (key250, 6), (key437, -2), (key449, -2), (key387, -2), (key250, -2), (key259, -2), (key238, -2), (key318, 2), (key327, 2), (key304, 2)]

theorem rawRowCheck1215 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block1.form1 = rawRow1215 := by decide +kernel

def row1215 : Integer.Sparse Key := [(key238, -2), (key250, 4), (key259, -2), (key304, 2), (key318, -4), (key327, 2), (key387, -2), (key408, 2), (key441, 2), (key449, -2)]

theorem rowCheck1215 : row1215 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1215 := by decide +kernel

theorem rowEval1215 (x : Key → ℝ) : Integer.Sparse.eval row1215 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1215, Integer.Sparse.eval_collectBalanced, rawRowCheck1215]

def rawRow1216 : Integer.Sparse Key := [(key318, -6), (key441, 2), (key408, 2), (key437, 2), (key250, 6), (key449, -2), (key387, -2), (key437, -2), (key259, -2), (key238, -2), (key250, -2), (key327, 2), (key304, 2), (key318, 2)]

theorem rawRowCheck1216 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block1.form1 = rawRow1216 := by decide +kernel

def row1216 : Integer.Sparse Key := [(key238, -2), (key250, 4), (key259, -2), (key304, 2), (key318, -4), (key327, 2), (key387, -2), (key408, 2), (key441, 2), (key449, -2)]

theorem rowCheck1216 : row1216 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1216 := by decide +kernel

theorem rowEval1216 (x : Key → ℝ) : Integer.Sparse.eval row1216 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1216, Integer.Sparse.eval_collectBalanced, rawRowCheck1216]

def rawRow1217 : Integer.Sparse Key := [(key318, -6), (key441, 2), (key437, 2), (key408, 2), (key250, 6), (key449, -2), (key437, -2), (key387, -2), (key259, -2), (key250, -2), (key238, -2), (key327, 2), (key318, 2), (key304, 2)]

theorem rawRowCheck1217 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block1.form1 = rawRow1217 := by decide +kernel

def row1217 : Integer.Sparse Key := [(key238, -2), (key250, 4), (key259, -2), (key304, 2), (key318, -4), (key327, 2), (key387, -2), (key408, 2), (key441, 2), (key449, -2)]

theorem rowCheck1217 : row1217 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1217 := by decide +kernel

theorem rowEval1217 (x : Key → ℝ) : Integer.Sparse.eval row1217 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1217, Integer.Sparse.eval_collectBalanced, rawRowCheck1217]

def rawRow1218 : Integer.Sparse Key := [(key1291, -2), (key1299, -2), (key1299, -2), (key1311, 1), (key1319, 1), (key1311, 1), (key1327, 1), (key1319, 1), (key1327, 1), (key1386, 2), (key1394, 2), (key1394, 2), (key1419, -1), (key1427, -1), (key1419, -1), (key1445, -1), (key1427, -1), (key1445, -1), (key1541, -1), (key1549, -1), (key1541, -1), (key1557, -1), (key1549, -1), (key1557, -1), (key1568, 1), (key1576, 1), (key1568, 1), (key1594, 1), (key1576, 1), (key1594, 1)]

theorem rawRowCheck1218 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block1.form2 = rawRow1218 := by decide +kernel

def row1218 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1386, 2), (key1394, 4), (key1419, -2), (key1427, -2), (key1445, -2), (key1541, -2), (key1549, -2), (key1557, -2), (key1568, 2), (key1576, 2), (key1594, 2)]

theorem rowCheck1218 : row1218 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1218 := by decide +kernel

theorem rowEval1218 (x : Key → ℝ) : Integer.Sparse.eval row1218 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck1218, Integer.Sparse.eval_collectBalanced, rawRowCheck1218]

def rawRow1219 : Integer.Sparse Key := [(key1299, -2), (key1291, -2), (key1299, -2), (key1319, 1), (key1311, 1), (key1327, 1), (key1311, 1), (key1327, 1), (key1319, 1), (key1394, 2), (key1386, 2), (key1394, 2), (key1427, -1), (key1419, -1), (key1445, -1), (key1419, -1), (key1445, -1), (key1427, -1), (key1549, -1), (key1541, -1), (key1557, -1), (key1541, -1), (key1557, -1), (key1549, -1), (key1576, 1), (key1568, 1), (key1594, 1), (key1568, 1), (key1594, 1), (key1576, 1)]

theorem rawRowCheck1219 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block1.form2 = rawRow1219 := by decide +kernel

def row1219 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1386, 2), (key1394, 4), (key1419, -2), (key1427, -2), (key1445, -2), (key1541, -2), (key1549, -2), (key1557, -2), (key1568, 2), (key1576, 2), (key1594, 2)]

theorem rowCheck1219 : row1219 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1219 := by decide +kernel

theorem rowEval1219 (x : Key → ℝ) : Integer.Sparse.eval row1219 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1219, Integer.Sparse.eval_collectBalanced, rawRowCheck1219]

def rawRow1220 : Integer.Sparse Key := [(key1299, -2), (key1299, -2), (key1291, -2), (key1327, 1), (key1327, 1), (key1319, 1), (key1319, 1), (key1311, 1), (key1311, 1), (key1394, 2), (key1394, 2), (key1386, 2), (key1445, -1), (key1445, -1), (key1427, -1), (key1427, -1), (key1419, -1), (key1419, -1), (key1557, -1), (key1557, -1), (key1549, -1), (key1549, -1), (key1541, -1), (key1541, -1), (key1594, 1), (key1594, 1), (key1576, 1), (key1576, 1), (key1568, 1), (key1568, 1)]

theorem rawRowCheck1220 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block1.form2 = rawRow1220 := by decide +kernel

def row1220 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1386, 2), (key1394, 4), (key1419, -2), (key1427, -2), (key1445, -2), (key1541, -2), (key1549, -2), (key1557, -2), (key1568, 2), (key1576, 2), (key1594, 2)]

theorem rowCheck1220 : row1220 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1220 := by decide +kernel

theorem rowEval1220 (x : Key → ℝ) : Integer.Sparse.eval row1220 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1220, Integer.Sparse.eval_collectBalanced, rawRowCheck1220]

def rawRow1221 : Integer.Sparse Key := [(key1311, -2), (key1319, -2), (key1352, -2), (key1291, 1), (key1299, 1), (key1311, 1), (key1327, 1), (key1352, 1), (key1355, 1), (key1419, 2), (key1427, 2), (key1473, 2), (key1386, -1), (key1394, -1), (key1419, -1), (key1445, -1), (key1473, -1), (key1481, -1), (key1568, -1), (key1576, -1), (key1617, -1), (key1625, -1), (key1682, -1), (key1684, -1), (key1541, 1), (key1549, 1), (key1617, 1), (key1634, 1), (key1682, 1), (key1690, 1)]

theorem rawRowCheck1221 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block1.form2 = rawRow1221 := by decide +kernel

def row1221 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 2), (key1445, -1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, 1), (key1568, -1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, -1), (key1690, 1)]

theorem rowCheck1221 : row1221 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1221 := by decide +kernel

theorem rowEval1221 (x : Key → ℝ) : Integer.Sparse.eval row1221 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck1221, Integer.Sparse.eval_collectBalanced, rawRowCheck1221]

def rawRow1222 : Integer.Sparse Key := [(key1319, -2), (key1311, -2), (key1352, -2), (key1299, 1), (key1291, 1), (key1327, 1), (key1311, 1), (key1355, 1), (key1352, 1), (key1427, 2), (key1419, 2), (key1473, 2), (key1394, -1), (key1386, -1), (key1445, -1), (key1419, -1), (key1481, -1), (key1473, -1), (key1576, -1), (key1568, -1), (key1625, -1), (key1617, -1), (key1684, -1), (key1682, -1), (key1549, 1), (key1541, 1), (key1634, 1), (key1617, 1), (key1690, 1), (key1682, 1)]

theorem rawRowCheck1222 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block1.form2 = rawRow1222 := by decide +kernel

def row1222 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 2), (key1445, -1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, 1), (key1568, -1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, -1), (key1690, 1)]

theorem rowCheck1222 : row1222 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1222 := by decide +kernel

theorem rowEval1222 (x : Key → ℝ) : Integer.Sparse.eval row1222 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1222, Integer.Sparse.eval_collectBalanced, rawRowCheck1222]

def rawRow1223 : Integer.Sparse Key := [(key1311, -2), (key1352, -2), (key1319, -2), (key1311, 1), (key1352, 1), (key1291, 1), (key1355, 1), (key1299, 1), (key1327, 1), (key1419, 2), (key1473, 2), (key1427, 2), (key1419, -1), (key1473, -1), (key1386, -1), (key1481, -1), (key1394, -1), (key1445, -1), (key1617, -1), (key1682, -1), (key1568, -1), (key1684, -1), (key1576, -1), (key1625, -1), (key1617, 1), (key1682, 1), (key1541, 1), (key1690, 1), (key1549, 1), (key1634, 1)]

theorem rawRowCheck1223 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block1.form2 = rawRow1223 := by decide +kernel

def row1223 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 2), (key1445, -1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, 1), (key1568, -1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, -1), (key1690, 1)]

theorem rowCheck1223 : row1223 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1223 := by decide +kernel

theorem rowEval1223 (x : Key → ℝ) : Integer.Sparse.eval row1223 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck1223, Integer.Sparse.eval_collectBalanced, rawRowCheck1223]

def rawRow1224 : Integer.Sparse Key := [(key1352, -2), (key1311, -2), (key1319, -2), (key1352, 1), (key1311, 1), (key1355, 1), (key1291, 1), (key1327, 1), (key1299, 1), (key1473, 2), (key1419, 2), (key1427, 2), (key1473, -1), (key1419, -1), (key1481, -1), (key1386, -1), (key1445, -1), (key1394, -1), (key1682, -1), (key1617, -1), (key1684, -1), (key1568, -1), (key1625, -1), (key1576, -1), (key1682, 1), (key1617, 1), (key1690, 1), (key1541, 1), (key1634, 1), (key1549, 1)]

theorem rawRowCheck1224 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block1.form2 = rawRow1224 := by decide +kernel

def row1224 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 2), (key1445, -1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, 1), (key1568, -1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, -1), (key1690, 1)]

theorem rowCheck1224 : row1224 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1224 := by decide +kernel

theorem rowEval1224 (x : Key → ℝ) : Integer.Sparse.eval row1224 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1224, Integer.Sparse.eval_collectBalanced, rawRowCheck1224]

def rawRow1225 : Integer.Sparse Key := [(key1319, -2), (key1352, -2), (key1311, -2), (key1327, 1), (key1355, 1), (key1299, 1), (key1352, 1), (key1291, 1), (key1311, 1), (key1427, 2), (key1473, 2), (key1419, 2), (key1445, -1), (key1481, -1), (key1394, -1), (key1473, -1), (key1386, -1), (key1419, -1), (key1625, -1), (key1684, -1), (key1576, -1), (key1682, -1), (key1568, -1), (key1617, -1), (key1634, 1), (key1690, 1), (key1549, 1), (key1682, 1), (key1541, 1), (key1617, 1)]

theorem rawRowCheck1225 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block1.form2 = rawRow1225 := by decide +kernel

def row1225 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 2), (key1445, -1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, 1), (key1568, -1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, -1), (key1690, 1)]

theorem rowCheck1225 : row1225 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1225 := by decide +kernel

theorem rowEval1225 (x : Key → ℝ) : Integer.Sparse.eval row1225 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1225, Integer.Sparse.eval_collectBalanced, rawRowCheck1225]

def rawRow1226 : Integer.Sparse Key := [(key1352, -2), (key1319, -2), (key1311, -2), (key1355, 1), (key1327, 1), (key1352, 1), (key1299, 1), (key1311, 1), (key1291, 1), (key1473, 2), (key1427, 2), (key1419, 2), (key1481, -1), (key1445, -1), (key1473, -1), (key1394, -1), (key1419, -1), (key1386, -1), (key1684, -1), (key1625, -1), (key1682, -1), (key1576, -1), (key1617, -1), (key1568, -1), (key1690, 1), (key1634, 1), (key1682, 1), (key1549, 1), (key1617, 1), (key1541, 1)]

theorem rawRowCheck1226 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block1.form2 = rawRow1226 := by decide +kernel

def row1226 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 2), (key1445, -1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, 1), (key1568, -1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, -1), (key1690, 1)]

theorem rowCheck1226 : row1226 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1226 := by decide +kernel

theorem rowEval1226 (x : Key → ℝ) : Integer.Sparse.eval row1226 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1226, Integer.Sparse.eval_collectBalanced, rawRowCheck1226]

def rawRow1227 : Integer.Sparse Key := [(key1386, -2), (key1394, -2), (key1394, -2), (key1541, 1), (key1549, 1), (key1541, 1), (key1557, 1), (key1549, 1), (key1557, 1), (key1291, 2), (key1299, 2), (key1299, 2), (key1568, -1), (key1576, -1), (key1568, -1), (key1594, -1), (key1576, -1), (key1594, -1), (key1311, -1), (key1319, -1), (key1311, -1), (key1327, -1), (key1319, -1), (key1327, -1), (key1419, 1), (key1427, 1), (key1419, 1), (key1445, 1), (key1427, 1), (key1445, 1)]

theorem rawRowCheck1227 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block1.form2 = rawRow1227 := by decide +kernel

def row1227 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, -2), (key1319, -2), (key1327, -2), (key1386, -2), (key1394, -4), (key1419, 2), (key1427, 2), (key1445, 2), (key1541, 2), (key1549, 2), (key1557, 2), (key1568, -2), (key1576, -2), (key1594, -2)]

theorem rowCheck1227 : row1227 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1227 := by decide +kernel

theorem rowEval1227 (x : Key → ℝ) : Integer.Sparse.eval row1227 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck1227, Integer.Sparse.eval_collectBalanced, rawRowCheck1227]

def rawRow1228 : Integer.Sparse Key := [(key1394, -2), (key1386, -2), (key1394, -2), (key1549, 1), (key1541, 1), (key1557, 1), (key1541, 1), (key1557, 1), (key1549, 1), (key1299, 2), (key1291, 2), (key1299, 2), (key1576, -1), (key1568, -1), (key1594, -1), (key1568, -1), (key1594, -1), (key1576, -1), (key1319, -1), (key1311, -1), (key1327, -1), (key1311, -1), (key1327, -1), (key1319, -1), (key1427, 1), (key1419, 1), (key1445, 1), (key1419, 1), (key1445, 1), (key1427, 1)]

theorem rawRowCheck1228 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block1.form2 = rawRow1228 := by decide +kernel

def row1228 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, -2), (key1319, -2), (key1327, -2), (key1386, -2), (key1394, -4), (key1419, 2), (key1427, 2), (key1445, 2), (key1541, 2), (key1549, 2), (key1557, 2), (key1568, -2), (key1576, -2), (key1594, -2)]

theorem rowCheck1228 : row1228 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1228 := by decide +kernel

theorem rowEval1228 (x : Key → ℝ) : Integer.Sparse.eval row1228 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1228, Integer.Sparse.eval_collectBalanced, rawRowCheck1228]

def rawRow1229 : Integer.Sparse Key := [(key1394, -2), (key1394, -2), (key1386, -2), (key1557, 1), (key1557, 1), (key1549, 1), (key1549, 1), (key1541, 1), (key1541, 1), (key1299, 2), (key1299, 2), (key1291, 2), (key1594, -1), (key1594, -1), (key1576, -1), (key1576, -1), (key1568, -1), (key1568, -1), (key1327, -1), (key1327, -1), (key1319, -1), (key1319, -1), (key1311, -1), (key1311, -1), (key1445, 1), (key1445, 1), (key1427, 1), (key1427, 1), (key1419, 1), (key1419, 1)]

theorem rawRowCheck1229 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block1.form2 = rawRow1229 := by decide +kernel

def row1229 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, -2), (key1319, -2), (key1327, -2), (key1386, -2), (key1394, -4), (key1419, 2), (key1427, 2), (key1445, 2), (key1541, 2), (key1549, 2), (key1557, 2), (key1568, -2), (key1576, -2), (key1594, -2)]

theorem rowCheck1229 : row1229 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1229 := by decide +kernel

theorem rowEval1229 (x : Key → ℝ) : Integer.Sparse.eval row1229 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1229, Integer.Sparse.eval_collectBalanced, rawRowCheck1229]

def rawRow1230 : Integer.Sparse Key := [(key1419, -2), (key1427, -2), (key1473, -2), (key1568, 1), (key1576, 1), (key1617, 1), (key1625, 1), (key1682, 1), (key1684, 1), (key1311, 2), (key1319, 2), (key1352, 2), (key1541, -1), (key1549, -1), (key1617, -1), (key1634, -1), (key1682, -1), (key1690, -1), (key1291, -1), (key1299, -1), (key1311, -1), (key1327, -1), (key1352, -1), (key1355, -1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1)]

theorem rawRowCheck1230 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block1.form2 = rawRow1230 := by decide +kernel

def row1230 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 2), (key1327, -1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, 1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, -1), (key1568, 1), (key1576, 1), (key1625, 1), (key1634, -1), (key1684, 1), (key1690, -1)]

theorem rowCheck1230 : row1230 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1230 := by decide +kernel

theorem rowEval1230 (x : Key → ℝ) : Integer.Sparse.eval row1230 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck1230, Integer.Sparse.eval_collectBalanced, rawRowCheck1230]

def rawRow1231 : Integer.Sparse Key := [(key1427, -2), (key1419, -2), (key1473, -2), (key1576, 1), (key1568, 1), (key1625, 1), (key1617, 1), (key1684, 1), (key1682, 1), (key1319, 2), (key1311, 2), (key1352, 2), (key1549, -1), (key1541, -1), (key1634, -1), (key1617, -1), (key1690, -1), (key1682, -1), (key1299, -1), (key1291, -1), (key1327, -1), (key1311, -1), (key1355, -1), (key1352, -1), (key1394, 1), (key1386, 1), (key1445, 1), (key1419, 1), (key1481, 1), (key1473, 1)]

theorem rawRowCheck1231 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block1.form2 = rawRow1231 := by decide +kernel

def row1231 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 2), (key1327, -1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, 1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, -1), (key1568, 1), (key1576, 1), (key1625, 1), (key1634, -1), (key1684, 1), (key1690, -1)]

theorem rowCheck1231 : row1231 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1231 := by decide +kernel

theorem rowEval1231 (x : Key → ℝ) : Integer.Sparse.eval row1231 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1231, Integer.Sparse.eval_collectBalanced, rawRowCheck1231]

def rawRow1232 : Integer.Sparse Key := [(key1419, -2), (key1473, -2), (key1427, -2), (key1617, 1), (key1682, 1), (key1568, 1), (key1684, 1), (key1576, 1), (key1625, 1), (key1311, 2), (key1352, 2), (key1319, 2), (key1617, -1), (key1682, -1), (key1541, -1), (key1690, -1), (key1549, -1), (key1634, -1), (key1311, -1), (key1352, -1), (key1291, -1), (key1355, -1), (key1299, -1), (key1327, -1), (key1419, 1), (key1473, 1), (key1386, 1), (key1481, 1), (key1394, 1), (key1445, 1)]

theorem rawRowCheck1232 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block1.form2 = rawRow1232 := by decide +kernel

def row1232 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 2), (key1327, -1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, 1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, -1), (key1568, 1), (key1576, 1), (key1625, 1), (key1634, -1), (key1684, 1), (key1690, -1)]

theorem rowCheck1232 : row1232 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1232 := by decide +kernel

theorem rowEval1232 (x : Key → ℝ) : Integer.Sparse.eval row1232 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck1232, Integer.Sparse.eval_collectBalanced, rawRowCheck1232]

def rawRow1233 : Integer.Sparse Key := [(key1473, -2), (key1419, -2), (key1427, -2), (key1682, 1), (key1617, 1), (key1684, 1), (key1568, 1), (key1625, 1), (key1576, 1), (key1352, 2), (key1311, 2), (key1319, 2), (key1682, -1), (key1617, -1), (key1690, -1), (key1541, -1), (key1634, -1), (key1549, -1), (key1352, -1), (key1311, -1), (key1355, -1), (key1291, -1), (key1327, -1), (key1299, -1), (key1473, 1), (key1419, 1), (key1481, 1), (key1386, 1), (key1445, 1), (key1394, 1)]

theorem rawRowCheck1233 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block1.form2 = rawRow1233 := by decide +kernel

def row1233 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 2), (key1327, -1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, 1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, -1), (key1568, 1), (key1576, 1), (key1625, 1), (key1634, -1), (key1684, 1), (key1690, -1)]

theorem rowCheck1233 : row1233 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1233 := by decide +kernel

theorem rowEval1233 (x : Key → ℝ) : Integer.Sparse.eval row1233 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1233, Integer.Sparse.eval_collectBalanced, rawRowCheck1233]

def rawRow1234 : Integer.Sparse Key := [(key1427, -2), (key1473, -2), (key1419, -2), (key1625, 1), (key1684, 1), (key1576, 1), (key1682, 1), (key1568, 1), (key1617, 1), (key1319, 2), (key1352, 2), (key1311, 2), (key1634, -1), (key1690, -1), (key1549, -1), (key1682, -1), (key1541, -1), (key1617, -1), (key1327, -1), (key1355, -1), (key1299, -1), (key1352, -1), (key1291, -1), (key1311, -1), (key1445, 1), (key1481, 1), (key1394, 1), (key1473, 1), (key1386, 1), (key1419, 1)]

theorem rawRowCheck1234 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block1.form2 = rawRow1234 := by decide +kernel

def row1234 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 2), (key1327, -1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, 1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, -1), (key1568, 1), (key1576, 1), (key1625, 1), (key1634, -1), (key1684, 1), (key1690, -1)]

theorem rowCheck1234 : row1234 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1234 := by decide +kernel

theorem rowEval1234 (x : Key → ℝ) : Integer.Sparse.eval row1234 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1234, Integer.Sparse.eval_collectBalanced, rawRowCheck1234]

def rawRow1235 : Integer.Sparse Key := [(key1473, -2), (key1427, -2), (key1419, -2), (key1684, 1), (key1625, 1), (key1682, 1), (key1576, 1), (key1617, 1), (key1568, 1), (key1352, 2), (key1319, 2), (key1311, 2), (key1690, -1), (key1634, -1), (key1682, -1), (key1549, -1), (key1617, -1), (key1541, -1), (key1355, -1), (key1327, -1), (key1352, -1), (key1299, -1), (key1311, -1), (key1291, -1), (key1481, 1), (key1445, 1), (key1473, 1), (key1394, 1), (key1419, 1), (key1386, 1)]

theorem rawRowCheck1235 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block1.form2 = rawRow1235 := by decide +kernel

def row1235 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 2), (key1327, -1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, 1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, -1), (key1568, 1), (key1576, 1), (key1625, 1), (key1634, -1), (key1684, 1), (key1690, -1)]

theorem rowCheck1235 : row1235 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1235 := by decide +kernel

theorem rowEval1235 (x : Key → ℝ) : Integer.Sparse.eval row1235 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1235, Integer.Sparse.eval_collectBalanced, rawRowCheck1235]

def rawRow1236 : Integer.Sparse Key := [(key18, -2), (key23, -2), (key23, -2), (key35, 6), (key375, 2), (key381, 2), (key381, 2), (key486, -2), (key486, -2), (key490, -2), (key654, -6), (key659, 2), (key659, 2), (key663, 2)]

theorem rawRowCheck1236 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block1.form3 = rawRow1236 := by decide +kernel

def row1236 : Integer.Sparse Key := [(key18, -2), (key23, -4), (key35, 6), (key375, 2), (key381, 4), (key486, -4), (key490, -2), (key654, -6), (key659, 4), (key663, 2)]

theorem rowCheck1236 : row1236 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1236 := by decide +kernel

theorem rowEval1236 (x : Key → ℝ) : Integer.Sparse.eval row1236 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1236, Integer.Sparse.eval_collectBalanced, rawRowCheck1236]

def rawRow1237 : Integer.Sparse Key := [(key23, -2), (key18, -2), (key23, -2), (key35, 6), (key381, 2), (key375, 2), (key381, 2), (key486, -2), (key490, -2), (key486, -2), (key654, -6), (key659, 2), (key663, 2), (key659, 2)]

theorem rawRowCheck1237 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block1.form3 = rawRow1237 := by decide +kernel

def row1237 : Integer.Sparse Key := [(key18, -2), (key23, -4), (key35, 6), (key375, 2), (key381, 4), (key486, -4), (key490, -2), (key654, -6), (key659, 4), (key663, 2)]

theorem rowCheck1237 : row1237 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1237 := by decide +kernel

theorem rowEval1237 (x : Key → ℝ) : Integer.Sparse.eval row1237 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1237, Integer.Sparse.eval_collectBalanced, rawRowCheck1237]

def rawRow1238 : Integer.Sparse Key := [(key23, -2), (key23, -2), (key18, -2), (key35, 6), (key381, 2), (key381, 2), (key375, 2), (key490, -2), (key486, -2), (key486, -2), (key654, -6), (key663, 2), (key659, 2), (key659, 2)]

theorem rawRowCheck1238 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block1.form3 = rawRow1238 := by decide +kernel

def row1238 : Integer.Sparse Key := [(key18, -2), (key23, -4), (key35, 6), (key375, 2), (key381, 4), (key486, -4), (key490, -2), (key654, -6), (key659, 4), (key663, 2)]

theorem rowCheck1238 : row1238 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1238 := by decide +kernel

theorem rowEval1238 (x : Key → ℝ) : Integer.Sparse.eval row1238 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1238, Integer.Sparse.eval_collectBalanced, rawRowCheck1238]

def rawRow1239 : Integer.Sparse Key := [(key18, -2), (key23, -2), (key35, -2), (key23, 6), (key426, 2), (key432, 2), (key486, 2), (key381, -2), (key432, -2), (key460, -2), (key659, -6), (key654, 2), (key659, 2), (key663, 2)]

theorem rawRowCheck1239 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block1.form3 = rawRow1239 := by decide +kernel

def row1239 : Integer.Sparse Key := [(key18, -2), (key23, 4), (key35, -2), (key381, -2), (key426, 2), (key460, -2), (key486, 2), (key654, 2), (key659, -4), (key663, 2)]

theorem rowCheck1239 : row1239 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1239 := by decide +kernel

theorem rowEval1239 (x : Key → ℝ) : Integer.Sparse.eval row1239 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1239, Integer.Sparse.eval_collectBalanced, rawRowCheck1239]

def rawRow1240 : Integer.Sparse Key := [(key23, -2), (key18, -2), (key35, -2), (key23, 6), (key432, 2), (key426, 2), (key486, 2), (key381, -2), (key460, -2), (key432, -2), (key659, -6), (key654, 2), (key663, 2), (key659, 2)]

theorem rawRowCheck1240 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block1.form3 = rawRow1240 := by decide +kernel

def row1240 : Integer.Sparse Key := [(key18, -2), (key23, 4), (key35, -2), (key381, -2), (key426, 2), (key460, -2), (key486, 2), (key654, 2), (key659, -4), (key663, 2)]

theorem rowCheck1240 : row1240 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1240 := by decide +kernel

theorem rowEval1240 (x : Key → ℝ) : Integer.Sparse.eval row1240 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1240, Integer.Sparse.eval_collectBalanced, rawRowCheck1240]

def rawRow1241 : Integer.Sparse Key := [(key18, -2), (key35, -2), (key23, -2), (key23, 6), (key426, 2), (key486, 2), (key432, 2), (key432, -2), (key381, -2), (key460, -2), (key659, -6), (key659, 2), (key654, 2), (key663, 2)]

theorem rawRowCheck1241 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block1.form3 = rawRow1241 := by decide +kernel

def row1241 : Integer.Sparse Key := [(key18, -2), (key23, 4), (key35, -2), (key381, -2), (key426, 2), (key460, -2), (key486, 2), (key654, 2), (key659, -4), (key663, 2)]

theorem rowCheck1241 : row1241 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1241 := by decide +kernel

theorem rowEval1241 (x : Key → ℝ) : Integer.Sparse.eval row1241 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1241, Integer.Sparse.eval_collectBalanced, rawRowCheck1241]

def rawRow1242 : Integer.Sparse Key := [(key35, -2), (key18, -2), (key23, -2), (key23, 6), (key486, 2), (key426, 2), (key432, 2), (key432, -2), (key460, -2), (key381, -2), (key659, -6), (key659, 2), (key663, 2), (key654, 2)]

theorem rawRowCheck1242 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block1.form3 = rawRow1242 := by decide +kernel

def row1242 : Integer.Sparse Key := [(key18, -2), (key23, 4), (key35, -2), (key381, -2), (key426, 2), (key460, -2), (key486, 2), (key654, 2), (key659, -4), (key663, 2)]

theorem rowCheck1242 : row1242 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1242 := by decide +kernel

theorem rowEval1242 (x : Key → ℝ) : Integer.Sparse.eval row1242 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1242, Integer.Sparse.eval_collectBalanced, rawRowCheck1242]

def rawRow1243 : Integer.Sparse Key := [(key23, -2), (key35, -2), (key18, -2), (key23, 6), (key432, 2), (key486, 2), (key426, 2), (key460, -2), (key381, -2), (key432, -2), (key659, -6), (key663, 2), (key654, 2), (key659, 2)]

theorem rawRowCheck1243 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block1.form3 = rawRow1243 := by decide +kernel

def row1243 : Integer.Sparse Key := [(key18, -2), (key23, 4), (key35, -2), (key381, -2), (key426, 2), (key460, -2), (key486, 2), (key654, 2), (key659, -4), (key663, 2)]

theorem rowCheck1243 : row1243 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1243 := by decide +kernel

theorem rowEval1243 (x : Key → ℝ) : Integer.Sparse.eval row1243 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1243, Integer.Sparse.eval_collectBalanced, rawRowCheck1243]

def rawRow1244 : Integer.Sparse Key := [(key35, -2), (key23, -2), (key18, -2), (key23, 6), (key486, 2), (key432, 2), (key426, 2), (key460, -2), (key432, -2), (key381, -2), (key659, -6), (key663, 2), (key659, 2), (key654, 2)]

theorem rawRowCheck1244 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block1.form3 = rawRow1244 := by decide +kernel

def row1244 : Integer.Sparse Key := [(key18, -2), (key23, 4), (key35, -2), (key381, -2), (key426, 2), (key460, -2), (key486, 2), (key654, 2), (key659, -4), (key663, 2)]

theorem rowCheck1244 : row1244 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1244 := by decide +kernel

theorem rowEval1244 (x : Key → ℝ) : Integer.Sparse.eval row1244 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1244, Integer.Sparse.eval_collectBalanced, rawRowCheck1244]

def rawRow1245 : Integer.Sparse Key := [(key43, -2), (key48, -2), (key48, -2), (key74, 6), (key206, 2), (key212, 2), (key212, 2), (key659, -2), (key659, -2), (key663, -2), (key218, -6), (key486, 2), (key486, 2), (key490, 2)]

theorem rawRowCheck1245 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block1.form3 = rawRow1245 := by decide +kernel

def row1245 : Integer.Sparse Key := [(key43, -2), (key48, -4), (key74, 6), (key206, 2), (key212, 4), (key218, -6), (key486, 4), (key490, 2), (key659, -4), (key663, -2)]

theorem rowCheck1245 : row1245 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1245 := by decide +kernel

theorem rowEval1245 (x : Key → ℝ) : Integer.Sparse.eval row1245 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1245, Integer.Sparse.eval_collectBalanced, rawRowCheck1245]

def rawRow1246 : Integer.Sparse Key := [(key48, -2), (key43, -2), (key48, -2), (key74, 6), (key212, 2), (key206, 2), (key212, 2), (key659, -2), (key663, -2), (key659, -2), (key218, -6), (key486, 2), (key490, 2), (key486, 2)]

theorem rawRowCheck1246 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block1.form3 = rawRow1246 := by decide +kernel

def row1246 : Integer.Sparse Key := [(key43, -2), (key48, -4), (key74, 6), (key206, 2), (key212, 4), (key218, -6), (key486, 4), (key490, 2), (key659, -4), (key663, -2)]

theorem rowCheck1246 : row1246 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1246 := by decide +kernel

theorem rowEval1246 (x : Key → ℝ) : Integer.Sparse.eval row1246 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1246, Integer.Sparse.eval_collectBalanced, rawRowCheck1246]

def rawRow1247 : Integer.Sparse Key := [(key48, -2), (key48, -2), (key43, -2), (key74, 6), (key212, 2), (key212, 2), (key206, 2), (key663, -2), (key659, -2), (key659, -2), (key218, -6), (key490, 2), (key486, 2), (key486, 2)]

theorem rawRowCheck1247 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block1.form3 = rawRow1247 := by decide +kernel

def row1247 : Integer.Sparse Key := [(key43, -2), (key48, -4), (key74, 6), (key206, 2), (key212, 4), (key218, -6), (key486, 4), (key490, 2), (key659, -4), (key663, -2)]

theorem rowCheck1247 : row1247 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1247 := by decide +kernel

theorem rowEval1247 (x : Key → ℝ) : Integer.Sparse.eval row1247 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1247, Integer.Sparse.eval_collectBalanced, rawRowCheck1247]

def rawRow1248 : Integer.Sparse Key := [(key100, -2), (key105, -2), (key115, -2), (key137, 6), (key18, 2), (key23, 2), (key35, 2), (key654, -2), (key659, -2), (key663, -2), (key212, -6), (key381, 2), (key432, 2), (key460, 2)]

theorem rawRowCheck1248 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block1.form3 = rawRow1248 := by decide +kernel

def row1248 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key100, -2), (key105, -2), (key115, -2), (key137, 6), (key212, -6), (key381, 2), (key432, 2), (key460, 2), (key654, -2), (key659, -2), (key663, -2)]

theorem rowCheck1248 : row1248 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1248 := by decide +kernel

theorem rowEval1248 (x : Key → ℝ) : Integer.Sparse.eval row1248 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1248, Integer.Sparse.eval_collectBalanced, rawRowCheck1248]

def rawRow1249 : Integer.Sparse Key := [(key105, -2), (key100, -2), (key115, -2), (key137, 6), (key23, 2), (key18, 2), (key35, 2), (key654, -2), (key663, -2), (key659, -2), (key212, -6), (key381, 2), (key460, 2), (key432, 2)]

theorem rawRowCheck1249 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block1.form3 = rawRow1249 := by decide +kernel

def row1249 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key100, -2), (key105, -2), (key115, -2), (key137, 6), (key212, -6), (key381, 2), (key432, 2), (key460, 2), (key654, -2), (key659, -2), (key663, -2)]

theorem rowCheck1249 : row1249 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1249 := by decide +kernel

theorem rowEval1249 (x : Key → ℝ) : Integer.Sparse.eval row1249 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1249, Integer.Sparse.eval_collectBalanced, rawRowCheck1249]

def rawRow1250 : Integer.Sparse Key := [(key100, -2), (key115, -2), (key105, -2), (key137, 6), (key18, 2), (key35, 2), (key23, 2), (key659, -2), (key654, -2), (key663, -2), (key212, -6), (key432, 2), (key381, 2), (key460, 2)]

theorem rawRowCheck1250 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block1.form3 = rawRow1250 := by decide +kernel

def row1250 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key100, -2), (key105, -2), (key115, -2), (key137, 6), (key212, -6), (key381, 2), (key432, 2), (key460, 2), (key654, -2), (key659, -2), (key663, -2)]

theorem rowCheck1250 : row1250 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1250 := by decide +kernel

theorem rowEval1250 (x : Key → ℝ) : Integer.Sparse.eval row1250 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1250, Integer.Sparse.eval_collectBalanced, rawRowCheck1250]

def rawRow1251 : Integer.Sparse Key := [(key115, -2), (key100, -2), (key105, -2), (key137, 6), (key35, 2), (key18, 2), (key23, 2), (key659, -2), (key663, -2), (key654, -2), (key212, -6), (key432, 2), (key460, 2), (key381, 2)]

theorem rawRowCheck1251 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block1.form3 = rawRow1251 := by decide +kernel

def row1251 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key100, -2), (key105, -2), (key115, -2), (key137, 6), (key212, -6), (key381, 2), (key432, 2), (key460, 2), (key654, -2), (key659, -2), (key663, -2)]

theorem rowCheck1251 : row1251 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1251 := by decide +kernel

theorem rowEval1251 (x : Key → ℝ) : Integer.Sparse.eval row1251 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1251, Integer.Sparse.eval_collectBalanced, rawRowCheck1251]

def rawRow1252 : Integer.Sparse Key := [(key105, -2), (key115, -2), (key100, -2), (key137, 6), (key23, 2), (key35, 2), (key18, 2), (key663, -2), (key654, -2), (key659, -2), (key212, -6), (key460, 2), (key381, 2), (key432, 2)]

theorem rawRowCheck1252 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block1.form3 = rawRow1252 := by decide +kernel

def row1252 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key100, -2), (key105, -2), (key115, -2), (key137, 6), (key212, -6), (key381, 2), (key432, 2), (key460, 2), (key654, -2), (key659, -2), (key663, -2)]

theorem rowCheck1252 : row1252 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1252 := by decide +kernel

theorem rowEval1252 (x : Key → ℝ) : Integer.Sparse.eval row1252 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1252, Integer.Sparse.eval_collectBalanced, rawRowCheck1252]

def rawRow1253 : Integer.Sparse Key := [(key115, -2), (key105, -2), (key100, -2), (key137, 6), (key35, 2), (key23, 2), (key18, 2), (key663, -2), (key659, -2), (key654, -2), (key212, -6), (key460, 2), (key432, 2), (key381, 2)]

theorem rawRowCheck1253 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block1.form3 = rawRow1253 := by decide +kernel

def row1253 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key100, -2), (key105, -2), (key115, -2), (key137, 6), (key212, -6), (key381, 2), (key432, 2), (key460, 2), (key654, -2), (key659, -2), (key663, -2)]

theorem rowCheck1253 : row1253 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1253 := by decide +kernel

theorem rowEval1253 (x : Key → ℝ) : Integer.Sparse.eval row1253 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1253, Integer.Sparse.eval_collectBalanced, rawRowCheck1253]

def rawRow1254 : Integer.Sparse Key := [(key1293, -6), (key1313, 2), (key1313, 2), (key1323, 2), (key1388, 6), (key1421, -2), (key1421, -2), (key1441, -2), (key1543, -2), (key1543, -2), (key1553, -2), (key1570, 2), (key1570, 2), (key1590, 2)]

theorem rawRowCheck1254 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block1.form4 = rawRow1254 := by decide +kernel

def row1254 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1388, 6), (key1421, -4), (key1441, -2), (key1543, -4), (key1553, -2), (key1570, 4), (key1590, 2)]

theorem rowCheck1254 : row1254 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1254 := by decide +kernel

theorem rowEval1254 (x : Key → ℝ) : Integer.Sparse.eval row1254 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1254, Integer.Sparse.eval_collectBalanced, rawRowCheck1254]

def rawRow1255 : Integer.Sparse Key := [(key1293, -6), (key1313, 2), (key1323, 2), (key1313, 2), (key1388, 6), (key1421, -2), (key1441, -2), (key1421, -2), (key1543, -2), (key1553, -2), (key1543, -2), (key1570, 2), (key1590, 2), (key1570, 2)]

theorem rawRowCheck1255 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block1.form4 = rawRow1255 := by decide +kernel

def row1255 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1388, 6), (key1421, -4), (key1441, -2), (key1543, -4), (key1553, -2), (key1570, 4), (key1590, 2)]

theorem rowCheck1255 : row1255 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1255 := by decide +kernel

theorem rowEval1255 (x : Key → ℝ) : Integer.Sparse.eval row1255 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1255, Integer.Sparse.eval_collectBalanced, rawRowCheck1255]

def rawRow1256 : Integer.Sparse Key := [(key1293, -6), (key1323, 2), (key1313, 2), (key1313, 2), (key1388, 6), (key1441, -2), (key1421, -2), (key1421, -2), (key1553, -2), (key1543, -2), (key1543, -2), (key1590, 2), (key1570, 2), (key1570, 2)]

theorem rawRowCheck1256 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block1.form4 = rawRow1256 := by decide +kernel

def row1256 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1388, 6), (key1421, -4), (key1441, -2), (key1543, -4), (key1553, -2), (key1570, 4), (key1590, 2)]

theorem rowCheck1256 : row1256 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1256 := by decide +kernel

theorem rowEval1256 (x : Key → ℝ) : Integer.Sparse.eval row1256 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1256, Integer.Sparse.eval_collectBalanced, rawRowCheck1256]

def rawRow1257 : Integer.Sparse Key := [(key1313, -6), (key1293, 2), (key1313, 2), (key1323, 2), (key1421, 6), (key1388, -2), (key1421, -2), (key1441, -2), (key1570, -2), (key1619, -2), (key1621, -2), (key1543, 2), (key1619, 2), (key1630, 2)]

theorem rawRowCheck1257 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block1.form4 = rawRow1257 := by decide +kernel

def row1257 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, -2), (key1421, 4), (key1441, -2), (key1543, 2), (key1570, -2), (key1621, -2), (key1630, 2)]

theorem rowCheck1257 : row1257 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1257 := by decide +kernel

theorem rowEval1257 (x : Key → ℝ) : Integer.Sparse.eval row1257 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1257, Integer.Sparse.eval_collectBalanced, rawRowCheck1257]

def rawRow1258 : Integer.Sparse Key := [(key1313, -6), (key1293, 2), (key1323, 2), (key1313, 2), (key1421, 6), (key1388, -2), (key1441, -2), (key1421, -2), (key1570, -2), (key1621, -2), (key1619, -2), (key1543, 2), (key1630, 2), (key1619, 2)]

theorem rawRowCheck1258 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block1.form4 = rawRow1258 := by decide +kernel

def row1258 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, -2), (key1421, 4), (key1441, -2), (key1543, 2), (key1570, -2), (key1621, -2), (key1630, 2)]

theorem rowCheck1258 : row1258 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1258 := by decide +kernel

theorem rowEval1258 (x : Key → ℝ) : Integer.Sparse.eval row1258 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1258, Integer.Sparse.eval_collectBalanced, rawRowCheck1258]

def rawRow1259 : Integer.Sparse Key := [(key1313, -6), (key1313, 2), (key1293, 2), (key1323, 2), (key1421, 6), (key1421, -2), (key1388, -2), (key1441, -2), (key1619, -2), (key1570, -2), (key1621, -2), (key1619, 2), (key1543, 2), (key1630, 2)]

theorem rawRowCheck1259 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block1.form4 = rawRow1259 := by decide +kernel

def row1259 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, -2), (key1421, 4), (key1441, -2), (key1543, 2), (key1570, -2), (key1621, -2), (key1630, 2)]

theorem rowCheck1259 : row1259 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1259 := by decide +kernel

theorem rowEval1259 (x : Key → ℝ) : Integer.Sparse.eval row1259 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1259, Integer.Sparse.eval_collectBalanced, rawRowCheck1259]

def rawRow1260 : Integer.Sparse Key := [(key1313, -6), (key1313, 2), (key1323, 2), (key1293, 2), (key1421, 6), (key1421, -2), (key1441, -2), (key1388, -2), (key1619, -2), (key1621, -2), (key1570, -2), (key1619, 2), (key1630, 2), (key1543, 2)]

theorem rawRowCheck1260 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block1.form4 = rawRow1260 := by decide +kernel

def row1260 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, -2), (key1421, 4), (key1441, -2), (key1543, 2), (key1570, -2), (key1621, -2), (key1630, 2)]

theorem rowCheck1260 : row1260 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1260 := by decide +kernel

theorem rowEval1260 (x : Key → ℝ) : Integer.Sparse.eval row1260 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1260, Integer.Sparse.eval_collectBalanced, rawRowCheck1260]

def rawRow1261 : Integer.Sparse Key := [(key1313, -6), (key1323, 2), (key1293, 2), (key1313, 2), (key1421, 6), (key1441, -2), (key1388, -2), (key1421, -2), (key1621, -2), (key1570, -2), (key1619, -2), (key1630, 2), (key1543, 2), (key1619, 2)]

theorem rawRowCheck1261 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block1.form4 = rawRow1261 := by decide +kernel

def row1261 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, -2), (key1421, 4), (key1441, -2), (key1543, 2), (key1570, -2), (key1621, -2), (key1630, 2)]

theorem rowCheck1261 : row1261 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1261 := by decide +kernel

theorem rowEval1261 (x : Key → ℝ) : Integer.Sparse.eval row1261 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1261, Integer.Sparse.eval_collectBalanced, rawRowCheck1261]

def rawRow1262 : Integer.Sparse Key := [(key1313, -6), (key1323, 2), (key1313, 2), (key1293, 2), (key1421, 6), (key1441, -2), (key1421, -2), (key1388, -2), (key1621, -2), (key1619, -2), (key1570, -2), (key1630, 2), (key1619, 2), (key1543, 2)]

theorem rawRowCheck1262 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block1.form4 = rawRow1262 := by decide +kernel

def row1262 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, -2), (key1421, 4), (key1441, -2), (key1543, 2), (key1570, -2), (key1621, -2), (key1630, 2)]

theorem rowCheck1262 : row1262 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1262 := by decide +kernel

theorem rowEval1262 (x : Key → ℝ) : Integer.Sparse.eval row1262 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1262, Integer.Sparse.eval_collectBalanced, rawRowCheck1262]

def rawRow1263 : Integer.Sparse Key := [(key1388, -6), (key1543, 2), (key1543, 2), (key1553, 2), (key1293, 6), (key1570, -2), (key1570, -2), (key1590, -2), (key1313, -2), (key1313, -2), (key1323, -2), (key1421, 2), (key1421, 2), (key1441, 2)]

theorem rawRowCheck1263 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block1.form4 = rawRow1263 := by decide +kernel

def row1263 : Integer.Sparse Key := [(key1293, 6), (key1313, -4), (key1323, -2), (key1388, -6), (key1421, 4), (key1441, 2), (key1543, 4), (key1553, 2), (key1570, -4), (key1590, -2)]

theorem rowCheck1263 : row1263 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1263 := by decide +kernel

theorem rowEval1263 (x : Key → ℝ) : Integer.Sparse.eval row1263 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1263, Integer.Sparse.eval_collectBalanced, rawRowCheck1263]

def rawRow1264 : Integer.Sparse Key := [(key1388, -6), (key1543, 2), (key1553, 2), (key1543, 2), (key1293, 6), (key1570, -2), (key1590, -2), (key1570, -2), (key1313, -2), (key1323, -2), (key1313, -2), (key1421, 2), (key1441, 2), (key1421, 2)]

theorem rawRowCheck1264 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block1.form4 = rawRow1264 := by decide +kernel

def row1264 : Integer.Sparse Key := [(key1293, 6), (key1313, -4), (key1323, -2), (key1388, -6), (key1421, 4), (key1441, 2), (key1543, 4), (key1553, 2), (key1570, -4), (key1590, -2)]

theorem rowCheck1264 : row1264 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1264 := by decide +kernel

theorem rowEval1264 (x : Key → ℝ) : Integer.Sparse.eval row1264 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1264, Integer.Sparse.eval_collectBalanced, rawRowCheck1264]

def rawRow1265 : Integer.Sparse Key := [(key1388, -6), (key1553, 2), (key1543, 2), (key1543, 2), (key1293, 6), (key1590, -2), (key1570, -2), (key1570, -2), (key1323, -2), (key1313, -2), (key1313, -2), (key1441, 2), (key1421, 2), (key1421, 2)]

theorem rawRowCheck1265 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block1.form4 = rawRow1265 := by decide +kernel

def row1265 : Integer.Sparse Key := [(key1293, 6), (key1313, -4), (key1323, -2), (key1388, -6), (key1421, 4), (key1441, 2), (key1543, 4), (key1553, 2), (key1570, -4), (key1590, -2)]

theorem rowCheck1265 : row1265 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1265 := by decide +kernel

theorem rowEval1265 (x : Key → ℝ) : Integer.Sparse.eval row1265 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1265, Integer.Sparse.eval_collectBalanced, rawRowCheck1265]

def rawRow1266 : Integer.Sparse Key := [(key1421, -6), (key1570, 2), (key1619, 2), (key1621, 2), (key1313, 6), (key1543, -2), (key1619, -2), (key1630, -2), (key1293, -2), (key1313, -2), (key1323, -2), (key1388, 2), (key1421, 2), (key1441, 2)]

theorem rawRowCheck1266 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block1.form4 = rawRow1266 := by decide +kernel

def row1266 : Integer.Sparse Key := [(key1293, -2), (key1313, 4), (key1323, -2), (key1388, 2), (key1421, -4), (key1441, 2), (key1543, -2), (key1570, 2), (key1621, 2), (key1630, -2)]

theorem rowCheck1266 : row1266 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1266 := by decide +kernel

theorem rowEval1266 (x : Key → ℝ) : Integer.Sparse.eval row1266 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1266, Integer.Sparse.eval_collectBalanced, rawRowCheck1266]

def rawRow1267 : Integer.Sparse Key := [(key1421, -6), (key1570, 2), (key1621, 2), (key1619, 2), (key1313, 6), (key1543, -2), (key1630, -2), (key1619, -2), (key1293, -2), (key1323, -2), (key1313, -2), (key1388, 2), (key1441, 2), (key1421, 2)]

theorem rawRowCheck1267 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block1.form4 = rawRow1267 := by decide +kernel

def row1267 : Integer.Sparse Key := [(key1293, -2), (key1313, 4), (key1323, -2), (key1388, 2), (key1421, -4), (key1441, 2), (key1543, -2), (key1570, 2), (key1621, 2), (key1630, -2)]

theorem rowCheck1267 : row1267 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1267 := by decide +kernel

theorem rowEval1267 (x : Key → ℝ) : Integer.Sparse.eval row1267 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1267, Integer.Sparse.eval_collectBalanced, rawRowCheck1267]

def rawRow1268 : Integer.Sparse Key := [(key1421, -6), (key1619, 2), (key1570, 2), (key1621, 2), (key1313, 6), (key1619, -2), (key1543, -2), (key1630, -2), (key1313, -2), (key1293, -2), (key1323, -2), (key1421, 2), (key1388, 2), (key1441, 2)]

theorem rawRowCheck1268 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block1.form4 = rawRow1268 := by decide +kernel

def row1268 : Integer.Sparse Key := [(key1293, -2), (key1313, 4), (key1323, -2), (key1388, 2), (key1421, -4), (key1441, 2), (key1543, -2), (key1570, 2), (key1621, 2), (key1630, -2)]

theorem rowCheck1268 : row1268 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1268 := by decide +kernel

theorem rowEval1268 (x : Key → ℝ) : Integer.Sparse.eval row1268 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1268, Integer.Sparse.eval_collectBalanced, rawRowCheck1268]

def rawRow1269 : Integer.Sparse Key := [(key1421, -6), (key1619, 2), (key1621, 2), (key1570, 2), (key1313, 6), (key1619, -2), (key1630, -2), (key1543, -2), (key1313, -2), (key1323, -2), (key1293, -2), (key1421, 2), (key1441, 2), (key1388, 2)]

theorem rawRowCheck1269 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block1.form4 = rawRow1269 := by decide +kernel

def row1269 : Integer.Sparse Key := [(key1293, -2), (key1313, 4), (key1323, -2), (key1388, 2), (key1421, -4), (key1441, 2), (key1543, -2), (key1570, 2), (key1621, 2), (key1630, -2)]

theorem rowCheck1269 : row1269 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1269 := by decide +kernel

theorem rowEval1269 (x : Key → ℝ) : Integer.Sparse.eval row1269 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1269, Integer.Sparse.eval_collectBalanced, rawRowCheck1269]

def rawRow1270 : Integer.Sparse Key := [(key1421, -6), (key1621, 2), (key1570, 2), (key1619, 2), (key1313, 6), (key1630, -2), (key1543, -2), (key1619, -2), (key1323, -2), (key1293, -2), (key1313, -2), (key1441, 2), (key1388, 2), (key1421, 2)]

theorem rawRowCheck1270 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block1.form4 = rawRow1270 := by decide +kernel

def row1270 : Integer.Sparse Key := [(key1293, -2), (key1313, 4), (key1323, -2), (key1388, 2), (key1421, -4), (key1441, 2), (key1543, -2), (key1570, 2), (key1621, 2), (key1630, -2)]

theorem rowCheck1270 : row1270 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1270 := by decide +kernel

theorem rowEval1270 (x : Key → ℝ) : Integer.Sparse.eval row1270 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1270, Integer.Sparse.eval_collectBalanced, rawRowCheck1270]

def rawRow1271 : Integer.Sparse Key := [(key1421, -6), (key1621, 2), (key1619, 2), (key1570, 2), (key1313, 6), (key1630, -2), (key1619, -2), (key1543, -2), (key1323, -2), (key1313, -2), (key1293, -2), (key1441, 2), (key1421, 2), (key1388, 2)]

theorem rawRowCheck1271 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block1.form4 = rawRow1271 := by decide +kernel

def row1271 : Integer.Sparse Key := [(key1293, -2), (key1313, 4), (key1323, -2), (key1388, 2), (key1421, -4), (key1441, 2), (key1543, -2), (key1570, 2), (key1621, 2), (key1630, -2)]

theorem rowCheck1271 : row1271 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1271 := by decide +kernel

theorem rowEval1271 (x : Key → ℝ) : Integer.Sparse.eval row1271 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1271, Integer.Sparse.eval_collectBalanced, rawRowCheck1271]

def rawRow1272 : Integer.Sparse Key := [(key316, -1), (key321, -1), (key316, -1), (key331, -1), (key321, -1), (key331, -1), (key346, 2), (key346, 2), (key347, 2), (key406, 1), (key411, 1), (key406, 1), (key421, 1), (key411, 1), (key421, 1), (key487, -1), (key488, -1), (key487, -1), (key489, -1), (key488, -1), (key489, -1), (key657, -2), (key657, -2), (key658, -2), (key660, 1), (key661, 1), (key660, 1), (key662, 1), (key661, 1), (key662, 1)]

theorem rawRowCheck1272 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block1.form5 = rawRow1272 := by decide +kernel

def row1272 : Integer.Sparse Key := [(key316, -2), (key321, -2), (key331, -2), (key346, 4), (key347, 2), (key406, 2), (key411, 2), (key421, 2), (key487, -2), (key488, -2), (key489, -2), (key657, -4), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

theorem rowCheck1272 : row1272 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1272 := by decide +kernel

theorem rowEval1272 (x : Key → ℝ) : Integer.Sparse.eval row1272 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block1.form5) x := by
  rw [rowCheck1272, Integer.Sparse.eval_collectBalanced, rawRowCheck1272]

def rawRow1273 : Integer.Sparse Key := [(key321, -1), (key316, -1), (key331, -1), (key316, -1), (key331, -1), (key321, -1), (key346, 2), (key347, 2), (key346, 2), (key411, 1), (key406, 1), (key421, 1), (key406, 1), (key421, 1), (key411, 1), (key488, -1), (key487, -1), (key489, -1), (key487, -1), (key489, -1), (key488, -1), (key657, -2), (key658, -2), (key657, -2), (key661, 1), (key660, 1), (key662, 1), (key660, 1), (key662, 1), (key661, 1)]

theorem rawRowCheck1273 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block1.form5 = rawRow1273 := by decide +kernel

def row1273 : Integer.Sparse Key := [(key316, -2), (key321, -2), (key331, -2), (key346, 4), (key347, 2), (key406, 2), (key411, 2), (key421, 2), (key487, -2), (key488, -2), (key489, -2), (key657, -4), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

theorem rowCheck1273 : row1273 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1273 := by decide +kernel

theorem rowEval1273 (x : Key → ℝ) : Integer.Sparse.eval row1273 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1273, Integer.Sparse.eval_collectBalanced, rawRowCheck1273]

def rawRow1274 : Integer.Sparse Key := [(key331, -1), (key331, -1), (key321, -1), (key321, -1), (key316, -1), (key316, -1), (key347, 2), (key346, 2), (key346, 2), (key421, 1), (key421, 1), (key411, 1), (key411, 1), (key406, 1), (key406, 1), (key489, -1), (key489, -1), (key488, -1), (key488, -1), (key487, -1), (key487, -1), (key658, -2), (key657, -2), (key657, -2), (key662, 1), (key662, 1), (key661, 1), (key661, 1), (key660, 1), (key660, 1)]

theorem rawRowCheck1274 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block1.form5 = rawRow1274 := by decide +kernel

def row1274 : Integer.Sparse Key := [(key316, -2), (key321, -2), (key331, -2), (key346, 4), (key347, 2), (key406, 2), (key411, 2), (key421, 2), (key487, -2), (key488, -2), (key489, -2), (key657, -4), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

theorem rowCheck1274 : row1274 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1274 := by decide +kernel

theorem rowEval1274 (x : Key → ℝ) : Integer.Sparse.eval row1274 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1274, Integer.Sparse.eval_collectBalanced, rawRowCheck1274]

def rawRow1275 : Integer.Sparse Key := [(key302, -1), (key307, -1), (key316, -1), (key331, -1), (key346, -1), (key347, -1), (key307, 2), (key321, 2), (key331, 2), (key385, 1), (key390, 1), (key435, 1), (key453, 1), (key487, 1), (key489, 1), (key390, -1), (key400, -1), (key411, -1), (key421, -1), (key445, -1), (key453, -1), (key655, -2), (key660, -2), (key662, -2), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key661, 1), (key662, 1)]

theorem rawRowCheck1275 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block1.form5 = rawRow1275 := by decide +kernel

def row1275 : Integer.Sparse Key := [(key302, -1), (key307, 1), (key316, -1), (key321, 2), (key331, 1), (key346, -1), (key347, -1), (key385, 1), (key400, -1), (key411, -1), (key421, -1), (key435, 1), (key445, -1), (key487, 1), (key489, 1), (key655, -1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, 1), (key662, -1)]

theorem rowCheck1275 : row1275 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1275 := by decide +kernel

theorem rowEval1275 (x : Key → ℝ) : Integer.Sparse.eval row1275 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block1.form5) x := by
  rw [rowCheck1275, Integer.Sparse.eval_collectBalanced, rawRowCheck1275]

def rawRow1276 : Integer.Sparse Key := [(key307, -1), (key302, -1), (key331, -1), (key316, -1), (key347, -1), (key346, -1), (key307, 2), (key331, 2), (key321, 2), (key390, 1), (key385, 1), (key453, 1), (key435, 1), (key489, 1), (key487, 1), (key400, -1), (key390, -1), (key421, -1), (key411, -1), (key453, -1), (key445, -1), (key655, -2), (key662, -2), (key660, -2), (key656, 1), (key655, 1), (key658, 1), (key657, 1), (key662, 1), (key661, 1)]

theorem rawRowCheck1276 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block1.form5 = rawRow1276 := by decide +kernel

def row1276 : Integer.Sparse Key := [(key302, -1), (key307, 1), (key316, -1), (key321, 2), (key331, 1), (key346, -1), (key347, -1), (key385, 1), (key400, -1), (key411, -1), (key421, -1), (key435, 1), (key445, -1), (key487, 1), (key489, 1), (key655, -1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, 1), (key662, -1)]

theorem rowCheck1276 : row1276 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1276 := by decide +kernel

theorem rowEval1276 (x : Key → ℝ) : Integer.Sparse.eval row1276 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1276, Integer.Sparse.eval_collectBalanced, rawRowCheck1276]

def rawRow1277 : Integer.Sparse Key := [(key316, -1), (key346, -1), (key302, -1), (key347, -1), (key307, -1), (key331, -1), (key321, 2), (key307, 2), (key331, 2), (key435, 1), (key487, 1), (key385, 1), (key489, 1), (key390, 1), (key453, 1), (key411, -1), (key445, -1), (key390, -1), (key453, -1), (key400, -1), (key421, -1), (key660, -2), (key655, -2), (key662, -2), (key657, 1), (key661, 1), (key655, 1), (key662, 1), (key656, 1), (key658, 1)]

theorem rawRowCheck1277 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block1.form5 = rawRow1277 := by decide +kernel

def row1277 : Integer.Sparse Key := [(key302, -1), (key307, 1), (key316, -1), (key321, 2), (key331, 1), (key346, -1), (key347, -1), (key385, 1), (key400, -1), (key411, -1), (key421, -1), (key435, 1), (key445, -1), (key487, 1), (key489, 1), (key655, -1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, 1), (key662, -1)]

theorem rowCheck1277 : row1277 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1277 := by decide +kernel

theorem rowEval1277 (x : Key → ℝ) : Integer.Sparse.eval row1277 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block1.form5) x := by
  rw [rowCheck1277, Integer.Sparse.eval_collectBalanced, rawRowCheck1277]

def rawRow1278 : Integer.Sparse Key := [(key346, -1), (key316, -1), (key347, -1), (key302, -1), (key331, -1), (key307, -1), (key321, 2), (key331, 2), (key307, 2), (key487, 1), (key435, 1), (key489, 1), (key385, 1), (key453, 1), (key390, 1), (key445, -1), (key411, -1), (key453, -1), (key390, -1), (key421, -1), (key400, -1), (key660, -2), (key662, -2), (key655, -2), (key661, 1), (key657, 1), (key662, 1), (key655, 1), (key658, 1), (key656, 1)]

theorem rawRowCheck1278 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block1.form5 = rawRow1278 := by decide +kernel

def row1278 : Integer.Sparse Key := [(key302, -1), (key307, 1), (key316, -1), (key321, 2), (key331, 1), (key346, -1), (key347, -1), (key385, 1), (key400, -1), (key411, -1), (key421, -1), (key435, 1), (key445, -1), (key487, 1), (key489, 1), (key655, -1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, 1), (key662, -1)]

theorem rowCheck1278 : row1278 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1278 := by decide +kernel

theorem rowEval1278 (x : Key → ℝ) : Integer.Sparse.eval row1278 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1278, Integer.Sparse.eval_collectBalanced, rawRowCheck1278]

def rawRow1279 : Integer.Sparse Key := [(key331, -1), (key347, -1), (key307, -1), (key346, -1), (key302, -1), (key316, -1), (key331, 2), (key307, 2), (key321, 2), (key453, 1), (key489, 1), (key390, 1), (key487, 1), (key385, 1), (key435, 1), (key421, -1), (key453, -1), (key400, -1), (key445, -1), (key390, -1), (key411, -1), (key662, -2), (key655, -2), (key660, -2), (key658, 1), (key662, 1), (key656, 1), (key661, 1), (key655, 1), (key657, 1)]

theorem rawRowCheck1279 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block1.form5 = rawRow1279 := by decide +kernel

def row1279 : Integer.Sparse Key := [(key302, -1), (key307, 1), (key316, -1), (key321, 2), (key331, 1), (key346, -1), (key347, -1), (key385, 1), (key400, -1), (key411, -1), (key421, -1), (key435, 1), (key445, -1), (key487, 1), (key489, 1), (key655, -1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, 1), (key662, -1)]

theorem rowCheck1279 : row1279 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1279 := by decide +kernel

theorem rowEval1279 (x : Key → ℝ) : Integer.Sparse.eval row1279 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1279, Integer.Sparse.eval_collectBalanced, rawRowCheck1279]

end MUB6.Certificate.GramRows

end OAI
