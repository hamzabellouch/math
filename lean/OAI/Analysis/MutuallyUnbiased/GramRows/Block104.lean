import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block6
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow10240 : Integer.Sparse Key := [(key1173, 6), (key1246, 6), (key1166, 6), (key1173, 6), (key1095, -6), (key1166, -6), (key981, -6), (key1095, -6)]

theorem rawRowCheck10240 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form12 = rawRow10240 := by decide +kernel

def row10240 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1173, 12), (key1246, 6)]

theorem rowCheck10240 : row10240 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10240 := by decide +kernel

theorem rowEval10240 (x : Key → ℝ) : Integer.Sparse.eval row10240 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck10240, Integer.Sparse.eval_collectBalanced, rawRowCheck10240]

def rawRow10241 : Integer.Sparse Key := [(key1246, 6), (key1173, 6), (key1166, 6), (key1173, 6), (key1095, -6), (key1166, -6), (key1095, -6), (key981, -6)]

theorem rawRowCheck10241 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form12 = rawRow10241 := by decide +kernel

def row10241 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1173, 12), (key1246, 6)]

theorem rowCheck10241 : row10241 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10241 := by decide +kernel

theorem rowEval10241 (x : Key → ℝ) : Integer.Sparse.eval row10241 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form12) x := by
  rw [rowCheck10241, Integer.Sparse.eval_collectBalanced, rawRowCheck10241]

def rawRow10242 : Integer.Sparse Key := [(key1173, 6), (key1173, 6), (key1246, 6), (key1166, 6), (key1166, -6), (key981, -6), (key1095, -6), (key1095, -6)]

theorem rawRowCheck10242 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form12 = rawRow10242 := by decide +kernel

def row10242 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1173, 12), (key1246, 6)]

theorem rowCheck10242 : row10242 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10242 := by decide +kernel

theorem rowEval10242 (x : Key → ℝ) : Integer.Sparse.eval row10242 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck10242, Integer.Sparse.eval_collectBalanced, rawRowCheck10242]

def rawRow10243 : Integer.Sparse Key := [(key1173, 6), (key1246, 6), (key1173, 6), (key1166, 6), (key1166, -6), (key1095, -6), (key981, -6), (key1095, -6)]

theorem rawRowCheck10243 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form12 = rawRow10243 := by decide +kernel

def row10243 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1173, 12), (key1246, 6)]

theorem rowCheck10243 : row10243 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10243 := by decide +kernel

theorem rowEval10243 (x : Key → ℝ) : Integer.Sparse.eval row10243 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck10243, Integer.Sparse.eval_collectBalanced, rawRowCheck10243]

def rawRow10244 : Integer.Sparse Key := [(key1246, 6), (key1173, 6), (key1173, 6), (key1166, 6), (key1166, -6), (key1095, -6), (key1095, -6), (key981, -6)]

theorem rawRowCheck10244 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form12 = rawRow10244 := by decide +kernel

def row10244 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1173, 12), (key1246, 6)]

theorem rowCheck10244 : row10244 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10244 := by decide +kernel

theorem rowEval10244 (x : Key → ℝ) : Integer.Sparse.eval row10244 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form12) x := by
  rw [rowCheck10244, Integer.Sparse.eval_collectBalanced, rawRowCheck10244]

def rawRow10245 : Integer.Sparse Key := [(key891, -6), (key891, -6), (key895, -6), (key916, -6), (key714, 2), (key714, 2), (key718, 2), (key891, 2), (key891, 2), (key947, 2), (key947, 2), (key948, 2), (key948, 2), (key916, 2), (key955, 2), (key955, 2)]

theorem rawRowCheck10245 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form13 = rawRow10245 := by decide +kernel

def row10245 : Integer.Sparse Key := [(key714, 4), (key718, 2), (key891, -8), (key895, -6), (key916, -4), (key947, 4), (key948, 4), (key955, 4)]

theorem rowCheck10245 : row10245 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10245 := by decide +kernel

theorem rowEval10245 (x : Key → ℝ) : Integer.Sparse.eval row10245 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck10245, Integer.Sparse.eval_collectBalanced, rawRowCheck10245]

def rawRow10246 : Integer.Sparse Key := [(key891, -6), (key895, -6), (key891, -6), (key916, -6), (key714, 2), (key718, 2), (key714, 2), (key947, 2), (key948, 2), (key891, 2), (key948, 2), (key891, 2), (key947, 2), (key955, 2), (key916, 2), (key955, 2)]

theorem rawRowCheck10246 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form13 = rawRow10246 := by decide +kernel

def row10246 : Integer.Sparse Key := [(key714, 4), (key718, 2), (key891, -8), (key895, -6), (key916, -4), (key947, 4), (key948, 4), (key955, 4)]

theorem rowCheck10246 : row10246 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10246 := by decide +kernel

theorem rowEval10246 (x : Key → ℝ) : Integer.Sparse.eval row10246 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck10246, Integer.Sparse.eval_collectBalanced, rawRowCheck10246]

def rawRow10247 : Integer.Sparse Key := [(key895, -6), (key891, -6), (key891, -6), (key916, -6), (key718, 2), (key714, 2), (key714, 2), (key948, 2), (key947, 2), (key948, 2), (key891, 2), (key947, 2), (key891, 2), (key955, 2), (key955, 2), (key916, 2)]

theorem rawRowCheck10247 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form13 = rawRow10247 := by decide +kernel

def row10247 : Integer.Sparse Key := [(key714, 4), (key718, 2), (key891, -8), (key895, -6), (key916, -4), (key947, 4), (key948, 4), (key955, 4)]

theorem rowCheck10247 : row10247 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10247 := by decide +kernel

theorem rowEval10247 (x : Key → ℝ) : Integer.Sparse.eval row10247 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck10247, Integer.Sparse.eval_collectBalanced, rawRowCheck10247]

def rawRow10248 : Integer.Sparse Key := [(key891, -6), (key891, -6), (key916, -6), (key895, -6), (key891, 2), (key891, 2), (key916, 2), (key714, 2), (key714, 2), (key947, 2), (key947, 2), (key955, 2), (key955, 2), (key718, 2), (key948, 2), (key948, 2)]

theorem rawRowCheck10248 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form13 = rawRow10248 := by decide +kernel

def row10248 : Integer.Sparse Key := [(key714, 4), (key718, 2), (key891, -8), (key895, -6), (key916, -4), (key947, 4), (key948, 4), (key955, 4)]

theorem rowCheck10248 : row10248 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10248 := by decide +kernel

theorem rowEval10248 (x : Key → ℝ) : Integer.Sparse.eval row10248 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck10248, Integer.Sparse.eval_collectBalanced, rawRowCheck10248]

def rawRow10249 : Integer.Sparse Key := [(key891, -6), (key916, -6), (key891, -6), (key895, -6), (key891, 2), (key916, 2), (key891, 2), (key947, 2), (key955, 2), (key714, 2), (key955, 2), (key714, 2), (key947, 2), (key948, 2), (key718, 2), (key948, 2)]

theorem rawRowCheck10249 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form13 = rawRow10249 := by decide +kernel

def row10249 : Integer.Sparse Key := [(key714, 4), (key718, 2), (key891, -8), (key895, -6), (key916, -4), (key947, 4), (key948, 4), (key955, 4)]

theorem rowCheck10249 : row10249 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10249 := by decide +kernel

theorem rowEval10249 (x : Key → ℝ) : Integer.Sparse.eval row10249 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck10249, Integer.Sparse.eval_collectBalanced, rawRowCheck10249]

def rawRow10250 : Integer.Sparse Key := [(key916, -6), (key891, -6), (key891, -6), (key895, -6), (key916, 2), (key891, 2), (key891, 2), (key955, 2), (key947, 2), (key955, 2), (key714, 2), (key947, 2), (key714, 2), (key948, 2), (key948, 2), (key718, 2)]

theorem rawRowCheck10250 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form13 = rawRow10250 := by decide +kernel

def row10250 : Integer.Sparse Key := [(key714, 4), (key718, 2), (key891, -8), (key895, -6), (key916, -4), (key947, 4), (key948, 4), (key955, 4)]

theorem rowCheck10250 : row10250 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10250 := by decide +kernel

theorem rowEval10250 (x : Key → ℝ) : Integer.Sparse.eval row10250 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form13) x := by
  rw [rowCheck10250, Integer.Sparse.eval_collectBalanced, rawRowCheck10250]

def rawRow10251 : Integer.Sparse Key := [(key891, -6), (key895, -6), (key916, -6), (key891, -6), (key947, 2), (key948, 2), (key955, 2), (key714, 2), (key718, 2), (key891, 2), (key948, 2), (key916, 2), (key955, 2), (key714, 2), (key891, 2), (key947, 2)]

theorem rawRowCheck10251 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form13 = rawRow10251 := by decide +kernel

def row10251 : Integer.Sparse Key := [(key714, 4), (key718, 2), (key891, -8), (key895, -6), (key916, -4), (key947, 4), (key948, 4), (key955, 4)]

theorem rowCheck10251 : row10251 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10251 := by decide +kernel

theorem rowEval10251 (x : Key → ℝ) : Integer.Sparse.eval row10251 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck10251, Integer.Sparse.eval_collectBalanced, rawRowCheck10251]

def rawRow10252 : Integer.Sparse Key := [(key895, -6), (key891, -6), (key916, -6), (key891, -6), (key948, 2), (key947, 2), (key955, 2), (key718, 2), (key714, 2), (key948, 2), (key891, 2), (key955, 2), (key916, 2), (key714, 2), (key947, 2), (key891, 2)]

theorem rawRowCheck10252 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form13 = rawRow10252 := by decide +kernel

def row10252 : Integer.Sparse Key := [(key714, 4), (key718, 2), (key891, -8), (key895, -6), (key916, -4), (key947, 4), (key948, 4), (key955, 4)]

theorem rowCheck10252 : row10252 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10252 := by decide +kernel

theorem rowEval10252 (x : Key → ℝ) : Integer.Sparse.eval row10252 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck10252, Integer.Sparse.eval_collectBalanced, rawRowCheck10252]

def rawRow10253 : Integer.Sparse Key := [(key891, -6), (key916, -6), (key895, -6), (key891, -6), (key947, 2), (key955, 2), (key948, 2), (key891, 2), (key916, 2), (key714, 2), (key955, 2), (key718, 2), (key948, 2), (key891, 2), (key714, 2), (key947, 2)]

theorem rawRowCheck10253 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form13 = rawRow10253 := by decide +kernel

def row10253 : Integer.Sparse Key := [(key714, 4), (key718, 2), (key891, -8), (key895, -6), (key916, -4), (key947, 4), (key948, 4), (key955, 4)]

theorem rowCheck10253 : row10253 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10253 := by decide +kernel

theorem rowEval10253 (x : Key → ℝ) : Integer.Sparse.eval row10253 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck10253, Integer.Sparse.eval_collectBalanced, rawRowCheck10253]

def rawRow10254 : Integer.Sparse Key := [(key916, -6), (key891, -6), (key895, -6), (key891, -6), (key955, 2), (key947, 2), (key948, 2), (key916, 2), (key891, 2), (key955, 2), (key714, 2), (key948, 2), (key718, 2), (key891, 2), (key947, 2), (key714, 2)]

theorem rawRowCheck10254 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form13 = rawRow10254 := by decide +kernel

def row10254 : Integer.Sparse Key := [(key714, 4), (key718, 2), (key891, -8), (key895, -6), (key916, -4), (key947, 4), (key948, 4), (key955, 4)]

theorem rowCheck10254 : row10254 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10254 := by decide +kernel

theorem rowEval10254 (x : Key → ℝ) : Integer.Sparse.eval row10254 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form13) x := by
  rw [rowCheck10254, Integer.Sparse.eval_collectBalanced, rawRowCheck10254]

def rawRow10255 : Integer.Sparse Key := [(key895, -6), (key916, -6), (key891, -6), (key891, -6), (key948, 2), (key955, 2), (key947, 2), (key948, 2), (key955, 2), (key718, 2), (key916, 2), (key714, 2), (key891, 2), (key947, 2), (key714, 2), (key891, 2)]

theorem rawRowCheck10255 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form13 = rawRow10255 := by decide +kernel

def row10255 : Integer.Sparse Key := [(key714, 4), (key718, 2), (key891, -8), (key895, -6), (key916, -4), (key947, 4), (key948, 4), (key955, 4)]

theorem rowCheck10255 : row10255 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10255 := by decide +kernel

theorem rowEval10255 (x : Key → ℝ) : Integer.Sparse.eval row10255 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck10255, Integer.Sparse.eval_collectBalanced, rawRowCheck10255]

def rawRow10256 : Integer.Sparse Key := [(key916, -6), (key895, -6), (key891, -6), (key891, -6), (key955, 2), (key948, 2), (key947, 2), (key955, 2), (key948, 2), (key916, 2), (key718, 2), (key891, 2), (key714, 2), (key947, 2), (key891, 2), (key714, 2)]

theorem rawRowCheck10256 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form13 = rawRow10256 := by decide +kernel

def row10256 : Integer.Sparse Key := [(key714, 4), (key718, 2), (key891, -8), (key895, -6), (key916, -4), (key947, 4), (key948, 4), (key955, 4)]

theorem rowCheck10256 : row10256 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10256 := by decide +kernel

theorem rowEval10256 (x : Key → ℝ) : Integer.Sparse.eval row10256 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form13) x := by
  rw [rowCheck10256, Integer.Sparse.eval_collectBalanced, rawRowCheck10256]

def rawRow10257 : Integer.Sparse Key := [(key947, -6), (key948, -6), (key948, -6), (key955, -6), (key714, 2), (key718, 2), (key718, 2), (key891, 2), (key895, 2), (key891, 2), (key948, 2), (key895, 2), (key948, 2), (key916, 2), (key916, 2), (key955, 2)]

theorem rawRowCheck10257 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form13 = rawRow10257 := by decide +kernel

def row10257 : Integer.Sparse Key := [(key714, 2), (key718, 4), (key891, 4), (key895, 4), (key916, 4), (key947, -6), (key948, -8), (key955, -4)]

theorem rowCheck10257 : row10257 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10257 := by decide +kernel

theorem rowEval10257 (x : Key → ℝ) : Integer.Sparse.eval row10257 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck10257, Integer.Sparse.eval_collectBalanced, rawRowCheck10257]

def rawRow10258 : Integer.Sparse Key := [(key948, -6), (key947, -6), (key948, -6), (key955, -6), (key718, 2), (key714, 2), (key718, 2), (key895, 2), (key891, 2), (key948, 2), (key891, 2), (key948, 2), (key895, 2), (key916, 2), (key955, 2), (key916, 2)]

theorem rawRowCheck10258 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form13 = rawRow10258 := by decide +kernel

def row10258 : Integer.Sparse Key := [(key714, 2), (key718, 4), (key891, 4), (key895, 4), (key916, 4), (key947, -6), (key948, -8), (key955, -4)]

theorem rowCheck10258 : row10258 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10258 := by decide +kernel

theorem rowEval10258 (x : Key → ℝ) : Integer.Sparse.eval row10258 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck10258, Integer.Sparse.eval_collectBalanced, rawRowCheck10258]

def rawRow10259 : Integer.Sparse Key := [(key948, -6), (key948, -6), (key947, -6), (key955, -6), (key718, 2), (key718, 2), (key714, 2), (key948, 2), (key948, 2), (key895, 2), (key895, 2), (key891, 2), (key891, 2), (key955, 2), (key916, 2), (key916, 2)]

theorem rawRowCheck10259 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form13 = rawRow10259 := by decide +kernel

def row10259 : Integer.Sparse Key := [(key714, 2), (key718, 4), (key891, 4), (key895, 4), (key916, 4), (key947, -6), (key948, -8), (key955, -4)]

theorem rowCheck10259 : row10259 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10259 := by decide +kernel

theorem rowEval10259 (x : Key → ℝ) : Integer.Sparse.eval row10259 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck10259, Integer.Sparse.eval_collectBalanced, rawRowCheck10259]

def rawRow10260 : Integer.Sparse Key := [(key947, -6), (key948, -6), (key955, -6), (key948, -6), (key891, 2), (key895, 2), (key916, 2), (key714, 2), (key718, 2), (key891, 2), (key948, 2), (key916, 2), (key955, 2), (key718, 2), (key895, 2), (key948, 2)]

theorem rawRowCheck10260 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form13 = rawRow10260 := by decide +kernel

def row10260 : Integer.Sparse Key := [(key714, 2), (key718, 4), (key891, 4), (key895, 4), (key916, 4), (key947, -6), (key948, -8), (key955, -4)]

theorem rowCheck10260 : row10260 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10260 := by decide +kernel

theorem rowEval10260 (x : Key → ℝ) : Integer.Sparse.eval row10260 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck10260, Integer.Sparse.eval_collectBalanced, rawRowCheck10260]

def rawRow10261 : Integer.Sparse Key := [(key948, -6), (key947, -6), (key955, -6), (key948, -6), (key895, 2), (key891, 2), (key916, 2), (key718, 2), (key714, 2), (key948, 2), (key891, 2), (key955, 2), (key916, 2), (key718, 2), (key948, 2), (key895, 2)]

theorem rawRowCheck10261 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form13 = rawRow10261 := by decide +kernel

def row10261 : Integer.Sparse Key := [(key714, 2), (key718, 4), (key891, 4), (key895, 4), (key916, 4), (key947, -6), (key948, -8), (key955, -4)]

theorem rowCheck10261 : row10261 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10261 := by decide +kernel

theorem rowEval10261 (x : Key → ℝ) : Integer.Sparse.eval row10261 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck10261, Integer.Sparse.eval_collectBalanced, rawRowCheck10261]

def rawRow10262 : Integer.Sparse Key := [(key947, -6), (key955, -6), (key948, -6), (key948, -6), (key891, 2), (key916, 2), (key895, 2), (key891, 2), (key916, 2), (key714, 2), (key955, 2), (key718, 2), (key948, 2), (key895, 2), (key718, 2), (key948, 2)]

theorem rawRowCheck10262 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form13 = rawRow10262 := by decide +kernel

def row10262 : Integer.Sparse Key := [(key714, 2), (key718, 4), (key891, 4), (key895, 4), (key916, 4), (key947, -6), (key948, -8), (key955, -4)]

theorem rowCheck10262 : row10262 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10262 := by decide +kernel

theorem rowEval10262 (x : Key → ℝ) : Integer.Sparse.eval row10262 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck10262, Integer.Sparse.eval_collectBalanced, rawRowCheck10262]

def rawRow10263 : Integer.Sparse Key := [(key955, -6), (key947, -6), (key948, -6), (key948, -6), (key916, 2), (key891, 2), (key895, 2), (key916, 2), (key891, 2), (key955, 2), (key714, 2), (key948, 2), (key718, 2), (key895, 2), (key948, 2), (key718, 2)]

theorem rawRowCheck10263 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form13 = rawRow10263 := by decide +kernel

def row10263 : Integer.Sparse Key := [(key714, 2), (key718, 4), (key891, 4), (key895, 4), (key916, 4), (key947, -6), (key948, -8), (key955, -4)]

theorem rowCheck10263 : row10263 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10263 := by decide +kernel

theorem rowEval10263 (x : Key → ℝ) : Integer.Sparse.eval row10263 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form13) x := by
  rw [rowCheck10263, Integer.Sparse.eval_collectBalanced, rawRowCheck10263]

def rawRow10264 : Integer.Sparse Key := [(key948, -6), (key955, -6), (key947, -6), (key948, -6), (key895, 2), (key916, 2), (key891, 2), (key948, 2), (key955, 2), (key718, 2), (key916, 2), (key714, 2), (key891, 2), (key948, 2), (key718, 2), (key895, 2)]

theorem rawRowCheck10264 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form13 = rawRow10264 := by decide +kernel

def row10264 : Integer.Sparse Key := [(key714, 2), (key718, 4), (key891, 4), (key895, 4), (key916, 4), (key947, -6), (key948, -8), (key955, -4)]

theorem rowCheck10264 : row10264 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10264 := by decide +kernel

theorem rowEval10264 (x : Key → ℝ) : Integer.Sparse.eval row10264 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck10264, Integer.Sparse.eval_collectBalanced, rawRowCheck10264]

def rawRow10265 : Integer.Sparse Key := [(key955, -6), (key948, -6), (key947, -6), (key948, -6), (key916, 2), (key895, 2), (key891, 2), (key955, 2), (key948, 2), (key916, 2), (key718, 2), (key891, 2), (key714, 2), (key948, 2), (key895, 2), (key718, 2)]

theorem rawRowCheck10265 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form13 = rawRow10265 := by decide +kernel

def row10265 : Integer.Sparse Key := [(key714, 2), (key718, 4), (key891, 4), (key895, 4), (key916, 4), (key947, -6), (key948, -8), (key955, -4)]

theorem rowCheck10265 : row10265 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10265 := by decide +kernel

theorem rowEval10265 (x : Key → ℝ) : Integer.Sparse.eval row10265 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form13) x := by
  rw [rowCheck10265, Integer.Sparse.eval_collectBalanced, rawRowCheck10265]

def rawRow10266 : Integer.Sparse Key := [(key948, -6), (key948, -6), (key955, -6), (key947, -6), (key948, 2), (key948, 2), (key955, 2), (key718, 2), (key718, 2), (key895, 2), (key895, 2), (key916, 2), (key916, 2), (key714, 2), (key891, 2), (key891, 2)]

theorem rawRowCheck10266 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form13 = rawRow10266 := by decide +kernel

def row10266 : Integer.Sparse Key := [(key714, 2), (key718, 4), (key891, 4), (key895, 4), (key916, 4), (key947, -6), (key948, -8), (key955, -4)]

theorem rowCheck10266 : row10266 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10266 := by decide +kernel

theorem rowEval10266 (x : Key → ℝ) : Integer.Sparse.eval row10266 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck10266, Integer.Sparse.eval_collectBalanced, rawRowCheck10266]

def rawRow10267 : Integer.Sparse Key := [(key948, -6), (key955, -6), (key948, -6), (key947, -6), (key948, 2), (key955, 2), (key948, 2), (key895, 2), (key916, 2), (key718, 2), (key916, 2), (key718, 2), (key895, 2), (key891, 2), (key714, 2), (key891, 2)]

theorem rawRowCheck10267 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form13 = rawRow10267 := by decide +kernel

def row10267 : Integer.Sparse Key := [(key714, 2), (key718, 4), (key891, 4), (key895, 4), (key916, 4), (key947, -6), (key948, -8), (key955, -4)]

theorem rowCheck10267 : row10267 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10267 := by decide +kernel

theorem rowEval10267 (x : Key → ℝ) : Integer.Sparse.eval row10267 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck10267, Integer.Sparse.eval_collectBalanced, rawRowCheck10267]

def rawRow10268 : Integer.Sparse Key := [(key955, -6), (key948, -6), (key948, -6), (key947, -6), (key955, 2), (key948, 2), (key948, 2), (key916, 2), (key895, 2), (key916, 2), (key718, 2), (key895, 2), (key718, 2), (key891, 2), (key891, 2), (key714, 2)]

theorem rawRowCheck10268 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form13 = rawRow10268 := by decide +kernel

def row10268 : Integer.Sparse Key := [(key714, 2), (key718, 4), (key891, 4), (key895, 4), (key916, 4), (key947, -6), (key948, -8), (key955, -4)]

theorem rowCheck10268 : row10268 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10268 := by decide +kernel

theorem rowEval10268 (x : Key → ℝ) : Integer.Sparse.eval row10268 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form13) x := by
  rw [rowCheck10268, Integer.Sparse.eval_collectBalanced, rawRowCheck10268]

def rawRow10269 : Integer.Sparse Key := [(key88, 6), (key88, 6), (key94, 6), (key156, 6), (key14, -6), (key97, -6), (key161, -6), (key161, -6)]

theorem rawRowCheck10269 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form14 = rawRow10269 := by decide +kernel

def row10269 : Integer.Sparse Key := [(key14, -6), (key88, 12), (key94, 6), (key97, -6), (key156, 6), (key161, -12)]

theorem rowCheck10269 : row10269 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10269 := by decide +kernel

theorem rowEval10269 (x : Key → ℝ) : Integer.Sparse.eval row10269 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck10269, Integer.Sparse.eval_collectBalanced, rawRowCheck10269]

def rawRow10270 : Integer.Sparse Key := [(key88, 6), (key94, 6), (key88, 6), (key156, 6), (key14, -6), (key161, -6), (key97, -6), (key161, -6)]

theorem rawRowCheck10270 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form14 = rawRow10270 := by decide +kernel

def row10270 : Integer.Sparse Key := [(key14, -6), (key88, 12), (key94, 6), (key97, -6), (key156, 6), (key161, -12)]

theorem rowCheck10270 : row10270 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10270 := by decide +kernel

theorem rowEval10270 (x : Key → ℝ) : Integer.Sparse.eval row10270 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck10270, Integer.Sparse.eval_collectBalanced, rawRowCheck10270]

def rawRow10271 : Integer.Sparse Key := [(key94, 6), (key88, 6), (key88, 6), (key156, 6), (key14, -6), (key161, -6), (key161, -6), (key97, -6)]

theorem rawRowCheck10271 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form14 = rawRow10271 := by decide +kernel

def row10271 : Integer.Sparse Key := [(key14, -6), (key88, 12), (key94, 6), (key97, -6), (key156, 6), (key161, -12)]

theorem rowCheck10271 : row10271 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10271 := by decide +kernel

theorem rowEval10271 (x : Key → ℝ) : Integer.Sparse.eval row10271 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck10271, Integer.Sparse.eval_collectBalanced, rawRowCheck10271]

def rawRow10272 : Integer.Sparse Key := [(key88, 6), (key88, 6), (key156, 6), (key94, 6), (key97, -6), (key14, -6), (key161, -6), (key161, -6)]

theorem rawRowCheck10272 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form14 = rawRow10272 := by decide +kernel

def row10272 : Integer.Sparse Key := [(key14, -6), (key88, 12), (key94, 6), (key97, -6), (key156, 6), (key161, -12)]

theorem rowCheck10272 : row10272 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10272 := by decide +kernel

theorem rowEval10272 (x : Key → ℝ) : Integer.Sparse.eval row10272 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck10272, Integer.Sparse.eval_collectBalanced, rawRowCheck10272]

def rawRow10273 : Integer.Sparse Key := [(key88, 6), (key156, 6), (key88, 6), (key94, 6), (key97, -6), (key161, -6), (key14, -6), (key161, -6)]

theorem rawRowCheck10273 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form14 = rawRow10273 := by decide +kernel

def row10273 : Integer.Sparse Key := [(key14, -6), (key88, 12), (key94, 6), (key97, -6), (key156, 6), (key161, -12)]

theorem rowCheck10273 : row10273 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10273 := by decide +kernel

theorem rowEval10273 (x : Key → ℝ) : Integer.Sparse.eval row10273 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck10273, Integer.Sparse.eval_collectBalanced, rawRowCheck10273]

def rawRow10274 : Integer.Sparse Key := [(key156, 6), (key88, 6), (key88, 6), (key94, 6), (key97, -6), (key161, -6), (key161, -6), (key14, -6)]

theorem rawRowCheck10274 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form14 = rawRow10274 := by decide +kernel

def row10274 : Integer.Sparse Key := [(key14, -6), (key88, 12), (key94, 6), (key97, -6), (key156, 6), (key161, -12)]

theorem rowCheck10274 : row10274 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10274 := by decide +kernel

theorem rowEval10274 (x : Key → ℝ) : Integer.Sparse.eval row10274 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form14) x := by
  rw [rowCheck10274, Integer.Sparse.eval_collectBalanced, rawRowCheck10274]

def rawRow10275 : Integer.Sparse Key := [(key88, 6), (key94, 6), (key156, 6), (key88, 6), (key161, -6), (key14, -6), (key97, -6), (key161, -6)]

theorem rawRowCheck10275 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form14 = rawRow10275 := by decide +kernel

def row10275 : Integer.Sparse Key := [(key14, -6), (key88, 12), (key94, 6), (key97, -6), (key156, 6), (key161, -12)]

theorem rowCheck10275 : row10275 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10275 := by decide +kernel

theorem rowEval10275 (x : Key → ℝ) : Integer.Sparse.eval row10275 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck10275, Integer.Sparse.eval_collectBalanced, rawRowCheck10275]

def rawRow10276 : Integer.Sparse Key := [(key94, 6), (key88, 6), (key156, 6), (key88, 6), (key161, -6), (key14, -6), (key161, -6), (key97, -6)]

theorem rawRowCheck10276 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form14 = rawRow10276 := by decide +kernel

def row10276 : Integer.Sparse Key := [(key14, -6), (key88, 12), (key94, 6), (key97, -6), (key156, 6), (key161, -12)]

theorem rowCheck10276 : row10276 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10276 := by decide +kernel

theorem rowEval10276 (x : Key → ℝ) : Integer.Sparse.eval row10276 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck10276, Integer.Sparse.eval_collectBalanced, rawRowCheck10276]

def rawRow10277 : Integer.Sparse Key := [(key88, 6), (key156, 6), (key94, 6), (key88, 6), (key161, -6), (key97, -6), (key14, -6), (key161, -6)]

theorem rawRowCheck10277 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form14 = rawRow10277 := by decide +kernel

def row10277 : Integer.Sparse Key := [(key14, -6), (key88, 12), (key94, 6), (key97, -6), (key156, 6), (key161, -12)]

theorem rowCheck10277 : row10277 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10277 := by decide +kernel

theorem rowEval10277 (x : Key → ℝ) : Integer.Sparse.eval row10277 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck10277, Integer.Sparse.eval_collectBalanced, rawRowCheck10277]

def rawRow10278 : Integer.Sparse Key := [(key156, 6), (key88, 6), (key94, 6), (key88, 6), (key161, -6), (key97, -6), (key161, -6), (key14, -6)]

theorem rawRowCheck10278 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form14 = rawRow10278 := by decide +kernel

def row10278 : Integer.Sparse Key := [(key14, -6), (key88, 12), (key94, 6), (key97, -6), (key156, 6), (key161, -12)]

theorem rowCheck10278 : row10278 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10278 := by decide +kernel

theorem rowEval10278 (x : Key → ℝ) : Integer.Sparse.eval row10278 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form14) x := by
  rw [rowCheck10278, Integer.Sparse.eval_collectBalanced, rawRowCheck10278]

def rawRow10279 : Integer.Sparse Key := [(key94, 6), (key156, 6), (key88, 6), (key88, 6), (key161, -6), (key161, -6), (key14, -6), (key97, -6)]

theorem rawRowCheck10279 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form14 = rawRow10279 := by decide +kernel

def row10279 : Integer.Sparse Key := [(key14, -6), (key88, 12), (key94, 6), (key97, -6), (key156, 6), (key161, -12)]

theorem rowCheck10279 : row10279 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10279 := by decide +kernel

theorem rowEval10279 (x : Key → ℝ) : Integer.Sparse.eval row10279 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck10279, Integer.Sparse.eval_collectBalanced, rawRowCheck10279]

def rawRow10280 : Integer.Sparse Key := [(key156, 6), (key94, 6), (key88, 6), (key88, 6), (key161, -6), (key161, -6), (key97, -6), (key14, -6)]

theorem rawRowCheck10280 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form14 = rawRow10280 := by decide +kernel

def row10280 : Integer.Sparse Key := [(key14, -6), (key88, 12), (key94, 6), (key97, -6), (key156, 6), (key161, -12)]

theorem rowCheck10280 : row10280 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10280 := by decide +kernel

theorem rowEval10280 (x : Key → ℝ) : Integer.Sparse.eval row10280 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form14) x := by
  rw [rowCheck10280, Integer.Sparse.eval_collectBalanced, rawRowCheck10280]

def rawRow10281 : Integer.Sparse Key := [(key165, 6), (key167, 6), (key167, 6), (key187, 6), (key9, -6), (key92, -6), (key92, -6), (key153, -6)]

theorem rawRowCheck10281 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form14 = rawRow10281 := by decide +kernel

def row10281 : Integer.Sparse Key := [(key9, -6), (key92, -12), (key153, -6), (key165, 6), (key167, 12), (key187, 6)]

theorem rowCheck10281 : row10281 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10281 := by decide +kernel

theorem rowEval10281 (x : Key → ℝ) : Integer.Sparse.eval row10281 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck10281, Integer.Sparse.eval_collectBalanced, rawRowCheck10281]

def rawRow10282 : Integer.Sparse Key := [(key167, 6), (key165, 6), (key167, 6), (key187, 6), (key9, -6), (key92, -6), (key153, -6), (key92, -6)]

theorem rawRowCheck10282 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form14 = rawRow10282 := by decide +kernel

def row10282 : Integer.Sparse Key := [(key9, -6), (key92, -12), (key153, -6), (key165, 6), (key167, 12), (key187, 6)]

theorem rowCheck10282 : row10282 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10282 := by decide +kernel

theorem rowEval10282 (x : Key → ℝ) : Integer.Sparse.eval row10282 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck10282, Integer.Sparse.eval_collectBalanced, rawRowCheck10282]

def rawRow10283 : Integer.Sparse Key := [(key167, 6), (key167, 6), (key165, 6), (key187, 6), (key9, -6), (key153, -6), (key92, -6), (key92, -6)]

theorem rawRowCheck10283 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form14 = rawRow10283 := by decide +kernel

def row10283 : Integer.Sparse Key := [(key9, -6), (key92, -12), (key153, -6), (key165, 6), (key167, 12), (key187, 6)]

theorem rowCheck10283 : row10283 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10283 := by decide +kernel

theorem rowEval10283 (x : Key → ℝ) : Integer.Sparse.eval row10283 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck10283, Integer.Sparse.eval_collectBalanced, rawRowCheck10283]

def rawRow10284 : Integer.Sparse Key := [(key165, 6), (key167, 6), (key187, 6), (key167, 6), (key92, -6), (key9, -6), (key92, -6), (key153, -6)]

theorem rawRowCheck10284 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form14 = rawRow10284 := by decide +kernel

def row10284 : Integer.Sparse Key := [(key9, -6), (key92, -12), (key153, -6), (key165, 6), (key167, 12), (key187, 6)]

theorem rowCheck10284 : row10284 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10284 := by decide +kernel

theorem rowEval10284 (x : Key → ℝ) : Integer.Sparse.eval row10284 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck10284, Integer.Sparse.eval_collectBalanced, rawRowCheck10284]

def rawRow10285 : Integer.Sparse Key := [(key167, 6), (key165, 6), (key187, 6), (key167, 6), (key92, -6), (key9, -6), (key153, -6), (key92, -6)]

theorem rawRowCheck10285 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form14 = rawRow10285 := by decide +kernel

def row10285 : Integer.Sparse Key := [(key9, -6), (key92, -12), (key153, -6), (key165, 6), (key167, 12), (key187, 6)]

theorem rowCheck10285 : row10285 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10285 := by decide +kernel

theorem rowEval10285 (x : Key → ℝ) : Integer.Sparse.eval row10285 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck10285, Integer.Sparse.eval_collectBalanced, rawRowCheck10285]

def rawRow10286 : Integer.Sparse Key := [(key165, 6), (key187, 6), (key167, 6), (key167, 6), (key92, -6), (key92, -6), (key9, -6), (key153, -6)]

theorem rawRowCheck10286 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form14 = rawRow10286 := by decide +kernel

def row10286 : Integer.Sparse Key := [(key9, -6), (key92, -12), (key153, -6), (key165, 6), (key167, 12), (key187, 6)]

theorem rowCheck10286 : row10286 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10286 := by decide +kernel

theorem rowEval10286 (x : Key → ℝ) : Integer.Sparse.eval row10286 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck10286, Integer.Sparse.eval_collectBalanced, rawRowCheck10286]

def rawRow10287 : Integer.Sparse Key := [(key187, 6), (key165, 6), (key167, 6), (key167, 6), (key92, -6), (key92, -6), (key153, -6), (key9, -6)]

theorem rawRowCheck10287 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form14 = rawRow10287 := by decide +kernel

def row10287 : Integer.Sparse Key := [(key9, -6), (key92, -12), (key153, -6), (key165, 6), (key167, 12), (key187, 6)]

theorem rowCheck10287 : row10287 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10287 := by decide +kernel

theorem rowEval10287 (x : Key → ℝ) : Integer.Sparse.eval row10287 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form14) x := by
  rw [rowCheck10287, Integer.Sparse.eval_collectBalanced, rawRowCheck10287]

def rawRow10288 : Integer.Sparse Key := [(key167, 6), (key187, 6), (key165, 6), (key167, 6), (key92, -6), (key153, -6), (key9, -6), (key92, -6)]

theorem rawRowCheck10288 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form14 = rawRow10288 := by decide +kernel

def row10288 : Integer.Sparse Key := [(key9, -6), (key92, -12), (key153, -6), (key165, 6), (key167, 12), (key187, 6)]

theorem rowCheck10288 : row10288 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10288 := by decide +kernel

theorem rowEval10288 (x : Key → ℝ) : Integer.Sparse.eval row10288 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck10288, Integer.Sparse.eval_collectBalanced, rawRowCheck10288]

def rawRow10289 : Integer.Sparse Key := [(key187, 6), (key167, 6), (key165, 6), (key167, 6), (key92, -6), (key153, -6), (key92, -6), (key9, -6)]

theorem rawRowCheck10289 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form14 = rawRow10289 := by decide +kernel

def row10289 : Integer.Sparse Key := [(key9, -6), (key92, -12), (key153, -6), (key165, 6), (key167, 12), (key187, 6)]

theorem rowCheck10289 : row10289 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10289 := by decide +kernel

theorem rowEval10289 (x : Key → ℝ) : Integer.Sparse.eval row10289 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form14) x := by
  rw [rowCheck10289, Integer.Sparse.eval_collectBalanced, rawRowCheck10289]

def rawRow10290 : Integer.Sparse Key := [(key167, 6), (key167, 6), (key187, 6), (key165, 6), (key153, -6), (key9, -6), (key92, -6), (key92, -6)]

theorem rawRowCheck10290 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form14 = rawRow10290 := by decide +kernel

def row10290 : Integer.Sparse Key := [(key9, -6), (key92, -12), (key153, -6), (key165, 6), (key167, 12), (key187, 6)]

theorem rowCheck10290 : row10290 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10290 := by decide +kernel

theorem rowEval10290 (x : Key → ℝ) : Integer.Sparse.eval row10290 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck10290, Integer.Sparse.eval_collectBalanced, rawRowCheck10290]

def rawRow10291 : Integer.Sparse Key := [(key167, 6), (key187, 6), (key167, 6), (key165, 6), (key153, -6), (key92, -6), (key9, -6), (key92, -6)]

theorem rawRowCheck10291 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form14 = rawRow10291 := by decide +kernel

def row10291 : Integer.Sparse Key := [(key9, -6), (key92, -12), (key153, -6), (key165, 6), (key167, 12), (key187, 6)]

theorem rowCheck10291 : row10291 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10291 := by decide +kernel

theorem rowEval10291 (x : Key → ℝ) : Integer.Sparse.eval row10291 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck10291, Integer.Sparse.eval_collectBalanced, rawRowCheck10291]

def rawRow10292 : Integer.Sparse Key := [(key187, 6), (key167, 6), (key167, 6), (key165, 6), (key153, -6), (key92, -6), (key92, -6), (key9, -6)]

theorem rawRowCheck10292 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form14 = rawRow10292 := by decide +kernel

def row10292 : Integer.Sparse Key := [(key9, -6), (key92, -12), (key153, -6), (key165, 6), (key167, 12), (key187, 6)]

theorem rowCheck10292 : row10292 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10292 := by decide +kernel

theorem rowEval10292 (x : Key → ℝ) : Integer.Sparse.eval row10292 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form14) x := by
  rw [rowCheck10292, Integer.Sparse.eval_collectBalanced, rawRowCheck10292]

def rawRow10293 : Integer.Sparse Key := [(key1095, -6), (key1095, -6), (key1099, -6), (key1184, -6), (key981, 2), (key981, 2), (key985, 2), (key1095, 2), (key1095, 2), (key1166, 2), (key1166, 2), (key1170, 2), (key1170, 2), (key1184, 2), (key1221, 2), (key1221, 2)]

theorem rawRowCheck10293 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form15 = rawRow10293 := by decide +kernel

def row10293 : Integer.Sparse Key := [(key981, 4), (key985, 2), (key1095, -8), (key1099, -6), (key1166, 4), (key1170, 4), (key1184, -4), (key1221, 4)]

theorem rowCheck10293 : row10293 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10293 := by decide +kernel

theorem rowEval10293 (x : Key → ℝ) : Integer.Sparse.eval row10293 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10293, Integer.Sparse.eval_collectBalanced, rawRowCheck10293]

def rawRow10294 : Integer.Sparse Key := [(key1095, -6), (key1099, -6), (key1095, -6), (key1184, -6), (key981, 2), (key985, 2), (key981, 2), (key1166, 2), (key1170, 2), (key1095, 2), (key1170, 2), (key1095, 2), (key1166, 2), (key1221, 2), (key1184, 2), (key1221, 2)]

theorem rawRowCheck10294 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form15 = rawRow10294 := by decide +kernel

def row10294 : Integer.Sparse Key := [(key981, 4), (key985, 2), (key1095, -8), (key1099, -6), (key1166, 4), (key1170, 4), (key1184, -4), (key1221, 4)]

theorem rowCheck10294 : row10294 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10294 := by decide +kernel

theorem rowEval10294 (x : Key → ℝ) : Integer.Sparse.eval row10294 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10294, Integer.Sparse.eval_collectBalanced, rawRowCheck10294]

def rawRow10295 : Integer.Sparse Key := [(key1099, -6), (key1095, -6), (key1095, -6), (key1184, -6), (key985, 2), (key981, 2), (key981, 2), (key1170, 2), (key1166, 2), (key1170, 2), (key1095, 2), (key1166, 2), (key1095, 2), (key1221, 2), (key1221, 2), (key1184, 2)]

theorem rawRowCheck10295 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form15 = rawRow10295 := by decide +kernel

def row10295 : Integer.Sparse Key := [(key981, 4), (key985, 2), (key1095, -8), (key1099, -6), (key1166, 4), (key1170, 4), (key1184, -4), (key1221, 4)]

theorem rowCheck10295 : row10295 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10295 := by decide +kernel

theorem rowEval10295 (x : Key → ℝ) : Integer.Sparse.eval row10295 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10295, Integer.Sparse.eval_collectBalanced, rawRowCheck10295]

def rawRow10296 : Integer.Sparse Key := [(key1095, -6), (key1095, -6), (key1184, -6), (key1099, -6), (key1095, 2), (key1095, 2), (key1184, 2), (key981, 2), (key981, 2), (key1166, 2), (key1166, 2), (key1221, 2), (key1221, 2), (key985, 2), (key1170, 2), (key1170, 2)]

theorem rawRowCheck10296 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form15 = rawRow10296 := by decide +kernel

def row10296 : Integer.Sparse Key := [(key981, 4), (key985, 2), (key1095, -8), (key1099, -6), (key1166, 4), (key1170, 4), (key1184, -4), (key1221, 4)]

theorem rowCheck10296 : row10296 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10296 := by decide +kernel

theorem rowEval10296 (x : Key → ℝ) : Integer.Sparse.eval row10296 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10296, Integer.Sparse.eval_collectBalanced, rawRowCheck10296]

def rawRow10297 : Integer.Sparse Key := [(key1095, -6), (key1184, -6), (key1095, -6), (key1099, -6), (key1095, 2), (key1184, 2), (key1095, 2), (key1166, 2), (key1221, 2), (key981, 2), (key1221, 2), (key981, 2), (key1166, 2), (key1170, 2), (key985, 2), (key1170, 2)]

theorem rawRowCheck10297 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form15 = rawRow10297 := by decide +kernel

def row10297 : Integer.Sparse Key := [(key981, 4), (key985, 2), (key1095, -8), (key1099, -6), (key1166, 4), (key1170, 4), (key1184, -4), (key1221, 4)]

theorem rowCheck10297 : row10297 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10297 := by decide +kernel

theorem rowEval10297 (x : Key → ℝ) : Integer.Sparse.eval row10297 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10297, Integer.Sparse.eval_collectBalanced, rawRowCheck10297]

def rawRow10298 : Integer.Sparse Key := [(key1184, -6), (key1095, -6), (key1095, -6), (key1099, -6), (key1184, 2), (key1095, 2), (key1095, 2), (key1221, 2), (key1166, 2), (key1221, 2), (key981, 2), (key1166, 2), (key981, 2), (key1170, 2), (key1170, 2), (key985, 2)]

theorem rawRowCheck10298 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form15 = rawRow10298 := by decide +kernel

def row10298 : Integer.Sparse Key := [(key981, 4), (key985, 2), (key1095, -8), (key1099, -6), (key1166, 4), (key1170, 4), (key1184, -4), (key1221, 4)]

theorem rowCheck10298 : row10298 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10298 := by decide +kernel

theorem rowEval10298 (x : Key → ℝ) : Integer.Sparse.eval row10298 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form15) x := by
  rw [rowCheck10298, Integer.Sparse.eval_collectBalanced, rawRowCheck10298]

def rawRow10299 : Integer.Sparse Key := [(key1095, -6), (key1099, -6), (key1184, -6), (key1095, -6), (key1166, 2), (key1170, 2), (key1221, 2), (key981, 2), (key985, 2), (key1095, 2), (key1170, 2), (key1184, 2), (key1221, 2), (key981, 2), (key1095, 2), (key1166, 2)]

theorem rawRowCheck10299 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form15 = rawRow10299 := by decide +kernel

def row10299 : Integer.Sparse Key := [(key981, 4), (key985, 2), (key1095, -8), (key1099, -6), (key1166, 4), (key1170, 4), (key1184, -4), (key1221, 4)]

theorem rowCheck10299 : row10299 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10299 := by decide +kernel

theorem rowEval10299 (x : Key → ℝ) : Integer.Sparse.eval row10299 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10299, Integer.Sparse.eval_collectBalanced, rawRowCheck10299]

def rawRow10300 : Integer.Sparse Key := [(key1099, -6), (key1095, -6), (key1184, -6), (key1095, -6), (key1170, 2), (key1166, 2), (key1221, 2), (key985, 2), (key981, 2), (key1170, 2), (key1095, 2), (key1221, 2), (key1184, 2), (key981, 2), (key1166, 2), (key1095, 2)]

theorem rawRowCheck10300 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form15 = rawRow10300 := by decide +kernel

def row10300 : Integer.Sparse Key := [(key981, 4), (key985, 2), (key1095, -8), (key1099, -6), (key1166, 4), (key1170, 4), (key1184, -4), (key1221, 4)]

theorem rowCheck10300 : row10300 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10300 := by decide +kernel

theorem rowEval10300 (x : Key → ℝ) : Integer.Sparse.eval row10300 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10300, Integer.Sparse.eval_collectBalanced, rawRowCheck10300]

def rawRow10301 : Integer.Sparse Key := [(key1095, -6), (key1184, -6), (key1099, -6), (key1095, -6), (key1166, 2), (key1221, 2), (key1170, 2), (key1095, 2), (key1184, 2), (key981, 2), (key1221, 2), (key985, 2), (key1170, 2), (key1095, 2), (key981, 2), (key1166, 2)]

theorem rawRowCheck10301 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form15 = rawRow10301 := by decide +kernel

def row10301 : Integer.Sparse Key := [(key981, 4), (key985, 2), (key1095, -8), (key1099, -6), (key1166, 4), (key1170, 4), (key1184, -4), (key1221, 4)]

theorem rowCheck10301 : row10301 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10301 := by decide +kernel

theorem rowEval10301 (x : Key → ℝ) : Integer.Sparse.eval row10301 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10301, Integer.Sparse.eval_collectBalanced, rawRowCheck10301]

def rawRow10302 : Integer.Sparse Key := [(key1184, -6), (key1095, -6), (key1099, -6), (key1095, -6), (key1221, 2), (key1166, 2), (key1170, 2), (key1184, 2), (key1095, 2), (key1221, 2), (key981, 2), (key1170, 2), (key985, 2), (key1095, 2), (key1166, 2), (key981, 2)]

theorem rawRowCheck10302 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form15 = rawRow10302 := by decide +kernel

def row10302 : Integer.Sparse Key := [(key981, 4), (key985, 2), (key1095, -8), (key1099, -6), (key1166, 4), (key1170, 4), (key1184, -4), (key1221, 4)]

theorem rowCheck10302 : row10302 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10302 := by decide +kernel

theorem rowEval10302 (x : Key → ℝ) : Integer.Sparse.eval row10302 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form15) x := by
  rw [rowCheck10302, Integer.Sparse.eval_collectBalanced, rawRowCheck10302]

def rawRow10303 : Integer.Sparse Key := [(key1099, -6), (key1184, -6), (key1095, -6), (key1095, -6), (key1170, 2), (key1221, 2), (key1166, 2), (key1170, 2), (key1221, 2), (key985, 2), (key1184, 2), (key981, 2), (key1095, 2), (key1166, 2), (key981, 2), (key1095, 2)]

theorem rawRowCheck10303 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form15 = rawRow10303 := by decide +kernel

def row10303 : Integer.Sparse Key := [(key981, 4), (key985, 2), (key1095, -8), (key1099, -6), (key1166, 4), (key1170, 4), (key1184, -4), (key1221, 4)]

theorem rowCheck10303 : row10303 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10303 := by decide +kernel

theorem rowEval10303 (x : Key → ℝ) : Integer.Sparse.eval row10303 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10303, Integer.Sparse.eval_collectBalanced, rawRowCheck10303]

def rawRow10304 : Integer.Sparse Key := [(key1184, -6), (key1099, -6), (key1095, -6), (key1095, -6), (key1221, 2), (key1170, 2), (key1166, 2), (key1221, 2), (key1170, 2), (key1184, 2), (key985, 2), (key1095, 2), (key981, 2), (key1166, 2), (key1095, 2), (key981, 2)]

theorem rawRowCheck10304 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form15 = rawRow10304 := by decide +kernel

def row10304 : Integer.Sparse Key := [(key981, 4), (key985, 2), (key1095, -8), (key1099, -6), (key1166, 4), (key1170, 4), (key1184, -4), (key1221, 4)]

theorem rowCheck10304 : row10304 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10304 := by decide +kernel

theorem rowEval10304 (x : Key → ℝ) : Integer.Sparse.eval row10304 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form15) x := by
  rw [rowCheck10304, Integer.Sparse.eval_collectBalanced, rawRowCheck10304]

def rawRow10305 : Integer.Sparse Key := [(key1166, -6), (key1170, -6), (key1170, -6), (key1221, -6), (key981, 2), (key985, 2), (key985, 2), (key1095, 2), (key1099, 2), (key1095, 2), (key1170, 2), (key1099, 2), (key1170, 2), (key1184, 2), (key1184, 2), (key1221, 2)]

theorem rawRowCheck10305 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form15 = rawRow10305 := by decide +kernel

def row10305 : Integer.Sparse Key := [(key981, 2), (key985, 4), (key1095, 4), (key1099, 4), (key1166, -6), (key1170, -8), (key1184, 4), (key1221, -4)]

theorem rowCheck10305 : row10305 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10305 := by decide +kernel

theorem rowEval10305 (x : Key → ℝ) : Integer.Sparse.eval row10305 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10305, Integer.Sparse.eval_collectBalanced, rawRowCheck10305]

def rawRow10306 : Integer.Sparse Key := [(key1170, -6), (key1166, -6), (key1170, -6), (key1221, -6), (key985, 2), (key981, 2), (key985, 2), (key1099, 2), (key1095, 2), (key1170, 2), (key1095, 2), (key1170, 2), (key1099, 2), (key1184, 2), (key1221, 2), (key1184, 2)]

theorem rawRowCheck10306 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form15 = rawRow10306 := by decide +kernel

def row10306 : Integer.Sparse Key := [(key981, 2), (key985, 4), (key1095, 4), (key1099, 4), (key1166, -6), (key1170, -8), (key1184, 4), (key1221, -4)]

theorem rowCheck10306 : row10306 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10306 := by decide +kernel

theorem rowEval10306 (x : Key → ℝ) : Integer.Sparse.eval row10306 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10306, Integer.Sparse.eval_collectBalanced, rawRowCheck10306]

def rawRow10307 : Integer.Sparse Key := [(key1170, -6), (key1170, -6), (key1166, -6), (key1221, -6), (key985, 2), (key985, 2), (key981, 2), (key1170, 2), (key1170, 2), (key1099, 2), (key1099, 2), (key1095, 2), (key1095, 2), (key1221, 2), (key1184, 2), (key1184, 2)]

theorem rawRowCheck10307 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form15 = rawRow10307 := by decide +kernel

def row10307 : Integer.Sparse Key := [(key981, 2), (key985, 4), (key1095, 4), (key1099, 4), (key1166, -6), (key1170, -8), (key1184, 4), (key1221, -4)]

theorem rowCheck10307 : row10307 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10307 := by decide +kernel

theorem rowEval10307 (x : Key → ℝ) : Integer.Sparse.eval row10307 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10307, Integer.Sparse.eval_collectBalanced, rawRowCheck10307]

def rawRow10308 : Integer.Sparse Key := [(key1166, -6), (key1170, -6), (key1221, -6), (key1170, -6), (key1095, 2), (key1099, 2), (key1184, 2), (key981, 2), (key985, 2), (key1095, 2), (key1170, 2), (key1184, 2), (key1221, 2), (key985, 2), (key1099, 2), (key1170, 2)]

theorem rawRowCheck10308 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form15 = rawRow10308 := by decide +kernel

def row10308 : Integer.Sparse Key := [(key981, 2), (key985, 4), (key1095, 4), (key1099, 4), (key1166, -6), (key1170, -8), (key1184, 4), (key1221, -4)]

theorem rowCheck10308 : row10308 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10308 := by decide +kernel

theorem rowEval10308 (x : Key → ℝ) : Integer.Sparse.eval row10308 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10308, Integer.Sparse.eval_collectBalanced, rawRowCheck10308]

def rawRow10309 : Integer.Sparse Key := [(key1170, -6), (key1166, -6), (key1221, -6), (key1170, -6), (key1099, 2), (key1095, 2), (key1184, 2), (key985, 2), (key981, 2), (key1170, 2), (key1095, 2), (key1221, 2), (key1184, 2), (key985, 2), (key1170, 2), (key1099, 2)]

theorem rawRowCheck10309 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form15 = rawRow10309 := by decide +kernel

def row10309 : Integer.Sparse Key := [(key981, 2), (key985, 4), (key1095, 4), (key1099, 4), (key1166, -6), (key1170, -8), (key1184, 4), (key1221, -4)]

theorem rowCheck10309 : row10309 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10309 := by decide +kernel

theorem rowEval10309 (x : Key → ℝ) : Integer.Sparse.eval row10309 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10309, Integer.Sparse.eval_collectBalanced, rawRowCheck10309]

def rawRow10310 : Integer.Sparse Key := [(key1166, -6), (key1221, -6), (key1170, -6), (key1170, -6), (key1095, 2), (key1184, 2), (key1099, 2), (key1095, 2), (key1184, 2), (key981, 2), (key1221, 2), (key985, 2), (key1170, 2), (key1099, 2), (key985, 2), (key1170, 2)]

theorem rawRowCheck10310 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form15 = rawRow10310 := by decide +kernel

def row10310 : Integer.Sparse Key := [(key981, 2), (key985, 4), (key1095, 4), (key1099, 4), (key1166, -6), (key1170, -8), (key1184, 4), (key1221, -4)]

theorem rowCheck10310 : row10310 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10310 := by decide +kernel

theorem rowEval10310 (x : Key → ℝ) : Integer.Sparse.eval row10310 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10310, Integer.Sparse.eval_collectBalanced, rawRowCheck10310]

def rawRow10311 : Integer.Sparse Key := [(key1221, -6), (key1166, -6), (key1170, -6), (key1170, -6), (key1184, 2), (key1095, 2), (key1099, 2), (key1184, 2), (key1095, 2), (key1221, 2), (key981, 2), (key1170, 2), (key985, 2), (key1099, 2), (key1170, 2), (key985, 2)]

theorem rawRowCheck10311 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form15 = rawRow10311 := by decide +kernel

def row10311 : Integer.Sparse Key := [(key981, 2), (key985, 4), (key1095, 4), (key1099, 4), (key1166, -6), (key1170, -8), (key1184, 4), (key1221, -4)]

theorem rowCheck10311 : row10311 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10311 := by decide +kernel

theorem rowEval10311 (x : Key → ℝ) : Integer.Sparse.eval row10311 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form15) x := by
  rw [rowCheck10311, Integer.Sparse.eval_collectBalanced, rawRowCheck10311]

def rawRow10312 : Integer.Sparse Key := [(key1170, -6), (key1221, -6), (key1166, -6), (key1170, -6), (key1099, 2), (key1184, 2), (key1095, 2), (key1170, 2), (key1221, 2), (key985, 2), (key1184, 2), (key981, 2), (key1095, 2), (key1170, 2), (key985, 2), (key1099, 2)]

theorem rawRowCheck10312 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form15 = rawRow10312 := by decide +kernel

def row10312 : Integer.Sparse Key := [(key981, 2), (key985, 4), (key1095, 4), (key1099, 4), (key1166, -6), (key1170, -8), (key1184, 4), (key1221, -4)]

theorem rowCheck10312 : row10312 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10312 := by decide +kernel

theorem rowEval10312 (x : Key → ℝ) : Integer.Sparse.eval row10312 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10312, Integer.Sparse.eval_collectBalanced, rawRowCheck10312]

def rawRow10313 : Integer.Sparse Key := [(key1221, -6), (key1170, -6), (key1166, -6), (key1170, -6), (key1184, 2), (key1099, 2), (key1095, 2), (key1221, 2), (key1170, 2), (key1184, 2), (key985, 2), (key1095, 2), (key981, 2), (key1170, 2), (key1099, 2), (key985, 2)]

theorem rawRowCheck10313 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form15 = rawRow10313 := by decide +kernel

def row10313 : Integer.Sparse Key := [(key981, 2), (key985, 4), (key1095, 4), (key1099, 4), (key1166, -6), (key1170, -8), (key1184, 4), (key1221, -4)]

theorem rowCheck10313 : row10313 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10313 := by decide +kernel

theorem rowEval10313 (x : Key → ℝ) : Integer.Sparse.eval row10313 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form15) x := by
  rw [rowCheck10313, Integer.Sparse.eval_collectBalanced, rawRowCheck10313]

def rawRow10314 : Integer.Sparse Key := [(key1170, -6), (key1170, -6), (key1221, -6), (key1166, -6), (key1170, 2), (key1170, 2), (key1221, 2), (key985, 2), (key985, 2), (key1099, 2), (key1099, 2), (key1184, 2), (key1184, 2), (key981, 2), (key1095, 2), (key1095, 2)]

theorem rawRowCheck10314 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form15 = rawRow10314 := by decide +kernel

def row10314 : Integer.Sparse Key := [(key981, 2), (key985, 4), (key1095, 4), (key1099, 4), (key1166, -6), (key1170, -8), (key1184, 4), (key1221, -4)]

theorem rowCheck10314 : row10314 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10314 := by decide +kernel

theorem rowEval10314 (x : Key → ℝ) : Integer.Sparse.eval row10314 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10314, Integer.Sparse.eval_collectBalanced, rawRowCheck10314]

def rawRow10315 : Integer.Sparse Key := [(key1170, -6), (key1221, -6), (key1170, -6), (key1166, -6), (key1170, 2), (key1221, 2), (key1170, 2), (key1099, 2), (key1184, 2), (key985, 2), (key1184, 2), (key985, 2), (key1099, 2), (key1095, 2), (key981, 2), (key1095, 2)]

theorem rawRowCheck10315 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form15 = rawRow10315 := by decide +kernel

def row10315 : Integer.Sparse Key := [(key981, 2), (key985, 4), (key1095, 4), (key1099, 4), (key1166, -6), (key1170, -8), (key1184, 4), (key1221, -4)]

theorem rowCheck10315 : row10315 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10315 := by decide +kernel

theorem rowEval10315 (x : Key → ℝ) : Integer.Sparse.eval row10315 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10315, Integer.Sparse.eval_collectBalanced, rawRowCheck10315]

def rawRow10316 : Integer.Sparse Key := [(key1221, -6), (key1170, -6), (key1170, -6), (key1166, -6), (key1221, 2), (key1170, 2), (key1170, 2), (key1184, 2), (key1099, 2), (key1184, 2), (key985, 2), (key1099, 2), (key985, 2), (key1095, 2), (key1095, 2), (key981, 2)]

theorem rawRowCheck10316 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form15 = rawRow10316 := by decide +kernel

def row10316 : Integer.Sparse Key := [(key981, 2), (key985, 4), (key1095, 4), (key1099, 4), (key1166, -6), (key1170, -8), (key1184, 4), (key1221, -4)]

theorem rowCheck10316 : row10316 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10316 := by decide +kernel

theorem rowEval10316 (x : Key → ℝ) : Integer.Sparse.eval row10316 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form15) x := by
  rw [rowCheck10316, Integer.Sparse.eval_collectBalanced, rawRowCheck10316]

def rawRow10317 : Integer.Sparse Key := [(key1037, -6), (key1115, -6), (key1124, -6), (key1124, -6), (key1002, 6), (key1115, 6), (key1151, 6), (key1151, 6)]

theorem rawRowCheck10317 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form16 = rawRow10317 := by decide +kernel

def row10317 : Integer.Sparse Key := [(key1002, 6), (key1037, -6), (key1124, -12), (key1151, 12)]

theorem rowCheck10317 : row10317 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10317 := by decide +kernel

theorem rowEval10317 (x : Key → ℝ) : Integer.Sparse.eval row10317 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck10317, Integer.Sparse.eval_collectBalanced, rawRowCheck10317]

def rawRow10318 : Integer.Sparse Key := [(key1037, -6), (key1124, -6), (key1115, -6), (key1124, -6), (key1002, 6), (key1151, 6), (key1115, 6), (key1151, 6)]

theorem rawRowCheck10318 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form16 = rawRow10318 := by decide +kernel

def row10318 : Integer.Sparse Key := [(key1002, 6), (key1037, -6), (key1124, -12), (key1151, 12)]

theorem rowCheck10318 : row10318 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10318 := by decide +kernel

theorem rowEval10318 (x : Key → ℝ) : Integer.Sparse.eval row10318 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck10318, Integer.Sparse.eval_collectBalanced, rawRowCheck10318]

def rawRow10319 : Integer.Sparse Key := [(key1037, -6), (key1124, -6), (key1124, -6), (key1115, -6), (key1002, 6), (key1151, 6), (key1151, 6), (key1115, 6)]

theorem rawRowCheck10319 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form16 = rawRow10319 := by decide +kernel

def row10319 : Integer.Sparse Key := [(key1002, 6), (key1037, -6), (key1124, -12), (key1151, 12)]

theorem rowCheck10319 : row10319 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10319 := by decide +kernel

theorem rowEval10319 (x : Key → ℝ) : Integer.Sparse.eval row10319 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck10319, Integer.Sparse.eval_collectBalanced, rawRowCheck10319]

def rawRow10320 : Integer.Sparse Key := [(key1115, -6), (key1037, -6), (key1124, -6), (key1124, -6), (key1115, 6), (key1002, 6), (key1151, 6), (key1151, 6)]

theorem rawRowCheck10320 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form16 = rawRow10320 := by decide +kernel

def row10320 : Integer.Sparse Key := [(key1002, 6), (key1037, -6), (key1124, -12), (key1151, 12)]

theorem rowCheck10320 : row10320 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10320 := by decide +kernel

theorem rowEval10320 (x : Key → ℝ) : Integer.Sparse.eval row10320 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck10320, Integer.Sparse.eval_collectBalanced, rawRowCheck10320]

def rawRow10321 : Integer.Sparse Key := [(key1115, -6), (key1124, -6), (key1037, -6), (key1124, -6), (key1115, 6), (key1151, 6), (key1002, 6), (key1151, 6)]

theorem rawRowCheck10321 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form16 = rawRow10321 := by decide +kernel

def row10321 : Integer.Sparse Key := [(key1002, 6), (key1037, -6), (key1124, -12), (key1151, 12)]

theorem rowCheck10321 : row10321 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10321 := by decide +kernel

theorem rowEval10321 (x : Key → ℝ) : Integer.Sparse.eval row10321 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck10321, Integer.Sparse.eval_collectBalanced, rawRowCheck10321]

def rawRow10322 : Integer.Sparse Key := [(key1115, -6), (key1124, -6), (key1124, -6), (key1037, -6), (key1115, 6), (key1151, 6), (key1151, 6), (key1002, 6)]

theorem rawRowCheck10322 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form16 = rawRow10322 := by decide +kernel

def row10322 : Integer.Sparse Key := [(key1002, 6), (key1037, -6), (key1124, -12), (key1151, 12)]

theorem rowCheck10322 : row10322 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10322 := by decide +kernel

theorem rowEval10322 (x : Key → ℝ) : Integer.Sparse.eval row10322 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form16) x := by
  rw [rowCheck10322, Integer.Sparse.eval_collectBalanced, rawRowCheck10322]

def rawRow10323 : Integer.Sparse Key := [(key1124, -6), (key1037, -6), (key1115, -6), (key1124, -6), (key1151, 6), (key1002, 6), (key1115, 6), (key1151, 6)]

theorem rawRowCheck10323 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form16 = rawRow10323 := by decide +kernel

def row10323 : Integer.Sparse Key := [(key1002, 6), (key1037, -6), (key1124, -12), (key1151, 12)]

theorem rowCheck10323 : row10323 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10323 := by decide +kernel

theorem rowEval10323 (x : Key → ℝ) : Integer.Sparse.eval row10323 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck10323, Integer.Sparse.eval_collectBalanced, rawRowCheck10323]

def rawRow10324 : Integer.Sparse Key := [(key1124, -6), (key1037, -6), (key1124, -6), (key1115, -6), (key1151, 6), (key1002, 6), (key1151, 6), (key1115, 6)]

theorem rawRowCheck10324 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form16 = rawRow10324 := by decide +kernel

def row10324 : Integer.Sparse Key := [(key1002, 6), (key1037, -6), (key1124, -12), (key1151, 12)]

theorem rowCheck10324 : row10324 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10324 := by decide +kernel

theorem rowEval10324 (x : Key → ℝ) : Integer.Sparse.eval row10324 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck10324, Integer.Sparse.eval_collectBalanced, rawRowCheck10324]

def rawRow10325 : Integer.Sparse Key := [(key1124, -6), (key1115, -6), (key1037, -6), (key1124, -6), (key1151, 6), (key1115, 6), (key1002, 6), (key1151, 6)]

theorem rawRowCheck10325 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form16 = rawRow10325 := by decide +kernel

def row10325 : Integer.Sparse Key := [(key1002, 6), (key1037, -6), (key1124, -12), (key1151, 12)]

theorem rowCheck10325 : row10325 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10325 := by decide +kernel

theorem rowEval10325 (x : Key → ℝ) : Integer.Sparse.eval row10325 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck10325, Integer.Sparse.eval_collectBalanced, rawRowCheck10325]

def rawRow10326 : Integer.Sparse Key := [(key1124, -6), (key1115, -6), (key1124, -6), (key1037, -6), (key1151, 6), (key1115, 6), (key1151, 6), (key1002, 6)]

theorem rawRowCheck10326 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form16 = rawRow10326 := by decide +kernel

def row10326 : Integer.Sparse Key := [(key1002, 6), (key1037, -6), (key1124, -12), (key1151, 12)]

theorem rowCheck10326 : row10326 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10326 := by decide +kernel

theorem rowEval10326 (x : Key → ℝ) : Integer.Sparse.eval row10326 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form16) x := by
  rw [rowCheck10326, Integer.Sparse.eval_collectBalanced, rawRowCheck10326]

def rawRow10327 : Integer.Sparse Key := [(key1124, -6), (key1124, -6), (key1037, -6), (key1115, -6), (key1151, 6), (key1151, 6), (key1002, 6), (key1115, 6)]

theorem rawRowCheck10327 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form16 = rawRow10327 := by decide +kernel

def row10327 : Integer.Sparse Key := [(key1002, 6), (key1037, -6), (key1124, -12), (key1151, 12)]

theorem rowCheck10327 : row10327 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10327 := by decide +kernel

theorem rowEval10327 (x : Key → ℝ) : Integer.Sparse.eval row10327 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck10327, Integer.Sparse.eval_collectBalanced, rawRowCheck10327]

def rawRow10328 : Integer.Sparse Key := [(key1124, -6), (key1124, -6), (key1115, -6), (key1037, -6), (key1151, 6), (key1151, 6), (key1115, 6), (key1002, 6)]

theorem rawRowCheck10328 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form16 = rawRow10328 := by decide +kernel

def row10328 : Integer.Sparse Key := [(key1002, 6), (key1037, -6), (key1124, -12), (key1151, 12)]

theorem rowCheck10328 : row10328 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10328 := by decide +kernel

theorem rowEval10328 (x : Key → ℝ) : Integer.Sparse.eval row10328 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form16) x := by
  rw [rowCheck10328, Integer.Sparse.eval_collectBalanced, rawRowCheck10328]

def rawRow10329 : Integer.Sparse Key := [(key1072, -6), (key1151, -6), (key1151, -6), (key1167, -6), (key1016, 6), (key1124, 6), (key1124, 6), (key1167, 6)]

theorem rawRowCheck10329 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form16 = rawRow10329 := by decide +kernel

def row10329 : Integer.Sparse Key := [(key1016, 6), (key1072, -6), (key1124, 12), (key1151, -12)]

theorem rowCheck10329 : row10329 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10329 := by decide +kernel

theorem rowEval10329 (x : Key → ℝ) : Integer.Sparse.eval row10329 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck10329, Integer.Sparse.eval_collectBalanced, rawRowCheck10329]

def rawRow10330 : Integer.Sparse Key := [(key1072, -6), (key1151, -6), (key1167, -6), (key1151, -6), (key1016, 6), (key1124, 6), (key1167, 6), (key1124, 6)]

theorem rawRowCheck10330 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form16 = rawRow10330 := by decide +kernel

def row10330 : Integer.Sparse Key := [(key1016, 6), (key1072, -6), (key1124, 12), (key1151, -12)]

theorem rowCheck10330 : row10330 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10330 := by decide +kernel

theorem rowEval10330 (x : Key → ℝ) : Integer.Sparse.eval row10330 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck10330, Integer.Sparse.eval_collectBalanced, rawRowCheck10330]

def rawRow10331 : Integer.Sparse Key := [(key1072, -6), (key1167, -6), (key1151, -6), (key1151, -6), (key1016, 6), (key1167, 6), (key1124, 6), (key1124, 6)]

theorem rawRowCheck10331 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form16 = rawRow10331 := by decide +kernel

def row10331 : Integer.Sparse Key := [(key1016, 6), (key1072, -6), (key1124, 12), (key1151, -12)]

theorem rowCheck10331 : row10331 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10331 := by decide +kernel

theorem rowEval10331 (x : Key → ℝ) : Integer.Sparse.eval row10331 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck10331, Integer.Sparse.eval_collectBalanced, rawRowCheck10331]

def rawRow10332 : Integer.Sparse Key := [(key1151, -6), (key1072, -6), (key1151, -6), (key1167, -6), (key1124, 6), (key1016, 6), (key1124, 6), (key1167, 6)]

theorem rawRowCheck10332 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form16 = rawRow10332 := by decide +kernel

def row10332 : Integer.Sparse Key := [(key1016, 6), (key1072, -6), (key1124, 12), (key1151, -12)]

theorem rowCheck10332 : row10332 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10332 := by decide +kernel

theorem rowEval10332 (x : Key → ℝ) : Integer.Sparse.eval row10332 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck10332, Integer.Sparse.eval_collectBalanced, rawRowCheck10332]

def rawRow10333 : Integer.Sparse Key := [(key1151, -6), (key1072, -6), (key1167, -6), (key1151, -6), (key1124, 6), (key1016, 6), (key1167, 6), (key1124, 6)]

theorem rawRowCheck10333 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form16 = rawRow10333 := by decide +kernel

def row10333 : Integer.Sparse Key := [(key1016, 6), (key1072, -6), (key1124, 12), (key1151, -12)]

theorem rowCheck10333 : row10333 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10333 := by decide +kernel

theorem rowEval10333 (x : Key → ℝ) : Integer.Sparse.eval row10333 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck10333, Integer.Sparse.eval_collectBalanced, rawRowCheck10333]

def rawRow10334 : Integer.Sparse Key := [(key1151, -6), (key1151, -6), (key1072, -6), (key1167, -6), (key1124, 6), (key1124, 6), (key1016, 6), (key1167, 6)]

theorem rawRowCheck10334 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form16 = rawRow10334 := by decide +kernel

def row10334 : Integer.Sparse Key := [(key1016, 6), (key1072, -6), (key1124, 12), (key1151, -12)]

theorem rowCheck10334 : row10334 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10334 := by decide +kernel

theorem rowEval10334 (x : Key → ℝ) : Integer.Sparse.eval row10334 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck10334, Integer.Sparse.eval_collectBalanced, rawRowCheck10334]

def rawRow10335 : Integer.Sparse Key := [(key1151, -6), (key1151, -6), (key1167, -6), (key1072, -6), (key1124, 6), (key1124, 6), (key1167, 6), (key1016, 6)]

theorem rawRowCheck10335 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form16 = rawRow10335 := by decide +kernel

def row10335 : Integer.Sparse Key := [(key1016, 6), (key1072, -6), (key1124, 12), (key1151, -12)]

theorem rowCheck10335 : row10335 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10335 := by decide +kernel

theorem rowEval10335 (x : Key → ℝ) : Integer.Sparse.eval row10335 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form16) x := by
  rw [rowCheck10335, Integer.Sparse.eval_collectBalanced, rawRowCheck10335]

def rawRow10336 : Integer.Sparse Key := [(key1151, -6), (key1167, -6), (key1072, -6), (key1151, -6), (key1124, 6), (key1167, 6), (key1016, 6), (key1124, 6)]

theorem rawRowCheck10336 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form16 = rawRow10336 := by decide +kernel

def row10336 : Integer.Sparse Key := [(key1016, 6), (key1072, -6), (key1124, 12), (key1151, -12)]

theorem rowCheck10336 : row10336 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10336 := by decide +kernel

theorem rowEval10336 (x : Key → ℝ) : Integer.Sparse.eval row10336 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck10336, Integer.Sparse.eval_collectBalanced, rawRowCheck10336]

def rawRow10337 : Integer.Sparse Key := [(key1151, -6), (key1167, -6), (key1151, -6), (key1072, -6), (key1124, 6), (key1167, 6), (key1124, 6), (key1016, 6)]

theorem rawRowCheck10337 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form16 = rawRow10337 := by decide +kernel

def row10337 : Integer.Sparse Key := [(key1016, 6), (key1072, -6), (key1124, 12), (key1151, -12)]

theorem rowCheck10337 : row10337 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10337 := by decide +kernel

theorem rowEval10337 (x : Key → ℝ) : Integer.Sparse.eval row10337 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form16) x := by
  rw [rowCheck10337, Integer.Sparse.eval_collectBalanced, rawRowCheck10337]

def rawRow10338 : Integer.Sparse Key := [(key1167, -6), (key1072, -6), (key1151, -6), (key1151, -6), (key1167, 6), (key1016, 6), (key1124, 6), (key1124, 6)]

theorem rawRowCheck10338 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form16 = rawRow10338 := by decide +kernel

def row10338 : Integer.Sparse Key := [(key1016, 6), (key1072, -6), (key1124, 12), (key1151, -12)]

theorem rowCheck10338 : row10338 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10338 := by decide +kernel

theorem rowEval10338 (x : Key → ℝ) : Integer.Sparse.eval row10338 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck10338, Integer.Sparse.eval_collectBalanced, rawRowCheck10338]

def rawRow10339 : Integer.Sparse Key := [(key1167, -6), (key1151, -6), (key1072, -6), (key1151, -6), (key1167, 6), (key1124, 6), (key1016, 6), (key1124, 6)]

theorem rawRowCheck10339 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form16 = rawRow10339 := by decide +kernel

def row10339 : Integer.Sparse Key := [(key1016, 6), (key1072, -6), (key1124, 12), (key1151, -12)]

theorem rowCheck10339 : row10339 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10339 := by decide +kernel

theorem rowEval10339 (x : Key → ℝ) : Integer.Sparse.eval row10339 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck10339, Integer.Sparse.eval_collectBalanced, rawRowCheck10339]

def rawRow10340 : Integer.Sparse Key := [(key1167, -6), (key1151, -6), (key1151, -6), (key1072, -6), (key1167, 6), (key1124, 6), (key1124, 6), (key1016, 6)]

theorem rawRowCheck10340 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form16 = rawRow10340 := by decide +kernel

def row10340 : Integer.Sparse Key := [(key1016, 6), (key1072, -6), (key1124, 12), (key1151, -12)]

theorem rowCheck10340 : row10340 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10340 := by decide +kernel

theorem rowEval10340 (x : Key → ℝ) : Integer.Sparse.eval row10340 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form16) x := by
  rw [rowCheck10340, Integer.Sparse.eval_collectBalanced, rawRowCheck10340]

def rawRow10341 : Integer.Sparse Key := [(key1004, -2), (key1008, -2), (key1008, -2), (key1117, -2), (key1157, -2), (key1157, -2), (key1195, -2), (key1195, -2), (key1214, -2), (key1214, -2), (key1216, -2), (key1216, -2), (key1004, 2), (key1021, 2), (key1021, 2), (key1039, 2), (key1078, 2), (key1078, 2), (key1201, 2), (key1201, 2), (key1214, 2), (key1214, 2), (key1225, 2), (key1225, 2)]

theorem rawRowCheck10341 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form17 = rawRow10341 := by decide +kernel

def row10341 : Integer.Sparse Key := [(key1008, -4), (key1021, 4), (key1039, 2), (key1078, 4), (key1117, -2), (key1157, -4), (key1195, -4), (key1201, 4), (key1216, -4), (key1225, 4)]

theorem rowCheck10341 : row10341 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10341 := by decide +kernel

theorem rowEval10341 (x : Key → ℝ) : Integer.Sparse.eval row10341 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck10341, Integer.Sparse.eval_collectBalanced, rawRowCheck10341]

def rawRow10342 : Integer.Sparse Key := [(key1008, -2), (key1004, -2), (key1008, -2), (key1157, -2), (key1117, -2), (key1157, -2), (key1214, -2), (key1216, -2), (key1195, -2), (key1216, -2), (key1195, -2), (key1214, -2), (key1021, 2), (key1004, 2), (key1021, 2), (key1078, 2), (key1039, 2), (key1078, 2), (key1214, 2), (key1225, 2), (key1201, 2), (key1225, 2), (key1201, 2), (key1214, 2)]

theorem rawRowCheck10342 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form17 = rawRow10342 := by decide +kernel

def row10342 : Integer.Sparse Key := [(key1008, -4), (key1021, 4), (key1039, 2), (key1078, 4), (key1117, -2), (key1157, -4), (key1195, -4), (key1201, 4), (key1216, -4), (key1225, 4)]

theorem rowCheck10342 : row10342 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10342 := by decide +kernel

theorem rowEval10342 (x : Key → ℝ) : Integer.Sparse.eval row10342 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck10342, Integer.Sparse.eval_collectBalanced, rawRowCheck10342]

def rawRow10343 : Integer.Sparse Key := [(key1008, -2), (key1008, -2), (key1004, -2), (key1157, -2), (key1157, -2), (key1117, -2), (key1216, -2), (key1214, -2), (key1216, -2), (key1195, -2), (key1214, -2), (key1195, -2), (key1021, 2), (key1021, 2), (key1004, 2), (key1078, 2), (key1078, 2), (key1039, 2), (key1225, 2), (key1214, 2), (key1225, 2), (key1201, 2), (key1214, 2), (key1201, 2)]

theorem rawRowCheck10343 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form17 = rawRow10343 := by decide +kernel

def row10343 : Integer.Sparse Key := [(key1008, -4), (key1021, 4), (key1039, 2), (key1078, 4), (key1117, -2), (key1157, -4), (key1195, -4), (key1201, 4), (key1216, -4), (key1225, 4)]

theorem rowCheck10343 : row10343 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10343 := by decide +kernel

theorem rowEval10343 (x : Key → ℝ) : Integer.Sparse.eval row10343 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10343, Integer.Sparse.eval_collectBalanced, rawRowCheck10343]

def rawRow10344 : Integer.Sparse Key := [(key1117, -2), (key1195, -2), (key1195, -2), (key1004, -2), (key1214, -2), (key1214, -2), (key1008, -2), (key1008, -2), (key1157, -2), (key1157, -2), (key1216, -2), (key1216, -2), (key1039, 2), (key1201, 2), (key1201, 2), (key1004, 2), (key1214, 2), (key1214, 2), (key1021, 2), (key1021, 2), (key1078, 2), (key1078, 2), (key1225, 2), (key1225, 2)]

theorem rawRowCheck10344 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form17 = rawRow10344 := by decide +kernel

def row10344 : Integer.Sparse Key := [(key1008, -4), (key1021, 4), (key1039, 2), (key1078, 4), (key1117, -2), (key1157, -4), (key1195, -4), (key1201, 4), (key1216, -4), (key1225, 4)]

theorem rowCheck10344 : row10344 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10344 := by decide +kernel

theorem rowEval10344 (x : Key → ℝ) : Integer.Sparse.eval row10344 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck10344, Integer.Sparse.eval_collectBalanced, rawRowCheck10344]

def rawRow10345 : Integer.Sparse Key := [(key1195, -2), (key1117, -2), (key1195, -2), (key1214, -2), (key1004, -2), (key1214, -2), (key1157, -2), (key1216, -2), (key1008, -2), (key1216, -2), (key1008, -2), (key1157, -2), (key1201, 2), (key1039, 2), (key1201, 2), (key1214, 2), (key1004, 2), (key1214, 2), (key1078, 2), (key1225, 2), (key1021, 2), (key1225, 2), (key1021, 2), (key1078, 2)]

theorem rawRowCheck10345 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form17 = rawRow10345 := by decide +kernel

def row10345 : Integer.Sparse Key := [(key1008, -4), (key1021, 4), (key1039, 2), (key1078, 4), (key1117, -2), (key1157, -4), (key1195, -4), (key1201, 4), (key1216, -4), (key1225, 4)]

theorem rowCheck10345 : row10345 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10345 := by decide +kernel

theorem rowEval10345 (x : Key → ℝ) : Integer.Sparse.eval row10345 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck10345, Integer.Sparse.eval_collectBalanced, rawRowCheck10345]

def rawRow10346 : Integer.Sparse Key := [(key1195, -2), (key1195, -2), (key1117, -2), (key1214, -2), (key1214, -2), (key1004, -2), (key1216, -2), (key1157, -2), (key1216, -2), (key1008, -2), (key1157, -2), (key1008, -2), (key1201, 2), (key1201, 2), (key1039, 2), (key1214, 2), (key1214, 2), (key1004, 2), (key1225, 2), (key1078, 2), (key1225, 2), (key1021, 2), (key1078, 2), (key1021, 2)]

theorem rawRowCheck10346 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form17 = rawRow10346 := by decide +kernel

def row10346 : Integer.Sparse Key := [(key1008, -4), (key1021, 4), (key1039, 2), (key1078, 4), (key1117, -2), (key1157, -4), (key1195, -4), (key1201, 4), (key1216, -4), (key1225, 4)]

theorem rowCheck10346 : row10346 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10346 := by decide +kernel

theorem rowEval10346 (x : Key → ℝ) : Integer.Sparse.eval row10346 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form17) x := by
  rw [rowCheck10346, Integer.Sparse.eval_collectBalanced, rawRowCheck10346]

def rawRow10347 : Integer.Sparse Key := [(key1157, -2), (key1214, -2), (key1216, -2), (key1008, -2), (key1195, -2), (key1216, -2), (key1004, -2), (key1008, -2), (key1117, -2), (key1157, -2), (key1195, -2), (key1214, -2), (key1078, 2), (key1214, 2), (key1225, 2), (key1021, 2), (key1201, 2), (key1225, 2), (key1004, 2), (key1021, 2), (key1039, 2), (key1078, 2), (key1201, 2), (key1214, 2)]

theorem rawRowCheck10347 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form17 = rawRow10347 := by decide +kernel

def row10347 : Integer.Sparse Key := [(key1008, -4), (key1021, 4), (key1039, 2), (key1078, 4), (key1117, -2), (key1157, -4), (key1195, -4), (key1201, 4), (key1216, -4), (key1225, 4)]

theorem rowCheck10347 : row10347 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10347 := by decide +kernel

theorem rowEval10347 (x : Key → ℝ) : Integer.Sparse.eval row10347 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck10347, Integer.Sparse.eval_collectBalanced, rawRowCheck10347]

def rawRow10348 : Integer.Sparse Key := [(key1157, -2), (key1216, -2), (key1214, -2), (key1008, -2), (key1216, -2), (key1195, -2), (key1008, -2), (key1004, -2), (key1157, -2), (key1117, -2), (key1214, -2), (key1195, -2), (key1078, 2), (key1225, 2), (key1214, 2), (key1021, 2), (key1225, 2), (key1201, 2), (key1021, 2), (key1004, 2), (key1078, 2), (key1039, 2), (key1214, 2), (key1201, 2)]

theorem rawRowCheck10348 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form17 = rawRow10348 := by decide +kernel

def row10348 : Integer.Sparse Key := [(key1008, -4), (key1021, 4), (key1039, 2), (key1078, 4), (key1117, -2), (key1157, -4), (key1195, -4), (key1201, 4), (key1216, -4), (key1225, 4)]

theorem rowCheck10348 : row10348 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10348 := by decide +kernel

theorem rowEval10348 (x : Key → ℝ) : Integer.Sparse.eval row10348 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10348, Integer.Sparse.eval_collectBalanced, rawRowCheck10348]

def rawRow10349 : Integer.Sparse Key := [(key1214, -2), (key1157, -2), (key1216, -2), (key1195, -2), (key1008, -2), (key1216, -2), (key1117, -2), (key1195, -2), (key1004, -2), (key1214, -2), (key1008, -2), (key1157, -2), (key1214, 2), (key1078, 2), (key1225, 2), (key1201, 2), (key1021, 2), (key1225, 2), (key1039, 2), (key1201, 2), (key1004, 2), (key1214, 2), (key1021, 2), (key1078, 2)]

theorem rawRowCheck10349 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form17 = rawRow10349 := by decide +kernel

def row10349 : Integer.Sparse Key := [(key1008, -4), (key1021, 4), (key1039, 2), (key1078, 4), (key1117, -2), (key1157, -4), (key1195, -4), (key1201, 4), (key1216, -4), (key1225, 4)]

theorem rowCheck10349 : row10349 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10349 := by decide +kernel

theorem rowEval10349 (x : Key → ℝ) : Integer.Sparse.eval row10349 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck10349, Integer.Sparse.eval_collectBalanced, rawRowCheck10349]

def rawRow10350 : Integer.Sparse Key := [(key1214, -2), (key1216, -2), (key1157, -2), (key1195, -2), (key1216, -2), (key1008, -2), (key1195, -2), (key1117, -2), (key1214, -2), (key1004, -2), (key1157, -2), (key1008, -2), (key1214, 2), (key1225, 2), (key1078, 2), (key1201, 2), (key1225, 2), (key1021, 2), (key1201, 2), (key1039, 2), (key1214, 2), (key1004, 2), (key1078, 2), (key1021, 2)]

theorem rawRowCheck10350 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form17 = rawRow10350 := by decide +kernel

def row10350 : Integer.Sparse Key := [(key1008, -4), (key1021, 4), (key1039, 2), (key1078, 4), (key1117, -2), (key1157, -4), (key1195, -4), (key1201, 4), (key1216, -4), (key1225, 4)]

theorem rowCheck10350 : row10350 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10350 := by decide +kernel

theorem rowEval10350 (x : Key → ℝ) : Integer.Sparse.eval row10350 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form17) x := by
  rw [rowCheck10350, Integer.Sparse.eval_collectBalanced, rawRowCheck10350]

def rawRow10351 : Integer.Sparse Key := [(key1216, -2), (key1157, -2), (key1214, -2), (key1216, -2), (key1008, -2), (key1195, -2), (key1157, -2), (key1214, -2), (key1008, -2), (key1195, -2), (key1004, -2), (key1117, -2), (key1225, 2), (key1078, 2), (key1214, 2), (key1225, 2), (key1021, 2), (key1201, 2), (key1078, 2), (key1214, 2), (key1021, 2), (key1201, 2), (key1004, 2), (key1039, 2)]

theorem rawRowCheck10351 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form17 = rawRow10351 := by decide +kernel

def row10351 : Integer.Sparse Key := [(key1008, -4), (key1021, 4), (key1039, 2), (key1078, 4), (key1117, -2), (key1157, -4), (key1195, -4), (key1201, 4), (key1216, -4), (key1225, 4)]

theorem rowCheck10351 : row10351 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10351 := by decide +kernel

theorem rowEval10351 (x : Key → ℝ) : Integer.Sparse.eval row10351 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10351, Integer.Sparse.eval_collectBalanced, rawRowCheck10351]

def rawRow10352 : Integer.Sparse Key := [(key1216, -2), (key1214, -2), (key1157, -2), (key1216, -2), (key1195, -2), (key1008, -2), (key1214, -2), (key1157, -2), (key1195, -2), (key1008, -2), (key1117, -2), (key1004, -2), (key1225, 2), (key1214, 2), (key1078, 2), (key1225, 2), (key1201, 2), (key1021, 2), (key1214, 2), (key1078, 2), (key1201, 2), (key1021, 2), (key1039, 2), (key1004, 2)]

theorem rawRowCheck10352 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form17 = rawRow10352 := by decide +kernel

def row10352 : Integer.Sparse Key := [(key1008, -4), (key1021, 4), (key1039, 2), (key1078, 4), (key1117, -2), (key1157, -4), (key1195, -4), (key1201, 4), (key1216, -4), (key1225, 4)]

theorem rowCheck10352 : row10352 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10352 := by decide +kernel

theorem rowEval10352 (x : Key → ℝ) : Integer.Sparse.eval row10352 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form17) x := by
  rw [rowCheck10352, Integer.Sparse.eval_collectBalanced, rawRowCheck10352]

def rawRow10353 : Integer.Sparse Key := [(key1021, -2), (key1021, -2), (key1023, -2), (key1129, -2), (key1129, -2), (key1176, -2), (key1201, -2), (key1202, -2), (key1201, -2), (key1225, -2), (key1202, -2), (key1225, -2), (key1008, 2), (key1008, 2), (key1023, 2), (key1043, 2), (key1043, 2), (key1081, 2), (key1195, 2), (key1202, 2), (key1195, 2), (key1216, 2), (key1202, 2), (key1216, 2)]

theorem rawRowCheck10353 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form17 = rawRow10353 := by decide +kernel

def row10353 : Integer.Sparse Key := [(key1008, 4), (key1021, -4), (key1043, 4), (key1081, 2), (key1129, -4), (key1176, -2), (key1195, 4), (key1201, -4), (key1216, 4), (key1225, -4)]

theorem rowCheck10353 : row10353 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10353 := by decide +kernel

theorem rowEval10353 (x : Key → ℝ) : Integer.Sparse.eval row10353 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck10353, Integer.Sparse.eval_collectBalanced, rawRowCheck10353]

def rawRow10354 : Integer.Sparse Key := [(key1021, -2), (key1023, -2), (key1021, -2), (key1129, -2), (key1176, -2), (key1129, -2), (key1202, -2), (key1201, -2), (key1225, -2), (key1201, -2), (key1225, -2), (key1202, -2), (key1008, 2), (key1023, 2), (key1008, 2), (key1043, 2), (key1081, 2), (key1043, 2), (key1202, 2), (key1195, 2), (key1216, 2), (key1195, 2), (key1216, 2), (key1202, 2)]

theorem rawRowCheck10354 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form17 = rawRow10354 := by decide +kernel

def row10354 : Integer.Sparse Key := [(key1008, 4), (key1021, -4), (key1043, 4), (key1081, 2), (key1129, -4), (key1176, -2), (key1195, 4), (key1201, -4), (key1216, 4), (key1225, -4)]

theorem rowCheck10354 : row10354 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10354 := by decide +kernel

theorem rowEval10354 (x : Key → ℝ) : Integer.Sparse.eval row10354 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10354, Integer.Sparse.eval_collectBalanced, rawRowCheck10354]

def rawRow10355 : Integer.Sparse Key := [(key1023, -2), (key1021, -2), (key1021, -2), (key1176, -2), (key1129, -2), (key1129, -2), (key1225, -2), (key1225, -2), (key1202, -2), (key1202, -2), (key1201, -2), (key1201, -2), (key1023, 2), (key1008, 2), (key1008, 2), (key1081, 2), (key1043, 2), (key1043, 2), (key1216, 2), (key1216, 2), (key1202, 2), (key1202, 2), (key1195, 2), (key1195, 2)]

theorem rawRowCheck10355 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form17 = rawRow10355 := by decide +kernel

def row10355 : Integer.Sparse Key := [(key1008, 4), (key1021, -4), (key1043, 4), (key1081, 2), (key1129, -4), (key1176, -2), (key1195, 4), (key1201, -4), (key1216, 4), (key1225, -4)]

theorem rowCheck10355 : row10355 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10355 := by decide +kernel

theorem rowEval10355 (x : Key → ℝ) : Integer.Sparse.eval row10355 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10355, Integer.Sparse.eval_collectBalanced, rawRowCheck10355]

def rawRow10356 : Integer.Sparse Key := [(key1129, -2), (key1201, -2), (key1202, -2), (key1021, -2), (key1201, -2), (key1225, -2), (key1021, -2), (key1023, -2), (key1129, -2), (key1176, -2), (key1202, -2), (key1225, -2), (key1043, 2), (key1195, 2), (key1202, 2), (key1008, 2), (key1195, 2), (key1216, 2), (key1008, 2), (key1023, 2), (key1043, 2), (key1081, 2), (key1202, 2), (key1216, 2)]

theorem rawRowCheck10356 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form17 = rawRow10356 := by decide +kernel

def row10356 : Integer.Sparse Key := [(key1008, 4), (key1021, -4), (key1043, 4), (key1081, 2), (key1129, -4), (key1176, -2), (key1195, 4), (key1201, -4), (key1216, 4), (key1225, -4)]

theorem rowCheck10356 : row10356 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10356 := by decide +kernel

theorem rowEval10356 (x : Key → ℝ) : Integer.Sparse.eval row10356 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck10356, Integer.Sparse.eval_collectBalanced, rawRowCheck10356]

def rawRow10357 : Integer.Sparse Key := [(key1129, -2), (key1202, -2), (key1201, -2), (key1021, -2), (key1225, -2), (key1201, -2), (key1023, -2), (key1021, -2), (key1176, -2), (key1129, -2), (key1225, -2), (key1202, -2), (key1043, 2), (key1202, 2), (key1195, 2), (key1008, 2), (key1216, 2), (key1195, 2), (key1023, 2), (key1008, 2), (key1081, 2), (key1043, 2), (key1216, 2), (key1202, 2)]

theorem rawRowCheck10357 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form17 = rawRow10357 := by decide +kernel

def row10357 : Integer.Sparse Key := [(key1008, 4), (key1021, -4), (key1043, 4), (key1081, 2), (key1129, -4), (key1176, -2), (key1195, 4), (key1201, -4), (key1216, 4), (key1225, -4)]

theorem rowCheck10357 : row10357 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10357 := by decide +kernel

theorem rowEval10357 (x : Key → ℝ) : Integer.Sparse.eval row10357 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10357, Integer.Sparse.eval_collectBalanced, rawRowCheck10357]

def rawRow10358 : Integer.Sparse Key := [(key1201, -2), (key1129, -2), (key1202, -2), (key1201, -2), (key1021, -2), (key1225, -2), (key1129, -2), (key1202, -2), (key1021, -2), (key1225, -2), (key1023, -2), (key1176, -2), (key1195, 2), (key1043, 2), (key1202, 2), (key1195, 2), (key1008, 2), (key1216, 2), (key1043, 2), (key1202, 2), (key1008, 2), (key1216, 2), (key1023, 2), (key1081, 2)]

theorem rawRowCheck10358 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form17 = rawRow10358 := by decide +kernel

def row10358 : Integer.Sparse Key := [(key1008, 4), (key1021, -4), (key1043, 4), (key1081, 2), (key1129, -4), (key1176, -2), (key1195, 4), (key1201, -4), (key1216, 4), (key1225, -4)]

theorem rowCheck10358 : row10358 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10358 := by decide +kernel

theorem rowEval10358 (x : Key → ℝ) : Integer.Sparse.eval row10358 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck10358, Integer.Sparse.eval_collectBalanced, rawRowCheck10358]

def rawRow10359 : Integer.Sparse Key := [(key1201, -2), (key1202, -2), (key1129, -2), (key1201, -2), (key1225, -2), (key1021, -2), (key1202, -2), (key1129, -2), (key1225, -2), (key1021, -2), (key1176, -2), (key1023, -2), (key1195, 2), (key1202, 2), (key1043, 2), (key1195, 2), (key1216, 2), (key1008, 2), (key1202, 2), (key1043, 2), (key1216, 2), (key1008, 2), (key1081, 2), (key1023, 2)]

theorem rawRowCheck10359 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form17 = rawRow10359 := by decide +kernel

def row10359 : Integer.Sparse Key := [(key1008, 4), (key1021, -4), (key1043, 4), (key1081, 2), (key1129, -4), (key1176, -2), (key1195, 4), (key1201, -4), (key1216, 4), (key1225, -4)]

theorem rowCheck10359 : row10359 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10359 := by decide +kernel

theorem rowEval10359 (x : Key → ℝ) : Integer.Sparse.eval row10359 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form17) x := by
  rw [rowCheck10359, Integer.Sparse.eval_collectBalanced, rawRowCheck10359]

def rawRow10360 : Integer.Sparse Key := [(key1202, -2), (key1129, -2), (key1201, -2), (key1225, -2), (key1021, -2), (key1201, -2), (key1176, -2), (key1225, -2), (key1023, -2), (key1202, -2), (key1021, -2), (key1129, -2), (key1202, 2), (key1043, 2), (key1195, 2), (key1216, 2), (key1008, 2), (key1195, 2), (key1081, 2), (key1216, 2), (key1023, 2), (key1202, 2), (key1008, 2), (key1043, 2)]

theorem rawRowCheck10360 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form17 = rawRow10360 := by decide +kernel

def row10360 : Integer.Sparse Key := [(key1008, 4), (key1021, -4), (key1043, 4), (key1081, 2), (key1129, -4), (key1176, -2), (key1195, 4), (key1201, -4), (key1216, 4), (key1225, -4)]

theorem rowCheck10360 : row10360 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10360 := by decide +kernel

theorem rowEval10360 (x : Key → ℝ) : Integer.Sparse.eval row10360 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10360, Integer.Sparse.eval_collectBalanced, rawRowCheck10360]

def rawRow10361 : Integer.Sparse Key := [(key1202, -2), (key1201, -2), (key1129, -2), (key1225, -2), (key1201, -2), (key1021, -2), (key1225, -2), (key1176, -2), (key1202, -2), (key1023, -2), (key1129, -2), (key1021, -2), (key1202, 2), (key1195, 2), (key1043, 2), (key1216, 2), (key1195, 2), (key1008, 2), (key1216, 2), (key1081, 2), (key1202, 2), (key1023, 2), (key1043, 2), (key1008, 2)]

theorem rawRowCheck10361 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form17 = rawRow10361 := by decide +kernel

def row10361 : Integer.Sparse Key := [(key1008, 4), (key1021, -4), (key1043, 4), (key1081, 2), (key1129, -4), (key1176, -2), (key1195, 4), (key1201, -4), (key1216, 4), (key1225, -4)]

theorem rowCheck10361 : row10361 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10361 := by decide +kernel

theorem rowEval10361 (x : Key → ℝ) : Integer.Sparse.eval row10361 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form17) x := by
  rw [rowCheck10361, Integer.Sparse.eval_collectBalanced, rawRowCheck10361]

def rawRow10362 : Integer.Sparse Key := [(key1176, -2), (key1225, -2), (key1225, -2), (key1023, -2), (key1202, -2), (key1202, -2), (key1021, -2), (key1021, -2), (key1129, -2), (key1129, -2), (key1201, -2), (key1201, -2), (key1081, 2), (key1216, 2), (key1216, 2), (key1023, 2), (key1202, 2), (key1202, 2), (key1008, 2), (key1008, 2), (key1043, 2), (key1043, 2), (key1195, 2), (key1195, 2)]

theorem rawRowCheck10362 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form17 = rawRow10362 := by decide +kernel

def row10362 : Integer.Sparse Key := [(key1008, 4), (key1021, -4), (key1043, 4), (key1081, 2), (key1129, -4), (key1176, -2), (key1195, 4), (key1201, -4), (key1216, 4), (key1225, -4)]

theorem rowCheck10362 : row10362 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10362 := by decide +kernel

theorem rowEval10362 (x : Key → ℝ) : Integer.Sparse.eval row10362 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10362, Integer.Sparse.eval_collectBalanced, rawRowCheck10362]

def rawRow10363 : Integer.Sparse Key := [(key1225, -2), (key1176, -2), (key1225, -2), (key1202, -2), (key1023, -2), (key1202, -2), (key1129, -2), (key1201, -2), (key1021, -2), (key1201, -2), (key1021, -2), (key1129, -2), (key1216, 2), (key1081, 2), (key1216, 2), (key1202, 2), (key1023, 2), (key1202, 2), (key1043, 2), (key1195, 2), (key1008, 2), (key1195, 2), (key1008, 2), (key1043, 2)]

theorem rawRowCheck10363 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form17 = rawRow10363 := by decide +kernel

def row10363 : Integer.Sparse Key := [(key1008, 4), (key1021, -4), (key1043, 4), (key1081, 2), (key1129, -4), (key1176, -2), (key1195, 4), (key1201, -4), (key1216, 4), (key1225, -4)]

theorem rowCheck10363 : row10363 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10363 := by decide +kernel

theorem rowEval10363 (x : Key → ℝ) : Integer.Sparse.eval row10363 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10363, Integer.Sparse.eval_collectBalanced, rawRowCheck10363]

def rawRow10364 : Integer.Sparse Key := [(key1225, -2), (key1225, -2), (key1176, -2), (key1202, -2), (key1202, -2), (key1023, -2), (key1201, -2), (key1129, -2), (key1201, -2), (key1021, -2), (key1129, -2), (key1021, -2), (key1216, 2), (key1216, 2), (key1081, 2), (key1202, 2), (key1202, 2), (key1023, 2), (key1195, 2), (key1043, 2), (key1195, 2), (key1008, 2), (key1043, 2), (key1008, 2)]

theorem rawRowCheck10364 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form17 = rawRow10364 := by decide +kernel

def row10364 : Integer.Sparse Key := [(key1008, 4), (key1021, -4), (key1043, 4), (key1081, 2), (key1129, -4), (key1176, -2), (key1195, 4), (key1201, -4), (key1216, 4), (key1225, -4)]

theorem rowCheck10364 : row10364 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10364 := by decide +kernel

theorem rowEval10364 (x : Key → ℝ) : Integer.Sparse.eval row10364 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form17) x := by
  rw [rowCheck10364, Integer.Sparse.eval_collectBalanced, rawRowCheck10364]

def rawRow10365 : Integer.Sparse Key := [(key10, 2), (key13, 2), (key13, 2), (key93, 2), (key158, 2), (key158, 2), (key169, 2), (key169, 2), (key189, 2), (key189, 2), (key192, 2), (key192, 2), (key13, -2), (key13, -2), (key15, -2), (key96, -2), (key96, -2), (key158, -2), (key158, -2), (key163, -2), (key163, -2), (key170, -2), (key192, -2), (key192, -2)]

theorem rawRowCheck10365 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form18 = rawRow10365 := by decide +kernel

def row10365 : Integer.Sparse Key := [(key10, 2), (key15, -2), (key93, 2), (key96, -4), (key163, -4), (key169, 4), (key170, -2), (key189, 4)]

theorem rowCheck10365 : row10365 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10365 := by decide +kernel

theorem rowEval10365 (x : Key → ℝ) : Integer.Sparse.eval row10365 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck10365, Integer.Sparse.eval_collectBalanced, rawRowCheck10365]

def rawRow10366 : Integer.Sparse Key := [(key13, 2), (key10, 2), (key13, 2), (key158, 2), (key93, 2), (key158, 2), (key189, 2), (key192, 2), (key169, 2), (key192, 2), (key169, 2), (key189, 2), (key13, -2), (key15, -2), (key13, -2), (key158, -2), (key163, -2), (key96, -2), (key163, -2), (key96, -2), (key158, -2), (key192, -2), (key170, -2), (key192, -2)]

theorem rawRowCheck10366 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form18 = rawRow10366 := by decide +kernel

def row10366 : Integer.Sparse Key := [(key10, 2), (key15, -2), (key93, 2), (key96, -4), (key163, -4), (key169, 4), (key170, -2), (key189, 4)]

theorem rowCheck10366 : row10366 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10366 := by decide +kernel

theorem rowEval10366 (x : Key → ℝ) : Integer.Sparse.eval row10366 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck10366, Integer.Sparse.eval_collectBalanced, rawRowCheck10366]

def rawRow10367 : Integer.Sparse Key := [(key13, 2), (key13, 2), (key10, 2), (key158, 2), (key158, 2), (key93, 2), (key192, 2), (key189, 2), (key192, 2), (key169, 2), (key189, 2), (key169, 2), (key15, -2), (key13, -2), (key13, -2), (key163, -2), (key158, -2), (key163, -2), (key96, -2), (key158, -2), (key96, -2), (key192, -2), (key192, -2), (key170, -2)]

theorem rawRowCheck10367 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form18 = rawRow10367 := by decide +kernel

def row10367 : Integer.Sparse Key := [(key10, 2), (key15, -2), (key93, 2), (key96, -4), (key163, -4), (key169, 4), (key170, -2), (key189, 4)]

theorem rowCheck10367 : row10367 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10367 := by decide +kernel

theorem rowEval10367 (x : Key → ℝ) : Integer.Sparse.eval row10367 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck10367, Integer.Sparse.eval_collectBalanced, rawRowCheck10367]

end MUB6.Certificate.GramRows

end OAI
