import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block6
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block16
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block17
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow8960 : Integer.Sparse Key := [(key2274, -2), (key2276, -2), (key2341, -2), (key2174, -2), (key2176, -2), (key2274, -2), (key2279, -2), (key2341, -2), (key2343, -2), (key2176, -2), (key2276, -2), (key2279, -2), (key2274, 2), (key2276, 2), (key2341, 2), (key2077, 2), (key2079, 2), (key2274, 2), (key2287, 2), (key2341, 2), (key2347, 2), (key2079, 2), (key2276, 2), (key2287, 2)]

theorem rawRowCheck8960 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form7 = rawRow8960 := by decide +kernel

def row8960 : Integer.Sparse Key := [(key2077, 2), (key2079, 4), (key2174, -2), (key2176, -4), (key2279, -4), (key2287, 4), (key2343, -2), (key2347, 2)]

theorem rowCheck8960 : row8960 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8960 := by decide +kernel

theorem rowEval8960 (x : Key → ℝ) : Integer.Sparse.eval row8960 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8960, Integer.Sparse.eval_collectBalanced, rawRowCheck8960]

def rawRow8961 : Integer.Sparse Key := [(key2276, -2), (key2274, -2), (key2341, -2), (key2176, -2), (key2174, -2), (key2279, -2), (key2274, -2), (key2343, -2), (key2341, -2), (key2176, -2), (key2279, -2), (key2276, -2), (key2276, 2), (key2274, 2), (key2341, 2), (key2079, 2), (key2077, 2), (key2287, 2), (key2274, 2), (key2347, 2), (key2341, 2), (key2079, 2), (key2287, 2), (key2276, 2)]

theorem rawRowCheck8961 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form7 = rawRow8961 := by decide +kernel

def row8961 : Integer.Sparse Key := [(key2077, 2), (key2079, 4), (key2174, -2), (key2176, -4), (key2279, -4), (key2287, 4), (key2343, -2), (key2347, 2)]

theorem rowCheck8961 : row8961 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8961 := by decide +kernel

theorem rowEval8961 (x : Key → ℝ) : Integer.Sparse.eval row8961 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8961, Integer.Sparse.eval_collectBalanced, rawRowCheck8961]

def rawRow8962 : Integer.Sparse Key := [(key2274, -2), (key2341, -2), (key2276, -2), (key2274, -2), (key2341, -2), (key2174, -2), (key2343, -2), (key2176, -2), (key2279, -2), (key2276, -2), (key2176, -2), (key2279, -2), (key2274, 2), (key2341, 2), (key2276, 2), (key2274, 2), (key2341, 2), (key2077, 2), (key2347, 2), (key2079, 2), (key2287, 2), (key2276, 2), (key2079, 2), (key2287, 2)]

theorem rawRowCheck8962 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form7 = rawRow8962 := by decide +kernel

def row8962 : Integer.Sparse Key := [(key2077, 2), (key2079, 4), (key2174, -2), (key2176, -4), (key2279, -4), (key2287, 4), (key2343, -2), (key2347, 2)]

theorem rowCheck8962 : row8962 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8962 := by decide +kernel

theorem rowEval8962 (x : Key → ℝ) : Integer.Sparse.eval row8962 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8962, Integer.Sparse.eval_collectBalanced, rawRowCheck8962]

def rawRow8963 : Integer.Sparse Key := [(key2341, -2), (key2274, -2), (key2276, -2), (key2341, -2), (key2274, -2), (key2343, -2), (key2174, -2), (key2279, -2), (key2176, -2), (key2276, -2), (key2279, -2), (key2176, -2), (key2341, 2), (key2274, 2), (key2276, 2), (key2341, 2), (key2274, 2), (key2347, 2), (key2077, 2), (key2287, 2), (key2079, 2), (key2276, 2), (key2287, 2), (key2079, 2)]

theorem rawRowCheck8963 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form7 = rawRow8963 := by decide +kernel

def row8963 : Integer.Sparse Key := [(key2077, 2), (key2079, 4), (key2174, -2), (key2176, -4), (key2279, -4), (key2287, 4), (key2343, -2), (key2347, 2)]

theorem rowCheck8963 : row8963 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8963 := by decide +kernel

theorem rowEval8963 (x : Key → ℝ) : Integer.Sparse.eval row8963 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck8963, Integer.Sparse.eval_collectBalanced, rawRowCheck8963]

def rawRow8964 : Integer.Sparse Key := [(key2276, -2), (key2341, -2), (key2274, -2), (key2279, -2), (key2343, -2), (key2176, -2), (key2341, -2), (key2174, -2), (key2274, -2), (key2279, -2), (key2176, -2), (key2276, -2), (key2276, 2), (key2341, 2), (key2274, 2), (key2287, 2), (key2347, 2), (key2079, 2), (key2341, 2), (key2077, 2), (key2274, 2), (key2287, 2), (key2079, 2), (key2276, 2)]

theorem rawRowCheck8964 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form7 = rawRow8964 := by decide +kernel

def row8964 : Integer.Sparse Key := [(key2077, 2), (key2079, 4), (key2174, -2), (key2176, -4), (key2279, -4), (key2287, 4), (key2343, -2), (key2347, 2)]

theorem rowCheck8964 : row8964 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8964 := by decide +kernel

theorem rowEval8964 (x : Key → ℝ) : Integer.Sparse.eval row8964 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8964, Integer.Sparse.eval_collectBalanced, rawRowCheck8964]

def rawRow8965 : Integer.Sparse Key := [(key2341, -2), (key2276, -2), (key2274, -2), (key2343, -2), (key2279, -2), (key2341, -2), (key2176, -2), (key2274, -2), (key2174, -2), (key2279, -2), (key2276, -2), (key2176, -2), (key2341, 2), (key2276, 2), (key2274, 2), (key2347, 2), (key2287, 2), (key2341, 2), (key2079, 2), (key2274, 2), (key2077, 2), (key2287, 2), (key2276, 2), (key2079, 2)]

theorem rawRowCheck8965 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form7 = rawRow8965 := by decide +kernel

def row8965 : Integer.Sparse Key := [(key2077, 2), (key2079, 4), (key2174, -2), (key2176, -4), (key2279, -4), (key2287, 4), (key2343, -2), (key2347, 2)]

theorem rowCheck8965 : row8965 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8965 := by decide +kernel

theorem rowEval8965 (x : Key → ℝ) : Integer.Sparse.eval row8965 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck8965, Integer.Sparse.eval_collectBalanced, rawRowCheck8965]

def rawRow8966 : Integer.Sparse Key := [(key2279, -2), (key2279, -2), (key2343, -2), (key2176, -2), (key2176, -2), (key2276, -2), (key2276, -2), (key2341, -2), (key2341, -2), (key2174, -2), (key2274, -2), (key2274, -2), (key2287, 2), (key2287, 2), (key2347, 2), (key2079, 2), (key2079, 2), (key2276, 2), (key2276, 2), (key2341, 2), (key2341, 2), (key2077, 2), (key2274, 2), (key2274, 2)]

theorem rawRowCheck8966 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form7 = rawRow8966 := by decide +kernel

def row8966 : Integer.Sparse Key := [(key2077, 2), (key2079, 4), (key2174, -2), (key2176, -4), (key2279, -4), (key2287, 4), (key2343, -2), (key2347, 2)]

theorem rowCheck8966 : row8966 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8966 := by decide +kernel

theorem rowEval8966 (x : Key → ℝ) : Integer.Sparse.eval row8966 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8966, Integer.Sparse.eval_collectBalanced, rawRowCheck8966]

def rawRow8967 : Integer.Sparse Key := [(key2279, -2), (key2343, -2), (key2279, -2), (key2276, -2), (key2341, -2), (key2176, -2), (key2341, -2), (key2176, -2), (key2276, -2), (key2274, -2), (key2174, -2), (key2274, -2), (key2287, 2), (key2347, 2), (key2287, 2), (key2276, 2), (key2341, 2), (key2079, 2), (key2341, 2), (key2079, 2), (key2276, 2), (key2274, 2), (key2077, 2), (key2274, 2)]

theorem rawRowCheck8967 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form7 = rawRow8967 := by decide +kernel

def row8967 : Integer.Sparse Key := [(key2077, 2), (key2079, 4), (key2174, -2), (key2176, -4), (key2279, -4), (key2287, 4), (key2343, -2), (key2347, 2)]

theorem rowCheck8967 : row8967 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8967 := by decide +kernel

theorem rowEval8967 (x : Key → ℝ) : Integer.Sparse.eval row8967 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8967, Integer.Sparse.eval_collectBalanced, rawRowCheck8967]

def rawRow8968 : Integer.Sparse Key := [(key2343, -2), (key2279, -2), (key2279, -2), (key2341, -2), (key2276, -2), (key2341, -2), (key2176, -2), (key2276, -2), (key2176, -2), (key2274, -2), (key2274, -2), (key2174, -2), (key2347, 2), (key2287, 2), (key2287, 2), (key2341, 2), (key2276, 2), (key2341, 2), (key2079, 2), (key2276, 2), (key2079, 2), (key2274, 2), (key2274, 2), (key2077, 2)]

theorem rawRowCheck8968 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form7 = rawRow8968 := by decide +kernel

def row8968 : Integer.Sparse Key := [(key2077, 2), (key2079, 4), (key2174, -2), (key2176, -4), (key2279, -4), (key2287, 4), (key2343, -2), (key2347, 2)]

theorem rowCheck8968 : row8968 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8968 := by decide +kernel

theorem rowEval8968 (x : Key → ℝ) : Integer.Sparse.eval row8968 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck8968, Integer.Sparse.eval_collectBalanced, rawRowCheck8968]

def rawRow8969 : Integer.Sparse Key := [(key817, -2), (key818, -2), (key818, -2), (key817, -2), (key818, -2), (key817, -2), (key825, -2), (key818, -2), (key825, -2), (key818, -2), (key818, -2), (key825, -2), (key897, 1), (key898, 1), (key897, 1), (key902, 1), (key898, 1), (key902, 1), (key897, 1), (key898, 1), (key897, 1), (key908, 1), (key898, 1), (key908, 1), (key897, 1), (key902, 1), (key897, 1), (key908, 1), (key902, 1), (key908, 1), (key898, 1), (key902, 1), (key898, 1), (key908, 1), (key902, 1), (key908, 1)]

theorem rawRowCheck8969 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form8 = rawRow8969 := by decide +kernel

def row8969 : Integer.Sparse Key := [(key817, -6), (key818, -12), (key825, -6), (key897, 6), (key898, 6), (key902, 6), (key908, 6)]

theorem rowCheck8969 : row8969 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8969 := by decide +kernel

theorem rowEval8969 (x : Key → ℝ) : Integer.Sparse.eval row8969 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8969, Integer.Sparse.eval_collectBalanced, rawRowCheck8969]

def rawRow8970 : Integer.Sparse Key := [(key818, -2), (key817, -2), (key818, -2), (key818, -2), (key817, -2), (key825, -2), (key817, -2), (key825, -2), (key818, -2), (key818, -2), (key825, -2), (key818, -2), (key898, 1), (key897, 1), (key902, 1), (key897, 1), (key902, 1), (key898, 1), (key898, 1), (key897, 1), (key908, 1), (key897, 1), (key908, 1), (key898, 1), (key902, 1), (key897, 1), (key908, 1), (key897, 1), (key908, 1), (key902, 1), (key902, 1), (key898, 1), (key908, 1), (key898, 1), (key908, 1), (key902, 1)]

theorem rawRowCheck8970 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form8 = rawRow8970 := by decide +kernel

def row8970 : Integer.Sparse Key := [(key817, -6), (key818, -12), (key825, -6), (key897, 6), (key898, 6), (key902, 6), (key908, 6)]

theorem rowCheck8970 : row8970 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8970 := by decide +kernel

theorem rowEval8970 (x : Key → ℝ) : Integer.Sparse.eval row8970 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8970, Integer.Sparse.eval_collectBalanced, rawRowCheck8970]

def rawRow8971 : Integer.Sparse Key := [(key818, -2), (key818, -2), (key817, -2), (key825, -2), (key825, -2), (key818, -2), (key818, -2), (key817, -2), (key817, -2), (key825, -2), (key818, -2), (key818, -2), (key902, 1), (key902, 1), (key898, 1), (key898, 1), (key897, 1), (key897, 1), (key908, 1), (key908, 1), (key898, 1), (key898, 1), (key897, 1), (key897, 1), (key908, 1), (key908, 1), (key902, 1), (key902, 1), (key897, 1), (key897, 1), (key908, 1), (key908, 1), (key902, 1), (key902, 1), (key898, 1), (key898, 1)]

theorem rawRowCheck8971 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form8 = rawRow8971 := by decide +kernel

def row8971 : Integer.Sparse Key := [(key817, -6), (key818, -12), (key825, -6), (key897, 6), (key898, 6), (key902, 6), (key908, 6)]

theorem rowCheck8971 : row8971 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8971 := by decide +kernel

theorem rowEval8971 (x : Key → ℝ) : Integer.Sparse.eval row8971 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8971, Integer.Sparse.eval_collectBalanced, rawRowCheck8971]

def rawRow8972 : Integer.Sparse Key := [(key825, -2), (key825, -2), (key825, -2), (key818, -2), (key818, -2), (key818, -2), (key818, -2), (key818, -2), (key818, -2), (key817, -2), (key817, -2), (key817, -2), (key908, 1), (key908, 1), (key908, 1), (key908, 1), (key908, 1), (key908, 1), (key902, 1), (key902, 1), (key902, 1), (key902, 1), (key902, 1), (key902, 1), (key898, 1), (key898, 1), (key898, 1), (key898, 1), (key898, 1), (key898, 1), (key897, 1), (key897, 1), (key897, 1), (key897, 1), (key897, 1), (key897, 1)]

theorem rawRowCheck8972 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form8 = rawRow8972 := by decide +kernel

def row8972 : Integer.Sparse Key := [(key817, -6), (key818, -12), (key825, -6), (key897, 6), (key898, 6), (key902, 6), (key908, 6)]

theorem rowCheck8972 : row8972 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8972 := by decide +kernel

theorem rowEval8972 (x : Key → ℝ) : Integer.Sparse.eval row8972 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8972, Integer.Sparse.eval_collectBalanced, rawRowCheck8972]

def rawRow8973 : Integer.Sparse Key := [(key737, -2), (key738, -2), (key738, -2), (key897, -2), (key898, -2), (key897, -2), (key908, -2), (key898, -2), (key908, -2), (key960, -2), (key960, -2), (key964, -2), (key737, 1), (key738, 1), (key737, 1), (key743, 1), (key738, 1), (key743, 1), (key817, 1), (key818, 1), (key817, 1), (key825, 1), (key818, 1), (key825, 1), (key897, 1), (key902, 1), (key897, 1), (key908, 1), (key902, 1), (key908, 1), (key960, 1), (key962, 1), (key960, 1), (key964, 1), (key962, 1), (key964, 1)]

theorem rawRowCheck8973 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form8 = rawRow8973 := by decide +kernel

def row8973 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key817, 2), (key818, 2), (key825, 2), (key897, -2), (key898, -4), (key902, 2), (key908, -2), (key960, -2), (key962, 2)]

theorem rowCheck8973 : row8973 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8973 := by decide +kernel

theorem rowEval8973 (x : Key → ℝ) : Integer.Sparse.eval row8973 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8973, Integer.Sparse.eval_collectBalanced, rawRowCheck8973]

def rawRow8974 : Integer.Sparse Key := [(key738, -2), (key737, -2), (key738, -2), (key898, -2), (key897, -2), (key908, -2), (key897, -2), (key908, -2), (key898, -2), (key960, -2), (key964, -2), (key960, -2), (key738, 1), (key737, 1), (key743, 1), (key737, 1), (key743, 1), (key738, 1), (key818, 1), (key817, 1), (key825, 1), (key817, 1), (key825, 1), (key818, 1), (key902, 1), (key897, 1), (key908, 1), (key897, 1), (key908, 1), (key902, 1), (key962, 1), (key960, 1), (key964, 1), (key960, 1), (key964, 1), (key962, 1)]

theorem rawRowCheck8974 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form8 = rawRow8974 := by decide +kernel

def row8974 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key817, 2), (key818, 2), (key825, 2), (key897, -2), (key898, -4), (key902, 2), (key908, -2), (key960, -2), (key962, 2)]

theorem rowCheck8974 : row8974 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8974 := by decide +kernel

theorem rowEval8974 (x : Key → ℝ) : Integer.Sparse.eval row8974 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8974, Integer.Sparse.eval_collectBalanced, rawRowCheck8974]

def rawRow8975 : Integer.Sparse Key := [(key738, -2), (key738, -2), (key737, -2), (key908, -2), (key908, -2), (key898, -2), (key898, -2), (key897, -2), (key897, -2), (key964, -2), (key960, -2), (key960, -2), (key743, 1), (key743, 1), (key738, 1), (key738, 1), (key737, 1), (key737, 1), (key825, 1), (key825, 1), (key818, 1), (key818, 1), (key817, 1), (key817, 1), (key908, 1), (key908, 1), (key902, 1), (key902, 1), (key897, 1), (key897, 1), (key964, 1), (key964, 1), (key962, 1), (key962, 1), (key960, 1), (key960, 1)]

theorem rawRowCheck8975 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form8 = rawRow8975 := by decide +kernel

def row8975 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key817, 2), (key818, 2), (key825, 2), (key897, -2), (key898, -4), (key902, 2), (key908, -2), (key960, -2), (key962, 2)]

theorem rowCheck8975 : row8975 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8975 := by decide +kernel

theorem rowEval8975 (x : Key → ℝ) : Integer.Sparse.eval row8975 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8975, Integer.Sparse.eval_collectBalanced, rawRowCheck8975]

def rawRow8976 : Integer.Sparse Key := [(key897, -2), (key898, -2), (key960, -2), (key737, -2), (key738, -2), (key897, -2), (key908, -2), (key960, -2), (key964, -2), (key738, -2), (key898, -2), (key908, -2), (key817, 1), (key818, 1), (key897, 1), (key902, 1), (key960, 1), (key962, 1), (key737, 1), (key738, 1), (key897, 1), (key908, 1), (key960, 1), (key964, 1), (key737, 1), (key743, 1), (key817, 1), (key825, 1), (key962, 1), (key964, 1), (key738, 1), (key743, 1), (key818, 1), (key825, 1), (key902, 1), (key908, 1)]

theorem rawRowCheck8976 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form8 = rawRow8976 := by decide +kernel

def row8976 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key817, 2), (key818, 2), (key825, 2), (key897, -2), (key898, -4), (key902, 2), (key908, -2), (key960, -2), (key962, 2)]

theorem rowCheck8976 : row8976 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8976 := by decide +kernel

theorem rowEval8976 (x : Key → ℝ) : Integer.Sparse.eval row8976 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8976, Integer.Sparse.eval_collectBalanced, rawRowCheck8976]

def rawRow8977 : Integer.Sparse Key := [(key898, -2), (key897, -2), (key960, -2), (key738, -2), (key737, -2), (key908, -2), (key897, -2), (key964, -2), (key960, -2), (key738, -2), (key908, -2), (key898, -2), (key818, 1), (key817, 1), (key902, 1), (key897, 1), (key962, 1), (key960, 1), (key738, 1), (key737, 1), (key908, 1), (key897, 1), (key964, 1), (key960, 1), (key743, 1), (key737, 1), (key825, 1), (key817, 1), (key964, 1), (key962, 1), (key743, 1), (key738, 1), (key825, 1), (key818, 1), (key908, 1), (key902, 1)]

theorem rawRowCheck8977 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form8 = rawRow8977 := by decide +kernel

def row8977 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key817, 2), (key818, 2), (key825, 2), (key897, -2), (key898, -4), (key902, 2), (key908, -2), (key960, -2), (key962, 2)]

theorem rowCheck8977 : row8977 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8977 := by decide +kernel

theorem rowEval8977 (x : Key → ℝ) : Integer.Sparse.eval row8977 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8977, Integer.Sparse.eval_collectBalanced, rawRowCheck8977]

def rawRow8978 : Integer.Sparse Key := [(key897, -2), (key960, -2), (key898, -2), (key897, -2), (key960, -2), (key737, -2), (key964, -2), (key738, -2), (key908, -2), (key898, -2), (key738, -2), (key908, -2), (key897, 1), (key960, 1), (key817, 1), (key962, 1), (key818, 1), (key902, 1), (key897, 1), (key960, 1), (key737, 1), (key964, 1), (key738, 1), (key908, 1), (key817, 1), (key962, 1), (key737, 1), (key964, 1), (key743, 1), (key825, 1), (key818, 1), (key902, 1), (key738, 1), (key908, 1), (key743, 1), (key825, 1)]

theorem rawRowCheck8978 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form8 = rawRow8978 := by decide +kernel

def row8978 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key817, 2), (key818, 2), (key825, 2), (key897, -2), (key898, -4), (key902, 2), (key908, -2), (key960, -2), (key962, 2)]

theorem rowCheck8978 : row8978 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8978 := by decide +kernel

theorem rowEval8978 (x : Key → ℝ) : Integer.Sparse.eval row8978 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8978, Integer.Sparse.eval_collectBalanced, rawRowCheck8978]

def rawRow8979 : Integer.Sparse Key := [(key960, -2), (key897, -2), (key898, -2), (key960, -2), (key897, -2), (key964, -2), (key737, -2), (key908, -2), (key738, -2), (key898, -2), (key908, -2), (key738, -2), (key960, 1), (key897, 1), (key962, 1), (key817, 1), (key902, 1), (key818, 1), (key960, 1), (key897, 1), (key964, 1), (key737, 1), (key908, 1), (key738, 1), (key962, 1), (key817, 1), (key964, 1), (key737, 1), (key825, 1), (key743, 1), (key902, 1), (key818, 1), (key908, 1), (key738, 1), (key825, 1), (key743, 1)]

theorem rawRowCheck8979 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form8 = rawRow8979 := by decide +kernel

def row8979 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key817, 2), (key818, 2), (key825, 2), (key897, -2), (key898, -4), (key902, 2), (key908, -2), (key960, -2), (key962, 2)]

theorem rowCheck8979 : row8979 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8979 := by decide +kernel

theorem rowEval8979 (x : Key → ℝ) : Integer.Sparse.eval row8979 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck8979, Integer.Sparse.eval_collectBalanced, rawRowCheck8979]

def rawRow8980 : Integer.Sparse Key := [(key898, -2), (key960, -2), (key897, -2), (key908, -2), (key964, -2), (key738, -2), (key960, -2), (key737, -2), (key897, -2), (key908, -2), (key738, -2), (key898, -2), (key902, 1), (key962, 1), (key818, 1), (key960, 1), (key817, 1), (key897, 1), (key908, 1), (key964, 1), (key738, 1), (key960, 1), (key737, 1), (key897, 1), (key825, 1), (key964, 1), (key743, 1), (key962, 1), (key737, 1), (key817, 1), (key825, 1), (key908, 1), (key743, 1), (key902, 1), (key738, 1), (key818, 1)]

theorem rawRowCheck8980 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form8 = rawRow8980 := by decide +kernel

def row8980 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key817, 2), (key818, 2), (key825, 2), (key897, -2), (key898, -4), (key902, 2), (key908, -2), (key960, -2), (key962, 2)]

theorem rowCheck8980 : row8980 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8980 := by decide +kernel

theorem rowEval8980 (x : Key → ℝ) : Integer.Sparse.eval row8980 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8980, Integer.Sparse.eval_collectBalanced, rawRowCheck8980]

def rawRow8981 : Integer.Sparse Key := [(key960, -2), (key898, -2), (key897, -2), (key964, -2), (key908, -2), (key960, -2), (key738, -2), (key897, -2), (key737, -2), (key908, -2), (key898, -2), (key738, -2), (key962, 1), (key902, 1), (key960, 1), (key818, 1), (key897, 1), (key817, 1), (key964, 1), (key908, 1), (key960, 1), (key738, 1), (key897, 1), (key737, 1), (key964, 1), (key825, 1), (key962, 1), (key743, 1), (key817, 1), (key737, 1), (key908, 1), (key825, 1), (key902, 1), (key743, 1), (key818, 1), (key738, 1)]

theorem rawRowCheck8981 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form8 = rawRow8981 := by decide +kernel

def row8981 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key817, 2), (key818, 2), (key825, 2), (key897, -2), (key898, -4), (key902, 2), (key908, -2), (key960, -2), (key962, 2)]

theorem rowCheck8981 : row8981 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8981 := by decide +kernel

theorem rowEval8981 (x : Key → ℝ) : Integer.Sparse.eval row8981 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck8981, Integer.Sparse.eval_collectBalanced, rawRowCheck8981]

def rawRow8982 : Integer.Sparse Key := [(key908, -2), (key908, -2), (key964, -2), (key738, -2), (key738, -2), (key898, -2), (key898, -2), (key960, -2), (key960, -2), (key737, -2), (key897, -2), (key897, -2), (key825, 1), (key825, 1), (key908, 1), (key908, 1), (key964, 1), (key964, 1), (key743, 1), (key743, 1), (key902, 1), (key902, 1), (key962, 1), (key962, 1), (key738, 1), (key738, 1), (key818, 1), (key818, 1), (key960, 1), (key960, 1), (key737, 1), (key737, 1), (key817, 1), (key817, 1), (key897, 1), (key897, 1)]

theorem rawRowCheck8982 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form8 = rawRow8982 := by decide +kernel

def row8982 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key817, 2), (key818, 2), (key825, 2), (key897, -2), (key898, -4), (key902, 2), (key908, -2), (key960, -2), (key962, 2)]

theorem rowCheck8982 : row8982 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8982 := by decide +kernel

theorem rowEval8982 (x : Key → ℝ) : Integer.Sparse.eval row8982 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8982, Integer.Sparse.eval_collectBalanced, rawRowCheck8982]

def rawRow8983 : Integer.Sparse Key := [(key908, -2), (key964, -2), (key908, -2), (key898, -2), (key960, -2), (key738, -2), (key960, -2), (key738, -2), (key898, -2), (key897, -2), (key737, -2), (key897, -2), (key908, 1), (key964, 1), (key825, 1), (key964, 1), (key825, 1), (key908, 1), (key902, 1), (key962, 1), (key743, 1), (key962, 1), (key743, 1), (key902, 1), (key818, 1), (key960, 1), (key738, 1), (key960, 1), (key738, 1), (key818, 1), (key817, 1), (key897, 1), (key737, 1), (key897, 1), (key737, 1), (key817, 1)]

theorem rawRowCheck8983 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form8 = rawRow8983 := by decide +kernel

def row8983 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key817, 2), (key818, 2), (key825, 2), (key897, -2), (key898, -4), (key902, 2), (key908, -2), (key960, -2), (key962, 2)]

theorem rowCheck8983 : row8983 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8983 := by decide +kernel

theorem rowEval8983 (x : Key → ℝ) : Integer.Sparse.eval row8983 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8983, Integer.Sparse.eval_collectBalanced, rawRowCheck8983]

def rawRow8984 : Integer.Sparse Key := [(key964, -2), (key908, -2), (key908, -2), (key960, -2), (key898, -2), (key960, -2), (key738, -2), (key898, -2), (key738, -2), (key897, -2), (key897, -2), (key737, -2), (key964, 1), (key908, 1), (key964, 1), (key825, 1), (key908, 1), (key825, 1), (key962, 1), (key902, 1), (key962, 1), (key743, 1), (key902, 1), (key743, 1), (key960, 1), (key818, 1), (key960, 1), (key738, 1), (key818, 1), (key738, 1), (key897, 1), (key817, 1), (key897, 1), (key737, 1), (key817, 1), (key737, 1)]

theorem rawRowCheck8984 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form8 = rawRow8984 := by decide +kernel

def row8984 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key817, 2), (key818, 2), (key825, 2), (key897, -2), (key898, -4), (key902, 2), (key908, -2), (key960, -2), (key962, 2)]

theorem rowCheck8984 : row8984 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8984 := by decide +kernel

theorem rowEval8984 (x : Key → ℝ) : Integer.Sparse.eval row8984 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck8984, Integer.Sparse.eval_collectBalanced, rawRowCheck8984]

def rawRow8985 : Integer.Sparse Key := [(key2274, 1), (key2276, 1), (key2274, 1), (key2279, 1), (key2276, 1), (key2279, 1), (key2274, 1), (key2276, 1), (key2274, 1), (key2287, 1), (key2276, 1), (key2287, 1), (key2274, 1), (key2279, 1), (key2274, 1), (key2287, 1), (key2279, 1), (key2287, 1), (key2276, 1), (key2279, 1), (key2276, 1), (key2287, 1), (key2279, 1), (key2287, 1), (key2341, -2), (key2341, -2), (key2343, -2), (key2341, -2), (key2341, -2), (key2347, -2), (key2341, -2), (key2343, -2), (key2341, -2), (key2347, -2), (key2343, -2), (key2347, -2)]

theorem rawRowCheck8985 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form9 = rawRow8985 := by decide +kernel

def row8985 : Integer.Sparse Key := [(key2274, 6), (key2276, 6), (key2279, 6), (key2287, 6), (key2341, -12), (key2343, -6), (key2347, -6)]

theorem rowCheck8985 : row8985 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8985 := by decide +kernel

theorem rowEval8985 (x : Key → ℝ) : Integer.Sparse.eval row8985 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form9) x := by
  rw [rowCheck8985, Integer.Sparse.eval_collectBalanced, rawRowCheck8985]

def rawRow8986 : Integer.Sparse Key := [(key2276, 1), (key2274, 1), (key2279, 1), (key2274, 1), (key2279, 1), (key2276, 1), (key2276, 1), (key2274, 1), (key2287, 1), (key2274, 1), (key2287, 1), (key2276, 1), (key2279, 1), (key2274, 1), (key2287, 1), (key2274, 1), (key2287, 1), (key2279, 1), (key2279, 1), (key2276, 1), (key2287, 1), (key2276, 1), (key2287, 1), (key2279, 1), (key2341, -2), (key2343, -2), (key2341, -2), (key2341, -2), (key2347, -2), (key2341, -2), (key2343, -2), (key2341, -2), (key2347, -2), (key2341, -2), (key2347, -2), (key2343, -2)]

theorem rawRowCheck8986 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form9 = rawRow8986 := by decide +kernel

def row8986 : Integer.Sparse Key := [(key2274, 6), (key2276, 6), (key2279, 6), (key2287, 6), (key2341, -12), (key2343, -6), (key2347, -6)]

theorem rowCheck8986 : row8986 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8986 := by decide +kernel

theorem rowEval8986 (x : Key → ℝ) : Integer.Sparse.eval row8986 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8986, Integer.Sparse.eval_collectBalanced, rawRowCheck8986]

def rawRow8987 : Integer.Sparse Key := [(key2279, 1), (key2279, 1), (key2276, 1), (key2276, 1), (key2274, 1), (key2274, 1), (key2287, 1), (key2287, 1), (key2276, 1), (key2276, 1), (key2274, 1), (key2274, 1), (key2287, 1), (key2287, 1), (key2279, 1), (key2279, 1), (key2274, 1), (key2274, 1), (key2287, 1), (key2287, 1), (key2279, 1), (key2279, 1), (key2276, 1), (key2276, 1), (key2343, -2), (key2341, -2), (key2341, -2), (key2347, -2), (key2341, -2), (key2341, -2), (key2347, -2), (key2347, -2), (key2343, -2), (key2343, -2), (key2341, -2), (key2341, -2)]

theorem rawRowCheck8987 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form9 = rawRow8987 := by decide +kernel

def row8987 : Integer.Sparse Key := [(key2274, 6), (key2276, 6), (key2279, 6), (key2287, 6), (key2341, -12), (key2343, -6), (key2347, -6)]

theorem rowCheck8987 : row8987 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8987 := by decide +kernel

theorem rowEval8987 (x : Key → ℝ) : Integer.Sparse.eval row8987 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8987, Integer.Sparse.eval_collectBalanced, rawRowCheck8987]

def rawRow8988 : Integer.Sparse Key := [(key2287, 1), (key2287, 1), (key2287, 1), (key2287, 1), (key2287, 1), (key2287, 1), (key2279, 1), (key2279, 1), (key2279, 1), (key2279, 1), (key2279, 1), (key2279, 1), (key2276, 1), (key2276, 1), (key2276, 1), (key2276, 1), (key2276, 1), (key2276, 1), (key2274, 1), (key2274, 1), (key2274, 1), (key2274, 1), (key2274, 1), (key2274, 1), (key2347, -2), (key2347, -2), (key2347, -2), (key2343, -2), (key2343, -2), (key2343, -2), (key2341, -2), (key2341, -2), (key2341, -2), (key2341, -2), (key2341, -2), (key2341, -2)]

theorem rawRowCheck8988 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form9 = rawRow8988 := by decide +kernel

def row8988 : Integer.Sparse Key := [(key2274, 6), (key2276, 6), (key2279, 6), (key2287, 6), (key2341, -12), (key2343, -6), (key2347, -6)]

theorem rowCheck8988 : row8988 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8988 := by decide +kernel

theorem rowEval8988 (x : Key → ℝ) : Integer.Sparse.eval row8988 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8988, Integer.Sparse.eval_collectBalanced, rawRowCheck8988]

def rawRow8989 : Integer.Sparse Key := [(key2077, 1), (key2079, 1), (key2077, 1), (key2085, 1), (key2079, 1), (key2085, 1), (key2174, 1), (key2176, 1), (key2174, 1), (key2187, 1), (key2176, 1), (key2187, 1), (key2274, 1), (key2279, 1), (key2274, 1), (key2287, 1), (key2279, 1), (key2287, 1), (key2341, 1), (key2343, 1), (key2341, 1), (key2347, 1), (key2343, 1), (key2347, 1), (key2079, -2), (key2079, -2), (key2085, -2), (key2176, -2), (key2176, -2), (key2187, -2), (key2276, -2), (key2279, -2), (key2276, -2), (key2287, -2), (key2279, -2), (key2287, -2)]

theorem rawRowCheck8989 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form9 = rawRow8989 := by decide +kernel

def row8989 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, 2), (key2276, -4), (key2279, -2), (key2287, -2), (key2341, 2), (key2343, 2), (key2347, 2)]

theorem rowCheck8989 : row8989 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8989 := by decide +kernel

theorem rowEval8989 (x : Key → ℝ) : Integer.Sparse.eval row8989 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form9) x := by
  rw [rowCheck8989, Integer.Sparse.eval_collectBalanced, rawRowCheck8989]

def rawRow8990 : Integer.Sparse Key := [(key2079, 1), (key2077, 1), (key2085, 1), (key2077, 1), (key2085, 1), (key2079, 1), (key2176, 1), (key2174, 1), (key2187, 1), (key2174, 1), (key2187, 1), (key2176, 1), (key2279, 1), (key2274, 1), (key2287, 1), (key2274, 1), (key2287, 1), (key2279, 1), (key2343, 1), (key2341, 1), (key2347, 1), (key2341, 1), (key2347, 1), (key2343, 1), (key2079, -2), (key2085, -2), (key2079, -2), (key2176, -2), (key2187, -2), (key2176, -2), (key2279, -2), (key2276, -2), (key2287, -2), (key2276, -2), (key2287, -2), (key2279, -2)]

theorem rawRowCheck8990 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form9 = rawRow8990 := by decide +kernel

def row8990 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, 2), (key2276, -4), (key2279, -2), (key2287, -2), (key2341, 2), (key2343, 2), (key2347, 2)]

theorem rowCheck8990 : row8990 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8990 := by decide +kernel

theorem rowEval8990 (x : Key → ℝ) : Integer.Sparse.eval row8990 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8990, Integer.Sparse.eval_collectBalanced, rawRowCheck8990]

def rawRow8991 : Integer.Sparse Key := [(key2085, 1), (key2085, 1), (key2079, 1), (key2079, 1), (key2077, 1), (key2077, 1), (key2187, 1), (key2187, 1), (key2176, 1), (key2176, 1), (key2174, 1), (key2174, 1), (key2287, 1), (key2287, 1), (key2279, 1), (key2279, 1), (key2274, 1), (key2274, 1), (key2347, 1), (key2347, 1), (key2343, 1), (key2343, 1), (key2341, 1), (key2341, 1), (key2085, -2), (key2079, -2), (key2079, -2), (key2187, -2), (key2176, -2), (key2176, -2), (key2287, -2), (key2287, -2), (key2279, -2), (key2279, -2), (key2276, -2), (key2276, -2)]

theorem rawRowCheck8991 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form9 = rawRow8991 := by decide +kernel

def row8991 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, 2), (key2276, -4), (key2279, -2), (key2287, -2), (key2341, 2), (key2343, 2), (key2347, 2)]

theorem rowCheck8991 : row8991 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8991 := by decide +kernel

theorem rowEval8991 (x : Key → ℝ) : Integer.Sparse.eval row8991 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8991, Integer.Sparse.eval_collectBalanced, rawRowCheck8991]

def rawRow8992 : Integer.Sparse Key := [(key2174, 1), (key2176, 1), (key2274, 1), (key2279, 1), (key2341, 1), (key2343, 1), (key2077, 1), (key2079, 1), (key2274, 1), (key2287, 1), (key2341, 1), (key2347, 1), (key2077, 1), (key2085, 1), (key2174, 1), (key2187, 1), (key2343, 1), (key2347, 1), (key2079, 1), (key2085, 1), (key2176, 1), (key2187, 1), (key2279, 1), (key2287, 1), (key2176, -2), (key2276, -2), (key2279, -2), (key2079, -2), (key2276, -2), (key2287, -2), (key2079, -2), (key2085, -2), (key2176, -2), (key2187, -2), (key2279, -2), (key2287, -2)]

theorem rawRowCheck8992 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form9 = rawRow8992 := by decide +kernel

def row8992 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, 2), (key2276, -4), (key2279, -2), (key2287, -2), (key2341, 2), (key2343, 2), (key2347, 2)]

theorem rowCheck8992 : row8992 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8992 := by decide +kernel

theorem rowEval8992 (x : Key → ℝ) : Integer.Sparse.eval row8992 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form9) x := by
  rw [rowCheck8992, Integer.Sparse.eval_collectBalanced, rawRowCheck8992]

def rawRow8993 : Integer.Sparse Key := [(key2176, 1), (key2174, 1), (key2279, 1), (key2274, 1), (key2343, 1), (key2341, 1), (key2079, 1), (key2077, 1), (key2287, 1), (key2274, 1), (key2347, 1), (key2341, 1), (key2085, 1), (key2077, 1), (key2187, 1), (key2174, 1), (key2347, 1), (key2343, 1), (key2085, 1), (key2079, 1), (key2187, 1), (key2176, 1), (key2287, 1), (key2279, 1), (key2176, -2), (key2279, -2), (key2276, -2), (key2079, -2), (key2287, -2), (key2276, -2), (key2085, -2), (key2079, -2), (key2187, -2), (key2176, -2), (key2287, -2), (key2279, -2)]

theorem rawRowCheck8993 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form9 = rawRow8993 := by decide +kernel

def row8993 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, 2), (key2276, -4), (key2279, -2), (key2287, -2), (key2341, 2), (key2343, 2), (key2347, 2)]

theorem rowCheck8993 : row8993 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8993 := by decide +kernel

theorem rowEval8993 (x : Key → ℝ) : Integer.Sparse.eval row8993 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8993, Integer.Sparse.eval_collectBalanced, rawRowCheck8993]

def rawRow8994 : Integer.Sparse Key := [(key2274, 1), (key2341, 1), (key2174, 1), (key2343, 1), (key2176, 1), (key2279, 1), (key2274, 1), (key2341, 1), (key2077, 1), (key2347, 1), (key2079, 1), (key2287, 1), (key2174, 1), (key2343, 1), (key2077, 1), (key2347, 1), (key2085, 1), (key2187, 1), (key2176, 1), (key2279, 1), (key2079, 1), (key2287, 1), (key2085, 1), (key2187, 1), (key2276, -2), (key2176, -2), (key2279, -2), (key2276, -2), (key2079, -2), (key2287, -2), (key2176, -2), (key2279, -2), (key2079, -2), (key2287, -2), (key2085, -2), (key2187, -2)]

theorem rawRowCheck8994 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form9 = rawRow8994 := by decide +kernel

def row8994 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, 2), (key2276, -4), (key2279, -2), (key2287, -2), (key2341, 2), (key2343, 2), (key2347, 2)]

theorem rowCheck8994 : row8994 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8994 := by decide +kernel

theorem rowEval8994 (x : Key → ℝ) : Integer.Sparse.eval row8994 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form9) x := by
  rw [rowCheck8994, Integer.Sparse.eval_collectBalanced, rawRowCheck8994]

def rawRow8995 : Integer.Sparse Key := [(key2341, 1), (key2274, 1), (key2343, 1), (key2174, 1), (key2279, 1), (key2176, 1), (key2341, 1), (key2274, 1), (key2347, 1), (key2077, 1), (key2287, 1), (key2079, 1), (key2343, 1), (key2174, 1), (key2347, 1), (key2077, 1), (key2187, 1), (key2085, 1), (key2279, 1), (key2176, 1), (key2287, 1), (key2079, 1), (key2187, 1), (key2085, 1), (key2276, -2), (key2279, -2), (key2176, -2), (key2276, -2), (key2287, -2), (key2079, -2), (key2279, -2), (key2176, -2), (key2287, -2), (key2079, -2), (key2187, -2), (key2085, -2)]

theorem rawRowCheck8995 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form9 = rawRow8995 := by decide +kernel

def row8995 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, 2), (key2276, -4), (key2279, -2), (key2287, -2), (key2341, 2), (key2343, 2), (key2347, 2)]

theorem rowCheck8995 : row8995 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8995 := by decide +kernel

theorem rowEval8995 (x : Key → ℝ) : Integer.Sparse.eval row8995 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck8995, Integer.Sparse.eval_collectBalanced, rawRowCheck8995]

def rawRow8996 : Integer.Sparse Key := [(key2279, 1), (key2343, 1), (key2176, 1), (key2341, 1), (key2174, 1), (key2274, 1), (key2287, 1), (key2347, 1), (key2079, 1), (key2341, 1), (key2077, 1), (key2274, 1), (key2187, 1), (key2347, 1), (key2085, 1), (key2343, 1), (key2077, 1), (key2174, 1), (key2187, 1), (key2287, 1), (key2085, 1), (key2279, 1), (key2079, 1), (key2176, 1), (key2279, -2), (key2176, -2), (key2276, -2), (key2287, -2), (key2079, -2), (key2276, -2), (key2187, -2), (key2287, -2), (key2085, -2), (key2279, -2), (key2079, -2), (key2176, -2)]

theorem rawRowCheck8996 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form9 = rawRow8996 := by decide +kernel

def row8996 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, 2), (key2276, -4), (key2279, -2), (key2287, -2), (key2341, 2), (key2343, 2), (key2347, 2)]

theorem rowCheck8996 : row8996 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8996 := by decide +kernel

theorem rowEval8996 (x : Key → ℝ) : Integer.Sparse.eval row8996 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8996, Integer.Sparse.eval_collectBalanced, rawRowCheck8996]

def rawRow8997 : Integer.Sparse Key := [(key2343, 1), (key2279, 1), (key2341, 1), (key2176, 1), (key2274, 1), (key2174, 1), (key2347, 1), (key2287, 1), (key2341, 1), (key2079, 1), (key2274, 1), (key2077, 1), (key2347, 1), (key2187, 1), (key2343, 1), (key2085, 1), (key2174, 1), (key2077, 1), (key2287, 1), (key2187, 1), (key2279, 1), (key2085, 1), (key2176, 1), (key2079, 1), (key2279, -2), (key2276, -2), (key2176, -2), (key2287, -2), (key2276, -2), (key2079, -2), (key2287, -2), (key2187, -2), (key2279, -2), (key2085, -2), (key2176, -2), (key2079, -2)]

theorem rawRowCheck8997 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form9 = rawRow8997 := by decide +kernel

def row8997 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, 2), (key2276, -4), (key2279, -2), (key2287, -2), (key2341, 2), (key2343, 2), (key2347, 2)]

theorem rowCheck8997 : row8997 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8997 := by decide +kernel

theorem rowEval8997 (x : Key → ℝ) : Integer.Sparse.eval row8997 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck8997, Integer.Sparse.eval_collectBalanced, rawRowCheck8997]

def rawRow8998 : Integer.Sparse Key := [(key2187, 1), (key2187, 1), (key2287, 1), (key2287, 1), (key2347, 1), (key2347, 1), (key2085, 1), (key2085, 1), (key2279, 1), (key2279, 1), (key2343, 1), (key2343, 1), (key2079, 1), (key2079, 1), (key2176, 1), (key2176, 1), (key2341, 1), (key2341, 1), (key2077, 1), (key2077, 1), (key2174, 1), (key2174, 1), (key2274, 1), (key2274, 1), (key2187, -2), (key2287, -2), (key2287, -2), (key2085, -2), (key2279, -2), (key2279, -2), (key2079, -2), (key2079, -2), (key2176, -2), (key2176, -2), (key2276, -2), (key2276, -2)]

theorem rawRowCheck8998 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form9 = rawRow8998 := by decide +kernel

def row8998 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, 2), (key2276, -4), (key2279, -2), (key2287, -2), (key2341, 2), (key2343, 2), (key2347, 2)]

theorem rowCheck8998 : row8998 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8998 := by decide +kernel

theorem rowEval8998 (x : Key → ℝ) : Integer.Sparse.eval row8998 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8998, Integer.Sparse.eval_collectBalanced, rawRowCheck8998]

def rawRow8999 : Integer.Sparse Key := [(key2287, 1), (key2347, 1), (key2187, 1), (key2347, 1), (key2187, 1), (key2287, 1), (key2279, 1), (key2343, 1), (key2085, 1), (key2343, 1), (key2085, 1), (key2279, 1), (key2176, 1), (key2341, 1), (key2079, 1), (key2341, 1), (key2079, 1), (key2176, 1), (key2174, 1), (key2274, 1), (key2077, 1), (key2274, 1), (key2077, 1), (key2174, 1), (key2287, -2), (key2187, -2), (key2287, -2), (key2279, -2), (key2085, -2), (key2279, -2), (key2176, -2), (key2276, -2), (key2079, -2), (key2276, -2), (key2079, -2), (key2176, -2)]

theorem rawRowCheck8999 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form9 = rawRow8999 := by decide +kernel

def row8999 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, 2), (key2276, -4), (key2279, -2), (key2287, -2), (key2341, 2), (key2343, 2), (key2347, 2)]

theorem rowCheck8999 : row8999 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8999 := by decide +kernel

theorem rowEval8999 (x : Key → ℝ) : Integer.Sparse.eval row8999 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8999, Integer.Sparse.eval_collectBalanced, rawRowCheck8999]

def rawRow9000 : Integer.Sparse Key := [(key2347, 1), (key2287, 1), (key2347, 1), (key2187, 1), (key2287, 1), (key2187, 1), (key2343, 1), (key2279, 1), (key2343, 1), (key2085, 1), (key2279, 1), (key2085, 1), (key2341, 1), (key2176, 1), (key2341, 1), (key2079, 1), (key2176, 1), (key2079, 1), (key2274, 1), (key2174, 1), (key2274, 1), (key2077, 1), (key2174, 1), (key2077, 1), (key2287, -2), (key2287, -2), (key2187, -2), (key2279, -2), (key2279, -2), (key2085, -2), (key2276, -2), (key2176, -2), (key2276, -2), (key2079, -2), (key2176, -2), (key2079, -2)]

theorem rawRowCheck9000 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form9 = rawRow9000 := by decide +kernel

def row9000 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, 2), (key2276, -4), (key2279, -2), (key2287, -2), (key2341, 2), (key2343, 2), (key2347, 2)]

theorem rowCheck9000 : row9000 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9000 := by decide +kernel

theorem rowEval9000 (x : Key → ℝ) : Integer.Sparse.eval row9000 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck9000, Integer.Sparse.eval_collectBalanced, rawRowCheck9000]

def rawRow9001 : Integer.Sparse Key := [(key843, -6), (key843, -6), (key843, -6), (key844, -6), (key943, 2), (key943, 2), (key944, 2), (key943, 2), (key943, 2), (key945, 2), (key943, 2), (key944, 2), (key943, 2), (key945, 2), (key944, 2), (key945, 2)]

theorem rawRowCheck9001 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form10 = rawRow9001 := by decide +kernel

def row9001 : Integer.Sparse Key := [(key843, -18), (key844, -6), (key943, 12), (key944, 6), (key945, 6)]

theorem rowCheck9001 : row9001 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9001 := by decide +kernel

theorem rowEval9001 (x : Key → ℝ) : Integer.Sparse.eval row9001 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form10) x := by
  rw [rowCheck9001, Integer.Sparse.eval_collectBalanced, rawRowCheck9001]

def rawRow9002 : Integer.Sparse Key := [(key843, -6), (key843, -6), (key844, -6), (key843, -6), (key943, 2), (key944, 2), (key943, 2), (key943, 2), (key945, 2), (key943, 2), (key944, 2), (key943, 2), (key945, 2), (key943, 2), (key945, 2), (key944, 2)]

theorem rawRowCheck9002 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form10 = rawRow9002 := by decide +kernel

def row9002 : Integer.Sparse Key := [(key843, -18), (key844, -6), (key943, 12), (key944, 6), (key945, 6)]

theorem rowCheck9002 : row9002 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9002 := by decide +kernel

theorem rowEval9002 (x : Key → ℝ) : Integer.Sparse.eval row9002 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9002, Integer.Sparse.eval_collectBalanced, rawRowCheck9002]

def rawRow9003 : Integer.Sparse Key := [(key843, -6), (key844, -6), (key843, -6), (key843, -6), (key944, 2), (key943, 2), (key943, 2), (key945, 2), (key943, 2), (key943, 2), (key945, 2), (key945, 2), (key944, 2), (key944, 2), (key943, 2), (key943, 2)]

theorem rawRowCheck9003 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form10 = rawRow9003 := by decide +kernel

def row9003 : Integer.Sparse Key := [(key843, -18), (key844, -6), (key943, 12), (key944, 6), (key945, 6)]

theorem rowCheck9003 : row9003 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9003 := by decide +kernel

theorem rowEval9003 (x : Key → ℝ) : Integer.Sparse.eval row9003 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9003, Integer.Sparse.eval_collectBalanced, rawRowCheck9003]

def rawRow9004 : Integer.Sparse Key := [(key844, -6), (key843, -6), (key843, -6), (key843, -6), (key945, 2), (key945, 2), (key945, 2), (key944, 2), (key944, 2), (key944, 2), (key943, 2), (key943, 2), (key943, 2), (key943, 2), (key943, 2), (key943, 2)]

theorem rawRowCheck9004 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form10 = rawRow9004 := by decide +kernel

def row9004 : Integer.Sparse Key := [(key843, -18), (key844, -6), (key943, 12), (key944, 6), (key945, 6)]

theorem rowCheck9004 : row9004 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9004 := by decide +kernel

theorem rowEval9004 (x : Key → ℝ) : Integer.Sparse.eval row9004 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9004, Integer.Sparse.eval_collectBalanced, rawRowCheck9004]

def rawRow9005 : Integer.Sparse Key := [(key754, -6), (key943, -6), (key943, -6), (key945, -6), (key754, 2), (key754, 2), (key755, 2), (key843, 2), (key843, 2), (key844, 2), (key943, 2), (key944, 2), (key943, 2), (key945, 2), (key944, 2), (key945, 2)]

theorem rawRowCheck9005 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form10 = rawRow9005 := by decide +kernel

def row9005 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 4), (key844, 2), (key943, -8), (key944, 4), (key945, -2)]

theorem rowCheck9005 : row9005 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9005 := by decide +kernel

theorem rowEval9005 (x : Key → ℝ) : Integer.Sparse.eval row9005 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form10) x := by
  rw [rowCheck9005, Integer.Sparse.eval_collectBalanced, rawRowCheck9005]

def rawRow9006 : Integer.Sparse Key := [(key754, -6), (key943, -6), (key945, -6), (key943, -6), (key754, 2), (key755, 2), (key754, 2), (key843, 2), (key844, 2), (key843, 2), (key944, 2), (key943, 2), (key945, 2), (key943, 2), (key945, 2), (key944, 2)]

theorem rawRowCheck9006 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form10 = rawRow9006 := by decide +kernel

def row9006 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 4), (key844, 2), (key943, -8), (key944, 4), (key945, -2)]

theorem rowCheck9006 : row9006 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9006 := by decide +kernel

theorem rowEval9006 (x : Key → ℝ) : Integer.Sparse.eval row9006 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9006, Integer.Sparse.eval_collectBalanced, rawRowCheck9006]

def rawRow9007 : Integer.Sparse Key := [(key754, -6), (key945, -6), (key943, -6), (key943, -6), (key755, 2), (key754, 2), (key754, 2), (key844, 2), (key843, 2), (key843, 2), (key945, 2), (key945, 2), (key944, 2), (key944, 2), (key943, 2), (key943, 2)]

theorem rawRowCheck9007 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form10 = rawRow9007 := by decide +kernel

def row9007 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 4), (key844, 2), (key943, -8), (key944, 4), (key945, -2)]

theorem rowCheck9007 : row9007 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9007 := by decide +kernel

theorem rowEval9007 (x : Key → ℝ) : Integer.Sparse.eval row9007 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9007, Integer.Sparse.eval_collectBalanced, rawRowCheck9007]

def rawRow9008 : Integer.Sparse Key := [(key943, -6), (key754, -6), (key943, -6), (key945, -6), (key843, 2), (key943, 2), (key944, 2), (key754, 2), (key943, 2), (key945, 2), (key754, 2), (key755, 2), (key843, 2), (key844, 2), (key944, 2), (key945, 2)]

theorem rawRowCheck9008 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form10 = rawRow9008 := by decide +kernel

def row9008 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 4), (key844, 2), (key943, -8), (key944, 4), (key945, -2)]

theorem rowCheck9008 : row9008 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9008 := by decide +kernel

theorem rowEval9008 (x : Key → ℝ) : Integer.Sparse.eval row9008 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form10) x := by
  rw [rowCheck9008, Integer.Sparse.eval_collectBalanced, rawRowCheck9008]

def rawRow9009 : Integer.Sparse Key := [(key943, -6), (key754, -6), (key945, -6), (key943, -6), (key843, 2), (key944, 2), (key943, 2), (key754, 2), (key945, 2), (key943, 2), (key755, 2), (key754, 2), (key844, 2), (key843, 2), (key945, 2), (key944, 2)]

theorem rawRowCheck9009 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form10 = rawRow9009 := by decide +kernel

def row9009 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 4), (key844, 2), (key943, -8), (key944, 4), (key945, -2)]

theorem rowCheck9009 : row9009 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9009 := by decide +kernel

theorem rowEval9009 (x : Key → ℝ) : Integer.Sparse.eval row9009 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9009, Integer.Sparse.eval_collectBalanced, rawRowCheck9009]

def rawRow9010 : Integer.Sparse Key := [(key943, -6), (key943, -6), (key754, -6), (key945, -6), (key943, 2), (key843, 2), (key944, 2), (key943, 2), (key754, 2), (key945, 2), (key843, 2), (key944, 2), (key754, 2), (key945, 2), (key755, 2), (key844, 2)]

theorem rawRowCheck9010 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form10 = rawRow9010 := by decide +kernel

def row9010 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 4), (key844, 2), (key943, -8), (key944, 4), (key945, -2)]

theorem rowCheck9010 : row9010 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9010 := by decide +kernel

theorem rowEval9010 (x : Key → ℝ) : Integer.Sparse.eval row9010 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form10) x := by
  rw [rowCheck9010, Integer.Sparse.eval_collectBalanced, rawRowCheck9010]

def rawRow9011 : Integer.Sparse Key := [(key943, -6), (key943, -6), (key945, -6), (key754, -6), (key943, 2), (key944, 2), (key843, 2), (key943, 2), (key945, 2), (key754, 2), (key944, 2), (key843, 2), (key945, 2), (key754, 2), (key844, 2), (key755, 2)]

theorem rawRowCheck9011 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form10 = rawRow9011 := by decide +kernel

def row9011 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 4), (key844, 2), (key943, -8), (key944, 4), (key945, -2)]

theorem rowCheck9011 : row9011 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9011 := by decide +kernel

theorem rowEval9011 (x : Key → ℝ) : Integer.Sparse.eval row9011 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck9011, Integer.Sparse.eval_collectBalanced, rawRowCheck9011]

def rawRow9012 : Integer.Sparse Key := [(key943, -6), (key945, -6), (key754, -6), (key943, -6), (key944, 2), (key843, 2), (key943, 2), (key945, 2), (key754, 2), (key943, 2), (key844, 2), (key945, 2), (key755, 2), (key944, 2), (key754, 2), (key843, 2)]

theorem rawRowCheck9012 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form10 = rawRow9012 := by decide +kernel

def row9012 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 4), (key844, 2), (key943, -8), (key944, 4), (key945, -2)]

theorem rowCheck9012 : row9012 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9012 := by decide +kernel

theorem rowEval9012 (x : Key → ℝ) : Integer.Sparse.eval row9012 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9012, Integer.Sparse.eval_collectBalanced, rawRowCheck9012]

def rawRow9013 : Integer.Sparse Key := [(key943, -6), (key945, -6), (key943, -6), (key754, -6), (key944, 2), (key943, 2), (key843, 2), (key945, 2), (key943, 2), (key754, 2), (key945, 2), (key844, 2), (key944, 2), (key755, 2), (key843, 2), (key754, 2)]

theorem rawRowCheck9013 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form10 = rawRow9013 := by decide +kernel

def row9013 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 4), (key844, 2), (key943, -8), (key944, 4), (key945, -2)]

theorem rowCheck9013 : row9013 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9013 := by decide +kernel

theorem rowEval9013 (x : Key → ℝ) : Integer.Sparse.eval row9013 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck9013, Integer.Sparse.eval_collectBalanced, rawRowCheck9013]

def rawRow9014 : Integer.Sparse Key := [(key945, -6), (key754, -6), (key943, -6), (key943, -6), (key844, 2), (key945, 2), (key945, 2), (key755, 2), (key944, 2), (key944, 2), (key754, 2), (key754, 2), (key843, 2), (key843, 2), (key943, 2), (key943, 2)]

theorem rawRowCheck9014 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form10 = rawRow9014 := by decide +kernel

def row9014 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 4), (key844, 2), (key943, -8), (key944, 4), (key945, -2)]

theorem rowCheck9014 : row9014 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9014 := by decide +kernel

theorem rowEval9014 (x : Key → ℝ) : Integer.Sparse.eval row9014 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9014, Integer.Sparse.eval_collectBalanced, rawRowCheck9014]

def rawRow9015 : Integer.Sparse Key := [(key945, -6), (key943, -6), (key754, -6), (key943, -6), (key945, 2), (key844, 2), (key945, 2), (key944, 2), (key755, 2), (key944, 2), (key843, 2), (key943, 2), (key754, 2), (key943, 2), (key754, 2), (key843, 2)]

theorem rawRowCheck9015 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form10 = rawRow9015 := by decide +kernel

def row9015 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 4), (key844, 2), (key943, -8), (key944, 4), (key945, -2)]

theorem rowCheck9015 : row9015 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9015 := by decide +kernel

theorem rowEval9015 (x : Key → ℝ) : Integer.Sparse.eval row9015 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9015, Integer.Sparse.eval_collectBalanced, rawRowCheck9015]

def rawRow9016 : Integer.Sparse Key := [(key945, -6), (key943, -6), (key943, -6), (key754, -6), (key945, 2), (key945, 2), (key844, 2), (key944, 2), (key944, 2), (key755, 2), (key943, 2), (key843, 2), (key943, 2), (key754, 2), (key843, 2), (key754, 2)]

theorem rawRowCheck9016 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form10 = rawRow9016 := by decide +kernel

def row9016 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 4), (key844, 2), (key943, -8), (key944, 4), (key945, -2)]

theorem rowCheck9016 : row9016 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9016 := by decide +kernel

theorem rowEval9016 (x : Key → ℝ) : Integer.Sparse.eval row9016 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck9016, Integer.Sparse.eval_collectBalanced, rawRowCheck9016]

def rawRow9017 : Integer.Sparse Key := [(key2006, 6), (key2007, 6), (key2007, 6), (key2007, 6), (key2340, -6), (key2340, -6), (key2340, -6), (key2349, -6)]

theorem rawRowCheck9017 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form11 = rawRow9017 := by decide +kernel

def row9017 : Integer.Sparse Key := [(key2006, 6), (key2007, 18), (key2340, -18), (key2349, -6)]

theorem rowCheck9017 : row9017 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9017 := by decide +kernel

theorem rowEval9017 (x : Key → ℝ) : Integer.Sparse.eval row9017 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form11) x := by
  rw [rowCheck9017, Integer.Sparse.eval_collectBalanced, rawRowCheck9017]

def rawRow9018 : Integer.Sparse Key := [(key2007, 6), (key2006, 6), (key2007, 6), (key2007, 6), (key2340, -6), (key2340, -6), (key2349, -6), (key2340, -6)]

theorem rawRowCheck9018 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form11 = rawRow9018 := by decide +kernel

def row9018 : Integer.Sparse Key := [(key2006, 6), (key2007, 18), (key2340, -18), (key2349, -6)]

theorem rowCheck9018 : row9018 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9018 := by decide +kernel

theorem rowEval9018 (x : Key → ℝ) : Integer.Sparse.eval row9018 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9018, Integer.Sparse.eval_collectBalanced, rawRowCheck9018]

def rawRow9019 : Integer.Sparse Key := [(key2007, 6), (key2007, 6), (key2006, 6), (key2007, 6), (key2340, -6), (key2349, -6), (key2340, -6), (key2340, -6)]

theorem rawRowCheck9019 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form11 = rawRow9019 := by decide +kernel

def row9019 : Integer.Sparse Key := [(key2006, 6), (key2007, 18), (key2340, -18), (key2349, -6)]

theorem rowCheck9019 : row9019 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9019 := by decide +kernel

theorem rowEval9019 (x : Key → ℝ) : Integer.Sparse.eval row9019 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9019, Integer.Sparse.eval_collectBalanced, rawRowCheck9019]

def rawRow9020 : Integer.Sparse Key := [(key2007, 6), (key2007, 6), (key2007, 6), (key2006, 6), (key2349, -6), (key2340, -6), (key2340, -6), (key2340, -6)]

theorem rawRowCheck9020 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form11 = rawRow9020 := by decide +kernel

def row9020 : Integer.Sparse Key := [(key2006, 6), (key2007, 18), (key2340, -18), (key2349, -6)]

theorem rowCheck9020 : row9020 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9020 := by decide +kernel

theorem rowEval9020 (x : Key → ℝ) : Integer.Sparse.eval row9020 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9020, Integer.Sparse.eval_collectBalanced, rawRowCheck9020]

def rawRow9021 : Integer.Sparse Key := [(key2299, 6), (key2300, 6), (key2300, 6), (key2340, 6), (key2007, -6), (key2300, -6), (key2300, -6), (key2313, -6)]

theorem rawRowCheck9021 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form11 = rawRow9021 := by decide +kernel

def row9021 : Integer.Sparse Key := [(key2007, -6), (key2299, 6), (key2313, -6), (key2340, 6)]

theorem rowCheck9021 : row9021 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9021 := by decide +kernel

theorem rowEval9021 (x : Key → ℝ) : Integer.Sparse.eval row9021 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form11) x := by
  rw [rowCheck9021, Integer.Sparse.eval_collectBalanced, rawRowCheck9021]

def rawRow9022 : Integer.Sparse Key := [(key2300, 6), (key2299, 6), (key2300, 6), (key2340, 6), (key2007, -6), (key2300, -6), (key2313, -6), (key2300, -6)]

theorem rawRowCheck9022 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form11 = rawRow9022 := by decide +kernel

def row9022 : Integer.Sparse Key := [(key2007, -6), (key2299, 6), (key2313, -6), (key2340, 6)]

theorem rowCheck9022 : row9022 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9022 := by decide +kernel

theorem rowEval9022 (x : Key → ℝ) : Integer.Sparse.eval row9022 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9022, Integer.Sparse.eval_collectBalanced, rawRowCheck9022]

def rawRow9023 : Integer.Sparse Key := [(key2300, 6), (key2300, 6), (key2299, 6), (key2340, 6), (key2007, -6), (key2313, -6), (key2300, -6), (key2300, -6)]

theorem rawRowCheck9023 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form11 = rawRow9023 := by decide +kernel

def row9023 : Integer.Sparse Key := [(key2007, -6), (key2299, 6), (key2313, -6), (key2340, 6)]

theorem rowCheck9023 : row9023 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9023 := by decide +kernel

theorem rowEval9023 (x : Key → ℝ) : Integer.Sparse.eval row9023 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9023, Integer.Sparse.eval_collectBalanced, rawRowCheck9023]

def rawRow9024 : Integer.Sparse Key := [(key2299, 6), (key2300, 6), (key2340, 6), (key2300, 6), (key2300, -6), (key2007, -6), (key2300, -6), (key2313, -6)]

theorem rawRowCheck9024 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form11 = rawRow9024 := by decide +kernel

def row9024 : Integer.Sparse Key := [(key2007, -6), (key2299, 6), (key2313, -6), (key2340, 6)]

theorem rowCheck9024 : row9024 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9024 := by decide +kernel

theorem rowEval9024 (x : Key → ℝ) : Integer.Sparse.eval row9024 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form11) x := by
  rw [rowCheck9024, Integer.Sparse.eval_collectBalanced, rawRowCheck9024]

def rawRow9025 : Integer.Sparse Key := [(key2300, 6), (key2299, 6), (key2340, 6), (key2300, 6), (key2300, -6), (key2007, -6), (key2313, -6), (key2300, -6)]

theorem rawRowCheck9025 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form11 = rawRow9025 := by decide +kernel

def row9025 : Integer.Sparse Key := [(key2007, -6), (key2299, 6), (key2313, -6), (key2340, 6)]

theorem rowCheck9025 : row9025 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9025 := by decide +kernel

theorem rowEval9025 (x : Key → ℝ) : Integer.Sparse.eval row9025 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9025, Integer.Sparse.eval_collectBalanced, rawRowCheck9025]

def rawRow9026 : Integer.Sparse Key := [(key2299, 6), (key2340, 6), (key2300, 6), (key2300, 6), (key2300, -6), (key2300, -6), (key2007, -6), (key2313, -6)]

theorem rawRowCheck9026 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form11 = rawRow9026 := by decide +kernel

def row9026 : Integer.Sparse Key := [(key2007, -6), (key2299, 6), (key2313, -6), (key2340, 6)]

theorem rowCheck9026 : row9026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9026 := by decide +kernel

theorem rowEval9026 (x : Key → ℝ) : Integer.Sparse.eval row9026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form11) x := by
  rw [rowCheck9026, Integer.Sparse.eval_collectBalanced, rawRowCheck9026]

def rawRow9027 : Integer.Sparse Key := [(key2340, 6), (key2299, 6), (key2300, 6), (key2300, 6), (key2300, -6), (key2300, -6), (key2313, -6), (key2007, -6)]

theorem rawRowCheck9027 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form11 = rawRow9027 := by decide +kernel

def row9027 : Integer.Sparse Key := [(key2007, -6), (key2299, 6), (key2313, -6), (key2340, 6)]

theorem rowCheck9027 : row9027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9027 := by decide +kernel

theorem rowEval9027 (x : Key → ℝ) : Integer.Sparse.eval row9027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9027, Integer.Sparse.eval_collectBalanced, rawRowCheck9027]

def rawRow9028 : Integer.Sparse Key := [(key2300, 6), (key2340, 6), (key2299, 6), (key2300, 6), (key2300, -6), (key2313, -6), (key2007, -6), (key2300, -6)]

theorem rawRowCheck9028 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form11 = rawRow9028 := by decide +kernel

def row9028 : Integer.Sparse Key := [(key2007, -6), (key2299, 6), (key2313, -6), (key2340, 6)]

theorem rowCheck9028 : row9028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9028 := by decide +kernel

theorem rowEval9028 (x : Key → ℝ) : Integer.Sparse.eval row9028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9028, Integer.Sparse.eval_collectBalanced, rawRowCheck9028]

def rawRow9029 : Integer.Sparse Key := [(key2340, 6), (key2300, 6), (key2299, 6), (key2300, 6), (key2300, -6), (key2313, -6), (key2300, -6), (key2007, -6)]

theorem rawRowCheck9029 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form11 = rawRow9029 := by decide +kernel

def row9029 : Integer.Sparse Key := [(key2007, -6), (key2299, 6), (key2313, -6), (key2340, 6)]

theorem rowCheck9029 : row9029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9029 := by decide +kernel

theorem rowEval9029 (x : Key → ℝ) : Integer.Sparse.eval row9029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9029, Integer.Sparse.eval_collectBalanced, rawRowCheck9029]

def rawRow9030 : Integer.Sparse Key := [(key2300, 6), (key2300, 6), (key2340, 6), (key2299, 6), (key2313, -6), (key2007, -6), (key2300, -6), (key2300, -6)]

theorem rawRowCheck9030 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form11 = rawRow9030 := by decide +kernel

def row9030 : Integer.Sparse Key := [(key2007, -6), (key2299, 6), (key2313, -6), (key2340, 6)]

theorem rowCheck9030 : row9030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9030 := by decide +kernel

theorem rowEval9030 (x : Key → ℝ) : Integer.Sparse.eval row9030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9030, Integer.Sparse.eval_collectBalanced, rawRowCheck9030]

def rawRow9031 : Integer.Sparse Key := [(key2300, 6), (key2340, 6), (key2300, 6), (key2299, 6), (key2313, -6), (key2300, -6), (key2007, -6), (key2300, -6)]

theorem rawRowCheck9031 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form11 = rawRow9031 := by decide +kernel

def row9031 : Integer.Sparse Key := [(key2007, -6), (key2299, 6), (key2313, -6), (key2340, 6)]

theorem rowCheck9031 : row9031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9031 := by decide +kernel

theorem rowEval9031 (x : Key → ℝ) : Integer.Sparse.eval row9031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9031, Integer.Sparse.eval_collectBalanced, rawRowCheck9031]

def rawRow9032 : Integer.Sparse Key := [(key2340, 6), (key2300, 6), (key2300, 6), (key2299, 6), (key2313, -6), (key2300, -6), (key2300, -6), (key2007, -6)]

theorem rawRowCheck9032 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form11 = rawRow9032 := by decide +kernel

def row9032 : Integer.Sparse Key := [(key2007, -6), (key2299, 6), (key2313, -6), (key2340, 6)]

theorem rowCheck9032 : row9032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9032 := by decide +kernel

theorem rowEval9032 (x : Key → ℝ) : Integer.Sparse.eval row9032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9032, Integer.Sparse.eval_collectBalanced, rawRowCheck9032]

def rawRow9033 : Integer.Sparse Key := [(key1998, 6), (key2000, 6), (key2000, 6), (key2000, 6), (key2340, -6), (key2340, -6), (key2340, -6), (key2349, -6)]

theorem rawRowCheck9033 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form12 = rawRow9033 := by decide +kernel

def row9033 : Integer.Sparse Key := [(key1998, 6), (key2000, 18), (key2340, -18), (key2349, -6)]

theorem rowCheck9033 : row9033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9033 := by decide +kernel

theorem rowEval9033 (x : Key → ℝ) : Integer.Sparse.eval row9033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form12) x := by
  rw [rowCheck9033, Integer.Sparse.eval_collectBalanced, rawRowCheck9033]

def rawRow9034 : Integer.Sparse Key := [(key2000, 6), (key1998, 6), (key2000, 6), (key2000, 6), (key2340, -6), (key2340, -6), (key2349, -6), (key2340, -6)]

theorem rawRowCheck9034 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form12 = rawRow9034 := by decide +kernel

def row9034 : Integer.Sparse Key := [(key1998, 6), (key2000, 18), (key2340, -18), (key2349, -6)]

theorem rowCheck9034 : row9034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9034 := by decide +kernel

theorem rowEval9034 (x : Key → ℝ) : Integer.Sparse.eval row9034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9034, Integer.Sparse.eval_collectBalanced, rawRowCheck9034]

def rawRow9035 : Integer.Sparse Key := [(key2000, 6), (key2000, 6), (key1998, 6), (key2000, 6), (key2340, -6), (key2349, -6), (key2340, -6), (key2340, -6)]

theorem rawRowCheck9035 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form12 = rawRow9035 := by decide +kernel

def row9035 : Integer.Sparse Key := [(key1998, 6), (key2000, 18), (key2340, -18), (key2349, -6)]

theorem rowCheck9035 : row9035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9035 := by decide +kernel

theorem rowEval9035 (x : Key → ℝ) : Integer.Sparse.eval row9035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9035, Integer.Sparse.eval_collectBalanced, rawRowCheck9035]

def rawRow9036 : Integer.Sparse Key := [(key2000, 6), (key2000, 6), (key2000, 6), (key1998, 6), (key2349, -6), (key2340, -6), (key2340, -6), (key2340, -6)]

theorem rawRowCheck9036 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form12 = rawRow9036 := by decide +kernel

def row9036 : Integer.Sparse Key := [(key1998, 6), (key2000, 18), (key2340, -18), (key2349, -6)]

theorem rowCheck9036 : row9036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9036 := by decide +kernel

theorem rowEval9036 (x : Key → ℝ) : Integer.Sparse.eval row9036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9036, Integer.Sparse.eval_collectBalanced, rawRowCheck9036]

def rawRow9037 : Integer.Sparse Key := [(key2267, 6), (key2269, 6), (key2269, 6), (key2340, 6), (key2000, -6), (key2269, -6), (key2269, -6), (key2292, -6)]

theorem rawRowCheck9037 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form12 = rawRow9037 := by decide +kernel

def row9037 : Integer.Sparse Key := [(key2000, -6), (key2267, 6), (key2292, -6), (key2340, 6)]

theorem rowCheck9037 : row9037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9037 := by decide +kernel

theorem rowEval9037 (x : Key → ℝ) : Integer.Sparse.eval row9037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form12) x := by
  rw [rowCheck9037, Integer.Sparse.eval_collectBalanced, rawRowCheck9037]

def rawRow9038 : Integer.Sparse Key := [(key2269, 6), (key2267, 6), (key2269, 6), (key2340, 6), (key2000, -6), (key2269, -6), (key2292, -6), (key2269, -6)]

theorem rawRowCheck9038 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form12 = rawRow9038 := by decide +kernel

def row9038 : Integer.Sparse Key := [(key2000, -6), (key2267, 6), (key2292, -6), (key2340, 6)]

theorem rowCheck9038 : row9038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9038 := by decide +kernel

theorem rowEval9038 (x : Key → ℝ) : Integer.Sparse.eval row9038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9038, Integer.Sparse.eval_collectBalanced, rawRowCheck9038]

def rawRow9039 : Integer.Sparse Key := [(key2269, 6), (key2269, 6), (key2267, 6), (key2340, 6), (key2000, -6), (key2292, -6), (key2269, -6), (key2269, -6)]

theorem rawRowCheck9039 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form12 = rawRow9039 := by decide +kernel

def row9039 : Integer.Sparse Key := [(key2000, -6), (key2267, 6), (key2292, -6), (key2340, 6)]

theorem rowCheck9039 : row9039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9039 := by decide +kernel

theorem rowEval9039 (x : Key → ℝ) : Integer.Sparse.eval row9039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9039, Integer.Sparse.eval_collectBalanced, rawRowCheck9039]

def rawRow9040 : Integer.Sparse Key := [(key2267, 6), (key2269, 6), (key2340, 6), (key2269, 6), (key2269, -6), (key2000, -6), (key2269, -6), (key2292, -6)]

theorem rawRowCheck9040 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form12 = rawRow9040 := by decide +kernel

def row9040 : Integer.Sparse Key := [(key2000, -6), (key2267, 6), (key2292, -6), (key2340, 6)]

theorem rowCheck9040 : row9040 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9040 := by decide +kernel

theorem rowEval9040 (x : Key → ℝ) : Integer.Sparse.eval row9040 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form12) x := by
  rw [rowCheck9040, Integer.Sparse.eval_collectBalanced, rawRowCheck9040]

def rawRow9041 : Integer.Sparse Key := [(key2269, 6), (key2267, 6), (key2340, 6), (key2269, 6), (key2269, -6), (key2000, -6), (key2292, -6), (key2269, -6)]

theorem rawRowCheck9041 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form12 = rawRow9041 := by decide +kernel

def row9041 : Integer.Sparse Key := [(key2000, -6), (key2267, 6), (key2292, -6), (key2340, 6)]

theorem rowCheck9041 : row9041 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9041 := by decide +kernel

theorem rowEval9041 (x : Key → ℝ) : Integer.Sparse.eval row9041 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9041, Integer.Sparse.eval_collectBalanced, rawRowCheck9041]

def rawRow9042 : Integer.Sparse Key := [(key2267, 6), (key2340, 6), (key2269, 6), (key2269, 6), (key2269, -6), (key2269, -6), (key2000, -6), (key2292, -6)]

theorem rawRowCheck9042 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form12 = rawRow9042 := by decide +kernel

def row9042 : Integer.Sparse Key := [(key2000, -6), (key2267, 6), (key2292, -6), (key2340, 6)]

theorem rowCheck9042 : row9042 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9042 := by decide +kernel

theorem rowEval9042 (x : Key → ℝ) : Integer.Sparse.eval row9042 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form12) x := by
  rw [rowCheck9042, Integer.Sparse.eval_collectBalanced, rawRowCheck9042]

def rawRow9043 : Integer.Sparse Key := [(key2340, 6), (key2267, 6), (key2269, 6), (key2269, 6), (key2269, -6), (key2269, -6), (key2292, -6), (key2000, -6)]

theorem rawRowCheck9043 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form12 = rawRow9043 := by decide +kernel

def row9043 : Integer.Sparse Key := [(key2000, -6), (key2267, 6), (key2292, -6), (key2340, 6)]

theorem rowCheck9043 : row9043 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9043 := by decide +kernel

theorem rowEval9043 (x : Key → ℝ) : Integer.Sparse.eval row9043 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9043, Integer.Sparse.eval_collectBalanced, rawRowCheck9043]

def rawRow9044 : Integer.Sparse Key := [(key2269, 6), (key2340, 6), (key2267, 6), (key2269, 6), (key2269, -6), (key2292, -6), (key2000, -6), (key2269, -6)]

theorem rawRowCheck9044 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form12 = rawRow9044 := by decide +kernel

def row9044 : Integer.Sparse Key := [(key2000, -6), (key2267, 6), (key2292, -6), (key2340, 6)]

theorem rowCheck9044 : row9044 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9044 := by decide +kernel

theorem rowEval9044 (x : Key → ℝ) : Integer.Sparse.eval row9044 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9044, Integer.Sparse.eval_collectBalanced, rawRowCheck9044]

def rawRow9045 : Integer.Sparse Key := [(key2340, 6), (key2269, 6), (key2267, 6), (key2269, 6), (key2269, -6), (key2292, -6), (key2269, -6), (key2000, -6)]

theorem rawRowCheck9045 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form12 = rawRow9045 := by decide +kernel

def row9045 : Integer.Sparse Key := [(key2000, -6), (key2267, 6), (key2292, -6), (key2340, 6)]

theorem rowCheck9045 : row9045 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9045 := by decide +kernel

theorem rowEval9045 (x : Key → ℝ) : Integer.Sparse.eval row9045 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9045, Integer.Sparse.eval_collectBalanced, rawRowCheck9045]

def rawRow9046 : Integer.Sparse Key := [(key2269, 6), (key2269, 6), (key2340, 6), (key2267, 6), (key2292, -6), (key2000, -6), (key2269, -6), (key2269, -6)]

theorem rawRowCheck9046 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form12 = rawRow9046 := by decide +kernel

def row9046 : Integer.Sparse Key := [(key2000, -6), (key2267, 6), (key2292, -6), (key2340, 6)]

theorem rowCheck9046 : row9046 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9046 := by decide +kernel

theorem rowEval9046 (x : Key → ℝ) : Integer.Sparse.eval row9046 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9046, Integer.Sparse.eval_collectBalanced, rawRowCheck9046]

def rawRow9047 : Integer.Sparse Key := [(key2269, 6), (key2340, 6), (key2269, 6), (key2267, 6), (key2292, -6), (key2269, -6), (key2000, -6), (key2269, -6)]

theorem rawRowCheck9047 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form12 = rawRow9047 := by decide +kernel

def row9047 : Integer.Sparse Key := [(key2000, -6), (key2267, 6), (key2292, -6), (key2340, 6)]

theorem rowCheck9047 : row9047 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9047 := by decide +kernel

theorem rowEval9047 (x : Key → ℝ) : Integer.Sparse.eval row9047 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9047, Integer.Sparse.eval_collectBalanced, rawRowCheck9047]

def rawRow9048 : Integer.Sparse Key := [(key2340, 6), (key2269, 6), (key2269, 6), (key2267, 6), (key2292, -6), (key2269, -6), (key2269, -6), (key2000, -6)]

theorem rawRowCheck9048 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form12 = rawRow9048 := by decide +kernel

def row9048 : Integer.Sparse Key := [(key2000, -6), (key2267, 6), (key2292, -6), (key2340, 6)]

theorem rowCheck9048 : row9048 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9048 := by decide +kernel

theorem rowEval9048 (x : Key → ℝ) : Integer.Sparse.eval row9048 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9048, Integer.Sparse.eval_collectBalanced, rawRowCheck9048]

def rawRow9049 : Integer.Sparse Key := [(key776, -6), (key778, -6), (key778, -6), (key778, -6), (key801, 2), (key803, 2), (key803, 2), (key801, 2), (key803, 2), (key801, 2), (key811, 2), (key803, 2), (key811, 2), (key803, 2), (key803, 2), (key811, 2)]

theorem rawRowCheck9049 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form13 = rawRow9049 := by decide +kernel

def row9049 : Integer.Sparse Key := [(key776, -6), (key778, -18), (key801, 6), (key803, 12), (key811, 6)]

theorem rowCheck9049 : row9049 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9049 := by decide +kernel

theorem rowEval9049 (x : Key → ℝ) : Integer.Sparse.eval row9049 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form13) x := by
  rw [rowCheck9049, Integer.Sparse.eval_collectBalanced, rawRowCheck9049]

def rawRow9050 : Integer.Sparse Key := [(key778, -6), (key776, -6), (key778, -6), (key778, -6), (key803, 2), (key801, 2), (key803, 2), (key803, 2), (key801, 2), (key811, 2), (key801, 2), (key811, 2), (key803, 2), (key803, 2), (key811, 2), (key803, 2)]

theorem rawRowCheck9050 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form13 = rawRow9050 := by decide +kernel

def row9050 : Integer.Sparse Key := [(key776, -6), (key778, -18), (key801, 6), (key803, 12), (key811, 6)]

theorem rowCheck9050 : row9050 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9050 := by decide +kernel

theorem rowEval9050 (x : Key → ℝ) : Integer.Sparse.eval row9050 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9050, Integer.Sparse.eval_collectBalanced, rawRowCheck9050]

def rawRow9051 : Integer.Sparse Key := [(key778, -6), (key778, -6), (key776, -6), (key778, -6), (key803, 2), (key803, 2), (key801, 2), (key811, 2), (key811, 2), (key803, 2), (key803, 2), (key801, 2), (key801, 2), (key811, 2), (key803, 2), (key803, 2)]

theorem rawRowCheck9051 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form13 = rawRow9051 := by decide +kernel

def row9051 : Integer.Sparse Key := [(key776, -6), (key778, -18), (key801, 6), (key803, 12), (key811, 6)]

theorem rowCheck9051 : row9051 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9051 := by decide +kernel

theorem rowEval9051 (x : Key → ℝ) : Integer.Sparse.eval row9051 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9051, Integer.Sparse.eval_collectBalanced, rawRowCheck9051]

def rawRow9052 : Integer.Sparse Key := [(key778, -6), (key778, -6), (key778, -6), (key776, -6), (key811, 2), (key811, 2), (key811, 2), (key803, 2), (key803, 2), (key803, 2), (key803, 2), (key803, 2), (key803, 2), (key801, 2), (key801, 2), (key801, 2)]

theorem rawRowCheck9052 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form13 = rawRow9052 := by decide +kernel

def row9052 : Integer.Sparse Key := [(key776, -6), (key778, -18), (key801, 6), (key803, 12), (key811, 6)]

theorem rowCheck9052 : row9052 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9052 := by decide +kernel

theorem rowEval9052 (x : Key → ℝ) : Integer.Sparse.eval row9052 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9052, Integer.Sparse.eval_collectBalanced, rawRowCheck9052]

def rawRow9053 : Integer.Sparse Key := [(key801, -6), (key803, -6), (key803, -6), (key811, -6), (key776, 2), (key778, 2), (key778, 2), (key801, 2), (key803, 2), (key801, 2), (key811, 2), (key803, 2), (key811, 2), (key836, 2), (key836, 2), (key839, 2)]

theorem rawRowCheck9053 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form13 = rawRow9053 := by decide +kernel

def row9053 : Integer.Sparse Key := [(key776, 2), (key778, 4), (key801, -2), (key803, -8), (key811, -2), (key836, 4), (key839, 2)]

theorem rowCheck9053 : row9053 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9053 := by decide +kernel

theorem rowEval9053 (x : Key → ℝ) : Integer.Sparse.eval row9053 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form13) x := by
  rw [rowCheck9053, Integer.Sparse.eval_collectBalanced, rawRowCheck9053]

def rawRow9054 : Integer.Sparse Key := [(key803, -6), (key801, -6), (key803, -6), (key811, -6), (key778, 2), (key776, 2), (key778, 2), (key803, 2), (key801, 2), (key811, 2), (key801, 2), (key811, 2), (key803, 2), (key836, 2), (key839, 2), (key836, 2)]

theorem rawRowCheck9054 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form13 = rawRow9054 := by decide +kernel

def row9054 : Integer.Sparse Key := [(key776, 2), (key778, 4), (key801, -2), (key803, -8), (key811, -2), (key836, 4), (key839, 2)]

theorem rowCheck9054 : row9054 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9054 := by decide +kernel

theorem rowEval9054 (x : Key → ℝ) : Integer.Sparse.eval row9054 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9054, Integer.Sparse.eval_collectBalanced, rawRowCheck9054]

def rawRow9055 : Integer.Sparse Key := [(key803, -6), (key803, -6), (key801, -6), (key811, -6), (key778, 2), (key778, 2), (key776, 2), (key811, 2), (key811, 2), (key803, 2), (key803, 2), (key801, 2), (key801, 2), (key839, 2), (key836, 2), (key836, 2)]

theorem rawRowCheck9055 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form13 = rawRow9055 := by decide +kernel

def row9055 : Integer.Sparse Key := [(key776, 2), (key778, 4), (key801, -2), (key803, -8), (key811, -2), (key836, 4), (key839, 2)]

theorem rowCheck9055 : row9055 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9055 := by decide +kernel

theorem rowEval9055 (x : Key → ℝ) : Integer.Sparse.eval row9055 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9055, Integer.Sparse.eval_collectBalanced, rawRowCheck9055]

def rawRow9056 : Integer.Sparse Key := [(key801, -6), (key803, -6), (key811, -6), (key803, -6), (key801, 2), (key803, 2), (key811, 2), (key776, 2), (key778, 2), (key801, 2), (key811, 2), (key836, 2), (key839, 2), (key778, 2), (key803, 2), (key811, 2)]

theorem rawRowCheck9056 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form13 = rawRow9056 := by decide +kernel

def row9056 : Integer.Sparse Key := [(key776, 2), (key778, 4), (key801, -2), (key803, -8), (key836, 2), (key839, 2)]

theorem rowCheck9056 : row9056 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9056 := by decide +kernel

theorem rowEval9056 (x : Key → ℝ) : Integer.Sparse.eval row9056 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form13) x := by
  rw [rowCheck9056, Integer.Sparse.eval_collectBalanced, rawRowCheck9056]

def rawRow9057 : Integer.Sparse Key := [(key803, -6), (key801, -6), (key811, -6), (key803, -6), (key803, 2), (key801, 2), (key811, 2), (key778, 2), (key776, 2), (key811, 2), (key801, 2), (key839, 2), (key836, 2), (key778, 2), (key811, 2), (key803, 2)]

theorem rawRowCheck9057 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form13 = rawRow9057 := by decide +kernel

def row9057 : Integer.Sparse Key := [(key776, 2), (key778, 4), (key801, -2), (key803, -8), (key836, 2), (key839, 2)]

theorem rowCheck9057 : row9057 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9057 := by decide +kernel

theorem rowEval9057 (x : Key → ℝ) : Integer.Sparse.eval row9057 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9057, Integer.Sparse.eval_collectBalanced, rawRowCheck9057]

def rawRow9058 : Integer.Sparse Key := [(key801, -6), (key811, -6), (key803, -6), (key803, -6), (key801, 2), (key811, 2), (key803, 2), (key801, 2), (key811, 2), (key776, 2), (key839, 2), (key778, 2), (key811, 2), (key803, 2), (key778, 2), (key811, 2)]

theorem rawRowCheck9058 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form13 = rawRow9058 := by decide +kernel

def row9058 : Integer.Sparse Key := [(key776, 2), (key778, 4), (key801, -2), (key803, -8), (key811, 2), (key839, 2)]

theorem rowCheck9058 : row9058 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9058 := by decide +kernel

theorem rowEval9058 (x : Key → ℝ) : Integer.Sparse.eval row9058 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form13) x := by
  rw [rowCheck9058, Integer.Sparse.eval_collectBalanced, rawRowCheck9058]

def rawRow9059 : Integer.Sparse Key := [(key811, -6), (key801, -6), (key803, -6), (key803, -6), (key811, 2), (key801, 2), (key803, 2), (key811, 2), (key801, 2), (key839, 2), (key776, 2), (key811, 2), (key778, 2), (key803, 2), (key811, 2), (key778, 2)]

theorem rawRowCheck9059 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form13 = rawRow9059 := by decide +kernel

def row9059 : Integer.Sparse Key := [(key776, 2), (key778, 4), (key801, -2), (key803, -8), (key811, 2), (key839, 2)]

theorem rowCheck9059 : row9059 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9059 := by decide +kernel

theorem rowEval9059 (x : Key → ℝ) : Integer.Sparse.eval row9059 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck9059, Integer.Sparse.eval_collectBalanced, rawRowCheck9059]

def rawRow9060 : Integer.Sparse Key := [(key803, -6), (key811, -6), (key801, -6), (key803, -6), (key803, 2), (key811, 2), (key801, 2), (key836, 2), (key839, 2), (key778, 2), (key811, 2), (key776, 2), (key801, 2), (key811, 2), (key778, 2), (key803, 2)]

theorem rawRowCheck9060 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form13 = rawRow9060 := by decide +kernel

def row9060 : Integer.Sparse Key := [(key776, 2), (key778, 4), (key801, -2), (key803, -8), (key836, 2), (key839, 2)]

theorem rowCheck9060 : row9060 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9060 := by decide +kernel

theorem rowEval9060 (x : Key → ℝ) : Integer.Sparse.eval row9060 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9060, Integer.Sparse.eval_collectBalanced, rawRowCheck9060]

def rawRow9061 : Integer.Sparse Key := [(key811, -6), (key803, -6), (key801, -6), (key803, -6), (key811, 2), (key803, 2), (key801, 2), (key839, 2), (key836, 2), (key811, 2), (key778, 2), (key801, 2), (key776, 2), (key811, 2), (key803, 2), (key778, 2)]

theorem rawRowCheck9061 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form13 = rawRow9061 := by decide +kernel

def row9061 : Integer.Sparse Key := [(key776, 2), (key778, 4), (key801, -2), (key803, -8), (key836, 2), (key839, 2)]

theorem rowCheck9061 : row9061 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9061 := by decide +kernel

theorem rowEval9061 (x : Key → ℝ) : Integer.Sparse.eval row9061 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck9061, Integer.Sparse.eval_collectBalanced, rawRowCheck9061]

def rawRow9062 : Integer.Sparse Key := [(key803, -6), (key803, -6), (key811, -6), (key801, -6), (key836, 2), (key836, 2), (key839, 2), (key778, 2), (key778, 2), (key803, 2), (key803, 2), (key811, 2), (key811, 2), (key776, 2), (key801, 2), (key801, 2)]

theorem rawRowCheck9062 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form13 = rawRow9062 := by decide +kernel

def row9062 : Integer.Sparse Key := [(key776, 2), (key778, 4), (key801, -2), (key803, -8), (key811, -2), (key836, 4), (key839, 2)]

theorem rowCheck9062 : row9062 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9062 := by decide +kernel

theorem rowEval9062 (x : Key → ℝ) : Integer.Sparse.eval row9062 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9062, Integer.Sparse.eval_collectBalanced, rawRowCheck9062]

def rawRow9063 : Integer.Sparse Key := [(key803, -6), (key811, -6), (key803, -6), (key801, -6), (key836, 2), (key839, 2), (key836, 2), (key803, 2), (key811, 2), (key778, 2), (key811, 2), (key778, 2), (key803, 2), (key801, 2), (key776, 2), (key801, 2)]

theorem rawRowCheck9063 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form13 = rawRow9063 := by decide +kernel

def row9063 : Integer.Sparse Key := [(key776, 2), (key778, 4), (key801, -2), (key803, -8), (key811, -2), (key836, 4), (key839, 2)]

theorem rowCheck9063 : row9063 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9063 := by decide +kernel

theorem rowEval9063 (x : Key → ℝ) : Integer.Sparse.eval row9063 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9063, Integer.Sparse.eval_collectBalanced, rawRowCheck9063]

def rawRow9064 : Integer.Sparse Key := [(key811, -6), (key803, -6), (key803, -6), (key801, -6), (key839, 2), (key836, 2), (key836, 2), (key811, 2), (key803, 2), (key811, 2), (key778, 2), (key803, 2), (key778, 2), (key801, 2), (key801, 2), (key776, 2)]

theorem rawRowCheck9064 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form13 = rawRow9064 := by decide +kernel

def row9064 : Integer.Sparse Key := [(key776, 2), (key778, 4), (key801, -2), (key803, -8), (key811, -2), (key836, 4), (key839, 2)]

theorem rowCheck9064 : row9064 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9064 := by decide +kernel

theorem rowEval9064 (x : Key → ℝ) : Integer.Sparse.eval row9064 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck9064, Integer.Sparse.eval_collectBalanced, rawRowCheck9064]

def rawRow9065 : Integer.Sparse Key := [(key984, 2), (key984, 2), (key984, 2), (key1098, 2), (key1098, 2), (key1098, 2), (key1183, 2), (key1183, 2), (key1183, 2), (key1183, 2), (key1183, 2), (key1183, 2), (key976, -2), (key976, -2), (key976, -2), (key1090, -2), (key1090, -2), (key1090, -2), (key1090, -2), (key1090, -2), (key1090, -2), (key1180, -2), (key1180, -2), (key1180, -2)]

theorem rawRowCheck9065 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form0 = rawRow9065 := by decide +kernel

def row9065 : Integer.Sparse Key := [(key976, -6), (key984, 6), (key1090, -12), (key1098, 6), (key1180, -6), (key1183, 12)]

theorem rowCheck9065 : row9065 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9065 := by decide +kernel

theorem rowEval9065 (x : Key → ℝ) : Integer.Sparse.eval row9065 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9065, Integer.Sparse.eval_collectBalanced, rawRowCheck9065]

def rawRow9066 : Integer.Sparse Key := [(key1098, 2), (key1183, 2), (key1183, 2), (key984, 2), (key1183, 2), (key1183, 2), (key984, 2), (key984, 2), (key1098, 2), (key1098, 2), (key1183, 2), (key1183, 2), (key1090, -2), (key1090, -2), (key1180, -2), (key976, -2), (key976, -2), (key1090, -2), (key1090, -2), (key1180, -2), (key1180, -2), (key976, -2), (key1090, -2), (key1090, -2)]

theorem rawRowCheck9066 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form0 = rawRow9066 := by decide +kernel

def row9066 : Integer.Sparse Key := [(key976, -6), (key984, 6), (key1090, -12), (key1098, 6), (key1180, -6), (key1183, 12)]

theorem rowCheck9066 : row9066 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9066 := by decide +kernel

theorem rowEval9066 (x : Key → ℝ) : Integer.Sparse.eval row9066 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9066, Integer.Sparse.eval_collectBalanced, rawRowCheck9066]

def rawRow9067 : Integer.Sparse Key := [(key1183, 2), (key1098, 2), (key1183, 2), (key1183, 2), (key984, 2), (key1183, 2), (key1098, 2), (key1183, 2), (key984, 2), (key1183, 2), (key984, 2), (key1098, 2), (key1090, -2), (key1180, -2), (key1090, -2), (key1090, -2), (key1180, -2), (key976, -2), (key1180, -2), (key976, -2), (key1090, -2), (key1090, -2), (key976, -2), (key1090, -2)]

theorem rawRowCheck9067 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form0 = rawRow9067 := by decide +kernel

def row9067 : Integer.Sparse Key := [(key976, -6), (key984, 6), (key1090, -12), (key1098, 6), (key1180, -6), (key1183, 12)]

theorem rowCheck9067 : row9067 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9067 := by decide +kernel

theorem rowEval9067 (x : Key → ℝ) : Integer.Sparse.eval row9067 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9067, Integer.Sparse.eval_collectBalanced, rawRowCheck9067]

def rawRow9068 : Integer.Sparse Key := [(key1183, 2), (key1183, 2), (key1098, 2), (key1183, 2), (key1183, 2), (key984, 2), (key1183, 2), (key1098, 2), (key1183, 2), (key984, 2), (key1098, 2), (key984, 2), (key1180, -2), (key1090, -2), (key1090, -2), (key1180, -2), (key1090, -2), (key1180, -2), (key976, -2), (key1090, -2), (key976, -2), (key1090, -2), (key1090, -2), (key976, -2)]

theorem rawRowCheck9068 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form0 = rawRow9068 := by decide +kernel

def row9068 : Integer.Sparse Key := [(key976, -6), (key984, 6), (key1090, -12), (key1098, 6), (key1180, -6), (key1183, 12)]

theorem rowCheck9068 : row9068 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9068 := by decide +kernel

theorem rowEval9068 (x : Key → ℝ) : Integer.Sparse.eval row9068 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck9068, Integer.Sparse.eval_collectBalanced, rawRowCheck9068]

def rawRow9069 : Integer.Sparse Key := [(key147, -24), (key3, 6), (key86, 6), (key86, 6), (key86, 6)]

theorem rawRowCheck9069 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form1 = rawRow9069 := by decide +kernel

def row9069 : Integer.Sparse Key := [(key3, 6), (key86, 18), (key147, -24)]

theorem rowCheck9069 : row9069 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9069 := by decide +kernel

theorem rowEval9069 (x : Key → ℝ) : Integer.Sparse.eval row9069 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9069, Integer.Sparse.eval_collectBalanced, rawRowCheck9069]

def rawRow9070 : Integer.Sparse Key := [(key147, -24), (key86, 6), (key3, 6), (key86, 6), (key86, 6)]

theorem rawRowCheck9070 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form1 = rawRow9070 := by decide +kernel

def row9070 : Integer.Sparse Key := [(key3, 6), (key86, 18), (key147, -24)]

theorem rowCheck9070 : row9070 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9070 := by decide +kernel

theorem rowEval9070 (x : Key → ℝ) : Integer.Sparse.eval row9070 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9070, Integer.Sparse.eval_collectBalanced, rawRowCheck9070]

def rawRow9071 : Integer.Sparse Key := [(key147, -24), (key86, 6), (key86, 6), (key3, 6), (key86, 6)]

theorem rawRowCheck9071 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form1 = rawRow9071 := by decide +kernel

def row9071 : Integer.Sparse Key := [(key3, 6), (key86, 18), (key147, -24)]

theorem rowCheck9071 : row9071 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9071 := by decide +kernel

theorem rowEval9071 (x : Key → ℝ) : Integer.Sparse.eval row9071 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9071, Integer.Sparse.eval_collectBalanced, rawRowCheck9071]

def rawRow9072 : Integer.Sparse Key := [(key147, -24), (key86, 6), (key86, 6), (key86, 6), (key3, 6)]

theorem rawRowCheck9072 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form1 = rawRow9072 := by decide +kernel

def row9072 : Integer.Sparse Key := [(key3, 6), (key86, 18), (key147, -24)]

theorem rowCheck9072 : row9072 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9072 := by decide +kernel

theorem rowEval9072 (x : Key → ℝ) : Integer.Sparse.eval row9072 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck9072, Integer.Sparse.eval_collectBalanced, rawRowCheck9072]

def rawRow9073 : Integer.Sparse Key := [(key193, -6), (key193, -6), (key193, -6), (key202, -6), (key7, 2), (key7, 2), (key7, 2), (key90, 2), (key90, 2), (key90, 2), (key90, 2), (key90, 2), (key90, 2), (key151, 2), (key151, 2), (key151, 2)]

theorem rawRowCheck9073 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form2 = rawRow9073 := by decide +kernel

def row9073 : Integer.Sparse Key := [(key7, 6), (key90, 12), (key151, 6), (key193, -18), (key202, -6)]

theorem rowCheck9073 : row9073 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9073 := by decide +kernel

theorem rowEval9073 (x : Key → ℝ) : Integer.Sparse.eval row9073 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9073, Integer.Sparse.eval_collectBalanced, rawRowCheck9073]

def rawRow9074 : Integer.Sparse Key := [(key193, -6), (key193, -6), (key202, -6), (key193, -6), (key90, 2), (key90, 2), (key151, 2), (key7, 2), (key7, 2), (key90, 2), (key90, 2), (key151, 2), (key151, 2), (key7, 2), (key90, 2), (key90, 2)]

theorem rawRowCheck9074 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form2 = rawRow9074 := by decide +kernel

def row9074 : Integer.Sparse Key := [(key7, 6), (key90, 12), (key151, 6), (key193, -18), (key202, -6)]

theorem rowCheck9074 : row9074 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9074 := by decide +kernel

theorem rowEval9074 (x : Key → ℝ) : Integer.Sparse.eval row9074 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9074, Integer.Sparse.eval_collectBalanced, rawRowCheck9074]

def rawRow9075 : Integer.Sparse Key := [(key193, -6), (key202, -6), (key193, -6), (key193, -6), (key90, 2), (key151, 2), (key90, 2), (key90, 2), (key151, 2), (key7, 2), (key151, 2), (key7, 2), (key90, 2), (key90, 2), (key7, 2), (key90, 2)]

theorem rawRowCheck9075 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form2 = rawRow9075 := by decide +kernel

def row9075 : Integer.Sparse Key := [(key7, 6), (key90, 12), (key151, 6), (key193, -18), (key202, -6)]

theorem rowCheck9075 : row9075 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9075 := by decide +kernel

theorem rowEval9075 (x : Key → ℝ) : Integer.Sparse.eval row9075 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9075, Integer.Sparse.eval_collectBalanced, rawRowCheck9075]

def rawRow9076 : Integer.Sparse Key := [(key202, -6), (key193, -6), (key193, -6), (key193, -6), (key151, 2), (key90, 2), (key90, 2), (key151, 2), (key90, 2), (key151, 2), (key7, 2), (key90, 2), (key7, 2), (key90, 2), (key90, 2), (key7, 2)]

theorem rawRowCheck9076 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form2 = rawRow9076 := by decide +kernel

def row9076 : Integer.Sparse Key := [(key7, 6), (key90, 12), (key151, 6), (key193, -18), (key202, -6)]

theorem rowCheck9076 : row9076 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9076 := by decide +kernel

theorem rowEval9076 (x : Key → ℝ) : Integer.Sparse.eval row9076 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck9076, Integer.Sparse.eval_collectBalanced, rawRowCheck9076]

def rawRow9077 : Integer.Sparse Key := [(key1030, -6), (key1030, -6), (key1030, -6), (key1067, -6), (key1108, 2), (key1108, 2), (key1119, 2), (key1108, 2), (key1108, 2), (key1146, 2), (key1108, 2), (key1119, 2), (key1108, 2), (key1146, 2), (key1119, 2), (key1146, 2)]

theorem rawRowCheck9077 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form3 = rawRow9077 := by decide +kernel

def row9077 : Integer.Sparse Key := [(key1030, -18), (key1067, -6), (key1108, 12), (key1119, 6), (key1146, 6)]

theorem rowCheck9077 : row9077 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9077 := by decide +kernel

theorem rowEval9077 (x : Key → ℝ) : Integer.Sparse.eval row9077 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck9077, Integer.Sparse.eval_collectBalanced, rawRowCheck9077]

def rawRow9078 : Integer.Sparse Key := [(key1030, -6), (key1030, -6), (key1067, -6), (key1030, -6), (key1108, 2), (key1119, 2), (key1108, 2), (key1108, 2), (key1146, 2), (key1108, 2), (key1119, 2), (key1108, 2), (key1146, 2), (key1108, 2), (key1146, 2), (key1119, 2)]

theorem rawRowCheck9078 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form3 = rawRow9078 := by decide +kernel

def row9078 : Integer.Sparse Key := [(key1030, -18), (key1067, -6), (key1108, 12), (key1119, 6), (key1146, 6)]

theorem rowCheck9078 : row9078 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9078 := by decide +kernel

theorem rowEval9078 (x : Key → ℝ) : Integer.Sparse.eval row9078 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9078, Integer.Sparse.eval_collectBalanced, rawRowCheck9078]

def rawRow9079 : Integer.Sparse Key := [(key1030, -6), (key1067, -6), (key1030, -6), (key1030, -6), (key1119, 2), (key1108, 2), (key1108, 2), (key1146, 2), (key1108, 2), (key1108, 2), (key1146, 2), (key1146, 2), (key1119, 2), (key1119, 2), (key1108, 2), (key1108, 2)]

theorem rawRowCheck9079 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form3 = rawRow9079 := by decide +kernel

def row9079 : Integer.Sparse Key := [(key1030, -18), (key1067, -6), (key1108, 12), (key1119, 6), (key1146, 6)]

theorem rowCheck9079 : row9079 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9079 := by decide +kernel

theorem rowEval9079 (x : Key → ℝ) : Integer.Sparse.eval row9079 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9079, Integer.Sparse.eval_collectBalanced, rawRowCheck9079]

def rawRow9080 : Integer.Sparse Key := [(key1067, -6), (key1030, -6), (key1030, -6), (key1030, -6), (key1146, 2), (key1146, 2), (key1146, 2), (key1119, 2), (key1119, 2), (key1119, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1108, 2)]

theorem rawRowCheck9080 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form3 = rawRow9080 := by decide +kernel

def row9080 : Integer.Sparse Key := [(key1030, -18), (key1067, -6), (key1108, 12), (key1119, 6), (key1146, 6)]

theorem rowCheck9080 : row9080 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9080 := by decide +kernel

theorem rowEval9080 (x : Key → ℝ) : Integer.Sparse.eval row9080 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9080, Integer.Sparse.eval_collectBalanced, rawRowCheck9080]

def rawRow9081 : Integer.Sparse Key := [(key1011, -6), (key1119, -6), (key1119, -6), (key1119, -6), (key995, 2), (key995, 2), (key995, 2), (key1030, 2), (key1030, 2), (key1030, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1108, 2)]

theorem rawRowCheck9081 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form3 = rawRow9081 := by decide +kernel

def row9081 : Integer.Sparse Key := [(key995, 6), (key1011, -6), (key1030, 6), (key1108, 12), (key1119, -18)]

theorem rowCheck9081 : row9081 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9081 := by decide +kernel

theorem rowEval9081 (x : Key → ℝ) : Integer.Sparse.eval row9081 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9081, Integer.Sparse.eval_collectBalanced, rawRowCheck9081]

def rawRow9082 : Integer.Sparse Key := [(key1119, -6), (key1011, -6), (key1119, -6), (key1119, -6), (key1030, 2), (key1108, 2), (key1108, 2), (key995, 2), (key1108, 2), (key1108, 2), (key995, 2), (key995, 2), (key1030, 2), (key1030, 2), (key1108, 2), (key1108, 2)]

theorem rawRowCheck9082 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form3 = rawRow9082 := by decide +kernel

def row9082 : Integer.Sparse Key := [(key995, 6), (key1011, -6), (key1030, 6), (key1108, 12), (key1119, -18)]

theorem rowCheck9082 : row9082 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9082 := by decide +kernel

theorem rowEval9082 (x : Key → ℝ) : Integer.Sparse.eval row9082 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9082, Integer.Sparse.eval_collectBalanced, rawRowCheck9082]

def rawRow9083 : Integer.Sparse Key := [(key1119, -6), (key1119, -6), (key1011, -6), (key1119, -6), (key1108, 2), (key1030, 2), (key1108, 2), (key1108, 2), (key995, 2), (key1108, 2), (key1030, 2), (key1108, 2), (key995, 2), (key1108, 2), (key995, 2), (key1030, 2)]

theorem rawRowCheck9083 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form3 = rawRow9083 := by decide +kernel

def row9083 : Integer.Sparse Key := [(key995, 6), (key1011, -6), (key1030, 6), (key1108, 12), (key1119, -18)]

theorem rowCheck9083 : row9083 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9083 := by decide +kernel

theorem rowEval9083 (x : Key → ℝ) : Integer.Sparse.eval row9083 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9083, Integer.Sparse.eval_collectBalanced, rawRowCheck9083]

def rawRow9084 : Integer.Sparse Key := [(key1119, -6), (key1119, -6), (key1119, -6), (key1011, -6), (key1108, 2), (key1108, 2), (key1030, 2), (key1108, 2), (key1108, 2), (key995, 2), (key1108, 2), (key1030, 2), (key1108, 2), (key995, 2), (key1030, 2), (key995, 2)]

theorem rawRowCheck9084 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form3 = rawRow9084 := by decide +kernel

def row9084 : Integer.Sparse Key := [(key995, 6), (key1011, -6), (key1030, 6), (key1108, 12), (key1119, -18)]

theorem rowCheck9084 : row9084 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9084 := by decide +kernel

theorem rowEval9084 (x : Key → ℝ) : Integer.Sparse.eval row9084 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck9084, Integer.Sparse.eval_collectBalanced, rawRowCheck9084]

def rawRow9085 : Integer.Sparse Key := [(key971, -6), (key979, -6), (key979, -6), (key979, -6), (key1085, 2), (key1093, 2), (key1093, 2), (key1085, 2), (key1093, 2), (key1085, 2), (key1164, 2), (key1093, 2), (key1164, 2), (key1093, 2), (key1093, 2), (key1164, 2)]

theorem rawRowCheck9085 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form4 = rawRow9085 := by decide +kernel

def row9085 : Integer.Sparse Key := [(key971, -6), (key979, -18), (key1085, 6), (key1093, 12), (key1164, 6)]

theorem rowCheck9085 : row9085 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9085 := by decide +kernel

theorem rowEval9085 (x : Key → ℝ) : Integer.Sparse.eval row9085 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck9085, Integer.Sparse.eval_collectBalanced, rawRowCheck9085]

def rawRow9086 : Integer.Sparse Key := [(key979, -6), (key971, -6), (key979, -6), (key979, -6), (key1093, 2), (key1085, 2), (key1093, 2), (key1093, 2), (key1085, 2), (key1164, 2), (key1085, 2), (key1164, 2), (key1093, 2), (key1093, 2), (key1164, 2), (key1093, 2)]

theorem rawRowCheck9086 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form4 = rawRow9086 := by decide +kernel

def row9086 : Integer.Sparse Key := [(key971, -6), (key979, -18), (key1085, 6), (key1093, 12), (key1164, 6)]

theorem rowCheck9086 : row9086 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9086 := by decide +kernel

theorem rowEval9086 (x : Key → ℝ) : Integer.Sparse.eval row9086 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9086, Integer.Sparse.eval_collectBalanced, rawRowCheck9086]

def rawRow9087 : Integer.Sparse Key := [(key979, -6), (key979, -6), (key971, -6), (key979, -6), (key1093, 2), (key1093, 2), (key1085, 2), (key1164, 2), (key1164, 2), (key1093, 2), (key1093, 2), (key1085, 2), (key1085, 2), (key1164, 2), (key1093, 2), (key1093, 2)]

theorem rawRowCheck9087 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form4 = rawRow9087 := by decide +kernel

def row9087 : Integer.Sparse Key := [(key971, -6), (key979, -18), (key1085, 6), (key1093, 12), (key1164, 6)]

theorem rowCheck9087 : row9087 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9087 := by decide +kernel

theorem rowEval9087 (x : Key → ℝ) : Integer.Sparse.eval row9087 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9087, Integer.Sparse.eval_collectBalanced, rawRowCheck9087]

end MUB6.Certificate.GramRows

end OAI
