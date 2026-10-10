import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block16
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

def rawRow18176 : Integer.Sparse Key := [(key2106, 4), (key2139, 4), (key2106, 4), (key2111, -4), (key2101, -4), (key2111, -4), (key2139, -4), (key2106, -4), (key2139, -4), (key2111, 12)]

theorem rawRowCheck18176 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form9 = rawRow18176 := by decide +kernel

def row18176 : Integer.Sparse Key := [(key2101, -4), (key2106, 4), (key2111, 4), (key2139, -4)]

theorem rowCheck18176 : row18176 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18176 := by decide +kernel

theorem rowEval18176 (x : Key → ℝ) : Integer.Sparse.eval row18176 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18176, Integer.Sparse.eval_collectBalanced, rawRowCheck18176]

def rawRow18177 : Integer.Sparse Key := [(key2139, 4), (key2106, 4), (key2106, 4), (key2111, -4), (key2111, -4), (key2101, -4), (key2139, -4), (key2139, -4), (key2106, -4), (key2111, 12)]

theorem rawRowCheck18177 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form9 = rawRow18177 := by decide +kernel

def row18177 : Integer.Sparse Key := [(key2101, -4), (key2106, 4), (key2111, 4), (key2139, -4)]

theorem rowCheck18177 : row18177 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18177 := by decide +kernel

theorem rowEval18177 (x : Key → ℝ) : Integer.Sparse.eval row18177 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18177, Integer.Sparse.eval_collectBalanced, rawRowCheck18177]

def rawRow18178 : Integer.Sparse Key := [(key2111, 4), (key2111, 4), (key2139, 4), (key2101, -4), (key2106, -4), (key2106, -4), (key2111, -4), (key2139, -4), (key2139, -4), (key2106, 12)]

theorem rawRowCheck18178 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form9 = rawRow18178 := by decide +kernel

def row18178 : Integer.Sparse Key := [(key2101, -4), (key2106, 4), (key2111, 4), (key2139, -4)]

theorem rowCheck18178 : row18178 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18178 := by decide +kernel

theorem rowEval18178 (x : Key → ℝ) : Integer.Sparse.eval row18178 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck18178, Integer.Sparse.eval_collectBalanced, rawRowCheck18178]

def rawRow18179 : Integer.Sparse Key := [(key2111, 4), (key2139, 4), (key2111, 4), (key2106, -4), (key2101, -4), (key2106, -4), (key2139, -4), (key2111, -4), (key2139, -4), (key2106, 12)]

theorem rawRowCheck18179 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form9 = rawRow18179 := by decide +kernel

def row18179 : Integer.Sparse Key := [(key2101, -4), (key2106, 4), (key2111, 4), (key2139, -4)]

theorem rowCheck18179 : row18179 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18179 := by decide +kernel

theorem rowEval18179 (x : Key → ℝ) : Integer.Sparse.eval row18179 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18179, Integer.Sparse.eval_collectBalanced, rawRowCheck18179]

def rawRow18180 : Integer.Sparse Key := [(key2139, 4), (key2111, 4), (key2111, 4), (key2106, -4), (key2106, -4), (key2101, -4), (key2139, -4), (key2139, -4), (key2111, -4), (key2106, 12)]

theorem rawRowCheck18180 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form9 = rawRow18180 := by decide +kernel

def row18180 : Integer.Sparse Key := [(key2101, -4), (key2106, 4), (key2111, 4), (key2139, -4)]

theorem rowCheck18180 : row18180 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18180 := by decide +kernel

theorem rowEval18180 (x : Key → ℝ) : Integer.Sparse.eval row18180 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18180, Integer.Sparse.eval_collectBalanced, rawRowCheck18180]

def rawRow18181 : Integer.Sparse Key := [(key2106, 4), (key2106, 4), (key2139, 4), (key2106, -4), (key2139, -4), (key2139, -4), (key2101, -4), (key2111, -4), (key2111, -4), (key2111, 12)]

theorem rawRowCheck18181 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form9 = rawRow18181 := by decide +kernel

def row18181 : Integer.Sparse Key := [(key2101, -4), (key2106, 4), (key2111, 4), (key2139, -4)]

theorem rowCheck18181 : row18181 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18181 := by decide +kernel

theorem rowEval18181 (x : Key → ℝ) : Integer.Sparse.eval row18181 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18181, Integer.Sparse.eval_collectBalanced, rawRowCheck18181]

def rawRow18182 : Integer.Sparse Key := [(key2106, 4), (key2139, 4), (key2106, 4), (key2139, -4), (key2106, -4), (key2139, -4), (key2111, -4), (key2101, -4), (key2111, -4), (key2111, 12)]

theorem rawRowCheck18182 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form9 = rawRow18182 := by decide +kernel

def row18182 : Integer.Sparse Key := [(key2101, -4), (key2106, 4), (key2111, 4), (key2139, -4)]

theorem rowCheck18182 : row18182 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18182 := by decide +kernel

theorem rowEval18182 (x : Key → ℝ) : Integer.Sparse.eval row18182 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18182, Integer.Sparse.eval_collectBalanced, rawRowCheck18182]

def rawRow18183 : Integer.Sparse Key := [(key2139, 4), (key2106, 4), (key2106, 4), (key2139, -4), (key2139, -4), (key2106, -4), (key2111, -4), (key2111, -4), (key2101, -4), (key2111, 12)]

theorem rawRowCheck18183 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form9 = rawRow18183 := by decide +kernel

def row18183 : Integer.Sparse Key := [(key2101, -4), (key2106, 4), (key2111, 4), (key2139, -4)]

theorem rowCheck18183 : row18183 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18183 := by decide +kernel

theorem rowEval18183 (x : Key → ℝ) : Integer.Sparse.eval row18183 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18183, Integer.Sparse.eval_collectBalanced, rawRowCheck18183]

def rawRow18184 : Integer.Sparse Key := [(key2139, 4), (key2139, 4), (key2139, 4), (key2106, -4), (key2106, -4), (key2106, -4), (key2111, -4), (key2111, -4), (key2111, -4), (key2101, 12)]

theorem rawRowCheck18184 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form9 = rawRow18184 := by decide +kernel

def row18184 : Integer.Sparse Key := [(key2101, 12), (key2106, -12), (key2111, -12), (key2139, 12)]

theorem rowCheck18184 : row18184 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18184 := by decide +kernel

theorem rowEval18184 (x : Key → ℝ) : Integer.Sparse.eval row18184 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18184, Integer.Sparse.eval_collectBalanced, rawRowCheck18184]

def rawRow18185 : Integer.Sparse Key := [(key2111, 4), (key2111, 4), (key2139, 4), (key2111, -4), (key2139, -4), (key2139, -4), (key2101, -4), (key2106, -4), (key2106, -4), (key2106, 12)]

theorem rawRowCheck18185 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form9 = rawRow18185 := by decide +kernel

def row18185 : Integer.Sparse Key := [(key2101, -4), (key2106, 4), (key2111, 4), (key2139, -4)]

theorem rowCheck18185 : row18185 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18185 := by decide +kernel

theorem rowEval18185 (x : Key → ℝ) : Integer.Sparse.eval row18185 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck18185, Integer.Sparse.eval_collectBalanced, rawRowCheck18185]

def rawRow18186 : Integer.Sparse Key := [(key2111, 4), (key2139, 4), (key2111, 4), (key2139, -4), (key2111, -4), (key2139, -4), (key2106, -4), (key2101, -4), (key2106, -4), (key2106, 12)]

theorem rawRowCheck18186 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form9 = rawRow18186 := by decide +kernel

def row18186 : Integer.Sparse Key := [(key2101, -4), (key2106, 4), (key2111, 4), (key2139, -4)]

theorem rowCheck18186 : row18186 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18186 := by decide +kernel

theorem rowEval18186 (x : Key → ℝ) : Integer.Sparse.eval row18186 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18186, Integer.Sparse.eval_collectBalanced, rawRowCheck18186]

def rawRow18187 : Integer.Sparse Key := [(key2139, 4), (key2111, 4), (key2111, 4), (key2139, -4), (key2139, -4), (key2111, -4), (key2106, -4), (key2106, -4), (key2101, -4), (key2106, 12)]

theorem rawRowCheck18187 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form9 = rawRow18187 := by decide +kernel

def row18187 : Integer.Sparse Key := [(key2101, -4), (key2106, 4), (key2111, 4), (key2139, -4)]

theorem rowCheck18187 : row18187 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18187 := by decide +kernel

theorem rowEval18187 (x : Key → ℝ) : Integer.Sparse.eval row18187 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18187, Integer.Sparse.eval_collectBalanced, rawRowCheck18187]

def rawRow18188 : Integer.Sparse Key := [(key2139, 4), (key2139, 4), (key2139, 4), (key2111, -4), (key2111, -4), (key2111, -4), (key2106, -4), (key2106, -4), (key2106, -4), (key2101, 12)]

theorem rawRowCheck18188 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form9 = rawRow18188 := by decide +kernel

def row18188 : Integer.Sparse Key := [(key2101, 12), (key2106, -12), (key2111, -12), (key2139, 12)]

theorem rowCheck18188 : row18188 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18188 := by decide +kernel

theorem rowEval18188 (x : Key → ℝ) : Integer.Sparse.eval row18188 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18188, Integer.Sparse.eval_collectBalanced, rawRowCheck18188]

def rawRow18189 : Integer.Sparse Key := [(key3047, -1), (key3050, -1), (key3096, -1), (key3103, -1), (key3106, -1), (key3110, -1), (key3054, 2), (key3106, 2), (key3110, 2), (key3047, -1), (key3050, -1), (key3096, -1), (key3103, -1), (key3106, -1), (key3110, -1), (key3061, 2), (key3066, 2), (key3096, 2), (key3103, 2), (key3134, 2), (key3136, 2), (key3069, -1), (key3072, -1), (key3106, -1), (key3110, -1), (key3134, -1), (key3136, -1), (key3054, 2), (key3106, 2), (key3110, 2), (key3069, -1), (key3072, -1), (key3106, -1), (key3110, -1), (key3134, -1), (key3136, -1)]

theorem rawRowCheck18189 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form10 = rawRow18189 := by decide +kernel

def row18189 : Integer.Sparse Key := [(key3047, -2), (key3050, -2), (key3054, 4), (key3061, 2), (key3066, 2), (key3069, -2), (key3072, -2)]

theorem rowCheck18189 : row18189 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18189 := by decide +kernel

theorem rowEval18189 (x : Key → ℝ) : Integer.Sparse.eval row18189 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck18189, Integer.Sparse.eval_collectBalanced, rawRowCheck18189]

def rawRow18190 : Integer.Sparse Key := [(key3050, -1), (key3047, -1), (key3103, -1), (key3096, -1), (key3110, -1), (key3106, -1), (key3054, 2), (key3110, 2), (key3106, 2), (key3050, -1), (key3047, -1), (key3103, -1), (key3096, -1), (key3110, -1), (key3106, -1), (key3066, 2), (key3061, 2), (key3103, 2), (key3096, 2), (key3136, 2), (key3134, 2), (key3072, -1), (key3069, -1), (key3110, -1), (key3106, -1), (key3136, -1), (key3134, -1), (key3054, 2), (key3110, 2), (key3106, 2), (key3072, -1), (key3069, -1), (key3110, -1), (key3106, -1), (key3136, -1), (key3134, -1)]

theorem rawRowCheck18190 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form10 = rawRow18190 := by decide +kernel

def row18190 : Integer.Sparse Key := [(key3047, -2), (key3050, -2), (key3054, 4), (key3061, 2), (key3066, 2), (key3069, -2), (key3072, -2)]

theorem rowCheck18190 : row18190 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18190 := by decide +kernel

theorem rowEval18190 (x : Key → ℝ) : Integer.Sparse.eval row18190 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck18190, Integer.Sparse.eval_collectBalanced, rawRowCheck18190]

def rawRow18191 : Integer.Sparse Key := [(key3096, -1), (key3106, -1), (key3047, -1), (key3110, -1), (key3050, -1), (key3103, -1), (key3106, 2), (key3054, 2), (key3110, 2), (key3096, -1), (key3106, -1), (key3047, -1), (key3110, -1), (key3050, -1), (key3103, -1), (key3096, 2), (key3134, 2), (key3061, 2), (key3136, 2), (key3066, 2), (key3103, 2), (key3106, -1), (key3134, -1), (key3069, -1), (key3136, -1), (key3072, -1), (key3110, -1), (key3106, 2), (key3054, 2), (key3110, 2), (key3106, -1), (key3134, -1), (key3069, -1), (key3136, -1), (key3072, -1), (key3110, -1)]

theorem rawRowCheck18191 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form10 = rawRow18191 := by decide +kernel

def row18191 : Integer.Sparse Key := [(key3047, -2), (key3050, -2), (key3054, 4), (key3061, 2), (key3066, 2), (key3069, -2), (key3072, -2)]

theorem rowCheck18191 : row18191 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18191 := by decide +kernel

theorem rowEval18191 (x : Key → ℝ) : Integer.Sparse.eval row18191 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck18191, Integer.Sparse.eval_collectBalanced, rawRowCheck18191]

def rawRow18192 : Integer.Sparse Key := [(key3106, -1), (key3096, -1), (key3110, -1), (key3047, -1), (key3103, -1), (key3050, -1), (key3106, 2), (key3110, 2), (key3054, 2), (key3106, -1), (key3096, -1), (key3110, -1), (key3047, -1), (key3103, -1), (key3050, -1), (key3134, 2), (key3096, 2), (key3136, 2), (key3061, 2), (key3103, 2), (key3066, 2), (key3134, -1), (key3106, -1), (key3136, -1), (key3069, -1), (key3110, -1), (key3072, -1), (key3106, 2), (key3110, 2), (key3054, 2), (key3134, -1), (key3106, -1), (key3136, -1), (key3069, -1), (key3110, -1), (key3072, -1)]

theorem rawRowCheck18192 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form10 = rawRow18192 := by decide +kernel

def row18192 : Integer.Sparse Key := [(key3047, -2), (key3050, -2), (key3054, 4), (key3061, 2), (key3066, 2), (key3069, -2), (key3072, -2)]

theorem rowCheck18192 : row18192 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18192 := by decide +kernel

theorem rowEval18192 (x : Key → ℝ) : Integer.Sparse.eval row18192 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck18192, Integer.Sparse.eval_collectBalanced, rawRowCheck18192]

def rawRow18193 : Integer.Sparse Key := [(key3103, -1), (key3110, -1), (key3050, -1), (key3106, -1), (key3047, -1), (key3096, -1), (key3110, 2), (key3054, 2), (key3106, 2), (key3103, -1), (key3110, -1), (key3050, -1), (key3106, -1), (key3047, -1), (key3096, -1), (key3103, 2), (key3136, 2), (key3066, 2), (key3134, 2), (key3061, 2), (key3096, 2), (key3110, -1), (key3136, -1), (key3072, -1), (key3134, -1), (key3069, -1), (key3106, -1), (key3110, 2), (key3054, 2), (key3106, 2), (key3110, -1), (key3136, -1), (key3072, -1), (key3134, -1), (key3069, -1), (key3106, -1)]

theorem rawRowCheck18193 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form10 = rawRow18193 := by decide +kernel

def row18193 : Integer.Sparse Key := [(key3047, -2), (key3050, -2), (key3054, 4), (key3061, 2), (key3066, 2), (key3069, -2), (key3072, -2)]

theorem rowCheck18193 : row18193 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18193 := by decide +kernel

theorem rowEval18193 (x : Key → ℝ) : Integer.Sparse.eval row18193 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck18193, Integer.Sparse.eval_collectBalanced, rawRowCheck18193]

def rawRow18194 : Integer.Sparse Key := [(key3110, -1), (key3103, -1), (key3106, -1), (key3050, -1), (key3096, -1), (key3047, -1), (key3110, 2), (key3106, 2), (key3054, 2), (key3110, -1), (key3103, -1), (key3106, -1), (key3050, -1), (key3096, -1), (key3047, -1), (key3136, 2), (key3103, 2), (key3134, 2), (key3066, 2), (key3096, 2), (key3061, 2), (key3136, -1), (key3110, -1), (key3134, -1), (key3072, -1), (key3106, -1), (key3069, -1), (key3110, 2), (key3106, 2), (key3054, 2), (key3136, -1), (key3110, -1), (key3134, -1), (key3072, -1), (key3106, -1), (key3069, -1)]

theorem rawRowCheck18194 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form10 = rawRow18194 := by decide +kernel

def row18194 : Integer.Sparse Key := [(key3047, -2), (key3050, -2), (key3054, 4), (key3061, 2), (key3066, 2), (key3069, -2), (key3072, -2)]

theorem rowCheck18194 : row18194 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18194 := by decide +kernel

theorem rowEval18194 (x : Key → ℝ) : Integer.Sparse.eval row18194 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck18194, Integer.Sparse.eval_collectBalanced, rawRowCheck18194]

def rawRow18195 : Integer.Sparse Key := [(key2679, -1), (key2689, -1), (key3047, -1), (key3110, -1), (key3054, -1), (key3110, -1), (key3050, 2), (key3050, 2), (key3103, 2), (key3061, -1), (key3069, -1), (key3061, -1), (key3136, -1), (key3069, -1), (key3136, -1), (key3047, 2), (key3072, 2), (key3047, 2), (key3110, 2), (key3072, 2), (key3110, 2), (key3050, -1), (key3066, -1), (key3050, -1), (key3103, -1), (key3066, -1), (key3103, -1), (key3069, 2), (key3069, 2), (key3136, 2), (key3054, -1), (key3072, -1), (key3054, -1), (key3110, -1), (key3072, -1), (key3110, -1)]

theorem rawRowCheck18195 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form10 = rawRow18195 := by decide +kernel

def row18195 : Integer.Sparse Key := [(key2679, -1), (key2689, -1), (key3047, 3), (key3050, 2), (key3054, -3), (key3061, -2), (key3066, -2), (key3069, 2), (key3072, 2)]

theorem rowCheck18195 : row18195 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18195 := by decide +kernel

theorem rowEval18195 (x : Key → ℝ) : Integer.Sparse.eval row18195 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck18195, Integer.Sparse.eval_collectBalanced, rawRowCheck18195]

def rawRow18196 : Integer.Sparse Key := [(key2689, -1), (key2679, -1), (key3110, -1), (key3047, -1), (key3110, -1), (key3054, -1), (key3050, 2), (key3103, 2), (key3050, 2), (key3069, -1), (key3061, -1), (key3136, -1), (key3061, -1), (key3136, -1), (key3069, -1), (key3072, 2), (key3047, 2), (key3110, 2), (key3047, 2), (key3110, 2), (key3072, 2), (key3066, -1), (key3050, -1), (key3103, -1), (key3050, -1), (key3103, -1), (key3066, -1), (key3069, 2), (key3136, 2), (key3069, 2), (key3072, -1), (key3054, -1), (key3110, -1), (key3054, -1), (key3110, -1), (key3072, -1)]

theorem rawRowCheck18196 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form10 = rawRow18196 := by decide +kernel

def row18196 : Integer.Sparse Key := [(key2679, -1), (key2689, -1), (key3047, 3), (key3050, 2), (key3054, -3), (key3061, -2), (key3066, -2), (key3069, 2), (key3072, 2)]

theorem rowCheck18196 : row18196 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18196 := by decide +kernel

theorem rowEval18196 (x : Key → ℝ) : Integer.Sparse.eval row18196 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck18196, Integer.Sparse.eval_collectBalanced, rawRowCheck18196]

def rawRow18197 : Integer.Sparse Key := [(key2955, -1), (key2955, -1), (key2689, -1), (key2689, -1), (key2679, -1), (key3047, -1), (key3103, 2), (key3050, 2), (key3050, 2), (key3136, -1), (key3136, -1), (key3069, -1), (key3069, -1), (key3061, -1), (key3061, -1), (key3110, 2), (key3110, 2), (key3072, 2), (key3072, 2), (key3047, 2), (key3047, 2), (key3103, -1), (key3103, -1), (key3066, -1), (key3066, -1), (key3050, -1), (key3050, -1), (key3136, 2), (key3069, 2), (key3069, 2), (key3110, -1), (key3110, -1), (key3072, -1), (key3072, -1), (key3054, -1), (key3054, -1)]

theorem rawRowCheck18197 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form10 = rawRow18197 := by decide +kernel

def row18197 : Integer.Sparse Key := [(key2679, -1), (key2689, -2), (key2955, -2), (key3047, 3), (key3050, 2), (key3054, -2), (key3061, -2), (key3066, -2), (key3069, 2), (key3072, 2), (key3110, 2)]

theorem rowCheck18197 : row18197 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18197 := by decide +kernel

theorem rowEval18197 (x : Key → ℝ) : Integer.Sparse.eval row18197 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck18197, Integer.Sparse.eval_collectBalanced, rawRowCheck18197]

def rawRow18198 : Integer.Sparse Key := [(key2682, -1), (key2689, -1), (key2682, -1), (key2818, -1), (key2689, -1), (key2818, -1), (key2679, 2), (key3047, 2), (key3096, 2), (key3066, -1), (key3072, -1), (key3066, -1), (key3134, -1), (key3072, -1), (key3134, -1), (key3050, 2), (key3069, 2), (key3050, 2), (key3106, 2), (key3069, 2), (key3106, 2), (key3047, -1), (key3061, -1), (key3047, -1), (key3096, -1), (key3061, -1), (key3096, -1), (key3072, 2), (key3072, 2), (key3134, 2), (key3054, -1), (key3069, -1), (key3054, -1), (key3106, -1), (key3069, -1), (key3106, -1)]

theorem rawRowCheck18198 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form10 = rawRow18198 := by decide +kernel

def row18198 : Integer.Sparse Key := [(key2679, 2), (key2682, -2), (key2689, -2), (key2818, -2), (key3050, 4), (key3054, -2), (key3061, -2), (key3066, -2), (key3069, 2), (key3072, 2), (key3106, 2)]

theorem rowCheck18198 : row18198 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18198 := by decide +kernel

theorem rowEval18198 (x : Key → ℝ) : Integer.Sparse.eval row18198 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck18198, Integer.Sparse.eval_collectBalanced, rawRowCheck18198]

def rawRow18199 : Integer.Sparse Key := [(key2689, -1), (key2682, -1), (key2818, -1), (key2682, -1), (key2818, -1), (key2689, -1), (key2679, 2), (key3096, 2), (key3047, 2), (key3072, -1), (key3066, -1), (key3134, -1), (key3066, -1), (key3134, -1), (key3072, -1), (key3069, 2), (key3050, 2), (key3106, 2), (key3050, 2), (key3106, 2), (key3069, 2), (key3061, -1), (key3047, -1), (key3096, -1), (key3047, -1), (key3096, -1), (key3061, -1), (key3072, 2), (key3134, 2), (key3072, 2), (key3069, -1), (key3054, -1), (key3106, -1), (key3054, -1), (key3106, -1), (key3069, -1)]

theorem rawRowCheck18199 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form10 = rawRow18199 := by decide +kernel

def row18199 : Integer.Sparse Key := [(key2679, 2), (key2682, -2), (key2689, -2), (key2818, -2), (key3050, 4), (key3054, -2), (key3061, -2), (key3066, -2), (key3069, 2), (key3072, 2), (key3106, 2)]

theorem rowCheck18199 : row18199 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18199 := by decide +kernel

theorem rowEval18199 (x : Key → ℝ) : Integer.Sparse.eval row18199 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck18199, Integer.Sparse.eval_collectBalanced, rawRowCheck18199]

def rawRow18200 : Integer.Sparse Key := [(key2818, -1), (key2818, -1), (key2689, -1), (key2689, -1), (key2682, -1), (key2682, -1), (key2813, 2), (key2679, 2), (key3047, 2), (key3134, -1), (key3134, -1), (key3072, -1), (key3072, -1), (key3066, -1), (key3066, -1), (key3106, 2), (key3106, 2), (key3069, 2), (key3069, 2), (key3050, 2), (key3050, 2), (key3096, -1), (key3096, -1), (key3061, -1), (key3061, -1), (key3047, -1), (key3047, -1), (key3134, 2), (key3072, 2), (key3072, 2), (key3106, -1), (key3106, -1), (key3069, -1), (key3069, -1), (key3054, -1), (key3054, -1)]

theorem rawRowCheck18200 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form10 = rawRow18200 := by decide +kernel

def row18200 : Integer.Sparse Key := [(key2679, 2), (key2682, -2), (key2689, -2), (key2813, 2), (key2818, -2), (key3050, 4), (key3054, -2), (key3061, -2), (key3066, -2), (key3069, 2), (key3072, 2), (key3096, -2), (key3106, 2)]

theorem rowCheck18200 : row18200 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18200 := by decide +kernel

theorem rowEval18200 (x : Key → ℝ) : Integer.Sparse.eval row18200 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck18200, Integer.Sparse.eval_collectBalanced, rawRowCheck18200]

def rawRow18201 : Integer.Sparse Key := [(key2710, -1), (key2715, -1), (key2710, -1), (key2979, -1), (key2715, -1), (key2979, -1), (key2715, 2), (key2715, 2), (key2979, 2), (key2679, -1), (key2689, -1), (key3047, -1), (key3110, -1), (key3054, -1), (key3110, -1), (key3047, 2), (key3072, 2), (key3047, 2), (key3110, 2), (key3072, 2), (key3110, 2), (key3054, -1), (key3072, -1), (key3054, -1), (key3110, -1), (key3072, -1), (key3110, -1), (key3050, 2), (key3050, 2), (key3103, 2), (key3050, -1), (key3066, -1), (key3050, -1), (key3103, -1), (key3066, -1), (key3103, -1)]

theorem rawRowCheck18201 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form10 = rawRow18201 := by decide +kernel

def row18201 : Integer.Sparse Key := [(key2679, -1), (key2689, -1), (key2710, -2), (key2715, 2), (key3047, 3), (key3050, 2), (key3054, -3), (key3066, -2), (key3072, 2)]

theorem rowCheck18201 : row18201 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18201 := by decide +kernel

theorem rowEval18201 (x : Key → ℝ) : Integer.Sparse.eval row18201 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck18201, Integer.Sparse.eval_collectBalanced, rawRowCheck18201]

def rawRow18202 : Integer.Sparse Key := [(key2715, -1), (key2710, -1), (key2979, -1), (key2710, -1), (key2979, -1), (key2715, -1), (key2715, 2), (key2979, 2), (key2715, 2), (key2689, -1), (key2679, -1), (key3110, -1), (key3047, -1), (key3110, -1), (key3054, -1), (key3072, 2), (key3047, 2), (key3110, 2), (key3047, 2), (key3110, 2), (key3072, 2), (key3072, -1), (key3054, -1), (key3110, -1), (key3054, -1), (key3110, -1), (key3072, -1), (key3050, 2), (key3103, 2), (key3050, 2), (key3066, -1), (key3050, -1), (key3103, -1), (key3050, -1), (key3103, -1), (key3066, -1)]

theorem rawRowCheck18202 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form10 = rawRow18202 := by decide +kernel

def row18202 : Integer.Sparse Key := [(key2679, -1), (key2689, -1), (key2710, -2), (key2715, 2), (key3047, 3), (key3050, 2), (key3054, -3), (key3066, -2), (key3072, 2)]

theorem rowCheck18202 : row18202 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18202 := by decide +kernel

theorem rowEval18202 (x : Key → ℝ) : Integer.Sparse.eval row18202 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck18202, Integer.Sparse.eval_collectBalanced, rawRowCheck18202]

def rawRow18203 : Integer.Sparse Key := [(key2979, -1), (key2979, -1), (key2715, -1), (key2715, -1), (key2710, -1), (key2710, -1), (key2979, 2), (key2715, 2), (key2715, 2), (key2955, -1), (key2955, -1), (key2689, -1), (key2689, -1), (key2679, -1), (key3047, -1), (key3110, 2), (key3110, 2), (key3072, 2), (key3072, 2), (key3047, 2), (key3047, 2), (key3110, -1), (key3110, -1), (key3072, -1), (key3072, -1), (key3054, -1), (key3054, -1), (key3103, 2), (key3050, 2), (key3050, 2), (key3103, -1), (key3103, -1), (key3066, -1), (key3066, -1), (key3050, -1), (key3050, -1)]

theorem rawRowCheck18203 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form10 = rawRow18203 := by decide +kernel

def row18203 : Integer.Sparse Key := [(key2679, -1), (key2689, -2), (key2710, -2), (key2715, 2), (key2955, -2), (key3047, 3), (key3050, 2), (key3054, -2), (key3066, -2), (key3072, 2), (key3110, 2)]

theorem rowCheck18203 : row18203 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18203 := by decide +kernel

theorem rowEval18203 (x : Key → ℝ) : Integer.Sparse.eval row18203 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck18203, Integer.Sparse.eval_collectBalanced, rawRowCheck18203]

def rawRow18204 : Integer.Sparse Key := [(key2715, -1), (key2715, -1), (key2715, -1), (key2715, -1), (key2715, -1), (key2715, -1), (key2710, 2), (key2710, 2), (key2710, 2), (key2742, -1), (key2742, -1), (key2742, -1), (key2742, -1), (key2742, -1), (key2742, -1), (key2689, 2), (key2689, 2), (key2689, 2), (key2689, 2), (key2689, 2), (key2689, 2), (key2679, -1), (key2679, -1), (key2679, -1), (key3047, -1), (key3047, -1), (key3047, -1), (key3066, 2), (key3066, 2), (key3066, 2), (key3050, -1), (key3050, -1), (key3050, -1), (key3050, -1), (key3050, -1), (key3050, -1)]

theorem rawRowCheck18204 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form10 = rawRow18204 := by decide +kernel

def row18204 : Integer.Sparse Key := [(key2679, -3), (key2689, 12), (key2710, 6), (key2715, -6), (key2742, -6), (key3047, -3), (key3050, -6), (key3066, 6)]

theorem rowCheck18204 : row18204 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18204 := by decide +kernel

theorem rowEval18204 (x : Key → ℝ) : Integer.Sparse.eval row18204 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck18204, Integer.Sparse.eval_collectBalanced, rawRowCheck18204]

def rawRow18205 : Integer.Sparse Key := [(key2740, -1), (key2742, -1), (key2740, -1), (key2900, -1), (key2742, -1), (key2900, -1), (key2742, 2), (key2742, 2), (key2900, 2), (key2682, -1), (key2689, -1), (key2682, -1), (key2818, -1), (key2689, -1), (key2818, -1), (key2682, 2), (key2715, 2), (key2682, 2), (key2818, 2), (key2715, 2), (key2818, 2), (key2689, -1), (key2715, -1), (key2689, -1), (key2818, -1), (key2715, -1), (key2818, -1), (key2679, 2), (key3047, 2), (key3096, 2), (key3047, -1), (key3061, -1), (key3047, -1), (key3096, -1), (key3061, -1), (key3096, -1)]

theorem rawRowCheck18205 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form10 = rawRow18205 := by decide +kernel

def row18205 : Integer.Sparse Key := [(key2679, 2), (key2682, 2), (key2689, -4), (key2715, 2), (key2740, -2), (key2742, 2), (key3061, -2)]

theorem rowCheck18205 : row18205 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18205 := by decide +kernel

theorem rowEval18205 (x : Key → ℝ) : Integer.Sparse.eval row18205 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck18205, Integer.Sparse.eval_collectBalanced, rawRowCheck18205]

def rawRow18206 : Integer.Sparse Key := [(key2742, -1), (key2740, -1), (key2900, -1), (key2740, -1), (key2900, -1), (key2742, -1), (key2742, 2), (key2900, 2), (key2742, 2), (key2689, -1), (key2682, -1), (key2818, -1), (key2682, -1), (key2818, -1), (key2689, -1), (key2715, 2), (key2682, 2), (key2818, 2), (key2682, 2), (key2818, 2), (key2715, 2), (key2715, -1), (key2689, -1), (key2818, -1), (key2689, -1), (key2818, -1), (key2715, -1), (key2679, 2), (key3096, 2), (key3047, 2), (key3061, -1), (key3047, -1), (key3096, -1), (key3047, -1), (key3096, -1), (key3061, -1)]

theorem rawRowCheck18206 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form10 = rawRow18206 := by decide +kernel

def row18206 : Integer.Sparse Key := [(key2679, 2), (key2682, 2), (key2689, -4), (key2715, 2), (key2740, -2), (key2742, 2), (key3061, -2)]

theorem rowCheck18206 : row18206 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18206 := by decide +kernel

theorem rowEval18206 (x : Key → ℝ) : Integer.Sparse.eval row18206 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck18206, Integer.Sparse.eval_collectBalanced, rawRowCheck18206]

def rawRow18207 : Integer.Sparse Key := [(key2900, -1), (key2900, -1), (key2742, -1), (key2742, -1), (key2740, -1), (key2740, -1), (key2900, 2), (key2742, 2), (key2742, 2), (key2818, -1), (key2818, -1), (key2689, -1), (key2689, -1), (key2682, -1), (key2682, -1), (key2818, 2), (key2818, 2), (key2715, 2), (key2715, 2), (key2682, 2), (key2682, 2), (key2818, -1), (key2818, -1), (key2715, -1), (key2715, -1), (key2689, -1), (key2689, -1), (key2813, 2), (key2679, 2), (key3047, 2), (key3096, -1), (key3096, -1), (key3061, -1), (key3061, -1), (key3047, -1), (key3047, -1)]

theorem rawRowCheck18207 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form10 = rawRow18207 := by decide +kernel

def row18207 : Integer.Sparse Key := [(key2679, 2), (key2682, 2), (key2689, -4), (key2715, 2), (key2740, -2), (key2742, 2), (key2813, 2), (key3061, -2), (key3096, -2)]

theorem rowCheck18207 : row18207 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18207 := by decide +kernel

theorem rowEval18207 (x : Key → ℝ) : Integer.Sparse.eval row18207 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck18207, Integer.Sparse.eval_collectBalanced, rawRowCheck18207]

def rawRow18208 : Integer.Sparse Key := [(key2742, -1), (key2742, -1), (key2742, -1), (key2742, -1), (key2742, -1), (key2742, -1), (key2740, 2), (key2740, 2), (key2740, 2), (key2715, -1), (key2715, -1), (key2715, -1), (key2715, -1), (key2715, -1), (key2715, -1), (key2689, 2), (key2689, 2), (key2689, 2), (key2689, 2), (key2689, 2), (key2689, 2), (key2682, -1), (key2682, -1), (key2682, -1), (key2682, -1), (key2682, -1), (key2682, -1), (key2710, 2), (key2710, 2), (key2710, 2), (key2679, -1), (key2679, -1), (key2679, -1), (key3047, -1), (key3047, -1), (key3047, -1)]

theorem rawRowCheck18208 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form10 = rawRow18208 := by decide +kernel

def row18208 : Integer.Sparse Key := [(key2679, -3), (key2682, -6), (key2689, 12), (key2710, 6), (key2715, -6), (key2740, 6), (key2742, -6), (key3047, -3)]

theorem rowCheck18208 : row18208 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18208 := by decide +kernel

theorem rowEval18208 (x : Key → ℝ) : Integer.Sparse.eval row18208 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck18208, Integer.Sparse.eval_collectBalanced, rawRowCheck18208]

def rawRow18209 : Integer.Sparse Key := [(key1500, -2), (key1503, -2), (key1507, -2), (key1507, 6), (key1500, -2), (key1503, -2), (key1507, -2), (key1500, 2), (key1503, 2), (key1732, 2), (key1874, 2), (key1736, 2), (key1875, 2), (key1507, -2), (key1736, -2), (key1875, -2), (key1507, 6), (key1507, -2), (key1736, -2), (key1875, -2)]

theorem rawRowCheck18209 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form11 = rawRow18209 := by decide +kernel

def row18209 : Integer.Sparse Key := [(key1500, -2), (key1503, -2), (key1507, 4), (key1732, 2), (key1736, -2), (key1874, 2), (key1875, -2)]

theorem rowCheck18209 : row18209 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18209 := by decide +kernel

theorem rowEval18209 (x : Key → ℝ) : Integer.Sparse.eval row18209 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck18209, Integer.Sparse.eval_collectBalanced, rawRowCheck18209]

def rawRow18210 : Integer.Sparse Key := [(key1503, -2), (key1500, -2), (key1507, -2), (key1507, 6), (key1503, -2), (key1500, -2), (key1507, -2), (key1503, 2), (key1500, 2), (key1874, 2), (key1732, 2), (key1875, 2), (key1736, 2), (key1507, -2), (key1875, -2), (key1736, -2), (key1507, 6), (key1507, -2), (key1875, -2), (key1736, -2)]

theorem rawRowCheck18210 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form11 = rawRow18210 := by decide +kernel

def row18210 : Integer.Sparse Key := [(key1500, -2), (key1503, -2), (key1507, 4), (key1732, 2), (key1736, -2), (key1874, 2), (key1875, -2)]

theorem rowCheck18210 : row18210 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18210 := by decide +kernel

theorem rowEval18210 (x : Key → ℝ) : Integer.Sparse.eval row18210 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck18210, Integer.Sparse.eval_collectBalanced, rawRowCheck18210]

def rawRow18211 : Integer.Sparse Key := [(key1500, -2), (key1507, -2), (key1503, -2), (key1507, 6), (key1500, -2), (key1507, -2), (key1503, -2), (key1732, 2), (key1736, 2), (key1500, 2), (key1875, 2), (key1503, 2), (key1874, 2), (key1736, -2), (key1507, -2), (key1875, -2), (key1507, 6), (key1736, -2), (key1507, -2), (key1875, -2)]

theorem rawRowCheck18211 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form11 = rawRow18211 := by decide +kernel

def row18211 : Integer.Sparse Key := [(key1500, -2), (key1503, -2), (key1507, 4), (key1732, 2), (key1736, -2), (key1874, 2), (key1875, -2)]

theorem rowCheck18211 : row18211 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18211 := by decide +kernel

theorem rowEval18211 (x : Key → ℝ) : Integer.Sparse.eval row18211 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck18211, Integer.Sparse.eval_collectBalanced, rawRowCheck18211]

def rawRow18212 : Integer.Sparse Key := [(key1507, -2), (key1500, -2), (key1503, -2), (key1507, 6), (key1507, -2), (key1500, -2), (key1503, -2), (key1736, 2), (key1732, 2), (key1875, 2), (key1500, 2), (key1874, 2), (key1503, 2), (key1736, -2), (key1875, -2), (key1507, -2), (key1507, 6), (key1736, -2), (key1875, -2), (key1507, -2)]

theorem rawRowCheck18212 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form11 = rawRow18212 := by decide +kernel

def row18212 : Integer.Sparse Key := [(key1500, -2), (key1503, -2), (key1507, 4), (key1732, 2), (key1736, -2), (key1874, 2), (key1875, -2)]

theorem rowCheck18212 : row18212 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18212 := by decide +kernel

theorem rowEval18212 (x : Key → ℝ) : Integer.Sparse.eval row18212 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck18212, Integer.Sparse.eval_collectBalanced, rawRowCheck18212]

def rawRow18213 : Integer.Sparse Key := [(key1503, -2), (key1507, -2), (key1500, -2), (key1507, 6), (key1503, -2), (key1507, -2), (key1500, -2), (key1874, 2), (key1875, 2), (key1503, 2), (key1736, 2), (key1500, 2), (key1732, 2), (key1875, -2), (key1507, -2), (key1736, -2), (key1507, 6), (key1875, -2), (key1507, -2), (key1736, -2)]

theorem rawRowCheck18213 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form11 = rawRow18213 := by decide +kernel

def row18213 : Integer.Sparse Key := [(key1500, -2), (key1503, -2), (key1507, 4), (key1732, 2), (key1736, -2), (key1874, 2), (key1875, -2)]

theorem rowCheck18213 : row18213 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18213 := by decide +kernel

theorem rowEval18213 (x : Key → ℝ) : Integer.Sparse.eval row18213 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck18213, Integer.Sparse.eval_collectBalanced, rawRowCheck18213]

def rawRow18214 : Integer.Sparse Key := [(key1507, -2), (key1503, -2), (key1500, -2), (key1507, 6), (key1507, -2), (key1503, -2), (key1500, -2), (key1875, 2), (key1874, 2), (key1736, 2), (key1503, 2), (key1732, 2), (key1500, 2), (key1875, -2), (key1736, -2), (key1507, -2), (key1507, 6), (key1875, -2), (key1736, -2), (key1507, -2)]

theorem rawRowCheck18214 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form11 = rawRow18214 := by decide +kernel

def row18214 : Integer.Sparse Key := [(key1500, -2), (key1503, -2), (key1507, 4), (key1732, 2), (key1736, -2), (key1874, 2), (key1875, -2)]

theorem rowCheck18214 : row18214 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18214 := by decide +kernel

theorem rowEval18214 (x : Key → ℝ) : Integer.Sparse.eval row18214 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck18214, Integer.Sparse.eval_collectBalanced, rawRowCheck18214]

def rawRow18215 : Integer.Sparse Key := [(key1500, -2), (key1507, -2), (key1507, -2), (key1503, 6), (key1732, -2), (key1736, -2), (key1736, -2), (key1500, 2), (key1507, 2), (key1500, 2), (key1875, 2), (key1507, 2), (key1875, 2), (key1503, -2), (key1503, -2), (key1874, -2), (key1736, 6), (key1507, -2), (key1507, -2), (key1875, -2)]

theorem rawRowCheck18215 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form11 = rawRow18215 := by decide +kernel

def row18215 : Integer.Sparse Key := [(key1500, 2), (key1503, 2), (key1507, -4), (key1732, -2), (key1736, 2), (key1874, -2), (key1875, 2)]

theorem rowCheck18215 : row18215 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18215 := by decide +kernel

theorem rowEval18215 (x : Key → ℝ) : Integer.Sparse.eval row18215 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck18215, Integer.Sparse.eval_collectBalanced, rawRowCheck18215]

def rawRow18216 : Integer.Sparse Key := [(key1507, -2), (key1500, -2), (key1507, -2), (key1503, 6), (key1736, -2), (key1732, -2), (key1736, -2), (key1507, 2), (key1500, 2), (key1875, 2), (key1500, 2), (key1875, 2), (key1507, 2), (key1503, -2), (key1874, -2), (key1503, -2), (key1736, 6), (key1507, -2), (key1875, -2), (key1507, -2)]

theorem rawRowCheck18216 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form11 = rawRow18216 := by decide +kernel

def row18216 : Integer.Sparse Key := [(key1500, 2), (key1503, 2), (key1507, -4), (key1732, -2), (key1736, 2), (key1874, -2), (key1875, 2)]

theorem rowCheck18216 : row18216 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18216 := by decide +kernel

theorem rowEval18216 (x : Key → ℝ) : Integer.Sparse.eval row18216 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck18216, Integer.Sparse.eval_collectBalanced, rawRowCheck18216]

def rawRow18217 : Integer.Sparse Key := [(key1507, -2), (key1507, -2), (key1500, -2), (key1503, 6), (key1736, -2), (key1736, -2), (key1732, -2), (key1875, 2), (key1875, 2), (key1507, 2), (key1507, 2), (key1500, 2), (key1500, 2), (key1874, -2), (key1503, -2), (key1503, -2), (key1736, 6), (key1875, -2), (key1507, -2), (key1507, -2)]

theorem rawRowCheck18217 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form11 = rawRow18217 := by decide +kernel

def row18217 : Integer.Sparse Key := [(key1500, 2), (key1503, 2), (key1507, -4), (key1732, -2), (key1736, 2), (key1874, -2), (key1875, 2)]

theorem rowCheck18217 : row18217 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18217 := by decide +kernel

theorem rowEval18217 (x : Key → ℝ) : Integer.Sparse.eval row18217 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck18217, Integer.Sparse.eval_collectBalanced, rawRowCheck18217]

def rawRow18218 : Integer.Sparse Key := [(key1503, -2), (key1507, -2), (key1507, -2), (key1500, 6), (key1874, -2), (key1875, -2), (key1875, -2), (key1503, 2), (key1507, 2), (key1503, 2), (key1736, 2), (key1507, 2), (key1736, 2), (key1500, -2), (key1500, -2), (key1732, -2), (key1875, 6), (key1507, -2), (key1507, -2), (key1736, -2)]

theorem rawRowCheck18218 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form11 = rawRow18218 := by decide +kernel

def row18218 : Integer.Sparse Key := [(key1500, 2), (key1503, 2), (key1507, -4), (key1732, -2), (key1736, 2), (key1874, -2), (key1875, 2)]

theorem rowCheck18218 : row18218 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18218 := by decide +kernel

theorem rowEval18218 (x : Key → ℝ) : Integer.Sparse.eval row18218 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck18218, Integer.Sparse.eval_collectBalanced, rawRowCheck18218]

def rawRow18219 : Integer.Sparse Key := [(key1507, -2), (key1503, -2), (key1507, -2), (key1500, 6), (key1875, -2), (key1874, -2), (key1875, -2), (key1507, 2), (key1503, 2), (key1736, 2), (key1503, 2), (key1736, 2), (key1507, 2), (key1500, -2), (key1732, -2), (key1500, -2), (key1875, 6), (key1507, -2), (key1736, -2), (key1507, -2)]

theorem rawRowCheck18219 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form11 = rawRow18219 := by decide +kernel

def row18219 : Integer.Sparse Key := [(key1500, 2), (key1503, 2), (key1507, -4), (key1732, -2), (key1736, 2), (key1874, -2), (key1875, 2)]

theorem rowCheck18219 : row18219 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18219 := by decide +kernel

theorem rowEval18219 (x : Key → ℝ) : Integer.Sparse.eval row18219 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck18219, Integer.Sparse.eval_collectBalanced, rawRowCheck18219]

def rawRow18220 : Integer.Sparse Key := [(key1507, -2), (key1507, -2), (key1503, -2), (key1500, 6), (key1875, -2), (key1875, -2), (key1874, -2), (key1736, 2), (key1736, 2), (key1507, 2), (key1507, 2), (key1503, 2), (key1503, 2), (key1732, -2), (key1500, -2), (key1500, -2), (key1875, 6), (key1736, -2), (key1507, -2), (key1507, -2)]

theorem rawRowCheck18220 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form11 = rawRow18220 := by decide +kernel

def row18220 : Integer.Sparse Key := [(key1500, 2), (key1503, 2), (key1507, -4), (key1732, -2), (key1736, 2), (key1874, -2), (key1875, 2)]

theorem rowCheck18220 : row18220 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18220 := by decide +kernel

theorem rowEval18220 (x : Key → ℝ) : Integer.Sparse.eval row18220 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck18220, Integer.Sparse.eval_collectBalanced, rawRowCheck18220]

def rawRow18221 : Integer.Sparse Key := [(key1732, -2), (key1736, -2), (key1736, -2), (key1736, 6), (key1500, -2), (key1507, -2), (key1507, -2), (key1500, 2), (key1507, 2), (key1500, 2), (key1875, 2), (key1507, 2), (key1875, 2), (key1507, -2), (key1507, -2), (key1875, -2), (key1503, 6), (key1503, -2), (key1503, -2), (key1874, -2)]

theorem rawRowCheck18221 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form11 = rawRow18221 := by decide +kernel

def row18221 : Integer.Sparse Key := [(key1500, 2), (key1503, 2), (key1507, -4), (key1732, -2), (key1736, 2), (key1874, -2), (key1875, 2)]

theorem rowCheck18221 : row18221 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18221 := by decide +kernel

theorem rowEval18221 (x : Key → ℝ) : Integer.Sparse.eval row18221 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck18221, Integer.Sparse.eval_collectBalanced, rawRowCheck18221]

def rawRow18222 : Integer.Sparse Key := [(key1736, -2), (key1732, -2), (key1736, -2), (key1736, 6), (key1507, -2), (key1500, -2), (key1507, -2), (key1507, 2), (key1500, 2), (key1875, 2), (key1500, 2), (key1875, 2), (key1507, 2), (key1507, -2), (key1875, -2), (key1507, -2), (key1503, 6), (key1503, -2), (key1874, -2), (key1503, -2)]

theorem rawRowCheck18222 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form11 = rawRow18222 := by decide +kernel

def row18222 : Integer.Sparse Key := [(key1500, 2), (key1503, 2), (key1507, -4), (key1732, -2), (key1736, 2), (key1874, -2), (key1875, 2)]

theorem rowCheck18222 : row18222 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18222 := by decide +kernel

theorem rowEval18222 (x : Key → ℝ) : Integer.Sparse.eval row18222 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck18222, Integer.Sparse.eval_collectBalanced, rawRowCheck18222]

def rawRow18223 : Integer.Sparse Key := [(key1736, -2), (key1736, -2), (key1732, -2), (key1736, 6), (key1507, -2), (key1507, -2), (key1500, -2), (key1875, 2), (key1875, 2), (key1507, 2), (key1507, 2), (key1500, 2), (key1500, 2), (key1875, -2), (key1507, -2), (key1507, -2), (key1503, 6), (key1874, -2), (key1503, -2), (key1503, -2)]

theorem rawRowCheck18223 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form11 = rawRow18223 := by decide +kernel

def row18223 : Integer.Sparse Key := [(key1500, 2), (key1503, 2), (key1507, -4), (key1732, -2), (key1736, 2), (key1874, -2), (key1875, 2)]

theorem rowCheck18223 : row18223 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18223 := by decide +kernel

theorem rowEval18223 (x : Key → ℝ) : Integer.Sparse.eval row18223 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck18223, Integer.Sparse.eval_collectBalanced, rawRowCheck18223]

def rawRow18224 : Integer.Sparse Key := [(key1736, -2), (key1736, -2), (key1736, -2), (key1732, 6), (key1875, -2), (key1875, -2), (key1875, -2), (key1507, 2), (key1507, 2), (key1507, 2), (key1507, 2), (key1507, 2), (key1507, 2), (key1500, -2), (key1500, -2), (key1500, -2), (key1874, 6), (key1503, -2), (key1503, -2), (key1503, -2)]

theorem rawRowCheck18224 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form11 = rawRow18224 := by decide +kernel

def row18224 : Integer.Sparse Key := [(key1500, -6), (key1503, -6), (key1507, 12), (key1732, 6), (key1736, -6), (key1874, 6), (key1875, -6)]

theorem rowCheck18224 : row18224 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18224 := by decide +kernel

theorem rowEval18224 (x : Key → ℝ) : Integer.Sparse.eval row18224 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck18224, Integer.Sparse.eval_collectBalanced, rawRowCheck18224]

def rawRow18225 : Integer.Sparse Key := [(key1874, -2), (key1875, -2), (key1875, -2), (key1875, 6), (key1503, -2), (key1507, -2), (key1507, -2), (key1503, 2), (key1507, 2), (key1503, 2), (key1736, 2), (key1507, 2), (key1736, 2), (key1507, -2), (key1507, -2), (key1736, -2), (key1500, 6), (key1500, -2), (key1500, -2), (key1732, -2)]

theorem rawRowCheck18225 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form11 = rawRow18225 := by decide +kernel

def row18225 : Integer.Sparse Key := [(key1500, 2), (key1503, 2), (key1507, -4), (key1732, -2), (key1736, 2), (key1874, -2), (key1875, 2)]

theorem rowCheck18225 : row18225 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18225 := by decide +kernel

theorem rowEval18225 (x : Key → ℝ) : Integer.Sparse.eval row18225 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck18225, Integer.Sparse.eval_collectBalanced, rawRowCheck18225]

def rawRow18226 : Integer.Sparse Key := [(key1875, -2), (key1874, -2), (key1875, -2), (key1875, 6), (key1507, -2), (key1503, -2), (key1507, -2), (key1507, 2), (key1503, 2), (key1736, 2), (key1503, 2), (key1736, 2), (key1507, 2), (key1507, -2), (key1736, -2), (key1507, -2), (key1500, 6), (key1500, -2), (key1732, -2), (key1500, -2)]

theorem rawRowCheck18226 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form11 = rawRow18226 := by decide +kernel

def row18226 : Integer.Sparse Key := [(key1500, 2), (key1503, 2), (key1507, -4), (key1732, -2), (key1736, 2), (key1874, -2), (key1875, 2)]

theorem rowCheck18226 : row18226 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18226 := by decide +kernel

theorem rowEval18226 (x : Key → ℝ) : Integer.Sparse.eval row18226 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck18226, Integer.Sparse.eval_collectBalanced, rawRowCheck18226]

def rawRow18227 : Integer.Sparse Key := [(key1875, -2), (key1875, -2), (key1874, -2), (key1875, 6), (key1507, -2), (key1507, -2), (key1503, -2), (key1736, 2), (key1736, 2), (key1507, 2), (key1507, 2), (key1503, 2), (key1503, 2), (key1736, -2), (key1507, -2), (key1507, -2), (key1500, 6), (key1732, -2), (key1500, -2), (key1500, -2)]

theorem rawRowCheck18227 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form11 = rawRow18227 := by decide +kernel

def row18227 : Integer.Sparse Key := [(key1500, 2), (key1503, 2), (key1507, -4), (key1732, -2), (key1736, 2), (key1874, -2), (key1875, 2)]

theorem rowCheck18227 : row18227 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18227 := by decide +kernel

theorem rowEval18227 (x : Key → ℝ) : Integer.Sparse.eval row18227 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck18227, Integer.Sparse.eval_collectBalanced, rawRowCheck18227]

def rawRow18228 : Integer.Sparse Key := [(key1875, -2), (key1875, -2), (key1875, -2), (key1874, 6), (key1736, -2), (key1736, -2), (key1736, -2), (key1507, 2), (key1507, 2), (key1507, 2), (key1507, 2), (key1507, 2), (key1507, 2), (key1503, -2), (key1503, -2), (key1503, -2), (key1732, 6), (key1500, -2), (key1500, -2), (key1500, -2)]

theorem rawRowCheck18228 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form11 = rawRow18228 := by decide +kernel

def row18228 : Integer.Sparse Key := [(key1500, -6), (key1503, -6), (key1507, 12), (key1732, 6), (key1736, -6), (key1874, 6), (key1875, -6)]

theorem rowCheck18228 : row18228 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18228 := by decide +kernel

theorem rowEval18228 (x : Key → ℝ) : Integer.Sparse.eval row18228 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck18228, Integer.Sparse.eval_collectBalanced, rawRowCheck18228]

def rawRow18229 : Integer.Sparse Key := [(key2421, 2), (key2428, 2), (key2429, 2), (key2428, -2), (key2429, -2), (key2442, -2), (key2421, 2), (key2428, 2), (key2429, 2), (key2428, -1), (key2429, -1), (key2496, -1), (key2550, -1), (key2508, -1), (key2556, -1), (key2428, -2), (key2429, -2), (key2442, -2), (key2428, -1), (key2429, -1), (key2496, -1), (key2550, -1), (key2508, -1), (key2556, -1), (key2442, 4), (key2508, 4), (key2556, 4)]

theorem rawRowCheck18229 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form12 = rawRow18229 := by decide +kernel

def row18229 : Integer.Sparse Key := [(key2421, 4), (key2428, -2), (key2429, -2), (key2496, -2), (key2508, 2), (key2550, -2), (key2556, 2)]

theorem rowCheck18229 : row18229 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18229 := by decide +kernel

theorem rowEval18229 (x : Key → ℝ) : Integer.Sparse.eval row18229 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck18229, Integer.Sparse.eval_collectBalanced, rawRowCheck18229]

def rawRow18230 : Integer.Sparse Key := [(key2421, 2), (key2429, 2), (key2428, 2), (key2429, -2), (key2428, -2), (key2442, -2), (key2421, 2), (key2429, 2), (key2428, 2), (key2429, -1), (key2428, -1), (key2550, -1), (key2496, -1), (key2556, -1), (key2508, -1), (key2429, -2), (key2428, -2), (key2442, -2), (key2429, -1), (key2428, -1), (key2550, -1), (key2496, -1), (key2556, -1), (key2508, -1), (key2442, 4), (key2556, 4), (key2508, 4)]

theorem rawRowCheck18230 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form12 = rawRow18230 := by decide +kernel

def row18230 : Integer.Sparse Key := [(key2421, 4), (key2428, -2), (key2429, -2), (key2496, -2), (key2508, 2), (key2550, -2), (key2556, 2)]

theorem rowCheck18230 : row18230 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18230 := by decide +kernel

theorem rowEval18230 (x : Key → ℝ) : Integer.Sparse.eval row18230 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck18230, Integer.Sparse.eval_collectBalanced, rawRowCheck18230]

def rawRow18231 : Integer.Sparse Key := [(key2428, 2), (key2421, 2), (key2429, 2), (key2428, -2), (key2442, -2), (key2429, -2), (key2428, 2), (key2421, 2), (key2429, 2), (key2496, -1), (key2508, -1), (key2428, -1), (key2556, -1), (key2429, -1), (key2550, -1), (key2428, -2), (key2442, -2), (key2429, -2), (key2496, -1), (key2508, -1), (key2428, -1), (key2556, -1), (key2429, -1), (key2550, -1), (key2508, 4), (key2442, 4), (key2556, 4)]

theorem rawRowCheck18231 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form12 = rawRow18231 := by decide +kernel

def row18231 : Integer.Sparse Key := [(key2421, 4), (key2428, -2), (key2429, -2), (key2496, -2), (key2508, 2), (key2550, -2), (key2556, 2)]

theorem rowCheck18231 : row18231 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18231 := by decide +kernel

theorem rowEval18231 (x : Key → ℝ) : Integer.Sparse.eval row18231 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck18231, Integer.Sparse.eval_collectBalanced, rawRowCheck18231]

def rawRow18232 : Integer.Sparse Key := [(key2428, 2), (key2429, 2), (key2421, 2), (key2442, -2), (key2428, -2), (key2429, -2), (key2428, 2), (key2429, 2), (key2421, 2), (key2508, -1), (key2496, -1), (key2556, -1), (key2428, -1), (key2550, -1), (key2429, -1), (key2442, -2), (key2428, -2), (key2429, -2), (key2508, -1), (key2496, -1), (key2556, -1), (key2428, -1), (key2550, -1), (key2429, -1), (key2508, 4), (key2556, 4), (key2442, 4)]

theorem rawRowCheck18232 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form12 = rawRow18232 := by decide +kernel

def row18232 : Integer.Sparse Key := [(key2421, 4), (key2428, -2), (key2429, -2), (key2496, -2), (key2508, 2), (key2550, -2), (key2556, 2)]

theorem rowCheck18232 : row18232 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18232 := by decide +kernel

theorem rowEval18232 (x : Key → ℝ) : Integer.Sparse.eval row18232 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck18232, Integer.Sparse.eval_collectBalanced, rawRowCheck18232]

def rawRow18233 : Integer.Sparse Key := [(key2429, 2), (key2421, 2), (key2428, 2), (key2429, -2), (key2442, -2), (key2428, -2), (key2429, 2), (key2421, 2), (key2428, 2), (key2550, -1), (key2556, -1), (key2429, -1), (key2508, -1), (key2428, -1), (key2496, -1), (key2429, -2), (key2442, -2), (key2428, -2), (key2550, -1), (key2556, -1), (key2429, -1), (key2508, -1), (key2428, -1), (key2496, -1), (key2556, 4), (key2442, 4), (key2508, 4)]

theorem rawRowCheck18233 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form12 = rawRow18233 := by decide +kernel

def row18233 : Integer.Sparse Key := [(key2421, 4), (key2428, -2), (key2429, -2), (key2496, -2), (key2508, 2), (key2550, -2), (key2556, 2)]

theorem rowCheck18233 : row18233 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18233 := by decide +kernel

theorem rowEval18233 (x : Key → ℝ) : Integer.Sparse.eval row18233 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck18233, Integer.Sparse.eval_collectBalanced, rawRowCheck18233]

def rawRow18234 : Integer.Sparse Key := [(key2429, 2), (key2428, 2), (key2421, 2), (key2442, -2), (key2429, -2), (key2428, -2), (key2429, 2), (key2428, 2), (key2421, 2), (key2556, -1), (key2550, -1), (key2508, -1), (key2429, -1), (key2496, -1), (key2428, -1), (key2442, -2), (key2429, -2), (key2428, -2), (key2556, -1), (key2550, -1), (key2508, -1), (key2429, -1), (key2496, -1), (key2428, -1), (key2556, 4), (key2508, 4), (key2442, 4)]

theorem rawRowCheck18234 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form12 = rawRow18234 := by decide +kernel

def row18234 : Integer.Sparse Key := [(key2421, 4), (key2428, -2), (key2429, -2), (key2496, -2), (key2508, 2), (key2550, -2), (key2556, 2)]

theorem rowCheck18234 : row18234 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18234 := by decide +kernel

theorem rowEval18234 (x : Key → ℝ) : Integer.Sparse.eval row18234 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck18234, Integer.Sparse.eval_collectBalanced, rawRowCheck18234]

def rawRow18235 : Integer.Sparse Key := [(key2428, 2), (key2428, 2), (key2442, 2), (key2421, -2), (key2429, -2), (key2429, -2), (key2496, 2), (key2496, 2), (key2508, 2), (key2421, -1), (key2429, -1), (key2421, -1), (key2550, -1), (key2429, -1), (key2550, -1), (key2496, -2), (key2508, -2), (key2508, -2), (key2428, -1), (key2442, -1), (key2428, -1), (key2556, -1), (key2442, -1), (key2556, -1), (key2429, 4), (key2429, 4), (key2550, 4)]

theorem rawRowCheck18235 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form12 = rawRow18235 := by decide +kernel

def row18235 : Integer.Sparse Key := [(key2421, -4), (key2428, 2), (key2429, 2), (key2496, 2), (key2508, -2), (key2550, 2), (key2556, -2)]

theorem rowCheck18235 : row18235 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18235 := by decide +kernel

theorem rowEval18235 (x : Key → ℝ) : Integer.Sparse.eval row18235 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck18235, Integer.Sparse.eval_collectBalanced, rawRowCheck18235]

def rawRow18236 : Integer.Sparse Key := [(key2428, 2), (key2442, 2), (key2428, 2), (key2429, -2), (key2421, -2), (key2429, -2), (key2496, 2), (key2508, 2), (key2496, 2), (key2429, -1), (key2421, -1), (key2550, -1), (key2421, -1), (key2550, -1), (key2429, -1), (key2508, -2), (key2496, -2), (key2508, -2), (key2442, -1), (key2428, -1), (key2556, -1), (key2428, -1), (key2556, -1), (key2442, -1), (key2429, 4), (key2550, 4), (key2429, 4)]

theorem rawRowCheck18236 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form12 = rawRow18236 := by decide +kernel

def row18236 : Integer.Sparse Key := [(key2421, -4), (key2428, 2), (key2429, 2), (key2496, 2), (key2508, -2), (key2550, 2), (key2556, -2)]

theorem rowCheck18236 : row18236 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18236 := by decide +kernel

theorem rowEval18236 (x : Key → ℝ) : Integer.Sparse.eval row18236 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck18236, Integer.Sparse.eval_collectBalanced, rawRowCheck18236]

def rawRow18237 : Integer.Sparse Key := [(key2442, 2), (key2428, 2), (key2428, 2), (key2429, -2), (key2429, -2), (key2421, -2), (key2508, 2), (key2496, 2), (key2496, 2), (key2550, -1), (key2550, -1), (key2429, -1), (key2429, -1), (key2421, -1), (key2421, -1), (key2508, -2), (key2508, -2), (key2496, -2), (key2556, -1), (key2556, -1), (key2442, -1), (key2442, -1), (key2428, -1), (key2428, -1), (key2550, 4), (key2429, 4), (key2429, 4)]

theorem rawRowCheck18237 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form12 = rawRow18237 := by decide +kernel

def row18237 : Integer.Sparse Key := [(key2421, -4), (key2428, 2), (key2429, 2), (key2496, 2), (key2508, -2), (key2550, 2), (key2556, -2)]

theorem rowCheck18237 : row18237 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18237 := by decide +kernel

theorem rowEval18237 (x : Key → ℝ) : Integer.Sparse.eval row18237 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck18237, Integer.Sparse.eval_collectBalanced, rawRowCheck18237]

def rawRow18238 : Integer.Sparse Key := [(key2429, 2), (key2429, 2), (key2442, 2), (key2421, -2), (key2428, -2), (key2428, -2), (key2550, 2), (key2550, 2), (key2556, 2), (key2421, -1), (key2428, -1), (key2421, -1), (key2496, -1), (key2428, -1), (key2496, -1), (key2550, -2), (key2556, -2), (key2556, -2), (key2429, -1), (key2442, -1), (key2429, -1), (key2508, -1), (key2442, -1), (key2508, -1), (key2428, 4), (key2428, 4), (key2496, 4)]

theorem rawRowCheck18238 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form12 = rawRow18238 := by decide +kernel

def row18238 : Integer.Sparse Key := [(key2421, -4), (key2428, 2), (key2429, 2), (key2496, 2), (key2508, -2), (key2550, 2), (key2556, -2)]

theorem rowCheck18238 : row18238 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18238 := by decide +kernel

theorem rowEval18238 (x : Key → ℝ) : Integer.Sparse.eval row18238 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck18238, Integer.Sparse.eval_collectBalanced, rawRowCheck18238]

def rawRow18239 : Integer.Sparse Key := [(key2429, 2), (key2442, 2), (key2429, 2), (key2428, -2), (key2421, -2), (key2428, -2), (key2550, 2), (key2556, 2), (key2550, 2), (key2428, -1), (key2421, -1), (key2496, -1), (key2421, -1), (key2496, -1), (key2428, -1), (key2556, -2), (key2550, -2), (key2556, -2), (key2442, -1), (key2429, -1), (key2508, -1), (key2429, -1), (key2508, -1), (key2442, -1), (key2428, 4), (key2496, 4), (key2428, 4)]

theorem rawRowCheck18239 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form12 = rawRow18239 := by decide +kernel

def row18239 : Integer.Sparse Key := [(key2421, -4), (key2428, 2), (key2429, 2), (key2496, 2), (key2508, -2), (key2550, 2), (key2556, -2)]

theorem rowCheck18239 : row18239 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18239 := by decide +kernel

theorem rowEval18239 (x : Key → ℝ) : Integer.Sparse.eval row18239 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck18239, Integer.Sparse.eval_collectBalanced, rawRowCheck18239]

def rawRow18240 : Integer.Sparse Key := [(key2442, 2), (key2429, 2), (key2429, 2), (key2428, -2), (key2428, -2), (key2421, -2), (key2556, 2), (key2550, 2), (key2550, 2), (key2496, -1), (key2496, -1), (key2428, -1), (key2428, -1), (key2421, -1), (key2421, -1), (key2556, -2), (key2556, -2), (key2550, -2), (key2508, -1), (key2508, -1), (key2442, -1), (key2442, -1), (key2429, -1), (key2429, -1), (key2496, 4), (key2428, 4), (key2428, 4)]

theorem rawRowCheck18240 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form12 = rawRow18240 := by decide +kernel

def row18240 : Integer.Sparse Key := [(key2421, -4), (key2428, 2), (key2429, 2), (key2496, 2), (key2508, -2), (key2550, 2), (key2556, -2)]

theorem rowCheck18240 : row18240 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18240 := by decide +kernel

theorem rowEval18240 (x : Key → ℝ) : Integer.Sparse.eval row18240 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck18240, Integer.Sparse.eval_collectBalanced, rawRowCheck18240]

def rawRow18241 : Integer.Sparse Key := [(key2496, 2), (key2496, 2), (key2508, 2), (key2496, -2), (key2508, -2), (key2508, -2), (key2428, 2), (key2428, 2), (key2442, 2), (key2428, -1), (key2442, -1), (key2428, -1), (key2556, -1), (key2442, -1), (key2556, -1), (key2421, -2), (key2429, -2), (key2429, -2), (key2421, -1), (key2429, -1), (key2421, -1), (key2550, -1), (key2429, -1), (key2550, -1), (key2429, 4), (key2429, 4), (key2550, 4)]

theorem rawRowCheck18241 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form12 = rawRow18241 := by decide +kernel

def row18241 : Integer.Sparse Key := [(key2421, -4), (key2428, 2), (key2429, 2), (key2496, 2), (key2508, -2), (key2550, 2), (key2556, -2)]

theorem rowCheck18241 : row18241 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18241 := by decide +kernel

theorem rowEval18241 (x : Key → ℝ) : Integer.Sparse.eval row18241 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck18241, Integer.Sparse.eval_collectBalanced, rawRowCheck18241]

def rawRow18242 : Integer.Sparse Key := [(key2496, 2), (key2508, 2), (key2496, 2), (key2508, -2), (key2496, -2), (key2508, -2), (key2428, 2), (key2442, 2), (key2428, 2), (key2442, -1), (key2428, -1), (key2556, -1), (key2428, -1), (key2556, -1), (key2442, -1), (key2429, -2), (key2421, -2), (key2429, -2), (key2429, -1), (key2421, -1), (key2550, -1), (key2421, -1), (key2550, -1), (key2429, -1), (key2429, 4), (key2550, 4), (key2429, 4)]

theorem rawRowCheck18242 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form12 = rawRow18242 := by decide +kernel

def row18242 : Integer.Sparse Key := [(key2421, -4), (key2428, 2), (key2429, 2), (key2496, 2), (key2508, -2), (key2550, 2), (key2556, -2)]

theorem rowCheck18242 : row18242 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18242 := by decide +kernel

theorem rowEval18242 (x : Key → ℝ) : Integer.Sparse.eval row18242 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck18242, Integer.Sparse.eval_collectBalanced, rawRowCheck18242]

def rawRow18243 : Integer.Sparse Key := [(key2508, 2), (key2496, 2), (key2496, 2), (key2508, -2), (key2508, -2), (key2496, -2), (key2442, 2), (key2428, 2), (key2428, 2), (key2556, -1), (key2556, -1), (key2442, -1), (key2442, -1), (key2428, -1), (key2428, -1), (key2429, -2), (key2429, -2), (key2421, -2), (key2550, -1), (key2550, -1), (key2429, -1), (key2429, -1), (key2421, -1), (key2421, -1), (key2550, 4), (key2429, 4), (key2429, 4)]

theorem rawRowCheck18243 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form12 = rawRow18243 := by decide +kernel

def row18243 : Integer.Sparse Key := [(key2421, -4), (key2428, 2), (key2429, 2), (key2496, 2), (key2508, -2), (key2550, 2), (key2556, -2)]

theorem rowCheck18243 : row18243 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18243 := by decide +kernel

theorem rowEval18243 (x : Key → ℝ) : Integer.Sparse.eval row18243 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck18243, Integer.Sparse.eval_collectBalanced, rawRowCheck18243]

def rawRow18244 : Integer.Sparse Key := [(key2508, 2), (key2508, 2), (key2508, 2), (key2496, -2), (key2496, -2), (key2496, -2), (key2556, 2), (key2556, 2), (key2556, 2), (key2428, -1), (key2428, -1), (key2428, -1), (key2428, -1), (key2428, -1), (key2428, -1), (key2550, -2), (key2550, -2), (key2550, -2), (key2429, -1), (key2429, -1), (key2429, -1), (key2429, -1), (key2429, -1), (key2429, -1), (key2421, 4), (key2421, 4), (key2421, 4)]

theorem rawRowCheck18244 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form12 = rawRow18244 := by decide +kernel

def row18244 : Integer.Sparse Key := [(key2421, 12), (key2428, -6), (key2429, -6), (key2496, -6), (key2508, 6), (key2550, -6), (key2556, 6)]

theorem rowCheck18244 : row18244 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18244 := by decide +kernel

theorem rowEval18244 (x : Key → ℝ) : Integer.Sparse.eval row18244 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck18244, Integer.Sparse.eval_collectBalanced, rawRowCheck18244]

def rawRow18245 : Integer.Sparse Key := [(key2550, 2), (key2550, 2), (key2556, 2), (key2550, -2), (key2556, -2), (key2556, -2), (key2429, 2), (key2429, 2), (key2442, 2), (key2429, -1), (key2442, -1), (key2429, -1), (key2508, -1), (key2442, -1), (key2508, -1), (key2421, -2), (key2428, -2), (key2428, -2), (key2421, -1), (key2428, -1), (key2421, -1), (key2496, -1), (key2428, -1), (key2496, -1), (key2428, 4), (key2428, 4), (key2496, 4)]

theorem rawRowCheck18245 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form12 = rawRow18245 := by decide +kernel

def row18245 : Integer.Sparse Key := [(key2421, -4), (key2428, 2), (key2429, 2), (key2496, 2), (key2508, -2), (key2550, 2), (key2556, -2)]

theorem rowCheck18245 : row18245 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18245 := by decide +kernel

theorem rowEval18245 (x : Key → ℝ) : Integer.Sparse.eval row18245 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck18245, Integer.Sparse.eval_collectBalanced, rawRowCheck18245]

def rawRow18246 : Integer.Sparse Key := [(key2550, 2), (key2556, 2), (key2550, 2), (key2556, -2), (key2550, -2), (key2556, -2), (key2429, 2), (key2442, 2), (key2429, 2), (key2442, -1), (key2429, -1), (key2508, -1), (key2429, -1), (key2508, -1), (key2442, -1), (key2428, -2), (key2421, -2), (key2428, -2), (key2428, -1), (key2421, -1), (key2496, -1), (key2421, -1), (key2496, -1), (key2428, -1), (key2428, 4), (key2496, 4), (key2428, 4)]

theorem rawRowCheck18246 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form12 = rawRow18246 := by decide +kernel

def row18246 : Integer.Sparse Key := [(key2421, -4), (key2428, 2), (key2429, 2), (key2496, 2), (key2508, -2), (key2550, 2), (key2556, -2)]

theorem rowCheck18246 : row18246 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18246 := by decide +kernel

theorem rowEval18246 (x : Key → ℝ) : Integer.Sparse.eval row18246 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck18246, Integer.Sparse.eval_collectBalanced, rawRowCheck18246]

def rawRow18247 : Integer.Sparse Key := [(key2556, 2), (key2550, 2), (key2550, 2), (key2556, -2), (key2556, -2), (key2550, -2), (key2442, 2), (key2429, 2), (key2429, 2), (key2508, -1), (key2508, -1), (key2442, -1), (key2442, -1), (key2429, -1), (key2429, -1), (key2428, -2), (key2428, -2), (key2421, -2), (key2496, -1), (key2496, -1), (key2428, -1), (key2428, -1), (key2421, -1), (key2421, -1), (key2496, 4), (key2428, 4), (key2428, 4)]

theorem rawRowCheck18247 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form12 = rawRow18247 := by decide +kernel

def row18247 : Integer.Sparse Key := [(key2421, -4), (key2428, 2), (key2429, 2), (key2496, 2), (key2508, -2), (key2550, 2), (key2556, -2)]

theorem rowCheck18247 : row18247 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18247 := by decide +kernel

theorem rowEval18247 (x : Key → ℝ) : Integer.Sparse.eval row18247 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck18247, Integer.Sparse.eval_collectBalanced, rawRowCheck18247]

def rawRow18248 : Integer.Sparse Key := [(key2556, 2), (key2556, 2), (key2556, 2), (key2550, -2), (key2550, -2), (key2550, -2), (key2508, 2), (key2508, 2), (key2508, 2), (key2429, -1), (key2429, -1), (key2429, -1), (key2429, -1), (key2429, -1), (key2429, -1), (key2496, -2), (key2496, -2), (key2496, -2), (key2428, -1), (key2428, -1), (key2428, -1), (key2428, -1), (key2428, -1), (key2428, -1), (key2421, 4), (key2421, 4), (key2421, 4)]

theorem rawRowCheck18248 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form12 = rawRow18248 := by decide +kernel

def row18248 : Integer.Sparse Key := [(key2421, 12), (key2428, -6), (key2429, -6), (key2496, -6), (key2508, 6), (key2550, -6), (key2556, 6)]

theorem rowCheck18248 : row18248 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18248 := by decide +kernel

theorem rowEval18248 (x : Key → ℝ) : Integer.Sparse.eval row18248 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck18248, Integer.Sparse.eval_collectBalanced, rawRowCheck18248]

def rawRow18249 : Integer.Sparse Key := [(key2680, 2), (key2683, 2), (key2690, 2), (key2680, -1), (key2683, -1), (key2711, -1), (key2741, -1), (key2716, -1), (key2743, -1), (key2680, 2), (key2683, 2), (key2690, 2), (key2680, -1), (key2683, -1), (key2814, -1), (key2954, -1), (key2819, -1), (key2956, -1), (key2680, -1), (key2683, -1), (key2711, -1), (key2741, -1), (key2716, -1), (key2743, -1), (key2680, -1), (key2683, -1), (key2814, -1), (key2954, -1), (key2819, -1), (key2956, -1), (key2711, 2), (key2741, 2), (key2814, 2), (key2954, 2), (key2901, 2), (key2980, 2)]

theorem rawRowCheck18249 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form13 = rawRow18249 := by decide +kernel

def row18249 : Integer.Sparse Key := [(key2690, 4), (key2716, -2), (key2743, -2), (key2819, -2), (key2901, 2), (key2956, -2), (key2980, 2)]

theorem rowCheck18249 : row18249 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18249 := by decide +kernel

theorem rowEval18249 (x : Key → ℝ) : Integer.Sparse.eval row18249 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form13) x := by
  rw [rowCheck18249, Integer.Sparse.eval_collectBalanced, rawRowCheck18249]

def rawRow18250 : Integer.Sparse Key := [(key2683, 2), (key2680, 2), (key2690, 2), (key2683, -1), (key2680, -1), (key2741, -1), (key2711, -1), (key2743, -1), (key2716, -1), (key2683, 2), (key2680, 2), (key2690, 2), (key2683, -1), (key2680, -1), (key2954, -1), (key2814, -1), (key2956, -1), (key2819, -1), (key2683, -1), (key2680, -1), (key2741, -1), (key2711, -1), (key2743, -1), (key2716, -1), (key2683, -1), (key2680, -1), (key2954, -1), (key2814, -1), (key2956, -1), (key2819, -1), (key2741, 2), (key2711, 2), (key2954, 2), (key2814, 2), (key2980, 2), (key2901, 2)]

theorem rawRowCheck18250 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form13 = rawRow18250 := by decide +kernel

def row18250 : Integer.Sparse Key := [(key2690, 4), (key2716, -2), (key2743, -2), (key2819, -2), (key2901, 2), (key2956, -2), (key2980, 2)]

theorem rowCheck18250 : row18250 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18250 := by decide +kernel

theorem rowEval18250 (x : Key → ℝ) : Integer.Sparse.eval row18250 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck18250, Integer.Sparse.eval_collectBalanced, rawRowCheck18250]

def rawRow18251 : Integer.Sparse Key := [(key2680, 2), (key2690, 2), (key2683, 2), (key2711, -1), (key2716, -1), (key2680, -1), (key2743, -1), (key2683, -1), (key2741, -1), (key2680, 2), (key2690, 2), (key2683, 2), (key2814, -1), (key2819, -1), (key2680, -1), (key2956, -1), (key2683, -1), (key2954, -1), (key2711, -1), (key2716, -1), (key2680, -1), (key2743, -1), (key2683, -1), (key2741, -1), (key2814, -1), (key2819, -1), (key2680, -1), (key2956, -1), (key2683, -1), (key2954, -1), (key2814, 2), (key2901, 2), (key2711, 2), (key2980, 2), (key2741, 2), (key2954, 2)]

theorem rawRowCheck18251 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form13 = rawRow18251 := by decide +kernel

def row18251 : Integer.Sparse Key := [(key2690, 4), (key2716, -2), (key2743, -2), (key2819, -2), (key2901, 2), (key2956, -2), (key2980, 2)]

theorem rowCheck18251 : row18251 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18251 := by decide +kernel

theorem rowEval18251 (x : Key → ℝ) : Integer.Sparse.eval row18251 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form13) x := by
  rw [rowCheck18251, Integer.Sparse.eval_collectBalanced, rawRowCheck18251]

def rawRow18252 : Integer.Sparse Key := [(key2690, 2), (key2680, 2), (key2683, 2), (key2716, -1), (key2711, -1), (key2743, -1), (key2680, -1), (key2741, -1), (key2683, -1), (key2690, 2), (key2680, 2), (key2683, 2), (key2819, -1), (key2814, -1), (key2956, -1), (key2680, -1), (key2954, -1), (key2683, -1), (key2716, -1), (key2711, -1), (key2743, -1), (key2680, -1), (key2741, -1), (key2683, -1), (key2819, -1), (key2814, -1), (key2956, -1), (key2680, -1), (key2954, -1), (key2683, -1), (key2901, 2), (key2814, 2), (key2980, 2), (key2711, 2), (key2954, 2), (key2741, 2)]

theorem rawRowCheck18252 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form13 = rawRow18252 := by decide +kernel

def row18252 : Integer.Sparse Key := [(key2690, 4), (key2716, -2), (key2743, -2), (key2819, -2), (key2901, 2), (key2956, -2), (key2980, 2)]

theorem rowCheck18252 : row18252 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18252 := by decide +kernel

theorem rowEval18252 (x : Key → ℝ) : Integer.Sparse.eval row18252 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck18252, Integer.Sparse.eval_collectBalanced, rawRowCheck18252]

def rawRow18253 : Integer.Sparse Key := [(key2683, 2), (key2690, 2), (key2680, 2), (key2741, -1), (key2743, -1), (key2683, -1), (key2716, -1), (key2680, -1), (key2711, -1), (key2683, 2), (key2690, 2), (key2680, 2), (key2954, -1), (key2956, -1), (key2683, -1), (key2819, -1), (key2680, -1), (key2814, -1), (key2741, -1), (key2743, -1), (key2683, -1), (key2716, -1), (key2680, -1), (key2711, -1), (key2954, -1), (key2956, -1), (key2683, -1), (key2819, -1), (key2680, -1), (key2814, -1), (key2954, 2), (key2980, 2), (key2741, 2), (key2901, 2), (key2711, 2), (key2814, 2)]

theorem rawRowCheck18253 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form13 = rawRow18253 := by decide +kernel

def row18253 : Integer.Sparse Key := [(key2690, 4), (key2716, -2), (key2743, -2), (key2819, -2), (key2901, 2), (key2956, -2), (key2980, 2)]

theorem rowCheck18253 : row18253 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18253 := by decide +kernel

theorem rowEval18253 (x : Key → ℝ) : Integer.Sparse.eval row18253 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck18253, Integer.Sparse.eval_collectBalanced, rawRowCheck18253]

def rawRow18254 : Integer.Sparse Key := [(key2690, 2), (key2683, 2), (key2680, 2), (key2743, -1), (key2741, -1), (key2716, -1), (key2683, -1), (key2711, -1), (key2680, -1), (key2690, 2), (key2683, 2), (key2680, 2), (key2956, -1), (key2954, -1), (key2819, -1), (key2683, -1), (key2814, -1), (key2680, -1), (key2743, -1), (key2741, -1), (key2716, -1), (key2683, -1), (key2711, -1), (key2680, -1), (key2956, -1), (key2954, -1), (key2819, -1), (key2683, -1), (key2814, -1), (key2680, -1), (key2980, 2), (key2954, 2), (key2901, 2), (key2741, 2), (key2814, 2), (key2711, 2)]

theorem rawRowCheck18254 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form13 = rawRow18254 := by decide +kernel

def row18254 : Integer.Sparse Key := [(key2690, 4), (key2716, -2), (key2743, -2), (key2819, -2), (key2901, 2), (key2956, -2), (key2980, 2)]

theorem rowCheck18254 : row18254 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18254 := by decide +kernel

theorem rowEval18254 (x : Key → ℝ) : Integer.Sparse.eval row18254 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck18254, Integer.Sparse.eval_collectBalanced, rawRowCheck18254]

def rawRow18255 : Integer.Sparse Key := [(key2711, 2), (key2716, 2), (key2716, 2), (key2680, -1), (key2690, -1), (key2680, -1), (key2743, -1), (key2690, -1), (key2743, -1), (key2814, 2), (key2819, 2), (key2819, 2), (key2680, -1), (key2690, -1), (key2680, -1), (key2956, -1), (key2690, -1), (key2956, -1), (key2814, -1), (key2819, -1), (key2814, -1), (key2901, -1), (key2819, -1), (key2901, -1), (key2711, -1), (key2716, -1), (key2711, -1), (key2980, -1), (key2716, -1), (key2980, -1), (key2680, 2), (key2743, 2), (key2680, 2), (key2956, 2), (key2743, 2), (key2956, 2)]

theorem rawRowCheck18255 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form13 = rawRow18255 := by decide +kernel

def row18255 : Integer.Sparse Key := [(key2690, -4), (key2716, 2), (key2743, 2), (key2819, 2), (key2901, -2), (key2956, 2), (key2980, -2)]

theorem rowCheck18255 : row18255 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18255 := by decide +kernel

theorem rowEval18255 (x : Key → ℝ) : Integer.Sparse.eval row18255 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form13) x := by
  rw [rowCheck18255, Integer.Sparse.eval_collectBalanced, rawRowCheck18255]

def rawRow18256 : Integer.Sparse Key := [(key2716, 2), (key2711, 2), (key2716, 2), (key2690, -1), (key2680, -1), (key2743, -1), (key2680, -1), (key2743, -1), (key2690, -1), (key2819, 2), (key2814, 2), (key2819, 2), (key2690, -1), (key2680, -1), (key2956, -1), (key2680, -1), (key2956, -1), (key2690, -1), (key2819, -1), (key2814, -1), (key2901, -1), (key2814, -1), (key2901, -1), (key2819, -1), (key2716, -1), (key2711, -1), (key2980, -1), (key2711, -1), (key2980, -1), (key2716, -1), (key2743, 2), (key2680, 2), (key2956, 2), (key2680, 2), (key2956, 2), (key2743, 2)]

theorem rawRowCheck18256 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form13 = rawRow18256 := by decide +kernel

def row18256 : Integer.Sparse Key := [(key2690, -4), (key2716, 2), (key2743, 2), (key2819, 2), (key2901, -2), (key2956, 2), (key2980, -2)]

theorem rowCheck18256 : row18256 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18256 := by decide +kernel

theorem rowEval18256 (x : Key → ℝ) : Integer.Sparse.eval row18256 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck18256, Integer.Sparse.eval_collectBalanced, rawRowCheck18256]

def rawRow18257 : Integer.Sparse Key := [(key2716, 2), (key2716, 2), (key2711, 2), (key2743, -1), (key2743, -1), (key2690, -1), (key2690, -1), (key2680, -1), (key2680, -1), (key2819, 2), (key2819, 2), (key2814, 2), (key2956, -1), (key2956, -1), (key2690, -1), (key2690, -1), (key2680, -1), (key2680, -1), (key2901, -1), (key2901, -1), (key2819, -1), (key2819, -1), (key2814, -1), (key2814, -1), (key2980, -1), (key2980, -1), (key2716, -1), (key2716, -1), (key2711, -1), (key2711, -1), (key2956, 2), (key2956, 2), (key2743, 2), (key2743, 2), (key2680, 2), (key2680, 2)]

theorem rawRowCheck18257 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form13 = rawRow18257 := by decide +kernel

def row18257 : Integer.Sparse Key := [(key2690, -4), (key2716, 2), (key2743, 2), (key2819, 2), (key2901, -2), (key2956, 2), (key2980, -2)]

theorem rowCheck18257 : row18257 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18257 := by decide +kernel

theorem rowEval18257 (x : Key → ℝ) : Integer.Sparse.eval row18257 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck18257, Integer.Sparse.eval_collectBalanced, rawRowCheck18257]

def rawRow18258 : Integer.Sparse Key := [(key2741, 2), (key2743, 2), (key2743, 2), (key2683, -1), (key2690, -1), (key2683, -1), (key2716, -1), (key2690, -1), (key2716, -1), (key2954, 2), (key2956, 2), (key2956, 2), (key2683, -1), (key2690, -1), (key2683, -1), (key2819, -1), (key2690, -1), (key2819, -1), (key2954, -1), (key2956, -1), (key2954, -1), (key2980, -1), (key2956, -1), (key2980, -1), (key2741, -1), (key2743, -1), (key2741, -1), (key2901, -1), (key2743, -1), (key2901, -1), (key2683, 2), (key2716, 2), (key2683, 2), (key2819, 2), (key2716, 2), (key2819, 2)]

theorem rawRowCheck18258 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form13 = rawRow18258 := by decide +kernel

def row18258 : Integer.Sparse Key := [(key2690, -4), (key2716, 2), (key2743, 2), (key2819, 2), (key2901, -2), (key2956, 2), (key2980, -2)]

theorem rowCheck18258 : row18258 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18258 := by decide +kernel

theorem rowEval18258 (x : Key → ℝ) : Integer.Sparse.eval row18258 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck18258, Integer.Sparse.eval_collectBalanced, rawRowCheck18258]

def rawRow18259 : Integer.Sparse Key := [(key2743, 2), (key2741, 2), (key2743, 2), (key2690, -1), (key2683, -1), (key2716, -1), (key2683, -1), (key2716, -1), (key2690, -1), (key2956, 2), (key2954, 2), (key2956, 2), (key2690, -1), (key2683, -1), (key2819, -1), (key2683, -1), (key2819, -1), (key2690, -1), (key2956, -1), (key2954, -1), (key2980, -1), (key2954, -1), (key2980, -1), (key2956, -1), (key2743, -1), (key2741, -1), (key2901, -1), (key2741, -1), (key2901, -1), (key2743, -1), (key2716, 2), (key2683, 2), (key2819, 2), (key2683, 2), (key2819, 2), (key2716, 2)]

theorem rawRowCheck18259 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form13 = rawRow18259 := by decide +kernel

def row18259 : Integer.Sparse Key := [(key2690, -4), (key2716, 2), (key2743, 2), (key2819, 2), (key2901, -2), (key2956, 2), (key2980, -2)]

theorem rowCheck18259 : row18259 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18259 := by decide +kernel

theorem rowEval18259 (x : Key → ℝ) : Integer.Sparse.eval row18259 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck18259, Integer.Sparse.eval_collectBalanced, rawRowCheck18259]

def rawRow18260 : Integer.Sparse Key := [(key2743, 2), (key2743, 2), (key2741, 2), (key2716, -1), (key2716, -1), (key2690, -1), (key2690, -1), (key2683, -1), (key2683, -1), (key2956, 2), (key2956, 2), (key2954, 2), (key2819, -1), (key2819, -1), (key2690, -1), (key2690, -1), (key2683, -1), (key2683, -1), (key2980, -1), (key2980, -1), (key2956, -1), (key2956, -1), (key2954, -1), (key2954, -1), (key2901, -1), (key2901, -1), (key2743, -1), (key2743, -1), (key2741, -1), (key2741, -1), (key2819, 2), (key2819, 2), (key2716, 2), (key2716, 2), (key2683, 2), (key2683, 2)]

theorem rawRowCheck18260 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form13 = rawRow18260 := by decide +kernel

def row18260 : Integer.Sparse Key := [(key2690, -4), (key2716, 2), (key2743, 2), (key2819, 2), (key2901, -2), (key2956, 2), (key2980, -2)]

theorem rowCheck18260 : row18260 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18260 := by decide +kernel

theorem rowEval18260 (x : Key → ℝ) : Integer.Sparse.eval row18260 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck18260, Integer.Sparse.eval_collectBalanced, rawRowCheck18260]

def rawRow18261 : Integer.Sparse Key := [(key2814, 2), (key2819, 2), (key2819, 2), (key2814, -1), (key2819, -1), (key2814, -1), (key2901, -1), (key2819, -1), (key2901, -1), (key2711, 2), (key2716, 2), (key2716, 2), (key2711, -1), (key2716, -1), (key2711, -1), (key2980, -1), (key2716, -1), (key2980, -1), (key2680, -1), (key2690, -1), (key2680, -1), (key2743, -1), (key2690, -1), (key2743, -1), (key2680, -1), (key2690, -1), (key2680, -1), (key2956, -1), (key2690, -1), (key2956, -1), (key2680, 2), (key2743, 2), (key2680, 2), (key2956, 2), (key2743, 2), (key2956, 2)]

theorem rawRowCheck18261 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form13 = rawRow18261 := by decide +kernel

def row18261 : Integer.Sparse Key := [(key2690, -4), (key2716, 2), (key2743, 2), (key2819, 2), (key2901, -2), (key2956, 2), (key2980, -2)]

theorem rowCheck18261 : row18261 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18261 := by decide +kernel

theorem rowEval18261 (x : Key → ℝ) : Integer.Sparse.eval row18261 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form13) x := by
  rw [rowCheck18261, Integer.Sparse.eval_collectBalanced, rawRowCheck18261]

def rawRow18262 : Integer.Sparse Key := [(key2819, 2), (key2814, 2), (key2819, 2), (key2819, -1), (key2814, -1), (key2901, -1), (key2814, -1), (key2901, -1), (key2819, -1), (key2716, 2), (key2711, 2), (key2716, 2), (key2716, -1), (key2711, -1), (key2980, -1), (key2711, -1), (key2980, -1), (key2716, -1), (key2690, -1), (key2680, -1), (key2743, -1), (key2680, -1), (key2743, -1), (key2690, -1), (key2690, -1), (key2680, -1), (key2956, -1), (key2680, -1), (key2956, -1), (key2690, -1), (key2743, 2), (key2680, 2), (key2956, 2), (key2680, 2), (key2956, 2), (key2743, 2)]

theorem rawRowCheck18262 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form13 = rawRow18262 := by decide +kernel

def row18262 : Integer.Sparse Key := [(key2690, -4), (key2716, 2), (key2743, 2), (key2819, 2), (key2901, -2), (key2956, 2), (key2980, -2)]

theorem rowCheck18262 : row18262 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18262 := by decide +kernel

theorem rowEval18262 (x : Key → ℝ) : Integer.Sparse.eval row18262 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck18262, Integer.Sparse.eval_collectBalanced, rawRowCheck18262]

def rawRow18263 : Integer.Sparse Key := [(key2819, 2), (key2819, 2), (key2814, 2), (key2901, -1), (key2901, -1), (key2819, -1), (key2819, -1), (key2814, -1), (key2814, -1), (key2716, 2), (key2716, 2), (key2711, 2), (key2980, -1), (key2980, -1), (key2716, -1), (key2716, -1), (key2711, -1), (key2711, -1), (key2743, -1), (key2743, -1), (key2690, -1), (key2690, -1), (key2680, -1), (key2680, -1), (key2956, -1), (key2956, -1), (key2690, -1), (key2690, -1), (key2680, -1), (key2680, -1), (key2956, 2), (key2956, 2), (key2743, 2), (key2743, 2), (key2680, 2), (key2680, 2)]

theorem rawRowCheck18263 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form13 = rawRow18263 := by decide +kernel

def row18263 : Integer.Sparse Key := [(key2690, -4), (key2716, 2), (key2743, 2), (key2819, 2), (key2901, -2), (key2956, 2), (key2980, -2)]

theorem rowCheck18263 : row18263 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18263 := by decide +kernel

theorem rowEval18263 (x : Key → ℝ) : Integer.Sparse.eval row18263 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck18263, Integer.Sparse.eval_collectBalanced, rawRowCheck18263]

def rawRow18264 : Integer.Sparse Key := [(key2901, 2), (key2901, 2), (key2901, 2), (key2819, -1), (key2819, -1), (key2819, -1), (key2819, -1), (key2819, -1), (key2819, -1), (key2980, 2), (key2980, 2), (key2980, 2), (key2716, -1), (key2716, -1), (key2716, -1), (key2716, -1), (key2716, -1), (key2716, -1), (key2956, -1), (key2956, -1), (key2956, -1), (key2956, -1), (key2956, -1), (key2956, -1), (key2743, -1), (key2743, -1), (key2743, -1), (key2743, -1), (key2743, -1), (key2743, -1), (key2690, 2), (key2690, 2), (key2690, 2), (key2690, 2), (key2690, 2), (key2690, 2)]

theorem rawRowCheck18264 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form13 = rawRow18264 := by decide +kernel

def row18264 : Integer.Sparse Key := [(key2690, 12), (key2716, -6), (key2743, -6), (key2819, -6), (key2901, 6), (key2956, -6), (key2980, 6)]

theorem rowCheck18264 : row18264 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18264 := by decide +kernel

theorem rowEval18264 (x : Key → ℝ) : Integer.Sparse.eval row18264 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck18264, Integer.Sparse.eval_collectBalanced, rawRowCheck18264]

def rawRow18265 : Integer.Sparse Key := [(key2954, 2), (key2956, 2), (key2956, 2), (key2954, -1), (key2956, -1), (key2954, -1), (key2980, -1), (key2956, -1), (key2980, -1), (key2741, 2), (key2743, 2), (key2743, 2), (key2741, -1), (key2743, -1), (key2741, -1), (key2901, -1), (key2743, -1), (key2901, -1), (key2683, -1), (key2690, -1), (key2683, -1), (key2716, -1), (key2690, -1), (key2716, -1), (key2683, -1), (key2690, -1), (key2683, -1), (key2819, -1), (key2690, -1), (key2819, -1), (key2683, 2), (key2716, 2), (key2683, 2), (key2819, 2), (key2716, 2), (key2819, 2)]

theorem rawRowCheck18265 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form13 = rawRow18265 := by decide +kernel

def row18265 : Integer.Sparse Key := [(key2690, -4), (key2716, 2), (key2743, 2), (key2819, 2), (key2901, -2), (key2956, 2), (key2980, -2)]

theorem rowCheck18265 : row18265 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18265 := by decide +kernel

theorem rowEval18265 (x : Key → ℝ) : Integer.Sparse.eval row18265 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck18265, Integer.Sparse.eval_collectBalanced, rawRowCheck18265]

def rawRow18266 : Integer.Sparse Key := [(key2956, 2), (key2954, 2), (key2956, 2), (key2956, -1), (key2954, -1), (key2980, -1), (key2954, -1), (key2980, -1), (key2956, -1), (key2743, 2), (key2741, 2), (key2743, 2), (key2743, -1), (key2741, -1), (key2901, -1), (key2741, -1), (key2901, -1), (key2743, -1), (key2690, -1), (key2683, -1), (key2716, -1), (key2683, -1), (key2716, -1), (key2690, -1), (key2690, -1), (key2683, -1), (key2819, -1), (key2683, -1), (key2819, -1), (key2690, -1), (key2716, 2), (key2683, 2), (key2819, 2), (key2683, 2), (key2819, 2), (key2716, 2)]

theorem rawRowCheck18266 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form13 = rawRow18266 := by decide +kernel

def row18266 : Integer.Sparse Key := [(key2690, -4), (key2716, 2), (key2743, 2), (key2819, 2), (key2901, -2), (key2956, 2), (key2980, -2)]

theorem rowCheck18266 : row18266 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18266 := by decide +kernel

theorem rowEval18266 (x : Key → ℝ) : Integer.Sparse.eval row18266 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck18266, Integer.Sparse.eval_collectBalanced, rawRowCheck18266]

def rawRow18267 : Integer.Sparse Key := [(key2956, 2), (key2956, 2), (key2954, 2), (key2980, -1), (key2980, -1), (key2956, -1), (key2956, -1), (key2954, -1), (key2954, -1), (key2743, 2), (key2743, 2), (key2741, 2), (key2901, -1), (key2901, -1), (key2743, -1), (key2743, -1), (key2741, -1), (key2741, -1), (key2716, -1), (key2716, -1), (key2690, -1), (key2690, -1), (key2683, -1), (key2683, -1), (key2819, -1), (key2819, -1), (key2690, -1), (key2690, -1), (key2683, -1), (key2683, -1), (key2819, 2), (key2819, 2), (key2716, 2), (key2716, 2), (key2683, 2), (key2683, 2)]

theorem rawRowCheck18267 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form13 = rawRow18267 := by decide +kernel

def row18267 : Integer.Sparse Key := [(key2690, -4), (key2716, 2), (key2743, 2), (key2819, 2), (key2901, -2), (key2956, 2), (key2980, -2)]

theorem rowCheck18267 : row18267 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18267 := by decide +kernel

theorem rowEval18267 (x : Key → ℝ) : Integer.Sparse.eval row18267 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck18267, Integer.Sparse.eval_collectBalanced, rawRowCheck18267]

def rawRow18268 : Integer.Sparse Key := [(key2980, 2), (key2980, 2), (key2980, 2), (key2956, -1), (key2956, -1), (key2956, -1), (key2956, -1), (key2956, -1), (key2956, -1), (key2901, 2), (key2901, 2), (key2901, 2), (key2743, -1), (key2743, -1), (key2743, -1), (key2743, -1), (key2743, -1), (key2743, -1), (key2819, -1), (key2819, -1), (key2819, -1), (key2819, -1), (key2819, -1), (key2819, -1), (key2716, -1), (key2716, -1), (key2716, -1), (key2716, -1), (key2716, -1), (key2716, -1), (key2690, 2), (key2690, 2), (key2690, 2), (key2690, 2), (key2690, 2), (key2690, 2)]

theorem rawRowCheck18268 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form13 = rawRow18268 := by decide +kernel

def row18268 : Integer.Sparse Key := [(key2690, 12), (key2716, -6), (key2743, -6), (key2819, -6), (key2901, 6), (key2956, -6), (key2980, 6)]

theorem rowCheck18268 : row18268 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18268 := by decide +kernel

theorem rowEval18268 (x : Key → ℝ) : Integer.Sparse.eval row18268 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck18268, Integer.Sparse.eval_collectBalanced, rawRowCheck18268]

def rawRow18269 : Integer.Sparse Key := [(key2680, -1), (key2683, -1), (key2711, -1), (key2741, -1), (key2716, -1), (key2743, -1), (key2690, 2), (key2716, 2), (key2743, 2), (key2680, 1), (key2683, 1), (key2814, 1), (key2954, 1), (key2819, 1), (key2956, 1), (key2690, -2), (key2819, -2), (key2956, -2), (key2680, -1), (key2683, -1), (key2711, -1), (key2741, -1), (key2716, -1), (key2743, -1), (key2680, 1), (key2683, 1), (key2814, 1), (key2954, 1), (key2819, 1), (key2956, 1), (key2690, 2), (key2716, 2), (key2743, 2), (key2690, -2), (key2819, -2), (key2956, -2)]

theorem rawRowCheck18269 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form14 = rawRow18269 := by decide +kernel

def row18269 : Integer.Sparse Key := [(key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2), (key2814, 2), (key2819, -2), (key2954, 2), (key2956, -2)]

theorem rowCheck18269 : row18269 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18269 := by decide +kernel

theorem rowEval18269 (x : Key → ℝ) : Integer.Sparse.eval row18269 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form14) x := by
  rw [rowCheck18269, Integer.Sparse.eval_collectBalanced, rawRowCheck18269]

def rawRow18270 : Integer.Sparse Key := [(key2683, -1), (key2680, -1), (key2741, -1), (key2711, -1), (key2743, -1), (key2716, -1), (key2690, 2), (key2743, 2), (key2716, 2), (key2683, 1), (key2680, 1), (key2954, 1), (key2814, 1), (key2956, 1), (key2819, 1), (key2690, -2), (key2956, -2), (key2819, -2), (key2683, -1), (key2680, -1), (key2741, -1), (key2711, -1), (key2743, -1), (key2716, -1), (key2683, 1), (key2680, 1), (key2954, 1), (key2814, 1), (key2956, 1), (key2819, 1), (key2690, 2), (key2743, 2), (key2716, 2), (key2690, -2), (key2956, -2), (key2819, -2)]

theorem rawRowCheck18270 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form14 = rawRow18270 := by decide +kernel

def row18270 : Integer.Sparse Key := [(key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2), (key2814, 2), (key2819, -2), (key2954, 2), (key2956, -2)]

theorem rowCheck18270 : row18270 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18270 := by decide +kernel

theorem rowEval18270 (x : Key → ℝ) : Integer.Sparse.eval row18270 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck18270, Integer.Sparse.eval_collectBalanced, rawRowCheck18270]

def rawRow18271 : Integer.Sparse Key := [(key2711, -1), (key2716, -1), (key2680, -1), (key2743, -1), (key2683, -1), (key2741, -1), (key2716, 2), (key2690, 2), (key2743, 2), (key2814, 1), (key2819, 1), (key2680, 1), (key2956, 1), (key2683, 1), (key2954, 1), (key2819, -2), (key2690, -2), (key2956, -2), (key2711, -1), (key2716, -1), (key2680, -1), (key2743, -1), (key2683, -1), (key2741, -1), (key2814, 1), (key2819, 1), (key2680, 1), (key2956, 1), (key2683, 1), (key2954, 1), (key2716, 2), (key2690, 2), (key2743, 2), (key2819, -2), (key2690, -2), (key2956, -2)]

theorem rawRowCheck18271 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form14 = rawRow18271 := by decide +kernel

def row18271 : Integer.Sparse Key := [(key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2), (key2814, 2), (key2819, -2), (key2954, 2), (key2956, -2)]

theorem rowCheck18271 : row18271 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18271 := by decide +kernel

theorem rowEval18271 (x : Key → ℝ) : Integer.Sparse.eval row18271 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form14) x := by
  rw [rowCheck18271, Integer.Sparse.eval_collectBalanced, rawRowCheck18271]

def rawRow18272 : Integer.Sparse Key := [(key2716, -1), (key2711, -1), (key2743, -1), (key2680, -1), (key2741, -1), (key2683, -1), (key2716, 2), (key2743, 2), (key2690, 2), (key2819, 1), (key2814, 1), (key2956, 1), (key2680, 1), (key2954, 1), (key2683, 1), (key2819, -2), (key2956, -2), (key2690, -2), (key2716, -1), (key2711, -1), (key2743, -1), (key2680, -1), (key2741, -1), (key2683, -1), (key2819, 1), (key2814, 1), (key2956, 1), (key2680, 1), (key2954, 1), (key2683, 1), (key2716, 2), (key2743, 2), (key2690, 2), (key2819, -2), (key2956, -2), (key2690, -2)]

theorem rawRowCheck18272 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form14 = rawRow18272 := by decide +kernel

def row18272 : Integer.Sparse Key := [(key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2), (key2814, 2), (key2819, -2), (key2954, 2), (key2956, -2)]

theorem rowCheck18272 : row18272 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18272 := by decide +kernel

theorem rowEval18272 (x : Key → ℝ) : Integer.Sparse.eval row18272 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck18272, Integer.Sparse.eval_collectBalanced, rawRowCheck18272]

def rawRow18273 : Integer.Sparse Key := [(key2741, -1), (key2743, -1), (key2683, -1), (key2716, -1), (key2680, -1), (key2711, -1), (key2743, 2), (key2690, 2), (key2716, 2), (key2954, 1), (key2956, 1), (key2683, 1), (key2819, 1), (key2680, 1), (key2814, 1), (key2956, -2), (key2690, -2), (key2819, -2), (key2741, -1), (key2743, -1), (key2683, -1), (key2716, -1), (key2680, -1), (key2711, -1), (key2954, 1), (key2956, 1), (key2683, 1), (key2819, 1), (key2680, 1), (key2814, 1), (key2743, 2), (key2690, 2), (key2716, 2), (key2956, -2), (key2690, -2), (key2819, -2)]

theorem rawRowCheck18273 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form14 = rawRow18273 := by decide +kernel

def row18273 : Integer.Sparse Key := [(key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2), (key2814, 2), (key2819, -2), (key2954, 2), (key2956, -2)]

theorem rowCheck18273 : row18273 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18273 := by decide +kernel

theorem rowEval18273 (x : Key → ℝ) : Integer.Sparse.eval row18273 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck18273, Integer.Sparse.eval_collectBalanced, rawRowCheck18273]

def rawRow18274 : Integer.Sparse Key := [(key2743, -1), (key2741, -1), (key2716, -1), (key2683, -1), (key2711, -1), (key2680, -1), (key2743, 2), (key2716, 2), (key2690, 2), (key2956, 1), (key2954, 1), (key2819, 1), (key2683, 1), (key2814, 1), (key2680, 1), (key2956, -2), (key2819, -2), (key2690, -2), (key2743, -1), (key2741, -1), (key2716, -1), (key2683, -1), (key2711, -1), (key2680, -1), (key2956, 1), (key2954, 1), (key2819, 1), (key2683, 1), (key2814, 1), (key2680, 1), (key2743, 2), (key2716, 2), (key2690, 2), (key2956, -2), (key2819, -2), (key2690, -2)]

theorem rawRowCheck18274 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form14 = rawRow18274 := by decide +kernel

def row18274 : Integer.Sparse Key := [(key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2), (key2814, 2), (key2819, -2), (key2954, 2), (key2956, -2)]

theorem rowCheck18274 : row18274 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18274 := by decide +kernel

theorem rowEval18274 (x : Key → ℝ) : Integer.Sparse.eval row18274 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck18274, Integer.Sparse.eval_collectBalanced, rawRowCheck18274]

def rawRow18275 : Integer.Sparse Key := [(key2680, -1), (key2690, -1), (key2680, -1), (key2743, -1), (key2690, -1), (key2743, -1), (key2683, 2), (key2683, 2), (key2741, 2), (key2680, 1), (key2690, 1), (key2680, 1), (key2956, 1), (key2690, 1), (key2956, 1), (key2683, -2), (key2683, -2), (key2954, -2), (key2814, -1), (key2819, -1), (key2814, -1), (key2901, -1), (key2819, -1), (key2901, -1), (key2711, 1), (key2716, 1), (key2711, 1), (key2980, 1), (key2716, 1), (key2980, 1), (key2819, 2), (key2819, 2), (key2901, 2), (key2716, -2), (key2716, -2), (key2980, -2)]

theorem rawRowCheck18275 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form14 = rawRow18275 := by decide +kernel

def row18275 : Integer.Sparse Key := [(key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2), (key2814, -2), (key2819, 2), (key2954, -2), (key2956, 2)]

theorem rowCheck18275 : row18275 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18275 := by decide +kernel

theorem rowEval18275 (x : Key → ℝ) : Integer.Sparse.eval row18275 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form14) x := by
  rw [rowCheck18275, Integer.Sparse.eval_collectBalanced, rawRowCheck18275]

def rawRow18276 : Integer.Sparse Key := [(key2690, -1), (key2680, -1), (key2743, -1), (key2680, -1), (key2743, -1), (key2690, -1), (key2683, 2), (key2741, 2), (key2683, 2), (key2690, 1), (key2680, 1), (key2956, 1), (key2680, 1), (key2956, 1), (key2690, 1), (key2683, -2), (key2954, -2), (key2683, -2), (key2819, -1), (key2814, -1), (key2901, -1), (key2814, -1), (key2901, -1), (key2819, -1), (key2716, 1), (key2711, 1), (key2980, 1), (key2711, 1), (key2980, 1), (key2716, 1), (key2819, 2), (key2901, 2), (key2819, 2), (key2716, -2), (key2980, -2), (key2716, -2)]

theorem rawRowCheck18276 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form14 = rawRow18276 := by decide +kernel

def row18276 : Integer.Sparse Key := [(key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2), (key2814, -2), (key2819, 2), (key2954, -2), (key2956, 2)]

theorem rowCheck18276 : row18276 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18276 := by decide +kernel

theorem rowEval18276 (x : Key → ℝ) : Integer.Sparse.eval row18276 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck18276, Integer.Sparse.eval_collectBalanced, rawRowCheck18276]

def rawRow18277 : Integer.Sparse Key := [(key2743, -1), (key2743, -1), (key2690, -1), (key2690, -1), (key2680, -1), (key2680, -1), (key2741, 2), (key2683, 2), (key2683, 2), (key2956, 1), (key2956, 1), (key2690, 1), (key2690, 1), (key2680, 1), (key2680, 1), (key2954, -2), (key2683, -2), (key2683, -2), (key2901, -1), (key2901, -1), (key2819, -1), (key2819, -1), (key2814, -1), (key2814, -1), (key2980, 1), (key2980, 1), (key2716, 1), (key2716, 1), (key2711, 1), (key2711, 1), (key2901, 2), (key2819, 2), (key2819, 2), (key2980, -2), (key2716, -2), (key2716, -2)]

theorem rawRowCheck18277 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form14 = rawRow18277 := by decide +kernel

def row18277 : Integer.Sparse Key := [(key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2), (key2814, -2), (key2819, 2), (key2954, -2), (key2956, 2)]

theorem rowCheck18277 : row18277 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18277 := by decide +kernel

theorem rowEval18277 (x : Key → ℝ) : Integer.Sparse.eval row18277 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck18277, Integer.Sparse.eval_collectBalanced, rawRowCheck18277]

def rawRow18278 : Integer.Sparse Key := [(key2683, -1), (key2690, -1), (key2683, -1), (key2716, -1), (key2690, -1), (key2716, -1), (key2680, 2), (key2680, 2), (key2711, 2), (key2683, 1), (key2690, 1), (key2683, 1), (key2819, 1), (key2690, 1), (key2819, 1), (key2680, -2), (key2680, -2), (key2814, -2), (key2954, -1), (key2956, -1), (key2954, -1), (key2980, -1), (key2956, -1), (key2980, -1), (key2741, 1), (key2743, 1), (key2741, 1), (key2901, 1), (key2743, 1), (key2901, 1), (key2956, 2), (key2956, 2), (key2980, 2), (key2743, -2), (key2743, -2), (key2901, -2)]

theorem rawRowCheck18278 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form14 = rawRow18278 := by decide +kernel

def row18278 : Integer.Sparse Key := [(key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2), (key2814, -2), (key2819, 2), (key2954, -2), (key2956, 2)]

theorem rowCheck18278 : row18278 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18278 := by decide +kernel

theorem rowEval18278 (x : Key → ℝ) : Integer.Sparse.eval row18278 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck18278, Integer.Sparse.eval_collectBalanced, rawRowCheck18278]

def rawRow18279 : Integer.Sparse Key := [(key2690, -1), (key2683, -1), (key2716, -1), (key2683, -1), (key2716, -1), (key2690, -1), (key2680, 2), (key2711, 2), (key2680, 2), (key2690, 1), (key2683, 1), (key2819, 1), (key2683, 1), (key2819, 1), (key2690, 1), (key2680, -2), (key2814, -2), (key2680, -2), (key2956, -1), (key2954, -1), (key2980, -1), (key2954, -1), (key2980, -1), (key2956, -1), (key2743, 1), (key2741, 1), (key2901, 1), (key2741, 1), (key2901, 1), (key2743, 1), (key2956, 2), (key2980, 2), (key2956, 2), (key2743, -2), (key2901, -2), (key2743, -2)]

theorem rawRowCheck18279 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form14 = rawRow18279 := by decide +kernel

def row18279 : Integer.Sparse Key := [(key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2), (key2814, -2), (key2819, 2), (key2954, -2), (key2956, 2)]

theorem rowCheck18279 : row18279 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18279 := by decide +kernel

theorem rowEval18279 (x : Key → ℝ) : Integer.Sparse.eval row18279 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck18279, Integer.Sparse.eval_collectBalanced, rawRowCheck18279]

def rawRow18280 : Integer.Sparse Key := [(key2716, -1), (key2716, -1), (key2690, -1), (key2690, -1), (key2683, -1), (key2683, -1), (key2711, 2), (key2680, 2), (key2680, 2), (key2819, 1), (key2819, 1), (key2690, 1), (key2690, 1), (key2683, 1), (key2683, 1), (key2814, -2), (key2680, -2), (key2680, -2), (key2980, -1), (key2980, -1), (key2956, -1), (key2956, -1), (key2954, -1), (key2954, -1), (key2901, 1), (key2901, 1), (key2743, 1), (key2743, 1), (key2741, 1), (key2741, 1), (key2980, 2), (key2956, 2), (key2956, 2), (key2901, -2), (key2743, -2), (key2743, -2)]

theorem rawRowCheck18280 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form14 = rawRow18280 := by decide +kernel

def row18280 : Integer.Sparse Key := [(key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2), (key2814, -2), (key2819, 2), (key2954, -2), (key2956, 2)]

theorem rowCheck18280 : row18280 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18280 := by decide +kernel

theorem rowEval18280 (x : Key → ℝ) : Integer.Sparse.eval row18280 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck18280, Integer.Sparse.eval_collectBalanced, rawRowCheck18280]

def rawRow18281 : Integer.Sparse Key := [(key2814, -1), (key2819, -1), (key2814, -1), (key2901, -1), (key2819, -1), (key2901, -1), (key2819, 2), (key2819, 2), (key2901, 2), (key2711, 1), (key2716, 1), (key2711, 1), (key2980, 1), (key2716, 1), (key2980, 1), (key2716, -2), (key2716, -2), (key2980, -2), (key2680, -1), (key2690, -1), (key2680, -1), (key2743, -1), (key2690, -1), (key2743, -1), (key2680, 1), (key2690, 1), (key2680, 1), (key2956, 1), (key2690, 1), (key2956, 1), (key2683, 2), (key2683, 2), (key2741, 2), (key2683, -2), (key2683, -2), (key2954, -2)]

theorem rawRowCheck18281 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form14 = rawRow18281 := by decide +kernel

def row18281 : Integer.Sparse Key := [(key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2), (key2814, -2), (key2819, 2), (key2954, -2), (key2956, 2)]

theorem rowCheck18281 : row18281 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18281 := by decide +kernel

theorem rowEval18281 (x : Key → ℝ) : Integer.Sparse.eval row18281 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form14) x := by
  rw [rowCheck18281, Integer.Sparse.eval_collectBalanced, rawRowCheck18281]

def rawRow18282 : Integer.Sparse Key := [(key2819, -1), (key2814, -1), (key2901, -1), (key2814, -1), (key2901, -1), (key2819, -1), (key2819, 2), (key2901, 2), (key2819, 2), (key2716, 1), (key2711, 1), (key2980, 1), (key2711, 1), (key2980, 1), (key2716, 1), (key2716, -2), (key2980, -2), (key2716, -2), (key2690, -1), (key2680, -1), (key2743, -1), (key2680, -1), (key2743, -1), (key2690, -1), (key2690, 1), (key2680, 1), (key2956, 1), (key2680, 1), (key2956, 1), (key2690, 1), (key2683, 2), (key2741, 2), (key2683, 2), (key2683, -2), (key2954, -2), (key2683, -2)]

theorem rawRowCheck18282 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form14 = rawRow18282 := by decide +kernel

def row18282 : Integer.Sparse Key := [(key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2), (key2814, -2), (key2819, 2), (key2954, -2), (key2956, 2)]

theorem rowCheck18282 : row18282 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18282 := by decide +kernel

theorem rowEval18282 (x : Key → ℝ) : Integer.Sparse.eval row18282 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck18282, Integer.Sparse.eval_collectBalanced, rawRowCheck18282]

def rawRow18283 : Integer.Sparse Key := [(key2901, -1), (key2901, -1), (key2819, -1), (key2819, -1), (key2814, -1), (key2814, -1), (key2901, 2), (key2819, 2), (key2819, 2), (key2980, 1), (key2980, 1), (key2716, 1), (key2716, 1), (key2711, 1), (key2711, 1), (key2980, -2), (key2716, -2), (key2716, -2), (key2743, -1), (key2743, -1), (key2690, -1), (key2690, -1), (key2680, -1), (key2680, -1), (key2956, 1), (key2956, 1), (key2690, 1), (key2690, 1), (key2680, 1), (key2680, 1), (key2741, 2), (key2683, 2), (key2683, 2), (key2954, -2), (key2683, -2), (key2683, -2)]

theorem rawRowCheck18283 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form14 = rawRow18283 := by decide +kernel

def row18283 : Integer.Sparse Key := [(key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2), (key2814, -2), (key2819, 2), (key2954, -2), (key2956, 2)]

theorem rowCheck18283 : row18283 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18283 := by decide +kernel

theorem rowEval18283 (x : Key → ℝ) : Integer.Sparse.eval row18283 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck18283, Integer.Sparse.eval_collectBalanced, rawRowCheck18283]

def rawRow18284 : Integer.Sparse Key := [(key2819, -1), (key2819, -1), (key2819, -1), (key2819, -1), (key2819, -1), (key2819, -1), (key2814, 2), (key2814, 2), (key2814, 2), (key2716, 1), (key2716, 1), (key2716, 1), (key2716, 1), (key2716, 1), (key2716, 1), (key2711, -2), (key2711, -2), (key2711, -2), (key2956, -1), (key2956, -1), (key2956, -1), (key2956, -1), (key2956, -1), (key2956, -1), (key2743, 1), (key2743, 1), (key2743, 1), (key2743, 1), (key2743, 1), (key2743, 1), (key2954, 2), (key2954, 2), (key2954, 2), (key2741, -2), (key2741, -2), (key2741, -2)]

theorem rawRowCheck18284 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form14 = rawRow18284 := by decide +kernel

def row18284 : Integer.Sparse Key := [(key2711, -6), (key2716, 6), (key2741, -6), (key2743, 6), (key2814, 6), (key2819, -6), (key2954, 6), (key2956, -6)]

theorem rowCheck18284 : row18284 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18284 := by decide +kernel

theorem rowEval18284 (x : Key → ℝ) : Integer.Sparse.eval row18284 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck18284, Integer.Sparse.eval_collectBalanced, rawRowCheck18284]

def rawRow18285 : Integer.Sparse Key := [(key2954, -1), (key2956, -1), (key2954, -1), (key2980, -1), (key2956, -1), (key2980, -1), (key2956, 2), (key2956, 2), (key2980, 2), (key2741, 1), (key2743, 1), (key2741, 1), (key2901, 1), (key2743, 1), (key2901, 1), (key2743, -2), (key2743, -2), (key2901, -2), (key2683, -1), (key2690, -1), (key2683, -1), (key2716, -1), (key2690, -1), (key2716, -1), (key2683, 1), (key2690, 1), (key2683, 1), (key2819, 1), (key2690, 1), (key2819, 1), (key2680, 2), (key2680, 2), (key2711, 2), (key2680, -2), (key2680, -2), (key2814, -2)]

theorem rawRowCheck18285 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form14 = rawRow18285 := by decide +kernel

def row18285 : Integer.Sparse Key := [(key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2), (key2814, -2), (key2819, 2), (key2954, -2), (key2956, 2)]

theorem rowCheck18285 : row18285 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18285 := by decide +kernel

theorem rowEval18285 (x : Key → ℝ) : Integer.Sparse.eval row18285 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck18285, Integer.Sparse.eval_collectBalanced, rawRowCheck18285]

def rawRow18286 : Integer.Sparse Key := [(key2956, -1), (key2954, -1), (key2980, -1), (key2954, -1), (key2980, -1), (key2956, -1), (key2956, 2), (key2980, 2), (key2956, 2), (key2743, 1), (key2741, 1), (key2901, 1), (key2741, 1), (key2901, 1), (key2743, 1), (key2743, -2), (key2901, -2), (key2743, -2), (key2690, -1), (key2683, -1), (key2716, -1), (key2683, -1), (key2716, -1), (key2690, -1), (key2690, 1), (key2683, 1), (key2819, 1), (key2683, 1), (key2819, 1), (key2690, 1), (key2680, 2), (key2711, 2), (key2680, 2), (key2680, -2), (key2814, -2), (key2680, -2)]

theorem rawRowCheck18286 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form14 = rawRow18286 := by decide +kernel

def row18286 : Integer.Sparse Key := [(key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2), (key2814, -2), (key2819, 2), (key2954, -2), (key2956, 2)]

theorem rowCheck18286 : row18286 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18286 := by decide +kernel

theorem rowEval18286 (x : Key → ℝ) : Integer.Sparse.eval row18286 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck18286, Integer.Sparse.eval_collectBalanced, rawRowCheck18286]

def rawRow18287 : Integer.Sparse Key := [(key2980, -1), (key2980, -1), (key2956, -1), (key2956, -1), (key2954, -1), (key2954, -1), (key2980, 2), (key2956, 2), (key2956, 2), (key2901, 1), (key2901, 1), (key2743, 1), (key2743, 1), (key2741, 1), (key2741, 1), (key2901, -2), (key2743, -2), (key2743, -2), (key2716, -1), (key2716, -1), (key2690, -1), (key2690, -1), (key2683, -1), (key2683, -1), (key2819, 1), (key2819, 1), (key2690, 1), (key2690, 1), (key2683, 1), (key2683, 1), (key2711, 2), (key2680, 2), (key2680, 2), (key2814, -2), (key2680, -2), (key2680, -2)]

theorem rawRowCheck18287 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form14 = rawRow18287 := by decide +kernel

def row18287 : Integer.Sparse Key := [(key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2), (key2814, -2), (key2819, 2), (key2954, -2), (key2956, 2)]

theorem rowCheck18287 : row18287 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18287 := by decide +kernel

theorem rowEval18287 (x : Key → ℝ) : Integer.Sparse.eval row18287 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck18287, Integer.Sparse.eval_collectBalanced, rawRowCheck18287]

def rawRow18288 : Integer.Sparse Key := [(key2956, -1), (key2956, -1), (key2956, -1), (key2956, -1), (key2956, -1), (key2956, -1), (key2954, 2), (key2954, 2), (key2954, 2), (key2743, 1), (key2743, 1), (key2743, 1), (key2743, 1), (key2743, 1), (key2743, 1), (key2741, -2), (key2741, -2), (key2741, -2), (key2819, -1), (key2819, -1), (key2819, -1), (key2819, -1), (key2819, -1), (key2819, -1), (key2716, 1), (key2716, 1), (key2716, 1), (key2716, 1), (key2716, 1), (key2716, 1), (key2814, 2), (key2814, 2), (key2814, 2), (key2711, -2), (key2711, -2), (key2711, -2)]

theorem rawRowCheck18288 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form14 = rawRow18288 := by decide +kernel

def row18288 : Integer.Sparse Key := [(key2711, -6), (key2716, 6), (key2741, -6), (key2743, 6), (key2814, 6), (key2819, -6), (key2954, 6), (key2956, -6)]

theorem rowCheck18288 : row18288 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18288 := by decide +kernel

theorem rowEval18288 (x : Key → ℝ) : Integer.Sparse.eval row18288 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck18288, Integer.Sparse.eval_collectBalanced, rawRowCheck18288]

def rawRow18289 : Integer.Sparse Key := [(key2679, -1), (key2682, -1), (key2710, -1), (key2740, -1), (key2715, -1), (key2742, -1), (key2689, 2), (key2715, 2), (key2742, 2), (key3047, 1), (key3050, 1), (key3096, 1), (key3103, 1), (key3106, 1), (key3110, 1), (key3054, -2), (key3106, -2), (key3110, -2), (key3047, -1), (key3050, -1), (key3061, -1), (key3066, -1), (key3069, -1), (key3072, -1), (key3047, 1), (key3050, 1), (key3096, 1), (key3103, 1), (key3106, 1), (key3110, 1), (key3054, 2), (key3069, 2), (key3072, 2), (key3054, -2), (key3106, -2), (key3110, -2)]

theorem rawRowCheck18289 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form15 = rawRow18289 := by decide +kernel

def row18289 : Integer.Sparse Key := [(key2679, -1), (key2682, -1), (key2689, 2), (key2710, -1), (key2715, 1), (key2740, -1), (key2742, 1), (key3047, 1), (key3050, 1), (key3054, -2), (key3061, -1), (key3066, -1), (key3069, 1), (key3072, 1), (key3096, 2), (key3103, 2), (key3106, -2), (key3110, -2)]

theorem rowCheck18289 : row18289 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18289 := by decide +kernel

theorem rowEval18289 (x : Key → ℝ) : Integer.Sparse.eval row18289 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form15) x := by
  rw [rowCheck18289, Integer.Sparse.eval_collectBalanced, rawRowCheck18289]

def rawRow18290 : Integer.Sparse Key := [(key2682, -1), (key2679, -1), (key2740, -1), (key2710, -1), (key2742, -1), (key2715, -1), (key2689, 2), (key2742, 2), (key2715, 2), (key3050, 1), (key3047, 1), (key3103, 1), (key3096, 1), (key3110, 1), (key3106, 1), (key3054, -2), (key3110, -2), (key3106, -2), (key3050, -1), (key3047, -1), (key3066, -1), (key3061, -1), (key3072, -1), (key3069, -1), (key3050, 1), (key3047, 1), (key3103, 1), (key3096, 1), (key3110, 1), (key3106, 1), (key3054, 2), (key3072, 2), (key3069, 2), (key3054, -2), (key3110, -2), (key3106, -2)]

theorem rawRowCheck18290 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form15 = rawRow18290 := by decide +kernel

def row18290 : Integer.Sparse Key := [(key2679, -1), (key2682, -1), (key2689, 2), (key2710, -1), (key2715, 1), (key2740, -1), (key2742, 1), (key3047, 1), (key3050, 1), (key3054, -2), (key3061, -1), (key3066, -1), (key3069, 1), (key3072, 1), (key3096, 2), (key3103, 2), (key3106, -2), (key3110, -2)]

theorem rowCheck18290 : row18290 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18290 := by decide +kernel

theorem rowEval18290 (x : Key → ℝ) : Integer.Sparse.eval row18290 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck18290, Integer.Sparse.eval_collectBalanced, rawRowCheck18290]

def rawRow18291 : Integer.Sparse Key := [(key2710, -1), (key2715, -1), (key2679, -1), (key2742, -1), (key2682, -1), (key2740, -1), (key2715, 2), (key2689, 2), (key2742, 2), (key3096, 1), (key3106, 1), (key3047, 1), (key3110, 1), (key3050, 1), (key3103, 1), (key3106, -2), (key3054, -2), (key3110, -2), (key3061, -1), (key3069, -1), (key3047, -1), (key3072, -1), (key3050, -1), (key3066, -1), (key3096, 1), (key3106, 1), (key3047, 1), (key3110, 1), (key3050, 1), (key3103, 1), (key3069, 2), (key3054, 2), (key3072, 2), (key3106, -2), (key3054, -2), (key3110, -2)]

theorem rawRowCheck18291 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form15 = rawRow18291 := by decide +kernel

def row18291 : Integer.Sparse Key := [(key2679, -1), (key2682, -1), (key2689, 2), (key2710, -1), (key2715, 1), (key2740, -1), (key2742, 1), (key3047, 1), (key3050, 1), (key3054, -2), (key3061, -1), (key3066, -1), (key3069, 1), (key3072, 1), (key3096, 2), (key3103, 2), (key3106, -2), (key3110, -2)]

theorem rowCheck18291 : row18291 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18291 := by decide +kernel

theorem rowEval18291 (x : Key → ℝ) : Integer.Sparse.eval row18291 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form15) x := by
  rw [rowCheck18291, Integer.Sparse.eval_collectBalanced, rawRowCheck18291]

def rawRow18292 : Integer.Sparse Key := [(key2715, -1), (key2710, -1), (key2742, -1), (key2679, -1), (key2740, -1), (key2682, -1), (key2715, 2), (key2742, 2), (key2689, 2), (key3106, 1), (key3096, 1), (key3110, 1), (key3047, 1), (key3103, 1), (key3050, 1), (key3106, -2), (key3110, -2), (key3054, -2), (key3069, -1), (key3061, -1), (key3072, -1), (key3047, -1), (key3066, -1), (key3050, -1), (key3106, 1), (key3096, 1), (key3110, 1), (key3047, 1), (key3103, 1), (key3050, 1), (key3069, 2), (key3072, 2), (key3054, 2), (key3106, -2), (key3110, -2), (key3054, -2)]

theorem rawRowCheck18292 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form15 = rawRow18292 := by decide +kernel

def row18292 : Integer.Sparse Key := [(key2679, -1), (key2682, -1), (key2689, 2), (key2710, -1), (key2715, 1), (key2740, -1), (key2742, 1), (key3047, 1), (key3050, 1), (key3054, -2), (key3061, -1), (key3066, -1), (key3069, 1), (key3072, 1), (key3096, 2), (key3103, 2), (key3106, -2), (key3110, -2)]

theorem rowCheck18292 : row18292 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18292 := by decide +kernel

theorem rowEval18292 (x : Key → ℝ) : Integer.Sparse.eval row18292 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck18292, Integer.Sparse.eval_collectBalanced, rawRowCheck18292]

def rawRow18293 : Integer.Sparse Key := [(key2740, -1), (key2742, -1), (key2682, -1), (key2715, -1), (key2679, -1), (key2710, -1), (key2742, 2), (key2689, 2), (key2715, 2), (key3103, 1), (key3110, 1), (key3050, 1), (key3106, 1), (key3047, 1), (key3096, 1), (key3110, -2), (key3054, -2), (key3106, -2), (key3066, -1), (key3072, -1), (key3050, -1), (key3069, -1), (key3047, -1), (key3061, -1), (key3103, 1), (key3110, 1), (key3050, 1), (key3106, 1), (key3047, 1), (key3096, 1), (key3072, 2), (key3054, 2), (key3069, 2), (key3110, -2), (key3054, -2), (key3106, -2)]

theorem rawRowCheck18293 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form15 = rawRow18293 := by decide +kernel

def row18293 : Integer.Sparse Key := [(key2679, -1), (key2682, -1), (key2689, 2), (key2710, -1), (key2715, 1), (key2740, -1), (key2742, 1), (key3047, 1), (key3050, 1), (key3054, -2), (key3061, -1), (key3066, -1), (key3069, 1), (key3072, 1), (key3096, 2), (key3103, 2), (key3106, -2), (key3110, -2)]

theorem rowCheck18293 : row18293 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18293 := by decide +kernel

theorem rowEval18293 (x : Key → ℝ) : Integer.Sparse.eval row18293 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck18293, Integer.Sparse.eval_collectBalanced, rawRowCheck18293]

def rawRow18294 : Integer.Sparse Key := [(key2742, -1), (key2740, -1), (key2715, -1), (key2682, -1), (key2710, -1), (key2679, -1), (key2742, 2), (key2715, 2), (key2689, 2), (key3110, 1), (key3103, 1), (key3106, 1), (key3050, 1), (key3096, 1), (key3047, 1), (key3110, -2), (key3106, -2), (key3054, -2), (key3072, -1), (key3066, -1), (key3069, -1), (key3050, -1), (key3061, -1), (key3047, -1), (key3110, 1), (key3103, 1), (key3106, 1), (key3050, 1), (key3096, 1), (key3047, 1), (key3072, 2), (key3069, 2), (key3054, 2), (key3110, -2), (key3106, -2), (key3054, -2)]

theorem rawRowCheck18294 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form15 = rawRow18294 := by decide +kernel

def row18294 : Integer.Sparse Key := [(key2679, -1), (key2682, -1), (key2689, 2), (key2710, -1), (key2715, 1), (key2740, -1), (key2742, 1), (key3047, 1), (key3050, 1), (key3054, -2), (key3061, -1), (key3066, -1), (key3069, 1), (key3072, 1), (key3096, 2), (key3103, 2), (key3106, -2), (key3110, -2)]

theorem rowCheck18294 : row18294 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18294 := by decide +kernel

theorem rowEval18294 (x : Key → ℝ) : Integer.Sparse.eval row18294 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck18294, Integer.Sparse.eval_collectBalanced, rawRowCheck18294]

def rawRow18295 : Integer.Sparse Key := [(key2679, -1), (key2689, -1), (key2679, -1), (key2742, -1), (key2689, -1), (key2742, -1), (key2682, 2), (key2682, 2), (key2740, 2), (key2679, 1), (key2689, 1), (key3047, 1), (key3110, 1), (key3054, 1), (key3110, 1), (key3050, -2), (key3050, -2), (key3103, -2), (key3096, -1), (key3106, -1), (key3096, -1), (key3134, -1), (key3106, -1), (key3134, -1), (key3061, 1), (key3069, 1), (key3061, 1), (key3136, 1), (key3069, 1), (key3136, 1), (key3106, 2), (key3106, 2), (key3134, 2), (key3069, -2), (key3069, -2), (key3136, -2)]

theorem rawRowCheck18295 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form15 = rawRow18295 := by decide +kernel

def row18295 : Integer.Sparse Key := [(key2679, -1), (key2682, 4), (key2689, -1), (key2740, 2), (key2742, -2), (key3047, 1), (key3050, -4), (key3054, 1), (key3061, 2), (key3069, -2), (key3096, -2), (key3103, -2), (key3106, 2), (key3110, 2)]

theorem rowCheck18295 : row18295 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18295 := by decide +kernel

theorem rowEval18295 (x : Key → ℝ) : Integer.Sparse.eval row18295 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form15) x := by
  rw [rowCheck18295, Integer.Sparse.eval_collectBalanced, rawRowCheck18295]

def rawRow18296 : Integer.Sparse Key := [(key2689, -1), (key2679, -1), (key2742, -1), (key2679, -1), (key2742, -1), (key2689, -1), (key2682, 2), (key2740, 2), (key2682, 2), (key2689, 1), (key2679, 1), (key3110, 1), (key3047, 1), (key3110, 1), (key3054, 1), (key3050, -2), (key3103, -2), (key3050, -2), (key3106, -1), (key3096, -1), (key3134, -1), (key3096, -1), (key3134, -1), (key3106, -1), (key3069, 1), (key3061, 1), (key3136, 1), (key3061, 1), (key3136, 1), (key3069, 1), (key3106, 2), (key3134, 2), (key3106, 2), (key3069, -2), (key3136, -2), (key3069, -2)]

theorem rawRowCheck18296 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form15 = rawRow18296 := by decide +kernel

def row18296 : Integer.Sparse Key := [(key2679, -1), (key2682, 4), (key2689, -1), (key2740, 2), (key2742, -2), (key3047, 1), (key3050, -4), (key3054, 1), (key3061, 2), (key3069, -2), (key3096, -2), (key3103, -2), (key3106, 2), (key3110, 2)]

theorem rowCheck18296 : row18296 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18296 := by decide +kernel

theorem rowEval18296 (x : Key → ℝ) : Integer.Sparse.eval row18296 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck18296, Integer.Sparse.eval_collectBalanced, rawRowCheck18296]

def rawRow18297 : Integer.Sparse Key := [(key2742, -1), (key2742, -1), (key2689, -1), (key2689, -1), (key2679, -1), (key2679, -1), (key2740, 2), (key2682, 2), (key2682, 2), (key2955, 1), (key2955, 1), (key2689, 1), (key2689, 1), (key2679, 1), (key3047, 1), (key3103, -2), (key3050, -2), (key3050, -2), (key3134, -1), (key3134, -1), (key3106, -1), (key3106, -1), (key3096, -1), (key3096, -1), (key3136, 1), (key3136, 1), (key3069, 1), (key3069, 1), (key3061, 1), (key3061, 1), (key3134, 2), (key3106, 2), (key3106, 2), (key3136, -2), (key3069, -2), (key3069, -2)]

theorem rawRowCheck18297 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form15 = rawRow18297 := by decide +kernel

def row18297 : Integer.Sparse Key := [(key2679, -1), (key2682, 4), (key2740, 2), (key2742, -2), (key2955, 2), (key3047, 1), (key3050, -4), (key3061, 2), (key3069, -2), (key3096, -2), (key3103, -2), (key3106, 2)]

theorem rowCheck18297 : row18297 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18297 := by decide +kernel

theorem rowEval18297 (x : Key → ℝ) : Integer.Sparse.eval row18297 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck18297, Integer.Sparse.eval_collectBalanced, rawRowCheck18297]

def rawRow18298 : Integer.Sparse Key := [(key2682, -1), (key2689, -1), (key2682, -1), (key2715, -1), (key2689, -1), (key2715, -1), (key2679, 2), (key2679, 2), (key2710, 2), (key2682, 1), (key2689, 1), (key2682, 1), (key2818, 1), (key2689, 1), (key2818, 1), (key2679, -2), (key3047, -2), (key3096, -2), (key3103, -1), (key3110, -1), (key3103, -1), (key3136, -1), (key3110, -1), (key3136, -1), (key3066, 1), (key3072, 1), (key3066, 1), (key3134, 1), (key3072, 1), (key3134, 1), (key3110, 2), (key3110, 2), (key3136, 2), (key3072, -2), (key3072, -2), (key3134, -2)]

theorem rawRowCheck18298 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form15 = rawRow18298 := by decide +kernel

def row18298 : Integer.Sparse Key := [(key2679, 2), (key2710, 2), (key2715, -2), (key2818, 2), (key3047, -2), (key3066, 2), (key3072, -2), (key3096, -2), (key3103, -2), (key3110, 2)]

theorem rowCheck18298 : row18298 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18298 := by decide +kernel

theorem rowEval18298 (x : Key → ℝ) : Integer.Sparse.eval row18298 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck18298, Integer.Sparse.eval_collectBalanced, rawRowCheck18298]

def rawRow18299 : Integer.Sparse Key := [(key2689, -1), (key2682, -1), (key2715, -1), (key2682, -1), (key2715, -1), (key2689, -1), (key2679, 2), (key2710, 2), (key2679, 2), (key2689, 1), (key2682, 1), (key2818, 1), (key2682, 1), (key2818, 1), (key2689, 1), (key2679, -2), (key3096, -2), (key3047, -2), (key3110, -1), (key3103, -1), (key3136, -1), (key3103, -1), (key3136, -1), (key3110, -1), (key3072, 1), (key3066, 1), (key3134, 1), (key3066, 1), (key3134, 1), (key3072, 1), (key3110, 2), (key3136, 2), (key3110, 2), (key3072, -2), (key3134, -2), (key3072, -2)]

theorem rawRowCheck18299 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form15 = rawRow18299 := by decide +kernel

def row18299 : Integer.Sparse Key := [(key2679, 2), (key2710, 2), (key2715, -2), (key2818, 2), (key3047, -2), (key3066, 2), (key3072, -2), (key3096, -2), (key3103, -2), (key3110, 2)]

theorem rowCheck18299 : row18299 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18299 := by decide +kernel

theorem rowEval18299 (x : Key → ℝ) : Integer.Sparse.eval row18299 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck18299, Integer.Sparse.eval_collectBalanced, rawRowCheck18299]

def rawRow18300 : Integer.Sparse Key := [(key2715, -1), (key2715, -1), (key2689, -1), (key2689, -1), (key2682, -1), (key2682, -1), (key2710, 2), (key2679, 2), (key2679, 2), (key2818, 1), (key2818, 1), (key2689, 1), (key2689, 1), (key2682, 1), (key2682, 1), (key2813, -2), (key2679, -2), (key3047, -2), (key3136, -1), (key3136, -1), (key3110, -1), (key3110, -1), (key3103, -1), (key3103, -1), (key3134, 1), (key3134, 1), (key3072, 1), (key3072, 1), (key3066, 1), (key3066, 1), (key3136, 2), (key3110, 2), (key3110, 2), (key3134, -2), (key3072, -2), (key3072, -2)]

theorem rawRowCheck18300 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form15 = rawRow18300 := by decide +kernel

def row18300 : Integer.Sparse Key := [(key2679, 2), (key2710, 2), (key2715, -2), (key2813, -2), (key2818, 2), (key3047, -2), (key3066, 2), (key3072, -2), (key3103, -2), (key3110, 2)]

theorem rowCheck18300 : row18300 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18300 := by decide +kernel

theorem rowEval18300 (x : Key → ℝ) : Integer.Sparse.eval row18300 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck18300, Integer.Sparse.eval_collectBalanced, rawRowCheck18300]

def rawRow18301 : Integer.Sparse Key := [(key2813, -1), (key2818, -1), (key2813, -1), (key2900, -1), (key2818, -1), (key2900, -1), (key2818, 2), (key2818, 2), (key2900, 2), (key2710, 1), (key2715, 1), (key2710, 1), (key2979, 1), (key2715, 1), (key2979, 1), (key2715, -2), (key2715, -2), (key2979, -2), (key2679, -1), (key2689, -1), (key2679, -1), (key2742, -1), (key2689, -1), (key2742, -1), (key2679, 1), (key2689, 1), (key3047, 1), (key3110, 1), (key3054, 1), (key3110, 1), (key3050, 2), (key3050, 2), (key3066, 2), (key3050, -2), (key3050, -2), (key3103, -2)]

theorem rawRowCheck18301 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form15 = rawRow18301 := by decide +kernel

def row18301 : Integer.Sparse Key := [(key2679, -1), (key2689, -1), (key2710, 2), (key2715, -2), (key2742, -2), (key2813, -2), (key2818, 2), (key3047, 1), (key3054, 1), (key3066, 2), (key3103, -2), (key3110, 2)]

theorem rowCheck18301 : row18301 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18301 := by decide +kernel

theorem rowEval18301 (x : Key → ℝ) : Integer.Sparse.eval row18301 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form15) x := by
  rw [rowCheck18301, Integer.Sparse.eval_collectBalanced, rawRowCheck18301]

def rawRow18302 : Integer.Sparse Key := [(key2818, -1), (key2813, -1), (key2900, -1), (key2813, -1), (key2900, -1), (key2818, -1), (key2818, 2), (key2900, 2), (key2818, 2), (key2715, 1), (key2710, 1), (key2979, 1), (key2710, 1), (key2979, 1), (key2715, 1), (key2715, -2), (key2979, -2), (key2715, -2), (key2689, -1), (key2679, -1), (key2742, -1), (key2679, -1), (key2742, -1), (key2689, -1), (key2689, 1), (key2679, 1), (key3110, 1), (key3047, 1), (key3110, 1), (key3054, 1), (key3050, 2), (key3066, 2), (key3050, 2), (key3050, -2), (key3103, -2), (key3050, -2)]

theorem rawRowCheck18302 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form15 = rawRow18302 := by decide +kernel

def row18302 : Integer.Sparse Key := [(key2679, -1), (key2689, -1), (key2710, 2), (key2715, -2), (key2742, -2), (key2813, -2), (key2818, 2), (key3047, 1), (key3054, 1), (key3066, 2), (key3103, -2), (key3110, 2)]

theorem rowCheck18302 : row18302 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18302 := by decide +kernel

theorem rowEval18302 (x : Key → ℝ) : Integer.Sparse.eval row18302 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck18302, Integer.Sparse.eval_collectBalanced, rawRowCheck18302]

def rawRow18303 : Integer.Sparse Key := [(key2900, -1), (key2900, -1), (key2818, -1), (key2818, -1), (key2813, -1), (key2813, -1), (key2900, 2), (key2818, 2), (key2818, 2), (key2979, 1), (key2979, 1), (key2715, 1), (key2715, 1), (key2710, 1), (key2710, 1), (key2979, -2), (key2715, -2), (key2715, -2), (key2742, -1), (key2742, -1), (key2689, -1), (key2689, -1), (key2679, -1), (key2679, -1), (key2955, 1), (key2955, 1), (key2689, 1), (key2689, 1), (key2679, 1), (key3047, 1), (key3066, 2), (key3050, 2), (key3050, 2), (key3103, -2), (key3050, -2), (key3050, -2)]

theorem rawRowCheck18303 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form15 = rawRow18303 := by decide +kernel

def row18303 : Integer.Sparse Key := [(key2679, -1), (key2710, 2), (key2715, -2), (key2742, -2), (key2813, -2), (key2818, 2), (key2955, 2), (key3047, 1), (key3066, 2), (key3103, -2)]

theorem rowCheck18303 : row18303 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18303 := by decide +kernel

theorem rowEval18303 (x : Key → ℝ) : Integer.Sparse.eval row18303 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck18303, Integer.Sparse.eval_collectBalanced, rawRowCheck18303]

end MUB6.Certificate.GramRows

end OAI
