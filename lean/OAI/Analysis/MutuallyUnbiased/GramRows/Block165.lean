import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
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

def rawRow18048 : Integer.Sparse Key := [(key2549, -2), (key2549, -2), (key2549, -2), (key2547, 6), (key2493, -2), (key2493, -2), (key2493, -2), (key2425, 2), (key2425, 2), (key2425, 2), (key2425, 2), (key2425, 2), (key2425, 2), (key2418, -2), (key2418, -2), (key2418, -2), (key2488, 6), (key2415, -2), (key2415, -2), (key2415, -2)]

theorem rawRowCheck18048 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form2 = rawRow18048 := by decide +kernel

def row18048 : Integer.Sparse Key := [(key2415, -6), (key2418, -6), (key2425, 12), (key2488, 6), (key2493, -6), (key2547, 6), (key2549, -6)]

theorem rowCheck18048 : row18048 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18048 := by decide +kernel

theorem rowEval18048 (x : Key → ℝ) : Integer.Sparse.eval row18048 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18048, Integer.Sparse.eval_collectBalanced, rawRowCheck18048]

def rawRow18049 : Integer.Sparse Key := [(key3046, 6), (key3046, -2), (key3060, -2), (key3064, -2), (key3046, 6), (key3046, -2), (key3095, -2), (key3101, -2), (key3046, -2), (key3060, -2), (key3064, -2), (key3046, -2), (key3095, -2), (key3101, -2), (key3060, 2), (key3064, 2), (key3095, 2), (key3101, 2), (key3123, 2), (key3125, 2)]

theorem rawRowCheck18049 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form3 = rawRow18049 := by decide +kernel

def row18049 : Integer.Sparse Key := [(key3046, 4), (key3060, -2), (key3064, -2), (key3095, -2), (key3101, -2), (key3123, 2), (key3125, 2)]

theorem rowCheck18049 : row18049 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18049 := by decide +kernel

theorem rowEval18049 (x : Key → ℝ) : Integer.Sparse.eval row18049 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18049, Integer.Sparse.eval_collectBalanced, rawRowCheck18049]

def rawRow18050 : Integer.Sparse Key := [(key3046, 6), (key3046, -2), (key3064, -2), (key3060, -2), (key3046, 6), (key3046, -2), (key3101, -2), (key3095, -2), (key3046, -2), (key3064, -2), (key3060, -2), (key3046, -2), (key3101, -2), (key3095, -2), (key3064, 2), (key3060, 2), (key3101, 2), (key3095, 2), (key3125, 2), (key3123, 2)]

theorem rawRowCheck18050 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form3 = rawRow18050 := by decide +kernel

def row18050 : Integer.Sparse Key := [(key3046, 4), (key3060, -2), (key3064, -2), (key3095, -2), (key3101, -2), (key3123, 2), (key3125, 2)]

theorem rowCheck18050 : row18050 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18050 := by decide +kernel

theorem rowEval18050 (x : Key → ℝ) : Integer.Sparse.eval row18050 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck18050, Integer.Sparse.eval_collectBalanced, rawRowCheck18050]

def rawRow18051 : Integer.Sparse Key := [(key3046, 6), (key3060, -2), (key3046, -2), (key3064, -2), (key3046, 6), (key3095, -2), (key3046, -2), (key3101, -2), (key3060, -2), (key3046, -2), (key3064, -2), (key3095, -2), (key3046, -2), (key3101, -2), (key3095, 2), (key3123, 2), (key3060, 2), (key3125, 2), (key3064, 2), (key3101, 2)]

theorem rawRowCheck18051 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form3 = rawRow18051 := by decide +kernel

def row18051 : Integer.Sparse Key := [(key3046, 4), (key3060, -2), (key3064, -2), (key3095, -2), (key3101, -2), (key3123, 2), (key3125, 2)]

theorem rowCheck18051 : row18051 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18051 := by decide +kernel

theorem rowEval18051 (x : Key → ℝ) : Integer.Sparse.eval row18051 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18051, Integer.Sparse.eval_collectBalanced, rawRowCheck18051]

def rawRow18052 : Integer.Sparse Key := [(key3046, 6), (key3060, -2), (key3064, -2), (key3046, -2), (key3046, 6), (key3095, -2), (key3101, -2), (key3046, -2), (key3060, -2), (key3064, -2), (key3046, -2), (key3095, -2), (key3101, -2), (key3046, -2), (key3123, 2), (key3095, 2), (key3125, 2), (key3060, 2), (key3101, 2), (key3064, 2)]

theorem rawRowCheck18052 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form3 = rawRow18052 := by decide +kernel

def row18052 : Integer.Sparse Key := [(key3046, 4), (key3060, -2), (key3064, -2), (key3095, -2), (key3101, -2), (key3123, 2), (key3125, 2)]

theorem rowCheck18052 : row18052 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18052 := by decide +kernel

theorem rowEval18052 (x : Key → ℝ) : Integer.Sparse.eval row18052 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18052, Integer.Sparse.eval_collectBalanced, rawRowCheck18052]

def rawRow18053 : Integer.Sparse Key := [(key3046, 6), (key3064, -2), (key3046, -2), (key3060, -2), (key3046, 6), (key3101, -2), (key3046, -2), (key3095, -2), (key3064, -2), (key3046, -2), (key3060, -2), (key3101, -2), (key3046, -2), (key3095, -2), (key3101, 2), (key3125, 2), (key3064, 2), (key3123, 2), (key3060, 2), (key3095, 2)]

theorem rawRowCheck18053 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form3 = rawRow18053 := by decide +kernel

def row18053 : Integer.Sparse Key := [(key3046, 4), (key3060, -2), (key3064, -2), (key3095, -2), (key3101, -2), (key3123, 2), (key3125, 2)]

theorem rowCheck18053 : row18053 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18053 := by decide +kernel

theorem rowEval18053 (x : Key → ℝ) : Integer.Sparse.eval row18053 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck18053, Integer.Sparse.eval_collectBalanced, rawRowCheck18053]

def rawRow18054 : Integer.Sparse Key := [(key3046, 6), (key3064, -2), (key3060, -2), (key3046, -2), (key3046, 6), (key3101, -2), (key3095, -2), (key3046, -2), (key3064, -2), (key3060, -2), (key3046, -2), (key3101, -2), (key3095, -2), (key3046, -2), (key3125, 2), (key3101, 2), (key3123, 2), (key3064, 2), (key3095, 2), (key3060, 2)]

theorem rawRowCheck18054 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form3 = rawRow18054 := by decide +kernel

def row18054 : Integer.Sparse Key := [(key3046, 4), (key3060, -2), (key3064, -2), (key3095, -2), (key3101, -2), (key3123, 2), (key3125, 2)]

theorem rowCheck18054 : row18054 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18054 := by decide +kernel

theorem rowEval18054 (x : Key → ℝ) : Integer.Sparse.eval row18054 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18054, Integer.Sparse.eval_collectBalanced, rawRowCheck18054]

def rawRow18055 : Integer.Sparse Key := [(key3060, 6), (key3046, -2), (key3046, -2), (key3064, -2), (key3095, 6), (key3046, -2), (key3046, -2), (key3101, -2), (key3095, -2), (key3095, -2), (key3123, -2), (key3060, -2), (key3060, -2), (key3125, -2), (key3046, 2), (key3064, 2), (key3046, 2), (key3101, 2), (key3064, 2), (key3101, 2)]

theorem rawRowCheck18055 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form3 = rawRow18055 := by decide +kernel

def row18055 : Integer.Sparse Key := [(key3046, -4), (key3060, 2), (key3064, 2), (key3095, 2), (key3101, 2), (key3123, -2), (key3125, -2)]

theorem rowCheck18055 : row18055 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18055 := by decide +kernel

theorem rowEval18055 (x : Key → ℝ) : Integer.Sparse.eval row18055 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18055, Integer.Sparse.eval_collectBalanced, rawRowCheck18055]

def rawRow18056 : Integer.Sparse Key := [(key3060, 6), (key3046, -2), (key3064, -2), (key3046, -2), (key3095, 6), (key3046, -2), (key3101, -2), (key3046, -2), (key3095, -2), (key3123, -2), (key3095, -2), (key3060, -2), (key3125, -2), (key3060, -2), (key3064, 2), (key3046, 2), (key3101, 2), (key3046, 2), (key3101, 2), (key3064, 2)]

theorem rawRowCheck18056 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form3 = rawRow18056 := by decide +kernel

def row18056 : Integer.Sparse Key := [(key3046, -4), (key3060, 2), (key3064, 2), (key3095, 2), (key3101, 2), (key3123, -2), (key3125, -2)]

theorem rowCheck18056 : row18056 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18056 := by decide +kernel

theorem rowEval18056 (x : Key → ℝ) : Integer.Sparse.eval row18056 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18056, Integer.Sparse.eval_collectBalanced, rawRowCheck18056]

def rawRow18057 : Integer.Sparse Key := [(key3060, 6), (key3064, -2), (key3046, -2), (key3046, -2), (key3095, 6), (key3101, -2), (key3046, -2), (key3046, -2), (key3123, -2), (key3095, -2), (key3095, -2), (key3125, -2), (key3060, -2), (key3060, -2), (key3101, 2), (key3101, 2), (key3064, 2), (key3064, 2), (key3046, 2), (key3046, 2)]

theorem rawRowCheck18057 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form3 = rawRow18057 := by decide +kernel

def row18057 : Integer.Sparse Key := [(key3046, -4), (key3060, 2), (key3064, 2), (key3095, 2), (key3101, 2), (key3123, -2), (key3125, -2)]

theorem rowCheck18057 : row18057 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18057 := by decide +kernel

theorem rowEval18057 (x : Key → ℝ) : Integer.Sparse.eval row18057 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18057, Integer.Sparse.eval_collectBalanced, rawRowCheck18057]

def rawRow18058 : Integer.Sparse Key := [(key3064, 6), (key3046, -2), (key3046, -2), (key3060, -2), (key3101, 6), (key3046, -2), (key3046, -2), (key3095, -2), (key3101, -2), (key3101, -2), (key3125, -2), (key3064, -2), (key3064, -2), (key3123, -2), (key3046, 2), (key3060, 2), (key3046, 2), (key3095, 2), (key3060, 2), (key3095, 2)]

theorem rawRowCheck18058 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form3 = rawRow18058 := by decide +kernel

def row18058 : Integer.Sparse Key := [(key3046, -4), (key3060, 2), (key3064, 2), (key3095, 2), (key3101, 2), (key3123, -2), (key3125, -2)]

theorem rowCheck18058 : row18058 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18058 := by decide +kernel

theorem rowEval18058 (x : Key → ℝ) : Integer.Sparse.eval row18058 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck18058, Integer.Sparse.eval_collectBalanced, rawRowCheck18058]

def rawRow18059 : Integer.Sparse Key := [(key3064, 6), (key3046, -2), (key3060, -2), (key3046, -2), (key3101, 6), (key3046, -2), (key3095, -2), (key3046, -2), (key3101, -2), (key3125, -2), (key3101, -2), (key3064, -2), (key3123, -2), (key3064, -2), (key3060, 2), (key3046, 2), (key3095, 2), (key3046, 2), (key3095, 2), (key3060, 2)]

theorem rawRowCheck18059 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form3 = rawRow18059 := by decide +kernel

def row18059 : Integer.Sparse Key := [(key3046, -4), (key3060, 2), (key3064, 2), (key3095, 2), (key3101, 2), (key3123, -2), (key3125, -2)]

theorem rowCheck18059 : row18059 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18059 := by decide +kernel

theorem rowEval18059 (x : Key → ℝ) : Integer.Sparse.eval row18059 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18059, Integer.Sparse.eval_collectBalanced, rawRowCheck18059]

def rawRow18060 : Integer.Sparse Key := [(key3064, 6), (key3060, -2), (key3046, -2), (key3046, -2), (key3101, 6), (key3095, -2), (key3046, -2), (key3046, -2), (key3125, -2), (key3101, -2), (key3101, -2), (key3123, -2), (key3064, -2), (key3064, -2), (key3095, 2), (key3095, 2), (key3060, 2), (key3060, 2), (key3046, 2), (key3046, 2)]

theorem rawRowCheck18060 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form3 = rawRow18060 := by decide +kernel

def row18060 : Integer.Sparse Key := [(key3046, -4), (key3060, 2), (key3064, 2), (key3095, 2), (key3101, 2), (key3123, -2), (key3125, -2)]

theorem rowCheck18060 : row18060 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18060 := by decide +kernel

theorem rowEval18060 (x : Key → ℝ) : Integer.Sparse.eval row18060 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18060, Integer.Sparse.eval_collectBalanced, rawRowCheck18060]

def rawRow18061 : Integer.Sparse Key := [(key3095, 6), (key3095, -2), (key3095, -2), (key3123, -2), (key3060, 6), (key3060, -2), (key3060, -2), (key3125, -2), (key3046, -2), (key3046, -2), (key3064, -2), (key3046, -2), (key3046, -2), (key3101, -2), (key3046, 2), (key3064, 2), (key3046, 2), (key3101, 2), (key3064, 2), (key3101, 2)]

theorem rawRowCheck18061 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form3 = rawRow18061 := by decide +kernel

def row18061 : Integer.Sparse Key := [(key3046, -4), (key3060, 2), (key3064, 2), (key3095, 2), (key3101, 2), (key3123, -2), (key3125, -2)]

theorem rowCheck18061 : row18061 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18061 := by decide +kernel

theorem rowEval18061 (x : Key → ℝ) : Integer.Sparse.eval row18061 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18061, Integer.Sparse.eval_collectBalanced, rawRowCheck18061]

def rawRow18062 : Integer.Sparse Key := [(key3095, 6), (key3095, -2), (key3123, -2), (key3095, -2), (key3060, 6), (key3060, -2), (key3125, -2), (key3060, -2), (key3046, -2), (key3064, -2), (key3046, -2), (key3046, -2), (key3101, -2), (key3046, -2), (key3064, 2), (key3046, 2), (key3101, 2), (key3046, 2), (key3101, 2), (key3064, 2)]

theorem rawRowCheck18062 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form3 = rawRow18062 := by decide +kernel

def row18062 : Integer.Sparse Key := [(key3046, -4), (key3060, 2), (key3064, 2), (key3095, 2), (key3101, 2), (key3123, -2), (key3125, -2)]

theorem rowCheck18062 : row18062 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18062 := by decide +kernel

theorem rowEval18062 (x : Key → ℝ) : Integer.Sparse.eval row18062 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18062, Integer.Sparse.eval_collectBalanced, rawRowCheck18062]

def rawRow18063 : Integer.Sparse Key := [(key3095, 6), (key3123, -2), (key3095, -2), (key3095, -2), (key3060, 6), (key3125, -2), (key3060, -2), (key3060, -2), (key3064, -2), (key3046, -2), (key3046, -2), (key3101, -2), (key3046, -2), (key3046, -2), (key3101, 2), (key3101, 2), (key3064, 2), (key3064, 2), (key3046, 2), (key3046, 2)]

theorem rawRowCheck18063 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form3 = rawRow18063 := by decide +kernel

def row18063 : Integer.Sparse Key := [(key3046, -4), (key3060, 2), (key3064, 2), (key3095, 2), (key3101, 2), (key3123, -2), (key3125, -2)]

theorem rowCheck18063 : row18063 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18063 := by decide +kernel

theorem rowEval18063 (x : Key → ℝ) : Integer.Sparse.eval row18063 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18063, Integer.Sparse.eval_collectBalanced, rawRowCheck18063]

def rawRow18064 : Integer.Sparse Key := [(key3123, 6), (key3095, -2), (key3095, -2), (key3095, -2), (key3125, 6), (key3060, -2), (key3060, -2), (key3060, -2), (key3101, -2), (key3101, -2), (key3101, -2), (key3064, -2), (key3064, -2), (key3064, -2), (key3046, 2), (key3046, 2), (key3046, 2), (key3046, 2), (key3046, 2), (key3046, 2)]

theorem rawRowCheck18064 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form3 = rawRow18064 := by decide +kernel

def row18064 : Integer.Sparse Key := [(key3046, 12), (key3060, -6), (key3064, -6), (key3095, -6), (key3101, -6), (key3123, 6), (key3125, 6)]

theorem rowCheck18064 : row18064 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18064 := by decide +kernel

theorem rowEval18064 (x : Key → ℝ) : Integer.Sparse.eval row18064 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18064, Integer.Sparse.eval_collectBalanced, rawRowCheck18064]

def rawRow18065 : Integer.Sparse Key := [(key3101, 6), (key3101, -2), (key3101, -2), (key3125, -2), (key3064, 6), (key3064, -2), (key3064, -2), (key3123, -2), (key3046, -2), (key3046, -2), (key3060, -2), (key3046, -2), (key3046, -2), (key3095, -2), (key3046, 2), (key3060, 2), (key3046, 2), (key3095, 2), (key3060, 2), (key3095, 2)]

theorem rawRowCheck18065 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form3 = rawRow18065 := by decide +kernel

def row18065 : Integer.Sparse Key := [(key3046, -4), (key3060, 2), (key3064, 2), (key3095, 2), (key3101, 2), (key3123, -2), (key3125, -2)]

theorem rowCheck18065 : row18065 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18065 := by decide +kernel

theorem rowEval18065 (x : Key → ℝ) : Integer.Sparse.eval row18065 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck18065, Integer.Sparse.eval_collectBalanced, rawRowCheck18065]

def rawRow18066 : Integer.Sparse Key := [(key3101, 6), (key3101, -2), (key3125, -2), (key3101, -2), (key3064, 6), (key3064, -2), (key3123, -2), (key3064, -2), (key3046, -2), (key3060, -2), (key3046, -2), (key3046, -2), (key3095, -2), (key3046, -2), (key3060, 2), (key3046, 2), (key3095, 2), (key3046, 2), (key3095, 2), (key3060, 2)]

theorem rawRowCheck18066 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form3 = rawRow18066 := by decide +kernel

def row18066 : Integer.Sparse Key := [(key3046, -4), (key3060, 2), (key3064, 2), (key3095, 2), (key3101, 2), (key3123, -2), (key3125, -2)]

theorem rowCheck18066 : row18066 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18066 := by decide +kernel

theorem rowEval18066 (x : Key → ℝ) : Integer.Sparse.eval row18066 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18066, Integer.Sparse.eval_collectBalanced, rawRowCheck18066]

def rawRow18067 : Integer.Sparse Key := [(key3101, 6), (key3125, -2), (key3101, -2), (key3101, -2), (key3064, 6), (key3123, -2), (key3064, -2), (key3064, -2), (key3060, -2), (key3046, -2), (key3046, -2), (key3095, -2), (key3046, -2), (key3046, -2), (key3095, 2), (key3095, 2), (key3060, 2), (key3060, 2), (key3046, 2), (key3046, 2)]

theorem rawRowCheck18067 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form3 = rawRow18067 := by decide +kernel

def row18067 : Integer.Sparse Key := [(key3046, -4), (key3060, 2), (key3064, 2), (key3095, 2), (key3101, 2), (key3123, -2), (key3125, -2)]

theorem rowCheck18067 : row18067 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18067 := by decide +kernel

theorem rowEval18067 (x : Key → ℝ) : Integer.Sparse.eval row18067 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18067, Integer.Sparse.eval_collectBalanced, rawRowCheck18067]

def rawRow18068 : Integer.Sparse Key := [(key3125, 6), (key3101, -2), (key3101, -2), (key3101, -2), (key3123, 6), (key3064, -2), (key3064, -2), (key3064, -2), (key3095, -2), (key3095, -2), (key3095, -2), (key3060, -2), (key3060, -2), (key3060, -2), (key3046, 2), (key3046, 2), (key3046, 2), (key3046, 2), (key3046, 2), (key3046, 2)]

theorem rawRowCheck18068 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form3 = rawRow18068 := by decide +kernel

def row18068 : Integer.Sparse Key := [(key3046, 12), (key3060, -6), (key3064, -6), (key3095, -6), (key3101, -6), (key3123, 6), (key3125, 6)]

theorem rowCheck18068 : row18068 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18068 := by decide +kernel

theorem rowEval18068 (x : Key → ℝ) : Integer.Sparse.eval row18068 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18068, Integer.Sparse.eval_collectBalanced, rawRowCheck18068]

def rawRow18069 : Integer.Sparse Key := [(key1048, -2), (key1051, -2), (key1059, -2), (key1059, 6), (key1048, -2), (key1051, -2), (key1059, -2), (key1048, 2), (key1051, 2), (key1134, 2), (key1204, 2), (key1139, 2), (key1206, 2), (key1059, -2), (key1139, -2), (key1206, -2), (key1059, 6), (key1059, -2), (key1139, -2), (key1206, -2)]

theorem rawRowCheck18069 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form4 = rawRow18069 := by decide +kernel

def row18069 : Integer.Sparse Key := [(key1048, -2), (key1051, -2), (key1059, 4), (key1134, 2), (key1139, -2), (key1204, 2), (key1206, -2)]

theorem rowCheck18069 : row18069 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18069 := by decide +kernel

theorem rowEval18069 (x : Key → ℝ) : Integer.Sparse.eval row18069 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18069, Integer.Sparse.eval_collectBalanced, rawRowCheck18069]

def rawRow18070 : Integer.Sparse Key := [(key1051, -2), (key1048, -2), (key1059, -2), (key1059, 6), (key1051, -2), (key1048, -2), (key1059, -2), (key1051, 2), (key1048, 2), (key1204, 2), (key1134, 2), (key1206, 2), (key1139, 2), (key1059, -2), (key1206, -2), (key1139, -2), (key1059, 6), (key1059, -2), (key1206, -2), (key1139, -2)]

theorem rawRowCheck18070 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form4 = rawRow18070 := by decide +kernel

def row18070 : Integer.Sparse Key := [(key1048, -2), (key1051, -2), (key1059, 4), (key1134, 2), (key1139, -2), (key1204, 2), (key1206, -2)]

theorem rowCheck18070 : row18070 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18070 := by decide +kernel

theorem rowEval18070 (x : Key → ℝ) : Integer.Sparse.eval row18070 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck18070, Integer.Sparse.eval_collectBalanced, rawRowCheck18070]

def rawRow18071 : Integer.Sparse Key := [(key1048, -2), (key1059, -2), (key1051, -2), (key1059, 6), (key1048, -2), (key1059, -2), (key1051, -2), (key1134, 2), (key1139, 2), (key1048, 2), (key1206, 2), (key1051, 2), (key1204, 2), (key1139, -2), (key1059, -2), (key1206, -2), (key1059, 6), (key1139, -2), (key1059, -2), (key1206, -2)]

theorem rawRowCheck18071 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form4 = rawRow18071 := by decide +kernel

def row18071 : Integer.Sparse Key := [(key1048, -2), (key1051, -2), (key1059, 4), (key1134, 2), (key1139, -2), (key1204, 2), (key1206, -2)]

theorem rowCheck18071 : row18071 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18071 := by decide +kernel

theorem rowEval18071 (x : Key → ℝ) : Integer.Sparse.eval row18071 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18071, Integer.Sparse.eval_collectBalanced, rawRowCheck18071]

def rawRow18072 : Integer.Sparse Key := [(key1059, -2), (key1048, -2), (key1051, -2), (key1059, 6), (key1059, -2), (key1048, -2), (key1051, -2), (key1139, 2), (key1134, 2), (key1206, 2), (key1048, 2), (key1204, 2), (key1051, 2), (key1139, -2), (key1206, -2), (key1059, -2), (key1059, 6), (key1139, -2), (key1206, -2), (key1059, -2)]

theorem rawRowCheck18072 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form4 = rawRow18072 := by decide +kernel

def row18072 : Integer.Sparse Key := [(key1048, -2), (key1051, -2), (key1059, 4), (key1134, 2), (key1139, -2), (key1204, 2), (key1206, -2)]

theorem rowCheck18072 : row18072 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18072 := by decide +kernel

theorem rowEval18072 (x : Key → ℝ) : Integer.Sparse.eval row18072 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18072, Integer.Sparse.eval_collectBalanced, rawRowCheck18072]

def rawRow18073 : Integer.Sparse Key := [(key1051, -2), (key1059, -2), (key1048, -2), (key1059, 6), (key1051, -2), (key1059, -2), (key1048, -2), (key1204, 2), (key1206, 2), (key1051, 2), (key1139, 2), (key1048, 2), (key1134, 2), (key1206, -2), (key1059, -2), (key1139, -2), (key1059, 6), (key1206, -2), (key1059, -2), (key1139, -2)]

theorem rawRowCheck18073 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form4 = rawRow18073 := by decide +kernel

def row18073 : Integer.Sparse Key := [(key1048, -2), (key1051, -2), (key1059, 4), (key1134, 2), (key1139, -2), (key1204, 2), (key1206, -2)]

theorem rowCheck18073 : row18073 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18073 := by decide +kernel

theorem rowEval18073 (x : Key → ℝ) : Integer.Sparse.eval row18073 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck18073, Integer.Sparse.eval_collectBalanced, rawRowCheck18073]

def rawRow18074 : Integer.Sparse Key := [(key1059, -2), (key1051, -2), (key1048, -2), (key1059, 6), (key1059, -2), (key1051, -2), (key1048, -2), (key1206, 2), (key1204, 2), (key1139, 2), (key1051, 2), (key1134, 2), (key1048, 2), (key1206, -2), (key1139, -2), (key1059, -2), (key1059, 6), (key1206, -2), (key1139, -2), (key1059, -2)]

theorem rawRowCheck18074 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form4 = rawRow18074 := by decide +kernel

def row18074 : Integer.Sparse Key := [(key1048, -2), (key1051, -2), (key1059, 4), (key1134, 2), (key1139, -2), (key1204, 2), (key1206, -2)]

theorem rowCheck18074 : row18074 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18074 := by decide +kernel

theorem rowEval18074 (x : Key → ℝ) : Integer.Sparse.eval row18074 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18074, Integer.Sparse.eval_collectBalanced, rawRowCheck18074]

def rawRow18075 : Integer.Sparse Key := [(key1048, -2), (key1059, -2), (key1059, -2), (key1051, 6), (key1134, -2), (key1139, -2), (key1139, -2), (key1048, 2), (key1059, 2), (key1048, 2), (key1206, 2), (key1059, 2), (key1206, 2), (key1051, -2), (key1051, -2), (key1204, -2), (key1139, 6), (key1059, -2), (key1059, -2), (key1206, -2)]

theorem rawRowCheck18075 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form4 = rawRow18075 := by decide +kernel

def row18075 : Integer.Sparse Key := [(key1048, 2), (key1051, 2), (key1059, -4), (key1134, -2), (key1139, 2), (key1204, -2), (key1206, 2)]

theorem rowCheck18075 : row18075 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18075 := by decide +kernel

theorem rowEval18075 (x : Key → ℝ) : Integer.Sparse.eval row18075 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18075, Integer.Sparse.eval_collectBalanced, rawRowCheck18075]

def rawRow18076 : Integer.Sparse Key := [(key1059, -2), (key1048, -2), (key1059, -2), (key1051, 6), (key1139, -2), (key1134, -2), (key1139, -2), (key1059, 2), (key1048, 2), (key1206, 2), (key1048, 2), (key1206, 2), (key1059, 2), (key1051, -2), (key1204, -2), (key1051, -2), (key1139, 6), (key1059, -2), (key1206, -2), (key1059, -2)]

theorem rawRowCheck18076 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form4 = rawRow18076 := by decide +kernel

def row18076 : Integer.Sparse Key := [(key1048, 2), (key1051, 2), (key1059, -4), (key1134, -2), (key1139, 2), (key1204, -2), (key1206, 2)]

theorem rowCheck18076 : row18076 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18076 := by decide +kernel

theorem rowEval18076 (x : Key → ℝ) : Integer.Sparse.eval row18076 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18076, Integer.Sparse.eval_collectBalanced, rawRowCheck18076]

def rawRow18077 : Integer.Sparse Key := [(key1059, -2), (key1059, -2), (key1048, -2), (key1051, 6), (key1139, -2), (key1139, -2), (key1134, -2), (key1206, 2), (key1206, 2), (key1059, 2), (key1059, 2), (key1048, 2), (key1048, 2), (key1204, -2), (key1051, -2), (key1051, -2), (key1139, 6), (key1206, -2), (key1059, -2), (key1059, -2)]

theorem rawRowCheck18077 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form4 = rawRow18077 := by decide +kernel

def row18077 : Integer.Sparse Key := [(key1048, 2), (key1051, 2), (key1059, -4), (key1134, -2), (key1139, 2), (key1204, -2), (key1206, 2)]

theorem rowCheck18077 : row18077 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18077 := by decide +kernel

theorem rowEval18077 (x : Key → ℝ) : Integer.Sparse.eval row18077 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18077, Integer.Sparse.eval_collectBalanced, rawRowCheck18077]

def rawRow18078 : Integer.Sparse Key := [(key1051, -2), (key1059, -2), (key1059, -2), (key1048, 6), (key1204, -2), (key1206, -2), (key1206, -2), (key1051, 2), (key1059, 2), (key1051, 2), (key1139, 2), (key1059, 2), (key1139, 2), (key1048, -2), (key1048, -2), (key1134, -2), (key1206, 6), (key1059, -2), (key1059, -2), (key1139, -2)]

theorem rawRowCheck18078 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form4 = rawRow18078 := by decide +kernel

def row18078 : Integer.Sparse Key := [(key1048, 2), (key1051, 2), (key1059, -4), (key1134, -2), (key1139, 2), (key1204, -2), (key1206, 2)]

theorem rowCheck18078 : row18078 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18078 := by decide +kernel

theorem rowEval18078 (x : Key → ℝ) : Integer.Sparse.eval row18078 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck18078, Integer.Sparse.eval_collectBalanced, rawRowCheck18078]

def rawRow18079 : Integer.Sparse Key := [(key1059, -2), (key1051, -2), (key1059, -2), (key1048, 6), (key1206, -2), (key1204, -2), (key1206, -2), (key1059, 2), (key1051, 2), (key1139, 2), (key1051, 2), (key1139, 2), (key1059, 2), (key1048, -2), (key1134, -2), (key1048, -2), (key1206, 6), (key1059, -2), (key1139, -2), (key1059, -2)]

theorem rawRowCheck18079 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form4 = rawRow18079 := by decide +kernel

def row18079 : Integer.Sparse Key := [(key1048, 2), (key1051, 2), (key1059, -4), (key1134, -2), (key1139, 2), (key1204, -2), (key1206, 2)]

theorem rowCheck18079 : row18079 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18079 := by decide +kernel

theorem rowEval18079 (x : Key → ℝ) : Integer.Sparse.eval row18079 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18079, Integer.Sparse.eval_collectBalanced, rawRowCheck18079]

def rawRow18080 : Integer.Sparse Key := [(key1059, -2), (key1059, -2), (key1051, -2), (key1048, 6), (key1206, -2), (key1206, -2), (key1204, -2), (key1139, 2), (key1139, 2), (key1059, 2), (key1059, 2), (key1051, 2), (key1051, 2), (key1134, -2), (key1048, -2), (key1048, -2), (key1206, 6), (key1139, -2), (key1059, -2), (key1059, -2)]

theorem rawRowCheck18080 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form4 = rawRow18080 := by decide +kernel

def row18080 : Integer.Sparse Key := [(key1048, 2), (key1051, 2), (key1059, -4), (key1134, -2), (key1139, 2), (key1204, -2), (key1206, 2)]

theorem rowCheck18080 : row18080 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18080 := by decide +kernel

theorem rowEval18080 (x : Key → ℝ) : Integer.Sparse.eval row18080 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18080, Integer.Sparse.eval_collectBalanced, rawRowCheck18080]

def rawRow18081 : Integer.Sparse Key := [(key1134, -2), (key1139, -2), (key1139, -2), (key1139, 6), (key1048, -2), (key1059, -2), (key1059, -2), (key1048, 2), (key1059, 2), (key1048, 2), (key1206, 2), (key1059, 2), (key1206, 2), (key1059, -2), (key1059, -2), (key1206, -2), (key1051, 6), (key1051, -2), (key1051, -2), (key1204, -2)]

theorem rawRowCheck18081 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form4 = rawRow18081 := by decide +kernel

def row18081 : Integer.Sparse Key := [(key1048, 2), (key1051, 2), (key1059, -4), (key1134, -2), (key1139, 2), (key1204, -2), (key1206, 2)]

theorem rowCheck18081 : row18081 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18081 := by decide +kernel

theorem rowEval18081 (x : Key → ℝ) : Integer.Sparse.eval row18081 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18081, Integer.Sparse.eval_collectBalanced, rawRowCheck18081]

def rawRow18082 : Integer.Sparse Key := [(key1139, -2), (key1134, -2), (key1139, -2), (key1139, 6), (key1059, -2), (key1048, -2), (key1059, -2), (key1059, 2), (key1048, 2), (key1206, 2), (key1048, 2), (key1206, 2), (key1059, 2), (key1059, -2), (key1206, -2), (key1059, -2), (key1051, 6), (key1051, -2), (key1204, -2), (key1051, -2)]

theorem rawRowCheck18082 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form4 = rawRow18082 := by decide +kernel

def row18082 : Integer.Sparse Key := [(key1048, 2), (key1051, 2), (key1059, -4), (key1134, -2), (key1139, 2), (key1204, -2), (key1206, 2)]

theorem rowCheck18082 : row18082 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18082 := by decide +kernel

theorem rowEval18082 (x : Key → ℝ) : Integer.Sparse.eval row18082 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18082, Integer.Sparse.eval_collectBalanced, rawRowCheck18082]

def rawRow18083 : Integer.Sparse Key := [(key1139, -2), (key1139, -2), (key1134, -2), (key1139, 6), (key1059, -2), (key1059, -2), (key1048, -2), (key1206, 2), (key1206, 2), (key1059, 2), (key1059, 2), (key1048, 2), (key1048, 2), (key1206, -2), (key1059, -2), (key1059, -2), (key1051, 6), (key1204, -2), (key1051, -2), (key1051, -2)]

theorem rawRowCheck18083 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form4 = rawRow18083 := by decide +kernel

def row18083 : Integer.Sparse Key := [(key1048, 2), (key1051, 2), (key1059, -4), (key1134, -2), (key1139, 2), (key1204, -2), (key1206, 2)]

theorem rowCheck18083 : row18083 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18083 := by decide +kernel

theorem rowEval18083 (x : Key → ℝ) : Integer.Sparse.eval row18083 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18083, Integer.Sparse.eval_collectBalanced, rawRowCheck18083]

def rawRow18084 : Integer.Sparse Key := [(key1139, -2), (key1139, -2), (key1139, -2), (key1134, 6), (key1206, -2), (key1206, -2), (key1206, -2), (key1059, 2), (key1059, 2), (key1059, 2), (key1059, 2), (key1059, 2), (key1059, 2), (key1048, -2), (key1048, -2), (key1048, -2), (key1204, 6), (key1051, -2), (key1051, -2), (key1051, -2)]

theorem rawRowCheck18084 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form4 = rawRow18084 := by decide +kernel

def row18084 : Integer.Sparse Key := [(key1048, -6), (key1051, -6), (key1059, 12), (key1134, 6), (key1139, -6), (key1204, 6), (key1206, -6)]

theorem rowCheck18084 : row18084 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18084 := by decide +kernel

theorem rowEval18084 (x : Key → ℝ) : Integer.Sparse.eval row18084 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18084, Integer.Sparse.eval_collectBalanced, rawRowCheck18084]

def rawRow18085 : Integer.Sparse Key := [(key1204, -2), (key1206, -2), (key1206, -2), (key1206, 6), (key1051, -2), (key1059, -2), (key1059, -2), (key1051, 2), (key1059, 2), (key1051, 2), (key1139, 2), (key1059, 2), (key1139, 2), (key1059, -2), (key1059, -2), (key1139, -2), (key1048, 6), (key1048, -2), (key1048, -2), (key1134, -2)]

theorem rawRowCheck18085 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form4 = rawRow18085 := by decide +kernel

def row18085 : Integer.Sparse Key := [(key1048, 2), (key1051, 2), (key1059, -4), (key1134, -2), (key1139, 2), (key1204, -2), (key1206, 2)]

theorem rowCheck18085 : row18085 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18085 := by decide +kernel

theorem rowEval18085 (x : Key → ℝ) : Integer.Sparse.eval row18085 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck18085, Integer.Sparse.eval_collectBalanced, rawRowCheck18085]

def rawRow18086 : Integer.Sparse Key := [(key1206, -2), (key1204, -2), (key1206, -2), (key1206, 6), (key1059, -2), (key1051, -2), (key1059, -2), (key1059, 2), (key1051, 2), (key1139, 2), (key1051, 2), (key1139, 2), (key1059, 2), (key1059, -2), (key1139, -2), (key1059, -2), (key1048, 6), (key1048, -2), (key1134, -2), (key1048, -2)]

theorem rawRowCheck18086 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form4 = rawRow18086 := by decide +kernel

def row18086 : Integer.Sparse Key := [(key1048, 2), (key1051, 2), (key1059, -4), (key1134, -2), (key1139, 2), (key1204, -2), (key1206, 2)]

theorem rowCheck18086 : row18086 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18086 := by decide +kernel

theorem rowEval18086 (x : Key → ℝ) : Integer.Sparse.eval row18086 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18086, Integer.Sparse.eval_collectBalanced, rawRowCheck18086]

def rawRow18087 : Integer.Sparse Key := [(key1206, -2), (key1206, -2), (key1204, -2), (key1206, 6), (key1059, -2), (key1059, -2), (key1051, -2), (key1139, 2), (key1139, 2), (key1059, 2), (key1059, 2), (key1051, 2), (key1051, 2), (key1139, -2), (key1059, -2), (key1059, -2), (key1048, 6), (key1134, -2), (key1048, -2), (key1048, -2)]

theorem rawRowCheck18087 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form4 = rawRow18087 := by decide +kernel

def row18087 : Integer.Sparse Key := [(key1048, 2), (key1051, 2), (key1059, -4), (key1134, -2), (key1139, 2), (key1204, -2), (key1206, 2)]

theorem rowCheck18087 : row18087 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18087 := by decide +kernel

theorem rowEval18087 (x : Key → ℝ) : Integer.Sparse.eval row18087 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18087, Integer.Sparse.eval_collectBalanced, rawRowCheck18087]

def rawRow18088 : Integer.Sparse Key := [(key1206, -2), (key1206, -2), (key1206, -2), (key1204, 6), (key1139, -2), (key1139, -2), (key1139, -2), (key1059, 2), (key1059, 2), (key1059, 2), (key1059, 2), (key1059, 2), (key1059, 2), (key1051, -2), (key1051, -2), (key1051, -2), (key1134, 6), (key1048, -2), (key1048, -2), (key1048, -2)]

theorem rawRowCheck18088 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form4 = rawRow18088 := by decide +kernel

def row18088 : Integer.Sparse Key := [(key1048, -6), (key1051, -6), (key1059, 12), (key1134, 6), (key1139, -6), (key1204, 6), (key1206, -6)]

theorem rowCheck18088 : row18088 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18088 := by decide +kernel

theorem rowEval18088 (x : Key → ℝ) : Integer.Sparse.eval row18088 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18088, Integer.Sparse.eval_collectBalanced, rawRowCheck18088]

def rawRow18089 : Integer.Sparse Key := [(key1056, 4), (key1144, 4), (key1208, 4), (key1064, -2), (key1065, -2), (key1144, -2), (key1208, -2), (key1158, -2), (key1215, -2), (key1064, -2), (key1065, -2), (key1144, -2), (key1208, -2), (key1158, -2), (key1215, -2), (key1079, 4), (key1158, 4), (key1215, 4)]

theorem rawRowCheck18089 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form5 = rawRow18089 := by decide +kernel

def row18089 : Integer.Sparse Key := [(key1056, 4), (key1064, -4), (key1065, -4), (key1079, 4)]

theorem rowCheck18089 : row18089 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18089 := by decide +kernel

theorem rowEval18089 (x : Key → ℝ) : Integer.Sparse.eval row18089 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18089, Integer.Sparse.eval_collectBalanced, rawRowCheck18089]

def rawRow18090 : Integer.Sparse Key := [(key1056, 4), (key1208, 4), (key1144, 4), (key1065, -2), (key1064, -2), (key1208, -2), (key1144, -2), (key1215, -2), (key1158, -2), (key1065, -2), (key1064, -2), (key1208, -2), (key1144, -2), (key1215, -2), (key1158, -2), (key1079, 4), (key1215, 4), (key1158, 4)]

theorem rawRowCheck18090 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form5 = rawRow18090 := by decide +kernel

def row18090 : Integer.Sparse Key := [(key1056, 4), (key1064, -4), (key1065, -4), (key1079, 4)]

theorem rowCheck18090 : row18090 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18090 := by decide +kernel

theorem rowEval18090 (x : Key → ℝ) : Integer.Sparse.eval row18090 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck18090, Integer.Sparse.eval_collectBalanced, rawRowCheck18090]

def rawRow18091 : Integer.Sparse Key := [(key1144, 4), (key1056, 4), (key1208, 4), (key1144, -2), (key1158, -2), (key1064, -2), (key1215, -2), (key1065, -2), (key1208, -2), (key1144, -2), (key1158, -2), (key1064, -2), (key1215, -2), (key1065, -2), (key1208, -2), (key1158, 4), (key1079, 4), (key1215, 4)]

theorem rawRowCheck18091 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form5 = rawRow18091 := by decide +kernel

def row18091 : Integer.Sparse Key := [(key1056, 4), (key1064, -4), (key1065, -4), (key1079, 4)]

theorem rowCheck18091 : row18091 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18091 := by decide +kernel

theorem rowEval18091 (x : Key → ℝ) : Integer.Sparse.eval row18091 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18091, Integer.Sparse.eval_collectBalanced, rawRowCheck18091]

def rawRow18092 : Integer.Sparse Key := [(key1144, 4), (key1208, 4), (key1056, 4), (key1158, -2), (key1144, -2), (key1215, -2), (key1064, -2), (key1208, -2), (key1065, -2), (key1158, -2), (key1144, -2), (key1215, -2), (key1064, -2), (key1208, -2), (key1065, -2), (key1158, 4), (key1215, 4), (key1079, 4)]

theorem rawRowCheck18092 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form5 = rawRow18092 := by decide +kernel

def row18092 : Integer.Sparse Key := [(key1056, 4), (key1064, -4), (key1065, -4), (key1079, 4)]

theorem rowCheck18092 : row18092 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18092 := by decide +kernel

theorem rowEval18092 (x : Key → ℝ) : Integer.Sparse.eval row18092 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18092, Integer.Sparse.eval_collectBalanced, rawRowCheck18092]

def rawRow18093 : Integer.Sparse Key := [(key1208, 4), (key1056, 4), (key1144, 4), (key1208, -2), (key1215, -2), (key1065, -2), (key1158, -2), (key1064, -2), (key1144, -2), (key1208, -2), (key1215, -2), (key1065, -2), (key1158, -2), (key1064, -2), (key1144, -2), (key1215, 4), (key1079, 4), (key1158, 4)]

theorem rawRowCheck18093 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form5 = rawRow18093 := by decide +kernel

def row18093 : Integer.Sparse Key := [(key1056, 4), (key1064, -4), (key1065, -4), (key1079, 4)]

theorem rowCheck18093 : row18093 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18093 := by decide +kernel

theorem rowEval18093 (x : Key → ℝ) : Integer.Sparse.eval row18093 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck18093, Integer.Sparse.eval_collectBalanced, rawRowCheck18093]

def rawRow18094 : Integer.Sparse Key := [(key1208, 4), (key1144, 4), (key1056, 4), (key1215, -2), (key1208, -2), (key1158, -2), (key1065, -2), (key1144, -2), (key1064, -2), (key1215, -2), (key1208, -2), (key1158, -2), (key1065, -2), (key1144, -2), (key1064, -2), (key1215, 4), (key1158, 4), (key1079, 4)]

theorem rawRowCheck18094 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form5 = rawRow18094 := by decide +kernel

def row18094 : Integer.Sparse Key := [(key1056, 4), (key1064, -4), (key1065, -4), (key1079, 4)]

theorem rowCheck18094 : row18094 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18094 := by decide +kernel

theorem rowEval18094 (x : Key → ℝ) : Integer.Sparse.eval row18094 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18094, Integer.Sparse.eval_collectBalanced, rawRowCheck18094]

def rawRow18095 : Integer.Sparse Key := [(key1064, 4), (key1064, 4), (key1215, 4), (key1056, -2), (key1065, -2), (key1056, -2), (key1208, -2), (key1065, -2), (key1208, -2), (key1064, -2), (key1079, -2), (key1064, -2), (key1215, -2), (key1079, -2), (key1215, -2), (key1065, 4), (key1065, 4), (key1208, 4)]

theorem rawRowCheck18095 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form5 = rawRow18095 := by decide +kernel

def row18095 : Integer.Sparse Key := [(key1056, -4), (key1064, 4), (key1065, 4), (key1079, -4)]

theorem rowCheck18095 : row18095 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18095 := by decide +kernel

theorem rowEval18095 (x : Key → ℝ) : Integer.Sparse.eval row18095 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18095, Integer.Sparse.eval_collectBalanced, rawRowCheck18095]

def rawRow18096 : Integer.Sparse Key := [(key1064, 4), (key1215, 4), (key1064, 4), (key1065, -2), (key1056, -2), (key1208, -2), (key1056, -2), (key1208, -2), (key1065, -2), (key1079, -2), (key1064, -2), (key1215, -2), (key1064, -2), (key1215, -2), (key1079, -2), (key1065, 4), (key1208, 4), (key1065, 4)]

theorem rawRowCheck18096 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form5 = rawRow18096 := by decide +kernel

def row18096 : Integer.Sparse Key := [(key1056, -4), (key1064, 4), (key1065, 4), (key1079, -4)]

theorem rowCheck18096 : row18096 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18096 := by decide +kernel

theorem rowEval18096 (x : Key → ℝ) : Integer.Sparse.eval row18096 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18096, Integer.Sparse.eval_collectBalanced, rawRowCheck18096]

def rawRow18097 : Integer.Sparse Key := [(key1215, 4), (key1064, 4), (key1064, 4), (key1208, -2), (key1208, -2), (key1065, -2), (key1065, -2), (key1056, -2), (key1056, -2), (key1215, -2), (key1215, -2), (key1079, -2), (key1079, -2), (key1064, -2), (key1064, -2), (key1208, 4), (key1065, 4), (key1065, 4)]

theorem rawRowCheck18097 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form5 = rawRow18097 := by decide +kernel

def row18097 : Integer.Sparse Key := [(key1056, -4), (key1064, 4), (key1065, 4), (key1079, -4)]

theorem rowCheck18097 : row18097 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18097 := by decide +kernel

theorem rowEval18097 (x : Key → ℝ) : Integer.Sparse.eval row18097 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18097, Integer.Sparse.eval_collectBalanced, rawRowCheck18097]

def rawRow18098 : Integer.Sparse Key := [(key1065, 4), (key1065, 4), (key1158, 4), (key1056, -2), (key1064, -2), (key1056, -2), (key1144, -2), (key1064, -2), (key1144, -2), (key1065, -2), (key1079, -2), (key1065, -2), (key1158, -2), (key1079, -2), (key1158, -2), (key1064, 4), (key1064, 4), (key1144, 4)]

theorem rawRowCheck18098 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form5 = rawRow18098 := by decide +kernel

def row18098 : Integer.Sparse Key := [(key1056, -4), (key1064, 4), (key1065, 4), (key1079, -4)]

theorem rowCheck18098 : row18098 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18098 := by decide +kernel

theorem rowEval18098 (x : Key → ℝ) : Integer.Sparse.eval row18098 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck18098, Integer.Sparse.eval_collectBalanced, rawRowCheck18098]

def rawRow18099 : Integer.Sparse Key := [(key1065, 4), (key1158, 4), (key1065, 4), (key1064, -2), (key1056, -2), (key1144, -2), (key1056, -2), (key1144, -2), (key1064, -2), (key1079, -2), (key1065, -2), (key1158, -2), (key1065, -2), (key1158, -2), (key1079, -2), (key1064, 4), (key1144, 4), (key1064, 4)]

theorem rawRowCheck18099 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form5 = rawRow18099 := by decide +kernel

def row18099 : Integer.Sparse Key := [(key1056, -4), (key1064, 4), (key1065, 4), (key1079, -4)]

theorem rowCheck18099 : row18099 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18099 := by decide +kernel

theorem rowEval18099 (x : Key → ℝ) : Integer.Sparse.eval row18099 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18099, Integer.Sparse.eval_collectBalanced, rawRowCheck18099]

def rawRow18100 : Integer.Sparse Key := [(key1158, 4), (key1065, 4), (key1065, 4), (key1144, -2), (key1144, -2), (key1064, -2), (key1064, -2), (key1056, -2), (key1056, -2), (key1158, -2), (key1158, -2), (key1079, -2), (key1079, -2), (key1065, -2), (key1065, -2), (key1144, 4), (key1064, 4), (key1064, 4)]

theorem rawRowCheck18100 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form5 = rawRow18100 := by decide +kernel

def row18100 : Integer.Sparse Key := [(key1056, -4), (key1064, 4), (key1065, 4), (key1079, -4)]

theorem rowCheck18100 : row18100 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18100 := by decide +kernel

theorem rowEval18100 (x : Key → ℝ) : Integer.Sparse.eval row18100 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18100, Integer.Sparse.eval_collectBalanced, rawRowCheck18100]

def rawRow18101 : Integer.Sparse Key := [(key1064, 4), (key1064, 4), (key1215, 4), (key1064, -2), (key1079, -2), (key1064, -2), (key1215, -2), (key1079, -2), (key1215, -2), (key1056, -2), (key1065, -2), (key1056, -2), (key1208, -2), (key1065, -2), (key1208, -2), (key1065, 4), (key1065, 4), (key1208, 4)]

theorem rawRowCheck18101 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form5 = rawRow18101 := by decide +kernel

def row18101 : Integer.Sparse Key := [(key1056, -4), (key1064, 4), (key1065, 4), (key1079, -4)]

theorem rowCheck18101 : row18101 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18101 := by decide +kernel

theorem rowEval18101 (x : Key → ℝ) : Integer.Sparse.eval row18101 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18101, Integer.Sparse.eval_collectBalanced, rawRowCheck18101]

def rawRow18102 : Integer.Sparse Key := [(key1064, 4), (key1215, 4), (key1064, 4), (key1079, -2), (key1064, -2), (key1215, -2), (key1064, -2), (key1215, -2), (key1079, -2), (key1065, -2), (key1056, -2), (key1208, -2), (key1056, -2), (key1208, -2), (key1065, -2), (key1065, 4), (key1208, 4), (key1065, 4)]

theorem rawRowCheck18102 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form5 = rawRow18102 := by decide +kernel

def row18102 : Integer.Sparse Key := [(key1056, -4), (key1064, 4), (key1065, 4), (key1079, -4)]

theorem rowCheck18102 : row18102 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18102 := by decide +kernel

theorem rowEval18102 (x : Key → ℝ) : Integer.Sparse.eval row18102 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18102, Integer.Sparse.eval_collectBalanced, rawRowCheck18102]

def rawRow18103 : Integer.Sparse Key := [(key1215, 4), (key1064, 4), (key1064, 4), (key1215, -2), (key1215, -2), (key1079, -2), (key1079, -2), (key1064, -2), (key1064, -2), (key1208, -2), (key1208, -2), (key1065, -2), (key1065, -2), (key1056, -2), (key1056, -2), (key1208, 4), (key1065, 4), (key1065, 4)]

theorem rawRowCheck18103 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form5 = rawRow18103 := by decide +kernel

def row18103 : Integer.Sparse Key := [(key1056, -4), (key1064, 4), (key1065, 4), (key1079, -4)]

theorem rowCheck18103 : row18103 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18103 := by decide +kernel

theorem rowEval18103 (x : Key → ℝ) : Integer.Sparse.eval row18103 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18103, Integer.Sparse.eval_collectBalanced, rawRowCheck18103]

def rawRow18104 : Integer.Sparse Key := [(key1079, 4), (key1079, 4), (key1079, 4), (key1064, -2), (key1064, -2), (key1064, -2), (key1064, -2), (key1064, -2), (key1064, -2), (key1065, -2), (key1065, -2), (key1065, -2), (key1065, -2), (key1065, -2), (key1065, -2), (key1056, 4), (key1056, 4), (key1056, 4)]

theorem rawRowCheck18104 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form5 = rawRow18104 := by decide +kernel

def row18104 : Integer.Sparse Key := [(key1056, 12), (key1064, -12), (key1065, -12), (key1079, 12)]

theorem rowCheck18104 : row18104 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18104 := by decide +kernel

theorem rowEval18104 (x : Key → ℝ) : Integer.Sparse.eval row18104 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18104, Integer.Sparse.eval_collectBalanced, rawRowCheck18104]

def rawRow18105 : Integer.Sparse Key := [(key1065, 4), (key1065, 4), (key1158, 4), (key1065, -2), (key1079, -2), (key1065, -2), (key1158, -2), (key1079, -2), (key1158, -2), (key1056, -2), (key1064, -2), (key1056, -2), (key1144, -2), (key1064, -2), (key1144, -2), (key1064, 4), (key1064, 4), (key1144, 4)]

theorem rawRowCheck18105 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form5 = rawRow18105 := by decide +kernel

def row18105 : Integer.Sparse Key := [(key1056, -4), (key1064, 4), (key1065, 4), (key1079, -4)]

theorem rowCheck18105 : row18105 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18105 := by decide +kernel

theorem rowEval18105 (x : Key → ℝ) : Integer.Sparse.eval row18105 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck18105, Integer.Sparse.eval_collectBalanced, rawRowCheck18105]

def rawRow18106 : Integer.Sparse Key := [(key1065, 4), (key1158, 4), (key1065, 4), (key1079, -2), (key1065, -2), (key1158, -2), (key1065, -2), (key1158, -2), (key1079, -2), (key1064, -2), (key1056, -2), (key1144, -2), (key1056, -2), (key1144, -2), (key1064, -2), (key1064, 4), (key1144, 4), (key1064, 4)]

theorem rawRowCheck18106 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form5 = rawRow18106 := by decide +kernel

def row18106 : Integer.Sparse Key := [(key1056, -4), (key1064, 4), (key1065, 4), (key1079, -4)]

theorem rowCheck18106 : row18106 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18106 := by decide +kernel

theorem rowEval18106 (x : Key → ℝ) : Integer.Sparse.eval row18106 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18106, Integer.Sparse.eval_collectBalanced, rawRowCheck18106]

def rawRow18107 : Integer.Sparse Key := [(key1158, 4), (key1065, 4), (key1065, 4), (key1158, -2), (key1158, -2), (key1079, -2), (key1079, -2), (key1065, -2), (key1065, -2), (key1144, -2), (key1144, -2), (key1064, -2), (key1064, -2), (key1056, -2), (key1056, -2), (key1144, 4), (key1064, 4), (key1064, 4)]

theorem rawRowCheck18107 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form5 = rawRow18107 := by decide +kernel

def row18107 : Integer.Sparse Key := [(key1056, -4), (key1064, 4), (key1065, 4), (key1079, -4)]

theorem rowCheck18107 : row18107 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18107 := by decide +kernel

theorem rowEval18107 (x : Key → ℝ) : Integer.Sparse.eval row18107 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18107, Integer.Sparse.eval_collectBalanced, rawRowCheck18107]

def rawRow18108 : Integer.Sparse Key := [(key1079, 4), (key1079, 4), (key1079, 4), (key1065, -2), (key1065, -2), (key1065, -2), (key1065, -2), (key1065, -2), (key1065, -2), (key1064, -2), (key1064, -2), (key1064, -2), (key1064, -2), (key1064, -2), (key1064, -2), (key1056, 4), (key1056, 4), (key1056, 4)]

theorem rawRowCheck18108 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form5 = rawRow18108 := by decide +kernel

def row18108 : Integer.Sparse Key := [(key1056, 12), (key1064, -12), (key1065, -12), (key1079, 12)]

theorem rowCheck18108 : row18108 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18108 := by decide +kernel

theorem rowEval18108 (x : Key → ℝ) : Integer.Sparse.eval row18108 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18108, Integer.Sparse.eval_collectBalanced, rawRowCheck18108]

def rawRow18109 : Integer.Sparse Key := [(key2680, -1), (key2683, -1), (key2814, -1), (key2954, -1), (key2819, -1), (key2956, -1), (key2690, 2), (key2819, 2), (key2956, 2), (key2680, -1), (key2683, -1), (key2814, -1), (key2954, -1), (key2819, -1), (key2956, -1), (key2711, 2), (key2741, 2), (key2814, 2), (key2954, 2), (key2901, 2), (key2980, 2), (key2716, -1), (key2743, -1), (key2819, -1), (key2956, -1), (key2901, -1), (key2980, -1), (key2690, 2), (key2819, 2), (key2956, 2), (key2716, -1), (key2743, -1), (key2819, -1), (key2956, -1), (key2901, -1), (key2980, -1)]

theorem rawRowCheck18109 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form6 = rawRow18109 := by decide +kernel

def row18109 : Integer.Sparse Key := [(key2680, -2), (key2683, -2), (key2690, 4), (key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2)]

theorem rowCheck18109 : row18109 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18109 := by decide +kernel

theorem rowEval18109 (x : Key → ℝ) : Integer.Sparse.eval row18109 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck18109, Integer.Sparse.eval_collectBalanced, rawRowCheck18109]

def rawRow18110 : Integer.Sparse Key := [(key2683, -1), (key2680, -1), (key2954, -1), (key2814, -1), (key2956, -1), (key2819, -1), (key2690, 2), (key2956, 2), (key2819, 2), (key2683, -1), (key2680, -1), (key2954, -1), (key2814, -1), (key2956, -1), (key2819, -1), (key2741, 2), (key2711, 2), (key2954, 2), (key2814, 2), (key2980, 2), (key2901, 2), (key2743, -1), (key2716, -1), (key2956, -1), (key2819, -1), (key2980, -1), (key2901, -1), (key2690, 2), (key2956, 2), (key2819, 2), (key2743, -1), (key2716, -1), (key2956, -1), (key2819, -1), (key2980, -1), (key2901, -1)]

theorem rawRowCheck18110 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form6 = rawRow18110 := by decide +kernel

def row18110 : Integer.Sparse Key := [(key2680, -2), (key2683, -2), (key2690, 4), (key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2)]

theorem rowCheck18110 : row18110 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18110 := by decide +kernel

theorem rowEval18110 (x : Key → ℝ) : Integer.Sparse.eval row18110 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck18110, Integer.Sparse.eval_collectBalanced, rawRowCheck18110]

def rawRow18111 : Integer.Sparse Key := [(key2814, -1), (key2819, -1), (key2680, -1), (key2956, -1), (key2683, -1), (key2954, -1), (key2819, 2), (key2690, 2), (key2956, 2), (key2814, -1), (key2819, -1), (key2680, -1), (key2956, -1), (key2683, -1), (key2954, -1), (key2814, 2), (key2901, 2), (key2711, 2), (key2980, 2), (key2741, 2), (key2954, 2), (key2819, -1), (key2901, -1), (key2716, -1), (key2980, -1), (key2743, -1), (key2956, -1), (key2819, 2), (key2690, 2), (key2956, 2), (key2819, -1), (key2901, -1), (key2716, -1), (key2980, -1), (key2743, -1), (key2956, -1)]

theorem rawRowCheck18111 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form6 = rawRow18111 := by decide +kernel

def row18111 : Integer.Sparse Key := [(key2680, -2), (key2683, -2), (key2690, 4), (key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2)]

theorem rowCheck18111 : row18111 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18111 := by decide +kernel

theorem rowEval18111 (x : Key → ℝ) : Integer.Sparse.eval row18111 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck18111, Integer.Sparse.eval_collectBalanced, rawRowCheck18111]

def rawRow18112 : Integer.Sparse Key := [(key2819, -1), (key2814, -1), (key2956, -1), (key2680, -1), (key2954, -1), (key2683, -1), (key2819, 2), (key2956, 2), (key2690, 2), (key2819, -1), (key2814, -1), (key2956, -1), (key2680, -1), (key2954, -1), (key2683, -1), (key2901, 2), (key2814, 2), (key2980, 2), (key2711, 2), (key2954, 2), (key2741, 2), (key2901, -1), (key2819, -1), (key2980, -1), (key2716, -1), (key2956, -1), (key2743, -1), (key2819, 2), (key2956, 2), (key2690, 2), (key2901, -1), (key2819, -1), (key2980, -1), (key2716, -1), (key2956, -1), (key2743, -1)]

theorem rawRowCheck18112 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form6 = rawRow18112 := by decide +kernel

def row18112 : Integer.Sparse Key := [(key2680, -2), (key2683, -2), (key2690, 4), (key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2)]

theorem rowCheck18112 : row18112 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18112 := by decide +kernel

theorem rowEval18112 (x : Key → ℝ) : Integer.Sparse.eval row18112 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck18112, Integer.Sparse.eval_collectBalanced, rawRowCheck18112]

def rawRow18113 : Integer.Sparse Key := [(key2954, -1), (key2956, -1), (key2683, -1), (key2819, -1), (key2680, -1), (key2814, -1), (key2956, 2), (key2690, 2), (key2819, 2), (key2954, -1), (key2956, -1), (key2683, -1), (key2819, -1), (key2680, -1), (key2814, -1), (key2954, 2), (key2980, 2), (key2741, 2), (key2901, 2), (key2711, 2), (key2814, 2), (key2956, -1), (key2980, -1), (key2743, -1), (key2901, -1), (key2716, -1), (key2819, -1), (key2956, 2), (key2690, 2), (key2819, 2), (key2956, -1), (key2980, -1), (key2743, -1), (key2901, -1), (key2716, -1), (key2819, -1)]

theorem rawRowCheck18113 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form6 = rawRow18113 := by decide +kernel

def row18113 : Integer.Sparse Key := [(key2680, -2), (key2683, -2), (key2690, 4), (key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2)]

theorem rowCheck18113 : row18113 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18113 := by decide +kernel

theorem rowEval18113 (x : Key → ℝ) : Integer.Sparse.eval row18113 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck18113, Integer.Sparse.eval_collectBalanced, rawRowCheck18113]

def rawRow18114 : Integer.Sparse Key := [(key2956, -1), (key2954, -1), (key2819, -1), (key2683, -1), (key2814, -1), (key2680, -1), (key2956, 2), (key2819, 2), (key2690, 2), (key2956, -1), (key2954, -1), (key2819, -1), (key2683, -1), (key2814, -1), (key2680, -1), (key2980, 2), (key2954, 2), (key2901, 2), (key2741, 2), (key2814, 2), (key2711, 2), (key2980, -1), (key2956, -1), (key2901, -1), (key2743, -1), (key2819, -1), (key2716, -1), (key2956, 2), (key2819, 2), (key2690, 2), (key2980, -1), (key2956, -1), (key2901, -1), (key2743, -1), (key2819, -1), (key2716, -1)]

theorem rawRowCheck18114 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form6 = rawRow18114 := by decide +kernel

def row18114 : Integer.Sparse Key := [(key2680, -2), (key2683, -2), (key2690, 4), (key2711, 2), (key2716, -2), (key2741, 2), (key2743, -2)]

theorem rowCheck18114 : row18114 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18114 := by decide +kernel

theorem rowEval18114 (x : Key → ℝ) : Integer.Sparse.eval row18114 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck18114, Integer.Sparse.eval_collectBalanced, rawRowCheck18114]

def rawRow18115 : Integer.Sparse Key := [(key2680, -1), (key2690, -1), (key2680, -1), (key2956, -1), (key2690, -1), (key2956, -1), (key2683, 2), (key2683, 2), (key2954, 2), (key2711, -1), (key2716, -1), (key2711, -1), (key2980, -1), (key2716, -1), (key2980, -1), (key2680, 2), (key2743, 2), (key2680, 2), (key2956, 2), (key2743, 2), (key2956, 2), (key2683, -1), (key2741, -1), (key2683, -1), (key2954, -1), (key2741, -1), (key2954, -1), (key2716, 2), (key2716, 2), (key2980, 2), (key2690, -1), (key2743, -1), (key2690, -1), (key2956, -1), (key2743, -1), (key2956, -1)]

theorem rawRowCheck18115 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form6 = rawRow18115 := by decide +kernel

def row18115 : Integer.Sparse Key := [(key2680, 2), (key2683, 2), (key2690, -4), (key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2)]

theorem rowCheck18115 : row18115 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18115 := by decide +kernel

theorem rowEval18115 (x : Key → ℝ) : Integer.Sparse.eval row18115 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck18115, Integer.Sparse.eval_collectBalanced, rawRowCheck18115]

def rawRow18116 : Integer.Sparse Key := [(key2690, -1), (key2680, -1), (key2956, -1), (key2680, -1), (key2956, -1), (key2690, -1), (key2683, 2), (key2954, 2), (key2683, 2), (key2716, -1), (key2711, -1), (key2980, -1), (key2711, -1), (key2980, -1), (key2716, -1), (key2743, 2), (key2680, 2), (key2956, 2), (key2680, 2), (key2956, 2), (key2743, 2), (key2741, -1), (key2683, -1), (key2954, -1), (key2683, -1), (key2954, -1), (key2741, -1), (key2716, 2), (key2980, 2), (key2716, 2), (key2743, -1), (key2690, -1), (key2956, -1), (key2690, -1), (key2956, -1), (key2743, -1)]

theorem rawRowCheck18116 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form6 = rawRow18116 := by decide +kernel

def row18116 : Integer.Sparse Key := [(key2680, 2), (key2683, 2), (key2690, -4), (key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2)]

theorem rowCheck18116 : row18116 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18116 := by decide +kernel

theorem rowEval18116 (x : Key → ℝ) : Integer.Sparse.eval row18116 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck18116, Integer.Sparse.eval_collectBalanced, rawRowCheck18116]

def rawRow18117 : Integer.Sparse Key := [(key2956, -1), (key2956, -1), (key2690, -1), (key2690, -1), (key2680, -1), (key2680, -1), (key2954, 2), (key2683, 2), (key2683, 2), (key2980, -1), (key2980, -1), (key2716, -1), (key2716, -1), (key2711, -1), (key2711, -1), (key2956, 2), (key2956, 2), (key2743, 2), (key2743, 2), (key2680, 2), (key2680, 2), (key2954, -1), (key2954, -1), (key2741, -1), (key2741, -1), (key2683, -1), (key2683, -1), (key2980, 2), (key2716, 2), (key2716, 2), (key2956, -1), (key2956, -1), (key2743, -1), (key2743, -1), (key2690, -1), (key2690, -1)]

theorem rawRowCheck18117 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form6 = rawRow18117 := by decide +kernel

def row18117 : Integer.Sparse Key := [(key2680, 2), (key2683, 2), (key2690, -4), (key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2)]

theorem rowCheck18117 : row18117 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18117 := by decide +kernel

theorem rowEval18117 (x : Key → ℝ) : Integer.Sparse.eval row18117 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck18117, Integer.Sparse.eval_collectBalanced, rawRowCheck18117]

def rawRow18118 : Integer.Sparse Key := [(key2683, -1), (key2690, -1), (key2683, -1), (key2819, -1), (key2690, -1), (key2819, -1), (key2680, 2), (key2680, 2), (key2814, 2), (key2741, -1), (key2743, -1), (key2741, -1), (key2901, -1), (key2743, -1), (key2901, -1), (key2683, 2), (key2716, 2), (key2683, 2), (key2819, 2), (key2716, 2), (key2819, 2), (key2680, -1), (key2711, -1), (key2680, -1), (key2814, -1), (key2711, -1), (key2814, -1), (key2743, 2), (key2743, 2), (key2901, 2), (key2690, -1), (key2716, -1), (key2690, -1), (key2819, -1), (key2716, -1), (key2819, -1)]

theorem rawRowCheck18118 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form6 = rawRow18118 := by decide +kernel

def row18118 : Integer.Sparse Key := [(key2680, 2), (key2683, 2), (key2690, -4), (key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2)]

theorem rowCheck18118 : row18118 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18118 := by decide +kernel

theorem rowEval18118 (x : Key → ℝ) : Integer.Sparse.eval row18118 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck18118, Integer.Sparse.eval_collectBalanced, rawRowCheck18118]

def rawRow18119 : Integer.Sparse Key := [(key2690, -1), (key2683, -1), (key2819, -1), (key2683, -1), (key2819, -1), (key2690, -1), (key2680, 2), (key2814, 2), (key2680, 2), (key2743, -1), (key2741, -1), (key2901, -1), (key2741, -1), (key2901, -1), (key2743, -1), (key2716, 2), (key2683, 2), (key2819, 2), (key2683, 2), (key2819, 2), (key2716, 2), (key2711, -1), (key2680, -1), (key2814, -1), (key2680, -1), (key2814, -1), (key2711, -1), (key2743, 2), (key2901, 2), (key2743, 2), (key2716, -1), (key2690, -1), (key2819, -1), (key2690, -1), (key2819, -1), (key2716, -1)]

theorem rawRowCheck18119 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form6 = rawRow18119 := by decide +kernel

def row18119 : Integer.Sparse Key := [(key2680, 2), (key2683, 2), (key2690, -4), (key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2)]

theorem rowCheck18119 : row18119 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18119 := by decide +kernel

theorem rowEval18119 (x : Key → ℝ) : Integer.Sparse.eval row18119 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck18119, Integer.Sparse.eval_collectBalanced, rawRowCheck18119]

def rawRow18120 : Integer.Sparse Key := [(key2819, -1), (key2819, -1), (key2690, -1), (key2690, -1), (key2683, -1), (key2683, -1), (key2814, 2), (key2680, 2), (key2680, 2), (key2901, -1), (key2901, -1), (key2743, -1), (key2743, -1), (key2741, -1), (key2741, -1), (key2819, 2), (key2819, 2), (key2716, 2), (key2716, 2), (key2683, 2), (key2683, 2), (key2814, -1), (key2814, -1), (key2711, -1), (key2711, -1), (key2680, -1), (key2680, -1), (key2901, 2), (key2743, 2), (key2743, 2), (key2819, -1), (key2819, -1), (key2716, -1), (key2716, -1), (key2690, -1), (key2690, -1)]

theorem rawRowCheck18120 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form6 = rawRow18120 := by decide +kernel

def row18120 : Integer.Sparse Key := [(key2680, 2), (key2683, 2), (key2690, -4), (key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2)]

theorem rowCheck18120 : row18120 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18120 := by decide +kernel

theorem rowEval18120 (x : Key → ℝ) : Integer.Sparse.eval row18120 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck18120, Integer.Sparse.eval_collectBalanced, rawRowCheck18120]

def rawRow18121 : Integer.Sparse Key := [(key2711, -1), (key2716, -1), (key2711, -1), (key2980, -1), (key2716, -1), (key2980, -1), (key2716, 2), (key2716, 2), (key2980, 2), (key2680, -1), (key2690, -1), (key2680, -1), (key2956, -1), (key2690, -1), (key2956, -1), (key2680, 2), (key2743, 2), (key2680, 2), (key2956, 2), (key2743, 2), (key2956, 2), (key2690, -1), (key2743, -1), (key2690, -1), (key2956, -1), (key2743, -1), (key2956, -1), (key2683, 2), (key2683, 2), (key2954, 2), (key2683, -1), (key2741, -1), (key2683, -1), (key2954, -1), (key2741, -1), (key2954, -1)]

theorem rawRowCheck18121 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form6 = rawRow18121 := by decide +kernel

def row18121 : Integer.Sparse Key := [(key2680, 2), (key2683, 2), (key2690, -4), (key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2)]

theorem rowCheck18121 : row18121 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18121 := by decide +kernel

theorem rowEval18121 (x : Key → ℝ) : Integer.Sparse.eval row18121 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck18121, Integer.Sparse.eval_collectBalanced, rawRowCheck18121]

def rawRow18122 : Integer.Sparse Key := [(key2716, -1), (key2711, -1), (key2980, -1), (key2711, -1), (key2980, -1), (key2716, -1), (key2716, 2), (key2980, 2), (key2716, 2), (key2690, -1), (key2680, -1), (key2956, -1), (key2680, -1), (key2956, -1), (key2690, -1), (key2743, 2), (key2680, 2), (key2956, 2), (key2680, 2), (key2956, 2), (key2743, 2), (key2743, -1), (key2690, -1), (key2956, -1), (key2690, -1), (key2956, -1), (key2743, -1), (key2683, 2), (key2954, 2), (key2683, 2), (key2741, -1), (key2683, -1), (key2954, -1), (key2683, -1), (key2954, -1), (key2741, -1)]

theorem rawRowCheck18122 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form6 = rawRow18122 := by decide +kernel

def row18122 : Integer.Sparse Key := [(key2680, 2), (key2683, 2), (key2690, -4), (key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2)]

theorem rowCheck18122 : row18122 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18122 := by decide +kernel

theorem rowEval18122 (x : Key → ℝ) : Integer.Sparse.eval row18122 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck18122, Integer.Sparse.eval_collectBalanced, rawRowCheck18122]

def rawRow18123 : Integer.Sparse Key := [(key2980, -1), (key2980, -1), (key2716, -1), (key2716, -1), (key2711, -1), (key2711, -1), (key2980, 2), (key2716, 2), (key2716, 2), (key2956, -1), (key2956, -1), (key2690, -1), (key2690, -1), (key2680, -1), (key2680, -1), (key2956, 2), (key2956, 2), (key2743, 2), (key2743, 2), (key2680, 2), (key2680, 2), (key2956, -1), (key2956, -1), (key2743, -1), (key2743, -1), (key2690, -1), (key2690, -1), (key2954, 2), (key2683, 2), (key2683, 2), (key2954, -1), (key2954, -1), (key2741, -1), (key2741, -1), (key2683, -1), (key2683, -1)]

theorem rawRowCheck18123 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form6 = rawRow18123 := by decide +kernel

def row18123 : Integer.Sparse Key := [(key2680, 2), (key2683, 2), (key2690, -4), (key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2)]

theorem rowCheck18123 : row18123 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18123 := by decide +kernel

theorem rowEval18123 (x : Key → ℝ) : Integer.Sparse.eval row18123 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck18123, Integer.Sparse.eval_collectBalanced, rawRowCheck18123]

def rawRow18124 : Integer.Sparse Key := [(key2716, -1), (key2716, -1), (key2716, -1), (key2716, -1), (key2716, -1), (key2716, -1), (key2711, 2), (key2711, 2), (key2711, 2), (key2743, -1), (key2743, -1), (key2743, -1), (key2743, -1), (key2743, -1), (key2743, -1), (key2690, 2), (key2690, 2), (key2690, 2), (key2690, 2), (key2690, 2), (key2690, 2), (key2680, -1), (key2680, -1), (key2680, -1), (key2680, -1), (key2680, -1), (key2680, -1), (key2741, 2), (key2741, 2), (key2741, 2), (key2683, -1), (key2683, -1), (key2683, -1), (key2683, -1), (key2683, -1), (key2683, -1)]

theorem rawRowCheck18124 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form6 = rawRow18124 := by decide +kernel

def row18124 : Integer.Sparse Key := [(key2680, -6), (key2683, -6), (key2690, 12), (key2711, 6), (key2716, -6), (key2741, 6), (key2743, -6)]

theorem rowCheck18124 : row18124 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18124 := by decide +kernel

theorem rowEval18124 (x : Key → ℝ) : Integer.Sparse.eval row18124 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck18124, Integer.Sparse.eval_collectBalanced, rawRowCheck18124]

def rawRow18125 : Integer.Sparse Key := [(key2741, -1), (key2743, -1), (key2741, -1), (key2901, -1), (key2743, -1), (key2901, -1), (key2743, 2), (key2743, 2), (key2901, 2), (key2683, -1), (key2690, -1), (key2683, -1), (key2819, -1), (key2690, -1), (key2819, -1), (key2683, 2), (key2716, 2), (key2683, 2), (key2819, 2), (key2716, 2), (key2819, 2), (key2690, -1), (key2716, -1), (key2690, -1), (key2819, -1), (key2716, -1), (key2819, -1), (key2680, 2), (key2680, 2), (key2814, 2), (key2680, -1), (key2711, -1), (key2680, -1), (key2814, -1), (key2711, -1), (key2814, -1)]

theorem rawRowCheck18125 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form6 = rawRow18125 := by decide +kernel

def row18125 : Integer.Sparse Key := [(key2680, 2), (key2683, 2), (key2690, -4), (key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2)]

theorem rowCheck18125 : row18125 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18125 := by decide +kernel

theorem rowEval18125 (x : Key → ℝ) : Integer.Sparse.eval row18125 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck18125, Integer.Sparse.eval_collectBalanced, rawRowCheck18125]

def rawRow18126 : Integer.Sparse Key := [(key2743, -1), (key2741, -1), (key2901, -1), (key2741, -1), (key2901, -1), (key2743, -1), (key2743, 2), (key2901, 2), (key2743, 2), (key2690, -1), (key2683, -1), (key2819, -1), (key2683, -1), (key2819, -1), (key2690, -1), (key2716, 2), (key2683, 2), (key2819, 2), (key2683, 2), (key2819, 2), (key2716, 2), (key2716, -1), (key2690, -1), (key2819, -1), (key2690, -1), (key2819, -1), (key2716, -1), (key2680, 2), (key2814, 2), (key2680, 2), (key2711, -1), (key2680, -1), (key2814, -1), (key2680, -1), (key2814, -1), (key2711, -1)]

theorem rawRowCheck18126 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form6 = rawRow18126 := by decide +kernel

def row18126 : Integer.Sparse Key := [(key2680, 2), (key2683, 2), (key2690, -4), (key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2)]

theorem rowCheck18126 : row18126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18126 := by decide +kernel

theorem rowEval18126 (x : Key → ℝ) : Integer.Sparse.eval row18126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck18126, Integer.Sparse.eval_collectBalanced, rawRowCheck18126]

def rawRow18127 : Integer.Sparse Key := [(key2901, -1), (key2901, -1), (key2743, -1), (key2743, -1), (key2741, -1), (key2741, -1), (key2901, 2), (key2743, 2), (key2743, 2), (key2819, -1), (key2819, -1), (key2690, -1), (key2690, -1), (key2683, -1), (key2683, -1), (key2819, 2), (key2819, 2), (key2716, 2), (key2716, 2), (key2683, 2), (key2683, 2), (key2819, -1), (key2819, -1), (key2716, -1), (key2716, -1), (key2690, -1), (key2690, -1), (key2814, 2), (key2680, 2), (key2680, 2), (key2814, -1), (key2814, -1), (key2711, -1), (key2711, -1), (key2680, -1), (key2680, -1)]

theorem rawRowCheck18127 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form6 = rawRow18127 := by decide +kernel

def row18127 : Integer.Sparse Key := [(key2680, 2), (key2683, 2), (key2690, -4), (key2711, -2), (key2716, 2), (key2741, -2), (key2743, 2)]

theorem rowCheck18127 : row18127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18127 := by decide +kernel

theorem rowEval18127 (x : Key → ℝ) : Integer.Sparse.eval row18127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck18127, Integer.Sparse.eval_collectBalanced, rawRowCheck18127]

def rawRow18128 : Integer.Sparse Key := [(key2743, -1), (key2743, -1), (key2743, -1), (key2743, -1), (key2743, -1), (key2743, -1), (key2741, 2), (key2741, 2), (key2741, 2), (key2716, -1), (key2716, -1), (key2716, -1), (key2716, -1), (key2716, -1), (key2716, -1), (key2690, 2), (key2690, 2), (key2690, 2), (key2690, 2), (key2690, 2), (key2690, 2), (key2683, -1), (key2683, -1), (key2683, -1), (key2683, -1), (key2683, -1), (key2683, -1), (key2711, 2), (key2711, 2), (key2711, 2), (key2680, -1), (key2680, -1), (key2680, -1), (key2680, -1), (key2680, -1), (key2680, -1)]

theorem rawRowCheck18128 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form6 = rawRow18128 := by decide +kernel

def row18128 : Integer.Sparse Key := [(key2680, -6), (key2683, -6), (key2690, 12), (key2711, 6), (key2716, -6), (key2741, 6), (key2743, -6)]

theorem rowCheck18128 : row18128 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18128 := by decide +kernel

theorem rowEval18128 (x : Key → ℝ) : Integer.Sparse.eval row18128 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck18128, Integer.Sparse.eval_collectBalanced, rawRowCheck18128]

def rawRow18129 : Integer.Sparse Key := [(key3080, 4), (key3085, 4), (key3087, 4), (key3085, -4), (key3087, -4), (key3100, -4), (key3085, -4), (key3087, -4), (key3100, -4), (key3100, 12)]

theorem rawRowCheck18129 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form7 = rawRow18129 := by decide +kernel

def row18129 : Integer.Sparse Key := [(key3080, 4), (key3085, -4), (key3087, -4), (key3100, 4)]

theorem rowCheck18129 : row18129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18129 := by decide +kernel

theorem rowEval18129 (x : Key → ℝ) : Integer.Sparse.eval row18129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18129, Integer.Sparse.eval_collectBalanced, rawRowCheck18129]

def rawRow18130 : Integer.Sparse Key := [(key3080, 4), (key3087, 4), (key3085, 4), (key3087, -4), (key3085, -4), (key3100, -4), (key3087, -4), (key3085, -4), (key3100, -4), (key3100, 12)]

theorem rawRowCheck18130 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form7 = rawRow18130 := by decide +kernel

def row18130 : Integer.Sparse Key := [(key3080, 4), (key3085, -4), (key3087, -4), (key3100, 4)]

theorem rowCheck18130 : row18130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18130 := by decide +kernel

theorem rowEval18130 (x : Key → ℝ) : Integer.Sparse.eval row18130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck18130, Integer.Sparse.eval_collectBalanced, rawRowCheck18130]

def rawRow18131 : Integer.Sparse Key := [(key3085, 4), (key3080, 4), (key3087, 4), (key3085, -4), (key3100, -4), (key3087, -4), (key3085, -4), (key3100, -4), (key3087, -4), (key3100, 12)]

theorem rawRowCheck18131 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form7 = rawRow18131 := by decide +kernel

def row18131 : Integer.Sparse Key := [(key3080, 4), (key3085, -4), (key3087, -4), (key3100, 4)]

theorem rowCheck18131 : row18131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18131 := by decide +kernel

theorem rowEval18131 (x : Key → ℝ) : Integer.Sparse.eval row18131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18131, Integer.Sparse.eval_collectBalanced, rawRowCheck18131]

def rawRow18132 : Integer.Sparse Key := [(key3085, 4), (key3087, 4), (key3080, 4), (key3100, -4), (key3085, -4), (key3087, -4), (key3100, -4), (key3085, -4), (key3087, -4), (key3100, 12)]

theorem rawRowCheck18132 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form7 = rawRow18132 := by decide +kernel

def row18132 : Integer.Sparse Key := [(key3080, 4), (key3085, -4), (key3087, -4), (key3100, 4)]

theorem rowCheck18132 : row18132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18132 := by decide +kernel

theorem rowEval18132 (x : Key → ℝ) : Integer.Sparse.eval row18132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18132, Integer.Sparse.eval_collectBalanced, rawRowCheck18132]

def rawRow18133 : Integer.Sparse Key := [(key3087, 4), (key3080, 4), (key3085, 4), (key3087, -4), (key3100, -4), (key3085, -4), (key3087, -4), (key3100, -4), (key3085, -4), (key3100, 12)]

theorem rawRowCheck18133 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form7 = rawRow18133 := by decide +kernel

def row18133 : Integer.Sparse Key := [(key3080, 4), (key3085, -4), (key3087, -4), (key3100, 4)]

theorem rowCheck18133 : row18133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18133 := by decide +kernel

theorem rowEval18133 (x : Key → ℝ) : Integer.Sparse.eval row18133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck18133, Integer.Sparse.eval_collectBalanced, rawRowCheck18133]

def rawRow18134 : Integer.Sparse Key := [(key3087, 4), (key3085, 4), (key3080, 4), (key3100, -4), (key3087, -4), (key3085, -4), (key3100, -4), (key3087, -4), (key3085, -4), (key3100, 12)]

theorem rawRowCheck18134 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form7 = rawRow18134 := by decide +kernel

def row18134 : Integer.Sparse Key := [(key3080, 4), (key3085, -4), (key3087, -4), (key3100, 4)]

theorem rowCheck18134 : row18134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18134 := by decide +kernel

theorem rowEval18134 (x : Key → ℝ) : Integer.Sparse.eval row18134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18134, Integer.Sparse.eval_collectBalanced, rawRowCheck18134]

def rawRow18135 : Integer.Sparse Key := [(key3085, 4), (key3085, 4), (key3100, 4), (key3080, -4), (key3087, -4), (key3087, -4), (key3085, -4), (key3100, -4), (key3100, -4), (key3087, 12)]

theorem rawRowCheck18135 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form7 = rawRow18135 := by decide +kernel

def row18135 : Integer.Sparse Key := [(key3080, -4), (key3085, 4), (key3087, 4), (key3100, -4)]

theorem rowCheck18135 : row18135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18135 := by decide +kernel

theorem rowEval18135 (x : Key → ℝ) : Integer.Sparse.eval row18135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18135, Integer.Sparse.eval_collectBalanced, rawRowCheck18135]

def rawRow18136 : Integer.Sparse Key := [(key3085, 4), (key3100, 4), (key3085, 4), (key3087, -4), (key3080, -4), (key3087, -4), (key3100, -4), (key3085, -4), (key3100, -4), (key3087, 12)]

theorem rawRowCheck18136 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form7 = rawRow18136 := by decide +kernel

def row18136 : Integer.Sparse Key := [(key3080, -4), (key3085, 4), (key3087, 4), (key3100, -4)]

theorem rowCheck18136 : row18136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18136 := by decide +kernel

theorem rowEval18136 (x : Key → ℝ) : Integer.Sparse.eval row18136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18136, Integer.Sparse.eval_collectBalanced, rawRowCheck18136]

def rawRow18137 : Integer.Sparse Key := [(key3100, 4), (key3085, 4), (key3085, 4), (key3087, -4), (key3087, -4), (key3080, -4), (key3100, -4), (key3100, -4), (key3085, -4), (key3087, 12)]

theorem rawRowCheck18137 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form7 = rawRow18137 := by decide +kernel

def row18137 : Integer.Sparse Key := [(key3080, -4), (key3085, 4), (key3087, 4), (key3100, -4)]

theorem rowCheck18137 : row18137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18137 := by decide +kernel

theorem rowEval18137 (x : Key → ℝ) : Integer.Sparse.eval row18137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18137, Integer.Sparse.eval_collectBalanced, rawRowCheck18137]

def rawRow18138 : Integer.Sparse Key := [(key3087, 4), (key3087, 4), (key3100, 4), (key3080, -4), (key3085, -4), (key3085, -4), (key3087, -4), (key3100, -4), (key3100, -4), (key3085, 12)]

theorem rawRowCheck18138 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form7 = rawRow18138 := by decide +kernel

def row18138 : Integer.Sparse Key := [(key3080, -4), (key3085, 4), (key3087, 4), (key3100, -4)]

theorem rowCheck18138 : row18138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18138 := by decide +kernel

theorem rowEval18138 (x : Key → ℝ) : Integer.Sparse.eval row18138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck18138, Integer.Sparse.eval_collectBalanced, rawRowCheck18138]

def rawRow18139 : Integer.Sparse Key := [(key3087, 4), (key3100, 4), (key3087, 4), (key3085, -4), (key3080, -4), (key3085, -4), (key3100, -4), (key3087, -4), (key3100, -4), (key3085, 12)]

theorem rawRowCheck18139 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form7 = rawRow18139 := by decide +kernel

def row18139 : Integer.Sparse Key := [(key3080, -4), (key3085, 4), (key3087, 4), (key3100, -4)]

theorem rowCheck18139 : row18139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18139 := by decide +kernel

theorem rowEval18139 (x : Key → ℝ) : Integer.Sparse.eval row18139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18139, Integer.Sparse.eval_collectBalanced, rawRowCheck18139]

def rawRow18140 : Integer.Sparse Key := [(key3100, 4), (key3087, 4), (key3087, 4), (key3085, -4), (key3085, -4), (key3080, -4), (key3100, -4), (key3100, -4), (key3087, -4), (key3085, 12)]

theorem rawRowCheck18140 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form7 = rawRow18140 := by decide +kernel

def row18140 : Integer.Sparse Key := [(key3080, -4), (key3085, 4), (key3087, 4), (key3100, -4)]

theorem rowCheck18140 : row18140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18140 := by decide +kernel

theorem rowEval18140 (x : Key → ℝ) : Integer.Sparse.eval row18140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18140, Integer.Sparse.eval_collectBalanced, rawRowCheck18140]

def rawRow18141 : Integer.Sparse Key := [(key3085, 4), (key3085, 4), (key3100, 4), (key3085, -4), (key3100, -4), (key3100, -4), (key3080, -4), (key3087, -4), (key3087, -4), (key3087, 12)]

theorem rawRowCheck18141 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form7 = rawRow18141 := by decide +kernel

def row18141 : Integer.Sparse Key := [(key3080, -4), (key3085, 4), (key3087, 4), (key3100, -4)]

theorem rowCheck18141 : row18141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18141 := by decide +kernel

theorem rowEval18141 (x : Key → ℝ) : Integer.Sparse.eval row18141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18141, Integer.Sparse.eval_collectBalanced, rawRowCheck18141]

def rawRow18142 : Integer.Sparse Key := [(key3085, 4), (key3100, 4), (key3085, 4), (key3100, -4), (key3085, -4), (key3100, -4), (key3087, -4), (key3080, -4), (key3087, -4), (key3087, 12)]

theorem rawRowCheck18142 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form7 = rawRow18142 := by decide +kernel

def row18142 : Integer.Sparse Key := [(key3080, -4), (key3085, 4), (key3087, 4), (key3100, -4)]

theorem rowCheck18142 : row18142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18142 := by decide +kernel

theorem rowEval18142 (x : Key → ℝ) : Integer.Sparse.eval row18142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18142, Integer.Sparse.eval_collectBalanced, rawRowCheck18142]

def rawRow18143 : Integer.Sparse Key := [(key3100, 4), (key3085, 4), (key3085, 4), (key3100, -4), (key3100, -4), (key3085, -4), (key3087, -4), (key3087, -4), (key3080, -4), (key3087, 12)]

theorem rawRowCheck18143 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form7 = rawRow18143 := by decide +kernel

def row18143 : Integer.Sparse Key := [(key3080, -4), (key3085, 4), (key3087, 4), (key3100, -4)]

theorem rowCheck18143 : row18143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18143 := by decide +kernel

theorem rowEval18143 (x : Key → ℝ) : Integer.Sparse.eval row18143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18143, Integer.Sparse.eval_collectBalanced, rawRowCheck18143]

def rawRow18144 : Integer.Sparse Key := [(key3100, 4), (key3100, 4), (key3100, 4), (key3085, -4), (key3085, -4), (key3085, -4), (key3087, -4), (key3087, -4), (key3087, -4), (key3080, 12)]

theorem rawRowCheck18144 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form7 = rawRow18144 := by decide +kernel

def row18144 : Integer.Sparse Key := [(key3080, 12), (key3085, -12), (key3087, -12), (key3100, 12)]

theorem rowCheck18144 : row18144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18144 := by decide +kernel

theorem rowEval18144 (x : Key → ℝ) : Integer.Sparse.eval row18144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18144, Integer.Sparse.eval_collectBalanced, rawRowCheck18144]

def rawRow18145 : Integer.Sparse Key := [(key3087, 4), (key3087, 4), (key3100, 4), (key3087, -4), (key3100, -4), (key3100, -4), (key3080, -4), (key3085, -4), (key3085, -4), (key3085, 12)]

theorem rawRowCheck18145 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form7 = rawRow18145 := by decide +kernel

def row18145 : Integer.Sparse Key := [(key3080, -4), (key3085, 4), (key3087, 4), (key3100, -4)]

theorem rowCheck18145 : row18145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18145 := by decide +kernel

theorem rowEval18145 (x : Key → ℝ) : Integer.Sparse.eval row18145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck18145, Integer.Sparse.eval_collectBalanced, rawRowCheck18145]

def rawRow18146 : Integer.Sparse Key := [(key3087, 4), (key3100, 4), (key3087, 4), (key3100, -4), (key3087, -4), (key3100, -4), (key3085, -4), (key3080, -4), (key3085, -4), (key3085, 12)]

theorem rawRowCheck18146 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form7 = rawRow18146 := by decide +kernel

def row18146 : Integer.Sparse Key := [(key3080, -4), (key3085, 4), (key3087, 4), (key3100, -4)]

theorem rowCheck18146 : row18146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18146 := by decide +kernel

theorem rowEval18146 (x : Key → ℝ) : Integer.Sparse.eval row18146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18146, Integer.Sparse.eval_collectBalanced, rawRowCheck18146]

def rawRow18147 : Integer.Sparse Key := [(key3100, 4), (key3087, 4), (key3087, 4), (key3100, -4), (key3100, -4), (key3087, -4), (key3085, -4), (key3085, -4), (key3080, -4), (key3085, 12)]

theorem rawRowCheck18147 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form7 = rawRow18147 := by decide +kernel

def row18147 : Integer.Sparse Key := [(key3080, -4), (key3085, 4), (key3087, 4), (key3100, -4)]

theorem rowCheck18147 : row18147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18147 := by decide +kernel

theorem rowEval18147 (x : Key → ℝ) : Integer.Sparse.eval row18147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18147, Integer.Sparse.eval_collectBalanced, rawRowCheck18147]

def rawRow18148 : Integer.Sparse Key := [(key3100, 4), (key3100, 4), (key3100, 4), (key3087, -4), (key3087, -4), (key3087, -4), (key3085, -4), (key3085, -4), (key3085, -4), (key3080, 12)]

theorem rawRowCheck18148 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form7 = rawRow18148 := by decide +kernel

def row18148 : Integer.Sparse Key := [(key3080, 12), (key3085, -12), (key3087, -12), (key3100, 12)]

theorem rowCheck18148 : row18148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18148 := by decide +kernel

theorem rowEval18148 (x : Key → ℝ) : Integer.Sparse.eval row18148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck18148, Integer.Sparse.eval_collectBalanced, rawRowCheck18148]

def rawRow18149 : Integer.Sparse Key := [(key2414, -2), (key2417, -2), (key2424, -2), (key2424, 6), (key3033, -2), (key3035, -2), (key3039, -2), (key3033, 2), (key3035, 2), (key3120, 2), (key3128, 2), (key3131, 2), (key3138, 2), (key3039, -2), (key3131, -2), (key3138, -2), (key3039, 6), (key3039, -2), (key3131, -2), (key3138, -2)]

theorem rawRowCheck18149 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form8 = rawRow18149 := by decide +kernel

def row18149 : Integer.Sparse Key := [(key2414, -2), (key2417, -2), (key2424, 4), (key3120, 2), (key3128, 2), (key3131, -2), (key3138, -2)]

theorem rowCheck18149 : row18149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18149 := by decide +kernel

theorem rowEval18149 (x : Key → ℝ) : Integer.Sparse.eval row18149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18149, Integer.Sparse.eval_collectBalanced, rawRowCheck18149]

def rawRow18150 : Integer.Sparse Key := [(key2417, -2), (key2414, -2), (key2424, -2), (key2424, 6), (key3035, -2), (key3033, -2), (key3039, -2), (key3035, 2), (key3033, 2), (key3128, 2), (key3120, 2), (key3138, 2), (key3131, 2), (key3039, -2), (key3138, -2), (key3131, -2), (key3039, 6), (key3039, -2), (key3138, -2), (key3131, -2)]

theorem rawRowCheck18150 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form8 = rawRow18150 := by decide +kernel

def row18150 : Integer.Sparse Key := [(key2414, -2), (key2417, -2), (key2424, 4), (key3120, 2), (key3128, 2), (key3131, -2), (key3138, -2)]

theorem rowCheck18150 : row18150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18150 := by decide +kernel

theorem rowEval18150 (x : Key → ℝ) : Integer.Sparse.eval row18150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck18150, Integer.Sparse.eval_collectBalanced, rawRowCheck18150]

def rawRow18151 : Integer.Sparse Key := [(key2414, -2), (key2424, -2), (key2417, -2), (key2424, 6), (key3033, -2), (key3039, -2), (key3035, -2), (key3120, 2), (key3131, 2), (key3033, 2), (key3138, 2), (key3035, 2), (key3128, 2), (key3131, -2), (key3039, -2), (key3138, -2), (key3039, 6), (key3131, -2), (key3039, -2), (key3138, -2)]

theorem rawRowCheck18151 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form8 = rawRow18151 := by decide +kernel

def row18151 : Integer.Sparse Key := [(key2414, -2), (key2417, -2), (key2424, 4), (key3120, 2), (key3128, 2), (key3131, -2), (key3138, -2)]

theorem rowCheck18151 : row18151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18151 := by decide +kernel

theorem rowEval18151 (x : Key → ℝ) : Integer.Sparse.eval row18151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18151, Integer.Sparse.eval_collectBalanced, rawRowCheck18151]

def rawRow18152 : Integer.Sparse Key := [(key2424, -2), (key2414, -2), (key2417, -2), (key2424, 6), (key3039, -2), (key3033, -2), (key3035, -2), (key3131, 2), (key3120, 2), (key3138, 2), (key3033, 2), (key3128, 2), (key3035, 2), (key3131, -2), (key3138, -2), (key3039, -2), (key3039, 6), (key3131, -2), (key3138, -2), (key3039, -2)]

theorem rawRowCheck18152 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form8 = rawRow18152 := by decide +kernel

def row18152 : Integer.Sparse Key := [(key2414, -2), (key2417, -2), (key2424, 4), (key3120, 2), (key3128, 2), (key3131, -2), (key3138, -2)]

theorem rowCheck18152 : row18152 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18152 := by decide +kernel

theorem rowEval18152 (x : Key → ℝ) : Integer.Sparse.eval row18152 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18152, Integer.Sparse.eval_collectBalanced, rawRowCheck18152]

def rawRow18153 : Integer.Sparse Key := [(key2417, -2), (key2424, -2), (key2414, -2), (key2424, 6), (key3035, -2), (key3039, -2), (key3033, -2), (key3128, 2), (key3138, 2), (key3035, 2), (key3131, 2), (key3033, 2), (key3120, 2), (key3138, -2), (key3039, -2), (key3131, -2), (key3039, 6), (key3138, -2), (key3039, -2), (key3131, -2)]

theorem rawRowCheck18153 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form8 = rawRow18153 := by decide +kernel

def row18153 : Integer.Sparse Key := [(key2414, -2), (key2417, -2), (key2424, 4), (key3120, 2), (key3128, 2), (key3131, -2), (key3138, -2)]

theorem rowCheck18153 : row18153 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18153 := by decide +kernel

theorem rowEval18153 (x : Key → ℝ) : Integer.Sparse.eval row18153 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck18153, Integer.Sparse.eval_collectBalanced, rawRowCheck18153]

def rawRow18154 : Integer.Sparse Key := [(key2424, -2), (key2417, -2), (key2414, -2), (key2424, 6), (key3039, -2), (key3035, -2), (key3033, -2), (key3138, 2), (key3128, 2), (key3131, 2), (key3035, 2), (key3120, 2), (key3033, 2), (key3138, -2), (key3131, -2), (key3039, -2), (key3039, 6), (key3138, -2), (key3131, -2), (key3039, -2)]

theorem rawRowCheck18154 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form8 = rawRow18154 := by decide +kernel

def row18154 : Integer.Sparse Key := [(key2414, -2), (key2417, -2), (key2424, 4), (key3120, 2), (key3128, 2), (key3131, -2), (key3138, -2)]

theorem rowCheck18154 : row18154 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18154 := by decide +kernel

theorem rowEval18154 (x : Key → ℝ) : Integer.Sparse.eval row18154 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18154, Integer.Sparse.eval_collectBalanced, rawRowCheck18154]

def rawRow18155 : Integer.Sparse Key := [(key2414, -2), (key2424, -2), (key2424, -2), (key2417, 6), (key3120, -2), (key3131, -2), (key3131, -2), (key3033, 2), (key3039, 2), (key3033, 2), (key3138, 2), (key3039, 2), (key3138, 2), (key3035, -2), (key3035, -2), (key3128, -2), (key3131, 6), (key3039, -2), (key3039, -2), (key3138, -2)]

theorem rawRowCheck18155 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form8 = rawRow18155 := by decide +kernel

def row18155 : Integer.Sparse Key := [(key2414, -2), (key2417, 6), (key2424, -4), (key3033, 4), (key3035, -4), (key3120, -2), (key3128, -2), (key3131, 2), (key3138, 2)]

theorem rowCheck18155 : row18155 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18155 := by decide +kernel

theorem rowEval18155 (x : Key → ℝ) : Integer.Sparse.eval row18155 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18155, Integer.Sparse.eval_collectBalanced, rawRowCheck18155]

def rawRow18156 : Integer.Sparse Key := [(key2424, -2), (key2414, -2), (key2424, -2), (key2417, 6), (key3131, -2), (key3120, -2), (key3131, -2), (key3039, 2), (key3033, 2), (key3138, 2), (key3033, 2), (key3138, 2), (key3039, 2), (key3035, -2), (key3128, -2), (key3035, -2), (key3131, 6), (key3039, -2), (key3138, -2), (key3039, -2)]

theorem rawRowCheck18156 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form8 = rawRow18156 := by decide +kernel

def row18156 : Integer.Sparse Key := [(key2414, -2), (key2417, 6), (key2424, -4), (key3033, 4), (key3035, -4), (key3120, -2), (key3128, -2), (key3131, 2), (key3138, 2)]

theorem rowCheck18156 : row18156 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18156 := by decide +kernel

theorem rowEval18156 (x : Key → ℝ) : Integer.Sparse.eval row18156 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18156, Integer.Sparse.eval_collectBalanced, rawRowCheck18156]

def rawRow18157 : Integer.Sparse Key := [(key2424, -2), (key2424, -2), (key2414, -2), (key2417, 6), (key3131, -2), (key3131, -2), (key3120, -2), (key3138, 2), (key3138, 2), (key3039, 2), (key3039, 2), (key3033, 2), (key3033, 2), (key3128, -2), (key3035, -2), (key3035, -2), (key3131, 6), (key3138, -2), (key3039, -2), (key3039, -2)]

theorem rawRowCheck18157 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form8 = rawRow18157 := by decide +kernel

def row18157 : Integer.Sparse Key := [(key2414, -2), (key2417, 6), (key2424, -4), (key3033, 4), (key3035, -4), (key3120, -2), (key3128, -2), (key3131, 2), (key3138, 2)]

theorem rowCheck18157 : row18157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18157 := by decide +kernel

theorem rowEval18157 (x : Key → ℝ) : Integer.Sparse.eval row18157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18157, Integer.Sparse.eval_collectBalanced, rawRowCheck18157]

def rawRow18158 : Integer.Sparse Key := [(key2417, -2), (key2424, -2), (key2424, -2), (key2414, 6), (key3128, -2), (key3138, -2), (key3138, -2), (key3035, 2), (key3039, 2), (key3035, 2), (key3131, 2), (key3039, 2), (key3131, 2), (key3033, -2), (key3033, -2), (key3120, -2), (key3138, 6), (key3039, -2), (key3039, -2), (key3131, -2)]

theorem rawRowCheck18158 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form8 = rawRow18158 := by decide +kernel

def row18158 : Integer.Sparse Key := [(key2414, 6), (key2417, -2), (key2424, -4), (key3033, -4), (key3035, 4), (key3120, -2), (key3128, -2), (key3131, 2), (key3138, 2)]

theorem rowCheck18158 : row18158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18158 := by decide +kernel

theorem rowEval18158 (x : Key → ℝ) : Integer.Sparse.eval row18158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck18158, Integer.Sparse.eval_collectBalanced, rawRowCheck18158]

def rawRow18159 : Integer.Sparse Key := [(key2424, -2), (key2417, -2), (key2424, -2), (key2414, 6), (key3138, -2), (key3128, -2), (key3138, -2), (key3039, 2), (key3035, 2), (key3131, 2), (key3035, 2), (key3131, 2), (key3039, 2), (key3033, -2), (key3120, -2), (key3033, -2), (key3138, 6), (key3039, -2), (key3131, -2), (key3039, -2)]

theorem rawRowCheck18159 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form8 = rawRow18159 := by decide +kernel

def row18159 : Integer.Sparse Key := [(key2414, 6), (key2417, -2), (key2424, -4), (key3033, -4), (key3035, 4), (key3120, -2), (key3128, -2), (key3131, 2), (key3138, 2)]

theorem rowCheck18159 : row18159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18159 := by decide +kernel

theorem rowEval18159 (x : Key → ℝ) : Integer.Sparse.eval row18159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18159, Integer.Sparse.eval_collectBalanced, rawRowCheck18159]

def rawRow18160 : Integer.Sparse Key := [(key2424, -2), (key2424, -2), (key2417, -2), (key2414, 6), (key3138, -2), (key3138, -2), (key3128, -2), (key3131, 2), (key3131, 2), (key3039, 2), (key3039, 2), (key3035, 2), (key3035, 2), (key3120, -2), (key3033, -2), (key3033, -2), (key3138, 6), (key3131, -2), (key3039, -2), (key3039, -2)]

theorem rawRowCheck18160 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form8 = rawRow18160 := by decide +kernel

def row18160 : Integer.Sparse Key := [(key2414, 6), (key2417, -2), (key2424, -4), (key3033, -4), (key3035, 4), (key3120, -2), (key3128, -2), (key3131, 2), (key3138, 2)]

theorem rowCheck18160 : row18160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18160 := by decide +kernel

theorem rowEval18160 (x : Key → ℝ) : Integer.Sparse.eval row18160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18160, Integer.Sparse.eval_collectBalanced, rawRowCheck18160]

def rawRow18161 : Integer.Sparse Key := [(key2487, -2), (key2492, -2), (key2492, -2), (key2492, 6), (key2414, -2), (key2424, -2), (key2424, -2), (key3033, 2), (key3039, 2), (key3033, 2), (key3138, 2), (key3039, 2), (key3138, 2), (key3039, -2), (key3039, -2), (key3138, -2), (key3035, 6), (key3035, -2), (key3035, -2), (key3128, -2)]

theorem rawRowCheck18161 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form8 = rawRow18161 := by decide +kernel

def row18161 : Integer.Sparse Key := [(key2414, -2), (key2424, -4), (key2487, -2), (key2492, 2), (key3033, 4), (key3035, 2), (key3128, -2), (key3138, 2)]

theorem rowCheck18161 : row18161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18161 := by decide +kernel

theorem rowEval18161 (x : Key → ℝ) : Integer.Sparse.eval row18161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18161, Integer.Sparse.eval_collectBalanced, rawRowCheck18161]

def rawRow18162 : Integer.Sparse Key := [(key2492, -2), (key2487, -2), (key2492, -2), (key2492, 6), (key2424, -2), (key2414, -2), (key2424, -2), (key3039, 2), (key3033, 2), (key3138, 2), (key3033, 2), (key3138, 2), (key3039, 2), (key3039, -2), (key3138, -2), (key3039, -2), (key3035, 6), (key3035, -2), (key3128, -2), (key3035, -2)]

theorem rawRowCheck18162 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form8 = rawRow18162 := by decide +kernel

def row18162 : Integer.Sparse Key := [(key2414, -2), (key2424, -4), (key2487, -2), (key2492, 2), (key3033, 4), (key3035, 2), (key3128, -2), (key3138, 2)]

theorem rowCheck18162 : row18162 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18162 := by decide +kernel

theorem rowEval18162 (x : Key → ℝ) : Integer.Sparse.eval row18162 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18162, Integer.Sparse.eval_collectBalanced, rawRowCheck18162]

def rawRow18163 : Integer.Sparse Key := [(key2492, -2), (key2492, -2), (key2487, -2), (key2492, 6), (key2424, -2), (key2424, -2), (key2414, -2), (key3138, 2), (key3138, 2), (key3039, 2), (key3039, 2), (key3033, 2), (key3033, 2), (key3138, -2), (key3039, -2), (key3039, -2), (key3035, 6), (key3128, -2), (key3035, -2), (key3035, -2)]

theorem rawRowCheck18163 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form8 = rawRow18163 := by decide +kernel

def row18163 : Integer.Sparse Key := [(key2414, -2), (key2424, -4), (key2487, -2), (key2492, 2), (key3033, 4), (key3035, 2), (key3128, -2), (key3138, 2)]

theorem rowCheck18163 : row18163 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18163 := by decide +kernel

theorem rowEval18163 (x : Key → ℝ) : Integer.Sparse.eval row18163 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18163, Integer.Sparse.eval_collectBalanced, rawRowCheck18163]

def rawRow18164 : Integer.Sparse Key := [(key2492, -2), (key2492, -2), (key2492, -2), (key2487, 6), (key2548, -2), (key2548, -2), (key2548, -2), (key2424, 2), (key2424, 2), (key2424, 2), (key2424, 2), (key2424, 2), (key2424, 2), (key2414, -2), (key3033, -2), (key3033, -2), (key3128, 6), (key3035, -2), (key3035, -2), (key3035, -2)]

theorem rawRowCheck18164 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form8 = rawRow18164 := by decide +kernel

def row18164 : Integer.Sparse Key := [(key2414, -2), (key2424, 12), (key2487, 6), (key2492, -6), (key2548, -6), (key3033, -4), (key3035, -6), (key3128, 6)]

theorem rowCheck18164 : row18164 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18164 := by decide +kernel

theorem rowEval18164 (x : Key → ℝ) : Integer.Sparse.eval row18164 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18164, Integer.Sparse.eval_collectBalanced, rawRowCheck18164]

def rawRow18165 : Integer.Sparse Key := [(key2546, -2), (key2548, -2), (key2548, -2), (key2548, 6), (key2417, -2), (key2424, -2), (key2424, -2), (key2417, 2), (key2424, 2), (key2417, 2), (key2492, 2), (key2424, 2), (key2492, 2), (key2424, -2), (key2424, -2), (key2492, -2), (key2414, 6), (key3033, -2), (key3033, -2), (key3120, -2)]

theorem rawRowCheck18165 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form8 = rawRow18165 := by decide +kernel

def row18165 : Integer.Sparse Key := [(key2414, 6), (key2417, 2), (key2424, -4), (key2492, 2), (key2546, -2), (key2548, 2), (key3033, -4), (key3120, -2)]

theorem rowCheck18165 : row18165 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18165 := by decide +kernel

theorem rowEval18165 (x : Key → ℝ) : Integer.Sparse.eval row18165 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck18165, Integer.Sparse.eval_collectBalanced, rawRowCheck18165]

def rawRow18166 : Integer.Sparse Key := [(key2548, -2), (key2546, -2), (key2548, -2), (key2548, 6), (key2424, -2), (key2417, -2), (key2424, -2), (key2424, 2), (key2417, 2), (key2492, 2), (key2417, 2), (key2492, 2), (key2424, 2), (key2424, -2), (key2492, -2), (key2424, -2), (key2414, 6), (key3033, -2), (key3120, -2), (key3033, -2)]

theorem rawRowCheck18166 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form8 = rawRow18166 := by decide +kernel

def row18166 : Integer.Sparse Key := [(key2414, 6), (key2417, 2), (key2424, -4), (key2492, 2), (key2546, -2), (key2548, 2), (key3033, -4), (key3120, -2)]

theorem rowCheck18166 : row18166 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18166 := by decide +kernel

theorem rowEval18166 (x : Key → ℝ) : Integer.Sparse.eval row18166 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18166, Integer.Sparse.eval_collectBalanced, rawRowCheck18166]

def rawRow18167 : Integer.Sparse Key := [(key2548, -2), (key2548, -2), (key2546, -2), (key2548, 6), (key2424, -2), (key2424, -2), (key2417, -2), (key2492, 2), (key2492, 2), (key2424, 2), (key2424, 2), (key2417, 2), (key2417, 2), (key2492, -2), (key2424, -2), (key2424, -2), (key2414, 6), (key3120, -2), (key3033, -2), (key3033, -2)]

theorem rawRowCheck18167 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form8 = rawRow18167 := by decide +kernel

def row18167 : Integer.Sparse Key := [(key2414, 6), (key2417, 2), (key2424, -4), (key2492, 2), (key2546, -2), (key2548, 2), (key3033, -4), (key3120, -2)]

theorem rowCheck18167 : row18167 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18167 := by decide +kernel

theorem rowEval18167 (x : Key → ℝ) : Integer.Sparse.eval row18167 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18167, Integer.Sparse.eval_collectBalanced, rawRowCheck18167]

def rawRow18168 : Integer.Sparse Key := [(key2548, -2), (key2548, -2), (key2548, -2), (key2546, 6), (key2492, -2), (key2492, -2), (key2492, -2), (key2424, 2), (key2424, 2), (key2424, 2), (key2424, 2), (key2424, 2), (key2424, 2), (key2417, -2), (key2417, -2), (key2417, -2), (key2487, 6), (key2414, -2), (key3033, -2), (key3033, -2)]

theorem rawRowCheck18168 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form8 = rawRow18168 := by decide +kernel

def row18168 : Integer.Sparse Key := [(key2414, -2), (key2417, -6), (key2424, 12), (key2487, 6), (key2492, -6), (key2546, 6), (key2548, -6), (key3033, -4)]

theorem rowCheck18168 : row18168 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18168 := by decide +kernel

theorem rowEval18168 (x : Key → ℝ) : Integer.Sparse.eval row18168 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck18168, Integer.Sparse.eval_collectBalanced, rawRowCheck18168]

def rawRow18169 : Integer.Sparse Key := [(key2101, 4), (key2106, 4), (key2111, 4), (key2106, -4), (key2111, -4), (key2139, -4), (key2106, -4), (key2111, -4), (key2139, -4), (key2139, 12)]

theorem rawRowCheck18169 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form9 = rawRow18169 := by decide +kernel

def row18169 : Integer.Sparse Key := [(key2101, 4), (key2106, -4), (key2111, -4), (key2139, 4)]

theorem rowCheck18169 : row18169 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18169 := by decide +kernel

theorem rowEval18169 (x : Key → ℝ) : Integer.Sparse.eval row18169 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18169, Integer.Sparse.eval_collectBalanced, rawRowCheck18169]

def rawRow18170 : Integer.Sparse Key := [(key2101, 4), (key2111, 4), (key2106, 4), (key2111, -4), (key2106, -4), (key2139, -4), (key2111, -4), (key2106, -4), (key2139, -4), (key2139, 12)]

theorem rawRowCheck18170 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form9 = rawRow18170 := by decide +kernel

def row18170 : Integer.Sparse Key := [(key2101, 4), (key2106, -4), (key2111, -4), (key2139, 4)]

theorem rowCheck18170 : row18170 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18170 := by decide +kernel

theorem rowEval18170 (x : Key → ℝ) : Integer.Sparse.eval row18170 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck18170, Integer.Sparse.eval_collectBalanced, rawRowCheck18170]

def rawRow18171 : Integer.Sparse Key := [(key2106, 4), (key2101, 4), (key2111, 4), (key2106, -4), (key2139, -4), (key2111, -4), (key2106, -4), (key2139, -4), (key2111, -4), (key2139, 12)]

theorem rawRowCheck18171 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form9 = rawRow18171 := by decide +kernel

def row18171 : Integer.Sparse Key := [(key2101, 4), (key2106, -4), (key2111, -4), (key2139, 4)]

theorem rowCheck18171 : row18171 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18171 := by decide +kernel

theorem rowEval18171 (x : Key → ℝ) : Integer.Sparse.eval row18171 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18171, Integer.Sparse.eval_collectBalanced, rawRowCheck18171]

def rawRow18172 : Integer.Sparse Key := [(key2106, 4), (key2111, 4), (key2101, 4), (key2139, -4), (key2106, -4), (key2111, -4), (key2139, -4), (key2106, -4), (key2111, -4), (key2139, 12)]

theorem rawRowCheck18172 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form9 = rawRow18172 := by decide +kernel

def row18172 : Integer.Sparse Key := [(key2101, 4), (key2106, -4), (key2111, -4), (key2139, 4)]

theorem rowCheck18172 : row18172 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18172 := by decide +kernel

theorem rowEval18172 (x : Key → ℝ) : Integer.Sparse.eval row18172 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18172, Integer.Sparse.eval_collectBalanced, rawRowCheck18172]

def rawRow18173 : Integer.Sparse Key := [(key2111, 4), (key2101, 4), (key2106, 4), (key2111, -4), (key2139, -4), (key2106, -4), (key2111, -4), (key2139, -4), (key2106, -4), (key2139, 12)]

theorem rawRowCheck18173 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form9 = rawRow18173 := by decide +kernel

def row18173 : Integer.Sparse Key := [(key2101, 4), (key2106, -4), (key2111, -4), (key2139, 4)]

theorem rowCheck18173 : row18173 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18173 := by decide +kernel

theorem rowEval18173 (x : Key → ℝ) : Integer.Sparse.eval row18173 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck18173, Integer.Sparse.eval_collectBalanced, rawRowCheck18173]

def rawRow18174 : Integer.Sparse Key := [(key2111, 4), (key2106, 4), (key2101, 4), (key2139, -4), (key2111, -4), (key2106, -4), (key2139, -4), (key2111, -4), (key2106, -4), (key2139, 12)]

theorem rawRowCheck18174 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form9 = rawRow18174 := by decide +kernel

def row18174 : Integer.Sparse Key := [(key2101, 4), (key2106, -4), (key2111, -4), (key2139, 4)]

theorem rowCheck18174 : row18174 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18174 := by decide +kernel

theorem rowEval18174 (x : Key → ℝ) : Integer.Sparse.eval row18174 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18174, Integer.Sparse.eval_collectBalanced, rawRowCheck18174]

def rawRow18175 : Integer.Sparse Key := [(key2106, 4), (key2106, 4), (key2139, 4), (key2101, -4), (key2111, -4), (key2111, -4), (key2106, -4), (key2139, -4), (key2139, -4), (key2111, 12)]

theorem rawRowCheck18175 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form9 = rawRow18175 := by decide +kernel

def row18175 : Integer.Sparse Key := [(key2101, -4), (key2106, 4), (key2111, 4), (key2139, -4)]

theorem rowCheck18175 : row18175 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18175 := by decide +kernel

theorem rowEval18175 (x : Key → ℝ) : Integer.Sparse.eval row18175 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck18175, Integer.Sparse.eval_collectBalanced, rawRowCheck18175]

end MUB6.Certificate.GramRows

end OAI
