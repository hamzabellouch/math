import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow19072 : Integer.Sparse Key := [(key2451, 6), (key2451, 6), (key2513, 6), (key2448, 6), (key2527, 6), (key2527, 6), (key2558, 6), (key2356, 6), (key2356, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2513, 6), (key2353, 6), (key2448, 6), (key2448, 6), (key2513, 6), (key2356, 6), (key2451, 6), (key2451, 6)]

theorem rawRowCheck19072 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block5.form6 = rawRow19072 := by decide +kernel

def row19072 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 24), (key2527, 12), (key2558, 6)]

theorem rowCheck19072 : row19072 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19072 := by decide +kernel

theorem rowEval19072 (x : Key → ℝ) : Integer.Sparse.eval row19072 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19072, Integer.Sparse.eval_collectBalanced, rawRowCheck19072]

def rawRow19073 : Integer.Sparse Key := [(key2451, 6), (key2513, 6), (key2451, 6), (key2448, 6), (key2527, 6), (key2558, 6), (key2527, 6), (key2451, 6), (key2513, 6), (key2356, 6), (key2513, 6), (key2356, 6), (key2451, 6), (key2448, 6), (key2353, 6), (key2448, 6), (key2513, 6), (key2451, 6), (key2356, 6), (key2451, 6)]

theorem rawRowCheck19073 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block5.form6 = rawRow19073 := by decide +kernel

def row19073 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 24), (key2527, 12), (key2558, 6)]

theorem rowCheck19073 : row19073 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19073 := by decide +kernel

theorem rowEval19073 (x : Key → ℝ) : Integer.Sparse.eval row19073 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19073, Integer.Sparse.eval_collectBalanced, rawRowCheck19073]

def rawRow19074 : Integer.Sparse Key := [(key2513, 6), (key2451, 6), (key2451, 6), (key2448, 6), (key2558, 6), (key2527, 6), (key2527, 6), (key2513, 6), (key2451, 6), (key2513, 6), (key2356, 6), (key2451, 6), (key2356, 6), (key2448, 6), (key2448, 6), (key2353, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2356, 6)]

theorem rawRowCheck19074 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block5.form6 = rawRow19074 := by decide +kernel

def row19074 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 24), (key2527, 12), (key2558, 6)]

theorem rowCheck19074 : row19074 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19074 := by decide +kernel

theorem rowEval19074 (x : Key → ℝ) : Integer.Sparse.eval row19074 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block5.form6) x := by
  rw [rowCheck19074, Integer.Sparse.eval_collectBalanced, rawRowCheck19074]

def rawRow19075 : Integer.Sparse Key := [(key2527, 6), (key2527, 6), (key2527, 6), (key2558, 6), (key2356, 6), (key2356, 6), (key2356, 6), (key2451, 6), (key2451, 6), (key2451, 6), (key2451, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2513, 6), (key2513, 6), (key2353, 6), (key2448, 6), (key2448, 6), (key2448, 6)]

theorem rawRowCheck19075 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block5.form6 = rawRow19075 := by decide +kernel

def row19075 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 18), (key2527, 18), (key2558, 6)]

theorem rowCheck19075 : row19075 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19075 := by decide +kernel

theorem rowEval19075 (x : Key → ℝ) : Integer.Sparse.eval row19075 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19075, Integer.Sparse.eval_collectBalanced, rawRowCheck19075]

def rawRow19076 : Integer.Sparse Key := [(key2527, 6), (key2527, 6), (key2558, 6), (key2527, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2356, 6), (key2356, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2513, 6), (key2356, 6), (key2451, 6), (key2451, 6), (key2448, 6), (key2353, 6), (key2448, 6), (key2448, 6)]

theorem rawRowCheck19076 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block5.form6 = rawRow19076 := by decide +kernel

def row19076 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 18), (key2527, 18), (key2558, 6)]

theorem rowCheck19076 : row19076 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19076 := by decide +kernel

theorem rowEval19076 (x : Key → ℝ) : Integer.Sparse.eval row19076 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19076, Integer.Sparse.eval_collectBalanced, rawRowCheck19076]

def rawRow19077 : Integer.Sparse Key := [(key2527, 6), (key2558, 6), (key2527, 6), (key2527, 6), (key2451, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2356, 6), (key2513, 6), (key2356, 6), (key2451, 6), (key2451, 6), (key2356, 6), (key2451, 6), (key2448, 6), (key2448, 6), (key2353, 6), (key2448, 6)]

theorem rawRowCheck19077 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block5.form6 = rawRow19077 := by decide +kernel

def row19077 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 18), (key2527, 18), (key2558, 6)]

theorem rowCheck19077 : row19077 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19077 := by decide +kernel

theorem rowEval19077 (x : Key → ℝ) : Integer.Sparse.eval row19077 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19077, Integer.Sparse.eval_collectBalanced, rawRowCheck19077]

def rawRow19078 : Integer.Sparse Key := [(key2558, 6), (key2527, 6), (key2527, 6), (key2527, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2451, 6), (key2513, 6), (key2356, 6), (key2451, 6), (key2356, 6), (key2451, 6), (key2451, 6), (key2356, 6), (key2448, 6), (key2448, 6), (key2448, 6), (key2353, 6)]

theorem rawRowCheck19078 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block5.form6 = rawRow19078 := by decide +kernel

def row19078 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 18), (key2527, 18), (key2558, 6)]

theorem rowCheck19078 : row19078 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19078 := by decide +kernel

theorem rowEval19078 (x : Key → ℝ) : Integer.Sparse.eval row19078 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block5.form6) x := by
  rw [rowCheck19078, Integer.Sparse.eval_collectBalanced, rawRowCheck19078]

def rawRow19079 : Integer.Sparse Key := [(key2372, 6), (key2372, 6), (key2372, 6), (key2385, 6), (key2400, 6), (key2400, 6), (key2400, 6), (key2466, 6), (key2466, 6), (key2466, 6), (key2466, 6), (key2466, 6), (key2466, 6), (key2475, 6), (key2475, 6), (key2475, 6), (key2432, 6), (key2498, 6), (key2498, 6), (key2498, 6)]

theorem rawRowCheck19079 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form0 = rawRow19079 := by decide +kernel

def row19079 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

theorem rowCheck19079 : row19079 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19079 := by decide +kernel

theorem rowEval19079 (x : Key → ℝ) : Integer.Sparse.eval row19079 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19079, Integer.Sparse.eval_collectBalanced, rawRowCheck19079]

def rawRow19080 : Integer.Sparse Key := [(key2372, 6), (key2372, 6), (key2385, 6), (key2372, 6), (key2466, 6), (key2466, 6), (key2475, 6), (key2400, 6), (key2400, 6), (key2466, 6), (key2466, 6), (key2475, 6), (key2475, 6), (key2400, 6), (key2466, 6), (key2466, 6), (key2498, 6), (key2432, 6), (key2498, 6), (key2498, 6)]

theorem rawRowCheck19080 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form0 = rawRow19080 := by decide +kernel

def row19080 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

theorem rowCheck19080 : row19080 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19080 := by decide +kernel

theorem rowEval19080 (x : Key → ℝ) : Integer.Sparse.eval row19080 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19080, Integer.Sparse.eval_collectBalanced, rawRowCheck19080]

def rawRow19081 : Integer.Sparse Key := [(key2372, 6), (key2385, 6), (key2372, 6), (key2372, 6), (key2466, 6), (key2475, 6), (key2466, 6), (key2466, 6), (key2475, 6), (key2400, 6), (key2475, 6), (key2400, 6), (key2466, 6), (key2466, 6), (key2400, 6), (key2466, 6), (key2498, 6), (key2498, 6), (key2432, 6), (key2498, 6)]

theorem rawRowCheck19081 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form0 = rawRow19081 := by decide +kernel

def row19081 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

theorem rowCheck19081 : row19081 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19081 := by decide +kernel

theorem rowEval19081 (x : Key → ℝ) : Integer.Sparse.eval row19081 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19081, Integer.Sparse.eval_collectBalanced, rawRowCheck19081]

def rawRow19082 : Integer.Sparse Key := [(key2385, 6), (key2372, 6), (key2372, 6), (key2372, 6), (key2475, 6), (key2466, 6), (key2466, 6), (key2475, 6), (key2466, 6), (key2475, 6), (key2400, 6), (key2466, 6), (key2400, 6), (key2466, 6), (key2466, 6), (key2400, 6), (key2498, 6), (key2498, 6), (key2498, 6), (key2432, 6)]

theorem rawRowCheck19082 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form0 = rawRow19082 := by decide +kernel

def row19082 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

theorem rowCheck19082 : row19082 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19082 := by decide +kernel

theorem rowEval19082 (x : Key → ℝ) : Integer.Sparse.eval row19082 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19082, Integer.Sparse.eval_collectBalanced, rawRowCheck19082]

def rawRow19083 : Integer.Sparse Key := [(key2400, 6), (key2400, 6), (key2400, 6), (key2432, 6), (key2372, 6), (key2372, 6), (key2372, 6), (key2466, 6), (key2466, 6), (key2466, 6), (key2466, 6), (key2466, 6), (key2466, 6), (key2498, 6), (key2498, 6), (key2498, 6), (key2385, 6), (key2475, 6), (key2475, 6), (key2475, 6)]

theorem rawRowCheck19083 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form0 = rawRow19083 := by decide +kernel

def row19083 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

theorem rowCheck19083 : row19083 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19083 := by decide +kernel

theorem rowEval19083 (x : Key → ℝ) : Integer.Sparse.eval row19083 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19083, Integer.Sparse.eval_collectBalanced, rawRowCheck19083]

def rawRow19084 : Integer.Sparse Key := [(key2400, 6), (key2400, 6), (key2432, 6), (key2400, 6), (key2466, 6), (key2466, 6), (key2498, 6), (key2372, 6), (key2372, 6), (key2466, 6), (key2466, 6), (key2498, 6), (key2498, 6), (key2372, 6), (key2466, 6), (key2466, 6), (key2475, 6), (key2385, 6), (key2475, 6), (key2475, 6)]

theorem rawRowCheck19084 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form0 = rawRow19084 := by decide +kernel

def row19084 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

theorem rowCheck19084 : row19084 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19084 := by decide +kernel

theorem rowEval19084 (x : Key → ℝ) : Integer.Sparse.eval row19084 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19084, Integer.Sparse.eval_collectBalanced, rawRowCheck19084]

def rawRow19085 : Integer.Sparse Key := [(key2400, 6), (key2432, 6), (key2400, 6), (key2400, 6), (key2466, 6), (key2498, 6), (key2466, 6), (key2466, 6), (key2498, 6), (key2372, 6), (key2498, 6), (key2372, 6), (key2466, 6), (key2466, 6), (key2372, 6), (key2466, 6), (key2475, 6), (key2475, 6), (key2385, 6), (key2475, 6)]

theorem rawRowCheck19085 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form0 = rawRow19085 := by decide +kernel

def row19085 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

theorem rowCheck19085 : row19085 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19085 := by decide +kernel

theorem rowEval19085 (x : Key → ℝ) : Integer.Sparse.eval row19085 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19085, Integer.Sparse.eval_collectBalanced, rawRowCheck19085]

def rawRow19086 : Integer.Sparse Key := [(key2432, 6), (key2400, 6), (key2400, 6), (key2400, 6), (key2498, 6), (key2466, 6), (key2466, 6), (key2498, 6), (key2466, 6), (key2498, 6), (key2372, 6), (key2466, 6), (key2372, 6), (key2466, 6), (key2466, 6), (key2372, 6), (key2475, 6), (key2475, 6), (key2475, 6), (key2385, 6)]

theorem rawRowCheck19086 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form0 = rawRow19086 := by decide +kernel

def row19086 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

theorem rowCheck19086 : row19086 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19086 := by decide +kernel

theorem rowEval19086 (x : Key → ℝ) : Integer.Sparse.eval row19086 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19086, Integer.Sparse.eval_collectBalanced, rawRowCheck19086]

def rawRow19087 : Integer.Sparse Key := [(key2466, 6), (key2466, 6), (key2475, 6), (key2498, 6), (key2372, 6), (key2372, 6), (key2385, 6), (key2400, 6), (key2400, 6), (key2466, 6), (key2466, 6), (key2475, 6), (key2475, 6), (key2432, 6), (key2498, 6), (key2498, 6), (key2372, 6), (key2400, 6), (key2466, 6), (key2466, 6)]

theorem rawRowCheck19087 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form0 = rawRow19087 := by decide +kernel

def row19087 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

theorem rowCheck19087 : row19087 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19087 := by decide +kernel

theorem rowEval19087 (x : Key → ℝ) : Integer.Sparse.eval row19087 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19087, Integer.Sparse.eval_collectBalanced, rawRowCheck19087]

def rawRow19088 : Integer.Sparse Key := [(key2466, 6), (key2475, 6), (key2466, 6), (key2498, 6), (key2372, 6), (key2385, 6), (key2372, 6), (key2466, 6), (key2475, 6), (key2400, 6), (key2475, 6), (key2400, 6), (key2466, 6), (key2498, 6), (key2432, 6), (key2498, 6), (key2372, 6), (key2466, 6), (key2400, 6), (key2466, 6)]

theorem rawRowCheck19088 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form0 = rawRow19088 := by decide +kernel

def row19088 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

theorem rowCheck19088 : row19088 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19088 := by decide +kernel

theorem rowEval19088 (x : Key → ℝ) : Integer.Sparse.eval row19088 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19088, Integer.Sparse.eval_collectBalanced, rawRowCheck19088]

def rawRow19089 : Integer.Sparse Key := [(key2475, 6), (key2466, 6), (key2466, 6), (key2498, 6), (key2385, 6), (key2372, 6), (key2372, 6), (key2475, 6), (key2466, 6), (key2475, 6), (key2400, 6), (key2466, 6), (key2400, 6), (key2498, 6), (key2498, 6), (key2432, 6), (key2372, 6), (key2466, 6), (key2466, 6), (key2400, 6)]

theorem rawRowCheck19089 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form0 = rawRow19089 := by decide +kernel

def row19089 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

theorem rowCheck19089 : row19089 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19089 := by decide +kernel

theorem rowEval19089 (x : Key → ℝ) : Integer.Sparse.eval row19089 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19089, Integer.Sparse.eval_collectBalanced, rawRowCheck19089]

def rawRow19090 : Integer.Sparse Key := [(key2466, 6), (key2466, 6), (key2498, 6), (key2475, 6), (key2400, 6), (key2400, 6), (key2432, 6), (key2372, 6), (key2372, 6), (key2466, 6), (key2466, 6), (key2498, 6), (key2498, 6), (key2385, 6), (key2475, 6), (key2475, 6), (key2400, 6), (key2372, 6), (key2466, 6), (key2466, 6)]

theorem rawRowCheck19090 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form0 = rawRow19090 := by decide +kernel

def row19090 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

theorem rowCheck19090 : row19090 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19090 := by decide +kernel

theorem rowEval19090 (x : Key → ℝ) : Integer.Sparse.eval row19090 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19090, Integer.Sparse.eval_collectBalanced, rawRowCheck19090]

def rawRow19091 : Integer.Sparse Key := [(key2466, 6), (key2498, 6), (key2466, 6), (key2475, 6), (key2400, 6), (key2432, 6), (key2400, 6), (key2466, 6), (key2498, 6), (key2372, 6), (key2498, 6), (key2372, 6), (key2466, 6), (key2475, 6), (key2385, 6), (key2475, 6), (key2400, 6), (key2466, 6), (key2372, 6), (key2466, 6)]

theorem rawRowCheck19091 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form0 = rawRow19091 := by decide +kernel

def row19091 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

theorem rowCheck19091 : row19091 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19091 := by decide +kernel

theorem rowEval19091 (x : Key → ℝ) : Integer.Sparse.eval row19091 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19091, Integer.Sparse.eval_collectBalanced, rawRowCheck19091]

def rawRow19092 : Integer.Sparse Key := [(key2498, 6), (key2466, 6), (key2466, 6), (key2475, 6), (key2432, 6), (key2400, 6), (key2400, 6), (key2498, 6), (key2466, 6), (key2498, 6), (key2372, 6), (key2466, 6), (key2372, 6), (key2475, 6), (key2475, 6), (key2385, 6), (key2400, 6), (key2466, 6), (key2466, 6), (key2372, 6)]

theorem rawRowCheck19092 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form0 = rawRow19092 := by decide +kernel

def row19092 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

theorem rowCheck19092 : row19092 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19092 := by decide +kernel

theorem rowEval19092 (x : Key → ℝ) : Integer.Sparse.eval row19092 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19092, Integer.Sparse.eval_collectBalanced, rawRowCheck19092]

def rawRow19093 : Integer.Sparse Key := [(key2466, 6), (key2475, 6), (key2498, 6), (key2466, 6), (key2466, 6), (key2475, 6), (key2498, 6), (key2372, 6), (key2385, 6), (key2400, 6), (key2475, 6), (key2432, 6), (key2498, 6), (key2372, 6), (key2400, 6), (key2466, 6), (key2466, 6), (key2372, 6), (key2400, 6), (key2466, 6)]

theorem rawRowCheck19093 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form0 = rawRow19093 := by decide +kernel

def row19093 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

theorem rowCheck19093 : row19093 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19093 := by decide +kernel

theorem rowEval19093 (x : Key → ℝ) : Integer.Sparse.eval row19093 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19093, Integer.Sparse.eval_collectBalanced, rawRowCheck19093]

def rawRow19094 : Integer.Sparse Key := [(key2475, 6), (key2466, 6), (key2498, 6), (key2466, 6), (key2475, 6), (key2466, 6), (key2498, 6), (key2385, 6), (key2372, 6), (key2475, 6), (key2400, 6), (key2498, 6), (key2432, 6), (key2372, 6), (key2466, 6), (key2400, 6), (key2466, 6), (key2372, 6), (key2466, 6), (key2400, 6)]

theorem rawRowCheck19094 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form0 = rawRow19094 := by decide +kernel

def row19094 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

theorem rowCheck19094 : row19094 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19094 := by decide +kernel

theorem rowEval19094 (x : Key → ℝ) : Integer.Sparse.eval row19094 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19094, Integer.Sparse.eval_collectBalanced, rawRowCheck19094]

def rawRow19095 : Integer.Sparse Key := [(key2466, 6), (key2498, 6), (key2475, 6), (key2466, 6), (key2466, 6), (key2498, 6), (key2475, 6), (key2400, 6), (key2432, 6), (key2372, 6), (key2498, 6), (key2385, 6), (key2475, 6), (key2400, 6), (key2372, 6), (key2466, 6), (key2466, 6), (key2400, 6), (key2372, 6), (key2466, 6)]

theorem rawRowCheck19095 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form0 = rawRow19095 := by decide +kernel

def row19095 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

theorem rowCheck19095 : row19095 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19095 := by decide +kernel

theorem rowEval19095 (x : Key → ℝ) : Integer.Sparse.eval row19095 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19095, Integer.Sparse.eval_collectBalanced, rawRowCheck19095]

def rawRow19096 : Integer.Sparse Key := [(key2498, 6), (key2466, 6), (key2475, 6), (key2466, 6), (key2498, 6), (key2466, 6), (key2475, 6), (key2432, 6), (key2400, 6), (key2498, 6), (key2372, 6), (key2475, 6), (key2385, 6), (key2400, 6), (key2466, 6), (key2372, 6), (key2466, 6), (key2400, 6), (key2466, 6), (key2372, 6)]

theorem rawRowCheck19096 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form0 = rawRow19096 := by decide +kernel

def row19096 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

theorem rowCheck19096 : row19096 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19096 := by decide +kernel

theorem rowEval19096 (x : Key → ℝ) : Integer.Sparse.eval row19096 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19096, Integer.Sparse.eval_collectBalanced, rawRowCheck19096]

def rawRow19097 : Integer.Sparse Key := [(key2475, 6), (key2498, 6), (key2466, 6), (key2466, 6), (key2475, 6), (key2498, 6), (key2466, 6), (key2475, 6), (key2498, 6), (key2385, 6), (key2432, 6), (key2372, 6), (key2400, 6), (key2466, 6), (key2372, 6), (key2400, 6), (key2466, 6), (key2466, 6), (key2372, 6), (key2400, 6)]

theorem rawRowCheck19097 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form0 = rawRow19097 := by decide +kernel

def row19097 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

theorem rowCheck19097 : row19097 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19097 := by decide +kernel

theorem rowEval19097 (x : Key → ℝ) : Integer.Sparse.eval row19097 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19097, Integer.Sparse.eval_collectBalanced, rawRowCheck19097]

def rawRow19098 : Integer.Sparse Key := [(key2498, 6), (key2475, 6), (key2466, 6), (key2466, 6), (key2498, 6), (key2475, 6), (key2466, 6), (key2498, 6), (key2475, 6), (key2432, 6), (key2385, 6), (key2400, 6), (key2372, 6), (key2466, 6), (key2400, 6), (key2372, 6), (key2466, 6), (key2466, 6), (key2400, 6), (key2372, 6)]

theorem rawRowCheck19098 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form0 = rawRow19098 := by decide +kernel

def row19098 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

theorem rowCheck19098 : row19098 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19098 := by decide +kernel

theorem rowEval19098 (x : Key → ℝ) : Integer.Sparse.eval row19098 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19098, Integer.Sparse.eval_collectBalanced, rawRowCheck19098]

def rawRow19099 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 24), (key1102, 24), (key1102, 24)]

theorem rawRowCheck19099 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form1 = rawRow19099 := by decide +kernel

def row19099 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

theorem rowCheck19099 : row19099 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19099 := by decide +kernel

theorem rowEval19099 (x : Key → ℝ) : Integer.Sparse.eval row19099 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19099, Integer.Sparse.eval_collectBalanced, rawRowCheck19099]

def rawRow19100 : Integer.Sparse Key := [(key989, 24), (key1102, 24), (key1024, 24), (key1102, 24), (key1102, 24)]

theorem rawRowCheck19100 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form1 = rawRow19100 := by decide +kernel

def row19100 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

theorem rowCheck19100 : row19100 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19100 := by decide +kernel

theorem rowEval19100 (x : Key → ℝ) : Integer.Sparse.eval row19100 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19100, Integer.Sparse.eval_collectBalanced, rawRowCheck19100]

def rawRow19101 : Integer.Sparse Key := [(key989, 24), (key1102, 24), (key1102, 24), (key1024, 24), (key1102, 24)]

theorem rawRowCheck19101 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form1 = rawRow19101 := by decide +kernel

def row19101 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

theorem rowCheck19101 : row19101 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19101 := by decide +kernel

theorem rowEval19101 (x : Key → ℝ) : Integer.Sparse.eval row19101 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19101, Integer.Sparse.eval_collectBalanced, rawRowCheck19101]

def rawRow19102 : Integer.Sparse Key := [(key989, 24), (key1102, 24), (key1102, 24), (key1102, 24), (key1024, 24)]

theorem rawRowCheck19102 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form1 = rawRow19102 := by decide +kernel

def row19102 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

theorem rowCheck19102 : row19102 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19102 := by decide +kernel

theorem rowEval19102 (x : Key → ℝ) : Integer.Sparse.eval row19102 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19102, Integer.Sparse.eval_collectBalanced, rawRowCheck19102]

def rawRow19103 : Integer.Sparse Key := [(key1024, 24), (key989, 24), (key1102, 24), (key1102, 24), (key1102, 24)]

theorem rawRowCheck19103 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form1 = rawRow19103 := by decide +kernel

def row19103 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

theorem rowCheck19103 : row19103 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19103 := by decide +kernel

theorem rowEval19103 (x : Key → ℝ) : Integer.Sparse.eval row19103 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19103, Integer.Sparse.eval_collectBalanced, rawRowCheck19103]

def rawRow19104 : Integer.Sparse Key := [(key1024, 24), (key1102, 24), (key989, 24), (key1102, 24), (key1102, 24)]

theorem rawRowCheck19104 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form1 = rawRow19104 := by decide +kernel

def row19104 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

theorem rowCheck19104 : row19104 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19104 := by decide +kernel

theorem rowEval19104 (x : Key → ℝ) : Integer.Sparse.eval row19104 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19104, Integer.Sparse.eval_collectBalanced, rawRowCheck19104]

def rawRow19105 : Integer.Sparse Key := [(key1024, 24), (key1102, 24), (key1102, 24), (key989, 24), (key1102, 24)]

theorem rawRowCheck19105 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form1 = rawRow19105 := by decide +kernel

def row19105 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

theorem rowCheck19105 : row19105 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19105 := by decide +kernel

theorem rowEval19105 (x : Key → ℝ) : Integer.Sparse.eval row19105 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19105, Integer.Sparse.eval_collectBalanced, rawRowCheck19105]

def rawRow19106 : Integer.Sparse Key := [(key1024, 24), (key1102, 24), (key1102, 24), (key1102, 24), (key989, 24)]

theorem rawRowCheck19106 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form1 = rawRow19106 := by decide +kernel

def row19106 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

theorem rowCheck19106 : row19106 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19106 := by decide +kernel

theorem rowEval19106 (x : Key → ℝ) : Integer.Sparse.eval row19106 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19106, Integer.Sparse.eval_collectBalanced, rawRowCheck19106]

def rawRow19107 : Integer.Sparse Key := [(key1102, 24), (key989, 24), (key1024, 24), (key1102, 24), (key1102, 24)]

theorem rawRowCheck19107 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form1 = rawRow19107 := by decide +kernel

def row19107 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

theorem rowCheck19107 : row19107 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19107 := by decide +kernel

theorem rowEval19107 (x : Key → ℝ) : Integer.Sparse.eval row19107 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19107, Integer.Sparse.eval_collectBalanced, rawRowCheck19107]

def rawRow19108 : Integer.Sparse Key := [(key1102, 24), (key989, 24), (key1102, 24), (key1024, 24), (key1102, 24)]

theorem rawRowCheck19108 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form1 = rawRow19108 := by decide +kernel

def row19108 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

theorem rowCheck19108 : row19108 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19108 := by decide +kernel

theorem rowEval19108 (x : Key → ℝ) : Integer.Sparse.eval row19108 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19108, Integer.Sparse.eval_collectBalanced, rawRowCheck19108]

def rawRow19109 : Integer.Sparse Key := [(key1102, 24), (key989, 24), (key1102, 24), (key1102, 24), (key1024, 24)]

theorem rawRowCheck19109 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form1 = rawRow19109 := by decide +kernel

def row19109 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

theorem rowCheck19109 : row19109 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19109 := by decide +kernel

theorem rowEval19109 (x : Key → ℝ) : Integer.Sparse.eval row19109 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19109, Integer.Sparse.eval_collectBalanced, rawRowCheck19109]

def rawRow19110 : Integer.Sparse Key := [(key1102, 24), (key1024, 24), (key989, 24), (key1102, 24), (key1102, 24)]

theorem rawRowCheck19110 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form1 = rawRow19110 := by decide +kernel

def row19110 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

theorem rowCheck19110 : row19110 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19110 := by decide +kernel

theorem rowEval19110 (x : Key → ℝ) : Integer.Sparse.eval row19110 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19110, Integer.Sparse.eval_collectBalanced, rawRowCheck19110]

def rawRow19111 : Integer.Sparse Key := [(key1102, 24), (key1024, 24), (key1102, 24), (key989, 24), (key1102, 24)]

theorem rawRowCheck19111 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form1 = rawRow19111 := by decide +kernel

def row19111 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

theorem rowCheck19111 : row19111 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19111 := by decide +kernel

theorem rowEval19111 (x : Key → ℝ) : Integer.Sparse.eval row19111 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19111, Integer.Sparse.eval_collectBalanced, rawRowCheck19111]

def rawRow19112 : Integer.Sparse Key := [(key1102, 24), (key1024, 24), (key1102, 24), (key1102, 24), (key989, 24)]

theorem rawRowCheck19112 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form1 = rawRow19112 := by decide +kernel

def row19112 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

theorem rowCheck19112 : row19112 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19112 := by decide +kernel

theorem rowEval19112 (x : Key → ℝ) : Integer.Sparse.eval row19112 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19112, Integer.Sparse.eval_collectBalanced, rawRowCheck19112]

def rawRow19113 : Integer.Sparse Key := [(key1102, 24), (key1102, 24), (key989, 24), (key1024, 24), (key1102, 24)]

theorem rawRowCheck19113 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form1 = rawRow19113 := by decide +kernel

def row19113 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

theorem rowCheck19113 : row19113 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19113 := by decide +kernel

theorem rowEval19113 (x : Key → ℝ) : Integer.Sparse.eval row19113 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19113, Integer.Sparse.eval_collectBalanced, rawRowCheck19113]

def rawRow19114 : Integer.Sparse Key := [(key1102, 24), (key1102, 24), (key989, 24), (key1102, 24), (key1024, 24)]

theorem rawRowCheck19114 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form1 = rawRow19114 := by decide +kernel

def row19114 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

theorem rowCheck19114 : row19114 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19114 := by decide +kernel

theorem rowEval19114 (x : Key → ℝ) : Integer.Sparse.eval row19114 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19114, Integer.Sparse.eval_collectBalanced, rawRowCheck19114]

def rawRow19115 : Integer.Sparse Key := [(key1102, 24), (key1102, 24), (key1024, 24), (key989, 24), (key1102, 24)]

theorem rawRowCheck19115 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form1 = rawRow19115 := by decide +kernel

def row19115 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

theorem rowCheck19115 : row19115 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19115 := by decide +kernel

theorem rowEval19115 (x : Key → ℝ) : Integer.Sparse.eval row19115 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19115, Integer.Sparse.eval_collectBalanced, rawRowCheck19115]

def rawRow19116 : Integer.Sparse Key := [(key1102, 24), (key1102, 24), (key1024, 24), (key1102, 24), (key989, 24)]

theorem rawRowCheck19116 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form1 = rawRow19116 := by decide +kernel

def row19116 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

theorem rowCheck19116 : row19116 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19116 := by decide +kernel

theorem rowEval19116 (x : Key → ℝ) : Integer.Sparse.eval row19116 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19116, Integer.Sparse.eval_collectBalanced, rawRowCheck19116]

def rawRow19117 : Integer.Sparse Key := [(key1102, 24), (key1102, 24), (key1102, 24), (key989, 24), (key1024, 24)]

theorem rawRowCheck19117 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form1 = rawRow19117 := by decide +kernel

def row19117 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

theorem rowCheck19117 : row19117 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19117 := by decide +kernel

theorem rowEval19117 (x : Key → ℝ) : Integer.Sparse.eval row19117 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19117, Integer.Sparse.eval_collectBalanced, rawRowCheck19117]

def rawRow19118 : Integer.Sparse Key := [(key1102, 24), (key1102, 24), (key1102, 24), (key1024, 24), (key989, 24)]

theorem rawRowCheck19118 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form1 = rawRow19118 := by decide +kernel

def row19118 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

theorem rowCheck19118 : row19118 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19118 := by decide +kernel

theorem rowEval19118 (x : Key → ℝ) : Integer.Sparse.eval row19118 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19118, Integer.Sparse.eval_collectBalanced, rawRowCheck19118]

def rawRow19119 : Integer.Sparse Key := [(key2610, 2), (key2610, 2), (key2610, 2), (key2626, 2), (key2626, 2), (key2626, 2), (key2626, 2), (key2626, 2), (key2626, 2), (key2635, 2), (key2635, 2), (key2635, 2), (key2665, 2), (key2665, 2), (key2665, 2), (key2780, 2), (key2780, 2), (key2780, 2), (key2780, 2), (key2780, 2), (key2780, 2), (key2789, 2), (key2789, 2), (key2789, 2), (key2700, 2), (key2700, 2), (key2700, 2), (key2700, 2), (key2700, 2), (key2700, 2), (key2803, 2), (key2803, 2), (key2803, 2), (key2803, 2), (key2803, 2), (key2803, 2), (key2853, 2), (key2853, 2), (key2853, 2), (key2853, 2), (key2853, 2), (key2853, 2), (key2855, 2), (key2855, 2), (key2855, 2), (key2855, 2), (key2855, 2), (key2855, 2), (key2721, 2), (key2721, 2), (key2721, 2), (key2824, 2), (key2824, 2), (key2824, 2), (key2865, 2), (key2865, 2), (key2865, 2), (key2865, 2), (key2865, 2), (key2865, 2)]

theorem rawRowCheck19119 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form2 = rawRow19119 := by decide +kernel

def row19119 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

theorem rowCheck19119 : row19119 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19119 := by decide +kernel

theorem rowEval19119 (x : Key → ℝ) : Integer.Sparse.eval row19119 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19119, Integer.Sparse.eval_collectBalanced, rawRowCheck19119]

def rawRow19120 : Integer.Sparse Key := [(key2626, 2), (key2626, 2), (key2635, 2), (key2610, 2), (key2610, 2), (key2626, 2), (key2626, 2), (key2635, 2), (key2635, 2), (key2610, 2), (key2626, 2), (key2626, 2), (key2780, 2), (key2780, 2), (key2789, 2), (key2665, 2), (key2665, 2), (key2780, 2), (key2780, 2), (key2789, 2), (key2789, 2), (key2665, 2), (key2780, 2), (key2780, 2), (key2803, 2), (key2803, 2), (key2853, 2), (key2853, 2), (key2855, 2), (key2855, 2), (key2700, 2), (key2700, 2), (key2853, 2), (key2853, 2), (key2855, 2), (key2855, 2), (key2700, 2), (key2700, 2), (key2803, 2), (key2803, 2), (key2855, 2), (key2855, 2), (key2700, 2), (key2700, 2), (key2803, 2), (key2803, 2), (key2853, 2), (key2853, 2), (key2824, 2), (key2865, 2), (key2865, 2), (key2721, 2), (key2865, 2), (key2865, 2), (key2721, 2), (key2721, 2), (key2824, 2), (key2824, 2), (key2865, 2), (key2865, 2)]

theorem rawRowCheck19120 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form2 = rawRow19120 := by decide +kernel

def row19120 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

theorem rowCheck19120 : row19120 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19120 := by decide +kernel

theorem rowEval19120 (x : Key → ℝ) : Integer.Sparse.eval row19120 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19120, Integer.Sparse.eval_collectBalanced, rawRowCheck19120]

def rawRow19121 : Integer.Sparse Key := [(key2626, 2), (key2635, 2), (key2626, 2), (key2626, 2), (key2635, 2), (key2610, 2), (key2635, 2), (key2610, 2), (key2626, 2), (key2626, 2), (key2610, 2), (key2626, 2), (key2780, 2), (key2789, 2), (key2780, 2), (key2780, 2), (key2789, 2), (key2665, 2), (key2789, 2), (key2665, 2), (key2780, 2), (key2780, 2), (key2665, 2), (key2780, 2), (key2853, 2), (key2855, 2), (key2803, 2), (key2855, 2), (key2803, 2), (key2853, 2), (key2853, 2), (key2855, 2), (key2700, 2), (key2855, 2), (key2700, 2), (key2853, 2), (key2803, 2), (key2855, 2), (key2700, 2), (key2855, 2), (key2700, 2), (key2803, 2), (key2803, 2), (key2853, 2), (key2700, 2), (key2853, 2), (key2700, 2), (key2803, 2), (key2865, 2), (key2824, 2), (key2865, 2), (key2865, 2), (key2721, 2), (key2865, 2), (key2824, 2), (key2865, 2), (key2721, 2), (key2865, 2), (key2721, 2), (key2824, 2)]

theorem rawRowCheck19121 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form2 = rawRow19121 := by decide +kernel

def row19121 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

theorem rowCheck19121 : row19121 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19121 := by decide +kernel

theorem rowEval19121 (x : Key → ℝ) : Integer.Sparse.eval row19121 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19121, Integer.Sparse.eval_collectBalanced, rawRowCheck19121]

def rawRow19122 : Integer.Sparse Key := [(key2635, 2), (key2626, 2), (key2626, 2), (key2635, 2), (key2626, 2), (key2635, 2), (key2610, 2), (key2626, 2), (key2610, 2), (key2626, 2), (key2626, 2), (key2610, 2), (key2789, 2), (key2780, 2), (key2780, 2), (key2789, 2), (key2780, 2), (key2789, 2), (key2665, 2), (key2780, 2), (key2665, 2), (key2780, 2), (key2780, 2), (key2665, 2), (key2855, 2), (key2853, 2), (key2855, 2), (key2803, 2), (key2853, 2), (key2803, 2), (key2855, 2), (key2853, 2), (key2855, 2), (key2700, 2), (key2853, 2), (key2700, 2), (key2855, 2), (key2803, 2), (key2855, 2), (key2700, 2), (key2803, 2), (key2700, 2), (key2853, 2), (key2803, 2), (key2853, 2), (key2700, 2), (key2803, 2), (key2700, 2), (key2865, 2), (key2865, 2), (key2824, 2), (key2865, 2), (key2865, 2), (key2721, 2), (key2865, 2), (key2824, 2), (key2865, 2), (key2721, 2), (key2824, 2), (key2721, 2)]

theorem rawRowCheck19122 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form2 = rawRow19122 := by decide +kernel

def row19122 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

theorem rowCheck19122 : row19122 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19122 := by decide +kernel

theorem rowEval19122 (x : Key → ℝ) : Integer.Sparse.eval row19122 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck19122, Integer.Sparse.eval_collectBalanced, rawRowCheck19122]

def rawRow19123 : Integer.Sparse Key := [(key2665, 2), (key2665, 2), (key2665, 2), (key2700, 2), (key2700, 2), (key2700, 2), (key2700, 2), (key2700, 2), (key2700, 2), (key2721, 2), (key2721, 2), (key2721, 2), (key2610, 2), (key2610, 2), (key2610, 2), (key2803, 2), (key2803, 2), (key2803, 2), (key2803, 2), (key2803, 2), (key2803, 2), (key2824, 2), (key2824, 2), (key2824, 2), (key2626, 2), (key2626, 2), (key2626, 2), (key2626, 2), (key2626, 2), (key2626, 2), (key2780, 2), (key2780, 2), (key2780, 2), (key2780, 2), (key2780, 2), (key2780, 2), (key2853, 2), (key2853, 2), (key2853, 2), (key2853, 2), (key2853, 2), (key2853, 2), (key2865, 2), (key2865, 2), (key2865, 2), (key2865, 2), (key2865, 2), (key2865, 2), (key2635, 2), (key2635, 2), (key2635, 2), (key2789, 2), (key2789, 2), (key2789, 2), (key2855, 2), (key2855, 2), (key2855, 2), (key2855, 2), (key2855, 2), (key2855, 2)]

theorem rawRowCheck19123 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form2 = rawRow19123 := by decide +kernel

def row19123 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

theorem rowCheck19123 : row19123 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19123 := by decide +kernel

theorem rowEval19123 (x : Key → ℝ) : Integer.Sparse.eval row19123 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19123, Integer.Sparse.eval_collectBalanced, rawRowCheck19123]

def rawRow19124 : Integer.Sparse Key := [(key2700, 2), (key2700, 2), (key2721, 2), (key2665, 2), (key2665, 2), (key2700, 2), (key2700, 2), (key2721, 2), (key2721, 2), (key2665, 2), (key2700, 2), (key2700, 2), (key2803, 2), (key2803, 2), (key2824, 2), (key2610, 2), (key2610, 2), (key2803, 2), (key2803, 2), (key2824, 2), (key2824, 2), (key2610, 2), (key2803, 2), (key2803, 2), (key2780, 2), (key2780, 2), (key2853, 2), (key2853, 2), (key2865, 2), (key2865, 2), (key2626, 2), (key2626, 2), (key2853, 2), (key2853, 2), (key2865, 2), (key2865, 2), (key2626, 2), (key2626, 2), (key2780, 2), (key2780, 2), (key2865, 2), (key2865, 2), (key2626, 2), (key2626, 2), (key2780, 2), (key2780, 2), (key2853, 2), (key2853, 2), (key2789, 2), (key2855, 2), (key2855, 2), (key2635, 2), (key2855, 2), (key2855, 2), (key2635, 2), (key2635, 2), (key2789, 2), (key2789, 2), (key2855, 2), (key2855, 2)]

theorem rawRowCheck19124 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form2 = rawRow19124 := by decide +kernel

def row19124 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

theorem rowCheck19124 : row19124 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19124 := by decide +kernel

theorem rowEval19124 (x : Key → ℝ) : Integer.Sparse.eval row19124 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19124, Integer.Sparse.eval_collectBalanced, rawRowCheck19124]

def rawRow19125 : Integer.Sparse Key := [(key2700, 2), (key2721, 2), (key2700, 2), (key2700, 2), (key2721, 2), (key2665, 2), (key2721, 2), (key2665, 2), (key2700, 2), (key2700, 2), (key2665, 2), (key2700, 2), (key2803, 2), (key2824, 2), (key2803, 2), (key2803, 2), (key2824, 2), (key2610, 2), (key2824, 2), (key2610, 2), (key2803, 2), (key2803, 2), (key2610, 2), (key2803, 2), (key2853, 2), (key2865, 2), (key2780, 2), (key2865, 2), (key2780, 2), (key2853, 2), (key2853, 2), (key2865, 2), (key2626, 2), (key2865, 2), (key2626, 2), (key2853, 2), (key2780, 2), (key2865, 2), (key2626, 2), (key2865, 2), (key2626, 2), (key2780, 2), (key2780, 2), (key2853, 2), (key2626, 2), (key2853, 2), (key2626, 2), (key2780, 2), (key2855, 2), (key2789, 2), (key2855, 2), (key2855, 2), (key2635, 2), (key2855, 2), (key2789, 2), (key2855, 2), (key2635, 2), (key2855, 2), (key2635, 2), (key2789, 2)]

theorem rawRowCheck19125 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form2 = rawRow19125 := by decide +kernel

def row19125 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

theorem rowCheck19125 : row19125 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19125 := by decide +kernel

theorem rowEval19125 (x : Key → ℝ) : Integer.Sparse.eval row19125 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19125, Integer.Sparse.eval_collectBalanced, rawRowCheck19125]

def rawRow19126 : Integer.Sparse Key := [(key2721, 2), (key2700, 2), (key2700, 2), (key2721, 2), (key2700, 2), (key2721, 2), (key2665, 2), (key2700, 2), (key2665, 2), (key2700, 2), (key2700, 2), (key2665, 2), (key2824, 2), (key2803, 2), (key2803, 2), (key2824, 2), (key2803, 2), (key2824, 2), (key2610, 2), (key2803, 2), (key2610, 2), (key2803, 2), (key2803, 2), (key2610, 2), (key2865, 2), (key2853, 2), (key2865, 2), (key2780, 2), (key2853, 2), (key2780, 2), (key2865, 2), (key2853, 2), (key2865, 2), (key2626, 2), (key2853, 2), (key2626, 2), (key2865, 2), (key2780, 2), (key2865, 2), (key2626, 2), (key2780, 2), (key2626, 2), (key2853, 2), (key2780, 2), (key2853, 2), (key2626, 2), (key2780, 2), (key2626, 2), (key2855, 2), (key2855, 2), (key2789, 2), (key2855, 2), (key2855, 2), (key2635, 2), (key2855, 2), (key2789, 2), (key2855, 2), (key2635, 2), (key2789, 2), (key2635, 2)]

theorem rawRowCheck19126 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form2 = rawRow19126 := by decide +kernel

def row19126 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

theorem rowCheck19126 : row19126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19126 := by decide +kernel

theorem rowEval19126 (x : Key → ℝ) : Integer.Sparse.eval row19126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19126, Integer.Sparse.eval_collectBalanced, rawRowCheck19126]

def rawRow19127 : Integer.Sparse Key := [(key2780, 2), (key2780, 2), (key2789, 2), (key2803, 2), (key2803, 2), (key2853, 2), (key2853, 2), (key2855, 2), (key2855, 2), (key2824, 2), (key2865, 2), (key2865, 2), (key2626, 2), (key2626, 2), (key2635, 2), (key2700, 2), (key2700, 2), (key2853, 2), (key2853, 2), (key2855, 2), (key2855, 2), (key2721, 2), (key2865, 2), (key2865, 2), (key2610, 2), (key2610, 2), (key2626, 2), (key2626, 2), (key2635, 2), (key2635, 2), (key2665, 2), (key2665, 2), (key2780, 2), (key2780, 2), (key2789, 2), (key2789, 2), (key2700, 2), (key2700, 2), (key2803, 2), (key2803, 2), (key2855, 2), (key2855, 2), (key2721, 2), (key2721, 2), (key2824, 2), (key2824, 2), (key2865, 2), (key2865, 2), (key2610, 2), (key2626, 2), (key2626, 2), (key2665, 2), (key2780, 2), (key2780, 2), (key2700, 2), (key2700, 2), (key2803, 2), (key2803, 2), (key2853, 2), (key2853, 2)]

theorem rawRowCheck19127 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form2 = rawRow19127 := by decide +kernel

def row19127 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

theorem rowCheck19127 : row19127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19127 := by decide +kernel

theorem rowEval19127 (x : Key → ℝ) : Integer.Sparse.eval row19127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19127, Integer.Sparse.eval_collectBalanced, rawRowCheck19127]

def rawRow19128 : Integer.Sparse Key := [(key2780, 2), (key2789, 2), (key2780, 2), (key2853, 2), (key2855, 2), (key2803, 2), (key2855, 2), (key2803, 2), (key2853, 2), (key2865, 2), (key2824, 2), (key2865, 2), (key2626, 2), (key2635, 2), (key2626, 2), (key2853, 2), (key2855, 2), (key2700, 2), (key2855, 2), (key2700, 2), (key2853, 2), (key2865, 2), (key2721, 2), (key2865, 2), (key2626, 2), (key2635, 2), (key2610, 2), (key2635, 2), (key2610, 2), (key2626, 2), (key2780, 2), (key2789, 2), (key2665, 2), (key2789, 2), (key2665, 2), (key2780, 2), (key2803, 2), (key2855, 2), (key2700, 2), (key2855, 2), (key2700, 2), (key2803, 2), (key2824, 2), (key2865, 2), (key2721, 2), (key2865, 2), (key2721, 2), (key2824, 2), (key2626, 2), (key2610, 2), (key2626, 2), (key2780, 2), (key2665, 2), (key2780, 2), (key2803, 2), (key2853, 2), (key2700, 2), (key2853, 2), (key2700, 2), (key2803, 2)]

theorem rawRowCheck19128 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form2 = rawRow19128 := by decide +kernel

def row19128 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

theorem rowCheck19128 : row19128 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19128 := by decide +kernel

theorem rowEval19128 (x : Key → ℝ) : Integer.Sparse.eval row19128 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19128, Integer.Sparse.eval_collectBalanced, rawRowCheck19128]

def rawRow19129 : Integer.Sparse Key := [(key2789, 2), (key2780, 2), (key2780, 2), (key2855, 2), (key2853, 2), (key2855, 2), (key2803, 2), (key2853, 2), (key2803, 2), (key2865, 2), (key2865, 2), (key2824, 2), (key2635, 2), (key2626, 2), (key2626, 2), (key2855, 2), (key2853, 2), (key2855, 2), (key2700, 2), (key2853, 2), (key2700, 2), (key2865, 2), (key2865, 2), (key2721, 2), (key2635, 2), (key2626, 2), (key2635, 2), (key2610, 2), (key2626, 2), (key2610, 2), (key2789, 2), (key2780, 2), (key2789, 2), (key2665, 2), (key2780, 2), (key2665, 2), (key2855, 2), (key2803, 2), (key2855, 2), (key2700, 2), (key2803, 2), (key2700, 2), (key2865, 2), (key2824, 2), (key2865, 2), (key2721, 2), (key2824, 2), (key2721, 2), (key2626, 2), (key2626, 2), (key2610, 2), (key2780, 2), (key2780, 2), (key2665, 2), (key2853, 2), (key2803, 2), (key2853, 2), (key2700, 2), (key2803, 2), (key2700, 2)]

theorem rawRowCheck19129 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form2 = rawRow19129 := by decide +kernel

def row19129 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

theorem rowCheck19129 : row19129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19129 := by decide +kernel

theorem rowEval19129 (x : Key → ℝ) : Integer.Sparse.eval row19129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck19129, Integer.Sparse.eval_collectBalanced, rawRowCheck19129]

def rawRow19130 : Integer.Sparse Key := [(key2803, 2), (key2803, 2), (key2824, 2), (key2780, 2), (key2780, 2), (key2853, 2), (key2853, 2), (key2865, 2), (key2865, 2), (key2789, 2), (key2855, 2), (key2855, 2), (key2700, 2), (key2700, 2), (key2721, 2), (key2626, 2), (key2626, 2), (key2853, 2), (key2853, 2), (key2865, 2), (key2865, 2), (key2635, 2), (key2855, 2), (key2855, 2), (key2665, 2), (key2665, 2), (key2700, 2), (key2700, 2), (key2721, 2), (key2721, 2), (key2610, 2), (key2610, 2), (key2803, 2), (key2803, 2), (key2824, 2), (key2824, 2), (key2626, 2), (key2626, 2), (key2780, 2), (key2780, 2), (key2865, 2), (key2865, 2), (key2635, 2), (key2635, 2), (key2789, 2), (key2789, 2), (key2855, 2), (key2855, 2), (key2665, 2), (key2700, 2), (key2700, 2), (key2610, 2), (key2803, 2), (key2803, 2), (key2626, 2), (key2626, 2), (key2780, 2), (key2780, 2), (key2853, 2), (key2853, 2)]

theorem rawRowCheck19130 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form2 = rawRow19130 := by decide +kernel

def row19130 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

theorem rowCheck19130 : row19130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19130 := by decide +kernel

theorem rowEval19130 (x : Key → ℝ) : Integer.Sparse.eval row19130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19130, Integer.Sparse.eval_collectBalanced, rawRowCheck19130]

def rawRow19131 : Integer.Sparse Key := [(key2803, 2), (key2824, 2), (key2803, 2), (key2853, 2), (key2865, 2), (key2780, 2), (key2865, 2), (key2780, 2), (key2853, 2), (key2855, 2), (key2789, 2), (key2855, 2), (key2700, 2), (key2721, 2), (key2700, 2), (key2853, 2), (key2865, 2), (key2626, 2), (key2865, 2), (key2626, 2), (key2853, 2), (key2855, 2), (key2635, 2), (key2855, 2), (key2700, 2), (key2721, 2), (key2665, 2), (key2721, 2), (key2665, 2), (key2700, 2), (key2803, 2), (key2824, 2), (key2610, 2), (key2824, 2), (key2610, 2), (key2803, 2), (key2780, 2), (key2865, 2), (key2626, 2), (key2865, 2), (key2626, 2), (key2780, 2), (key2789, 2), (key2855, 2), (key2635, 2), (key2855, 2), (key2635, 2), (key2789, 2), (key2700, 2), (key2665, 2), (key2700, 2), (key2803, 2), (key2610, 2), (key2803, 2), (key2780, 2), (key2853, 2), (key2626, 2), (key2853, 2), (key2626, 2), (key2780, 2)]

theorem rawRowCheck19131 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form2 = rawRow19131 := by decide +kernel

def row19131 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

theorem rowCheck19131 : row19131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19131 := by decide +kernel

theorem rowEval19131 (x : Key → ℝ) : Integer.Sparse.eval row19131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19131, Integer.Sparse.eval_collectBalanced, rawRowCheck19131]

def rawRow19132 : Integer.Sparse Key := [(key2824, 2), (key2803, 2), (key2803, 2), (key2865, 2), (key2853, 2), (key2865, 2), (key2780, 2), (key2853, 2), (key2780, 2), (key2855, 2), (key2855, 2), (key2789, 2), (key2721, 2), (key2700, 2), (key2700, 2), (key2865, 2), (key2853, 2), (key2865, 2), (key2626, 2), (key2853, 2), (key2626, 2), (key2855, 2), (key2855, 2), (key2635, 2), (key2721, 2), (key2700, 2), (key2721, 2), (key2665, 2), (key2700, 2), (key2665, 2), (key2824, 2), (key2803, 2), (key2824, 2), (key2610, 2), (key2803, 2), (key2610, 2), (key2865, 2), (key2780, 2), (key2865, 2), (key2626, 2), (key2780, 2), (key2626, 2), (key2855, 2), (key2789, 2), (key2855, 2), (key2635, 2), (key2789, 2), (key2635, 2), (key2700, 2), (key2700, 2), (key2665, 2), (key2803, 2), (key2803, 2), (key2610, 2), (key2853, 2), (key2780, 2), (key2853, 2), (key2626, 2), (key2780, 2), (key2626, 2)]

theorem rawRowCheck19132 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form2 = rawRow19132 := by decide +kernel

def row19132 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

theorem rowCheck19132 : row19132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19132 := by decide +kernel

theorem rowEval19132 (x : Key → ℝ) : Integer.Sparse.eval row19132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19132, Integer.Sparse.eval_collectBalanced, rawRowCheck19132]

def rawRow19133 : Integer.Sparse Key := [(key2853, 2), (key2855, 2), (key2865, 2), (key2780, 2), (key2789, 2), (key2803, 2), (key2855, 2), (key2824, 2), (key2865, 2), (key2780, 2), (key2803, 2), (key2853, 2), (key2853, 2), (key2855, 2), (key2865, 2), (key2626, 2), (key2635, 2), (key2700, 2), (key2855, 2), (key2721, 2), (key2865, 2), (key2626, 2), (key2700, 2), (key2853, 2), (key2780, 2), (key2789, 2), (key2803, 2), (key2855, 2), (key2824, 2), (key2865, 2), (key2626, 2), (key2635, 2), (key2700, 2), (key2855, 2), (key2721, 2), (key2865, 2), (key2610, 2), (key2635, 2), (key2665, 2), (key2789, 2), (key2721, 2), (key2824, 2), (key2610, 2), (key2626, 2), (key2665, 2), (key2780, 2), (key2700, 2), (key2803, 2), (key2780, 2), (key2803, 2), (key2853, 2), (key2626, 2), (key2700, 2), (key2853, 2), (key2610, 2), (key2626, 2), (key2665, 2), (key2780, 2), (key2700, 2), (key2803, 2)]

theorem rawRowCheck19133 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form2 = rawRow19133 := by decide +kernel

def row19133 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

theorem rowCheck19133 : row19133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19133 := by decide +kernel

theorem rowEval19133 (x : Key → ℝ) : Integer.Sparse.eval row19133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19133, Integer.Sparse.eval_collectBalanced, rawRowCheck19133]

def rawRow19134 : Integer.Sparse Key := [(key2855, 2), (key2853, 2), (key2865, 2), (key2789, 2), (key2780, 2), (key2855, 2), (key2803, 2), (key2865, 2), (key2824, 2), (key2780, 2), (key2853, 2), (key2803, 2), (key2855, 2), (key2853, 2), (key2865, 2), (key2635, 2), (key2626, 2), (key2855, 2), (key2700, 2), (key2865, 2), (key2721, 2), (key2626, 2), (key2853, 2), (key2700, 2), (key2789, 2), (key2780, 2), (key2855, 2), (key2803, 2), (key2865, 2), (key2824, 2), (key2635, 2), (key2626, 2), (key2855, 2), (key2700, 2), (key2865, 2), (key2721, 2), (key2635, 2), (key2610, 2), (key2789, 2), (key2665, 2), (key2824, 2), (key2721, 2), (key2626, 2), (key2610, 2), (key2780, 2), (key2665, 2), (key2803, 2), (key2700, 2), (key2780, 2), (key2853, 2), (key2803, 2), (key2626, 2), (key2853, 2), (key2700, 2), (key2626, 2), (key2610, 2), (key2780, 2), (key2665, 2), (key2803, 2), (key2700, 2)]

theorem rawRowCheck19134 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form2 = rawRow19134 := by decide +kernel

def row19134 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

theorem rowCheck19134 : row19134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19134 := by decide +kernel

theorem rowEval19134 (x : Key → ℝ) : Integer.Sparse.eval row19134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck19134, Integer.Sparse.eval_collectBalanced, rawRowCheck19134]

def rawRow19135 : Integer.Sparse Key := [(key2853, 2), (key2865, 2), (key2855, 2), (key2803, 2), (key2824, 2), (key2780, 2), (key2865, 2), (key2789, 2), (key2855, 2), (key2803, 2), (key2780, 2), (key2853, 2), (key2853, 2), (key2865, 2), (key2855, 2), (key2700, 2), (key2721, 2), (key2626, 2), (key2865, 2), (key2635, 2), (key2855, 2), (key2700, 2), (key2626, 2), (key2853, 2), (key2803, 2), (key2824, 2), (key2780, 2), (key2865, 2), (key2789, 2), (key2855, 2), (key2700, 2), (key2721, 2), (key2626, 2), (key2865, 2), (key2635, 2), (key2855, 2), (key2665, 2), (key2721, 2), (key2610, 2), (key2824, 2), (key2635, 2), (key2789, 2), (key2665, 2), (key2700, 2), (key2610, 2), (key2803, 2), (key2626, 2), (key2780, 2), (key2803, 2), (key2780, 2), (key2853, 2), (key2700, 2), (key2626, 2), (key2853, 2), (key2665, 2), (key2700, 2), (key2610, 2), (key2803, 2), (key2626, 2), (key2780, 2)]

theorem rawRowCheck19135 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form2 = rawRow19135 := by decide +kernel

def row19135 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

theorem rowCheck19135 : row19135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19135 := by decide +kernel

theorem rowEval19135 (x : Key → ℝ) : Integer.Sparse.eval row19135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19135, Integer.Sparse.eval_collectBalanced, rawRowCheck19135]

def rawRow19136 : Integer.Sparse Key := [(key2865, 2), (key2853, 2), (key2855, 2), (key2824, 2), (key2803, 2), (key2865, 2), (key2780, 2), (key2855, 2), (key2789, 2), (key2803, 2), (key2853, 2), (key2780, 2), (key2865, 2), (key2853, 2), (key2855, 2), (key2721, 2), (key2700, 2), (key2865, 2), (key2626, 2), (key2855, 2), (key2635, 2), (key2700, 2), (key2853, 2), (key2626, 2), (key2824, 2), (key2803, 2), (key2865, 2), (key2780, 2), (key2855, 2), (key2789, 2), (key2721, 2), (key2700, 2), (key2865, 2), (key2626, 2), (key2855, 2), (key2635, 2), (key2721, 2), (key2665, 2), (key2824, 2), (key2610, 2), (key2789, 2), (key2635, 2), (key2700, 2), (key2665, 2), (key2803, 2), (key2610, 2), (key2780, 2), (key2626, 2), (key2803, 2), (key2853, 2), (key2780, 2), (key2700, 2), (key2853, 2), (key2626, 2), (key2700, 2), (key2665, 2), (key2803, 2), (key2610, 2), (key2780, 2), (key2626, 2)]

theorem rawRowCheck19136 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form2 = rawRow19136 := by decide +kernel

def row19136 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

theorem rowCheck19136 : row19136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19136 := by decide +kernel

theorem rowEval19136 (x : Key → ℝ) : Integer.Sparse.eval row19136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19136, Integer.Sparse.eval_collectBalanced, rawRowCheck19136]

def rawRow19137 : Integer.Sparse Key := [(key2855, 2), (key2865, 2), (key2853, 2), (key2855, 2), (key2865, 2), (key2789, 2), (key2824, 2), (key2780, 2), (key2803, 2), (key2853, 2), (key2780, 2), (key2803, 2), (key2855, 2), (key2865, 2), (key2853, 2), (key2855, 2), (key2865, 2), (key2635, 2), (key2721, 2), (key2626, 2), (key2700, 2), (key2853, 2), (key2626, 2), (key2700, 2), (key2855, 2), (key2865, 2), (key2789, 2), (key2824, 2), (key2780, 2), (key2803, 2), (key2855, 2), (key2865, 2), (key2635, 2), (key2721, 2), (key2626, 2), (key2700, 2), (key2789, 2), (key2824, 2), (key2635, 2), (key2721, 2), (key2610, 2), (key2665, 2), (key2780, 2), (key2803, 2), (key2626, 2), (key2700, 2), (key2610, 2), (key2665, 2), (key2853, 2), (key2780, 2), (key2803, 2), (key2853, 2), (key2626, 2), (key2700, 2), (key2780, 2), (key2803, 2), (key2626, 2), (key2700, 2), (key2610, 2), (key2665, 2)]

theorem rawRowCheck19137 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form2 = rawRow19137 := by decide +kernel

def row19137 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

theorem rowCheck19137 : row19137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19137 := by decide +kernel

theorem rowEval19137 (x : Key → ℝ) : Integer.Sparse.eval row19137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck19137, Integer.Sparse.eval_collectBalanced, rawRowCheck19137]

def rawRow19138 : Integer.Sparse Key := [(key2865, 2), (key2855, 2), (key2853, 2), (key2865, 2), (key2855, 2), (key2824, 2), (key2789, 2), (key2803, 2), (key2780, 2), (key2853, 2), (key2803, 2), (key2780, 2), (key2865, 2), (key2855, 2), (key2853, 2), (key2865, 2), (key2855, 2), (key2721, 2), (key2635, 2), (key2700, 2), (key2626, 2), (key2853, 2), (key2700, 2), (key2626, 2), (key2865, 2), (key2855, 2), (key2824, 2), (key2789, 2), (key2803, 2), (key2780, 2), (key2865, 2), (key2855, 2), (key2721, 2), (key2635, 2), (key2700, 2), (key2626, 2), (key2824, 2), (key2789, 2), (key2721, 2), (key2635, 2), (key2665, 2), (key2610, 2), (key2803, 2), (key2780, 2), (key2700, 2), (key2626, 2), (key2665, 2), (key2610, 2), (key2853, 2), (key2803, 2), (key2780, 2), (key2853, 2), (key2700, 2), (key2626, 2), (key2803, 2), (key2780, 2), (key2700, 2), (key2626, 2), (key2665, 2), (key2610, 2)]

theorem rawRowCheck19138 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form2 = rawRow19138 := by decide +kernel

def row19138 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

theorem rowCheck19138 : row19138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19138 := by decide +kernel

theorem rowEval19138 (x : Key → ℝ) : Integer.Sparse.eval row19138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19138, Integer.Sparse.eval_collectBalanced, rawRowCheck19138]

def rawRow19139 : Integer.Sparse Key := [(key2368, 24), (key2760, 24), (key2837, 24), (key2837, 24), (key2837, 24)]

theorem rawRowCheck19139 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form3 = rawRow19139 := by decide +kernel

def row19139 : Integer.Sparse Key := [(key2368, 24), (key2760, 24), (key2837, 72)]

theorem rowCheck19139 : row19139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19139 := by decide +kernel

theorem rowEval19139 (x : Key → ℝ) : Integer.Sparse.eval row19139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19139, Integer.Sparse.eval_collectBalanced, rawRowCheck19139]

def rawRow19140 : Integer.Sparse Key := [(key2368, 24), (key2837, 24), (key2760, 24), (key2837, 24), (key2837, 24)]

theorem rawRowCheck19140 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form3 = rawRow19140 := by decide +kernel

def row19140 : Integer.Sparse Key := [(key2368, 24), (key2760, 24), (key2837, 72)]

theorem rowCheck19140 : row19140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19140 := by decide +kernel

theorem rowEval19140 (x : Key → ℝ) : Integer.Sparse.eval row19140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19140, Integer.Sparse.eval_collectBalanced, rawRowCheck19140]

def rawRow19141 : Integer.Sparse Key := [(key2368, 24), (key2837, 24), (key2837, 24), (key2760, 24), (key2837, 24)]

theorem rawRowCheck19141 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form3 = rawRow19141 := by decide +kernel

def row19141 : Integer.Sparse Key := [(key2368, 24), (key2760, 24), (key2837, 72)]

theorem rowCheck19141 : row19141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19141 := by decide +kernel

theorem rowEval19141 (x : Key → ℝ) : Integer.Sparse.eval row19141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19141, Integer.Sparse.eval_collectBalanced, rawRowCheck19141]

def rawRow19142 : Integer.Sparse Key := [(key2368, 24), (key2837, 24), (key2837, 24), (key2837, 24), (key2760, 24)]

theorem rawRowCheck19142 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form3 = rawRow19142 := by decide +kernel

def row19142 : Integer.Sparse Key := [(key2368, 24), (key2760, 24), (key2837, 72)]

theorem rowCheck19142 : row19142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19142 := by decide +kernel

theorem rowEval19142 (x : Key → ℝ) : Integer.Sparse.eval row19142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19142, Integer.Sparse.eval_collectBalanced, rawRowCheck19142]

def rawRow19143 : Integer.Sparse Key := [(key2396, 24), (key2581, 24), (key2837, 24), (key2837, 24), (key2837, 24)]

theorem rawRowCheck19143 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form3 = rawRow19143 := by decide +kernel

def row19143 : Integer.Sparse Key := [(key2396, 24), (key2581, 24), (key2837, 72)]

theorem rowCheck19143 : row19143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19143 := by decide +kernel

theorem rowEval19143 (x : Key → ℝ) : Integer.Sparse.eval row19143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19143, Integer.Sparse.eval_collectBalanced, rawRowCheck19143]

def rawRow19144 : Integer.Sparse Key := [(key2396, 24), (key2837, 24), (key2581, 24), (key2837, 24), (key2837, 24)]

theorem rawRowCheck19144 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form3 = rawRow19144 := by decide +kernel

def row19144 : Integer.Sparse Key := [(key2396, 24), (key2581, 24), (key2837, 72)]

theorem rowCheck19144 : row19144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19144 := by decide +kernel

theorem rowEval19144 (x : Key → ℝ) : Integer.Sparse.eval row19144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19144, Integer.Sparse.eval_collectBalanced, rawRowCheck19144]

def rawRow19145 : Integer.Sparse Key := [(key2396, 24), (key2837, 24), (key2837, 24), (key2581, 24), (key2837, 24)]

theorem rawRowCheck19145 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form3 = rawRow19145 := by decide +kernel

def row19145 : Integer.Sparse Key := [(key2396, 24), (key2581, 24), (key2837, 72)]

theorem rowCheck19145 : row19145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19145 := by decide +kernel

theorem rowEval19145 (x : Key → ℝ) : Integer.Sparse.eval row19145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19145, Integer.Sparse.eval_collectBalanced, rawRowCheck19145]

def rawRow19146 : Integer.Sparse Key := [(key2396, 24), (key2837, 24), (key2837, 24), (key2837, 24), (key2581, 24)]

theorem rawRowCheck19146 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form3 = rawRow19146 := by decide +kernel

def row19146 : Integer.Sparse Key := [(key2396, 24), (key2581, 24), (key2837, 72)]

theorem rowCheck19146 : row19146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19146 := by decide +kernel

theorem rowEval19146 (x : Key → ℝ) : Integer.Sparse.eval row19146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19146, Integer.Sparse.eval_collectBalanced, rawRowCheck19146]

def rawRow19147 : Integer.Sparse Key := [(key2462, 24), (key2368, 24), (key2760, 24), (key2837, 24), (key2837, 24)]

theorem rawRowCheck19147 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form3 = rawRow19147 := by decide +kernel

def row19147 : Integer.Sparse Key := [(key2368, 24), (key2462, 24), (key2760, 24), (key2837, 48)]

theorem rowCheck19147 : row19147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19147 := by decide +kernel

theorem rowEval19147 (x : Key → ℝ) : Integer.Sparse.eval row19147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19147, Integer.Sparse.eval_collectBalanced, rawRowCheck19147]

def rawRow19148 : Integer.Sparse Key := [(key2462, 24), (key2368, 24), (key2837, 24), (key2760, 24), (key2837, 24)]

theorem rawRowCheck19148 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form3 = rawRow19148 := by decide +kernel

def row19148 : Integer.Sparse Key := [(key2368, 24), (key2462, 24), (key2760, 24), (key2837, 48)]

theorem rowCheck19148 : row19148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19148 := by decide +kernel

theorem rowEval19148 (x : Key → ℝ) : Integer.Sparse.eval row19148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19148, Integer.Sparse.eval_collectBalanced, rawRowCheck19148]

def rawRow19149 : Integer.Sparse Key := [(key2462, 24), (key2368, 24), (key2837, 24), (key2837, 24), (key2760, 24)]

theorem rawRowCheck19149 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form3 = rawRow19149 := by decide +kernel

def row19149 : Integer.Sparse Key := [(key2368, 24), (key2462, 24), (key2760, 24), (key2837, 48)]

theorem rowCheck19149 : row19149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19149 := by decide +kernel

theorem rowEval19149 (x : Key → ℝ) : Integer.Sparse.eval row19149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19149, Integer.Sparse.eval_collectBalanced, rawRowCheck19149]

def rawRow19150 : Integer.Sparse Key := [(key2462, 24), (key2396, 24), (key2581, 24), (key2837, 24), (key2837, 24)]

theorem rawRowCheck19150 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form3 = rawRow19150 := by decide +kernel

def row19150 : Integer.Sparse Key := [(key2396, 24), (key2462, 24), (key2581, 24), (key2837, 48)]

theorem rowCheck19150 : row19150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19150 := by decide +kernel

theorem rowEval19150 (x : Key → ℝ) : Integer.Sparse.eval row19150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19150, Integer.Sparse.eval_collectBalanced, rawRowCheck19150]

def rawRow19151 : Integer.Sparse Key := [(key2462, 24), (key2396, 24), (key2837, 24), (key2581, 24), (key2837, 24)]

theorem rawRowCheck19151 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form3 = rawRow19151 := by decide +kernel

def row19151 : Integer.Sparse Key := [(key2396, 24), (key2462, 24), (key2581, 24), (key2837, 48)]

theorem rowCheck19151 : row19151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19151 := by decide +kernel

theorem rowEval19151 (x : Key → ℝ) : Integer.Sparse.eval row19151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19151, Integer.Sparse.eval_collectBalanced, rawRowCheck19151]

def rawRow19152 : Integer.Sparse Key := [(key2462, 24), (key2396, 24), (key2837, 24), (key2837, 24), (key2581, 24)]

theorem rawRowCheck19152 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form3 = rawRow19152 := by decide +kernel

def row19152 : Integer.Sparse Key := [(key2396, 24), (key2462, 24), (key2581, 24), (key2837, 48)]

theorem rowCheck19152 : row19152 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19152 := by decide +kernel

theorem rowEval19152 (x : Key → ℝ) : Integer.Sparse.eval row19152 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19152, Integer.Sparse.eval_collectBalanced, rawRowCheck19152]

def rawRow19153 : Integer.Sparse Key := [(key2462, 24), (key2462, 24), (key2368, 24), (key2760, 24), (key2837, 24)]

theorem rawRowCheck19153 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form3 = rawRow19153 := by decide +kernel

def row19153 : Integer.Sparse Key := [(key2368, 24), (key2462, 48), (key2760, 24), (key2837, 24)]

theorem rowCheck19153 : row19153 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19153 := by decide +kernel

theorem rowEval19153 (x : Key → ℝ) : Integer.Sparse.eval row19153 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19153, Integer.Sparse.eval_collectBalanced, rawRowCheck19153]

def rawRow19154 : Integer.Sparse Key := [(key2462, 24), (key2462, 24), (key2368, 24), (key2837, 24), (key2760, 24)]

theorem rawRowCheck19154 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form3 = rawRow19154 := by decide +kernel

def row19154 : Integer.Sparse Key := [(key2368, 24), (key2462, 48), (key2760, 24), (key2837, 24)]

theorem rowCheck19154 : row19154 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19154 := by decide +kernel

theorem rowEval19154 (x : Key → ℝ) : Integer.Sparse.eval row19154 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19154, Integer.Sparse.eval_collectBalanced, rawRowCheck19154]

def rawRow19155 : Integer.Sparse Key := [(key2462, 24), (key2462, 24), (key2396, 24), (key2581, 24), (key2837, 24)]

theorem rawRowCheck19155 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form3 = rawRow19155 := by decide +kernel

def row19155 : Integer.Sparse Key := [(key2396, 24), (key2462, 48), (key2581, 24), (key2837, 24)]

theorem rowCheck19155 : row19155 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19155 := by decide +kernel

theorem rowEval19155 (x : Key → ℝ) : Integer.Sparse.eval row19155 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19155, Integer.Sparse.eval_collectBalanced, rawRowCheck19155]

def rawRow19156 : Integer.Sparse Key := [(key2462, 24), (key2462, 24), (key2396, 24), (key2837, 24), (key2581, 24)]

theorem rawRowCheck19156 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form3 = rawRow19156 := by decide +kernel

def row19156 : Integer.Sparse Key := [(key2396, 24), (key2462, 48), (key2581, 24), (key2837, 24)]

theorem rowCheck19156 : row19156 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19156 := by decide +kernel

theorem rowEval19156 (x : Key → ℝ) : Integer.Sparse.eval row19156 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19156, Integer.Sparse.eval_collectBalanced, rawRowCheck19156]

def rawRow19157 : Integer.Sparse Key := [(key2462, 24), (key2462, 24), (key2462, 24), (key2368, 24), (key2760, 24)]

theorem rawRowCheck19157 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form3 = rawRow19157 := by decide +kernel

def row19157 : Integer.Sparse Key := [(key2368, 24), (key2462, 72), (key2760, 24)]

theorem rowCheck19157 : row19157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19157 := by decide +kernel

theorem rowEval19157 (x : Key → ℝ) : Integer.Sparse.eval row19157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19157, Integer.Sparse.eval_collectBalanced, rawRowCheck19157]

def rawRow19158 : Integer.Sparse Key := [(key2462, 24), (key2462, 24), (key2462, 24), (key2396, 24), (key2581, 24)]

theorem rawRowCheck19158 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form3 = rawRow19158 := by decide +kernel

def row19158 : Integer.Sparse Key := [(key2396, 24), (key2462, 72), (key2581, 24)]

theorem rowCheck19158 : row19158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19158 := by decide +kernel

theorem rowEval19158 (x : Key → ℝ) : Integer.Sparse.eval row19158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19158, Integer.Sparse.eval_collectBalanced, rawRowCheck19158]

def rawRow19159 : Integer.Sparse Key := [(key995, 6), (key995, 6), (key995, 6), (key1011, 6), (key1030, 6), (key1030, 6), (key1030, 6), (key1108, 6), (key1108, 6), (key1108, 6), (key1108, 6), (key1108, 6), (key1108, 6), (key1119, 6), (key1119, 6), (key1119, 6), (key1067, 6), (key1146, 6), (key1146, 6), (key1146, 6)]

theorem rawRowCheck19159 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form4 = rawRow19159 := by decide +kernel

def row19159 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

theorem rowCheck19159 : row19159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19159 := by decide +kernel

theorem rowEval19159 (x : Key → ℝ) : Integer.Sparse.eval row19159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19159, Integer.Sparse.eval_collectBalanced, rawRowCheck19159]

def rawRow19160 : Integer.Sparse Key := [(key995, 6), (key995, 6), (key1011, 6), (key995, 6), (key1108, 6), (key1108, 6), (key1119, 6), (key1030, 6), (key1030, 6), (key1108, 6), (key1108, 6), (key1119, 6), (key1119, 6), (key1030, 6), (key1108, 6), (key1108, 6), (key1146, 6), (key1067, 6), (key1146, 6), (key1146, 6)]

theorem rawRowCheck19160 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form4 = rawRow19160 := by decide +kernel

def row19160 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

theorem rowCheck19160 : row19160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19160 := by decide +kernel

theorem rowEval19160 (x : Key → ℝ) : Integer.Sparse.eval row19160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19160, Integer.Sparse.eval_collectBalanced, rawRowCheck19160]

def rawRow19161 : Integer.Sparse Key := [(key995, 6), (key1011, 6), (key995, 6), (key995, 6), (key1108, 6), (key1119, 6), (key1108, 6), (key1108, 6), (key1119, 6), (key1030, 6), (key1119, 6), (key1030, 6), (key1108, 6), (key1108, 6), (key1030, 6), (key1108, 6), (key1146, 6), (key1146, 6), (key1067, 6), (key1146, 6)]

theorem rawRowCheck19161 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form4 = rawRow19161 := by decide +kernel

def row19161 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

theorem rowCheck19161 : row19161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19161 := by decide +kernel

theorem rowEval19161 (x : Key → ℝ) : Integer.Sparse.eval row19161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19161, Integer.Sparse.eval_collectBalanced, rawRowCheck19161]

def rawRow19162 : Integer.Sparse Key := [(key1011, 6), (key995, 6), (key995, 6), (key995, 6), (key1119, 6), (key1108, 6), (key1108, 6), (key1119, 6), (key1108, 6), (key1119, 6), (key1030, 6), (key1108, 6), (key1030, 6), (key1108, 6), (key1108, 6), (key1030, 6), (key1146, 6), (key1146, 6), (key1146, 6), (key1067, 6)]

theorem rawRowCheck19162 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form4 = rawRow19162 := by decide +kernel

def row19162 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

theorem rowCheck19162 : row19162 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19162 := by decide +kernel

theorem rowEval19162 (x : Key → ℝ) : Integer.Sparse.eval row19162 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19162, Integer.Sparse.eval_collectBalanced, rawRowCheck19162]

def rawRow19163 : Integer.Sparse Key := [(key1030, 6), (key1030, 6), (key1030, 6), (key1067, 6), (key995, 6), (key995, 6), (key995, 6), (key1108, 6), (key1108, 6), (key1108, 6), (key1108, 6), (key1108, 6), (key1108, 6), (key1146, 6), (key1146, 6), (key1146, 6), (key1011, 6), (key1119, 6), (key1119, 6), (key1119, 6)]

theorem rawRowCheck19163 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form4 = rawRow19163 := by decide +kernel

def row19163 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

theorem rowCheck19163 : row19163 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19163 := by decide +kernel

theorem rowEval19163 (x : Key → ℝ) : Integer.Sparse.eval row19163 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19163, Integer.Sparse.eval_collectBalanced, rawRowCheck19163]

def rawRow19164 : Integer.Sparse Key := [(key1030, 6), (key1030, 6), (key1067, 6), (key1030, 6), (key1108, 6), (key1108, 6), (key1146, 6), (key995, 6), (key995, 6), (key1108, 6), (key1108, 6), (key1146, 6), (key1146, 6), (key995, 6), (key1108, 6), (key1108, 6), (key1119, 6), (key1011, 6), (key1119, 6), (key1119, 6)]

theorem rawRowCheck19164 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form4 = rawRow19164 := by decide +kernel

def row19164 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

theorem rowCheck19164 : row19164 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19164 := by decide +kernel

theorem rowEval19164 (x : Key → ℝ) : Integer.Sparse.eval row19164 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19164, Integer.Sparse.eval_collectBalanced, rawRowCheck19164]

def rawRow19165 : Integer.Sparse Key := [(key1030, 6), (key1067, 6), (key1030, 6), (key1030, 6), (key1108, 6), (key1146, 6), (key1108, 6), (key1108, 6), (key1146, 6), (key995, 6), (key1146, 6), (key995, 6), (key1108, 6), (key1108, 6), (key995, 6), (key1108, 6), (key1119, 6), (key1119, 6), (key1011, 6), (key1119, 6)]

theorem rawRowCheck19165 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form4 = rawRow19165 := by decide +kernel

def row19165 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

theorem rowCheck19165 : row19165 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19165 := by decide +kernel

theorem rowEval19165 (x : Key → ℝ) : Integer.Sparse.eval row19165 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19165, Integer.Sparse.eval_collectBalanced, rawRowCheck19165]

def rawRow19166 : Integer.Sparse Key := [(key1067, 6), (key1030, 6), (key1030, 6), (key1030, 6), (key1146, 6), (key1108, 6), (key1108, 6), (key1146, 6), (key1108, 6), (key1146, 6), (key995, 6), (key1108, 6), (key995, 6), (key1108, 6), (key1108, 6), (key995, 6), (key1119, 6), (key1119, 6), (key1119, 6), (key1011, 6)]

theorem rawRowCheck19166 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form4 = rawRow19166 := by decide +kernel

def row19166 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

theorem rowCheck19166 : row19166 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19166 := by decide +kernel

theorem rowEval19166 (x : Key → ℝ) : Integer.Sparse.eval row19166 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19166, Integer.Sparse.eval_collectBalanced, rawRowCheck19166]

def rawRow19167 : Integer.Sparse Key := [(key1108, 6), (key1108, 6), (key1119, 6), (key1146, 6), (key995, 6), (key995, 6), (key1011, 6), (key1030, 6), (key1030, 6), (key1108, 6), (key1108, 6), (key1119, 6), (key1119, 6), (key1067, 6), (key1146, 6), (key1146, 6), (key995, 6), (key1030, 6), (key1108, 6), (key1108, 6)]

theorem rawRowCheck19167 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form4 = rawRow19167 := by decide +kernel

def row19167 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

theorem rowCheck19167 : row19167 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19167 := by decide +kernel

theorem rowEval19167 (x : Key → ℝ) : Integer.Sparse.eval row19167 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19167, Integer.Sparse.eval_collectBalanced, rawRowCheck19167]

def rawRow19168 : Integer.Sparse Key := [(key1108, 6), (key1119, 6), (key1108, 6), (key1146, 6), (key995, 6), (key1011, 6), (key995, 6), (key1108, 6), (key1119, 6), (key1030, 6), (key1119, 6), (key1030, 6), (key1108, 6), (key1146, 6), (key1067, 6), (key1146, 6), (key995, 6), (key1108, 6), (key1030, 6), (key1108, 6)]

theorem rawRowCheck19168 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form4 = rawRow19168 := by decide +kernel

def row19168 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

theorem rowCheck19168 : row19168 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19168 := by decide +kernel

theorem rowEval19168 (x : Key → ℝ) : Integer.Sparse.eval row19168 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19168, Integer.Sparse.eval_collectBalanced, rawRowCheck19168]

def rawRow19169 : Integer.Sparse Key := [(key1119, 6), (key1108, 6), (key1108, 6), (key1146, 6), (key1011, 6), (key995, 6), (key995, 6), (key1119, 6), (key1108, 6), (key1119, 6), (key1030, 6), (key1108, 6), (key1030, 6), (key1146, 6), (key1146, 6), (key1067, 6), (key995, 6), (key1108, 6), (key1108, 6), (key1030, 6)]

theorem rawRowCheck19169 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form4 = rawRow19169 := by decide +kernel

def row19169 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

theorem rowCheck19169 : row19169 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19169 := by decide +kernel

theorem rowEval19169 (x : Key → ℝ) : Integer.Sparse.eval row19169 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19169, Integer.Sparse.eval_collectBalanced, rawRowCheck19169]

def rawRow19170 : Integer.Sparse Key := [(key1108, 6), (key1108, 6), (key1146, 6), (key1119, 6), (key1030, 6), (key1030, 6), (key1067, 6), (key995, 6), (key995, 6), (key1108, 6), (key1108, 6), (key1146, 6), (key1146, 6), (key1011, 6), (key1119, 6), (key1119, 6), (key1030, 6), (key995, 6), (key1108, 6), (key1108, 6)]

theorem rawRowCheck19170 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form4 = rawRow19170 := by decide +kernel

def row19170 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

theorem rowCheck19170 : row19170 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19170 := by decide +kernel

theorem rowEval19170 (x : Key → ℝ) : Integer.Sparse.eval row19170 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19170, Integer.Sparse.eval_collectBalanced, rawRowCheck19170]

def rawRow19171 : Integer.Sparse Key := [(key1108, 6), (key1146, 6), (key1108, 6), (key1119, 6), (key1030, 6), (key1067, 6), (key1030, 6), (key1108, 6), (key1146, 6), (key995, 6), (key1146, 6), (key995, 6), (key1108, 6), (key1119, 6), (key1011, 6), (key1119, 6), (key1030, 6), (key1108, 6), (key995, 6), (key1108, 6)]

theorem rawRowCheck19171 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form4 = rawRow19171 := by decide +kernel

def row19171 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

theorem rowCheck19171 : row19171 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19171 := by decide +kernel

theorem rowEval19171 (x : Key → ℝ) : Integer.Sparse.eval row19171 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19171, Integer.Sparse.eval_collectBalanced, rawRowCheck19171]

def rawRow19172 : Integer.Sparse Key := [(key1146, 6), (key1108, 6), (key1108, 6), (key1119, 6), (key1067, 6), (key1030, 6), (key1030, 6), (key1146, 6), (key1108, 6), (key1146, 6), (key995, 6), (key1108, 6), (key995, 6), (key1119, 6), (key1119, 6), (key1011, 6), (key1030, 6), (key1108, 6), (key1108, 6), (key995, 6)]

theorem rawRowCheck19172 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form4 = rawRow19172 := by decide +kernel

def row19172 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

theorem rowCheck19172 : row19172 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19172 := by decide +kernel

theorem rowEval19172 (x : Key → ℝ) : Integer.Sparse.eval row19172 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19172, Integer.Sparse.eval_collectBalanced, rawRowCheck19172]

def rawRow19173 : Integer.Sparse Key := [(key1108, 6), (key1119, 6), (key1146, 6), (key1108, 6), (key1108, 6), (key1119, 6), (key1146, 6), (key995, 6), (key1011, 6), (key1030, 6), (key1119, 6), (key1067, 6), (key1146, 6), (key995, 6), (key1030, 6), (key1108, 6), (key1108, 6), (key995, 6), (key1030, 6), (key1108, 6)]

theorem rawRowCheck19173 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form4 = rawRow19173 := by decide +kernel

def row19173 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

theorem rowCheck19173 : row19173 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19173 := by decide +kernel

theorem rowEval19173 (x : Key → ℝ) : Integer.Sparse.eval row19173 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19173, Integer.Sparse.eval_collectBalanced, rawRowCheck19173]

def rawRow19174 : Integer.Sparse Key := [(key1119, 6), (key1108, 6), (key1146, 6), (key1108, 6), (key1119, 6), (key1108, 6), (key1146, 6), (key1011, 6), (key995, 6), (key1119, 6), (key1030, 6), (key1146, 6), (key1067, 6), (key995, 6), (key1108, 6), (key1030, 6), (key1108, 6), (key995, 6), (key1108, 6), (key1030, 6)]

theorem rawRowCheck19174 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form4 = rawRow19174 := by decide +kernel

def row19174 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

theorem rowCheck19174 : row19174 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19174 := by decide +kernel

theorem rowEval19174 (x : Key → ℝ) : Integer.Sparse.eval row19174 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19174, Integer.Sparse.eval_collectBalanced, rawRowCheck19174]

def rawRow19175 : Integer.Sparse Key := [(key1108, 6), (key1146, 6), (key1119, 6), (key1108, 6), (key1108, 6), (key1146, 6), (key1119, 6), (key1030, 6), (key1067, 6), (key995, 6), (key1146, 6), (key1011, 6), (key1119, 6), (key1030, 6), (key995, 6), (key1108, 6), (key1108, 6), (key1030, 6), (key995, 6), (key1108, 6)]

theorem rawRowCheck19175 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form4 = rawRow19175 := by decide +kernel

def row19175 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

theorem rowCheck19175 : row19175 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19175 := by decide +kernel

theorem rowEval19175 (x : Key → ℝ) : Integer.Sparse.eval row19175 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19175, Integer.Sparse.eval_collectBalanced, rawRowCheck19175]

def rawRow19176 : Integer.Sparse Key := [(key1146, 6), (key1108, 6), (key1119, 6), (key1108, 6), (key1146, 6), (key1108, 6), (key1119, 6), (key1067, 6), (key1030, 6), (key1146, 6), (key995, 6), (key1119, 6), (key1011, 6), (key1030, 6), (key1108, 6), (key995, 6), (key1108, 6), (key1030, 6), (key1108, 6), (key995, 6)]

theorem rawRowCheck19176 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form4 = rawRow19176 := by decide +kernel

def row19176 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

theorem rowCheck19176 : row19176 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19176 := by decide +kernel

theorem rowEval19176 (x : Key → ℝ) : Integer.Sparse.eval row19176 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19176, Integer.Sparse.eval_collectBalanced, rawRowCheck19176]

def rawRow19177 : Integer.Sparse Key := [(key1119, 6), (key1146, 6), (key1108, 6), (key1108, 6), (key1119, 6), (key1146, 6), (key1108, 6), (key1119, 6), (key1146, 6), (key1011, 6), (key1067, 6), (key995, 6), (key1030, 6), (key1108, 6), (key995, 6), (key1030, 6), (key1108, 6), (key1108, 6), (key995, 6), (key1030, 6)]

theorem rawRowCheck19177 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form4 = rawRow19177 := by decide +kernel

def row19177 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

theorem rowCheck19177 : row19177 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19177 := by decide +kernel

theorem rowEval19177 (x : Key → ℝ) : Integer.Sparse.eval row19177 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19177, Integer.Sparse.eval_collectBalanced, rawRowCheck19177]

def rawRow19178 : Integer.Sparse Key := [(key1146, 6), (key1119, 6), (key1108, 6), (key1108, 6), (key1146, 6), (key1119, 6), (key1108, 6), (key1146, 6), (key1119, 6), (key1067, 6), (key1011, 6), (key1030, 6), (key995, 6), (key1108, 6), (key1030, 6), (key995, 6), (key1108, 6), (key1108, 6), (key1030, 6), (key995, 6)]

theorem rawRowCheck19178 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form4 = rawRow19178 := by decide +kernel

def row19178 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

theorem rowCheck19178 : row19178 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19178 := by decide +kernel

theorem rowEval19178 (x : Key → ℝ) : Integer.Sparse.eval row19178 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19178, Integer.Sparse.eval_collectBalanced, rawRowCheck19178]

def rawRow19179 : Integer.Sparse Key := [(key2377, 4), (key2377, 4), (key2377, 4), (key2389, 4), (key2389, 4), (key2389, 4), (key2405, 4), (key2405, 4), (key2405, 4), (key2471, 4), (key2471, 4), (key2471, 4), (key2479, 4), (key2479, 4), (key2479, 4), (key2479, 4), (key2479, 4), (key2479, 4), (key2436, 4), (key2436, 4), (key2436, 4), (key2502, 4), (key2502, 4), (key2502, 4), (key2502, 4), (key2502, 4), (key2502, 4), (key2518, 4), (key2518, 4), (key2518, 4)]

theorem rawRowCheck19179 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form5 = rawRow19179 := by decide +kernel

def row19179 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

theorem rowCheck19179 : row19179 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19179 := by decide +kernel

theorem rowEval19179 (x : Key → ℝ) : Integer.Sparse.eval row19179 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19179, Integer.Sparse.eval_collectBalanced, rawRowCheck19179]

def rawRow19180 : Integer.Sparse Key := [(key2377, 4), (key2389, 4), (key2389, 4), (key2377, 4), (key2377, 4), (key2389, 4), (key2471, 4), (key2479, 4), (key2479, 4), (key2405, 4), (key2479, 4), (key2479, 4), (key2405, 4), (key2405, 4), (key2471, 4), (key2471, 4), (key2479, 4), (key2479, 4), (key2502, 4), (key2502, 4), (key2518, 4), (key2436, 4), (key2436, 4), (key2502, 4), (key2502, 4), (key2518, 4), (key2518, 4), (key2436, 4), (key2502, 4), (key2502, 4)]

theorem rawRowCheck19180 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form5 = rawRow19180 := by decide +kernel

def row19180 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

theorem rowCheck19180 : row19180 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19180 := by decide +kernel

theorem rowEval19180 (x : Key → ℝ) : Integer.Sparse.eval row19180 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19180, Integer.Sparse.eval_collectBalanced, rawRowCheck19180]

def rawRow19181 : Integer.Sparse Key := [(key2389, 4), (key2377, 4), (key2389, 4), (key2377, 4), (key2389, 4), (key2377, 4), (key2479, 4), (key2471, 4), (key2479, 4), (key2479, 4), (key2405, 4), (key2479, 4), (key2471, 4), (key2479, 4), (key2405, 4), (key2479, 4), (key2405, 4), (key2471, 4), (key2502, 4), (key2518, 4), (key2502, 4), (key2502, 4), (key2518, 4), (key2436, 4), (key2518, 4), (key2436, 4), (key2502, 4), (key2502, 4), (key2436, 4), (key2502, 4)]

theorem rawRowCheck19181 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form5 = rawRow19181 := by decide +kernel

def row19181 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

theorem rowCheck19181 : row19181 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19181 := by decide +kernel

theorem rowEval19181 (x : Key → ℝ) : Integer.Sparse.eval row19181 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19181, Integer.Sparse.eval_collectBalanced, rawRowCheck19181]

def rawRow19182 : Integer.Sparse Key := [(key2389, 4), (key2389, 4), (key2377, 4), (key2389, 4), (key2377, 4), (key2377, 4), (key2479, 4), (key2479, 4), (key2471, 4), (key2479, 4), (key2479, 4), (key2405, 4), (key2479, 4), (key2471, 4), (key2479, 4), (key2405, 4), (key2471, 4), (key2405, 4), (key2518, 4), (key2502, 4), (key2502, 4), (key2518, 4), (key2502, 4), (key2518, 4), (key2436, 4), (key2502, 4), (key2436, 4), (key2502, 4), (key2502, 4), (key2436, 4)]

theorem rawRowCheck19182 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form5 = rawRow19182 := by decide +kernel

def row19182 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

theorem rowCheck19182 : row19182 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19182 := by decide +kernel

theorem rowEval19182 (x : Key → ℝ) : Integer.Sparse.eval row19182 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19182, Integer.Sparse.eval_collectBalanced, rawRowCheck19182]

def rawRow19183 : Integer.Sparse Key := [(key2405, 4), (key2405, 4), (key2405, 4), (key2436, 4), (key2436, 4), (key2436, 4), (key2377, 4), (key2377, 4), (key2377, 4), (key2471, 4), (key2471, 4), (key2471, 4), (key2502, 4), (key2502, 4), (key2502, 4), (key2502, 4), (key2502, 4), (key2502, 4), (key2389, 4), (key2389, 4), (key2389, 4), (key2479, 4), (key2479, 4), (key2479, 4), (key2479, 4), (key2479, 4), (key2479, 4), (key2518, 4), (key2518, 4), (key2518, 4)]

theorem rawRowCheck19183 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form5 = rawRow19183 := by decide +kernel

def row19183 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

theorem rowCheck19183 : row19183 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19183 := by decide +kernel

theorem rowEval19183 (x : Key → ℝ) : Integer.Sparse.eval row19183 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19183, Integer.Sparse.eval_collectBalanced, rawRowCheck19183]

def rawRow19184 : Integer.Sparse Key := [(key2405, 4), (key2436, 4), (key2436, 4), (key2405, 4), (key2405, 4), (key2436, 4), (key2471, 4), (key2502, 4), (key2502, 4), (key2377, 4), (key2502, 4), (key2502, 4), (key2377, 4), (key2377, 4), (key2471, 4), (key2471, 4), (key2502, 4), (key2502, 4), (key2479, 4), (key2479, 4), (key2518, 4), (key2389, 4), (key2389, 4), (key2479, 4), (key2479, 4), (key2518, 4), (key2518, 4), (key2389, 4), (key2479, 4), (key2479, 4)]

theorem rawRowCheck19184 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form5 = rawRow19184 := by decide +kernel

def row19184 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

theorem rowCheck19184 : row19184 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19184 := by decide +kernel

theorem rowEval19184 (x : Key → ℝ) : Integer.Sparse.eval row19184 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19184, Integer.Sparse.eval_collectBalanced, rawRowCheck19184]

def rawRow19185 : Integer.Sparse Key := [(key2436, 4), (key2405, 4), (key2436, 4), (key2405, 4), (key2436, 4), (key2405, 4), (key2502, 4), (key2471, 4), (key2502, 4), (key2502, 4), (key2377, 4), (key2502, 4), (key2471, 4), (key2502, 4), (key2377, 4), (key2502, 4), (key2377, 4), (key2471, 4), (key2479, 4), (key2518, 4), (key2479, 4), (key2479, 4), (key2518, 4), (key2389, 4), (key2518, 4), (key2389, 4), (key2479, 4), (key2479, 4), (key2389, 4), (key2479, 4)]

theorem rawRowCheck19185 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form5 = rawRow19185 := by decide +kernel

def row19185 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

theorem rowCheck19185 : row19185 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19185 := by decide +kernel

theorem rowEval19185 (x : Key → ℝ) : Integer.Sparse.eval row19185 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19185, Integer.Sparse.eval_collectBalanced, rawRowCheck19185]

def rawRow19186 : Integer.Sparse Key := [(key2436, 4), (key2436, 4), (key2405, 4), (key2436, 4), (key2405, 4), (key2405, 4), (key2502, 4), (key2502, 4), (key2471, 4), (key2502, 4), (key2502, 4), (key2377, 4), (key2502, 4), (key2471, 4), (key2502, 4), (key2377, 4), (key2471, 4), (key2377, 4), (key2518, 4), (key2479, 4), (key2479, 4), (key2518, 4), (key2479, 4), (key2518, 4), (key2389, 4), (key2479, 4), (key2389, 4), (key2479, 4), (key2479, 4), (key2389, 4)]

theorem rawRowCheck19186 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form5 = rawRow19186 := by decide +kernel

def row19186 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

theorem rowCheck19186 : row19186 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19186 := by decide +kernel

theorem rowEval19186 (x : Key → ℝ) : Integer.Sparse.eval row19186 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19186, Integer.Sparse.eval_collectBalanced, rawRowCheck19186]

def rawRow19187 : Integer.Sparse Key := [(key2471, 4), (key2479, 4), (key2479, 4), (key2502, 4), (key2502, 4), (key2518, 4), (key2377, 4), (key2389, 4), (key2389, 4), (key2405, 4), (key2479, 4), (key2479, 4), (key2436, 4), (key2436, 4), (key2502, 4), (key2502, 4), (key2518, 4), (key2518, 4), (key2377, 4), (key2377, 4), (key2389, 4), (key2405, 4), (key2405, 4), (key2471, 4), (key2471, 4), (key2479, 4), (key2479, 4), (key2436, 4), (key2502, 4), (key2502, 4)]

theorem rawRowCheck19187 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form5 = rawRow19187 := by decide +kernel

def row19187 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

theorem rowCheck19187 : row19187 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19187 := by decide +kernel

theorem rowEval19187 (x : Key → ℝ) : Integer.Sparse.eval row19187 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19187, Integer.Sparse.eval_collectBalanced, rawRowCheck19187]

def rawRow19188 : Integer.Sparse Key := [(key2479, 4), (key2471, 4), (key2479, 4), (key2502, 4), (key2518, 4), (key2502, 4), (key2389, 4), (key2377, 4), (key2389, 4), (key2479, 4), (key2405, 4), (key2479, 4), (key2502, 4), (key2518, 4), (key2436, 4), (key2518, 4), (key2436, 4), (key2502, 4), (key2377, 4), (key2389, 4), (key2377, 4), (key2471, 4), (key2479, 4), (key2405, 4), (key2479, 4), (key2405, 4), (key2471, 4), (key2502, 4), (key2436, 4), (key2502, 4)]

theorem rawRowCheck19188 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form5 = rawRow19188 := by decide +kernel

def row19188 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

theorem rowCheck19188 : row19188 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19188 := by decide +kernel

theorem rowEval19188 (x : Key → ℝ) : Integer.Sparse.eval row19188 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19188, Integer.Sparse.eval_collectBalanced, rawRowCheck19188]

def rawRow19189 : Integer.Sparse Key := [(key2479, 4), (key2479, 4), (key2471, 4), (key2518, 4), (key2502, 4), (key2502, 4), (key2389, 4), (key2389, 4), (key2377, 4), (key2479, 4), (key2479, 4), (key2405, 4), (key2518, 4), (key2502, 4), (key2518, 4), (key2436, 4), (key2502, 4), (key2436, 4), (key2389, 4), (key2377, 4), (key2377, 4), (key2479, 4), (key2471, 4), (key2479, 4), (key2405, 4), (key2471, 4), (key2405, 4), (key2502, 4), (key2502, 4), (key2436, 4)]

theorem rawRowCheck19189 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form5 = rawRow19189 := by decide +kernel

def row19189 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

theorem rowCheck19189 : row19189 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19189 := by decide +kernel

theorem rowEval19189 (x : Key → ℝ) : Integer.Sparse.eval row19189 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19189, Integer.Sparse.eval_collectBalanced, rawRowCheck19189]

def rawRow19190 : Integer.Sparse Key := [(key2471, 4), (key2502, 4), (key2502, 4), (key2479, 4), (key2479, 4), (key2518, 4), (key2405, 4), (key2436, 4), (key2436, 4), (key2377, 4), (key2502, 4), (key2502, 4), (key2389, 4), (key2389, 4), (key2479, 4), (key2479, 4), (key2518, 4), (key2518, 4), (key2405, 4), (key2405, 4), (key2436, 4), (key2377, 4), (key2377, 4), (key2471, 4), (key2471, 4), (key2502, 4), (key2502, 4), (key2389, 4), (key2479, 4), (key2479, 4)]

theorem rawRowCheck19190 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form5 = rawRow19190 := by decide +kernel

def row19190 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

theorem rowCheck19190 : row19190 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19190 := by decide +kernel

theorem rowEval19190 (x : Key → ℝ) : Integer.Sparse.eval row19190 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19190, Integer.Sparse.eval_collectBalanced, rawRowCheck19190]

def rawRow19191 : Integer.Sparse Key := [(key2502, 4), (key2471, 4), (key2502, 4), (key2479, 4), (key2518, 4), (key2479, 4), (key2436, 4), (key2405, 4), (key2436, 4), (key2502, 4), (key2377, 4), (key2502, 4), (key2479, 4), (key2518, 4), (key2389, 4), (key2518, 4), (key2389, 4), (key2479, 4), (key2405, 4), (key2436, 4), (key2405, 4), (key2471, 4), (key2502, 4), (key2377, 4), (key2502, 4), (key2377, 4), (key2471, 4), (key2479, 4), (key2389, 4), (key2479, 4)]

theorem rawRowCheck19191 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form5 = rawRow19191 := by decide +kernel

def row19191 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

theorem rowCheck19191 : row19191 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19191 := by decide +kernel

theorem rowEval19191 (x : Key → ℝ) : Integer.Sparse.eval row19191 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19191, Integer.Sparse.eval_collectBalanced, rawRowCheck19191]

def rawRow19192 : Integer.Sparse Key := [(key2502, 4), (key2502, 4), (key2471, 4), (key2518, 4), (key2479, 4), (key2479, 4), (key2436, 4), (key2436, 4), (key2405, 4), (key2502, 4), (key2502, 4), (key2377, 4), (key2518, 4), (key2479, 4), (key2518, 4), (key2389, 4), (key2479, 4), (key2389, 4), (key2436, 4), (key2405, 4), (key2405, 4), (key2502, 4), (key2471, 4), (key2502, 4), (key2377, 4), (key2471, 4), (key2377, 4), (key2479, 4), (key2479, 4), (key2389, 4)]

theorem rawRowCheck19192 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form5 = rawRow19192 := by decide +kernel

def row19192 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

theorem rowCheck19192 : row19192 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19192 := by decide +kernel

theorem rowEval19192 (x : Key → ℝ) : Integer.Sparse.eval row19192 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19192, Integer.Sparse.eval_collectBalanced, rawRowCheck19192]

def rawRow19193 : Integer.Sparse Key := [(key2479, 4), (key2502, 4), (key2518, 4), (key2471, 4), (key2479, 4), (key2502, 4), (key2479, 4), (key2502, 4), (key2518, 4), (key2389, 4), (key2436, 4), (key2518, 4), (key2377, 4), (key2389, 4), (key2405, 4), (key2479, 4), (key2436, 4), (key2502, 4), (key2471, 4), (key2479, 4), (key2502, 4), (key2377, 4), (key2389, 4), (key2405, 4), (key2479, 4), (key2436, 4), (key2502, 4), (key2377, 4), (key2405, 4), (key2471, 4)]

theorem rawRowCheck19193 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form5 = rawRow19193 := by decide +kernel

def row19193 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

theorem rowCheck19193 : row19193 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19193 := by decide +kernel

theorem rowEval19193 (x : Key → ℝ) : Integer.Sparse.eval row19193 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19193, Integer.Sparse.eval_collectBalanced, rawRowCheck19193]

def rawRow19194 : Integer.Sparse Key := [(key2479, 4), (key2518, 4), (key2502, 4), (key2479, 4), (key2471, 4), (key2502, 4), (key2479, 4), (key2518, 4), (key2502, 4), (key2389, 4), (key2518, 4), (key2436, 4), (key2389, 4), (key2377, 4), (key2479, 4), (key2405, 4), (key2502, 4), (key2436, 4), (key2479, 4), (key2471, 4), (key2502, 4), (key2389, 4), (key2377, 4), (key2479, 4), (key2405, 4), (key2502, 4), (key2436, 4), (key2377, 4), (key2471, 4), (key2405, 4)]

theorem rawRowCheck19194 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form5 = rawRow19194 := by decide +kernel

def row19194 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

theorem rowCheck19194 : row19194 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19194 := by decide +kernel

theorem rowEval19194 (x : Key → ℝ) : Integer.Sparse.eval row19194 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19194, Integer.Sparse.eval_collectBalanced, rawRowCheck19194]

def rawRow19195 : Integer.Sparse Key := [(key2502, 4), (key2479, 4), (key2518, 4), (key2471, 4), (key2502, 4), (key2479, 4), (key2502, 4), (key2479, 4), (key2518, 4), (key2436, 4), (key2389, 4), (key2518, 4), (key2405, 4), (key2436, 4), (key2377, 4), (key2502, 4), (key2389, 4), (key2479, 4), (key2471, 4), (key2502, 4), (key2479, 4), (key2405, 4), (key2436, 4), (key2377, 4), (key2502, 4), (key2389, 4), (key2479, 4), (key2405, 4), (key2377, 4), (key2471, 4)]

theorem rawRowCheck19195 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form5 = rawRow19195 := by decide +kernel

def row19195 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

theorem rowCheck19195 : row19195 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19195 := by decide +kernel

theorem rowEval19195 (x : Key → ℝ) : Integer.Sparse.eval row19195 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19195, Integer.Sparse.eval_collectBalanced, rawRowCheck19195]

def rawRow19196 : Integer.Sparse Key := [(key2502, 4), (key2518, 4), (key2479, 4), (key2502, 4), (key2471, 4), (key2479, 4), (key2502, 4), (key2518, 4), (key2479, 4), (key2436, 4), (key2518, 4), (key2389, 4), (key2436, 4), (key2405, 4), (key2502, 4), (key2377, 4), (key2479, 4), (key2389, 4), (key2502, 4), (key2471, 4), (key2479, 4), (key2436, 4), (key2405, 4), (key2502, 4), (key2377, 4), (key2479, 4), (key2389, 4), (key2405, 4), (key2471, 4), (key2377, 4)]

theorem rawRowCheck19196 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form5 = rawRow19196 := by decide +kernel

def row19196 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

theorem rowCheck19196 : row19196 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19196 := by decide +kernel

theorem rowEval19196 (x : Key → ℝ) : Integer.Sparse.eval row19196 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19196, Integer.Sparse.eval_collectBalanced, rawRowCheck19196]

def rawRow19197 : Integer.Sparse Key := [(key2518, 4), (key2479, 4), (key2502, 4), (key2479, 4), (key2502, 4), (key2471, 4), (key2518, 4), (key2479, 4), (key2502, 4), (key2518, 4), (key2389, 4), (key2436, 4), (key2479, 4), (key2502, 4), (key2389, 4), (key2436, 4), (key2377, 4), (key2405, 4), (key2479, 4), (key2502, 4), (key2471, 4), (key2479, 4), (key2502, 4), (key2389, 4), (key2436, 4), (key2377, 4), (key2405, 4), (key2471, 4), (key2377, 4), (key2405, 4)]

theorem rawRowCheck19197 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form5 = rawRow19197 := by decide +kernel

def row19197 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

theorem rowCheck19197 : row19197 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19197 := by decide +kernel

theorem rowEval19197 (x : Key → ℝ) : Integer.Sparse.eval row19197 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19197, Integer.Sparse.eval_collectBalanced, rawRowCheck19197]

def rawRow19198 : Integer.Sparse Key := [(key2518, 4), (key2502, 4), (key2479, 4), (key2502, 4), (key2479, 4), (key2471, 4), (key2518, 4), (key2502, 4), (key2479, 4), (key2518, 4), (key2436, 4), (key2389, 4), (key2502, 4), (key2479, 4), (key2436, 4), (key2389, 4), (key2405, 4), (key2377, 4), (key2502, 4), (key2479, 4), (key2471, 4), (key2502, 4), (key2479, 4), (key2436, 4), (key2389, 4), (key2405, 4), (key2377, 4), (key2471, 4), (key2405, 4), (key2377, 4)]

theorem rawRowCheck19198 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form5 = rawRow19198 := by decide +kernel

def row19198 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

theorem rowCheck19198 : row19198 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19198 := by decide +kernel

theorem rowEval19198 (x : Key → ℝ) : Integer.Sparse.eval row19198 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19198, Integer.Sparse.eval_collectBalanced, rawRowCheck19198]

def rawRow19199 : Integer.Sparse Key := [(key2369, 6), (key2369, 6), (key2369, 6), (key2384, 6), (key2397, 6), (key2397, 6), (key2397, 6), (key2463, 6), (key2463, 6), (key2463, 6), (key2463, 6), (key2463, 6), (key2463, 6), (key2474, 6), (key2474, 6), (key2474, 6), (key2431, 6), (key2497, 6), (key2497, 6), (key2497, 6)]

theorem rawRowCheck19199 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form6 = rawRow19199 := by decide +kernel

def row19199 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

theorem rowCheck19199 : row19199 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19199 := by decide +kernel

theorem rowEval19199 (x : Key → ℝ) : Integer.Sparse.eval row19199 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19199, Integer.Sparse.eval_collectBalanced, rawRowCheck19199]

end MUB6.Certificate.GramRows

end OAI
