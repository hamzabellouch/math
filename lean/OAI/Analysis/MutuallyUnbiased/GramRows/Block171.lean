import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow18816 : Integer.Sparse Key := [(key1178, 24), (key1178, 24), (key974, 24), (key1088, 24), (key1088, 24)]

theorem rawRowCheck18816 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block5.form1 = rawRow18816 := by decide +kernel

def row18816 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

theorem rowCheck18816 : row18816 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18816 := by decide +kernel

theorem rowEval18816 (x : Key → ℝ) : Integer.Sparse.eval row18816 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18816, Integer.Sparse.eval_collectBalanced, rawRowCheck18816]

def rawRow18817 : Integer.Sparse Key := [(key1178, 24), (key1178, 24), (key1088, 24), (key974, 24), (key1088, 24)]

theorem rawRowCheck18817 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block5.form1 = rawRow18817 := by decide +kernel

def row18817 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

theorem rowCheck18817 : row18817 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18817 := by decide +kernel

theorem rowEval18817 (x : Key → ℝ) : Integer.Sparse.eval row18817 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18817, Integer.Sparse.eval_collectBalanced, rawRowCheck18817]

def rawRow18818 : Integer.Sparse Key := [(key1178, 24), (key1178, 24), (key1088, 24), (key1088, 24), (key974, 24)]

theorem rawRowCheck18818 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block5.form1 = rawRow18818 := by decide +kernel

def row18818 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

theorem rowCheck18818 : row18818 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18818 := by decide +kernel

theorem rowEval18818 (x : Key → ℝ) : Integer.Sparse.eval row18818 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18818, Integer.Sparse.eval_collectBalanced, rawRowCheck18818]

def rawRow18819 : Integer.Sparse Key := [(key2378, 2), (key2378, 2), (key2383, 2), (key2378, 2), (key2378, 2), (key2390, 2), (key2390, 2), (key2394, 2), (key2394, 2), (key2383, 2), (key2394, 2), (key2394, 2), (key2406, 2), (key2406, 2), (key2411, 2), (key2406, 2), (key2406, 2), (key2437, 2), (key2437, 2), (key2443, 2), (key2443, 2), (key2411, 2), (key2443, 2), (key2443, 2), (key2472, 2), (key2472, 2), (key2480, 2), (key2480, 2), (key2484, 2), (key2484, 2), (key2472, 2), (key2472, 2), (key2503, 2), (key2503, 2), (key2509, 2), (key2509, 2), (key2480, 2), (key2480, 2), (key2503, 2), (key2503, 2), (key2524, 2), (key2524, 2), (key2484, 2), (key2484, 2), (key2509, 2), (key2509, 2), (key2524, 2), (key2524, 2), (key2569, 2), (key2571, 2), (key2571, 2), (key2569, 2), (key2576, 2), (key2576, 2), (key2571, 2), (key2571, 2), (key2576, 2), (key2576, 2), (key2580, 2), (key2580, 2)]

theorem rawRowCheck18819 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block5.form2 = rawRow18819 := by decide +kernel

def row18819 : Integer.Sparse Key := [(key2378, 8), (key2383, 4), (key2390, 4), (key2394, 8), (key2406, 8), (key2411, 4), (key2437, 4), (key2443, 8), (key2472, 8), (key2480, 8), (key2484, 8), (key2503, 8), (key2509, 8), (key2524, 8), (key2569, 4), (key2571, 8), (key2576, 8), (key2580, 4)]

theorem rowCheck18819 : row18819 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18819 := by decide +kernel

theorem rowEval18819 (x : Key → ℝ) : Integer.Sparse.eval row18819 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block5.form2) x := by
  rw [rowCheck18819, Integer.Sparse.eval_collectBalanced, rawRowCheck18819]

def rawRow18820 : Integer.Sparse Key := [(key2378, 2), (key2383, 2), (key2378, 2), (key2390, 2), (key2394, 2), (key2378, 2), (key2394, 2), (key2378, 2), (key2390, 2), (key2394, 2), (key2383, 2), (key2394, 2), (key2406, 2), (key2411, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2406, 2), (key2443, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2411, 2), (key2443, 2), (key2480, 2), (key2484, 2), (key2472, 2), (key2484, 2), (key2472, 2), (key2480, 2), (key2503, 2), (key2509, 2), (key2472, 2), (key2509, 2), (key2472, 2), (key2503, 2), (key2503, 2), (key2524, 2), (key2480, 2), (key2524, 2), (key2480, 2), (key2503, 2), (key2509, 2), (key2524, 2), (key2484, 2), (key2524, 2), (key2484, 2), (key2509, 2), (key2571, 2), (key2569, 2), (key2571, 2), (key2576, 2), (key2569, 2), (key2576, 2), (key2576, 2), (key2580, 2), (key2571, 2), (key2580, 2), (key2571, 2), (key2576, 2)]

theorem rawRowCheck18820 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block5.form2 = rawRow18820 := by decide +kernel

def row18820 : Integer.Sparse Key := [(key2378, 8), (key2383, 4), (key2390, 4), (key2394, 8), (key2406, 8), (key2411, 4), (key2437, 4), (key2443, 8), (key2472, 8), (key2480, 8), (key2484, 8), (key2503, 8), (key2509, 8), (key2524, 8), (key2569, 4), (key2571, 8), (key2576, 8), (key2580, 4)]

theorem rowCheck18820 : row18820 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18820 := by decide +kernel

theorem rowEval18820 (x : Key → ℝ) : Integer.Sparse.eval row18820 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block5.form2) x := by
  rw [rowCheck18820, Integer.Sparse.eval_collectBalanced, rawRowCheck18820]

def rawRow18821 : Integer.Sparse Key := [(key2383, 2), (key2378, 2), (key2378, 2), (key2394, 2), (key2390, 2), (key2394, 2), (key2378, 2), (key2390, 2), (key2378, 2), (key2394, 2), (key2394, 2), (key2383, 2), (key2411, 2), (key2406, 2), (key2406, 2), (key2443, 2), (key2437, 2), (key2443, 2), (key2406, 2), (key2437, 2), (key2406, 2), (key2443, 2), (key2443, 2), (key2411, 2), (key2484, 2), (key2480, 2), (key2484, 2), (key2472, 2), (key2480, 2), (key2472, 2), (key2509, 2), (key2503, 2), (key2509, 2), (key2472, 2), (key2503, 2), (key2472, 2), (key2524, 2), (key2503, 2), (key2524, 2), (key2480, 2), (key2503, 2), (key2480, 2), (key2524, 2), (key2509, 2), (key2524, 2), (key2484, 2), (key2509, 2), (key2484, 2), (key2571, 2), (key2571, 2), (key2569, 2), (key2576, 2), (key2576, 2), (key2569, 2), (key2580, 2), (key2576, 2), (key2580, 2), (key2571, 2), (key2576, 2), (key2571, 2)]

theorem rawRowCheck18821 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block5.form2 = rawRow18821 := by decide +kernel

def row18821 : Integer.Sparse Key := [(key2378, 8), (key2383, 4), (key2390, 4), (key2394, 8), (key2406, 8), (key2411, 4), (key2437, 4), (key2443, 8), (key2472, 8), (key2480, 8), (key2484, 8), (key2503, 8), (key2509, 8), (key2524, 8), (key2569, 4), (key2571, 8), (key2576, 8), (key2580, 4)]

theorem rowCheck18821 : row18821 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18821 := by decide +kernel

theorem rowEval18821 (x : Key → ℝ) : Integer.Sparse.eval row18821 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18821, Integer.Sparse.eval_collectBalanced, rawRowCheck18821]

def rawRow18822 : Integer.Sparse Key := [(key2390, 2), (key2394, 2), (key2394, 2), (key2378, 2), (key2383, 2), (key2378, 2), (key2394, 2), (key2383, 2), (key2394, 2), (key2378, 2), (key2378, 2), (key2390, 2), (key2437, 2), (key2443, 2), (key2443, 2), (key2406, 2), (key2411, 2), (key2406, 2), (key2443, 2), (key2411, 2), (key2443, 2), (key2406, 2), (key2406, 2), (key2437, 2), (key2503, 2), (key2509, 2), (key2503, 2), (key2524, 2), (key2509, 2), (key2524, 2), (key2480, 2), (key2484, 2), (key2480, 2), (key2524, 2), (key2484, 2), (key2524, 2), (key2472, 2), (key2484, 2), (key2472, 2), (key2509, 2), (key2484, 2), (key2509, 2), (key2472, 2), (key2480, 2), (key2472, 2), (key2503, 2), (key2480, 2), (key2503, 2), (key2576, 2), (key2576, 2), (key2580, 2), (key2571, 2), (key2571, 2), (key2580, 2), (key2569, 2), (key2571, 2), (key2569, 2), (key2576, 2), (key2571, 2), (key2576, 2)]

theorem rawRowCheck18822 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block5.form2 = rawRow18822 := by decide +kernel

def row18822 : Integer.Sparse Key := [(key2378, 8), (key2383, 4), (key2390, 4), (key2394, 8), (key2406, 8), (key2411, 4), (key2437, 4), (key2443, 8), (key2472, 8), (key2480, 8), (key2484, 8), (key2503, 8), (key2509, 8), (key2524, 8), (key2569, 4), (key2571, 8), (key2576, 8), (key2580, 4)]

theorem rowCheck18822 : row18822 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18822 := by decide +kernel

theorem rowEval18822 (x : Key → ℝ) : Integer.Sparse.eval row18822 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block5.form2) x := by
  rw [rowCheck18822, Integer.Sparse.eval_collectBalanced, rawRowCheck18822]

def rawRow18823 : Integer.Sparse Key := [(key2394, 2), (key2390, 2), (key2394, 2), (key2383, 2), (key2378, 2), (key2394, 2), (key2378, 2), (key2394, 2), (key2383, 2), (key2378, 2), (key2390, 2), (key2378, 2), (key2443, 2), (key2437, 2), (key2443, 2), (key2411, 2), (key2406, 2), (key2443, 2), (key2406, 2), (key2443, 2), (key2411, 2), (key2406, 2), (key2437, 2), (key2406, 2), (key2509, 2), (key2503, 2), (key2524, 2), (key2503, 2), (key2524, 2), (key2509, 2), (key2484, 2), (key2480, 2), (key2524, 2), (key2480, 2), (key2524, 2), (key2484, 2), (key2484, 2), (key2472, 2), (key2509, 2), (key2472, 2), (key2509, 2), (key2484, 2), (key2480, 2), (key2472, 2), (key2503, 2), (key2472, 2), (key2503, 2), (key2480, 2), (key2576, 2), (key2580, 2), (key2576, 2), (key2571, 2), (key2580, 2), (key2571, 2), (key2571, 2), (key2569, 2), (key2576, 2), (key2569, 2), (key2576, 2), (key2571, 2)]

theorem rawRowCheck18823 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block5.form2 = rawRow18823 := by decide +kernel

def row18823 : Integer.Sparse Key := [(key2378, 8), (key2383, 4), (key2390, 4), (key2394, 8), (key2406, 8), (key2411, 4), (key2437, 4), (key2443, 8), (key2472, 8), (key2480, 8), (key2484, 8), (key2503, 8), (key2509, 8), (key2524, 8), (key2569, 4), (key2571, 8), (key2576, 8), (key2580, 4)]

theorem rowCheck18823 : row18823 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18823 := by decide +kernel

theorem rowEval18823 (x : Key → ℝ) : Integer.Sparse.eval row18823 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18823, Integer.Sparse.eval_collectBalanced, rawRowCheck18823]

def rawRow18824 : Integer.Sparse Key := [(key2394, 2), (key2394, 2), (key2390, 2), (key2394, 2), (key2394, 2), (key2383, 2), (key2383, 2), (key2378, 2), (key2378, 2), (key2390, 2), (key2378, 2), (key2378, 2), (key2443, 2), (key2443, 2), (key2437, 2), (key2443, 2), (key2443, 2), (key2411, 2), (key2411, 2), (key2406, 2), (key2406, 2), (key2437, 2), (key2406, 2), (key2406, 2), (key2524, 2), (key2524, 2), (key2509, 2), (key2509, 2), (key2503, 2), (key2503, 2), (key2524, 2), (key2524, 2), (key2484, 2), (key2484, 2), (key2480, 2), (key2480, 2), (key2509, 2), (key2509, 2), (key2484, 2), (key2484, 2), (key2472, 2), (key2472, 2), (key2503, 2), (key2503, 2), (key2480, 2), (key2480, 2), (key2472, 2), (key2472, 2), (key2580, 2), (key2576, 2), (key2576, 2), (key2580, 2), (key2571, 2), (key2571, 2), (key2576, 2), (key2576, 2), (key2571, 2), (key2571, 2), (key2569, 2), (key2569, 2)]

theorem rawRowCheck18824 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block5.form2 = rawRow18824 := by decide +kernel

def row18824 : Integer.Sparse Key := [(key2378, 8), (key2383, 4), (key2390, 4), (key2394, 8), (key2406, 8), (key2411, 4), (key2437, 4), (key2443, 8), (key2472, 8), (key2480, 8), (key2484, 8), (key2503, 8), (key2509, 8), (key2524, 8), (key2569, 4), (key2571, 8), (key2576, 8), (key2580, 4)]

theorem rowCheck18824 : row18824 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18824 := by decide +kernel

theorem rowEval18824 (x : Key → ℝ) : Integer.Sparse.eval row18824 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18824, Integer.Sparse.eval_collectBalanced, rawRowCheck18824]

def rawRow18825 : Integer.Sparse Key := [(key2766, 2), (key2766, 2), (key2772, 2), (key2843, 2), (key2843, 2), (key2887, 2), (key2887, 2), (key2889, 2), (key2889, 2), (key2880, 2), (key2910, 2), (key2910, 2), (key2587, 2), (key2587, 2), (key2593, 2), (key2843, 2), (key2843, 2), (key2966, 2), (key2966, 2), (key2968, 2), (key2968, 2), (key2880, 2), (key2989, 2), (key2989, 2), (key2378, 2), (key2378, 2), (key2390, 2), (key2390, 2), (key2394, 2), (key2394, 2), (key2406, 2), (key2406, 2), (key2437, 2), (key2437, 2), (key2443, 2), (key2443, 2), (key2480, 2), (key2480, 2), (key2503, 2), (key2503, 2), (key2524, 2), (key2524, 2), (key2571, 2), (key2571, 2), (key2576, 2), (key2576, 2), (key2580, 2), (key2580, 2), (key2383, 2), (key2394, 2), (key2394, 2), (key2411, 2), (key2443, 2), (key2443, 2), (key2484, 2), (key2484, 2), (key2509, 2), (key2509, 2), (key2524, 2), (key2524, 2)]

theorem rawRowCheck18825 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block5.form2 = rawRow18825 := by decide +kernel

def row18825 : Integer.Sparse Key := [(key2378, 4), (key2383, 2), (key2390, 4), (key2394, 8), (key2406, 4), (key2411, 2), (key2437, 4), (key2443, 8), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 8), (key2571, 4), (key2576, 4), (key2580, 4), (key2587, 4), (key2593, 2), (key2766, 4), (key2772, 2), (key2843, 8), (key2880, 4), (key2887, 4), (key2889, 4), (key2910, 4), (key2966, 4), (key2968, 4), (key2989, 4)]

theorem rowCheck18825 : row18825 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18825 := by decide +kernel

theorem rowEval18825 (x : Key → ℝ) : Integer.Sparse.eval row18825 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block5.form2) x := by
  rw [rowCheck18825, Integer.Sparse.eval_collectBalanced, rawRowCheck18825]

def rawRow18826 : Integer.Sparse Key := [(key2766, 2), (key2772, 2), (key2766, 2), (key2887, 2), (key2889, 2), (key2843, 2), (key2889, 2), (key2843, 2), (key2887, 2), (key2910, 2), (key2880, 2), (key2910, 2), (key2587, 2), (key2593, 2), (key2587, 2), (key2966, 2), (key2968, 2), (key2843, 2), (key2968, 2), (key2843, 2), (key2966, 2), (key2989, 2), (key2880, 2), (key2989, 2), (key2390, 2), (key2394, 2), (key2378, 2), (key2394, 2), (key2378, 2), (key2390, 2), (key2437, 2), (key2443, 2), (key2406, 2), (key2443, 2), (key2406, 2), (key2437, 2), (key2503, 2), (key2524, 2), (key2480, 2), (key2524, 2), (key2480, 2), (key2503, 2), (key2576, 2), (key2580, 2), (key2571, 2), (key2580, 2), (key2571, 2), (key2576, 2), (key2394, 2), (key2383, 2), (key2394, 2), (key2443, 2), (key2411, 2), (key2443, 2), (key2509, 2), (key2524, 2), (key2484, 2), (key2524, 2), (key2484, 2), (key2509, 2)]

theorem rawRowCheck18826 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block5.form2 = rawRow18826 := by decide +kernel

def row18826 : Integer.Sparse Key := [(key2378, 4), (key2383, 2), (key2390, 4), (key2394, 8), (key2406, 4), (key2411, 2), (key2437, 4), (key2443, 8), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 8), (key2571, 4), (key2576, 4), (key2580, 4), (key2587, 4), (key2593, 2), (key2766, 4), (key2772, 2), (key2843, 8), (key2880, 4), (key2887, 4), (key2889, 4), (key2910, 4), (key2966, 4), (key2968, 4), (key2989, 4)]

theorem rowCheck18826 : row18826 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18826 := by decide +kernel

theorem rowEval18826 (x : Key → ℝ) : Integer.Sparse.eval row18826 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block5.form2) x := by
  rw [rowCheck18826, Integer.Sparse.eval_collectBalanced, rawRowCheck18826]

def rawRow18827 : Integer.Sparse Key := [(key2772, 2), (key2766, 2), (key2766, 2), (key2889, 2), (key2887, 2), (key2889, 2), (key2843, 2), (key2887, 2), (key2843, 2), (key2910, 2), (key2910, 2), (key2880, 2), (key2593, 2), (key2587, 2), (key2587, 2), (key2968, 2), (key2966, 2), (key2968, 2), (key2843, 2), (key2966, 2), (key2843, 2), (key2989, 2), (key2989, 2), (key2880, 2), (key2394, 2), (key2390, 2), (key2394, 2), (key2378, 2), (key2390, 2), (key2378, 2), (key2443, 2), (key2437, 2), (key2443, 2), (key2406, 2), (key2437, 2), (key2406, 2), (key2524, 2), (key2503, 2), (key2524, 2), (key2480, 2), (key2503, 2), (key2480, 2), (key2580, 2), (key2576, 2), (key2580, 2), (key2571, 2), (key2576, 2), (key2571, 2), (key2394, 2), (key2394, 2), (key2383, 2), (key2443, 2), (key2443, 2), (key2411, 2), (key2524, 2), (key2509, 2), (key2524, 2), (key2484, 2), (key2509, 2), (key2484, 2)]

theorem rawRowCheck18827 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block5.form2 = rawRow18827 := by decide +kernel

def row18827 : Integer.Sparse Key := [(key2378, 4), (key2383, 2), (key2390, 4), (key2394, 8), (key2406, 4), (key2411, 2), (key2437, 4), (key2443, 8), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 8), (key2571, 4), (key2576, 4), (key2580, 4), (key2587, 4), (key2593, 2), (key2766, 4), (key2772, 2), (key2843, 8), (key2880, 4), (key2887, 4), (key2889, 4), (key2910, 4), (key2966, 4), (key2968, 4), (key2989, 4)]

theorem rowCheck18827 : row18827 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18827 := by decide +kernel

theorem rowEval18827 (x : Key → ℝ) : Integer.Sparse.eval row18827 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18827, Integer.Sparse.eval_collectBalanced, rawRowCheck18827]

def rawRow18828 : Integer.Sparse Key := [(key2843, 2), (key2843, 2), (key2880, 2), (key2766, 2), (key2766, 2), (key2887, 2), (key2887, 2), (key2910, 2), (key2910, 2), (key2772, 2), (key2889, 2), (key2889, 2), (key2843, 2), (key2843, 2), (key2880, 2), (key2587, 2), (key2587, 2), (key2966, 2), (key2966, 2), (key2989, 2), (key2989, 2), (key2593, 2), (key2968, 2), (key2968, 2), (key2766, 2), (key2766, 2), (key2887, 2), (key2887, 2), (key2910, 2), (key2910, 2), (key2587, 2), (key2587, 2), (key2966, 2), (key2966, 2), (key2989, 2), (key2989, 2), (key2390, 2), (key2390, 2), (key2437, 2), (key2437, 2), (key2580, 2), (key2580, 2), (key2394, 2), (key2394, 2), (key2443, 2), (key2443, 2), (key2524, 2), (key2524, 2), (key2411, 2), (key2484, 2), (key2484, 2), (key2383, 2), (key2509, 2), (key2509, 2), (key2394, 2), (key2394, 2), (key2443, 2), (key2443, 2), (key2524, 2), (key2524, 2)]

theorem rawRowCheck18828 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block5.form2 = rawRow18828 := by decide +kernel

def row18828 : Integer.Sparse Key := [(key2383, 2), (key2390, 4), (key2394, 8), (key2411, 2), (key2437, 4), (key2443, 8), (key2484, 4), (key2509, 4), (key2524, 8), (key2580, 4), (key2587, 8), (key2593, 2), (key2766, 8), (key2772, 2), (key2843, 8), (key2880, 4), (key2887, 8), (key2889, 4), (key2910, 8), (key2966, 8), (key2968, 4), (key2989, 8)]

theorem rowCheck18828 : row18828 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18828 := by decide +kernel

theorem rowEval18828 (x : Key → ℝ) : Integer.Sparse.eval row18828 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block5.form2) x := by
  rw [rowCheck18828, Integer.Sparse.eval_collectBalanced, rawRowCheck18828]

def rawRow18829 : Integer.Sparse Key := [(key2843, 2), (key2880, 2), (key2843, 2), (key2887, 2), (key2910, 2), (key2766, 2), (key2910, 2), (key2766, 2), (key2887, 2), (key2889, 2), (key2772, 2), (key2889, 2), (key2843, 2), (key2880, 2), (key2843, 2), (key2966, 2), (key2989, 2), (key2587, 2), (key2989, 2), (key2587, 2), (key2966, 2), (key2968, 2), (key2593, 2), (key2968, 2), (key2887, 2), (key2910, 2), (key2766, 2), (key2910, 2), (key2766, 2), (key2887, 2), (key2966, 2), (key2989, 2), (key2587, 2), (key2989, 2), (key2587, 2), (key2966, 2), (key2929, 2), (key3002, 2), (key2598, 2), (key3002, 2), (key2390, 2), (key2437, 2), (key2443, 2), (key2524, 2), (key2394, 2), (key2524, 2), (key2394, 2), (key2443, 2), (key2484, 2), (key2411, 2), (key2484, 2), (key2509, 2), (key2383, 2), (key2509, 2), (key2443, 2), (key2524, 2), (key2394, 2), (key2524, 2), (key2394, 2), (key2443, 2)]

theorem rawRowCheck18829 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block5.form2 = rawRow18829 := by decide +kernel

def row18829 : Integer.Sparse Key := [(key2383, 2), (key2390, 2), (key2394, 8), (key2411, 2), (key2437, 2), (key2443, 8), (key2484, 4), (key2509, 4), (key2524, 8), (key2587, 8), (key2593, 2), (key2598, 2), (key2766, 8), (key2772, 2), (key2843, 8), (key2880, 4), (key2887, 8), (key2889, 4), (key2910, 8), (key2929, 2), (key2966, 8), (key2968, 4), (key2989, 8), (key3002, 4)]

theorem rowCheck18829 : row18829 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18829 := by decide +kernel

theorem rowEval18829 (x : Key → ℝ) : Integer.Sparse.eval row18829 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block5.form2) x := by
  rw [rowCheck18829, Integer.Sparse.eval_collectBalanced, rawRowCheck18829]

def rawRow18830 : Integer.Sparse Key := [(key2880, 2), (key2843, 2), (key2843, 2), (key2910, 2), (key2887, 2), (key2910, 2), (key2766, 2), (key2887, 2), (key2766, 2), (key2889, 2), (key2889, 2), (key2772, 2), (key2880, 2), (key2843, 2), (key2843, 2), (key2989, 2), (key2966, 2), (key2989, 2), (key2587, 2), (key2966, 2), (key2587, 2), (key2968, 2), (key2968, 2), (key2593, 2), (key2910, 2), (key2887, 2), (key2910, 2), (key2766, 2), (key2887, 2), (key2766, 2), (key2989, 2), (key2966, 2), (key2989, 2), (key2587, 2), (key2966, 2), (key2587, 2), (key3002, 2), (key2929, 2), (key3002, 2), (key2598, 2), (key2437, 2), (key2390, 2), (key2524, 2), (key2443, 2), (key2524, 2), (key2394, 2), (key2443, 2), (key2394, 2), (key2484, 2), (key2484, 2), (key2411, 2), (key2509, 2), (key2509, 2), (key2383, 2), (key2524, 2), (key2443, 2), (key2524, 2), (key2394, 2), (key2443, 2), (key2394, 2)]

theorem rawRowCheck18830 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block5.form2 = rawRow18830 := by decide +kernel

def row18830 : Integer.Sparse Key := [(key2383, 2), (key2390, 2), (key2394, 8), (key2411, 2), (key2437, 2), (key2443, 8), (key2484, 4), (key2509, 4), (key2524, 8), (key2587, 8), (key2593, 2), (key2598, 2), (key2766, 8), (key2772, 2), (key2843, 8), (key2880, 4), (key2887, 8), (key2889, 4), (key2910, 8), (key2929, 2), (key2966, 8), (key2968, 4), (key2989, 8), (key3002, 4)]

theorem rowCheck18830 : row18830 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18830 := by decide +kernel

theorem rowEval18830 (x : Key → ℝ) : Integer.Sparse.eval row18830 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block5.form2) x := by
  rw [rowCheck18830, Integer.Sparse.eval_collectBalanced, rawRowCheck18830]

def rawRow18831 : Integer.Sparse Key := [(key2887, 2), (key2889, 2), (key2910, 2), (key2766, 2), (key2772, 2), (key2843, 2), (key2889, 2), (key2880, 2), (key2910, 2), (key2766, 2), (key2843, 2), (key2887, 2), (key2966, 2), (key2968, 2), (key2989, 2), (key2587, 2), (key2593, 2), (key2843, 2), (key2968, 2), (key2880, 2), (key2989, 2), (key2587, 2), (key2843, 2), (key2966, 2), (key2929, 2), (key2931, 2), (key2966, 2), (key2995, 2), (key2989, 2), (key3002, 2), (key2598, 2), (key2600, 2), (key2887, 2), (key2995, 2), (key2910, 2), (key3002, 2), (key2587, 2), (key2600, 2), (key2766, 2), (key2931, 2), (key2910, 2), (key2989, 2), (key2378, 2), (key2390, 2), (key2406, 2), (key2437, 2), (key2480, 2), (key2503, 2), (key2443, 2), (key2509, 2), (key2524, 2), (key2394, 2), (key2484, 2), (key2524, 2), (key2383, 2), (key2394, 2), (key2411, 2), (key2443, 2), (key2484, 2), (key2509, 2)]

theorem rawRowCheck18831 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block5.form2 = rawRow18831 := by decide +kernel

def row18831 : Integer.Sparse Key := [(key2378, 2), (key2383, 2), (key2390, 2), (key2394, 4), (key2406, 2), (key2411, 2), (key2437, 2), (key2443, 4), (key2480, 2), (key2484, 4), (key2503, 2), (key2509, 4), (key2524, 4), (key2587, 6), (key2593, 2), (key2598, 2), (key2600, 4), (key2766, 6), (key2772, 2), (key2843, 8), (key2880, 4), (key2887, 6), (key2889, 4), (key2910, 8), (key2929, 2), (key2931, 4), (key2966, 6), (key2968, 4), (key2989, 8), (key2995, 4), (key3002, 4)]

theorem rowCheck18831 : row18831 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18831 := by decide +kernel

theorem rowEval18831 (x : Key → ℝ) : Integer.Sparse.eval row18831 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block5.form2) x := by
  rw [rowCheck18831, Integer.Sparse.eval_collectBalanced, rawRowCheck18831]

def rawRow18832 : Integer.Sparse Key := [(key2889, 2), (key2887, 2), (key2910, 2), (key2772, 2), (key2766, 2), (key2889, 2), (key2843, 2), (key2910, 2), (key2880, 2), (key2766, 2), (key2887, 2), (key2843, 2), (key2968, 2), (key2966, 2), (key2989, 2), (key2593, 2), (key2587, 2), (key2968, 2), (key2843, 2), (key2989, 2), (key2880, 2), (key2587, 2), (key2966, 2), (key2843, 2), (key2931, 2), (key2929, 2), (key2995, 2), (key2966, 2), (key3002, 2), (key2989, 2), (key2600, 2), (key2598, 2), (key2995, 2), (key2887, 2), (key3002, 2), (key2910, 2), (key2600, 2), (key2587, 2), (key2931, 2), (key2766, 2), (key2989, 2), (key2910, 2), (key2390, 2), (key2378, 2), (key2437, 2), (key2406, 2), (key2503, 2), (key2480, 2), (key2443, 2), (key2524, 2), (key2509, 2), (key2394, 2), (key2524, 2), (key2484, 2), (key2394, 2), (key2383, 2), (key2443, 2), (key2411, 2), (key2509, 2), (key2484, 2)]

theorem rawRowCheck18832 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block5.form2 = rawRow18832 := by decide +kernel

def row18832 : Integer.Sparse Key := [(key2378, 2), (key2383, 2), (key2390, 2), (key2394, 4), (key2406, 2), (key2411, 2), (key2437, 2), (key2443, 4), (key2480, 2), (key2484, 4), (key2503, 2), (key2509, 4), (key2524, 4), (key2587, 6), (key2593, 2), (key2598, 2), (key2600, 4), (key2766, 6), (key2772, 2), (key2843, 8), (key2880, 4), (key2887, 6), (key2889, 4), (key2910, 8), (key2929, 2), (key2931, 4), (key2966, 6), (key2968, 4), (key2989, 8), (key2995, 4), (key3002, 4)]

theorem rowCheck18832 : row18832 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18832 := by decide +kernel

theorem rowEval18832 (x : Key → ℝ) : Integer.Sparse.eval row18832 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18832, Integer.Sparse.eval_collectBalanced, rawRowCheck18832]

def rawRow18833 : Integer.Sparse Key := [(key2887, 2), (key2910, 2), (key2889, 2), (key2843, 2), (key2880, 2), (key2766, 2), (key2910, 2), (key2772, 2), (key2889, 2), (key2843, 2), (key2766, 2), (key2887, 2), (key2966, 2), (key2989, 2), (key2968, 2), (key2843, 2), (key2880, 2), (key2587, 2), (key2989, 2), (key2593, 2), (key2968, 2), (key2843, 2), (key2587, 2), (key2966, 2), (key2966, 2), (key2989, 2), (key2929, 2), (key3002, 2), (key2931, 2), (key2995, 2), (key2887, 2), (key2910, 2), (key2598, 2), (key3002, 2), (key2600, 2), (key2995, 2), (key2766, 2), (key2910, 2), (key2587, 2), (key2989, 2), (key2600, 2), (key2931, 2), (key2406, 2), (key2480, 2), (key2378, 2), (key2503, 2), (key2390, 2), (key2437, 2), (key2509, 2), (key2443, 2), (key2524, 2), (key2484, 2), (key2394, 2), (key2524, 2), (key2411, 2), (key2484, 2), (key2383, 2), (key2509, 2), (key2394, 2), (key2443, 2)]

theorem rawRowCheck18833 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block5.form2 = rawRow18833 := by decide +kernel

def row18833 : Integer.Sparse Key := [(key2378, 2), (key2383, 2), (key2390, 2), (key2394, 4), (key2406, 2), (key2411, 2), (key2437, 2), (key2443, 4), (key2480, 2), (key2484, 4), (key2503, 2), (key2509, 4), (key2524, 4), (key2587, 6), (key2593, 2), (key2598, 2), (key2600, 4), (key2766, 6), (key2772, 2), (key2843, 8), (key2880, 4), (key2887, 6), (key2889, 4), (key2910, 8), (key2929, 2), (key2931, 4), (key2966, 6), (key2968, 4), (key2989, 8), (key2995, 4), (key3002, 4)]

theorem rowCheck18833 : row18833 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18833 := by decide +kernel

theorem rowEval18833 (x : Key → ℝ) : Integer.Sparse.eval row18833 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block5.form2) x := by
  rw [rowCheck18833, Integer.Sparse.eval_collectBalanced, rawRowCheck18833]

def rawRow18834 : Integer.Sparse Key := [(key2910, 2), (key2887, 2), (key2889, 2), (key2880, 2), (key2843, 2), (key2910, 2), (key2766, 2), (key2889, 2), (key2772, 2), (key2843, 2), (key2887, 2), (key2766, 2), (key2989, 2), (key2966, 2), (key2968, 2), (key2880, 2), (key2843, 2), (key2989, 2), (key2587, 2), (key2968, 2), (key2593, 2), (key2843, 2), (key2966, 2), (key2587, 2), (key2989, 2), (key2966, 2), (key3002, 2), (key2929, 2), (key2995, 2), (key2931, 2), (key2910, 2), (key2887, 2), (key3002, 2), (key2598, 2), (key2995, 2), (key2600, 2), (key2910, 2), (key2766, 2), (key2989, 2), (key2587, 2), (key2931, 2), (key2600, 2), (key2480, 2), (key2406, 2), (key2503, 2), (key2378, 2), (key2437, 2), (key2390, 2), (key2509, 2), (key2524, 2), (key2443, 2), (key2484, 2), (key2524, 2), (key2394, 2), (key2484, 2), (key2411, 2), (key2509, 2), (key2383, 2), (key2443, 2), (key2394, 2)]

theorem rawRowCheck18834 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block5.form2 = rawRow18834 := by decide +kernel

def row18834 : Integer.Sparse Key := [(key2378, 2), (key2383, 2), (key2390, 2), (key2394, 4), (key2406, 2), (key2411, 2), (key2437, 2), (key2443, 4), (key2480, 2), (key2484, 4), (key2503, 2), (key2509, 4), (key2524, 4), (key2587, 6), (key2593, 2), (key2598, 2), (key2600, 4), (key2766, 6), (key2772, 2), (key2843, 8), (key2880, 4), (key2887, 6), (key2889, 4), (key2910, 8), (key2929, 2), (key2931, 4), (key2966, 6), (key2968, 4), (key2989, 8), (key2995, 4), (key3002, 4)]

theorem rowCheck18834 : row18834 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18834 := by decide +kernel

theorem rowEval18834 (x : Key → ℝ) : Integer.Sparse.eval row18834 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block5.form2) x := by
  rw [rowCheck18834, Integer.Sparse.eval_collectBalanced, rawRowCheck18834]

def rawRow18835 : Integer.Sparse Key := [(key2889, 2), (key2910, 2), (key2887, 2), (key2889, 2), (key2910, 2), (key2772, 2), (key2880, 2), (key2766, 2), (key2843, 2), (key2887, 2), (key2766, 2), (key2843, 2), (key2968, 2), (key2989, 2), (key2966, 2), (key2968, 2), (key2989, 2), (key2593, 2), (key2880, 2), (key2587, 2), (key2843, 2), (key2966, 2), (key2587, 2), (key2843, 2), (key2995, 2), (key3002, 2), (key2931, 2), (key2989, 2), (key2929, 2), (key2966, 2), (key2995, 2), (key3002, 2), (key2600, 2), (key2910, 2), (key2598, 2), (key2887, 2), (key2931, 2), (key2989, 2), (key2600, 2), (key2910, 2), (key2587, 2), (key2766, 2), (key2437, 2), (key2503, 2), (key2390, 2), (key2480, 2), (key2378, 2), (key2406, 2), (key2524, 2), (key2443, 2), (key2509, 2), (key2524, 2), (key2394, 2), (key2484, 2), (key2443, 2), (key2509, 2), (key2394, 2), (key2484, 2), (key2383, 2), (key2411, 2)]

theorem rawRowCheck18835 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block5.form2 = rawRow18835 := by decide +kernel

def row18835 : Integer.Sparse Key := [(key2378, 2), (key2383, 2), (key2390, 2), (key2394, 4), (key2406, 2), (key2411, 2), (key2437, 2), (key2443, 4), (key2480, 2), (key2484, 4), (key2503, 2), (key2509, 4), (key2524, 4), (key2587, 6), (key2593, 2), (key2598, 2), (key2600, 4), (key2766, 6), (key2772, 2), (key2843, 8), (key2880, 4), (key2887, 6), (key2889, 4), (key2910, 8), (key2929, 2), (key2931, 4), (key2966, 6), (key2968, 4), (key2989, 8), (key2995, 4), (key3002, 4)]

theorem rowCheck18835 : row18835 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18835 := by decide +kernel

theorem rowEval18835 (x : Key → ℝ) : Integer.Sparse.eval row18835 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18835, Integer.Sparse.eval_collectBalanced, rawRowCheck18835]

def rawRow18836 : Integer.Sparse Key := [(key2910, 2), (key2889, 2), (key2887, 2), (key2910, 2), (key2889, 2), (key2880, 2), (key2772, 2), (key2843, 2), (key2766, 2), (key2887, 2), (key2843, 2), (key2766, 2), (key2989, 2), (key2968, 2), (key2966, 2), (key2989, 2), (key2968, 2), (key2880, 2), (key2593, 2), (key2843, 2), (key2587, 2), (key2966, 2), (key2843, 2), (key2587, 2), (key3002, 2), (key2995, 2), (key2989, 2), (key2931, 2), (key2966, 2), (key2929, 2), (key3002, 2), (key2995, 2), (key2910, 2), (key2600, 2), (key2887, 2), (key2598, 2), (key2989, 2), (key2931, 2), (key2910, 2), (key2600, 2), (key2766, 2), (key2587, 2), (key2503, 2), (key2437, 2), (key2480, 2), (key2390, 2), (key2406, 2), (key2378, 2), (key2524, 2), (key2509, 2), (key2443, 2), (key2524, 2), (key2484, 2), (key2394, 2), (key2509, 2), (key2443, 2), (key2484, 2), (key2394, 2), (key2411, 2), (key2383, 2)]

theorem rawRowCheck18836 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block5.form2 = rawRow18836 := by decide +kernel

def row18836 : Integer.Sparse Key := [(key2378, 2), (key2383, 2), (key2390, 2), (key2394, 4), (key2406, 2), (key2411, 2), (key2437, 2), (key2443, 4), (key2480, 2), (key2484, 4), (key2503, 2), (key2509, 4), (key2524, 4), (key2587, 6), (key2593, 2), (key2598, 2), (key2600, 4), (key2766, 6), (key2772, 2), (key2843, 8), (key2880, 4), (key2887, 6), (key2889, 4), (key2910, 8), (key2929, 2), (key2931, 4), (key2966, 6), (key2968, 4), (key2989, 8), (key2995, 4), (key3002, 4)]

theorem rowCheck18836 : row18836 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18836 := by decide +kernel

theorem rowEval18836 (x : Key → ℝ) : Integer.Sparse.eval row18836 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block5.form2) x := by
  rw [rowCheck18836, Integer.Sparse.eval_collectBalanced, rawRowCheck18836]

def rawRow18837 : Integer.Sparse Key := [(key2929, 2), (key2931, 2), (key2931, 2), (key2966, 2), (key2968, 2), (key2966, 2), (key2995, 2), (key2968, 2), (key2995, 2), (key2989, 2), (key2989, 2), (key3002, 2), (key2598, 2), (key2600, 2), (key2600, 2), (key2887, 2), (key2889, 2), (key2887, 2), (key2995, 2), (key2889, 2), (key2995, 2), (key2910, 2), (key2910, 2), (key3002, 2), (key2587, 2), (key2593, 2), (key2587, 2), (key2600, 2), (key2593, 2), (key2600, 2), (key2766, 2), (key2772, 2), (key2766, 2), (key2931, 2), (key2772, 2), (key2931, 2), (key2843, 2), (key2889, 2), (key2843, 2), (key2968, 2), (key2889, 2), (key2968, 2), (key2880, 2), (key2910, 2), (key2880, 2), (key2989, 2), (key2910, 2), (key2989, 2), (key2378, 2), (key2378, 2), (key2390, 2), (key2406, 2), (key2406, 2), (key2437, 2), (key2472, 2), (key2480, 2), (key2472, 2), (key2503, 2), (key2480, 2), (key2503, 2)]

theorem rawRowCheck18837 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block5.form2 = rawRow18837 := by decide +kernel

def row18837 : Integer.Sparse Key := [(key2378, 4), (key2390, 2), (key2406, 4), (key2437, 2), (key2472, 4), (key2480, 4), (key2503, 4), (key2587, 4), (key2593, 4), (key2598, 2), (key2600, 8), (key2766, 4), (key2772, 4), (key2843, 4), (key2880, 4), (key2887, 4), (key2889, 8), (key2910, 8), (key2929, 2), (key2931, 8), (key2966, 4), (key2968, 8), (key2989, 8), (key2995, 8), (key3002, 4)]

theorem rowCheck18837 : row18837 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18837 := by decide +kernel

theorem rowEval18837 (x : Key → ℝ) : Integer.Sparse.eval row18837 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block5.form2) x := by
  rw [rowCheck18837, Integer.Sparse.eval_collectBalanced, rawRowCheck18837]

def rawRow18838 : Integer.Sparse Key := [(key2931, 2), (key2929, 2), (key2931, 2), (key2968, 2), (key2966, 2), (key2995, 2), (key2966, 2), (key2995, 2), (key2968, 2), (key2989, 2), (key3002, 2), (key2989, 2), (key2600, 2), (key2598, 2), (key2600, 2), (key2889, 2), (key2887, 2), (key2995, 2), (key2887, 2), (key2995, 2), (key2889, 2), (key2910, 2), (key3002, 2), (key2910, 2), (key2593, 2), (key2587, 2), (key2600, 2), (key2587, 2), (key2600, 2), (key2593, 2), (key2772, 2), (key2766, 2), (key2931, 2), (key2766, 2), (key2931, 2), (key2772, 2), (key2889, 2), (key2843, 2), (key2968, 2), (key2843, 2), (key2968, 2), (key2889, 2), (key2910, 2), (key2880, 2), (key2989, 2), (key2880, 2), (key2989, 2), (key2910, 2), (key2378, 2), (key2390, 2), (key2378, 2), (key2406, 2), (key2437, 2), (key2406, 2), (key2480, 2), (key2472, 2), (key2503, 2), (key2472, 2), (key2503, 2), (key2480, 2)]

theorem rawRowCheck18838 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block5.form2 = rawRow18838 := by decide +kernel

def row18838 : Integer.Sparse Key := [(key2378, 4), (key2390, 2), (key2406, 4), (key2437, 2), (key2472, 4), (key2480, 4), (key2503, 4), (key2587, 4), (key2593, 4), (key2598, 2), (key2600, 8), (key2766, 4), (key2772, 4), (key2843, 4), (key2880, 4), (key2887, 4), (key2889, 8), (key2910, 8), (key2929, 2), (key2931, 8), (key2966, 4), (key2968, 8), (key2989, 8), (key2995, 8), (key3002, 4)]

theorem rowCheck18838 : row18838 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18838 := by decide +kernel

theorem rowEval18838 (x : Key → ℝ) : Integer.Sparse.eval row18838 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18838, Integer.Sparse.eval_collectBalanced, rawRowCheck18838]

def rawRow18839 : Integer.Sparse Key := [(key2931, 2), (key2931, 2), (key2929, 2), (key2995, 2), (key2995, 2), (key2968, 2), (key2968, 2), (key2966, 2), (key2966, 2), (key3002, 2), (key2989, 2), (key2989, 2), (key2600, 2), (key2600, 2), (key2598, 2), (key2995, 2), (key2995, 2), (key2889, 2), (key2889, 2), (key2887, 2), (key2887, 2), (key3002, 2), (key2910, 2), (key2910, 2), (key2600, 2), (key2600, 2), (key2593, 2), (key2593, 2), (key2587, 2), (key2587, 2), (key2931, 2), (key2931, 2), (key2772, 2), (key2772, 2), (key2766, 2), (key2766, 2), (key2968, 2), (key2968, 2), (key2889, 2), (key2889, 2), (key2843, 2), (key2843, 2), (key2989, 2), (key2989, 2), (key2910, 2), (key2910, 2), (key2880, 2), (key2880, 2), (key2390, 2), (key2378, 2), (key2378, 2), (key2437, 2), (key2406, 2), (key2406, 2), (key2503, 2), (key2503, 2), (key2480, 2), (key2480, 2), (key2472, 2), (key2472, 2)]

theorem rawRowCheck18839 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block5.form2 = rawRow18839 := by decide +kernel

def row18839 : Integer.Sparse Key := [(key2378, 4), (key2390, 2), (key2406, 4), (key2437, 2), (key2472, 4), (key2480, 4), (key2503, 4), (key2587, 4), (key2593, 4), (key2598, 2), (key2600, 8), (key2766, 4), (key2772, 4), (key2843, 4), (key2880, 4), (key2887, 4), (key2889, 8), (key2910, 8), (key2929, 2), (key2931, 8), (key2966, 4), (key2968, 8), (key2989, 8), (key2995, 8), (key3002, 4)]

theorem rowCheck18839 : row18839 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18839 := by decide +kernel

theorem rowEval18839 (x : Key → ℝ) : Integer.Sparse.eval row18839 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18839, Integer.Sparse.eval_collectBalanced, rawRowCheck18839]

def rawRow18840 : Integer.Sparse Key := [(key2966, 2), (key2968, 2), (key2989, 2), (key2929, 2), (key2931, 2), (key2966, 2), (key2995, 2), (key2989, 2), (key3002, 2), (key2931, 2), (key2968, 2), (key2995, 2), (key2887, 2), (key2889, 2), (key2910, 2), (key2598, 2), (key2600, 2), (key2887, 2), (key2995, 2), (key2910, 2), (key3002, 2), (key2600, 2), (key2889, 2), (key2995, 2), (key2766, 2), (key2772, 2), (key2843, 2), (key2889, 2), (key2880, 2), (key2910, 2), (key2587, 2), (key2593, 2), (key2843, 2), (key2968, 2), (key2880, 2), (key2989, 2), (key2587, 2), (key2600, 2), (key2766, 2), (key2931, 2), (key2910, 2), (key2989, 2), (key2593, 2), (key2600, 2), (key2772, 2), (key2931, 2), (key2889, 2), (key2968, 2), (key2406, 2), (key2472, 2), (key2480, 2), (key2378, 2), (key2472, 2), (key2503, 2), (key2378, 2), (key2390, 2), (key2406, 2), (key2437, 2), (key2480, 2), (key2503, 2)]

theorem rawRowCheck18840 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block5.form2 = rawRow18840 := by decide +kernel

def row18840 : Integer.Sparse Key := [(key2378, 4), (key2390, 2), (key2406, 4), (key2437, 2), (key2472, 4), (key2480, 4), (key2503, 4), (key2587, 4), (key2593, 4), (key2598, 2), (key2600, 8), (key2766, 4), (key2772, 4), (key2843, 4), (key2880, 4), (key2887, 4), (key2889, 8), (key2910, 8), (key2929, 2), (key2931, 8), (key2966, 4), (key2968, 8), (key2989, 8), (key2995, 8), (key3002, 4)]

theorem rowCheck18840 : row18840 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18840 := by decide +kernel

theorem rowEval18840 (x : Key → ℝ) : Integer.Sparse.eval row18840 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block5.form2) x := by
  rw [rowCheck18840, Integer.Sparse.eval_collectBalanced, rawRowCheck18840]

def rawRow18841 : Integer.Sparse Key := [(key2968, 2), (key2966, 2), (key2989, 2), (key2931, 2), (key2929, 2), (key2995, 2), (key2966, 2), (key3002, 2), (key2989, 2), (key2931, 2), (key2995, 2), (key2968, 2), (key2889, 2), (key2887, 2), (key2910, 2), (key2600, 2), (key2598, 2), (key2995, 2), (key2887, 2), (key3002, 2), (key2910, 2), (key2600, 2), (key2995, 2), (key2889, 2), (key2772, 2), (key2766, 2), (key2889, 2), (key2843, 2), (key2910, 2), (key2880, 2), (key2593, 2), (key2587, 2), (key2968, 2), (key2843, 2), (key2989, 2), (key2880, 2), (key2600, 2), (key2587, 2), (key2931, 2), (key2766, 2), (key2989, 2), (key2910, 2), (key2600, 2), (key2593, 2), (key2931, 2), (key2772, 2), (key2968, 2), (key2889, 2), (key2406, 2), (key2480, 2), (key2472, 2), (key2378, 2), (key2503, 2), (key2472, 2), (key2390, 2), (key2378, 2), (key2437, 2), (key2406, 2), (key2503, 2), (key2480, 2)]

theorem rawRowCheck18841 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block5.form2 = rawRow18841 := by decide +kernel

def row18841 : Integer.Sparse Key := [(key2378, 4), (key2390, 2), (key2406, 4), (key2437, 2), (key2472, 4), (key2480, 4), (key2503, 4), (key2587, 4), (key2593, 4), (key2598, 2), (key2600, 8), (key2766, 4), (key2772, 4), (key2843, 4), (key2880, 4), (key2887, 4), (key2889, 8), (key2910, 8), (key2929, 2), (key2931, 8), (key2966, 4), (key2968, 8), (key2989, 8), (key2995, 8), (key3002, 4)]

theorem rowCheck18841 : row18841 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18841 := by decide +kernel

theorem rowEval18841 (x : Key → ℝ) : Integer.Sparse.eval row18841 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18841, Integer.Sparse.eval_collectBalanced, rawRowCheck18841]

def rawRow18842 : Integer.Sparse Key := [(key2966, 2), (key2989, 2), (key2968, 2), (key2966, 2), (key2989, 2), (key2929, 2), (key3002, 2), (key2931, 2), (key2995, 2), (key2968, 2), (key2931, 2), (key2995, 2), (key2887, 2), (key2910, 2), (key2889, 2), (key2887, 2), (key2910, 2), (key2598, 2), (key3002, 2), (key2600, 2), (key2995, 2), (key2889, 2), (key2600, 2), (key2995, 2), (key2843, 2), (key2880, 2), (key2766, 2), (key2910, 2), (key2772, 2), (key2889, 2), (key2843, 2), (key2880, 2), (key2587, 2), (key2989, 2), (key2593, 2), (key2968, 2), (key2766, 2), (key2910, 2), (key2587, 2), (key2989, 2), (key2600, 2), (key2931, 2), (key2772, 2), (key2889, 2), (key2593, 2), (key2968, 2), (key2600, 2), (key2931, 2), (key2472, 2), (key2406, 2), (key2480, 2), (key2472, 2), (key2378, 2), (key2503, 2), (key2406, 2), (key2480, 2), (key2378, 2), (key2503, 2), (key2390, 2), (key2437, 2)]

theorem rawRowCheck18842 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block5.form2 = rawRow18842 := by decide +kernel

def row18842 : Integer.Sparse Key := [(key2378, 4), (key2390, 2), (key2406, 4), (key2437, 2), (key2472, 4), (key2480, 4), (key2503, 4), (key2587, 4), (key2593, 4), (key2598, 2), (key2600, 8), (key2766, 4), (key2772, 4), (key2843, 4), (key2880, 4), (key2887, 4), (key2889, 8), (key2910, 8), (key2929, 2), (key2931, 8), (key2966, 4), (key2968, 8), (key2989, 8), (key2995, 8), (key3002, 4)]

theorem rowCheck18842 : row18842 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18842 := by decide +kernel

theorem rowEval18842 (x : Key → ℝ) : Integer.Sparse.eval row18842 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block5.form2) x := by
  rw [rowCheck18842, Integer.Sparse.eval_collectBalanced, rawRowCheck18842]

def rawRow18843 : Integer.Sparse Key := [(key2989, 2), (key2966, 2), (key2968, 2), (key2989, 2), (key2966, 2), (key3002, 2), (key2929, 2), (key2995, 2), (key2931, 2), (key2968, 2), (key2995, 2), (key2931, 2), (key2910, 2), (key2887, 2), (key2889, 2), (key2910, 2), (key2887, 2), (key3002, 2), (key2598, 2), (key2995, 2), (key2600, 2), (key2889, 2), (key2995, 2), (key2600, 2), (key2880, 2), (key2843, 2), (key2910, 2), (key2766, 2), (key2889, 2), (key2772, 2), (key2880, 2), (key2843, 2), (key2989, 2), (key2587, 2), (key2968, 2), (key2593, 2), (key2910, 2), (key2766, 2), (key2989, 2), (key2587, 2), (key2931, 2), (key2600, 2), (key2889, 2), (key2772, 2), (key2968, 2), (key2593, 2), (key2931, 2), (key2600, 2), (key2472, 2), (key2480, 2), (key2406, 2), (key2472, 2), (key2503, 2), (key2378, 2), (key2480, 2), (key2406, 2), (key2503, 2), (key2378, 2), (key2437, 2), (key2390, 2)]

theorem rawRowCheck18843 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block5.form2 = rawRow18843 := by decide +kernel

def row18843 : Integer.Sparse Key := [(key2378, 4), (key2390, 2), (key2406, 4), (key2437, 2), (key2472, 4), (key2480, 4), (key2503, 4), (key2587, 4), (key2593, 4), (key2598, 2), (key2600, 8), (key2766, 4), (key2772, 4), (key2843, 4), (key2880, 4), (key2887, 4), (key2889, 8), (key2910, 8), (key2929, 2), (key2931, 8), (key2966, 4), (key2968, 8), (key2989, 8), (key2995, 8), (key3002, 4)]

theorem rowCheck18843 : row18843 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18843 := by decide +kernel

theorem rowEval18843 (x : Key → ℝ) : Integer.Sparse.eval row18843 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block5.form2) x := by
  rw [rowCheck18843, Integer.Sparse.eval_collectBalanced, rawRowCheck18843]

def rawRow18844 : Integer.Sparse Key := [(key2968, 2), (key2989, 2), (key2966, 2), (key2995, 2), (key3002, 2), (key2931, 2), (key2989, 2), (key2929, 2), (key2966, 2), (key2995, 2), (key2931, 2), (key2968, 2), (key2889, 2), (key2910, 2), (key2887, 2), (key2995, 2), (key3002, 2), (key2600, 2), (key2910, 2), (key2598, 2), (key2887, 2), (key2995, 2), (key2600, 2), (key2889, 2), (key2889, 2), (key2910, 2), (key2772, 2), (key2880, 2), (key2766, 2), (key2843, 2), (key2968, 2), (key2989, 2), (key2593, 2), (key2880, 2), (key2587, 2), (key2843, 2), (key2931, 2), (key2989, 2), (key2600, 2), (key2910, 2), (key2587, 2), (key2766, 2), (key2931, 2), (key2968, 2), (key2600, 2), (key2889, 2), (key2593, 2), (key2772, 2), (key2480, 2), (key2406, 2), (key2472, 2), (key2503, 2), (key2378, 2), (key2472, 2), (key2437, 2), (key2503, 2), (key2390, 2), (key2480, 2), (key2378, 2), (key2406, 2)]

theorem rawRowCheck18844 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block5.form2 = rawRow18844 := by decide +kernel

def row18844 : Integer.Sparse Key := [(key2378, 4), (key2390, 2), (key2406, 4), (key2437, 2), (key2472, 4), (key2480, 4), (key2503, 4), (key2587, 4), (key2593, 4), (key2598, 2), (key2600, 8), (key2766, 4), (key2772, 4), (key2843, 4), (key2880, 4), (key2887, 4), (key2889, 8), (key2910, 8), (key2929, 2), (key2931, 8), (key2966, 4), (key2968, 8), (key2989, 8), (key2995, 8), (key3002, 4)]

theorem rowCheck18844 : row18844 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18844 := by decide +kernel

theorem rowEval18844 (x : Key → ℝ) : Integer.Sparse.eval row18844 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18844, Integer.Sparse.eval_collectBalanced, rawRowCheck18844]

def rawRow18845 : Integer.Sparse Key := [(key2989, 2), (key2968, 2), (key2966, 2), (key3002, 2), (key2995, 2), (key2989, 2), (key2931, 2), (key2966, 2), (key2929, 2), (key2995, 2), (key2968, 2), (key2931, 2), (key2910, 2), (key2889, 2), (key2887, 2), (key3002, 2), (key2995, 2), (key2910, 2), (key2600, 2), (key2887, 2), (key2598, 2), (key2995, 2), (key2889, 2), (key2600, 2), (key2910, 2), (key2889, 2), (key2880, 2), (key2772, 2), (key2843, 2), (key2766, 2), (key2989, 2), (key2968, 2), (key2880, 2), (key2593, 2), (key2843, 2), (key2587, 2), (key2989, 2), (key2931, 2), (key2910, 2), (key2600, 2), (key2766, 2), (key2587, 2), (key2968, 2), (key2931, 2), (key2889, 2), (key2600, 2), (key2772, 2), (key2593, 2), (key2480, 2), (key2472, 2), (key2406, 2), (key2503, 2), (key2472, 2), (key2378, 2), (key2503, 2), (key2437, 2), (key2480, 2), (key2390, 2), (key2406, 2), (key2378, 2)]

theorem rawRowCheck18845 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block5.form2 = rawRow18845 := by decide +kernel

def row18845 : Integer.Sparse Key := [(key2378, 4), (key2390, 2), (key2406, 4), (key2437, 2), (key2472, 4), (key2480, 4), (key2503, 4), (key2587, 4), (key2593, 4), (key2598, 2), (key2600, 8), (key2766, 4), (key2772, 4), (key2843, 4), (key2880, 4), (key2887, 4), (key2889, 8), (key2910, 8), (key2929, 2), (key2931, 8), (key2966, 4), (key2968, 8), (key2989, 8), (key2995, 8), (key3002, 4)]

theorem rowCheck18845 : row18845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18845 := by decide +kernel

theorem rowEval18845 (x : Key → ℝ) : Integer.Sparse.eval row18845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block5.form2) x := by
  rw [rowCheck18845, Integer.Sparse.eval_collectBalanced, rawRowCheck18845]

def rawRow18846 : Integer.Sparse Key := [(key2995, 2), (key2995, 2), (key3002, 2), (key2931, 2), (key2931, 2), (key2968, 2), (key2968, 2), (key2989, 2), (key2989, 2), (key2929, 2), (key2966, 2), (key2966, 2), (key2995, 2), (key2995, 2), (key3002, 2), (key2600, 2), (key2600, 2), (key2889, 2), (key2889, 2), (key2910, 2), (key2910, 2), (key2598, 2), (key2887, 2), (key2887, 2), (key2931, 2), (key2931, 2), (key2968, 2), (key2968, 2), (key2989, 2), (key2989, 2), (key2600, 2), (key2600, 2), (key2889, 2), (key2889, 2), (key2910, 2), (key2910, 2), (key2593, 2), (key2593, 2), (key2772, 2), (key2772, 2), (key2880, 2), (key2880, 2), (key2587, 2), (key2587, 2), (key2766, 2), (key2766, 2), (key2843, 2), (key2843, 2), (key2437, 2), (key2503, 2), (key2503, 2), (key2390, 2), (key2480, 2), (key2480, 2), (key2378, 2), (key2378, 2), (key2406, 2), (key2406, 2), (key2472, 2), (key2472, 2)]

theorem rawRowCheck18846 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block5.form2 = rawRow18846 := by decide +kernel

def row18846 : Integer.Sparse Key := [(key2378, 4), (key2390, 2), (key2406, 4), (key2437, 2), (key2472, 4), (key2480, 4), (key2503, 4), (key2587, 4), (key2593, 4), (key2598, 2), (key2600, 8), (key2766, 4), (key2772, 4), (key2843, 4), (key2880, 4), (key2887, 4), (key2889, 8), (key2910, 8), (key2929, 2), (key2931, 8), (key2966, 4), (key2968, 8), (key2989, 8), (key2995, 8), (key3002, 4)]

theorem rowCheck18846 : row18846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18846 := by decide +kernel

theorem rowEval18846 (x : Key → ℝ) : Integer.Sparse.eval row18846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18846, Integer.Sparse.eval_collectBalanced, rawRowCheck18846]

def rawRow18847 : Integer.Sparse Key := [(key2995, 2), (key3002, 2), (key2995, 2), (key2968, 2), (key2989, 2), (key2931, 2), (key2989, 2), (key2931, 2), (key2968, 2), (key2966, 2), (key2929, 2), (key2966, 2), (key2995, 2), (key3002, 2), (key2995, 2), (key2889, 2), (key2910, 2), (key2600, 2), (key2910, 2), (key2600, 2), (key2889, 2), (key2887, 2), (key2598, 2), (key2887, 2), (key2968, 2), (key2989, 2), (key2931, 2), (key2989, 2), (key2931, 2), (key2968, 2), (key2889, 2), (key2910, 2), (key2600, 2), (key2910, 2), (key2600, 2), (key2889, 2), (key2772, 2), (key2880, 2), (key2593, 2), (key2880, 2), (key2593, 2), (key2772, 2), (key2766, 2), (key2843, 2), (key2587, 2), (key2843, 2), (key2587, 2), (key2766, 2), (key2503, 2), (key2437, 2), (key2503, 2), (key2480, 2), (key2390, 2), (key2480, 2), (key2406, 2), (key2472, 2), (key2378, 2), (key2472, 2), (key2378, 2), (key2406, 2)]

theorem rawRowCheck18847 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block5.form2 = rawRow18847 := by decide +kernel

def row18847 : Integer.Sparse Key := [(key2378, 4), (key2390, 2), (key2406, 4), (key2437, 2), (key2472, 4), (key2480, 4), (key2503, 4), (key2587, 4), (key2593, 4), (key2598, 2), (key2600, 8), (key2766, 4), (key2772, 4), (key2843, 4), (key2880, 4), (key2887, 4), (key2889, 8), (key2910, 8), (key2929, 2), (key2931, 8), (key2966, 4), (key2968, 8), (key2989, 8), (key2995, 8), (key3002, 4)]

theorem rowCheck18847 : row18847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18847 := by decide +kernel

theorem rowEval18847 (x : Key → ℝ) : Integer.Sparse.eval row18847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18847, Integer.Sparse.eval_collectBalanced, rawRowCheck18847]

def rawRow18848 : Integer.Sparse Key := [(key3002, 2), (key2995, 2), (key2995, 2), (key2989, 2), (key2968, 2), (key2989, 2), (key2931, 2), (key2968, 2), (key2931, 2), (key2966, 2), (key2966, 2), (key2929, 2), (key3002, 2), (key2995, 2), (key2995, 2), (key2910, 2), (key2889, 2), (key2910, 2), (key2600, 2), (key2889, 2), (key2600, 2), (key2887, 2), (key2887, 2), (key2598, 2), (key2989, 2), (key2968, 2), (key2989, 2), (key2931, 2), (key2968, 2), (key2931, 2), (key2910, 2), (key2889, 2), (key2910, 2), (key2600, 2), (key2889, 2), (key2600, 2), (key2880, 2), (key2772, 2), (key2880, 2), (key2593, 2), (key2772, 2), (key2593, 2), (key2843, 2), (key2766, 2), (key2843, 2), (key2587, 2), (key2766, 2), (key2587, 2), (key2503, 2), (key2503, 2), (key2437, 2), (key2480, 2), (key2480, 2), (key2390, 2), (key2472, 2), (key2406, 2), (key2472, 2), (key2378, 2), (key2406, 2), (key2378, 2)]

theorem rawRowCheck18848 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block5.form2 = rawRow18848 := by decide +kernel

def row18848 : Integer.Sparse Key := [(key2378, 4), (key2390, 2), (key2406, 4), (key2437, 2), (key2472, 4), (key2480, 4), (key2503, 4), (key2587, 4), (key2593, 4), (key2598, 2), (key2600, 8), (key2766, 4), (key2772, 4), (key2843, 4), (key2880, 4), (key2887, 4), (key2889, 8), (key2910, 8), (key2929, 2), (key2931, 8), (key2966, 4), (key2968, 8), (key2989, 8), (key2995, 8), (key3002, 4)]

theorem rowCheck18848 : row18848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18848 := by decide +kernel

theorem rowEval18848 (x : Key → ℝ) : Integer.Sparse.eval row18848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block5.form2) x := by
  rw [rowCheck18848, Integer.Sparse.eval_collectBalanced, rawRowCheck18848]

def rawRow18849 : Integer.Sparse Key := [(key2360, 24), (key2455, 24), (key2455, 24), (key2516, 24), (key2516, 24)]

theorem rawRowCheck18849 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block5.form3 = rawRow18849 := by decide +kernel

def row18849 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

theorem rowCheck18849 : row18849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18849 := by decide +kernel

theorem rowEval18849 (x : Key → ℝ) : Integer.Sparse.eval row18849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck18849, Integer.Sparse.eval_collectBalanced, rawRowCheck18849]

def rawRow18850 : Integer.Sparse Key := [(key2360, 24), (key2455, 24), (key2516, 24), (key2455, 24), (key2516, 24)]

theorem rawRowCheck18850 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block5.form3 = rawRow18850 := by decide +kernel

def row18850 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

theorem rowCheck18850 : row18850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18850 := by decide +kernel

theorem rowEval18850 (x : Key → ℝ) : Integer.Sparse.eval row18850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck18850, Integer.Sparse.eval_collectBalanced, rawRowCheck18850]

def rawRow18851 : Integer.Sparse Key := [(key2360, 24), (key2455, 24), (key2516, 24), (key2516, 24), (key2455, 24)]

theorem rawRowCheck18851 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block5.form3 = rawRow18851 := by decide +kernel

def row18851 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

theorem rowCheck18851 : row18851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18851 := by decide +kernel

theorem rowEval18851 (x : Key → ℝ) : Integer.Sparse.eval row18851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18851, Integer.Sparse.eval_collectBalanced, rawRowCheck18851]

def rawRow18852 : Integer.Sparse Key := [(key2360, 24), (key2516, 24), (key2455, 24), (key2455, 24), (key2516, 24)]

theorem rawRowCheck18852 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block5.form3 = rawRow18852 := by decide +kernel

def row18852 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

theorem rowCheck18852 : row18852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18852 := by decide +kernel

theorem rowEval18852 (x : Key → ℝ) : Integer.Sparse.eval row18852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck18852, Integer.Sparse.eval_collectBalanced, rawRowCheck18852]

def rawRow18853 : Integer.Sparse Key := [(key2360, 24), (key2516, 24), (key2455, 24), (key2516, 24), (key2455, 24)]

theorem rawRowCheck18853 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block5.form3 = rawRow18853 := by decide +kernel

def row18853 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

theorem rowCheck18853 : row18853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18853 := by decide +kernel

theorem rowEval18853 (x : Key → ℝ) : Integer.Sparse.eval row18853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18853, Integer.Sparse.eval_collectBalanced, rawRowCheck18853]

def rawRow18854 : Integer.Sparse Key := [(key2360, 24), (key2516, 24), (key2516, 24), (key2455, 24), (key2455, 24)]

theorem rawRowCheck18854 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block5.form3 = rawRow18854 := by decide +kernel

def row18854 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

theorem rowCheck18854 : row18854 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18854 := by decide +kernel

theorem rowEval18854 (x : Key → ℝ) : Integer.Sparse.eval row18854 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18854, Integer.Sparse.eval_collectBalanced, rawRowCheck18854]

def rawRow18855 : Integer.Sparse Key := [(key2455, 24), (key2360, 24), (key2455, 24), (key2516, 24), (key2516, 24)]

theorem rawRowCheck18855 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block5.form3 = rawRow18855 := by decide +kernel

def row18855 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

theorem rowCheck18855 : row18855 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18855 := by decide +kernel

theorem rowEval18855 (x : Key → ℝ) : Integer.Sparse.eval row18855 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck18855, Integer.Sparse.eval_collectBalanced, rawRowCheck18855]

def rawRow18856 : Integer.Sparse Key := [(key2455, 24), (key2360, 24), (key2516, 24), (key2455, 24), (key2516, 24)]

theorem rawRowCheck18856 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block5.form3 = rawRow18856 := by decide +kernel

def row18856 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

theorem rowCheck18856 : row18856 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18856 := by decide +kernel

theorem rowEval18856 (x : Key → ℝ) : Integer.Sparse.eval row18856 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck18856, Integer.Sparse.eval_collectBalanced, rawRowCheck18856]

def rawRow18857 : Integer.Sparse Key := [(key2455, 24), (key2360, 24), (key2516, 24), (key2516, 24), (key2455, 24)]

theorem rawRowCheck18857 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block5.form3 = rawRow18857 := by decide +kernel

def row18857 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

theorem rowCheck18857 : row18857 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18857 := by decide +kernel

theorem rowEval18857 (x : Key → ℝ) : Integer.Sparse.eval row18857 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18857, Integer.Sparse.eval_collectBalanced, rawRowCheck18857]

def rawRow18858 : Integer.Sparse Key := [(key2455, 24), (key2455, 24), (key2360, 24), (key2516, 24), (key2516, 24)]

theorem rawRowCheck18858 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block5.form3 = rawRow18858 := by decide +kernel

def row18858 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

theorem rowCheck18858 : row18858 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18858 := by decide +kernel

theorem rowEval18858 (x : Key → ℝ) : Integer.Sparse.eval row18858 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck18858, Integer.Sparse.eval_collectBalanced, rawRowCheck18858]

def rawRow18859 : Integer.Sparse Key := [(key2455, 24), (key2455, 24), (key2516, 24), (key2360, 24), (key2516, 24)]

theorem rawRowCheck18859 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block5.form3 = rawRow18859 := by decide +kernel

def row18859 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

theorem rowCheck18859 : row18859 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18859 := by decide +kernel

theorem rowEval18859 (x : Key → ℝ) : Integer.Sparse.eval row18859 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck18859, Integer.Sparse.eval_collectBalanced, rawRowCheck18859]

def rawRow18860 : Integer.Sparse Key := [(key2455, 24), (key2455, 24), (key2516, 24), (key2516, 24), (key2360, 24)]

theorem rawRowCheck18860 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block5.form3 = rawRow18860 := by decide +kernel

def row18860 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

theorem rowCheck18860 : row18860 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18860 := by decide +kernel

theorem rowEval18860 (x : Key → ℝ) : Integer.Sparse.eval row18860 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck18860, Integer.Sparse.eval_collectBalanced, rawRowCheck18860]

def rawRow18861 : Integer.Sparse Key := [(key2455, 24), (key2516, 24), (key2360, 24), (key2455, 24), (key2516, 24)]

theorem rawRowCheck18861 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block5.form3 = rawRow18861 := by decide +kernel

def row18861 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

theorem rowCheck18861 : row18861 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18861 := by decide +kernel

theorem rowEval18861 (x : Key → ℝ) : Integer.Sparse.eval row18861 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck18861, Integer.Sparse.eval_collectBalanced, rawRowCheck18861]

def rawRow18862 : Integer.Sparse Key := [(key2455, 24), (key2516, 24), (key2360, 24), (key2516, 24), (key2455, 24)]

theorem rawRowCheck18862 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block5.form3 = rawRow18862 := by decide +kernel

def row18862 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

theorem rowCheck18862 : row18862 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18862 := by decide +kernel

theorem rowEval18862 (x : Key → ℝ) : Integer.Sparse.eval row18862 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18862, Integer.Sparse.eval_collectBalanced, rawRowCheck18862]

def rawRow18863 : Integer.Sparse Key := [(key2455, 24), (key2516, 24), (key2455, 24), (key2360, 24), (key2516, 24)]

theorem rawRowCheck18863 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block5.form3 = rawRow18863 := by decide +kernel

def row18863 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

theorem rowCheck18863 : row18863 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18863 := by decide +kernel

theorem rowEval18863 (x : Key → ℝ) : Integer.Sparse.eval row18863 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck18863, Integer.Sparse.eval_collectBalanced, rawRowCheck18863]

def rawRow18864 : Integer.Sparse Key := [(key2455, 24), (key2516, 24), (key2455, 24), (key2516, 24), (key2360, 24)]

theorem rawRowCheck18864 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block5.form3 = rawRow18864 := by decide +kernel

def row18864 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

theorem rowCheck18864 : row18864 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18864 := by decide +kernel

theorem rowEval18864 (x : Key → ℝ) : Integer.Sparse.eval row18864 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck18864, Integer.Sparse.eval_collectBalanced, rawRowCheck18864]

def rawRow18865 : Integer.Sparse Key := [(key2455, 24), (key2516, 24), (key2516, 24), (key2360, 24), (key2455, 24)]

theorem rawRowCheck18865 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block5.form3 = rawRow18865 := by decide +kernel

def row18865 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

theorem rowCheck18865 : row18865 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18865 := by decide +kernel

theorem rowEval18865 (x : Key → ℝ) : Integer.Sparse.eval row18865 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18865, Integer.Sparse.eval_collectBalanced, rawRowCheck18865]

def rawRow18866 : Integer.Sparse Key := [(key2455, 24), (key2516, 24), (key2516, 24), (key2455, 24), (key2360, 24)]

theorem rawRowCheck18866 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block5.form3 = rawRow18866 := by decide +kernel

def row18866 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

theorem rowCheck18866 : row18866 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18866 := by decide +kernel

theorem rowEval18866 (x : Key → ℝ) : Integer.Sparse.eval row18866 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck18866, Integer.Sparse.eval_collectBalanced, rawRowCheck18866]

def rawRow18867 : Integer.Sparse Key := [(key2516, 24), (key2360, 24), (key2455, 24), (key2455, 24), (key2516, 24)]

theorem rawRowCheck18867 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block5.form3 = rawRow18867 := by decide +kernel

def row18867 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

theorem rowCheck18867 : row18867 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18867 := by decide +kernel

theorem rowEval18867 (x : Key → ℝ) : Integer.Sparse.eval row18867 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck18867, Integer.Sparse.eval_collectBalanced, rawRowCheck18867]

def rawRow18868 : Integer.Sparse Key := [(key2516, 24), (key2360, 24), (key2455, 24), (key2516, 24), (key2455, 24)]

theorem rawRowCheck18868 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block5.form3 = rawRow18868 := by decide +kernel

def row18868 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

theorem rowCheck18868 : row18868 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18868 := by decide +kernel

theorem rowEval18868 (x : Key → ℝ) : Integer.Sparse.eval row18868 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18868, Integer.Sparse.eval_collectBalanced, rawRowCheck18868]

def rawRow18869 : Integer.Sparse Key := [(key2516, 24), (key2360, 24), (key2516, 24), (key2455, 24), (key2455, 24)]

theorem rawRowCheck18869 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block5.form3 = rawRow18869 := by decide +kernel

def row18869 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

theorem rowCheck18869 : row18869 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18869 := by decide +kernel

theorem rowEval18869 (x : Key → ℝ) : Integer.Sparse.eval row18869 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18869, Integer.Sparse.eval_collectBalanced, rawRowCheck18869]

def rawRow18870 : Integer.Sparse Key := [(key2516, 24), (key2455, 24), (key2360, 24), (key2455, 24), (key2516, 24)]

theorem rawRowCheck18870 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block5.form3 = rawRow18870 := by decide +kernel

def row18870 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

theorem rowCheck18870 : row18870 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18870 := by decide +kernel

theorem rowEval18870 (x : Key → ℝ) : Integer.Sparse.eval row18870 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck18870, Integer.Sparse.eval_collectBalanced, rawRowCheck18870]

def rawRow18871 : Integer.Sparse Key := [(key2516, 24), (key2455, 24), (key2360, 24), (key2516, 24), (key2455, 24)]

theorem rawRowCheck18871 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block5.form3 = rawRow18871 := by decide +kernel

def row18871 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

theorem rowCheck18871 : row18871 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18871 := by decide +kernel

theorem rowEval18871 (x : Key → ℝ) : Integer.Sparse.eval row18871 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18871, Integer.Sparse.eval_collectBalanced, rawRowCheck18871]

def rawRow18872 : Integer.Sparse Key := [(key2516, 24), (key2455, 24), (key2455, 24), (key2360, 24), (key2516, 24)]

theorem rawRowCheck18872 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block5.form3 = rawRow18872 := by decide +kernel

def row18872 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

theorem rowCheck18872 : row18872 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18872 := by decide +kernel

theorem rowEval18872 (x : Key → ℝ) : Integer.Sparse.eval row18872 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck18872, Integer.Sparse.eval_collectBalanced, rawRowCheck18872]

def rawRow18873 : Integer.Sparse Key := [(key2516, 24), (key2455, 24), (key2455, 24), (key2516, 24), (key2360, 24)]

theorem rawRowCheck18873 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block5.form3 = rawRow18873 := by decide +kernel

def row18873 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

theorem rowCheck18873 : row18873 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18873 := by decide +kernel

theorem rowEval18873 (x : Key → ℝ) : Integer.Sparse.eval row18873 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck18873, Integer.Sparse.eval_collectBalanced, rawRowCheck18873]

def rawRow18874 : Integer.Sparse Key := [(key2516, 24), (key2455, 24), (key2516, 24), (key2360, 24), (key2455, 24)]

theorem rawRowCheck18874 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block5.form3 = rawRow18874 := by decide +kernel

def row18874 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

theorem rowCheck18874 : row18874 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18874 := by decide +kernel

theorem rowEval18874 (x : Key → ℝ) : Integer.Sparse.eval row18874 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18874, Integer.Sparse.eval_collectBalanced, rawRowCheck18874]

def rawRow18875 : Integer.Sparse Key := [(key2516, 24), (key2455, 24), (key2516, 24), (key2455, 24), (key2360, 24)]

theorem rawRowCheck18875 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block5.form3 = rawRow18875 := by decide +kernel

def row18875 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

theorem rowCheck18875 : row18875 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18875 := by decide +kernel

theorem rowEval18875 (x : Key → ℝ) : Integer.Sparse.eval row18875 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck18875, Integer.Sparse.eval_collectBalanced, rawRowCheck18875]

def rawRow18876 : Integer.Sparse Key := [(key2516, 24), (key2516, 24), (key2360, 24), (key2455, 24), (key2455, 24)]

theorem rawRowCheck18876 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block5.form3 = rawRow18876 := by decide +kernel

def row18876 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

theorem rowCheck18876 : row18876 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18876 := by decide +kernel

theorem rowEval18876 (x : Key → ℝ) : Integer.Sparse.eval row18876 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18876, Integer.Sparse.eval_collectBalanced, rawRowCheck18876]

def rawRow18877 : Integer.Sparse Key := [(key2516, 24), (key2516, 24), (key2455, 24), (key2360, 24), (key2455, 24)]

theorem rawRowCheck18877 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block5.form3 = rawRow18877 := by decide +kernel

def row18877 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

theorem rowCheck18877 : row18877 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18877 := by decide +kernel

theorem rowEval18877 (x : Key → ℝ) : Integer.Sparse.eval row18877 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18877, Integer.Sparse.eval_collectBalanced, rawRowCheck18877]

def rawRow18878 : Integer.Sparse Key := [(key2516, 24), (key2516, 24), (key2455, 24), (key2455, 24), (key2360, 24)]

theorem rawRowCheck18878 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block5.form3 = rawRow18878 := by decide +kernel

def row18878 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

theorem rowCheck18878 : row18878 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18878 := by decide +kernel

theorem rowEval18878 (x : Key → ℝ) : Integer.Sparse.eval row18878 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck18878, Integer.Sparse.eval_collectBalanced, rawRowCheck18878]

def rawRow18879 : Integer.Sparse Key := [(key976, 6), (key976, 6), (key984, 6), (key984, 6), (key1090, 6), (key1090, 6), (key1098, 6), (key1090, 6), (key1090, 6), (key1180, 6), (key1180, 6), (key1183, 6), (key1183, 6), (key1098, 6), (key1183, 6), (key1183, 6), (key1169, 6), (key1169, 6), (key1220, 6), (key1220, 6)]

theorem rawRowCheck18879 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block5.form4 = rawRow18879 := by decide +kernel

def row18879 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

theorem rowCheck18879 : row18879 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18879 := by decide +kernel

theorem rowEval18879 (x : Key → ℝ) : Integer.Sparse.eval row18879 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck18879, Integer.Sparse.eval_collectBalanced, rawRowCheck18879]

def rawRow18880 : Integer.Sparse Key := [(key976, 6), (key984, 6), (key976, 6), (key984, 6), (key1090, 6), (key1098, 6), (key1090, 6), (key1180, 6), (key1183, 6), (key1090, 6), (key1183, 6), (key1090, 6), (key1180, 6), (key1183, 6), (key1098, 6), (key1183, 6), (key1169, 6), (key1220, 6), (key1169, 6), (key1220, 6)]

theorem rawRowCheck18880 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block5.form4 = rawRow18880 := by decide +kernel

def row18880 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

theorem rowCheck18880 : row18880 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18880 := by decide +kernel

theorem rowEval18880 (x : Key → ℝ) : Integer.Sparse.eval row18880 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck18880, Integer.Sparse.eval_collectBalanced, rawRowCheck18880]

def rawRow18881 : Integer.Sparse Key := [(key984, 6), (key976, 6), (key976, 6), (key984, 6), (key1098, 6), (key1090, 6), (key1090, 6), (key1183, 6), (key1180, 6), (key1183, 6), (key1090, 6), (key1180, 6), (key1090, 6), (key1183, 6), (key1183, 6), (key1098, 6), (key1169, 6), (key1220, 6), (key1220, 6), (key1169, 6)]

theorem rawRowCheck18881 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block5.form4 = rawRow18881 := by decide +kernel

def row18881 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

theorem rowCheck18881 : row18881 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18881 := by decide +kernel

theorem rowEval18881 (x : Key → ℝ) : Integer.Sparse.eval row18881 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18881, Integer.Sparse.eval_collectBalanced, rawRowCheck18881]

def rawRow18882 : Integer.Sparse Key := [(key976, 6), (key984, 6), (key984, 6), (key976, 6), (key1180, 6), (key1183, 6), (key1183, 6), (key1090, 6), (key1098, 6), (key1090, 6), (key1183, 6), (key1098, 6), (key1183, 6), (key1090, 6), (key1090, 6), (key1180, 6), (key1220, 6), (key1169, 6), (key1169, 6), (key1220, 6)]

theorem rawRowCheck18882 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block5.form4 = rawRow18882 := by decide +kernel

def row18882 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

theorem rowCheck18882 : row18882 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18882 := by decide +kernel

theorem rowEval18882 (x : Key → ℝ) : Integer.Sparse.eval row18882 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck18882, Integer.Sparse.eval_collectBalanced, rawRowCheck18882]

def rawRow18883 : Integer.Sparse Key := [(key984, 6), (key976, 6), (key984, 6), (key976, 6), (key1183, 6), (key1180, 6), (key1183, 6), (key1098, 6), (key1090, 6), (key1183, 6), (key1090, 6), (key1183, 6), (key1098, 6), (key1090, 6), (key1180, 6), (key1090, 6), (key1220, 6), (key1169, 6), (key1220, 6), (key1169, 6)]

theorem rawRowCheck18883 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block5.form4 = rawRow18883 := by decide +kernel

def row18883 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

theorem rowCheck18883 : row18883 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18883 := by decide +kernel

theorem rowEval18883 (x : Key → ℝ) : Integer.Sparse.eval row18883 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18883, Integer.Sparse.eval_collectBalanced, rawRowCheck18883]

def rawRow18884 : Integer.Sparse Key := [(key984, 6), (key984, 6), (key976, 6), (key976, 6), (key1183, 6), (key1183, 6), (key1180, 6), (key1183, 6), (key1183, 6), (key1098, 6), (key1098, 6), (key1090, 6), (key1090, 6), (key1180, 6), (key1090, 6), (key1090, 6), (key1220, 6), (key1220, 6), (key1169, 6), (key1169, 6)]

theorem rawRowCheck18884 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block5.form4 = rawRow18884 := by decide +kernel

def row18884 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

theorem rowCheck18884 : row18884 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18884 := by decide +kernel

theorem rowEval18884 (x : Key → ℝ) : Integer.Sparse.eval row18884 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18884, Integer.Sparse.eval_collectBalanced, rawRowCheck18884]

def rawRow18885 : Integer.Sparse Key := [(key1090, 6), (key1090, 6), (key1098, 6), (key1169, 6), (key976, 6), (key976, 6), (key984, 6), (key1090, 6), (key1090, 6), (key1180, 6), (key1180, 6), (key1183, 6), (key1183, 6), (key1169, 6), (key1220, 6), (key1220, 6), (key984, 6), (key1098, 6), (key1183, 6), (key1183, 6)]

theorem rawRowCheck18885 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block5.form4 = rawRow18885 := by decide +kernel

def row18885 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

theorem rowCheck18885 : row18885 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18885 := by decide +kernel

theorem rowEval18885 (x : Key → ℝ) : Integer.Sparse.eval row18885 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck18885, Integer.Sparse.eval_collectBalanced, rawRowCheck18885]

def rawRow18886 : Integer.Sparse Key := [(key1090, 6), (key1098, 6), (key1090, 6), (key1169, 6), (key976, 6), (key984, 6), (key976, 6), (key1180, 6), (key1183, 6), (key1090, 6), (key1183, 6), (key1090, 6), (key1180, 6), (key1220, 6), (key1169, 6), (key1220, 6), (key984, 6), (key1183, 6), (key1098, 6), (key1183, 6)]

theorem rawRowCheck18886 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block5.form4 = rawRow18886 := by decide +kernel

def row18886 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

theorem rowCheck18886 : row18886 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18886 := by decide +kernel

theorem rowEval18886 (x : Key → ℝ) : Integer.Sparse.eval row18886 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck18886, Integer.Sparse.eval_collectBalanced, rawRowCheck18886]

def rawRow18887 : Integer.Sparse Key := [(key1098, 6), (key1090, 6), (key1090, 6), (key1169, 6), (key984, 6), (key976, 6), (key976, 6), (key1183, 6), (key1180, 6), (key1183, 6), (key1090, 6), (key1180, 6), (key1090, 6), (key1220, 6), (key1220, 6), (key1169, 6), (key984, 6), (key1183, 6), (key1183, 6), (key1098, 6)]

theorem rawRowCheck18887 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block5.form4 = rawRow18887 := by decide +kernel

def row18887 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

theorem rowCheck18887 : row18887 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18887 := by decide +kernel

theorem rowEval18887 (x : Key → ℝ) : Integer.Sparse.eval row18887 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18887, Integer.Sparse.eval_collectBalanced, rawRowCheck18887]

def rawRow18888 : Integer.Sparse Key := [(key1090, 6), (key1090, 6), (key1169, 6), (key1098, 6), (key1090, 6), (key1090, 6), (key1169, 6), (key976, 6), (key976, 6), (key1180, 6), (key1180, 6), (key1220, 6), (key1220, 6), (key984, 6), (key1183, 6), (key1183, 6), (key1098, 6), (key984, 6), (key1183, 6), (key1183, 6)]

theorem rawRowCheck18888 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block5.form4 = rawRow18888 := by decide +kernel

def row18888 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

theorem rowCheck18888 : row18888 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18888 := by decide +kernel

theorem rowEval18888 (x : Key → ℝ) : Integer.Sparse.eval row18888 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck18888, Integer.Sparse.eval_collectBalanced, rawRowCheck18888]

def rawRow18889 : Integer.Sparse Key := [(key1090, 6), (key1169, 6), (key1090, 6), (key1098, 6), (key1090, 6), (key1169, 6), (key1090, 6), (key1180, 6), (key1220, 6), (key976, 6), (key1220, 6), (key976, 6), (key1180, 6), (key1183, 6), (key984, 6), (key1183, 6), (key1098, 6), (key1183, 6), (key984, 6), (key1183, 6)]

theorem rawRowCheck18889 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block5.form4 = rawRow18889 := by decide +kernel

def row18889 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

theorem rowCheck18889 : row18889 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18889 := by decide +kernel

theorem rowEval18889 (x : Key → ℝ) : Integer.Sparse.eval row18889 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck18889, Integer.Sparse.eval_collectBalanced, rawRowCheck18889]

def rawRow18890 : Integer.Sparse Key := [(key1169, 6), (key1090, 6), (key1090, 6), (key1098, 6), (key1169, 6), (key1090, 6), (key1090, 6), (key1220, 6), (key1180, 6), (key1220, 6), (key976, 6), (key1180, 6), (key976, 6), (key1183, 6), (key1183, 6), (key984, 6), (key1098, 6), (key1183, 6), (key1183, 6), (key984, 6)]

theorem rawRowCheck18890 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block5.form4 = rawRow18890 := by decide +kernel

def row18890 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

theorem rowCheck18890 : row18890 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18890 := by decide +kernel

theorem rowEval18890 (x : Key → ℝ) : Integer.Sparse.eval row18890 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block5.form4) x := by
  rw [rowCheck18890, Integer.Sparse.eval_collectBalanced, rawRowCheck18890]

def rawRow18891 : Integer.Sparse Key := [(key1090, 6), (key1098, 6), (key1169, 6), (key1090, 6), (key1180, 6), (key1183, 6), (key1220, 6), (key976, 6), (key984, 6), (key1090, 6), (key1183, 6), (key1169, 6), (key1220, 6), (key976, 6), (key1090, 6), (key1180, 6), (key1183, 6), (key984, 6), (key1098, 6), (key1183, 6)]

theorem rawRowCheck18891 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block5.form4 = rawRow18891 := by decide +kernel

def row18891 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

theorem rowCheck18891 : row18891 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18891 := by decide +kernel

theorem rowEval18891 (x : Key → ℝ) : Integer.Sparse.eval row18891 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck18891, Integer.Sparse.eval_collectBalanced, rawRowCheck18891]

def rawRow18892 : Integer.Sparse Key := [(key1098, 6), (key1090, 6), (key1169, 6), (key1090, 6), (key1183, 6), (key1180, 6), (key1220, 6), (key984, 6), (key976, 6), (key1183, 6), (key1090, 6), (key1220, 6), (key1169, 6), (key976, 6), (key1180, 6), (key1090, 6), (key1183, 6), (key984, 6), (key1183, 6), (key1098, 6)]

theorem rawRowCheck18892 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block5.form4 = rawRow18892 := by decide +kernel

def row18892 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

theorem rowCheck18892 : row18892 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18892 := by decide +kernel

theorem rowEval18892 (x : Key → ℝ) : Integer.Sparse.eval row18892 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18892, Integer.Sparse.eval_collectBalanced, rawRowCheck18892]

def rawRow18893 : Integer.Sparse Key := [(key1090, 6), (key1169, 6), (key1098, 6), (key1090, 6), (key1180, 6), (key1220, 6), (key1183, 6), (key1090, 6), (key1169, 6), (key976, 6), (key1220, 6), (key984, 6), (key1183, 6), (key1090, 6), (key976, 6), (key1180, 6), (key1183, 6), (key1098, 6), (key984, 6), (key1183, 6)]

theorem rawRowCheck18893 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block5.form4 = rawRow18893 := by decide +kernel

def row18893 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

theorem rowCheck18893 : row18893 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18893 := by decide +kernel

theorem rowEval18893 (x : Key → ℝ) : Integer.Sparse.eval row18893 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck18893, Integer.Sparse.eval_collectBalanced, rawRowCheck18893]

def rawRow18894 : Integer.Sparse Key := [(key1169, 6), (key1090, 6), (key1098, 6), (key1090, 6), (key1220, 6), (key1180, 6), (key1183, 6), (key1169, 6), (key1090, 6), (key1220, 6), (key976, 6), (key1183, 6), (key984, 6), (key1090, 6), (key1180, 6), (key976, 6), (key1183, 6), (key1098, 6), (key1183, 6), (key984, 6)]

theorem rawRowCheck18894 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block5.form4 = rawRow18894 := by decide +kernel

def row18894 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

theorem rowCheck18894 : row18894 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18894 := by decide +kernel

theorem rowEval18894 (x : Key → ℝ) : Integer.Sparse.eval row18894 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block5.form4) x := by
  rw [rowCheck18894, Integer.Sparse.eval_collectBalanced, rawRowCheck18894]

def rawRow18895 : Integer.Sparse Key := [(key1098, 6), (key1169, 6), (key1090, 6), (key1090, 6), (key1183, 6), (key1220, 6), (key1180, 6), (key1183, 6), (key1220, 6), (key984, 6), (key1169, 6), (key976, 6), (key1090, 6), (key1180, 6), (key976, 6), (key1090, 6), (key1183, 6), (key1183, 6), (key984, 6), (key1098, 6)]

theorem rawRowCheck18895 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block5.form4 = rawRow18895 := by decide +kernel

def row18895 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

theorem rowCheck18895 : row18895 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18895 := by decide +kernel

theorem rowEval18895 (x : Key → ℝ) : Integer.Sparse.eval row18895 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18895, Integer.Sparse.eval_collectBalanced, rawRowCheck18895]

def rawRow18896 : Integer.Sparse Key := [(key1169, 6), (key1098, 6), (key1090, 6), (key1090, 6), (key1220, 6), (key1183, 6), (key1180, 6), (key1220, 6), (key1183, 6), (key1169, 6), (key984, 6), (key1090, 6), (key976, 6), (key1180, 6), (key1090, 6), (key976, 6), (key1183, 6), (key1183, 6), (key1098, 6), (key984, 6)]

theorem rawRowCheck18896 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block5.form4 = rawRow18896 := by decide +kernel

def row18896 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

theorem rowCheck18896 : row18896 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18896 := by decide +kernel

theorem rowEval18896 (x : Key → ℝ) : Integer.Sparse.eval row18896 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block5.form4) x := by
  rw [rowCheck18896, Integer.Sparse.eval_collectBalanced, rawRowCheck18896]

def rawRow18897 : Integer.Sparse Key := [(key1180, 6), (key1183, 6), (key1183, 6), (key1220, 6), (key976, 6), (key984, 6), (key984, 6), (key1090, 6), (key1098, 6), (key1090, 6), (key1183, 6), (key1098, 6), (key1183, 6), (key1169, 6), (key1169, 6), (key1220, 6), (key976, 6), (key1090, 6), (key1090, 6), (key1180, 6)]

theorem rawRowCheck18897 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block5.form4 = rawRow18897 := by decide +kernel

def row18897 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

theorem rowCheck18897 : row18897 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18897 := by decide +kernel

theorem rowEval18897 (x : Key → ℝ) : Integer.Sparse.eval row18897 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck18897, Integer.Sparse.eval_collectBalanced, rawRowCheck18897]

def rawRow18898 : Integer.Sparse Key := [(key1183, 6), (key1180, 6), (key1183, 6), (key1220, 6), (key984, 6), (key976, 6), (key984, 6), (key1098, 6), (key1090, 6), (key1183, 6), (key1090, 6), (key1183, 6), (key1098, 6), (key1169, 6), (key1220, 6), (key1169, 6), (key976, 6), (key1090, 6), (key1180, 6), (key1090, 6)]

theorem rawRowCheck18898 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block5.form4 = rawRow18898 := by decide +kernel

def row18898 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

theorem rowCheck18898 : row18898 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18898 := by decide +kernel

theorem rowEval18898 (x : Key → ℝ) : Integer.Sparse.eval row18898 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18898, Integer.Sparse.eval_collectBalanced, rawRowCheck18898]

def rawRow18899 : Integer.Sparse Key := [(key1183, 6), (key1183, 6), (key1180, 6), (key1220, 6), (key984, 6), (key984, 6), (key976, 6), (key1183, 6), (key1183, 6), (key1098, 6), (key1098, 6), (key1090, 6), (key1090, 6), (key1220, 6), (key1169, 6), (key1169, 6), (key976, 6), (key1180, 6), (key1090, 6), (key1090, 6)]

theorem rawRowCheck18899 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block5.form4 = rawRow18899 := by decide +kernel

def row18899 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

theorem rowCheck18899 : row18899 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18899 := by decide +kernel

theorem rowEval18899 (x : Key → ℝ) : Integer.Sparse.eval row18899 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18899, Integer.Sparse.eval_collectBalanced, rawRowCheck18899]

def rawRow18900 : Integer.Sparse Key := [(key1180, 6), (key1183, 6), (key1220, 6), (key1183, 6), (key1090, 6), (key1098, 6), (key1169, 6), (key976, 6), (key984, 6), (key1090, 6), (key1183, 6), (key1169, 6), (key1220, 6), (key984, 6), (key1098, 6), (key1183, 6), (key1090, 6), (key976, 6), (key1090, 6), (key1180, 6)]

theorem rawRowCheck18900 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block5.form4 = rawRow18900 := by decide +kernel

def row18900 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

theorem rowCheck18900 : row18900 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18900 := by decide +kernel

theorem rowEval18900 (x : Key → ℝ) : Integer.Sparse.eval row18900 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck18900, Integer.Sparse.eval_collectBalanced, rawRowCheck18900]

def rawRow18901 : Integer.Sparse Key := [(key1183, 6), (key1180, 6), (key1220, 6), (key1183, 6), (key1098, 6), (key1090, 6), (key1169, 6), (key984, 6), (key976, 6), (key1183, 6), (key1090, 6), (key1220, 6), (key1169, 6), (key984, 6), (key1183, 6), (key1098, 6), (key1090, 6), (key976, 6), (key1180, 6), (key1090, 6)]

theorem rawRowCheck18901 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block5.form4 = rawRow18901 := by decide +kernel

def row18901 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

theorem rowCheck18901 : row18901 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18901 := by decide +kernel

theorem rowEval18901 (x : Key → ℝ) : Integer.Sparse.eval row18901 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18901, Integer.Sparse.eval_collectBalanced, rawRowCheck18901]

def rawRow18902 : Integer.Sparse Key := [(key1180, 6), (key1220, 6), (key1183, 6), (key1183, 6), (key1090, 6), (key1169, 6), (key1098, 6), (key1090, 6), (key1169, 6), (key976, 6), (key1220, 6), (key984, 6), (key1183, 6), (key1098, 6), (key984, 6), (key1183, 6), (key1090, 6), (key1090, 6), (key976, 6), (key1180, 6)]

theorem rawRowCheck18902 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block5.form4 = rawRow18902 := by decide +kernel

def row18902 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

theorem rowCheck18902 : row18902 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18902 := by decide +kernel

theorem rowEval18902 (x : Key → ℝ) : Integer.Sparse.eval row18902 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck18902, Integer.Sparse.eval_collectBalanced, rawRowCheck18902]

def rawRow18903 : Integer.Sparse Key := [(key1220, 6), (key1180, 6), (key1183, 6), (key1183, 6), (key1169, 6), (key1090, 6), (key1098, 6), (key1169, 6), (key1090, 6), (key1220, 6), (key976, 6), (key1183, 6), (key984, 6), (key1098, 6), (key1183, 6), (key984, 6), (key1090, 6), (key1090, 6), (key1180, 6), (key976, 6)]

theorem rawRowCheck18903 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block5.form4 = rawRow18903 := by decide +kernel

def row18903 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

theorem rowCheck18903 : row18903 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18903 := by decide +kernel

theorem rowEval18903 (x : Key → ℝ) : Integer.Sparse.eval row18903 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block5.form4) x := by
  rw [rowCheck18903, Integer.Sparse.eval_collectBalanced, rawRowCheck18903]

def rawRow18904 : Integer.Sparse Key := [(key1183, 6), (key1220, 6), (key1180, 6), (key1183, 6), (key1098, 6), (key1169, 6), (key1090, 6), (key1183, 6), (key1220, 6), (key984, 6), (key1169, 6), (key976, 6), (key1090, 6), (key1183, 6), (key984, 6), (key1098, 6), (key1090, 6), (key1180, 6), (key976, 6), (key1090, 6)]

theorem rawRowCheck18904 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block5.form4 = rawRow18904 := by decide +kernel

def row18904 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

theorem rowCheck18904 : row18904 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18904 := by decide +kernel

theorem rowEval18904 (x : Key → ℝ) : Integer.Sparse.eval row18904 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18904, Integer.Sparse.eval_collectBalanced, rawRowCheck18904]

def rawRow18905 : Integer.Sparse Key := [(key1220, 6), (key1183, 6), (key1180, 6), (key1183, 6), (key1169, 6), (key1098, 6), (key1090, 6), (key1220, 6), (key1183, 6), (key1169, 6), (key984, 6), (key1090, 6), (key976, 6), (key1183, 6), (key1098, 6), (key984, 6), (key1090, 6), (key1180, 6), (key1090, 6), (key976, 6)]

theorem rawRowCheck18905 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block5.form4 = rawRow18905 := by decide +kernel

def row18905 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

theorem rowCheck18905 : row18905 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18905 := by decide +kernel

theorem rowEval18905 (x : Key → ℝ) : Integer.Sparse.eval row18905 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block5.form4) x := by
  rw [rowCheck18905, Integer.Sparse.eval_collectBalanced, rawRowCheck18905]

def rawRow18906 : Integer.Sparse Key := [(key1183, 6), (key1183, 6), (key1220, 6), (key1180, 6), (key1183, 6), (key1183, 6), (key1220, 6), (key984, 6), (key984, 6), (key1098, 6), (key1098, 6), (key1169, 6), (key1169, 6), (key976, 6), (key1090, 6), (key1090, 6), (key1180, 6), (key976, 6), (key1090, 6), (key1090, 6)]

theorem rawRowCheck18906 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block5.form4 = rawRow18906 := by decide +kernel

def row18906 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

theorem rowCheck18906 : row18906 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18906 := by decide +kernel

theorem rowEval18906 (x : Key → ℝ) : Integer.Sparse.eval row18906 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18906, Integer.Sparse.eval_collectBalanced, rawRowCheck18906]

def rawRow18907 : Integer.Sparse Key := [(key1183, 6), (key1220, 6), (key1183, 6), (key1180, 6), (key1183, 6), (key1220, 6), (key1183, 6), (key1098, 6), (key1169, 6), (key984, 6), (key1169, 6), (key984, 6), (key1098, 6), (key1090, 6), (key976, 6), (key1090, 6), (key1180, 6), (key1090, 6), (key976, 6), (key1090, 6)]

theorem rawRowCheck18907 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block5.form4 = rawRow18907 := by decide +kernel

def row18907 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

theorem rowCheck18907 : row18907 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18907 := by decide +kernel

theorem rowEval18907 (x : Key → ℝ) : Integer.Sparse.eval row18907 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18907, Integer.Sparse.eval_collectBalanced, rawRowCheck18907]

def rawRow18908 : Integer.Sparse Key := [(key1220, 6), (key1183, 6), (key1183, 6), (key1180, 6), (key1220, 6), (key1183, 6), (key1183, 6), (key1169, 6), (key1098, 6), (key1169, 6), (key984, 6), (key1098, 6), (key984, 6), (key1090, 6), (key1090, 6), (key976, 6), (key1180, 6), (key1090, 6), (key1090, 6), (key976, 6)]

theorem rawRowCheck18908 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block5.form4 = rawRow18908 := by decide +kernel

def row18908 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

theorem rowCheck18908 : row18908 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18908 := by decide +kernel

theorem rowEval18908 (x : Key → ℝ) : Integer.Sparse.eval row18908 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block5.form4) x := by
  rw [rowCheck18908, Integer.Sparse.eval_collectBalanced, rawRowCheck18908]

def rawRow18909 : Integer.Sparse Key := [(key2362, 4), (key2365, 4), (key2365, 4), (key2365, 4), (key2365, 4), (key2367, 4), (key2457, 4), (key2460, 4), (key2460, 4), (key2457, 4), (key2521, 4), (key2521, 4), (key2460, 4), (key2460, 4), (key2521, 4), (key2521, 4), (key2525, 4), (key2525, 4), (key2532, 4), (key2532, 4), (key2533, 4), (key2532, 4), (key2532, 4), (key2562, 4), (key2562, 4), (key2564, 4), (key2564, 4), (key2533, 4), (key2564, 4), (key2564, 4)]

theorem rawRowCheck18909 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block5.form5 = rawRow18909 := by decide +kernel

def row18909 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 16), (key2525, 8), (key2532, 16), (key2533, 8), (key2562, 8), (key2564, 16)]

theorem rowCheck18909 : row18909 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18909 := by decide +kernel

theorem rowEval18909 (x : Key → ℝ) : Integer.Sparse.eval row18909 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block5.form5) x := by
  rw [rowCheck18909, Integer.Sparse.eval_collectBalanced, rawRowCheck18909]

def rawRow18910 : Integer.Sparse Key := [(key2365, 4), (key2362, 4), (key2365, 4), (key2365, 4), (key2367, 4), (key2365, 4), (key2460, 4), (key2457, 4), (key2460, 4), (key2521, 4), (key2457, 4), (key2521, 4), (key2521, 4), (key2525, 4), (key2460, 4), (key2525, 4), (key2460, 4), (key2521, 4), (key2532, 4), (key2533, 4), (key2532, 4), (key2562, 4), (key2564, 4), (key2532, 4), (key2564, 4), (key2532, 4), (key2562, 4), (key2564, 4), (key2533, 4), (key2564, 4)]

theorem rawRowCheck18910 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block5.form5 = rawRow18910 := by decide +kernel

def row18910 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 16), (key2525, 8), (key2532, 16), (key2533, 8), (key2562, 8), (key2564, 16)]

theorem rowCheck18910 : row18910 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18910 := by decide +kernel

theorem rowEval18910 (x : Key → ℝ) : Integer.Sparse.eval row18910 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block5.form5) x := by
  rw [rowCheck18910, Integer.Sparse.eval_collectBalanced, rawRowCheck18910]

def rawRow18911 : Integer.Sparse Key := [(key2365, 4), (key2365, 4), (key2362, 4), (key2367, 4), (key2365, 4), (key2365, 4), (key2460, 4), (key2460, 4), (key2457, 4), (key2521, 4), (key2521, 4), (key2457, 4), (key2525, 4), (key2521, 4), (key2525, 4), (key2460, 4), (key2521, 4), (key2460, 4), (key2533, 4), (key2532, 4), (key2532, 4), (key2564, 4), (key2562, 4), (key2564, 4), (key2532, 4), (key2562, 4), (key2532, 4), (key2564, 4), (key2564, 4), (key2533, 4)]

theorem rawRowCheck18911 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block5.form5 = rawRow18911 := by decide +kernel

def row18911 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 16), (key2525, 8), (key2532, 16), (key2533, 8), (key2562, 8), (key2564, 16)]

theorem rowCheck18911 : row18911 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18911 := by decide +kernel

theorem rowEval18911 (x : Key → ℝ) : Integer.Sparse.eval row18911 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck18911, Integer.Sparse.eval_collectBalanced, rawRowCheck18911]

def rawRow18912 : Integer.Sparse Key := [(key2365, 4), (key2365, 4), (key2367, 4), (key2362, 4), (key2365, 4), (key2365, 4), (key2521, 4), (key2521, 4), (key2525, 4), (key2460, 4), (key2460, 4), (key2525, 4), (key2457, 4), (key2460, 4), (key2457, 4), (key2521, 4), (key2460, 4), (key2521, 4), (key2562, 4), (key2564, 4), (key2564, 4), (key2532, 4), (key2533, 4), (key2532, 4), (key2564, 4), (key2533, 4), (key2564, 4), (key2532, 4), (key2532, 4), (key2562, 4)]

theorem rawRowCheck18912 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block5.form5 = rawRow18912 := by decide +kernel

def row18912 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 16), (key2525, 8), (key2532, 16), (key2533, 8), (key2562, 8), (key2564, 16)]

theorem rowCheck18912 : row18912 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18912 := by decide +kernel

theorem rowEval18912 (x : Key → ℝ) : Integer.Sparse.eval row18912 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block5.form5) x := by
  rw [rowCheck18912, Integer.Sparse.eval_collectBalanced, rawRowCheck18912]

def rawRow18913 : Integer.Sparse Key := [(key2365, 4), (key2367, 4), (key2365, 4), (key2365, 4), (key2362, 4), (key2365, 4), (key2521, 4), (key2525, 4), (key2521, 4), (key2460, 4), (key2525, 4), (key2460, 4), (key2460, 4), (key2457, 4), (key2521, 4), (key2457, 4), (key2521, 4), (key2460, 4), (key2564, 4), (key2562, 4), (key2564, 4), (key2533, 4), (key2532, 4), (key2564, 4), (key2532, 4), (key2564, 4), (key2533, 4), (key2532, 4), (key2562, 4), (key2532, 4)]

theorem rawRowCheck18913 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block5.form5 = rawRow18913 := by decide +kernel

def row18913 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 16), (key2525, 8), (key2532, 16), (key2533, 8), (key2562, 8), (key2564, 16)]

theorem rowCheck18913 : row18913 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18913 := by decide +kernel

theorem rowEval18913 (x : Key → ℝ) : Integer.Sparse.eval row18913 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck18913, Integer.Sparse.eval_collectBalanced, rawRowCheck18913]

def rawRow18914 : Integer.Sparse Key := [(key2367, 4), (key2365, 4), (key2365, 4), (key2365, 4), (key2365, 4), (key2362, 4), (key2525, 4), (key2521, 4), (key2521, 4), (key2525, 4), (key2460, 4), (key2460, 4), (key2521, 4), (key2521, 4), (key2460, 4), (key2460, 4), (key2457, 4), (key2457, 4), (key2564, 4), (key2564, 4), (key2562, 4), (key2564, 4), (key2564, 4), (key2533, 4), (key2533, 4), (key2532, 4), (key2532, 4), (key2562, 4), (key2532, 4), (key2532, 4)]

theorem rawRowCheck18914 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block5.form5 = rawRow18914 := by decide +kernel

def row18914 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 16), (key2525, 8), (key2532, 16), (key2533, 8), (key2562, 8), (key2564, 16)]

theorem rowCheck18914 : row18914 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18914 := by decide +kernel

theorem rowEval18914 (x : Key → ℝ) : Integer.Sparse.eval row18914 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck18914, Integer.Sparse.eval_collectBalanced, rawRowCheck18914]

def rawRow18915 : Integer.Sparse Key := [(key2457, 4), (key2460, 4), (key2460, 4), (key2521, 4), (key2521, 4), (key2525, 4), (key2362, 4), (key2365, 4), (key2365, 4), (key2457, 4), (key2521, 4), (key2521, 4), (key2532, 4), (key2532, 4), (key2562, 4), (key2562, 4), (key2564, 4), (key2564, 4), (key2365, 4), (key2365, 4), (key2367, 4), (key2460, 4), (key2460, 4), (key2521, 4), (key2521, 4), (key2525, 4), (key2525, 4), (key2533, 4), (key2564, 4), (key2564, 4)]

theorem rawRowCheck18915 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block5.form5 = rawRow18915 := by decide +kernel

def row18915 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 24), (key2525, 12), (key2532, 8), (key2533, 4), (key2562, 8), (key2564, 16)]

theorem rowCheck18915 : row18915 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18915 := by decide +kernel

theorem rowEval18915 (x : Key → ℝ) : Integer.Sparse.eval row18915 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block5.form5) x := by
  rw [rowCheck18915, Integer.Sparse.eval_collectBalanced, rawRowCheck18915]

def rawRow18916 : Integer.Sparse Key := [(key2460, 4), (key2457, 4), (key2460, 4), (key2521, 4), (key2525, 4), (key2521, 4), (key2365, 4), (key2362, 4), (key2365, 4), (key2521, 4), (key2457, 4), (key2521, 4), (key2562, 4), (key2564, 4), (key2532, 4), (key2564, 4), (key2532, 4), (key2562, 4), (key2365, 4), (key2367, 4), (key2365, 4), (key2521, 4), (key2525, 4), (key2460, 4), (key2525, 4), (key2460, 4), (key2521, 4), (key2564, 4), (key2533, 4), (key2564, 4)]

theorem rawRowCheck18916 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block5.form5 = rawRow18916 := by decide +kernel

def row18916 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 24), (key2525, 12), (key2532, 8), (key2533, 4), (key2562, 8), (key2564, 16)]

theorem rowCheck18916 : row18916 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18916 := by decide +kernel

theorem rowEval18916 (x : Key → ℝ) : Integer.Sparse.eval row18916 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block5.form5) x := by
  rw [rowCheck18916, Integer.Sparse.eval_collectBalanced, rawRowCheck18916]

def rawRow18917 : Integer.Sparse Key := [(key2460, 4), (key2460, 4), (key2457, 4), (key2525, 4), (key2521, 4), (key2521, 4), (key2365, 4), (key2365, 4), (key2362, 4), (key2521, 4), (key2521, 4), (key2457, 4), (key2564, 4), (key2562, 4), (key2564, 4), (key2532, 4), (key2562, 4), (key2532, 4), (key2367, 4), (key2365, 4), (key2365, 4), (key2525, 4), (key2521, 4), (key2525, 4), (key2460, 4), (key2521, 4), (key2460, 4), (key2564, 4), (key2564, 4), (key2533, 4)]

theorem rawRowCheck18917 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block5.form5 = rawRow18917 := by decide +kernel

def row18917 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 24), (key2525, 12), (key2532, 8), (key2533, 4), (key2562, 8), (key2564, 16)]

theorem rowCheck18917 : row18917 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18917 := by decide +kernel

theorem rowEval18917 (x : Key → ℝ) : Integer.Sparse.eval row18917 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck18917, Integer.Sparse.eval_collectBalanced, rawRowCheck18917]

def rawRow18918 : Integer.Sparse Key := [(key2457, 4), (key2521, 4), (key2521, 4), (key2460, 4), (key2460, 4), (key2525, 4), (key2457, 4), (key2521, 4), (key2521, 4), (key2362, 4), (key2562, 4), (key2562, 4), (key2365, 4), (key2365, 4), (key2521, 4), (key2521, 4), (key2564, 4), (key2564, 4), (key2460, 4), (key2460, 4), (key2533, 4), (key2365, 4), (key2365, 4), (key2521, 4), (key2521, 4), (key2564, 4), (key2564, 4), (key2367, 4), (key2525, 4), (key2525, 4)]

theorem rawRowCheck18918 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block5.form5 = rawRow18918 := by decide +kernel

def row18918 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 32), (key2525, 12), (key2533, 4), (key2562, 8), (key2564, 16)]

theorem rowCheck18918 : row18918 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18918 := by decide +kernel

theorem rowEval18918 (x : Key → ℝ) : Integer.Sparse.eval row18918 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block5.form5) x := by
  rw [rowCheck18918, Integer.Sparse.eval_collectBalanced, rawRowCheck18918]

def rawRow18919 : Integer.Sparse Key := [(key2521, 4), (key2457, 4), (key2521, 4), (key2460, 4), (key2525, 4), (key2460, 4), (key2521, 4), (key2457, 4), (key2521, 4), (key2562, 4), (key2362, 4), (key2562, 4), (key2521, 4), (key2564, 4), (key2365, 4), (key2564, 4), (key2365, 4), (key2521, 4), (key2460, 4), (key2533, 4), (key2460, 4), (key2521, 4), (key2564, 4), (key2365, 4), (key2564, 4), (key2365, 4), (key2521, 4), (key2525, 4), (key2367, 4), (key2525, 4)]

theorem rawRowCheck18919 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block5.form5 = rawRow18919 := by decide +kernel

def row18919 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 32), (key2525, 12), (key2533, 4), (key2562, 8), (key2564, 16)]

theorem rowCheck18919 : row18919 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18919 := by decide +kernel

theorem rowEval18919 (x : Key → ℝ) : Integer.Sparse.eval row18919 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block5.form5) x := by
  rw [rowCheck18919, Integer.Sparse.eval_collectBalanced, rawRowCheck18919]

def rawRow18920 : Integer.Sparse Key := [(key2521, 4), (key2521, 4), (key2457, 4), (key2525, 4), (key2460, 4), (key2460, 4), (key2521, 4), (key2521, 4), (key2457, 4), (key2562, 4), (key2562, 4), (key2362, 4), (key2564, 4), (key2521, 4), (key2564, 4), (key2365, 4), (key2521, 4), (key2365, 4), (key2533, 4), (key2460, 4), (key2460, 4), (key2564, 4), (key2521, 4), (key2564, 4), (key2365, 4), (key2521, 4), (key2365, 4), (key2525, 4), (key2525, 4), (key2367, 4)]

theorem rawRowCheck18920 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block5.form5 = rawRow18920 := by decide +kernel

def row18920 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 32), (key2525, 12), (key2533, 4), (key2562, 8), (key2564, 16)]

theorem rowCheck18920 : row18920 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18920 := by decide +kernel

theorem rowEval18920 (x : Key → ℝ) : Integer.Sparse.eval row18920 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block5.form5) x := by
  rw [rowCheck18920, Integer.Sparse.eval_collectBalanced, rawRowCheck18920]

def rawRow18921 : Integer.Sparse Key := [(key2460, 4), (key2521, 4), (key2525, 4), (key2457, 4), (key2460, 4), (key2521, 4), (key2532, 4), (key2562, 4), (key2564, 4), (key2365, 4), (key2521, 4), (key2564, 4), (key2362, 4), (key2365, 4), (key2457, 4), (key2521, 4), (key2532, 4), (key2562, 4), (key2521, 4), (key2525, 4), (key2564, 4), (key2365, 4), (key2367, 4), (key2460, 4), (key2525, 4), (key2533, 4), (key2564, 4), (key2365, 4), (key2460, 4), (key2521, 4)]

theorem rawRowCheck18921 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block5.form5 = rawRow18921 := by decide +kernel

def row18921 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 24), (key2525, 12), (key2532, 8), (key2533, 4), (key2562, 8), (key2564, 16)]

theorem rowCheck18921 : row18921 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18921 := by decide +kernel

theorem rowEval18921 (x : Key → ℝ) : Integer.Sparse.eval row18921 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block5.form5) x := by
  rw [rowCheck18921, Integer.Sparse.eval_collectBalanced, rawRowCheck18921]

def rawRow18922 : Integer.Sparse Key := [(key2460, 4), (key2525, 4), (key2521, 4), (key2460, 4), (key2457, 4), (key2521, 4), (key2532, 4), (key2564, 4), (key2562, 4), (key2365, 4), (key2564, 4), (key2521, 4), (key2365, 4), (key2362, 4), (key2521, 4), (key2457, 4), (key2562, 4), (key2532, 4), (key2525, 4), (key2521, 4), (key2564, 4), (key2367, 4), (key2365, 4), (key2525, 4), (key2460, 4), (key2564, 4), (key2533, 4), (key2365, 4), (key2521, 4), (key2460, 4)]

theorem rawRowCheck18922 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block5.form5 = rawRow18922 := by decide +kernel

def row18922 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 24), (key2525, 12), (key2532, 8), (key2533, 4), (key2562, 8), (key2564, 16)]

theorem rowCheck18922 : row18922 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18922 := by decide +kernel

theorem rowEval18922 (x : Key → ℝ) : Integer.Sparse.eval row18922 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck18922, Integer.Sparse.eval_collectBalanced, rawRowCheck18922]

def rawRow18923 : Integer.Sparse Key := [(key2521, 4), (key2460, 4), (key2525, 4), (key2457, 4), (key2521, 4), (key2460, 4), (key2562, 4), (key2532, 4), (key2564, 4), (key2521, 4), (key2365, 4), (key2564, 4), (key2457, 4), (key2521, 4), (key2362, 4), (key2562, 4), (key2365, 4), (key2521, 4), (key2521, 4), (key2564, 4), (key2525, 4), (key2460, 4), (key2533, 4), (key2365, 4), (key2564, 4), (key2367, 4), (key2525, 4), (key2460, 4), (key2365, 4), (key2521, 4)]

theorem rawRowCheck18923 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block5.form5 = rawRow18923 := by decide +kernel

def row18923 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 28), (key2525, 12), (key2532, 4), (key2533, 4), (key2562, 8), (key2564, 16)]

theorem rowCheck18923 : row18923 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18923 := by decide +kernel

theorem rowEval18923 (x : Key → ℝ) : Integer.Sparse.eval row18923 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block5.form5) x := by
  rw [rowCheck18923, Integer.Sparse.eval_collectBalanced, rawRowCheck18923]

def rawRow18924 : Integer.Sparse Key := [(key2521, 4), (key2525, 4), (key2460, 4), (key2521, 4), (key2457, 4), (key2460, 4), (key2562, 4), (key2564, 4), (key2532, 4), (key2521, 4), (key2564, 4), (key2365, 4), (key2521, 4), (key2457, 4), (key2562, 4), (key2362, 4), (key2521, 4), (key2365, 4), (key2564, 4), (key2521, 4), (key2525, 4), (key2533, 4), (key2460, 4), (key2564, 4), (key2365, 4), (key2525, 4), (key2367, 4), (key2460, 4), (key2521, 4), (key2365, 4)]

theorem rawRowCheck18924 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block5.form5 = rawRow18924 := by decide +kernel

def row18924 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 28), (key2525, 12), (key2532, 4), (key2533, 4), (key2562, 8), (key2564, 16)]

theorem rowCheck18924 : row18924 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18924 := by decide +kernel

theorem rowEval18924 (x : Key → ℝ) : Integer.Sparse.eval row18924 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block5.form5) x := by
  rw [rowCheck18924, Integer.Sparse.eval_collectBalanced, rawRowCheck18924]

def rawRow18925 : Integer.Sparse Key := [(key2525, 4), (key2460, 4), (key2521, 4), (key2460, 4), (key2521, 4), (key2457, 4), (key2564, 4), (key2532, 4), (key2562, 4), (key2564, 4), (key2365, 4), (key2521, 4), (key2532, 4), (key2562, 4), (key2365, 4), (key2521, 4), (key2362, 4), (key2457, 4), (key2525, 4), (key2564, 4), (key2521, 4), (key2525, 4), (key2564, 4), (key2367, 4), (key2533, 4), (key2365, 4), (key2460, 4), (key2521, 4), (key2365, 4), (key2460, 4)]

theorem rawRowCheck18925 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block5.form5 = rawRow18925 := by decide +kernel

def row18925 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 24), (key2525, 12), (key2532, 8), (key2533, 4), (key2562, 8), (key2564, 16)]

theorem rowCheck18925 : row18925 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18925 := by decide +kernel

theorem rowEval18925 (x : Key → ℝ) : Integer.Sparse.eval row18925 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck18925, Integer.Sparse.eval_collectBalanced, rawRowCheck18925]

def rawRow18926 : Integer.Sparse Key := [(key2525, 4), (key2521, 4), (key2460, 4), (key2521, 4), (key2460, 4), (key2457, 4), (key2564, 4), (key2562, 4), (key2532, 4), (key2564, 4), (key2521, 4), (key2365, 4), (key2562, 4), (key2532, 4), (key2521, 4), (key2365, 4), (key2457, 4), (key2362, 4), (key2564, 4), (key2525, 4), (key2521, 4), (key2564, 4), (key2525, 4), (key2533, 4), (key2367, 4), (key2460, 4), (key2365, 4), (key2521, 4), (key2460, 4), (key2365, 4)]

theorem rawRowCheck18926 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block5.form5 = rawRow18926 := by decide +kernel

def row18926 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 24), (key2525, 12), (key2532, 8), (key2533, 4), (key2562, 8), (key2564, 16)]

theorem rowCheck18926 : row18926 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18926 := by decide +kernel

theorem rowEval18926 (x : Key → ℝ) : Integer.Sparse.eval row18926 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block5.form5) x := by
  rw [rowCheck18926, Integer.Sparse.eval_collectBalanced, rawRowCheck18926]

def rawRow18927 : Integer.Sparse Key := [(key2532, 4), (key2532, 4), (key2533, 4), (key2562, 4), (key2564, 4), (key2564, 4), (key2365, 4), (key2365, 4), (key2367, 4), (key2460, 4), (key2460, 4), (key2533, 4), (key2521, 4), (key2525, 4), (key2521, 4), (key2564, 4), (key2525, 4), (key2564, 4), (key2362, 4), (key2365, 4), (key2365, 4), (key2457, 4), (key2460, 4), (key2457, 4), (key2521, 4), (key2460, 4), (key2521, 4), (key2532, 4), (key2532, 4), (key2562, 4)]

theorem rawRowCheck18927 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block5.form5 = rawRow18927 := by decide +kernel

def row18927 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 16), (key2525, 8), (key2532, 16), (key2533, 8), (key2562, 8), (key2564, 16)]

theorem rowCheck18927 : row18927 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18927 := by decide +kernel

theorem rowEval18927 (x : Key → ℝ) : Integer.Sparse.eval row18927 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block5.form5) x := by
  rw [rowCheck18927, Integer.Sparse.eval_collectBalanced, rawRowCheck18927]

def rawRow18928 : Integer.Sparse Key := [(key2532, 4), (key2533, 4), (key2532, 4), (key2564, 4), (key2562, 4), (key2564, 4), (key2365, 4), (key2367, 4), (key2365, 4), (key2460, 4), (key2533, 4), (key2460, 4), (key2525, 4), (key2521, 4), (key2564, 4), (key2521, 4), (key2564, 4), (key2525, 4), (key2365, 4), (key2362, 4), (key2365, 4), (key2460, 4), (key2457, 4), (key2521, 4), (key2457, 4), (key2521, 4), (key2460, 4), (key2532, 4), (key2562, 4), (key2532, 4)]

theorem rawRowCheck18928 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block5.form5 = rawRow18928 := by decide +kernel

def row18928 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 16), (key2525, 8), (key2532, 16), (key2533, 8), (key2562, 8), (key2564, 16)]

theorem rowCheck18928 : row18928 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18928 := by decide +kernel

theorem rowEval18928 (x : Key → ℝ) : Integer.Sparse.eval row18928 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck18928, Integer.Sparse.eval_collectBalanced, rawRowCheck18928]

def rawRow18929 : Integer.Sparse Key := [(key2533, 4), (key2532, 4), (key2532, 4), (key2564, 4), (key2564, 4), (key2562, 4), (key2367, 4), (key2365, 4), (key2365, 4), (key2533, 4), (key2460, 4), (key2460, 4), (key2564, 4), (key2564, 4), (key2525, 4), (key2525, 4), (key2521, 4), (key2521, 4), (key2365, 4), (key2365, 4), (key2362, 4), (key2521, 4), (key2521, 4), (key2460, 4), (key2460, 4), (key2457, 4), (key2457, 4), (key2562, 4), (key2532, 4), (key2532, 4)]

theorem rawRowCheck18929 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block5.form5 = rawRow18929 := by decide +kernel

def row18929 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 16), (key2525, 8), (key2532, 16), (key2533, 8), (key2562, 8), (key2564, 16)]

theorem rowCheck18929 : row18929 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18929 := by decide +kernel

theorem rowEval18929 (x : Key → ℝ) : Integer.Sparse.eval row18929 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck18929, Integer.Sparse.eval_collectBalanced, rawRowCheck18929]

def rawRow18930 : Integer.Sparse Key := [(key2532, 4), (key2562, 4), (key2564, 4), (key2532, 4), (key2533, 4), (key2564, 4), (key2460, 4), (key2521, 4), (key2525, 4), (key2365, 4), (key2521, 4), (key2564, 4), (key2365, 4), (key2367, 4), (key2460, 4), (key2533, 4), (key2525, 4), (key2564, 4), (key2457, 4), (key2460, 4), (key2521, 4), (key2362, 4), (key2365, 4), (key2457, 4), (key2521, 4), (key2532, 4), (key2562, 4), (key2365, 4), (key2460, 4), (key2521, 4)]

theorem rawRowCheck18930 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block5.form5 = rawRow18930 := by decide +kernel

def row18930 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 20), (key2525, 8), (key2532, 12), (key2533, 8), (key2562, 8), (key2564, 16)]

theorem rowCheck18930 : row18930 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18930 := by decide +kernel

theorem rowEval18930 (x : Key → ℝ) : Integer.Sparse.eval row18930 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block5.form5) x := by
  rw [rowCheck18930, Integer.Sparse.eval_collectBalanced, rawRowCheck18930]

def rawRow18931 : Integer.Sparse Key := [(key2532, 4), (key2564, 4), (key2562, 4), (key2533, 4), (key2532, 4), (key2564, 4), (key2460, 4), (key2525, 4), (key2521, 4), (key2365, 4), (key2564, 4), (key2521, 4), (key2367, 4), (key2365, 4), (key2533, 4), (key2460, 4), (key2564, 4), (key2525, 4), (key2460, 4), (key2457, 4), (key2521, 4), (key2365, 4), (key2362, 4), (key2521, 4), (key2457, 4), (key2562, 4), (key2532, 4), (key2365, 4), (key2521, 4), (key2460, 4)]

theorem rawRowCheck18931 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block5.form5 = rawRow18931 := by decide +kernel

def row18931 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 20), (key2525, 8), (key2532, 12), (key2533, 8), (key2562, 8), (key2564, 16)]

theorem rowCheck18931 : row18931 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18931 := by decide +kernel

theorem rowEval18931 (x : Key → ℝ) : Integer.Sparse.eval row18931 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck18931, Integer.Sparse.eval_collectBalanced, rawRowCheck18931]

def rawRow18932 : Integer.Sparse Key := [(key2562, 4), (key2532, 4), (key2564, 4), (key2532, 4), (key2564, 4), (key2533, 4), (key2521, 4), (key2460, 4), (key2525, 4), (key2521, 4), (key2365, 4), (key2564, 4), (key2460, 4), (key2525, 4), (key2365, 4), (key2564, 4), (key2367, 4), (key2533, 4), (key2457, 4), (key2521, 4), (key2460, 4), (key2457, 4), (key2521, 4), (key2362, 4), (key2562, 4), (key2365, 4), (key2521, 4), (key2460, 4), (key2365, 4), (key2521, 4)]

theorem rawRowCheck18932 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block5.form5 = rawRow18932 := by decide +kernel

def row18932 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 24), (key2525, 8), (key2532, 8), (key2533, 8), (key2562, 8), (key2564, 16)]

theorem rowCheck18932 : row18932 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18932 := by decide +kernel

theorem rowEval18932 (x : Key → ℝ) : Integer.Sparse.eval row18932 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block5.form5) x := by
  rw [rowCheck18932, Integer.Sparse.eval_collectBalanced, rawRowCheck18932]

def rawRow18933 : Integer.Sparse Key := [(key2562, 4), (key2564, 4), (key2532, 4), (key2564, 4), (key2532, 4), (key2533, 4), (key2521, 4), (key2525, 4), (key2460, 4), (key2521, 4), (key2564, 4), (key2365, 4), (key2525, 4), (key2460, 4), (key2564, 4), (key2365, 4), (key2533, 4), (key2367, 4), (key2521, 4), (key2457, 4), (key2460, 4), (key2521, 4), (key2457, 4), (key2562, 4), (key2362, 4), (key2521, 4), (key2365, 4), (key2460, 4), (key2521, 4), (key2365, 4)]

theorem rawRowCheck18933 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block5.form5 = rawRow18933 := by decide +kernel

def row18933 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 24), (key2525, 8), (key2532, 8), (key2533, 8), (key2562, 8), (key2564, 16)]

theorem rowCheck18933 : row18933 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18933 := by decide +kernel

theorem rowEval18933 (x : Key → ℝ) : Integer.Sparse.eval row18933 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block5.form5) x := by
  rw [rowCheck18933, Integer.Sparse.eval_collectBalanced, rawRowCheck18933]

def rawRow18934 : Integer.Sparse Key := [(key2564, 4), (key2532, 4), (key2562, 4), (key2533, 4), (key2564, 4), (key2532, 4), (key2525, 4), (key2460, 4), (key2521, 4), (key2564, 4), (key2365, 4), (key2521, 4), (key2533, 4), (key2564, 4), (key2367, 4), (key2525, 4), (key2365, 4), (key2460, 4), (key2460, 4), (key2521, 4), (key2457, 4), (key2532, 4), (key2562, 4), (key2365, 4), (key2521, 4), (key2362, 4), (key2457, 4), (key2521, 4), (key2365, 4), (key2460, 4)]

theorem rawRowCheck18934 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block5.form5 = rawRow18934 := by decide +kernel

def row18934 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 20), (key2525, 8), (key2532, 12), (key2533, 8), (key2562, 8), (key2564, 16)]

theorem rowCheck18934 : row18934 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18934 := by decide +kernel

theorem rowEval18934 (x : Key → ℝ) : Integer.Sparse.eval row18934 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck18934, Integer.Sparse.eval_collectBalanced, rawRowCheck18934]

def rawRow18935 : Integer.Sparse Key := [(key2564, 4), (key2562, 4), (key2532, 4), (key2564, 4), (key2533, 4), (key2532, 4), (key2525, 4), (key2521, 4), (key2460, 4), (key2564, 4), (key2521, 4), (key2365, 4), (key2564, 4), (key2533, 4), (key2525, 4), (key2367, 4), (key2460, 4), (key2365, 4), (key2521, 4), (key2460, 4), (key2457, 4), (key2562, 4), (key2532, 4), (key2521, 4), (key2365, 4), (key2457, 4), (key2362, 4), (key2521, 4), (key2460, 4), (key2365, 4)]

theorem rawRowCheck18935 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block5.form5 = rawRow18935 := by decide +kernel

def row18935 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 20), (key2525, 8), (key2532, 12), (key2533, 8), (key2562, 8), (key2564, 16)]

theorem rowCheck18935 : row18935 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18935 := by decide +kernel

theorem rowEval18935 (x : Key → ℝ) : Integer.Sparse.eval row18935 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block5.form5) x := by
  rw [rowCheck18935, Integer.Sparse.eval_collectBalanced, rawRowCheck18935]

def rawRow18936 : Integer.Sparse Key := [(key2533, 4), (key2564, 4), (key2564, 4), (key2532, 4), (key2532, 4), (key2562, 4), (key2533, 4), (key2564, 4), (key2564, 4), (key2367, 4), (key2525, 4), (key2525, 4), (key2365, 4), (key2365, 4), (key2460, 4), (key2460, 4), (key2521, 4), (key2521, 4), (key2532, 4), (key2532, 4), (key2562, 4), (key2365, 4), (key2365, 4), (key2460, 4), (key2460, 4), (key2521, 4), (key2521, 4), (key2362, 4), (key2457, 4), (key2457, 4)]

theorem rawRowCheck18936 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block5.form5 = rawRow18936 := by decide +kernel

def row18936 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 16), (key2525, 8), (key2532, 16), (key2533, 8), (key2562, 8), (key2564, 16)]

theorem rowCheck18936 : row18936 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18936 := by decide +kernel

theorem rowEval18936 (x : Key → ℝ) : Integer.Sparse.eval row18936 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck18936, Integer.Sparse.eval_collectBalanced, rawRowCheck18936]

def rawRow18937 : Integer.Sparse Key := [(key2564, 4), (key2533, 4), (key2564, 4), (key2532, 4), (key2562, 4), (key2532, 4), (key2564, 4), (key2533, 4), (key2564, 4), (key2525, 4), (key2367, 4), (key2525, 4), (key2460, 4), (key2521, 4), (key2365, 4), (key2521, 4), (key2365, 4), (key2460, 4), (key2532, 4), (key2562, 4), (key2532, 4), (key2460, 4), (key2521, 4), (key2365, 4), (key2521, 4), (key2365, 4), (key2460, 4), (key2457, 4), (key2362, 4), (key2457, 4)]

theorem rawRowCheck18937 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block5.form5 = rawRow18937 := by decide +kernel

def row18937 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 16), (key2525, 8), (key2532, 16), (key2533, 8), (key2562, 8), (key2564, 16)]

theorem rowCheck18937 : row18937 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18937 := by decide +kernel

theorem rowEval18937 (x : Key → ℝ) : Integer.Sparse.eval row18937 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck18937, Integer.Sparse.eval_collectBalanced, rawRowCheck18937]

def rawRow18938 : Integer.Sparse Key := [(key2564, 4), (key2564, 4), (key2533, 4), (key2562, 4), (key2532, 4), (key2532, 4), (key2564, 4), (key2564, 4), (key2533, 4), (key2525, 4), (key2525, 4), (key2367, 4), (key2521, 4), (key2460, 4), (key2521, 4), (key2365, 4), (key2460, 4), (key2365, 4), (key2562, 4), (key2532, 4), (key2532, 4), (key2521, 4), (key2460, 4), (key2521, 4), (key2365, 4), (key2460, 4), (key2365, 4), (key2457, 4), (key2457, 4), (key2362, 4)]

theorem rawRowCheck18938 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block5.form5 = rawRow18938 := by decide +kernel

def row18938 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 16), (key2525, 8), (key2532, 16), (key2533, 8), (key2562, 8), (key2564, 16)]

theorem rowCheck18938 : row18938 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18938 := by decide +kernel

theorem rowEval18938 (x : Key → ℝ) : Integer.Sparse.eval row18938 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block5.form5) x := by
  rw [rowCheck18938, Integer.Sparse.eval_collectBalanced, rawRowCheck18938]

def rawRow18939 : Integer.Sparse Key := [(key2354, 6), (key2358, 6), (key2358, 6), (key2358, 6), (key2449, 6), (key2453, 6), (key2453, 6), (key2449, 6), (key2453, 6), (key2449, 6), (key2529, 6), (key2453, 6), (key2529, 6), (key2453, 6), (key2453, 6), (key2529, 6), (key2514, 6), (key2514, 6), (key2514, 6), (key2559, 6)]

theorem rawRowCheck18939 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block5.form0 = rawRow18939 := by decide +kernel

def row18939 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

theorem rowCheck18939 : row18939 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18939 := by decide +kernel

theorem rowEval18939 (x : Key → ℝ) : Integer.Sparse.eval row18939 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18939, Integer.Sparse.eval_collectBalanced, rawRowCheck18939]

def rawRow18940 : Integer.Sparse Key := [(key2358, 6), (key2354, 6), (key2358, 6), (key2358, 6), (key2453, 6), (key2449, 6), (key2453, 6), (key2453, 6), (key2449, 6), (key2529, 6), (key2449, 6), (key2529, 6), (key2453, 6), (key2453, 6), (key2529, 6), (key2453, 6), (key2514, 6), (key2514, 6), (key2559, 6), (key2514, 6)]

theorem rawRowCheck18940 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block5.form0 = rawRow18940 := by decide +kernel

def row18940 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

theorem rowCheck18940 : row18940 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18940 := by decide +kernel

theorem rowEval18940 (x : Key → ℝ) : Integer.Sparse.eval row18940 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18940, Integer.Sparse.eval_collectBalanced, rawRowCheck18940]

def rawRow18941 : Integer.Sparse Key := [(key2358, 6), (key2358, 6), (key2354, 6), (key2358, 6), (key2453, 6), (key2453, 6), (key2449, 6), (key2529, 6), (key2529, 6), (key2453, 6), (key2453, 6), (key2449, 6), (key2449, 6), (key2529, 6), (key2453, 6), (key2453, 6), (key2514, 6), (key2559, 6), (key2514, 6), (key2514, 6)]

theorem rawRowCheck18941 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block5.form0 = rawRow18941 := by decide +kernel

def row18941 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

theorem rowCheck18941 : row18941 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18941 := by decide +kernel

theorem rowEval18941 (x : Key → ℝ) : Integer.Sparse.eval row18941 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18941, Integer.Sparse.eval_collectBalanced, rawRowCheck18941]

def rawRow18942 : Integer.Sparse Key := [(key2358, 6), (key2358, 6), (key2358, 6), (key2354, 6), (key2529, 6), (key2529, 6), (key2529, 6), (key2453, 6), (key2453, 6), (key2453, 6), (key2453, 6), (key2453, 6), (key2453, 6), (key2449, 6), (key2449, 6), (key2449, 6), (key2559, 6), (key2514, 6), (key2514, 6), (key2514, 6)]

theorem rawRowCheck18942 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block5.form0 = rawRow18942 := by decide +kernel

def row18942 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

theorem rowCheck18942 : row18942 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18942 := by decide +kernel

theorem rowEval18942 (x : Key → ℝ) : Integer.Sparse.eval row18942 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18942, Integer.Sparse.eval_collectBalanced, rawRowCheck18942]

def rawRow18943 : Integer.Sparse Key := [(key2449, 6), (key2453, 6), (key2453, 6), (key2514, 6), (key2354, 6), (key2358, 6), (key2358, 6), (key2449, 6), (key2453, 6), (key2449, 6), (key2529, 6), (key2453, 6), (key2529, 6), (key2514, 6), (key2514, 6), (key2559, 6), (key2358, 6), (key2453, 6), (key2453, 6), (key2529, 6)]

theorem rawRowCheck18943 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block5.form0 = rawRow18943 := by decide +kernel

def row18943 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

theorem rowCheck18943 : row18943 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18943 := by decide +kernel

theorem rowEval18943 (x : Key → ℝ) : Integer.Sparse.eval row18943 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18943, Integer.Sparse.eval_collectBalanced, rawRowCheck18943]

end MUB6.Certificate.GramRows

end OAI
