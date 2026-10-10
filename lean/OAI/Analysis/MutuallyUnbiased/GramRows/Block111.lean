import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block16
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block17
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow11136 : Integer.Sparse Key := [(key2469, 6), (key2500, 6), (key2465, 6), (key2477, 6), (key2403, -6), (key2536, -6), (key2375, -6), (key2469, -6)]

theorem rawRowCheck11136 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form12 = rawRow11136 := by decide +kernel

def row11136 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

theorem rowCheck11136 : row11136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11136 := by decide +kernel

theorem rowEval11136 (x : Key → ℝ) : Integer.Sparse.eval row11136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11136, Integer.Sparse.eval_collectBalanced, rawRowCheck11136]

def rawRow11137 : Integer.Sparse Key := [(key2500, 6), (key2469, 6), (key2465, 6), (key2477, 6), (key2403, -6), (key2536, -6), (key2469, -6), (key2375, -6)]

theorem rawRowCheck11137 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form12 = rawRow11137 := by decide +kernel

def row11137 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

theorem rowCheck11137 : row11137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11137 := by decide +kernel

theorem rowEval11137 (x : Key → ℝ) : Integer.Sparse.eval row11137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck11137, Integer.Sparse.eval_collectBalanced, rawRowCheck11137]

def rawRow11138 : Integer.Sparse Key := [(key2465, 6), (key2477, 6), (key2500, 6), (key2469, 6), (key2469, -6), (key2375, -6), (key2403, -6), (key2536, -6)]

theorem rawRowCheck11138 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form12 = rawRow11138 := by decide +kernel

def row11138 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

theorem rowCheck11138 : row11138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11138 := by decide +kernel

theorem rowEval11138 (x : Key → ℝ) : Integer.Sparse.eval row11138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11138, Integer.Sparse.eval_collectBalanced, rawRowCheck11138]

def rawRow11139 : Integer.Sparse Key := [(key2477, 6), (key2465, 6), (key2500, 6), (key2469, 6), (key2469, -6), (key2375, -6), (key2536, -6), (key2403, -6)]

theorem rawRowCheck11139 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form12 = rawRow11139 := by decide +kernel

def row11139 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

theorem rowCheck11139 : row11139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11139 := by decide +kernel

theorem rowEval11139 (x : Key → ℝ) : Integer.Sparse.eval row11139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11139, Integer.Sparse.eval_collectBalanced, rawRowCheck11139]

def rawRow11140 : Integer.Sparse Key := [(key2465, 6), (key2500, 6), (key2477, 6), (key2469, 6), (key2469, -6), (key2403, -6), (key2375, -6), (key2536, -6)]

theorem rawRowCheck11140 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form12 = rawRow11140 := by decide +kernel

def row11140 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

theorem rowCheck11140 : row11140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11140 := by decide +kernel

theorem rowEval11140 (x : Key → ℝ) : Integer.Sparse.eval row11140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11140, Integer.Sparse.eval_collectBalanced, rawRowCheck11140]

def rawRow11141 : Integer.Sparse Key := [(key2500, 6), (key2465, 6), (key2477, 6), (key2469, 6), (key2469, -6), (key2403, -6), (key2536, -6), (key2375, -6)]

theorem rawRowCheck11141 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form12 = rawRow11141 := by decide +kernel

def row11141 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

theorem rowCheck11141 : row11141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11141 := by decide +kernel

theorem rowEval11141 (x : Key → ℝ) : Integer.Sparse.eval row11141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck11141, Integer.Sparse.eval_collectBalanced, rawRowCheck11141]

def rawRow11142 : Integer.Sparse Key := [(key2477, 6), (key2500, 6), (key2465, 6), (key2469, 6), (key2469, -6), (key2536, -6), (key2375, -6), (key2403, -6)]

theorem rawRowCheck11142 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form12 = rawRow11142 := by decide +kernel

def row11142 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

theorem rowCheck11142 : row11142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11142 := by decide +kernel

theorem rowEval11142 (x : Key → ℝ) : Integer.Sparse.eval row11142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11142, Integer.Sparse.eval_collectBalanced, rawRowCheck11142]

def rawRow11143 : Integer.Sparse Key := [(key2500, 6), (key2477, 6), (key2465, 6), (key2469, 6), (key2469, -6), (key2536, -6), (key2403, -6), (key2375, -6)]

theorem rawRowCheck11143 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form12 = rawRow11143 := by decide +kernel

def row11143 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

theorem rowCheck11143 : row11143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11143 := by decide +kernel

theorem rowEval11143 (x : Key → ℝ) : Integer.Sparse.eval row11143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck11143, Integer.Sparse.eval_collectBalanced, rawRowCheck11143]

def rawRow11144 : Integer.Sparse Key := [(key2469, 6), (key2477, 6), (key2500, 6), (key2465, 6), (key2536, -6), (key2375, -6), (key2403, -6), (key2469, -6)]

theorem rawRowCheck11144 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form12 = rawRow11144 := by decide +kernel

def row11144 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

theorem rowCheck11144 : row11144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11144 := by decide +kernel

theorem rowEval11144 (x : Key → ℝ) : Integer.Sparse.eval row11144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11144, Integer.Sparse.eval_collectBalanced, rawRowCheck11144]

def rawRow11145 : Integer.Sparse Key := [(key2477, 6), (key2469, 6), (key2500, 6), (key2465, 6), (key2536, -6), (key2375, -6), (key2469, -6), (key2403, -6)]

theorem rawRowCheck11145 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form12 = rawRow11145 := by decide +kernel

def row11145 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

theorem rowCheck11145 : row11145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11145 := by decide +kernel

theorem rowEval11145 (x : Key → ℝ) : Integer.Sparse.eval row11145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11145, Integer.Sparse.eval_collectBalanced, rawRowCheck11145]

def rawRow11146 : Integer.Sparse Key := [(key2469, 6), (key2500, 6), (key2477, 6), (key2465, 6), (key2536, -6), (key2403, -6), (key2375, -6), (key2469, -6)]

theorem rawRowCheck11146 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form12 = rawRow11146 := by decide +kernel

def row11146 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

theorem rowCheck11146 : row11146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11146 := by decide +kernel

theorem rowEval11146 (x : Key → ℝ) : Integer.Sparse.eval row11146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11146, Integer.Sparse.eval_collectBalanced, rawRowCheck11146]

def rawRow11147 : Integer.Sparse Key := [(key2500, 6), (key2469, 6), (key2477, 6), (key2465, 6), (key2536, -6), (key2403, -6), (key2469, -6), (key2375, -6)]

theorem rawRowCheck11147 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form12 = rawRow11147 := by decide +kernel

def row11147 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

theorem rowCheck11147 : row11147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11147 := by decide +kernel

theorem rowEval11147 (x : Key → ℝ) : Integer.Sparse.eval row11147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck11147, Integer.Sparse.eval_collectBalanced, rawRowCheck11147]

def rawRow11148 : Integer.Sparse Key := [(key2477, 6), (key2500, 6), (key2469, 6), (key2465, 6), (key2536, -6), (key2469, -6), (key2375, -6), (key2403, -6)]

theorem rawRowCheck11148 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form12 = rawRow11148 := by decide +kernel

def row11148 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

theorem rowCheck11148 : row11148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11148 := by decide +kernel

theorem rowEval11148 (x : Key → ℝ) : Integer.Sparse.eval row11148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11148, Integer.Sparse.eval_collectBalanced, rawRowCheck11148]

def rawRow11149 : Integer.Sparse Key := [(key2500, 6), (key2477, 6), (key2469, 6), (key2465, 6), (key2536, -6), (key2469, -6), (key2403, -6), (key2375, -6)]

theorem rawRowCheck11149 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form12 = rawRow11149 := by decide +kernel

def row11149 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

theorem rowCheck11149 : row11149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11149 := by decide +kernel

theorem rowEval11149 (x : Key → ℝ) : Integer.Sparse.eval row11149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck11149, Integer.Sparse.eval_collectBalanced, rawRowCheck11149]

def rawRow11150 : Integer.Sparse Key := [(key2536, 6), (key2536, 6), (key2541, 6), (key2552, 6), (key2371, -6), (key2399, -6), (key2465, -6), (key2465, -6)]

theorem rawRowCheck11150 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form12 = rawRow11150 := by decide +kernel

def row11150 : Integer.Sparse Key := [(key2371, -6), (key2399, -6), (key2465, -12), (key2536, 12), (key2541, 6), (key2552, 6)]

theorem rowCheck11150 : row11150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11150 := by decide +kernel

theorem rowEval11150 (x : Key → ℝ) : Integer.Sparse.eval row11150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11150, Integer.Sparse.eval_collectBalanced, rawRowCheck11150]

def rawRow11151 : Integer.Sparse Key := [(key2536, 6), (key2541, 6), (key2536, 6), (key2552, 6), (key2371, -6), (key2465, -6), (key2399, -6), (key2465, -6)]

theorem rawRowCheck11151 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form12 = rawRow11151 := by decide +kernel

def row11151 : Integer.Sparse Key := [(key2371, -6), (key2399, -6), (key2465, -12), (key2536, 12), (key2541, 6), (key2552, 6)]

theorem rowCheck11151 : row11151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11151 := by decide +kernel

theorem rowEval11151 (x : Key → ℝ) : Integer.Sparse.eval row11151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11151, Integer.Sparse.eval_collectBalanced, rawRowCheck11151]

def rawRow11152 : Integer.Sparse Key := [(key2541, 6), (key2536, 6), (key2536, 6), (key2552, 6), (key2371, -6), (key2465, -6), (key2465, -6), (key2399, -6)]

theorem rawRowCheck11152 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form12 = rawRow11152 := by decide +kernel

def row11152 : Integer.Sparse Key := [(key2371, -6), (key2399, -6), (key2465, -12), (key2536, 12), (key2541, 6), (key2552, 6)]

theorem rowCheck11152 : row11152 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11152 := by decide +kernel

theorem rowEval11152 (x : Key → ℝ) : Integer.Sparse.eval row11152 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11152, Integer.Sparse.eval_collectBalanced, rawRowCheck11152]

def rawRow11153 : Integer.Sparse Key := [(key2536, 6), (key2536, 6), (key2552, 6), (key2541, 6), (key2399, -6), (key2371, -6), (key2465, -6), (key2465, -6)]

theorem rawRowCheck11153 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form12 = rawRow11153 := by decide +kernel

def row11153 : Integer.Sparse Key := [(key2371, -6), (key2399, -6), (key2465, -12), (key2536, 12), (key2541, 6), (key2552, 6)]

theorem rowCheck11153 : row11153 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11153 := by decide +kernel

theorem rowEval11153 (x : Key → ℝ) : Integer.Sparse.eval row11153 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11153, Integer.Sparse.eval_collectBalanced, rawRowCheck11153]

def rawRow11154 : Integer.Sparse Key := [(key2536, 6), (key2552, 6), (key2536, 6), (key2541, 6), (key2399, -6), (key2465, -6), (key2371, -6), (key2465, -6)]

theorem rawRowCheck11154 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form12 = rawRow11154 := by decide +kernel

def row11154 : Integer.Sparse Key := [(key2371, -6), (key2399, -6), (key2465, -12), (key2536, 12), (key2541, 6), (key2552, 6)]

theorem rowCheck11154 : row11154 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11154 := by decide +kernel

theorem rowEval11154 (x : Key → ℝ) : Integer.Sparse.eval row11154 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11154, Integer.Sparse.eval_collectBalanced, rawRowCheck11154]

def rawRow11155 : Integer.Sparse Key := [(key2552, 6), (key2536, 6), (key2536, 6), (key2541, 6), (key2399, -6), (key2465, -6), (key2465, -6), (key2371, -6)]

theorem rawRowCheck11155 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form12 = rawRow11155 := by decide +kernel

def row11155 : Integer.Sparse Key := [(key2371, -6), (key2399, -6), (key2465, -12), (key2536, 12), (key2541, 6), (key2552, 6)]

theorem rowCheck11155 : row11155 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11155 := by decide +kernel

theorem rowEval11155 (x : Key → ℝ) : Integer.Sparse.eval row11155 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck11155, Integer.Sparse.eval_collectBalanced, rawRowCheck11155]

def rawRow11156 : Integer.Sparse Key := [(key2536, 6), (key2541, 6), (key2552, 6), (key2536, 6), (key2465, -6), (key2371, -6), (key2399, -6), (key2465, -6)]

theorem rawRowCheck11156 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form12 = rawRow11156 := by decide +kernel

def row11156 : Integer.Sparse Key := [(key2371, -6), (key2399, -6), (key2465, -12), (key2536, 12), (key2541, 6), (key2552, 6)]

theorem rowCheck11156 : row11156 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11156 := by decide +kernel

theorem rowEval11156 (x : Key → ℝ) : Integer.Sparse.eval row11156 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11156, Integer.Sparse.eval_collectBalanced, rawRowCheck11156]

def rawRow11157 : Integer.Sparse Key := [(key2541, 6), (key2536, 6), (key2552, 6), (key2536, 6), (key2465, -6), (key2371, -6), (key2465, -6), (key2399, -6)]

theorem rawRowCheck11157 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form12 = rawRow11157 := by decide +kernel

def row11157 : Integer.Sparse Key := [(key2371, -6), (key2399, -6), (key2465, -12), (key2536, 12), (key2541, 6), (key2552, 6)]

theorem rowCheck11157 : row11157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11157 := by decide +kernel

theorem rowEval11157 (x : Key → ℝ) : Integer.Sparse.eval row11157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11157, Integer.Sparse.eval_collectBalanced, rawRowCheck11157]

def rawRow11158 : Integer.Sparse Key := [(key2536, 6), (key2552, 6), (key2541, 6), (key2536, 6), (key2465, -6), (key2399, -6), (key2371, -6), (key2465, -6)]

theorem rawRowCheck11158 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form12 = rawRow11158 := by decide +kernel

def row11158 : Integer.Sparse Key := [(key2371, -6), (key2399, -6), (key2465, -12), (key2536, 12), (key2541, 6), (key2552, 6)]

theorem rowCheck11158 : row11158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11158 := by decide +kernel

theorem rowEval11158 (x : Key → ℝ) : Integer.Sparse.eval row11158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11158, Integer.Sparse.eval_collectBalanced, rawRowCheck11158]

def rawRow11159 : Integer.Sparse Key := [(key2552, 6), (key2536, 6), (key2541, 6), (key2536, 6), (key2465, -6), (key2399, -6), (key2465, -6), (key2371, -6)]

theorem rawRowCheck11159 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form12 = rawRow11159 := by decide +kernel

def row11159 : Integer.Sparse Key := [(key2371, -6), (key2399, -6), (key2465, -12), (key2536, 12), (key2541, 6), (key2552, 6)]

theorem rowCheck11159 : row11159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11159 := by decide +kernel

theorem rowEval11159 (x : Key → ℝ) : Integer.Sparse.eval row11159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck11159, Integer.Sparse.eval_collectBalanced, rawRowCheck11159]

def rawRow11160 : Integer.Sparse Key := [(key2541, 6), (key2552, 6), (key2536, 6), (key2536, 6), (key2465, -6), (key2465, -6), (key2371, -6), (key2399, -6)]

theorem rawRowCheck11160 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form12 = rawRow11160 := by decide +kernel

def row11160 : Integer.Sparse Key := [(key2371, -6), (key2399, -6), (key2465, -12), (key2536, 12), (key2541, 6), (key2552, 6)]

theorem rowCheck11160 : row11160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11160 := by decide +kernel

theorem rowEval11160 (x : Key → ℝ) : Integer.Sparse.eval row11160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11160, Integer.Sparse.eval_collectBalanced, rawRowCheck11160]

def rawRow11161 : Integer.Sparse Key := [(key2552, 6), (key2541, 6), (key2536, 6), (key2536, 6), (key2465, -6), (key2465, -6), (key2399, -6), (key2371, -6)]

theorem rawRowCheck11161 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form12 = rawRow11161 := by decide +kernel

def row11161 : Integer.Sparse Key := [(key2371, -6), (key2399, -6), (key2465, -12), (key2536, 12), (key2541, 6), (key2552, 6)]

theorem rowCheck11161 : row11161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11161 := by decide +kernel

theorem rowEval11161 (x : Key → ℝ) : Integer.Sparse.eval row11161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck11161, Integer.Sparse.eval_collectBalanced, rawRowCheck11161]

def rawRow11162 : Integer.Sparse Key := [(key2302, -6), (key2303, -6), (key2305, -6), (key2310, -6), (key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2302, 2), (key2341, 2), (key2305, 2), (key2343, 2), (key2200, 2), (key2310, 2), (key2347, 2)]

theorem rawRowCheck11162 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form13 = rawRow11162 := by decide +kernel

def row11162 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

theorem rowCheck11162 : row11162 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11162 := by decide +kernel

theorem rowEval11162 (x : Key → ℝ) : Integer.Sparse.eval row11162 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck11162, Integer.Sparse.eval_collectBalanced, rawRowCheck11162]

def rawRow11163 : Integer.Sparse Key := [(key2303, -6), (key2302, -6), (key2305, -6), (key2310, -6), (key2092, 2), (key2091, 2), (key2095, 2), (key2194, 2), (key2193, 2), (key2341, 2), (key2302, 2), (key2343, 2), (key2305, 2), (key2200, 2), (key2347, 2), (key2310, 2)]

theorem rawRowCheck11163 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form13 = rawRow11163 := by decide +kernel

def row11163 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

theorem rowCheck11163 : row11163 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11163 := by decide +kernel

theorem rowEval11163 (x : Key → ℝ) : Integer.Sparse.eval row11163 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck11163, Integer.Sparse.eval_collectBalanced, rawRowCheck11163]

def rawRow11164 : Integer.Sparse Key := [(key2302, -6), (key2305, -6), (key2303, -6), (key2310, -6), (key2091, 2), (key2095, 2), (key2092, 2), (key2302, 2), (key2305, 2), (key2193, 2), (key2343, 2), (key2194, 2), (key2341, 2), (key2310, 2), (key2200, 2), (key2347, 2)]

theorem rawRowCheck11164 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form13 = rawRow11164 := by decide +kernel

def row11164 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

theorem rowCheck11164 : row11164 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11164 := by decide +kernel

theorem rowEval11164 (x : Key → ℝ) : Integer.Sparse.eval row11164 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck11164, Integer.Sparse.eval_collectBalanced, rawRowCheck11164]

def rawRow11165 : Integer.Sparse Key := [(key2305, -6), (key2302, -6), (key2303, -6), (key2310, -6), (key2095, 2), (key2091, 2), (key2092, 2), (key2305, 2), (key2302, 2), (key2343, 2), (key2193, 2), (key2341, 2), (key2194, 2), (key2310, 2), (key2347, 2), (key2200, 2)]

theorem rawRowCheck11165 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form13 = rawRow11165 := by decide +kernel

def row11165 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

theorem rowCheck11165 : row11165 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11165 := by decide +kernel

theorem rowEval11165 (x : Key → ℝ) : Integer.Sparse.eval row11165 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck11165, Integer.Sparse.eval_collectBalanced, rawRowCheck11165]

def rawRow11166 : Integer.Sparse Key := [(key2303, -6), (key2305, -6), (key2302, -6), (key2310, -6), (key2092, 2), (key2095, 2), (key2091, 2), (key2341, 2), (key2343, 2), (key2194, 2), (key2305, 2), (key2193, 2), (key2302, 2), (key2347, 2), (key2200, 2), (key2310, 2)]

theorem rawRowCheck11166 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form13 = rawRow11166 := by decide +kernel

def row11166 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

theorem rowCheck11166 : row11166 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11166 := by decide +kernel

theorem rowEval11166 (x : Key → ℝ) : Integer.Sparse.eval row11166 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck11166, Integer.Sparse.eval_collectBalanced, rawRowCheck11166]

def rawRow11167 : Integer.Sparse Key := [(key2305, -6), (key2303, -6), (key2302, -6), (key2310, -6), (key2095, 2), (key2092, 2), (key2091, 2), (key2343, 2), (key2341, 2), (key2305, 2), (key2194, 2), (key2302, 2), (key2193, 2), (key2347, 2), (key2310, 2), (key2200, 2)]

theorem rawRowCheck11167 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form13 = rawRow11167 := by decide +kernel

def row11167 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

theorem rowCheck11167 : row11167 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11167 := by decide +kernel

theorem rowEval11167 (x : Key → ℝ) : Integer.Sparse.eval row11167 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck11167, Integer.Sparse.eval_collectBalanced, rawRowCheck11167]

def rawRow11168 : Integer.Sparse Key := [(key2302, -6), (key2303, -6), (key2310, -6), (key2305, -6), (key2193, 2), (key2194, 2), (key2200, 2), (key2091, 2), (key2092, 2), (key2302, 2), (key2341, 2), (key2310, 2), (key2347, 2), (key2095, 2), (key2305, 2), (key2343, 2)]

theorem rawRowCheck11168 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form13 = rawRow11168 := by decide +kernel

def row11168 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

theorem rowCheck11168 : row11168 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11168 := by decide +kernel

theorem rowEval11168 (x : Key → ℝ) : Integer.Sparse.eval row11168 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck11168, Integer.Sparse.eval_collectBalanced, rawRowCheck11168]

def rawRow11169 : Integer.Sparse Key := [(key2303, -6), (key2302, -6), (key2310, -6), (key2305, -6), (key2194, 2), (key2193, 2), (key2200, 2), (key2092, 2), (key2091, 2), (key2341, 2), (key2302, 2), (key2347, 2), (key2310, 2), (key2095, 2), (key2343, 2), (key2305, 2)]

theorem rawRowCheck11169 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form13 = rawRow11169 := by decide +kernel

def row11169 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

theorem rowCheck11169 : row11169 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11169 := by decide +kernel

theorem rowEval11169 (x : Key → ℝ) : Integer.Sparse.eval row11169 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck11169, Integer.Sparse.eval_collectBalanced, rawRowCheck11169]

def rawRow11170 : Integer.Sparse Key := [(key2302, -6), (key2310, -6), (key2303, -6), (key2305, -6), (key2193, 2), (key2200, 2), (key2194, 2), (key2302, 2), (key2310, 2), (key2091, 2), (key2347, 2), (key2092, 2), (key2341, 2), (key2305, 2), (key2095, 2), (key2343, 2)]

theorem rawRowCheck11170 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form13 = rawRow11170 := by decide +kernel

def row11170 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

theorem rowCheck11170 : row11170 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11170 := by decide +kernel

theorem rowEval11170 (x : Key → ℝ) : Integer.Sparse.eval row11170 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck11170, Integer.Sparse.eval_collectBalanced, rawRowCheck11170]

def rawRow11171 : Integer.Sparse Key := [(key2310, -6), (key2302, -6), (key2303, -6), (key2305, -6), (key2200, 2), (key2193, 2), (key2194, 2), (key2310, 2), (key2302, 2), (key2347, 2), (key2091, 2), (key2341, 2), (key2092, 2), (key2305, 2), (key2343, 2), (key2095, 2)]

theorem rawRowCheck11171 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form13 = rawRow11171 := by decide +kernel

def row11171 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

theorem rowCheck11171 : row11171 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11171 := by decide +kernel

theorem rowEval11171 (x : Key → ℝ) : Integer.Sparse.eval row11171 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck11171, Integer.Sparse.eval_collectBalanced, rawRowCheck11171]

def rawRow11172 : Integer.Sparse Key := [(key2303, -6), (key2310, -6), (key2302, -6), (key2305, -6), (key2194, 2), (key2200, 2), (key2193, 2), (key2341, 2), (key2347, 2), (key2092, 2), (key2310, 2), (key2091, 2), (key2302, 2), (key2343, 2), (key2095, 2), (key2305, 2)]

theorem rawRowCheck11172 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form13 = rawRow11172 := by decide +kernel

def row11172 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

theorem rowCheck11172 : row11172 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11172 := by decide +kernel

theorem rowEval11172 (x : Key → ℝ) : Integer.Sparse.eval row11172 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck11172, Integer.Sparse.eval_collectBalanced, rawRowCheck11172]

def rawRow11173 : Integer.Sparse Key := [(key2310, -6), (key2303, -6), (key2302, -6), (key2305, -6), (key2200, 2), (key2194, 2), (key2193, 2), (key2347, 2), (key2341, 2), (key2310, 2), (key2092, 2), (key2302, 2), (key2091, 2), (key2343, 2), (key2305, 2), (key2095, 2)]

theorem rawRowCheck11173 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form13 = rawRow11173 := by decide +kernel

def row11173 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

theorem rowCheck11173 : row11173 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11173 := by decide +kernel

theorem rowEval11173 (x : Key → ℝ) : Integer.Sparse.eval row11173 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck11173, Integer.Sparse.eval_collectBalanced, rawRowCheck11173]

def rawRow11174 : Integer.Sparse Key := [(key2302, -6), (key2305, -6), (key2310, -6), (key2303, -6), (key2302, 2), (key2305, 2), (key2310, 2), (key2091, 2), (key2095, 2), (key2193, 2), (key2343, 2), (key2200, 2), (key2347, 2), (key2092, 2), (key2194, 2), (key2341, 2)]

theorem rawRowCheck11174 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form13 = rawRow11174 := by decide +kernel

def row11174 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

theorem rowCheck11174 : row11174 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11174 := by decide +kernel

theorem rowEval11174 (x : Key → ℝ) : Integer.Sparse.eval row11174 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck11174, Integer.Sparse.eval_collectBalanced, rawRowCheck11174]

def rawRow11175 : Integer.Sparse Key := [(key2305, -6), (key2302, -6), (key2310, -6), (key2303, -6), (key2305, 2), (key2302, 2), (key2310, 2), (key2095, 2), (key2091, 2), (key2343, 2), (key2193, 2), (key2347, 2), (key2200, 2), (key2092, 2), (key2341, 2), (key2194, 2)]

theorem rawRowCheck11175 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form13 = rawRow11175 := by decide +kernel

def row11175 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

theorem rowCheck11175 : row11175 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11175 := by decide +kernel

theorem rowEval11175 (x : Key → ℝ) : Integer.Sparse.eval row11175 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck11175, Integer.Sparse.eval_collectBalanced, rawRowCheck11175]

def rawRow11176 : Integer.Sparse Key := [(key2302, -6), (key2310, -6), (key2305, -6), (key2303, -6), (key2302, 2), (key2310, 2), (key2305, 2), (key2193, 2), (key2200, 2), (key2091, 2), (key2347, 2), (key2095, 2), (key2343, 2), (key2194, 2), (key2092, 2), (key2341, 2)]

theorem rawRowCheck11176 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form13 = rawRow11176 := by decide +kernel

def row11176 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

theorem rowCheck11176 : row11176 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11176 := by decide +kernel

theorem rowEval11176 (x : Key → ℝ) : Integer.Sparse.eval row11176 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck11176, Integer.Sparse.eval_collectBalanced, rawRowCheck11176]

def rawRow11177 : Integer.Sparse Key := [(key2310, -6), (key2302, -6), (key2305, -6), (key2303, -6), (key2310, 2), (key2302, 2), (key2305, 2), (key2200, 2), (key2193, 2), (key2347, 2), (key2091, 2), (key2343, 2), (key2095, 2), (key2194, 2), (key2341, 2), (key2092, 2)]

theorem rawRowCheck11177 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form13 = rawRow11177 := by decide +kernel

def row11177 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

theorem rowCheck11177 : row11177 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11177 := by decide +kernel

theorem rowEval11177 (x : Key → ℝ) : Integer.Sparse.eval row11177 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck11177, Integer.Sparse.eval_collectBalanced, rawRowCheck11177]

def rawRow11178 : Integer.Sparse Key := [(key2305, -6), (key2310, -6), (key2302, -6), (key2303, -6), (key2305, 2), (key2310, 2), (key2302, 2), (key2343, 2), (key2347, 2), (key2095, 2), (key2200, 2), (key2091, 2), (key2193, 2), (key2341, 2), (key2092, 2), (key2194, 2)]

theorem rawRowCheck11178 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form13 = rawRow11178 := by decide +kernel

def row11178 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

theorem rowCheck11178 : row11178 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11178 := by decide +kernel

theorem rowEval11178 (x : Key → ℝ) : Integer.Sparse.eval row11178 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck11178, Integer.Sparse.eval_collectBalanced, rawRowCheck11178]

def rawRow11179 : Integer.Sparse Key := [(key2310, -6), (key2305, -6), (key2302, -6), (key2303, -6), (key2310, 2), (key2305, 2), (key2302, 2), (key2347, 2), (key2343, 2), (key2200, 2), (key2095, 2), (key2193, 2), (key2091, 2), (key2341, 2), (key2194, 2), (key2092, 2)]

theorem rawRowCheck11179 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form13 = rawRow11179 := by decide +kernel

def row11179 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

theorem rowCheck11179 : row11179 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11179 := by decide +kernel

theorem rowEval11179 (x : Key → ℝ) : Integer.Sparse.eval row11179 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck11179, Integer.Sparse.eval_collectBalanced, rawRowCheck11179]

def rawRow11180 : Integer.Sparse Key := [(key2303, -6), (key2305, -6), (key2310, -6), (key2302, -6), (key2341, 2), (key2343, 2), (key2347, 2), (key2092, 2), (key2095, 2), (key2194, 2), (key2305, 2), (key2200, 2), (key2310, 2), (key2091, 2), (key2193, 2), (key2302, 2)]

theorem rawRowCheck11180 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form13 = rawRow11180 := by decide +kernel

def row11180 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

theorem rowCheck11180 : row11180 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11180 := by decide +kernel

theorem rowEval11180 (x : Key → ℝ) : Integer.Sparse.eval row11180 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck11180, Integer.Sparse.eval_collectBalanced, rawRowCheck11180]

def rawRow11181 : Integer.Sparse Key := [(key2305, -6), (key2303, -6), (key2310, -6), (key2302, -6), (key2343, 2), (key2341, 2), (key2347, 2), (key2095, 2), (key2092, 2), (key2305, 2), (key2194, 2), (key2310, 2), (key2200, 2), (key2091, 2), (key2302, 2), (key2193, 2)]

theorem rawRowCheck11181 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form13 = rawRow11181 := by decide +kernel

def row11181 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

theorem rowCheck11181 : row11181 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11181 := by decide +kernel

theorem rowEval11181 (x : Key → ℝ) : Integer.Sparse.eval row11181 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck11181, Integer.Sparse.eval_collectBalanced, rawRowCheck11181]

def rawRow11182 : Integer.Sparse Key := [(key2303, -6), (key2310, -6), (key2305, -6), (key2302, -6), (key2341, 2), (key2347, 2), (key2343, 2), (key2194, 2), (key2200, 2), (key2092, 2), (key2310, 2), (key2095, 2), (key2305, 2), (key2193, 2), (key2091, 2), (key2302, 2)]

theorem rawRowCheck11182 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form13 = rawRow11182 := by decide +kernel

def row11182 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

theorem rowCheck11182 : row11182 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11182 := by decide +kernel

theorem rowEval11182 (x : Key → ℝ) : Integer.Sparse.eval row11182 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck11182, Integer.Sparse.eval_collectBalanced, rawRowCheck11182]

def rawRow11183 : Integer.Sparse Key := [(key2310, -6), (key2303, -6), (key2305, -6), (key2302, -6), (key2347, 2), (key2341, 2), (key2343, 2), (key2200, 2), (key2194, 2), (key2310, 2), (key2092, 2), (key2305, 2), (key2095, 2), (key2193, 2), (key2302, 2), (key2091, 2)]

theorem rawRowCheck11183 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form13 = rawRow11183 := by decide +kernel

def row11183 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

theorem rowCheck11183 : row11183 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11183 := by decide +kernel

theorem rowEval11183 (x : Key → ℝ) : Integer.Sparse.eval row11183 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck11183, Integer.Sparse.eval_collectBalanced, rawRowCheck11183]

def rawRow11184 : Integer.Sparse Key := [(key2305, -6), (key2310, -6), (key2303, -6), (key2302, -6), (key2343, 2), (key2347, 2), (key2341, 2), (key2305, 2), (key2310, 2), (key2095, 2), (key2200, 2), (key2092, 2), (key2194, 2), (key2302, 2), (key2091, 2), (key2193, 2)]

theorem rawRowCheck11184 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form13 = rawRow11184 := by decide +kernel

def row11184 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

theorem rowCheck11184 : row11184 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11184 := by decide +kernel

theorem rowEval11184 (x : Key → ℝ) : Integer.Sparse.eval row11184 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck11184, Integer.Sparse.eval_collectBalanced, rawRowCheck11184]

def rawRow11185 : Integer.Sparse Key := [(key2310, -6), (key2305, -6), (key2303, -6), (key2302, -6), (key2347, 2), (key2343, 2), (key2341, 2), (key2310, 2), (key2305, 2), (key2200, 2), (key2095, 2), (key2194, 2), (key2092, 2), (key2302, 2), (key2193, 2), (key2091, 2)]

theorem rawRowCheck11185 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form13 = rawRow11185 := by decide +kernel

def row11185 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

theorem rowCheck11185 : row11185 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11185 := by decide +kernel

theorem rowEval11185 (x : Key → ℝ) : Integer.Sparse.eval row11185 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck11185, Integer.Sparse.eval_collectBalanced, rawRowCheck11185]

def rawRow11186 : Integer.Sparse Key := [(key2341, -6), (key2341, -6), (key2343, -6), (key2347, -6), (key2092, 2), (key2092, 2), (key2095, 2), (key2194, 2), (key2194, 2), (key2303, 2), (key2303, 2), (key2305, 2), (key2305, 2), (key2200, 2), (key2310, 2), (key2310, 2)]

theorem rawRowCheck11186 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form13 = rawRow11186 := by decide +kernel

def row11186 : Integer.Sparse Key := [(key2092, 4), (key2095, 2), (key2194, 4), (key2200, 2), (key2303, 4), (key2305, 4), (key2310, 4), (key2341, -12), (key2343, -6), (key2347, -6)]

theorem rowCheck11186 : row11186 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11186 := by decide +kernel

theorem rowEval11186 (x : Key → ℝ) : Integer.Sparse.eval row11186 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck11186, Integer.Sparse.eval_collectBalanced, rawRowCheck11186]

def rawRow11187 : Integer.Sparse Key := [(key2341, -6), (key2343, -6), (key2341, -6), (key2347, -6), (key2092, 2), (key2095, 2), (key2092, 2), (key2303, 2), (key2305, 2), (key2194, 2), (key2305, 2), (key2194, 2), (key2303, 2), (key2310, 2), (key2200, 2), (key2310, 2)]

theorem rawRowCheck11187 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form13 = rawRow11187 := by decide +kernel

def row11187 : Integer.Sparse Key := [(key2092, 4), (key2095, 2), (key2194, 4), (key2200, 2), (key2303, 4), (key2305, 4), (key2310, 4), (key2341, -12), (key2343, -6), (key2347, -6)]

theorem rowCheck11187 : row11187 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11187 := by decide +kernel

theorem rowEval11187 (x : Key → ℝ) : Integer.Sparse.eval row11187 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck11187, Integer.Sparse.eval_collectBalanced, rawRowCheck11187]

def rawRow11188 : Integer.Sparse Key := [(key2343, -6), (key2341, -6), (key2341, -6), (key2347, -6), (key2095, 2), (key2092, 2), (key2092, 2), (key2305, 2), (key2303, 2), (key2305, 2), (key2194, 2), (key2303, 2), (key2194, 2), (key2310, 2), (key2310, 2), (key2200, 2)]

theorem rawRowCheck11188 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form13 = rawRow11188 := by decide +kernel

def row11188 : Integer.Sparse Key := [(key2092, 4), (key2095, 2), (key2194, 4), (key2200, 2), (key2303, 4), (key2305, 4), (key2310, 4), (key2341, -12), (key2343, -6), (key2347, -6)]

theorem rowCheck11188 : row11188 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11188 := by decide +kernel

theorem rowEval11188 (x : Key → ℝ) : Integer.Sparse.eval row11188 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck11188, Integer.Sparse.eval_collectBalanced, rawRowCheck11188]

def rawRow11189 : Integer.Sparse Key := [(key2341, -6), (key2341, -6), (key2347, -6), (key2343, -6), (key2194, 2), (key2194, 2), (key2200, 2), (key2092, 2), (key2092, 2), (key2303, 2), (key2303, 2), (key2310, 2), (key2310, 2), (key2095, 2), (key2305, 2), (key2305, 2)]

theorem rawRowCheck11189 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form13 = rawRow11189 := by decide +kernel

def row11189 : Integer.Sparse Key := [(key2092, 4), (key2095, 2), (key2194, 4), (key2200, 2), (key2303, 4), (key2305, 4), (key2310, 4), (key2341, -12), (key2343, -6), (key2347, -6)]

theorem rowCheck11189 : row11189 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11189 := by decide +kernel

theorem rowEval11189 (x : Key → ℝ) : Integer.Sparse.eval row11189 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck11189, Integer.Sparse.eval_collectBalanced, rawRowCheck11189]

def rawRow11190 : Integer.Sparse Key := [(key2341, -6), (key2347, -6), (key2341, -6), (key2343, -6), (key2194, 2), (key2200, 2), (key2194, 2), (key2303, 2), (key2310, 2), (key2092, 2), (key2310, 2), (key2092, 2), (key2303, 2), (key2305, 2), (key2095, 2), (key2305, 2)]

theorem rawRowCheck11190 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form13 = rawRow11190 := by decide +kernel

def row11190 : Integer.Sparse Key := [(key2092, 4), (key2095, 2), (key2194, 4), (key2200, 2), (key2303, 4), (key2305, 4), (key2310, 4), (key2341, -12), (key2343, -6), (key2347, -6)]

theorem rowCheck11190 : row11190 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11190 := by decide +kernel

theorem rowEval11190 (x : Key → ℝ) : Integer.Sparse.eval row11190 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck11190, Integer.Sparse.eval_collectBalanced, rawRowCheck11190]

def rawRow11191 : Integer.Sparse Key := [(key2347, -6), (key2341, -6), (key2341, -6), (key2343, -6), (key2200, 2), (key2194, 2), (key2194, 2), (key2310, 2), (key2303, 2), (key2310, 2), (key2092, 2), (key2303, 2), (key2092, 2), (key2305, 2), (key2305, 2), (key2095, 2)]

theorem rawRowCheck11191 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form13 = rawRow11191 := by decide +kernel

def row11191 : Integer.Sparse Key := [(key2092, 4), (key2095, 2), (key2194, 4), (key2200, 2), (key2303, 4), (key2305, 4), (key2310, 4), (key2341, -12), (key2343, -6), (key2347, -6)]

theorem rowCheck11191 : row11191 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11191 := by decide +kernel

theorem rowEval11191 (x : Key → ℝ) : Integer.Sparse.eval row11191 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck11191, Integer.Sparse.eval_collectBalanced, rawRowCheck11191]

def rawRow11192 : Integer.Sparse Key := [(key2341, -6), (key2343, -6), (key2347, -6), (key2341, -6), (key2303, 2), (key2305, 2), (key2310, 2), (key2092, 2), (key2095, 2), (key2194, 2), (key2305, 2), (key2200, 2), (key2310, 2), (key2092, 2), (key2194, 2), (key2303, 2)]

theorem rawRowCheck11192 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form13 = rawRow11192 := by decide +kernel

def row11192 : Integer.Sparse Key := [(key2092, 4), (key2095, 2), (key2194, 4), (key2200, 2), (key2303, 4), (key2305, 4), (key2310, 4), (key2341, -12), (key2343, -6), (key2347, -6)]

theorem rowCheck11192 : row11192 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11192 := by decide +kernel

theorem rowEval11192 (x : Key → ℝ) : Integer.Sparse.eval row11192 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck11192, Integer.Sparse.eval_collectBalanced, rawRowCheck11192]

def rawRow11193 : Integer.Sparse Key := [(key2343, -6), (key2341, -6), (key2347, -6), (key2341, -6), (key2305, 2), (key2303, 2), (key2310, 2), (key2095, 2), (key2092, 2), (key2305, 2), (key2194, 2), (key2310, 2), (key2200, 2), (key2092, 2), (key2303, 2), (key2194, 2)]

theorem rawRowCheck11193 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form13 = rawRow11193 := by decide +kernel

def row11193 : Integer.Sparse Key := [(key2092, 4), (key2095, 2), (key2194, 4), (key2200, 2), (key2303, 4), (key2305, 4), (key2310, 4), (key2341, -12), (key2343, -6), (key2347, -6)]

theorem rowCheck11193 : row11193 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11193 := by decide +kernel

theorem rowEval11193 (x : Key → ℝ) : Integer.Sparse.eval row11193 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck11193, Integer.Sparse.eval_collectBalanced, rawRowCheck11193]

def rawRow11194 : Integer.Sparse Key := [(key2341, -6), (key2347, -6), (key2343, -6), (key2341, -6), (key2303, 2), (key2310, 2), (key2305, 2), (key2194, 2), (key2200, 2), (key2092, 2), (key2310, 2), (key2095, 2), (key2305, 2), (key2194, 2), (key2092, 2), (key2303, 2)]

theorem rawRowCheck11194 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form13 = rawRow11194 := by decide +kernel

def row11194 : Integer.Sparse Key := [(key2092, 4), (key2095, 2), (key2194, 4), (key2200, 2), (key2303, 4), (key2305, 4), (key2310, 4), (key2341, -12), (key2343, -6), (key2347, -6)]

theorem rowCheck11194 : row11194 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11194 := by decide +kernel

theorem rowEval11194 (x : Key → ℝ) : Integer.Sparse.eval row11194 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck11194, Integer.Sparse.eval_collectBalanced, rawRowCheck11194]

def rawRow11195 : Integer.Sparse Key := [(key2347, -6), (key2341, -6), (key2343, -6), (key2341, -6), (key2310, 2), (key2303, 2), (key2305, 2), (key2200, 2), (key2194, 2), (key2310, 2), (key2092, 2), (key2305, 2), (key2095, 2), (key2194, 2), (key2303, 2), (key2092, 2)]

theorem rawRowCheck11195 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form13 = rawRow11195 := by decide +kernel

def row11195 : Integer.Sparse Key := [(key2092, 4), (key2095, 2), (key2194, 4), (key2200, 2), (key2303, 4), (key2305, 4), (key2310, 4), (key2341, -12), (key2343, -6), (key2347, -6)]

theorem rowCheck11195 : row11195 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11195 := by decide +kernel

theorem rowEval11195 (x : Key → ℝ) : Integer.Sparse.eval row11195 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck11195, Integer.Sparse.eval_collectBalanced, rawRowCheck11195]

def rawRow11196 : Integer.Sparse Key := [(key2343, -6), (key2347, -6), (key2341, -6), (key2341, -6), (key2305, 2), (key2310, 2), (key2303, 2), (key2305, 2), (key2310, 2), (key2095, 2), (key2200, 2), (key2092, 2), (key2194, 2), (key2303, 2), (key2092, 2), (key2194, 2)]

theorem rawRowCheck11196 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form13 = rawRow11196 := by decide +kernel

def row11196 : Integer.Sparse Key := [(key2092, 4), (key2095, 2), (key2194, 4), (key2200, 2), (key2303, 4), (key2305, 4), (key2310, 4), (key2341, -12), (key2343, -6), (key2347, -6)]

theorem rowCheck11196 : row11196 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11196 := by decide +kernel

theorem rowEval11196 (x : Key → ℝ) : Integer.Sparse.eval row11196 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck11196, Integer.Sparse.eval_collectBalanced, rawRowCheck11196]

def rawRow11197 : Integer.Sparse Key := [(key2347, -6), (key2343, -6), (key2341, -6), (key2341, -6), (key2310, 2), (key2305, 2), (key2303, 2), (key2310, 2), (key2305, 2), (key2200, 2), (key2095, 2), (key2194, 2), (key2092, 2), (key2303, 2), (key2194, 2), (key2092, 2)]

theorem rawRowCheck11197 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form13 = rawRow11197 := by decide +kernel

def row11197 : Integer.Sparse Key := [(key2092, 4), (key2095, 2), (key2194, 4), (key2200, 2), (key2303, 4), (key2305, 4), (key2310, 4), (key2341, -12), (key2343, -6), (key2347, -6)]

theorem rowCheck11197 : row11197 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11197 := by decide +kernel

theorem rowEval11197 (x : Key → ℝ) : Integer.Sparse.eval row11197 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck11197, Integer.Sparse.eval_collectBalanced, rawRowCheck11197]

def rawRow11198 : Integer.Sparse Key := [(key1107, 6), (key1112, 6), (key1121, 6), (key1148, 6), (key999, -6), (key1034, -6), (key1112, -6), (key1191, -6)]

theorem rawRowCheck11198 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form14 = rawRow11198 := by decide +kernel

def row11198 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

theorem rowCheck11198 : row11198 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11198 := by decide +kernel

theorem rowEval11198 (x : Key → ℝ) : Integer.Sparse.eval row11198 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11198, Integer.Sparse.eval_collectBalanced, rawRowCheck11198]

def rawRow11199 : Integer.Sparse Key := [(key1112, 6), (key1107, 6), (key1121, 6), (key1148, 6), (key999, -6), (key1034, -6), (key1191, -6), (key1112, -6)]

theorem rawRowCheck11199 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form14 = rawRow11199 := by decide +kernel

def row11199 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

theorem rowCheck11199 : row11199 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11199 := by decide +kernel

theorem rowEval11199 (x : Key → ℝ) : Integer.Sparse.eval row11199 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11199, Integer.Sparse.eval_collectBalanced, rawRowCheck11199]

def rawRow11200 : Integer.Sparse Key := [(key1107, 6), (key1121, 6), (key1112, 6), (key1148, 6), (key999, -6), (key1112, -6), (key1034, -6), (key1191, -6)]

theorem rawRowCheck11200 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form14 = rawRow11200 := by decide +kernel

def row11200 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

theorem rowCheck11200 : row11200 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11200 := by decide +kernel

theorem rowEval11200 (x : Key → ℝ) : Integer.Sparse.eval row11200 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11200, Integer.Sparse.eval_collectBalanced, rawRowCheck11200]

def rawRow11201 : Integer.Sparse Key := [(key1121, 6), (key1107, 6), (key1112, 6), (key1148, 6), (key999, -6), (key1112, -6), (key1191, -6), (key1034, -6)]

theorem rawRowCheck11201 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form14 = rawRow11201 := by decide +kernel

def row11201 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

theorem rowCheck11201 : row11201 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11201 := by decide +kernel

theorem rowEval11201 (x : Key → ℝ) : Integer.Sparse.eval row11201 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11201, Integer.Sparse.eval_collectBalanced, rawRowCheck11201]

def rawRow11202 : Integer.Sparse Key := [(key1112, 6), (key1121, 6), (key1107, 6), (key1148, 6), (key999, -6), (key1191, -6), (key1034, -6), (key1112, -6)]

theorem rawRowCheck11202 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form14 = rawRow11202 := by decide +kernel

def row11202 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

theorem rowCheck11202 : row11202 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11202 := by decide +kernel

theorem rowEval11202 (x : Key → ℝ) : Integer.Sparse.eval row11202 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11202, Integer.Sparse.eval_collectBalanced, rawRowCheck11202]

def rawRow11203 : Integer.Sparse Key := [(key1121, 6), (key1112, 6), (key1107, 6), (key1148, 6), (key999, -6), (key1191, -6), (key1112, -6), (key1034, -6)]

theorem rawRowCheck11203 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form14 = rawRow11203 := by decide +kernel

def row11203 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

theorem rowCheck11203 : row11203 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11203 := by decide +kernel

theorem rowEval11203 (x : Key → ℝ) : Integer.Sparse.eval row11203 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11203, Integer.Sparse.eval_collectBalanced, rawRowCheck11203]

def rawRow11204 : Integer.Sparse Key := [(key1107, 6), (key1112, 6), (key1148, 6), (key1121, 6), (key1034, -6), (key999, -6), (key1112, -6), (key1191, -6)]

theorem rawRowCheck11204 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form14 = rawRow11204 := by decide +kernel

def row11204 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

theorem rowCheck11204 : row11204 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11204 := by decide +kernel

theorem rowEval11204 (x : Key → ℝ) : Integer.Sparse.eval row11204 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11204, Integer.Sparse.eval_collectBalanced, rawRowCheck11204]

def rawRow11205 : Integer.Sparse Key := [(key1112, 6), (key1107, 6), (key1148, 6), (key1121, 6), (key1034, -6), (key999, -6), (key1191, -6), (key1112, -6)]

theorem rawRowCheck11205 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form14 = rawRow11205 := by decide +kernel

def row11205 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

theorem rowCheck11205 : row11205 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11205 := by decide +kernel

theorem rowEval11205 (x : Key → ℝ) : Integer.Sparse.eval row11205 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11205, Integer.Sparse.eval_collectBalanced, rawRowCheck11205]

def rawRow11206 : Integer.Sparse Key := [(key1107, 6), (key1148, 6), (key1112, 6), (key1121, 6), (key1034, -6), (key1112, -6), (key999, -6), (key1191, -6)]

theorem rawRowCheck11206 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form14 = rawRow11206 := by decide +kernel

def row11206 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

theorem rowCheck11206 : row11206 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11206 := by decide +kernel

theorem rowEval11206 (x : Key → ℝ) : Integer.Sparse.eval row11206 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11206, Integer.Sparse.eval_collectBalanced, rawRowCheck11206]

def rawRow11207 : Integer.Sparse Key := [(key1148, 6), (key1107, 6), (key1112, 6), (key1121, 6), (key1034, -6), (key1112, -6), (key1191, -6), (key999, -6)]

theorem rawRowCheck11207 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form14 = rawRow11207 := by decide +kernel

def row11207 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

theorem rowCheck11207 : row11207 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11207 := by decide +kernel

theorem rowEval11207 (x : Key → ℝ) : Integer.Sparse.eval row11207 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck11207, Integer.Sparse.eval_collectBalanced, rawRowCheck11207]

def rawRow11208 : Integer.Sparse Key := [(key1112, 6), (key1148, 6), (key1107, 6), (key1121, 6), (key1034, -6), (key1191, -6), (key999, -6), (key1112, -6)]

theorem rawRowCheck11208 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form14 = rawRow11208 := by decide +kernel

def row11208 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

theorem rowCheck11208 : row11208 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11208 := by decide +kernel

theorem rowEval11208 (x : Key → ℝ) : Integer.Sparse.eval row11208 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11208, Integer.Sparse.eval_collectBalanced, rawRowCheck11208]

def rawRow11209 : Integer.Sparse Key := [(key1148, 6), (key1112, 6), (key1107, 6), (key1121, 6), (key1034, -6), (key1191, -6), (key1112, -6), (key999, -6)]

theorem rawRowCheck11209 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form14 = rawRow11209 := by decide +kernel

def row11209 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

theorem rowCheck11209 : row11209 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11209 := by decide +kernel

theorem rowEval11209 (x : Key → ℝ) : Integer.Sparse.eval row11209 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck11209, Integer.Sparse.eval_collectBalanced, rawRowCheck11209]

def rawRow11210 : Integer.Sparse Key := [(key1107, 6), (key1121, 6), (key1148, 6), (key1112, 6), (key1112, -6), (key999, -6), (key1034, -6), (key1191, -6)]

theorem rawRowCheck11210 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form14 = rawRow11210 := by decide +kernel

def row11210 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

theorem rowCheck11210 : row11210 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11210 := by decide +kernel

theorem rowEval11210 (x : Key → ℝ) : Integer.Sparse.eval row11210 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11210, Integer.Sparse.eval_collectBalanced, rawRowCheck11210]

def rawRow11211 : Integer.Sparse Key := [(key1121, 6), (key1107, 6), (key1148, 6), (key1112, 6), (key1112, -6), (key999, -6), (key1191, -6), (key1034, -6)]

theorem rawRowCheck11211 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form14 = rawRow11211 := by decide +kernel

def row11211 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

theorem rowCheck11211 : row11211 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11211 := by decide +kernel

theorem rowEval11211 (x : Key → ℝ) : Integer.Sparse.eval row11211 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11211, Integer.Sparse.eval_collectBalanced, rawRowCheck11211]

def rawRow11212 : Integer.Sparse Key := [(key1107, 6), (key1148, 6), (key1121, 6), (key1112, 6), (key1112, -6), (key1034, -6), (key999, -6), (key1191, -6)]

theorem rawRowCheck11212 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form14 = rawRow11212 := by decide +kernel

def row11212 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

theorem rowCheck11212 : row11212 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11212 := by decide +kernel

theorem rowEval11212 (x : Key → ℝ) : Integer.Sparse.eval row11212 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11212, Integer.Sparse.eval_collectBalanced, rawRowCheck11212]

def rawRow11213 : Integer.Sparse Key := [(key1148, 6), (key1107, 6), (key1121, 6), (key1112, 6), (key1112, -6), (key1034, -6), (key1191, -6), (key999, -6)]

theorem rawRowCheck11213 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form14 = rawRow11213 := by decide +kernel

def row11213 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

theorem rowCheck11213 : row11213 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11213 := by decide +kernel

theorem rowEval11213 (x : Key → ℝ) : Integer.Sparse.eval row11213 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck11213, Integer.Sparse.eval_collectBalanced, rawRowCheck11213]

def rawRow11214 : Integer.Sparse Key := [(key1121, 6), (key1148, 6), (key1107, 6), (key1112, 6), (key1112, -6), (key1191, -6), (key999, -6), (key1034, -6)]

theorem rawRowCheck11214 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form14 = rawRow11214 := by decide +kernel

def row11214 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

theorem rowCheck11214 : row11214 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11214 := by decide +kernel

theorem rowEval11214 (x : Key → ℝ) : Integer.Sparse.eval row11214 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11214, Integer.Sparse.eval_collectBalanced, rawRowCheck11214]

def rawRow11215 : Integer.Sparse Key := [(key1148, 6), (key1121, 6), (key1107, 6), (key1112, 6), (key1112, -6), (key1191, -6), (key1034, -6), (key999, -6)]

theorem rawRowCheck11215 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form14 = rawRow11215 := by decide +kernel

def row11215 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

theorem rowCheck11215 : row11215 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11215 := by decide +kernel

theorem rowEval11215 (x : Key → ℝ) : Integer.Sparse.eval row11215 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck11215, Integer.Sparse.eval_collectBalanced, rawRowCheck11215]

def rawRow11216 : Integer.Sparse Key := [(key1112, 6), (key1121, 6), (key1148, 6), (key1107, 6), (key1191, -6), (key999, -6), (key1034, -6), (key1112, -6)]

theorem rawRowCheck11216 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form14 = rawRow11216 := by decide +kernel

def row11216 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

theorem rowCheck11216 : row11216 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11216 := by decide +kernel

theorem rowEval11216 (x : Key → ℝ) : Integer.Sparse.eval row11216 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11216, Integer.Sparse.eval_collectBalanced, rawRowCheck11216]

def rawRow11217 : Integer.Sparse Key := [(key1121, 6), (key1112, 6), (key1148, 6), (key1107, 6), (key1191, -6), (key999, -6), (key1112, -6), (key1034, -6)]

theorem rawRowCheck11217 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form14 = rawRow11217 := by decide +kernel

def row11217 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

theorem rowCheck11217 : row11217 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11217 := by decide +kernel

theorem rowEval11217 (x : Key → ℝ) : Integer.Sparse.eval row11217 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11217, Integer.Sparse.eval_collectBalanced, rawRowCheck11217]

def rawRow11218 : Integer.Sparse Key := [(key1112, 6), (key1148, 6), (key1121, 6), (key1107, 6), (key1191, -6), (key1034, -6), (key999, -6), (key1112, -6)]

theorem rawRowCheck11218 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form14 = rawRow11218 := by decide +kernel

def row11218 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

theorem rowCheck11218 : row11218 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11218 := by decide +kernel

theorem rowEval11218 (x : Key → ℝ) : Integer.Sparse.eval row11218 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11218, Integer.Sparse.eval_collectBalanced, rawRowCheck11218]

def rawRow11219 : Integer.Sparse Key := [(key1148, 6), (key1112, 6), (key1121, 6), (key1107, 6), (key1191, -6), (key1034, -6), (key1112, -6), (key999, -6)]

theorem rawRowCheck11219 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form14 = rawRow11219 := by decide +kernel

def row11219 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

theorem rowCheck11219 : row11219 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11219 := by decide +kernel

theorem rowEval11219 (x : Key → ℝ) : Integer.Sparse.eval row11219 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck11219, Integer.Sparse.eval_collectBalanced, rawRowCheck11219]

def rawRow11220 : Integer.Sparse Key := [(key1121, 6), (key1148, 6), (key1112, 6), (key1107, 6), (key1191, -6), (key1112, -6), (key999, -6), (key1034, -6)]

theorem rawRowCheck11220 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form14 = rawRow11220 := by decide +kernel

def row11220 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

theorem rowCheck11220 : row11220 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11220 := by decide +kernel

theorem rowEval11220 (x : Key → ℝ) : Integer.Sparse.eval row11220 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11220, Integer.Sparse.eval_collectBalanced, rawRowCheck11220]

def rawRow11221 : Integer.Sparse Key := [(key1148, 6), (key1121, 6), (key1112, 6), (key1107, 6), (key1191, -6), (key1112, -6), (key1034, -6), (key999, -6)]

theorem rawRowCheck11221 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form14 = rawRow11221 := by decide +kernel

def row11221 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

theorem rowCheck11221 : row11221 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11221 := by decide +kernel

theorem rowEval11221 (x : Key → ℝ) : Integer.Sparse.eval row11221 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck11221, Integer.Sparse.eval_collectBalanced, rawRowCheck11221]

def rawRow11222 : Integer.Sparse Key := [(key1191, 6), (key1191, 6), (key1197, 6), (key1210, 6), (key994, -6), (key1029, -6), (key1107, -6), (key1107, -6)]

theorem rawRowCheck11222 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form14 = rawRow11222 := by decide +kernel

def row11222 : Integer.Sparse Key := [(key994, -6), (key1029, -6), (key1107, -12), (key1191, 12), (key1197, 6), (key1210, 6)]

theorem rowCheck11222 : row11222 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11222 := by decide +kernel

theorem rowEval11222 (x : Key → ℝ) : Integer.Sparse.eval row11222 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11222, Integer.Sparse.eval_collectBalanced, rawRowCheck11222]

def rawRow11223 : Integer.Sparse Key := [(key1191, 6), (key1197, 6), (key1191, 6), (key1210, 6), (key994, -6), (key1107, -6), (key1029, -6), (key1107, -6)]

theorem rawRowCheck11223 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form14 = rawRow11223 := by decide +kernel

def row11223 : Integer.Sparse Key := [(key994, -6), (key1029, -6), (key1107, -12), (key1191, 12), (key1197, 6), (key1210, 6)]

theorem rowCheck11223 : row11223 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11223 := by decide +kernel

theorem rowEval11223 (x : Key → ℝ) : Integer.Sparse.eval row11223 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11223, Integer.Sparse.eval_collectBalanced, rawRowCheck11223]

def rawRow11224 : Integer.Sparse Key := [(key1197, 6), (key1191, 6), (key1191, 6), (key1210, 6), (key994, -6), (key1107, -6), (key1107, -6), (key1029, -6)]

theorem rawRowCheck11224 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form14 = rawRow11224 := by decide +kernel

def row11224 : Integer.Sparse Key := [(key994, -6), (key1029, -6), (key1107, -12), (key1191, 12), (key1197, 6), (key1210, 6)]

theorem rowCheck11224 : row11224 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11224 := by decide +kernel

theorem rowEval11224 (x : Key → ℝ) : Integer.Sparse.eval row11224 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11224, Integer.Sparse.eval_collectBalanced, rawRowCheck11224]

def rawRow11225 : Integer.Sparse Key := [(key1191, 6), (key1191, 6), (key1210, 6), (key1197, 6), (key1029, -6), (key994, -6), (key1107, -6), (key1107, -6)]

theorem rawRowCheck11225 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form14 = rawRow11225 := by decide +kernel

def row11225 : Integer.Sparse Key := [(key994, -6), (key1029, -6), (key1107, -12), (key1191, 12), (key1197, 6), (key1210, 6)]

theorem rowCheck11225 : row11225 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11225 := by decide +kernel

theorem rowEval11225 (x : Key → ℝ) : Integer.Sparse.eval row11225 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11225, Integer.Sparse.eval_collectBalanced, rawRowCheck11225]

def rawRow11226 : Integer.Sparse Key := [(key1191, 6), (key1210, 6), (key1191, 6), (key1197, 6), (key1029, -6), (key1107, -6), (key994, -6), (key1107, -6)]

theorem rawRowCheck11226 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form14 = rawRow11226 := by decide +kernel

def row11226 : Integer.Sparse Key := [(key994, -6), (key1029, -6), (key1107, -12), (key1191, 12), (key1197, 6), (key1210, 6)]

theorem rowCheck11226 : row11226 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11226 := by decide +kernel

theorem rowEval11226 (x : Key → ℝ) : Integer.Sparse.eval row11226 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11226, Integer.Sparse.eval_collectBalanced, rawRowCheck11226]

def rawRow11227 : Integer.Sparse Key := [(key1210, 6), (key1191, 6), (key1191, 6), (key1197, 6), (key1029, -6), (key1107, -6), (key1107, -6), (key994, -6)]

theorem rawRowCheck11227 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form14 = rawRow11227 := by decide +kernel

def row11227 : Integer.Sparse Key := [(key994, -6), (key1029, -6), (key1107, -12), (key1191, 12), (key1197, 6), (key1210, 6)]

theorem rowCheck11227 : row11227 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11227 := by decide +kernel

theorem rowEval11227 (x : Key → ℝ) : Integer.Sparse.eval row11227 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck11227, Integer.Sparse.eval_collectBalanced, rawRowCheck11227]

def rawRow11228 : Integer.Sparse Key := [(key1191, 6), (key1197, 6), (key1210, 6), (key1191, 6), (key1107, -6), (key994, -6), (key1029, -6), (key1107, -6)]

theorem rawRowCheck11228 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form14 = rawRow11228 := by decide +kernel

def row11228 : Integer.Sparse Key := [(key994, -6), (key1029, -6), (key1107, -12), (key1191, 12), (key1197, 6), (key1210, 6)]

theorem rowCheck11228 : row11228 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11228 := by decide +kernel

theorem rowEval11228 (x : Key → ℝ) : Integer.Sparse.eval row11228 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11228, Integer.Sparse.eval_collectBalanced, rawRowCheck11228]

def rawRow11229 : Integer.Sparse Key := [(key1197, 6), (key1191, 6), (key1210, 6), (key1191, 6), (key1107, -6), (key994, -6), (key1107, -6), (key1029, -6)]

theorem rawRowCheck11229 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form14 = rawRow11229 := by decide +kernel

def row11229 : Integer.Sparse Key := [(key994, -6), (key1029, -6), (key1107, -12), (key1191, 12), (key1197, 6), (key1210, 6)]

theorem rowCheck11229 : row11229 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11229 := by decide +kernel

theorem rowEval11229 (x : Key → ℝ) : Integer.Sparse.eval row11229 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11229, Integer.Sparse.eval_collectBalanced, rawRowCheck11229]

def rawRow11230 : Integer.Sparse Key := [(key1191, 6), (key1210, 6), (key1197, 6), (key1191, 6), (key1107, -6), (key1029, -6), (key994, -6), (key1107, -6)]

theorem rawRowCheck11230 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form14 = rawRow11230 := by decide +kernel

def row11230 : Integer.Sparse Key := [(key994, -6), (key1029, -6), (key1107, -12), (key1191, 12), (key1197, 6), (key1210, 6)]

theorem rowCheck11230 : row11230 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11230 := by decide +kernel

theorem rowEval11230 (x : Key → ℝ) : Integer.Sparse.eval row11230 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11230, Integer.Sparse.eval_collectBalanced, rawRowCheck11230]

def rawRow11231 : Integer.Sparse Key := [(key1210, 6), (key1191, 6), (key1197, 6), (key1191, 6), (key1107, -6), (key1029, -6), (key1107, -6), (key994, -6)]

theorem rawRowCheck11231 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form14 = rawRow11231 := by decide +kernel

def row11231 : Integer.Sparse Key := [(key994, -6), (key1029, -6), (key1107, -12), (key1191, 12), (key1197, 6), (key1210, 6)]

theorem rowCheck11231 : row11231 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11231 := by decide +kernel

theorem rowEval11231 (x : Key → ℝ) : Integer.Sparse.eval row11231 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck11231, Integer.Sparse.eval_collectBalanced, rawRowCheck11231]

def rawRow11232 : Integer.Sparse Key := [(key1197, 6), (key1210, 6), (key1191, 6), (key1191, 6), (key1107, -6), (key1107, -6), (key994, -6), (key1029, -6)]

theorem rawRowCheck11232 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form14 = rawRow11232 := by decide +kernel

def row11232 : Integer.Sparse Key := [(key994, -6), (key1029, -6), (key1107, -12), (key1191, 12), (key1197, 6), (key1210, 6)]

theorem rowCheck11232 : row11232 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11232 := by decide +kernel

theorem rowEval11232 (x : Key → ℝ) : Integer.Sparse.eval row11232 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11232, Integer.Sparse.eval_collectBalanced, rawRowCheck11232]

def rawRow11233 : Integer.Sparse Key := [(key1210, 6), (key1197, 6), (key1191, 6), (key1191, 6), (key1107, -6), (key1107, -6), (key1029, -6), (key994, -6)]

theorem rawRowCheck11233 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form14 = rawRow11233 := by decide +kernel

def row11233 : Integer.Sparse Key := [(key994, -6), (key1029, -6), (key1107, -12), (key1191, 12), (key1197, 6), (key1210, 6)]

theorem rowCheck11233 : row11233 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11233 := by decide +kernel

theorem rowEval11233 (x : Key → ℝ) : Integer.Sparse.eval row11233 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck11233, Integer.Sparse.eval_collectBalanced, rawRowCheck11233]

def rawRow11234 : Integer.Sparse Key := [(key2464, -6), (key2467, -6), (key2476, -6), (key2499, -6), (key2370, 2), (key2373, 2), (key2386, 2), (key2762, 2), (key2765, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2928, 2), (key2965, 2), (key2987, 2)]

theorem rawRowCheck11234 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form15 = rawRow11234 := by decide +kernel

def row11234 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2464, -6), (key2467, -6), (key2476, -6), (key2499, -6), (key2762, 2), (key2765, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2928, 2), (key2965, 2), (key2987, 2)]

theorem rowCheck11234 : row11234 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11234 := by decide +kernel

theorem rowEval11234 (x : Key → ℝ) : Integer.Sparse.eval row11234 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck11234, Integer.Sparse.eval_collectBalanced, rawRowCheck11234]

def rawRow11235 : Integer.Sparse Key := [(key2467, -6), (key2464, -6), (key2476, -6), (key2499, -6), (key2373, 2), (key2370, 2), (key2386, 2), (key2765, 2), (key2762, 2), (key2874, 2), (key2839, 2), (key2908, 2), (key2886, 2), (key2928, 2), (key2987, 2), (key2965, 2)]

theorem rawRowCheck11235 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form15 = rawRow11235 := by decide +kernel

def row11235 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2464, -6), (key2467, -6), (key2476, -6), (key2499, -6), (key2762, 2), (key2765, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2928, 2), (key2965, 2), (key2987, 2)]

theorem rowCheck11235 : row11235 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11235 := by decide +kernel

theorem rowEval11235 (x : Key → ℝ) : Integer.Sparse.eval row11235 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck11235, Integer.Sparse.eval_collectBalanced, rawRowCheck11235]

def rawRow11236 : Integer.Sparse Key := [(key2464, -6), (key2476, -6), (key2467, -6), (key2499, -6), (key2370, 2), (key2386, 2), (key2373, 2), (key2839, 2), (key2886, 2), (key2762, 2), (key2908, 2), (key2765, 2), (key2874, 2), (key2965, 2), (key2928, 2), (key2987, 2)]

theorem rawRowCheck11236 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form15 = rawRow11236 := by decide +kernel

def row11236 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2464, -6), (key2467, -6), (key2476, -6), (key2499, -6), (key2762, 2), (key2765, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2928, 2), (key2965, 2), (key2987, 2)]

theorem rowCheck11236 : row11236 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11236 := by decide +kernel

theorem rowEval11236 (x : Key → ℝ) : Integer.Sparse.eval row11236 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck11236, Integer.Sparse.eval_collectBalanced, rawRowCheck11236]

def rawRow11237 : Integer.Sparse Key := [(key2476, -6), (key2464, -6), (key2467, -6), (key2499, -6), (key2386, 2), (key2370, 2), (key2373, 2), (key2886, 2), (key2839, 2), (key2908, 2), (key2762, 2), (key2874, 2), (key2765, 2), (key2965, 2), (key2987, 2), (key2928, 2)]

theorem rawRowCheck11237 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form15 = rawRow11237 := by decide +kernel

def row11237 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2464, -6), (key2467, -6), (key2476, -6), (key2499, -6), (key2762, 2), (key2765, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2928, 2), (key2965, 2), (key2987, 2)]

theorem rowCheck11237 : row11237 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11237 := by decide +kernel

theorem rowEval11237 (x : Key → ℝ) : Integer.Sparse.eval row11237 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck11237, Integer.Sparse.eval_collectBalanced, rawRowCheck11237]

def rawRow11238 : Integer.Sparse Key := [(key2467, -6), (key2476, -6), (key2464, -6), (key2499, -6), (key2373, 2), (key2386, 2), (key2370, 2), (key2874, 2), (key2908, 2), (key2765, 2), (key2886, 2), (key2762, 2), (key2839, 2), (key2987, 2), (key2928, 2), (key2965, 2)]

theorem rawRowCheck11238 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form15 = rawRow11238 := by decide +kernel

def row11238 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2464, -6), (key2467, -6), (key2476, -6), (key2499, -6), (key2762, 2), (key2765, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2928, 2), (key2965, 2), (key2987, 2)]

theorem rowCheck11238 : row11238 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11238 := by decide +kernel

theorem rowEval11238 (x : Key → ℝ) : Integer.Sparse.eval row11238 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck11238, Integer.Sparse.eval_collectBalanced, rawRowCheck11238]

def rawRow11239 : Integer.Sparse Key := [(key2476, -6), (key2467, -6), (key2464, -6), (key2499, -6), (key2386, 2), (key2373, 2), (key2370, 2), (key2908, 2), (key2874, 2), (key2886, 2), (key2765, 2), (key2839, 2), (key2762, 2), (key2987, 2), (key2965, 2), (key2928, 2)]

theorem rawRowCheck11239 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form15 = rawRow11239 := by decide +kernel

def row11239 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2464, -6), (key2467, -6), (key2476, -6), (key2499, -6), (key2762, 2), (key2765, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2928, 2), (key2965, 2), (key2987, 2)]

theorem rowCheck11239 : row11239 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11239 := by decide +kernel

theorem rowEval11239 (x : Key → ℝ) : Integer.Sparse.eval row11239 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck11239, Integer.Sparse.eval_collectBalanced, rawRowCheck11239]

def rawRow11240 : Integer.Sparse Key := [(key2464, -6), (key2467, -6), (key2499, -6), (key2476, -6), (key2398, 2), (key2401, 2), (key2433, 2), (key2583, 2), (key2586, 2), (key2839, 2), (key2874, 2), (key2965, 2), (key2987, 2), (key2597, 2), (key2886, 2), (key2908, 2)]

theorem rawRowCheck11240 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form15 = rawRow11240 := by decide +kernel

def row11240 : Integer.Sparse Key := [(key2398, 2), (key2401, 2), (key2433, 2), (key2464, -6), (key2467, -6), (key2476, -6), (key2499, -6), (key2583, 2), (key2586, 2), (key2597, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2965, 2), (key2987, 2)]

theorem rowCheck11240 : row11240 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11240 := by decide +kernel

theorem rowEval11240 (x : Key → ℝ) : Integer.Sparse.eval row11240 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck11240, Integer.Sparse.eval_collectBalanced, rawRowCheck11240]

def rawRow11241 : Integer.Sparse Key := [(key2467, -6), (key2464, -6), (key2499, -6), (key2476, -6), (key2401, 2), (key2398, 2), (key2433, 2), (key2586, 2), (key2583, 2), (key2874, 2), (key2839, 2), (key2987, 2), (key2965, 2), (key2597, 2), (key2908, 2), (key2886, 2)]

theorem rawRowCheck11241 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form15 = rawRow11241 := by decide +kernel

def row11241 : Integer.Sparse Key := [(key2398, 2), (key2401, 2), (key2433, 2), (key2464, -6), (key2467, -6), (key2476, -6), (key2499, -6), (key2583, 2), (key2586, 2), (key2597, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2965, 2), (key2987, 2)]

theorem rowCheck11241 : row11241 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11241 := by decide +kernel

theorem rowEval11241 (x : Key → ℝ) : Integer.Sparse.eval row11241 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck11241, Integer.Sparse.eval_collectBalanced, rawRowCheck11241]

def rawRow11242 : Integer.Sparse Key := [(key2464, -6), (key2499, -6), (key2467, -6), (key2476, -6), (key2398, 2), (key2433, 2), (key2401, 2), (key2839, 2), (key2965, 2), (key2583, 2), (key2987, 2), (key2586, 2), (key2874, 2), (key2886, 2), (key2597, 2), (key2908, 2)]

theorem rawRowCheck11242 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form15 = rawRow11242 := by decide +kernel

def row11242 : Integer.Sparse Key := [(key2398, 2), (key2401, 2), (key2433, 2), (key2464, -6), (key2467, -6), (key2476, -6), (key2499, -6), (key2583, 2), (key2586, 2), (key2597, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2965, 2), (key2987, 2)]

theorem rowCheck11242 : row11242 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11242 := by decide +kernel

theorem rowEval11242 (x : Key → ℝ) : Integer.Sparse.eval row11242 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck11242, Integer.Sparse.eval_collectBalanced, rawRowCheck11242]

def rawRow11243 : Integer.Sparse Key := [(key2499, -6), (key2464, -6), (key2467, -6), (key2476, -6), (key2433, 2), (key2398, 2), (key2401, 2), (key2965, 2), (key2839, 2), (key2987, 2), (key2583, 2), (key2874, 2), (key2586, 2), (key2886, 2), (key2908, 2), (key2597, 2)]

theorem rawRowCheck11243 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form15 = rawRow11243 := by decide +kernel

def row11243 : Integer.Sparse Key := [(key2398, 2), (key2401, 2), (key2433, 2), (key2464, -6), (key2467, -6), (key2476, -6), (key2499, -6), (key2583, 2), (key2586, 2), (key2597, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2965, 2), (key2987, 2)]

theorem rowCheck11243 : row11243 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11243 := by decide +kernel

theorem rowEval11243 (x : Key → ℝ) : Integer.Sparse.eval row11243 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck11243, Integer.Sparse.eval_collectBalanced, rawRowCheck11243]

def rawRow11244 : Integer.Sparse Key := [(key2467, -6), (key2499, -6), (key2464, -6), (key2476, -6), (key2401, 2), (key2433, 2), (key2398, 2), (key2874, 2), (key2987, 2), (key2586, 2), (key2965, 2), (key2583, 2), (key2839, 2), (key2908, 2), (key2597, 2), (key2886, 2)]

theorem rawRowCheck11244 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form15 = rawRow11244 := by decide +kernel

def row11244 : Integer.Sparse Key := [(key2398, 2), (key2401, 2), (key2433, 2), (key2464, -6), (key2467, -6), (key2476, -6), (key2499, -6), (key2583, 2), (key2586, 2), (key2597, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2965, 2), (key2987, 2)]

theorem rowCheck11244 : row11244 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11244 := by decide +kernel

theorem rowEval11244 (x : Key → ℝ) : Integer.Sparse.eval row11244 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck11244, Integer.Sparse.eval_collectBalanced, rawRowCheck11244]

def rawRow11245 : Integer.Sparse Key := [(key2499, -6), (key2467, -6), (key2464, -6), (key2476, -6), (key2433, 2), (key2401, 2), (key2398, 2), (key2987, 2), (key2874, 2), (key2965, 2), (key2586, 2), (key2839, 2), (key2583, 2), (key2908, 2), (key2886, 2), (key2597, 2)]

theorem rawRowCheck11245 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form15 = rawRow11245 := by decide +kernel

def row11245 : Integer.Sparse Key := [(key2398, 2), (key2401, 2), (key2433, 2), (key2464, -6), (key2467, -6), (key2476, -6), (key2499, -6), (key2583, 2), (key2586, 2), (key2597, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2965, 2), (key2987, 2)]

theorem rowCheck11245 : row11245 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11245 := by decide +kernel

theorem rowEval11245 (x : Key → ℝ) : Integer.Sparse.eval row11245 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck11245, Integer.Sparse.eval_collectBalanced, rawRowCheck11245]

def rawRow11246 : Integer.Sparse Key := [(key2464, -6), (key2476, -6), (key2499, -6), (key2467, -6), (key2464, 2), (key2476, 2), (key2499, 2), (key2370, 2), (key2386, 2), (key2762, 2), (key2908, 2), (key2928, 2), (key2987, 2), (key2586, 2), (key2765, 2), (key2874, 2)]

theorem rawRowCheck11246 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form15 = rawRow11246 := by decide +kernel

def row11246 : Integer.Sparse Key := [(key2370, 2), (key2386, 2), (key2464, -4), (key2467, -6), (key2476, -4), (key2499, -4), (key2586, 2), (key2762, 2), (key2765, 2), (key2874, 2), (key2908, 2), (key2928, 2), (key2987, 2)]

theorem rowCheck11246 : row11246 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11246 := by decide +kernel

theorem rowEval11246 (x : Key → ℝ) : Integer.Sparse.eval row11246 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck11246, Integer.Sparse.eval_collectBalanced, rawRowCheck11246]

def rawRow11247 : Integer.Sparse Key := [(key2476, -6), (key2464, -6), (key2499, -6), (key2467, -6), (key2476, 2), (key2464, 2), (key2499, 2), (key2386, 2), (key2370, 2), (key2908, 2), (key2762, 2), (key2987, 2), (key2928, 2), (key2586, 2), (key2874, 2), (key2765, 2)]

theorem rawRowCheck11247 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form15 = rawRow11247 := by decide +kernel

def row11247 : Integer.Sparse Key := [(key2370, 2), (key2386, 2), (key2464, -4), (key2467, -6), (key2476, -4), (key2499, -4), (key2586, 2), (key2762, 2), (key2765, 2), (key2874, 2), (key2908, 2), (key2928, 2), (key2987, 2)]

theorem rowCheck11247 : row11247 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11247 := by decide +kernel

theorem rowEval11247 (x : Key → ℝ) : Integer.Sparse.eval row11247 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck11247, Integer.Sparse.eval_collectBalanced, rawRowCheck11247]

def rawRow11248 : Integer.Sparse Key := [(key2464, -6), (key2499, -6), (key2476, -6), (key2467, -6), (key2464, 2), (key2499, 2), (key2476, 2), (key2398, 2), (key2433, 2), (key2583, 2), (key2987, 2), (key2597, 2), (key2908, 2), (key2765, 2), (key2586, 2), (key2874, 2)]

theorem rawRowCheck11248 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form15 = rawRow11248 := by decide +kernel

def row11248 : Integer.Sparse Key := [(key2398, 2), (key2433, 2), (key2464, -4), (key2467, -6), (key2476, -4), (key2499, -4), (key2583, 2), (key2586, 2), (key2597, 2), (key2765, 2), (key2874, 2), (key2908, 2), (key2987, 2)]

theorem rowCheck11248 : row11248 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11248 := by decide +kernel

theorem rowEval11248 (x : Key → ℝ) : Integer.Sparse.eval row11248 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck11248, Integer.Sparse.eval_collectBalanced, rawRowCheck11248]

def rawRow11249 : Integer.Sparse Key := [(key2499, -6), (key2464, -6), (key2476, -6), (key2467, -6), (key2499, 2), (key2464, 2), (key2476, 2), (key2433, 2), (key2398, 2), (key2987, 2), (key2583, 2), (key2908, 2), (key2597, 2), (key2765, 2), (key2874, 2), (key2586, 2)]

theorem rawRowCheck11249 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form15 = rawRow11249 := by decide +kernel

def row11249 : Integer.Sparse Key := [(key2398, 2), (key2433, 2), (key2464, -4), (key2467, -6), (key2476, -4), (key2499, -4), (key2583, 2), (key2586, 2), (key2597, 2), (key2765, 2), (key2874, 2), (key2908, 2), (key2987, 2)]

theorem rowCheck11249 : row11249 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11249 := by decide +kernel

theorem rowEval11249 (x : Key → ℝ) : Integer.Sparse.eval row11249 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck11249, Integer.Sparse.eval_collectBalanced, rawRowCheck11249]

def rawRow11250 : Integer.Sparse Key := [(key2476, -6), (key2499, -6), (key2464, -6), (key2467, -6), (key2476, 2), (key2499, 2), (key2464, 2), (key2540, 2), (key2551, 2), (key2386, 2), (key2433, 2), (key2370, 2), (key2762, 2), (key2874, 2), (key2586, 2), (key2765, 2)]

theorem rawRowCheck11250 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form15 = rawRow11250 := by decide +kernel

def row11250 : Integer.Sparse Key := [(key2370, 2), (key2386, 2), (key2433, 2), (key2464, -4), (key2467, -6), (key2476, -4), (key2499, -4), (key2540, 2), (key2551, 2), (key2586, 2), (key2762, 2), (key2765, 2), (key2874, 2)]

theorem rowCheck11250 : row11250 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11250 := by decide +kernel

theorem rowEval11250 (x : Key → ℝ) : Integer.Sparse.eval row11250 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck11250, Integer.Sparse.eval_collectBalanced, rawRowCheck11250]

def rawRow11251 : Integer.Sparse Key := [(key2499, -6), (key2476, -6), (key2464, -6), (key2467, -6), (key2499, 2), (key2476, 2), (key2464, 2), (key2551, 2), (key2540, 2), (key2433, 2), (key2386, 2), (key2398, 2), (key2583, 2), (key2874, 2), (key2765, 2), (key2586, 2)]

theorem rawRowCheck11251 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form15 = rawRow11251 := by decide +kernel

def row11251 : Integer.Sparse Key := [(key2386, 2), (key2398, 2), (key2433, 2), (key2464, -4), (key2467, -6), (key2476, -4), (key2499, -4), (key2540, 2), (key2551, 2), (key2583, 2), (key2586, 2), (key2765, 2), (key2874, 2)]

theorem rowCheck11251 : row11251 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11251 := by decide +kernel

theorem rowEval11251 (x : Key → ℝ) : Integer.Sparse.eval row11251 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck11251, Integer.Sparse.eval_collectBalanced, rawRowCheck11251]

def rawRow11252 : Integer.Sparse Key := [(key2467, -6), (key2476, -6), (key2499, -6), (key2464, -6), (key2534, 2), (key2540, 2), (key2551, 2), (key2373, 2), (key2386, 2), (key2401, 2), (key2476, 2), (key2433, 2), (key2499, 2), (key2370, 2), (key2762, 2), (key2839, 2)]

theorem rawRowCheck11252 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form15 = rawRow11252 := by decide +kernel

def row11252 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2401, 2), (key2433, 2), (key2464, -6), (key2467, -6), (key2476, -4), (key2499, -4), (key2534, 2), (key2540, 2), (key2551, 2), (key2762, 2), (key2839, 2)]

theorem rowCheck11252 : row11252 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11252 := by decide +kernel

theorem rowEval11252 (x : Key → ℝ) : Integer.Sparse.eval row11252 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck11252, Integer.Sparse.eval_collectBalanced, rawRowCheck11252]

def rawRow11253 : Integer.Sparse Key := [(key2476, -6), (key2467, -6), (key2499, -6), (key2464, -6), (key2540, 2), (key2534, 2), (key2551, 2), (key2386, 2), (key2373, 2), (key2476, 2), (key2401, 2), (key2499, 2), (key2433, 2), (key2370, 2), (key2839, 2), (key2762, 2)]

theorem rawRowCheck11253 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form15 = rawRow11253 := by decide +kernel

def row11253 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2401, 2), (key2433, 2), (key2464, -6), (key2467, -6), (key2476, -4), (key2499, -4), (key2534, 2), (key2540, 2), (key2551, 2), (key2762, 2), (key2839, 2)]

theorem rowCheck11253 : row11253 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11253 := by decide +kernel

theorem rowEval11253 (x : Key → ℝ) : Integer.Sparse.eval row11253 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck11253, Integer.Sparse.eval_collectBalanced, rawRowCheck11253]

def rawRow11254 : Integer.Sparse Key := [(key2467, -6), (key2499, -6), (key2476, -6), (key2464, -6), (key2534, 2), (key2551, 2), (key2540, 2), (key2401, 2), (key2433, 2), (key2373, 2), (key2499, 2), (key2386, 2), (key2476, 2), (key2398, 2), (key2583, 2), (key2839, 2)]

theorem rawRowCheck11254 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form15 = rawRow11254 := by decide +kernel

def row11254 : Integer.Sparse Key := [(key2373, 2), (key2386, 2), (key2398, 2), (key2401, 2), (key2433, 2), (key2464, -6), (key2467, -6), (key2476, -4), (key2499, -4), (key2534, 2), (key2540, 2), (key2551, 2), (key2583, 2), (key2839, 2)]

theorem rowCheck11254 : row11254 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11254 := by decide +kernel

theorem rowEval11254 (x : Key → ℝ) : Integer.Sparse.eval row11254 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck11254, Integer.Sparse.eval_collectBalanced, rawRowCheck11254]

def rawRow11255 : Integer.Sparse Key := [(key2499, -6), (key2467, -6), (key2476, -6), (key2464, -6), (key2551, 2), (key2534, 2), (key2540, 2), (key2433, 2), (key2401, 2), (key2499, 2), (key2373, 2), (key2476, 2), (key2386, 2), (key2398, 2), (key2839, 2), (key2583, 2)]

theorem rawRowCheck11255 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form15 = rawRow11255 := by decide +kernel

def row11255 : Integer.Sparse Key := [(key2373, 2), (key2386, 2), (key2398, 2), (key2401, 2), (key2433, 2), (key2464, -6), (key2467, -6), (key2476, -4), (key2499, -4), (key2534, 2), (key2540, 2), (key2551, 2), (key2583, 2), (key2839, 2)]

theorem rowCheck11255 : row11255 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11255 := by decide +kernel

theorem rowEval11255 (x : Key → ℝ) : Integer.Sparse.eval row11255 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck11255, Integer.Sparse.eval_collectBalanced, rawRowCheck11255]

def rawRow11256 : Integer.Sparse Key := [(key2476, -6), (key2499, -6), (key2467, -6), (key2464, -6), (key2540, 2), (key2551, 2), (key2534, 2), (key2476, 2), (key2499, 2), (key2386, 2), (key2433, 2), (key2373, 2), (key2401, 2), (key2464, 2), (key2370, 2), (key2762, 2)]

theorem rawRowCheck11256 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form15 = rawRow11256 := by decide +kernel

def row11256 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2401, 2), (key2433, 2), (key2464, -4), (key2467, -6), (key2476, -4), (key2499, -4), (key2534, 2), (key2540, 2), (key2551, 2), (key2762, 2)]

theorem rowCheck11256 : row11256 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11256 := by decide +kernel

theorem rowEval11256 (x : Key → ℝ) : Integer.Sparse.eval row11256 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck11256, Integer.Sparse.eval_collectBalanced, rawRowCheck11256]

def rawRow11257 : Integer.Sparse Key := [(key2499, -6), (key2476, -6), (key2467, -6), (key2464, -6), (key2551, 2), (key2540, 2), (key2534, 2), (key2499, 2), (key2476, 2), (key2433, 2), (key2386, 2), (key2401, 2), (key2373, 2), (key2464, 2), (key2398, 2), (key2583, 2)]

theorem rawRowCheck11257 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form15 = rawRow11257 := by decide +kernel

def row11257 : Integer.Sparse Key := [(key2373, 2), (key2386, 2), (key2398, 2), (key2401, 2), (key2433, 2), (key2464, -4), (key2467, -6), (key2476, -4), (key2499, -4), (key2534, 2), (key2540, 2), (key2551, 2), (key2583, 2)]

theorem rowCheck11257 : row11257 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11257 := by decide +kernel

theorem rowEval11257 (x : Key → ℝ) : Integer.Sparse.eval row11257 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck11257, Integer.Sparse.eval_collectBalanced, rawRowCheck11257]

def rawRow11258 : Integer.Sparse Key := [(key2534, -6), (key2534, -6), (key2540, -6), (key2551, -6), (key2373, 2), (key2373, 2), (key2386, 2), (key2401, 2), (key2401, 2), (key2467, 2), (key2467, 2), (key2476, 2), (key2476, 2), (key2433, 2), (key2499, 2), (key2499, 2)]

theorem rawRowCheck11258 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form15 = rawRow11258 := by decide +kernel

def row11258 : Integer.Sparse Key := [(key2373, 4), (key2386, 2), (key2401, 4), (key2433, 2), (key2467, 4), (key2476, 4), (key2499, 4), (key2534, -12), (key2540, -6), (key2551, -6)]

theorem rowCheck11258 : row11258 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11258 := by decide +kernel

theorem rowEval11258 (x : Key → ℝ) : Integer.Sparse.eval row11258 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck11258, Integer.Sparse.eval_collectBalanced, rawRowCheck11258]

def rawRow11259 : Integer.Sparse Key := [(key2534, -6), (key2540, -6), (key2534, -6), (key2551, -6), (key2373, 2), (key2386, 2), (key2373, 2), (key2467, 2), (key2476, 2), (key2401, 2), (key2476, 2), (key2401, 2), (key2467, 2), (key2499, 2), (key2433, 2), (key2499, 2)]

theorem rawRowCheck11259 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form15 = rawRow11259 := by decide +kernel

def row11259 : Integer.Sparse Key := [(key2373, 4), (key2386, 2), (key2401, 4), (key2433, 2), (key2467, 4), (key2476, 4), (key2499, 4), (key2534, -12), (key2540, -6), (key2551, -6)]

theorem rowCheck11259 : row11259 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11259 := by decide +kernel

theorem rowEval11259 (x : Key → ℝ) : Integer.Sparse.eval row11259 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck11259, Integer.Sparse.eval_collectBalanced, rawRowCheck11259]

def rawRow11260 : Integer.Sparse Key := [(key2540, -6), (key2534, -6), (key2534, -6), (key2551, -6), (key2386, 2), (key2373, 2), (key2373, 2), (key2476, 2), (key2467, 2), (key2476, 2), (key2401, 2), (key2467, 2), (key2401, 2), (key2499, 2), (key2499, 2), (key2433, 2)]

theorem rawRowCheck11260 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form15 = rawRow11260 := by decide +kernel

def row11260 : Integer.Sparse Key := [(key2373, 4), (key2386, 2), (key2401, 4), (key2433, 2), (key2467, 4), (key2476, 4), (key2499, 4), (key2534, -12), (key2540, -6), (key2551, -6)]

theorem rowCheck11260 : row11260 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11260 := by decide +kernel

theorem rowEval11260 (x : Key → ℝ) : Integer.Sparse.eval row11260 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck11260, Integer.Sparse.eval_collectBalanced, rawRowCheck11260]

def rawRow11261 : Integer.Sparse Key := [(key2534, -6), (key2534, -6), (key2551, -6), (key2540, -6), (key2401, 2), (key2401, 2), (key2433, 2), (key2373, 2), (key2373, 2), (key2467, 2), (key2467, 2), (key2499, 2), (key2499, 2), (key2386, 2), (key2476, 2), (key2476, 2)]

theorem rawRowCheck11261 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form15 = rawRow11261 := by decide +kernel

def row11261 : Integer.Sparse Key := [(key2373, 4), (key2386, 2), (key2401, 4), (key2433, 2), (key2467, 4), (key2476, 4), (key2499, 4), (key2534, -12), (key2540, -6), (key2551, -6)]

theorem rowCheck11261 : row11261 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11261 := by decide +kernel

theorem rowEval11261 (x : Key → ℝ) : Integer.Sparse.eval row11261 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck11261, Integer.Sparse.eval_collectBalanced, rawRowCheck11261]

def rawRow11262 : Integer.Sparse Key := [(key2534, -6), (key2551, -6), (key2534, -6), (key2540, -6), (key2401, 2), (key2433, 2), (key2401, 2), (key2467, 2), (key2499, 2), (key2373, 2), (key2499, 2), (key2373, 2), (key2467, 2), (key2476, 2), (key2386, 2), (key2476, 2)]

theorem rawRowCheck11262 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form15 = rawRow11262 := by decide +kernel

def row11262 : Integer.Sparse Key := [(key2373, 4), (key2386, 2), (key2401, 4), (key2433, 2), (key2467, 4), (key2476, 4), (key2499, 4), (key2534, -12), (key2540, -6), (key2551, -6)]

theorem rowCheck11262 : row11262 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11262 := by decide +kernel

theorem rowEval11262 (x : Key → ℝ) : Integer.Sparse.eval row11262 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck11262, Integer.Sparse.eval_collectBalanced, rawRowCheck11262]

def rawRow11263 : Integer.Sparse Key := [(key2551, -6), (key2534, -6), (key2534, -6), (key2540, -6), (key2433, 2), (key2401, 2), (key2401, 2), (key2499, 2), (key2467, 2), (key2499, 2), (key2373, 2), (key2467, 2), (key2373, 2), (key2476, 2), (key2476, 2), (key2386, 2)]

theorem rawRowCheck11263 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form15 = rawRow11263 := by decide +kernel

def row11263 : Integer.Sparse Key := [(key2373, 4), (key2386, 2), (key2401, 4), (key2433, 2), (key2467, 4), (key2476, 4), (key2499, 4), (key2534, -12), (key2540, -6), (key2551, -6)]

theorem rowCheck11263 : row11263 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11263 := by decide +kernel

theorem rowEval11263 (x : Key → ℝ) : Integer.Sparse.eval row11263 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck11263, Integer.Sparse.eval_collectBalanced, rawRowCheck11263]

end MUB6.Certificate.GramRows

end OAI
