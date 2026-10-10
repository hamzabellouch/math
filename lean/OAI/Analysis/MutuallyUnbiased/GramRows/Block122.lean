import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow12544 : Integer.Sparse Key := [(key1856, 2), (key1856, 2), (key1703, 2), (key1887, 2), (key1887, 2), (key1280, 2), (key1890, 2), (key1757, 2), (key1890, 2), (key1284, 2), (key1757, 2), (key1284, 2), (key1858, -2), (key1707, -2), (key1707, -2), (key1890, -2), (key1757, -2), (key1890, -2), (key1284, -2), (key1757, -2), (key1284, -2), (key1760, -2), (key1760, -2), (key1286, -2)]

theorem rawRowCheck12544 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form0 = rawRow12544 := by decide +kernel

def row12544 : Integer.Sparse Key := [(key1280, 2), (key1286, -2), (key1703, 2), (key1707, -4), (key1760, -4), (key1856, 4), (key1858, -2), (key1887, 4)]

theorem rowCheck12544 : row12544 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12544 := by decide +kernel

theorem rowEval12544 (x : Key → ℝ) : Integer.Sparse.eval row12544 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck12544, Integer.Sparse.eval_collectBalanced, rawRowCheck12544]

def rawRow12545 : Integer.Sparse Key := [(key1757, 2), (key1887, 2), (key1890, 2), (key1284, 2), (key1856, 2), (key1890, 2), (key1280, 2), (key1284, 2), (key1703, 2), (key1757, 2), (key1856, 2), (key1887, 2), (key1757, -2), (key1760, -2), (key1890, -2), (key1284, -2), (key1286, -2), (key1707, -2), (key1760, -2), (key1858, -2), (key1890, -2), (key1284, -2), (key1707, -2), (key1757, -2)]

theorem rawRowCheck12545 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form0 = rawRow12545 := by decide +kernel

def row12545 : Integer.Sparse Key := [(key1280, 2), (key1286, -2), (key1703, 2), (key1707, -4), (key1760, -4), (key1856, 4), (key1858, -2), (key1887, 4)]

theorem rowCheck12545 : row12545 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12545 := by decide +kernel

theorem rowEval12545 (x : Key → ℝ) : Integer.Sparse.eval row12545 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck12545, Integer.Sparse.eval_collectBalanced, rawRowCheck12545]

def rawRow12546 : Integer.Sparse Key := [(key1757, 2), (key1890, 2), (key1887, 2), (key1284, 2), (key1890, 2), (key1856, 2), (key1284, 2), (key1280, 2), (key1757, 2), (key1703, 2), (key1887, 2), (key1856, 2), (key1760, -2), (key1757, -2), (key1890, -2), (key1286, -2), (key1284, -2), (key1760, -2), (key1707, -2), (key1890, -2), (key1858, -2), (key1284, -2), (key1757, -2), (key1707, -2)]

theorem rawRowCheck12546 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form0 = rawRow12546 := by decide +kernel

def row12546 : Integer.Sparse Key := [(key1280, 2), (key1286, -2), (key1703, 2), (key1707, -4), (key1760, -4), (key1856, 4), (key1858, -2), (key1887, 4)]

theorem rowCheck12546 : row12546 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12546 := by decide +kernel

theorem rowEval12546 (x : Key → ℝ) : Integer.Sparse.eval row12546 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck12546, Integer.Sparse.eval_collectBalanced, rawRowCheck12546]

def rawRow12547 : Integer.Sparse Key := [(key1887, 2), (key1757, 2), (key1890, 2), (key1856, 2), (key1284, 2), (key1890, 2), (key1703, 2), (key1856, 2), (key1280, 2), (key1887, 2), (key1284, 2), (key1757, 2), (key1757, -2), (key1890, -2), (key1760, -2), (key1707, -2), (key1858, -2), (key1284, -2), (key1890, -2), (key1286, -2), (key1760, -2), (key1707, -2), (key1284, -2), (key1757, -2)]

theorem rawRowCheck12547 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form0 = rawRow12547 := by decide +kernel

def row12547 : Integer.Sparse Key := [(key1280, 2), (key1286, -2), (key1703, 2), (key1707, -4), (key1760, -4), (key1856, 4), (key1858, -2), (key1887, 4)]

theorem rowCheck12547 : row12547 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12547 := by decide +kernel

theorem rowEval12547 (x : Key → ℝ) : Integer.Sparse.eval row12547 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck12547, Integer.Sparse.eval_collectBalanced, rawRowCheck12547]

def rawRow12548 : Integer.Sparse Key := [(key1887, 2), (key1890, 2), (key1757, 2), (key1856, 2), (key1890, 2), (key1284, 2), (key1856, 2), (key1703, 2), (key1887, 2), (key1280, 2), (key1757, 2), (key1284, 2), (key1890, -2), (key1757, -2), (key1760, -2), (key1858, -2), (key1707, -2), (key1890, -2), (key1284, -2), (key1760, -2), (key1286, -2), (key1707, -2), (key1757, -2), (key1284, -2)]

theorem rawRowCheck12548 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form0 = rawRow12548 := by decide +kernel

def row12548 : Integer.Sparse Key := [(key1280, 2), (key1286, -2), (key1703, 2), (key1707, -4), (key1760, -4), (key1856, 4), (key1858, -2), (key1887, 4)]

theorem rowCheck12548 : row12548 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12548 := by decide +kernel

theorem rowEval12548 (x : Key → ℝ) : Integer.Sparse.eval row12548 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck12548, Integer.Sparse.eval_collectBalanced, rawRowCheck12548]

def rawRow12549 : Integer.Sparse Key := [(key1890, 2), (key1757, 2), (key1887, 2), (key1890, 2), (key1284, 2), (key1856, 2), (key1757, 2), (key1887, 2), (key1284, 2), (key1856, 2), (key1280, 2), (key1703, 2), (key1760, -2), (key1890, -2), (key1757, -2), (key1760, -2), (key1890, -2), (key1286, -2), (key1858, -2), (key1284, -2), (key1707, -2), (key1757, -2), (key1284, -2), (key1707, -2)]

theorem rawRowCheck12549 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form0 = rawRow12549 := by decide +kernel

def row12549 : Integer.Sparse Key := [(key1280, 2), (key1286, -2), (key1703, 2), (key1707, -4), (key1760, -4), (key1856, 4), (key1858, -2), (key1887, 4)]

theorem rowCheck12549 : row12549 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12549 := by decide +kernel

theorem rowEval12549 (x : Key → ℝ) : Integer.Sparse.eval row12549 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck12549, Integer.Sparse.eval_collectBalanced, rawRowCheck12549]

def rawRow12550 : Integer.Sparse Key := [(key1890, 2), (key1887, 2), (key1757, 2), (key1890, 2), (key1856, 2), (key1284, 2), (key1887, 2), (key1757, 2), (key1856, 2), (key1284, 2), (key1703, 2), (key1280, 2), (key1890, -2), (key1760, -2), (key1757, -2), (key1890, -2), (key1760, -2), (key1858, -2), (key1286, -2), (key1707, -2), (key1284, -2), (key1757, -2), (key1707, -2), (key1284, -2)]

theorem rawRowCheck12550 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form0 = rawRow12550 := by decide +kernel

def row12550 : Integer.Sparse Key := [(key1280, 2), (key1286, -2), (key1703, 2), (key1707, -4), (key1760, -4), (key1856, 4), (key1858, -2), (key1887, 4)]

theorem rowCheck12550 : row12550 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12550 := by decide +kernel

theorem rowEval12550 (x : Key → ℝ) : Integer.Sparse.eval row12550 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck12550, Integer.Sparse.eval_collectBalanced, rawRowCheck12550]

def rawRow12551 : Integer.Sparse Key := [(key1284, 2), (key1284, 2), (key1286, 2), (key1707, 2), (key1707, 2), (key1760, 2), (key1856, 2), (key1858, 2), (key1856, 2), (key1890, 2), (key1858, 2), (key1890, 2), (key1280, -2), (key1284, -2), (key1284, -2), (key1703, -2), (key1707, -2), (key1703, -2), (key1757, -2), (key1707, -2), (key1757, -2), (key1856, -2), (key1856, -2), (key1887, -2)]

theorem rawRowCheck12551 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form0 = rawRow12551 := by decide +kernel

def row12551 : Integer.Sparse Key := [(key1280, -2), (key1286, 2), (key1703, -4), (key1757, -4), (key1760, 2), (key1858, 4), (key1887, -2), (key1890, 4)]

theorem rowCheck12551 : row12551 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12551 := by decide +kernel

theorem rowEval12551 (x : Key → ℝ) : Integer.Sparse.eval row12551 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck12551, Integer.Sparse.eval_collectBalanced, rawRowCheck12551]

def rawRow12552 : Integer.Sparse Key := [(key1284, 2), (key1286, 2), (key1284, 2), (key1707, 2), (key1760, 2), (key1707, 2), (key1858, 2), (key1856, 2), (key1890, 2), (key1856, 2), (key1890, 2), (key1858, 2), (key1284, -2), (key1280, -2), (key1284, -2), (key1707, -2), (key1703, -2), (key1757, -2), (key1703, -2), (key1757, -2), (key1707, -2), (key1856, -2), (key1887, -2), (key1856, -2)]

theorem rawRowCheck12552 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form0 = rawRow12552 := by decide +kernel

def row12552 : Integer.Sparse Key := [(key1280, -2), (key1286, 2), (key1703, -4), (key1757, -4), (key1760, 2), (key1858, 4), (key1887, -2), (key1890, 4)]

theorem rowCheck12552 : row12552 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12552 := by decide +kernel

theorem rowEval12552 (x : Key → ℝ) : Integer.Sparse.eval row12552 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck12552, Integer.Sparse.eval_collectBalanced, rawRowCheck12552]

def rawRow12553 : Integer.Sparse Key := [(key1286, 2), (key1284, 2), (key1284, 2), (key1760, 2), (key1707, 2), (key1707, 2), (key1890, 2), (key1890, 2), (key1858, 2), (key1858, 2), (key1856, 2), (key1856, 2), (key1284, -2), (key1284, -2), (key1280, -2), (key1757, -2), (key1757, -2), (key1707, -2), (key1707, -2), (key1703, -2), (key1703, -2), (key1887, -2), (key1856, -2), (key1856, -2)]

theorem rawRowCheck12553 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form0 = rawRow12553 := by decide +kernel

def row12553 : Integer.Sparse Key := [(key1280, -2), (key1286, 2), (key1703, -4), (key1757, -4), (key1760, 2), (key1858, 4), (key1887, -2), (key1890, 4)]

theorem rowCheck12553 : row12553 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12553 := by decide +kernel

theorem rowEval12553 (x : Key → ℝ) : Integer.Sparse.eval row12553 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck12553, Integer.Sparse.eval_collectBalanced, rawRowCheck12553]

def rawRow12554 : Integer.Sparse Key := [(key1707, 2), (key1856, 2), (key1858, 2), (key1284, 2), (key1856, 2), (key1890, 2), (key1284, 2), (key1286, 2), (key1707, 2), (key1760, 2), (key1858, 2), (key1890, 2), (key1703, -2), (key1707, -2), (key1856, -2), (key1280, -2), (key1284, -2), (key1703, -2), (key1757, -2), (key1856, -2), (key1887, -2), (key1284, -2), (key1707, -2), (key1757, -2)]

theorem rawRowCheck12554 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form0 = rawRow12554 := by decide +kernel

def row12554 : Integer.Sparse Key := [(key1280, -2), (key1286, 2), (key1703, -4), (key1757, -4), (key1760, 2), (key1858, 4), (key1887, -2), (key1890, 4)]

theorem rowCheck12554 : row12554 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12554 := by decide +kernel

theorem rowEval12554 (x : Key → ℝ) : Integer.Sparse.eval row12554 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck12554, Integer.Sparse.eval_collectBalanced, rawRowCheck12554]

def rawRow12555 : Integer.Sparse Key := [(key1707, 2), (key1858, 2), (key1856, 2), (key1284, 2), (key1890, 2), (key1856, 2), (key1286, 2), (key1284, 2), (key1760, 2), (key1707, 2), (key1890, 2), (key1858, 2), (key1707, -2), (key1703, -2), (key1856, -2), (key1284, -2), (key1280, -2), (key1757, -2), (key1703, -2), (key1887, -2), (key1856, -2), (key1284, -2), (key1757, -2), (key1707, -2)]

theorem rawRowCheck12555 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form0 = rawRow12555 := by decide +kernel

def row12555 : Integer.Sparse Key := [(key1280, -2), (key1286, 2), (key1703, -4), (key1757, -4), (key1760, 2), (key1858, 4), (key1887, -2), (key1890, 4)]

theorem rowCheck12555 : row12555 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12555 := by decide +kernel

theorem rowEval12555 (x : Key → ℝ) : Integer.Sparse.eval row12555 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck12555, Integer.Sparse.eval_collectBalanced, rawRowCheck12555]

def rawRow12556 : Integer.Sparse Key := [(key1856, 2), (key1707, 2), (key1858, 2), (key1856, 2), (key1284, 2), (key1890, 2), (key1707, 2), (key1858, 2), (key1284, 2), (key1890, 2), (key1286, 2), (key1760, 2), (key1703, -2), (key1856, -2), (key1707, -2), (key1703, -2), (key1856, -2), (key1280, -2), (key1887, -2), (key1284, -2), (key1757, -2), (key1707, -2), (key1284, -2), (key1757, -2)]

theorem rawRowCheck12556 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form0 = rawRow12556 := by decide +kernel

def row12556 : Integer.Sparse Key := [(key1280, -2), (key1286, 2), (key1703, -4), (key1757, -4), (key1760, 2), (key1858, 4), (key1887, -2), (key1890, 4)]

theorem rowCheck12556 : row12556 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12556 := by decide +kernel

theorem rowEval12556 (x : Key → ℝ) : Integer.Sparse.eval row12556 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck12556, Integer.Sparse.eval_collectBalanced, rawRowCheck12556]

def rawRow12557 : Integer.Sparse Key := [(key1856, 2), (key1858, 2), (key1707, 2), (key1856, 2), (key1890, 2), (key1284, 2), (key1858, 2), (key1707, 2), (key1890, 2), (key1284, 2), (key1760, 2), (key1286, 2), (key1856, -2), (key1703, -2), (key1707, -2), (key1856, -2), (key1703, -2), (key1887, -2), (key1280, -2), (key1757, -2), (key1284, -2), (key1707, -2), (key1757, -2), (key1284, -2)]

theorem rawRowCheck12557 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form0 = rawRow12557 := by decide +kernel

def row12557 : Integer.Sparse Key := [(key1280, -2), (key1286, 2), (key1703, -4), (key1757, -4), (key1760, 2), (key1858, 4), (key1887, -2), (key1890, 4)]

theorem rowCheck12557 : row12557 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12557 := by decide +kernel

theorem rowEval12557 (x : Key → ℝ) : Integer.Sparse.eval row12557 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck12557, Integer.Sparse.eval_collectBalanced, rawRowCheck12557]

def rawRow12558 : Integer.Sparse Key := [(key1858, 2), (key1707, 2), (key1856, 2), (key1890, 2), (key1284, 2), (key1856, 2), (key1760, 2), (key1890, 2), (key1286, 2), (key1858, 2), (key1284, 2), (key1707, 2), (key1707, -2), (key1856, -2), (key1703, -2), (key1757, -2), (key1887, -2), (key1284, -2), (key1856, -2), (key1280, -2), (key1703, -2), (key1757, -2), (key1284, -2), (key1707, -2)]

theorem rawRowCheck12558 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form0 = rawRow12558 := by decide +kernel

def row12558 : Integer.Sparse Key := [(key1280, -2), (key1286, 2), (key1703, -4), (key1757, -4), (key1760, 2), (key1858, 4), (key1887, -2), (key1890, 4)]

theorem rowCheck12558 : row12558 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12558 := by decide +kernel

theorem rowEval12558 (x : Key → ℝ) : Integer.Sparse.eval row12558 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck12558, Integer.Sparse.eval_collectBalanced, rawRowCheck12558]

def rawRow12559 : Integer.Sparse Key := [(key1858, 2), (key1856, 2), (key1707, 2), (key1890, 2), (key1856, 2), (key1284, 2), (key1890, 2), (key1760, 2), (key1858, 2), (key1286, 2), (key1707, 2), (key1284, 2), (key1856, -2), (key1707, -2), (key1703, -2), (key1887, -2), (key1757, -2), (key1856, -2), (key1284, -2), (key1703, -2), (key1280, -2), (key1757, -2), (key1707, -2), (key1284, -2)]

theorem rawRowCheck12559 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form0 = rawRow12559 := by decide +kernel

def row12559 : Integer.Sparse Key := [(key1280, -2), (key1286, 2), (key1703, -4), (key1757, -4), (key1760, 2), (key1858, 4), (key1887, -2), (key1890, 4)]

theorem rowCheck12559 : row12559 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12559 := by decide +kernel

theorem rowEval12559 (x : Key → ℝ) : Integer.Sparse.eval row12559 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck12559, Integer.Sparse.eval_collectBalanced, rawRowCheck12559]

def rawRow12560 : Integer.Sparse Key := [(key1760, 2), (key1890, 2), (key1890, 2), (key1286, 2), (key1858, 2), (key1858, 2), (key1284, 2), (key1284, 2), (key1707, 2), (key1707, 2), (key1856, 2), (key1856, 2), (key1757, -2), (key1757, -2), (key1887, -2), (key1284, -2), (key1284, -2), (key1707, -2), (key1707, -2), (key1856, -2), (key1856, -2), (key1280, -2), (key1703, -2), (key1703, -2)]

theorem rawRowCheck12560 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form0 = rawRow12560 := by decide +kernel

def row12560 : Integer.Sparse Key := [(key1280, -2), (key1286, 2), (key1703, -4), (key1757, -4), (key1760, 2), (key1858, 4), (key1887, -2), (key1890, 4)]

theorem rowCheck12560 : row12560 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12560 := by decide +kernel

theorem rowEval12560 (x : Key → ℝ) : Integer.Sparse.eval row12560 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck12560, Integer.Sparse.eval_collectBalanced, rawRowCheck12560]

def rawRow12561 : Integer.Sparse Key := [(key1890, 2), (key1760, 2), (key1890, 2), (key1858, 2), (key1286, 2), (key1858, 2), (key1707, 2), (key1856, 2), (key1284, 2), (key1856, 2), (key1284, 2), (key1707, 2), (key1757, -2), (key1887, -2), (key1757, -2), (key1707, -2), (key1856, -2), (key1284, -2), (key1856, -2), (key1284, -2), (key1707, -2), (key1703, -2), (key1280, -2), (key1703, -2)]

theorem rawRowCheck12561 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form0 = rawRow12561 := by decide +kernel

def row12561 : Integer.Sparse Key := [(key1280, -2), (key1286, 2), (key1703, -4), (key1757, -4), (key1760, 2), (key1858, 4), (key1887, -2), (key1890, 4)]

theorem rowCheck12561 : row12561 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12561 := by decide +kernel

theorem rowEval12561 (x : Key → ℝ) : Integer.Sparse.eval row12561 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck12561, Integer.Sparse.eval_collectBalanced, rawRowCheck12561]

def rawRow12562 : Integer.Sparse Key := [(key1890, 2), (key1890, 2), (key1760, 2), (key1858, 2), (key1858, 2), (key1286, 2), (key1856, 2), (key1707, 2), (key1856, 2), (key1284, 2), (key1707, 2), (key1284, 2), (key1887, -2), (key1757, -2), (key1757, -2), (key1856, -2), (key1707, -2), (key1856, -2), (key1284, -2), (key1707, -2), (key1284, -2), (key1703, -2), (key1703, -2), (key1280, -2)]

theorem rawRowCheck12562 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form0 = rawRow12562 := by decide +kernel

def row12562 : Integer.Sparse Key := [(key1280, -2), (key1286, 2), (key1703, -4), (key1757, -4), (key1760, 2), (key1858, 4), (key1887, -2), (key1890, 4)]

theorem rowCheck12562 : row12562 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12562 := by decide +kernel

theorem rowEval12562 (x : Key → ℝ) : Integer.Sparse.eval row12562 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck12562, Integer.Sparse.eval_collectBalanced, rawRowCheck12562]

def rawRow12563 : Integer.Sparse Key := [(key501, -24), (key229, 6), (key501, 6), (key557, 6), (key557, 6)]

theorem rawRowCheck12563 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form1 = rawRow12563 := by decide +kernel

def row12563 : Integer.Sparse Key := [(key229, 6), (key501, -18), (key557, 12)]

theorem rowCheck12563 : row12563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12563 := by decide +kernel

theorem rowEval12563 (x : Key → ℝ) : Integer.Sparse.eval row12563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12563, Integer.Sparse.eval_collectBalanced, rawRowCheck12563]

def rawRow12564 : Integer.Sparse Key := [(key501, -24), (key229, 6), (key557, 6), (key501, 6), (key557, 6)]

theorem rawRowCheck12564 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form1 = rawRow12564 := by decide +kernel

def row12564 : Integer.Sparse Key := [(key229, 6), (key501, -18), (key557, 12)]

theorem rowCheck12564 : row12564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12564 := by decide +kernel

theorem rowEval12564 (x : Key → ℝ) : Integer.Sparse.eval row12564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12564, Integer.Sparse.eval_collectBalanced, rawRowCheck12564]

def rawRow12565 : Integer.Sparse Key := [(key501, -24), (key229, 6), (key557, 6), (key557, 6), (key501, 6)]

theorem rawRowCheck12565 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form1 = rawRow12565 := by decide +kernel

def row12565 : Integer.Sparse Key := [(key229, 6), (key501, -18), (key557, 12)]

theorem rowCheck12565 : row12565 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12565 := by decide +kernel

theorem rowEval12565 (x : Key → ℝ) : Integer.Sparse.eval row12565 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12565, Integer.Sparse.eval_collectBalanced, rawRowCheck12565]

def rawRow12566 : Integer.Sparse Key := [(key501, -24), (key501, 6), (key229, 6), (key557, 6), (key557, 6)]

theorem rawRowCheck12566 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form1 = rawRow12566 := by decide +kernel

def row12566 : Integer.Sparse Key := [(key229, 6), (key501, -18), (key557, 12)]

theorem rowCheck12566 : row12566 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12566 := by decide +kernel

theorem rowEval12566 (x : Key → ℝ) : Integer.Sparse.eval row12566 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12566, Integer.Sparse.eval_collectBalanced, rawRowCheck12566]

def rawRow12567 : Integer.Sparse Key := [(key501, -24), (key501, 6), (key557, 6), (key229, 6), (key557, 6)]

theorem rawRowCheck12567 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form1 = rawRow12567 := by decide +kernel

def row12567 : Integer.Sparse Key := [(key229, 6), (key501, -18), (key557, 12)]

theorem rowCheck12567 : row12567 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12567 := by decide +kernel

theorem rowEval12567 (x : Key → ℝ) : Integer.Sparse.eval row12567 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12567, Integer.Sparse.eval_collectBalanced, rawRowCheck12567]

def rawRow12568 : Integer.Sparse Key := [(key501, -24), (key501, 6), (key557, 6), (key557, 6), (key229, 6)]

theorem rawRowCheck12568 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form1 = rawRow12568 := by decide +kernel

def row12568 : Integer.Sparse Key := [(key229, 6), (key501, -18), (key557, 12)]

theorem rowCheck12568 : row12568 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12568 := by decide +kernel

theorem rowEval12568 (x : Key → ℝ) : Integer.Sparse.eval row12568 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck12568, Integer.Sparse.eval_collectBalanced, rawRowCheck12568]

def rawRow12569 : Integer.Sparse Key := [(key501, -24), (key557, 6), (key229, 6), (key501, 6), (key557, 6)]

theorem rawRowCheck12569 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form1 = rawRow12569 := by decide +kernel

def row12569 : Integer.Sparse Key := [(key229, 6), (key501, -18), (key557, 12)]

theorem rowCheck12569 : row12569 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12569 := by decide +kernel

theorem rowEval12569 (x : Key → ℝ) : Integer.Sparse.eval row12569 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12569, Integer.Sparse.eval_collectBalanced, rawRowCheck12569]

def rawRow12570 : Integer.Sparse Key := [(key501, -24), (key557, 6), (key229, 6), (key557, 6), (key501, 6)]

theorem rawRowCheck12570 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form1 = rawRow12570 := by decide +kernel

def row12570 : Integer.Sparse Key := [(key229, 6), (key501, -18), (key557, 12)]

theorem rowCheck12570 : row12570 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12570 := by decide +kernel

theorem rowEval12570 (x : Key → ℝ) : Integer.Sparse.eval row12570 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12570, Integer.Sparse.eval_collectBalanced, rawRowCheck12570]

def rawRow12571 : Integer.Sparse Key := [(key501, -24), (key557, 6), (key501, 6), (key229, 6), (key557, 6)]

theorem rawRowCheck12571 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form1 = rawRow12571 := by decide +kernel

def row12571 : Integer.Sparse Key := [(key229, 6), (key501, -18), (key557, 12)]

theorem rowCheck12571 : row12571 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12571 := by decide +kernel

theorem rowEval12571 (x : Key → ℝ) : Integer.Sparse.eval row12571 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12571, Integer.Sparse.eval_collectBalanced, rawRowCheck12571]

def rawRow12572 : Integer.Sparse Key := [(key501, -24), (key557, 6), (key501, 6), (key557, 6), (key229, 6)]

theorem rawRowCheck12572 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form1 = rawRow12572 := by decide +kernel

def row12572 : Integer.Sparse Key := [(key229, 6), (key501, -18), (key557, 12)]

theorem rowCheck12572 : row12572 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12572 := by decide +kernel

theorem rowEval12572 (x : Key → ℝ) : Integer.Sparse.eval row12572 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck12572, Integer.Sparse.eval_collectBalanced, rawRowCheck12572]

def rawRow12573 : Integer.Sparse Key := [(key501, -24), (key557, 6), (key557, 6), (key229, 6), (key501, 6)]

theorem rawRowCheck12573 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form1 = rawRow12573 := by decide +kernel

def row12573 : Integer.Sparse Key := [(key229, 6), (key501, -18), (key557, 12)]

theorem rowCheck12573 : row12573 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12573 := by decide +kernel

theorem rowEval12573 (x : Key → ℝ) : Integer.Sparse.eval row12573 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12573, Integer.Sparse.eval_collectBalanced, rawRowCheck12573]

def rawRow12574 : Integer.Sparse Key := [(key501, -24), (key557, 6), (key557, 6), (key501, 6), (key229, 6)]

theorem rawRowCheck12574 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form1 = rawRow12574 := by decide +kernel

def row12574 : Integer.Sparse Key := [(key229, 6), (key501, -18), (key557, 12)]

theorem rowCheck12574 : row12574 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12574 := by decide +kernel

theorem rowEval12574 (x : Key → ℝ) : Integer.Sparse.eval row12574 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck12574, Integer.Sparse.eval_collectBalanced, rawRowCheck12574]

def rawRow12575 : Integer.Sparse Key := [(key557, -24), (key229, 6), (key501, 6), (key501, 6), (key557, 6)]

theorem rawRowCheck12575 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form1 = rawRow12575 := by decide +kernel

def row12575 : Integer.Sparse Key := [(key229, 6), (key501, 12), (key557, -18)]

theorem rowCheck12575 : row12575 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12575 := by decide +kernel

theorem rowEval12575 (x : Key → ℝ) : Integer.Sparse.eval row12575 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12575, Integer.Sparse.eval_collectBalanced, rawRowCheck12575]

def rawRow12576 : Integer.Sparse Key := [(key557, -24), (key229, 6), (key501, 6), (key557, 6), (key501, 6)]

theorem rawRowCheck12576 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form1 = rawRow12576 := by decide +kernel

def row12576 : Integer.Sparse Key := [(key229, 6), (key501, 12), (key557, -18)]

theorem rowCheck12576 : row12576 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12576 := by decide +kernel

theorem rowEval12576 (x : Key → ℝ) : Integer.Sparse.eval row12576 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12576, Integer.Sparse.eval_collectBalanced, rawRowCheck12576]

def rawRow12577 : Integer.Sparse Key := [(key557, -24), (key229, 6), (key557, 6), (key501, 6), (key501, 6)]

theorem rawRowCheck12577 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form1 = rawRow12577 := by decide +kernel

def row12577 : Integer.Sparse Key := [(key229, 6), (key501, 12), (key557, -18)]

theorem rowCheck12577 : row12577 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12577 := by decide +kernel

theorem rowEval12577 (x : Key → ℝ) : Integer.Sparse.eval row12577 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12577, Integer.Sparse.eval_collectBalanced, rawRowCheck12577]

def rawRow12578 : Integer.Sparse Key := [(key557, -24), (key501, 6), (key229, 6), (key501, 6), (key557, 6)]

theorem rawRowCheck12578 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form1 = rawRow12578 := by decide +kernel

def row12578 : Integer.Sparse Key := [(key229, 6), (key501, 12), (key557, -18)]

theorem rowCheck12578 : row12578 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12578 := by decide +kernel

theorem rowEval12578 (x : Key → ℝ) : Integer.Sparse.eval row12578 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12578, Integer.Sparse.eval_collectBalanced, rawRowCheck12578]

def rawRow12579 : Integer.Sparse Key := [(key557, -24), (key501, 6), (key229, 6), (key557, 6), (key501, 6)]

theorem rawRowCheck12579 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form1 = rawRow12579 := by decide +kernel

def row12579 : Integer.Sparse Key := [(key229, 6), (key501, 12), (key557, -18)]

theorem rowCheck12579 : row12579 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12579 := by decide +kernel

theorem rowEval12579 (x : Key → ℝ) : Integer.Sparse.eval row12579 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12579, Integer.Sparse.eval_collectBalanced, rawRowCheck12579]

def rawRow12580 : Integer.Sparse Key := [(key557, -24), (key501, 6), (key501, 6), (key229, 6), (key557, 6)]

theorem rawRowCheck12580 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form1 = rawRow12580 := by decide +kernel

def row12580 : Integer.Sparse Key := [(key229, 6), (key501, 12), (key557, -18)]

theorem rowCheck12580 : row12580 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12580 := by decide +kernel

theorem rowEval12580 (x : Key → ℝ) : Integer.Sparse.eval row12580 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12580, Integer.Sparse.eval_collectBalanced, rawRowCheck12580]

def rawRow12581 : Integer.Sparse Key := [(key557, -24), (key501, 6), (key501, 6), (key557, 6), (key229, 6)]

theorem rawRowCheck12581 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form1 = rawRow12581 := by decide +kernel

def row12581 : Integer.Sparse Key := [(key229, 6), (key501, 12), (key557, -18)]

theorem rowCheck12581 : row12581 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12581 := by decide +kernel

theorem rowEval12581 (x : Key → ℝ) : Integer.Sparse.eval row12581 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck12581, Integer.Sparse.eval_collectBalanced, rawRowCheck12581]

def rawRow12582 : Integer.Sparse Key := [(key557, -24), (key501, 6), (key557, 6), (key229, 6), (key501, 6)]

theorem rawRowCheck12582 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form1 = rawRow12582 := by decide +kernel

def row12582 : Integer.Sparse Key := [(key229, 6), (key501, 12), (key557, -18)]

theorem rowCheck12582 : row12582 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12582 := by decide +kernel

theorem rowEval12582 (x : Key → ℝ) : Integer.Sparse.eval row12582 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12582, Integer.Sparse.eval_collectBalanced, rawRowCheck12582]

def rawRow12583 : Integer.Sparse Key := [(key557, -24), (key501, 6), (key557, 6), (key501, 6), (key229, 6)]

theorem rawRowCheck12583 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form1 = rawRow12583 := by decide +kernel

def row12583 : Integer.Sparse Key := [(key229, 6), (key501, 12), (key557, -18)]

theorem rowCheck12583 : row12583 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12583 := by decide +kernel

theorem rowEval12583 (x : Key → ℝ) : Integer.Sparse.eval row12583 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck12583, Integer.Sparse.eval_collectBalanced, rawRowCheck12583]

def rawRow12584 : Integer.Sparse Key := [(key557, -24), (key557, 6), (key229, 6), (key501, 6), (key501, 6)]

theorem rawRowCheck12584 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form1 = rawRow12584 := by decide +kernel

def row12584 : Integer.Sparse Key := [(key229, 6), (key501, 12), (key557, -18)]

theorem rowCheck12584 : row12584 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12584 := by decide +kernel

theorem rowEval12584 (x : Key → ℝ) : Integer.Sparse.eval row12584 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12584, Integer.Sparse.eval_collectBalanced, rawRowCheck12584]

def rawRow12585 : Integer.Sparse Key := [(key557, -24), (key557, 6), (key501, 6), (key229, 6), (key501, 6)]

theorem rawRowCheck12585 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form1 = rawRow12585 := by decide +kernel

def row12585 : Integer.Sparse Key := [(key229, 6), (key501, 12), (key557, -18)]

theorem rowCheck12585 : row12585 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12585 := by decide +kernel

theorem rowEval12585 (x : Key → ℝ) : Integer.Sparse.eval row12585 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12585, Integer.Sparse.eval_collectBalanced, rawRowCheck12585]

def rawRow12586 : Integer.Sparse Key := [(key557, -24), (key557, 6), (key501, 6), (key501, 6), (key229, 6)]

theorem rawRowCheck12586 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form1 = rawRow12586 := by decide +kernel

def row12586 : Integer.Sparse Key := [(key229, 6), (key501, 12), (key557, -18)]

theorem rowCheck12586 : row12586 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12586 := by decide +kernel

theorem rowEval12586 (x : Key → ℝ) : Integer.Sparse.eval row12586 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck12586, Integer.Sparse.eval_collectBalanced, rawRowCheck12586]

def rawRow12587 : Integer.Sparse Key := [(key498, -6), (key498, -6), (key504, -6), (key666, -6), (key226, 2), (key226, 2), (key232, 2), (key498, 2), (key498, 2), (key552, 2), (key552, 2), (key562, 2), (key562, 2), (key666, 2), (key683, 2), (key683, 2)]

theorem rawRowCheck12587 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form2 = rawRow12587 := by decide +kernel

def row12587 : Integer.Sparse Key := [(key226, 4), (key232, 2), (key498, -8), (key504, -6), (key552, 4), (key562, 4), (key666, -4), (key683, 4)]

theorem rowCheck12587 : row12587 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12587 := by decide +kernel

theorem rowEval12587 (x : Key → ℝ) : Integer.Sparse.eval row12587 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12587, Integer.Sparse.eval_collectBalanced, rawRowCheck12587]

def rawRow12588 : Integer.Sparse Key := [(key498, -6), (key504, -6), (key498, -6), (key666, -6), (key226, 2), (key232, 2), (key226, 2), (key552, 2), (key562, 2), (key498, 2), (key562, 2), (key498, 2), (key552, 2), (key683, 2), (key666, 2), (key683, 2)]

theorem rawRowCheck12588 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form2 = rawRow12588 := by decide +kernel

def row12588 : Integer.Sparse Key := [(key226, 4), (key232, 2), (key498, -8), (key504, -6), (key552, 4), (key562, 4), (key666, -4), (key683, 4)]

theorem rowCheck12588 : row12588 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12588 := by decide +kernel

theorem rowEval12588 (x : Key → ℝ) : Integer.Sparse.eval row12588 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12588, Integer.Sparse.eval_collectBalanced, rawRowCheck12588]

def rawRow12589 : Integer.Sparse Key := [(key504, -6), (key498, -6), (key498, -6), (key666, -6), (key232, 2), (key226, 2), (key226, 2), (key562, 2), (key552, 2), (key562, 2), (key498, 2), (key552, 2), (key498, 2), (key683, 2), (key683, 2), (key666, 2)]

theorem rawRowCheck12589 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form2 = rawRow12589 := by decide +kernel

def row12589 : Integer.Sparse Key := [(key226, 4), (key232, 2), (key498, -8), (key504, -6), (key552, 4), (key562, 4), (key666, -4), (key683, 4)]

theorem rowCheck12589 : row12589 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12589 := by decide +kernel

theorem rowEval12589 (x : Key → ℝ) : Integer.Sparse.eval row12589 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12589, Integer.Sparse.eval_collectBalanced, rawRowCheck12589]

def rawRow12590 : Integer.Sparse Key := [(key498, -6), (key498, -6), (key666, -6), (key504, -6), (key498, 2), (key498, 2), (key666, 2), (key226, 2), (key226, 2), (key552, 2), (key552, 2), (key683, 2), (key683, 2), (key232, 2), (key562, 2), (key562, 2)]

theorem rawRowCheck12590 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form2 = rawRow12590 := by decide +kernel

def row12590 : Integer.Sparse Key := [(key226, 4), (key232, 2), (key498, -8), (key504, -6), (key552, 4), (key562, 4), (key666, -4), (key683, 4)]

theorem rowCheck12590 : row12590 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12590 := by decide +kernel

theorem rowEval12590 (x : Key → ℝ) : Integer.Sparse.eval row12590 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12590, Integer.Sparse.eval_collectBalanced, rawRowCheck12590]

def rawRow12591 : Integer.Sparse Key := [(key498, -6), (key666, -6), (key498, -6), (key504, -6), (key498, 2), (key666, 2), (key498, 2), (key552, 2), (key683, 2), (key226, 2), (key683, 2), (key226, 2), (key552, 2), (key562, 2), (key232, 2), (key562, 2)]

theorem rawRowCheck12591 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form2 = rawRow12591 := by decide +kernel

def row12591 : Integer.Sparse Key := [(key226, 4), (key232, 2), (key498, -8), (key504, -6), (key552, 4), (key562, 4), (key666, -4), (key683, 4)]

theorem rowCheck12591 : row12591 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12591 := by decide +kernel

theorem rowEval12591 (x : Key → ℝ) : Integer.Sparse.eval row12591 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12591, Integer.Sparse.eval_collectBalanced, rawRowCheck12591]

def rawRow12592 : Integer.Sparse Key := [(key666, -6), (key498, -6), (key498, -6), (key504, -6), (key666, 2), (key498, 2), (key498, 2), (key683, 2), (key552, 2), (key683, 2), (key226, 2), (key552, 2), (key226, 2), (key562, 2), (key562, 2), (key232, 2)]

theorem rawRowCheck12592 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form2 = rawRow12592 := by decide +kernel

def row12592 : Integer.Sparse Key := [(key226, 4), (key232, 2), (key498, -8), (key504, -6), (key552, 4), (key562, 4), (key666, -4), (key683, 4)]

theorem rowCheck12592 : row12592 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12592 := by decide +kernel

theorem rowEval12592 (x : Key → ℝ) : Integer.Sparse.eval row12592 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck12592, Integer.Sparse.eval_collectBalanced, rawRowCheck12592]

def rawRow12593 : Integer.Sparse Key := [(key498, -6), (key504, -6), (key666, -6), (key498, -6), (key552, 2), (key562, 2), (key683, 2), (key226, 2), (key232, 2), (key498, 2), (key562, 2), (key666, 2), (key683, 2), (key226, 2), (key498, 2), (key552, 2)]

theorem rawRowCheck12593 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form2 = rawRow12593 := by decide +kernel

def row12593 : Integer.Sparse Key := [(key226, 4), (key232, 2), (key498, -8), (key504, -6), (key552, 4), (key562, 4), (key666, -4), (key683, 4)]

theorem rowCheck12593 : row12593 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12593 := by decide +kernel

theorem rowEval12593 (x : Key → ℝ) : Integer.Sparse.eval row12593 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12593, Integer.Sparse.eval_collectBalanced, rawRowCheck12593]

def rawRow12594 : Integer.Sparse Key := [(key504, -6), (key498, -6), (key666, -6), (key498, -6), (key562, 2), (key552, 2), (key683, 2), (key232, 2), (key226, 2), (key562, 2), (key498, 2), (key683, 2), (key666, 2), (key226, 2), (key552, 2), (key498, 2)]

theorem rawRowCheck12594 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form2 = rawRow12594 := by decide +kernel

def row12594 : Integer.Sparse Key := [(key226, 4), (key232, 2), (key498, -8), (key504, -6), (key552, 4), (key562, 4), (key666, -4), (key683, 4)]

theorem rowCheck12594 : row12594 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12594 := by decide +kernel

theorem rowEval12594 (x : Key → ℝ) : Integer.Sparse.eval row12594 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12594, Integer.Sparse.eval_collectBalanced, rawRowCheck12594]

def rawRow12595 : Integer.Sparse Key := [(key498, -6), (key666, -6), (key504, -6), (key498, -6), (key552, 2), (key683, 2), (key562, 2), (key498, 2), (key666, 2), (key226, 2), (key683, 2), (key232, 2), (key562, 2), (key498, 2), (key226, 2), (key552, 2)]

theorem rawRowCheck12595 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form2 = rawRow12595 := by decide +kernel

def row12595 : Integer.Sparse Key := [(key226, 4), (key232, 2), (key498, -8), (key504, -6), (key552, 4), (key562, 4), (key666, -4), (key683, 4)]

theorem rowCheck12595 : row12595 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12595 := by decide +kernel

theorem rowEval12595 (x : Key → ℝ) : Integer.Sparse.eval row12595 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12595, Integer.Sparse.eval_collectBalanced, rawRowCheck12595]

def rawRow12596 : Integer.Sparse Key := [(key666, -6), (key498, -6), (key504, -6), (key498, -6), (key683, 2), (key552, 2), (key562, 2), (key666, 2), (key498, 2), (key683, 2), (key226, 2), (key562, 2), (key232, 2), (key498, 2), (key552, 2), (key226, 2)]

theorem rawRowCheck12596 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form2 = rawRow12596 := by decide +kernel

def row12596 : Integer.Sparse Key := [(key226, 4), (key232, 2), (key498, -8), (key504, -6), (key552, 4), (key562, 4), (key666, -4), (key683, 4)]

theorem rowCheck12596 : row12596 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12596 := by decide +kernel

theorem rowEval12596 (x : Key → ℝ) : Integer.Sparse.eval row12596 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck12596, Integer.Sparse.eval_collectBalanced, rawRowCheck12596]

def rawRow12597 : Integer.Sparse Key := [(key504, -6), (key666, -6), (key498, -6), (key498, -6), (key562, 2), (key683, 2), (key552, 2), (key562, 2), (key683, 2), (key232, 2), (key666, 2), (key226, 2), (key498, 2), (key552, 2), (key226, 2), (key498, 2)]

theorem rawRowCheck12597 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form2 = rawRow12597 := by decide +kernel

def row12597 : Integer.Sparse Key := [(key226, 4), (key232, 2), (key498, -8), (key504, -6), (key552, 4), (key562, 4), (key666, -4), (key683, 4)]

theorem rowCheck12597 : row12597 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12597 := by decide +kernel

theorem rowEval12597 (x : Key → ℝ) : Integer.Sparse.eval row12597 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12597, Integer.Sparse.eval_collectBalanced, rawRowCheck12597]

def rawRow12598 : Integer.Sparse Key := [(key666, -6), (key504, -6), (key498, -6), (key498, -6), (key683, 2), (key562, 2), (key552, 2), (key683, 2), (key562, 2), (key666, 2), (key232, 2), (key498, 2), (key226, 2), (key552, 2), (key498, 2), (key226, 2)]

theorem rawRowCheck12598 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form2 = rawRow12598 := by decide +kernel

def row12598 : Integer.Sparse Key := [(key226, 4), (key232, 2), (key498, -8), (key504, -6), (key552, 4), (key562, 4), (key666, -4), (key683, 4)]

theorem rowCheck12598 : row12598 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12598 := by decide +kernel

theorem rowEval12598 (x : Key → ℝ) : Integer.Sparse.eval row12598 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck12598, Integer.Sparse.eval_collectBalanced, rawRowCheck12598]

def rawRow12599 : Integer.Sparse Key := [(key552, -6), (key562, -6), (key562, -6), (key683, -6), (key226, 2), (key232, 2), (key232, 2), (key498, 2), (key504, 2), (key498, 2), (key562, 2), (key504, 2), (key562, 2), (key666, 2), (key666, 2), (key683, 2)]

theorem rawRowCheck12599 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form2 = rawRow12599 := by decide +kernel

def row12599 : Integer.Sparse Key := [(key226, 2), (key232, 4), (key498, 4), (key504, 4), (key552, -6), (key562, -8), (key666, 4), (key683, -4)]

theorem rowCheck12599 : row12599 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12599 := by decide +kernel

theorem rowEval12599 (x : Key → ℝ) : Integer.Sparse.eval row12599 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12599, Integer.Sparse.eval_collectBalanced, rawRowCheck12599]

def rawRow12600 : Integer.Sparse Key := [(key562, -6), (key552, -6), (key562, -6), (key683, -6), (key232, 2), (key226, 2), (key232, 2), (key504, 2), (key498, 2), (key562, 2), (key498, 2), (key562, 2), (key504, 2), (key666, 2), (key683, 2), (key666, 2)]

theorem rawRowCheck12600 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form2 = rawRow12600 := by decide +kernel

def row12600 : Integer.Sparse Key := [(key226, 2), (key232, 4), (key498, 4), (key504, 4), (key552, -6), (key562, -8), (key666, 4), (key683, -4)]

theorem rowCheck12600 : row12600 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12600 := by decide +kernel

theorem rowEval12600 (x : Key → ℝ) : Integer.Sparse.eval row12600 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12600, Integer.Sparse.eval_collectBalanced, rawRowCheck12600]

def rawRow12601 : Integer.Sparse Key := [(key562, -6), (key562, -6), (key552, -6), (key683, -6), (key232, 2), (key232, 2), (key226, 2), (key562, 2), (key562, 2), (key504, 2), (key504, 2), (key498, 2), (key498, 2), (key683, 2), (key666, 2), (key666, 2)]

theorem rawRowCheck12601 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form2 = rawRow12601 := by decide +kernel

def row12601 : Integer.Sparse Key := [(key226, 2), (key232, 4), (key498, 4), (key504, 4), (key552, -6), (key562, -8), (key666, 4), (key683, -4)]

theorem rowCheck12601 : row12601 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12601 := by decide +kernel

theorem rowEval12601 (x : Key → ℝ) : Integer.Sparse.eval row12601 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12601, Integer.Sparse.eval_collectBalanced, rawRowCheck12601]

def rawRow12602 : Integer.Sparse Key := [(key552, -6), (key562, -6), (key683, -6), (key562, -6), (key498, 2), (key504, 2), (key666, 2), (key226, 2), (key232, 2), (key498, 2), (key562, 2), (key666, 2), (key683, 2), (key232, 2), (key504, 2), (key562, 2)]

theorem rawRowCheck12602 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form2 = rawRow12602 := by decide +kernel

def row12602 : Integer.Sparse Key := [(key226, 2), (key232, 4), (key498, 4), (key504, 4), (key552, -6), (key562, -8), (key666, 4), (key683, -4)]

theorem rowCheck12602 : row12602 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12602 := by decide +kernel

theorem rowEval12602 (x : Key → ℝ) : Integer.Sparse.eval row12602 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12602, Integer.Sparse.eval_collectBalanced, rawRowCheck12602]

def rawRow12603 : Integer.Sparse Key := [(key562, -6), (key552, -6), (key683, -6), (key562, -6), (key504, 2), (key498, 2), (key666, 2), (key232, 2), (key226, 2), (key562, 2), (key498, 2), (key683, 2), (key666, 2), (key232, 2), (key562, 2), (key504, 2)]

theorem rawRowCheck12603 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form2 = rawRow12603 := by decide +kernel

def row12603 : Integer.Sparse Key := [(key226, 2), (key232, 4), (key498, 4), (key504, 4), (key552, -6), (key562, -8), (key666, 4), (key683, -4)]

theorem rowCheck12603 : row12603 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12603 := by decide +kernel

theorem rowEval12603 (x : Key → ℝ) : Integer.Sparse.eval row12603 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12603, Integer.Sparse.eval_collectBalanced, rawRowCheck12603]

def rawRow12604 : Integer.Sparse Key := [(key552, -6), (key683, -6), (key562, -6), (key562, -6), (key498, 2), (key666, 2), (key504, 2), (key498, 2), (key666, 2), (key226, 2), (key683, 2), (key232, 2), (key562, 2), (key504, 2), (key232, 2), (key562, 2)]

theorem rawRowCheck12604 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form2 = rawRow12604 := by decide +kernel

def row12604 : Integer.Sparse Key := [(key226, 2), (key232, 4), (key498, 4), (key504, 4), (key552, -6), (key562, -8), (key666, 4), (key683, -4)]

theorem rowCheck12604 : row12604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12604 := by decide +kernel

theorem rowEval12604 (x : Key → ℝ) : Integer.Sparse.eval row12604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12604, Integer.Sparse.eval_collectBalanced, rawRowCheck12604]

def rawRow12605 : Integer.Sparse Key := [(key683, -6), (key552, -6), (key562, -6), (key562, -6), (key666, 2), (key498, 2), (key504, 2), (key666, 2), (key498, 2), (key683, 2), (key226, 2), (key562, 2), (key232, 2), (key504, 2), (key562, 2), (key232, 2)]

theorem rawRowCheck12605 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form2 = rawRow12605 := by decide +kernel

def row12605 : Integer.Sparse Key := [(key226, 2), (key232, 4), (key498, 4), (key504, 4), (key552, -6), (key562, -8), (key666, 4), (key683, -4)]

theorem rowCheck12605 : row12605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12605 := by decide +kernel

theorem rowEval12605 (x : Key → ℝ) : Integer.Sparse.eval row12605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck12605, Integer.Sparse.eval_collectBalanced, rawRowCheck12605]

def rawRow12606 : Integer.Sparse Key := [(key562, -6), (key683, -6), (key552, -6), (key562, -6), (key504, 2), (key666, 2), (key498, 2), (key562, 2), (key683, 2), (key232, 2), (key666, 2), (key226, 2), (key498, 2), (key562, 2), (key232, 2), (key504, 2)]

theorem rawRowCheck12606 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form2 = rawRow12606 := by decide +kernel

def row12606 : Integer.Sparse Key := [(key226, 2), (key232, 4), (key498, 4), (key504, 4), (key552, -6), (key562, -8), (key666, 4), (key683, -4)]

theorem rowCheck12606 : row12606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12606 := by decide +kernel

theorem rowEval12606 (x : Key → ℝ) : Integer.Sparse.eval row12606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12606, Integer.Sparse.eval_collectBalanced, rawRowCheck12606]

def rawRow12607 : Integer.Sparse Key := [(key683, -6), (key562, -6), (key552, -6), (key562, -6), (key666, 2), (key504, 2), (key498, 2), (key683, 2), (key562, 2), (key666, 2), (key232, 2), (key498, 2), (key226, 2), (key562, 2), (key504, 2), (key232, 2)]

theorem rawRowCheck12607 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form2 = rawRow12607 := by decide +kernel

def row12607 : Integer.Sparse Key := [(key226, 2), (key232, 4), (key498, 4), (key504, 4), (key552, -6), (key562, -8), (key666, 4), (key683, -4)]

theorem rowCheck12607 : row12607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12607 := by decide +kernel

theorem rowEval12607 (x : Key → ℝ) : Integer.Sparse.eval row12607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck12607, Integer.Sparse.eval_collectBalanced, rawRowCheck12607]

def rawRow12608 : Integer.Sparse Key := [(key562, -6), (key562, -6), (key683, -6), (key552, -6), (key562, 2), (key562, 2), (key683, 2), (key232, 2), (key232, 2), (key504, 2), (key504, 2), (key666, 2), (key666, 2), (key226, 2), (key498, 2), (key498, 2)]

theorem rawRowCheck12608 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form2 = rawRow12608 := by decide +kernel

def row12608 : Integer.Sparse Key := [(key226, 2), (key232, 4), (key498, 4), (key504, 4), (key552, -6), (key562, -8), (key666, 4), (key683, -4)]

theorem rowCheck12608 : row12608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12608 := by decide +kernel

theorem rowEval12608 (x : Key → ℝ) : Integer.Sparse.eval row12608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12608, Integer.Sparse.eval_collectBalanced, rawRowCheck12608]

def rawRow12609 : Integer.Sparse Key := [(key562, -6), (key683, -6), (key562, -6), (key552, -6), (key562, 2), (key683, 2), (key562, 2), (key504, 2), (key666, 2), (key232, 2), (key666, 2), (key232, 2), (key504, 2), (key498, 2), (key226, 2), (key498, 2)]

theorem rawRowCheck12609 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form2 = rawRow12609 := by decide +kernel

def row12609 : Integer.Sparse Key := [(key226, 2), (key232, 4), (key498, 4), (key504, 4), (key552, -6), (key562, -8), (key666, 4), (key683, -4)]

theorem rowCheck12609 : row12609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12609 := by decide +kernel

theorem rowEval12609 (x : Key → ℝ) : Integer.Sparse.eval row12609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12609, Integer.Sparse.eval_collectBalanced, rawRowCheck12609]

def rawRow12610 : Integer.Sparse Key := [(key683, -6), (key562, -6), (key562, -6), (key552, -6), (key683, 2), (key562, 2), (key562, 2), (key666, 2), (key504, 2), (key666, 2), (key232, 2), (key504, 2), (key232, 2), (key498, 2), (key498, 2), (key226, 2)]

theorem rawRowCheck12610 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form2 = rawRow12610 := by decide +kernel

def row12610 : Integer.Sparse Key := [(key226, 2), (key232, 4), (key498, 4), (key504, 4), (key552, -6), (key562, -8), (key666, 4), (key683, -4)]

theorem rowCheck12610 : row12610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12610 := by decide +kernel

theorem rowEval12610 (x : Key → ℝ) : Integer.Sparse.eval row12610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck12610, Integer.Sparse.eval_collectBalanced, rawRowCheck12610]

def rawRow12611 : Integer.Sparse Key := [(key1368, -6), (key1720, -6), (key1744, -6), (key1744, -6), (key1368, 2), (key1377, 2), (key1377, 2), (key1494, 2), (key1516, 2), (key1516, 2), (key1726, 2), (key1726, 2), (key1744, 2), (key1744, 2), (key1755, 2), (key1755, 2)]

theorem rawRowCheck12611 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form3 = rawRow12611 := by decide +kernel

def row12611 : Integer.Sparse Key := [(key1368, -4), (key1377, 4), (key1494, 2), (key1516, 4), (key1720, -6), (key1726, 4), (key1744, -8), (key1755, 4)]

theorem rowCheck12611 : row12611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12611 := by decide +kernel

theorem rowEval12611 (x : Key → ℝ) : Integer.Sparse.eval row12611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12611, Integer.Sparse.eval_collectBalanced, rawRowCheck12611]

def rawRow12612 : Integer.Sparse Key := [(key1368, -6), (key1744, -6), (key1720, -6), (key1744, -6), (key1377, 2), (key1368, 2), (key1377, 2), (key1516, 2), (key1494, 2), (key1516, 2), (key1744, 2), (key1755, 2), (key1726, 2), (key1755, 2), (key1726, 2), (key1744, 2)]

theorem rawRowCheck12612 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form3 = rawRow12612 := by decide +kernel

def row12612 : Integer.Sparse Key := [(key1368, -4), (key1377, 4), (key1494, 2), (key1516, 4), (key1720, -6), (key1726, 4), (key1744, -8), (key1755, 4)]

theorem rowCheck12612 : row12612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12612 := by decide +kernel

theorem rowEval12612 (x : Key → ℝ) : Integer.Sparse.eval row12612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12612, Integer.Sparse.eval_collectBalanced, rawRowCheck12612]

def rawRow12613 : Integer.Sparse Key := [(key1368, -6), (key1744, -6), (key1744, -6), (key1720, -6), (key1377, 2), (key1377, 2), (key1368, 2), (key1516, 2), (key1516, 2), (key1494, 2), (key1755, 2), (key1744, 2), (key1755, 2), (key1726, 2), (key1744, 2), (key1726, 2)]

theorem rawRowCheck12613 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form3 = rawRow12613 := by decide +kernel

def row12613 : Integer.Sparse Key := [(key1368, -4), (key1377, 4), (key1494, 2), (key1516, 4), (key1720, -6), (key1726, 4), (key1744, -8), (key1755, 4)]

theorem rowCheck12613 : row12613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12613 := by decide +kernel

theorem rowEval12613 (x : Key → ℝ) : Integer.Sparse.eval row12613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12613, Integer.Sparse.eval_collectBalanced, rawRowCheck12613]

def rawRow12614 : Integer.Sparse Key := [(key1720, -6), (key1368, -6), (key1744, -6), (key1744, -6), (key1494, 2), (key1726, 2), (key1726, 2), (key1368, 2), (key1744, 2), (key1744, 2), (key1377, 2), (key1377, 2), (key1516, 2), (key1516, 2), (key1755, 2), (key1755, 2)]

theorem rawRowCheck12614 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form3 = rawRow12614 := by decide +kernel

def row12614 : Integer.Sparse Key := [(key1368, -4), (key1377, 4), (key1494, 2), (key1516, 4), (key1720, -6), (key1726, 4), (key1744, -8), (key1755, 4)]

theorem rowCheck12614 : row12614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12614 := by decide +kernel

theorem rowEval12614 (x : Key → ℝ) : Integer.Sparse.eval row12614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12614, Integer.Sparse.eval_collectBalanced, rawRowCheck12614]

def rawRow12615 : Integer.Sparse Key := [(key1720, -6), (key1744, -6), (key1368, -6), (key1744, -6), (key1726, 2), (key1494, 2), (key1726, 2), (key1744, 2), (key1368, 2), (key1744, 2), (key1516, 2), (key1755, 2), (key1377, 2), (key1755, 2), (key1377, 2), (key1516, 2)]

theorem rawRowCheck12615 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form3 = rawRow12615 := by decide +kernel

def row12615 : Integer.Sparse Key := [(key1368, -4), (key1377, 4), (key1494, 2), (key1516, 4), (key1720, -6), (key1726, 4), (key1744, -8), (key1755, 4)]

theorem rowCheck12615 : row12615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12615 := by decide +kernel

theorem rowEval12615 (x : Key → ℝ) : Integer.Sparse.eval row12615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12615, Integer.Sparse.eval_collectBalanced, rawRowCheck12615]

def rawRow12616 : Integer.Sparse Key := [(key1720, -6), (key1744, -6), (key1744, -6), (key1368, -6), (key1726, 2), (key1726, 2), (key1494, 2), (key1744, 2), (key1744, 2), (key1368, 2), (key1755, 2), (key1516, 2), (key1755, 2), (key1377, 2), (key1516, 2), (key1377, 2)]

theorem rawRowCheck12616 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form3 = rawRow12616 := by decide +kernel

def row12616 : Integer.Sparse Key := [(key1368, -4), (key1377, 4), (key1494, 2), (key1516, 4), (key1720, -6), (key1726, 4), (key1744, -8), (key1755, 4)]

theorem rowCheck12616 : row12616 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12616 := by decide +kernel

theorem rowEval12616 (x : Key → ℝ) : Integer.Sparse.eval row12616 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck12616, Integer.Sparse.eval_collectBalanced, rawRowCheck12616]

def rawRow12617 : Integer.Sparse Key := [(key1744, -6), (key1368, -6), (key1720, -6), (key1744, -6), (key1516, 2), (key1744, 2), (key1755, 2), (key1377, 2), (key1726, 2), (key1755, 2), (key1368, 2), (key1377, 2), (key1494, 2), (key1516, 2), (key1726, 2), (key1744, 2)]

theorem rawRowCheck12617 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form3 = rawRow12617 := by decide +kernel

def row12617 : Integer.Sparse Key := [(key1368, -4), (key1377, 4), (key1494, 2), (key1516, 4), (key1720, -6), (key1726, 4), (key1744, -8), (key1755, 4)]

theorem rowCheck12617 : row12617 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12617 := by decide +kernel

theorem rowEval12617 (x : Key → ℝ) : Integer.Sparse.eval row12617 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12617, Integer.Sparse.eval_collectBalanced, rawRowCheck12617]

def rawRow12618 : Integer.Sparse Key := [(key1744, -6), (key1368, -6), (key1744, -6), (key1720, -6), (key1516, 2), (key1755, 2), (key1744, 2), (key1377, 2), (key1755, 2), (key1726, 2), (key1377, 2), (key1368, 2), (key1516, 2), (key1494, 2), (key1744, 2), (key1726, 2)]

theorem rawRowCheck12618 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form3 = rawRow12618 := by decide +kernel

def row12618 : Integer.Sparse Key := [(key1368, -4), (key1377, 4), (key1494, 2), (key1516, 4), (key1720, -6), (key1726, 4), (key1744, -8), (key1755, 4)]

theorem rowCheck12618 : row12618 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12618 := by decide +kernel

theorem rowEval12618 (x : Key → ℝ) : Integer.Sparse.eval row12618 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12618, Integer.Sparse.eval_collectBalanced, rawRowCheck12618]

def rawRow12619 : Integer.Sparse Key := [(key1744, -6), (key1720, -6), (key1368, -6), (key1744, -6), (key1744, 2), (key1516, 2), (key1755, 2), (key1726, 2), (key1377, 2), (key1755, 2), (key1494, 2), (key1726, 2), (key1368, 2), (key1744, 2), (key1377, 2), (key1516, 2)]

theorem rawRowCheck12619 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form3 = rawRow12619 := by decide +kernel

def row12619 : Integer.Sparse Key := [(key1368, -4), (key1377, 4), (key1494, 2), (key1516, 4), (key1720, -6), (key1726, 4), (key1744, -8), (key1755, 4)]

theorem rowCheck12619 : row12619 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12619 := by decide +kernel

theorem rowEval12619 (x : Key → ℝ) : Integer.Sparse.eval row12619 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12619, Integer.Sparse.eval_collectBalanced, rawRowCheck12619]

def rawRow12620 : Integer.Sparse Key := [(key1744, -6), (key1720, -6), (key1744, -6), (key1368, -6), (key1744, 2), (key1755, 2), (key1516, 2), (key1726, 2), (key1755, 2), (key1377, 2), (key1726, 2), (key1494, 2), (key1744, 2), (key1368, 2), (key1516, 2), (key1377, 2)]

theorem rawRowCheck12620 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form3 = rawRow12620 := by decide +kernel

def row12620 : Integer.Sparse Key := [(key1368, -4), (key1377, 4), (key1494, 2), (key1516, 4), (key1720, -6), (key1726, 4), (key1744, -8), (key1755, 4)]

theorem rowCheck12620 : row12620 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12620 := by decide +kernel

theorem rowEval12620 (x : Key → ℝ) : Integer.Sparse.eval row12620 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck12620, Integer.Sparse.eval_collectBalanced, rawRowCheck12620]

def rawRow12621 : Integer.Sparse Key := [(key1744, -6), (key1744, -6), (key1368, -6), (key1720, -6), (key1755, 2), (key1516, 2), (key1744, 2), (key1755, 2), (key1377, 2), (key1726, 2), (key1516, 2), (key1744, 2), (key1377, 2), (key1726, 2), (key1368, 2), (key1494, 2)]

theorem rawRowCheck12621 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form3 = rawRow12621 := by decide +kernel

def row12621 : Integer.Sparse Key := [(key1368, -4), (key1377, 4), (key1494, 2), (key1516, 4), (key1720, -6), (key1726, 4), (key1744, -8), (key1755, 4)]

theorem rowCheck12621 : row12621 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12621 := by decide +kernel

theorem rowEval12621 (x : Key → ℝ) : Integer.Sparse.eval row12621 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12621, Integer.Sparse.eval_collectBalanced, rawRowCheck12621]

def rawRow12622 : Integer.Sparse Key := [(key1744, -6), (key1744, -6), (key1720, -6), (key1368, -6), (key1755, 2), (key1744, 2), (key1516, 2), (key1755, 2), (key1726, 2), (key1377, 2), (key1744, 2), (key1516, 2), (key1726, 2), (key1377, 2), (key1494, 2), (key1368, 2)]

theorem rawRowCheck12622 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form3 = rawRow12622 := by decide +kernel

def row12622 : Integer.Sparse Key := [(key1368, -4), (key1377, 4), (key1494, 2), (key1516, 4), (key1720, -6), (key1726, 4), (key1744, -8), (key1755, 4)]

theorem rowCheck12622 : row12622 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12622 := by decide +kernel

theorem rowEval12622 (x : Key → ℝ) : Integer.Sparse.eval row12622 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck12622, Integer.Sparse.eval_collectBalanced, rawRowCheck12622]

def rawRow12623 : Integer.Sparse Key := [(key1377, -6), (key1726, -6), (key1726, -6), (key1755, -6), (key1368, 2), (key1368, 2), (key1377, 2), (key1494, 2), (key1494, 2), (key1516, 2), (key1720, 2), (key1726, 2), (key1720, 2), (key1744, 2), (key1726, 2), (key1744, 2)]

theorem rawRowCheck12623 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form3 = rawRow12623 := by decide +kernel

def row12623 : Integer.Sparse Key := [(key1368, 4), (key1377, -4), (key1494, 4), (key1516, 2), (key1720, 4), (key1726, -8), (key1744, 4), (key1755, -6)]

theorem rowCheck12623 : row12623 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12623 := by decide +kernel

theorem rowEval12623 (x : Key → ℝ) : Integer.Sparse.eval row12623 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12623, Integer.Sparse.eval_collectBalanced, rawRowCheck12623]

def rawRow12624 : Integer.Sparse Key := [(key1377, -6), (key1726, -6), (key1755, -6), (key1726, -6), (key1368, 2), (key1377, 2), (key1368, 2), (key1494, 2), (key1516, 2), (key1494, 2), (key1726, 2), (key1720, 2), (key1744, 2), (key1720, 2), (key1744, 2), (key1726, 2)]

theorem rawRowCheck12624 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form3 = rawRow12624 := by decide +kernel

def row12624 : Integer.Sparse Key := [(key1368, 4), (key1377, -4), (key1494, 4), (key1516, 2), (key1720, 4), (key1726, -8), (key1744, 4), (key1755, -6)]

theorem rowCheck12624 : row12624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12624 := by decide +kernel

theorem rowEval12624 (x : Key → ℝ) : Integer.Sparse.eval row12624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12624, Integer.Sparse.eval_collectBalanced, rawRowCheck12624]

def rawRow12625 : Integer.Sparse Key := [(key1377, -6), (key1755, -6), (key1726, -6), (key1726, -6), (key1377, 2), (key1368, 2), (key1368, 2), (key1516, 2), (key1494, 2), (key1494, 2), (key1744, 2), (key1744, 2), (key1726, 2), (key1726, 2), (key1720, 2), (key1720, 2)]

theorem rawRowCheck12625 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form3 = rawRow12625 := by decide +kernel

def row12625 : Integer.Sparse Key := [(key1368, 4), (key1377, -4), (key1494, 4), (key1516, 2), (key1720, 4), (key1726, -8), (key1744, 4), (key1755, -6)]

theorem rowCheck12625 : row12625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12625 := by decide +kernel

theorem rowEval12625 (x : Key → ℝ) : Integer.Sparse.eval row12625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12625, Integer.Sparse.eval_collectBalanced, rawRowCheck12625]

def rawRow12626 : Integer.Sparse Key := [(key1726, -6), (key1377, -6), (key1726, -6), (key1755, -6), (key1494, 2), (key1720, 2), (key1726, 2), (key1368, 2), (key1720, 2), (key1744, 2), (key1368, 2), (key1377, 2), (key1494, 2), (key1516, 2), (key1726, 2), (key1744, 2)]

theorem rawRowCheck12626 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form3 = rawRow12626 := by decide +kernel

def row12626 : Integer.Sparse Key := [(key1368, 4), (key1377, -4), (key1494, 4), (key1516, 2), (key1720, 4), (key1726, -8), (key1744, 4), (key1755, -6)]

theorem rowCheck12626 : row12626 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12626 := by decide +kernel

theorem rowEval12626 (x : Key → ℝ) : Integer.Sparse.eval row12626 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12626, Integer.Sparse.eval_collectBalanced, rawRowCheck12626]

def rawRow12627 : Integer.Sparse Key := [(key1726, -6), (key1377, -6), (key1755, -6), (key1726, -6), (key1494, 2), (key1726, 2), (key1720, 2), (key1368, 2), (key1744, 2), (key1720, 2), (key1377, 2), (key1368, 2), (key1516, 2), (key1494, 2), (key1744, 2), (key1726, 2)]

theorem rawRowCheck12627 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form3 = rawRow12627 := by decide +kernel

def row12627 : Integer.Sparse Key := [(key1368, 4), (key1377, -4), (key1494, 4), (key1516, 2), (key1720, 4), (key1726, -8), (key1744, 4), (key1755, -6)]

theorem rowCheck12627 : row12627 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12627 := by decide +kernel

theorem rowEval12627 (x : Key → ℝ) : Integer.Sparse.eval row12627 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12627, Integer.Sparse.eval_collectBalanced, rawRowCheck12627]

def rawRow12628 : Integer.Sparse Key := [(key1726, -6), (key1726, -6), (key1377, -6), (key1755, -6), (key1720, 2), (key1494, 2), (key1726, 2), (key1720, 2), (key1368, 2), (key1744, 2), (key1494, 2), (key1726, 2), (key1368, 2), (key1744, 2), (key1377, 2), (key1516, 2)]

theorem rawRowCheck12628 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form3 = rawRow12628 := by decide +kernel

def row12628 : Integer.Sparse Key := [(key1368, 4), (key1377, -4), (key1494, 4), (key1516, 2), (key1720, 4), (key1726, -8), (key1744, 4), (key1755, -6)]

theorem rowCheck12628 : row12628 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12628 := by decide +kernel

theorem rowEval12628 (x : Key → ℝ) : Integer.Sparse.eval row12628 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12628, Integer.Sparse.eval_collectBalanced, rawRowCheck12628]

def rawRow12629 : Integer.Sparse Key := [(key1726, -6), (key1726, -6), (key1755, -6), (key1377, -6), (key1720, 2), (key1726, 2), (key1494, 2), (key1720, 2), (key1744, 2), (key1368, 2), (key1726, 2), (key1494, 2), (key1744, 2), (key1368, 2), (key1516, 2), (key1377, 2)]

theorem rawRowCheck12629 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form3 = rawRow12629 := by decide +kernel

def row12629 : Integer.Sparse Key := [(key1368, 4), (key1377, -4), (key1494, 4), (key1516, 2), (key1720, 4), (key1726, -8), (key1744, 4), (key1755, -6)]

theorem rowCheck12629 : row12629 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12629 := by decide +kernel

theorem rowEval12629 (x : Key → ℝ) : Integer.Sparse.eval row12629 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck12629, Integer.Sparse.eval_collectBalanced, rawRowCheck12629]

def rawRow12630 : Integer.Sparse Key := [(key1726, -6), (key1755, -6), (key1377, -6), (key1726, -6), (key1726, 2), (key1494, 2), (key1720, 2), (key1744, 2), (key1368, 2), (key1720, 2), (key1516, 2), (key1744, 2), (key1377, 2), (key1726, 2), (key1368, 2), (key1494, 2)]

theorem rawRowCheck12630 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form3 = rawRow12630 := by decide +kernel

def row12630 : Integer.Sparse Key := [(key1368, 4), (key1377, -4), (key1494, 4), (key1516, 2), (key1720, 4), (key1726, -8), (key1744, 4), (key1755, -6)]

theorem rowCheck12630 : row12630 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12630 := by decide +kernel

theorem rowEval12630 (x : Key → ℝ) : Integer.Sparse.eval row12630 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12630, Integer.Sparse.eval_collectBalanced, rawRowCheck12630]

def rawRow12631 : Integer.Sparse Key := [(key1726, -6), (key1755, -6), (key1726, -6), (key1377, -6), (key1726, 2), (key1720, 2), (key1494, 2), (key1744, 2), (key1720, 2), (key1368, 2), (key1744, 2), (key1516, 2), (key1726, 2), (key1377, 2), (key1494, 2), (key1368, 2)]

theorem rawRowCheck12631 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form3 = rawRow12631 := by decide +kernel

def row12631 : Integer.Sparse Key := [(key1368, 4), (key1377, -4), (key1494, 4), (key1516, 2), (key1720, 4), (key1726, -8), (key1744, 4), (key1755, -6)]

theorem rowCheck12631 : row12631 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12631 := by decide +kernel

theorem rowEval12631 (x : Key → ℝ) : Integer.Sparse.eval row12631 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck12631, Integer.Sparse.eval_collectBalanced, rawRowCheck12631]

def rawRow12632 : Integer.Sparse Key := [(key1755, -6), (key1377, -6), (key1726, -6), (key1726, -6), (key1516, 2), (key1744, 2), (key1744, 2), (key1377, 2), (key1726, 2), (key1726, 2), (key1368, 2), (key1368, 2), (key1494, 2), (key1494, 2), (key1720, 2), (key1720, 2)]

theorem rawRowCheck12632 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form3 = rawRow12632 := by decide +kernel

def row12632 : Integer.Sparse Key := [(key1368, 4), (key1377, -4), (key1494, 4), (key1516, 2), (key1720, 4), (key1726, -8), (key1744, 4), (key1755, -6)]

theorem rowCheck12632 : row12632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12632 := by decide +kernel

theorem rowEval12632 (x : Key → ℝ) : Integer.Sparse.eval row12632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12632, Integer.Sparse.eval_collectBalanced, rawRowCheck12632]

def rawRow12633 : Integer.Sparse Key := [(key1755, -6), (key1726, -6), (key1377, -6), (key1726, -6), (key1744, 2), (key1516, 2), (key1744, 2), (key1726, 2), (key1377, 2), (key1726, 2), (key1494, 2), (key1720, 2), (key1368, 2), (key1720, 2), (key1368, 2), (key1494, 2)]

theorem rawRowCheck12633 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form3 = rawRow12633 := by decide +kernel

def row12633 : Integer.Sparse Key := [(key1368, 4), (key1377, -4), (key1494, 4), (key1516, 2), (key1720, 4), (key1726, -8), (key1744, 4), (key1755, -6)]

theorem rowCheck12633 : row12633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12633 := by decide +kernel

theorem rowEval12633 (x : Key → ℝ) : Integer.Sparse.eval row12633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12633, Integer.Sparse.eval_collectBalanced, rawRowCheck12633]

def rawRow12634 : Integer.Sparse Key := [(key1755, -6), (key1726, -6), (key1726, -6), (key1377, -6), (key1744, 2), (key1744, 2), (key1516, 2), (key1726, 2), (key1726, 2), (key1377, 2), (key1720, 2), (key1494, 2), (key1720, 2), (key1368, 2), (key1494, 2), (key1368, 2)]

theorem rawRowCheck12634 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form3 = rawRow12634 := by decide +kernel

def row12634 : Integer.Sparse Key := [(key1368, 4), (key1377, -4), (key1494, 4), (key1516, 2), (key1720, 4), (key1726, -8), (key1744, 4), (key1755, -6)]

theorem rowCheck12634 : row12634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12634 := by decide +kernel

theorem rowEval12634 (x : Key → ℝ) : Integer.Sparse.eval row12634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck12634, Integer.Sparse.eval_collectBalanced, rawRowCheck12634]

def rawRow12635 : Integer.Sparse Key := [(key1702, -6), (key1702, -6), (key1708, -6), (key1935, -6), (key1279, 2), (key1279, 2), (key1285, 2), (key1702, 2), (key1702, 2), (key1752, 2), (key1752, 2), (key1758, 2), (key1758, 2), (key1935, 2), (key1955, 2), (key1955, 2)]

theorem rawRowCheck12635 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form4 = rawRow12635 := by decide +kernel

def row12635 : Integer.Sparse Key := [(key1279, 4), (key1285, 2), (key1702, -8), (key1708, -6), (key1752, 4), (key1758, 4), (key1935, -4), (key1955, 4)]

theorem rowCheck12635 : row12635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12635 := by decide +kernel

theorem rowEval12635 (x : Key → ℝ) : Integer.Sparse.eval row12635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12635, Integer.Sparse.eval_collectBalanced, rawRowCheck12635]

def rawRow12636 : Integer.Sparse Key := [(key1702, -6), (key1708, -6), (key1702, -6), (key1935, -6), (key1279, 2), (key1285, 2), (key1279, 2), (key1752, 2), (key1758, 2), (key1702, 2), (key1758, 2), (key1702, 2), (key1752, 2), (key1955, 2), (key1935, 2), (key1955, 2)]

theorem rawRowCheck12636 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form4 = rawRow12636 := by decide +kernel

def row12636 : Integer.Sparse Key := [(key1279, 4), (key1285, 2), (key1702, -8), (key1708, -6), (key1752, 4), (key1758, 4), (key1935, -4), (key1955, 4)]

theorem rowCheck12636 : row12636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12636 := by decide +kernel

theorem rowEval12636 (x : Key → ℝ) : Integer.Sparse.eval row12636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12636, Integer.Sparse.eval_collectBalanced, rawRowCheck12636]

def rawRow12637 : Integer.Sparse Key := [(key1708, -6), (key1702, -6), (key1702, -6), (key1935, -6), (key1285, 2), (key1279, 2), (key1279, 2), (key1758, 2), (key1752, 2), (key1758, 2), (key1702, 2), (key1752, 2), (key1702, 2), (key1955, 2), (key1955, 2), (key1935, 2)]

theorem rawRowCheck12637 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form4 = rawRow12637 := by decide +kernel

def row12637 : Integer.Sparse Key := [(key1279, 4), (key1285, 2), (key1702, -8), (key1708, -6), (key1752, 4), (key1758, 4), (key1935, -4), (key1955, 4)]

theorem rowCheck12637 : row12637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12637 := by decide +kernel

theorem rowEval12637 (x : Key → ℝ) : Integer.Sparse.eval row12637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12637, Integer.Sparse.eval_collectBalanced, rawRowCheck12637]

def rawRow12638 : Integer.Sparse Key := [(key1702, -6), (key1702, -6), (key1935, -6), (key1708, -6), (key1702, 2), (key1702, 2), (key1935, 2), (key1279, 2), (key1279, 2), (key1752, 2), (key1752, 2), (key1955, 2), (key1955, 2), (key1285, 2), (key1758, 2), (key1758, 2)]

theorem rawRowCheck12638 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form4 = rawRow12638 := by decide +kernel

def row12638 : Integer.Sparse Key := [(key1279, 4), (key1285, 2), (key1702, -8), (key1708, -6), (key1752, 4), (key1758, 4), (key1935, -4), (key1955, 4)]

theorem rowCheck12638 : row12638 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12638 := by decide +kernel

theorem rowEval12638 (x : Key → ℝ) : Integer.Sparse.eval row12638 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12638, Integer.Sparse.eval_collectBalanced, rawRowCheck12638]

def rawRow12639 : Integer.Sparse Key := [(key1702, -6), (key1935, -6), (key1702, -6), (key1708, -6), (key1702, 2), (key1935, 2), (key1702, 2), (key1752, 2), (key1955, 2), (key1279, 2), (key1955, 2), (key1279, 2), (key1752, 2), (key1758, 2), (key1285, 2), (key1758, 2)]

theorem rawRowCheck12639 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form4 = rawRow12639 := by decide +kernel

def row12639 : Integer.Sparse Key := [(key1279, 4), (key1285, 2), (key1702, -8), (key1708, -6), (key1752, 4), (key1758, 4), (key1935, -4), (key1955, 4)]

theorem rowCheck12639 : row12639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12639 := by decide +kernel

theorem rowEval12639 (x : Key → ℝ) : Integer.Sparse.eval row12639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12639, Integer.Sparse.eval_collectBalanced, rawRowCheck12639]

def rawRow12640 : Integer.Sparse Key := [(key1935, -6), (key1702, -6), (key1702, -6), (key1708, -6), (key1935, 2), (key1702, 2), (key1702, 2), (key1955, 2), (key1752, 2), (key1955, 2), (key1279, 2), (key1752, 2), (key1279, 2), (key1758, 2), (key1758, 2), (key1285, 2)]

theorem rawRowCheck12640 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form4 = rawRow12640 := by decide +kernel

def row12640 : Integer.Sparse Key := [(key1279, 4), (key1285, 2), (key1702, -8), (key1708, -6), (key1752, 4), (key1758, 4), (key1935, -4), (key1955, 4)]

theorem rowCheck12640 : row12640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12640 := by decide +kernel

theorem rowEval12640 (x : Key → ℝ) : Integer.Sparse.eval row12640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck12640, Integer.Sparse.eval_collectBalanced, rawRowCheck12640]

def rawRow12641 : Integer.Sparse Key := [(key1702, -6), (key1708, -6), (key1935, -6), (key1702, -6), (key1752, 2), (key1758, 2), (key1955, 2), (key1279, 2), (key1285, 2), (key1702, 2), (key1758, 2), (key1935, 2), (key1955, 2), (key1279, 2), (key1702, 2), (key1752, 2)]

theorem rawRowCheck12641 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form4 = rawRow12641 := by decide +kernel

def row12641 : Integer.Sparse Key := [(key1279, 4), (key1285, 2), (key1702, -8), (key1708, -6), (key1752, 4), (key1758, 4), (key1935, -4), (key1955, 4)]

theorem rowCheck12641 : row12641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12641 := by decide +kernel

theorem rowEval12641 (x : Key → ℝ) : Integer.Sparse.eval row12641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12641, Integer.Sparse.eval_collectBalanced, rawRowCheck12641]

def rawRow12642 : Integer.Sparse Key := [(key1708, -6), (key1702, -6), (key1935, -6), (key1702, -6), (key1758, 2), (key1752, 2), (key1955, 2), (key1285, 2), (key1279, 2), (key1758, 2), (key1702, 2), (key1955, 2), (key1935, 2), (key1279, 2), (key1752, 2), (key1702, 2)]

theorem rawRowCheck12642 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form4 = rawRow12642 := by decide +kernel

def row12642 : Integer.Sparse Key := [(key1279, 4), (key1285, 2), (key1702, -8), (key1708, -6), (key1752, 4), (key1758, 4), (key1935, -4), (key1955, 4)]

theorem rowCheck12642 : row12642 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12642 := by decide +kernel

theorem rowEval12642 (x : Key → ℝ) : Integer.Sparse.eval row12642 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12642, Integer.Sparse.eval_collectBalanced, rawRowCheck12642]

def rawRow12643 : Integer.Sparse Key := [(key1702, -6), (key1935, -6), (key1708, -6), (key1702, -6), (key1752, 2), (key1955, 2), (key1758, 2), (key1702, 2), (key1935, 2), (key1279, 2), (key1955, 2), (key1285, 2), (key1758, 2), (key1702, 2), (key1279, 2), (key1752, 2)]

theorem rawRowCheck12643 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form4 = rawRow12643 := by decide +kernel

def row12643 : Integer.Sparse Key := [(key1279, 4), (key1285, 2), (key1702, -8), (key1708, -6), (key1752, 4), (key1758, 4), (key1935, -4), (key1955, 4)]

theorem rowCheck12643 : row12643 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12643 := by decide +kernel

theorem rowEval12643 (x : Key → ℝ) : Integer.Sparse.eval row12643 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12643, Integer.Sparse.eval_collectBalanced, rawRowCheck12643]

def rawRow12644 : Integer.Sparse Key := [(key1935, -6), (key1702, -6), (key1708, -6), (key1702, -6), (key1955, 2), (key1752, 2), (key1758, 2), (key1935, 2), (key1702, 2), (key1955, 2), (key1279, 2), (key1758, 2), (key1285, 2), (key1702, 2), (key1752, 2), (key1279, 2)]

theorem rawRowCheck12644 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form4 = rawRow12644 := by decide +kernel

def row12644 : Integer.Sparse Key := [(key1279, 4), (key1285, 2), (key1702, -8), (key1708, -6), (key1752, 4), (key1758, 4), (key1935, -4), (key1955, 4)]

theorem rowCheck12644 : row12644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12644 := by decide +kernel

theorem rowEval12644 (x : Key → ℝ) : Integer.Sparse.eval row12644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck12644, Integer.Sparse.eval_collectBalanced, rawRowCheck12644]

def rawRow12645 : Integer.Sparse Key := [(key1708, -6), (key1935, -6), (key1702, -6), (key1702, -6), (key1758, 2), (key1955, 2), (key1752, 2), (key1758, 2), (key1955, 2), (key1285, 2), (key1935, 2), (key1279, 2), (key1702, 2), (key1752, 2), (key1279, 2), (key1702, 2)]

theorem rawRowCheck12645 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form4 = rawRow12645 := by decide +kernel

def row12645 : Integer.Sparse Key := [(key1279, 4), (key1285, 2), (key1702, -8), (key1708, -6), (key1752, 4), (key1758, 4), (key1935, -4), (key1955, 4)]

theorem rowCheck12645 : row12645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12645 := by decide +kernel

theorem rowEval12645 (x : Key → ℝ) : Integer.Sparse.eval row12645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12645, Integer.Sparse.eval_collectBalanced, rawRowCheck12645]

def rawRow12646 : Integer.Sparse Key := [(key1935, -6), (key1708, -6), (key1702, -6), (key1702, -6), (key1955, 2), (key1758, 2), (key1752, 2), (key1955, 2), (key1758, 2), (key1935, 2), (key1285, 2), (key1702, 2), (key1279, 2), (key1752, 2), (key1702, 2), (key1279, 2)]

theorem rawRowCheck12646 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form4 = rawRow12646 := by decide +kernel

def row12646 : Integer.Sparse Key := [(key1279, 4), (key1285, 2), (key1702, -8), (key1708, -6), (key1752, 4), (key1758, 4), (key1935, -4), (key1955, 4)]

theorem rowCheck12646 : row12646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12646 := by decide +kernel

theorem rowEval12646 (x : Key → ℝ) : Integer.Sparse.eval row12646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck12646, Integer.Sparse.eval_collectBalanced, rawRowCheck12646]

def rawRow12647 : Integer.Sparse Key := [(key1752, -6), (key1758, -6), (key1758, -6), (key1955, -6), (key1279, 2), (key1285, 2), (key1285, 2), (key1702, 2), (key1708, 2), (key1702, 2), (key1758, 2), (key1708, 2), (key1758, 2), (key1935, 2), (key1935, 2), (key1955, 2)]

theorem rawRowCheck12647 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form4 = rawRow12647 := by decide +kernel

def row12647 : Integer.Sparse Key := [(key1279, 2), (key1285, 4), (key1702, 4), (key1708, 4), (key1752, -6), (key1758, -8), (key1935, 4), (key1955, -4)]

theorem rowCheck12647 : row12647 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12647 := by decide +kernel

theorem rowEval12647 (x : Key → ℝ) : Integer.Sparse.eval row12647 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12647, Integer.Sparse.eval_collectBalanced, rawRowCheck12647]

def rawRow12648 : Integer.Sparse Key := [(key1758, -6), (key1752, -6), (key1758, -6), (key1955, -6), (key1285, 2), (key1279, 2), (key1285, 2), (key1708, 2), (key1702, 2), (key1758, 2), (key1702, 2), (key1758, 2), (key1708, 2), (key1935, 2), (key1955, 2), (key1935, 2)]

theorem rawRowCheck12648 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form4 = rawRow12648 := by decide +kernel

def row12648 : Integer.Sparse Key := [(key1279, 2), (key1285, 4), (key1702, 4), (key1708, 4), (key1752, -6), (key1758, -8), (key1935, 4), (key1955, -4)]

theorem rowCheck12648 : row12648 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12648 := by decide +kernel

theorem rowEval12648 (x : Key → ℝ) : Integer.Sparse.eval row12648 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12648, Integer.Sparse.eval_collectBalanced, rawRowCheck12648]

def rawRow12649 : Integer.Sparse Key := [(key1758, -6), (key1758, -6), (key1752, -6), (key1955, -6), (key1285, 2), (key1285, 2), (key1279, 2), (key1758, 2), (key1758, 2), (key1708, 2), (key1708, 2), (key1702, 2), (key1702, 2), (key1955, 2), (key1935, 2), (key1935, 2)]

theorem rawRowCheck12649 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form4 = rawRow12649 := by decide +kernel

def row12649 : Integer.Sparse Key := [(key1279, 2), (key1285, 4), (key1702, 4), (key1708, 4), (key1752, -6), (key1758, -8), (key1935, 4), (key1955, -4)]

theorem rowCheck12649 : row12649 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12649 := by decide +kernel

theorem rowEval12649 (x : Key → ℝ) : Integer.Sparse.eval row12649 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12649, Integer.Sparse.eval_collectBalanced, rawRowCheck12649]

def rawRow12650 : Integer.Sparse Key := [(key1752, -6), (key1758, -6), (key1955, -6), (key1758, -6), (key1702, 2), (key1708, 2), (key1935, 2), (key1279, 2), (key1285, 2), (key1702, 2), (key1758, 2), (key1935, 2), (key1955, 2), (key1285, 2), (key1708, 2), (key1758, 2)]

theorem rawRowCheck12650 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form4 = rawRow12650 := by decide +kernel

def row12650 : Integer.Sparse Key := [(key1279, 2), (key1285, 4), (key1702, 4), (key1708, 4), (key1752, -6), (key1758, -8), (key1935, 4), (key1955, -4)]

theorem rowCheck12650 : row12650 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12650 := by decide +kernel

theorem rowEval12650 (x : Key → ℝ) : Integer.Sparse.eval row12650 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12650, Integer.Sparse.eval_collectBalanced, rawRowCheck12650]

def rawRow12651 : Integer.Sparse Key := [(key1758, -6), (key1752, -6), (key1955, -6), (key1758, -6), (key1708, 2), (key1702, 2), (key1935, 2), (key1285, 2), (key1279, 2), (key1758, 2), (key1702, 2), (key1955, 2), (key1935, 2), (key1285, 2), (key1758, 2), (key1708, 2)]

theorem rawRowCheck12651 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form4 = rawRow12651 := by decide +kernel

def row12651 : Integer.Sparse Key := [(key1279, 2), (key1285, 4), (key1702, 4), (key1708, 4), (key1752, -6), (key1758, -8), (key1935, 4), (key1955, -4)]

theorem rowCheck12651 : row12651 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12651 := by decide +kernel

theorem rowEval12651 (x : Key → ℝ) : Integer.Sparse.eval row12651 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12651, Integer.Sparse.eval_collectBalanced, rawRowCheck12651]

def rawRow12652 : Integer.Sparse Key := [(key1752, -6), (key1955, -6), (key1758, -6), (key1758, -6), (key1702, 2), (key1935, 2), (key1708, 2), (key1702, 2), (key1935, 2), (key1279, 2), (key1955, 2), (key1285, 2), (key1758, 2), (key1708, 2), (key1285, 2), (key1758, 2)]

theorem rawRowCheck12652 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form4 = rawRow12652 := by decide +kernel

def row12652 : Integer.Sparse Key := [(key1279, 2), (key1285, 4), (key1702, 4), (key1708, 4), (key1752, -6), (key1758, -8), (key1935, 4), (key1955, -4)]

theorem rowCheck12652 : row12652 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12652 := by decide +kernel

theorem rowEval12652 (x : Key → ℝ) : Integer.Sparse.eval row12652 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12652, Integer.Sparse.eval_collectBalanced, rawRowCheck12652]

def rawRow12653 : Integer.Sparse Key := [(key1955, -6), (key1752, -6), (key1758, -6), (key1758, -6), (key1935, 2), (key1702, 2), (key1708, 2), (key1935, 2), (key1702, 2), (key1955, 2), (key1279, 2), (key1758, 2), (key1285, 2), (key1708, 2), (key1758, 2), (key1285, 2)]

theorem rawRowCheck12653 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form4 = rawRow12653 := by decide +kernel

def row12653 : Integer.Sparse Key := [(key1279, 2), (key1285, 4), (key1702, 4), (key1708, 4), (key1752, -6), (key1758, -8), (key1935, 4), (key1955, -4)]

theorem rowCheck12653 : row12653 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12653 := by decide +kernel

theorem rowEval12653 (x : Key → ℝ) : Integer.Sparse.eval row12653 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck12653, Integer.Sparse.eval_collectBalanced, rawRowCheck12653]

def rawRow12654 : Integer.Sparse Key := [(key1758, -6), (key1955, -6), (key1752, -6), (key1758, -6), (key1708, 2), (key1935, 2), (key1702, 2), (key1758, 2), (key1955, 2), (key1285, 2), (key1935, 2), (key1279, 2), (key1702, 2), (key1758, 2), (key1285, 2), (key1708, 2)]

theorem rawRowCheck12654 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form4 = rawRow12654 := by decide +kernel

def row12654 : Integer.Sparse Key := [(key1279, 2), (key1285, 4), (key1702, 4), (key1708, 4), (key1752, -6), (key1758, -8), (key1935, 4), (key1955, -4)]

theorem rowCheck12654 : row12654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12654 := by decide +kernel

theorem rowEval12654 (x : Key → ℝ) : Integer.Sparse.eval row12654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12654, Integer.Sparse.eval_collectBalanced, rawRowCheck12654]

def rawRow12655 : Integer.Sparse Key := [(key1955, -6), (key1758, -6), (key1752, -6), (key1758, -6), (key1935, 2), (key1708, 2), (key1702, 2), (key1955, 2), (key1758, 2), (key1935, 2), (key1285, 2), (key1702, 2), (key1279, 2), (key1758, 2), (key1708, 2), (key1285, 2)]

theorem rawRowCheck12655 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form4 = rawRow12655 := by decide +kernel

def row12655 : Integer.Sparse Key := [(key1279, 2), (key1285, 4), (key1702, 4), (key1708, 4), (key1752, -6), (key1758, -8), (key1935, 4), (key1955, -4)]

theorem rowCheck12655 : row12655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12655 := by decide +kernel

theorem rowEval12655 (x : Key → ℝ) : Integer.Sparse.eval row12655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck12655, Integer.Sparse.eval_collectBalanced, rawRowCheck12655]

def rawRow12656 : Integer.Sparse Key := [(key1758, -6), (key1758, -6), (key1955, -6), (key1752, -6), (key1758, 2), (key1758, 2), (key1955, 2), (key1285, 2), (key1285, 2), (key1708, 2), (key1708, 2), (key1935, 2), (key1935, 2), (key1279, 2), (key1702, 2), (key1702, 2)]

theorem rawRowCheck12656 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form4 = rawRow12656 := by decide +kernel

def row12656 : Integer.Sparse Key := [(key1279, 2), (key1285, 4), (key1702, 4), (key1708, 4), (key1752, -6), (key1758, -8), (key1935, 4), (key1955, -4)]

theorem rowCheck12656 : row12656 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12656 := by decide +kernel

theorem rowEval12656 (x : Key → ℝ) : Integer.Sparse.eval row12656 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12656, Integer.Sparse.eval_collectBalanced, rawRowCheck12656]

def rawRow12657 : Integer.Sparse Key := [(key1758, -6), (key1955, -6), (key1758, -6), (key1752, -6), (key1758, 2), (key1955, 2), (key1758, 2), (key1708, 2), (key1935, 2), (key1285, 2), (key1935, 2), (key1285, 2), (key1708, 2), (key1702, 2), (key1279, 2), (key1702, 2)]

theorem rawRowCheck12657 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form4 = rawRow12657 := by decide +kernel

def row12657 : Integer.Sparse Key := [(key1279, 2), (key1285, 4), (key1702, 4), (key1708, 4), (key1752, -6), (key1758, -8), (key1935, 4), (key1955, -4)]

theorem rowCheck12657 : row12657 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12657 := by decide +kernel

theorem rowEval12657 (x : Key → ℝ) : Integer.Sparse.eval row12657 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12657, Integer.Sparse.eval_collectBalanced, rawRowCheck12657]

def rawRow12658 : Integer.Sparse Key := [(key1955, -6), (key1758, -6), (key1758, -6), (key1752, -6), (key1955, 2), (key1758, 2), (key1758, 2), (key1935, 2), (key1708, 2), (key1935, 2), (key1285, 2), (key1708, 2), (key1285, 2), (key1702, 2), (key1702, 2), (key1279, 2)]

theorem rawRowCheck12658 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form4 = rawRow12658 := by decide +kernel

def row12658 : Integer.Sparse Key := [(key1279, 2), (key1285, 4), (key1702, 4), (key1708, 4), (key1752, -6), (key1758, -8), (key1935, 4), (key1955, -4)]

theorem rowCheck12658 : row12658 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12658 := by decide +kernel

theorem rowEval12658 (x : Key → ℝ) : Integer.Sparse.eval row12658 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck12658, Integer.Sparse.eval_collectBalanced, rawRowCheck12658]

def rawRow12659 : Integer.Sparse Key := [(key1365, -2), (key1365, -2), (key1371, -2), (key1717, -2), (key1717, -2), (key1742, -2), (key1742, -2), (key1748, -2), (key1748, -2), (key1939, -2), (key1951, -2), (key1951, -2), (key1365, 1), (key1365, 1), (key1375, 1), (key1375, 1), (key1380, 1), (key1380, 1), (key1491, 1), (key1491, 1), (key1514, 1), (key1514, 1), (key1520, 1), (key1520, 1), (key1724, 1), (key1724, 1), (key1742, 1), (key1742, 1), (key1759, 1), (key1759, 1), (key1942, 1), (key1942, 1), (key1951, 1), (key1951, 1), (key1956, 1), (key1956, 1)]

theorem rawRowCheck12659 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form5 = rawRow12659 := by decide +kernel

def row12659 : Integer.Sparse Key := [(key1365, -2), (key1371, -2), (key1375, 2), (key1380, 2), (key1491, 2), (key1514, 2), (key1520, 2), (key1717, -4), (key1724, 2), (key1742, -2), (key1748, -4), (key1759, 2), (key1939, -2), (key1942, 2), (key1951, -2), (key1956, 2)]

theorem rowCheck12659 : row12659 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12659 := by decide +kernel

theorem rowEval12659 (x : Key → ℝ) : Integer.Sparse.eval row12659 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck12659, Integer.Sparse.eval_collectBalanced, rawRowCheck12659]

def rawRow12660 : Integer.Sparse Key := [(key1365, -2), (key1371, -2), (key1365, -2), (key1742, -2), (key1748, -2), (key1717, -2), (key1748, -2), (key1717, -2), (key1742, -2), (key1951, -2), (key1939, -2), (key1951, -2), (key1375, 1), (key1380, 1), (key1365, 1), (key1380, 1), (key1365, 1), (key1375, 1), (key1514, 1), (key1520, 1), (key1491, 1), (key1520, 1), (key1491, 1), (key1514, 1), (key1742, 1), (key1759, 1), (key1724, 1), (key1759, 1), (key1724, 1), (key1742, 1), (key1951, 1), (key1956, 1), (key1942, 1), (key1956, 1), (key1942, 1), (key1951, 1)]

theorem rawRowCheck12660 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form5 = rawRow12660 := by decide +kernel

def row12660 : Integer.Sparse Key := [(key1365, -2), (key1371, -2), (key1375, 2), (key1380, 2), (key1491, 2), (key1514, 2), (key1520, 2), (key1717, -4), (key1724, 2), (key1742, -2), (key1748, -4), (key1759, 2), (key1939, -2), (key1942, 2), (key1951, -2), (key1956, 2)]

theorem rowCheck12660 : row12660 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12660 := by decide +kernel

theorem rowEval12660 (x : Key → ℝ) : Integer.Sparse.eval row12660 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck12660, Integer.Sparse.eval_collectBalanced, rawRowCheck12660]

def rawRow12661 : Integer.Sparse Key := [(key1371, -2), (key1365, -2), (key1365, -2), (key1748, -2), (key1742, -2), (key1748, -2), (key1717, -2), (key1742, -2), (key1717, -2), (key1951, -2), (key1951, -2), (key1939, -2), (key1380, 1), (key1375, 1), (key1380, 1), (key1365, 1), (key1375, 1), (key1365, 1), (key1520, 1), (key1514, 1), (key1520, 1), (key1491, 1), (key1514, 1), (key1491, 1), (key1759, 1), (key1742, 1), (key1759, 1), (key1724, 1), (key1742, 1), (key1724, 1), (key1956, 1), (key1951, 1), (key1956, 1), (key1942, 1), (key1951, 1), (key1942, 1)]

theorem rawRowCheck12661 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form5 = rawRow12661 := by decide +kernel

def row12661 : Integer.Sparse Key := [(key1365, -2), (key1371, -2), (key1375, 2), (key1380, 2), (key1491, 2), (key1514, 2), (key1520, 2), (key1717, -4), (key1724, 2), (key1742, -2), (key1748, -4), (key1759, 2), (key1939, -2), (key1942, 2), (key1951, -2), (key1956, 2)]

theorem rowCheck12661 : row12661 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12661 := by decide +kernel

theorem rowEval12661 (x : Key → ℝ) : Integer.Sparse.eval row12661 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck12661, Integer.Sparse.eval_collectBalanced, rawRowCheck12661]

def rawRow12662 : Integer.Sparse Key := [(key1717, -2), (key1717, -2), (key1939, -2), (key1365, -2), (key1365, -2), (key1742, -2), (key1742, -2), (key1951, -2), (key1951, -2), (key1371, -2), (key1748, -2), (key1748, -2), (key1491, 1), (key1491, 1), (key1724, 1), (key1724, 1), (key1942, 1), (key1942, 1), (key1365, 1), (key1365, 1), (key1742, 1), (key1742, 1), (key1951, 1), (key1951, 1), (key1375, 1), (key1375, 1), (key1514, 1), (key1514, 1), (key1956, 1), (key1956, 1), (key1380, 1), (key1380, 1), (key1520, 1), (key1520, 1), (key1759, 1), (key1759, 1)]

theorem rawRowCheck12662 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form5 = rawRow12662 := by decide +kernel

def row12662 : Integer.Sparse Key := [(key1365, -2), (key1371, -2), (key1375, 2), (key1380, 2), (key1491, 2), (key1514, 2), (key1520, 2), (key1717, -4), (key1724, 2), (key1742, -2), (key1748, -4), (key1759, 2), (key1939, -2), (key1942, 2), (key1951, -2), (key1956, 2)]

theorem rowCheck12662 : row12662 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12662 := by decide +kernel

theorem rowEval12662 (x : Key → ℝ) : Integer.Sparse.eval row12662 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck12662, Integer.Sparse.eval_collectBalanced, rawRowCheck12662]

def rawRow12663 : Integer.Sparse Key := [(key1717, -2), (key1939, -2), (key1717, -2), (key1742, -2), (key1951, -2), (key1365, -2), (key1951, -2), (key1365, -2), (key1742, -2), (key1748, -2), (key1371, -2), (key1748, -2), (key1724, 1), (key1942, 1), (key1491, 1), (key1942, 1), (key1491, 1), (key1724, 1), (key1742, 1), (key1951, 1), (key1365, 1), (key1951, 1), (key1365, 1), (key1742, 1), (key1514, 1), (key1956, 1), (key1375, 1), (key1956, 1), (key1375, 1), (key1514, 1), (key1520, 1), (key1759, 1), (key1380, 1), (key1759, 1), (key1380, 1), (key1520, 1)]

theorem rawRowCheck12663 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form5 = rawRow12663 := by decide +kernel

def row12663 : Integer.Sparse Key := [(key1365, -2), (key1371, -2), (key1375, 2), (key1380, 2), (key1491, 2), (key1514, 2), (key1520, 2), (key1717, -4), (key1724, 2), (key1742, -2), (key1748, -4), (key1759, 2), (key1939, -2), (key1942, 2), (key1951, -2), (key1956, 2)]

theorem rowCheck12663 : row12663 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12663 := by decide +kernel

theorem rowEval12663 (x : Key → ℝ) : Integer.Sparse.eval row12663 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck12663, Integer.Sparse.eval_collectBalanced, rawRowCheck12663]

def rawRow12664 : Integer.Sparse Key := [(key1939, -2), (key1717, -2), (key1717, -2), (key1951, -2), (key1742, -2), (key1951, -2), (key1365, -2), (key1742, -2), (key1365, -2), (key1748, -2), (key1748, -2), (key1371, -2), (key1942, 1), (key1724, 1), (key1942, 1), (key1491, 1), (key1724, 1), (key1491, 1), (key1951, 1), (key1742, 1), (key1951, 1), (key1365, 1), (key1742, 1), (key1365, 1), (key1956, 1), (key1514, 1), (key1956, 1), (key1375, 1), (key1514, 1), (key1375, 1), (key1759, 1), (key1520, 1), (key1759, 1), (key1380, 1), (key1520, 1), (key1380, 1)]

theorem rawRowCheck12664 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form5 = rawRow12664 := by decide +kernel

def row12664 : Integer.Sparse Key := [(key1365, -2), (key1371, -2), (key1375, 2), (key1380, 2), (key1491, 2), (key1514, 2), (key1520, 2), (key1717, -4), (key1724, 2), (key1742, -2), (key1748, -4), (key1759, 2), (key1939, -2), (key1942, 2), (key1951, -2), (key1956, 2)]

theorem rowCheck12664 : row12664 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12664 := by decide +kernel

theorem rowEval12664 (x : Key → ℝ) : Integer.Sparse.eval row12664 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck12664, Integer.Sparse.eval_collectBalanced, rawRowCheck12664]

def rawRow12665 : Integer.Sparse Key := [(key1742, -2), (key1748, -2), (key1951, -2), (key1365, -2), (key1371, -2), (key1717, -2), (key1748, -2), (key1939, -2), (key1951, -2), (key1365, -2), (key1717, -2), (key1742, -2), (key1514, 1), (key1520, 1), (key1742, 1), (key1759, 1), (key1951, 1), (key1956, 1), (key1375, 1), (key1380, 1), (key1724, 1), (key1759, 1), (key1942, 1), (key1956, 1), (key1365, 1), (key1380, 1), (key1491, 1), (key1520, 1), (key1942, 1), (key1951, 1), (key1365, 1), (key1375, 1), (key1491, 1), (key1514, 1), (key1724, 1), (key1742, 1)]

theorem rawRowCheck12665 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form5 = rawRow12665 := by decide +kernel

def row12665 : Integer.Sparse Key := [(key1365, -2), (key1371, -2), (key1375, 2), (key1380, 2), (key1491, 2), (key1514, 2), (key1520, 2), (key1717, -4), (key1724, 2), (key1742, -2), (key1748, -4), (key1759, 2), (key1939, -2), (key1942, 2), (key1951, -2), (key1956, 2)]

theorem rowCheck12665 : row12665 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12665 := by decide +kernel

theorem rowEval12665 (x : Key → ℝ) : Integer.Sparse.eval row12665 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck12665, Integer.Sparse.eval_collectBalanced, rawRowCheck12665]

def rawRow12666 : Integer.Sparse Key := [(key1748, -2), (key1742, -2), (key1951, -2), (key1371, -2), (key1365, -2), (key1748, -2), (key1717, -2), (key1951, -2), (key1939, -2), (key1365, -2), (key1742, -2), (key1717, -2), (key1520, 1), (key1514, 1), (key1759, 1), (key1742, 1), (key1956, 1), (key1951, 1), (key1380, 1), (key1375, 1), (key1759, 1), (key1724, 1), (key1956, 1), (key1942, 1), (key1380, 1), (key1365, 1), (key1520, 1), (key1491, 1), (key1951, 1), (key1942, 1), (key1375, 1), (key1365, 1), (key1514, 1), (key1491, 1), (key1742, 1), (key1724, 1)]

theorem rawRowCheck12666 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form5 = rawRow12666 := by decide +kernel

def row12666 : Integer.Sparse Key := [(key1365, -2), (key1371, -2), (key1375, 2), (key1380, 2), (key1491, 2), (key1514, 2), (key1520, 2), (key1717, -4), (key1724, 2), (key1742, -2), (key1748, -4), (key1759, 2), (key1939, -2), (key1942, 2), (key1951, -2), (key1956, 2)]

theorem rowCheck12666 : row12666 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12666 := by decide +kernel

theorem rowEval12666 (x : Key → ℝ) : Integer.Sparse.eval row12666 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck12666, Integer.Sparse.eval_collectBalanced, rawRowCheck12666]

def rawRow12667 : Integer.Sparse Key := [(key1742, -2), (key1951, -2), (key1748, -2), (key1717, -2), (key1939, -2), (key1365, -2), (key1951, -2), (key1371, -2), (key1748, -2), (key1717, -2), (key1365, -2), (key1742, -2), (key1742, 1), (key1951, 1), (key1514, 1), (key1956, 1), (key1520, 1), (key1759, 1), (key1724, 1), (key1942, 1), (key1375, 1), (key1956, 1), (key1380, 1), (key1759, 1), (key1491, 1), (key1942, 1), (key1365, 1), (key1951, 1), (key1380, 1), (key1520, 1), (key1491, 1), (key1724, 1), (key1365, 1), (key1742, 1), (key1375, 1), (key1514, 1)]

theorem rawRowCheck12667 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form5 = rawRow12667 := by decide +kernel

def row12667 : Integer.Sparse Key := [(key1365, -2), (key1371, -2), (key1375, 2), (key1380, 2), (key1491, 2), (key1514, 2), (key1520, 2), (key1717, -4), (key1724, 2), (key1742, -2), (key1748, -4), (key1759, 2), (key1939, -2), (key1942, 2), (key1951, -2), (key1956, 2)]

theorem rowCheck12667 : row12667 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12667 := by decide +kernel

theorem rowEval12667 (x : Key → ℝ) : Integer.Sparse.eval row12667 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck12667, Integer.Sparse.eval_collectBalanced, rawRowCheck12667]

def rawRow12668 : Integer.Sparse Key := [(key1951, -2), (key1742, -2), (key1748, -2), (key1939, -2), (key1717, -2), (key1951, -2), (key1365, -2), (key1748, -2), (key1371, -2), (key1717, -2), (key1742, -2), (key1365, -2), (key1951, 1), (key1742, 1), (key1956, 1), (key1514, 1), (key1759, 1), (key1520, 1), (key1942, 1), (key1724, 1), (key1956, 1), (key1375, 1), (key1759, 1), (key1380, 1), (key1942, 1), (key1491, 1), (key1951, 1), (key1365, 1), (key1520, 1), (key1380, 1), (key1724, 1), (key1491, 1), (key1742, 1), (key1365, 1), (key1514, 1), (key1375, 1)]

theorem rawRowCheck12668 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form5 = rawRow12668 := by decide +kernel

def row12668 : Integer.Sparse Key := [(key1365, -2), (key1371, -2), (key1375, 2), (key1380, 2), (key1491, 2), (key1514, 2), (key1520, 2), (key1717, -4), (key1724, 2), (key1742, -2), (key1748, -4), (key1759, 2), (key1939, -2), (key1942, 2), (key1951, -2), (key1956, 2)]

theorem rowCheck12668 : row12668 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12668 := by decide +kernel

theorem rowEval12668 (x : Key → ℝ) : Integer.Sparse.eval row12668 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck12668, Integer.Sparse.eval_collectBalanced, rawRowCheck12668]

def rawRow12669 : Integer.Sparse Key := [(key1748, -2), (key1951, -2), (key1742, -2), (key1748, -2), (key1951, -2), (key1371, -2), (key1939, -2), (key1365, -2), (key1717, -2), (key1742, -2), (key1365, -2), (key1717, -2), (key1759, 1), (key1956, 1), (key1520, 1), (key1951, 1), (key1514, 1), (key1742, 1), (key1759, 1), (key1956, 1), (key1380, 1), (key1942, 1), (key1375, 1), (key1724, 1), (key1520, 1), (key1951, 1), (key1380, 1), (key1942, 1), (key1365, 1), (key1491, 1), (key1514, 1), (key1742, 1), (key1375, 1), (key1724, 1), (key1365, 1), (key1491, 1)]

theorem rawRowCheck12669 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form5 = rawRow12669 := by decide +kernel

def row12669 : Integer.Sparse Key := [(key1365, -2), (key1371, -2), (key1375, 2), (key1380, 2), (key1491, 2), (key1514, 2), (key1520, 2), (key1717, -4), (key1724, 2), (key1742, -2), (key1748, -4), (key1759, 2), (key1939, -2), (key1942, 2), (key1951, -2), (key1956, 2)]

theorem rowCheck12669 : row12669 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12669 := by decide +kernel

theorem rowEval12669 (x : Key → ℝ) : Integer.Sparse.eval row12669 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck12669, Integer.Sparse.eval_collectBalanced, rawRowCheck12669]

def rawRow12670 : Integer.Sparse Key := [(key1951, -2), (key1748, -2), (key1742, -2), (key1951, -2), (key1748, -2), (key1939, -2), (key1371, -2), (key1717, -2), (key1365, -2), (key1742, -2), (key1717, -2), (key1365, -2), (key1956, 1), (key1759, 1), (key1951, 1), (key1520, 1), (key1742, 1), (key1514, 1), (key1956, 1), (key1759, 1), (key1942, 1), (key1380, 1), (key1724, 1), (key1375, 1), (key1951, 1), (key1520, 1), (key1942, 1), (key1380, 1), (key1491, 1), (key1365, 1), (key1742, 1), (key1514, 1), (key1724, 1), (key1375, 1), (key1491, 1), (key1365, 1)]

theorem rawRowCheck12670 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form5 = rawRow12670 := by decide +kernel

def row12670 : Integer.Sparse Key := [(key1365, -2), (key1371, -2), (key1375, 2), (key1380, 2), (key1491, 2), (key1514, 2), (key1520, 2), (key1717, -4), (key1724, 2), (key1742, -2), (key1748, -4), (key1759, 2), (key1939, -2), (key1942, 2), (key1951, -2), (key1956, 2)]

theorem rowCheck12670 : row12670 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12670 := by decide +kernel

theorem rowEval12670 (x : Key → ℝ) : Integer.Sparse.eval row12670 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck12670, Integer.Sparse.eval_collectBalanced, rawRowCheck12670]

def rawRow12671 : Integer.Sparse Key := [(key1375, -2), (key1380, -2), (key1380, -2), (key1724, -2), (key1729, -2), (key1724, -2), (key1759, -2), (key1729, -2), (key1759, -2), (key1942, -2), (key1942, -2), (key1956, -2), (key1365, 1), (key1371, 1), (key1365, 1), (key1380, 1), (key1371, 1), (key1380, 1), (key1491, 1), (key1497, 1), (key1491, 1), (key1520, 1), (key1497, 1), (key1520, 1), (key1717, 1), (key1729, 1), (key1717, 1), (key1748, 1), (key1729, 1), (key1748, 1), (key1939, 1), (key1942, 1), (key1939, 1), (key1951, 1), (key1942, 1), (key1951, 1)]

theorem rawRowCheck12671 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form5 = rawRow12671 := by decide +kernel

def row12671 : Integer.Sparse Key := [(key1365, 2), (key1371, 2), (key1375, -2), (key1380, -2), (key1491, 2), (key1497, 2), (key1520, 2), (key1717, 2), (key1724, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1939, 2), (key1942, -2), (key1951, 2), (key1956, -2)]

theorem rowCheck12671 : row12671 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12671 := by decide +kernel

theorem rowEval12671 (x : Key → ℝ) : Integer.Sparse.eval row12671 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck12671, Integer.Sparse.eval_collectBalanced, rawRowCheck12671]

end MUB6.Certificate.GramRows

end OAI
