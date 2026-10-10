import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block6
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block17
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow17536 : Integer.Sparse Key := [(key1858, 2), (key1856, 2), (key1856, 2), (key1856, -2), (key1856, -2), (key1854, -2), (key1890, 2), (key1887, 2), (key1887, 2), (key1887, -1), (key1887, -1), (key1856, -1), (key1856, -1), (key1854, -1), (key1854, -1), (key1890, -2), (key1890, -2), (key1887, -2), (key1890, -1), (key1890, -1), (key1858, -1), (key1858, -1), (key1856, -1), (key1856, -1), (key1887, 4), (key1856, 4), (key1856, 4)]

theorem rawRowCheck17536 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form12 = rawRow17536 := by decide +kernel

def row17536 : Integer.Sparse Key := [(key1854, -4), (key1856, 4), (key1887, 4), (key1890, -4)]

theorem rowCheck17536 : row17536 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17536 := by decide +kernel

theorem rowEval17536 (x : Key → ℝ) : Integer.Sparse.eval row17536 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck17536, Integer.Sparse.eval_collectBalanced, rawRowCheck17536]

def rawRow17537 : Integer.Sparse Key := [(key1887, 2), (key1887, 2), (key1890, 2), (key1887, -2), (key1890, -2), (key1890, -2), (key1856, 2), (key1856, 2), (key1858, 2), (key1856, -1), (key1858, -1), (key1856, -1), (key1890, -1), (key1858, -1), (key1890, -1), (key1854, -2), (key1856, -2), (key1856, -2), (key1854, -1), (key1856, -1), (key1854, -1), (key1887, -1), (key1856, -1), (key1887, -1), (key1856, 4), (key1856, 4), (key1887, 4)]

theorem rawRowCheck17537 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form12 = rawRow17537 := by decide +kernel

def row17537 : Integer.Sparse Key := [(key1854, -4), (key1856, 4), (key1887, 4), (key1890, -4)]

theorem rowCheck17537 : row17537 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17537 := by decide +kernel

theorem rowEval17537 (x : Key → ℝ) : Integer.Sparse.eval row17537 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck17537, Integer.Sparse.eval_collectBalanced, rawRowCheck17537]

def rawRow17538 : Integer.Sparse Key := [(key1887, 2), (key1890, 2), (key1887, 2), (key1890, -2), (key1887, -2), (key1890, -2), (key1856, 2), (key1858, 2), (key1856, 2), (key1858, -1), (key1856, -1), (key1890, -1), (key1856, -1), (key1890, -1), (key1858, -1), (key1856, -2), (key1854, -2), (key1856, -2), (key1856, -1), (key1854, -1), (key1887, -1), (key1854, -1), (key1887, -1), (key1856, -1), (key1856, 4), (key1887, 4), (key1856, 4)]

theorem rawRowCheck17538 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form12 = rawRow17538 := by decide +kernel

def row17538 : Integer.Sparse Key := [(key1854, -4), (key1856, 4), (key1887, 4), (key1890, -4)]

theorem rowCheck17538 : row17538 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17538 := by decide +kernel

theorem rowEval17538 (x : Key → ℝ) : Integer.Sparse.eval row17538 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck17538, Integer.Sparse.eval_collectBalanced, rawRowCheck17538]

def rawRow17539 : Integer.Sparse Key := [(key1890, 2), (key1887, 2), (key1887, 2), (key1890, -2), (key1890, -2), (key1887, -2), (key1858, 2), (key1856, 2), (key1856, 2), (key1890, -1), (key1890, -1), (key1858, -1), (key1858, -1), (key1856, -1), (key1856, -1), (key1856, -2), (key1856, -2), (key1854, -2), (key1887, -1), (key1887, -1), (key1856, -1), (key1856, -1), (key1854, -1), (key1854, -1), (key1887, 4), (key1856, 4), (key1856, 4)]

theorem rawRowCheck17539 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form12 = rawRow17539 := by decide +kernel

def row17539 : Integer.Sparse Key := [(key1854, -4), (key1856, 4), (key1887, 4), (key1890, -4)]

theorem rowCheck17539 : row17539 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17539 := by decide +kernel

theorem rowEval17539 (x : Key → ℝ) : Integer.Sparse.eval row17539 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck17539, Integer.Sparse.eval_collectBalanced, rawRowCheck17539]

def rawRow17540 : Integer.Sparse Key := [(key1890, 2), (key1890, 2), (key1890, 2), (key1887, -2), (key1887, -2), (key1887, -2), (key1890, 2), (key1890, 2), (key1890, 2), (key1856, -1), (key1856, -1), (key1856, -1), (key1856, -1), (key1856, -1), (key1856, -1), (key1887, -2), (key1887, -2), (key1887, -2), (key1856, -1), (key1856, -1), (key1856, -1), (key1856, -1), (key1856, -1), (key1856, -1), (key1854, 4), (key1854, 4), (key1854, 4)]

theorem rawRowCheck17540 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form12 = rawRow17540 := by decide +kernel

def row17540 : Integer.Sparse Key := [(key1854, 12), (key1856, -12), (key1887, -12), (key1890, 12)]

theorem rowCheck17540 : row17540 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17540 := by decide +kernel

theorem rowEval17540 (x : Key → ℝ) : Integer.Sparse.eval row17540 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck17540, Integer.Sparse.eval_collectBalanced, rawRowCheck17540]

def rawRow17541 : Integer.Sparse Key := [(key1862, 2), (key1862, 2), (key1866, 2), (key1862, -1), (key1862, -1), (key1868, -1), (key1868, -1), (key1871, -1), (key1871, -1), (key1862, 2), (key1862, 2), (key1866, 2), (key1862, -1), (key1862, -1), (key1878, -1), (key1878, -1), (key1881, -1), (key1881, -1), (key1862, -1), (key1862, -1), (key1868, -1), (key1868, -1), (key1871, -1), (key1871, -1), (key1862, -1), (key1862, -1), (key1878, -1), (key1878, -1), (key1881, -1), (key1881, -1), (key1868, 2), (key1868, 2), (key1878, 2), (key1878, 2), (key1889, 2), (key1889, 2)]

theorem rawRowCheck17541 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form13 = rawRow17541 := by decide +kernel

def row17541 : Integer.Sparse Key := [(key1866, 4), (key1871, -4), (key1881, -4), (key1889, 4)]

theorem rowCheck17541 : row17541 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17541 := by decide +kernel

theorem rowEval17541 (x : Key → ℝ) : Integer.Sparse.eval row17541 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form13) x := by
  rw [rowCheck17541, Integer.Sparse.eval_collectBalanced, rawRowCheck17541]

def rawRow17542 : Integer.Sparse Key := [(key1862, 2), (key1866, 2), (key1862, 2), (key1868, -1), (key1871, -1), (key1862, -1), (key1871, -1), (key1862, -1), (key1868, -1), (key1862, 2), (key1866, 2), (key1862, 2), (key1878, -1), (key1881, -1), (key1862, -1), (key1881, -1), (key1862, -1), (key1878, -1), (key1868, -1), (key1871, -1), (key1862, -1), (key1871, -1), (key1862, -1), (key1868, -1), (key1878, -1), (key1881, -1), (key1862, -1), (key1881, -1), (key1862, -1), (key1878, -1), (key1878, 2), (key1889, 2), (key1868, 2), (key1889, 2), (key1868, 2), (key1878, 2)]

theorem rawRowCheck17542 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form13 = rawRow17542 := by decide +kernel

def row17542 : Integer.Sparse Key := [(key1866, 4), (key1871, -4), (key1881, -4), (key1889, 4)]

theorem rowCheck17542 : row17542 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17542 := by decide +kernel

theorem rowEval17542 (x : Key → ℝ) : Integer.Sparse.eval row17542 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form13) x := by
  rw [rowCheck17542, Integer.Sparse.eval_collectBalanced, rawRowCheck17542]

def rawRow17543 : Integer.Sparse Key := [(key1866, 2), (key1862, 2), (key1862, 2), (key1871, -1), (key1868, -1), (key1871, -1), (key1862, -1), (key1868, -1), (key1862, -1), (key1866, 2), (key1862, 2), (key1862, 2), (key1881, -1), (key1878, -1), (key1881, -1), (key1862, -1), (key1878, -1), (key1862, -1), (key1871, -1), (key1868, -1), (key1871, -1), (key1862, -1), (key1868, -1), (key1862, -1), (key1881, -1), (key1878, -1), (key1881, -1), (key1862, -1), (key1878, -1), (key1862, -1), (key1889, 2), (key1878, 2), (key1889, 2), (key1868, 2), (key1878, 2), (key1868, 2)]

theorem rawRowCheck17543 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form13 = rawRow17543 := by decide +kernel

def row17543 : Integer.Sparse Key := [(key1866, 4), (key1871, -4), (key1881, -4), (key1889, 4)]

theorem rowCheck17543 : row17543 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17543 := by decide +kernel

theorem rowEval17543 (x : Key → ℝ) : Integer.Sparse.eval row17543 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck17543, Integer.Sparse.eval_collectBalanced, rawRowCheck17543]

def rawRow17544 : Integer.Sparse Key := [(key1868, 2), (key1871, 2), (key1871, 2), (key1862, -1), (key1866, -1), (key1862, -1), (key1871, -1), (key1866, -1), (key1871, -1), (key1878, 2), (key1881, 2), (key1881, 2), (key1862, -1), (key1866, -1), (key1862, -1), (key1881, -1), (key1866, -1), (key1881, -1), (key1878, -1), (key1881, -1), (key1878, -1), (key1889, -1), (key1881, -1), (key1889, -1), (key1868, -1), (key1871, -1), (key1868, -1), (key1889, -1), (key1871, -1), (key1889, -1), (key1862, 2), (key1871, 2), (key1862, 2), (key1881, 2), (key1871, 2), (key1881, 2)]

theorem rawRowCheck17544 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form13 = rawRow17544 := by decide +kernel

def row17544 : Integer.Sparse Key := [(key1866, -4), (key1871, 4), (key1881, 4), (key1889, -4)]

theorem rowCheck17544 : row17544 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17544 := by decide +kernel

theorem rowEval17544 (x : Key → ℝ) : Integer.Sparse.eval row17544 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form13) x := by
  rw [rowCheck17544, Integer.Sparse.eval_collectBalanced, rawRowCheck17544]

def rawRow17545 : Integer.Sparse Key := [(key1871, 2), (key1868, 2), (key1871, 2), (key1866, -1), (key1862, -1), (key1871, -1), (key1862, -1), (key1871, -1), (key1866, -1), (key1881, 2), (key1878, 2), (key1881, 2), (key1866, -1), (key1862, -1), (key1881, -1), (key1862, -1), (key1881, -1), (key1866, -1), (key1881, -1), (key1878, -1), (key1889, -1), (key1878, -1), (key1889, -1), (key1881, -1), (key1871, -1), (key1868, -1), (key1889, -1), (key1868, -1), (key1889, -1), (key1871, -1), (key1871, 2), (key1862, 2), (key1881, 2), (key1862, 2), (key1881, 2), (key1871, 2)]

theorem rawRowCheck17545 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form13 = rawRow17545 := by decide +kernel

def row17545 : Integer.Sparse Key := [(key1866, -4), (key1871, 4), (key1881, 4), (key1889, -4)]

theorem rowCheck17545 : row17545 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17545 := by decide +kernel

theorem rowEval17545 (x : Key → ℝ) : Integer.Sparse.eval row17545 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck17545, Integer.Sparse.eval_collectBalanced, rawRowCheck17545]

def rawRow17546 : Integer.Sparse Key := [(key1871, 2), (key1871, 2), (key1868, 2), (key1871, -1), (key1871, -1), (key1866, -1), (key1866, -1), (key1862, -1), (key1862, -1), (key1881, 2), (key1881, 2), (key1878, 2), (key1881, -1), (key1881, -1), (key1866, -1), (key1866, -1), (key1862, -1), (key1862, -1), (key1889, -1), (key1889, -1), (key1881, -1), (key1881, -1), (key1878, -1), (key1878, -1), (key1889, -1), (key1889, -1), (key1871, -1), (key1871, -1), (key1868, -1), (key1868, -1), (key1881, 2), (key1881, 2), (key1871, 2), (key1871, 2), (key1862, 2), (key1862, 2)]

theorem rawRowCheck17546 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form13 = rawRow17546 := by decide +kernel

def row17546 : Integer.Sparse Key := [(key1866, -4), (key1871, 4), (key1881, 4), (key1889, -4)]

theorem rowCheck17546 : row17546 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17546 := by decide +kernel

theorem rowEval17546 (x : Key → ℝ) : Integer.Sparse.eval row17546 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck17546, Integer.Sparse.eval_collectBalanced, rawRowCheck17546]

def rawRow17547 : Integer.Sparse Key := [(key1878, 2), (key1881, 2), (key1881, 2), (key1878, -1), (key1881, -1), (key1878, -1), (key1889, -1), (key1881, -1), (key1889, -1), (key1868, 2), (key1871, 2), (key1871, 2), (key1868, -1), (key1871, -1), (key1868, -1), (key1889, -1), (key1871, -1), (key1889, -1), (key1862, -1), (key1866, -1), (key1862, -1), (key1871, -1), (key1866, -1), (key1871, -1), (key1862, -1), (key1866, -1), (key1862, -1), (key1881, -1), (key1866, -1), (key1881, -1), (key1862, 2), (key1871, 2), (key1862, 2), (key1881, 2), (key1871, 2), (key1881, 2)]

theorem rawRowCheck17547 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form13 = rawRow17547 := by decide +kernel

def row17547 : Integer.Sparse Key := [(key1866, -4), (key1871, 4), (key1881, 4), (key1889, -4)]

theorem rowCheck17547 : row17547 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17547 := by decide +kernel

theorem rowEval17547 (x : Key → ℝ) : Integer.Sparse.eval row17547 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form13) x := by
  rw [rowCheck17547, Integer.Sparse.eval_collectBalanced, rawRowCheck17547]

def rawRow17548 : Integer.Sparse Key := [(key1881, 2), (key1878, 2), (key1881, 2), (key1881, -1), (key1878, -1), (key1889, -1), (key1878, -1), (key1889, -1), (key1881, -1), (key1871, 2), (key1868, 2), (key1871, 2), (key1871, -1), (key1868, -1), (key1889, -1), (key1868, -1), (key1889, -1), (key1871, -1), (key1866, -1), (key1862, -1), (key1871, -1), (key1862, -1), (key1871, -1), (key1866, -1), (key1866, -1), (key1862, -1), (key1881, -1), (key1862, -1), (key1881, -1), (key1866, -1), (key1871, 2), (key1862, 2), (key1881, 2), (key1862, 2), (key1881, 2), (key1871, 2)]

theorem rawRowCheck17548 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form13 = rawRow17548 := by decide +kernel

def row17548 : Integer.Sparse Key := [(key1866, -4), (key1871, 4), (key1881, 4), (key1889, -4)]

theorem rowCheck17548 : row17548 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17548 := by decide +kernel

theorem rowEval17548 (x : Key → ℝ) : Integer.Sparse.eval row17548 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck17548, Integer.Sparse.eval_collectBalanced, rawRowCheck17548]

def rawRow17549 : Integer.Sparse Key := [(key1881, 2), (key1881, 2), (key1878, 2), (key1889, -1), (key1889, -1), (key1881, -1), (key1881, -1), (key1878, -1), (key1878, -1), (key1871, 2), (key1871, 2), (key1868, 2), (key1889, -1), (key1889, -1), (key1871, -1), (key1871, -1), (key1868, -1), (key1868, -1), (key1871, -1), (key1871, -1), (key1866, -1), (key1866, -1), (key1862, -1), (key1862, -1), (key1881, -1), (key1881, -1), (key1866, -1), (key1866, -1), (key1862, -1), (key1862, -1), (key1881, 2), (key1881, 2), (key1871, 2), (key1871, 2), (key1862, 2), (key1862, 2)]

theorem rawRowCheck17549 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form13 = rawRow17549 := by decide +kernel

def row17549 : Integer.Sparse Key := [(key1866, -4), (key1871, 4), (key1881, 4), (key1889, -4)]

theorem rowCheck17549 : row17549 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17549 := by decide +kernel

theorem rowEval17549 (x : Key → ℝ) : Integer.Sparse.eval row17549 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck17549, Integer.Sparse.eval_collectBalanced, rawRowCheck17549]

def rawRow17550 : Integer.Sparse Key := [(key1889, 2), (key1889, 2), (key1889, 2), (key1881, -1), (key1881, -1), (key1881, -1), (key1881, -1), (key1881, -1), (key1881, -1), (key1889, 2), (key1889, 2), (key1889, 2), (key1871, -1), (key1871, -1), (key1871, -1), (key1871, -1), (key1871, -1), (key1871, -1), (key1881, -1), (key1881, -1), (key1881, -1), (key1881, -1), (key1881, -1), (key1881, -1), (key1871, -1), (key1871, -1), (key1871, -1), (key1871, -1), (key1871, -1), (key1871, -1), (key1866, 2), (key1866, 2), (key1866, 2), (key1866, 2), (key1866, 2), (key1866, 2)]

theorem rawRowCheck17550 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form13 = rawRow17550 := by decide +kernel

def row17550 : Integer.Sparse Key := [(key1866, 12), (key1871, -12), (key1881, -12), (key1889, 12)]

theorem rowCheck17550 : row17550 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17550 := by decide +kernel

theorem rowEval17550 (x : Key → ℝ) : Integer.Sparse.eval row17550 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck17550, Integer.Sparse.eval_collectBalanced, rawRowCheck17550]

def rawRow17551 : Integer.Sparse Key := [(key1862, -1), (key1862, -1), (key1868, -1), (key1868, -1), (key1871, -1), (key1871, -1), (key1866, 2), (key1871, 2), (key1871, 2), (key1862, 1), (key1862, 1), (key1878, 1), (key1878, 1), (key1881, 1), (key1881, 1), (key1866, -2), (key1881, -2), (key1881, -2), (key1862, -1), (key1862, -1), (key1868, -1), (key1868, -1), (key1871, -1), (key1871, -1), (key1862, 1), (key1862, 1), (key1878, 1), (key1878, 1), (key1881, 1), (key1881, 1), (key1866, 2), (key1871, 2), (key1871, 2), (key1866, -2), (key1881, -2), (key1881, -2)]

theorem rawRowCheck17551 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form14 = rawRow17551 := by decide +kernel

def row17551 : Integer.Sparse Key := [(key1868, -4), (key1871, 4), (key1878, 4), (key1881, -4)]

theorem rowCheck17551 : row17551 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17551 := by decide +kernel

theorem rowEval17551 (x : Key → ℝ) : Integer.Sparse.eval row17551 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form14) x := by
  rw [rowCheck17551, Integer.Sparse.eval_collectBalanced, rawRowCheck17551]

def rawRow17552 : Integer.Sparse Key := [(key1868, -1), (key1871, -1), (key1862, -1), (key1871, -1), (key1862, -1), (key1868, -1), (key1871, 2), (key1866, 2), (key1871, 2), (key1878, 1), (key1881, 1), (key1862, 1), (key1881, 1), (key1862, 1), (key1878, 1), (key1881, -2), (key1866, -2), (key1881, -2), (key1868, -1), (key1871, -1), (key1862, -1), (key1871, -1), (key1862, -1), (key1868, -1), (key1878, 1), (key1881, 1), (key1862, 1), (key1881, 1), (key1862, 1), (key1878, 1), (key1871, 2), (key1866, 2), (key1871, 2), (key1881, -2), (key1866, -2), (key1881, -2)]

theorem rawRowCheck17552 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form14 = rawRow17552 := by decide +kernel

def row17552 : Integer.Sparse Key := [(key1868, -4), (key1871, 4), (key1878, 4), (key1881, -4)]

theorem rowCheck17552 : row17552 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17552 := by decide +kernel

theorem rowEval17552 (x : Key → ℝ) : Integer.Sparse.eval row17552 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form14) x := by
  rw [rowCheck17552, Integer.Sparse.eval_collectBalanced, rawRowCheck17552]

def rawRow17553 : Integer.Sparse Key := [(key1871, -1), (key1868, -1), (key1871, -1), (key1862, -1), (key1868, -1), (key1862, -1), (key1871, 2), (key1871, 2), (key1866, 2), (key1881, 1), (key1878, 1), (key1881, 1), (key1862, 1), (key1878, 1), (key1862, 1), (key1881, -2), (key1881, -2), (key1866, -2), (key1871, -1), (key1868, -1), (key1871, -1), (key1862, -1), (key1868, -1), (key1862, -1), (key1881, 1), (key1878, 1), (key1881, 1), (key1862, 1), (key1878, 1), (key1862, 1), (key1871, 2), (key1871, 2), (key1866, 2), (key1881, -2), (key1881, -2), (key1866, -2)]

theorem rawRowCheck17553 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form14 = rawRow17553 := by decide +kernel

def row17553 : Integer.Sparse Key := [(key1868, -4), (key1871, 4), (key1878, 4), (key1881, -4)]

theorem rowCheck17553 : row17553 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17553 := by decide +kernel

theorem rowEval17553 (x : Key → ℝ) : Integer.Sparse.eval row17553 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck17553, Integer.Sparse.eval_collectBalanced, rawRowCheck17553]

def rawRow17554 : Integer.Sparse Key := [(key1862, -1), (key1866, -1), (key1862, -1), (key1871, -1), (key1866, -1), (key1871, -1), (key1862, 2), (key1862, 2), (key1868, 2), (key1862, 1), (key1866, 1), (key1862, 1), (key1881, 1), (key1866, 1), (key1881, 1), (key1862, -2), (key1862, -2), (key1878, -2), (key1878, -1), (key1881, -1), (key1878, -1), (key1889, -1), (key1881, -1), (key1889, -1), (key1868, 1), (key1871, 1), (key1868, 1), (key1889, 1), (key1871, 1), (key1889, 1), (key1881, 2), (key1881, 2), (key1889, 2), (key1871, -2), (key1871, -2), (key1889, -2)]

theorem rawRowCheck17554 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form14 = rawRow17554 := by decide +kernel

def row17554 : Integer.Sparse Key := [(key1868, 4), (key1871, -4), (key1878, -4), (key1881, 4)]

theorem rowCheck17554 : row17554 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17554 := by decide +kernel

theorem rowEval17554 (x : Key → ℝ) : Integer.Sparse.eval row17554 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form14) x := by
  rw [rowCheck17554, Integer.Sparse.eval_collectBalanced, rawRowCheck17554]

def rawRow17555 : Integer.Sparse Key := [(key1866, -1), (key1862, -1), (key1871, -1), (key1862, -1), (key1871, -1), (key1866, -1), (key1862, 2), (key1868, 2), (key1862, 2), (key1866, 1), (key1862, 1), (key1881, 1), (key1862, 1), (key1881, 1), (key1866, 1), (key1862, -2), (key1878, -2), (key1862, -2), (key1881, -1), (key1878, -1), (key1889, -1), (key1878, -1), (key1889, -1), (key1881, -1), (key1871, 1), (key1868, 1), (key1889, 1), (key1868, 1), (key1889, 1), (key1871, 1), (key1881, 2), (key1889, 2), (key1881, 2), (key1871, -2), (key1889, -2), (key1871, -2)]

theorem rawRowCheck17555 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form14 = rawRow17555 := by decide +kernel

def row17555 : Integer.Sparse Key := [(key1868, 4), (key1871, -4), (key1878, -4), (key1881, 4)]

theorem rowCheck17555 : row17555 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17555 := by decide +kernel

theorem rowEval17555 (x : Key → ℝ) : Integer.Sparse.eval row17555 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck17555, Integer.Sparse.eval_collectBalanced, rawRowCheck17555]

def rawRow17556 : Integer.Sparse Key := [(key1871, -1), (key1871, -1), (key1866, -1), (key1866, -1), (key1862, -1), (key1862, -1), (key1868, 2), (key1862, 2), (key1862, 2), (key1881, 1), (key1881, 1), (key1866, 1), (key1866, 1), (key1862, 1), (key1862, 1), (key1878, -2), (key1862, -2), (key1862, -2), (key1889, -1), (key1889, -1), (key1881, -1), (key1881, -1), (key1878, -1), (key1878, -1), (key1889, 1), (key1889, 1), (key1871, 1), (key1871, 1), (key1868, 1), (key1868, 1), (key1889, 2), (key1881, 2), (key1881, 2), (key1889, -2), (key1871, -2), (key1871, -2)]

theorem rawRowCheck17556 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form14 = rawRow17556 := by decide +kernel

def row17556 : Integer.Sparse Key := [(key1868, 4), (key1871, -4), (key1878, -4), (key1881, 4)]

theorem rowCheck17556 : row17556 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17556 := by decide +kernel

theorem rowEval17556 (x : Key → ℝ) : Integer.Sparse.eval row17556 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck17556, Integer.Sparse.eval_collectBalanced, rawRowCheck17556]

def rawRow17557 : Integer.Sparse Key := [(key1878, -1), (key1881, -1), (key1878, -1), (key1889, -1), (key1881, -1), (key1889, -1), (key1881, 2), (key1881, 2), (key1889, 2), (key1868, 1), (key1871, 1), (key1868, 1), (key1889, 1), (key1871, 1), (key1889, 1), (key1871, -2), (key1871, -2), (key1889, -2), (key1862, -1), (key1866, -1), (key1862, -1), (key1871, -1), (key1866, -1), (key1871, -1), (key1862, 1), (key1866, 1), (key1862, 1), (key1881, 1), (key1866, 1), (key1881, 1), (key1862, 2), (key1862, 2), (key1868, 2), (key1862, -2), (key1862, -2), (key1878, -2)]

theorem rawRowCheck17557 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form14 = rawRow17557 := by decide +kernel

def row17557 : Integer.Sparse Key := [(key1868, 4), (key1871, -4), (key1878, -4), (key1881, 4)]

theorem rowCheck17557 : row17557 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17557 := by decide +kernel

theorem rowEval17557 (x : Key → ℝ) : Integer.Sparse.eval row17557 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form14) x := by
  rw [rowCheck17557, Integer.Sparse.eval_collectBalanced, rawRowCheck17557]

def rawRow17558 : Integer.Sparse Key := [(key1881, -1), (key1878, -1), (key1889, -1), (key1878, -1), (key1889, -1), (key1881, -1), (key1881, 2), (key1889, 2), (key1881, 2), (key1871, 1), (key1868, 1), (key1889, 1), (key1868, 1), (key1889, 1), (key1871, 1), (key1871, -2), (key1889, -2), (key1871, -2), (key1866, -1), (key1862, -1), (key1871, -1), (key1862, -1), (key1871, -1), (key1866, -1), (key1866, 1), (key1862, 1), (key1881, 1), (key1862, 1), (key1881, 1), (key1866, 1), (key1862, 2), (key1868, 2), (key1862, 2), (key1862, -2), (key1878, -2), (key1862, -2)]

theorem rawRowCheck17558 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form14 = rawRow17558 := by decide +kernel

def row17558 : Integer.Sparse Key := [(key1868, 4), (key1871, -4), (key1878, -4), (key1881, 4)]

theorem rowCheck17558 : row17558 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17558 := by decide +kernel

theorem rowEval17558 (x : Key → ℝ) : Integer.Sparse.eval row17558 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck17558, Integer.Sparse.eval_collectBalanced, rawRowCheck17558]

def rawRow17559 : Integer.Sparse Key := [(key1889, -1), (key1889, -1), (key1881, -1), (key1881, -1), (key1878, -1), (key1878, -1), (key1889, 2), (key1881, 2), (key1881, 2), (key1889, 1), (key1889, 1), (key1871, 1), (key1871, 1), (key1868, 1), (key1868, 1), (key1889, -2), (key1871, -2), (key1871, -2), (key1871, -1), (key1871, -1), (key1866, -1), (key1866, -1), (key1862, -1), (key1862, -1), (key1881, 1), (key1881, 1), (key1866, 1), (key1866, 1), (key1862, 1), (key1862, 1), (key1868, 2), (key1862, 2), (key1862, 2), (key1878, -2), (key1862, -2), (key1862, -2)]

theorem rawRowCheck17559 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form14 = rawRow17559 := by decide +kernel

def row17559 : Integer.Sparse Key := [(key1868, 4), (key1871, -4), (key1878, -4), (key1881, 4)]

theorem rowCheck17559 : row17559 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17559 := by decide +kernel

theorem rowEval17559 (x : Key → ℝ) : Integer.Sparse.eval row17559 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck17559, Integer.Sparse.eval_collectBalanced, rawRowCheck17559]

def rawRow17560 : Integer.Sparse Key := [(key1881, -1), (key1881, -1), (key1881, -1), (key1881, -1), (key1881, -1), (key1881, -1), (key1878, 2), (key1878, 2), (key1878, 2), (key1871, 1), (key1871, 1), (key1871, 1), (key1871, 1), (key1871, 1), (key1871, 1), (key1868, -2), (key1868, -2), (key1868, -2), (key1881, -1), (key1881, -1), (key1881, -1), (key1881, -1), (key1881, -1), (key1881, -1), (key1871, 1), (key1871, 1), (key1871, 1), (key1871, 1), (key1871, 1), (key1871, 1), (key1878, 2), (key1878, 2), (key1878, 2), (key1868, -2), (key1868, -2), (key1868, -2)]

theorem rawRowCheck17560 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form14 = rawRow17560 := by decide +kernel

def row17560 : Integer.Sparse Key := [(key1868, -12), (key1871, 12), (key1878, 12), (key1881, -12)]

theorem rowCheck17560 : row17560 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17560 := by decide +kernel

theorem rowEval17560 (x : Key → ℝ) : Integer.Sparse.eval row17560 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck17560, Integer.Sparse.eval_collectBalanced, rawRowCheck17560]

def rawRow17561 : Integer.Sparse Key := [(key1938, -1), (key1938, -1), (key1941, -1), (key1941, -1), (key1942, -1), (key1942, -1), (key1939, 2), (key1942, 2), (key1942, 2), (key1938, 1), (key1938, 1), (key1950, 1), (key1950, 1), (key1951, 1), (key1951, 1), (key1939, -2), (key1951, -2), (key1951, -2), (key1938, -1), (key1938, -1), (key1941, -1), (key1941, -1), (key1942, -1), (key1942, -1), (key1938, 1), (key1938, 1), (key1950, 1), (key1950, 1), (key1951, 1), (key1951, 1), (key1939, 2), (key1942, 2), (key1942, 2), (key1939, -2), (key1951, -2), (key1951, -2)]

theorem rawRowCheck17561 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form15 = rawRow17561 := by decide +kernel

def row17561 : Integer.Sparse Key := [(key1941, -4), (key1942, 4), (key1950, 4), (key1951, -4)]

theorem rowCheck17561 : row17561 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17561 := by decide +kernel

theorem rowEval17561 (x : Key → ℝ) : Integer.Sparse.eval row17561 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form15) x := by
  rw [rowCheck17561, Integer.Sparse.eval_collectBalanced, rawRowCheck17561]

def rawRow17562 : Integer.Sparse Key := [(key1941, -1), (key1942, -1), (key1938, -1), (key1942, -1), (key1938, -1), (key1941, -1), (key1942, 2), (key1939, 2), (key1942, 2), (key1950, 1), (key1951, 1), (key1938, 1), (key1951, 1), (key1938, 1), (key1950, 1), (key1951, -2), (key1939, -2), (key1951, -2), (key1941, -1), (key1942, -1), (key1938, -1), (key1942, -1), (key1938, -1), (key1941, -1), (key1950, 1), (key1951, 1), (key1938, 1), (key1951, 1), (key1938, 1), (key1950, 1), (key1942, 2), (key1939, 2), (key1942, 2), (key1951, -2), (key1939, -2), (key1951, -2)]

theorem rawRowCheck17562 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form15 = rawRow17562 := by decide +kernel

def row17562 : Integer.Sparse Key := [(key1941, -4), (key1942, 4), (key1950, 4), (key1951, -4)]

theorem rowCheck17562 : row17562 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17562 := by decide +kernel

theorem rowEval17562 (x : Key → ℝ) : Integer.Sparse.eval row17562 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form15) x := by
  rw [rowCheck17562, Integer.Sparse.eval_collectBalanced, rawRowCheck17562]

def rawRow17563 : Integer.Sparse Key := [(key1942, -1), (key1941, -1), (key1942, -1), (key1938, -1), (key1941, -1), (key1938, -1), (key1942, 2), (key1942, 2), (key1939, 2), (key1951, 1), (key1950, 1), (key1951, 1), (key1938, 1), (key1950, 1), (key1938, 1), (key1951, -2), (key1951, -2), (key1939, -2), (key1942, -1), (key1941, -1), (key1942, -1), (key1938, -1), (key1941, -1), (key1938, -1), (key1951, 1), (key1950, 1), (key1951, 1), (key1938, 1), (key1950, 1), (key1938, 1), (key1942, 2), (key1942, 2), (key1939, 2), (key1951, -2), (key1951, -2), (key1939, -2)]

theorem rawRowCheck17563 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form15 = rawRow17563 := by decide +kernel

def row17563 : Integer.Sparse Key := [(key1941, -4), (key1942, 4), (key1950, 4), (key1951, -4)]

theorem rowCheck17563 : row17563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17563 := by decide +kernel

theorem rowEval17563 (x : Key → ℝ) : Integer.Sparse.eval row17563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck17563, Integer.Sparse.eval_collectBalanced, rawRowCheck17563]

def rawRow17564 : Integer.Sparse Key := [(key1938, -1), (key1939, -1), (key1938, -1), (key1942, -1), (key1939, -1), (key1942, -1), (key1938, 2), (key1938, 2), (key1941, 2), (key1938, 1), (key1939, 1), (key1938, 1), (key1951, 1), (key1939, 1), (key1951, 1), (key1938, -2), (key1938, -2), (key1950, -2), (key1950, -1), (key1951, -1), (key1950, -1), (key1956, -1), (key1951, -1), (key1956, -1), (key1941, 1), (key1942, 1), (key1941, 1), (key1956, 1), (key1942, 1), (key1956, 1), (key1951, 2), (key1951, 2), (key1956, 2), (key1942, -2), (key1942, -2), (key1956, -2)]

theorem rawRowCheck17564 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form15 = rawRow17564 := by decide +kernel

def row17564 : Integer.Sparse Key := [(key1941, 4), (key1942, -4), (key1950, -4), (key1951, 4)]

theorem rowCheck17564 : row17564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17564 := by decide +kernel

theorem rowEval17564 (x : Key → ℝ) : Integer.Sparse.eval row17564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form15) x := by
  rw [rowCheck17564, Integer.Sparse.eval_collectBalanced, rawRowCheck17564]

def rawRow17565 : Integer.Sparse Key := [(key1939, -1), (key1938, -1), (key1942, -1), (key1938, -1), (key1942, -1), (key1939, -1), (key1938, 2), (key1941, 2), (key1938, 2), (key1939, 1), (key1938, 1), (key1951, 1), (key1938, 1), (key1951, 1), (key1939, 1), (key1938, -2), (key1950, -2), (key1938, -2), (key1951, -1), (key1950, -1), (key1956, -1), (key1950, -1), (key1956, -1), (key1951, -1), (key1942, 1), (key1941, 1), (key1956, 1), (key1941, 1), (key1956, 1), (key1942, 1), (key1951, 2), (key1956, 2), (key1951, 2), (key1942, -2), (key1956, -2), (key1942, -2)]

theorem rawRowCheck17565 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form15 = rawRow17565 := by decide +kernel

def row17565 : Integer.Sparse Key := [(key1941, 4), (key1942, -4), (key1950, -4), (key1951, 4)]

theorem rowCheck17565 : row17565 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17565 := by decide +kernel

theorem rowEval17565 (x : Key → ℝ) : Integer.Sparse.eval row17565 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck17565, Integer.Sparse.eval_collectBalanced, rawRowCheck17565]

def rawRow17566 : Integer.Sparse Key := [(key1942, -1), (key1942, -1), (key1939, -1), (key1939, -1), (key1938, -1), (key1938, -1), (key1941, 2), (key1938, 2), (key1938, 2), (key1951, 1), (key1951, 1), (key1939, 1), (key1939, 1), (key1938, 1), (key1938, 1), (key1950, -2), (key1938, -2), (key1938, -2), (key1956, -1), (key1956, -1), (key1951, -1), (key1951, -1), (key1950, -1), (key1950, -1), (key1956, 1), (key1956, 1), (key1942, 1), (key1942, 1), (key1941, 1), (key1941, 1), (key1956, 2), (key1951, 2), (key1951, 2), (key1956, -2), (key1942, -2), (key1942, -2)]

theorem rawRowCheck17566 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form15 = rawRow17566 := by decide +kernel

def row17566 : Integer.Sparse Key := [(key1941, 4), (key1942, -4), (key1950, -4), (key1951, 4)]

theorem rowCheck17566 : row17566 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17566 := by decide +kernel

theorem rowEval17566 (x : Key → ℝ) : Integer.Sparse.eval row17566 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck17566, Integer.Sparse.eval_collectBalanced, rawRowCheck17566]

def rawRow17567 : Integer.Sparse Key := [(key1950, -1), (key1951, -1), (key1950, -1), (key1956, -1), (key1951, -1), (key1956, -1), (key1951, 2), (key1951, 2), (key1956, 2), (key1941, 1), (key1942, 1), (key1941, 1), (key1956, 1), (key1942, 1), (key1956, 1), (key1942, -2), (key1942, -2), (key1956, -2), (key1938, -1), (key1939, -1), (key1938, -1), (key1942, -1), (key1939, -1), (key1942, -1), (key1938, 1), (key1939, 1), (key1938, 1), (key1951, 1), (key1939, 1), (key1951, 1), (key1938, 2), (key1938, 2), (key1941, 2), (key1938, -2), (key1938, -2), (key1950, -2)]

theorem rawRowCheck17567 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form15 = rawRow17567 := by decide +kernel

def row17567 : Integer.Sparse Key := [(key1941, 4), (key1942, -4), (key1950, -4), (key1951, 4)]

theorem rowCheck17567 : row17567 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17567 := by decide +kernel

theorem rowEval17567 (x : Key → ℝ) : Integer.Sparse.eval row17567 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form15) x := by
  rw [rowCheck17567, Integer.Sparse.eval_collectBalanced, rawRowCheck17567]

def rawRow17568 : Integer.Sparse Key := [(key1951, -1), (key1950, -1), (key1956, -1), (key1950, -1), (key1956, -1), (key1951, -1), (key1951, 2), (key1956, 2), (key1951, 2), (key1942, 1), (key1941, 1), (key1956, 1), (key1941, 1), (key1956, 1), (key1942, 1), (key1942, -2), (key1956, -2), (key1942, -2), (key1939, -1), (key1938, -1), (key1942, -1), (key1938, -1), (key1942, -1), (key1939, -1), (key1939, 1), (key1938, 1), (key1951, 1), (key1938, 1), (key1951, 1), (key1939, 1), (key1938, 2), (key1941, 2), (key1938, 2), (key1938, -2), (key1950, -2), (key1938, -2)]

theorem rawRowCheck17568 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form15 = rawRow17568 := by decide +kernel

def row17568 : Integer.Sparse Key := [(key1941, 4), (key1942, -4), (key1950, -4), (key1951, 4)]

theorem rowCheck17568 : row17568 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17568 := by decide +kernel

theorem rowEval17568 (x : Key → ℝ) : Integer.Sparse.eval row17568 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck17568, Integer.Sparse.eval_collectBalanced, rawRowCheck17568]

def rawRow17569 : Integer.Sparse Key := [(key1956, -1), (key1956, -1), (key1951, -1), (key1951, -1), (key1950, -1), (key1950, -1), (key1956, 2), (key1951, 2), (key1951, 2), (key1956, 1), (key1956, 1), (key1942, 1), (key1942, 1), (key1941, 1), (key1941, 1), (key1956, -2), (key1942, -2), (key1942, -2), (key1942, -1), (key1942, -1), (key1939, -1), (key1939, -1), (key1938, -1), (key1938, -1), (key1951, 1), (key1951, 1), (key1939, 1), (key1939, 1), (key1938, 1), (key1938, 1), (key1941, 2), (key1938, 2), (key1938, 2), (key1950, -2), (key1938, -2), (key1938, -2)]

theorem rawRowCheck17569 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form15 = rawRow17569 := by decide +kernel

def row17569 : Integer.Sparse Key := [(key1941, 4), (key1942, -4), (key1950, -4), (key1951, 4)]

theorem rowCheck17569 : row17569 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17569 := by decide +kernel

theorem rowEval17569 (x : Key → ℝ) : Integer.Sparse.eval row17569 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck17569, Integer.Sparse.eval_collectBalanced, rawRowCheck17569]

def rawRow17570 : Integer.Sparse Key := [(key1951, -1), (key1951, -1), (key1951, -1), (key1951, -1), (key1951, -1), (key1951, -1), (key1950, 2), (key1950, 2), (key1950, 2), (key1942, 1), (key1942, 1), (key1942, 1), (key1942, 1), (key1942, 1), (key1942, 1), (key1941, -2), (key1941, -2), (key1941, -2), (key1951, -1), (key1951, -1), (key1951, -1), (key1951, -1), (key1951, -1), (key1951, -1), (key1942, 1), (key1942, 1), (key1942, 1), (key1942, 1), (key1942, 1), (key1942, 1), (key1950, 2), (key1950, 2), (key1950, 2), (key1941, -2), (key1941, -2), (key1941, -2)]

theorem rawRowCheck17570 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form15 = rawRow17570 := by decide +kernel

def row17570 : Integer.Sparse Key := [(key1941, -12), (key1942, 12), (key1950, 12), (key1951, -12)]

theorem rowCheck17570 : row17570 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17570 := by decide +kernel

theorem rowEval17570 (x : Key → ℝ) : Integer.Sparse.eval row17570 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck17570, Integer.Sparse.eval_collectBalanced, rawRowCheck17570]

def rawRow17571 : Integer.Sparse Key := [(key1863, 2), (key1880, 2), (key1880, 2), (key1865, -1), (key1865, -1), (key1880, -1), (key1880, -1), (key1883, -1), (key1883, -1), (key1863, 2), (key1880, 2), (key1880, 2), (key1870, -1), (key1870, -1), (key1880, -1), (key1880, -1), (key1891, -1), (key1891, -1), (key1865, -1), (key1865, -1), (key1880, -1), (key1880, -1), (key1883, -1), (key1883, -1), (key1870, -1), (key1870, -1), (key1880, -1), (key1880, -1), (key1891, -1), (key1891, -1), (key1872, 2), (key1872, 2), (key1883, 2), (key1883, 2), (key1891, 2), (key1891, 2)]

theorem rawRowCheck17571 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form16 = rawRow17571 := by decide +kernel

def row17571 : Integer.Sparse Key := [(key1863, 4), (key1865, -4), (key1870, -4), (key1872, 4)]

theorem rowCheck17571 : row17571 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17571 := by decide +kernel

theorem rowEval17571 (x : Key → ℝ) : Integer.Sparse.eval row17571 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form16) x := by
  rw [rowCheck17571, Integer.Sparse.eval_collectBalanced, rawRowCheck17571]

def rawRow17572 : Integer.Sparse Key := [(key1880, 2), (key1863, 2), (key1880, 2), (key1880, -1), (key1883, -1), (key1865, -1), (key1883, -1), (key1865, -1), (key1880, -1), (key1880, 2), (key1863, 2), (key1880, 2), (key1880, -1), (key1891, -1), (key1870, -1), (key1891, -1), (key1870, -1), (key1880, -1), (key1880, -1), (key1883, -1), (key1865, -1), (key1883, -1), (key1865, -1), (key1880, -1), (key1880, -1), (key1891, -1), (key1870, -1), (key1891, -1), (key1870, -1), (key1880, -1), (key1883, 2), (key1891, 2), (key1872, 2), (key1891, 2), (key1872, 2), (key1883, 2)]

theorem rawRowCheck17572 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form16 = rawRow17572 := by decide +kernel

def row17572 : Integer.Sparse Key := [(key1863, 4), (key1865, -4), (key1870, -4), (key1872, 4)]

theorem rowCheck17572 : row17572 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17572 := by decide +kernel

theorem rowEval17572 (x : Key → ℝ) : Integer.Sparse.eval row17572 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form16) x := by
  rw [rowCheck17572, Integer.Sparse.eval_collectBalanced, rawRowCheck17572]

def rawRow17573 : Integer.Sparse Key := [(key1880, 2), (key1880, 2), (key1863, 2), (key1883, -1), (key1880, -1), (key1883, -1), (key1865, -1), (key1880, -1), (key1865, -1), (key1880, 2), (key1880, 2), (key1863, 2), (key1891, -1), (key1880, -1), (key1891, -1), (key1870, -1), (key1880, -1), (key1870, -1), (key1883, -1), (key1880, -1), (key1883, -1), (key1865, -1), (key1880, -1), (key1865, -1), (key1891, -1), (key1880, -1), (key1891, -1), (key1870, -1), (key1880, -1), (key1870, -1), (key1891, 2), (key1883, 2), (key1891, 2), (key1872, 2), (key1883, 2), (key1872, 2)]

theorem rawRowCheck17573 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form16 = rawRow17573 := by decide +kernel

def row17573 : Integer.Sparse Key := [(key1863, 4), (key1865, -4), (key1870, -4), (key1872, 4)]

theorem rowCheck17573 : row17573 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17573 := by decide +kernel

theorem rowEval17573 (x : Key → ℝ) : Integer.Sparse.eval row17573 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form16) x := by
  rw [rowCheck17573, Integer.Sparse.eval_collectBalanced, rawRowCheck17573]

def rawRow17574 : Integer.Sparse Key := [(key1865, 2), (key1865, 2), (key1883, 2), (key1863, -1), (key1865, -1), (key1863, -1), (key1880, -1), (key1865, -1), (key1880, -1), (key1870, 2), (key1870, 2), (key1891, 2), (key1863, -1), (key1870, -1), (key1863, -1), (key1880, -1), (key1870, -1), (key1880, -1), (key1870, -1), (key1872, -1), (key1870, -1), (key1891, -1), (key1872, -1), (key1891, -1), (key1865, -1), (key1872, -1), (key1865, -1), (key1883, -1), (key1872, -1), (key1883, -1), (key1865, 2), (key1870, 2), (key1865, 2), (key1880, 2), (key1870, 2), (key1880, 2)]

theorem rawRowCheck17574 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form16 = rawRow17574 := by decide +kernel

def row17574 : Integer.Sparse Key := [(key1863, -4), (key1865, 4), (key1870, 4), (key1872, -4)]

theorem rowCheck17574 : row17574 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17574 := by decide +kernel

theorem rowEval17574 (x : Key → ℝ) : Integer.Sparse.eval row17574 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form16) x := by
  rw [rowCheck17574, Integer.Sparse.eval_collectBalanced, rawRowCheck17574]

def rawRow17575 : Integer.Sparse Key := [(key1865, 2), (key1883, 2), (key1865, 2), (key1865, -1), (key1863, -1), (key1880, -1), (key1863, -1), (key1880, -1), (key1865, -1), (key1870, 2), (key1891, 2), (key1870, 2), (key1870, -1), (key1863, -1), (key1880, -1), (key1863, -1), (key1880, -1), (key1870, -1), (key1872, -1), (key1870, -1), (key1891, -1), (key1870, -1), (key1891, -1), (key1872, -1), (key1872, -1), (key1865, -1), (key1883, -1), (key1865, -1), (key1883, -1), (key1872, -1), (key1870, 2), (key1865, 2), (key1880, 2), (key1865, 2), (key1880, 2), (key1870, 2)]

theorem rawRowCheck17575 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form16 = rawRow17575 := by decide +kernel

def row17575 : Integer.Sparse Key := [(key1863, -4), (key1865, 4), (key1870, 4), (key1872, -4)]

theorem rowCheck17575 : row17575 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17575 := by decide +kernel

theorem rowEval17575 (x : Key → ℝ) : Integer.Sparse.eval row17575 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form16) x := by
  rw [rowCheck17575, Integer.Sparse.eval_collectBalanced, rawRowCheck17575]

def rawRow17576 : Integer.Sparse Key := [(key1883, 2), (key1865, 2), (key1865, 2), (key1880, -1), (key1880, -1), (key1865, -1), (key1865, -1), (key1863, -1), (key1863, -1), (key1891, 2), (key1870, 2), (key1870, 2), (key1880, -1), (key1880, -1), (key1870, -1), (key1870, -1), (key1863, -1), (key1863, -1), (key1891, -1), (key1891, -1), (key1872, -1), (key1872, -1), (key1870, -1), (key1870, -1), (key1883, -1), (key1883, -1), (key1872, -1), (key1872, -1), (key1865, -1), (key1865, -1), (key1880, 2), (key1880, 2), (key1870, 2), (key1870, 2), (key1865, 2), (key1865, 2)]

theorem rawRowCheck17576 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form16 = rawRow17576 := by decide +kernel

def row17576 : Integer.Sparse Key := [(key1863, -4), (key1865, 4), (key1870, 4), (key1872, -4)]

theorem rowCheck17576 : row17576 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17576 := by decide +kernel

theorem rowEval17576 (x : Key → ℝ) : Integer.Sparse.eval row17576 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form16) x := by
  rw [rowCheck17576, Integer.Sparse.eval_collectBalanced, rawRowCheck17576]

def rawRow17577 : Integer.Sparse Key := [(key1870, 2), (key1870, 2), (key1891, 2), (key1870, -1), (key1872, -1), (key1870, -1), (key1891, -1), (key1872, -1), (key1891, -1), (key1865, 2), (key1865, 2), (key1883, 2), (key1865, -1), (key1872, -1), (key1865, -1), (key1883, -1), (key1872, -1), (key1883, -1), (key1863, -1), (key1865, -1), (key1863, -1), (key1880, -1), (key1865, -1), (key1880, -1), (key1863, -1), (key1870, -1), (key1863, -1), (key1880, -1), (key1870, -1), (key1880, -1), (key1865, 2), (key1870, 2), (key1865, 2), (key1880, 2), (key1870, 2), (key1880, 2)]

theorem rawRowCheck17577 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form16 = rawRow17577 := by decide +kernel

def row17577 : Integer.Sparse Key := [(key1863, -4), (key1865, 4), (key1870, 4), (key1872, -4)]

theorem rowCheck17577 : row17577 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17577 := by decide +kernel

theorem rowEval17577 (x : Key → ℝ) : Integer.Sparse.eval row17577 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form16) x := by
  rw [rowCheck17577, Integer.Sparse.eval_collectBalanced, rawRowCheck17577]

def rawRow17578 : Integer.Sparse Key := [(key1870, 2), (key1891, 2), (key1870, 2), (key1872, -1), (key1870, -1), (key1891, -1), (key1870, -1), (key1891, -1), (key1872, -1), (key1865, 2), (key1883, 2), (key1865, 2), (key1872, -1), (key1865, -1), (key1883, -1), (key1865, -1), (key1883, -1), (key1872, -1), (key1865, -1), (key1863, -1), (key1880, -1), (key1863, -1), (key1880, -1), (key1865, -1), (key1870, -1), (key1863, -1), (key1880, -1), (key1863, -1), (key1880, -1), (key1870, -1), (key1870, 2), (key1865, 2), (key1880, 2), (key1865, 2), (key1880, 2), (key1870, 2)]

theorem rawRowCheck17578 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form16 = rawRow17578 := by decide +kernel

def row17578 : Integer.Sparse Key := [(key1863, -4), (key1865, 4), (key1870, 4), (key1872, -4)]

theorem rowCheck17578 : row17578 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17578 := by decide +kernel

theorem rowEval17578 (x : Key → ℝ) : Integer.Sparse.eval row17578 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form16) x := by
  rw [rowCheck17578, Integer.Sparse.eval_collectBalanced, rawRowCheck17578]

def rawRow17579 : Integer.Sparse Key := [(key1891, 2), (key1870, 2), (key1870, 2), (key1891, -1), (key1891, -1), (key1872, -1), (key1872, -1), (key1870, -1), (key1870, -1), (key1883, 2), (key1865, 2), (key1865, 2), (key1883, -1), (key1883, -1), (key1872, -1), (key1872, -1), (key1865, -1), (key1865, -1), (key1880, -1), (key1880, -1), (key1865, -1), (key1865, -1), (key1863, -1), (key1863, -1), (key1880, -1), (key1880, -1), (key1870, -1), (key1870, -1), (key1863, -1), (key1863, -1), (key1880, 2), (key1880, 2), (key1870, 2), (key1870, 2), (key1865, 2), (key1865, 2)]

theorem rawRowCheck17579 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form16 = rawRow17579 := by decide +kernel

def row17579 : Integer.Sparse Key := [(key1863, -4), (key1865, 4), (key1870, 4), (key1872, -4)]

theorem rowCheck17579 : row17579 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17579 := by decide +kernel

theorem rowEval17579 (x : Key → ℝ) : Integer.Sparse.eval row17579 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form16) x := by
  rw [rowCheck17579, Integer.Sparse.eval_collectBalanced, rawRowCheck17579]

def rawRow17580 : Integer.Sparse Key := [(key1872, 2), (key1872, 2), (key1872, 2), (key1870, -1), (key1870, -1), (key1870, -1), (key1870, -1), (key1870, -1), (key1870, -1), (key1872, 2), (key1872, 2), (key1872, 2), (key1865, -1), (key1865, -1), (key1865, -1), (key1865, -1), (key1865, -1), (key1865, -1), (key1870, -1), (key1870, -1), (key1870, -1), (key1870, -1), (key1870, -1), (key1870, -1), (key1865, -1), (key1865, -1), (key1865, -1), (key1865, -1), (key1865, -1), (key1865, -1), (key1863, 2), (key1863, 2), (key1863, 2), (key1863, 2), (key1863, 2), (key1863, 2)]

theorem rawRowCheck17580 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form16 = rawRow17580 := by decide +kernel

def row17580 : Integer.Sparse Key := [(key1863, 12), (key1865, -12), (key1870, -12), (key1872, 12)]

theorem rowCheck17580 : row17580 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17580 := by decide +kernel

theorem rowEval17580 (x : Key → ℝ) : Integer.Sparse.eval row17580 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form16) x := by
  rw [rowCheck17580, Integer.Sparse.eval_collectBalanced, rawRowCheck17580]

def rawRow17581 : Integer.Sparse Key := [(key533, 4), (key533, 4), (key536, 4), (key533, -2), (key533, -2), (key539, -2), (key539, -2), (key544, -2), (key544, -2), (key533, -2), (key533, -2), (key539, -2), (key539, -2), (key544, -2), (key544, -2), (key539, 4), (key539, 4), (key556, 4)]

theorem rawRowCheck17581 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form17 = rawRow17581 := by decide +kernel

def row17581 : Integer.Sparse Key := [(key536, 4), (key544, -8), (key556, 4)]

theorem rowCheck17581 : row17581 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17581 := by decide +kernel

theorem rowEval17581 (x : Key → ℝ) : Integer.Sparse.eval row17581 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17581, Integer.Sparse.eval_collectBalanced, rawRowCheck17581]

def rawRow17582 : Integer.Sparse Key := [(key533, 4), (key536, 4), (key533, 4), (key539, -2), (key544, -2), (key533, -2), (key544, -2), (key533, -2), (key539, -2), (key539, -2), (key544, -2), (key533, -2), (key544, -2), (key533, -2), (key539, -2), (key539, 4), (key556, 4), (key539, 4)]

theorem rawRowCheck17582 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form17 = rawRow17582 := by decide +kernel

def row17582 : Integer.Sparse Key := [(key536, 4), (key544, -8), (key556, 4)]

theorem rowCheck17582 : row17582 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17582 := by decide +kernel

theorem rowEval17582 (x : Key → ℝ) : Integer.Sparse.eval row17582 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17582, Integer.Sparse.eval_collectBalanced, rawRowCheck17582]

def rawRow17583 : Integer.Sparse Key := [(key536, 4), (key533, 4), (key533, 4), (key544, -2), (key539, -2), (key544, -2), (key533, -2), (key539, -2), (key533, -2), (key544, -2), (key539, -2), (key544, -2), (key533, -2), (key539, -2), (key533, -2), (key556, 4), (key539, 4), (key539, 4)]

theorem rawRowCheck17583 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form17 = rawRow17583 := by decide +kernel

def row17583 : Integer.Sparse Key := [(key536, 4), (key544, -8), (key556, 4)]

theorem rowCheck17583 : row17583 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17583 := by decide +kernel

theorem rowEval17583 (x : Key → ℝ) : Integer.Sparse.eval row17583 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17583, Integer.Sparse.eval_collectBalanced, rawRowCheck17583]

def rawRow17584 : Integer.Sparse Key := [(key539, 4), (key544, 4), (key544, 4), (key533, -2), (key536, -2), (key533, -2), (key544, -2), (key536, -2), (key544, -2), (key539, -2), (key544, -2), (key539, -2), (key556, -2), (key544, -2), (key556, -2), (key533, 4), (key544, 4), (key544, 4)]

theorem rawRowCheck17584 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form17 = rawRow17584 := by decide +kernel

def row17584 : Integer.Sparse Key := [(key536, -4), (key544, 8), (key556, -4)]

theorem rowCheck17584 : row17584 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17584 := by decide +kernel

theorem rowEval17584 (x : Key → ℝ) : Integer.Sparse.eval row17584 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17584, Integer.Sparse.eval_collectBalanced, rawRowCheck17584]

def rawRow17585 : Integer.Sparse Key := [(key544, 4), (key539, 4), (key544, 4), (key536, -2), (key533, -2), (key544, -2), (key533, -2), (key544, -2), (key536, -2), (key544, -2), (key539, -2), (key556, -2), (key539, -2), (key556, -2), (key544, -2), (key544, 4), (key533, 4), (key544, 4)]

theorem rawRowCheck17585 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form17 = rawRow17585 := by decide +kernel

def row17585 : Integer.Sparse Key := [(key536, -4), (key544, 8), (key556, -4)]

theorem rowCheck17585 : row17585 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17585 := by decide +kernel

theorem rowEval17585 (x : Key → ℝ) : Integer.Sparse.eval row17585 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17585, Integer.Sparse.eval_collectBalanced, rawRowCheck17585]

def rawRow17586 : Integer.Sparse Key := [(key544, 4), (key544, 4), (key539, 4), (key544, -2), (key544, -2), (key536, -2), (key536, -2), (key533, -2), (key533, -2), (key556, -2), (key556, -2), (key544, -2), (key544, -2), (key539, -2), (key539, -2), (key544, 4), (key544, 4), (key533, 4)]

theorem rawRowCheck17586 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form17 = rawRow17586 := by decide +kernel

def row17586 : Integer.Sparse Key := [(key536, -4), (key544, 8), (key556, -4)]

theorem rowCheck17586 : row17586 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17586 := by decide +kernel

theorem rowEval17586 (x : Key → ℝ) : Integer.Sparse.eval row17586 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17586, Integer.Sparse.eval_collectBalanced, rawRowCheck17586]

def rawRow17587 : Integer.Sparse Key := [(key539, 4), (key544, 4), (key544, 4), (key539, -2), (key544, -2), (key539, -2), (key556, -2), (key544, -2), (key556, -2), (key533, -2), (key536, -2), (key533, -2), (key544, -2), (key536, -2), (key544, -2), (key533, 4), (key544, 4), (key544, 4)]

theorem rawRowCheck17587 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form17 = rawRow17587 := by decide +kernel

def row17587 : Integer.Sparse Key := [(key536, -4), (key544, 8), (key556, -4)]

theorem rowCheck17587 : row17587 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17587 := by decide +kernel

theorem rowEval17587 (x : Key → ℝ) : Integer.Sparse.eval row17587 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17587, Integer.Sparse.eval_collectBalanced, rawRowCheck17587]

def rawRow17588 : Integer.Sparse Key := [(key544, 4), (key539, 4), (key544, 4), (key544, -2), (key539, -2), (key556, -2), (key539, -2), (key556, -2), (key544, -2), (key536, -2), (key533, -2), (key544, -2), (key533, -2), (key544, -2), (key536, -2), (key544, 4), (key533, 4), (key544, 4)]

theorem rawRowCheck17588 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form17 = rawRow17588 := by decide +kernel

def row17588 : Integer.Sparse Key := [(key536, -4), (key544, 8), (key556, -4)]

theorem rowCheck17588 : row17588 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17588 := by decide +kernel

theorem rowEval17588 (x : Key → ℝ) : Integer.Sparse.eval row17588 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17588, Integer.Sparse.eval_collectBalanced, rawRowCheck17588]

def rawRow17589 : Integer.Sparse Key := [(key544, 4), (key544, 4), (key539, 4), (key556, -2), (key556, -2), (key544, -2), (key544, -2), (key539, -2), (key539, -2), (key544, -2), (key544, -2), (key536, -2), (key536, -2), (key533, -2), (key533, -2), (key544, 4), (key544, 4), (key533, 4)]

theorem rawRowCheck17589 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form17 = rawRow17589 := by decide +kernel

def row17589 : Integer.Sparse Key := [(key536, -4), (key544, 8), (key556, -4)]

theorem rowCheck17589 : row17589 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17589 := by decide +kernel

theorem rowEval17589 (x : Key → ℝ) : Integer.Sparse.eval row17589 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17589, Integer.Sparse.eval_collectBalanced, rawRowCheck17589]

def rawRow17590 : Integer.Sparse Key := [(key556, 4), (key556, 4), (key556, 4), (key544, -2), (key544, -2), (key544, -2), (key544, -2), (key544, -2), (key544, -2), (key544, -2), (key544, -2), (key544, -2), (key544, -2), (key544, -2), (key544, -2), (key536, 4), (key536, 4), (key536, 4)]

theorem rawRowCheck17590 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form17 = rawRow17590 := by decide +kernel

def row17590 : Integer.Sparse Key := [(key536, 12), (key544, -24), (key556, 12)]

theorem rowCheck17590 : row17590 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17590 := by decide +kernel

theorem rowEval17590 (x : Key → ℝ) : Integer.Sparse.eval row17590 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17590, Integer.Sparse.eval_collectBalanced, rawRowCheck17590]

def rawRow17591 : Integer.Sparse Key := [(key633, -2), (key633, -2), (key635, -2), (key635, -2), (key638, -2), (key638, -2), (key635, 2), (key635, 2), (key644, 2), (key638, 2), (key638, 2), (key644, 2), (key635, 2), (key635, 2), (key644, 2), (key644, -6), (key638, 2), (key638, 2), (key644, 2), (key644, -6)]

theorem rawRowCheck17591 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form18 = rawRow17591 := by decide +kernel

def row17591 : Integer.Sparse Key := [(key633, -4), (key635, 4), (key638, 4), (key644, -4)]

theorem rowCheck17591 : row17591 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17591 := by decide +kernel

theorem rowEval17591 (x : Key → ℝ) : Integer.Sparse.eval row17591 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17591, Integer.Sparse.eval_collectBalanced, rawRowCheck17591]

def rawRow17592 : Integer.Sparse Key := [(key635, -2), (key638, -2), (key633, -2), (key638, -2), (key633, -2), (key635, -2), (key635, 2), (key644, 2), (key635, 2), (key638, 2), (key644, 2), (key638, 2), (key635, 2), (key644, 2), (key635, 2), (key644, -6), (key638, 2), (key644, 2), (key638, 2), (key644, -6)]

theorem rawRowCheck17592 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form18 = rawRow17592 := by decide +kernel

def row17592 : Integer.Sparse Key := [(key633, -4), (key635, 4), (key638, 4), (key644, -4)]

theorem rowCheck17592 : row17592 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17592 := by decide +kernel

theorem rowEval17592 (x : Key → ℝ) : Integer.Sparse.eval row17592 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17592, Integer.Sparse.eval_collectBalanced, rawRowCheck17592]

def rawRow17593 : Integer.Sparse Key := [(key638, -2), (key635, -2), (key638, -2), (key633, -2), (key635, -2), (key633, -2), (key644, 2), (key635, 2), (key635, 2), (key644, 2), (key638, 2), (key638, 2), (key644, 2), (key635, 2), (key635, 2), (key644, -6), (key644, 2), (key638, 2), (key638, 2), (key644, -6)]

theorem rawRowCheck17593 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form18 = rawRow17593 := by decide +kernel

def row17593 : Integer.Sparse Key := [(key633, -4), (key635, 4), (key638, 4), (key644, -4)]

theorem rowCheck17593 : row17593 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17593 := by decide +kernel

theorem rowEval17593 (x : Key → ℝ) : Integer.Sparse.eval row17593 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck17593, Integer.Sparse.eval_collectBalanced, rawRowCheck17593]

def rawRow17594 : Integer.Sparse Key := [(key635, -2), (key638, -2), (key635, -2), (key644, -2), (key638, -2), (key644, -2), (key633, 2), (key638, 2), (key638, 2), (key633, 2), (key635, 2), (key635, 2), (key635, 2), (key644, 2), (key644, 2), (key635, -6), (key638, 2), (key644, 2), (key644, 2), (key638, -6)]

theorem rawRowCheck17594 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form18 = rawRow17594 := by decide +kernel

def row17594 : Integer.Sparse Key := [(key633, 4), (key635, -4), (key638, -4), (key644, 4)]

theorem rowCheck17594 : row17594 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17594 := by decide +kernel

theorem rowEval17594 (x : Key → ℝ) : Integer.Sparse.eval row17594 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17594, Integer.Sparse.eval_collectBalanced, rawRowCheck17594]

def rawRow17595 : Integer.Sparse Key := [(key638, -2), (key635, -2), (key644, -2), (key635, -2), (key644, -2), (key638, -2), (key638, 2), (key633, 2), (key638, 2), (key635, 2), (key633, 2), (key635, 2), (key644, 2), (key635, 2), (key644, 2), (key635, -6), (key644, 2), (key638, 2), (key644, 2), (key638, -6)]

theorem rawRowCheck17595 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form18 = rawRow17595 := by decide +kernel

def row17595 : Integer.Sparse Key := [(key633, 4), (key635, -4), (key638, -4), (key644, 4)]

theorem rowCheck17595 : row17595 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17595 := by decide +kernel

theorem rowEval17595 (x : Key → ℝ) : Integer.Sparse.eval row17595 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck17595, Integer.Sparse.eval_collectBalanced, rawRowCheck17595]

def rawRow17596 : Integer.Sparse Key := [(key644, -2), (key644, -2), (key638, -2), (key638, -2), (key635, -2), (key635, -2), (key638, 2), (key638, 2), (key633, 2), (key635, 2), (key635, 2), (key633, 2), (key644, 2), (key644, 2), (key635, 2), (key635, -6), (key644, 2), (key644, 2), (key638, 2), (key638, -6)]

theorem rawRowCheck17596 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form18 = rawRow17596 := by decide +kernel

def row17596 : Integer.Sparse Key := [(key633, 4), (key635, -4), (key638, -4), (key644, 4)]

theorem rowCheck17596 : row17596 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17596 := by decide +kernel

theorem rowEval17596 (x : Key → ℝ) : Integer.Sparse.eval row17596 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck17596, Integer.Sparse.eval_collectBalanced, rawRowCheck17596]

def rawRow17597 : Integer.Sparse Key := [(key635, -2), (key638, -2), (key635, -2), (key644, -2), (key638, -2), (key644, -2), (key635, 2), (key644, 2), (key644, 2), (key638, 2), (key644, 2), (key644, 2), (key633, 2), (key638, 2), (key638, 2), (key638, -6), (key633, 2), (key635, 2), (key635, 2), (key635, -6)]

theorem rawRowCheck17597 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form18 = rawRow17597 := by decide +kernel

def row17597 : Integer.Sparse Key := [(key633, 4), (key635, -4), (key638, -4), (key644, 4)]

theorem rowCheck17597 : row17597 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17597 := by decide +kernel

theorem rowEval17597 (x : Key → ℝ) : Integer.Sparse.eval row17597 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17597, Integer.Sparse.eval_collectBalanced, rawRowCheck17597]

def rawRow17598 : Integer.Sparse Key := [(key638, -2), (key635, -2), (key644, -2), (key635, -2), (key644, -2), (key638, -2), (key644, 2), (key635, 2), (key644, 2), (key644, 2), (key638, 2), (key644, 2), (key638, 2), (key633, 2), (key638, 2), (key638, -6), (key635, 2), (key633, 2), (key635, 2), (key635, -6)]

theorem rawRowCheck17598 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form18 = rawRow17598 := by decide +kernel

def row17598 : Integer.Sparse Key := [(key633, 4), (key635, -4), (key638, -4), (key644, 4)]

theorem rowCheck17598 : row17598 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17598 := by decide +kernel

theorem rowEval17598 (x : Key → ℝ) : Integer.Sparse.eval row17598 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck17598, Integer.Sparse.eval_collectBalanced, rawRowCheck17598]

def rawRow17599 : Integer.Sparse Key := [(key644, -2), (key644, -2), (key638, -2), (key638, -2), (key635, -2), (key635, -2), (key644, 2), (key644, 2), (key635, 2), (key644, 2), (key644, 2), (key638, 2), (key638, 2), (key638, 2), (key633, 2), (key638, -6), (key635, 2), (key635, 2), (key633, 2), (key635, -6)]

theorem rawRowCheck17599 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form18 = rawRow17599 := by decide +kernel

def row17599 : Integer.Sparse Key := [(key633, 4), (key635, -4), (key638, -4), (key644, 4)]

theorem rowCheck17599 : row17599 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17599 := by decide +kernel

theorem rowEval17599 (x : Key → ℝ) : Integer.Sparse.eval row17599 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck17599, Integer.Sparse.eval_collectBalanced, rawRowCheck17599]

def rawRow17600 : Integer.Sparse Key := [(key644, -2), (key644, -2), (key644, -2), (key644, -2), (key644, -2), (key644, -2), (key638, 2), (key638, 2), (key638, 2), (key635, 2), (key635, 2), (key635, 2), (key638, 2), (key638, 2), (key638, 2), (key633, -6), (key635, 2), (key635, 2), (key635, 2), (key633, -6)]

theorem rawRowCheck17600 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form18 = rawRow17600 := by decide +kernel

def row17600 : Integer.Sparse Key := [(key633, -12), (key635, 12), (key638, 12), (key644, -12)]

theorem rowCheck17600 : row17600 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17600 := by decide +kernel

theorem rowEval17600 (x : Key → ℝ) : Integer.Sparse.eval row17600 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck17600, Integer.Sparse.eval_collectBalanced, rawRowCheck17600]

def rawRow17601 : Integer.Sparse Key := [(key291, 4), (key294, 4), (key294, 4), (key294, -4), (key294, -4), (key298, -4), (key294, -4), (key294, -4), (key298, -4), (key298, 12)]

theorem rawRowCheck17601 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form19 = rawRow17601 := by decide +kernel

def row17601 : Integer.Sparse Key := [(key291, 4), (key294, -8), (key298, 4)]

theorem rowCheck17601 : row17601 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17601 := by decide +kernel

theorem rowEval17601 (x : Key → ℝ) : Integer.Sparse.eval row17601 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17601, Integer.Sparse.eval_collectBalanced, rawRowCheck17601]

def rawRow17602 : Integer.Sparse Key := [(key294, 4), (key291, 4), (key294, 4), (key294, -4), (key298, -4), (key294, -4), (key294, -4), (key298, -4), (key294, -4), (key298, 12)]

theorem rawRowCheck17602 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form19 = rawRow17602 := by decide +kernel

def row17602 : Integer.Sparse Key := [(key291, 4), (key294, -8), (key298, 4)]

theorem rowCheck17602 : row17602 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17602 := by decide +kernel

theorem rowEval17602 (x : Key → ℝ) : Integer.Sparse.eval row17602 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17602, Integer.Sparse.eval_collectBalanced, rawRowCheck17602]

def rawRow17603 : Integer.Sparse Key := [(key294, 4), (key294, 4), (key291, 4), (key298, -4), (key294, -4), (key294, -4), (key298, -4), (key294, -4), (key294, -4), (key298, 12)]

theorem rawRowCheck17603 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form19 = rawRow17603 := by decide +kernel

def row17603 : Integer.Sparse Key := [(key291, 4), (key294, -8), (key298, 4)]

theorem rowCheck17603 : row17603 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17603 := by decide +kernel

theorem rowEval17603 (x : Key → ℝ) : Integer.Sparse.eval row17603 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form19) x := by
  rw [rowCheck17603, Integer.Sparse.eval_collectBalanced, rawRowCheck17603]

def rawRow17604 : Integer.Sparse Key := [(key294, 4), (key294, 4), (key298, 4), (key291, -4), (key294, -4), (key294, -4), (key294, -4), (key298, -4), (key298, -4), (key294, 12)]

theorem rawRowCheck17604 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form19 = rawRow17604 := by decide +kernel

def row17604 : Integer.Sparse Key := [(key291, -4), (key294, 8), (key298, -4)]

theorem rowCheck17604 : row17604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17604 := by decide +kernel

theorem rowEval17604 (x : Key → ℝ) : Integer.Sparse.eval row17604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17604, Integer.Sparse.eval_collectBalanced, rawRowCheck17604]

def rawRow17605 : Integer.Sparse Key := [(key294, 4), (key298, 4), (key294, 4), (key294, -4), (key291, -4), (key294, -4), (key298, -4), (key294, -4), (key298, -4), (key294, 12)]

theorem rawRowCheck17605 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form19 = rawRow17605 := by decide +kernel

def row17605 : Integer.Sparse Key := [(key291, -4), (key294, 8), (key298, -4)]

theorem rowCheck17605 : row17605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17605 := by decide +kernel

theorem rowEval17605 (x : Key → ℝ) : Integer.Sparse.eval row17605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form19) x := by
  rw [rowCheck17605, Integer.Sparse.eval_collectBalanced, rawRowCheck17605]

def rawRow17606 : Integer.Sparse Key := [(key298, 4), (key294, 4), (key294, 4), (key294, -4), (key294, -4), (key291, -4), (key298, -4), (key298, -4), (key294, -4), (key294, 12)]

theorem rawRowCheck17606 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form19 = rawRow17606 := by decide +kernel

def row17606 : Integer.Sparse Key := [(key291, -4), (key294, 8), (key298, -4)]

theorem rowCheck17606 : row17606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17606 := by decide +kernel

theorem rowEval17606 (x : Key → ℝ) : Integer.Sparse.eval row17606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form19) x := by
  rw [rowCheck17606, Integer.Sparse.eval_collectBalanced, rawRowCheck17606]

def rawRow17607 : Integer.Sparse Key := [(key294, 4), (key294, 4), (key298, 4), (key294, -4), (key298, -4), (key298, -4), (key291, -4), (key294, -4), (key294, -4), (key294, 12)]

theorem rawRowCheck17607 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form19 = rawRow17607 := by decide +kernel

def row17607 : Integer.Sparse Key := [(key291, -4), (key294, 8), (key298, -4)]

theorem rowCheck17607 : row17607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17607 := by decide +kernel

theorem rowEval17607 (x : Key → ℝ) : Integer.Sparse.eval row17607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17607, Integer.Sparse.eval_collectBalanced, rawRowCheck17607]

def rawRow17608 : Integer.Sparse Key := [(key294, 4), (key298, 4), (key294, 4), (key298, -4), (key294, -4), (key298, -4), (key294, -4), (key291, -4), (key294, -4), (key294, 12)]

theorem rawRowCheck17608 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form19 = rawRow17608 := by decide +kernel

def row17608 : Integer.Sparse Key := [(key291, -4), (key294, 8), (key298, -4)]

theorem rowCheck17608 : row17608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17608 := by decide +kernel

theorem rowEval17608 (x : Key → ℝ) : Integer.Sparse.eval row17608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form19) x := by
  rw [rowCheck17608, Integer.Sparse.eval_collectBalanced, rawRowCheck17608]

def rawRow17609 : Integer.Sparse Key := [(key298, 4), (key294, 4), (key294, 4), (key298, -4), (key298, -4), (key294, -4), (key294, -4), (key294, -4), (key291, -4), (key294, 12)]

theorem rawRowCheck17609 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form19 = rawRow17609 := by decide +kernel

def row17609 : Integer.Sparse Key := [(key291, -4), (key294, 8), (key298, -4)]

theorem rowCheck17609 : row17609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17609 := by decide +kernel

theorem rowEval17609 (x : Key → ℝ) : Integer.Sparse.eval row17609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form19) x := by
  rw [rowCheck17609, Integer.Sparse.eval_collectBalanced, rawRowCheck17609]

def rawRow17610 : Integer.Sparse Key := [(key298, 4), (key298, 4), (key298, 4), (key294, -4), (key294, -4), (key294, -4), (key294, -4), (key294, -4), (key294, -4), (key291, 12)]

theorem rawRowCheck17610 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form19 = rawRow17610 := by decide +kernel

def row17610 : Integer.Sparse Key := [(key291, 12), (key294, -24), (key298, 12)]

theorem rowCheck17610 : row17610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17610 := by decide +kernel

theorem rowEval17610 (x : Key → ℝ) : Integer.Sparse.eval row17610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form19) x := by
  rw [rowCheck17610, Integer.Sparse.eval_collectBalanced, rawRowCheck17610]

def rawRow17611 : Integer.Sparse Key := [(key2237, 4), (key2237, 4), (key2260, 4), (key2271, -2), (key2273, -2), (key2271, -2), (key2295, -2), (key2273, -2), (key2295, -2), (key2271, -2), (key2273, -2), (key2271, -2), (key2295, -2), (key2273, -2), (key2295, -2), (key2325, 4), (key2325, 4), (key2337, 4)]

theorem rawRowCheck17611 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form0 = rawRow17611 := by decide +kernel

def row17611 : Integer.Sparse Key := [(key2237, 8), (key2260, 4), (key2271, -8), (key2273, -8), (key2295, -8), (key2325, 8), (key2337, 4)]

theorem rowCheck17611 : row17611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17611 := by decide +kernel

theorem rowEval17611 (x : Key → ℝ) : Integer.Sparse.eval row17611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17611, Integer.Sparse.eval_collectBalanced, rawRowCheck17611]

def rawRow17612 : Integer.Sparse Key := [(key2237, 4), (key2260, 4), (key2237, 4), (key2273, -2), (key2271, -2), (key2295, -2), (key2271, -2), (key2295, -2), (key2273, -2), (key2273, -2), (key2271, -2), (key2295, -2), (key2271, -2), (key2295, -2), (key2273, -2), (key2325, 4), (key2337, 4), (key2325, 4)]

theorem rawRowCheck17612 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form0 = rawRow17612 := by decide +kernel

def row17612 : Integer.Sparse Key := [(key2237, 8), (key2260, 4), (key2271, -8), (key2273, -8), (key2295, -8), (key2325, 8), (key2337, 4)]

theorem rowCheck17612 : row17612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17612 := by decide +kernel

theorem rowEval17612 (x : Key → ℝ) : Integer.Sparse.eval row17612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17612, Integer.Sparse.eval_collectBalanced, rawRowCheck17612]

def rawRow17613 : Integer.Sparse Key := [(key2260, 4), (key2237, 4), (key2237, 4), (key2295, -2), (key2295, -2), (key2273, -2), (key2273, -2), (key2271, -2), (key2271, -2), (key2295, -2), (key2295, -2), (key2273, -2), (key2273, -2), (key2271, -2), (key2271, -2), (key2337, 4), (key2325, 4), (key2325, 4)]

theorem rawRowCheck17613 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form0 = rawRow17613 := by decide +kernel

def row17613 : Integer.Sparse Key := [(key2237, 8), (key2260, 4), (key2271, -8), (key2273, -8), (key2295, -8), (key2325, 8), (key2337, 4)]

theorem rowCheck17613 : row17613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17613 := by decide +kernel

theorem rowEval17613 (x : Key → ℝ) : Integer.Sparse.eval row17613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17613, Integer.Sparse.eval_collectBalanced, rawRowCheck17613]

def rawRow17614 : Integer.Sparse Key := [(key1992, 4), (key2271, 4), (key2295, 4), (key1992, -2), (key1995, -2), (key2237, -2), (key2260, -2), (key2273, -2), (key2295, -2), (key2002, -2), (key2004, -2), (key2271, -2), (key2295, -2), (key2325, -2), (key2337, -2), (key2004, 4), (key2273, 4), (key2295, 4)]

theorem rawRowCheck17614 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form0 = rawRow17614 := by decide +kernel

def row17614 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, -2), (key2271, 2), (key2273, 2), (key2295, 4), (key2325, -2), (key2337, -2)]

theorem rowCheck17614 : row17614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17614 := by decide +kernel

theorem rowEval17614 (x : Key → ℝ) : Integer.Sparse.eval row17614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17614, Integer.Sparse.eval_collectBalanced, rawRowCheck17614]

def rawRow17615 : Integer.Sparse Key := [(key1992, 4), (key2295, 4), (key2271, 4), (key1995, -2), (key1992, -2), (key2260, -2), (key2237, -2), (key2295, -2), (key2273, -2), (key2004, -2), (key2002, -2), (key2295, -2), (key2271, -2), (key2337, -2), (key2325, -2), (key2004, 4), (key2295, 4), (key2273, 4)]

theorem rawRowCheck17615 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form0 = rawRow17615 := by decide +kernel

def row17615 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, -2), (key2271, 2), (key2273, 2), (key2295, 4), (key2325, -2), (key2337, -2)]

theorem rowCheck17615 : row17615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17615 := by decide +kernel

theorem rowEval17615 (x : Key → ℝ) : Integer.Sparse.eval row17615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17615, Integer.Sparse.eval_collectBalanced, rawRowCheck17615]

def rawRow17616 : Integer.Sparse Key := [(key2271, 4), (key1992, 4), (key2295, 4), (key2237, -2), (key2273, -2), (key1992, -2), (key2295, -2), (key1995, -2), (key2260, -2), (key2271, -2), (key2325, -2), (key2002, -2), (key2337, -2), (key2004, -2), (key2295, -2), (key2273, 4), (key2004, 4), (key2295, 4)]

theorem rawRowCheck17616 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form0 = rawRow17616 := by decide +kernel

def row17616 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, -2), (key2271, 2), (key2273, 2), (key2295, 4), (key2325, -2), (key2337, -2)]

theorem rowCheck17616 : row17616 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17616 := by decide +kernel

theorem rowEval17616 (x : Key → ℝ) : Integer.Sparse.eval row17616 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17616, Integer.Sparse.eval_collectBalanced, rawRowCheck17616]

def rawRow17617 : Integer.Sparse Key := [(key2271, 4), (key2295, 4), (key1992, 4), (key2273, -2), (key2237, -2), (key2295, -2), (key1992, -2), (key2260, -2), (key1995, -2), (key2325, -2), (key2271, -2), (key2337, -2), (key2002, -2), (key2295, -2), (key2004, -2), (key2273, 4), (key2295, 4), (key2004, 4)]

theorem rawRowCheck17617 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form0 = rawRow17617 := by decide +kernel

def row17617 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, -2), (key2271, 2), (key2273, 2), (key2295, 4), (key2325, -2), (key2337, -2)]

theorem rowCheck17617 : row17617 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17617 := by decide +kernel

theorem rowEval17617 (x : Key → ℝ) : Integer.Sparse.eval row17617 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17617, Integer.Sparse.eval_collectBalanced, rawRowCheck17617]

def rawRow17618 : Integer.Sparse Key := [(key2295, 4), (key1992, 4), (key2271, 4), (key2260, -2), (key2295, -2), (key1995, -2), (key2273, -2), (key1992, -2), (key2237, -2), (key2295, -2), (key2337, -2), (key2004, -2), (key2325, -2), (key2002, -2), (key2271, -2), (key2295, 4), (key2004, 4), (key2273, 4)]

theorem rawRowCheck17618 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form0 = rawRow17618 := by decide +kernel

def row17618 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, -2), (key2271, 2), (key2273, 2), (key2295, 4), (key2325, -2), (key2337, -2)]

theorem rowCheck17618 : row17618 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17618 := by decide +kernel

theorem rowEval17618 (x : Key → ℝ) : Integer.Sparse.eval row17618 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17618, Integer.Sparse.eval_collectBalanced, rawRowCheck17618]

def rawRow17619 : Integer.Sparse Key := [(key2295, 4), (key2271, 4), (key1992, 4), (key2295, -2), (key2260, -2), (key2273, -2), (key1995, -2), (key2237, -2), (key1992, -2), (key2337, -2), (key2295, -2), (key2325, -2), (key2004, -2), (key2271, -2), (key2002, -2), (key2295, 4), (key2273, 4), (key2004, 4)]

theorem rawRowCheck17619 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form0 = rawRow17619 := by decide +kernel

def row17619 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, -2), (key2271, 2), (key2273, 2), (key2295, 4), (key2325, -2), (key2337, -2)]

theorem rowCheck17619 : row17619 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17619 := by decide +kernel

theorem rowEval17619 (x : Key → ℝ) : Integer.Sparse.eval row17619 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17619, Integer.Sparse.eval_collectBalanced, rawRowCheck17619]

def rawRow17620 : Integer.Sparse Key := [(key1992, 4), (key2271, 4), (key2295, 4), (key2002, -2), (key2004, -2), (key2271, -2), (key2295, -2), (key2325, -2), (key2337, -2), (key1992, -2), (key1995, -2), (key2237, -2), (key2260, -2), (key2273, -2), (key2295, -2), (key2004, 4), (key2273, 4), (key2295, 4)]

theorem rawRowCheck17620 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form0 = rawRow17620 := by decide +kernel

def row17620 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, -2), (key2271, 2), (key2273, 2), (key2295, 4), (key2325, -2), (key2337, -2)]

theorem rowCheck17620 : row17620 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17620 := by decide +kernel

theorem rowEval17620 (x : Key → ℝ) : Integer.Sparse.eval row17620 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17620, Integer.Sparse.eval_collectBalanced, rawRowCheck17620]

def rawRow17621 : Integer.Sparse Key := [(key1992, 4), (key2295, 4), (key2271, 4), (key2004, -2), (key2002, -2), (key2295, -2), (key2271, -2), (key2337, -2), (key2325, -2), (key1995, -2), (key1992, -2), (key2260, -2), (key2237, -2), (key2295, -2), (key2273, -2), (key2004, 4), (key2295, 4), (key2273, 4)]

theorem rawRowCheck17621 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form0 = rawRow17621 := by decide +kernel

def row17621 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, -2), (key2271, 2), (key2273, 2), (key2295, 4), (key2325, -2), (key2337, -2)]

theorem rowCheck17621 : row17621 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17621 := by decide +kernel

theorem rowEval17621 (x : Key → ℝ) : Integer.Sparse.eval row17621 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17621, Integer.Sparse.eval_collectBalanced, rawRowCheck17621]

def rawRow17622 : Integer.Sparse Key := [(key2271, 4), (key1992, 4), (key2295, 4), (key2271, -2), (key2325, -2), (key2002, -2), (key2337, -2), (key2004, -2), (key2295, -2), (key2237, -2), (key2273, -2), (key1992, -2), (key2295, -2), (key1995, -2), (key2260, -2), (key2273, 4), (key2004, 4), (key2295, 4)]

theorem rawRowCheck17622 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form0 = rawRow17622 := by decide +kernel

def row17622 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, -2), (key2271, 2), (key2273, 2), (key2295, 4), (key2325, -2), (key2337, -2)]

theorem rowCheck17622 : row17622 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17622 := by decide +kernel

theorem rowEval17622 (x : Key → ℝ) : Integer.Sparse.eval row17622 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17622, Integer.Sparse.eval_collectBalanced, rawRowCheck17622]

def rawRow17623 : Integer.Sparse Key := [(key2271, 4), (key2295, 4), (key1992, 4), (key2325, -2), (key2271, -2), (key2337, -2), (key2002, -2), (key2295, -2), (key2004, -2), (key2273, -2), (key2237, -2), (key2295, -2), (key1992, -2), (key2260, -2), (key1995, -2), (key2273, 4), (key2295, 4), (key2004, 4)]

theorem rawRowCheck17623 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form0 = rawRow17623 := by decide +kernel

def row17623 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, -2), (key2271, 2), (key2273, 2), (key2295, 4), (key2325, -2), (key2337, -2)]

theorem rowCheck17623 : row17623 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17623 := by decide +kernel

theorem rowEval17623 (x : Key → ℝ) : Integer.Sparse.eval row17623 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17623, Integer.Sparse.eval_collectBalanced, rawRowCheck17623]

def rawRow17624 : Integer.Sparse Key := [(key2295, 4), (key1992, 4), (key2271, 4), (key2295, -2), (key2337, -2), (key2004, -2), (key2325, -2), (key2002, -2), (key2271, -2), (key2260, -2), (key2295, -2), (key1995, -2), (key2273, -2), (key1992, -2), (key2237, -2), (key2295, 4), (key2004, 4), (key2273, 4)]

theorem rawRowCheck17624 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form0 = rawRow17624 := by decide +kernel

def row17624 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, -2), (key2271, 2), (key2273, 2), (key2295, 4), (key2325, -2), (key2337, -2)]

theorem rowCheck17624 : row17624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17624 := by decide +kernel

theorem rowEval17624 (x : Key → ℝ) : Integer.Sparse.eval row17624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17624, Integer.Sparse.eval_collectBalanced, rawRowCheck17624]

def rawRow17625 : Integer.Sparse Key := [(key2295, 4), (key2271, 4), (key1992, 4), (key2337, -2), (key2295, -2), (key2325, -2), (key2004, -2), (key2271, -2), (key2002, -2), (key2295, -2), (key2260, -2), (key2273, -2), (key1995, -2), (key2237, -2), (key1992, -2), (key2295, 4), (key2273, 4), (key2004, 4)]

theorem rawRowCheck17625 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form0 = rawRow17625 := by decide +kernel

def row17625 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, -2), (key2271, 2), (key2273, 2), (key2295, 4), (key2325, -2), (key2337, -2)]

theorem rowCheck17625 : row17625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17625 := by decide +kernel

theorem rowEval17625 (x : Key → ℝ) : Integer.Sparse.eval row17625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17625, Integer.Sparse.eval_collectBalanced, rawRowCheck17625]

def rawRow17626 : Integer.Sparse Key := [(key2002, 4), (key2002, 4), (key2337, 4), (key1992, -2), (key2004, -2), (key1992, -2), (key2295, -2), (key2004, -2), (key2295, -2), (key1992, -2), (key2004, -2), (key1992, -2), (key2295, -2), (key2004, -2), (key2295, -2), (key1995, 4), (key1995, 4), (key2260, 4)]

theorem rawRowCheck17626 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form0 = rawRow17626 := by decide +kernel

def row17626 : Integer.Sparse Key := [(key1992, -8), (key1995, 8), (key2002, 8), (key2004, -8), (key2260, 4), (key2295, -8), (key2337, 4)]

theorem rowCheck17626 : row17626 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17626 := by decide +kernel

theorem rowEval17626 (x : Key → ℝ) : Integer.Sparse.eval row17626 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17626, Integer.Sparse.eval_collectBalanced, rawRowCheck17626]

def rawRow17627 : Integer.Sparse Key := [(key2002, 4), (key2337, 4), (key2002, 4), (key2004, -2), (key1992, -2), (key2295, -2), (key1992, -2), (key2295, -2), (key2004, -2), (key2004, -2), (key1992, -2), (key2295, -2), (key1992, -2), (key2295, -2), (key2004, -2), (key1995, 4), (key2260, 4), (key1995, 4)]

theorem rawRowCheck17627 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form0 = rawRow17627 := by decide +kernel

def row17627 : Integer.Sparse Key := [(key1992, -8), (key1995, 8), (key2002, 8), (key2004, -8), (key2260, 4), (key2295, -8), (key2337, 4)]

theorem rowCheck17627 : row17627 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17627 := by decide +kernel

theorem rowEval17627 (x : Key → ℝ) : Integer.Sparse.eval row17627 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17627, Integer.Sparse.eval_collectBalanced, rawRowCheck17627]

def rawRow17628 : Integer.Sparse Key := [(key2337, 4), (key2002, 4), (key2002, 4), (key2295, -2), (key2295, -2), (key2004, -2), (key2004, -2), (key1992, -2), (key1992, -2), (key2295, -2), (key2295, -2), (key2004, -2), (key2004, -2), (key1992, -2), (key1992, -2), (key2260, 4), (key1995, 4), (key1995, 4)]

theorem rawRowCheck17628 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form0 = rawRow17628 := by decide +kernel

def row17628 : Integer.Sparse Key := [(key1992, -8), (key1995, 8), (key2002, 8), (key2004, -8), (key2260, 4), (key2295, -8), (key2337, 4)]

theorem rowCheck17628 : row17628 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17628 := by decide +kernel

theorem rowEval17628 (x : Key → ℝ) : Integer.Sparse.eval row17628 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17628, Integer.Sparse.eval_collectBalanced, rawRowCheck17628]

def rawRow17629 : Integer.Sparse Key := [(key60, -2), (key62, -2), (key62, -2), (key72, 6), (key704, -2), (key709, -2), (key709, -2), (key858, 2), (key863, 2), (key858, 2), (key885, 2), (key863, 2), (key885, 2), (key923, -2), (key923, -2), (key940, -2), (key723, 6), (key923, -2), (key923, -2), (key940, -2)]

theorem rawRowCheck17629 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form1 = rawRow17629 := by decide +kernel

def row17629 : Integer.Sparse Key := [(key60, -2), (key62, -4), (key72, 6), (key704, -2), (key709, -4), (key723, 6), (key858, 4), (key863, 4), (key885, 4), (key923, -8), (key940, -4)]

theorem rowCheck17629 : row17629 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17629 := by decide +kernel

theorem rowEval17629 (x : Key → ℝ) : Integer.Sparse.eval row17629 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17629, Integer.Sparse.eval_collectBalanced, rawRowCheck17629]

def rawRow17630 : Integer.Sparse Key := [(key62, -2), (key60, -2), (key62, -2), (key72, 6), (key709, -2), (key704, -2), (key709, -2), (key863, 2), (key858, 2), (key885, 2), (key858, 2), (key885, 2), (key863, 2), (key923, -2), (key940, -2), (key923, -2), (key723, 6), (key923, -2), (key940, -2), (key923, -2)]

theorem rawRowCheck17630 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form1 = rawRow17630 := by decide +kernel

def row17630 : Integer.Sparse Key := [(key60, -2), (key62, -4), (key72, 6), (key704, -2), (key709, -4), (key723, 6), (key858, 4), (key863, 4), (key885, 4), (key923, -8), (key940, -4)]

theorem rowCheck17630 : row17630 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17630 := by decide +kernel

theorem rowEval17630 (x : Key → ℝ) : Integer.Sparse.eval row17630 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck17630, Integer.Sparse.eval_collectBalanced, rawRowCheck17630]

def rawRow17631 : Integer.Sparse Key := [(key62, -2), (key62, -2), (key60, -2), (key72, 6), (key709, -2), (key709, -2), (key704, -2), (key885, 2), (key885, 2), (key863, 2), (key863, 2), (key858, 2), (key858, 2), (key940, -2), (key923, -2), (key923, -2), (key723, 6), (key940, -2), (key923, -2), (key923, -2)]

theorem rawRowCheck17631 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form1 = rawRow17631 := by decide +kernel

def row17631 : Integer.Sparse Key := [(key60, -2), (key62, -4), (key72, 6), (key704, -2), (key709, -4), (key723, 6), (key858, 4), (key863, 4), (key885, 4), (key923, -8), (key940, -4)]

theorem rowCheck17631 : row17631 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17631 := by decide +kernel

theorem rowEval17631 (x : Key → ℝ) : Integer.Sparse.eval row17631 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck17631, Integer.Sparse.eval_collectBalanced, rawRowCheck17631]

def rawRow17632 : Integer.Sparse Key := [(key60, -2), (key62, -2), (key72, -2), (key62, 6), (key858, -2), (key863, -2), (key923, -2), (key704, 2), (key709, 2), (key858, 2), (key885, 2), (key923, 2), (key940, 2), (key709, -2), (key863, -2), (key885, -2), (key923, 6), (key723, -2), (key923, -2), (key940, -2)]

theorem rawRowCheck17632 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form1 = rawRow17632 := by decide +kernel

def row17632 : Integer.Sparse Key := [(key60, -2), (key62, 4), (key72, -2), (key704, 2), (key723, -2), (key863, -4), (key923, 4)]

theorem rowCheck17632 : row17632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17632 := by decide +kernel

theorem rowEval17632 (x : Key → ℝ) : Integer.Sparse.eval row17632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17632, Integer.Sparse.eval_collectBalanced, rawRowCheck17632]

def rawRow17633 : Integer.Sparse Key := [(key62, -2), (key60, -2), (key72, -2), (key62, 6), (key863, -2), (key858, -2), (key923, -2), (key709, 2), (key704, 2), (key885, 2), (key858, 2), (key940, 2), (key923, 2), (key709, -2), (key885, -2), (key863, -2), (key923, 6), (key723, -2), (key940, -2), (key923, -2)]

theorem rawRowCheck17633 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form1 = rawRow17633 := by decide +kernel

def row17633 : Integer.Sparse Key := [(key60, -2), (key62, 4), (key72, -2), (key704, 2), (key723, -2), (key863, -4), (key923, 4)]

theorem rowCheck17633 : row17633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17633 := by decide +kernel

theorem rowEval17633 (x : Key → ℝ) : Integer.Sparse.eval row17633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck17633, Integer.Sparse.eval_collectBalanced, rawRowCheck17633]

def rawRow17634 : Integer.Sparse Key := [(key60, -2), (key72, -2), (key62, -2), (key62, 6), (key858, -2), (key923, -2), (key863, -2), (key858, 2), (key923, 2), (key704, 2), (key940, 2), (key709, 2), (key885, 2), (key863, -2), (key709, -2), (key885, -2), (key923, 6), (key923, -2), (key723, -2), (key940, -2)]

theorem rawRowCheck17634 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form1 = rawRow17634 := by decide +kernel

def row17634 : Integer.Sparse Key := [(key60, -2), (key62, 4), (key72, -2), (key704, 2), (key723, -2), (key863, -4), (key923, 4)]

theorem rowCheck17634 : row17634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17634 := by decide +kernel

theorem rowEval17634 (x : Key → ℝ) : Integer.Sparse.eval row17634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17634, Integer.Sparse.eval_collectBalanced, rawRowCheck17634]

def rawRow17635 : Integer.Sparse Key := [(key72, -2), (key60, -2), (key62, -2), (key62, 6), (key923, -2), (key858, -2), (key863, -2), (key923, 2), (key858, 2), (key940, 2), (key704, 2), (key885, 2), (key709, 2), (key863, -2), (key885, -2), (key709, -2), (key923, 6), (key923, -2), (key940, -2), (key723, -2)]

theorem rawRowCheck17635 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form1 = rawRow17635 := by decide +kernel

def row17635 : Integer.Sparse Key := [(key60, -2), (key62, 4), (key72, -2), (key704, 2), (key723, -2), (key863, -4), (key923, 4)]

theorem rowCheck17635 : row17635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17635 := by decide +kernel

theorem rowEval17635 (x : Key → ℝ) : Integer.Sparse.eval row17635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17635, Integer.Sparse.eval_collectBalanced, rawRowCheck17635]

def rawRow17636 : Integer.Sparse Key := [(key62, -2), (key72, -2), (key60, -2), (key62, 6), (key863, -2), (key923, -2), (key858, -2), (key885, 2), (key940, 2), (key709, 2), (key923, 2), (key704, 2), (key858, 2), (key885, -2), (key709, -2), (key863, -2), (key923, 6), (key940, -2), (key723, -2), (key923, -2)]

theorem rawRowCheck17636 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form1 = rawRow17636 := by decide +kernel

def row17636 : Integer.Sparse Key := [(key60, -2), (key62, 4), (key72, -2), (key704, 2), (key723, -2), (key863, -4), (key923, 4)]

theorem rowCheck17636 : row17636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17636 := by decide +kernel

theorem rowEval17636 (x : Key → ℝ) : Integer.Sparse.eval row17636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck17636, Integer.Sparse.eval_collectBalanced, rawRowCheck17636]

def rawRow17637 : Integer.Sparse Key := [(key72, -2), (key62, -2), (key60, -2), (key62, 6), (key923, -2), (key863, -2), (key858, -2), (key940, 2), (key885, 2), (key923, 2), (key709, 2), (key858, 2), (key704, 2), (key885, -2), (key863, -2), (key709, -2), (key923, 6), (key940, -2), (key923, -2), (key723, -2)]

theorem rawRowCheck17637 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form1 = rawRow17637 := by decide +kernel

def row17637 : Integer.Sparse Key := [(key60, -2), (key62, 4), (key72, -2), (key704, 2), (key723, -2), (key863, -4), (key923, 4)]

theorem rowCheck17637 : row17637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17637 := by decide +kernel

theorem rowEval17637 (x : Key → ℝ) : Integer.Sparse.eval row17637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17637, Integer.Sparse.eval_collectBalanced, rawRowCheck17637]

def rawRow17638 : Integer.Sparse Key := [(key125, -2), (key127, -2), (key135, -2), (key135, 6), (key60, -2), (key62, -2), (key72, -2), (key704, 2), (key709, 2), (key858, 2), (key885, 2), (key923, 2), (key940, 2), (key723, -2), (key923, -2), (key940, -2), (key709, 6), (key709, -2), (key863, -2), (key885, -2)]

theorem rawRowCheck17638 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form1 = rawRow17638 := by decide +kernel

def row17638 : Integer.Sparse Key := [(key60, -2), (key62, -2), (key72, -2), (key125, -2), (key127, -2), (key135, 4), (key704, 2), (key709, 6), (key723, -2), (key858, 2), (key863, -2)]

theorem rowCheck17638 : row17638 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17638 := by decide +kernel

theorem rowEval17638 (x : Key → ℝ) : Integer.Sparse.eval row17638 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17638, Integer.Sparse.eval_collectBalanced, rawRowCheck17638]

def rawRow17639 : Integer.Sparse Key := [(key127, -2), (key125, -2), (key135, -2), (key135, 6), (key62, -2), (key60, -2), (key72, -2), (key709, 2), (key704, 2), (key885, 2), (key858, 2), (key940, 2), (key923, 2), (key723, -2), (key940, -2), (key923, -2), (key709, 6), (key709, -2), (key885, -2), (key863, -2)]

theorem rawRowCheck17639 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form1 = rawRow17639 := by decide +kernel

def row17639 : Integer.Sparse Key := [(key60, -2), (key62, -2), (key72, -2), (key125, -2), (key127, -2), (key135, 4), (key704, 2), (key709, 6), (key723, -2), (key858, 2), (key863, -2)]

theorem rowCheck17639 : row17639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17639 := by decide +kernel

theorem rowEval17639 (x : Key → ℝ) : Integer.Sparse.eval row17639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck17639, Integer.Sparse.eval_collectBalanced, rawRowCheck17639]

def rawRow17640 : Integer.Sparse Key := [(key125, -2), (key135, -2), (key127, -2), (key135, 6), (key60, -2), (key72, -2), (key62, -2), (key858, 2), (key923, 2), (key704, 2), (key940, 2), (key709, 2), (key885, 2), (key923, -2), (key723, -2), (key940, -2), (key709, 6), (key863, -2), (key709, -2), (key885, -2)]

theorem rawRowCheck17640 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form1 = rawRow17640 := by decide +kernel

def row17640 : Integer.Sparse Key := [(key60, -2), (key62, -2), (key72, -2), (key125, -2), (key127, -2), (key135, 4), (key704, 2), (key709, 6), (key723, -2), (key858, 2), (key863, -2)]

theorem rowCheck17640 : row17640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17640 := by decide +kernel

theorem rowEval17640 (x : Key → ℝ) : Integer.Sparse.eval row17640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17640, Integer.Sparse.eval_collectBalanced, rawRowCheck17640]

def rawRow17641 : Integer.Sparse Key := [(key135, -2), (key125, -2), (key127, -2), (key135, 6), (key72, -2), (key60, -2), (key62, -2), (key923, 2), (key858, 2), (key940, 2), (key704, 2), (key885, 2), (key709, 2), (key923, -2), (key940, -2), (key723, -2), (key709, 6), (key863, -2), (key885, -2), (key709, -2)]

theorem rawRowCheck17641 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form1 = rawRow17641 := by decide +kernel

def row17641 : Integer.Sparse Key := [(key60, -2), (key62, -2), (key72, -2), (key125, -2), (key127, -2), (key135, 4), (key704, 2), (key709, 6), (key723, -2), (key858, 2), (key863, -2)]

theorem rowCheck17641 : row17641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17641 := by decide +kernel

theorem rowEval17641 (x : Key → ℝ) : Integer.Sparse.eval row17641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17641, Integer.Sparse.eval_collectBalanced, rawRowCheck17641]

def rawRow17642 : Integer.Sparse Key := [(key127, -2), (key135, -2), (key125, -2), (key135, 6), (key62, -2), (key72, -2), (key60, -2), (key885, 2), (key940, 2), (key709, 2), (key923, 2), (key704, 2), (key858, 2), (key940, -2), (key723, -2), (key923, -2), (key709, 6), (key885, -2), (key709, -2), (key863, -2)]

theorem rawRowCheck17642 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form1 = rawRow17642 := by decide +kernel

def row17642 : Integer.Sparse Key := [(key60, -2), (key62, -2), (key72, -2), (key125, -2), (key127, -2), (key135, 4), (key704, 2), (key709, 6), (key723, -2), (key858, 2), (key863, -2)]

theorem rowCheck17642 : row17642 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17642 := by decide +kernel

theorem rowEval17642 (x : Key → ℝ) : Integer.Sparse.eval row17642 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck17642, Integer.Sparse.eval_collectBalanced, rawRowCheck17642]

def rawRow17643 : Integer.Sparse Key := [(key135, -2), (key127, -2), (key125, -2), (key135, 6), (key72, -2), (key62, -2), (key60, -2), (key940, 2), (key885, 2), (key923, 2), (key709, 2), (key858, 2), (key704, 2), (key940, -2), (key923, -2), (key723, -2), (key709, 6), (key885, -2), (key863, -2), (key709, -2)]

theorem rawRowCheck17643 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form1 = rawRow17643 := by decide +kernel

def row17643 : Integer.Sparse Key := [(key60, -2), (key62, -2), (key72, -2), (key125, -2), (key127, -2), (key135, 4), (key704, 2), (key709, 6), (key723, -2), (key858, 2), (key863, -2)]

theorem rowCheck17643 : row17643 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17643 := by decide +kernel

theorem rowEval17643 (x : Key → ℝ) : Integer.Sparse.eval row17643 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17643, Integer.Sparse.eval_collectBalanced, rawRowCheck17643]

def rawRow17644 : Integer.Sparse Key := [(key125, -2), (key135, -2), (key135, -2), (key127, 6), (key125, -2), (key135, -2), (key135, -2), (key60, 2), (key72, 2), (key704, 2), (key940, 2), (key723, 2), (key940, 2), (key709, -2), (key709, -2), (key885, -2), (key863, 6), (key709, -2), (key709, -2), (key885, -2)]

theorem rawRowCheck17644 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form1 = rawRow17644 := by decide +kernel

def row17644 : Integer.Sparse Key := [(key60, 2), (key72, 2), (key125, -4), (key127, 6), (key135, -8), (key704, 2), (key709, -8), (key723, 2), (key863, 6), (key885, -4), (key940, 4)]

theorem rowCheck17644 : row17644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17644 := by decide +kernel

theorem rowEval17644 (x : Key → ℝ) : Integer.Sparse.eval row17644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17644, Integer.Sparse.eval_collectBalanced, rawRowCheck17644]

def rawRow17645 : Integer.Sparse Key := [(key135, -2), (key125, -2), (key135, -2), (key127, 6), (key135, -2), (key125, -2), (key135, -2), (key72, 2), (key60, 2), (key940, 2), (key704, 2), (key940, 2), (key723, 2), (key709, -2), (key885, -2), (key709, -2), (key863, 6), (key709, -2), (key885, -2), (key709, -2)]

theorem rawRowCheck17645 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form1 = rawRow17645 := by decide +kernel

def row17645 : Integer.Sparse Key := [(key60, 2), (key72, 2), (key125, -4), (key127, 6), (key135, -8), (key704, 2), (key709, -8), (key723, 2), (key863, 6), (key885, -4), (key940, 4)]

theorem rowCheck17645 : row17645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17645 := by decide +kernel

theorem rowEval17645 (x : Key → ℝ) : Integer.Sparse.eval row17645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17645, Integer.Sparse.eval_collectBalanced, rawRowCheck17645]

def rawRow17646 : Integer.Sparse Key := [(key135, -2), (key135, -2), (key125, -2), (key127, 6), (key135, -2), (key135, -2), (key125, -2), (key180, 2), (key180, 2), (key72, 2), (key72, 2), (key704, 2), (key704, 2), (key885, -2), (key709, -2), (key709, -2), (key863, 6), (key885, -2), (key709, -2), (key709, -2)]

theorem rawRowCheck17646 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form1 = rawRow17646 := by decide +kernel

def row17646 : Integer.Sparse Key := [(key72, 4), (key125, -4), (key127, 6), (key135, -8), (key180, 4), (key704, 4), (key709, -8), (key863, 6), (key885, -4)]

theorem rowCheck17646 : row17646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17646 := by decide +kernel

theorem rowEval17646 (x : Key → ℝ) : Integer.Sparse.eval row17646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17646, Integer.Sparse.eval_collectBalanced, rawRowCheck17646]

def rawRow17647 : Integer.Sparse Key := [(key1988, -2), (key1993, -2), (key1993, -2), (key2008, 6), (key1988, -2), (key1993, -2), (key1993, -2), (key2233, 2), (key2238, 2), (key2233, 2), (key2258, 2), (key2238, 2), (key2258, 2), (key2301, -2), (key2301, -2), (key2314, -2), (key2008, 6), (key2301, -2), (key2301, -2), (key2314, -2)]

theorem rawRowCheck17647 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form2 = rawRow17647 := by decide +kernel

def row17647 : Integer.Sparse Key := [(key1988, -4), (key1993, -8), (key2008, 12), (key2233, 4), (key2238, 4), (key2258, 4), (key2301, -8), (key2314, -4)]

theorem rowCheck17647 : row17647 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17647 := by decide +kernel

theorem rowEval17647 (x : Key → ℝ) : Integer.Sparse.eval row17647 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17647, Integer.Sparse.eval_collectBalanced, rawRowCheck17647]

def rawRow17648 : Integer.Sparse Key := [(key1993, -2), (key1988, -2), (key1993, -2), (key2008, 6), (key1993, -2), (key1988, -2), (key1993, -2), (key2238, 2), (key2233, 2), (key2258, 2), (key2233, 2), (key2258, 2), (key2238, 2), (key2301, -2), (key2314, -2), (key2301, -2), (key2008, 6), (key2301, -2), (key2314, -2), (key2301, -2)]

theorem rawRowCheck17648 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form2 = rawRow17648 := by decide +kernel

def row17648 : Integer.Sparse Key := [(key1988, -4), (key1993, -8), (key2008, 12), (key2233, 4), (key2238, 4), (key2258, 4), (key2301, -8), (key2314, -4)]

theorem rowCheck17648 : row17648 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17648 := by decide +kernel

theorem rowEval17648 (x : Key → ℝ) : Integer.Sparse.eval row17648 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck17648, Integer.Sparse.eval_collectBalanced, rawRowCheck17648]

def rawRow17649 : Integer.Sparse Key := [(key1993, -2), (key1993, -2), (key1988, -2), (key2008, 6), (key1993, -2), (key1993, -2), (key1988, -2), (key2258, 2), (key2258, 2), (key2238, 2), (key2238, 2), (key2233, 2), (key2233, 2), (key2314, -2), (key2301, -2), (key2301, -2), (key2008, 6), (key2314, -2), (key2301, -2), (key2301, -2)]

theorem rawRowCheck17649 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form2 = rawRow17649 := by decide +kernel

def row17649 : Integer.Sparse Key := [(key1988, -4), (key1993, -8), (key2008, 12), (key2233, 4), (key2238, 4), (key2258, 4), (key2301, -8), (key2314, -4)]

theorem rowCheck17649 : row17649 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17649 := by decide +kernel

theorem rowEval17649 (x : Key → ℝ) : Integer.Sparse.eval row17649 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck17649, Integer.Sparse.eval_collectBalanced, rawRowCheck17649]

def rawRow17650 : Integer.Sparse Key := [(key1988, -2), (key1993, -2), (key2008, -2), (key1993, 6), (key2233, -2), (key2238, -2), (key2301, -2), (key1988, 2), (key1993, 2), (key2233, 2), (key2258, 2), (key2301, 2), (key2314, 2), (key1993, -2), (key2238, -2), (key2258, -2), (key2301, 6), (key2008, -2), (key2301, -2), (key2314, -2)]

theorem rawRowCheck17650 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form2 = rawRow17650 := by decide +kernel

def row17650 : Integer.Sparse Key := [(key1993, 4), (key2008, -4), (key2238, -4), (key2301, 4)]

theorem rowCheck17650 : row17650 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17650 := by decide +kernel

theorem rowEval17650 (x : Key → ℝ) : Integer.Sparse.eval row17650 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17650, Integer.Sparse.eval_collectBalanced, rawRowCheck17650]

def rawRow17651 : Integer.Sparse Key := [(key1993, -2), (key1988, -2), (key2008, -2), (key1993, 6), (key2238, -2), (key2233, -2), (key2301, -2), (key1993, 2), (key1988, 2), (key2258, 2), (key2233, 2), (key2314, 2), (key2301, 2), (key1993, -2), (key2258, -2), (key2238, -2), (key2301, 6), (key2008, -2), (key2314, -2), (key2301, -2)]

theorem rawRowCheck17651 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form2 = rawRow17651 := by decide +kernel

def row17651 : Integer.Sparse Key := [(key1993, 4), (key2008, -4), (key2238, -4), (key2301, 4)]

theorem rowCheck17651 : row17651 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17651 := by decide +kernel

theorem rowEval17651 (x : Key → ℝ) : Integer.Sparse.eval row17651 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck17651, Integer.Sparse.eval_collectBalanced, rawRowCheck17651]

def rawRow17652 : Integer.Sparse Key := [(key1988, -2), (key2008, -2), (key1993, -2), (key1993, 6), (key2233, -2), (key2301, -2), (key2238, -2), (key2233, 2), (key2301, 2), (key1988, 2), (key2314, 2), (key1993, 2), (key2258, 2), (key2238, -2), (key1993, -2), (key2258, -2), (key2301, 6), (key2301, -2), (key2008, -2), (key2314, -2)]

theorem rawRowCheck17652 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form2 = rawRow17652 := by decide +kernel

def row17652 : Integer.Sparse Key := [(key1993, 4), (key2008, -4), (key2238, -4), (key2301, 4)]

theorem rowCheck17652 : row17652 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17652 := by decide +kernel

theorem rowEval17652 (x : Key → ℝ) : Integer.Sparse.eval row17652 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17652, Integer.Sparse.eval_collectBalanced, rawRowCheck17652]

def rawRow17653 : Integer.Sparse Key := [(key2008, -2), (key1988, -2), (key1993, -2), (key1993, 6), (key2301, -2), (key2233, -2), (key2238, -2), (key2301, 2), (key2233, 2), (key2314, 2), (key1988, 2), (key2258, 2), (key1993, 2), (key2238, -2), (key2258, -2), (key1993, -2), (key2301, 6), (key2301, -2), (key2314, -2), (key2008, -2)]

theorem rawRowCheck17653 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form2 = rawRow17653 := by decide +kernel

def row17653 : Integer.Sparse Key := [(key1993, 4), (key2008, -4), (key2238, -4), (key2301, 4)]

theorem rowCheck17653 : row17653 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17653 := by decide +kernel

theorem rowEval17653 (x : Key → ℝ) : Integer.Sparse.eval row17653 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17653, Integer.Sparse.eval_collectBalanced, rawRowCheck17653]

def rawRow17654 : Integer.Sparse Key := [(key1993, -2), (key2008, -2), (key1988, -2), (key1993, 6), (key2238, -2), (key2301, -2), (key2233, -2), (key2258, 2), (key2314, 2), (key1993, 2), (key2301, 2), (key1988, 2), (key2233, 2), (key2258, -2), (key1993, -2), (key2238, -2), (key2301, 6), (key2314, -2), (key2008, -2), (key2301, -2)]

theorem rawRowCheck17654 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form2 = rawRow17654 := by decide +kernel

def row17654 : Integer.Sparse Key := [(key1993, 4), (key2008, -4), (key2238, -4), (key2301, 4)]

theorem rowCheck17654 : row17654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17654 := by decide +kernel

theorem rowEval17654 (x : Key → ℝ) : Integer.Sparse.eval row17654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck17654, Integer.Sparse.eval_collectBalanced, rawRowCheck17654]

def rawRow17655 : Integer.Sparse Key := [(key2008, -2), (key1993, -2), (key1988, -2), (key1993, 6), (key2301, -2), (key2238, -2), (key2233, -2), (key2314, 2), (key2258, 2), (key2301, 2), (key1993, 2), (key2233, 2), (key1988, 2), (key2258, -2), (key2238, -2), (key1993, -2), (key2301, 6), (key2314, -2), (key2301, -2), (key2008, -2)]

theorem rawRowCheck17655 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form2 = rawRow17655 := by decide +kernel

def row17655 : Integer.Sparse Key := [(key1993, 4), (key2008, -4), (key2238, -4), (key2301, 4)]

theorem rowCheck17655 : row17655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17655 := by decide +kernel

theorem rowEval17655 (x : Key → ℝ) : Integer.Sparse.eval row17655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17655, Integer.Sparse.eval_collectBalanced, rawRowCheck17655]

def rawRow17656 : Integer.Sparse Key := [(key2233, -2), (key2238, -2), (key2301, -2), (key2301, 6), (key1988, -2), (key1993, -2), (key2008, -2), (key1988, 2), (key1993, 2), (key2233, 2), (key2258, 2), (key2301, 2), (key2314, 2), (key2008, -2), (key2301, -2), (key2314, -2), (key1993, 6), (key1993, -2), (key2238, -2), (key2258, -2)]

theorem rawRowCheck17656 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form2 = rawRow17656 := by decide +kernel

def row17656 : Integer.Sparse Key := [(key1993, 4), (key2008, -4), (key2238, -4), (key2301, 4)]

theorem rowCheck17656 : row17656 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17656 := by decide +kernel

theorem rowEval17656 (x : Key → ℝ) : Integer.Sparse.eval row17656 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17656, Integer.Sparse.eval_collectBalanced, rawRowCheck17656]

def rawRow17657 : Integer.Sparse Key := [(key2238, -2), (key2233, -2), (key2301, -2), (key2301, 6), (key1993, -2), (key1988, -2), (key2008, -2), (key1993, 2), (key1988, 2), (key2258, 2), (key2233, 2), (key2314, 2), (key2301, 2), (key2008, -2), (key2314, -2), (key2301, -2), (key1993, 6), (key1993, -2), (key2258, -2), (key2238, -2)]

theorem rawRowCheck17657 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form2 = rawRow17657 := by decide +kernel

def row17657 : Integer.Sparse Key := [(key1993, 4), (key2008, -4), (key2238, -4), (key2301, 4)]

theorem rowCheck17657 : row17657 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17657 := by decide +kernel

theorem rowEval17657 (x : Key → ℝ) : Integer.Sparse.eval row17657 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck17657, Integer.Sparse.eval_collectBalanced, rawRowCheck17657]

def rawRow17658 : Integer.Sparse Key := [(key2233, -2), (key2301, -2), (key2238, -2), (key2301, 6), (key1988, -2), (key2008, -2), (key1993, -2), (key2233, 2), (key2301, 2), (key1988, 2), (key2314, 2), (key1993, 2), (key2258, 2), (key2301, -2), (key2008, -2), (key2314, -2), (key1993, 6), (key2238, -2), (key1993, -2), (key2258, -2)]

theorem rawRowCheck17658 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form2 = rawRow17658 := by decide +kernel

def row17658 : Integer.Sparse Key := [(key1993, 4), (key2008, -4), (key2238, -4), (key2301, 4)]

theorem rowCheck17658 : row17658 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17658 := by decide +kernel

theorem rowEval17658 (x : Key → ℝ) : Integer.Sparse.eval row17658 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17658, Integer.Sparse.eval_collectBalanced, rawRowCheck17658]

def rawRow17659 : Integer.Sparse Key := [(key2301, -2), (key2233, -2), (key2238, -2), (key2301, 6), (key2008, -2), (key1988, -2), (key1993, -2), (key2301, 2), (key2233, 2), (key2314, 2), (key1988, 2), (key2258, 2), (key1993, 2), (key2301, -2), (key2314, -2), (key2008, -2), (key1993, 6), (key2238, -2), (key2258, -2), (key1993, -2)]

theorem rawRowCheck17659 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form2 = rawRow17659 := by decide +kernel

def row17659 : Integer.Sparse Key := [(key1993, 4), (key2008, -4), (key2238, -4), (key2301, 4)]

theorem rowCheck17659 : row17659 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17659 := by decide +kernel

theorem rowEval17659 (x : Key → ℝ) : Integer.Sparse.eval row17659 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17659, Integer.Sparse.eval_collectBalanced, rawRowCheck17659]

def rawRow17660 : Integer.Sparse Key := [(key2238, -2), (key2301, -2), (key2233, -2), (key2301, 6), (key1993, -2), (key2008, -2), (key1988, -2), (key2258, 2), (key2314, 2), (key1993, 2), (key2301, 2), (key1988, 2), (key2233, 2), (key2314, -2), (key2008, -2), (key2301, -2), (key1993, 6), (key2258, -2), (key1993, -2), (key2238, -2)]

theorem rawRowCheck17660 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form2 = rawRow17660 := by decide +kernel

def row17660 : Integer.Sparse Key := [(key1993, 4), (key2008, -4), (key2238, -4), (key2301, 4)]

theorem rowCheck17660 : row17660 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17660 := by decide +kernel

theorem rowEval17660 (x : Key → ℝ) : Integer.Sparse.eval row17660 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck17660, Integer.Sparse.eval_collectBalanced, rawRowCheck17660]

def rawRow17661 : Integer.Sparse Key := [(key2301, -2), (key2238, -2), (key2233, -2), (key2301, 6), (key2008, -2), (key1993, -2), (key1988, -2), (key2314, 2), (key2258, 2), (key2301, 2), (key1993, 2), (key2233, 2), (key1988, 2), (key2314, -2), (key2301, -2), (key2008, -2), (key1993, 6), (key2258, -2), (key2238, -2), (key1993, -2)]

theorem rawRowCheck17661 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form2 = rawRow17661 := by decide +kernel

def row17661 : Integer.Sparse Key := [(key1993, 4), (key2008, -4), (key2238, -4), (key2301, 4)]

theorem rowCheck17661 : row17661 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17661 := by decide +kernel

theorem rowEval17661 (x : Key → ℝ) : Integer.Sparse.eval row17661 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17661, Integer.Sparse.eval_collectBalanced, rawRowCheck17661]

def rawRow17662 : Integer.Sparse Key := [(key2233, -2), (key2301, -2), (key2301, -2), (key2238, 6), (key2233, -2), (key2301, -2), (key2301, -2), (key1988, 2), (key2008, 2), (key1988, 2), (key2314, 2), (key2008, 2), (key2314, 2), (key1993, -2), (key1993, -2), (key2258, -2), (key2238, 6), (key1993, -2), (key1993, -2), (key2258, -2)]

theorem rawRowCheck17662 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form2 = rawRow17662 := by decide +kernel

def row17662 : Integer.Sparse Key := [(key1988, 4), (key1993, -8), (key2008, 4), (key2233, -4), (key2238, 12), (key2258, -4), (key2301, -8), (key2314, 4)]

theorem rowCheck17662 : row17662 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17662 := by decide +kernel

theorem rowEval17662 (x : Key → ℝ) : Integer.Sparse.eval row17662 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17662, Integer.Sparse.eval_collectBalanced, rawRowCheck17662]

def rawRow17663 : Integer.Sparse Key := [(key2301, -2), (key2233, -2), (key2301, -2), (key2238, 6), (key2301, -2), (key2233, -2), (key2301, -2), (key2008, 2), (key1988, 2), (key2314, 2), (key1988, 2), (key2314, 2), (key2008, 2), (key1993, -2), (key2258, -2), (key1993, -2), (key2238, 6), (key1993, -2), (key2258, -2), (key1993, -2)]

theorem rawRowCheck17663 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form2 = rawRow17663 := by decide +kernel

def row17663 : Integer.Sparse Key := [(key1988, 4), (key1993, -8), (key2008, 4), (key2233, -4), (key2238, 12), (key2258, -4), (key2301, -8), (key2314, 4)]

theorem rowCheck17663 : row17663 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17663 := by decide +kernel

theorem rowEval17663 (x : Key → ℝ) : Integer.Sparse.eval row17663 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17663, Integer.Sparse.eval_collectBalanced, rawRowCheck17663]

end MUB6.Certificate.GramRows

end OAI
