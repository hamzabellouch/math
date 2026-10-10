import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block2
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block6
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow7296 : Integer.Sparse Key := [(key823, 1), (key822, 1), (key822, -2), (key911, 1), (key910, 1), (key911, -2), (key906, -2), (key910, 1), (key906, 1), (key953, -2), (key953, 1), (key952, 1), (key828, -2), (key827, -2), (key828, 1), (key822, 1), (key827, 1), (key822, 1), (key918, 1), (key910, 1), (key910, -2), (key957, 1), (key953, 1), (key953, -2), (key828, 4), (key828, -2), (key823, -2), (key918, -2), (key911, -2), (key911, 4)]

theorem rawRowCheck7296 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form9 = rawRow7296 := by decide +kernel

def row7296 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

theorem rowCheck7296 : row7296 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7296 := by decide +kernel

theorem rowEval7296 (x : Key → ℝ) : Integer.Sparse.eval row7296 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7296, Integer.Sparse.eval_collectBalanced, rawRowCheck7296]

def rawRow7297 : Integer.Sparse Key := [(key906, 1), (key906, 1), (key952, -2), (key822, 1), (key822, 1), (key910, -2), (key910, -2), (key953, 1), (key953, 1), (key823, -2), (key911, 1), (key911, 1), (key822, -2), (key822, -2), (key910, 1), (key910, 1), (key953, 1), (key953, 1), (key827, 1), (key827, 1), (key957, -2), (key828, 1), (key828, 1), (key918, -2), (key823, 4), (key911, -2), (key911, -2), (key828, -2), (key828, -2), (key918, 4)]

theorem rawRowCheck7297 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form9 = rawRow7297 := by decide +kernel

def row7297 : Integer.Sparse Key := [(key822, -2), (key823, 2), (key827, 2), (key828, -2), (key906, 2), (key910, -2), (key911, -2), (key918, 2), (key952, -2), (key953, 4), (key957, -2)]

theorem rowCheck7297 : row7297 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7297 := by decide +kernel

theorem rowEval7297 (x : Key → ℝ) : Integer.Sparse.eval row7297 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7297, Integer.Sparse.eval_collectBalanced, rawRowCheck7297]

def rawRow7298 : Integer.Sparse Key := [(key906, 1), (key952, 1), (key906, -2), (key910, 1), (key953, 1), (key822, -2), (key953, -2), (key822, 1), (key910, 1), (key911, -2), (key823, 1), (key911, 1), (key910, -2), (key953, -2), (key822, 1), (key953, 1), (key822, 1), (key910, 1), (key827, 1), (key957, 1), (key827, -2), (key828, 1), (key918, 1), (key828, -2), (key911, 4), (key823, -2), (key911, -2), (key828, -2), (key918, -2), (key828, 4)]

theorem rawRowCheck7298 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form9 = rawRow7298 := by decide +kernel

def row7298 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

theorem rowCheck7298 : row7298 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7298 := by decide +kernel

theorem rowEval7298 (x : Key → ℝ) : Integer.Sparse.eval row7298 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7298, Integer.Sparse.eval_collectBalanced, rawRowCheck7298]

def rawRow7299 : Integer.Sparse Key := [(key952, 1), (key906, 1), (key906, -2), (key953, 1), (key910, 1), (key953, -2), (key822, -2), (key910, 1), (key822, 1), (key911, -2), (key911, 1), (key823, 1), (key953, -2), (key910, -2), (key953, 1), (key822, 1), (key910, 1), (key822, 1), (key957, 1), (key827, 1), (key827, -2), (key918, 1), (key828, 1), (key828, -2), (key911, 4), (key911, -2), (key823, -2), (key918, -2), (key828, -2), (key828, 4)]

theorem rawRowCheck7299 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form9 = rawRow7299 := by decide +kernel

def row7299 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

theorem rowCheck7299 : row7299 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7299 := by decide +kernel

theorem rowEval7299 (x : Key → ℝ) : Integer.Sparse.eval row7299 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7299, Integer.Sparse.eval_collectBalanced, rawRowCheck7299]

def rawRow7300 : Integer.Sparse Key := [(key910, 1), (key911, 1), (key953, -2), (key822, 1), (key823, 1), (key906, -2), (key911, -2), (key952, 1), (key953, 1), (key822, -2), (key906, 1), (key910, 1), (key827, -2), (key828, -2), (key910, 1), (key918, 1), (key953, 1), (key957, 1), (key822, 1), (key828, 1), (key953, -2), (key822, 1), (key827, 1), (key910, -2), (key828, 4), (key911, -2), (key918, -2), (key823, -2), (key828, -2), (key911, 4)]

theorem rawRowCheck7300 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form9 = rawRow7300 := by decide +kernel

def row7300 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

theorem rowCheck7300 : row7300 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7300 := by decide +kernel

theorem rowEval7300 (x : Key → ℝ) : Integer.Sparse.eval row7300 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7300, Integer.Sparse.eval_collectBalanced, rawRowCheck7300]

def rawRow7301 : Integer.Sparse Key := [(key911, 1), (key910, 1), (key953, -2), (key823, 1), (key822, 1), (key911, -2), (key906, -2), (key953, 1), (key952, 1), (key822, -2), (key910, 1), (key906, 1), (key828, -2), (key827, -2), (key918, 1), (key910, 1), (key957, 1), (key953, 1), (key828, 1), (key822, 1), (key953, -2), (key827, 1), (key822, 1), (key910, -2), (key828, 4), (key918, -2), (key911, -2), (key828, -2), (key823, -2), (key911, 4)]

theorem rawRowCheck7301 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form9 = rawRow7301 := by decide +kernel

def row7301 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

theorem rowCheck7301 : row7301 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7301 := by decide +kernel

theorem rowEval7301 (x : Key → ℝ) : Integer.Sparse.eval row7301 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7301, Integer.Sparse.eval_collectBalanced, rawRowCheck7301]

def rawRow7302 : Integer.Sparse Key := [(key910, 1), (key953, 1), (key911, -2), (key906, 1), (key952, 1), (key822, -2), (key953, -2), (key823, 1), (key911, 1), (key906, -2), (key822, 1), (key910, 1), (key910, -2), (key953, -2), (key827, 1), (key957, 1), (key828, 1), (key918, 1), (key822, 1), (key953, 1), (key828, -2), (key822, 1), (key910, 1), (key827, -2), (key911, 4), (key828, -2), (key918, -2), (key823, -2), (key911, -2), (key828, 4)]

theorem rawRowCheck7302 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form9 = rawRow7302 := by decide +kernel

def row7302 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

theorem rowCheck7302 : row7302 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7302 := by decide +kernel

theorem rowEval7302 (x : Key → ℝ) : Integer.Sparse.eval row7302 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7302, Integer.Sparse.eval_collectBalanced, rawRowCheck7302]

def rawRow7303 : Integer.Sparse Key := [(key953, 1), (key910, 1), (key911, -2), (key952, 1), (key906, 1), (key953, -2), (key822, -2), (key911, 1), (key823, 1), (key906, -2), (key910, 1), (key822, 1), (key953, -2), (key910, -2), (key957, 1), (key827, 1), (key918, 1), (key828, 1), (key953, 1), (key822, 1), (key828, -2), (key910, 1), (key822, 1), (key827, -2), (key911, 4), (key918, -2), (key828, -2), (key911, -2), (key823, -2), (key828, 4)]

theorem rawRowCheck7303 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form9 = rawRow7303 := by decide +kernel

def row7303 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

theorem rowCheck7303 : row7303 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7303 := by decide +kernel

theorem rowEval7303 (x : Key → ℝ) : Integer.Sparse.eval row7303 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7303, Integer.Sparse.eval_collectBalanced, rawRowCheck7303]

def rawRow7304 : Integer.Sparse Key := [(key911, 1), (key953, 1), (key910, -2), (key911, 1), (key953, 1), (key823, -2), (key952, -2), (key822, 1), (key906, 1), (key910, -2), (key822, 1), (key906, 1), (key918, -2), (key957, -2), (key828, 1), (key953, 1), (key827, 1), (key910, 1), (key828, 1), (key953, 1), (key822, -2), (key827, 1), (key910, 1), (key822, -2), (key918, 4), (key828, -2), (key911, -2), (key828, -2), (key911, -2), (key823, 4)]

theorem rawRowCheck7304 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form9 = rawRow7304 := by decide +kernel

def row7304 : Integer.Sparse Key := [(key822, -2), (key823, 2), (key827, 2), (key828, -2), (key906, 2), (key910, -2), (key911, -2), (key918, 2), (key952, -2), (key953, 4), (key957, -2)]

theorem rowCheck7304 : row7304 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7304 := by decide +kernel

theorem rowEval7304 (x : Key → ℝ) : Integer.Sparse.eval row7304 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7304, Integer.Sparse.eval_collectBalanced, rawRowCheck7304]

def rawRow7305 : Integer.Sparse Key := [(key953, 1), (key911, 1), (key910, -2), (key953, 1), (key911, 1), (key952, -2), (key823, -2), (key906, 1), (key822, 1), (key910, -2), (key906, 1), (key822, 1), (key957, -2), (key918, -2), (key953, 1), (key828, 1), (key910, 1), (key827, 1), (key953, 1), (key828, 1), (key822, -2), (key910, 1), (key827, 1), (key822, -2), (key918, 4), (key911, -2), (key828, -2), (key911, -2), (key828, -2), (key823, 4)]

theorem rawRowCheck7305 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form9 = rawRow7305 := by decide +kernel

def row7305 : Integer.Sparse Key := [(key822, -2), (key823, 2), (key827, 2), (key828, -2), (key906, 2), (key910, -2), (key911, -2), (key918, 2), (key952, -2), (key953, 4), (key957, -2)]

theorem rowCheck7305 : row7305 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7305 := by decide +kernel

theorem rowEval7305 (x : Key → ℝ) : Integer.Sparse.eval row7305 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7305, Integer.Sparse.eval_collectBalanced, rawRowCheck7305]

def rawRow7306 : Integer.Sparse Key := [(key827, 1), (key828, 1), (key828, -2), (key910, 1), (key911, 1), (key910, -2), (key918, -2), (key911, 1), (key918, 1), (key953, -2), (key953, 1), (key957, 1), (key822, -2), (key823, -2), (key822, 1), (key828, 1), (key823, 1), (key828, 1), (key906, 1), (key911, 1), (key911, -2), (key952, 1), (key953, 1), (key953, -2), (key822, 4), (key822, -2), (key827, -2), (key906, -2), (key910, -2), (key910, 4)]

theorem rawRowCheck7306 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form9 = rawRow7306 := by decide +kernel

def row7306 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

theorem rowCheck7306 : row7306 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7306 := by decide +kernel

theorem rowEval7306 (x : Key → ℝ) : Integer.Sparse.eval row7306 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7306, Integer.Sparse.eval_collectBalanced, rawRowCheck7306]

def rawRow7307 : Integer.Sparse Key := [(key828, 1), (key827, 1), (key828, -2), (key911, 1), (key910, 1), (key918, -2), (key910, -2), (key918, 1), (key911, 1), (key953, -2), (key957, 1), (key953, 1), (key823, -2), (key822, -2), (key828, 1), (key822, 1), (key828, 1), (key823, 1), (key911, 1), (key906, 1), (key911, -2), (key953, 1), (key952, 1), (key953, -2), (key822, 4), (key827, -2), (key822, -2), (key910, -2), (key906, -2), (key910, 4)]

theorem rawRowCheck7307 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form9 = rawRow7307 := by decide +kernel

def row7307 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

theorem rowCheck7307 : row7307 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7307 := by decide +kernel

theorem rowEval7307 (x : Key → ℝ) : Integer.Sparse.eval row7307 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7307, Integer.Sparse.eval_collectBalanced, rawRowCheck7307]

def rawRow7308 : Integer.Sparse Key := [(key828, 1), (key828, 1), (key827, -2), (key918, 1), (key918, 1), (key911, -2), (key911, -2), (key910, 1), (key910, 1), (key957, -2), (key953, 1), (key953, 1), (key828, -2), (key828, -2), (key823, 1), (key823, 1), (key822, 1), (key822, 1), (key911, 1), (key911, 1), (key906, -2), (key953, 1), (key953, 1), (key952, -2), (key827, 4), (key822, -2), (key822, -2), (key910, -2), (key910, -2), (key906, 4)]

theorem rawRowCheck7308 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form9 = rawRow7308 := by decide +kernel

def row7308 : Integer.Sparse Key := [(key822, -2), (key823, 2), (key827, 2), (key828, -2), (key906, 2), (key910, -2), (key911, -2), (key918, 2), (key952, -2), (key953, 4), (key957, -2)]

theorem rowCheck7308 : row7308 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7308 := by decide +kernel

theorem rowEval7308 (x : Key → ℝ) : Integer.Sparse.eval row7308 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7308, Integer.Sparse.eval_collectBalanced, rawRowCheck7308]

def rawRow7309 : Integer.Sparse Key := [(key910, 1), (key911, 1), (key953, -2), (key827, 1), (key828, 1), (key910, -2), (key918, -2), (key953, 1), (key957, 1), (key828, -2), (key911, 1), (key918, 1), (key822, -2), (key823, -2), (key906, 1), (key911, 1), (key952, 1), (key953, 1), (key822, 1), (key828, 1), (key953, -2), (key823, 1), (key828, 1), (key911, -2), (key822, 4), (key906, -2), (key910, -2), (key822, -2), (key827, -2), (key910, 4)]

theorem rawRowCheck7309 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form9 = rawRow7309 := by decide +kernel

def row7309 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

theorem rowCheck7309 : row7309 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7309 := by decide +kernel

theorem rowEval7309 (x : Key → ℝ) : Integer.Sparse.eval row7309 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7309, Integer.Sparse.eval_collectBalanced, rawRowCheck7309]

def rawRow7310 : Integer.Sparse Key := [(key911, 1), (key910, 1), (key953, -2), (key828, 1), (key827, 1), (key918, -2), (key910, -2), (key957, 1), (key953, 1), (key828, -2), (key918, 1), (key911, 1), (key823, -2), (key822, -2), (key911, 1), (key906, 1), (key953, 1), (key952, 1), (key828, 1), (key822, 1), (key953, -2), (key828, 1), (key823, 1), (key911, -2), (key822, 4), (key910, -2), (key906, -2), (key827, -2), (key822, -2), (key910, 4)]

theorem rawRowCheck7310 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form9 = rawRow7310 := by decide +kernel

def row7310 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

theorem rowCheck7310 : row7310 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7310 := by decide +kernel

theorem rowEval7310 (x : Key → ℝ) : Integer.Sparse.eval row7310 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7310, Integer.Sparse.eval_collectBalanced, rawRowCheck7310]

def rawRow7311 : Integer.Sparse Key := [(key910, 1), (key953, 1), (key911, -2), (key910, 1), (key953, 1), (key827, -2), (key957, -2), (key828, 1), (key918, 1), (key911, -2), (key828, 1), (key918, 1), (key906, -2), (key952, -2), (key822, 1), (key953, 1), (key823, 1), (key911, 1), (key822, 1), (key953, 1), (key828, -2), (key823, 1), (key911, 1), (key828, -2), (key906, 4), (key822, -2), (key910, -2), (key822, -2), (key910, -2), (key827, 4)]

theorem rawRowCheck7311 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form9 = rawRow7311 := by decide +kernel

def row7311 : Integer.Sparse Key := [(key822, -2), (key823, 2), (key827, 2), (key828, -2), (key906, 2), (key910, -2), (key911, -2), (key918, 2), (key952, -2), (key953, 4), (key957, -2)]

theorem rowCheck7311 : row7311 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7311 := by decide +kernel

theorem rowEval7311 (x : Key → ℝ) : Integer.Sparse.eval row7311 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7311, Integer.Sparse.eval_collectBalanced, rawRowCheck7311]

def rawRow7312 : Integer.Sparse Key := [(key953, 1), (key910, 1), (key911, -2), (key953, 1), (key910, 1), (key957, -2), (key827, -2), (key918, 1), (key828, 1), (key911, -2), (key918, 1), (key828, 1), (key952, -2), (key906, -2), (key953, 1), (key822, 1), (key911, 1), (key823, 1), (key953, 1), (key822, 1), (key828, -2), (key911, 1), (key823, 1), (key828, -2), (key906, 4), (key910, -2), (key822, -2), (key910, -2), (key822, -2), (key827, 4)]

theorem rawRowCheck7312 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form9 = rawRow7312 := by decide +kernel

def row7312 : Integer.Sparse Key := [(key822, -2), (key823, 2), (key827, 2), (key828, -2), (key906, 2), (key910, -2), (key911, -2), (key918, 2), (key952, -2), (key953, 4), (key957, -2)]

theorem rowCheck7312 : row7312 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7312 := by decide +kernel

theorem rowEval7312 (x : Key → ℝ) : Integer.Sparse.eval row7312 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7312, Integer.Sparse.eval_collectBalanced, rawRowCheck7312]

def rawRow7313 : Integer.Sparse Key := [(key911, 1), (key953, 1), (key910, -2), (key918, 1), (key957, 1), (key828, -2), (key953, -2), (key827, 1), (key910, 1), (key918, -2), (key828, 1), (key911, 1), (key911, -2), (key953, -2), (key823, 1), (key952, 1), (key822, 1), (key906, 1), (key828, 1), (key953, 1), (key822, -2), (key828, 1), (key911, 1), (key823, -2), (key910, 4), (key822, -2), (key906, -2), (key827, -2), (key910, -2), (key822, 4)]

theorem rawRowCheck7313 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form9 = rawRow7313 := by decide +kernel

def row7313 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

theorem rowCheck7313 : row7313 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7313 := by decide +kernel

theorem rowEval7313 (x : Key → ℝ) : Integer.Sparse.eval row7313 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7313, Integer.Sparse.eval_collectBalanced, rawRowCheck7313]

def rawRow7314 : Integer.Sparse Key := [(key953, 1), (key911, 1), (key910, -2), (key957, 1), (key918, 1), (key953, -2), (key828, -2), (key910, 1), (key827, 1), (key918, -2), (key911, 1), (key828, 1), (key953, -2), (key911, -2), (key952, 1), (key823, 1), (key906, 1), (key822, 1), (key953, 1), (key828, 1), (key822, -2), (key911, 1), (key828, 1), (key823, -2), (key910, 4), (key906, -2), (key822, -2), (key910, -2), (key827, -2), (key822, 4)]

theorem rawRowCheck7314 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form9 = rawRow7314 := by decide +kernel

def row7314 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

theorem rowCheck7314 : row7314 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7314 := by decide +kernel

theorem rowEval7314 (x : Key → ℝ) : Integer.Sparse.eval row7314 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7314, Integer.Sparse.eval_collectBalanced, rawRowCheck7314]

def rawRow7315 : Integer.Sparse Key := [(key918, 1), (key918, 1), (key957, -2), (key828, 1), (key828, 1), (key911, -2), (key911, -2), (key953, 1), (key953, 1), (key827, -2), (key910, 1), (key910, 1), (key828, -2), (key828, -2), (key911, 1), (key911, 1), (key953, 1), (key953, 1), (key823, 1), (key823, 1), (key952, -2), (key822, 1), (key822, 1), (key906, -2), (key827, 4), (key910, -2), (key910, -2), (key822, -2), (key822, -2), (key906, 4)]

theorem rawRowCheck7315 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form9 = rawRow7315 := by decide +kernel

def row7315 : Integer.Sparse Key := [(key822, -2), (key823, 2), (key827, 2), (key828, -2), (key906, 2), (key910, -2), (key911, -2), (key918, 2), (key952, -2), (key953, 4), (key957, -2)]

theorem rowCheck7315 : row7315 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7315 := by decide +kernel

theorem rowEval7315 (x : Key → ℝ) : Integer.Sparse.eval row7315 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7315, Integer.Sparse.eval_collectBalanced, rawRowCheck7315]

def rawRow7316 : Integer.Sparse Key := [(key918, 1), (key957, 1), (key918, -2), (key911, 1), (key953, 1), (key828, -2), (key953, -2), (key828, 1), (key911, 1), (key910, -2), (key827, 1), (key910, 1), (key911, -2), (key953, -2), (key828, 1), (key953, 1), (key828, 1), (key911, 1), (key823, 1), (key952, 1), (key823, -2), (key822, 1), (key906, 1), (key822, -2), (key910, 4), (key827, -2), (key910, -2), (key822, -2), (key906, -2), (key822, 4)]

theorem rawRowCheck7316 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form9 = rawRow7316 := by decide +kernel

def row7316 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

theorem rowCheck7316 : row7316 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7316 := by decide +kernel

theorem rowEval7316 (x : Key → ℝ) : Integer.Sparse.eval row7316 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7316, Integer.Sparse.eval_collectBalanced, rawRowCheck7316]

def rawRow7317 : Integer.Sparse Key := [(key957, 1), (key918, 1), (key918, -2), (key953, 1), (key911, 1), (key953, -2), (key828, -2), (key911, 1), (key828, 1), (key910, -2), (key910, 1), (key827, 1), (key953, -2), (key911, -2), (key953, 1), (key828, 1), (key911, 1), (key828, 1), (key952, 1), (key823, 1), (key823, -2), (key906, 1), (key822, 1), (key822, -2), (key910, 4), (key910, -2), (key827, -2), (key906, -2), (key822, -2), (key822, 4)]

theorem rawRowCheck7317 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form9 = rawRow7317 := by decide +kernel

def row7317 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

theorem rowCheck7317 : row7317 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7317 := by decide +kernel

theorem rowEval7317 (x : Key → ℝ) : Integer.Sparse.eval row7317 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7317, Integer.Sparse.eval_collectBalanced, rawRowCheck7317]

def rawRow7318 : Integer.Sparse Key := [(key781, -4), (key784, 2), (key784, 2), (key784, 2), (key784, 2), (key786, -4), (key806, 2), (key809, -1), (key809, -1), (key806, 2), (key814, -1), (key814, -1), (key809, -1), (key809, -1), (key814, -1), (key814, -1), (key816, 2), (key816, 2), (key822, -1), (key822, -1), (key823, 2), (key822, -1), (key822, -1), (key827, 2), (key827, 2), (key828, -1), (key828, -1), (key823, 2), (key828, -1), (key828, -1)]

theorem rawRowCheck7318 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form10 = rawRow7318 := by decide +kernel

def row7318 : Integer.Sparse Key := [(key781, -4), (key784, 8), (key786, -4), (key806, 4), (key809, -4), (key814, -4), (key816, 4), (key822, -4), (key823, 4), (key827, 4), (key828, -4)]

theorem rowCheck7318 : row7318 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7318 := by decide +kernel

theorem rowEval7318 (x : Key → ℝ) : Integer.Sparse.eval row7318 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form10) x := by
  rw [rowCheck7318, Integer.Sparse.eval_collectBalanced, rawRowCheck7318]

def rawRow7319 : Integer.Sparse Key := [(key784, -4), (key781, 2), (key784, 2), (key784, 2), (key786, 2), (key784, -4), (key809, 2), (key806, -1), (key809, -1), (key814, 2), (key806, -1), (key814, -1), (key814, -1), (key816, -1), (key809, -1), (key816, -1), (key809, 2), (key814, 2), (key822, -1), (key823, -1), (key822, 2), (key827, -1), (key828, -1), (key822, 2), (key828, 2), (key822, -1), (key827, -1), (key828, 2), (key823, -1), (key828, -1)]

theorem rawRowCheck7319 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form10 = rawRow7319 := by decide +kernel

def row7319 : Integer.Sparse Key := [(key781, 2), (key784, -4), (key786, 2), (key806, -2), (key809, 2), (key814, 2), (key816, -2), (key822, 2), (key823, -2), (key827, -2), (key828, 2)]

theorem rowCheck7319 : row7319 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7319 := by decide +kernel

theorem rowEval7319 (x : Key → ℝ) : Integer.Sparse.eval row7319 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form10) x := by
  rw [rowCheck7319, Integer.Sparse.eval_collectBalanced, rawRowCheck7319]

def rawRow7320 : Integer.Sparse Key := [(key784, -4), (key784, 2), (key781, 2), (key786, 2), (key784, 2), (key784, -4), (key809, 2), (key809, -1), (key806, -1), (key814, 2), (key814, -1), (key806, -1), (key816, -1), (key814, -1), (key816, -1), (key809, -1), (key814, 2), (key809, 2), (key823, -1), (key822, -1), (key822, 2), (key828, -1), (key827, -1), (key828, 2), (key822, 2), (key827, -1), (key822, -1), (key828, 2), (key828, -1), (key823, -1)]

theorem rawRowCheck7320 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form10 = rawRow7320 := by decide +kernel

def row7320 : Integer.Sparse Key := [(key781, 2), (key784, -4), (key786, 2), (key806, -2), (key809, 2), (key814, 2), (key816, -2), (key822, 2), (key823, -2), (key827, -2), (key828, 2)]

theorem rowCheck7320 : row7320 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7320 := by decide +kernel

theorem rowEval7320 (x : Key → ℝ) : Integer.Sparse.eval row7320 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form10) x := by
  rw [rowCheck7320, Integer.Sparse.eval_collectBalanced, rawRowCheck7320]

def rawRow7321 : Integer.Sparse Key := [(key784, -4), (key784, 2), (key786, 2), (key781, 2), (key784, 2), (key784, -4), (key814, 2), (key814, -1), (key816, -1), (key809, 2), (key809, -1), (key816, -1), (key806, -1), (key809, -1), (key806, -1), (key814, -1), (key809, 2), (key814, 2), (key827, -1), (key828, -1), (key828, 2), (key822, -1), (key823, -1), (key822, 2), (key828, 2), (key823, -1), (key828, -1), (key822, 2), (key822, -1), (key827, -1)]

theorem rawRowCheck7321 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form10 = rawRow7321 := by decide +kernel

def row7321 : Integer.Sparse Key := [(key781, 2), (key784, -4), (key786, 2), (key806, -2), (key809, 2), (key814, 2), (key816, -2), (key822, 2), (key823, -2), (key827, -2), (key828, 2)]

theorem rowCheck7321 : row7321 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7321 := by decide +kernel

theorem rowEval7321 (x : Key → ℝ) : Integer.Sparse.eval row7321 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form10) x := by
  rw [rowCheck7321, Integer.Sparse.eval_collectBalanced, rawRowCheck7321]

def rawRow7322 : Integer.Sparse Key := [(key784, -4), (key786, 2), (key784, 2), (key784, 2), (key781, 2), (key784, -4), (key814, 2), (key816, -1), (key814, -1), (key809, 2), (key816, -1), (key809, -1), (key809, -1), (key806, -1), (key814, -1), (key806, -1), (key814, 2), (key809, 2), (key828, -1), (key827, -1), (key828, 2), (key823, -1), (key822, -1), (key828, 2), (key822, 2), (key828, -1), (key823, -1), (key822, 2), (key827, -1), (key822, -1)]

theorem rawRowCheck7322 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form10 = rawRow7322 := by decide +kernel

def row7322 : Integer.Sparse Key := [(key781, 2), (key784, -4), (key786, 2), (key806, -2), (key809, 2), (key814, 2), (key816, -2), (key822, 2), (key823, -2), (key827, -2), (key828, 2)]

theorem rowCheck7322 : row7322 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7322 := by decide +kernel

theorem rowEval7322 (x : Key → ℝ) : Integer.Sparse.eval row7322 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form10) x := by
  rw [rowCheck7322, Integer.Sparse.eval_collectBalanced, rawRowCheck7322]

def rawRow7323 : Integer.Sparse Key := [(key786, -4), (key784, 2), (key784, 2), (key784, 2), (key784, 2), (key781, -4), (key816, 2), (key814, -1), (key814, -1), (key816, 2), (key809, -1), (key809, -1), (key814, -1), (key814, -1), (key809, -1), (key809, -1), (key806, 2), (key806, 2), (key828, -1), (key828, -1), (key827, 2), (key828, -1), (key828, -1), (key823, 2), (key823, 2), (key822, -1), (key822, -1), (key827, 2), (key822, -1), (key822, -1)]

theorem rawRowCheck7323 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form10 = rawRow7323 := by decide +kernel

def row7323 : Integer.Sparse Key := [(key781, -4), (key784, 8), (key786, -4), (key806, 4), (key809, -4), (key814, -4), (key816, 4), (key822, -4), (key823, 4), (key827, 4), (key828, -4)]

theorem rowCheck7323 : row7323 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7323 := by decide +kernel

theorem rowEval7323 (x : Key → ℝ) : Integer.Sparse.eval row7323 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form10) x := by
  rw [rowCheck7323, Integer.Sparse.eval_collectBalanced, rawRowCheck7323]

def rawRow7324 : Integer.Sparse Key := [(key806, -4), (key809, 2), (key809, 2), (key814, 2), (key814, 2), (key816, -4), (key781, 2), (key784, -1), (key784, -1), (key806, 2), (key814, -1), (key814, -1), (key822, -1), (key822, -1), (key827, -1), (key827, -1), (key828, 2), (key828, 2), (key784, -1), (key784, -1), (key786, 2), (key809, -1), (key809, -1), (key814, 2), (key814, 2), (key816, -1), (key816, -1), (key823, 2), (key828, -1), (key828, -1)]

theorem rawRowCheck7324 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form10 = rawRow7324 := by decide +kernel

def row7324 : Integer.Sparse Key := [(key781, 2), (key784, -4), (key786, 2), (key806, -2), (key809, 2), (key814, 6), (key816, -6), (key822, -2), (key823, 2), (key827, -2), (key828, 2)]

theorem rowCheck7324 : row7324 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7324 := by decide +kernel

theorem rowEval7324 (x : Key → ℝ) : Integer.Sparse.eval row7324 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form10) x := by
  rw [rowCheck7324, Integer.Sparse.eval_collectBalanced, rawRowCheck7324]

def rawRow7325 : Integer.Sparse Key := [(key809, -4), (key806, 2), (key809, 2), (key814, 2), (key816, 2), (key814, -4), (key784, 2), (key781, -1), (key784, -1), (key814, 2), (key806, -1), (key814, -1), (key827, -1), (key828, -1), (key822, -1), (key828, -1), (key822, 2), (key827, 2), (key784, -1), (key786, -1), (key784, 2), (key814, -1), (key816, -1), (key809, 2), (key816, 2), (key809, -1), (key814, -1), (key828, 2), (key823, -1), (key828, -1)]

theorem rawRowCheck7325 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form10 = rawRow7325 := by decide +kernel

def row7325 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, -3), (key816, 3), (key822, 1), (key823, -1), (key827, 1), (key828, -1)]

theorem rowCheck7325 : row7325 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7325 := by decide +kernel

theorem rowEval7325 (x : Key → ℝ) : Integer.Sparse.eval row7325 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form10) x := by
  rw [rowCheck7325, Integer.Sparse.eval_collectBalanced, rawRowCheck7325]

def rawRow7326 : Integer.Sparse Key := [(key809, -4), (key809, 2), (key806, 2), (key816, 2), (key814, 2), (key814, -4), (key784, 2), (key784, -1), (key781, -1), (key814, 2), (key814, -1), (key806, -1), (key828, -1), (key827, -1), (key828, -1), (key822, -1), (key827, 2), (key822, 2), (key786, -1), (key784, -1), (key784, 2), (key816, -1), (key814, -1), (key816, 2), (key809, 2), (key814, -1), (key809, -1), (key828, 2), (key828, -1), (key823, -1)]

theorem rawRowCheck7326 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form10 = rawRow7326 := by decide +kernel

def row7326 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, -3), (key816, 3), (key822, 1), (key823, -1), (key827, 1), (key828, -1)]

theorem rowCheck7326 : row7326 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7326 := by decide +kernel

theorem rowEval7326 (x : Key → ℝ) : Integer.Sparse.eval row7326 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form10) x := by
  rw [rowCheck7326, Integer.Sparse.eval_collectBalanced, rawRowCheck7326]

def rawRow7327 : Integer.Sparse Key := [(key806, -4), (key814, 2), (key814, 2), (key809, 2), (key809, 2), (key816, -4), (key806, 2), (key814, -1), (key814, -1), (key781, 2), (key827, -1), (key827, -1), (key784, -1), (key784, -1), (key814, -1), (key814, -1), (key828, 2), (key828, 2), (key809, -1), (key809, -1), (key823, 2), (key784, -1), (key784, -1), (key814, 2), (key814, 2), (key828, -1), (key828, -1), (key786, 2), (key816, -1), (key816, -1)]

theorem rawRowCheck7327 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form10 = rawRow7327 := by decide +kernel

def row7327 : Integer.Sparse Key := [(key781, 2), (key784, -4), (key786, 2), (key806, -2), (key809, 2), (key814, 4), (key816, -6), (key823, 2), (key827, -2), (key828, 2)]

theorem rowCheck7327 : row7327 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7327 := by decide +kernel

theorem rowEval7327 (x : Key → ℝ) : Integer.Sparse.eval row7327 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form10) x := by
  rw [rowCheck7327, Integer.Sparse.eval_collectBalanced, rawRowCheck7327]

def rawRow7328 : Integer.Sparse Key := [(key814, -4), (key806, 2), (key814, 2), (key809, 2), (key816, 2), (key809, -4), (key814, 2), (key806, -1), (key814, -1), (key827, 2), (key781, -1), (key827, -1), (key814, -1), (key828, -1), (key784, -1), (key828, -1), (key784, 2), (key814, 2), (key809, -1), (key823, -1), (key809, 2), (key814, -1), (key828, -1), (key784, 2), (key828, 2), (key784, -1), (key814, -1), (key816, 2), (key786, -1), (key816, -1)]

theorem rawRowCheck7328 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form10 = rawRow7328 := by decide +kernel

def row7328 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, -2), (key816, 3), (key823, -1), (key827, 1), (key828, -1)]

theorem rowCheck7328 : row7328 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7328 := by decide +kernel

theorem rowEval7328 (x : Key → ℝ) : Integer.Sparse.eval row7328 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form10) x := by
  rw [rowCheck7328, Integer.Sparse.eval_collectBalanced, rawRowCheck7328]

def rawRow7329 : Integer.Sparse Key := [(key814, -4), (key814, 2), (key806, 2), (key816, 2), (key809, 2), (key809, -4), (key814, 2), (key814, -1), (key806, -1), (key827, 2), (key827, -1), (key781, -1), (key828, -1), (key814, -1), (key828, -1), (key784, -1), (key814, 2), (key784, 2), (key823, -1), (key809, -1), (key809, 2), (key828, -1), (key814, -1), (key828, 2), (key784, 2), (key814, -1), (key784, -1), (key816, 2), (key816, -1), (key786, -1)]

theorem rawRowCheck7329 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form10 = rawRow7329 := by decide +kernel

def row7329 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, -2), (key816, 3), (key823, -1), (key827, 1), (key828, -1)]

theorem rowCheck7329 : row7329 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7329 := by decide +kernel

theorem rowEval7329 (x : Key → ℝ) : Integer.Sparse.eval row7329 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form10) x := by
  rw [rowCheck7329, Integer.Sparse.eval_collectBalanced, rawRowCheck7329]

def rawRow7330 : Integer.Sparse Key := [(key809, -4), (key814, 2), (key816, 2), (key806, 2), (key809, 2), (key814, -4), (key822, 2), (key827, -1), (key828, -1), (key784, 2), (key814, -1), (key828, -1), (key781, -1), (key784, -1), (key806, -1), (key814, -1), (key822, 2), (key827, 2), (key814, -1), (key816, -1), (key828, 2), (key784, -1), (key786, -1), (key809, 2), (key816, 2), (key823, -1), (key828, -1), (key784, 2), (key809, -1), (key814, -1)]

theorem rawRowCheck7330 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form10 = rawRow7330 := by decide +kernel

def row7330 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, -6), (key816, 3), (key822, 4), (key823, -1), (key827, 1), (key828, -1)]

theorem rowCheck7330 : row7330 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7330 := by decide +kernel

theorem rowEval7330 (x : Key → ℝ) : Integer.Sparse.eval row7330 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form10) x := by
  rw [rowCheck7330, Integer.Sparse.eval_collectBalanced, rawRowCheck7330]

def rawRow7331 : Integer.Sparse Key := [(key809, -4), (key816, 2), (key814, 2), (key809, 2), (key806, 2), (key814, -4), (key822, 2), (key828, -1), (key827, -1), (key784, 2), (key828, -1), (key814, -1), (key784, -1), (key781, -1), (key814, -1), (key806, -1), (key827, 2), (key822, 2), (key816, -1), (key814, -1), (key828, 2), (key786, -1), (key784, -1), (key816, 2), (key809, 2), (key828, -1), (key823, -1), (key784, 2), (key814, -1), (key809, -1)]

theorem rawRowCheck7331 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form10 = rawRow7331 := by decide +kernel

def row7331 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, -6), (key816, 3), (key822, 4), (key823, -1), (key827, 1), (key828, -1)]

theorem rowCheck7331 : row7331 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7331 := by decide +kernel

theorem rowEval7331 (x : Key → ℝ) : Integer.Sparse.eval row7331 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form10) x := by
  rw [rowCheck7331, Integer.Sparse.eval_collectBalanced, rawRowCheck7331]

def rawRow7332 : Integer.Sparse Key := [(key814, -4), (key809, 2), (key816, 2), (key806, 2), (key814, 2), (key809, -4), (key827, 2), (key822, -1), (key828, -1), (key814, 2), (key784, -1), (key828, -1), (key806, -1), (key814, -1), (key781, -1), (key827, -1), (key784, 2), (key814, 2), (key814, -1), (key828, -1), (key816, 2), (key809, -1), (key823, -1), (key784, 2), (key828, 2), (key786, -1), (key816, -1), (key809, 2), (key784, -1), (key814, -1)]

theorem rawRowCheck7332 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form10 = rawRow7332 := by decide +kernel

def row7332 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, -1), (key816, 3), (key822, -1), (key823, -1), (key827, 1), (key828, -1)]

theorem rowCheck7332 : row7332 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7332 := by decide +kernel

theorem rowEval7332 (x : Key → ℝ) : Integer.Sparse.eval row7332 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form10) x := by
  rw [rowCheck7332, Integer.Sparse.eval_collectBalanced, rawRowCheck7332]

def rawRow7333 : Integer.Sparse Key := [(key814, -4), (key816, 2), (key809, 2), (key814, 2), (key806, 2), (key809, -4), (key827, 2), (key828, -1), (key822, -1), (key814, 2), (key828, -1), (key784, -1), (key814, -1), (key806, -1), (key827, -1), (key781, -1), (key814, 2), (key784, 2), (key828, -1), (key814, -1), (key816, 2), (key823, -1), (key809, -1), (key828, 2), (key784, 2), (key816, -1), (key786, -1), (key809, 2), (key814, -1), (key784, -1)]

theorem rawRowCheck7333 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form10 = rawRow7333 := by decide +kernel

def row7333 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, -1), (key816, 3), (key822, -1), (key823, -1), (key827, 1), (key828, -1)]

theorem rowCheck7333 : row7333 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7333 := by decide +kernel

theorem rowEval7333 (x : Key → ℝ) : Integer.Sparse.eval row7333 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form10) x := by
  rw [rowCheck7333, Integer.Sparse.eval_collectBalanced, rawRowCheck7333]

def rawRow7334 : Integer.Sparse Key := [(key816, -4), (key809, 2), (key814, 2), (key809, 2), (key814, 2), (key806, -4), (key828, 2), (key822, -1), (key827, -1), (key828, 2), (key784, -1), (key814, -1), (key822, -1), (key827, -1), (key784, -1), (key814, -1), (key781, 2), (key806, 2), (key816, -1), (key828, -1), (key814, 2), (key816, -1), (key828, -1), (key786, 2), (key823, 2), (key784, -1), (key809, -1), (key814, 2), (key784, -1), (key809, -1)]

theorem rawRowCheck7334 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form10 = rawRow7334 := by decide +kernel

def row7334 : Integer.Sparse Key := [(key781, 2), (key784, -4), (key786, 2), (key806, -2), (key809, 2), (key814, 6), (key816, -6), (key822, -2), (key823, 2), (key827, -2), (key828, 2)]

theorem rowCheck7334 : row7334 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7334 := by decide +kernel

theorem rowEval7334 (x : Key → ℝ) : Integer.Sparse.eval row7334 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form10) x := by
  rw [rowCheck7334, Integer.Sparse.eval_collectBalanced, rawRowCheck7334]

def rawRow7335 : Integer.Sparse Key := [(key816, -4), (key814, 2), (key809, 2), (key814, 2), (key809, 2), (key806, -4), (key828, 2), (key827, -1), (key822, -1), (key828, 2), (key814, -1), (key784, -1), (key827, -1), (key822, -1), (key814, -1), (key784, -1), (key806, 2), (key781, 2), (key828, -1), (key816, -1), (key814, 2), (key828, -1), (key816, -1), (key823, 2), (key786, 2), (key809, -1), (key784, -1), (key814, 2), (key809, -1), (key784, -1)]

theorem rawRowCheck7335 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form10 = rawRow7335 := by decide +kernel

def row7335 : Integer.Sparse Key := [(key781, 2), (key784, -4), (key786, 2), (key806, -2), (key809, 2), (key814, 6), (key816, -6), (key822, -2), (key823, 2), (key827, -2), (key828, 2)]

theorem rowCheck7335 : row7335 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7335 := by decide +kernel

theorem rowEval7335 (x : Key → ℝ) : Integer.Sparse.eval row7335 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form10) x := by
  rw [rowCheck7335, Integer.Sparse.eval_collectBalanced, rawRowCheck7335]

def rawRow7336 : Integer.Sparse Key := [(key822, -4), (key822, 2), (key823, 2), (key827, 2), (key828, 2), (key828, -4), (key784, 2), (key784, -1), (key786, -1), (key809, 2), (key809, -1), (key823, -1), (key814, -1), (key816, -1), (key814, -1), (key828, -1), (key816, 2), (key828, 2), (key781, -1), (key784, -1), (key784, 2), (key806, -1), (key809, -1), (key806, 2), (key814, 2), (key809, -1), (key814, -1), (key822, 2), (key822, -1), (key827, -1)]

theorem rawRowCheck7336 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form10 = rawRow7336 := by decide +kernel

def row7336 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, -1), (key816, 1), (key822, -1), (key823, 1), (key827, 1), (key828, -1)]

theorem rowCheck7336 : row7336 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7336 := by decide +kernel

theorem rowEval7336 (x : Key → ℝ) : Integer.Sparse.eval row7336 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form10) x := by
  rw [rowCheck7336, Integer.Sparse.eval_collectBalanced, rawRowCheck7336]

def rawRow7337 : Integer.Sparse Key := [(key822, -4), (key823, 2), (key822, 2), (key828, 2), (key827, 2), (key828, -4), (key784, 2), (key786, -1), (key784, -1), (key809, 2), (key823, -1), (key809, -1), (key816, -1), (key814, -1), (key828, -1), (key814, -1), (key828, 2), (key816, 2), (key784, -1), (key781, -1), (key784, 2), (key809, -1), (key806, -1), (key814, 2), (key806, 2), (key814, -1), (key809, -1), (key822, 2), (key827, -1), (key822, -1)]

theorem rawRowCheck7337 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form10 = rawRow7337 := by decide +kernel

def row7337 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, -1), (key816, 1), (key822, -1), (key823, 1), (key827, 1), (key828, -1)]

theorem rowCheck7337 : row7337 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7337 := by decide +kernel

theorem rowEval7337 (x : Key → ℝ) : Integer.Sparse.eval row7337 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form10) x := by
  rw [rowCheck7337, Integer.Sparse.eval_collectBalanced, rawRowCheck7337]

def rawRow7338 : Integer.Sparse Key := [(key823, -4), (key822, 2), (key822, 2), (key828, 2), (key828, 2), (key827, -4), (key786, 2), (key784, -1), (key784, -1), (key823, 2), (key809, -1), (key809, -1), (key828, -1), (key828, -1), (key816, -1), (key816, -1), (key814, 2), (key814, 2), (key784, -1), (key784, -1), (key781, 2), (key814, -1), (key814, -1), (key809, 2), (key809, 2), (key806, -1), (key806, -1), (key827, 2), (key822, -1), (key822, -1)]

theorem rawRowCheck7338 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form10 = rawRow7338 := by decide +kernel

def row7338 : Integer.Sparse Key := [(key781, 2), (key784, -4), (key786, 2), (key806, -2), (key809, 2), (key814, 2), (key816, -2), (key822, 2), (key823, -2), (key827, -2), (key828, 2)]

theorem rowCheck7338 : row7338 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7338 := by decide +kernel

theorem rowEval7338 (x : Key → ℝ) : Integer.Sparse.eval row7338 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form10) x := by
  rw [rowCheck7338, Integer.Sparse.eval_collectBalanced, rawRowCheck7338]

def rawRow7339 : Integer.Sparse Key := [(key822, -4), (key827, 2), (key828, 2), (key822, 2), (key823, 2), (key828, -4), (key809, 2), (key814, -1), (key816, -1), (key784, 2), (key814, -1), (key828, -1), (key784, -1), (key786, -1), (key809, -1), (key823, -1), (key816, 2), (key828, 2), (key806, -1), (key809, -1), (key814, 2), (key781, -1), (key784, -1), (key806, 2), (key814, 2), (key822, -1), (key827, -1), (key784, 2), (key809, -1), (key814, -1)]

theorem rawRowCheck7339 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form10 = rawRow7339 := by decide +kernel

def row7339 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, 1), (key816, 1), (key822, -3), (key823, 1), (key827, 1), (key828, -1)]

theorem rowCheck7339 : row7339 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7339 := by decide +kernel

theorem rowEval7339 (x : Key → ℝ) : Integer.Sparse.eval row7339 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form10) x := by
  rw [rowCheck7339, Integer.Sparse.eval_collectBalanced, rawRowCheck7339]

def rawRow7340 : Integer.Sparse Key := [(key822, -4), (key828, 2), (key827, 2), (key823, 2), (key822, 2), (key828, -4), (key809, 2), (key816, -1), (key814, -1), (key784, 2), (key828, -1), (key814, -1), (key786, -1), (key784, -1), (key823, -1), (key809, -1), (key828, 2), (key816, 2), (key809, -1), (key806, -1), (key814, 2), (key784, -1), (key781, -1), (key814, 2), (key806, 2), (key827, -1), (key822, -1), (key784, 2), (key814, -1), (key809, -1)]

theorem rawRowCheck7340 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form10 = rawRow7340 := by decide +kernel

def row7340 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, 1), (key816, 1), (key822, -3), (key823, 1), (key827, 1), (key828, -1)]

theorem rowCheck7340 : row7340 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7340 := by decide +kernel

theorem rowEval7340 (x : Key → ℝ) : Integer.Sparse.eval row7340 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form10) x := by
  rw [rowCheck7340, Integer.Sparse.eval_collectBalanced, rawRowCheck7340]

def rawRow7341 : Integer.Sparse Key := [(key827, -4), (key822, 2), (key828, 2), (key822, 2), (key828, 2), (key823, -4), (key814, 2), (key809, -1), (key816, -1), (key814, 2), (key784, -1), (key828, -1), (key809, -1), (key816, -1), (key784, -1), (key828, -1), (key786, 2), (key823, 2), (key806, -1), (key814, -1), (key809, 2), (key806, -1), (key814, -1), (key781, 2), (key827, 2), (key784, -1), (key814, -1), (key809, 2), (key784, -1), (key814, -1)]

theorem rawRowCheck7341 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form10 = rawRow7341 := by decide +kernel

def row7341 : Integer.Sparse Key := [(key781, 2), (key784, -4), (key786, 2), (key806, -2), (key809, 2), (key816, -2), (key822, 4), (key823, -2), (key827, -2), (key828, 2)]

theorem rowCheck7341 : row7341 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7341 := by decide +kernel

theorem rowEval7341 (x : Key → ℝ) : Integer.Sparse.eval row7341 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form10) x := by
  rw [rowCheck7341, Integer.Sparse.eval_collectBalanced, rawRowCheck7341]

def rawRow7342 : Integer.Sparse Key := [(key827, -4), (key828, 2), (key822, 2), (key828, 2), (key822, 2), (key823, -4), (key814, 2), (key816, -1), (key809, -1), (key814, 2), (key828, -1), (key784, -1), (key816, -1), (key809, -1), (key828, -1), (key784, -1), (key823, 2), (key786, 2), (key814, -1), (key806, -1), (key809, 2), (key814, -1), (key806, -1), (key827, 2), (key781, 2), (key814, -1), (key784, -1), (key809, 2), (key814, -1), (key784, -1)]

theorem rawRowCheck7342 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form10 = rawRow7342 := by decide +kernel

def row7342 : Integer.Sparse Key := [(key781, 2), (key784, -4), (key786, 2), (key806, -2), (key809, 2), (key816, -2), (key822, 4), (key823, -2), (key827, -2), (key828, 2)]

theorem rowCheck7342 : row7342 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7342 := by decide +kernel

theorem rowEval7342 (x : Key → ℝ) : Integer.Sparse.eval row7342 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form10) x := by
  rw [rowCheck7342, Integer.Sparse.eval_collectBalanced, rawRowCheck7342]

def rawRow7343 : Integer.Sparse Key := [(key828, -4), (key822, 2), (key827, 2), (key823, 2), (key828, 2), (key822, -4), (key816, 2), (key809, -1), (key814, -1), (key828, 2), (key784, -1), (key814, -1), (key823, -1), (key828, -1), (key786, -1), (key816, -1), (key784, 2), (key809, 2), (key809, -1), (key814, -1), (key806, 2), (key822, -1), (key827, -1), (key784, 2), (key814, 2), (key781, -1), (key806, -1), (key814, 2), (key784, -1), (key809, -1)]

theorem rawRowCheck7343 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form10 = rawRow7343 := by decide +kernel

def row7343 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, 1), (key816, 1), (key822, -3), (key823, 1), (key827, 1), (key828, -1)]

theorem rowCheck7343 : row7343 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7343 := by decide +kernel

theorem rowEval7343 (x : Key → ℝ) : Integer.Sparse.eval row7343 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form10) x := by
  rw [rowCheck7343, Integer.Sparse.eval_collectBalanced, rawRowCheck7343]

def rawRow7344 : Integer.Sparse Key := [(key828, -4), (key827, 2), (key822, 2), (key828, 2), (key823, 2), (key822, -4), (key816, 2), (key814, -1), (key809, -1), (key828, 2), (key814, -1), (key784, -1), (key828, -1), (key823, -1), (key816, -1), (key786, -1), (key809, 2), (key784, 2), (key814, -1), (key809, -1), (key806, 2), (key827, -1), (key822, -1), (key814, 2), (key784, 2), (key806, -1), (key781, -1), (key814, 2), (key809, -1), (key784, -1)]

theorem rawRowCheck7344 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form10 = rawRow7344 := by decide +kernel

def row7344 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, 1), (key816, 1), (key822, -3), (key823, 1), (key827, 1), (key828, -1)]

theorem rowCheck7344 : row7344 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7344 := by decide +kernel

theorem rowEval7344 (x : Key → ℝ) : Integer.Sparse.eval row7344 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form10) x := by
  rw [rowCheck7344, Integer.Sparse.eval_collectBalanced, rawRowCheck7344]

def rawRow7345 : Integer.Sparse Key := [(key823, -4), (key828, 2), (key828, 2), (key822, 2), (key822, 2), (key827, -4), (key823, 2), (key828, -1), (key828, -1), (key786, 2), (key816, -1), (key816, -1), (key784, -1), (key784, -1), (key809, -1), (key809, -1), (key814, 2), (key814, 2), (key822, -1), (key822, -1), (key827, 2), (key784, -1), (key784, -1), (key809, 2), (key809, 2), (key814, -1), (key814, -1), (key781, 2), (key806, -1), (key806, -1)]

theorem rawRowCheck7345 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form10 = rawRow7345 := by decide +kernel

def row7345 : Integer.Sparse Key := [(key781, 2), (key784, -4), (key786, 2), (key806, -2), (key809, 2), (key814, 2), (key816, -2), (key822, 2), (key823, -2), (key827, -2), (key828, 2)]

theorem rowCheck7345 : row7345 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7345 := by decide +kernel

theorem rowEval7345 (x : Key → ℝ) : Integer.Sparse.eval row7345 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form10) x := by
  rw [rowCheck7345, Integer.Sparse.eval_collectBalanced, rawRowCheck7345]

def rawRow7346 : Integer.Sparse Key := [(key828, -4), (key823, 2), (key828, 2), (key822, 2), (key827, 2), (key822, -4), (key828, 2), (key823, -1), (key828, -1), (key816, 2), (key786, -1), (key816, -1), (key809, -1), (key814, -1), (key784, -1), (key814, -1), (key784, 2), (key809, 2), (key822, -1), (key827, -1), (key822, 2), (key809, -1), (key814, -1), (key784, 2), (key814, 2), (key784, -1), (key809, -1), (key806, 2), (key781, -1), (key806, -1)]

theorem rawRowCheck7346 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form10 = rawRow7346 := by decide +kernel

def row7346 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, -1), (key816, 1), (key822, -1), (key823, 1), (key827, 1), (key828, -1)]

theorem rowCheck7346 : row7346 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7346 := by decide +kernel

theorem rowEval7346 (x : Key → ℝ) : Integer.Sparse.eval row7346 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form10) x := by
  rw [rowCheck7346, Integer.Sparse.eval_collectBalanced, rawRowCheck7346]

def rawRow7347 : Integer.Sparse Key := [(key828, -4), (key828, 2), (key823, 2), (key827, 2), (key822, 2), (key822, -4), (key828, 2), (key828, -1), (key823, -1), (key816, 2), (key816, -1), (key786, -1), (key814, -1), (key809, -1), (key814, -1), (key784, -1), (key809, 2), (key784, 2), (key827, -1), (key822, -1), (key822, 2), (key814, -1), (key809, -1), (key814, 2), (key784, 2), (key809, -1), (key784, -1), (key806, 2), (key806, -1), (key781, -1)]

theorem rawRowCheck7347 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form10 = rawRow7347 := by decide +kernel

def row7347 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, -1), (key816, 1), (key822, -1), (key823, 1), (key827, 1), (key828, -1)]

theorem rowCheck7347 : row7347 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7347 := by decide +kernel

theorem rowEval7347 (x : Key → ℝ) : Integer.Sparse.eval row7347 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form10) x := by
  rw [rowCheck7347, Integer.Sparse.eval_collectBalanced, rawRowCheck7347]

def rawRow7348 : Integer.Sparse Key := [(key2362, 2), (key2365, 2), (key2365, 2), (key2457, 2), (key2521, 2), (key2521, 2), (key2532, 2), (key2532, 2), (key2562, 2), (key2562, 2), (key2564, 2), (key2564, 2), (key2365, -2), (key2365, -2), (key2367, -2), (key2460, -2), (key2460, -2), (key2521, -2), (key2521, -2), (key2525, -2), (key2525, -2), (key2533, -2), (key2564, -2), (key2564, -2)]

theorem rawRowCheck7348 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form0 = rawRow7348 := by decide +kernel

def row7348 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, -4), (key2525, -4), (key2532, 4), (key2533, -2), (key2562, 4)]

theorem rowCheck7348 : row7348 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7348 := by decide +kernel

theorem rowEval7348 (x : Key → ℝ) : Integer.Sparse.eval row7348 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7348, Integer.Sparse.eval_collectBalanced, rawRowCheck7348]

def rawRow7349 : Integer.Sparse Key := [(key2365, 2), (key2362, 2), (key2365, 2), (key2521, 2), (key2457, 2), (key2521, 2), (key2562, 2), (key2564, 2), (key2532, 2), (key2564, 2), (key2532, 2), (key2562, 2), (key2365, -2), (key2367, -2), (key2365, -2), (key2521, -2), (key2525, -2), (key2460, -2), (key2525, -2), (key2460, -2), (key2521, -2), (key2564, -2), (key2533, -2), (key2564, -2)]

theorem rawRowCheck7349 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form0 = rawRow7349 := by decide +kernel

def row7349 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, -4), (key2525, -4), (key2532, 4), (key2533, -2), (key2562, 4)]

theorem rowCheck7349 : row7349 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7349 := by decide +kernel

theorem rowEval7349 (x : Key → ℝ) : Integer.Sparse.eval row7349 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7349, Integer.Sparse.eval_collectBalanced, rawRowCheck7349]

def rawRow7350 : Integer.Sparse Key := [(key2365, 2), (key2365, 2), (key2362, 2), (key2521, 2), (key2521, 2), (key2457, 2), (key2564, 2), (key2562, 2), (key2564, 2), (key2532, 2), (key2562, 2), (key2532, 2), (key2367, -2), (key2365, -2), (key2365, -2), (key2525, -2), (key2521, -2), (key2525, -2), (key2460, -2), (key2521, -2), (key2460, -2), (key2564, -2), (key2564, -2), (key2533, -2)]

theorem rawRowCheck7350 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form0 = rawRow7350 := by decide +kernel

def row7350 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, -4), (key2525, -4), (key2532, 4), (key2533, -2), (key2562, 4)]

theorem rowCheck7350 : row7350 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7350 := by decide +kernel

theorem rowEval7350 (x : Key → ℝ) : Integer.Sparse.eval row7350 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7350, Integer.Sparse.eval_collectBalanced, rawRowCheck7350]

def rawRow7351 : Integer.Sparse Key := [(key2457, 2), (key2521, 2), (key2521, 2), (key2362, 2), (key2562, 2), (key2562, 2), (key2365, 2), (key2365, 2), (key2521, 2), (key2521, 2), (key2564, 2), (key2564, 2), (key2460, -2), (key2460, -2), (key2533, -2), (key2365, -2), (key2365, -2), (key2521, -2), (key2521, -2), (key2564, -2), (key2564, -2), (key2367, -2), (key2525, -2), (key2525, -2)]

theorem rawRowCheck7351 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form0 = rawRow7351 := by decide +kernel

def row7351 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, -4), (key2521, 4), (key2525, -4), (key2533, -2), (key2562, 4)]

theorem rowCheck7351 : row7351 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7351 := by decide +kernel

theorem rowEval7351 (x : Key → ℝ) : Integer.Sparse.eval row7351 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7351, Integer.Sparse.eval_collectBalanced, rawRowCheck7351]

def rawRow7352 : Integer.Sparse Key := [(key2521, 2), (key2457, 2), (key2521, 2), (key2562, 2), (key2362, 2), (key2562, 2), (key2521, 2), (key2564, 2), (key2365, 2), (key2564, 2), (key2365, 2), (key2521, 2), (key2460, -2), (key2533, -2), (key2460, -2), (key2521, -2), (key2564, -2), (key2365, -2), (key2564, -2), (key2365, -2), (key2521, -2), (key2525, -2), (key2367, -2), (key2525, -2)]

theorem rawRowCheck7352 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form0 = rawRow7352 := by decide +kernel

def row7352 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, -4), (key2521, 4), (key2525, -4), (key2533, -2), (key2562, 4)]

theorem rowCheck7352 : row7352 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7352 := by decide +kernel

theorem rowEval7352 (x : Key → ℝ) : Integer.Sparse.eval row7352 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7352, Integer.Sparse.eval_collectBalanced, rawRowCheck7352]

def rawRow7353 : Integer.Sparse Key := [(key2521, 2), (key2521, 2), (key2457, 2), (key2562, 2), (key2562, 2), (key2362, 2), (key2564, 2), (key2521, 2), (key2564, 2), (key2365, 2), (key2521, 2), (key2365, 2), (key2533, -2), (key2460, -2), (key2460, -2), (key2564, -2), (key2521, -2), (key2564, -2), (key2365, -2), (key2521, -2), (key2365, -2), (key2525, -2), (key2525, -2), (key2367, -2)]

theorem rawRowCheck7353 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form0 = rawRow7353 := by decide +kernel

def row7353 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, -4), (key2521, 4), (key2525, -4), (key2533, -2), (key2562, 4)]

theorem rowCheck7353 : row7353 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7353 := by decide +kernel

theorem rowEval7353 (x : Key → ℝ) : Integer.Sparse.eval row7353 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck7353, Integer.Sparse.eval_collectBalanced, rawRowCheck7353]

def rawRow7354 : Integer.Sparse Key := [(key2532, 2), (key2562, 2), (key2564, 2), (key2365, 2), (key2521, 2), (key2564, 2), (key2362, 2), (key2365, 2), (key2457, 2), (key2521, 2), (key2532, 2), (key2562, 2), (key2521, -2), (key2525, -2), (key2564, -2), (key2365, -2), (key2367, -2), (key2460, -2), (key2525, -2), (key2533, -2), (key2564, -2), (key2365, -2), (key2460, -2), (key2521, -2)]

theorem rawRowCheck7354 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form0 = rawRow7354 := by decide +kernel

def row7354 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, -4), (key2525, -4), (key2532, 4), (key2533, -2), (key2562, 4)]

theorem rowCheck7354 : row7354 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7354 := by decide +kernel

theorem rowEval7354 (x : Key → ℝ) : Integer.Sparse.eval row7354 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7354, Integer.Sparse.eval_collectBalanced, rawRowCheck7354]

def rawRow7355 : Integer.Sparse Key := [(key2532, 2), (key2564, 2), (key2562, 2), (key2365, 2), (key2564, 2), (key2521, 2), (key2365, 2), (key2362, 2), (key2521, 2), (key2457, 2), (key2562, 2), (key2532, 2), (key2525, -2), (key2521, -2), (key2564, -2), (key2367, -2), (key2365, -2), (key2525, -2), (key2460, -2), (key2564, -2), (key2533, -2), (key2365, -2), (key2521, -2), (key2460, -2)]

theorem rawRowCheck7355 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form0 = rawRow7355 := by decide +kernel

def row7355 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, -4), (key2525, -4), (key2532, 4), (key2533, -2), (key2562, 4)]

theorem rowCheck7355 : row7355 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7355 := by decide +kernel

theorem rowEval7355 (x : Key → ℝ) : Integer.Sparse.eval row7355 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7355, Integer.Sparse.eval_collectBalanced, rawRowCheck7355]

def rawRow7356 : Integer.Sparse Key := [(key2562, 2), (key2532, 2), (key2564, 2), (key2521, 2), (key2365, 2), (key2564, 2), (key2457, 2), (key2521, 2), (key2362, 2), (key2562, 2), (key2365, 2), (key2521, 2), (key2521, -2), (key2564, -2), (key2525, -2), (key2460, -2), (key2533, -2), (key2365, -2), (key2564, -2), (key2367, -2), (key2525, -2), (key2460, -2), (key2365, -2), (key2521, -2)]

theorem rawRowCheck7356 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form0 = rawRow7356 := by decide +kernel

def row7356 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, -4), (key2521, 2), (key2525, -4), (key2532, 2), (key2533, -2), (key2562, 4)]

theorem rowCheck7356 : row7356 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7356 := by decide +kernel

theorem rowEval7356 (x : Key → ℝ) : Integer.Sparse.eval row7356 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7356, Integer.Sparse.eval_collectBalanced, rawRowCheck7356]

def rawRow7357 : Integer.Sparse Key := [(key2562, 2), (key2564, 2), (key2532, 2), (key2521, 2), (key2564, 2), (key2365, 2), (key2521, 2), (key2457, 2), (key2562, 2), (key2362, 2), (key2521, 2), (key2365, 2), (key2564, -2), (key2521, -2), (key2525, -2), (key2533, -2), (key2460, -2), (key2564, -2), (key2365, -2), (key2525, -2), (key2367, -2), (key2460, -2), (key2521, -2), (key2365, -2)]

theorem rawRowCheck7357 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form0 = rawRow7357 := by decide +kernel

def row7357 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, -4), (key2521, 2), (key2525, -4), (key2532, 2), (key2533, -2), (key2562, 4)]

theorem rowCheck7357 : row7357 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7357 := by decide +kernel

theorem rowEval7357 (x : Key → ℝ) : Integer.Sparse.eval row7357 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck7357, Integer.Sparse.eval_collectBalanced, rawRowCheck7357]

def rawRow7358 : Integer.Sparse Key := [(key2564, 2), (key2532, 2), (key2562, 2), (key2564, 2), (key2365, 2), (key2521, 2), (key2532, 2), (key2562, 2), (key2365, 2), (key2521, 2), (key2362, 2), (key2457, 2), (key2525, -2), (key2564, -2), (key2521, -2), (key2525, -2), (key2564, -2), (key2367, -2), (key2533, -2), (key2365, -2), (key2460, -2), (key2521, -2), (key2365, -2), (key2460, -2)]

theorem rawRowCheck7358 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form0 = rawRow7358 := by decide +kernel

def row7358 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, -4), (key2525, -4), (key2532, 4), (key2533, -2), (key2562, 4)]

theorem rowCheck7358 : row7358 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7358 := by decide +kernel

theorem rowEval7358 (x : Key → ℝ) : Integer.Sparse.eval row7358 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7358, Integer.Sparse.eval_collectBalanced, rawRowCheck7358]

def rawRow7359 : Integer.Sparse Key := [(key2564, 2), (key2562, 2), (key2532, 2), (key2564, 2), (key2521, 2), (key2365, 2), (key2562, 2), (key2532, 2), (key2521, 2), (key2365, 2), (key2457, 2), (key2362, 2), (key2564, -2), (key2525, -2), (key2521, -2), (key2564, -2), (key2525, -2), (key2533, -2), (key2367, -2), (key2460, -2), (key2365, -2), (key2521, -2), (key2460, -2), (key2365, -2)]

theorem rawRowCheck7359 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form0 = rawRow7359 := by decide +kernel

def row7359 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, -4), (key2525, -4), (key2532, 4), (key2533, -2), (key2562, 4)]

theorem rowCheck7359 : row7359 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7359 := by decide +kernel

theorem rowEval7359 (x : Key → ℝ) : Integer.Sparse.eval row7359 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck7359, Integer.Sparse.eval_collectBalanced, rawRowCheck7359]

def rawRow7360 : Integer.Sparse Key := [(key2365, 2), (key2365, 2), (key2367, 2), (key2460, 2), (key2460, 2), (key2533, 2), (key2521, 2), (key2525, 2), (key2521, 2), (key2564, 2), (key2525, 2), (key2564, 2), (key2362, -2), (key2365, -2), (key2365, -2), (key2457, -2), (key2460, -2), (key2457, -2), (key2521, -2), (key2460, -2), (key2521, -2), (key2532, -2), (key2532, -2), (key2562, -2)]

theorem rawRowCheck7360 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form0 = rawRow7360 := by decide +kernel

def row7360 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -4), (key2525, 4), (key2532, -4), (key2533, 2), (key2562, -2), (key2564, 4)]

theorem rowCheck7360 : row7360 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7360 := by decide +kernel

theorem rowEval7360 (x : Key → ℝ) : Integer.Sparse.eval row7360 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7360, Integer.Sparse.eval_collectBalanced, rawRowCheck7360]

def rawRow7361 : Integer.Sparse Key := [(key2365, 2), (key2367, 2), (key2365, 2), (key2460, 2), (key2533, 2), (key2460, 2), (key2525, 2), (key2521, 2), (key2564, 2), (key2521, 2), (key2564, 2), (key2525, 2), (key2365, -2), (key2362, -2), (key2365, -2), (key2460, -2), (key2457, -2), (key2521, -2), (key2457, -2), (key2521, -2), (key2460, -2), (key2532, -2), (key2562, -2), (key2532, -2)]

theorem rawRowCheck7361 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form0 = rawRow7361 := by decide +kernel

def row7361 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -4), (key2525, 4), (key2532, -4), (key2533, 2), (key2562, -2), (key2564, 4)]

theorem rowCheck7361 : row7361 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7361 := by decide +kernel

theorem rowEval7361 (x : Key → ℝ) : Integer.Sparse.eval row7361 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7361, Integer.Sparse.eval_collectBalanced, rawRowCheck7361]

def rawRow7362 : Integer.Sparse Key := [(key2367, 2), (key2365, 2), (key2365, 2), (key2533, 2), (key2460, 2), (key2460, 2), (key2564, 2), (key2564, 2), (key2525, 2), (key2525, 2), (key2521, 2), (key2521, 2), (key2365, -2), (key2365, -2), (key2362, -2), (key2521, -2), (key2521, -2), (key2460, -2), (key2460, -2), (key2457, -2), (key2457, -2), (key2562, -2), (key2532, -2), (key2532, -2)]

theorem rawRowCheck7362 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form0 = rawRow7362 := by decide +kernel

def row7362 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -4), (key2525, 4), (key2532, -4), (key2533, 2), (key2562, -2), (key2564, 4)]

theorem rowCheck7362 : row7362 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7362 := by decide +kernel

theorem rowEval7362 (x : Key → ℝ) : Integer.Sparse.eval row7362 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7362, Integer.Sparse.eval_collectBalanced, rawRowCheck7362]

def rawRow7363 : Integer.Sparse Key := [(key2460, 2), (key2521, 2), (key2525, 2), (key2365, 2), (key2521, 2), (key2564, 2), (key2365, 2), (key2367, 2), (key2460, 2), (key2533, 2), (key2525, 2), (key2564, 2), (key2457, -2), (key2460, -2), (key2521, -2), (key2362, -2), (key2365, -2), (key2457, -2), (key2521, -2), (key2532, -2), (key2562, -2), (key2365, -2), (key2460, -2), (key2521, -2)]

theorem rawRowCheck7363 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form0 = rawRow7363 := by decide +kernel

def row7363 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -4), (key2521, -2), (key2525, 4), (key2532, -2), (key2533, 2), (key2562, -2), (key2564, 4)]

theorem rowCheck7363 : row7363 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7363 := by decide +kernel

theorem rowEval7363 (x : Key → ℝ) : Integer.Sparse.eval row7363 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7363, Integer.Sparse.eval_collectBalanced, rawRowCheck7363]

def rawRow7364 : Integer.Sparse Key := [(key2460, 2), (key2525, 2), (key2521, 2), (key2365, 2), (key2564, 2), (key2521, 2), (key2367, 2), (key2365, 2), (key2533, 2), (key2460, 2), (key2564, 2), (key2525, 2), (key2460, -2), (key2457, -2), (key2521, -2), (key2365, -2), (key2362, -2), (key2521, -2), (key2457, -2), (key2562, -2), (key2532, -2), (key2365, -2), (key2521, -2), (key2460, -2)]

theorem rawRowCheck7364 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form0 = rawRow7364 := by decide +kernel

def row7364 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -4), (key2521, -2), (key2525, 4), (key2532, -2), (key2533, 2), (key2562, -2), (key2564, 4)]

theorem rowCheck7364 : row7364 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7364 := by decide +kernel

theorem rowEval7364 (x : Key → ℝ) : Integer.Sparse.eval row7364 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7364, Integer.Sparse.eval_collectBalanced, rawRowCheck7364]

def rawRow7365 : Integer.Sparse Key := [(key2521, 2), (key2460, 2), (key2525, 2), (key2521, 2), (key2365, 2), (key2564, 2), (key2460, 2), (key2525, 2), (key2365, 2), (key2564, 2), (key2367, 2), (key2533, 2), (key2457, -2), (key2521, -2), (key2460, -2), (key2457, -2), (key2521, -2), (key2362, -2), (key2562, -2), (key2365, -2), (key2521, -2), (key2460, -2), (key2365, -2), (key2521, -2)]

theorem rawRowCheck7365 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form0 = rawRow7365 := by decide +kernel

def row7365 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -4), (key2521, -4), (key2525, 4), (key2533, 2), (key2562, -2), (key2564, 4)]

theorem rowCheck7365 : row7365 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7365 := by decide +kernel

theorem rowEval7365 (x : Key → ℝ) : Integer.Sparse.eval row7365 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7365, Integer.Sparse.eval_collectBalanced, rawRowCheck7365]

def rawRow7366 : Integer.Sparse Key := [(key2521, 2), (key2525, 2), (key2460, 2), (key2521, 2), (key2564, 2), (key2365, 2), (key2525, 2), (key2460, 2), (key2564, 2), (key2365, 2), (key2533, 2), (key2367, 2), (key2521, -2), (key2457, -2), (key2460, -2), (key2521, -2), (key2457, -2), (key2562, -2), (key2362, -2), (key2521, -2), (key2365, -2), (key2460, -2), (key2521, -2), (key2365, -2)]

theorem rawRowCheck7366 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form0 = rawRow7366 := by decide +kernel

def row7366 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -4), (key2521, -4), (key2525, 4), (key2533, 2), (key2562, -2), (key2564, 4)]

theorem rowCheck7366 : row7366 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7366 := by decide +kernel

theorem rowEval7366 (x : Key → ℝ) : Integer.Sparse.eval row7366 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck7366, Integer.Sparse.eval_collectBalanced, rawRowCheck7366]

def rawRow7367 : Integer.Sparse Key := [(key2525, 2), (key2460, 2), (key2521, 2), (key2564, 2), (key2365, 2), (key2521, 2), (key2533, 2), (key2564, 2), (key2367, 2), (key2525, 2), (key2365, 2), (key2460, 2), (key2460, -2), (key2521, -2), (key2457, -2), (key2532, -2), (key2562, -2), (key2365, -2), (key2521, -2), (key2362, -2), (key2457, -2), (key2521, -2), (key2365, -2), (key2460, -2)]

theorem rawRowCheck7367 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form0 = rawRow7367 := by decide +kernel

def row7367 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -4), (key2521, -2), (key2525, 4), (key2532, -2), (key2533, 2), (key2562, -2), (key2564, 4)]

theorem rowCheck7367 : row7367 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7367 := by decide +kernel

theorem rowEval7367 (x : Key → ℝ) : Integer.Sparse.eval row7367 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7367, Integer.Sparse.eval_collectBalanced, rawRowCheck7367]

def rawRow7368 : Integer.Sparse Key := [(key2525, 2), (key2521, 2), (key2460, 2), (key2564, 2), (key2521, 2), (key2365, 2), (key2564, 2), (key2533, 2), (key2525, 2), (key2367, 2), (key2460, 2), (key2365, 2), (key2521, -2), (key2460, -2), (key2457, -2), (key2562, -2), (key2532, -2), (key2521, -2), (key2365, -2), (key2457, -2), (key2362, -2), (key2521, -2), (key2460, -2), (key2365, -2)]

theorem rawRowCheck7368 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form0 = rawRow7368 := by decide +kernel

def row7368 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -4), (key2521, -2), (key2525, 4), (key2532, -2), (key2533, 2), (key2562, -2), (key2564, 4)]

theorem rowCheck7368 : row7368 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7368 := by decide +kernel

theorem rowEval7368 (x : Key → ℝ) : Integer.Sparse.eval row7368 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck7368, Integer.Sparse.eval_collectBalanced, rawRowCheck7368]

def rawRow7369 : Integer.Sparse Key := [(key2533, 2), (key2564, 2), (key2564, 2), (key2367, 2), (key2525, 2), (key2525, 2), (key2365, 2), (key2365, 2), (key2460, 2), (key2460, 2), (key2521, 2), (key2521, 2), (key2532, -2), (key2532, -2), (key2562, -2), (key2365, -2), (key2365, -2), (key2460, -2), (key2460, -2), (key2521, -2), (key2521, -2), (key2362, -2), (key2457, -2), (key2457, -2)]

theorem rawRowCheck7369 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form0 = rawRow7369 := by decide +kernel

def row7369 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -4), (key2525, 4), (key2532, -4), (key2533, 2), (key2562, -2), (key2564, 4)]

theorem rowCheck7369 : row7369 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7369 := by decide +kernel

theorem rowEval7369 (x : Key → ℝ) : Integer.Sparse.eval row7369 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7369, Integer.Sparse.eval_collectBalanced, rawRowCheck7369]

def rawRow7370 : Integer.Sparse Key := [(key2564, 2), (key2533, 2), (key2564, 2), (key2525, 2), (key2367, 2), (key2525, 2), (key2460, 2), (key2521, 2), (key2365, 2), (key2521, 2), (key2365, 2), (key2460, 2), (key2532, -2), (key2562, -2), (key2532, -2), (key2460, -2), (key2521, -2), (key2365, -2), (key2521, -2), (key2365, -2), (key2460, -2), (key2457, -2), (key2362, -2), (key2457, -2)]

theorem rawRowCheck7370 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form0 = rawRow7370 := by decide +kernel

def row7370 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -4), (key2525, 4), (key2532, -4), (key2533, 2), (key2562, -2), (key2564, 4)]

theorem rowCheck7370 : row7370 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7370 := by decide +kernel

theorem rowEval7370 (x : Key → ℝ) : Integer.Sparse.eval row7370 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7370, Integer.Sparse.eval_collectBalanced, rawRowCheck7370]

def rawRow7371 : Integer.Sparse Key := [(key2564, 2), (key2564, 2), (key2533, 2), (key2525, 2), (key2525, 2), (key2367, 2), (key2521, 2), (key2460, 2), (key2521, 2), (key2365, 2), (key2460, 2), (key2365, 2), (key2562, -2), (key2532, -2), (key2532, -2), (key2521, -2), (key2460, -2), (key2521, -2), (key2365, -2), (key2460, -2), (key2365, -2), (key2457, -2), (key2457, -2), (key2362, -2)]

theorem rawRowCheck7371 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form0 = rawRow7371 := by decide +kernel

def row7371 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -4), (key2525, 4), (key2532, -4), (key2533, 2), (key2562, -2), (key2564, 4)]

theorem rowCheck7371 : row7371 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7371 := by decide +kernel

theorem rowEval7371 (x : Key → ℝ) : Integer.Sparse.eval row7371 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck7371, Integer.Sparse.eval_collectBalanced, rawRowCheck7371]

def rawRow7372 : Integer.Sparse Key := [(key1088, 2), (key1088, 2), (key1088, 2), (key1088, 2), (key1088, 2), (key1088, 2), (key1088, 2), (key1088, 2), (key1088, 2), (key1088, 2), (key1088, 2), (key1088, 2), (key1178, -2), (key1178, -2), (key1178, -2), (key1178, -2), (key1178, -2), (key1178, -2), (key1178, -2), (key1178, -2), (key1178, -2), (key1178, -2), (key1178, -2), (key1178, -2)]

theorem rawRowCheck7372 : GramPolynomial.normalizedRow 0 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form0 = rawRow7372 := by decide +kernel

def row7372 : Integer.Sparse Key := [(key1088, 24), (key1178, -24)]

theorem rowCheck7372 : row7372 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7372 := by decide +kernel

theorem rowEval7372 (x : Key → ℝ) : Integer.Sparse.eval row7372 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7372, Integer.Sparse.eval_collectBalanced, rawRowCheck7372]

def rawRow7373 : Integer.Sparse Key := [(key974, 2), (key974, 2), (key974, 2), (key1088, 2), (key1088, 2), (key1088, 2), (key1178, 2), (key1178, 2), (key1178, 2), (key1178, 2), (key1178, 2), (key1178, 2), (key974, -2), (key974, -2), (key974, -2), (key1088, -2), (key1088, -2), (key1088, -2), (key1088, -2), (key1088, -2), (key1088, -2), (key1178, -2), (key1178, -2), (key1178, -2)]

theorem rawRowCheck7373 : GramPolynomial.normalizedRow 0 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form0 = rawRow7373 := by decide +kernel

def row7373 : Integer.Sparse Key := [(key1088, -6), (key1178, 6)]

theorem rowCheck7373 : row7373 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7373 := by decide +kernel

theorem rowEval7373 (x : Key → ℝ) : Integer.Sparse.eval row7373 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7373, Integer.Sparse.eval_collectBalanced, rawRowCheck7373]

def rawRow7374 : Integer.Sparse Key := [(key1088, 2), (key1178, 2), (key1178, 2), (key974, 2), (key1178, 2), (key1178, 2), (key974, 2), (key974, 2), (key1088, 2), (key1088, 2), (key1178, 2), (key1178, 2), (key1088, -2), (key1088, -2), (key1178, -2), (key974, -2), (key974, -2), (key1088, -2), (key1088, -2), (key1178, -2), (key1178, -2), (key974, -2), (key1088, -2), (key1088, -2)]

theorem rawRowCheck7374 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form0 = rawRow7374 := by decide +kernel

def row7374 : Integer.Sparse Key := [(key1088, -6), (key1178, 6)]

theorem rowCheck7374 : row7374 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7374 := by decide +kernel

theorem rowEval7374 (x : Key → ℝ) : Integer.Sparse.eval row7374 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7374, Integer.Sparse.eval_collectBalanced, rawRowCheck7374]

def rawRow7375 : Integer.Sparse Key := [(key1178, 2), (key1088, 2), (key1178, 2), (key1178, 2), (key974, 2), (key1178, 2), (key1088, 2), (key1178, 2), (key974, 2), (key1178, 2), (key974, 2), (key1088, 2), (key1088, -2), (key1178, -2), (key1088, -2), (key1088, -2), (key1178, -2), (key974, -2), (key1178, -2), (key974, -2), (key1088, -2), (key1088, -2), (key974, -2), (key1088, -2)]

theorem rawRowCheck7375 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form0 = rawRow7375 := by decide +kernel

def row7375 : Integer.Sparse Key := [(key1088, -6), (key1178, 6)]

theorem rowCheck7375 : row7375 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7375 := by decide +kernel

theorem rowEval7375 (x : Key → ℝ) : Integer.Sparse.eval row7375 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7375, Integer.Sparse.eval_collectBalanced, rawRowCheck7375]

def rawRow7376 : Integer.Sparse Key := [(key1178, 2), (key1178, 2), (key1088, 2), (key1178, 2), (key1178, 2), (key974, 2), (key1178, 2), (key1088, 2), (key1178, 2), (key974, 2), (key1088, 2), (key974, 2), (key1178, -2), (key1088, -2), (key1088, -2), (key1178, -2), (key1088, -2), (key1178, -2), (key974, -2), (key1088, -2), (key974, -2), (key1088, -2), (key1088, -2), (key974, -2)]

theorem rawRowCheck7376 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form0 = rawRow7376 := by decide +kernel

def row7376 : Integer.Sparse Key := [(key1088, -6), (key1178, 6)]

theorem rowCheck7376 : row7376 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7376 := by decide +kernel

theorem rowEval7376 (x : Key → ℝ) : Integer.Sparse.eval row7376 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck7376, Integer.Sparse.eval_collectBalanced, rawRowCheck7376]

def rawRow7377 : Integer.Sparse Key := [(key0, -24), (key83, 6), (key83, 6), (key83, 6), (key83, 6)]

theorem rawRowCheck7377 : GramPolynomial.normalizedRow 0 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form1 = rawRow7377 := by decide +kernel

def row7377 : Integer.Sparse Key := [(key0, -24), (key83, 24)]

theorem rowCheck7377 : row7377 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7377 := by decide +kernel

theorem rowEval7377 (x : Key → ℝ) : Integer.Sparse.eval row7377 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7377, Integer.Sparse.eval_collectBalanced, rawRowCheck7377]

def rawRow7378 : Integer.Sparse Key := [(key83, -24), (key0, 6), (key83, 6), (key83, 6), (key83, 6)]

theorem rawRowCheck7378 : GramPolynomial.normalizedRow 0 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form1 = rawRow7378 := by decide +kernel

def row7378 : Integer.Sparse Key := [(key0, 6), (key83, -6)]

theorem rowCheck7378 : row7378 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7378 := by decide +kernel

theorem rowEval7378 (x : Key → ℝ) : Integer.Sparse.eval row7378 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7378, Integer.Sparse.eval_collectBalanced, rawRowCheck7378]

def rawRow7379 : Integer.Sparse Key := [(key83, -24), (key83, 6), (key0, 6), (key83, 6), (key83, 6)]

theorem rawRowCheck7379 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form1 = rawRow7379 := by decide +kernel

def row7379 : Integer.Sparse Key := [(key0, 6), (key83, -6)]

theorem rowCheck7379 : row7379 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7379 := by decide +kernel

theorem rowEval7379 (x : Key → ℝ) : Integer.Sparse.eval row7379 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7379, Integer.Sparse.eval_collectBalanced, rawRowCheck7379]

def rawRow7380 : Integer.Sparse Key := [(key83, -24), (key83, 6), (key83, 6), (key0, 6), (key83, 6)]

theorem rawRowCheck7380 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form1 = rawRow7380 := by decide +kernel

def row7380 : Integer.Sparse Key := [(key0, 6), (key83, -6)]

theorem rowCheck7380 : row7380 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7380 := by decide +kernel

theorem rowEval7380 (x : Key → ℝ) : Integer.Sparse.eval row7380 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7380, Integer.Sparse.eval_collectBalanced, rawRowCheck7380]

def rawRow7381 : Integer.Sparse Key := [(key83, -24), (key83, 6), (key83, 6), (key83, 6), (key0, 6)]

theorem rawRowCheck7381 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form1 = rawRow7381 := by decide +kernel

def row7381 : Integer.Sparse Key := [(key0, 6), (key83, -6)]

theorem rowCheck7381 : row7381 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7381 := by decide +kernel

theorem rowEval7381 (x : Key → ℝ) : Integer.Sparse.eval row7381 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck7381, Integer.Sparse.eval_collectBalanced, rawRowCheck7381]

def rawRow7382 : Integer.Sparse Key := [(key1090, 2), (key1090, 2), (key1098, 2), (key1090, 2), (key1090, 2), (key1169, 2), (key1090, 2), (key1098, 2), (key1090, 2), (key1169, 2), (key1098, 2), (key1169, 2), (key1180, -2), (key1183, -2), (key1183, -2), (key1180, -2), (key1183, -2), (key1180, -2), (key1220, -2), (key1183, -2), (key1220, -2), (key1183, -2), (key1183, -2), (key1220, -2)]

theorem rawRowCheck7382 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form0 = rawRow7382 := by decide +kernel

def row7382 : Integer.Sparse Key := [(key1090, 12), (key1098, 6), (key1169, 6), (key1180, -6), (key1183, -12), (key1220, -6)]

theorem rowCheck7382 : row7382 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7382 := by decide +kernel

theorem rowEval7382 (x : Key → ℝ) : Integer.Sparse.eval row7382 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7382, Integer.Sparse.eval_collectBalanced, rawRowCheck7382]

def rawRow7383 : Integer.Sparse Key := [(key1090, 2), (key1098, 2), (key1090, 2), (key1090, 2), (key1169, 2), (key1090, 2), (key1098, 2), (key1090, 2), (key1169, 2), (key1090, 2), (key1169, 2), (key1098, 2), (key1183, -2), (key1180, -2), (key1183, -2), (key1183, -2), (key1180, -2), (key1220, -2), (key1180, -2), (key1220, -2), (key1183, -2), (key1183, -2), (key1220, -2), (key1183, -2)]

theorem rawRowCheck7383 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form0 = rawRow7383 := by decide +kernel

def row7383 : Integer.Sparse Key := [(key1090, 12), (key1098, 6), (key1169, 6), (key1180, -6), (key1183, -12), (key1220, -6)]

theorem rowCheck7383 : row7383 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7383 := by decide +kernel

theorem rowEval7383 (x : Key → ℝ) : Integer.Sparse.eval row7383 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7383, Integer.Sparse.eval_collectBalanced, rawRowCheck7383]

def rawRow7384 : Integer.Sparse Key := [(key1098, 2), (key1090, 2), (key1090, 2), (key1169, 2), (key1090, 2), (key1090, 2), (key1169, 2), (key1169, 2), (key1098, 2), (key1098, 2), (key1090, 2), (key1090, 2), (key1183, -2), (key1183, -2), (key1180, -2), (key1220, -2), (key1220, -2), (key1183, -2), (key1183, -2), (key1180, -2), (key1180, -2), (key1220, -2), (key1183, -2), (key1183, -2)]

theorem rawRowCheck7384 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form0 = rawRow7384 := by decide +kernel

def row7384 : Integer.Sparse Key := [(key1090, 12), (key1098, 6), (key1169, 6), (key1180, -6), (key1183, -12), (key1220, -6)]

theorem rowCheck7384 : row7384 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7384 := by decide +kernel

theorem rowEval7384 (x : Key → ℝ) : Integer.Sparse.eval row7384 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7384, Integer.Sparse.eval_collectBalanced, rawRowCheck7384]

def rawRow7385 : Integer.Sparse Key := [(key1169, 2), (key1169, 2), (key1169, 2), (key1098, 2), (key1098, 2), (key1098, 2), (key1090, 2), (key1090, 2), (key1090, 2), (key1090, 2), (key1090, 2), (key1090, 2), (key1220, -2), (key1220, -2), (key1220, -2), (key1183, -2), (key1183, -2), (key1183, -2), (key1183, -2), (key1183, -2), (key1183, -2), (key1180, -2), (key1180, -2), (key1180, -2)]

theorem rawRowCheck7385 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form0 = rawRow7385 := by decide +kernel

def row7385 : Integer.Sparse Key := [(key1090, 12), (key1098, 6), (key1169, 6), (key1180, -6), (key1183, -12), (key1220, -6)]

theorem rowCheck7385 : row7385 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7385 := by decide +kernel

theorem rowEval7385 (x : Key → ℝ) : Integer.Sparse.eval row7385 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7385, Integer.Sparse.eval_collectBalanced, rawRowCheck7385]

def rawRow7386 : Integer.Sparse Key := [(key976, 2), (key976, 2), (key984, 2), (key1090, 2), (key1090, 2), (key1169, 2), (key1180, 2), (key1183, 2), (key1180, 2), (key1220, 2), (key1183, 2), (key1220, 2), (key976, -2), (key984, -2), (key984, -2), (key1090, -2), (key1098, -2), (key1090, -2), (key1169, -2), (key1098, -2), (key1169, -2), (key1183, -2), (key1183, -2), (key1220, -2)]

theorem rawRowCheck7386 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block3.form0 = rawRow7386 := by decide +kernel

def row7386 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1098, -4), (key1169, -2), (key1180, 4), (key1220, 2)]

theorem rowCheck7386 : row7386 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7386 := by decide +kernel

theorem rowEval7386 (x : Key → ℝ) : Integer.Sparse.eval row7386 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7386, Integer.Sparse.eval_collectBalanced, rawRowCheck7386]

def rawRow7387 : Integer.Sparse Key := [(key976, 2), (key984, 2), (key976, 2), (key1090, 2), (key1169, 2), (key1090, 2), (key1183, 2), (key1180, 2), (key1220, 2), (key1180, 2), (key1220, 2), (key1183, 2), (key984, -2), (key976, -2), (key984, -2), (key1098, -2), (key1090, -2), (key1169, -2), (key1090, -2), (key1169, -2), (key1098, -2), (key1183, -2), (key1220, -2), (key1183, -2)]

theorem rawRowCheck7387 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block3.form0 = rawRow7387 := by decide +kernel

def row7387 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1098, -4), (key1169, -2), (key1180, 4), (key1220, 2)]

theorem rowCheck7387 : row7387 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7387 := by decide +kernel

theorem rowEval7387 (x : Key → ℝ) : Integer.Sparse.eval row7387 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7387, Integer.Sparse.eval_collectBalanced, rawRowCheck7387]

def rawRow7388 : Integer.Sparse Key := [(key984, 2), (key976, 2), (key976, 2), (key1169, 2), (key1090, 2), (key1090, 2), (key1220, 2), (key1220, 2), (key1183, 2), (key1183, 2), (key1180, 2), (key1180, 2), (key984, -2), (key984, -2), (key976, -2), (key1169, -2), (key1169, -2), (key1098, -2), (key1098, -2), (key1090, -2), (key1090, -2), (key1220, -2), (key1183, -2), (key1183, -2)]

theorem rawRowCheck7388 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block3.form0 = rawRow7388 := by decide +kernel

def row7388 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1098, -4), (key1169, -2), (key1180, 4), (key1220, 2)]

theorem rowCheck7388 : row7388 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7388 := by decide +kernel

theorem rowEval7388 (x : Key → ℝ) : Integer.Sparse.eval row7388 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7388, Integer.Sparse.eval_collectBalanced, rawRowCheck7388]

def rawRow7389 : Integer.Sparse Key := [(key1090, 2), (key1180, 2), (key1183, 2), (key976, 2), (key1180, 2), (key1220, 2), (key976, 2), (key984, 2), (key1090, 2), (key1169, 2), (key1183, 2), (key1220, 2), (key1090, -2), (key1098, -2), (key1183, -2), (key976, -2), (key984, -2), (key1090, -2), (key1169, -2), (key1183, -2), (key1220, -2), (key984, -2), (key1098, -2), (key1169, -2)]

theorem rawRowCheck7389 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block3.form0 = rawRow7389 := by decide +kernel

def row7389 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1098, -4), (key1169, -2), (key1180, 4), (key1220, 2)]

theorem rowCheck7389 : row7389 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7389 := by decide +kernel

theorem rowEval7389 (x : Key → ℝ) : Integer.Sparse.eval row7389 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7389, Integer.Sparse.eval_collectBalanced, rawRowCheck7389]

def rawRow7390 : Integer.Sparse Key := [(key1090, 2), (key1183, 2), (key1180, 2), (key976, 2), (key1220, 2), (key1180, 2), (key984, 2), (key976, 2), (key1169, 2), (key1090, 2), (key1220, 2), (key1183, 2), (key1098, -2), (key1090, -2), (key1183, -2), (key984, -2), (key976, -2), (key1169, -2), (key1090, -2), (key1220, -2), (key1183, -2), (key984, -2), (key1169, -2), (key1098, -2)]

theorem rawRowCheck7390 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block3.form0 = rawRow7390 := by decide +kernel

def row7390 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1098, -4), (key1169, -2), (key1180, 4), (key1220, 2)]

theorem rowCheck7390 : row7390 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7390 := by decide +kernel

theorem rowEval7390 (x : Key → ℝ) : Integer.Sparse.eval row7390 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7390, Integer.Sparse.eval_collectBalanced, rawRowCheck7390]

def rawRow7391 : Integer.Sparse Key := [(key1180, 2), (key1090, 2), (key1183, 2), (key1180, 2), (key976, 2), (key1220, 2), (key1090, 2), (key1183, 2), (key976, 2), (key1220, 2), (key984, 2), (key1169, 2), (key1090, -2), (key1183, -2), (key1098, -2), (key1090, -2), (key1183, -2), (key976, -2), (key1220, -2), (key984, -2), (key1169, -2), (key1098, -2), (key984, -2), (key1169, -2)]

theorem rawRowCheck7391 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block3.form0 = rawRow7391 := by decide +kernel

def row7391 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1098, -4), (key1169, -2), (key1180, 4), (key1220, 2)]

theorem rowCheck7391 : row7391 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7391 := by decide +kernel

theorem rowEval7391 (x : Key → ℝ) : Integer.Sparse.eval row7391 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7391, Integer.Sparse.eval_collectBalanced, rawRowCheck7391]

def rawRow7392 : Integer.Sparse Key := [(key1180, 2), (key1183, 2), (key1090, 2), (key1180, 2), (key1220, 2), (key976, 2), (key1183, 2), (key1090, 2), (key1220, 2), (key976, 2), (key1169, 2), (key984, 2), (key1183, -2), (key1090, -2), (key1098, -2), (key1183, -2), (key1090, -2), (key1220, -2), (key976, -2), (key1169, -2), (key984, -2), (key1098, -2), (key1169, -2), (key984, -2)]

theorem rawRowCheck7392 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block3.form0 = rawRow7392 := by decide +kernel

def row7392 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1098, -4), (key1169, -2), (key1180, 4), (key1220, 2)]

theorem rowCheck7392 : row7392 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7392 := by decide +kernel

theorem rowEval7392 (x : Key → ℝ) : Integer.Sparse.eval row7392 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck7392, Integer.Sparse.eval_collectBalanced, rawRowCheck7392]

def rawRow7393 : Integer.Sparse Key := [(key1183, 2), (key1090, 2), (key1180, 2), (key1220, 2), (key976, 2), (key1180, 2), (key1169, 2), (key1220, 2), (key984, 2), (key1183, 2), (key976, 2), (key1090, 2), (key1098, -2), (key1183, -2), (key1090, -2), (key1169, -2), (key1220, -2), (key984, -2), (key1183, -2), (key976, -2), (key1090, -2), (key1169, -2), (key984, -2), (key1098, -2)]

theorem rawRowCheck7393 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block3.form0 = rawRow7393 := by decide +kernel

def row7393 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1098, -4), (key1169, -2), (key1180, 4), (key1220, 2)]

theorem rowCheck7393 : row7393 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7393 := by decide +kernel

theorem rowEval7393 (x : Key → ℝ) : Integer.Sparse.eval row7393 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7393, Integer.Sparse.eval_collectBalanced, rawRowCheck7393]

def rawRow7394 : Integer.Sparse Key := [(key1183, 2), (key1180, 2), (key1090, 2), (key1220, 2), (key1180, 2), (key976, 2), (key1220, 2), (key1169, 2), (key1183, 2), (key984, 2), (key1090, 2), (key976, 2), (key1183, -2), (key1098, -2), (key1090, -2), (key1220, -2), (key1169, -2), (key1183, -2), (key984, -2), (key1090, -2), (key976, -2), (key1169, -2), (key1098, -2), (key984, -2)]

theorem rawRowCheck7394 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block3.form0 = rawRow7394 := by decide +kernel

def row7394 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1098, -4), (key1169, -2), (key1180, 4), (key1220, 2)]

theorem rowCheck7394 : row7394 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7394 := by decide +kernel

theorem rowEval7394 (x : Key → ℝ) : Integer.Sparse.eval row7394 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck7394, Integer.Sparse.eval_collectBalanced, rawRowCheck7394]

def rawRow7395 : Integer.Sparse Key := [(key1169, 2), (key1220, 2), (key1220, 2), (key984, 2), (key1183, 2), (key1183, 2), (key976, 2), (key976, 2), (key1090, 2), (key1090, 2), (key1180, 2), (key1180, 2), (key1169, -2), (key1169, -2), (key1220, -2), (key984, -2), (key984, -2), (key1098, -2), (key1098, -2), (key1183, -2), (key1183, -2), (key976, -2), (key1090, -2), (key1090, -2)]

theorem rawRowCheck7395 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block3.form0 = rawRow7395 := by decide +kernel

def row7395 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1098, -4), (key1169, -2), (key1180, 4), (key1220, 2)]

theorem rowCheck7395 : row7395 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7395 := by decide +kernel

theorem rowEval7395 (x : Key → ℝ) : Integer.Sparse.eval row7395 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7395, Integer.Sparse.eval_collectBalanced, rawRowCheck7395]

def rawRow7396 : Integer.Sparse Key := [(key1220, 2), (key1169, 2), (key1220, 2), (key1183, 2), (key984, 2), (key1183, 2), (key1090, 2), (key1180, 2), (key976, 2), (key1180, 2), (key976, 2), (key1090, 2), (key1169, -2), (key1220, -2), (key1169, -2), (key1098, -2), (key1183, -2), (key984, -2), (key1183, -2), (key984, -2), (key1098, -2), (key1090, -2), (key976, -2), (key1090, -2)]

theorem rawRowCheck7396 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block3.form0 = rawRow7396 := by decide +kernel

def row7396 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1098, -4), (key1169, -2), (key1180, 4), (key1220, 2)]

theorem rowCheck7396 : row7396 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7396 := by decide +kernel

theorem rowEval7396 (x : Key → ℝ) : Integer.Sparse.eval row7396 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7396, Integer.Sparse.eval_collectBalanced, rawRowCheck7396]

def rawRow7397 : Integer.Sparse Key := [(key1220, 2), (key1220, 2), (key1169, 2), (key1183, 2), (key1183, 2), (key984, 2), (key1180, 2), (key1090, 2), (key1180, 2), (key976, 2), (key1090, 2), (key976, 2), (key1220, -2), (key1169, -2), (key1169, -2), (key1183, -2), (key1098, -2), (key1183, -2), (key984, -2), (key1098, -2), (key984, -2), (key1090, -2), (key1090, -2), (key976, -2)]

theorem rawRowCheck7397 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block3.form0 = rawRow7397 := by decide +kernel

def row7397 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1098, -4), (key1169, -2), (key1180, 4), (key1220, 2)]

theorem rowCheck7397 : row7397 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7397 := by decide +kernel

theorem rowEval7397 (x : Key → ℝ) : Integer.Sparse.eval row7397 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck7397, Integer.Sparse.eval_collectBalanced, rawRowCheck7397]

def rawRow7398 : Integer.Sparse Key := [(key3, -24), (key86, 6), (key86, 6), (key86, 6), (key147, 6)]

theorem rawRowCheck7398 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form1 = rawRow7398 := by decide +kernel

def row7398 : Integer.Sparse Key := [(key3, -24), (key86, 18), (key147, 6)]

theorem rowCheck7398 : row7398 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7398 := by decide +kernel

theorem rowEval7398 (x : Key → ℝ) : Integer.Sparse.eval row7398 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7398, Integer.Sparse.eval_collectBalanced, rawRowCheck7398]

def rawRow7399 : Integer.Sparse Key := [(key3, -24), (key86, 6), (key86, 6), (key147, 6), (key86, 6)]

theorem rawRowCheck7399 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form1 = rawRow7399 := by decide +kernel

def row7399 : Integer.Sparse Key := [(key3, -24), (key86, 18), (key147, 6)]

theorem rowCheck7399 : row7399 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7399 := by decide +kernel

theorem rowEval7399 (x : Key → ℝ) : Integer.Sparse.eval row7399 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7399, Integer.Sparse.eval_collectBalanced, rawRowCheck7399]

def rawRow7400 : Integer.Sparse Key := [(key3, -24), (key86, 6), (key147, 6), (key86, 6), (key86, 6)]

theorem rawRowCheck7400 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form1 = rawRow7400 := by decide +kernel

def row7400 : Integer.Sparse Key := [(key3, -24), (key86, 18), (key147, 6)]

theorem rowCheck7400 : row7400 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7400 := by decide +kernel

theorem rowEval7400 (x : Key → ℝ) : Integer.Sparse.eval row7400 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7400, Integer.Sparse.eval_collectBalanced, rawRowCheck7400]

def rawRow7401 : Integer.Sparse Key := [(key3, -24), (key147, 6), (key86, 6), (key86, 6), (key86, 6)]

theorem rawRowCheck7401 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form1 = rawRow7401 := by decide +kernel

def row7401 : Integer.Sparse Key := [(key3, -24), (key86, 18), (key147, 6)]

theorem rowCheck7401 : row7401 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7401 := by decide +kernel

theorem rowEval7401 (x : Key → ℝ) : Integer.Sparse.eval row7401 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7401, Integer.Sparse.eval_collectBalanced, rawRowCheck7401]

def rawRow7402 : Integer.Sparse Key := [(key86, -24), (key3, 6), (key86, 6), (key86, 6), (key147, 6)]

theorem rawRowCheck7402 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block3.form1 = rawRow7402 := by decide +kernel

def row7402 : Integer.Sparse Key := [(key3, 6), (key86, -12), (key147, 6)]

theorem rowCheck7402 : row7402 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7402 := by decide +kernel

theorem rowEval7402 (x : Key → ℝ) : Integer.Sparse.eval row7402 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7402, Integer.Sparse.eval_collectBalanced, rawRowCheck7402]

def rawRow7403 : Integer.Sparse Key := [(key86, -24), (key3, 6), (key86, 6), (key147, 6), (key86, 6)]

theorem rawRowCheck7403 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block3.form1 = rawRow7403 := by decide +kernel

def row7403 : Integer.Sparse Key := [(key3, 6), (key86, -12), (key147, 6)]

theorem rowCheck7403 : row7403 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7403 := by decide +kernel

theorem rowEval7403 (x : Key → ℝ) : Integer.Sparse.eval row7403 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7403, Integer.Sparse.eval_collectBalanced, rawRowCheck7403]

def rawRow7404 : Integer.Sparse Key := [(key86, -24), (key3, 6), (key147, 6), (key86, 6), (key86, 6)]

theorem rawRowCheck7404 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block3.form1 = rawRow7404 := by decide +kernel

def row7404 : Integer.Sparse Key := [(key3, 6), (key86, -12), (key147, 6)]

theorem rowCheck7404 : row7404 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7404 := by decide +kernel

theorem rowEval7404 (x : Key → ℝ) : Integer.Sparse.eval row7404 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7404, Integer.Sparse.eval_collectBalanced, rawRowCheck7404]

def rawRow7405 : Integer.Sparse Key := [(key86, -24), (key86, 6), (key3, 6), (key86, 6), (key147, 6)]

theorem rawRowCheck7405 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block3.form1 = rawRow7405 := by decide +kernel

def row7405 : Integer.Sparse Key := [(key3, 6), (key86, -12), (key147, 6)]

theorem rowCheck7405 : row7405 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7405 := by decide +kernel

theorem rowEval7405 (x : Key → ℝ) : Integer.Sparse.eval row7405 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7405, Integer.Sparse.eval_collectBalanced, rawRowCheck7405]

def rawRow7406 : Integer.Sparse Key := [(key86, -24), (key86, 6), (key3, 6), (key147, 6), (key86, 6)]

theorem rawRowCheck7406 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block3.form1 = rawRow7406 := by decide +kernel

def row7406 : Integer.Sparse Key := [(key3, 6), (key86, -12), (key147, 6)]

theorem rowCheck7406 : row7406 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7406 := by decide +kernel

theorem rowEval7406 (x : Key → ℝ) : Integer.Sparse.eval row7406 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7406, Integer.Sparse.eval_collectBalanced, rawRowCheck7406]

def rawRow7407 : Integer.Sparse Key := [(key86, -24), (key86, 6), (key86, 6), (key3, 6), (key147, 6)]

theorem rawRowCheck7407 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block3.form1 = rawRow7407 := by decide +kernel

def row7407 : Integer.Sparse Key := [(key3, 6), (key86, -12), (key147, 6)]

theorem rowCheck7407 : row7407 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7407 := by decide +kernel

theorem rowEval7407 (x : Key → ℝ) : Integer.Sparse.eval row7407 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7407, Integer.Sparse.eval_collectBalanced, rawRowCheck7407]

def rawRow7408 : Integer.Sparse Key := [(key86, -24), (key86, 6), (key86, 6), (key147, 6), (key3, 6)]

theorem rawRowCheck7408 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block3.form1 = rawRow7408 := by decide +kernel

def row7408 : Integer.Sparse Key := [(key3, 6), (key86, -12), (key147, 6)]

theorem rowCheck7408 : row7408 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7408 := by decide +kernel

theorem rowEval7408 (x : Key → ℝ) : Integer.Sparse.eval row7408 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck7408, Integer.Sparse.eval_collectBalanced, rawRowCheck7408]

def rawRow7409 : Integer.Sparse Key := [(key86, -24), (key86, 6), (key147, 6), (key3, 6), (key86, 6)]

theorem rawRowCheck7409 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block3.form1 = rawRow7409 := by decide +kernel

def row7409 : Integer.Sparse Key := [(key3, 6), (key86, -12), (key147, 6)]

theorem rowCheck7409 : row7409 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7409 := by decide +kernel

theorem rowEval7409 (x : Key → ℝ) : Integer.Sparse.eval row7409 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7409, Integer.Sparse.eval_collectBalanced, rawRowCheck7409]

def rawRow7410 : Integer.Sparse Key := [(key86, -24), (key86, 6), (key147, 6), (key86, 6), (key3, 6)]

theorem rawRowCheck7410 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block3.form1 = rawRow7410 := by decide +kernel

def row7410 : Integer.Sparse Key := [(key3, 6), (key86, -12), (key147, 6)]

theorem rowCheck7410 : row7410 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7410 := by decide +kernel

theorem rowEval7410 (x : Key → ℝ) : Integer.Sparse.eval row7410 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck7410, Integer.Sparse.eval_collectBalanced, rawRowCheck7410]

def rawRow7411 : Integer.Sparse Key := [(key86, -24), (key147, 6), (key3, 6), (key86, 6), (key86, 6)]

theorem rawRowCheck7411 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block3.form1 = rawRow7411 := by decide +kernel

def row7411 : Integer.Sparse Key := [(key3, 6), (key86, -12), (key147, 6)]

theorem rowCheck7411 : row7411 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7411 := by decide +kernel

theorem rowEval7411 (x : Key → ℝ) : Integer.Sparse.eval row7411 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7411, Integer.Sparse.eval_collectBalanced, rawRowCheck7411]

def rawRow7412 : Integer.Sparse Key := [(key86, -24), (key147, 6), (key86, 6), (key3, 6), (key86, 6)]

theorem rawRowCheck7412 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block3.form1 = rawRow7412 := by decide +kernel

def row7412 : Integer.Sparse Key := [(key3, 6), (key86, -12), (key147, 6)]

theorem rowCheck7412 : row7412 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7412 := by decide +kernel

theorem rowEval7412 (x : Key → ℝ) : Integer.Sparse.eval row7412 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7412, Integer.Sparse.eval_collectBalanced, rawRowCheck7412]

def rawRow7413 : Integer.Sparse Key := [(key86, -24), (key147, 6), (key86, 6), (key86, 6), (key3, 6)]

theorem rawRowCheck7413 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block3.form1 = rawRow7413 := by decide +kernel

def row7413 : Integer.Sparse Key := [(key3, 6), (key86, -12), (key147, 6)]

theorem rowCheck7413 : row7413 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7413 := by decide +kernel

theorem rowEval7413 (x : Key → ℝ) : Integer.Sparse.eval row7413 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck7413, Integer.Sparse.eval_collectBalanced, rawRowCheck7413]

def rawRow7414 : Integer.Sparse Key := [(key1, -6), (key7, -6), (key7, -6), (key7, -6), (key84, 2), (key90, 2), (key90, 2), (key84, 2), (key90, 2), (key84, 2), (key151, 2), (key90, 2), (key151, 2), (key90, 2), (key90, 2), (key151, 2)]

theorem rawRowCheck7414 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form2 = rawRow7414 := by decide +kernel

def row7414 : Integer.Sparse Key := [(key1, -6), (key7, -18), (key84, 6), (key90, 12), (key151, 6)]

theorem rowCheck7414 : row7414 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7414 := by decide +kernel

theorem rowEval7414 (x : Key → ℝ) : Integer.Sparse.eval row7414 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7414, Integer.Sparse.eval_collectBalanced, rawRowCheck7414]

def rawRow7415 : Integer.Sparse Key := [(key7, -6), (key1, -6), (key7, -6), (key7, -6), (key90, 2), (key84, 2), (key90, 2), (key90, 2), (key84, 2), (key151, 2), (key84, 2), (key151, 2), (key90, 2), (key90, 2), (key151, 2), (key90, 2)]

theorem rawRowCheck7415 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form2 = rawRow7415 := by decide +kernel

def row7415 : Integer.Sparse Key := [(key1, -6), (key7, -18), (key84, 6), (key90, 12), (key151, 6)]

theorem rowCheck7415 : row7415 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7415 := by decide +kernel

theorem rowEval7415 (x : Key → ℝ) : Integer.Sparse.eval row7415 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7415, Integer.Sparse.eval_collectBalanced, rawRowCheck7415]

def rawRow7416 : Integer.Sparse Key := [(key7, -6), (key7, -6), (key1, -6), (key7, -6), (key90, 2), (key90, 2), (key84, 2), (key151, 2), (key151, 2), (key90, 2), (key90, 2), (key84, 2), (key84, 2), (key151, 2), (key90, 2), (key90, 2)]

theorem rawRowCheck7416 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form2 = rawRow7416 := by decide +kernel

def row7416 : Integer.Sparse Key := [(key1, -6), (key7, -18), (key84, 6), (key90, 12), (key151, 6)]

theorem rowCheck7416 : row7416 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7416 := by decide +kernel

theorem rowEval7416 (x : Key → ℝ) : Integer.Sparse.eval row7416 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7416, Integer.Sparse.eval_collectBalanced, rawRowCheck7416]

def rawRow7417 : Integer.Sparse Key := [(key7, -6), (key7, -6), (key7, -6), (key1, -6), (key151, 2), (key151, 2), (key151, 2), (key90, 2), (key90, 2), (key90, 2), (key90, 2), (key90, 2), (key90, 2), (key84, 2), (key84, 2), (key84, 2)]

theorem rawRowCheck7417 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form2 = rawRow7417 := by decide +kernel

def row7417 : Integer.Sparse Key := [(key1, -6), (key7, -18), (key84, 6), (key90, 12), (key151, 6)]

theorem rowCheck7417 : row7417 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7417 := by decide +kernel

theorem rowEval7417 (x : Key → ℝ) : Integer.Sparse.eval row7417 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7417, Integer.Sparse.eval_collectBalanced, rawRowCheck7417]

def rawRow7418 : Integer.Sparse Key := [(key84, -6), (key90, -6), (key90, -6), (key151, -6), (key1, 2), (key7, 2), (key7, 2), (key84, 2), (key90, 2), (key84, 2), (key151, 2), (key90, 2), (key151, 2), (key193, 2), (key193, 2), (key202, 2)]

theorem rawRowCheck7418 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block3.form2 = rawRow7418 := by decide +kernel

def row7418 : Integer.Sparse Key := [(key1, 2), (key7, 4), (key84, -2), (key90, -8), (key151, -2), (key193, 4), (key202, 2)]

theorem rowCheck7418 : row7418 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7418 := by decide +kernel

theorem rowEval7418 (x : Key → ℝ) : Integer.Sparse.eval row7418 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7418, Integer.Sparse.eval_collectBalanced, rawRowCheck7418]

def rawRow7419 : Integer.Sparse Key := [(key90, -6), (key84, -6), (key90, -6), (key151, -6), (key7, 2), (key1, 2), (key7, 2), (key90, 2), (key84, 2), (key151, 2), (key84, 2), (key151, 2), (key90, 2), (key193, 2), (key202, 2), (key193, 2)]

theorem rawRowCheck7419 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block3.form2 = rawRow7419 := by decide +kernel

def row7419 : Integer.Sparse Key := [(key1, 2), (key7, 4), (key84, -2), (key90, -8), (key151, -2), (key193, 4), (key202, 2)]

theorem rowCheck7419 : row7419 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7419 := by decide +kernel

theorem rowEval7419 (x : Key → ℝ) : Integer.Sparse.eval row7419 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7419, Integer.Sparse.eval_collectBalanced, rawRowCheck7419]

def rawRow7420 : Integer.Sparse Key := [(key90, -6), (key90, -6), (key84, -6), (key151, -6), (key7, 2), (key7, 2), (key1, 2), (key151, 2), (key151, 2), (key90, 2), (key90, 2), (key84, 2), (key84, 2), (key202, 2), (key193, 2), (key193, 2)]

theorem rawRowCheck7420 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block3.form2 = rawRow7420 := by decide +kernel

def row7420 : Integer.Sparse Key := [(key1, 2), (key7, 4), (key84, -2), (key90, -8), (key151, -2), (key193, 4), (key202, 2)]

theorem rowCheck7420 : row7420 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7420 := by decide +kernel

theorem rowEval7420 (x : Key → ℝ) : Integer.Sparse.eval row7420 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7420, Integer.Sparse.eval_collectBalanced, rawRowCheck7420]

def rawRow7421 : Integer.Sparse Key := [(key84, -6), (key90, -6), (key151, -6), (key90, -6), (key84, 2), (key90, 2), (key151, 2), (key1, 2), (key7, 2), (key84, 2), (key151, 2), (key193, 2), (key202, 2), (key7, 2), (key90, 2), (key151, 2)]

theorem rawRowCheck7421 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block3.form2 = rawRow7421 := by decide +kernel

def row7421 : Integer.Sparse Key := [(key1, 2), (key7, 4), (key84, -2), (key90, -8), (key193, 2), (key202, 2)]

theorem rowCheck7421 : row7421 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7421 := by decide +kernel

theorem rowEval7421 (x : Key → ℝ) : Integer.Sparse.eval row7421 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7421, Integer.Sparse.eval_collectBalanced, rawRowCheck7421]

def rawRow7422 : Integer.Sparse Key := [(key90, -6), (key84, -6), (key151, -6), (key90, -6), (key90, 2), (key84, 2), (key151, 2), (key7, 2), (key1, 2), (key151, 2), (key84, 2), (key202, 2), (key193, 2), (key7, 2), (key151, 2), (key90, 2)]

theorem rawRowCheck7422 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block3.form2 = rawRow7422 := by decide +kernel

def row7422 : Integer.Sparse Key := [(key1, 2), (key7, 4), (key84, -2), (key90, -8), (key193, 2), (key202, 2)]

theorem rowCheck7422 : row7422 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7422 := by decide +kernel

theorem rowEval7422 (x : Key → ℝ) : Integer.Sparse.eval row7422 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7422, Integer.Sparse.eval_collectBalanced, rawRowCheck7422]

def rawRow7423 : Integer.Sparse Key := [(key84, -6), (key151, -6), (key90, -6), (key90, -6), (key84, 2), (key151, 2), (key90, 2), (key84, 2), (key151, 2), (key1, 2), (key202, 2), (key7, 2), (key151, 2), (key90, 2), (key7, 2), (key151, 2)]

theorem rawRowCheck7423 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block3.form2 = rawRow7423 := by decide +kernel

def row7423 : Integer.Sparse Key := [(key1, 2), (key7, 4), (key84, -2), (key90, -8), (key151, 2), (key202, 2)]

theorem rowCheck7423 : row7423 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7423 := by decide +kernel

theorem rowEval7423 (x : Key → ℝ) : Integer.Sparse.eval row7423 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7423, Integer.Sparse.eval_collectBalanced, rawRowCheck7423]

end MUB6.Certificate.GramRows

end OAI
