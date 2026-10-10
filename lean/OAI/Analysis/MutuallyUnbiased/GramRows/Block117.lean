import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
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

def rawRow11904 : Integer.Sparse Key := [(key2394, -2), (key2390, -2), (key2394, -2), (key2383, -2), (key2378, -2), (key2394, -2), (key2378, -2), (key2394, -2), (key2383, -2), (key2378, -2), (key2390, -2), (key2378, -2), (key2443, 2), (key2437, 2), (key2443, 2), (key2411, 2), (key2406, 2), (key2443, 2), (key2406, 2), (key2443, 2), (key2411, 2), (key2406, 2), (key2437, 2), (key2406, 2)]

theorem rawRowCheck11904 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form7 = rawRow11904 := by decide +kernel

def row11904 : Integer.Sparse Key := [(key2378, -8), (key2383, -4), (key2390, -4), (key2394, -8), (key2406, 8), (key2411, 4), (key2437, 4), (key2443, 8)]

theorem rowCheck11904 : row11904 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11904 := by decide +kernel

theorem rowEval11904 (x : Key → ℝ) : Integer.Sparse.eval row11904 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck11904, Integer.Sparse.eval_collectBalanced, rawRowCheck11904]

def rawRow11905 : Integer.Sparse Key := [(key2394, -2), (key2394, -2), (key2390, -2), (key2394, -2), (key2394, -2), (key2383, -2), (key2383, -2), (key2378, -2), (key2378, -2), (key2390, -2), (key2378, -2), (key2378, -2), (key2443, 2), (key2443, 2), (key2437, 2), (key2443, 2), (key2443, 2), (key2411, 2), (key2411, 2), (key2406, 2), (key2406, 2), (key2437, 2), (key2406, 2), (key2406, 2)]

theorem rawRowCheck11905 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form7 = rawRow11905 := by decide +kernel

def row11905 : Integer.Sparse Key := [(key2378, -8), (key2383, -4), (key2390, -4), (key2394, -8), (key2406, 8), (key2411, 4), (key2437, 4), (key2443, 8)]

theorem rowCheck11905 : row11905 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11905 := by decide +kernel

theorem rowEval11905 (x : Key → ℝ) : Integer.Sparse.eval row11905 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck11905, Integer.Sparse.eval_collectBalanced, rawRowCheck11905]

def rawRow11906 : Integer.Sparse Key := [(key2766, -2), (key2766, -2), (key2772, -2), (key2843, -2), (key2843, -2), (key2887, -2), (key2887, -2), (key2889, -2), (key2889, -2), (key2880, -2), (key2910, -2), (key2910, -2), (key2587, 2), (key2587, 2), (key2593, 2), (key2843, 2), (key2843, 2), (key2966, 2), (key2966, 2), (key2968, 2), (key2968, 2), (key2880, 2), (key2989, 2), (key2989, 2)]

theorem rawRowCheck11906 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form7 = rawRow11906 := by decide +kernel

def row11906 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4)]

theorem rowCheck11906 : row11906 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11906 := by decide +kernel

theorem rowEval11906 (x : Key → ℝ) : Integer.Sparse.eval row11906 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck11906, Integer.Sparse.eval_collectBalanced, rawRowCheck11906]

def rawRow11907 : Integer.Sparse Key := [(key2766, -2), (key2772, -2), (key2766, -2), (key2887, -2), (key2889, -2), (key2843, -2), (key2889, -2), (key2843, -2), (key2887, -2), (key2910, -2), (key2880, -2), (key2910, -2), (key2587, 2), (key2593, 2), (key2587, 2), (key2966, 2), (key2968, 2), (key2843, 2), (key2968, 2), (key2843, 2), (key2966, 2), (key2989, 2), (key2880, 2), (key2989, 2)]

theorem rawRowCheck11907 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form7 = rawRow11907 := by decide +kernel

def row11907 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4)]

theorem rowCheck11907 : row11907 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11907 := by decide +kernel

theorem rowEval11907 (x : Key → ℝ) : Integer.Sparse.eval row11907 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck11907, Integer.Sparse.eval_collectBalanced, rawRowCheck11907]

def rawRow11908 : Integer.Sparse Key := [(key2772, -2), (key2766, -2), (key2766, -2), (key2889, -2), (key2887, -2), (key2889, -2), (key2843, -2), (key2887, -2), (key2843, -2), (key2910, -2), (key2910, -2), (key2880, -2), (key2593, 2), (key2587, 2), (key2587, 2), (key2968, 2), (key2966, 2), (key2968, 2), (key2843, 2), (key2966, 2), (key2843, 2), (key2989, 2), (key2989, 2), (key2880, 2)]

theorem rawRowCheck11908 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form7 = rawRow11908 := by decide +kernel

def row11908 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4)]

theorem rowCheck11908 : row11908 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11908 := by decide +kernel

theorem rowEval11908 (x : Key → ℝ) : Integer.Sparse.eval row11908 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck11908, Integer.Sparse.eval_collectBalanced, rawRowCheck11908]

def rawRow11909 : Integer.Sparse Key := [(key2843, -2), (key2843, -2), (key2880, -2), (key2766, -2), (key2766, -2), (key2887, -2), (key2887, -2), (key2910, -2), (key2910, -2), (key2772, -2), (key2889, -2), (key2889, -2), (key2843, 2), (key2843, 2), (key2880, 2), (key2587, 2), (key2587, 2), (key2966, 2), (key2966, 2), (key2989, 2), (key2989, 2), (key2593, 2), (key2968, 2), (key2968, 2)]

theorem rawRowCheck11909 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form7 = rawRow11909 := by decide +kernel

def row11909 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4)]

theorem rowCheck11909 : row11909 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11909 := by decide +kernel

theorem rowEval11909 (x : Key → ℝ) : Integer.Sparse.eval row11909 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck11909, Integer.Sparse.eval_collectBalanced, rawRowCheck11909]

def rawRow11910 : Integer.Sparse Key := [(key2843, -2), (key2880, -2), (key2843, -2), (key2887, -2), (key2910, -2), (key2766, -2), (key2910, -2), (key2766, -2), (key2887, -2), (key2889, -2), (key2772, -2), (key2889, -2), (key2843, 2), (key2880, 2), (key2843, 2), (key2966, 2), (key2989, 2), (key2587, 2), (key2989, 2), (key2587, 2), (key2966, 2), (key2968, 2), (key2593, 2), (key2968, 2)]

theorem rawRowCheck11910 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form7 = rawRow11910 := by decide +kernel

def row11910 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4)]

theorem rowCheck11910 : row11910 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11910 := by decide +kernel

theorem rowEval11910 (x : Key → ℝ) : Integer.Sparse.eval row11910 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck11910, Integer.Sparse.eval_collectBalanced, rawRowCheck11910]

def rawRow11911 : Integer.Sparse Key := [(key2880, -2), (key2843, -2), (key2843, -2), (key2910, -2), (key2887, -2), (key2910, -2), (key2766, -2), (key2887, -2), (key2766, -2), (key2889, -2), (key2889, -2), (key2772, -2), (key2880, 2), (key2843, 2), (key2843, 2), (key2989, 2), (key2966, 2), (key2989, 2), (key2587, 2), (key2966, 2), (key2587, 2), (key2968, 2), (key2968, 2), (key2593, 2)]

theorem rawRowCheck11911 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form7 = rawRow11911 := by decide +kernel

def row11911 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4)]

theorem rowCheck11911 : row11911 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11911 := by decide +kernel

theorem rowEval11911 (x : Key → ℝ) : Integer.Sparse.eval row11911 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form7) x := by
  rw [rowCheck11911, Integer.Sparse.eval_collectBalanced, rawRowCheck11911]

def rawRow11912 : Integer.Sparse Key := [(key2887, -2), (key2889, -2), (key2910, -2), (key2766, -2), (key2772, -2), (key2843, -2), (key2889, -2), (key2880, -2), (key2910, -2), (key2766, -2), (key2843, -2), (key2887, -2), (key2966, 2), (key2968, 2), (key2989, 2), (key2587, 2), (key2593, 2), (key2843, 2), (key2968, 2), (key2880, 2), (key2989, 2), (key2587, 2), (key2843, 2), (key2966, 2)]

theorem rawRowCheck11912 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form7 = rawRow11912 := by decide +kernel

def row11912 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4)]

theorem rowCheck11912 : row11912 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11912 := by decide +kernel

theorem rowEval11912 (x : Key → ℝ) : Integer.Sparse.eval row11912 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck11912, Integer.Sparse.eval_collectBalanced, rawRowCheck11912]

def rawRow11913 : Integer.Sparse Key := [(key2889, -2), (key2887, -2), (key2910, -2), (key2772, -2), (key2766, -2), (key2889, -2), (key2843, -2), (key2910, -2), (key2880, -2), (key2766, -2), (key2887, -2), (key2843, -2), (key2968, 2), (key2966, 2), (key2989, 2), (key2593, 2), (key2587, 2), (key2968, 2), (key2843, 2), (key2989, 2), (key2880, 2), (key2587, 2), (key2966, 2), (key2843, 2)]

theorem rawRowCheck11913 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form7 = rawRow11913 := by decide +kernel

def row11913 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4)]

theorem rowCheck11913 : row11913 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11913 := by decide +kernel

theorem rowEval11913 (x : Key → ℝ) : Integer.Sparse.eval row11913 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck11913, Integer.Sparse.eval_collectBalanced, rawRowCheck11913]

def rawRow11914 : Integer.Sparse Key := [(key2887, -2), (key2910, -2), (key2889, -2), (key2843, -2), (key2880, -2), (key2766, -2), (key2910, -2), (key2772, -2), (key2889, -2), (key2843, -2), (key2766, -2), (key2887, -2), (key2966, 2), (key2989, 2), (key2968, 2), (key2843, 2), (key2880, 2), (key2587, 2), (key2989, 2), (key2593, 2), (key2968, 2), (key2843, 2), (key2587, 2), (key2966, 2)]

theorem rawRowCheck11914 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form7 = rawRow11914 := by decide +kernel

def row11914 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4)]

theorem rowCheck11914 : row11914 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11914 := by decide +kernel

theorem rowEval11914 (x : Key → ℝ) : Integer.Sparse.eval row11914 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck11914, Integer.Sparse.eval_collectBalanced, rawRowCheck11914]

def rawRow11915 : Integer.Sparse Key := [(key2910, -2), (key2887, -2), (key2889, -2), (key2880, -2), (key2843, -2), (key2910, -2), (key2766, -2), (key2889, -2), (key2772, -2), (key2843, -2), (key2887, -2), (key2766, -2), (key2989, 2), (key2966, 2), (key2968, 2), (key2880, 2), (key2843, 2), (key2989, 2), (key2587, 2), (key2968, 2), (key2593, 2), (key2843, 2), (key2966, 2), (key2587, 2)]

theorem rawRowCheck11915 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form7 = rawRow11915 := by decide +kernel

def row11915 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4)]

theorem rowCheck11915 : row11915 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11915 := by decide +kernel

theorem rowEval11915 (x : Key → ℝ) : Integer.Sparse.eval row11915 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form7) x := by
  rw [rowCheck11915, Integer.Sparse.eval_collectBalanced, rawRowCheck11915]

def rawRow11916 : Integer.Sparse Key := [(key2889, -2), (key2910, -2), (key2887, -2), (key2889, -2), (key2910, -2), (key2772, -2), (key2880, -2), (key2766, -2), (key2843, -2), (key2887, -2), (key2766, -2), (key2843, -2), (key2968, 2), (key2989, 2), (key2966, 2), (key2968, 2), (key2989, 2), (key2593, 2), (key2880, 2), (key2587, 2), (key2843, 2), (key2966, 2), (key2587, 2), (key2843, 2)]

theorem rawRowCheck11916 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form7 = rawRow11916 := by decide +kernel

def row11916 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4)]

theorem rowCheck11916 : row11916 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11916 := by decide +kernel

theorem rowEval11916 (x : Key → ℝ) : Integer.Sparse.eval row11916 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck11916, Integer.Sparse.eval_collectBalanced, rawRowCheck11916]

def rawRow11917 : Integer.Sparse Key := [(key2910, -2), (key2889, -2), (key2887, -2), (key2910, -2), (key2889, -2), (key2880, -2), (key2772, -2), (key2843, -2), (key2766, -2), (key2887, -2), (key2843, -2), (key2766, -2), (key2989, 2), (key2968, 2), (key2966, 2), (key2989, 2), (key2968, 2), (key2880, 2), (key2593, 2), (key2843, 2), (key2587, 2), (key2966, 2), (key2843, 2), (key2587, 2)]

theorem rawRowCheck11917 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form7 = rawRow11917 := by decide +kernel

def row11917 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4)]

theorem rowCheck11917 : row11917 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11917 := by decide +kernel

theorem rowEval11917 (x : Key → ℝ) : Integer.Sparse.eval row11917 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form7) x := by
  rw [rowCheck11917, Integer.Sparse.eval_collectBalanced, rawRowCheck11917]

def rawRow11918 : Integer.Sparse Key := [(key1531, -2), (key1531, -2), (key1536, -2), (key1531, -2), (key1531, -2), (key1765, -2), (key1765, -2), (key1768, -2), (key1768, -2), (key1536, -2), (key1768, -2), (key1768, -2), (key1609, 1), (key1609, 1), (key1648, 1), (key1648, 1), (key1651, 1), (key1651, 1), (key1609, 1), (key1609, 1), (key1806, 1), (key1806, 1), (key1809, 1), (key1809, 1), (key1648, 1), (key1648, 1), (key1806, 1), (key1806, 1), (key1837, 1), (key1837, 1), (key1651, 1), (key1651, 1), (key1809, 1), (key1809, 1), (key1837, 1), (key1837, 1)]

theorem rawRowCheck11918 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form8 = rawRow11918 := by decide +kernel

def row11918 : Integer.Sparse Key := [(key1531, -8), (key1536, -4), (key1609, 4), (key1648, 4), (key1651, 4), (key1765, -4), (key1768, -8), (key1806, 4), (key1809, 4), (key1837, 4)]

theorem rowCheck11918 : row11918 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11918 := by decide +kernel

theorem rowEval11918 (x : Key → ℝ) : Integer.Sparse.eval row11918 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck11918, Integer.Sparse.eval_collectBalanced, rawRowCheck11918]

def rawRow11919 : Integer.Sparse Key := [(key1531, -2), (key1536, -2), (key1531, -2), (key1765, -2), (key1768, -2), (key1531, -2), (key1768, -2), (key1531, -2), (key1765, -2), (key1768, -2), (key1536, -2), (key1768, -2), (key1648, 1), (key1651, 1), (key1609, 1), (key1651, 1), (key1609, 1), (key1648, 1), (key1806, 1), (key1809, 1), (key1609, 1), (key1809, 1), (key1609, 1), (key1806, 1), (key1806, 1), (key1837, 1), (key1648, 1), (key1837, 1), (key1648, 1), (key1806, 1), (key1809, 1), (key1837, 1), (key1651, 1), (key1837, 1), (key1651, 1), (key1809, 1)]

theorem rawRowCheck11919 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form8 = rawRow11919 := by decide +kernel

def row11919 : Integer.Sparse Key := [(key1531, -8), (key1536, -4), (key1609, 4), (key1648, 4), (key1651, 4), (key1765, -4), (key1768, -8), (key1806, 4), (key1809, 4), (key1837, 4)]

theorem rowCheck11919 : row11919 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11919 := by decide +kernel

theorem rowEval11919 (x : Key → ℝ) : Integer.Sparse.eval row11919 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck11919, Integer.Sparse.eval_collectBalanced, rawRowCheck11919]

def rawRow11920 : Integer.Sparse Key := [(key1536, -2), (key1531, -2), (key1531, -2), (key1768, -2), (key1765, -2), (key1768, -2), (key1531, -2), (key1765, -2), (key1531, -2), (key1768, -2), (key1768, -2), (key1536, -2), (key1651, 1), (key1648, 1), (key1651, 1), (key1609, 1), (key1648, 1), (key1609, 1), (key1809, 1), (key1806, 1), (key1809, 1), (key1609, 1), (key1806, 1), (key1609, 1), (key1837, 1), (key1806, 1), (key1837, 1), (key1648, 1), (key1806, 1), (key1648, 1), (key1837, 1), (key1809, 1), (key1837, 1), (key1651, 1), (key1809, 1), (key1651, 1)]

theorem rawRowCheck11920 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form8 = rawRow11920 := by decide +kernel

def row11920 : Integer.Sparse Key := [(key1531, -8), (key1536, -4), (key1609, 4), (key1648, 4), (key1651, 4), (key1765, -4), (key1768, -8), (key1806, 4), (key1809, 4), (key1837, 4)]

theorem rowCheck11920 : row11920 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11920 := by decide +kernel

theorem rowEval11920 (x : Key → ℝ) : Integer.Sparse.eval row11920 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck11920, Integer.Sparse.eval_collectBalanced, rawRowCheck11920]

def rawRow11921 : Integer.Sparse Key := [(key1765, -2), (key1768, -2), (key1768, -2), (key1531, -2), (key1536, -2), (key1531, -2), (key1768, -2), (key1536, -2), (key1768, -2), (key1531, -2), (key1531, -2), (key1765, -2), (key1806, 1), (key1809, 1), (key1806, 1), (key1837, 1), (key1809, 1), (key1837, 1), (key1648, 1), (key1651, 1), (key1648, 1), (key1837, 1), (key1651, 1), (key1837, 1), (key1609, 1), (key1651, 1), (key1609, 1), (key1809, 1), (key1651, 1), (key1809, 1), (key1609, 1), (key1648, 1), (key1609, 1), (key1806, 1), (key1648, 1), (key1806, 1)]

theorem rawRowCheck11921 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form8 = rawRow11921 := by decide +kernel

def row11921 : Integer.Sparse Key := [(key1531, -8), (key1536, -4), (key1609, 4), (key1648, 4), (key1651, 4), (key1765, -4), (key1768, -8), (key1806, 4), (key1809, 4), (key1837, 4)]

theorem rowCheck11921 : row11921 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11921 := by decide +kernel

theorem rowEval11921 (x : Key → ℝ) : Integer.Sparse.eval row11921 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck11921, Integer.Sparse.eval_collectBalanced, rawRowCheck11921]

def rawRow11922 : Integer.Sparse Key := [(key1768, -2), (key1765, -2), (key1768, -2), (key1536, -2), (key1531, -2), (key1768, -2), (key1531, -2), (key1768, -2), (key1536, -2), (key1531, -2), (key1765, -2), (key1531, -2), (key1809, 1), (key1806, 1), (key1837, 1), (key1806, 1), (key1837, 1), (key1809, 1), (key1651, 1), (key1648, 1), (key1837, 1), (key1648, 1), (key1837, 1), (key1651, 1), (key1651, 1), (key1609, 1), (key1809, 1), (key1609, 1), (key1809, 1), (key1651, 1), (key1648, 1), (key1609, 1), (key1806, 1), (key1609, 1), (key1806, 1), (key1648, 1)]

theorem rawRowCheck11922 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form8 = rawRow11922 := by decide +kernel

def row11922 : Integer.Sparse Key := [(key1531, -8), (key1536, -4), (key1609, 4), (key1648, 4), (key1651, 4), (key1765, -4), (key1768, -8), (key1806, 4), (key1809, 4), (key1837, 4)]

theorem rowCheck11922 : row11922 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11922 := by decide +kernel

theorem rowEval11922 (x : Key → ℝ) : Integer.Sparse.eval row11922 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck11922, Integer.Sparse.eval_collectBalanced, rawRowCheck11922]

def rawRow11923 : Integer.Sparse Key := [(key1768, -2), (key1768, -2), (key1765, -2), (key1768, -2), (key1768, -2), (key1536, -2), (key1536, -2), (key1531, -2), (key1531, -2), (key1765, -2), (key1531, -2), (key1531, -2), (key1837, 1), (key1837, 1), (key1809, 1), (key1809, 1), (key1806, 1), (key1806, 1), (key1837, 1), (key1837, 1), (key1651, 1), (key1651, 1), (key1648, 1), (key1648, 1), (key1809, 1), (key1809, 1), (key1651, 1), (key1651, 1), (key1609, 1), (key1609, 1), (key1806, 1), (key1806, 1), (key1648, 1), (key1648, 1), (key1609, 1), (key1609, 1)]

theorem rawRowCheck11923 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form8 = rawRow11923 := by decide +kernel

def row11923 : Integer.Sparse Key := [(key1531, -8), (key1536, -4), (key1609, 4), (key1648, 4), (key1651, 4), (key1765, -4), (key1768, -8), (key1806, 4), (key1809, 4), (key1837, 4)]

theorem rowCheck11923 : row11923 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11923 := by decide +kernel

theorem rowEval11923 (x : Key → ℝ) : Integer.Sparse.eval row11923 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck11923, Integer.Sparse.eval_collectBalanced, rawRowCheck11923]

def rawRow11924 : Integer.Sparse Key := [(key1256, -2), (key1256, -2), (key1261, -2), (key1609, -2), (key1609, -2), (key1806, -2), (key1806, -2), (key1809, -2), (key1809, -2), (key1642, -2), (key1832, -2), (key1832, -2), (key1256, 1), (key1256, 1), (key1265, 1), (key1265, 1), (key1268, 1), (key1268, 1), (key1531, 1), (key1531, 1), (key1765, 1), (key1765, 1), (key1768, 1), (key1768, 1), (key1648, 1), (key1648, 1), (key1806, 1), (key1806, 1), (key1837, 1), (key1837, 1), (key1674, 1), (key1674, 1), (key1832, 1), (key1832, 1), (key1848, 1), (key1848, 1)]

theorem rawRowCheck11924 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form8 = rawRow11924 := by decide +kernel

def row11924 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1609, -4), (key1642, -2), (key1648, 2), (key1674, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -4), (key1832, -2), (key1837, 2), (key1848, 2)]

theorem rowCheck11924 : row11924 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11924 := by decide +kernel

theorem rowEval11924 (x : Key → ℝ) : Integer.Sparse.eval row11924 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck11924, Integer.Sparse.eval_collectBalanced, rawRowCheck11924]

def rawRow11925 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1256, -2), (key1806, -2), (key1809, -2), (key1609, -2), (key1809, -2), (key1609, -2), (key1806, -2), (key1832, -2), (key1642, -2), (key1832, -2), (key1265, 1), (key1268, 1), (key1256, 1), (key1268, 1), (key1256, 1), (key1265, 1), (key1765, 1), (key1768, 1), (key1531, 1), (key1768, 1), (key1531, 1), (key1765, 1), (key1806, 1), (key1837, 1), (key1648, 1), (key1837, 1), (key1648, 1), (key1806, 1), (key1832, 1), (key1848, 1), (key1674, 1), (key1848, 1), (key1674, 1), (key1832, 1)]

theorem rawRowCheck11925 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form8 = rawRow11925 := by decide +kernel

def row11925 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1609, -4), (key1642, -2), (key1648, 2), (key1674, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -4), (key1832, -2), (key1837, 2), (key1848, 2)]

theorem rowCheck11925 : row11925 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11925 := by decide +kernel

theorem rowEval11925 (x : Key → ℝ) : Integer.Sparse.eval row11925 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck11925, Integer.Sparse.eval_collectBalanced, rawRowCheck11925]

def rawRow11926 : Integer.Sparse Key := [(key1261, -2), (key1256, -2), (key1256, -2), (key1809, -2), (key1806, -2), (key1809, -2), (key1609, -2), (key1806, -2), (key1609, -2), (key1832, -2), (key1832, -2), (key1642, -2), (key1268, 1), (key1265, 1), (key1268, 1), (key1256, 1), (key1265, 1), (key1256, 1), (key1768, 1), (key1765, 1), (key1768, 1), (key1531, 1), (key1765, 1), (key1531, 1), (key1837, 1), (key1806, 1), (key1837, 1), (key1648, 1), (key1806, 1), (key1648, 1), (key1848, 1), (key1832, 1), (key1848, 1), (key1674, 1), (key1832, 1), (key1674, 1)]

theorem rawRowCheck11926 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form8 = rawRow11926 := by decide +kernel

def row11926 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1609, -4), (key1642, -2), (key1648, 2), (key1674, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -4), (key1832, -2), (key1837, 2), (key1848, 2)]

theorem rowCheck11926 : row11926 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11926 := by decide +kernel

theorem rowEval11926 (x : Key → ℝ) : Integer.Sparse.eval row11926 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck11926, Integer.Sparse.eval_collectBalanced, rawRowCheck11926]

def rawRow11927 : Integer.Sparse Key := [(key1609, -2), (key1609, -2), (key1642, -2), (key1256, -2), (key1256, -2), (key1806, -2), (key1806, -2), (key1832, -2), (key1832, -2), (key1261, -2), (key1809, -2), (key1809, -2), (key1531, 1), (key1531, 1), (key1648, 1), (key1648, 1), (key1674, 1), (key1674, 1), (key1256, 1), (key1256, 1), (key1806, 1), (key1806, 1), (key1832, 1), (key1832, 1), (key1265, 1), (key1265, 1), (key1765, 1), (key1765, 1), (key1848, 1), (key1848, 1), (key1268, 1), (key1268, 1), (key1768, 1), (key1768, 1), (key1837, 1), (key1837, 1)]

theorem rawRowCheck11927 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form8 = rawRow11927 := by decide +kernel

def row11927 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1609, -4), (key1642, -2), (key1648, 2), (key1674, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -4), (key1832, -2), (key1837, 2), (key1848, 2)]

theorem rowCheck11927 : row11927 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11927 := by decide +kernel

theorem rowEval11927 (x : Key → ℝ) : Integer.Sparse.eval row11927 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck11927, Integer.Sparse.eval_collectBalanced, rawRowCheck11927]

def rawRow11928 : Integer.Sparse Key := [(key1609, -2), (key1642, -2), (key1609, -2), (key1806, -2), (key1832, -2), (key1256, -2), (key1832, -2), (key1256, -2), (key1806, -2), (key1809, -2), (key1261, -2), (key1809, -2), (key1648, 1), (key1674, 1), (key1531, 1), (key1674, 1), (key1531, 1), (key1648, 1), (key1806, 1), (key1832, 1), (key1256, 1), (key1832, 1), (key1256, 1), (key1806, 1), (key1765, 1), (key1848, 1), (key1265, 1), (key1848, 1), (key1265, 1), (key1765, 1), (key1768, 1), (key1837, 1), (key1268, 1), (key1837, 1), (key1268, 1), (key1768, 1)]

theorem rawRowCheck11928 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form8 = rawRow11928 := by decide +kernel

def row11928 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1609, -4), (key1642, -2), (key1648, 2), (key1674, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -4), (key1832, -2), (key1837, 2), (key1848, 2)]

theorem rowCheck11928 : row11928 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11928 := by decide +kernel

theorem rowEval11928 (x : Key → ℝ) : Integer.Sparse.eval row11928 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck11928, Integer.Sparse.eval_collectBalanced, rawRowCheck11928]

def rawRow11929 : Integer.Sparse Key := [(key1642, -2), (key1609, -2), (key1609, -2), (key1832, -2), (key1806, -2), (key1832, -2), (key1256, -2), (key1806, -2), (key1256, -2), (key1809, -2), (key1809, -2), (key1261, -2), (key1674, 1), (key1648, 1), (key1674, 1), (key1531, 1), (key1648, 1), (key1531, 1), (key1832, 1), (key1806, 1), (key1832, 1), (key1256, 1), (key1806, 1), (key1256, 1), (key1848, 1), (key1765, 1), (key1848, 1), (key1265, 1), (key1765, 1), (key1265, 1), (key1837, 1), (key1768, 1), (key1837, 1), (key1268, 1), (key1768, 1), (key1268, 1)]

theorem rawRowCheck11929 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form8 = rawRow11929 := by decide +kernel

def row11929 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1609, -4), (key1642, -2), (key1648, 2), (key1674, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -4), (key1832, -2), (key1837, 2), (key1848, 2)]

theorem rowCheck11929 : row11929 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11929 := by decide +kernel

theorem rowEval11929 (x : Key → ℝ) : Integer.Sparse.eval row11929 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form8) x := by
  rw [rowCheck11929, Integer.Sparse.eval_collectBalanced, rawRowCheck11929]

def rawRow11930 : Integer.Sparse Key := [(key1806, -2), (key1809, -2), (key1832, -2), (key1256, -2), (key1261, -2), (key1609, -2), (key1809, -2), (key1642, -2), (key1832, -2), (key1256, -2), (key1609, -2), (key1806, -2), (key1765, 1), (key1768, 1), (key1806, 1), (key1837, 1), (key1832, 1), (key1848, 1), (key1265, 1), (key1268, 1), (key1648, 1), (key1837, 1), (key1674, 1), (key1848, 1), (key1256, 1), (key1268, 1), (key1531, 1), (key1768, 1), (key1674, 1), (key1832, 1), (key1256, 1), (key1265, 1), (key1531, 1), (key1765, 1), (key1648, 1), (key1806, 1)]

theorem rawRowCheck11930 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form8 = rawRow11930 := by decide +kernel

def row11930 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1609, -4), (key1642, -2), (key1648, 2), (key1674, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -4), (key1832, -2), (key1837, 2), (key1848, 2)]

theorem rowCheck11930 : row11930 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11930 := by decide +kernel

theorem rowEval11930 (x : Key → ℝ) : Integer.Sparse.eval row11930 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck11930, Integer.Sparse.eval_collectBalanced, rawRowCheck11930]

def rawRow11931 : Integer.Sparse Key := [(key1809, -2), (key1806, -2), (key1832, -2), (key1261, -2), (key1256, -2), (key1809, -2), (key1609, -2), (key1832, -2), (key1642, -2), (key1256, -2), (key1806, -2), (key1609, -2), (key1768, 1), (key1765, 1), (key1837, 1), (key1806, 1), (key1848, 1), (key1832, 1), (key1268, 1), (key1265, 1), (key1837, 1), (key1648, 1), (key1848, 1), (key1674, 1), (key1268, 1), (key1256, 1), (key1768, 1), (key1531, 1), (key1832, 1), (key1674, 1), (key1265, 1), (key1256, 1), (key1765, 1), (key1531, 1), (key1806, 1), (key1648, 1)]

theorem rawRowCheck11931 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form8 = rawRow11931 := by decide +kernel

def row11931 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1609, -4), (key1642, -2), (key1648, 2), (key1674, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -4), (key1832, -2), (key1837, 2), (key1848, 2)]

theorem rowCheck11931 : row11931 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11931 := by decide +kernel

theorem rowEval11931 (x : Key → ℝ) : Integer.Sparse.eval row11931 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck11931, Integer.Sparse.eval_collectBalanced, rawRowCheck11931]

def rawRow11932 : Integer.Sparse Key := [(key1806, -2), (key1832, -2), (key1809, -2), (key1609, -2), (key1642, -2), (key1256, -2), (key1832, -2), (key1261, -2), (key1809, -2), (key1609, -2), (key1256, -2), (key1806, -2), (key1806, 1), (key1832, 1), (key1765, 1), (key1848, 1), (key1768, 1), (key1837, 1), (key1648, 1), (key1674, 1), (key1265, 1), (key1848, 1), (key1268, 1), (key1837, 1), (key1531, 1), (key1674, 1), (key1256, 1), (key1832, 1), (key1268, 1), (key1768, 1), (key1531, 1), (key1648, 1), (key1256, 1), (key1806, 1), (key1265, 1), (key1765, 1)]

theorem rawRowCheck11932 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form8 = rawRow11932 := by decide +kernel

def row11932 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1609, -4), (key1642, -2), (key1648, 2), (key1674, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -4), (key1832, -2), (key1837, 2), (key1848, 2)]

theorem rowCheck11932 : row11932 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11932 := by decide +kernel

theorem rowEval11932 (x : Key → ℝ) : Integer.Sparse.eval row11932 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck11932, Integer.Sparse.eval_collectBalanced, rawRowCheck11932]

def rawRow11933 : Integer.Sparse Key := [(key1832, -2), (key1806, -2), (key1809, -2), (key1642, -2), (key1609, -2), (key1832, -2), (key1256, -2), (key1809, -2), (key1261, -2), (key1609, -2), (key1806, -2), (key1256, -2), (key1832, 1), (key1806, 1), (key1848, 1), (key1765, 1), (key1837, 1), (key1768, 1), (key1674, 1), (key1648, 1), (key1848, 1), (key1265, 1), (key1837, 1), (key1268, 1), (key1674, 1), (key1531, 1), (key1832, 1), (key1256, 1), (key1768, 1), (key1268, 1), (key1648, 1), (key1531, 1), (key1806, 1), (key1256, 1), (key1765, 1), (key1265, 1)]

theorem rawRowCheck11933 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form8 = rawRow11933 := by decide +kernel

def row11933 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1609, -4), (key1642, -2), (key1648, 2), (key1674, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -4), (key1832, -2), (key1837, 2), (key1848, 2)]

theorem rowCheck11933 : row11933 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11933 := by decide +kernel

theorem rowEval11933 (x : Key → ℝ) : Integer.Sparse.eval row11933 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form8) x := by
  rw [rowCheck11933, Integer.Sparse.eval_collectBalanced, rawRowCheck11933]

def rawRow11934 : Integer.Sparse Key := [(key1809, -2), (key1832, -2), (key1806, -2), (key1809, -2), (key1832, -2), (key1261, -2), (key1642, -2), (key1256, -2), (key1609, -2), (key1806, -2), (key1256, -2), (key1609, -2), (key1837, 1), (key1848, 1), (key1768, 1), (key1832, 1), (key1765, 1), (key1806, 1), (key1837, 1), (key1848, 1), (key1268, 1), (key1674, 1), (key1265, 1), (key1648, 1), (key1768, 1), (key1832, 1), (key1268, 1), (key1674, 1), (key1256, 1), (key1531, 1), (key1765, 1), (key1806, 1), (key1265, 1), (key1648, 1), (key1256, 1), (key1531, 1)]

theorem rawRowCheck11934 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form8 = rawRow11934 := by decide +kernel

def row11934 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1609, -4), (key1642, -2), (key1648, 2), (key1674, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -4), (key1832, -2), (key1837, 2), (key1848, 2)]

theorem rowCheck11934 : row11934 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11934 := by decide +kernel

theorem rowEval11934 (x : Key → ℝ) : Integer.Sparse.eval row11934 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck11934, Integer.Sparse.eval_collectBalanced, rawRowCheck11934]

def rawRow11935 : Integer.Sparse Key := [(key1832, -2), (key1809, -2), (key1806, -2), (key1832, -2), (key1809, -2), (key1642, -2), (key1261, -2), (key1609, -2), (key1256, -2), (key1806, -2), (key1609, -2), (key1256, -2), (key1848, 1), (key1837, 1), (key1832, 1), (key1768, 1), (key1806, 1), (key1765, 1), (key1848, 1), (key1837, 1), (key1674, 1), (key1268, 1), (key1648, 1), (key1265, 1), (key1832, 1), (key1768, 1), (key1674, 1), (key1268, 1), (key1531, 1), (key1256, 1), (key1806, 1), (key1765, 1), (key1648, 1), (key1265, 1), (key1531, 1), (key1256, 1)]

theorem rawRowCheck11935 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form8 = rawRow11935 := by decide +kernel

def row11935 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1609, -4), (key1642, -2), (key1648, 2), (key1674, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -4), (key1832, -2), (key1837, 2), (key1848, 2)]

theorem rowCheck11935 : row11935 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11935 := by decide +kernel

theorem rowEval11935 (x : Key → ℝ) : Integer.Sparse.eval row11935 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form8) x := by
  rw [rowCheck11935, Integer.Sparse.eval_collectBalanced, rawRowCheck11935]

def rawRow11936 : Integer.Sparse Key := [(key2472, 1), (key2472, 1), (key2480, 1), (key2480, 1), (key2484, 1), (key2484, 1), (key2472, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2509, 1), (key2509, 1), (key2480, 1), (key2480, 1), (key2503, 1), (key2503, 1), (key2524, 1), (key2524, 1), (key2484, 1), (key2484, 1), (key2509, 1), (key2509, 1), (key2524, 1), (key2524, 1), (key2569, -2), (key2571, -2), (key2571, -2), (key2569, -2), (key2576, -2), (key2576, -2), (key2571, -2), (key2571, -2), (key2576, -2), (key2576, -2), (key2580, -2), (key2580, -2)]

theorem rawRowCheck11936 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form9 = rawRow11936 := by decide +kernel

def row11936 : Integer.Sparse Key := [(key2472, 4), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 4), (key2569, -4), (key2571, -8), (key2576, -8), (key2580, -4)]

theorem rowCheck11936 : row11936 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11936 := by decide +kernel

theorem rowEval11936 (x : Key → ℝ) : Integer.Sparse.eval row11936 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck11936, Integer.Sparse.eval_collectBalanced, rawRowCheck11936]

def rawRow11937 : Integer.Sparse Key := [(key2480, 1), (key2484, 1), (key2472, 1), (key2484, 1), (key2472, 1), (key2480, 1), (key2503, 1), (key2509, 1), (key2472, 1), (key2509, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2524, 1), (key2480, 1), (key2524, 1), (key2480, 1), (key2503, 1), (key2509, 1), (key2524, 1), (key2484, 1), (key2524, 1), (key2484, 1), (key2509, 1), (key2571, -2), (key2569, -2), (key2571, -2), (key2576, -2), (key2569, -2), (key2576, -2), (key2576, -2), (key2580, -2), (key2571, -2), (key2580, -2), (key2571, -2), (key2576, -2)]

theorem rawRowCheck11937 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form9 = rawRow11937 := by decide +kernel

def row11937 : Integer.Sparse Key := [(key2472, 4), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 4), (key2569, -4), (key2571, -8), (key2576, -8), (key2580, -4)]

theorem rowCheck11937 : row11937 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11937 := by decide +kernel

theorem rowEval11937 (x : Key → ℝ) : Integer.Sparse.eval row11937 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck11937, Integer.Sparse.eval_collectBalanced, rawRowCheck11937]

def rawRow11938 : Integer.Sparse Key := [(key2484, 1), (key2480, 1), (key2484, 1), (key2472, 1), (key2480, 1), (key2472, 1), (key2509, 1), (key2503, 1), (key2509, 1), (key2472, 1), (key2503, 1), (key2472, 1), (key2524, 1), (key2503, 1), (key2524, 1), (key2480, 1), (key2503, 1), (key2480, 1), (key2524, 1), (key2509, 1), (key2524, 1), (key2484, 1), (key2509, 1), (key2484, 1), (key2571, -2), (key2571, -2), (key2569, -2), (key2576, -2), (key2576, -2), (key2569, -2), (key2580, -2), (key2576, -2), (key2580, -2), (key2571, -2), (key2576, -2), (key2571, -2)]

theorem rawRowCheck11938 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form9 = rawRow11938 := by decide +kernel

def row11938 : Integer.Sparse Key := [(key2472, 4), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 4), (key2569, -4), (key2571, -8), (key2576, -8), (key2580, -4)]

theorem rowCheck11938 : row11938 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11938 := by decide +kernel

theorem rowEval11938 (x : Key → ℝ) : Integer.Sparse.eval row11938 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck11938, Integer.Sparse.eval_collectBalanced, rawRowCheck11938]

def rawRow11939 : Integer.Sparse Key := [(key2503, 1), (key2509, 1), (key2503, 1), (key2524, 1), (key2509, 1), (key2524, 1), (key2480, 1), (key2484, 1), (key2480, 1), (key2524, 1), (key2484, 1), (key2524, 1), (key2472, 1), (key2484, 1), (key2472, 1), (key2509, 1), (key2484, 1), (key2509, 1), (key2472, 1), (key2480, 1), (key2472, 1), (key2503, 1), (key2480, 1), (key2503, 1), (key2576, -2), (key2576, -2), (key2580, -2), (key2571, -2), (key2571, -2), (key2580, -2), (key2569, -2), (key2571, -2), (key2569, -2), (key2576, -2), (key2571, -2), (key2576, -2)]

theorem rawRowCheck11939 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form9 = rawRow11939 := by decide +kernel

def row11939 : Integer.Sparse Key := [(key2472, 4), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 4), (key2569, -4), (key2571, -8), (key2576, -8), (key2580, -4)]

theorem rowCheck11939 : row11939 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11939 := by decide +kernel

theorem rowEval11939 (x : Key → ℝ) : Integer.Sparse.eval row11939 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck11939, Integer.Sparse.eval_collectBalanced, rawRowCheck11939]

def rawRow11940 : Integer.Sparse Key := [(key2509, 1), (key2503, 1), (key2524, 1), (key2503, 1), (key2524, 1), (key2509, 1), (key2484, 1), (key2480, 1), (key2524, 1), (key2480, 1), (key2524, 1), (key2484, 1), (key2484, 1), (key2472, 1), (key2509, 1), (key2472, 1), (key2509, 1), (key2484, 1), (key2480, 1), (key2472, 1), (key2503, 1), (key2472, 1), (key2503, 1), (key2480, 1), (key2576, -2), (key2580, -2), (key2576, -2), (key2571, -2), (key2580, -2), (key2571, -2), (key2571, -2), (key2569, -2), (key2576, -2), (key2569, -2), (key2576, -2), (key2571, -2)]

theorem rawRowCheck11940 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form9 = rawRow11940 := by decide +kernel

def row11940 : Integer.Sparse Key := [(key2472, 4), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 4), (key2569, -4), (key2571, -8), (key2576, -8), (key2580, -4)]

theorem rowCheck11940 : row11940 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11940 := by decide +kernel

theorem rowEval11940 (x : Key → ℝ) : Integer.Sparse.eval row11940 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck11940, Integer.Sparse.eval_collectBalanced, rawRowCheck11940]

def rawRow11941 : Integer.Sparse Key := [(key2524, 1), (key2524, 1), (key2509, 1), (key2509, 1), (key2503, 1), (key2503, 1), (key2524, 1), (key2524, 1), (key2484, 1), (key2484, 1), (key2480, 1), (key2480, 1), (key2509, 1), (key2509, 1), (key2484, 1), (key2484, 1), (key2472, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2480, 1), (key2480, 1), (key2472, 1), (key2472, 1), (key2580, -2), (key2576, -2), (key2576, -2), (key2580, -2), (key2571, -2), (key2571, -2), (key2576, -2), (key2576, -2), (key2571, -2), (key2571, -2), (key2569, -2), (key2569, -2)]

theorem rawRowCheck11941 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form9 = rawRow11941 := by decide +kernel

def row11941 : Integer.Sparse Key := [(key2472, 4), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 4), (key2569, -4), (key2571, -8), (key2576, -8), (key2580, -4)]

theorem rowCheck11941 : row11941 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11941 := by decide +kernel

theorem rowEval11941 (x : Key → ℝ) : Integer.Sparse.eval row11941 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck11941, Integer.Sparse.eval_collectBalanced, rawRowCheck11941]

def rawRow11942 : Integer.Sparse Key := [(key2378, 1), (key2378, 1), (key2390, 1), (key2390, 1), (key2394, 1), (key2394, 1), (key2406, 1), (key2406, 1), (key2437, 1), (key2437, 1), (key2443, 1), (key2443, 1), (key2480, 1), (key2480, 1), (key2503, 1), (key2503, 1), (key2524, 1), (key2524, 1), (key2571, 1), (key2571, 1), (key2576, 1), (key2576, 1), (key2580, 1), (key2580, 1), (key2383, -2), (key2394, -2), (key2394, -2), (key2411, -2), (key2443, -2), (key2443, -2), (key2484, -2), (key2484, -2), (key2509, -2), (key2509, -2), (key2524, -2), (key2524, -2)]

theorem rawRowCheck11942 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form9 = rawRow11942 := by decide +kernel

def row11942 : Integer.Sparse Key := [(key2378, 2), (key2383, -2), (key2390, 2), (key2394, -2), (key2406, 2), (key2411, -2), (key2437, 2), (key2443, -2), (key2480, 2), (key2484, -4), (key2503, 2), (key2509, -4), (key2524, -2), (key2571, 2), (key2576, 2), (key2580, 2)]

theorem rowCheck11942 : row11942 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11942 := by decide +kernel

theorem rowEval11942 (x : Key → ℝ) : Integer.Sparse.eval row11942 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck11942, Integer.Sparse.eval_collectBalanced, rawRowCheck11942]

def rawRow11943 : Integer.Sparse Key := [(key2390, 1), (key2394, 1), (key2378, 1), (key2394, 1), (key2378, 1), (key2390, 1), (key2437, 1), (key2443, 1), (key2406, 1), (key2443, 1), (key2406, 1), (key2437, 1), (key2503, 1), (key2524, 1), (key2480, 1), (key2524, 1), (key2480, 1), (key2503, 1), (key2576, 1), (key2580, 1), (key2571, 1), (key2580, 1), (key2571, 1), (key2576, 1), (key2394, -2), (key2383, -2), (key2394, -2), (key2443, -2), (key2411, -2), (key2443, -2), (key2509, -2), (key2524, -2), (key2484, -2), (key2524, -2), (key2484, -2), (key2509, -2)]

theorem rawRowCheck11943 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form9 = rawRow11943 := by decide +kernel

def row11943 : Integer.Sparse Key := [(key2378, 2), (key2383, -2), (key2390, 2), (key2394, -2), (key2406, 2), (key2411, -2), (key2437, 2), (key2443, -2), (key2480, 2), (key2484, -4), (key2503, 2), (key2509, -4), (key2524, -2), (key2571, 2), (key2576, 2), (key2580, 2)]

theorem rowCheck11943 : row11943 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11943 := by decide +kernel

theorem rowEval11943 (x : Key → ℝ) : Integer.Sparse.eval row11943 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck11943, Integer.Sparse.eval_collectBalanced, rawRowCheck11943]

def rawRow11944 : Integer.Sparse Key := [(key2394, 1), (key2390, 1), (key2394, 1), (key2378, 1), (key2390, 1), (key2378, 1), (key2443, 1), (key2437, 1), (key2443, 1), (key2406, 1), (key2437, 1), (key2406, 1), (key2524, 1), (key2503, 1), (key2524, 1), (key2480, 1), (key2503, 1), (key2480, 1), (key2580, 1), (key2576, 1), (key2580, 1), (key2571, 1), (key2576, 1), (key2571, 1), (key2394, -2), (key2394, -2), (key2383, -2), (key2443, -2), (key2443, -2), (key2411, -2), (key2524, -2), (key2509, -2), (key2524, -2), (key2484, -2), (key2509, -2), (key2484, -2)]

theorem rawRowCheck11944 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form9 = rawRow11944 := by decide +kernel

def row11944 : Integer.Sparse Key := [(key2378, 2), (key2383, -2), (key2390, 2), (key2394, -2), (key2406, 2), (key2411, -2), (key2437, 2), (key2443, -2), (key2480, 2), (key2484, -4), (key2503, 2), (key2509, -4), (key2524, -2), (key2571, 2), (key2576, 2), (key2580, 2)]

theorem rowCheck11944 : row11944 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11944 := by decide +kernel

theorem rowEval11944 (x : Key → ℝ) : Integer.Sparse.eval row11944 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck11944, Integer.Sparse.eval_collectBalanced, rawRowCheck11944]

def rawRow11945 : Integer.Sparse Key := [(key2766, 1), (key2766, 1), (key2887, 1), (key2887, 1), (key2910, 1), (key2910, 1), (key2587, 1), (key2587, 1), (key2966, 1), (key2966, 1), (key2989, 1), (key2989, 1), (key2390, 1), (key2390, 1), (key2437, 1), (key2437, 1), (key2580, 1), (key2580, 1), (key2394, 1), (key2394, 1), (key2443, 1), (key2443, 1), (key2524, 1), (key2524, 1), (key2411, -2), (key2484, -2), (key2484, -2), (key2383, -2), (key2509, -2), (key2509, -2), (key2394, -2), (key2394, -2), (key2443, -2), (key2443, -2), (key2524, -2), (key2524, -2)]

theorem rawRowCheck11945 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form9 = rawRow11945 := by decide +kernel

def row11945 : Integer.Sparse Key := [(key2383, -2), (key2390, 2), (key2394, -2), (key2411, -2), (key2437, 2), (key2443, -2), (key2484, -4), (key2509, -4), (key2524, -2), (key2580, 2), (key2587, 2), (key2766, 2), (key2887, 2), (key2910, 2), (key2966, 2), (key2989, 2)]

theorem rowCheck11945 : row11945 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11945 := by decide +kernel

theorem rowEval11945 (x : Key → ℝ) : Integer.Sparse.eval row11945 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck11945, Integer.Sparse.eval_collectBalanced, rawRowCheck11945]

def rawRow11946 : Integer.Sparse Key := [(key2887, 1), (key2910, 1), (key2766, 1), (key2910, 1), (key2766, 1), (key2887, 1), (key2966, 1), (key2989, 1), (key2587, 1), (key2989, 1), (key2587, 1), (key2966, 1), (key2929, 1), (key3002, 1), (key2598, 1), (key3002, 1), (key2390, 1), (key2437, 1), (key2443, 1), (key2524, 1), (key2394, 1), (key2524, 1), (key2394, 1), (key2443, 1), (key2484, -2), (key2411, -2), (key2484, -2), (key2509, -2), (key2383, -2), (key2509, -2), (key2443, -2), (key2524, -2), (key2394, -2), (key2524, -2), (key2394, -2), (key2443, -2)]

theorem rawRowCheck11946 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form9 = rawRow11946 := by decide +kernel

def row11946 : Integer.Sparse Key := [(key2383, -2), (key2390, 1), (key2394, -2), (key2411, -2), (key2437, 1), (key2443, -2), (key2484, -4), (key2509, -4), (key2524, -2), (key2587, 2), (key2598, 1), (key2766, 2), (key2887, 2), (key2910, 2), (key2929, 1), (key2966, 2), (key2989, 2), (key3002, 2)]

theorem rowCheck11946 : row11946 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11946 := by decide +kernel

theorem rowEval11946 (x : Key → ℝ) : Integer.Sparse.eval row11946 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck11946, Integer.Sparse.eval_collectBalanced, rawRowCheck11946]

def rawRow11947 : Integer.Sparse Key := [(key2910, 1), (key2887, 1), (key2910, 1), (key2766, 1), (key2887, 1), (key2766, 1), (key2989, 1), (key2966, 1), (key2989, 1), (key2587, 1), (key2966, 1), (key2587, 1), (key3002, 1), (key2929, 1), (key3002, 1), (key2598, 1), (key2437, 1), (key2390, 1), (key2524, 1), (key2443, 1), (key2524, 1), (key2394, 1), (key2443, 1), (key2394, 1), (key2484, -2), (key2484, -2), (key2411, -2), (key2509, -2), (key2509, -2), (key2383, -2), (key2524, -2), (key2443, -2), (key2524, -2), (key2394, -2), (key2443, -2), (key2394, -2)]

theorem rawRowCheck11947 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form9 = rawRow11947 := by decide +kernel

def row11947 : Integer.Sparse Key := [(key2383, -2), (key2390, 1), (key2394, -2), (key2411, -2), (key2437, 1), (key2443, -2), (key2484, -4), (key2509, -4), (key2524, -2), (key2587, 2), (key2598, 1), (key2766, 2), (key2887, 2), (key2910, 2), (key2929, 1), (key2966, 2), (key2989, 2), (key3002, 2)]

theorem rowCheck11947 : row11947 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11947 := by decide +kernel

theorem rowEval11947 (x : Key → ℝ) : Integer.Sparse.eval row11947 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form9) x := by
  rw [rowCheck11947, Integer.Sparse.eval_collectBalanced, rawRowCheck11947]

def rawRow11948 : Integer.Sparse Key := [(key2929, 1), (key2931, 1), (key2966, 1), (key2995, 1), (key2989, 1), (key3002, 1), (key2598, 1), (key2600, 1), (key2887, 1), (key2995, 1), (key2910, 1), (key3002, 1), (key2587, 1), (key2600, 1), (key2766, 1), (key2931, 1), (key2910, 1), (key2989, 1), (key2378, 1), (key2390, 1), (key2406, 1), (key2437, 1), (key2480, 1), (key2503, 1), (key2443, -2), (key2509, -2), (key2524, -2), (key2394, -2), (key2484, -2), (key2524, -2), (key2383, -2), (key2394, -2), (key2411, -2), (key2443, -2), (key2484, -2), (key2509, -2)]

theorem rawRowCheck11948 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form9 = rawRow11948 := by decide +kernel

def row11948 : Integer.Sparse Key := [(key2378, 1), (key2383, -2), (key2390, 1), (key2394, -4), (key2406, 1), (key2411, -2), (key2437, 1), (key2443, -4), (key2480, 1), (key2484, -4), (key2503, 1), (key2509, -4), (key2524, -4), (key2587, 1), (key2598, 1), (key2600, 2), (key2766, 1), (key2887, 1), (key2910, 2), (key2929, 1), (key2931, 2), (key2966, 1), (key2989, 2), (key2995, 2), (key3002, 2)]

theorem rowCheck11948 : row11948 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11948 := by decide +kernel

theorem rowEval11948 (x : Key → ℝ) : Integer.Sparse.eval row11948 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck11948, Integer.Sparse.eval_collectBalanced, rawRowCheck11948]

def rawRow11949 : Integer.Sparse Key := [(key2931, 1), (key2929, 1), (key2995, 1), (key2966, 1), (key3002, 1), (key2989, 1), (key2600, 1), (key2598, 1), (key2995, 1), (key2887, 1), (key3002, 1), (key2910, 1), (key2600, 1), (key2587, 1), (key2931, 1), (key2766, 1), (key2989, 1), (key2910, 1), (key2390, 1), (key2378, 1), (key2437, 1), (key2406, 1), (key2503, 1), (key2480, 1), (key2443, -2), (key2524, -2), (key2509, -2), (key2394, -2), (key2524, -2), (key2484, -2), (key2394, -2), (key2383, -2), (key2443, -2), (key2411, -2), (key2509, -2), (key2484, -2)]

theorem rawRowCheck11949 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form9 = rawRow11949 := by decide +kernel

def row11949 : Integer.Sparse Key := [(key2378, 1), (key2383, -2), (key2390, 1), (key2394, -4), (key2406, 1), (key2411, -2), (key2437, 1), (key2443, -4), (key2480, 1), (key2484, -4), (key2503, 1), (key2509, -4), (key2524, -4), (key2587, 1), (key2598, 1), (key2600, 2), (key2766, 1), (key2887, 1), (key2910, 2), (key2929, 1), (key2931, 2), (key2966, 1), (key2989, 2), (key2995, 2), (key3002, 2)]

theorem rowCheck11949 : row11949 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11949 := by decide +kernel

theorem rowEval11949 (x : Key → ℝ) : Integer.Sparse.eval row11949 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck11949, Integer.Sparse.eval_collectBalanced, rawRowCheck11949]

def rawRow11950 : Integer.Sparse Key := [(key2966, 1), (key2989, 1), (key2929, 1), (key3002, 1), (key2931, 1), (key2995, 1), (key2887, 1), (key2910, 1), (key2598, 1), (key3002, 1), (key2600, 1), (key2995, 1), (key2766, 1), (key2910, 1), (key2587, 1), (key2989, 1), (key2600, 1), (key2931, 1), (key2406, 1), (key2480, 1), (key2378, 1), (key2503, 1), (key2390, 1), (key2437, 1), (key2509, -2), (key2443, -2), (key2524, -2), (key2484, -2), (key2394, -2), (key2524, -2), (key2411, -2), (key2484, -2), (key2383, -2), (key2509, -2), (key2394, -2), (key2443, -2)]

theorem rawRowCheck11950 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form9 = rawRow11950 := by decide +kernel

def row11950 : Integer.Sparse Key := [(key2378, 1), (key2383, -2), (key2390, 1), (key2394, -4), (key2406, 1), (key2411, -2), (key2437, 1), (key2443, -4), (key2480, 1), (key2484, -4), (key2503, 1), (key2509, -4), (key2524, -4), (key2587, 1), (key2598, 1), (key2600, 2), (key2766, 1), (key2887, 1), (key2910, 2), (key2929, 1), (key2931, 2), (key2966, 1), (key2989, 2), (key2995, 2), (key3002, 2)]

theorem rowCheck11950 : row11950 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11950 := by decide +kernel

theorem rowEval11950 (x : Key → ℝ) : Integer.Sparse.eval row11950 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck11950, Integer.Sparse.eval_collectBalanced, rawRowCheck11950]

def rawRow11951 : Integer.Sparse Key := [(key2989, 1), (key2966, 1), (key3002, 1), (key2929, 1), (key2995, 1), (key2931, 1), (key2910, 1), (key2887, 1), (key3002, 1), (key2598, 1), (key2995, 1), (key2600, 1), (key2910, 1), (key2766, 1), (key2989, 1), (key2587, 1), (key2931, 1), (key2600, 1), (key2480, 1), (key2406, 1), (key2503, 1), (key2378, 1), (key2437, 1), (key2390, 1), (key2509, -2), (key2524, -2), (key2443, -2), (key2484, -2), (key2524, -2), (key2394, -2), (key2484, -2), (key2411, -2), (key2509, -2), (key2383, -2), (key2443, -2), (key2394, -2)]

theorem rawRowCheck11951 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form9 = rawRow11951 := by decide +kernel

def row11951 : Integer.Sparse Key := [(key2378, 1), (key2383, -2), (key2390, 1), (key2394, -4), (key2406, 1), (key2411, -2), (key2437, 1), (key2443, -4), (key2480, 1), (key2484, -4), (key2503, 1), (key2509, -4), (key2524, -4), (key2587, 1), (key2598, 1), (key2600, 2), (key2766, 1), (key2887, 1), (key2910, 2), (key2929, 1), (key2931, 2), (key2966, 1), (key2989, 2), (key2995, 2), (key3002, 2)]

theorem rowCheck11951 : row11951 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11951 := by decide +kernel

theorem rowEval11951 (x : Key → ℝ) : Integer.Sparse.eval row11951 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form9) x := by
  rw [rowCheck11951, Integer.Sparse.eval_collectBalanced, rawRowCheck11951]

def rawRow11952 : Integer.Sparse Key := [(key2995, 1), (key3002, 1), (key2931, 1), (key2989, 1), (key2929, 1), (key2966, 1), (key2995, 1), (key3002, 1), (key2600, 1), (key2910, 1), (key2598, 1), (key2887, 1), (key2931, 1), (key2989, 1), (key2600, 1), (key2910, 1), (key2587, 1), (key2766, 1), (key2437, 1), (key2503, 1), (key2390, 1), (key2480, 1), (key2378, 1), (key2406, 1), (key2524, -2), (key2443, -2), (key2509, -2), (key2524, -2), (key2394, -2), (key2484, -2), (key2443, -2), (key2509, -2), (key2394, -2), (key2484, -2), (key2383, -2), (key2411, -2)]

theorem rawRowCheck11952 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form9 = rawRow11952 := by decide +kernel

def row11952 : Integer.Sparse Key := [(key2378, 1), (key2383, -2), (key2390, 1), (key2394, -4), (key2406, 1), (key2411, -2), (key2437, 1), (key2443, -4), (key2480, 1), (key2484, -4), (key2503, 1), (key2509, -4), (key2524, -4), (key2587, 1), (key2598, 1), (key2600, 2), (key2766, 1), (key2887, 1), (key2910, 2), (key2929, 1), (key2931, 2), (key2966, 1), (key2989, 2), (key2995, 2), (key3002, 2)]

theorem rowCheck11952 : row11952 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11952 := by decide +kernel

theorem rowEval11952 (x : Key → ℝ) : Integer.Sparse.eval row11952 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck11952, Integer.Sparse.eval_collectBalanced, rawRowCheck11952]

def rawRow11953 : Integer.Sparse Key := [(key3002, 1), (key2995, 1), (key2989, 1), (key2931, 1), (key2966, 1), (key2929, 1), (key3002, 1), (key2995, 1), (key2910, 1), (key2600, 1), (key2887, 1), (key2598, 1), (key2989, 1), (key2931, 1), (key2910, 1), (key2600, 1), (key2766, 1), (key2587, 1), (key2503, 1), (key2437, 1), (key2480, 1), (key2390, 1), (key2406, 1), (key2378, 1), (key2524, -2), (key2509, -2), (key2443, -2), (key2524, -2), (key2484, -2), (key2394, -2), (key2509, -2), (key2443, -2), (key2484, -2), (key2394, -2), (key2411, -2), (key2383, -2)]

theorem rawRowCheck11953 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form9 = rawRow11953 := by decide +kernel

def row11953 : Integer.Sparse Key := [(key2378, 1), (key2383, -2), (key2390, 1), (key2394, -4), (key2406, 1), (key2411, -2), (key2437, 1), (key2443, -4), (key2480, 1), (key2484, -4), (key2503, 1), (key2509, -4), (key2524, -4), (key2587, 1), (key2598, 1), (key2600, 2), (key2766, 1), (key2887, 1), (key2910, 2), (key2929, 1), (key2931, 2), (key2966, 1), (key2989, 2), (key2995, 2), (key3002, 2)]

theorem rowCheck11953 : row11953 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11953 := by decide +kernel

theorem rowEval11953 (x : Key → ℝ) : Integer.Sparse.eval row11953 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form9) x := by
  rw [rowCheck11953, Integer.Sparse.eval_collectBalanced, rawRowCheck11953]

def rawRow11954 : Integer.Sparse Key := [(key1529, -6), (key1529, -6), (key1763, -6), (key1763, -6), (key1607, 2), (key1646, 2), (key1646, 2), (key1607, 2), (key1804, 2), (key1804, 2), (key1646, 2), (key1646, 2), (key1804, 2), (key1804, 2), (key1835, 2), (key1835, 2)]

theorem rawRowCheck11954 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form10 = rawRow11954 := by decide +kernel

def row11954 : Integer.Sparse Key := [(key1529, -12), (key1607, 4), (key1646, 8), (key1763, -12), (key1804, 8), (key1835, 4)]

theorem rowCheck11954 : row11954 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11954 := by decide +kernel

theorem rowEval11954 (x : Key → ℝ) : Integer.Sparse.eval row11954 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck11954, Integer.Sparse.eval_collectBalanced, rawRowCheck11954]

def rawRow11955 : Integer.Sparse Key := [(key1529, -6), (key1763, -6), (key1529, -6), (key1763, -6), (key1646, 2), (key1607, 2), (key1646, 2), (key1804, 2), (key1607, 2), (key1804, 2), (key1804, 2), (key1835, 2), (key1646, 2), (key1835, 2), (key1646, 2), (key1804, 2)]

theorem rawRowCheck11955 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form10 = rawRow11955 := by decide +kernel

def row11955 : Integer.Sparse Key := [(key1529, -12), (key1607, 4), (key1646, 8), (key1763, -12), (key1804, 8), (key1835, 4)]

theorem rowCheck11955 : row11955 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11955 := by decide +kernel

theorem rowEval11955 (x : Key → ℝ) : Integer.Sparse.eval row11955 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck11955, Integer.Sparse.eval_collectBalanced, rawRowCheck11955]

def rawRow11956 : Integer.Sparse Key := [(key1529, -6), (key1763, -6), (key1763, -6), (key1529, -6), (key1646, 2), (key1646, 2), (key1607, 2), (key1804, 2), (key1804, 2), (key1607, 2), (key1835, 2), (key1804, 2), (key1835, 2), (key1646, 2), (key1804, 2), (key1646, 2)]

theorem rawRowCheck11956 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form10 = rawRow11956 := by decide +kernel

def row11956 : Integer.Sparse Key := [(key1529, -12), (key1607, 4), (key1646, 8), (key1763, -12), (key1804, 8), (key1835, 4)]

theorem rowCheck11956 : row11956 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11956 := by decide +kernel

theorem rowEval11956 (x : Key → ℝ) : Integer.Sparse.eval row11956 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck11956, Integer.Sparse.eval_collectBalanced, rawRowCheck11956]

def rawRow11957 : Integer.Sparse Key := [(key1763, -6), (key1529, -6), (key1529, -6), (key1763, -6), (key1804, 2), (key1804, 2), (key1835, 2), (key1646, 2), (key1646, 2), (key1835, 2), (key1607, 2), (key1646, 2), (key1607, 2), (key1804, 2), (key1646, 2), (key1804, 2)]

theorem rawRowCheck11957 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form10 = rawRow11957 := by decide +kernel

def row11957 : Integer.Sparse Key := [(key1529, -12), (key1607, 4), (key1646, 8), (key1763, -12), (key1804, 8), (key1835, 4)]

theorem rowCheck11957 : row11957 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11957 := by decide +kernel

theorem rowEval11957 (x : Key → ℝ) : Integer.Sparse.eval row11957 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck11957, Integer.Sparse.eval_collectBalanced, rawRowCheck11957]

def rawRow11958 : Integer.Sparse Key := [(key1763, -6), (key1529, -6), (key1763, -6), (key1529, -6), (key1804, 2), (key1835, 2), (key1804, 2), (key1646, 2), (key1835, 2), (key1646, 2), (key1646, 2), (key1607, 2), (key1804, 2), (key1607, 2), (key1804, 2), (key1646, 2)]

theorem rawRowCheck11958 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form10 = rawRow11958 := by decide +kernel

def row11958 : Integer.Sparse Key := [(key1529, -12), (key1607, 4), (key1646, 8), (key1763, -12), (key1804, 8), (key1835, 4)]

theorem rowCheck11958 : row11958 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11958 := by decide +kernel

theorem rowEval11958 (x : Key → ℝ) : Integer.Sparse.eval row11958 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck11958, Integer.Sparse.eval_collectBalanced, rawRowCheck11958]

def rawRow11959 : Integer.Sparse Key := [(key1763, -6), (key1763, -6), (key1529, -6), (key1529, -6), (key1835, 2), (key1804, 2), (key1804, 2), (key1835, 2), (key1646, 2), (key1646, 2), (key1804, 2), (key1804, 2), (key1646, 2), (key1646, 2), (key1607, 2), (key1607, 2)]

theorem rawRowCheck11959 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form10 = rawRow11959 := by decide +kernel

def row11959 : Integer.Sparse Key := [(key1529, -12), (key1607, 4), (key1646, 8), (key1763, -12), (key1804, 8), (key1835, 4)]

theorem rowCheck11959 : row11959 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11959 := by decide +kernel

theorem rowEval11959 (x : Key → ℝ) : Integer.Sparse.eval row11959 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck11959, Integer.Sparse.eval_collectBalanced, rawRowCheck11959]

def rawRow11960 : Integer.Sparse Key := [(key1254, -6), (key1607, -6), (key1804, -6), (key1804, -6), (key1254, 2), (key1263, 2), (key1263, 2), (key1529, 2), (key1763, 2), (key1763, 2), (key1646, 2), (key1646, 2), (key1804, 2), (key1804, 2), (key1835, 2), (key1835, 2)]

theorem rawRowCheck11960 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form10 = rawRow11960 := by decide +kernel

def row11960 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 2), (key1607, -6), (key1646, 4), (key1763, 4), (key1804, -8), (key1835, 4)]

theorem rowCheck11960 : row11960 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11960 := by decide +kernel

theorem rowEval11960 (x : Key → ℝ) : Integer.Sparse.eval row11960 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck11960, Integer.Sparse.eval_collectBalanced, rawRowCheck11960]

def rawRow11961 : Integer.Sparse Key := [(key1254, -6), (key1804, -6), (key1607, -6), (key1804, -6), (key1263, 2), (key1254, 2), (key1263, 2), (key1763, 2), (key1529, 2), (key1763, 2), (key1804, 2), (key1835, 2), (key1646, 2), (key1835, 2), (key1646, 2), (key1804, 2)]

theorem rawRowCheck11961 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form10 = rawRow11961 := by decide +kernel

def row11961 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 2), (key1607, -6), (key1646, 4), (key1763, 4), (key1804, -8), (key1835, 4)]

theorem rowCheck11961 : row11961 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11961 := by decide +kernel

theorem rowEval11961 (x : Key → ℝ) : Integer.Sparse.eval row11961 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck11961, Integer.Sparse.eval_collectBalanced, rawRowCheck11961]

def rawRow11962 : Integer.Sparse Key := [(key1254, -6), (key1804, -6), (key1804, -6), (key1607, -6), (key1263, 2), (key1263, 2), (key1254, 2), (key1763, 2), (key1763, 2), (key1529, 2), (key1835, 2), (key1804, 2), (key1835, 2), (key1646, 2), (key1804, 2), (key1646, 2)]

theorem rawRowCheck11962 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form10 = rawRow11962 := by decide +kernel

def row11962 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 2), (key1607, -6), (key1646, 4), (key1763, 4), (key1804, -8), (key1835, 4)]

theorem rowCheck11962 : row11962 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11962 := by decide +kernel

theorem rowEval11962 (x : Key → ℝ) : Integer.Sparse.eval row11962 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck11962, Integer.Sparse.eval_collectBalanced, rawRowCheck11962]

def rawRow11963 : Integer.Sparse Key := [(key1607, -6), (key1254, -6), (key1804, -6), (key1804, -6), (key1529, 2), (key1646, 2), (key1646, 2), (key1254, 2), (key1804, 2), (key1804, 2), (key1263, 2), (key1263, 2), (key1763, 2), (key1763, 2), (key1835, 2), (key1835, 2)]

theorem rawRowCheck11963 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form10 = rawRow11963 := by decide +kernel

def row11963 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 2), (key1607, -6), (key1646, 4), (key1763, 4), (key1804, -8), (key1835, 4)]

theorem rowCheck11963 : row11963 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11963 := by decide +kernel

theorem rowEval11963 (x : Key → ℝ) : Integer.Sparse.eval row11963 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck11963, Integer.Sparse.eval_collectBalanced, rawRowCheck11963]

def rawRow11964 : Integer.Sparse Key := [(key1607, -6), (key1804, -6), (key1254, -6), (key1804, -6), (key1646, 2), (key1529, 2), (key1646, 2), (key1804, 2), (key1254, 2), (key1804, 2), (key1763, 2), (key1835, 2), (key1263, 2), (key1835, 2), (key1263, 2), (key1763, 2)]

theorem rawRowCheck11964 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form10 = rawRow11964 := by decide +kernel

def row11964 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 2), (key1607, -6), (key1646, 4), (key1763, 4), (key1804, -8), (key1835, 4)]

theorem rowCheck11964 : row11964 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11964 := by decide +kernel

theorem rowEval11964 (x : Key → ℝ) : Integer.Sparse.eval row11964 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck11964, Integer.Sparse.eval_collectBalanced, rawRowCheck11964]

def rawRow11965 : Integer.Sparse Key := [(key1607, -6), (key1804, -6), (key1804, -6), (key1254, -6), (key1646, 2), (key1646, 2), (key1529, 2), (key1804, 2), (key1804, 2), (key1254, 2), (key1835, 2), (key1763, 2), (key1835, 2), (key1263, 2), (key1763, 2), (key1263, 2)]

theorem rawRowCheck11965 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form10 = rawRow11965 := by decide +kernel

def row11965 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 2), (key1607, -6), (key1646, 4), (key1763, 4), (key1804, -8), (key1835, 4)]

theorem rowCheck11965 : row11965 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11965 := by decide +kernel

theorem rowEval11965 (x : Key → ℝ) : Integer.Sparse.eval row11965 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form10) x := by
  rw [rowCheck11965, Integer.Sparse.eval_collectBalanced, rawRowCheck11965]

def rawRow11966 : Integer.Sparse Key := [(key1804, -6), (key1254, -6), (key1607, -6), (key1804, -6), (key1763, 2), (key1804, 2), (key1835, 2), (key1263, 2), (key1646, 2), (key1835, 2), (key1254, 2), (key1263, 2), (key1529, 2), (key1763, 2), (key1646, 2), (key1804, 2)]

theorem rawRowCheck11966 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form10 = rawRow11966 := by decide +kernel

def row11966 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 2), (key1607, -6), (key1646, 4), (key1763, 4), (key1804, -8), (key1835, 4)]

theorem rowCheck11966 : row11966 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11966 := by decide +kernel

theorem rowEval11966 (x : Key → ℝ) : Integer.Sparse.eval row11966 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck11966, Integer.Sparse.eval_collectBalanced, rawRowCheck11966]

def rawRow11967 : Integer.Sparse Key := [(key1804, -6), (key1254, -6), (key1804, -6), (key1607, -6), (key1763, 2), (key1835, 2), (key1804, 2), (key1263, 2), (key1835, 2), (key1646, 2), (key1263, 2), (key1254, 2), (key1763, 2), (key1529, 2), (key1804, 2), (key1646, 2)]

theorem rawRowCheck11967 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form10 = rawRow11967 := by decide +kernel

def row11967 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 2), (key1607, -6), (key1646, 4), (key1763, 4), (key1804, -8), (key1835, 4)]

theorem rowCheck11967 : row11967 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11967 := by decide +kernel

theorem rowEval11967 (x : Key → ℝ) : Integer.Sparse.eval row11967 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck11967, Integer.Sparse.eval_collectBalanced, rawRowCheck11967]

def rawRow11968 : Integer.Sparse Key := [(key1804, -6), (key1607, -6), (key1254, -6), (key1804, -6), (key1804, 2), (key1763, 2), (key1835, 2), (key1646, 2), (key1263, 2), (key1835, 2), (key1529, 2), (key1646, 2), (key1254, 2), (key1804, 2), (key1263, 2), (key1763, 2)]

theorem rawRowCheck11968 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form10 = rawRow11968 := by decide +kernel

def row11968 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 2), (key1607, -6), (key1646, 4), (key1763, 4), (key1804, -8), (key1835, 4)]

theorem rowCheck11968 : row11968 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11968 := by decide +kernel

theorem rowEval11968 (x : Key → ℝ) : Integer.Sparse.eval row11968 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck11968, Integer.Sparse.eval_collectBalanced, rawRowCheck11968]

def rawRow11969 : Integer.Sparse Key := [(key1804, -6), (key1607, -6), (key1804, -6), (key1254, -6), (key1804, 2), (key1835, 2), (key1763, 2), (key1646, 2), (key1835, 2), (key1263, 2), (key1646, 2), (key1529, 2), (key1804, 2), (key1254, 2), (key1763, 2), (key1263, 2)]

theorem rawRowCheck11969 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form10 = rawRow11969 := by decide +kernel

def row11969 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 2), (key1607, -6), (key1646, 4), (key1763, 4), (key1804, -8), (key1835, 4)]

theorem rowCheck11969 : row11969 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11969 := by decide +kernel

theorem rowEval11969 (x : Key → ℝ) : Integer.Sparse.eval row11969 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form10) x := by
  rw [rowCheck11969, Integer.Sparse.eval_collectBalanced, rawRowCheck11969]

def rawRow11970 : Integer.Sparse Key := [(key1804, -6), (key1804, -6), (key1254, -6), (key1607, -6), (key1835, 2), (key1763, 2), (key1804, 2), (key1835, 2), (key1263, 2), (key1646, 2), (key1763, 2), (key1804, 2), (key1263, 2), (key1646, 2), (key1254, 2), (key1529, 2)]

theorem rawRowCheck11970 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form10 = rawRow11970 := by decide +kernel

def row11970 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 2), (key1607, -6), (key1646, 4), (key1763, 4), (key1804, -8), (key1835, 4)]

theorem rowCheck11970 : row11970 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11970 := by decide +kernel

theorem rowEval11970 (x : Key → ℝ) : Integer.Sparse.eval row11970 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck11970, Integer.Sparse.eval_collectBalanced, rawRowCheck11970]

def rawRow11971 : Integer.Sparse Key := [(key1804, -6), (key1804, -6), (key1607, -6), (key1254, -6), (key1835, 2), (key1804, 2), (key1763, 2), (key1835, 2), (key1646, 2), (key1263, 2), (key1804, 2), (key1763, 2), (key1646, 2), (key1263, 2), (key1529, 2), (key1254, 2)]

theorem rawRowCheck11971 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form10 = rawRow11971 := by decide +kernel

def row11971 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 2), (key1607, -6), (key1646, 4), (key1763, 4), (key1804, -8), (key1835, 4)]

theorem rowCheck11971 : row11971 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11971 := by decide +kernel

theorem rowEval11971 (x : Key → ℝ) : Integer.Sparse.eval row11971 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form10) x := by
  rw [rowCheck11971, Integer.Sparse.eval_collectBalanced, rawRowCheck11971]

def rawRow11972 : Integer.Sparse Key := [(key2361, 6), (key2361, 6), (key2364, 6), (key2364, 6), (key2531, -6), (key2531, -6), (key2561, -6), (key2561, -6)]

theorem rawRowCheck11972 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form11 = rawRow11972 := by decide +kernel

def row11972 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2531, -12), (key2561, -12)]

theorem rowCheck11972 : row11972 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11972 := by decide +kernel

theorem rowEval11972 (x : Key → ℝ) : Integer.Sparse.eval row11972 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11972, Integer.Sparse.eval_collectBalanced, rawRowCheck11972]

def rawRow11973 : Integer.Sparse Key := [(key2361, 6), (key2364, 6), (key2361, 6), (key2364, 6), (key2531, -6), (key2561, -6), (key2531, -6), (key2561, -6)]

theorem rawRowCheck11973 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form11 = rawRow11973 := by decide +kernel

def row11973 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2531, -12), (key2561, -12)]

theorem rowCheck11973 : row11973 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11973 := by decide +kernel

theorem rowEval11973 (x : Key → ℝ) : Integer.Sparse.eval row11973 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11973, Integer.Sparse.eval_collectBalanced, rawRowCheck11973]

def rawRow11974 : Integer.Sparse Key := [(key2364, 6), (key2361, 6), (key2361, 6), (key2364, 6), (key2531, -6), (key2561, -6), (key2561, -6), (key2531, -6)]

theorem rawRowCheck11974 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form11 = rawRow11974 := by decide +kernel

def row11974 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2531, -12), (key2561, -12)]

theorem rowCheck11974 : row11974 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11974 := by decide +kernel

theorem rowEval11974 (x : Key → ℝ) : Integer.Sparse.eval row11974 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck11974, Integer.Sparse.eval_collectBalanced, rawRowCheck11974]

def rawRow11975 : Integer.Sparse Key := [(key2361, 6), (key2364, 6), (key2364, 6), (key2361, 6), (key2561, -6), (key2531, -6), (key2531, -6), (key2561, -6)]

theorem rawRowCheck11975 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form11 = rawRow11975 := by decide +kernel

def row11975 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2531, -12), (key2561, -12)]

theorem rowCheck11975 : row11975 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11975 := by decide +kernel

theorem rowEval11975 (x : Key → ℝ) : Integer.Sparse.eval row11975 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11975, Integer.Sparse.eval_collectBalanced, rawRowCheck11975]

def rawRow11976 : Integer.Sparse Key := [(key2364, 6), (key2361, 6), (key2364, 6), (key2361, 6), (key2561, -6), (key2531, -6), (key2561, -6), (key2531, -6)]

theorem rawRowCheck11976 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form11 = rawRow11976 := by decide +kernel

def row11976 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2531, -12), (key2561, -12)]

theorem rowCheck11976 : row11976 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11976 := by decide +kernel

theorem rowEval11976 (x : Key → ℝ) : Integer.Sparse.eval row11976 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck11976, Integer.Sparse.eval_collectBalanced, rawRowCheck11976]

def rawRow11977 : Integer.Sparse Key := [(key2364, 6), (key2364, 6), (key2361, 6), (key2361, 6), (key2561, -6), (key2561, -6), (key2531, -6), (key2531, -6)]

theorem rawRowCheck11977 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form11 = rawRow11977 := by decide +kernel

def row11977 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2531, -12), (key2561, -12)]

theorem rowCheck11977 : row11977 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11977 := by decide +kernel

theorem rowEval11977 (x : Key → ℝ) : Integer.Sparse.eval row11977 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck11977, Integer.Sparse.eval_collectBalanced, rawRowCheck11977]

def rawRow11978 : Integer.Sparse Key := [(key2456, 6), (key2456, 6), (key2459, 6), (key2531, 6), (key2364, -6), (key2459, -6), (key2520, -6), (key2520, -6)]

theorem rawRowCheck11978 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form11 = rawRow11978 := by decide +kernel

def row11978 : Integer.Sparse Key := [(key2364, -6), (key2456, 12), (key2520, -12), (key2531, 6)]

theorem rowCheck11978 : row11978 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11978 := by decide +kernel

theorem rowEval11978 (x : Key → ℝ) : Integer.Sparse.eval row11978 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11978, Integer.Sparse.eval_collectBalanced, rawRowCheck11978]

def rawRow11979 : Integer.Sparse Key := [(key2456, 6), (key2459, 6), (key2456, 6), (key2531, 6), (key2364, -6), (key2520, -6), (key2459, -6), (key2520, -6)]

theorem rawRowCheck11979 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form11 = rawRow11979 := by decide +kernel

def row11979 : Integer.Sparse Key := [(key2364, -6), (key2456, 12), (key2520, -12), (key2531, 6)]

theorem rowCheck11979 : row11979 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11979 := by decide +kernel

theorem rowEval11979 (x : Key → ℝ) : Integer.Sparse.eval row11979 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11979, Integer.Sparse.eval_collectBalanced, rawRowCheck11979]

def rawRow11980 : Integer.Sparse Key := [(key2459, 6), (key2456, 6), (key2456, 6), (key2531, 6), (key2364, -6), (key2520, -6), (key2520, -6), (key2459, -6)]

theorem rawRowCheck11980 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form11 = rawRow11980 := by decide +kernel

def row11980 : Integer.Sparse Key := [(key2364, -6), (key2456, 12), (key2520, -12), (key2531, 6)]

theorem rowCheck11980 : row11980 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11980 := by decide +kernel

theorem rowEval11980 (x : Key → ℝ) : Integer.Sparse.eval row11980 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck11980, Integer.Sparse.eval_collectBalanced, rawRowCheck11980]

def rawRow11981 : Integer.Sparse Key := [(key2456, 6), (key2456, 6), (key2531, 6), (key2459, 6), (key2459, -6), (key2364, -6), (key2520, -6), (key2520, -6)]

theorem rawRowCheck11981 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form11 = rawRow11981 := by decide +kernel

def row11981 : Integer.Sparse Key := [(key2364, -6), (key2456, 12), (key2520, -12), (key2531, 6)]

theorem rowCheck11981 : row11981 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11981 := by decide +kernel

theorem rowEval11981 (x : Key → ℝ) : Integer.Sparse.eval row11981 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11981, Integer.Sparse.eval_collectBalanced, rawRowCheck11981]

def rawRow11982 : Integer.Sparse Key := [(key2456, 6), (key2531, 6), (key2456, 6), (key2459, 6), (key2459, -6), (key2520, -6), (key2364, -6), (key2520, -6)]

theorem rawRowCheck11982 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form11 = rawRow11982 := by decide +kernel

def row11982 : Integer.Sparse Key := [(key2364, -6), (key2456, 12), (key2520, -12), (key2531, 6)]

theorem rowCheck11982 : row11982 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11982 := by decide +kernel

theorem rowEval11982 (x : Key → ℝ) : Integer.Sparse.eval row11982 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11982, Integer.Sparse.eval_collectBalanced, rawRowCheck11982]

def rawRow11983 : Integer.Sparse Key := [(key2531, 6), (key2456, 6), (key2456, 6), (key2459, 6), (key2459, -6), (key2520, -6), (key2520, -6), (key2364, -6)]

theorem rawRowCheck11983 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form11 = rawRow11983 := by decide +kernel

def row11983 : Integer.Sparse Key := [(key2364, -6), (key2456, 12), (key2520, -12), (key2531, 6)]

theorem rowCheck11983 : row11983 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11983 := by decide +kernel

theorem rowEval11983 (x : Key → ℝ) : Integer.Sparse.eval row11983 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form11) x := by
  rw [rowCheck11983, Integer.Sparse.eval_collectBalanced, rawRowCheck11983]

def rawRow11984 : Integer.Sparse Key := [(key2456, 6), (key2459, 6), (key2531, 6), (key2456, 6), (key2520, -6), (key2364, -6), (key2459, -6), (key2520, -6)]

theorem rawRowCheck11984 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form11 = rawRow11984 := by decide +kernel

def row11984 : Integer.Sparse Key := [(key2364, -6), (key2456, 12), (key2520, -12), (key2531, 6)]

theorem rowCheck11984 : row11984 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11984 := by decide +kernel

theorem rowEval11984 (x : Key → ℝ) : Integer.Sparse.eval row11984 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11984, Integer.Sparse.eval_collectBalanced, rawRowCheck11984]

def rawRow11985 : Integer.Sparse Key := [(key2459, 6), (key2456, 6), (key2531, 6), (key2456, 6), (key2520, -6), (key2364, -6), (key2520, -6), (key2459, -6)]

theorem rawRowCheck11985 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form11 = rawRow11985 := by decide +kernel

def row11985 : Integer.Sparse Key := [(key2364, -6), (key2456, 12), (key2520, -12), (key2531, 6)]

theorem rowCheck11985 : row11985 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11985 := by decide +kernel

theorem rowEval11985 (x : Key → ℝ) : Integer.Sparse.eval row11985 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck11985, Integer.Sparse.eval_collectBalanced, rawRowCheck11985]

def rawRow11986 : Integer.Sparse Key := [(key2456, 6), (key2531, 6), (key2459, 6), (key2456, 6), (key2520, -6), (key2459, -6), (key2364, -6), (key2520, -6)]

theorem rawRowCheck11986 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form11 = rawRow11986 := by decide +kernel

def row11986 : Integer.Sparse Key := [(key2364, -6), (key2456, 12), (key2520, -12), (key2531, 6)]

theorem rowCheck11986 : row11986 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11986 := by decide +kernel

theorem rowEval11986 (x : Key → ℝ) : Integer.Sparse.eval row11986 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11986, Integer.Sparse.eval_collectBalanced, rawRowCheck11986]

def rawRow11987 : Integer.Sparse Key := [(key2531, 6), (key2456, 6), (key2459, 6), (key2456, 6), (key2520, -6), (key2459, -6), (key2520, -6), (key2364, -6)]

theorem rawRowCheck11987 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form11 = rawRow11987 := by decide +kernel

def row11987 : Integer.Sparse Key := [(key2364, -6), (key2456, 12), (key2520, -12), (key2531, 6)]

theorem rowCheck11987 : row11987 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11987 := by decide +kernel

theorem rowEval11987 (x : Key → ℝ) : Integer.Sparse.eval row11987 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form11) x := by
  rw [rowCheck11987, Integer.Sparse.eval_collectBalanced, rawRowCheck11987]

def rawRow11988 : Integer.Sparse Key := [(key2459, 6), (key2531, 6), (key2456, 6), (key2456, 6), (key2520, -6), (key2520, -6), (key2364, -6), (key2459, -6)]

theorem rawRowCheck11988 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form11 = rawRow11988 := by decide +kernel

def row11988 : Integer.Sparse Key := [(key2364, -6), (key2456, 12), (key2520, -12), (key2531, 6)]

theorem rowCheck11988 : row11988 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11988 := by decide +kernel

theorem rowEval11988 (x : Key → ℝ) : Integer.Sparse.eval row11988 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck11988, Integer.Sparse.eval_collectBalanced, rawRowCheck11988]

def rawRow11989 : Integer.Sparse Key := [(key2531, 6), (key2459, 6), (key2456, 6), (key2456, 6), (key2520, -6), (key2520, -6), (key2459, -6), (key2364, -6)]

theorem rawRowCheck11989 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form11 = rawRow11989 := by decide +kernel

def row11989 : Integer.Sparse Key := [(key2364, -6), (key2456, 12), (key2520, -12), (key2531, 6)]

theorem rowCheck11989 : row11989 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11989 := by decide +kernel

theorem rowEval11989 (x : Key → ℝ) : Integer.Sparse.eval row11989 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form11) x := by
  rw [rowCheck11989, Integer.Sparse.eval_collectBalanced, rawRowCheck11989]

def rawRow11990 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2366, 6), (key2366, 6), (key2567, -6), (key2567, -6), (key2579, -6), (key2579, -6)]

theorem rawRowCheck11990 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form12 = rawRow11990 := by decide +kernel

def row11990 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2366, 12), (key2567, -12), (key2579, -12)]

theorem rowCheck11990 : row11990 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11990 := by decide +kernel

theorem rowEval11990 (x : Key → ℝ) : Integer.Sparse.eval row11990 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11990, Integer.Sparse.eval_collectBalanced, rawRowCheck11990]

def rawRow11991 : Integer.Sparse Key := [(key2357, 6), (key2363, 6), (key2361, 6), (key2366, 6), (key2567, -6), (key2579, -6), (key2567, -6), (key2579, -6)]

theorem rawRowCheck11991 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form12 = rawRow11991 := by decide +kernel

def row11991 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 6), (key2366, 6), (key2567, -12), (key2579, -12)]

theorem rowCheck11991 : row11991 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11991 := by decide +kernel

theorem rowEval11991 (x : Key → ℝ) : Integer.Sparse.eval row11991 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11991, Integer.Sparse.eval_collectBalanced, rawRowCheck11991]

def rawRow11992 : Integer.Sparse Key := [(key2363, 6), (key2357, 6), (key2361, 6), (key2366, 6), (key2567, -6), (key2579, -6), (key2579, -6), (key2567, -6)]

theorem rawRowCheck11992 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form12 = rawRow11992 := by decide +kernel

def row11992 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 6), (key2366, 6), (key2567, -12), (key2579, -12)]

theorem rowCheck11992 : row11992 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11992 := by decide +kernel

theorem rowEval11992 (x : Key → ℝ) : Integer.Sparse.eval row11992 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11992, Integer.Sparse.eval_collectBalanced, rawRowCheck11992]

def rawRow11993 : Integer.Sparse Key := [(key2357, 6), (key2363, 6), (key2363, 6), (key2361, 6), (key2579, -6), (key2567, -6), (key2567, -6), (key2579, -6)]

theorem rawRowCheck11993 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form12 = rawRow11993 := by decide +kernel

def row11993 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2567, -12), (key2579, -12)]

theorem rowCheck11993 : row11993 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11993 := by decide +kernel

theorem rowEval11993 (x : Key → ℝ) : Integer.Sparse.eval row11993 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11993, Integer.Sparse.eval_collectBalanced, rawRowCheck11993]

def rawRow11994 : Integer.Sparse Key := [(key2363, 6), (key2357, 6), (key2363, 6), (key2361, 6), (key2579, -6), (key2567, -6), (key2579, -6), (key2567, -6)]

theorem rawRowCheck11994 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form12 = rawRow11994 := by decide +kernel

def row11994 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2567, -12), (key2579, -12)]

theorem rowCheck11994 : row11994 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11994 := by decide +kernel

theorem rowEval11994 (x : Key → ℝ) : Integer.Sparse.eval row11994 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11994, Integer.Sparse.eval_collectBalanced, rawRowCheck11994]

def rawRow11995 : Integer.Sparse Key := [(key2363, 6), (key2363, 6), (key2357, 6), (key2361, 6), (key2579, -6), (key2579, -6), (key2567, -6), (key2567, -6)]

theorem rawRowCheck11995 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form12 = rawRow11995 := by decide +kernel

def row11995 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2567, -12), (key2579, -12)]

theorem rowCheck11995 : row11995 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11995 := by decide +kernel

theorem rowEval11995 (x : Key → ℝ) : Integer.Sparse.eval row11995 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11995, Integer.Sparse.eval_collectBalanced, rawRowCheck11995]

def rawRow11996 : Integer.Sparse Key := [(key2452, 6), (key2452, 6), (key2458, 6), (key2519, 6), (key2366, -6), (key2461, -6), (key2523, -6), (key2523, -6)]

theorem rawRowCheck11996 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form12 = rawRow11996 := by decide +kernel

def row11996 : Integer.Sparse Key := [(key2366, -6), (key2452, 12), (key2458, 6), (key2461, -6), (key2519, 6), (key2523, -12)]

theorem rowCheck11996 : row11996 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11996 := by decide +kernel

theorem rowEval11996 (x : Key → ℝ) : Integer.Sparse.eval row11996 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11996, Integer.Sparse.eval_collectBalanced, rawRowCheck11996]

def rawRow11997 : Integer.Sparse Key := [(key2452, 6), (key2458, 6), (key2452, 6), (key2519, 6), (key2366, -6), (key2523, -6), (key2461, -6), (key2523, -6)]

theorem rawRowCheck11997 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form12 = rawRow11997 := by decide +kernel

def row11997 : Integer.Sparse Key := [(key2366, -6), (key2452, 12), (key2458, 6), (key2461, -6), (key2519, 6), (key2523, -12)]

theorem rowCheck11997 : row11997 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11997 := by decide +kernel

theorem rowEval11997 (x : Key → ℝ) : Integer.Sparse.eval row11997 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11997, Integer.Sparse.eval_collectBalanced, rawRowCheck11997]

def rawRow11998 : Integer.Sparse Key := [(key2458, 6), (key2452, 6), (key2452, 6), (key2519, 6), (key2366, -6), (key2523, -6), (key2523, -6), (key2461, -6)]

theorem rawRowCheck11998 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form12 = rawRow11998 := by decide +kernel

def row11998 : Integer.Sparse Key := [(key2366, -6), (key2452, 12), (key2458, 6), (key2461, -6), (key2519, 6), (key2523, -12)]

theorem rowCheck11998 : row11998 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11998 := by decide +kernel

theorem rowEval11998 (x : Key → ℝ) : Integer.Sparse.eval row11998 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11998, Integer.Sparse.eval_collectBalanced, rawRowCheck11998]

def rawRow11999 : Integer.Sparse Key := [(key2452, 6), (key2452, 6), (key2519, 6), (key2458, 6), (key2461, -6), (key2366, -6), (key2523, -6), (key2523, -6)]

theorem rawRowCheck11999 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form12 = rawRow11999 := by decide +kernel

def row11999 : Integer.Sparse Key := [(key2366, -6), (key2452, 12), (key2458, 6), (key2461, -6), (key2519, 6), (key2523, -12)]

theorem rowCheck11999 : row11999 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11999 := by decide +kernel

theorem rowEval11999 (x : Key → ℝ) : Integer.Sparse.eval row11999 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11999, Integer.Sparse.eval_collectBalanced, rawRowCheck11999]

def rawRow12000 : Integer.Sparse Key := [(key2452, 6), (key2519, 6), (key2452, 6), (key2458, 6), (key2461, -6), (key2523, -6), (key2366, -6), (key2523, -6)]

theorem rawRowCheck12000 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form12 = rawRow12000 := by decide +kernel

def row12000 : Integer.Sparse Key := [(key2366, -6), (key2452, 12), (key2458, 6), (key2461, -6), (key2519, 6), (key2523, -12)]

theorem rowCheck12000 : row12000 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12000 := by decide +kernel

theorem rowEval12000 (x : Key → ℝ) : Integer.Sparse.eval row12000 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12000, Integer.Sparse.eval_collectBalanced, rawRowCheck12000]

def rawRow12001 : Integer.Sparse Key := [(key2519, 6), (key2452, 6), (key2452, 6), (key2458, 6), (key2461, -6), (key2523, -6), (key2523, -6), (key2366, -6)]

theorem rawRowCheck12001 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form12 = rawRow12001 := by decide +kernel

def row12001 : Integer.Sparse Key := [(key2366, -6), (key2452, 12), (key2458, 6), (key2461, -6), (key2519, 6), (key2523, -12)]

theorem rowCheck12001 : row12001 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12001 := by decide +kernel

theorem rowEval12001 (x : Key → ℝ) : Integer.Sparse.eval row12001 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form12) x := by
  rw [rowCheck12001, Integer.Sparse.eval_collectBalanced, rawRowCheck12001]

def rawRow12002 : Integer.Sparse Key := [(key2452, 6), (key2458, 6), (key2519, 6), (key2452, 6), (key2523, -6), (key2366, -6), (key2461, -6), (key2523, -6)]

theorem rawRowCheck12002 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form12 = rawRow12002 := by decide +kernel

def row12002 : Integer.Sparse Key := [(key2366, -6), (key2452, 12), (key2458, 6), (key2461, -6), (key2519, 6), (key2523, -12)]

theorem rowCheck12002 : row12002 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12002 := by decide +kernel

theorem rowEval12002 (x : Key → ℝ) : Integer.Sparse.eval row12002 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12002, Integer.Sparse.eval_collectBalanced, rawRowCheck12002]

def rawRow12003 : Integer.Sparse Key := [(key2458, 6), (key2452, 6), (key2519, 6), (key2452, 6), (key2523, -6), (key2366, -6), (key2523, -6), (key2461, -6)]

theorem rawRowCheck12003 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form12 = rawRow12003 := by decide +kernel

def row12003 : Integer.Sparse Key := [(key2366, -6), (key2452, 12), (key2458, 6), (key2461, -6), (key2519, 6), (key2523, -12)]

theorem rowCheck12003 : row12003 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12003 := by decide +kernel

theorem rowEval12003 (x : Key → ℝ) : Integer.Sparse.eval row12003 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck12003, Integer.Sparse.eval_collectBalanced, rawRowCheck12003]

def rawRow12004 : Integer.Sparse Key := [(key2452, 6), (key2519, 6), (key2458, 6), (key2452, 6), (key2523, -6), (key2461, -6), (key2366, -6), (key2523, -6)]

theorem rawRowCheck12004 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form12 = rawRow12004 := by decide +kernel

def row12004 : Integer.Sparse Key := [(key2366, -6), (key2452, 12), (key2458, 6), (key2461, -6), (key2519, 6), (key2523, -12)]

theorem rowCheck12004 : row12004 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12004 := by decide +kernel

theorem rowEval12004 (x : Key → ℝ) : Integer.Sparse.eval row12004 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12004, Integer.Sparse.eval_collectBalanced, rawRowCheck12004]

def rawRow12005 : Integer.Sparse Key := [(key2519, 6), (key2452, 6), (key2458, 6), (key2452, 6), (key2523, -6), (key2461, -6), (key2523, -6), (key2366, -6)]

theorem rawRowCheck12005 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form12 = rawRow12005 := by decide +kernel

def row12005 : Integer.Sparse Key := [(key2366, -6), (key2452, 12), (key2458, 6), (key2461, -6), (key2519, 6), (key2523, -12)]

theorem rowCheck12005 : row12005 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12005 := by decide +kernel

theorem rowEval12005 (x : Key → ℝ) : Integer.Sparse.eval row12005 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form12) x := by
  rw [rowCheck12005, Integer.Sparse.eval_collectBalanced, rawRowCheck12005]

def rawRow12006 : Integer.Sparse Key := [(key2458, 6), (key2519, 6), (key2452, 6), (key2452, 6), (key2523, -6), (key2523, -6), (key2366, -6), (key2461, -6)]

theorem rawRowCheck12006 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form12 = rawRow12006 := by decide +kernel

def row12006 : Integer.Sparse Key := [(key2366, -6), (key2452, 12), (key2458, 6), (key2461, -6), (key2519, 6), (key2523, -12)]

theorem rowCheck12006 : row12006 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12006 := by decide +kernel

theorem rowEval12006 (x : Key → ℝ) : Integer.Sparse.eval row12006 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck12006, Integer.Sparse.eval_collectBalanced, rawRowCheck12006]

def rawRow12007 : Integer.Sparse Key := [(key2519, 6), (key2458, 6), (key2452, 6), (key2452, 6), (key2523, -6), (key2523, -6), (key2461, -6), (key2366, -6)]

theorem rawRowCheck12007 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form12 = rawRow12007 := by decide +kernel

def row12007 : Integer.Sparse Key := [(key2366, -6), (key2452, 12), (key2458, 6), (key2461, -6), (key2519, 6), (key2523, -12)]

theorem rowCheck12007 : row12007 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12007 := by decide +kernel

theorem rowEval12007 (x : Key → ℝ) : Integer.Sparse.eval row12007 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form12) x := by
  rw [rowCheck12007, Integer.Sparse.eval_collectBalanced, rawRowCheck12007]

def rawRow12008 : Integer.Sparse Key := [(key1999, -6), (key1999, -6), (key2003, -6), (key2003, -6), (key2268, 2), (key2268, 2), (key2272, 2), (key2268, 2), (key2268, 2), (key2323, 2), (key2323, 2), (key2324, 2), (key2324, 2), (key2272, 2), (key2324, 2), (key2324, 2)]

theorem rawRowCheck12008 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form13 = rawRow12008 := by decide +kernel

def row12008 : Integer.Sparse Key := [(key1999, -12), (key2003, -12), (key2268, 8), (key2272, 4), (key2323, 4), (key2324, 8)]

theorem rowCheck12008 : row12008 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12008 := by decide +kernel

theorem rowEval12008 (x : Key → ℝ) : Integer.Sparse.eval row12008 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12008, Integer.Sparse.eval_collectBalanced, rawRowCheck12008]

def rawRow12009 : Integer.Sparse Key := [(key1999, -6), (key2003, -6), (key1999, -6), (key2003, -6), (key2268, 2), (key2272, 2), (key2268, 2), (key2323, 2), (key2324, 2), (key2268, 2), (key2324, 2), (key2268, 2), (key2323, 2), (key2324, 2), (key2272, 2), (key2324, 2)]

theorem rawRowCheck12009 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form13 = rawRow12009 := by decide +kernel

def row12009 : Integer.Sparse Key := [(key1999, -12), (key2003, -12), (key2268, 8), (key2272, 4), (key2323, 4), (key2324, 8)]

theorem rowCheck12009 : row12009 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12009 := by decide +kernel

theorem rowEval12009 (x : Key → ℝ) : Integer.Sparse.eval row12009 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12009, Integer.Sparse.eval_collectBalanced, rawRowCheck12009]

def rawRow12010 : Integer.Sparse Key := [(key2003, -6), (key1999, -6), (key1999, -6), (key2003, -6), (key2272, 2), (key2268, 2), (key2268, 2), (key2324, 2), (key2323, 2), (key2324, 2), (key2268, 2), (key2323, 2), (key2268, 2), (key2324, 2), (key2324, 2), (key2272, 2)]

theorem rawRowCheck12010 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form13 = rawRow12010 := by decide +kernel

def row12010 : Integer.Sparse Key := [(key1999, -12), (key2003, -12), (key2268, 8), (key2272, 4), (key2323, 4), (key2324, 8)]

theorem rowCheck12010 : row12010 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12010 := by decide +kernel

theorem rowEval12010 (x : Key → ℝ) : Integer.Sparse.eval row12010 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12010, Integer.Sparse.eval_collectBalanced, rawRowCheck12010]

def rawRow12011 : Integer.Sparse Key := [(key1999, -6), (key2003, -6), (key2003, -6), (key1999, -6), (key2323, 2), (key2324, 2), (key2324, 2), (key2268, 2), (key2272, 2), (key2268, 2), (key2324, 2), (key2272, 2), (key2324, 2), (key2268, 2), (key2268, 2), (key2323, 2)]

theorem rawRowCheck12011 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form13 = rawRow12011 := by decide +kernel

def row12011 : Integer.Sparse Key := [(key1999, -12), (key2003, -12), (key2268, 8), (key2272, 4), (key2323, 4), (key2324, 8)]

theorem rowCheck12011 : row12011 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12011 := by decide +kernel

theorem rowEval12011 (x : Key → ℝ) : Integer.Sparse.eval row12011 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12011, Integer.Sparse.eval_collectBalanced, rawRowCheck12011]

def rawRow12012 : Integer.Sparse Key := [(key2003, -6), (key1999, -6), (key2003, -6), (key1999, -6), (key2324, 2), (key2323, 2), (key2324, 2), (key2272, 2), (key2268, 2), (key2324, 2), (key2268, 2), (key2324, 2), (key2272, 2), (key2268, 2), (key2323, 2), (key2268, 2)]

theorem rawRowCheck12012 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form13 = rawRow12012 := by decide +kernel

def row12012 : Integer.Sparse Key := [(key1999, -12), (key2003, -12), (key2268, 8), (key2272, 4), (key2323, 4), (key2324, 8)]

theorem rowCheck12012 : row12012 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12012 := by decide +kernel

theorem rowEval12012 (x : Key → ℝ) : Integer.Sparse.eval row12012 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12012, Integer.Sparse.eval_collectBalanced, rawRowCheck12012]

def rawRow12013 : Integer.Sparse Key := [(key2003, -6), (key2003, -6), (key1999, -6), (key1999, -6), (key2324, 2), (key2324, 2), (key2323, 2), (key2324, 2), (key2324, 2), (key2272, 2), (key2272, 2), (key2268, 2), (key2268, 2), (key2323, 2), (key2268, 2), (key2268, 2)]

theorem rawRowCheck12013 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form13 = rawRow12013 := by decide +kernel

def row12013 : Integer.Sparse Key := [(key1999, -12), (key2003, -12), (key2268, 8), (key2272, 4), (key2323, 4), (key2324, 8)]

theorem rowCheck12013 : row12013 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12013 := by decide +kernel

theorem rowEval12013 (x : Key → ℝ) : Integer.Sparse.eval row12013 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12013, Integer.Sparse.eval_collectBalanced, rawRowCheck12013]

def rawRow12014 : Integer.Sparse Key := [(key2268, -6), (key2268, -6), (key2272, -6), (key2294, -6), (key1999, 2), (key1999, 2), (key2003, 2), (key2268, 2), (key2268, 2), (key2323, 2), (key2323, 2), (key2324, 2), (key2324, 2), (key2294, 2), (key2336, 2), (key2336, 2)]

theorem rawRowCheck12014 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form13 = rawRow12014 := by decide +kernel

def row12014 : Integer.Sparse Key := [(key1999, 4), (key2003, 2), (key2268, -8), (key2272, -6), (key2294, -4), (key2323, 4), (key2324, 4), (key2336, 4)]

theorem rowCheck12014 : row12014 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12014 := by decide +kernel

theorem rowEval12014 (x : Key → ℝ) : Integer.Sparse.eval row12014 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12014, Integer.Sparse.eval_collectBalanced, rawRowCheck12014]

def rawRow12015 : Integer.Sparse Key := [(key2268, -6), (key2272, -6), (key2268, -6), (key2294, -6), (key1999, 2), (key2003, 2), (key1999, 2), (key2323, 2), (key2324, 2), (key2268, 2), (key2324, 2), (key2268, 2), (key2323, 2), (key2336, 2), (key2294, 2), (key2336, 2)]

theorem rawRowCheck12015 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form13 = rawRow12015 := by decide +kernel

def row12015 : Integer.Sparse Key := [(key1999, 4), (key2003, 2), (key2268, -8), (key2272, -6), (key2294, -4), (key2323, 4), (key2324, 4), (key2336, 4)]

theorem rowCheck12015 : row12015 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12015 := by decide +kernel

theorem rowEval12015 (x : Key → ℝ) : Integer.Sparse.eval row12015 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12015, Integer.Sparse.eval_collectBalanced, rawRowCheck12015]

def rawRow12016 : Integer.Sparse Key := [(key2272, -6), (key2268, -6), (key2268, -6), (key2294, -6), (key2003, 2), (key1999, 2), (key1999, 2), (key2324, 2), (key2323, 2), (key2324, 2), (key2268, 2), (key2323, 2), (key2268, 2), (key2336, 2), (key2336, 2), (key2294, 2)]

theorem rawRowCheck12016 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form13 = rawRow12016 := by decide +kernel

def row12016 : Integer.Sparse Key := [(key1999, 4), (key2003, 2), (key2268, -8), (key2272, -6), (key2294, -4), (key2323, 4), (key2324, 4), (key2336, 4)]

theorem rowCheck12016 : row12016 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12016 := by decide +kernel

theorem rowEval12016 (x : Key → ℝ) : Integer.Sparse.eval row12016 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12016, Integer.Sparse.eval_collectBalanced, rawRowCheck12016]

def rawRow12017 : Integer.Sparse Key := [(key2268, -6), (key2268, -6), (key2294, -6), (key2272, -6), (key2268, 2), (key2268, 2), (key2294, 2), (key1999, 2), (key1999, 2), (key2323, 2), (key2323, 2), (key2336, 2), (key2336, 2), (key2003, 2), (key2324, 2), (key2324, 2)]

theorem rawRowCheck12017 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form13 = rawRow12017 := by decide +kernel

def row12017 : Integer.Sparse Key := [(key1999, 4), (key2003, 2), (key2268, -8), (key2272, -6), (key2294, -4), (key2323, 4), (key2324, 4), (key2336, 4)]

theorem rowCheck12017 : row12017 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12017 := by decide +kernel

theorem rowEval12017 (x : Key → ℝ) : Integer.Sparse.eval row12017 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12017, Integer.Sparse.eval_collectBalanced, rawRowCheck12017]

def rawRow12018 : Integer.Sparse Key := [(key2268, -6), (key2294, -6), (key2268, -6), (key2272, -6), (key2268, 2), (key2294, 2), (key2268, 2), (key2323, 2), (key2336, 2), (key1999, 2), (key2336, 2), (key1999, 2), (key2323, 2), (key2324, 2), (key2003, 2), (key2324, 2)]

theorem rawRowCheck12018 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form13 = rawRow12018 := by decide +kernel

def row12018 : Integer.Sparse Key := [(key1999, 4), (key2003, 2), (key2268, -8), (key2272, -6), (key2294, -4), (key2323, 4), (key2324, 4), (key2336, 4)]

theorem rowCheck12018 : row12018 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12018 := by decide +kernel

theorem rowEval12018 (x : Key → ℝ) : Integer.Sparse.eval row12018 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12018, Integer.Sparse.eval_collectBalanced, rawRowCheck12018]

def rawRow12019 : Integer.Sparse Key := [(key2294, -6), (key2268, -6), (key2268, -6), (key2272, -6), (key2294, 2), (key2268, 2), (key2268, 2), (key2336, 2), (key2323, 2), (key2336, 2), (key1999, 2), (key2323, 2), (key1999, 2), (key2324, 2), (key2324, 2), (key2003, 2)]

theorem rawRowCheck12019 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form13 = rawRow12019 := by decide +kernel

def row12019 : Integer.Sparse Key := [(key1999, 4), (key2003, 2), (key2268, -8), (key2272, -6), (key2294, -4), (key2323, 4), (key2324, 4), (key2336, 4)]

theorem rowCheck12019 : row12019 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12019 := by decide +kernel

theorem rowEval12019 (x : Key → ℝ) : Integer.Sparse.eval row12019 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form13) x := by
  rw [rowCheck12019, Integer.Sparse.eval_collectBalanced, rawRowCheck12019]

def rawRow12020 : Integer.Sparse Key := [(key2268, -6), (key2272, -6), (key2294, -6), (key2268, -6), (key2323, 2), (key2324, 2), (key2336, 2), (key1999, 2), (key2003, 2), (key2268, 2), (key2324, 2), (key2294, 2), (key2336, 2), (key1999, 2), (key2268, 2), (key2323, 2)]

theorem rawRowCheck12020 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form13 = rawRow12020 := by decide +kernel

def row12020 : Integer.Sparse Key := [(key1999, 4), (key2003, 2), (key2268, -8), (key2272, -6), (key2294, -4), (key2323, 4), (key2324, 4), (key2336, 4)]

theorem rowCheck12020 : row12020 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12020 := by decide +kernel

theorem rowEval12020 (x : Key → ℝ) : Integer.Sparse.eval row12020 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12020, Integer.Sparse.eval_collectBalanced, rawRowCheck12020]

def rawRow12021 : Integer.Sparse Key := [(key2272, -6), (key2268, -6), (key2294, -6), (key2268, -6), (key2324, 2), (key2323, 2), (key2336, 2), (key2003, 2), (key1999, 2), (key2324, 2), (key2268, 2), (key2336, 2), (key2294, 2), (key1999, 2), (key2323, 2), (key2268, 2)]

theorem rawRowCheck12021 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form13 = rawRow12021 := by decide +kernel

def row12021 : Integer.Sparse Key := [(key1999, 4), (key2003, 2), (key2268, -8), (key2272, -6), (key2294, -4), (key2323, 4), (key2324, 4), (key2336, 4)]

theorem rowCheck12021 : row12021 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12021 := by decide +kernel

theorem rowEval12021 (x : Key → ℝ) : Integer.Sparse.eval row12021 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12021, Integer.Sparse.eval_collectBalanced, rawRowCheck12021]

def rawRow12022 : Integer.Sparse Key := [(key2268, -6), (key2294, -6), (key2272, -6), (key2268, -6), (key2323, 2), (key2336, 2), (key2324, 2), (key2268, 2), (key2294, 2), (key1999, 2), (key2336, 2), (key2003, 2), (key2324, 2), (key2268, 2), (key1999, 2), (key2323, 2)]

theorem rawRowCheck12022 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form13 = rawRow12022 := by decide +kernel

def row12022 : Integer.Sparse Key := [(key1999, 4), (key2003, 2), (key2268, -8), (key2272, -6), (key2294, -4), (key2323, 4), (key2324, 4), (key2336, 4)]

theorem rowCheck12022 : row12022 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12022 := by decide +kernel

theorem rowEval12022 (x : Key → ℝ) : Integer.Sparse.eval row12022 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12022, Integer.Sparse.eval_collectBalanced, rawRowCheck12022]

def rawRow12023 : Integer.Sparse Key := [(key2294, -6), (key2268, -6), (key2272, -6), (key2268, -6), (key2336, 2), (key2323, 2), (key2324, 2), (key2294, 2), (key2268, 2), (key2336, 2), (key1999, 2), (key2324, 2), (key2003, 2), (key2268, 2), (key2323, 2), (key1999, 2)]

theorem rawRowCheck12023 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form13 = rawRow12023 := by decide +kernel

def row12023 : Integer.Sparse Key := [(key1999, 4), (key2003, 2), (key2268, -8), (key2272, -6), (key2294, -4), (key2323, 4), (key2324, 4), (key2336, 4)]

theorem rowCheck12023 : row12023 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12023 := by decide +kernel

theorem rowEval12023 (x : Key → ℝ) : Integer.Sparse.eval row12023 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form13) x := by
  rw [rowCheck12023, Integer.Sparse.eval_collectBalanced, rawRowCheck12023]

def rawRow12024 : Integer.Sparse Key := [(key2272, -6), (key2294, -6), (key2268, -6), (key2268, -6), (key2324, 2), (key2336, 2), (key2323, 2), (key2324, 2), (key2336, 2), (key2003, 2), (key2294, 2), (key1999, 2), (key2268, 2), (key2323, 2), (key1999, 2), (key2268, 2)]

theorem rawRowCheck12024 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form13 = rawRow12024 := by decide +kernel

def row12024 : Integer.Sparse Key := [(key1999, 4), (key2003, 2), (key2268, -8), (key2272, -6), (key2294, -4), (key2323, 4), (key2324, 4), (key2336, 4)]

theorem rowCheck12024 : row12024 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12024 := by decide +kernel

theorem rowEval12024 (x : Key → ℝ) : Integer.Sparse.eval row12024 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12024, Integer.Sparse.eval_collectBalanced, rawRowCheck12024]

def rawRow12025 : Integer.Sparse Key := [(key2294, -6), (key2272, -6), (key2268, -6), (key2268, -6), (key2336, 2), (key2324, 2), (key2323, 2), (key2336, 2), (key2324, 2), (key2294, 2), (key2003, 2), (key2268, 2), (key1999, 2), (key2323, 2), (key2268, 2), (key1999, 2)]

theorem rawRowCheck12025 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form13 = rawRow12025 := by decide +kernel

def row12025 : Integer.Sparse Key := [(key1999, 4), (key2003, 2), (key2268, -8), (key2272, -6), (key2294, -4), (key2323, 4), (key2324, 4), (key2336, 4)]

theorem rowCheck12025 : row12025 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12025 := by decide +kernel

theorem rowEval12025 (x : Key → ℝ) : Integer.Sparse.eval row12025 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form13) x := by
  rw [rowCheck12025, Integer.Sparse.eval_collectBalanced, rawRowCheck12025]

def rawRow12026 : Integer.Sparse Key := [(key976, 6), (key976, 6), (key984, 6), (key984, 6), (key1169, -6), (key1169, -6), (key1220, -6), (key1220, -6)]

theorem rawRowCheck12026 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form14 = rawRow12026 := by decide +kernel

def row12026 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1169, -12), (key1220, -12)]

theorem rowCheck12026 : row12026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12026 := by decide +kernel

theorem rowEval12026 (x : Key → ℝ) : Integer.Sparse.eval row12026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12026, Integer.Sparse.eval_collectBalanced, rawRowCheck12026]

def rawRow12027 : Integer.Sparse Key := [(key976, 6), (key984, 6), (key976, 6), (key984, 6), (key1169, -6), (key1220, -6), (key1169, -6), (key1220, -6)]

theorem rawRowCheck12027 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form14 = rawRow12027 := by decide +kernel

def row12027 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1169, -12), (key1220, -12)]

theorem rowCheck12027 : row12027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12027 := by decide +kernel

theorem rowEval12027 (x : Key → ℝ) : Integer.Sparse.eval row12027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12027, Integer.Sparse.eval_collectBalanced, rawRowCheck12027]

def rawRow12028 : Integer.Sparse Key := [(key984, 6), (key976, 6), (key976, 6), (key984, 6), (key1169, -6), (key1220, -6), (key1220, -6), (key1169, -6)]

theorem rawRowCheck12028 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form14 = rawRow12028 := by decide +kernel

def row12028 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1169, -12), (key1220, -12)]

theorem rowCheck12028 : row12028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12028 := by decide +kernel

theorem rowEval12028 (x : Key → ℝ) : Integer.Sparse.eval row12028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12028, Integer.Sparse.eval_collectBalanced, rawRowCheck12028]

def rawRow12029 : Integer.Sparse Key := [(key976, 6), (key984, 6), (key984, 6), (key976, 6), (key1220, -6), (key1169, -6), (key1169, -6), (key1220, -6)]

theorem rawRowCheck12029 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form14 = rawRow12029 := by decide +kernel

def row12029 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1169, -12), (key1220, -12)]

theorem rowCheck12029 : row12029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12029 := by decide +kernel

theorem rowEval12029 (x : Key → ℝ) : Integer.Sparse.eval row12029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12029, Integer.Sparse.eval_collectBalanced, rawRowCheck12029]

def rawRow12030 : Integer.Sparse Key := [(key984, 6), (key976, 6), (key984, 6), (key976, 6), (key1220, -6), (key1169, -6), (key1220, -6), (key1169, -6)]

theorem rawRowCheck12030 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form14 = rawRow12030 := by decide +kernel

def row12030 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1169, -12), (key1220, -12)]

theorem rowCheck12030 : row12030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12030 := by decide +kernel

theorem rowEval12030 (x : Key → ℝ) : Integer.Sparse.eval row12030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12030, Integer.Sparse.eval_collectBalanced, rawRowCheck12030]

def rawRow12031 : Integer.Sparse Key := [(key984, 6), (key984, 6), (key976, 6), (key976, 6), (key1220, -6), (key1220, -6), (key1169, -6), (key1169, -6)]

theorem rawRowCheck12031 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form14 = rawRow12031 := by decide +kernel

def row12031 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1169, -12), (key1220, -12)]

theorem rowCheck12031 : row12031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12031 := by decide +kernel

theorem rowEval12031 (x : Key → ℝ) : Integer.Sparse.eval row12031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12031, Integer.Sparse.eval_collectBalanced, rawRowCheck12031]

end MUB6.Certificate.GramRows

end OAI
