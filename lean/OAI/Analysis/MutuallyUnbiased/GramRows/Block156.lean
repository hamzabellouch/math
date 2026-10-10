import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block6
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block16
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block17
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow16896 : Integer.Sparse Key := [(key2058, -1), (key2063, -1), (key2240, -1), (key2253, -1), (key2276, -1), (key2287, -1), (key2079, 2), (key2276, 2), (key2287, 2), (key2028, -1), (key2033, -1), (key2147, -1), (key2166, -1), (key2176, -1), (key2187, -1), (key2058, 2), (key2069, 2), (key2147, 2), (key2166, 2), (key2279, 2), (key2287, 2), (key2079, -1), (key2085, -1), (key2176, -1), (key2187, -1), (key2279, -1), (key2287, -1), (key2033, 2), (key2152, 2), (key2166, 2), (key2063, -1), (key2069, -1), (key2152, -1), (key2166, -1), (key2246, -1), (key2253, -1)]

theorem rawRowCheck16896 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form10 = rawRow16896 := by decide +kernel

def row16896 : Integer.Sparse Key := [(key2028, -1), (key2033, 1), (key2058, 1), (key2063, -2), (key2069, 1), (key2079, 1), (key2085, -1), (key2147, 1), (key2152, 1), (key2166, 2), (key2176, -2), (key2187, -2), (key2240, -1), (key2246, -1), (key2253, -2), (key2276, 1), (key2279, 1), (key2287, 2)]

theorem rowCheck16896 : row16896 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16896 := by decide +kernel

theorem rowEval16896 (x : Key → ℝ) : Integer.Sparse.eval row16896 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form10) x := by
  rw [rowCheck16896, Integer.Sparse.eval_collectBalanced, rawRowCheck16896]

def rawRow16897 : Integer.Sparse Key := [(key2063, -1), (key2058, -1), (key2253, -1), (key2240, -1), (key2287, -1), (key2276, -1), (key2079, 2), (key2287, 2), (key2276, 2), (key2033, -1), (key2028, -1), (key2166, -1), (key2147, -1), (key2187, -1), (key2176, -1), (key2069, 2), (key2058, 2), (key2166, 2), (key2147, 2), (key2287, 2), (key2279, 2), (key2085, -1), (key2079, -1), (key2187, -1), (key2176, -1), (key2287, -1), (key2279, -1), (key2033, 2), (key2166, 2), (key2152, 2), (key2069, -1), (key2063, -1), (key2166, -1), (key2152, -1), (key2253, -1), (key2246, -1)]

theorem rawRowCheck16897 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form10 = rawRow16897 := by decide +kernel

def row16897 : Integer.Sparse Key := [(key2028, -1), (key2033, 1), (key2058, 1), (key2063, -2), (key2069, 1), (key2079, 1), (key2085, -1), (key2147, 1), (key2152, 1), (key2166, 2), (key2176, -2), (key2187, -2), (key2240, -1), (key2246, -1), (key2253, -2), (key2276, 1), (key2279, 1), (key2287, 2)]

theorem rowCheck16897 : row16897 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16897 := by decide +kernel

theorem rowEval16897 (x : Key → ℝ) : Integer.Sparse.eval row16897 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck16897, Integer.Sparse.eval_collectBalanced, rawRowCheck16897]

def rawRow16898 : Integer.Sparse Key := [(key2240, -1), (key2276, -1), (key2058, -1), (key2287, -1), (key2063, -1), (key2253, -1), (key2276, 2), (key2079, 2), (key2287, 2), (key2147, -1), (key2176, -1), (key2028, -1), (key2187, -1), (key2033, -1), (key2166, -1), (key2147, 2), (key2279, 2), (key2058, 2), (key2287, 2), (key2069, 2), (key2166, 2), (key2176, -1), (key2279, -1), (key2079, -1), (key2287, -1), (key2085, -1), (key2187, -1), (key2152, 2), (key2033, 2), (key2166, 2), (key2152, -1), (key2246, -1), (key2063, -1), (key2253, -1), (key2069, -1), (key2166, -1)]

theorem rawRowCheck16898 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form10 = rawRow16898 := by decide +kernel

def row16898 : Integer.Sparse Key := [(key2028, -1), (key2033, 1), (key2058, 1), (key2063, -2), (key2069, 1), (key2079, 1), (key2085, -1), (key2147, 1), (key2152, 1), (key2166, 2), (key2176, -2), (key2187, -2), (key2240, -1), (key2246, -1), (key2253, -2), (key2276, 1), (key2279, 1), (key2287, 2)]

theorem rowCheck16898 : row16898 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16898 := by decide +kernel

theorem rowEval16898 (x : Key → ℝ) : Integer.Sparse.eval row16898 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form10) x := by
  rw [rowCheck16898, Integer.Sparse.eval_collectBalanced, rawRowCheck16898]

def rawRow16899 : Integer.Sparse Key := [(key2276, -1), (key2240, -1), (key2287, -1), (key2058, -1), (key2253, -1), (key2063, -1), (key2276, 2), (key2287, 2), (key2079, 2), (key2176, -1), (key2147, -1), (key2187, -1), (key2028, -1), (key2166, -1), (key2033, -1), (key2279, 2), (key2147, 2), (key2287, 2), (key2058, 2), (key2166, 2), (key2069, 2), (key2279, -1), (key2176, -1), (key2287, -1), (key2079, -1), (key2187, -1), (key2085, -1), (key2152, 2), (key2166, 2), (key2033, 2), (key2246, -1), (key2152, -1), (key2253, -1), (key2063, -1), (key2166, -1), (key2069, -1)]

theorem rawRowCheck16899 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form10 = rawRow16899 := by decide +kernel

def row16899 : Integer.Sparse Key := [(key2028, -1), (key2033, 1), (key2058, 1), (key2063, -2), (key2069, 1), (key2079, 1), (key2085, -1), (key2147, 1), (key2152, 1), (key2166, 2), (key2176, -2), (key2187, -2), (key2240, -1), (key2246, -1), (key2253, -2), (key2276, 1), (key2279, 1), (key2287, 2)]

theorem rowCheck16899 : row16899 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16899 := by decide +kernel

theorem rowEval16899 (x : Key → ℝ) : Integer.Sparse.eval row16899 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck16899, Integer.Sparse.eval_collectBalanced, rawRowCheck16899]

def rawRow16900 : Integer.Sparse Key := [(key2253, -1), (key2287, -1), (key2063, -1), (key2276, -1), (key2058, -1), (key2240, -1), (key2287, 2), (key2079, 2), (key2276, 2), (key2166, -1), (key2187, -1), (key2033, -1), (key2176, -1), (key2028, -1), (key2147, -1), (key2166, 2), (key2287, 2), (key2069, 2), (key2279, 2), (key2058, 2), (key2147, 2), (key2187, -1), (key2287, -1), (key2085, -1), (key2279, -1), (key2079, -1), (key2176, -1), (key2166, 2), (key2033, 2), (key2152, 2), (key2166, -1), (key2253, -1), (key2069, -1), (key2246, -1), (key2063, -1), (key2152, -1)]

theorem rawRowCheck16900 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form10 = rawRow16900 := by decide +kernel

def row16900 : Integer.Sparse Key := [(key2028, -1), (key2033, 1), (key2058, 1), (key2063, -2), (key2069, 1), (key2079, 1), (key2085, -1), (key2147, 1), (key2152, 1), (key2166, 2), (key2176, -2), (key2187, -2), (key2240, -1), (key2246, -1), (key2253, -2), (key2276, 1), (key2279, 1), (key2287, 2)]

theorem rowCheck16900 : row16900 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16900 := by decide +kernel

theorem rowEval16900 (x : Key → ℝ) : Integer.Sparse.eval row16900 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck16900, Integer.Sparse.eval_collectBalanced, rawRowCheck16900]

def rawRow16901 : Integer.Sparse Key := [(key2287, -1), (key2253, -1), (key2276, -1), (key2063, -1), (key2240, -1), (key2058, -1), (key2287, 2), (key2276, 2), (key2079, 2), (key2187, -1), (key2166, -1), (key2176, -1), (key2033, -1), (key2147, -1), (key2028, -1), (key2287, 2), (key2166, 2), (key2279, 2), (key2069, 2), (key2147, 2), (key2058, 2), (key2287, -1), (key2187, -1), (key2279, -1), (key2085, -1), (key2176, -1), (key2079, -1), (key2166, 2), (key2152, 2), (key2033, 2), (key2253, -1), (key2166, -1), (key2246, -1), (key2069, -1), (key2152, -1), (key2063, -1)]

theorem rawRowCheck16901 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form10 = rawRow16901 := by decide +kernel

def row16901 : Integer.Sparse Key := [(key2028, -1), (key2033, 1), (key2058, 1), (key2063, -2), (key2069, 1), (key2079, 1), (key2085, -1), (key2147, 1), (key2152, 1), (key2166, 2), (key2176, -2), (key2187, -2), (key2240, -1), (key2246, -1), (key2253, -2), (key2276, 1), (key2279, 1), (key2287, 2)]

theorem rowCheck16901 : row16901 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16901 := by decide +kernel

theorem rowEval16901 (x : Key → ℝ) : Integer.Sparse.eval row16901 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck16901, Integer.Sparse.eval_collectBalanced, rawRowCheck16901]

def rawRow16902 : Integer.Sparse Key := [(key2058, -1), (key2079, -1), (key2058, -1), (key2287, -1), (key2079, -1), (key2287, -1), (key2063, 2), (key2063, 2), (key2253, 2), (key2058, -1), (key2079, -1), (key2058, -1), (key2287, -1), (key2079, -1), (key2287, -1), (key2028, 2), (key2085, 2), (key2028, 2), (key2187, 2), (key2085, 2), (key2187, 2), (key2033, -1), (key2069, -1), (key2033, -1), (key2166, -1), (key2069, -1), (key2166, -1), (key2063, 2), (key2063, 2), (key2253, 2), (key2033, -1), (key2069, -1), (key2033, -1), (key2166, -1), (key2069, -1), (key2166, -1)]

theorem rawRowCheck16902 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form10 = rawRow16902 := by decide +kernel

def row16902 : Integer.Sparse Key := [(key2028, 4), (key2033, -4), (key2058, -4), (key2063, 8), (key2069, -4), (key2079, -4), (key2085, 4), (key2166, -4), (key2187, 4), (key2253, 4), (key2287, -4)]

theorem rowCheck16902 : row16902 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16902 := by decide +kernel

theorem rowEval16902 (x : Key → ℝ) : Integer.Sparse.eval row16902 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form10) x := by
  rw [rowCheck16902, Integer.Sparse.eval_collectBalanced, rawRowCheck16902]

def rawRow16903 : Integer.Sparse Key := [(key2079, -1), (key2058, -1), (key2287, -1), (key2058, -1), (key2287, -1), (key2079, -1), (key2063, 2), (key2253, 2), (key2063, 2), (key2079, -1), (key2058, -1), (key2287, -1), (key2058, -1), (key2287, -1), (key2079, -1), (key2085, 2), (key2028, 2), (key2187, 2), (key2028, 2), (key2187, 2), (key2085, 2), (key2069, -1), (key2033, -1), (key2166, -1), (key2033, -1), (key2166, -1), (key2069, -1), (key2063, 2), (key2253, 2), (key2063, 2), (key2069, -1), (key2033, -1), (key2166, -1), (key2033, -1), (key2166, -1), (key2069, -1)]

theorem rawRowCheck16903 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form10 = rawRow16903 := by decide +kernel

def row16903 : Integer.Sparse Key := [(key2028, 4), (key2033, -4), (key2058, -4), (key2063, 8), (key2069, -4), (key2079, -4), (key2085, 4), (key2166, -4), (key2187, 4), (key2253, 4), (key2287, -4)]

theorem rowCheck16903 : row16903 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16903 := by decide +kernel

theorem rowEval16903 (x : Key → ℝ) : Integer.Sparse.eval row16903 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck16903, Integer.Sparse.eval_collectBalanced, rawRowCheck16903]

def rawRow16904 : Integer.Sparse Key := [(key2287, -1), (key2287, -1), (key2079, -1), (key2079, -1), (key2058, -1), (key2058, -1), (key2253, 2), (key2063, 2), (key2063, 2), (key2287, -1), (key2287, -1), (key2079, -1), (key2079, -1), (key2058, -1), (key2058, -1), (key2187, 2), (key2187, 2), (key2085, 2), (key2085, 2), (key2028, 2), (key2028, 2), (key2166, -1), (key2166, -1), (key2069, -1), (key2069, -1), (key2033, -1), (key2033, -1), (key2253, 2), (key2063, 2), (key2063, 2), (key2166, -1), (key2166, -1), (key2069, -1), (key2069, -1), (key2033, -1), (key2033, -1)]

theorem rawRowCheck16904 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form10 = rawRow16904 := by decide +kernel

def row16904 : Integer.Sparse Key := [(key2028, 4), (key2033, -4), (key2058, -4), (key2063, 8), (key2069, -4), (key2079, -4), (key2085, 4), (key2166, -4), (key2187, 4), (key2253, 4), (key2287, -4)]

theorem rowCheck16904 : row16904 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16904 := by decide +kernel

theorem rowEval16904 (x : Key → ℝ) : Integer.Sparse.eval row16904 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck16904, Integer.Sparse.eval_collectBalanced, rawRowCheck16904]

def rawRow16905 : Integer.Sparse Key := [(key360, -2), (key362, -2), (key362, -2), (key366, 6), (key731, -2), (key733, -2), (key733, -2), (key865, 2), (key867, 2), (key865, 2), (key881, 2), (key867, 2), (key881, 2), (key927, -2), (key927, -2), (key938, -2), (key750, 6), (key927, -2), (key927, -2), (key938, -2)]

theorem rawRowCheck16905 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form11 = rawRow16905 := by decide +kernel

def row16905 : Integer.Sparse Key := [(key360, -2), (key362, -4), (key366, 6), (key731, -2), (key733, -4), (key750, 6), (key865, 4), (key867, 4), (key881, 4), (key927, -8), (key938, -4)]

theorem rowCheck16905 : row16905 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16905 := by decide +kernel

theorem rowEval16905 (x : Key → ℝ) : Integer.Sparse.eval row16905 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form11) x := by
  rw [rowCheck16905, Integer.Sparse.eval_collectBalanced, rawRowCheck16905]

def rawRow16906 : Integer.Sparse Key := [(key362, -2), (key360, -2), (key362, -2), (key366, 6), (key733, -2), (key731, -2), (key733, -2), (key867, 2), (key865, 2), (key881, 2), (key865, 2), (key881, 2), (key867, 2), (key927, -2), (key938, -2), (key927, -2), (key750, 6), (key927, -2), (key938, -2), (key927, -2)]

theorem rawRowCheck16906 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form11 = rawRow16906 := by decide +kernel

def row16906 : Integer.Sparse Key := [(key360, -2), (key362, -4), (key366, 6), (key731, -2), (key733, -4), (key750, 6), (key865, 4), (key867, 4), (key881, 4), (key927, -8), (key938, -4)]

theorem rowCheck16906 : row16906 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16906 := by decide +kernel

theorem rowEval16906 (x : Key → ℝ) : Integer.Sparse.eval row16906 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck16906, Integer.Sparse.eval_collectBalanced, rawRowCheck16906]

def rawRow16907 : Integer.Sparse Key := [(key362, -2), (key362, -2), (key360, -2), (key366, 6), (key733, -2), (key733, -2), (key731, -2), (key881, 2), (key881, 2), (key867, 2), (key867, 2), (key865, 2), (key865, 2), (key938, -2), (key927, -2), (key927, -2), (key750, 6), (key938, -2), (key927, -2), (key927, -2)]

theorem rawRowCheck16907 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form11 = rawRow16907 := by decide +kernel

def row16907 : Integer.Sparse Key := [(key360, -2), (key362, -4), (key366, 6), (key731, -2), (key733, -4), (key750, 6), (key865, 4), (key867, 4), (key881, 4), (key927, -8), (key938, -4)]

theorem rowCheck16907 : row16907 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16907 := by decide +kernel

theorem rowEval16907 (x : Key → ℝ) : Integer.Sparse.eval row16907 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck16907, Integer.Sparse.eval_collectBalanced, rawRowCheck16907]

def rawRow16908 : Integer.Sparse Key := [(key360, -2), (key362, -2), (key366, -2), (key362, 6), (key865, -2), (key867, -2), (key927, -2), (key731, 2), (key733, 2), (key865, 2), (key881, 2), (key927, 2), (key938, 2), (key733, -2), (key867, -2), (key881, -2), (key927, 6), (key750, -2), (key927, -2), (key938, -2)]

theorem rawRowCheck16908 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form11 = rawRow16908 := by decide +kernel

def row16908 : Integer.Sparse Key := [(key360, -2), (key362, 4), (key366, -2), (key731, 2), (key750, -2), (key867, -4), (key927, 4)]

theorem rowCheck16908 : row16908 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16908 := by decide +kernel

theorem rowEval16908 (x : Key → ℝ) : Integer.Sparse.eval row16908 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form11) x := by
  rw [rowCheck16908, Integer.Sparse.eval_collectBalanced, rawRowCheck16908]

def rawRow16909 : Integer.Sparse Key := [(key362, -2), (key360, -2), (key366, -2), (key362, 6), (key867, -2), (key865, -2), (key927, -2), (key733, 2), (key731, 2), (key881, 2), (key865, 2), (key938, 2), (key927, 2), (key733, -2), (key881, -2), (key867, -2), (key927, 6), (key750, -2), (key938, -2), (key927, -2)]

theorem rawRowCheck16909 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form11 = rawRow16909 := by decide +kernel

def row16909 : Integer.Sparse Key := [(key360, -2), (key362, 4), (key366, -2), (key731, 2), (key750, -2), (key867, -4), (key927, 4)]

theorem rowCheck16909 : row16909 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16909 := by decide +kernel

theorem rowEval16909 (x : Key → ℝ) : Integer.Sparse.eval row16909 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck16909, Integer.Sparse.eval_collectBalanced, rawRowCheck16909]

def rawRow16910 : Integer.Sparse Key := [(key360, -2), (key366, -2), (key362, -2), (key362, 6), (key865, -2), (key927, -2), (key867, -2), (key865, 2), (key927, 2), (key731, 2), (key938, 2), (key733, 2), (key881, 2), (key867, -2), (key733, -2), (key881, -2), (key927, 6), (key927, -2), (key750, -2), (key938, -2)]

theorem rawRowCheck16910 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form11 = rawRow16910 := by decide +kernel

def row16910 : Integer.Sparse Key := [(key360, -2), (key362, 4), (key366, -2), (key731, 2), (key750, -2), (key867, -4), (key927, 4)]

theorem rowCheck16910 : row16910 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16910 := by decide +kernel

theorem rowEval16910 (x : Key → ℝ) : Integer.Sparse.eval row16910 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form11) x := by
  rw [rowCheck16910, Integer.Sparse.eval_collectBalanced, rawRowCheck16910]

def rawRow16911 : Integer.Sparse Key := [(key366, -2), (key360, -2), (key362, -2), (key362, 6), (key927, -2), (key865, -2), (key867, -2), (key927, 2), (key865, 2), (key938, 2), (key731, 2), (key881, 2), (key733, 2), (key867, -2), (key881, -2), (key733, -2), (key927, 6), (key927, -2), (key938, -2), (key750, -2)]

theorem rawRowCheck16911 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form11 = rawRow16911 := by decide +kernel

def row16911 : Integer.Sparse Key := [(key360, -2), (key362, 4), (key366, -2), (key731, 2), (key750, -2), (key867, -4), (key927, 4)]

theorem rowCheck16911 : row16911 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16911 := by decide +kernel

theorem rowEval16911 (x : Key → ℝ) : Integer.Sparse.eval row16911 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck16911, Integer.Sparse.eval_collectBalanced, rawRowCheck16911]

def rawRow16912 : Integer.Sparse Key := [(key362, -2), (key366, -2), (key360, -2), (key362, 6), (key867, -2), (key927, -2), (key865, -2), (key881, 2), (key938, 2), (key733, 2), (key927, 2), (key731, 2), (key865, 2), (key881, -2), (key733, -2), (key867, -2), (key927, 6), (key938, -2), (key750, -2), (key927, -2)]

theorem rawRowCheck16912 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form11 = rawRow16912 := by decide +kernel

def row16912 : Integer.Sparse Key := [(key360, -2), (key362, 4), (key366, -2), (key731, 2), (key750, -2), (key867, -4), (key927, 4)]

theorem rowCheck16912 : row16912 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16912 := by decide +kernel

theorem rowEval16912 (x : Key → ℝ) : Integer.Sparse.eval row16912 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck16912, Integer.Sparse.eval_collectBalanced, rawRowCheck16912]

def rawRow16913 : Integer.Sparse Key := [(key366, -2), (key362, -2), (key360, -2), (key362, 6), (key927, -2), (key867, -2), (key865, -2), (key938, 2), (key881, 2), (key927, 2), (key733, 2), (key865, 2), (key731, 2), (key881, -2), (key867, -2), (key733, -2), (key927, 6), (key938, -2), (key927, -2), (key750, -2)]

theorem rawRowCheck16913 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form11 = rawRow16913 := by decide +kernel

def row16913 : Integer.Sparse Key := [(key360, -2), (key362, 4), (key366, -2), (key731, 2), (key750, -2), (key867, -4), (key927, 4)]

theorem rowCheck16913 : row16913 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16913 := by decide +kernel

theorem rowEval16913 (x : Key → ℝ) : Integer.Sparse.eval row16913 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck16913, Integer.Sparse.eval_collectBalanced, rawRowCheck16913]

def rawRow16914 : Integer.Sparse Key := [(key529, -2), (key531, -2), (key537, -2), (key537, 6), (key360, -2), (key362, -2), (key366, -2), (key731, 2), (key733, 2), (key865, 2), (key881, 2), (key927, 2), (key938, 2), (key750, -2), (key927, -2), (key938, -2), (key733, 6), (key733, -2), (key867, -2), (key881, -2)]

theorem rawRowCheck16914 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form11 = rawRow16914 := by decide +kernel

def row16914 : Integer.Sparse Key := [(key360, -2), (key362, -2), (key366, -2), (key529, -2), (key531, -2), (key537, 4), (key731, 2), (key733, 6), (key750, -2), (key865, 2), (key867, -2)]

theorem rowCheck16914 : row16914 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16914 := by decide +kernel

theorem rowEval16914 (x : Key → ℝ) : Integer.Sparse.eval row16914 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form11) x := by
  rw [rowCheck16914, Integer.Sparse.eval_collectBalanced, rawRowCheck16914]

def rawRow16915 : Integer.Sparse Key := [(key531, -2), (key529, -2), (key537, -2), (key537, 6), (key362, -2), (key360, -2), (key366, -2), (key733, 2), (key731, 2), (key881, 2), (key865, 2), (key938, 2), (key927, 2), (key750, -2), (key938, -2), (key927, -2), (key733, 6), (key733, -2), (key881, -2), (key867, -2)]

theorem rawRowCheck16915 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form11 = rawRow16915 := by decide +kernel

def row16915 : Integer.Sparse Key := [(key360, -2), (key362, -2), (key366, -2), (key529, -2), (key531, -2), (key537, 4), (key731, 2), (key733, 6), (key750, -2), (key865, 2), (key867, -2)]

theorem rowCheck16915 : row16915 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16915 := by decide +kernel

theorem rowEval16915 (x : Key → ℝ) : Integer.Sparse.eval row16915 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck16915, Integer.Sparse.eval_collectBalanced, rawRowCheck16915]

def rawRow16916 : Integer.Sparse Key := [(key529, -2), (key537, -2), (key531, -2), (key537, 6), (key360, -2), (key366, -2), (key362, -2), (key865, 2), (key927, 2), (key731, 2), (key938, 2), (key733, 2), (key881, 2), (key927, -2), (key750, -2), (key938, -2), (key733, 6), (key867, -2), (key733, -2), (key881, -2)]

theorem rawRowCheck16916 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form11 = rawRow16916 := by decide +kernel

def row16916 : Integer.Sparse Key := [(key360, -2), (key362, -2), (key366, -2), (key529, -2), (key531, -2), (key537, 4), (key731, 2), (key733, 6), (key750, -2), (key865, 2), (key867, -2)]

theorem rowCheck16916 : row16916 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16916 := by decide +kernel

theorem rowEval16916 (x : Key → ℝ) : Integer.Sparse.eval row16916 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form11) x := by
  rw [rowCheck16916, Integer.Sparse.eval_collectBalanced, rawRowCheck16916]

def rawRow16917 : Integer.Sparse Key := [(key537, -2), (key529, -2), (key531, -2), (key537, 6), (key366, -2), (key360, -2), (key362, -2), (key927, 2), (key865, 2), (key938, 2), (key731, 2), (key881, 2), (key733, 2), (key927, -2), (key938, -2), (key750, -2), (key733, 6), (key867, -2), (key881, -2), (key733, -2)]

theorem rawRowCheck16917 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form11 = rawRow16917 := by decide +kernel

def row16917 : Integer.Sparse Key := [(key360, -2), (key362, -2), (key366, -2), (key529, -2), (key531, -2), (key537, 4), (key731, 2), (key733, 6), (key750, -2), (key865, 2), (key867, -2)]

theorem rowCheck16917 : row16917 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16917 := by decide +kernel

theorem rowEval16917 (x : Key → ℝ) : Integer.Sparse.eval row16917 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck16917, Integer.Sparse.eval_collectBalanced, rawRowCheck16917]

def rawRow16918 : Integer.Sparse Key := [(key531, -2), (key537, -2), (key529, -2), (key537, 6), (key362, -2), (key366, -2), (key360, -2), (key881, 2), (key938, 2), (key733, 2), (key927, 2), (key731, 2), (key865, 2), (key938, -2), (key750, -2), (key927, -2), (key733, 6), (key881, -2), (key733, -2), (key867, -2)]

theorem rawRowCheck16918 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form11 = rawRow16918 := by decide +kernel

def row16918 : Integer.Sparse Key := [(key360, -2), (key362, -2), (key366, -2), (key529, -2), (key531, -2), (key537, 4), (key731, 2), (key733, 6), (key750, -2), (key865, 2), (key867, -2)]

theorem rowCheck16918 : row16918 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16918 := by decide +kernel

theorem rowEval16918 (x : Key → ℝ) : Integer.Sparse.eval row16918 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck16918, Integer.Sparse.eval_collectBalanced, rawRowCheck16918]

def rawRow16919 : Integer.Sparse Key := [(key537, -2), (key531, -2), (key529, -2), (key537, 6), (key366, -2), (key362, -2), (key360, -2), (key938, 2), (key881, 2), (key927, 2), (key733, 2), (key865, 2), (key731, 2), (key938, -2), (key927, -2), (key750, -2), (key733, 6), (key881, -2), (key867, -2), (key733, -2)]

theorem rawRowCheck16919 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form11 = rawRow16919 := by decide +kernel

def row16919 : Integer.Sparse Key := [(key360, -2), (key362, -2), (key366, -2), (key529, -2), (key531, -2), (key537, 4), (key731, 2), (key733, 6), (key750, -2), (key865, 2), (key867, -2)]

theorem rowCheck16919 : row16919 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16919 := by decide +kernel

theorem rowEval16919 (x : Key → ℝ) : Integer.Sparse.eval row16919 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck16919, Integer.Sparse.eval_collectBalanced, rawRowCheck16919]

def rawRow16920 : Integer.Sparse Key := [(key529, -2), (key537, -2), (key537, -2), (key531, 6), (key529, -2), (key537, -2), (key537, -2), (key360, 2), (key366, 2), (key731, 2), (key938, 2), (key750, 2), (key938, 2), (key733, -2), (key733, -2), (key881, -2), (key867, 6), (key733, -2), (key733, -2), (key881, -2)]

theorem rawRowCheck16920 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form11 = rawRow16920 := by decide +kernel

def row16920 : Integer.Sparse Key := [(key360, 2), (key366, 2), (key529, -4), (key531, 6), (key537, -8), (key731, 2), (key733, -8), (key750, 2), (key867, 6), (key881, -4), (key938, 4)]

theorem rowCheck16920 : row16920 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16920 := by decide +kernel

theorem rowEval16920 (x : Key → ℝ) : Integer.Sparse.eval row16920 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form11) x := by
  rw [rowCheck16920, Integer.Sparse.eval_collectBalanced, rawRowCheck16920]

def rawRow16921 : Integer.Sparse Key := [(key537, -2), (key529, -2), (key537, -2), (key531, 6), (key537, -2), (key529, -2), (key537, -2), (key366, 2), (key360, 2), (key938, 2), (key731, 2), (key938, 2), (key750, 2), (key733, -2), (key881, -2), (key733, -2), (key867, 6), (key733, -2), (key881, -2), (key733, -2)]

theorem rawRowCheck16921 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form11 = rawRow16921 := by decide +kernel

def row16921 : Integer.Sparse Key := [(key360, 2), (key366, 2), (key529, -4), (key531, 6), (key537, -8), (key731, 2), (key733, -8), (key750, 2), (key867, 6), (key881, -4), (key938, 4)]

theorem rowCheck16921 : row16921 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16921 := by decide +kernel

theorem rowEval16921 (x : Key → ℝ) : Integer.Sparse.eval row16921 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck16921, Integer.Sparse.eval_collectBalanced, rawRowCheck16921]

def rawRow16922 : Integer.Sparse Key := [(key537, -2), (key537, -2), (key529, -2), (key531, 6), (key537, -2), (key537, -2), (key529, -2), (key676, 2), (key676, 2), (key366, 2), (key366, 2), (key360, 2), (key731, 2), (key881, -2), (key733, -2), (key733, -2), (key867, 6), (key881, -2), (key733, -2), (key733, -2)]

theorem rawRowCheck16922 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form11 = rawRow16922 := by decide +kernel

def row16922 : Integer.Sparse Key := [(key360, 2), (key366, 4), (key529, -4), (key531, 6), (key537, -8), (key676, 4), (key731, 2), (key733, -8), (key867, 6), (key881, -4)]

theorem rowCheck16922 : row16922 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16922 := by decide +kernel

theorem rowEval16922 (x : Key → ℝ) : Integer.Sparse.eval row16922 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck16922, Integer.Sparse.eval_collectBalanced, rawRowCheck16922]

def rawRow16923 : Integer.Sparse Key := [(key1989, 2), (key1989, 2), (key1994, 2), (key1999, -2), (key2003, -2), (key2003, -2), (key1989, 2), (key1989, 2), (key1994, 2), (key2268, -1), (key2272, -1), (key2268, -1), (key2294, -1), (key2272, -1), (key2294, -1), (key1999, -2), (key2003, -2), (key2003, -2), (key2268, -1), (key2272, -1), (key2268, -1), (key2294, -1), (key2272, -1), (key2294, -1), (key2324, 4), (key2324, 4), (key2336, 4)]

theorem rawRowCheck16923 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form12 = rawRow16923 := by decide +kernel

def row16923 : Integer.Sparse Key := [(key1989, 8), (key1994, 4), (key1999, -4), (key2003, -8), (key2268, -4), (key2272, -4), (key2294, -4), (key2324, 8), (key2336, 4)]

theorem rowCheck16923 : row16923 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16923 := by decide +kernel

theorem rowEval16923 (x : Key → ℝ) : Integer.Sparse.eval row16923 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form12) x := by
  rw [rowCheck16923, Integer.Sparse.eval_collectBalanced, rawRowCheck16923]

def rawRow16924 : Integer.Sparse Key := [(key1989, 2), (key1994, 2), (key1989, 2), (key2003, -2), (key1999, -2), (key2003, -2), (key1989, 2), (key1994, 2), (key1989, 2), (key2272, -1), (key2268, -1), (key2294, -1), (key2268, -1), (key2294, -1), (key2272, -1), (key2003, -2), (key1999, -2), (key2003, -2), (key2272, -1), (key2268, -1), (key2294, -1), (key2268, -1), (key2294, -1), (key2272, -1), (key2324, 4), (key2336, 4), (key2324, 4)]

theorem rawRowCheck16924 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form12 = rawRow16924 := by decide +kernel

def row16924 : Integer.Sparse Key := [(key1989, 8), (key1994, 4), (key1999, -4), (key2003, -8), (key2268, -4), (key2272, -4), (key2294, -4), (key2324, 8), (key2336, 4)]

theorem rowCheck16924 : row16924 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16924 := by decide +kernel

theorem rowEval16924 (x : Key → ℝ) : Integer.Sparse.eval row16924 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck16924, Integer.Sparse.eval_collectBalanced, rawRowCheck16924]

def rawRow16925 : Integer.Sparse Key := [(key1994, 2), (key1989, 2), (key1989, 2), (key2003, -2), (key2003, -2), (key1999, -2), (key1994, 2), (key1989, 2), (key1989, 2), (key2294, -1), (key2294, -1), (key2272, -1), (key2272, -1), (key2268, -1), (key2268, -1), (key2003, -2), (key2003, -2), (key1999, -2), (key2294, -1), (key2294, -1), (key2272, -1), (key2272, -1), (key2268, -1), (key2268, -1), (key2336, 4), (key2324, 4), (key2324, 4)]

theorem rawRowCheck16925 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form12 = rawRow16925 := by decide +kernel

def row16925 : Integer.Sparse Key := [(key1989, 8), (key1994, 4), (key1999, -4), (key2003, -8), (key2268, -4), (key2272, -4), (key2294, -4), (key2324, 8), (key2336, 4)]

theorem rowCheck16925 : row16925 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16925 := by decide +kernel

theorem rowEval16925 (x : Key → ℝ) : Integer.Sparse.eval row16925 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck16925, Integer.Sparse.eval_collectBalanced, rawRowCheck16925]

def rawRow16926 : Integer.Sparse Key := [(key1989, 2), (key1999, 2), (key2003, 2), (key1989, -2), (key1994, -2), (key2003, -2), (key2234, 2), (key2268, 2), (key2272, 2), (key1989, -1), (key1994, -1), (key2234, -1), (key2259, -1), (key2272, -1), (key2294, -1), (key2268, -2), (key2272, -2), (key2324, -2), (key1999, -1), (key2003, -1), (key2268, -1), (key2294, -1), (key2324, -1), (key2336, -1), (key2003, 4), (key2272, 4), (key2294, 4)]

theorem rawRowCheck16926 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form12 = rawRow16926 := by decide +kernel

def row16926 : Integer.Sparse Key := [(key1989, -1), (key1994, -3), (key1999, 1), (key2003, 3), (key2234, 1), (key2259, -1), (key2268, -1), (key2272, 3), (key2294, 2), (key2324, -3), (key2336, -1)]

theorem rowCheck16926 : row16926 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16926 := by decide +kernel

theorem rowEval16926 (x : Key → ℝ) : Integer.Sparse.eval row16926 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form12) x := by
  rw [rowCheck16926, Integer.Sparse.eval_collectBalanced, rawRowCheck16926]

def rawRow16927 : Integer.Sparse Key := [(key1989, 2), (key2003, 2), (key1999, 2), (key1994, -2), (key1989, -2), (key2003, -2), (key2234, 2), (key2272, 2), (key2268, 2), (key1994, -1), (key1989, -1), (key2259, -1), (key2234, -1), (key2294, -1), (key2272, -1), (key2272, -2), (key2268, -2), (key2324, -2), (key2003, -1), (key1999, -1), (key2294, -1), (key2268, -1), (key2336, -1), (key2324, -1), (key2003, 4), (key2294, 4), (key2272, 4)]

theorem rawRowCheck16927 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form12 = rawRow16927 := by decide +kernel

def row16927 : Integer.Sparse Key := [(key1989, -1), (key1994, -3), (key1999, 1), (key2003, 3), (key2234, 1), (key2259, -1), (key2268, -1), (key2272, 3), (key2294, 2), (key2324, -3), (key2336, -1)]

theorem rowCheck16927 : row16927 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16927 := by decide +kernel

theorem rowEval16927 (x : Key → ℝ) : Integer.Sparse.eval row16927 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck16927, Integer.Sparse.eval_collectBalanced, rawRowCheck16927]

def rawRow16928 : Integer.Sparse Key := [(key1999, 2), (key1989, 2), (key2003, 2), (key1989, -2), (key2003, -2), (key1994, -2), (key2268, 2), (key2234, 2), (key2272, 2), (key2234, -1), (key2272, -1), (key1989, -1), (key2294, -1), (key1994, -1), (key2259, -1), (key2268, -2), (key2324, -2), (key2272, -2), (key2268, -1), (key2324, -1), (key1999, -1), (key2336, -1), (key2003, -1), (key2294, -1), (key2272, 4), (key2003, 4), (key2294, 4)]

theorem rawRowCheck16928 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form12 = rawRow16928 := by decide +kernel

def row16928 : Integer.Sparse Key := [(key1989, -1), (key1994, -3), (key1999, 1), (key2003, 3), (key2234, 1), (key2259, -1), (key2268, -1), (key2272, 3), (key2294, 2), (key2324, -3), (key2336, -1)]

theorem rowCheck16928 : row16928 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16928 := by decide +kernel

theorem rowEval16928 (x : Key → ℝ) : Integer.Sparse.eval row16928 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form12) x := by
  rw [rowCheck16928, Integer.Sparse.eval_collectBalanced, rawRowCheck16928]

def rawRow16929 : Integer.Sparse Key := [(key1999, 2), (key2003, 2), (key1989, 2), (key2003, -2), (key1989, -2), (key1994, -2), (key2268, 2), (key2272, 2), (key2234, 2), (key2272, -1), (key2234, -1), (key2294, -1), (key1989, -1), (key2259, -1), (key1994, -1), (key2324, -2), (key2268, -2), (key2272, -2), (key2324, -1), (key2268, -1), (key2336, -1), (key1999, -1), (key2294, -1), (key2003, -1), (key2272, 4), (key2294, 4), (key2003, 4)]

theorem rawRowCheck16929 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form12 = rawRow16929 := by decide +kernel

def row16929 : Integer.Sparse Key := [(key1989, -1), (key1994, -3), (key1999, 1), (key2003, 3), (key2234, 1), (key2259, -1), (key2268, -1), (key2272, 3), (key2294, 2), (key2324, -3), (key2336, -1)]

theorem rowCheck16929 : row16929 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16929 := by decide +kernel

theorem rowEval16929 (x : Key → ℝ) : Integer.Sparse.eval row16929 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck16929, Integer.Sparse.eval_collectBalanced, rawRowCheck16929]

def rawRow16930 : Integer.Sparse Key := [(key2003, 2), (key1989, 2), (key1999, 2), (key1994, -2), (key2003, -2), (key1989, -2), (key2272, 2), (key2234, 2), (key2268, 2), (key2259, -1), (key2294, -1), (key1994, -1), (key2272, -1), (key1989, -1), (key2234, -1), (key2272, -2), (key2324, -2), (key2268, -2), (key2294, -1), (key2336, -1), (key2003, -1), (key2324, -1), (key1999, -1), (key2268, -1), (key2294, 4), (key2003, 4), (key2272, 4)]

theorem rawRowCheck16930 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form12 = rawRow16930 := by decide +kernel

def row16930 : Integer.Sparse Key := [(key1989, -1), (key1994, -3), (key1999, 1), (key2003, 3), (key2234, 1), (key2259, -1), (key2268, -1), (key2272, 3), (key2294, 2), (key2324, -3), (key2336, -1)]

theorem rowCheck16930 : row16930 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16930 := by decide +kernel

theorem rowEval16930 (x : Key → ℝ) : Integer.Sparse.eval row16930 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck16930, Integer.Sparse.eval_collectBalanced, rawRowCheck16930]

def rawRow16931 : Integer.Sparse Key := [(key2003, 2), (key1999, 2), (key1989, 2), (key2003, -2), (key1994, -2), (key1989, -2), (key2272, 2), (key2268, 2), (key2234, 2), (key2294, -1), (key2259, -1), (key2272, -1), (key1994, -1), (key2234, -1), (key1989, -1), (key2324, -2), (key2272, -2), (key2268, -2), (key2336, -1), (key2294, -1), (key2324, -1), (key2003, -1), (key2268, -1), (key1999, -1), (key2294, 4), (key2272, 4), (key2003, 4)]

theorem rawRowCheck16931 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form12 = rawRow16931 := by decide +kernel

def row16931 : Integer.Sparse Key := [(key1989, -1), (key1994, -3), (key1999, 1), (key2003, 3), (key2234, 1), (key2259, -1), (key2268, -1), (key2272, 3), (key2294, 2), (key2324, -3), (key2336, -1)]

theorem rowCheck16931 : row16931 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16931 := by decide +kernel

theorem rowEval16931 (x : Key → ℝ) : Integer.Sparse.eval row16931 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck16931, Integer.Sparse.eval_collectBalanced, rawRowCheck16931]

def rawRow16932 : Integer.Sparse Key := [(key2234, 2), (key2268, 2), (key2272, 2), (key2268, -2), (key2272, -2), (key2324, -2), (key1989, 2), (key1999, 2), (key2003, 2), (key1999, -1), (key2003, -1), (key2268, -1), (key2294, -1), (key2324, -1), (key2336, -1), (key1989, -2), (key1994, -2), (key2003, -2), (key1989, -1), (key1994, -1), (key2234, -1), (key2259, -1), (key2272, -1), (key2294, -1), (key2003, 4), (key2272, 4), (key2294, 4)]

theorem rawRowCheck16932 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form12 = rawRow16932 := by decide +kernel

def row16932 : Integer.Sparse Key := [(key1989, -1), (key1994, -3), (key1999, 1), (key2003, 3), (key2234, 1), (key2259, -1), (key2268, -1), (key2272, 3), (key2294, 2), (key2324, -3), (key2336, -1)]

theorem rowCheck16932 : row16932 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16932 := by decide +kernel

theorem rowEval16932 (x : Key → ℝ) : Integer.Sparse.eval row16932 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form12) x := by
  rw [rowCheck16932, Integer.Sparse.eval_collectBalanced, rawRowCheck16932]

def rawRow16933 : Integer.Sparse Key := [(key2234, 2), (key2272, 2), (key2268, 2), (key2272, -2), (key2268, -2), (key2324, -2), (key1989, 2), (key2003, 2), (key1999, 2), (key2003, -1), (key1999, -1), (key2294, -1), (key2268, -1), (key2336, -1), (key2324, -1), (key1994, -2), (key1989, -2), (key2003, -2), (key1994, -1), (key1989, -1), (key2259, -1), (key2234, -1), (key2294, -1), (key2272, -1), (key2003, 4), (key2294, 4), (key2272, 4)]

theorem rawRowCheck16933 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form12 = rawRow16933 := by decide +kernel

def row16933 : Integer.Sparse Key := [(key1989, -1), (key1994, -3), (key1999, 1), (key2003, 3), (key2234, 1), (key2259, -1), (key2268, -1), (key2272, 3), (key2294, 2), (key2324, -3), (key2336, -1)]

theorem rowCheck16933 : row16933 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16933 := by decide +kernel

theorem rowEval16933 (x : Key → ℝ) : Integer.Sparse.eval row16933 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck16933, Integer.Sparse.eval_collectBalanced, rawRowCheck16933]

def rawRow16934 : Integer.Sparse Key := [(key2268, 2), (key2234, 2), (key2272, 2), (key2268, -2), (key2324, -2), (key2272, -2), (key1999, 2), (key1989, 2), (key2003, 2), (key2268, -1), (key2324, -1), (key1999, -1), (key2336, -1), (key2003, -1), (key2294, -1), (key1989, -2), (key2003, -2), (key1994, -2), (key2234, -1), (key2272, -1), (key1989, -1), (key2294, -1), (key1994, -1), (key2259, -1), (key2272, 4), (key2003, 4), (key2294, 4)]

theorem rawRowCheck16934 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form12 = rawRow16934 := by decide +kernel

def row16934 : Integer.Sparse Key := [(key1989, -1), (key1994, -3), (key1999, 1), (key2003, 3), (key2234, 1), (key2259, -1), (key2268, -1), (key2272, 3), (key2294, 2), (key2324, -3), (key2336, -1)]

theorem rowCheck16934 : row16934 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16934 := by decide +kernel

theorem rowEval16934 (x : Key → ℝ) : Integer.Sparse.eval row16934 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form12) x := by
  rw [rowCheck16934, Integer.Sparse.eval_collectBalanced, rawRowCheck16934]

def rawRow16935 : Integer.Sparse Key := [(key2268, 2), (key2272, 2), (key2234, 2), (key2324, -2), (key2268, -2), (key2272, -2), (key1999, 2), (key2003, 2), (key1989, 2), (key2324, -1), (key2268, -1), (key2336, -1), (key1999, -1), (key2294, -1), (key2003, -1), (key2003, -2), (key1989, -2), (key1994, -2), (key2272, -1), (key2234, -1), (key2294, -1), (key1989, -1), (key2259, -1), (key1994, -1), (key2272, 4), (key2294, 4), (key2003, 4)]

theorem rawRowCheck16935 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form12 = rawRow16935 := by decide +kernel

def row16935 : Integer.Sparse Key := [(key1989, -1), (key1994, -3), (key1999, 1), (key2003, 3), (key2234, 1), (key2259, -1), (key2268, -1), (key2272, 3), (key2294, 2), (key2324, -3), (key2336, -1)]

theorem rowCheck16935 : row16935 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16935 := by decide +kernel

theorem rowEval16935 (x : Key → ℝ) : Integer.Sparse.eval row16935 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck16935, Integer.Sparse.eval_collectBalanced, rawRowCheck16935]

def rawRow16936 : Integer.Sparse Key := [(key2272, 2), (key2234, 2), (key2268, 2), (key2272, -2), (key2324, -2), (key2268, -2), (key2003, 2), (key1989, 2), (key1999, 2), (key2294, -1), (key2336, -1), (key2003, -1), (key2324, -1), (key1999, -1), (key2268, -1), (key1994, -2), (key2003, -2), (key1989, -2), (key2259, -1), (key2294, -1), (key1994, -1), (key2272, -1), (key1989, -1), (key2234, -1), (key2294, 4), (key2003, 4), (key2272, 4)]

theorem rawRowCheck16936 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form12 = rawRow16936 := by decide +kernel

def row16936 : Integer.Sparse Key := [(key1989, -1), (key1994, -3), (key1999, 1), (key2003, 3), (key2234, 1), (key2259, -1), (key2268, -1), (key2272, 3), (key2294, 2), (key2324, -3), (key2336, -1)]

theorem rowCheck16936 : row16936 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16936 := by decide +kernel

theorem rowEval16936 (x : Key → ℝ) : Integer.Sparse.eval row16936 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck16936, Integer.Sparse.eval_collectBalanced, rawRowCheck16936]

def rawRow16937 : Integer.Sparse Key := [(key2272, 2), (key2268, 2), (key2234, 2), (key2324, -2), (key2272, -2), (key2268, -2), (key2003, 2), (key1999, 2), (key1989, 2), (key2336, -1), (key2294, -1), (key2324, -1), (key2003, -1), (key2268, -1), (key1999, -1), (key2003, -2), (key1994, -2), (key1989, -2), (key2294, -1), (key2259, -1), (key2272, -1), (key1994, -1), (key2234, -1), (key1989, -1), (key2294, 4), (key2272, 4), (key2003, 4)]

theorem rawRowCheck16937 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form12 = rawRow16937 := by decide +kernel

def row16937 : Integer.Sparse Key := [(key1989, -1), (key1994, -3), (key1999, 1), (key2003, 3), (key2234, 1), (key2259, -1), (key2268, -1), (key2272, 3), (key2294, 2), (key2324, -3), (key2336, -1)]

theorem rowCheck16937 : row16937 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16937 := by decide +kernel

theorem rowEval16937 (x : Key → ℝ) : Integer.Sparse.eval row16937 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck16937, Integer.Sparse.eval_collectBalanced, rawRowCheck16937]

def rawRow16938 : Integer.Sparse Key := [(key2268, 2), (key2268, 2), (key2324, 2), (key2234, -2), (key2272, -2), (key2272, -2), (key2268, 2), (key2268, 2), (key2324, 2), (key1989, -1), (key2003, -1), (key1989, -1), (key2294, -1), (key2003, -1), (key2294, -1), (key2234, -2), (key2272, -2), (key2272, -2), (key1989, -1), (key2003, -1), (key1989, -1), (key2294, -1), (key2003, -1), (key2294, -1), (key1994, 4), (key1994, 4), (key2259, 4)]

theorem rawRowCheck16938 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form12 = rawRow16938 := by decide +kernel

def row16938 : Integer.Sparse Key := [(key1989, -4), (key1994, 8), (key2003, -4), (key2234, -4), (key2259, 4), (key2268, 8), (key2272, -8), (key2294, -4), (key2324, 4)]

theorem rowCheck16938 : row16938 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16938 := by decide +kernel

theorem rowEval16938 (x : Key → ℝ) : Integer.Sparse.eval row16938 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form12) x := by
  rw [rowCheck16938, Integer.Sparse.eval_collectBalanced, rawRowCheck16938]

def rawRow16939 : Integer.Sparse Key := [(key2268, 2), (key2324, 2), (key2268, 2), (key2272, -2), (key2234, -2), (key2272, -2), (key2268, 2), (key2324, 2), (key2268, 2), (key2003, -1), (key1989, -1), (key2294, -1), (key1989, -1), (key2294, -1), (key2003, -1), (key2272, -2), (key2234, -2), (key2272, -2), (key2003, -1), (key1989, -1), (key2294, -1), (key1989, -1), (key2294, -1), (key2003, -1), (key1994, 4), (key2259, 4), (key1994, 4)]

theorem rawRowCheck16939 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form12 = rawRow16939 := by decide +kernel

def row16939 : Integer.Sparse Key := [(key1989, -4), (key1994, 8), (key2003, -4), (key2234, -4), (key2259, 4), (key2268, 8), (key2272, -8), (key2294, -4), (key2324, 4)]

theorem rowCheck16939 : row16939 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16939 := by decide +kernel

theorem rowEval16939 (x : Key → ℝ) : Integer.Sparse.eval row16939 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck16939, Integer.Sparse.eval_collectBalanced, rawRowCheck16939]

def rawRow16940 : Integer.Sparse Key := [(key2324, 2), (key2268, 2), (key2268, 2), (key2272, -2), (key2272, -2), (key2234, -2), (key2324, 2), (key2268, 2), (key2268, 2), (key2294, -1), (key2294, -1), (key2003, -1), (key2003, -1), (key1989, -1), (key1989, -1), (key2272, -2), (key2272, -2), (key2234, -2), (key2294, -1), (key2294, -1), (key2003, -1), (key2003, -1), (key1989, -1), (key1989, -1), (key2259, 4), (key1994, 4), (key1994, 4)]

theorem rawRowCheck16940 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form12 = rawRow16940 := by decide +kernel

def row16940 : Integer.Sparse Key := [(key1989, -4), (key1994, 8), (key2003, -4), (key2234, -4), (key2259, 4), (key2268, 8), (key2272, -8), (key2294, -4), (key2324, 4)]

theorem rowCheck16940 : row16940 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16940 := by decide +kernel

theorem rowEval16940 (x : Key → ℝ) : Integer.Sparse.eval row16940 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck16940, Integer.Sparse.eval_collectBalanced, rawRowCheck16940]

def rawRow16941 : Integer.Sparse Key := [(key2027, 2), (key2033, 2), (key2033, 2), (key2057, -1), (key2063, -1), (key2057, -1), (key2069, -1), (key2063, -1), (key2069, -1), (key2027, 2), (key2033, 2), (key2033, 2), (key2146, -1), (key2152, -1), (key2146, -1), (key2166, -1), (key2152, -1), (key2166, -1), (key2057, -1), (key2063, -1), (key2057, -1), (key2069, -1), (key2063, -1), (key2069, -1), (key2146, -1), (key2152, -1), (key2146, -1), (key2166, -1), (key2152, -1), (key2166, -1), (key2239, 2), (key2246, 2), (key2239, 2), (key2253, 2), (key2246, 2), (key2253, 2)]

theorem rawRowCheck16941 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form13 = rawRow16941 := by decide +kernel

def row16941 : Integer.Sparse Key := [(key2027, 4), (key2033, 8), (key2057, -4), (key2063, -4), (key2069, -4), (key2146, -4), (key2152, -4), (key2166, -4), (key2239, 4), (key2246, 4), (key2253, 4)]

theorem rowCheck16941 : row16941 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16941 := by decide +kernel

theorem rowEval16941 (x : Key → ℝ) : Integer.Sparse.eval row16941 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form13) x := by
  rw [rowCheck16941, Integer.Sparse.eval_collectBalanced, rawRowCheck16941]

def rawRow16942 : Integer.Sparse Key := [(key2033, 2), (key2027, 2), (key2033, 2), (key2063, -1), (key2057, -1), (key2069, -1), (key2057, -1), (key2069, -1), (key2063, -1), (key2033, 2), (key2027, 2), (key2033, 2), (key2152, -1), (key2146, -1), (key2166, -1), (key2146, -1), (key2166, -1), (key2152, -1), (key2063, -1), (key2057, -1), (key2069, -1), (key2057, -1), (key2069, -1), (key2063, -1), (key2152, -1), (key2146, -1), (key2166, -1), (key2146, -1), (key2166, -1), (key2152, -1), (key2246, 2), (key2239, 2), (key2253, 2), (key2239, 2), (key2253, 2), (key2246, 2)]

theorem rawRowCheck16942 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form13 = rawRow16942 := by decide +kernel

def row16942 : Integer.Sparse Key := [(key2027, 4), (key2033, 8), (key2057, -4), (key2063, -4), (key2069, -4), (key2146, -4), (key2152, -4), (key2166, -4), (key2239, 4), (key2246, 4), (key2253, 4)]

theorem rowCheck16942 : row16942 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16942 := by decide +kernel

theorem rowEval16942 (x : Key → ℝ) : Integer.Sparse.eval row16942 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck16942, Integer.Sparse.eval_collectBalanced, rawRowCheck16942]

def rawRow16943 : Integer.Sparse Key := [(key2033, 2), (key2033, 2), (key2027, 2), (key2069, -1), (key2069, -1), (key2063, -1), (key2063, -1), (key2057, -1), (key2057, -1), (key2033, 2), (key2033, 2), (key2027, 2), (key2166, -1), (key2166, -1), (key2152, -1), (key2152, -1), (key2146, -1), (key2146, -1), (key2069, -1), (key2069, -1), (key2063, -1), (key2063, -1), (key2057, -1), (key2057, -1), (key2166, -1), (key2166, -1), (key2152, -1), (key2152, -1), (key2146, -1), (key2146, -1), (key2253, 2), (key2253, 2), (key2246, 2), (key2246, 2), (key2239, 2), (key2239, 2)]

theorem rawRowCheck16943 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form13 = rawRow16943 := by decide +kernel

def row16943 : Integer.Sparse Key := [(key2027, 4), (key2033, 8), (key2057, -4), (key2063, -4), (key2069, -4), (key2146, -4), (key2152, -4), (key2166, -4), (key2239, 4), (key2246, 4), (key2253, 4)]

theorem rowCheck16943 : row16943 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16943 := by decide +kernel

theorem rowEval16943 (x : Key → ℝ) : Integer.Sparse.eval row16943 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck16943, Integer.Sparse.eval_collectBalanced, rawRowCheck16943]

def rawRow16944 : Integer.Sparse Key := [(key2057, 2), (key2063, 2), (key2092, 2), (key2027, -1), (key2033, -1), (key2057, -1), (key2069, -1), (key2092, -1), (key2095, -1), (key2146, 2), (key2152, 2), (key2194, 2), (key2027, -1), (key2033, -1), (key2146, -1), (key2166, -1), (key2194, -1), (key2200, -1), (key2146, -1), (key2152, -1), (key2239, -1), (key2246, -1), (key2303, -1), (key2305, -1), (key2057, -1), (key2063, -1), (key2239, -1), (key2253, -1), (key2303, -1), (key2310, -1), (key2057, 2), (key2069, 2), (key2146, 2), (key2166, 2), (key2305, 2), (key2310, 2)]

theorem rawRowCheck16944 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form13 = rawRow16944 := by decide +kernel

def row16944 : Integer.Sparse Key := [(key2027, -2), (key2033, -2), (key2057, 2), (key2063, 1), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 2), (key2152, 1), (key2166, 1), (key2194, 1), (key2200, -1), (key2239, -2), (key2246, -1), (key2253, -1), (key2303, -2), (key2305, 1), (key2310, 1)]

theorem rowCheck16944 : row16944 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16944 := by decide +kernel

theorem rowEval16944 (x : Key → ℝ) : Integer.Sparse.eval row16944 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form13) x := by
  rw [rowCheck16944, Integer.Sparse.eval_collectBalanced, rawRowCheck16944]

def rawRow16945 : Integer.Sparse Key := [(key2063, 2), (key2057, 2), (key2092, 2), (key2033, -1), (key2027, -1), (key2069, -1), (key2057, -1), (key2095, -1), (key2092, -1), (key2152, 2), (key2146, 2), (key2194, 2), (key2033, -1), (key2027, -1), (key2166, -1), (key2146, -1), (key2200, -1), (key2194, -1), (key2152, -1), (key2146, -1), (key2246, -1), (key2239, -1), (key2305, -1), (key2303, -1), (key2063, -1), (key2057, -1), (key2253, -1), (key2239, -1), (key2310, -1), (key2303, -1), (key2069, 2), (key2057, 2), (key2166, 2), (key2146, 2), (key2310, 2), (key2305, 2)]

theorem rawRowCheck16945 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form13 = rawRow16945 := by decide +kernel

def row16945 : Integer.Sparse Key := [(key2027, -2), (key2033, -2), (key2057, 2), (key2063, 1), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 2), (key2152, 1), (key2166, 1), (key2194, 1), (key2200, -1), (key2239, -2), (key2246, -1), (key2253, -1), (key2303, -2), (key2305, 1), (key2310, 1)]

theorem rowCheck16945 : row16945 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16945 := by decide +kernel

theorem rowEval16945 (x : Key → ℝ) : Integer.Sparse.eval row16945 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck16945, Integer.Sparse.eval_collectBalanced, rawRowCheck16945]

def rawRow16946 : Integer.Sparse Key := [(key2057, 2), (key2092, 2), (key2063, 2), (key2057, -1), (key2092, -1), (key2027, -1), (key2095, -1), (key2033, -1), (key2069, -1), (key2146, 2), (key2194, 2), (key2152, 2), (key2146, -1), (key2194, -1), (key2027, -1), (key2200, -1), (key2033, -1), (key2166, -1), (key2239, -1), (key2303, -1), (key2146, -1), (key2305, -1), (key2152, -1), (key2246, -1), (key2239, -1), (key2303, -1), (key2057, -1), (key2310, -1), (key2063, -1), (key2253, -1), (key2146, 2), (key2305, 2), (key2057, 2), (key2310, 2), (key2069, 2), (key2166, 2)]

theorem rawRowCheck16946 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form13 = rawRow16946 := by decide +kernel

def row16946 : Integer.Sparse Key := [(key2027, -2), (key2033, -2), (key2057, 2), (key2063, 1), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 2), (key2152, 1), (key2166, 1), (key2194, 1), (key2200, -1), (key2239, -2), (key2246, -1), (key2253, -1), (key2303, -2), (key2305, 1), (key2310, 1)]

theorem rowCheck16946 : row16946 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16946 := by decide +kernel

theorem rowEval16946 (x : Key → ℝ) : Integer.Sparse.eval row16946 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form13) x := by
  rw [rowCheck16946, Integer.Sparse.eval_collectBalanced, rawRowCheck16946]

def rawRow16947 : Integer.Sparse Key := [(key2092, 2), (key2057, 2), (key2063, 2), (key2092, -1), (key2057, -1), (key2095, -1), (key2027, -1), (key2069, -1), (key2033, -1), (key2194, 2), (key2146, 2), (key2152, 2), (key2194, -1), (key2146, -1), (key2200, -1), (key2027, -1), (key2166, -1), (key2033, -1), (key2303, -1), (key2239, -1), (key2305, -1), (key2146, -1), (key2246, -1), (key2152, -1), (key2303, -1), (key2239, -1), (key2310, -1), (key2057, -1), (key2253, -1), (key2063, -1), (key2305, 2), (key2146, 2), (key2310, 2), (key2057, 2), (key2166, 2), (key2069, 2)]

theorem rawRowCheck16947 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form13 = rawRow16947 := by decide +kernel

def row16947 : Integer.Sparse Key := [(key2027, -2), (key2033, -2), (key2057, 2), (key2063, 1), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 2), (key2152, 1), (key2166, 1), (key2194, 1), (key2200, -1), (key2239, -2), (key2246, -1), (key2253, -1), (key2303, -2), (key2305, 1), (key2310, 1)]

theorem rowCheck16947 : row16947 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16947 := by decide +kernel

theorem rowEval16947 (x : Key → ℝ) : Integer.Sparse.eval row16947 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck16947, Integer.Sparse.eval_collectBalanced, rawRowCheck16947]

def rawRow16948 : Integer.Sparse Key := [(key2063, 2), (key2092, 2), (key2057, 2), (key2069, -1), (key2095, -1), (key2033, -1), (key2092, -1), (key2027, -1), (key2057, -1), (key2152, 2), (key2194, 2), (key2146, 2), (key2166, -1), (key2200, -1), (key2033, -1), (key2194, -1), (key2027, -1), (key2146, -1), (key2246, -1), (key2305, -1), (key2152, -1), (key2303, -1), (key2146, -1), (key2239, -1), (key2253, -1), (key2310, -1), (key2063, -1), (key2303, -1), (key2057, -1), (key2239, -1), (key2166, 2), (key2310, 2), (key2069, 2), (key2305, 2), (key2057, 2), (key2146, 2)]

theorem rawRowCheck16948 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form13 = rawRow16948 := by decide +kernel

def row16948 : Integer.Sparse Key := [(key2027, -2), (key2033, -2), (key2057, 2), (key2063, 1), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 2), (key2152, 1), (key2166, 1), (key2194, 1), (key2200, -1), (key2239, -2), (key2246, -1), (key2253, -1), (key2303, -2), (key2305, 1), (key2310, 1)]

theorem rowCheck16948 : row16948 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16948 := by decide +kernel

theorem rowEval16948 (x : Key → ℝ) : Integer.Sparse.eval row16948 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck16948, Integer.Sparse.eval_collectBalanced, rawRowCheck16948]

def rawRow16949 : Integer.Sparse Key := [(key2092, 2), (key2063, 2), (key2057, 2), (key2095, -1), (key2069, -1), (key2092, -1), (key2033, -1), (key2057, -1), (key2027, -1), (key2194, 2), (key2152, 2), (key2146, 2), (key2200, -1), (key2166, -1), (key2194, -1), (key2033, -1), (key2146, -1), (key2027, -1), (key2305, -1), (key2246, -1), (key2303, -1), (key2152, -1), (key2239, -1), (key2146, -1), (key2310, -1), (key2253, -1), (key2303, -1), (key2063, -1), (key2239, -1), (key2057, -1), (key2310, 2), (key2166, 2), (key2305, 2), (key2069, 2), (key2146, 2), (key2057, 2)]

theorem rawRowCheck16949 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form13 = rawRow16949 := by decide +kernel

def row16949 : Integer.Sparse Key := [(key2027, -2), (key2033, -2), (key2057, 2), (key2063, 1), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 2), (key2152, 1), (key2166, 1), (key2194, 1), (key2200, -1), (key2239, -2), (key2246, -1), (key2253, -1), (key2303, -2), (key2305, 1), (key2310, 1)]

theorem rowCheck16949 : row16949 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16949 := by decide +kernel

theorem rowEval16949 (x : Key → ℝ) : Integer.Sparse.eval row16949 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck16949, Integer.Sparse.eval_collectBalanced, rawRowCheck16949]

def rawRow16950 : Integer.Sparse Key := [(key2146, 2), (key2152, 2), (key2194, 2), (key2146, -1), (key2152, -1), (key2239, -1), (key2246, -1), (key2303, -1), (key2305, -1), (key2057, 2), (key2063, 2), (key2092, 2), (key2057, -1), (key2063, -1), (key2239, -1), (key2253, -1), (key2303, -1), (key2310, -1), (key2027, -1), (key2033, -1), (key2057, -1), (key2069, -1), (key2092, -1), (key2095, -1), (key2027, -1), (key2033, -1), (key2146, -1), (key2166, -1), (key2194, -1), (key2200, -1), (key2057, 2), (key2069, 2), (key2146, 2), (key2166, 2), (key2305, 2), (key2310, 2)]

theorem rawRowCheck16950 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form13 = rawRow16950 := by decide +kernel

def row16950 : Integer.Sparse Key := [(key2027, -2), (key2033, -2), (key2057, 2), (key2063, 1), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 2), (key2152, 1), (key2166, 1), (key2194, 1), (key2200, -1), (key2239, -2), (key2246, -1), (key2253, -1), (key2303, -2), (key2305, 1), (key2310, 1)]

theorem rowCheck16950 : row16950 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16950 := by decide +kernel

theorem rowEval16950 (x : Key → ℝ) : Integer.Sparse.eval row16950 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form13) x := by
  rw [rowCheck16950, Integer.Sparse.eval_collectBalanced, rawRowCheck16950]

def rawRow16951 : Integer.Sparse Key := [(key2152, 2), (key2146, 2), (key2194, 2), (key2152, -1), (key2146, -1), (key2246, -1), (key2239, -1), (key2305, -1), (key2303, -1), (key2063, 2), (key2057, 2), (key2092, 2), (key2063, -1), (key2057, -1), (key2253, -1), (key2239, -1), (key2310, -1), (key2303, -1), (key2033, -1), (key2027, -1), (key2069, -1), (key2057, -1), (key2095, -1), (key2092, -1), (key2033, -1), (key2027, -1), (key2166, -1), (key2146, -1), (key2200, -1), (key2194, -1), (key2069, 2), (key2057, 2), (key2166, 2), (key2146, 2), (key2310, 2), (key2305, 2)]

theorem rawRowCheck16951 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form13 = rawRow16951 := by decide +kernel

def row16951 : Integer.Sparse Key := [(key2027, -2), (key2033, -2), (key2057, 2), (key2063, 1), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 2), (key2152, 1), (key2166, 1), (key2194, 1), (key2200, -1), (key2239, -2), (key2246, -1), (key2253, -1), (key2303, -2), (key2305, 1), (key2310, 1)]

theorem rowCheck16951 : row16951 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16951 := by decide +kernel

theorem rowEval16951 (x : Key → ℝ) : Integer.Sparse.eval row16951 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck16951, Integer.Sparse.eval_collectBalanced, rawRowCheck16951]

def rawRow16952 : Integer.Sparse Key := [(key2146, 2), (key2194, 2), (key2152, 2), (key2239, -1), (key2303, -1), (key2146, -1), (key2305, -1), (key2152, -1), (key2246, -1), (key2057, 2), (key2092, 2), (key2063, 2), (key2239, -1), (key2303, -1), (key2057, -1), (key2310, -1), (key2063, -1), (key2253, -1), (key2057, -1), (key2092, -1), (key2027, -1), (key2095, -1), (key2033, -1), (key2069, -1), (key2146, -1), (key2194, -1), (key2027, -1), (key2200, -1), (key2033, -1), (key2166, -1), (key2146, 2), (key2305, 2), (key2057, 2), (key2310, 2), (key2069, 2), (key2166, 2)]

theorem rawRowCheck16952 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form13 = rawRow16952 := by decide +kernel

def row16952 : Integer.Sparse Key := [(key2027, -2), (key2033, -2), (key2057, 2), (key2063, 1), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 2), (key2152, 1), (key2166, 1), (key2194, 1), (key2200, -1), (key2239, -2), (key2246, -1), (key2253, -1), (key2303, -2), (key2305, 1), (key2310, 1)]

theorem rowCheck16952 : row16952 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16952 := by decide +kernel

theorem rowEval16952 (x : Key → ℝ) : Integer.Sparse.eval row16952 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form13) x := by
  rw [rowCheck16952, Integer.Sparse.eval_collectBalanced, rawRowCheck16952]

def rawRow16953 : Integer.Sparse Key := [(key2194, 2), (key2146, 2), (key2152, 2), (key2303, -1), (key2239, -1), (key2305, -1), (key2146, -1), (key2246, -1), (key2152, -1), (key2092, 2), (key2057, 2), (key2063, 2), (key2303, -1), (key2239, -1), (key2310, -1), (key2057, -1), (key2253, -1), (key2063, -1), (key2092, -1), (key2057, -1), (key2095, -1), (key2027, -1), (key2069, -1), (key2033, -1), (key2194, -1), (key2146, -1), (key2200, -1), (key2027, -1), (key2166, -1), (key2033, -1), (key2305, 2), (key2146, 2), (key2310, 2), (key2057, 2), (key2166, 2), (key2069, 2)]

theorem rawRowCheck16953 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form13 = rawRow16953 := by decide +kernel

def row16953 : Integer.Sparse Key := [(key2027, -2), (key2033, -2), (key2057, 2), (key2063, 1), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 2), (key2152, 1), (key2166, 1), (key2194, 1), (key2200, -1), (key2239, -2), (key2246, -1), (key2253, -1), (key2303, -2), (key2305, 1), (key2310, 1)]

theorem rowCheck16953 : row16953 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16953 := by decide +kernel

theorem rowEval16953 (x : Key → ℝ) : Integer.Sparse.eval row16953 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck16953, Integer.Sparse.eval_collectBalanced, rawRowCheck16953]

def rawRow16954 : Integer.Sparse Key := [(key2152, 2), (key2194, 2), (key2146, 2), (key2246, -1), (key2305, -1), (key2152, -1), (key2303, -1), (key2146, -1), (key2239, -1), (key2063, 2), (key2092, 2), (key2057, 2), (key2253, -1), (key2310, -1), (key2063, -1), (key2303, -1), (key2057, -1), (key2239, -1), (key2069, -1), (key2095, -1), (key2033, -1), (key2092, -1), (key2027, -1), (key2057, -1), (key2166, -1), (key2200, -1), (key2033, -1), (key2194, -1), (key2027, -1), (key2146, -1), (key2166, 2), (key2310, 2), (key2069, 2), (key2305, 2), (key2057, 2), (key2146, 2)]

theorem rawRowCheck16954 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form13 = rawRow16954 := by decide +kernel

def row16954 : Integer.Sparse Key := [(key2027, -2), (key2033, -2), (key2057, 2), (key2063, 1), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 2), (key2152, 1), (key2166, 1), (key2194, 1), (key2200, -1), (key2239, -2), (key2246, -1), (key2253, -1), (key2303, -2), (key2305, 1), (key2310, 1)]

theorem rowCheck16954 : row16954 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16954 := by decide +kernel

theorem rowEval16954 (x : Key → ℝ) : Integer.Sparse.eval row16954 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck16954, Integer.Sparse.eval_collectBalanced, rawRowCheck16954]

def rawRow16955 : Integer.Sparse Key := [(key2194, 2), (key2152, 2), (key2146, 2), (key2305, -1), (key2246, -1), (key2303, -1), (key2152, -1), (key2239, -1), (key2146, -1), (key2092, 2), (key2063, 2), (key2057, 2), (key2310, -1), (key2253, -1), (key2303, -1), (key2063, -1), (key2239, -1), (key2057, -1), (key2095, -1), (key2069, -1), (key2092, -1), (key2033, -1), (key2057, -1), (key2027, -1), (key2200, -1), (key2166, -1), (key2194, -1), (key2033, -1), (key2146, -1), (key2027, -1), (key2310, 2), (key2166, 2), (key2305, 2), (key2069, 2), (key2146, 2), (key2057, 2)]

theorem rawRowCheck16955 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form13 = rawRow16955 := by decide +kernel

def row16955 : Integer.Sparse Key := [(key2027, -2), (key2033, -2), (key2057, 2), (key2063, 1), (key2069, 1), (key2092, 1), (key2095, -1), (key2146, 2), (key2152, 1), (key2166, 1), (key2194, 1), (key2200, -1), (key2239, -2), (key2246, -1), (key2253, -1), (key2303, -2), (key2305, 1), (key2310, 1)]

theorem rowCheck16955 : row16955 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16955 := by decide +kernel

theorem rowEval16955 (x : Key → ℝ) : Integer.Sparse.eval row16955 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck16955, Integer.Sparse.eval_collectBalanced, rawRowCheck16955]

def rawRow16956 : Integer.Sparse Key := [(key2239, 2), (key2303, 2), (key2303, 2), (key2146, -1), (key2194, -1), (key2146, -1), (key2305, -1), (key2194, -1), (key2305, -1), (key2239, 2), (key2303, 2), (key2303, 2), (key2057, -1), (key2092, -1), (key2057, -1), (key2310, -1), (key2092, -1), (key2310, -1), (key2146, -1), (key2194, -1), (key2146, -1), (key2305, -1), (key2194, -1), (key2305, -1), (key2057, -1), (key2092, -1), (key2057, -1), (key2310, -1), (key2092, -1), (key2310, -1), (key2027, 2), (key2095, 2), (key2027, 2), (key2200, 2), (key2095, 2), (key2200, 2)]

theorem rawRowCheck16956 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form13 = rawRow16956 := by decide +kernel

def row16956 : Integer.Sparse Key := [(key2027, 4), (key2057, -4), (key2092, -4), (key2095, 4), (key2146, -4), (key2194, -4), (key2200, 4), (key2239, 4), (key2303, 8), (key2305, -4), (key2310, -4)]

theorem rowCheck16956 : row16956 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16956 := by decide +kernel

theorem rowEval16956 (x : Key → ℝ) : Integer.Sparse.eval row16956 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form13) x := by
  rw [rowCheck16956, Integer.Sparse.eval_collectBalanced, rawRowCheck16956]

def rawRow16957 : Integer.Sparse Key := [(key2303, 2), (key2239, 2), (key2303, 2), (key2194, -1), (key2146, -1), (key2305, -1), (key2146, -1), (key2305, -1), (key2194, -1), (key2303, 2), (key2239, 2), (key2303, 2), (key2092, -1), (key2057, -1), (key2310, -1), (key2057, -1), (key2310, -1), (key2092, -1), (key2194, -1), (key2146, -1), (key2305, -1), (key2146, -1), (key2305, -1), (key2194, -1), (key2092, -1), (key2057, -1), (key2310, -1), (key2057, -1), (key2310, -1), (key2092, -1), (key2095, 2), (key2027, 2), (key2200, 2), (key2027, 2), (key2200, 2), (key2095, 2)]

theorem rawRowCheck16957 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form13 = rawRow16957 := by decide +kernel

def row16957 : Integer.Sparse Key := [(key2027, 4), (key2057, -4), (key2092, -4), (key2095, 4), (key2146, -4), (key2194, -4), (key2200, 4), (key2239, 4), (key2303, 8), (key2305, -4), (key2310, -4)]

theorem rowCheck16957 : row16957 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16957 := by decide +kernel

theorem rowEval16957 (x : Key → ℝ) : Integer.Sparse.eval row16957 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck16957, Integer.Sparse.eval_collectBalanced, rawRowCheck16957]

def rawRow16958 : Integer.Sparse Key := [(key2303, 2), (key2303, 2), (key2239, 2), (key2305, -1), (key2305, -1), (key2194, -1), (key2194, -1), (key2146, -1), (key2146, -1), (key2303, 2), (key2303, 2), (key2239, 2), (key2310, -1), (key2310, -1), (key2092, -1), (key2092, -1), (key2057, -1), (key2057, -1), (key2305, -1), (key2305, -1), (key2194, -1), (key2194, -1), (key2146, -1), (key2146, -1), (key2310, -1), (key2310, -1), (key2092, -1), (key2092, -1), (key2057, -1), (key2057, -1), (key2200, 2), (key2200, 2), (key2095, 2), (key2095, 2), (key2027, 2), (key2027, 2)]

theorem rawRowCheck16958 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form13 = rawRow16958 := by decide +kernel

def row16958 : Integer.Sparse Key := [(key2027, 4), (key2057, -4), (key2092, -4), (key2095, 4), (key2146, -4), (key2194, -4), (key2200, 4), (key2239, 4), (key2303, 8), (key2305, -4), (key2310, -4)]

theorem rowCheck16958 : row16958 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16958 := by decide +kernel

theorem rowEval16958 (x : Key → ℝ) : Integer.Sparse.eval row16958 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck16958, Integer.Sparse.eval_collectBalanced, rawRowCheck16958]

def rawRow16959 : Integer.Sparse Key := [(key2057, -1), (key2063, -1), (key2057, -1), (key2069, -1), (key2063, -1), (key2069, -1), (key2092, 2), (key2092, 2), (key2095, 2), (key2146, 1), (key2152, 1), (key2146, 1), (key2166, 1), (key2152, 1), (key2166, 1), (key2194, -2), (key2194, -2), (key2200, -2), (key2057, -1), (key2063, -1), (key2057, -1), (key2069, -1), (key2063, -1), (key2069, -1), (key2146, 1), (key2152, 1), (key2146, 1), (key2166, 1), (key2152, 1), (key2166, 1), (key2092, 2), (key2092, 2), (key2095, 2), (key2194, -2), (key2194, -2), (key2200, -2)]

theorem rawRowCheck16959 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form14 = rawRow16959 := by decide +kernel

def row16959 : Integer.Sparse Key := [(key2057, -4), (key2063, -4), (key2069, -4), (key2092, 8), (key2095, 4), (key2146, 4), (key2152, 4), (key2166, 4), (key2194, -8), (key2200, -4)]

theorem rowCheck16959 : row16959 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16959 := by decide +kernel

theorem rowEval16959 (x : Key → ℝ) : Integer.Sparse.eval row16959 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form14) x := by
  rw [rowCheck16959, Integer.Sparse.eval_collectBalanced, rawRowCheck16959]

def rawRow16960 : Integer.Sparse Key := [(key2063, -1), (key2057, -1), (key2069, -1), (key2057, -1), (key2069, -1), (key2063, -1), (key2092, 2), (key2095, 2), (key2092, 2), (key2152, 1), (key2146, 1), (key2166, 1), (key2146, 1), (key2166, 1), (key2152, 1), (key2194, -2), (key2200, -2), (key2194, -2), (key2063, -1), (key2057, -1), (key2069, -1), (key2057, -1), (key2069, -1), (key2063, -1), (key2152, 1), (key2146, 1), (key2166, 1), (key2146, 1), (key2166, 1), (key2152, 1), (key2092, 2), (key2095, 2), (key2092, 2), (key2194, -2), (key2200, -2), (key2194, -2)]

theorem rawRowCheck16960 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form14 = rawRow16960 := by decide +kernel

def row16960 : Integer.Sparse Key := [(key2057, -4), (key2063, -4), (key2069, -4), (key2092, 8), (key2095, 4), (key2146, 4), (key2152, 4), (key2166, 4), (key2194, -8), (key2200, -4)]

theorem rowCheck16960 : row16960 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16960 := by decide +kernel

theorem rowEval16960 (x : Key → ℝ) : Integer.Sparse.eval row16960 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck16960, Integer.Sparse.eval_collectBalanced, rawRowCheck16960]

def rawRow16961 : Integer.Sparse Key := [(key2069, -1), (key2069, -1), (key2063, -1), (key2063, -1), (key2057, -1), (key2057, -1), (key2095, 2), (key2092, 2), (key2092, 2), (key2166, 1), (key2166, 1), (key2152, 1), (key2152, 1), (key2146, 1), (key2146, 1), (key2200, -2), (key2194, -2), (key2194, -2), (key2069, -1), (key2069, -1), (key2063, -1), (key2063, -1), (key2057, -1), (key2057, -1), (key2166, 1), (key2166, 1), (key2152, 1), (key2152, 1), (key2146, 1), (key2146, 1), (key2095, 2), (key2092, 2), (key2092, 2), (key2200, -2), (key2194, -2), (key2194, -2)]

theorem rawRowCheck16961 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form14 = rawRow16961 := by decide +kernel

def row16961 : Integer.Sparse Key := [(key2057, -4), (key2063, -4), (key2069, -4), (key2092, 8), (key2095, 4), (key2146, 4), (key2152, 4), (key2166, 4), (key2194, -8), (key2200, -4)]

theorem rowCheck16961 : row16961 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16961 := by decide +kernel

theorem rowEval16961 (x : Key → ℝ) : Integer.Sparse.eval row16961 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck16961, Integer.Sparse.eval_collectBalanced, rawRowCheck16961]

def rawRow16962 : Integer.Sparse Key := [(key2027, -1), (key2033, -1), (key2057, -1), (key2069, -1), (key2092, -1), (key2095, -1), (key2033, 2), (key2063, 2), (key2069, 2), (key2027, 1), (key2033, 1), (key2146, 1), (key2166, 1), (key2194, 1), (key2200, 1), (key2033, -2), (key2152, -2), (key2166, -2), (key2146, -1), (key2152, -1), (key2239, -1), (key2246, -1), (key2303, -1), (key2305, -1), (key2057, 1), (key2063, 1), (key2239, 1), (key2253, 1), (key2303, 1), (key2310, 1), (key2194, 2), (key2303, 2), (key2305, 2), (key2092, -2), (key2303, -2), (key2310, -2)]

theorem rawRowCheck16962 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form14 = rawRow16962 := by decide +kernel

def row16962 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2092, -3), (key2095, -1), (key2152, -3), (key2166, -1), (key2194, 3), (key2200, 1), (key2246, -1), (key2253, 1), (key2305, 1), (key2310, -1)]

theorem rowCheck16962 : row16962 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16962 := by decide +kernel

theorem rowEval16962 (x : Key → ℝ) : Integer.Sparse.eval row16962 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form14) x := by
  rw [rowCheck16962, Integer.Sparse.eval_collectBalanced, rawRowCheck16962]

def rawRow16963 : Integer.Sparse Key := [(key2033, -1), (key2027, -1), (key2069, -1), (key2057, -1), (key2095, -1), (key2092, -1), (key2033, 2), (key2069, 2), (key2063, 2), (key2033, 1), (key2027, 1), (key2166, 1), (key2146, 1), (key2200, 1), (key2194, 1), (key2033, -2), (key2166, -2), (key2152, -2), (key2152, -1), (key2146, -1), (key2246, -1), (key2239, -1), (key2305, -1), (key2303, -1), (key2063, 1), (key2057, 1), (key2253, 1), (key2239, 1), (key2310, 1), (key2303, 1), (key2194, 2), (key2305, 2), (key2303, 2), (key2092, -2), (key2310, -2), (key2303, -2)]

theorem rawRowCheck16963 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form14 = rawRow16963 := by decide +kernel

def row16963 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2092, -3), (key2095, -1), (key2152, -3), (key2166, -1), (key2194, 3), (key2200, 1), (key2246, -1), (key2253, 1), (key2305, 1), (key2310, -1)]

theorem rowCheck16963 : row16963 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16963 := by decide +kernel

theorem rowEval16963 (x : Key → ℝ) : Integer.Sparse.eval row16963 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck16963, Integer.Sparse.eval_collectBalanced, rawRowCheck16963]

def rawRow16964 : Integer.Sparse Key := [(key2057, -1), (key2092, -1), (key2027, -1), (key2095, -1), (key2033, -1), (key2069, -1), (key2063, 2), (key2033, 2), (key2069, 2), (key2146, 1), (key2194, 1), (key2027, 1), (key2200, 1), (key2033, 1), (key2166, 1), (key2152, -2), (key2033, -2), (key2166, -2), (key2239, -1), (key2303, -1), (key2146, -1), (key2305, -1), (key2152, -1), (key2246, -1), (key2239, 1), (key2303, 1), (key2057, 1), (key2310, 1), (key2063, 1), (key2253, 1), (key2303, 2), (key2194, 2), (key2305, 2), (key2303, -2), (key2092, -2), (key2310, -2)]

theorem rawRowCheck16964 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form14 = rawRow16964 := by decide +kernel

def row16964 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2092, -3), (key2095, -1), (key2152, -3), (key2166, -1), (key2194, 3), (key2200, 1), (key2246, -1), (key2253, 1), (key2305, 1), (key2310, -1)]

theorem rowCheck16964 : row16964 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16964 := by decide +kernel

theorem rowEval16964 (x : Key → ℝ) : Integer.Sparse.eval row16964 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form14) x := by
  rw [rowCheck16964, Integer.Sparse.eval_collectBalanced, rawRowCheck16964]

def rawRow16965 : Integer.Sparse Key := [(key2092, -1), (key2057, -1), (key2095, -1), (key2027, -1), (key2069, -1), (key2033, -1), (key2063, 2), (key2069, 2), (key2033, 2), (key2194, 1), (key2146, 1), (key2200, 1), (key2027, 1), (key2166, 1), (key2033, 1), (key2152, -2), (key2166, -2), (key2033, -2), (key2303, -1), (key2239, -1), (key2305, -1), (key2146, -1), (key2246, -1), (key2152, -1), (key2303, 1), (key2239, 1), (key2310, 1), (key2057, 1), (key2253, 1), (key2063, 1), (key2303, 2), (key2305, 2), (key2194, 2), (key2303, -2), (key2310, -2), (key2092, -2)]

theorem rawRowCheck16965 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form14 = rawRow16965 := by decide +kernel

def row16965 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2092, -3), (key2095, -1), (key2152, -3), (key2166, -1), (key2194, 3), (key2200, 1), (key2246, -1), (key2253, 1), (key2305, 1), (key2310, -1)]

theorem rowCheck16965 : row16965 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16965 := by decide +kernel

theorem rowEval16965 (x : Key → ℝ) : Integer.Sparse.eval row16965 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck16965, Integer.Sparse.eval_collectBalanced, rawRowCheck16965]

def rawRow16966 : Integer.Sparse Key := [(key2069, -1), (key2095, -1), (key2033, -1), (key2092, -1), (key2027, -1), (key2057, -1), (key2069, 2), (key2033, 2), (key2063, 2), (key2166, 1), (key2200, 1), (key2033, 1), (key2194, 1), (key2027, 1), (key2146, 1), (key2166, -2), (key2033, -2), (key2152, -2), (key2246, -1), (key2305, -1), (key2152, -1), (key2303, -1), (key2146, -1), (key2239, -1), (key2253, 1), (key2310, 1), (key2063, 1), (key2303, 1), (key2057, 1), (key2239, 1), (key2305, 2), (key2194, 2), (key2303, 2), (key2310, -2), (key2092, -2), (key2303, -2)]

theorem rawRowCheck16966 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form14 = rawRow16966 := by decide +kernel

def row16966 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2092, -3), (key2095, -1), (key2152, -3), (key2166, -1), (key2194, 3), (key2200, 1), (key2246, -1), (key2253, 1), (key2305, 1), (key2310, -1)]

theorem rowCheck16966 : row16966 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16966 := by decide +kernel

theorem rowEval16966 (x : Key → ℝ) : Integer.Sparse.eval row16966 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck16966, Integer.Sparse.eval_collectBalanced, rawRowCheck16966]

def rawRow16967 : Integer.Sparse Key := [(key2095, -1), (key2069, -1), (key2092, -1), (key2033, -1), (key2057, -1), (key2027, -1), (key2069, 2), (key2063, 2), (key2033, 2), (key2200, 1), (key2166, 1), (key2194, 1), (key2033, 1), (key2146, 1), (key2027, 1), (key2166, -2), (key2152, -2), (key2033, -2), (key2305, -1), (key2246, -1), (key2303, -1), (key2152, -1), (key2239, -1), (key2146, -1), (key2310, 1), (key2253, 1), (key2303, 1), (key2063, 1), (key2239, 1), (key2057, 1), (key2305, 2), (key2303, 2), (key2194, 2), (key2310, -2), (key2303, -2), (key2092, -2)]

theorem rawRowCheck16967 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form14 = rawRow16967 := by decide +kernel

def row16967 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2092, -3), (key2095, -1), (key2152, -3), (key2166, -1), (key2194, 3), (key2200, 1), (key2246, -1), (key2253, 1), (key2305, 1), (key2310, -1)]

theorem rowCheck16967 : row16967 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16967 := by decide +kernel

theorem rowEval16967 (x : Key → ℝ) : Integer.Sparse.eval row16967 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck16967, Integer.Sparse.eval_collectBalanced, rawRowCheck16967]

def rawRow16968 : Integer.Sparse Key := [(key2146, -1), (key2152, -1), (key2239, -1), (key2246, -1), (key2303, -1), (key2305, -1), (key2194, 2), (key2303, 2), (key2305, 2), (key2057, 1), (key2063, 1), (key2239, 1), (key2253, 1), (key2303, 1), (key2310, 1), (key2092, -2), (key2303, -2), (key2310, -2), (key2027, -1), (key2033, -1), (key2057, -1), (key2069, -1), (key2092, -1), (key2095, -1), (key2027, 1), (key2033, 1), (key2146, 1), (key2166, 1), (key2194, 1), (key2200, 1), (key2033, 2), (key2063, 2), (key2069, 2), (key2033, -2), (key2152, -2), (key2166, -2)]

theorem rawRowCheck16968 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form14 = rawRow16968 := by decide +kernel

def row16968 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2092, -3), (key2095, -1), (key2152, -3), (key2166, -1), (key2194, 3), (key2200, 1), (key2246, -1), (key2253, 1), (key2305, 1), (key2310, -1)]

theorem rowCheck16968 : row16968 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16968 := by decide +kernel

theorem rowEval16968 (x : Key → ℝ) : Integer.Sparse.eval row16968 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form14) x := by
  rw [rowCheck16968, Integer.Sparse.eval_collectBalanced, rawRowCheck16968]

def rawRow16969 : Integer.Sparse Key := [(key2152, -1), (key2146, -1), (key2246, -1), (key2239, -1), (key2305, -1), (key2303, -1), (key2194, 2), (key2305, 2), (key2303, 2), (key2063, 1), (key2057, 1), (key2253, 1), (key2239, 1), (key2310, 1), (key2303, 1), (key2092, -2), (key2310, -2), (key2303, -2), (key2033, -1), (key2027, -1), (key2069, -1), (key2057, -1), (key2095, -1), (key2092, -1), (key2033, 1), (key2027, 1), (key2166, 1), (key2146, 1), (key2200, 1), (key2194, 1), (key2033, 2), (key2069, 2), (key2063, 2), (key2033, -2), (key2166, -2), (key2152, -2)]

theorem rawRowCheck16969 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form14 = rawRow16969 := by decide +kernel

def row16969 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2092, -3), (key2095, -1), (key2152, -3), (key2166, -1), (key2194, 3), (key2200, 1), (key2246, -1), (key2253, 1), (key2305, 1), (key2310, -1)]

theorem rowCheck16969 : row16969 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16969 := by decide +kernel

theorem rowEval16969 (x : Key → ℝ) : Integer.Sparse.eval row16969 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck16969, Integer.Sparse.eval_collectBalanced, rawRowCheck16969]

def rawRow16970 : Integer.Sparse Key := [(key2239, -1), (key2303, -1), (key2146, -1), (key2305, -1), (key2152, -1), (key2246, -1), (key2303, 2), (key2194, 2), (key2305, 2), (key2239, 1), (key2303, 1), (key2057, 1), (key2310, 1), (key2063, 1), (key2253, 1), (key2303, -2), (key2092, -2), (key2310, -2), (key2057, -1), (key2092, -1), (key2027, -1), (key2095, -1), (key2033, -1), (key2069, -1), (key2146, 1), (key2194, 1), (key2027, 1), (key2200, 1), (key2033, 1), (key2166, 1), (key2063, 2), (key2033, 2), (key2069, 2), (key2152, -2), (key2033, -2), (key2166, -2)]

theorem rawRowCheck16970 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form14 = rawRow16970 := by decide +kernel

def row16970 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2092, -3), (key2095, -1), (key2152, -3), (key2166, -1), (key2194, 3), (key2200, 1), (key2246, -1), (key2253, 1), (key2305, 1), (key2310, -1)]

theorem rowCheck16970 : row16970 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16970 := by decide +kernel

theorem rowEval16970 (x : Key → ℝ) : Integer.Sparse.eval row16970 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form14) x := by
  rw [rowCheck16970, Integer.Sparse.eval_collectBalanced, rawRowCheck16970]

def rawRow16971 : Integer.Sparse Key := [(key2303, -1), (key2239, -1), (key2305, -1), (key2146, -1), (key2246, -1), (key2152, -1), (key2303, 2), (key2305, 2), (key2194, 2), (key2303, 1), (key2239, 1), (key2310, 1), (key2057, 1), (key2253, 1), (key2063, 1), (key2303, -2), (key2310, -2), (key2092, -2), (key2092, -1), (key2057, -1), (key2095, -1), (key2027, -1), (key2069, -1), (key2033, -1), (key2194, 1), (key2146, 1), (key2200, 1), (key2027, 1), (key2166, 1), (key2033, 1), (key2063, 2), (key2069, 2), (key2033, 2), (key2152, -2), (key2166, -2), (key2033, -2)]

theorem rawRowCheck16971 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form14 = rawRow16971 := by decide +kernel

def row16971 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2092, -3), (key2095, -1), (key2152, -3), (key2166, -1), (key2194, 3), (key2200, 1), (key2246, -1), (key2253, 1), (key2305, 1), (key2310, -1)]

theorem rowCheck16971 : row16971 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16971 := by decide +kernel

theorem rowEval16971 (x : Key → ℝ) : Integer.Sparse.eval row16971 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck16971, Integer.Sparse.eval_collectBalanced, rawRowCheck16971]

def rawRow16972 : Integer.Sparse Key := [(key2246, -1), (key2305, -1), (key2152, -1), (key2303, -1), (key2146, -1), (key2239, -1), (key2305, 2), (key2194, 2), (key2303, 2), (key2253, 1), (key2310, 1), (key2063, 1), (key2303, 1), (key2057, 1), (key2239, 1), (key2310, -2), (key2092, -2), (key2303, -2), (key2069, -1), (key2095, -1), (key2033, -1), (key2092, -1), (key2027, -1), (key2057, -1), (key2166, 1), (key2200, 1), (key2033, 1), (key2194, 1), (key2027, 1), (key2146, 1), (key2069, 2), (key2033, 2), (key2063, 2), (key2166, -2), (key2033, -2), (key2152, -2)]

theorem rawRowCheck16972 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form14 = rawRow16972 := by decide +kernel

def row16972 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2092, -3), (key2095, -1), (key2152, -3), (key2166, -1), (key2194, 3), (key2200, 1), (key2246, -1), (key2253, 1), (key2305, 1), (key2310, -1)]

theorem rowCheck16972 : row16972 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16972 := by decide +kernel

theorem rowEval16972 (x : Key → ℝ) : Integer.Sparse.eval row16972 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck16972, Integer.Sparse.eval_collectBalanced, rawRowCheck16972]

def rawRow16973 : Integer.Sparse Key := [(key2305, -1), (key2246, -1), (key2303, -1), (key2152, -1), (key2239, -1), (key2146, -1), (key2305, 2), (key2303, 2), (key2194, 2), (key2310, 1), (key2253, 1), (key2303, 1), (key2063, 1), (key2239, 1), (key2057, 1), (key2310, -2), (key2303, -2), (key2092, -2), (key2095, -1), (key2069, -1), (key2092, -1), (key2033, -1), (key2057, -1), (key2027, -1), (key2200, 1), (key2166, 1), (key2194, 1), (key2033, 1), (key2146, 1), (key2027, 1), (key2069, 2), (key2063, 2), (key2033, 2), (key2166, -2), (key2152, -2), (key2033, -2)]

theorem rawRowCheck16973 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form14 = rawRow16973 := by decide +kernel

def row16973 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2092, -3), (key2095, -1), (key2152, -3), (key2166, -1), (key2194, 3), (key2200, 1), (key2246, -1), (key2253, 1), (key2305, 1), (key2310, -1)]

theorem rowCheck16973 : row16973 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16973 := by decide +kernel

theorem rowEval16973 (x : Key → ℝ) : Integer.Sparse.eval row16973 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck16973, Integer.Sparse.eval_collectBalanced, rawRowCheck16973]

def rawRow16974 : Integer.Sparse Key := [(key2146, -1), (key2194, -1), (key2146, -1), (key2305, -1), (key2194, -1), (key2305, -1), (key2152, 2), (key2152, 2), (key2246, 2), (key2057, 1), (key2092, 1), (key2057, 1), (key2310, 1), (key2092, 1), (key2310, 1), (key2063, -2), (key2063, -2), (key2253, -2), (key2146, -1), (key2194, -1), (key2146, -1), (key2305, -1), (key2194, -1), (key2305, -1), (key2057, 1), (key2092, 1), (key2057, 1), (key2310, 1), (key2092, 1), (key2310, 1), (key2152, 2), (key2152, 2), (key2246, 2), (key2063, -2), (key2063, -2), (key2253, -2)]

theorem rawRowCheck16974 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form14 = rawRow16974 := by decide +kernel

def row16974 : Integer.Sparse Key := [(key2057, 4), (key2063, -8), (key2092, 4), (key2146, -4), (key2152, 8), (key2194, -4), (key2246, 4), (key2253, -4), (key2305, -4), (key2310, 4)]

theorem rowCheck16974 : row16974 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16974 := by decide +kernel

theorem rowEval16974 (x : Key → ℝ) : Integer.Sparse.eval row16974 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form14) x := by
  rw [rowCheck16974, Integer.Sparse.eval_collectBalanced, rawRowCheck16974]

def rawRow16975 : Integer.Sparse Key := [(key2194, -1), (key2146, -1), (key2305, -1), (key2146, -1), (key2305, -1), (key2194, -1), (key2152, 2), (key2246, 2), (key2152, 2), (key2092, 1), (key2057, 1), (key2310, 1), (key2057, 1), (key2310, 1), (key2092, 1), (key2063, -2), (key2253, -2), (key2063, -2), (key2194, -1), (key2146, -1), (key2305, -1), (key2146, -1), (key2305, -1), (key2194, -1), (key2092, 1), (key2057, 1), (key2310, 1), (key2057, 1), (key2310, 1), (key2092, 1), (key2152, 2), (key2246, 2), (key2152, 2), (key2063, -2), (key2253, -2), (key2063, -2)]

theorem rawRowCheck16975 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form14 = rawRow16975 := by decide +kernel

def row16975 : Integer.Sparse Key := [(key2057, 4), (key2063, -8), (key2092, 4), (key2146, -4), (key2152, 8), (key2194, -4), (key2246, 4), (key2253, -4), (key2305, -4), (key2310, 4)]

theorem rowCheck16975 : row16975 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16975 := by decide +kernel

theorem rowEval16975 (x : Key → ℝ) : Integer.Sparse.eval row16975 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck16975, Integer.Sparse.eval_collectBalanced, rawRowCheck16975]

def rawRow16976 : Integer.Sparse Key := [(key2305, -1), (key2305, -1), (key2194, -1), (key2194, -1), (key2146, -1), (key2146, -1), (key2246, 2), (key2152, 2), (key2152, 2), (key2310, 1), (key2310, 1), (key2092, 1), (key2092, 1), (key2057, 1), (key2057, 1), (key2253, -2), (key2063, -2), (key2063, -2), (key2305, -1), (key2305, -1), (key2194, -1), (key2194, -1), (key2146, -1), (key2146, -1), (key2310, 1), (key2310, 1), (key2092, 1), (key2092, 1), (key2057, 1), (key2057, 1), (key2246, 2), (key2152, 2), (key2152, 2), (key2253, -2), (key2063, -2), (key2063, -2)]

theorem rawRowCheck16976 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form14 = rawRow16976 := by decide +kernel

def row16976 : Integer.Sparse Key := [(key2057, 4), (key2063, -8), (key2092, 4), (key2146, -4), (key2152, 8), (key2194, -4), (key2246, 4), (key2253, -4), (key2305, -4), (key2310, 4)]

theorem rowCheck16976 : row16976 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16976 := by decide +kernel

theorem rowEval16976 (x : Key → ℝ) : Integer.Sparse.eval row16976 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck16976, Integer.Sparse.eval_collectBalanced, rawRowCheck16976]

def rawRow16977 : Integer.Sparse Key := [(key2058, -1), (key2063, -1), (key2058, -1), (key2069, -1), (key2063, -1), (key2069, -1), (key2079, 2), (key2079, 2), (key2085, 2), (key2147, 1), (key2152, 1), (key2147, 1), (key2166, 1), (key2152, 1), (key2166, 1), (key2176, -2), (key2176, -2), (key2187, -2), (key2058, -1), (key2063, -1), (key2058, -1), (key2069, -1), (key2063, -1), (key2069, -1), (key2147, 1), (key2152, 1), (key2147, 1), (key2166, 1), (key2152, 1), (key2166, 1), (key2079, 2), (key2079, 2), (key2085, 2), (key2176, -2), (key2176, -2), (key2187, -2)]

theorem rawRowCheck16977 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form15 = rawRow16977 := by decide +kernel

def row16977 : Integer.Sparse Key := [(key2058, -4), (key2063, -4), (key2069, -4), (key2079, 8), (key2085, 4), (key2147, 4), (key2152, 4), (key2166, 4), (key2176, -8), (key2187, -4)]

theorem rowCheck16977 : row16977 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16977 := by decide +kernel

theorem rowEval16977 (x : Key → ℝ) : Integer.Sparse.eval row16977 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form15) x := by
  rw [rowCheck16977, Integer.Sparse.eval_collectBalanced, rawRowCheck16977]

def rawRow16978 : Integer.Sparse Key := [(key2063, -1), (key2058, -1), (key2069, -1), (key2058, -1), (key2069, -1), (key2063, -1), (key2079, 2), (key2085, 2), (key2079, 2), (key2152, 1), (key2147, 1), (key2166, 1), (key2147, 1), (key2166, 1), (key2152, 1), (key2176, -2), (key2187, -2), (key2176, -2), (key2063, -1), (key2058, -1), (key2069, -1), (key2058, -1), (key2069, -1), (key2063, -1), (key2152, 1), (key2147, 1), (key2166, 1), (key2147, 1), (key2166, 1), (key2152, 1), (key2079, 2), (key2085, 2), (key2079, 2), (key2176, -2), (key2187, -2), (key2176, -2)]

theorem rawRowCheck16978 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form15 = rawRow16978 := by decide +kernel

def row16978 : Integer.Sparse Key := [(key2058, -4), (key2063, -4), (key2069, -4), (key2079, 8), (key2085, 4), (key2147, 4), (key2152, 4), (key2166, 4), (key2176, -8), (key2187, -4)]

theorem rowCheck16978 : row16978 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16978 := by decide +kernel

theorem rowEval16978 (x : Key → ℝ) : Integer.Sparse.eval row16978 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck16978, Integer.Sparse.eval_collectBalanced, rawRowCheck16978]

def rawRow16979 : Integer.Sparse Key := [(key2069, -1), (key2069, -1), (key2063, -1), (key2063, -1), (key2058, -1), (key2058, -1), (key2085, 2), (key2079, 2), (key2079, 2), (key2166, 1), (key2166, 1), (key2152, 1), (key2152, 1), (key2147, 1), (key2147, 1), (key2187, -2), (key2176, -2), (key2176, -2), (key2069, -1), (key2069, -1), (key2063, -1), (key2063, -1), (key2058, -1), (key2058, -1), (key2166, 1), (key2166, 1), (key2152, 1), (key2152, 1), (key2147, 1), (key2147, 1), (key2085, 2), (key2079, 2), (key2079, 2), (key2187, -2), (key2176, -2), (key2176, -2)]

theorem rawRowCheck16979 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form15 = rawRow16979 := by decide +kernel

def row16979 : Integer.Sparse Key := [(key2058, -4), (key2063, -4), (key2069, -4), (key2079, 8), (key2085, 4), (key2147, 4), (key2152, 4), (key2166, 4), (key2176, -8), (key2187, -4)]

theorem rowCheck16979 : row16979 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16979 := by decide +kernel

theorem rowEval16979 (x : Key → ℝ) : Integer.Sparse.eval row16979 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck16979, Integer.Sparse.eval_collectBalanced, rawRowCheck16979]

def rawRow16980 : Integer.Sparse Key := [(key2028, -1), (key2033, -1), (key2058, -1), (key2069, -1), (key2079, -1), (key2085, -1), (key2033, 2), (key2063, 2), (key2069, 2), (key2028, 1), (key2033, 1), (key2147, 1), (key2166, 1), (key2176, 1), (key2187, 1), (key2033, -2), (key2152, -2), (key2166, -2), (key2147, -1), (key2152, -1), (key2240, -1), (key2246, -1), (key2276, -1), (key2279, -1), (key2058, 1), (key2063, 1), (key2240, 1), (key2253, 1), (key2276, 1), (key2287, 1), (key2176, 2), (key2276, 2), (key2279, 2), (key2079, -2), (key2276, -2), (key2287, -2)]

theorem rawRowCheck16980 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form15 = rawRow16980 := by decide +kernel

def row16980 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2079, -3), (key2085, -1), (key2152, -3), (key2166, -1), (key2176, 3), (key2187, 1), (key2246, -1), (key2253, 1), (key2279, 1), (key2287, -1)]

theorem rowCheck16980 : row16980 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16980 := by decide +kernel

theorem rowEval16980 (x : Key → ℝ) : Integer.Sparse.eval row16980 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form15) x := by
  rw [rowCheck16980, Integer.Sparse.eval_collectBalanced, rawRowCheck16980]

def rawRow16981 : Integer.Sparse Key := [(key2033, -1), (key2028, -1), (key2069, -1), (key2058, -1), (key2085, -1), (key2079, -1), (key2033, 2), (key2069, 2), (key2063, 2), (key2033, 1), (key2028, 1), (key2166, 1), (key2147, 1), (key2187, 1), (key2176, 1), (key2033, -2), (key2166, -2), (key2152, -2), (key2152, -1), (key2147, -1), (key2246, -1), (key2240, -1), (key2279, -1), (key2276, -1), (key2063, 1), (key2058, 1), (key2253, 1), (key2240, 1), (key2287, 1), (key2276, 1), (key2176, 2), (key2279, 2), (key2276, 2), (key2079, -2), (key2287, -2), (key2276, -2)]

theorem rawRowCheck16981 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form15 = rawRow16981 := by decide +kernel

def row16981 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2079, -3), (key2085, -1), (key2152, -3), (key2166, -1), (key2176, 3), (key2187, 1), (key2246, -1), (key2253, 1), (key2279, 1), (key2287, -1)]

theorem rowCheck16981 : row16981 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16981 := by decide +kernel

theorem rowEval16981 (x : Key → ℝ) : Integer.Sparse.eval row16981 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck16981, Integer.Sparse.eval_collectBalanced, rawRowCheck16981]

def rawRow16982 : Integer.Sparse Key := [(key2058, -1), (key2079, -1), (key2028, -1), (key2085, -1), (key2033, -1), (key2069, -1), (key2063, 2), (key2033, 2), (key2069, 2), (key2147, 1), (key2176, 1), (key2028, 1), (key2187, 1), (key2033, 1), (key2166, 1), (key2152, -2), (key2033, -2), (key2166, -2), (key2240, -1), (key2276, -1), (key2147, -1), (key2279, -1), (key2152, -1), (key2246, -1), (key2240, 1), (key2276, 1), (key2058, 1), (key2287, 1), (key2063, 1), (key2253, 1), (key2276, 2), (key2176, 2), (key2279, 2), (key2276, -2), (key2079, -2), (key2287, -2)]

theorem rawRowCheck16982 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form15 = rawRow16982 := by decide +kernel

def row16982 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2079, -3), (key2085, -1), (key2152, -3), (key2166, -1), (key2176, 3), (key2187, 1), (key2246, -1), (key2253, 1), (key2279, 1), (key2287, -1)]

theorem rowCheck16982 : row16982 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16982 := by decide +kernel

theorem rowEval16982 (x : Key → ℝ) : Integer.Sparse.eval row16982 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form15) x := by
  rw [rowCheck16982, Integer.Sparse.eval_collectBalanced, rawRowCheck16982]

def rawRow16983 : Integer.Sparse Key := [(key2079, -1), (key2058, -1), (key2085, -1), (key2028, -1), (key2069, -1), (key2033, -1), (key2063, 2), (key2069, 2), (key2033, 2), (key2176, 1), (key2147, 1), (key2187, 1), (key2028, 1), (key2166, 1), (key2033, 1), (key2152, -2), (key2166, -2), (key2033, -2), (key2276, -1), (key2240, -1), (key2279, -1), (key2147, -1), (key2246, -1), (key2152, -1), (key2276, 1), (key2240, 1), (key2287, 1), (key2058, 1), (key2253, 1), (key2063, 1), (key2276, 2), (key2279, 2), (key2176, 2), (key2276, -2), (key2287, -2), (key2079, -2)]

theorem rawRowCheck16983 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form15 = rawRow16983 := by decide +kernel

def row16983 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2079, -3), (key2085, -1), (key2152, -3), (key2166, -1), (key2176, 3), (key2187, 1), (key2246, -1), (key2253, 1), (key2279, 1), (key2287, -1)]

theorem rowCheck16983 : row16983 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16983 := by decide +kernel

theorem rowEval16983 (x : Key → ℝ) : Integer.Sparse.eval row16983 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck16983, Integer.Sparse.eval_collectBalanced, rawRowCheck16983]

def rawRow16984 : Integer.Sparse Key := [(key2069, -1), (key2085, -1), (key2033, -1), (key2079, -1), (key2028, -1), (key2058, -1), (key2069, 2), (key2033, 2), (key2063, 2), (key2166, 1), (key2187, 1), (key2033, 1), (key2176, 1), (key2028, 1), (key2147, 1), (key2166, -2), (key2033, -2), (key2152, -2), (key2246, -1), (key2279, -1), (key2152, -1), (key2276, -1), (key2147, -1), (key2240, -1), (key2253, 1), (key2287, 1), (key2063, 1), (key2276, 1), (key2058, 1), (key2240, 1), (key2279, 2), (key2176, 2), (key2276, 2), (key2287, -2), (key2079, -2), (key2276, -2)]

theorem rawRowCheck16984 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form15 = rawRow16984 := by decide +kernel

def row16984 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2079, -3), (key2085, -1), (key2152, -3), (key2166, -1), (key2176, 3), (key2187, 1), (key2246, -1), (key2253, 1), (key2279, 1), (key2287, -1)]

theorem rowCheck16984 : row16984 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16984 := by decide +kernel

theorem rowEval16984 (x : Key → ℝ) : Integer.Sparse.eval row16984 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck16984, Integer.Sparse.eval_collectBalanced, rawRowCheck16984]

def rawRow16985 : Integer.Sparse Key := [(key2085, -1), (key2069, -1), (key2079, -1), (key2033, -1), (key2058, -1), (key2028, -1), (key2069, 2), (key2063, 2), (key2033, 2), (key2187, 1), (key2166, 1), (key2176, 1), (key2033, 1), (key2147, 1), (key2028, 1), (key2166, -2), (key2152, -2), (key2033, -2), (key2279, -1), (key2246, -1), (key2276, -1), (key2152, -1), (key2240, -1), (key2147, -1), (key2287, 1), (key2253, 1), (key2276, 1), (key2063, 1), (key2240, 1), (key2058, 1), (key2279, 2), (key2276, 2), (key2176, 2), (key2287, -2), (key2276, -2), (key2079, -2)]

theorem rawRowCheck16985 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form15 = rawRow16985 := by decide +kernel

def row16985 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2079, -3), (key2085, -1), (key2152, -3), (key2166, -1), (key2176, 3), (key2187, 1), (key2246, -1), (key2253, 1), (key2279, 1), (key2287, -1)]

theorem rowCheck16985 : row16985 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16985 := by decide +kernel

theorem rowEval16985 (x : Key → ℝ) : Integer.Sparse.eval row16985 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck16985, Integer.Sparse.eval_collectBalanced, rawRowCheck16985]

def rawRow16986 : Integer.Sparse Key := [(key2147, -1), (key2152, -1), (key2240, -1), (key2246, -1), (key2276, -1), (key2279, -1), (key2176, 2), (key2276, 2), (key2279, 2), (key2058, 1), (key2063, 1), (key2240, 1), (key2253, 1), (key2276, 1), (key2287, 1), (key2079, -2), (key2276, -2), (key2287, -2), (key2028, -1), (key2033, -1), (key2058, -1), (key2069, -1), (key2079, -1), (key2085, -1), (key2028, 1), (key2033, 1), (key2147, 1), (key2166, 1), (key2176, 1), (key2187, 1), (key2033, 2), (key2063, 2), (key2069, 2), (key2033, -2), (key2152, -2), (key2166, -2)]

theorem rawRowCheck16986 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form15 = rawRow16986 := by decide +kernel

def row16986 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2079, -3), (key2085, -1), (key2152, -3), (key2166, -1), (key2176, 3), (key2187, 1), (key2246, -1), (key2253, 1), (key2279, 1), (key2287, -1)]

theorem rowCheck16986 : row16986 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16986 := by decide +kernel

theorem rowEval16986 (x : Key → ℝ) : Integer.Sparse.eval row16986 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form15) x := by
  rw [rowCheck16986, Integer.Sparse.eval_collectBalanced, rawRowCheck16986]

def rawRow16987 : Integer.Sparse Key := [(key2152, -1), (key2147, -1), (key2246, -1), (key2240, -1), (key2279, -1), (key2276, -1), (key2176, 2), (key2279, 2), (key2276, 2), (key2063, 1), (key2058, 1), (key2253, 1), (key2240, 1), (key2287, 1), (key2276, 1), (key2079, -2), (key2287, -2), (key2276, -2), (key2033, -1), (key2028, -1), (key2069, -1), (key2058, -1), (key2085, -1), (key2079, -1), (key2033, 1), (key2028, 1), (key2166, 1), (key2147, 1), (key2187, 1), (key2176, 1), (key2033, 2), (key2069, 2), (key2063, 2), (key2033, -2), (key2166, -2), (key2152, -2)]

theorem rawRowCheck16987 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form15 = rawRow16987 := by decide +kernel

def row16987 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2079, -3), (key2085, -1), (key2152, -3), (key2166, -1), (key2176, 3), (key2187, 1), (key2246, -1), (key2253, 1), (key2279, 1), (key2287, -1)]

theorem rowCheck16987 : row16987 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16987 := by decide +kernel

theorem rowEval16987 (x : Key → ℝ) : Integer.Sparse.eval row16987 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck16987, Integer.Sparse.eval_collectBalanced, rawRowCheck16987]

def rawRow16988 : Integer.Sparse Key := [(key2240, -1), (key2276, -1), (key2147, -1), (key2279, -1), (key2152, -1), (key2246, -1), (key2276, 2), (key2176, 2), (key2279, 2), (key2240, 1), (key2276, 1), (key2058, 1), (key2287, 1), (key2063, 1), (key2253, 1), (key2276, -2), (key2079, -2), (key2287, -2), (key2058, -1), (key2079, -1), (key2028, -1), (key2085, -1), (key2033, -1), (key2069, -1), (key2147, 1), (key2176, 1), (key2028, 1), (key2187, 1), (key2033, 1), (key2166, 1), (key2063, 2), (key2033, 2), (key2069, 2), (key2152, -2), (key2033, -2), (key2166, -2)]

theorem rawRowCheck16988 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form15 = rawRow16988 := by decide +kernel

def row16988 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2079, -3), (key2085, -1), (key2152, -3), (key2166, -1), (key2176, 3), (key2187, 1), (key2246, -1), (key2253, 1), (key2279, 1), (key2287, -1)]

theorem rowCheck16988 : row16988 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16988 := by decide +kernel

theorem rowEval16988 (x : Key → ℝ) : Integer.Sparse.eval row16988 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form15) x := by
  rw [rowCheck16988, Integer.Sparse.eval_collectBalanced, rawRowCheck16988]

def rawRow16989 : Integer.Sparse Key := [(key2276, -1), (key2240, -1), (key2279, -1), (key2147, -1), (key2246, -1), (key2152, -1), (key2276, 2), (key2279, 2), (key2176, 2), (key2276, 1), (key2240, 1), (key2287, 1), (key2058, 1), (key2253, 1), (key2063, 1), (key2276, -2), (key2287, -2), (key2079, -2), (key2079, -1), (key2058, -1), (key2085, -1), (key2028, -1), (key2069, -1), (key2033, -1), (key2176, 1), (key2147, 1), (key2187, 1), (key2028, 1), (key2166, 1), (key2033, 1), (key2063, 2), (key2069, 2), (key2033, 2), (key2152, -2), (key2166, -2), (key2033, -2)]

theorem rawRowCheck16989 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form15 = rawRow16989 := by decide +kernel

def row16989 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2079, -3), (key2085, -1), (key2152, -3), (key2166, -1), (key2176, 3), (key2187, 1), (key2246, -1), (key2253, 1), (key2279, 1), (key2287, -1)]

theorem rowCheck16989 : row16989 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16989 := by decide +kernel

theorem rowEval16989 (x : Key → ℝ) : Integer.Sparse.eval row16989 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck16989, Integer.Sparse.eval_collectBalanced, rawRowCheck16989]

def rawRow16990 : Integer.Sparse Key := [(key2246, -1), (key2279, -1), (key2152, -1), (key2276, -1), (key2147, -1), (key2240, -1), (key2279, 2), (key2176, 2), (key2276, 2), (key2253, 1), (key2287, 1), (key2063, 1), (key2276, 1), (key2058, 1), (key2240, 1), (key2287, -2), (key2079, -2), (key2276, -2), (key2069, -1), (key2085, -1), (key2033, -1), (key2079, -1), (key2028, -1), (key2058, -1), (key2166, 1), (key2187, 1), (key2033, 1), (key2176, 1), (key2028, 1), (key2147, 1), (key2069, 2), (key2033, 2), (key2063, 2), (key2166, -2), (key2033, -2), (key2152, -2)]

theorem rawRowCheck16990 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form15 = rawRow16990 := by decide +kernel

def row16990 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2079, -3), (key2085, -1), (key2152, -3), (key2166, -1), (key2176, 3), (key2187, 1), (key2246, -1), (key2253, 1), (key2279, 1), (key2287, -1)]

theorem rowCheck16990 : row16990 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16990 := by decide +kernel

theorem rowEval16990 (x : Key → ℝ) : Integer.Sparse.eval row16990 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck16990, Integer.Sparse.eval_collectBalanced, rawRowCheck16990]

def rawRow16991 : Integer.Sparse Key := [(key2279, -1), (key2246, -1), (key2276, -1), (key2152, -1), (key2240, -1), (key2147, -1), (key2279, 2), (key2276, 2), (key2176, 2), (key2287, 1), (key2253, 1), (key2276, 1), (key2063, 1), (key2240, 1), (key2058, 1), (key2287, -2), (key2276, -2), (key2079, -2), (key2085, -1), (key2069, -1), (key2079, -1), (key2033, -1), (key2058, -1), (key2028, -1), (key2187, 1), (key2166, 1), (key2176, 1), (key2033, 1), (key2147, 1), (key2028, 1), (key2069, 2), (key2063, 2), (key2033, 2), (key2166, -2), (key2152, -2), (key2033, -2)]

theorem rawRowCheck16991 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form15 = rawRow16991 := by decide +kernel

def row16991 : Integer.Sparse Key := [(key2063, 3), (key2069, 1), (key2079, -3), (key2085, -1), (key2152, -3), (key2166, -1), (key2176, 3), (key2187, 1), (key2246, -1), (key2253, 1), (key2279, 1), (key2287, -1)]

theorem rowCheck16991 : row16991 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16991 := by decide +kernel

theorem rowEval16991 (x : Key → ℝ) : Integer.Sparse.eval row16991 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck16991, Integer.Sparse.eval_collectBalanced, rawRowCheck16991]

def rawRow16992 : Integer.Sparse Key := [(key2147, -1), (key2176, -1), (key2147, -1), (key2279, -1), (key2176, -1), (key2279, -1), (key2152, 2), (key2152, 2), (key2246, 2), (key2058, 1), (key2079, 1), (key2058, 1), (key2287, 1), (key2079, 1), (key2287, 1), (key2063, -2), (key2063, -2), (key2253, -2), (key2147, -1), (key2176, -1), (key2147, -1), (key2279, -1), (key2176, -1), (key2279, -1), (key2058, 1), (key2079, 1), (key2058, 1), (key2287, 1), (key2079, 1), (key2287, 1), (key2152, 2), (key2152, 2), (key2246, 2), (key2063, -2), (key2063, -2), (key2253, -2)]

theorem rawRowCheck16992 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form15 = rawRow16992 := by decide +kernel

def row16992 : Integer.Sparse Key := [(key2058, 4), (key2063, -8), (key2079, 4), (key2147, -4), (key2152, 8), (key2176, -4), (key2246, 4), (key2253, -4), (key2279, -4), (key2287, 4)]

theorem rowCheck16992 : row16992 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16992 := by decide +kernel

theorem rowEval16992 (x : Key → ℝ) : Integer.Sparse.eval row16992 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form15) x := by
  rw [rowCheck16992, Integer.Sparse.eval_collectBalanced, rawRowCheck16992]

def rawRow16993 : Integer.Sparse Key := [(key2176, -1), (key2147, -1), (key2279, -1), (key2147, -1), (key2279, -1), (key2176, -1), (key2152, 2), (key2246, 2), (key2152, 2), (key2079, 1), (key2058, 1), (key2287, 1), (key2058, 1), (key2287, 1), (key2079, 1), (key2063, -2), (key2253, -2), (key2063, -2), (key2176, -1), (key2147, -1), (key2279, -1), (key2147, -1), (key2279, -1), (key2176, -1), (key2079, 1), (key2058, 1), (key2287, 1), (key2058, 1), (key2287, 1), (key2079, 1), (key2152, 2), (key2246, 2), (key2152, 2), (key2063, -2), (key2253, -2), (key2063, -2)]

theorem rawRowCheck16993 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form15 = rawRow16993 := by decide +kernel

def row16993 : Integer.Sparse Key := [(key2058, 4), (key2063, -8), (key2079, 4), (key2147, -4), (key2152, 8), (key2176, -4), (key2246, 4), (key2253, -4), (key2279, -4), (key2287, 4)]

theorem rowCheck16993 : row16993 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16993 := by decide +kernel

theorem rowEval16993 (x : Key → ℝ) : Integer.Sparse.eval row16993 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck16993, Integer.Sparse.eval_collectBalanced, rawRowCheck16993]

def rawRow16994 : Integer.Sparse Key := [(key2279, -1), (key2279, -1), (key2176, -1), (key2176, -1), (key2147, -1), (key2147, -1), (key2246, 2), (key2152, 2), (key2152, 2), (key2287, 1), (key2287, 1), (key2079, 1), (key2079, 1), (key2058, 1), (key2058, 1), (key2253, -2), (key2063, -2), (key2063, -2), (key2279, -1), (key2279, -1), (key2176, -1), (key2176, -1), (key2147, -1), (key2147, -1), (key2287, 1), (key2287, 1), (key2079, 1), (key2079, 1), (key2058, 1), (key2058, 1), (key2246, 2), (key2152, 2), (key2152, 2), (key2253, -2), (key2063, -2), (key2063, -2)]

theorem rawRowCheck16994 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form15 = rawRow16994 := by decide +kernel

def row16994 : Integer.Sparse Key := [(key2058, 4), (key2063, -8), (key2079, 4), (key2147, -4), (key2152, 8), (key2176, -4), (key2246, 4), (key2253, -4), (key2279, -4), (key2287, 4)]

theorem rowCheck16994 : row16994 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16994 := by decide +kernel

theorem rowEval16994 (x : Key → ℝ) : Integer.Sparse.eval row16994 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck16994, Integer.Sparse.eval_collectBalanced, rawRowCheck16994]

def rawRow16995 : Integer.Sparse Key := [(key2151, 2), (key2151, 2), (key2169, 2), (key2175, -1), (key2179, -1), (key2175, -1), (key2189, -1), (key2179, -1), (key2189, -1), (key2151, 2), (key2151, 2), (key2169, 2), (key2275, -1), (key2281, -1), (key2275, -1), (key2289, -1), (key2281, -1), (key2289, -1), (key2175, -1), (key2179, -1), (key2175, -1), (key2189, -1), (key2179, -1), (key2189, -1), (key2275, -1), (key2281, -1), (key2275, -1), (key2289, -1), (key2281, -1), (key2289, -1), (key2328, 2), (key2330, 2), (key2328, 2), (key2333, 2), (key2330, 2), (key2333, 2)]

theorem rawRowCheck16995 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form16 = rawRow16995 := by decide +kernel

def row16995 : Integer.Sparse Key := [(key2151, 8), (key2169, 4), (key2175, -4), (key2179, -4), (key2189, -4), (key2275, -4), (key2281, -4), (key2289, -4), (key2328, 4), (key2330, 4), (key2333, 4)]

theorem rowCheck16995 : row16995 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16995 := by decide +kernel

theorem rowEval16995 (x : Key → ℝ) : Integer.Sparse.eval row16995 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form16) x := by
  rw [rowCheck16995, Integer.Sparse.eval_collectBalanced, rawRowCheck16995]

def rawRow16996 : Integer.Sparse Key := [(key2151, 2), (key2169, 2), (key2151, 2), (key2179, -1), (key2175, -1), (key2189, -1), (key2175, -1), (key2189, -1), (key2179, -1), (key2151, 2), (key2169, 2), (key2151, 2), (key2281, -1), (key2275, -1), (key2289, -1), (key2275, -1), (key2289, -1), (key2281, -1), (key2179, -1), (key2175, -1), (key2189, -1), (key2175, -1), (key2189, -1), (key2179, -1), (key2281, -1), (key2275, -1), (key2289, -1), (key2275, -1), (key2289, -1), (key2281, -1), (key2330, 2), (key2328, 2), (key2333, 2), (key2328, 2), (key2333, 2), (key2330, 2)]

theorem rawRowCheck16996 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form16 = rawRow16996 := by decide +kernel

def row16996 : Integer.Sparse Key := [(key2151, 8), (key2169, 4), (key2175, -4), (key2179, -4), (key2189, -4), (key2275, -4), (key2281, -4), (key2289, -4), (key2328, 4), (key2330, 4), (key2333, 4)]

theorem rowCheck16996 : row16996 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16996 := by decide +kernel

theorem rowEval16996 (x : Key → ℝ) : Integer.Sparse.eval row16996 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form16) x := by
  rw [rowCheck16996, Integer.Sparse.eval_collectBalanced, rawRowCheck16996]

def rawRow16997 : Integer.Sparse Key := [(key2169, 2), (key2151, 2), (key2151, 2), (key2189, -1), (key2189, -1), (key2179, -1), (key2179, -1), (key2175, -1), (key2175, -1), (key2169, 2), (key2151, 2), (key2151, 2), (key2289, -1), (key2289, -1), (key2281, -1), (key2281, -1), (key2275, -1), (key2275, -1), (key2189, -1), (key2189, -1), (key2179, -1), (key2179, -1), (key2175, -1), (key2175, -1), (key2289, -1), (key2289, -1), (key2281, -1), (key2281, -1), (key2275, -1), (key2275, -1), (key2333, 2), (key2333, 2), (key2330, 2), (key2330, 2), (key2328, 2), (key2328, 2)]

theorem rawRowCheck16997 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form16 = rawRow16997 := by decide +kernel

def row16997 : Integer.Sparse Key := [(key2151, 8), (key2169, 4), (key2175, -4), (key2179, -4), (key2189, -4), (key2275, -4), (key2281, -4), (key2289, -4), (key2328, 4), (key2330, 4), (key2333, 4)]

theorem rowCheck16997 : row16997 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16997 := by decide +kernel

theorem rowEval16997 (x : Key → ℝ) : Integer.Sparse.eval row16997 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form16) x := by
  rw [rowCheck16997, Integer.Sparse.eval_collectBalanced, rawRowCheck16997]

def rawRow16998 : Integer.Sparse Key := [(key2032, 2), (key2175, 2), (key2189, 2), (key2032, -1), (key2037, -1), (key2151, -1), (key2169, -1), (key2179, -1), (key2189, -1), (key2062, 2), (key2275, 2), (key2289, 2), (key2062, -1), (key2072, -1), (key2151, -1), (key2169, -1), (key2281, -1), (key2289, -1), (key2078, -1), (key2082, -1), (key2275, -1), (key2289, -1), (key2328, -1), (key2333, -1), (key2078, -1), (key2087, -1), (key2175, -1), (key2189, -1), (key2330, -1), (key2333, -1), (key2082, 2), (key2087, 2), (key2179, 2), (key2189, 2), (key2281, 2), (key2289, 2)]

theorem rawRowCheck16998 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form16 = rawRow16998 := by decide +kernel

def row16998 : Integer.Sparse Key := [(key2032, 1), (key2037, -1), (key2062, 1), (key2072, -1), (key2078, -2), (key2082, 1), (key2087, 1), (key2151, -2), (key2169, -2), (key2175, 1), (key2179, 1), (key2189, 2), (key2275, 1), (key2281, 1), (key2289, 2), (key2328, -1), (key2330, -1), (key2333, -2)]

theorem rowCheck16998 : row16998 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16998 := by decide +kernel

theorem rowEval16998 (x : Key → ℝ) : Integer.Sparse.eval row16998 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form16) x := by
  rw [rowCheck16998, Integer.Sparse.eval_collectBalanced, rawRowCheck16998]

def rawRow16999 : Integer.Sparse Key := [(key2032, 2), (key2189, 2), (key2175, 2), (key2037, -1), (key2032, -1), (key2169, -1), (key2151, -1), (key2189, -1), (key2179, -1), (key2062, 2), (key2289, 2), (key2275, 2), (key2072, -1), (key2062, -1), (key2169, -1), (key2151, -1), (key2289, -1), (key2281, -1), (key2082, -1), (key2078, -1), (key2289, -1), (key2275, -1), (key2333, -1), (key2328, -1), (key2087, -1), (key2078, -1), (key2189, -1), (key2175, -1), (key2333, -1), (key2330, -1), (key2087, 2), (key2082, 2), (key2189, 2), (key2179, 2), (key2289, 2), (key2281, 2)]

theorem rawRowCheck16999 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form16 = rawRow16999 := by decide +kernel

def row16999 : Integer.Sparse Key := [(key2032, 1), (key2037, -1), (key2062, 1), (key2072, -1), (key2078, -2), (key2082, 1), (key2087, 1), (key2151, -2), (key2169, -2), (key2175, 1), (key2179, 1), (key2189, 2), (key2275, 1), (key2281, 1), (key2289, 2), (key2328, -1), (key2330, -1), (key2333, -2)]

theorem rowCheck16999 : row16999 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16999 := by decide +kernel

theorem rowEval16999 (x : Key → ℝ) : Integer.Sparse.eval row16999 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form16) x := by
  rw [rowCheck16999, Integer.Sparse.eval_collectBalanced, rawRowCheck16999]

def rawRow17000 : Integer.Sparse Key := [(key2175, 2), (key2032, 2), (key2189, 2), (key2151, -1), (key2179, -1), (key2032, -1), (key2189, -1), (key2037, -1), (key2169, -1), (key2275, 2), (key2062, 2), (key2289, 2), (key2151, -1), (key2281, -1), (key2062, -1), (key2289, -1), (key2072, -1), (key2169, -1), (key2275, -1), (key2328, -1), (key2078, -1), (key2333, -1), (key2082, -1), (key2289, -1), (key2175, -1), (key2330, -1), (key2078, -1), (key2333, -1), (key2087, -1), (key2189, -1), (key2179, 2), (key2281, 2), (key2082, 2), (key2289, 2), (key2087, 2), (key2189, 2)]

theorem rawRowCheck17000 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form16 = rawRow17000 := by decide +kernel

def row17000 : Integer.Sparse Key := [(key2032, 1), (key2037, -1), (key2062, 1), (key2072, -1), (key2078, -2), (key2082, 1), (key2087, 1), (key2151, -2), (key2169, -2), (key2175, 1), (key2179, 1), (key2189, 2), (key2275, 1), (key2281, 1), (key2289, 2), (key2328, -1), (key2330, -1), (key2333, -2)]

theorem rowCheck17000 : row17000 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17000 := by decide +kernel

theorem rowEval17000 (x : Key → ℝ) : Integer.Sparse.eval row17000 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form16) x := by
  rw [rowCheck17000, Integer.Sparse.eval_collectBalanced, rawRowCheck17000]

def rawRow17001 : Integer.Sparse Key := [(key2175, 2), (key2189, 2), (key2032, 2), (key2179, -1), (key2151, -1), (key2189, -1), (key2032, -1), (key2169, -1), (key2037, -1), (key2275, 2), (key2289, 2), (key2062, 2), (key2281, -1), (key2151, -1), (key2289, -1), (key2062, -1), (key2169, -1), (key2072, -1), (key2328, -1), (key2275, -1), (key2333, -1), (key2078, -1), (key2289, -1), (key2082, -1), (key2330, -1), (key2175, -1), (key2333, -1), (key2078, -1), (key2189, -1), (key2087, -1), (key2281, 2), (key2179, 2), (key2289, 2), (key2082, 2), (key2189, 2), (key2087, 2)]

theorem rawRowCheck17001 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form16 = rawRow17001 := by decide +kernel

def row17001 : Integer.Sparse Key := [(key2032, 1), (key2037, -1), (key2062, 1), (key2072, -1), (key2078, -2), (key2082, 1), (key2087, 1), (key2151, -2), (key2169, -2), (key2175, 1), (key2179, 1), (key2189, 2), (key2275, 1), (key2281, 1), (key2289, 2), (key2328, -1), (key2330, -1), (key2333, -2)]

theorem rowCheck17001 : row17001 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17001 := by decide +kernel

theorem rowEval17001 (x : Key → ℝ) : Integer.Sparse.eval row17001 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck17001, Integer.Sparse.eval_collectBalanced, rawRowCheck17001]

def rawRow17002 : Integer.Sparse Key := [(key2189, 2), (key2032, 2), (key2175, 2), (key2169, -1), (key2189, -1), (key2037, -1), (key2179, -1), (key2032, -1), (key2151, -1), (key2289, 2), (key2062, 2), (key2275, 2), (key2169, -1), (key2289, -1), (key2072, -1), (key2281, -1), (key2062, -1), (key2151, -1), (key2289, -1), (key2333, -1), (key2082, -1), (key2328, -1), (key2078, -1), (key2275, -1), (key2189, -1), (key2333, -1), (key2087, -1), (key2330, -1), (key2078, -1), (key2175, -1), (key2189, 2), (key2289, 2), (key2087, 2), (key2281, 2), (key2082, 2), (key2179, 2)]

theorem rawRowCheck17002 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form16 = rawRow17002 := by decide +kernel

def row17002 : Integer.Sparse Key := [(key2032, 1), (key2037, -1), (key2062, 1), (key2072, -1), (key2078, -2), (key2082, 1), (key2087, 1), (key2151, -2), (key2169, -2), (key2175, 1), (key2179, 1), (key2189, 2), (key2275, 1), (key2281, 1), (key2289, 2), (key2328, -1), (key2330, -1), (key2333, -2)]

theorem rowCheck17002 : row17002 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17002 := by decide +kernel

theorem rowEval17002 (x : Key → ℝ) : Integer.Sparse.eval row17002 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form16) x := by
  rw [rowCheck17002, Integer.Sparse.eval_collectBalanced, rawRowCheck17002]

def rawRow17003 : Integer.Sparse Key := [(key2189, 2), (key2175, 2), (key2032, 2), (key2189, -1), (key2169, -1), (key2179, -1), (key2037, -1), (key2151, -1), (key2032, -1), (key2289, 2), (key2275, 2), (key2062, 2), (key2289, -1), (key2169, -1), (key2281, -1), (key2072, -1), (key2151, -1), (key2062, -1), (key2333, -1), (key2289, -1), (key2328, -1), (key2082, -1), (key2275, -1), (key2078, -1), (key2333, -1), (key2189, -1), (key2330, -1), (key2087, -1), (key2175, -1), (key2078, -1), (key2289, 2), (key2189, 2), (key2281, 2), (key2087, 2), (key2179, 2), (key2082, 2)]

theorem rawRowCheck17003 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form16 = rawRow17003 := by decide +kernel

def row17003 : Integer.Sparse Key := [(key2032, 1), (key2037, -1), (key2062, 1), (key2072, -1), (key2078, -2), (key2082, 1), (key2087, 1), (key2151, -2), (key2169, -2), (key2175, 1), (key2179, 1), (key2189, 2), (key2275, 1), (key2281, 1), (key2289, 2), (key2328, -1), (key2330, -1), (key2333, -2)]

theorem rowCheck17003 : row17003 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17003 := by decide +kernel

theorem rowEval17003 (x : Key → ℝ) : Integer.Sparse.eval row17003 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck17003, Integer.Sparse.eval_collectBalanced, rawRowCheck17003]

def rawRow17004 : Integer.Sparse Key := [(key2062, 2), (key2275, 2), (key2289, 2), (key2078, -1), (key2082, -1), (key2275, -1), (key2289, -1), (key2328, -1), (key2333, -1), (key2032, 2), (key2175, 2), (key2189, 2), (key2078, -1), (key2087, -1), (key2175, -1), (key2189, -1), (key2330, -1), (key2333, -1), (key2032, -1), (key2037, -1), (key2151, -1), (key2169, -1), (key2179, -1), (key2189, -1), (key2062, -1), (key2072, -1), (key2151, -1), (key2169, -1), (key2281, -1), (key2289, -1), (key2082, 2), (key2087, 2), (key2179, 2), (key2189, 2), (key2281, 2), (key2289, 2)]

theorem rawRowCheck17004 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form16 = rawRow17004 := by decide +kernel

def row17004 : Integer.Sparse Key := [(key2032, 1), (key2037, -1), (key2062, 1), (key2072, -1), (key2078, -2), (key2082, 1), (key2087, 1), (key2151, -2), (key2169, -2), (key2175, 1), (key2179, 1), (key2189, 2), (key2275, 1), (key2281, 1), (key2289, 2), (key2328, -1), (key2330, -1), (key2333, -2)]

theorem rowCheck17004 : row17004 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17004 := by decide +kernel

theorem rowEval17004 (x : Key → ℝ) : Integer.Sparse.eval row17004 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form16) x := by
  rw [rowCheck17004, Integer.Sparse.eval_collectBalanced, rawRowCheck17004]

def rawRow17005 : Integer.Sparse Key := [(key2062, 2), (key2289, 2), (key2275, 2), (key2082, -1), (key2078, -1), (key2289, -1), (key2275, -1), (key2333, -1), (key2328, -1), (key2032, 2), (key2189, 2), (key2175, 2), (key2087, -1), (key2078, -1), (key2189, -1), (key2175, -1), (key2333, -1), (key2330, -1), (key2037, -1), (key2032, -1), (key2169, -1), (key2151, -1), (key2189, -1), (key2179, -1), (key2072, -1), (key2062, -1), (key2169, -1), (key2151, -1), (key2289, -1), (key2281, -1), (key2087, 2), (key2082, 2), (key2189, 2), (key2179, 2), (key2289, 2), (key2281, 2)]

theorem rawRowCheck17005 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form16 = rawRow17005 := by decide +kernel

def row17005 : Integer.Sparse Key := [(key2032, 1), (key2037, -1), (key2062, 1), (key2072, -1), (key2078, -2), (key2082, 1), (key2087, 1), (key2151, -2), (key2169, -2), (key2175, 1), (key2179, 1), (key2189, 2), (key2275, 1), (key2281, 1), (key2289, 2), (key2328, -1), (key2330, -1), (key2333, -2)]

theorem rowCheck17005 : row17005 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17005 := by decide +kernel

theorem rowEval17005 (x : Key → ℝ) : Integer.Sparse.eval row17005 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form16) x := by
  rw [rowCheck17005, Integer.Sparse.eval_collectBalanced, rawRowCheck17005]

def rawRow17006 : Integer.Sparse Key := [(key2275, 2), (key2062, 2), (key2289, 2), (key2275, -1), (key2328, -1), (key2078, -1), (key2333, -1), (key2082, -1), (key2289, -1), (key2175, 2), (key2032, 2), (key2189, 2), (key2175, -1), (key2330, -1), (key2078, -1), (key2333, -1), (key2087, -1), (key2189, -1), (key2151, -1), (key2179, -1), (key2032, -1), (key2189, -1), (key2037, -1), (key2169, -1), (key2151, -1), (key2281, -1), (key2062, -1), (key2289, -1), (key2072, -1), (key2169, -1), (key2179, 2), (key2281, 2), (key2082, 2), (key2289, 2), (key2087, 2), (key2189, 2)]

theorem rawRowCheck17006 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form16 = rawRow17006 := by decide +kernel

def row17006 : Integer.Sparse Key := [(key2032, 1), (key2037, -1), (key2062, 1), (key2072, -1), (key2078, -2), (key2082, 1), (key2087, 1), (key2151, -2), (key2169, -2), (key2175, 1), (key2179, 1), (key2189, 2), (key2275, 1), (key2281, 1), (key2289, 2), (key2328, -1), (key2330, -1), (key2333, -2)]

theorem rowCheck17006 : row17006 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17006 := by decide +kernel

theorem rowEval17006 (x : Key → ℝ) : Integer.Sparse.eval row17006 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form16) x := by
  rw [rowCheck17006, Integer.Sparse.eval_collectBalanced, rawRowCheck17006]

def rawRow17007 : Integer.Sparse Key := [(key2275, 2), (key2289, 2), (key2062, 2), (key2328, -1), (key2275, -1), (key2333, -1), (key2078, -1), (key2289, -1), (key2082, -1), (key2175, 2), (key2189, 2), (key2032, 2), (key2330, -1), (key2175, -1), (key2333, -1), (key2078, -1), (key2189, -1), (key2087, -1), (key2179, -1), (key2151, -1), (key2189, -1), (key2032, -1), (key2169, -1), (key2037, -1), (key2281, -1), (key2151, -1), (key2289, -1), (key2062, -1), (key2169, -1), (key2072, -1), (key2281, 2), (key2179, 2), (key2289, 2), (key2082, 2), (key2189, 2), (key2087, 2)]

theorem rawRowCheck17007 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form16 = rawRow17007 := by decide +kernel

def row17007 : Integer.Sparse Key := [(key2032, 1), (key2037, -1), (key2062, 1), (key2072, -1), (key2078, -2), (key2082, 1), (key2087, 1), (key2151, -2), (key2169, -2), (key2175, 1), (key2179, 1), (key2189, 2), (key2275, 1), (key2281, 1), (key2289, 2), (key2328, -1), (key2330, -1), (key2333, -2)]

theorem rowCheck17007 : row17007 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17007 := by decide +kernel

theorem rowEval17007 (x : Key → ℝ) : Integer.Sparse.eval row17007 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck17007, Integer.Sparse.eval_collectBalanced, rawRowCheck17007]

def rawRow17008 : Integer.Sparse Key := [(key2289, 2), (key2062, 2), (key2275, 2), (key2289, -1), (key2333, -1), (key2082, -1), (key2328, -1), (key2078, -1), (key2275, -1), (key2189, 2), (key2032, 2), (key2175, 2), (key2189, -1), (key2333, -1), (key2087, -1), (key2330, -1), (key2078, -1), (key2175, -1), (key2169, -1), (key2189, -1), (key2037, -1), (key2179, -1), (key2032, -1), (key2151, -1), (key2169, -1), (key2289, -1), (key2072, -1), (key2281, -1), (key2062, -1), (key2151, -1), (key2189, 2), (key2289, 2), (key2087, 2), (key2281, 2), (key2082, 2), (key2179, 2)]

theorem rawRowCheck17008 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form16 = rawRow17008 := by decide +kernel

def row17008 : Integer.Sparse Key := [(key2032, 1), (key2037, -1), (key2062, 1), (key2072, -1), (key2078, -2), (key2082, 1), (key2087, 1), (key2151, -2), (key2169, -2), (key2175, 1), (key2179, 1), (key2189, 2), (key2275, 1), (key2281, 1), (key2289, 2), (key2328, -1), (key2330, -1), (key2333, -2)]

theorem rowCheck17008 : row17008 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17008 := by decide +kernel

theorem rowEval17008 (x : Key → ℝ) : Integer.Sparse.eval row17008 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form16) x := by
  rw [rowCheck17008, Integer.Sparse.eval_collectBalanced, rawRowCheck17008]

def rawRow17009 : Integer.Sparse Key := [(key2289, 2), (key2275, 2), (key2062, 2), (key2333, -1), (key2289, -1), (key2328, -1), (key2082, -1), (key2275, -1), (key2078, -1), (key2189, 2), (key2175, 2), (key2032, 2), (key2333, -1), (key2189, -1), (key2330, -1), (key2087, -1), (key2175, -1), (key2078, -1), (key2189, -1), (key2169, -1), (key2179, -1), (key2037, -1), (key2151, -1), (key2032, -1), (key2289, -1), (key2169, -1), (key2281, -1), (key2072, -1), (key2151, -1), (key2062, -1), (key2289, 2), (key2189, 2), (key2281, 2), (key2087, 2), (key2179, 2), (key2082, 2)]

theorem rawRowCheck17009 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form16 = rawRow17009 := by decide +kernel

def row17009 : Integer.Sparse Key := [(key2032, 1), (key2037, -1), (key2062, 1), (key2072, -1), (key2078, -2), (key2082, 1), (key2087, 1), (key2151, -2), (key2169, -2), (key2175, 1), (key2179, 1), (key2189, 2), (key2275, 1), (key2281, 1), (key2289, 2), (key2328, -1), (key2330, -1), (key2333, -2)]

theorem rowCheck17009 : row17009 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17009 := by decide +kernel

theorem rowEval17009 (x : Key → ℝ) : Integer.Sparse.eval row17009 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck17009, Integer.Sparse.eval_collectBalanced, rawRowCheck17009]

def rawRow17010 : Integer.Sparse Key := [(key2078, 2), (key2078, 2), (key2333, 2), (key2062, -1), (key2082, -1), (key2062, -1), (key2289, -1), (key2082, -1), (key2289, -1), (key2078, 2), (key2078, 2), (key2333, 2), (key2032, -1), (key2087, -1), (key2032, -1), (key2189, -1), (key2087, -1), (key2189, -1), (key2062, -1), (key2082, -1), (key2062, -1), (key2289, -1), (key2082, -1), (key2289, -1), (key2032, -1), (key2087, -1), (key2032, -1), (key2189, -1), (key2087, -1), (key2189, -1), (key2037, 2), (key2072, 2), (key2037, 2), (key2169, 2), (key2072, 2), (key2169, 2)]

theorem rawRowCheck17010 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form16 = rawRow17010 := by decide +kernel

def row17010 : Integer.Sparse Key := [(key2032, -4), (key2037, 4), (key2062, -4), (key2072, 4), (key2078, 8), (key2082, -4), (key2087, -4), (key2169, 4), (key2189, -4), (key2289, -4), (key2333, 4)]

theorem rowCheck17010 : row17010 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17010 := by decide +kernel

theorem rowEval17010 (x : Key → ℝ) : Integer.Sparse.eval row17010 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form16) x := by
  rw [rowCheck17010, Integer.Sparse.eval_collectBalanced, rawRowCheck17010]

def rawRow17011 : Integer.Sparse Key := [(key2078, 2), (key2333, 2), (key2078, 2), (key2082, -1), (key2062, -1), (key2289, -1), (key2062, -1), (key2289, -1), (key2082, -1), (key2078, 2), (key2333, 2), (key2078, 2), (key2087, -1), (key2032, -1), (key2189, -1), (key2032, -1), (key2189, -1), (key2087, -1), (key2082, -1), (key2062, -1), (key2289, -1), (key2062, -1), (key2289, -1), (key2082, -1), (key2087, -1), (key2032, -1), (key2189, -1), (key2032, -1), (key2189, -1), (key2087, -1), (key2072, 2), (key2037, 2), (key2169, 2), (key2037, 2), (key2169, 2), (key2072, 2)]

theorem rawRowCheck17011 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form16 = rawRow17011 := by decide +kernel

def row17011 : Integer.Sparse Key := [(key2032, -4), (key2037, 4), (key2062, -4), (key2072, 4), (key2078, 8), (key2082, -4), (key2087, -4), (key2169, 4), (key2189, -4), (key2289, -4), (key2333, 4)]

theorem rowCheck17011 : row17011 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17011 := by decide +kernel

theorem rowEval17011 (x : Key → ℝ) : Integer.Sparse.eval row17011 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck17011, Integer.Sparse.eval_collectBalanced, rawRowCheck17011]

def rawRow17012 : Integer.Sparse Key := [(key2333, 2), (key2078, 2), (key2078, 2), (key2289, -1), (key2289, -1), (key2082, -1), (key2082, -1), (key2062, -1), (key2062, -1), (key2333, 2), (key2078, 2), (key2078, 2), (key2189, -1), (key2189, -1), (key2087, -1), (key2087, -1), (key2032, -1), (key2032, -1), (key2289, -1), (key2289, -1), (key2082, -1), (key2082, -1), (key2062, -1), (key2062, -1), (key2189, -1), (key2189, -1), (key2087, -1), (key2087, -1), (key2032, -1), (key2032, -1), (key2169, 2), (key2169, 2), (key2072, 2), (key2072, 2), (key2037, 2), (key2037, 2)]

theorem rawRowCheck17012 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form16 = rawRow17012 := by decide +kernel

def row17012 : Integer.Sparse Key := [(key2032, -4), (key2037, 4), (key2062, -4), (key2072, 4), (key2078, 8), (key2082, -4), (key2087, -4), (key2169, 4), (key2189, -4), (key2289, -4), (key2333, 4)]

theorem rowCheck17012 : row17012 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17012 := by decide +kernel

theorem rowEval17012 (x : Key → ℝ) : Integer.Sparse.eval row17012 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck17012, Integer.Sparse.eval_collectBalanced, rawRowCheck17012]

def rawRow17013 : Integer.Sparse Key := [(key776, 4), (key778, 4), (key778, 4), (key801, -2), (key803, -2), (key801, -2), (key811, -2), (key803, -2), (key811, -2), (key801, -2), (key803, -2), (key801, -2), (key811, -2), (key803, -2), (key811, -2), (key871, 4), (key876, 4), (key876, 4)]

theorem rawRowCheck17013 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form17 = rawRow17013 := by decide +kernel

def row17013 : Integer.Sparse Key := [(key776, 4), (key778, 8), (key801, -8), (key803, -8), (key811, -8), (key871, 4), (key876, 8)]

theorem rowCheck17013 : row17013 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17013 := by decide +kernel

theorem rowEval17013 (x : Key → ℝ) : Integer.Sparse.eval row17013 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form17) x := by
  rw [rowCheck17013, Integer.Sparse.eval_collectBalanced, rawRowCheck17013]

def rawRow17014 : Integer.Sparse Key := [(key778, 4), (key776, 4), (key778, 4), (key803, -2), (key801, -2), (key811, -2), (key801, -2), (key811, -2), (key803, -2), (key803, -2), (key801, -2), (key811, -2), (key801, -2), (key811, -2), (key803, -2), (key876, 4), (key871, 4), (key876, 4)]

theorem rawRowCheck17014 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form17 = rawRow17014 := by decide +kernel

def row17014 : Integer.Sparse Key := [(key776, 4), (key778, 8), (key801, -8), (key803, -8), (key811, -8), (key871, 4), (key876, 8)]

theorem rowCheck17014 : row17014 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17014 := by decide +kernel

theorem rowEval17014 (x : Key → ℝ) : Integer.Sparse.eval row17014 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17014, Integer.Sparse.eval_collectBalanced, rawRowCheck17014]

def rawRow17015 : Integer.Sparse Key := [(key778, 4), (key778, 4), (key776, 4), (key811, -2), (key811, -2), (key803, -2), (key803, -2), (key801, -2), (key801, -2), (key811, -2), (key811, -2), (key803, -2), (key803, -2), (key801, -2), (key801, -2), (key876, 4), (key876, 4), (key871, 4)]

theorem rawRowCheck17015 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form17 = rawRow17015 := by decide +kernel

def row17015 : Integer.Sparse Key := [(key776, 4), (key778, 8), (key801, -8), (key803, -8), (key811, -8), (key871, 4), (key876, 8)]

theorem rowCheck17015 : row17015 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17015 := by decide +kernel

theorem rowEval17015 (x : Key → ℝ) : Integer.Sparse.eval row17015 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17015, Integer.Sparse.eval_collectBalanced, rawRowCheck17015]

def rawRow17016 : Integer.Sparse Key := [(key801, 4), (key803, 4), (key811, 4), (key776, -2), (key778, -2), (key801, -2), (key811, -2), (key836, -2), (key839, -2), (key801, -2), (key803, -2), (key871, -2), (key876, -2), (key931, -2), (key934, -2), (key801, 4), (key811, 4), (key934, 4)]

theorem rawRowCheck17016 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form17 = rawRow17016 := by decide +kernel

def row17016 : Integer.Sparse Key := [(key776, -2), (key778, -2), (key801, 4), (key803, 2), (key811, 6), (key836, -2), (key839, -2), (key871, -2), (key876, -2), (key931, -2), (key934, 2)]

theorem rowCheck17016 : row17016 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17016 := by decide +kernel

theorem rowEval17016 (x : Key → ℝ) : Integer.Sparse.eval row17016 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form17) x := by
  rw [rowCheck17016, Integer.Sparse.eval_collectBalanced, rawRowCheck17016]

def rawRow17017 : Integer.Sparse Key := [(key803, 4), (key801, 4), (key811, 4), (key778, -2), (key776, -2), (key811, -2), (key801, -2), (key839, -2), (key836, -2), (key803, -2), (key801, -2), (key876, -2), (key871, -2), (key934, -2), (key931, -2), (key811, 4), (key801, 4), (key934, 4)]

theorem rawRowCheck17017 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form17 = rawRow17017 := by decide +kernel

def row17017 : Integer.Sparse Key := [(key776, -2), (key778, -2), (key801, 4), (key803, 2), (key811, 6), (key836, -2), (key839, -2), (key871, -2), (key876, -2), (key931, -2), (key934, 2)]

theorem rowCheck17017 : row17017 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17017 := by decide +kernel

theorem rowEval17017 (x : Key → ℝ) : Integer.Sparse.eval row17017 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17017, Integer.Sparse.eval_collectBalanced, rawRowCheck17017]

def rawRow17018 : Integer.Sparse Key := [(key801, 4), (key811, 4), (key803, 4), (key801, -2), (key811, -2), (key776, -2), (key839, -2), (key778, -2), (key811, -2), (key871, -2), (key931, -2), (key801, -2), (key934, -2), (key803, -2), (key876, -2), (key801, 4), (key934, 4), (key811, 4)]

theorem rawRowCheck17018 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form17 = rawRow17018 := by decide +kernel

def row17018 : Integer.Sparse Key := [(key776, -2), (key778, -2), (key801, 4), (key803, 2), (key811, 4), (key839, -2), (key871, -2), (key876, -2), (key931, -2), (key934, 2)]

theorem rowCheck17018 : row17018 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17018 := by decide +kernel

theorem rowEval17018 (x : Key → ℝ) : Integer.Sparse.eval row17018 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form17) x := by
  rw [rowCheck17018, Integer.Sparse.eval_collectBalanced, rawRowCheck17018]

def rawRow17019 : Integer.Sparse Key := [(key811, 4), (key801, 4), (key803, 4), (key811, -2), (key801, -2), (key839, -2), (key776, -2), (key811, -2), (key778, -2), (key931, -2), (key871, -2), (key934, -2), (key801, -2), (key876, -2), (key803, -2), (key934, 4), (key801, 4), (key811, 4)]

theorem rawRowCheck17019 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form17 = rawRow17019 := by decide +kernel

def row17019 : Integer.Sparse Key := [(key776, -2), (key778, -2), (key801, 4), (key803, 2), (key811, 4), (key839, -2), (key871, -2), (key876, -2), (key931, -2), (key934, 2)]

theorem rowCheck17019 : row17019 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17019 := by decide +kernel

theorem rowEval17019 (x : Key → ℝ) : Integer.Sparse.eval row17019 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17019, Integer.Sparse.eval_collectBalanced, rawRowCheck17019]

def rawRow17020 : Integer.Sparse Key := [(key803, 4), (key811, 4), (key801, 4), (key836, -2), (key839, -2), (key778, -2), (key811, -2), (key776, -2), (key801, -2), (key876, -2), (key934, -2), (key803, -2), (key931, -2), (key801, -2), (key871, -2), (key811, 4), (key934, 4), (key801, 4)]

theorem rawRowCheck17020 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form17 = rawRow17020 := by decide +kernel

def row17020 : Integer.Sparse Key := [(key776, -2), (key778, -2), (key801, 4), (key803, 2), (key811, 6), (key836, -2), (key839, -2), (key871, -2), (key876, -2), (key931, -2), (key934, 2)]

theorem rowCheck17020 : row17020 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17020 := by decide +kernel

theorem rowEval17020 (x : Key → ℝ) : Integer.Sparse.eval row17020 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17020, Integer.Sparse.eval_collectBalanced, rawRowCheck17020]

def rawRow17021 : Integer.Sparse Key := [(key811, 4), (key803, 4), (key801, 4), (key839, -2), (key836, -2), (key811, -2), (key778, -2), (key801, -2), (key776, -2), (key934, -2), (key876, -2), (key931, -2), (key803, -2), (key871, -2), (key801, -2), (key934, 4), (key811, 4), (key801, 4)]

theorem rawRowCheck17021 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form17 = rawRow17021 := by decide +kernel

def row17021 : Integer.Sparse Key := [(key776, -2), (key778, -2), (key801, 4), (key803, 2), (key811, 6), (key836, -2), (key839, -2), (key871, -2), (key876, -2), (key931, -2), (key934, 2)]

theorem rowCheck17021 : row17021 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17021 := by decide +kernel

theorem rowEval17021 (x : Key → ℝ) : Integer.Sparse.eval row17021 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17021, Integer.Sparse.eval_collectBalanced, rawRowCheck17021]

def rawRow17022 : Integer.Sparse Key := [(key801, 4), (key803, 4), (key811, 4), (key801, -2), (key803, -2), (key871, -2), (key931, -2), (key876, -2), (key934, -2), (key776, -2), (key778, -2), (key801, -2), (key811, -2), (key836, -2), (key839, -2), (key801, 4), (key811, 4), (key934, 4)]

theorem rawRowCheck17022 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form17 = rawRow17022 := by decide +kernel

def row17022 : Integer.Sparse Key := [(key776, -2), (key778, -2), (key801, 4), (key803, 2), (key811, 6), (key836, -2), (key839, -2), (key871, -2), (key876, -2), (key931, -2), (key934, 2)]

theorem rowCheck17022 : row17022 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17022 := by decide +kernel

theorem rowEval17022 (x : Key → ℝ) : Integer.Sparse.eval row17022 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form17) x := by
  rw [rowCheck17022, Integer.Sparse.eval_collectBalanced, rawRowCheck17022]

def rawRow17023 : Integer.Sparse Key := [(key803, 4), (key801, 4), (key811, 4), (key803, -2), (key801, -2), (key931, -2), (key871, -2), (key934, -2), (key876, -2), (key778, -2), (key776, -2), (key811, -2), (key801, -2), (key839, -2), (key836, -2), (key811, 4), (key801, 4), (key934, 4)]

theorem rawRowCheck17023 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form17 = rawRow17023 := by decide +kernel

def row17023 : Integer.Sparse Key := [(key776, -2), (key778, -2), (key801, 4), (key803, 2), (key811, 6), (key836, -2), (key839, -2), (key871, -2), (key876, -2), (key931, -2), (key934, 2)]

theorem rowCheck17023 : row17023 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17023 := by decide +kernel

theorem rowEval17023 (x : Key → ℝ) : Integer.Sparse.eval row17023 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17023, Integer.Sparse.eval_collectBalanced, rawRowCheck17023]

end MUB6.Certificate.GramRows

end OAI
