import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
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

def rawRow1920 : Integer.Sparse Key := [(key2932, -2), (key2770, -2), (key2770, -2), (key2932, 1), (key2932, 1), (key2773, 1), (key2773, 1), (key2770, 1), (key2770, 1), (key2969, 2), (key2847, 2), (key2847, 2), (key2969, -1), (key2969, -1), (key2890, -1), (key2890, -1), (key2847, -1), (key2847, -1), (key2990, -1), (key2990, -1), (key2881, -1), (key2881, -1), (key2878, -1), (key2878, -1), (key2990, 1), (key2990, 1), (key2911, 1), (key2911, 1), (key2878, 1), (key2878, 1)]

theorem rawRowCheck1920 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form0 = rawRow1920 := by decide +kernel

def row1920 : Integer.Sparse Key := [(key2770, -2), (key2773, 2), (key2847, 2), (key2881, -2), (key2890, -2), (key2911, 2)]

theorem rowCheck1920 : row1920 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1920 := by decide +kernel

theorem rowEval1920 (x : Key → ℝ) : Integer.Sparse.eval row1920 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1920, Integer.Sparse.eval_collectBalanced, rawRowCheck1920]

def rawRow1921 : Integer.Sparse Key := [(key2773, -2), (key2773, -2), (key2773, -2), (key2770, 1), (key2770, 1), (key2770, 1), (key2770, 1), (key2770, 1), (key2770, 1), (key2890, 2), (key2890, 2), (key2890, 2), (key2847, -1), (key2847, -1), (key2847, -1), (key2847, -1), (key2847, -1), (key2847, -1), (key2911, -1), (key2911, -1), (key2911, -1), (key2911, -1), (key2911, -1), (key2911, -1), (key2881, 1), (key2881, 1), (key2881, 1), (key2881, 1), (key2881, 1), (key2881, 1)]

theorem rawRowCheck1921 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form0 = rawRow1921 := by decide +kernel

def row1921 : Integer.Sparse Key := [(key2770, 6), (key2773, -6), (key2847, -6), (key2881, 6), (key2890, 6), (key2911, -6)]

theorem rowCheck1921 : row1921 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1921 := by decide +kernel

theorem rowEval1921 (x : Key → ℝ) : Integer.Sparse.eval row1921 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1921, Integer.Sparse.eval_collectBalanced, rawRowCheck1921]

def rawRow1922 : Integer.Sparse Key := [(key2847, -2), (key2847, -2), (key2969, -2), (key2878, 1), (key2881, 1), (key2878, 1), (key2990, 1), (key2881, 1), (key2990, 1), (key2770, 2), (key2770, 2), (key2932, 2), (key2878, -1), (key2911, -1), (key2878, -1), (key2990, -1), (key2911, -1), (key2990, -1), (key2770, -1), (key2773, -1), (key2770, -1), (key2932, -1), (key2773, -1), (key2932, -1), (key2847, 1), (key2890, 1), (key2847, 1), (key2969, 1), (key2890, 1), (key2969, 1)]

theorem rawRowCheck1922 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form0 = rawRow1922 := by decide +kernel

def row1922 : Integer.Sparse Key := [(key2770, 2), (key2773, -2), (key2847, -2), (key2881, 2), (key2890, 2), (key2911, -2)]

theorem rowCheck1922 : row1922 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1922 := by decide +kernel

theorem rowEval1922 (x : Key → ℝ) : Integer.Sparse.eval row1922 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1922, Integer.Sparse.eval_collectBalanced, rawRowCheck1922]

def rawRow1923 : Integer.Sparse Key := [(key2847, -2), (key2969, -2), (key2847, -2), (key2881, 1), (key2878, 1), (key2990, 1), (key2878, 1), (key2990, 1), (key2881, 1), (key2770, 2), (key2932, 2), (key2770, 2), (key2911, -1), (key2878, -1), (key2990, -1), (key2878, -1), (key2990, -1), (key2911, -1), (key2773, -1), (key2770, -1), (key2932, -1), (key2770, -1), (key2932, -1), (key2773, -1), (key2890, 1), (key2847, 1), (key2969, 1), (key2847, 1), (key2969, 1), (key2890, 1)]

theorem rawRowCheck1923 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form0 = rawRow1923 := by decide +kernel

def row1923 : Integer.Sparse Key := [(key2770, 2), (key2773, -2), (key2847, -2), (key2881, 2), (key2890, 2), (key2911, -2)]

theorem rowCheck1923 : row1923 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1923 := by decide +kernel

theorem rowEval1923 (x : Key → ℝ) : Integer.Sparse.eval row1923 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1923, Integer.Sparse.eval_collectBalanced, rawRowCheck1923]

def rawRow1924 : Integer.Sparse Key := [(key2969, -2), (key2847, -2), (key2847, -2), (key2990, 1), (key2990, 1), (key2881, 1), (key2881, 1), (key2878, 1), (key2878, 1), (key2932, 2), (key2770, 2), (key2770, 2), (key2990, -1), (key2990, -1), (key2911, -1), (key2911, -1), (key2878, -1), (key2878, -1), (key2932, -1), (key2932, -1), (key2773, -1), (key2773, -1), (key2770, -1), (key2770, -1), (key2969, 1), (key2969, 1), (key2890, 1), (key2890, 1), (key2847, 1), (key2847, 1)]

theorem rawRowCheck1924 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form0 = rawRow1924 := by decide +kernel

def row1924 : Integer.Sparse Key := [(key2770, 2), (key2773, -2), (key2847, -2), (key2881, 2), (key2890, 2), (key2911, -2)]

theorem rowCheck1924 : row1924 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1924 := by decide +kernel

theorem rowEval1924 (x : Key → ℝ) : Integer.Sparse.eval row1924 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1924, Integer.Sparse.eval_collectBalanced, rawRowCheck1924]

def rawRow1925 : Integer.Sparse Key := [(key2594, -2), (key2881, -2), (key2881, -2), (key2591, 1), (key2591, 1), (key2847, 1), (key2847, 1), (key2878, 1), (key2878, 1), (key2601, 2), (key2911, 2), (key2911, 2), (key2591, -1), (key2591, -1), (key2770, -1), (key2770, -1), (key2878, -1), (key2878, -1), (key2601, -1), (key2601, -1), (key2890, -1), (key2890, -1), (key2911, -1), (key2911, -1), (key2594, 1), (key2594, 1), (key2773, 1), (key2773, 1), (key2881, 1), (key2881, 1)]

theorem rawRowCheck1925 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form0 = rawRow1925 := by decide +kernel

def row1925 : Integer.Sparse Key := [(key2770, -2), (key2773, 2), (key2847, 2), (key2881, -2), (key2890, -2), (key2911, 2)]

theorem rowCheck1925 : row1925 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1925 := by decide +kernel

theorem rowEval1925 (x : Key → ℝ) : Integer.Sparse.eval row1925 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1925, Integer.Sparse.eval_collectBalanced, rawRowCheck1925]

def rawRow1926 : Integer.Sparse Key := [(key2881, -2), (key2594, -2), (key2881, -2), (key2847, 1), (key2878, 1), (key2591, 1), (key2878, 1), (key2591, 1), (key2847, 1), (key2911, 2), (key2601, 2), (key2911, 2), (key2770, -1), (key2878, -1), (key2591, -1), (key2878, -1), (key2591, -1), (key2770, -1), (key2890, -1), (key2911, -1), (key2601, -1), (key2911, -1), (key2601, -1), (key2890, -1), (key2773, 1), (key2881, 1), (key2594, 1), (key2881, 1), (key2594, 1), (key2773, 1)]

theorem rawRowCheck1926 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form0 = rawRow1926 := by decide +kernel

def row1926 : Integer.Sparse Key := [(key2770, -2), (key2773, 2), (key2847, 2), (key2881, -2), (key2890, -2), (key2911, 2)]

theorem rowCheck1926 : row1926 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1926 := by decide +kernel

theorem rowEval1926 (x : Key → ℝ) : Integer.Sparse.eval row1926 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1926, Integer.Sparse.eval_collectBalanced, rawRowCheck1926]

def rawRow1927 : Integer.Sparse Key := [(key2881, -2), (key2881, -2), (key2594, -2), (key2878, 1), (key2847, 1), (key2878, 1), (key2591, 1), (key2847, 1), (key2591, 1), (key2911, 2), (key2911, 2), (key2601, 2), (key2878, -1), (key2770, -1), (key2878, -1), (key2591, -1), (key2770, -1), (key2591, -1), (key2911, -1), (key2890, -1), (key2911, -1), (key2601, -1), (key2890, -1), (key2601, -1), (key2881, 1), (key2773, 1), (key2881, 1), (key2594, 1), (key2773, 1), (key2594, 1)]

theorem rawRowCheck1927 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form0 = rawRow1927 := by decide +kernel

def row1927 : Integer.Sparse Key := [(key2770, -2), (key2773, 2), (key2847, 2), (key2881, -2), (key2890, -2), (key2911, 2)]

theorem rowCheck1927 : row1927 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1927 := by decide +kernel

theorem rowEval1927 (x : Key → ℝ) : Integer.Sparse.eval row1927 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form0) x := by
  rw [rowCheck1927, Integer.Sparse.eval_collectBalanced, rawRowCheck1927]

def rawRow1928 : Integer.Sparse Key := [(key2890, -2), (key2890, -2), (key2890, -2), (key2911, 1), (key2911, 1), (key2911, 1), (key2911, 1), (key2911, 1), (key2911, 1), (key2773, 2), (key2773, 2), (key2773, 2), (key2881, -1), (key2881, -1), (key2881, -1), (key2881, -1), (key2881, -1), (key2881, -1), (key2770, -1), (key2770, -1), (key2770, -1), (key2770, -1), (key2770, -1), (key2770, -1), (key2847, 1), (key2847, 1), (key2847, 1), (key2847, 1), (key2847, 1), (key2847, 1)]

theorem rawRowCheck1928 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form0 = rawRow1928 := by decide +kernel

def row1928 : Integer.Sparse Key := [(key2770, -6), (key2773, 6), (key2847, 6), (key2881, -6), (key2890, -6), (key2911, 6)]

theorem rowCheck1928 : row1928 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1928 := by decide +kernel

theorem rowEval1928 (x : Key → ℝ) : Integer.Sparse.eval row1928 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1928, Integer.Sparse.eval_collectBalanced, rawRowCheck1928]

def rawRow1929 : Integer.Sparse Key := [(key2601, -2), (key2911, -2), (key2911, -2), (key2601, 1), (key2601, 1), (key2890, 1), (key2890, 1), (key2911, 1), (key2911, 1), (key2594, 2), (key2881, 2), (key2881, 2), (key2594, -1), (key2594, -1), (key2773, -1), (key2773, -1), (key2881, -1), (key2881, -1), (key2591, -1), (key2591, -1), (key2847, -1), (key2847, -1), (key2878, -1), (key2878, -1), (key2591, 1), (key2591, 1), (key2770, 1), (key2770, 1), (key2878, 1), (key2878, 1)]

theorem rawRowCheck1929 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form0 = rawRow1929 := by decide +kernel

def row1929 : Integer.Sparse Key := [(key2770, 2), (key2773, -2), (key2847, -2), (key2881, 2), (key2890, 2), (key2911, -2)]

theorem rowCheck1929 : row1929 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1929 := by decide +kernel

theorem rowEval1929 (x : Key → ℝ) : Integer.Sparse.eval row1929 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1929, Integer.Sparse.eval_collectBalanced, rawRowCheck1929]

def rawRow1930 : Integer.Sparse Key := [(key2911, -2), (key2601, -2), (key2911, -2), (key2890, 1), (key2911, 1), (key2601, 1), (key2911, 1), (key2601, 1), (key2890, 1), (key2881, 2), (key2594, 2), (key2881, 2), (key2773, -1), (key2881, -1), (key2594, -1), (key2881, -1), (key2594, -1), (key2773, -1), (key2847, -1), (key2878, -1), (key2591, -1), (key2878, -1), (key2591, -1), (key2847, -1), (key2770, 1), (key2878, 1), (key2591, 1), (key2878, 1), (key2591, 1), (key2770, 1)]

theorem rawRowCheck1930 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form0 = rawRow1930 := by decide +kernel

def row1930 : Integer.Sparse Key := [(key2770, 2), (key2773, -2), (key2847, -2), (key2881, 2), (key2890, 2), (key2911, -2)]

theorem rowCheck1930 : row1930 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1930 := by decide +kernel

theorem rowEval1930 (x : Key → ℝ) : Integer.Sparse.eval row1930 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1930, Integer.Sparse.eval_collectBalanced, rawRowCheck1930]

def rawRow1931 : Integer.Sparse Key := [(key2911, -2), (key2911, -2), (key2601, -2), (key2911, 1), (key2890, 1), (key2911, 1), (key2601, 1), (key2890, 1), (key2601, 1), (key2881, 2), (key2881, 2), (key2594, 2), (key2881, -1), (key2773, -1), (key2881, -1), (key2594, -1), (key2773, -1), (key2594, -1), (key2878, -1), (key2847, -1), (key2878, -1), (key2591, -1), (key2847, -1), (key2591, -1), (key2878, 1), (key2770, 1), (key2878, 1), (key2591, 1), (key2770, 1), (key2591, 1)]

theorem rawRowCheck1931 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form0 = rawRow1931 := by decide +kernel

def row1931 : Integer.Sparse Key := [(key2770, 2), (key2773, -2), (key2847, -2), (key2881, 2), (key2890, 2), (key2911, -2)]

theorem rowCheck1931 : row1931 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1931 := by decide +kernel

theorem rowEval1931 (x : Key → ℝ) : Integer.Sparse.eval row1931 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form0) x := by
  rw [rowCheck1931, Integer.Sparse.eval_collectBalanced, rawRowCheck1931]

def rawRow1932 : Integer.Sparse Key := [(key1249, -6), (key1249, 2), (key1249, 2), (key1262, 2), (key1524, 6), (key1524, -2), (key1524, -2), (key1762, -2), (key1602, -2), (key1602, -2), (key1645, -2), (key1602, 2), (key1602, 2), (key1803, 2)]

theorem rawRowCheck1932 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form1 = rawRow1932 := by decide +kernel

def row1932 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 2), (key1645, -2), (key1762, -2), (key1803, 2)]

theorem rowCheck1932 : row1932 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1932 := by decide +kernel

theorem rowEval1932 (x : Key → ℝ) : Integer.Sparse.eval row1932 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1932, Integer.Sparse.eval_collectBalanced, rawRowCheck1932]

def rawRow1933 : Integer.Sparse Key := [(key1249, -6), (key1249, 2), (key1262, 2), (key1249, 2), (key1524, 6), (key1524, -2), (key1762, -2), (key1524, -2), (key1602, -2), (key1645, -2), (key1602, -2), (key1602, 2), (key1803, 2), (key1602, 2)]

theorem rawRowCheck1933 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form1 = rawRow1933 := by decide +kernel

def row1933 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 2), (key1645, -2), (key1762, -2), (key1803, 2)]

theorem rowCheck1933 : row1933 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1933 := by decide +kernel

theorem rowEval1933 (x : Key → ℝ) : Integer.Sparse.eval row1933 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1933, Integer.Sparse.eval_collectBalanced, rawRowCheck1933]

def rawRow1934 : Integer.Sparse Key := [(key1249, -6), (key1262, 2), (key1249, 2), (key1249, 2), (key1524, 6), (key1762, -2), (key1524, -2), (key1524, -2), (key1645, -2), (key1602, -2), (key1602, -2), (key1803, 2), (key1602, 2), (key1602, 2)]

theorem rawRowCheck1934 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form1 = rawRow1934 := by decide +kernel

def row1934 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 2), (key1645, -2), (key1762, -2), (key1803, 2)]

theorem rowCheck1934 : row1934 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1934 := by decide +kernel

theorem rowEval1934 (x : Key → ℝ) : Integer.Sparse.eval row1934 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1934, Integer.Sparse.eval_collectBalanced, rawRowCheck1934]

def rawRow1935 : Integer.Sparse Key := [(key1262, -6), (key1249, 2), (key1249, 2), (key1249, 2), (key1762, 6), (key1524, -2), (key1524, -2), (key1524, -2), (key1803, -2), (key1803, -2), (key1803, -2), (key1645, 2), (key1645, 2), (key1645, 2)]

theorem rawRowCheck1935 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form1 = rawRow1935 := by decide +kernel

def row1935 : Integer.Sparse Key := [(key1249, 6), (key1262, -6), (key1524, -6), (key1645, 6), (key1762, 6), (key1803, -6)]

theorem rowCheck1935 : row1935 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1935 := by decide +kernel

theorem rowEval1935 (x : Key → ℝ) : Integer.Sparse.eval row1935 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1935, Integer.Sparse.eval_collectBalanced, rawRowCheck1935]

def rawRow1936 : Integer.Sparse Key := [(key1524, -6), (key1602, 2), (key1602, 2), (key1645, 2), (key1249, 6), (key1602, -2), (key1602, -2), (key1803, -2), (key1249, -2), (key1249, -2), (key1262, -2), (key1524, 2), (key1524, 2), (key1762, 2)]

theorem rawRowCheck1936 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form1 = rawRow1936 := by decide +kernel

def row1936 : Integer.Sparse Key := [(key1249, 2), (key1262, -2), (key1524, -2), (key1645, 2), (key1762, 2), (key1803, -2)]

theorem rowCheck1936 : row1936 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1936 := by decide +kernel

theorem rowEval1936 (x : Key → ℝ) : Integer.Sparse.eval row1936 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1936, Integer.Sparse.eval_collectBalanced, rawRowCheck1936]

def rawRow1937 : Integer.Sparse Key := [(key1524, -6), (key1602, 2), (key1645, 2), (key1602, 2), (key1249, 6), (key1602, -2), (key1803, -2), (key1602, -2), (key1249, -2), (key1262, -2), (key1249, -2), (key1524, 2), (key1762, 2), (key1524, 2)]

theorem rawRowCheck1937 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form1 = rawRow1937 := by decide +kernel

def row1937 : Integer.Sparse Key := [(key1249, 2), (key1262, -2), (key1524, -2), (key1645, 2), (key1762, 2), (key1803, -2)]

theorem rowCheck1937 : row1937 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1937 := by decide +kernel

theorem rowEval1937 (x : Key → ℝ) : Integer.Sparse.eval row1937 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1937, Integer.Sparse.eval_collectBalanced, rawRowCheck1937]

def rawRow1938 : Integer.Sparse Key := [(key1524, -6), (key1645, 2), (key1602, 2), (key1602, 2), (key1249, 6), (key1803, -2), (key1602, -2), (key1602, -2), (key1262, -2), (key1249, -2), (key1249, -2), (key1762, 2), (key1524, 2), (key1524, 2)]

theorem rawRowCheck1938 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form1 = rawRow1938 := by decide +kernel

def row1938 : Integer.Sparse Key := [(key1249, 2), (key1262, -2), (key1524, -2), (key1645, 2), (key1762, 2), (key1803, -2)]

theorem rowCheck1938 : row1938 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1938 := by decide +kernel

theorem rowEval1938 (x : Key → ℝ) : Integer.Sparse.eval row1938 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1938, Integer.Sparse.eval_collectBalanced, rawRowCheck1938]

def rawRow1939 : Integer.Sparse Key := [(key1645, -6), (key1524, 2), (key1602, 2), (key1602, 2), (key1803, 6), (key1249, -2), (key1602, -2), (key1602, -2), (key1762, -2), (key1803, -2), (key1803, -2), (key1262, 2), (key1645, 2), (key1645, 2)]

theorem rawRowCheck1939 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form1 = rawRow1939 := by decide +kernel

def row1939 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 2), (key1645, -2), (key1762, -2), (key1803, 2)]

theorem rowCheck1939 : row1939 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1939 := by decide +kernel

theorem rowEval1939 (x : Key → ℝ) : Integer.Sparse.eval row1939 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1939, Integer.Sparse.eval_collectBalanced, rawRowCheck1939]

def rawRow1940 : Integer.Sparse Key := [(key1645, -6), (key1602, 2), (key1524, 2), (key1602, 2), (key1803, 6), (key1602, -2), (key1249, -2), (key1602, -2), (key1803, -2), (key1762, -2), (key1803, -2), (key1645, 2), (key1262, 2), (key1645, 2)]

theorem rawRowCheck1940 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form1 = rawRow1940 := by decide +kernel

def row1940 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 2), (key1645, -2), (key1762, -2), (key1803, 2)]

theorem rowCheck1940 : row1940 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1940 := by decide +kernel

theorem rowEval1940 (x : Key → ℝ) : Integer.Sparse.eval row1940 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1940, Integer.Sparse.eval_collectBalanced, rawRowCheck1940]

def rawRow1941 : Integer.Sparse Key := [(key1645, -6), (key1602, 2), (key1602, 2), (key1524, 2), (key1803, 6), (key1602, -2), (key1602, -2), (key1249, -2), (key1803, -2), (key1803, -2), (key1762, -2), (key1645, 2), (key1645, 2), (key1262, 2)]

theorem rawRowCheck1941 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form1 = rawRow1941 := by decide +kernel

def row1941 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 2), (key1645, -2), (key1762, -2), (key1803, 2)]

theorem rowCheck1941 : row1941 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1941 := by decide +kernel

theorem rowEval1941 (x : Key → ℝ) : Integer.Sparse.eval row1941 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form1) x := by
  rw [rowCheck1941, Integer.Sparse.eval_collectBalanced, rawRowCheck1941]

def rawRow1942 : Integer.Sparse Key := [(key1762, -6), (key1803, 2), (key1803, 2), (key1803, 2), (key1262, 6), (key1645, -2), (key1645, -2), (key1645, -2), (key1249, -2), (key1249, -2), (key1249, -2), (key1524, 2), (key1524, 2), (key1524, 2)]

theorem rawRowCheck1942 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form1 = rawRow1942 := by decide +kernel

def row1942 : Integer.Sparse Key := [(key1249, -6), (key1262, 6), (key1524, 6), (key1645, -6), (key1762, -6), (key1803, 6)]

theorem rowCheck1942 : row1942 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1942 := by decide +kernel

theorem rowEval1942 (x : Key → ℝ) : Integer.Sparse.eval row1942 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1942, Integer.Sparse.eval_collectBalanced, rawRowCheck1942]

def rawRow1943 : Integer.Sparse Key := [(key1803, -6), (key1762, 2), (key1803, 2), (key1803, 2), (key1645, 6), (key1262, -2), (key1645, -2), (key1645, -2), (key1524, -2), (key1602, -2), (key1602, -2), (key1249, 2), (key1602, 2), (key1602, 2)]

theorem rawRowCheck1943 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form1 = rawRow1943 := by decide +kernel

def row1943 : Integer.Sparse Key := [(key1249, 2), (key1262, -2), (key1524, -2), (key1645, 2), (key1762, 2), (key1803, -2)]

theorem rowCheck1943 : row1943 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1943 := by decide +kernel

theorem rowEval1943 (x : Key → ℝ) : Integer.Sparse.eval row1943 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1943, Integer.Sparse.eval_collectBalanced, rawRowCheck1943]

def rawRow1944 : Integer.Sparse Key := [(key1803, -6), (key1803, 2), (key1762, 2), (key1803, 2), (key1645, 6), (key1645, -2), (key1262, -2), (key1645, -2), (key1602, -2), (key1524, -2), (key1602, -2), (key1602, 2), (key1249, 2), (key1602, 2)]

theorem rawRowCheck1944 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form1 = rawRow1944 := by decide +kernel

def row1944 : Integer.Sparse Key := [(key1249, 2), (key1262, -2), (key1524, -2), (key1645, 2), (key1762, 2), (key1803, -2)]

theorem rowCheck1944 : row1944 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1944 := by decide +kernel

theorem rowEval1944 (x : Key → ℝ) : Integer.Sparse.eval row1944 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1944, Integer.Sparse.eval_collectBalanced, rawRowCheck1944]

def rawRow1945 : Integer.Sparse Key := [(key1803, -6), (key1803, 2), (key1803, 2), (key1762, 2), (key1645, 6), (key1645, -2), (key1645, -2), (key1262, -2), (key1602, -2), (key1602, -2), (key1524, -2), (key1602, 2), (key1602, 2), (key1249, 2)]

theorem rawRowCheck1945 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form1 = rawRow1945 := by decide +kernel

def row1945 : Integer.Sparse Key := [(key1249, 2), (key1262, -2), (key1524, -2), (key1645, 2), (key1762, 2), (key1803, -2)]

theorem rowCheck1945 : row1945 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1945 := by decide +kernel

theorem rowEval1945 (x : Key → ℝ) : Integer.Sparse.eval row1945 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form1) x := by
  rw [rowCheck1945, Integer.Sparse.eval_collectBalanced, rawRowCheck1945]

def rawRow1946 : Integer.Sparse Key := [(key2584, -2), (key2588, -2), (key2588, -2), (key2584, 1), (key2588, 1), (key2584, 1), (key2599, 1), (key2588, 1), (key2599, 1), (key2763, 2), (key2767, 2), (key2767, 2), (key2763, -1), (key2767, -1), (key2763, -1), (key2930, -1), (key2767, -1), (key2930, -1), (key2840, -1), (key2844, -1), (key2840, -1), (key2888, -1), (key2844, -1), (key2888, -1), (key2840, 1), (key2844, 1), (key2840, 1), (key2967, 1), (key2844, 1), (key2967, 1)]

theorem rawRowCheck1946 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form2 = rawRow1946 := by decide +kernel

def row1946 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2767, 2), (key2888, -2), (key2930, -2), (key2967, 2)]

theorem rowCheck1946 : row1946 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1946 := by decide +kernel

theorem rowEval1946 (x : Key → ℝ) : Integer.Sparse.eval row1946 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1946, Integer.Sparse.eval_collectBalanced, rawRowCheck1946]

def rawRow1947 : Integer.Sparse Key := [(key2588, -2), (key2584, -2), (key2588, -2), (key2588, 1), (key2584, 1), (key2599, 1), (key2584, 1), (key2599, 1), (key2588, 1), (key2767, 2), (key2763, 2), (key2767, 2), (key2767, -1), (key2763, -1), (key2930, -1), (key2763, -1), (key2930, -1), (key2767, -1), (key2844, -1), (key2840, -1), (key2888, -1), (key2840, -1), (key2888, -1), (key2844, -1), (key2844, 1), (key2840, 1), (key2967, 1), (key2840, 1), (key2967, 1), (key2844, 1)]

theorem rawRowCheck1947 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form2 = rawRow1947 := by decide +kernel

def row1947 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2767, 2), (key2888, -2), (key2930, -2), (key2967, 2)]

theorem rowCheck1947 : row1947 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1947 := by decide +kernel

theorem rowEval1947 (x : Key → ℝ) : Integer.Sparse.eval row1947 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1947, Integer.Sparse.eval_collectBalanced, rawRowCheck1947]

def rawRow1948 : Integer.Sparse Key := [(key2588, -2), (key2588, -2), (key2584, -2), (key2599, 1), (key2599, 1), (key2588, 1), (key2588, 1), (key2584, 1), (key2584, 1), (key2767, 2), (key2767, 2), (key2763, 2), (key2930, -1), (key2930, -1), (key2767, -1), (key2767, -1), (key2763, -1), (key2763, -1), (key2888, -1), (key2888, -1), (key2844, -1), (key2844, -1), (key2840, -1), (key2840, -1), (key2967, 1), (key2967, 1), (key2844, 1), (key2844, 1), (key2840, 1), (key2840, 1)]

theorem rawRowCheck1948 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form2 = rawRow1948 := by decide +kernel

def row1948 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2767, 2), (key2888, -2), (key2930, -2), (key2967, 2)]

theorem rowCheck1948 : row1948 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1948 := by decide +kernel

theorem rowEval1948 (x : Key → ℝ) : Integer.Sparse.eval row1948 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1948, Integer.Sparse.eval_collectBalanced, rawRowCheck1948]

def rawRow1949 : Integer.Sparse Key := [(key2599, -2), (key2599, -2), (key2599, -2), (key2588, 1), (key2588, 1), (key2588, 1), (key2588, 1), (key2588, 1), (key2588, 1), (key2930, 2), (key2930, 2), (key2930, 2), (key2767, -1), (key2767, -1), (key2767, -1), (key2767, -1), (key2767, -1), (key2767, -1), (key2967, -1), (key2967, -1), (key2967, -1), (key2967, -1), (key2967, -1), (key2967, -1), (key2888, 1), (key2888, 1), (key2888, 1), (key2888, 1), (key2888, 1), (key2888, 1)]

theorem rawRowCheck1949 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form2 = rawRow1949 := by decide +kernel

def row1949 : Integer.Sparse Key := [(key2588, 6), (key2599, -6), (key2767, -6), (key2888, 6), (key2930, 6), (key2967, -6)]

theorem rowCheck1949 : row1949 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1949 := by decide +kernel

theorem rowEval1949 (x : Key → ℝ) : Integer.Sparse.eval row1949 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1949, Integer.Sparse.eval_collectBalanced, rawRowCheck1949]

def rawRow1950 : Integer.Sparse Key := [(key2763, -2), (key2767, -2), (key2767, -2), (key2840, 1), (key2844, 1), (key2840, 1), (key2888, 1), (key2844, 1), (key2888, 1), (key2584, 2), (key2588, 2), (key2588, 2), (key2840, -1), (key2844, -1), (key2840, -1), (key2967, -1), (key2844, -1), (key2967, -1), (key2584, -1), (key2588, -1), (key2584, -1), (key2599, -1), (key2588, -1), (key2599, -1), (key2763, 1), (key2767, 1), (key2763, 1), (key2930, 1), (key2767, 1), (key2930, 1)]

theorem rawRowCheck1950 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form2 = rawRow1950 := by decide +kernel

def row1950 : Integer.Sparse Key := [(key2588, 2), (key2599, -2), (key2767, -2), (key2888, 2), (key2930, 2), (key2967, -2)]

theorem rowCheck1950 : row1950 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1950 := by decide +kernel

theorem rowEval1950 (x : Key → ℝ) : Integer.Sparse.eval row1950 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1950, Integer.Sparse.eval_collectBalanced, rawRowCheck1950]

def rawRow1951 : Integer.Sparse Key := [(key2767, -2), (key2763, -2), (key2767, -2), (key2844, 1), (key2840, 1), (key2888, 1), (key2840, 1), (key2888, 1), (key2844, 1), (key2588, 2), (key2584, 2), (key2588, 2), (key2844, -1), (key2840, -1), (key2967, -1), (key2840, -1), (key2967, -1), (key2844, -1), (key2588, -1), (key2584, -1), (key2599, -1), (key2584, -1), (key2599, -1), (key2588, -1), (key2767, 1), (key2763, 1), (key2930, 1), (key2763, 1), (key2930, 1), (key2767, 1)]

theorem rawRowCheck1951 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form2 = rawRow1951 := by decide +kernel

def row1951 : Integer.Sparse Key := [(key2588, 2), (key2599, -2), (key2767, -2), (key2888, 2), (key2930, 2), (key2967, -2)]

theorem rowCheck1951 : row1951 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1951 := by decide +kernel

theorem rowEval1951 (x : Key → ℝ) : Integer.Sparse.eval row1951 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1951, Integer.Sparse.eval_collectBalanced, rawRowCheck1951]

def rawRow1952 : Integer.Sparse Key := [(key2767, -2), (key2767, -2), (key2763, -2), (key2888, 1), (key2888, 1), (key2844, 1), (key2844, 1), (key2840, 1), (key2840, 1), (key2588, 2), (key2588, 2), (key2584, 2), (key2967, -1), (key2967, -1), (key2844, -1), (key2844, -1), (key2840, -1), (key2840, -1), (key2599, -1), (key2599, -1), (key2588, -1), (key2588, -1), (key2584, -1), (key2584, -1), (key2930, 1), (key2930, 1), (key2767, 1), (key2767, 1), (key2763, 1), (key2763, 1)]

theorem rawRowCheck1952 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form2 = rawRow1952 := by decide +kernel

def row1952 : Integer.Sparse Key := [(key2588, 2), (key2599, -2), (key2767, -2), (key2888, 2), (key2930, 2), (key2967, -2)]

theorem rowCheck1952 : row1952 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1952 := by decide +kernel

theorem rowEval1952 (x : Key → ℝ) : Integer.Sparse.eval row1952 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1952, Integer.Sparse.eval_collectBalanced, rawRowCheck1952]

def rawRow1953 : Integer.Sparse Key := [(key2888, -2), (key2888, -2), (key2909, -2), (key2767, 1), (key2767, 1), (key2844, 1), (key2844, 1), (key2875, 1), (key2875, 1), (key2967, 2), (key2967, 2), (key2988, 2), (key2588, -1), (key2588, -1), (key2844, -1), (key2844, -1), (key2875, -1), (key2875, -1), (key2930, -1), (key2930, -1), (key2967, -1), (key2967, -1), (key2988, -1), (key2988, -1), (key2599, 1), (key2599, 1), (key2888, 1), (key2888, 1), (key2909, 1), (key2909, 1)]

theorem rawRowCheck1953 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form2 = rawRow1953 := by decide +kernel

def row1953 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2767, 2), (key2888, -2), (key2930, -2), (key2967, 2)]

theorem rowCheck1953 : row1953 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1953 := by decide +kernel

theorem rowEval1953 (x : Key → ℝ) : Integer.Sparse.eval row1953 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1953, Integer.Sparse.eval_collectBalanced, rawRowCheck1953]

def rawRow1954 : Integer.Sparse Key := [(key2888, -2), (key2909, -2), (key2888, -2), (key2844, 1), (key2875, 1), (key2767, 1), (key2875, 1), (key2767, 1), (key2844, 1), (key2967, 2), (key2988, 2), (key2967, 2), (key2844, -1), (key2875, -1), (key2588, -1), (key2875, -1), (key2588, -1), (key2844, -1), (key2967, -1), (key2988, -1), (key2930, -1), (key2988, -1), (key2930, -1), (key2967, -1), (key2888, 1), (key2909, 1), (key2599, 1), (key2909, 1), (key2599, 1), (key2888, 1)]

theorem rawRowCheck1954 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form2 = rawRow1954 := by decide +kernel

def row1954 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2767, 2), (key2888, -2), (key2930, -2), (key2967, 2)]

theorem rowCheck1954 : row1954 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1954 := by decide +kernel

theorem rowEval1954 (x : Key → ℝ) : Integer.Sparse.eval row1954 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1954, Integer.Sparse.eval_collectBalanced, rawRowCheck1954]

def rawRow1955 : Integer.Sparse Key := [(key2909, -2), (key2888, -2), (key2888, -2), (key2875, 1), (key2844, 1), (key2875, 1), (key2767, 1), (key2844, 1), (key2767, 1), (key2988, 2), (key2967, 2), (key2967, 2), (key2875, -1), (key2844, -1), (key2875, -1), (key2588, -1), (key2844, -1), (key2588, -1), (key2988, -1), (key2967, -1), (key2988, -1), (key2930, -1), (key2967, -1), (key2930, -1), (key2909, 1), (key2888, 1), (key2909, 1), (key2599, 1), (key2888, 1), (key2599, 1)]

theorem rawRowCheck1955 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form2 = rawRow1955 := by decide +kernel

def row1955 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2767, 2), (key2888, -2), (key2930, -2), (key2967, 2)]

theorem rowCheck1955 : row1955 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1955 := by decide +kernel

theorem rowEval1955 (x : Key → ℝ) : Integer.Sparse.eval row1955 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form2) x := by
  rw [rowCheck1955, Integer.Sparse.eval_collectBalanced, rawRowCheck1955]

def rawRow1956 : Integer.Sparse Key := [(key2930, -2), (key2930, -2), (key2930, -2), (key2967, 1), (key2967, 1), (key2967, 1), (key2967, 1), (key2967, 1), (key2967, 1), (key2599, 2), (key2599, 2), (key2599, 2), (key2888, -1), (key2888, -1), (key2888, -1), (key2888, -1), (key2888, -1), (key2888, -1), (key2588, -1), (key2588, -1), (key2588, -1), (key2588, -1), (key2588, -1), (key2588, -1), (key2767, 1), (key2767, 1), (key2767, 1), (key2767, 1), (key2767, 1), (key2767, 1)]

theorem rawRowCheck1956 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form2 = rawRow1956 := by decide +kernel

def row1956 : Integer.Sparse Key := [(key2588, -6), (key2599, 6), (key2767, 6), (key2888, -6), (key2930, -6), (key2967, 6)]

theorem rowCheck1956 : row1956 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1956 := by decide +kernel

theorem rowEval1956 (x : Key → ℝ) : Integer.Sparse.eval row1956 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1956, Integer.Sparse.eval_collectBalanced, rawRowCheck1956]

def rawRow1957 : Integer.Sparse Key := [(key2967, -2), (key2967, -2), (key2988, -2), (key2930, 1), (key2930, 1), (key2967, 1), (key2967, 1), (key2988, 1), (key2988, 1), (key2888, 2), (key2888, 2), (key2909, 2), (key2599, -1), (key2599, -1), (key2888, -1), (key2888, -1), (key2909, -1), (key2909, -1), (key2767, -1), (key2767, -1), (key2844, -1), (key2844, -1), (key2875, -1), (key2875, -1), (key2588, 1), (key2588, 1), (key2844, 1), (key2844, 1), (key2875, 1), (key2875, 1)]

theorem rawRowCheck1957 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form2 = rawRow1957 := by decide +kernel

def row1957 : Integer.Sparse Key := [(key2588, 2), (key2599, -2), (key2767, -2), (key2888, 2), (key2930, 2), (key2967, -2)]

theorem rowCheck1957 : row1957 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1957 := by decide +kernel

theorem rowEval1957 (x : Key → ℝ) : Integer.Sparse.eval row1957 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1957, Integer.Sparse.eval_collectBalanced, rawRowCheck1957]

def rawRow1958 : Integer.Sparse Key := [(key2967, -2), (key2988, -2), (key2967, -2), (key2967, 1), (key2988, 1), (key2930, 1), (key2988, 1), (key2930, 1), (key2967, 1), (key2888, 2), (key2909, 2), (key2888, 2), (key2888, -1), (key2909, -1), (key2599, -1), (key2909, -1), (key2599, -1), (key2888, -1), (key2844, -1), (key2875, -1), (key2767, -1), (key2875, -1), (key2767, -1), (key2844, -1), (key2844, 1), (key2875, 1), (key2588, 1), (key2875, 1), (key2588, 1), (key2844, 1)]

theorem rawRowCheck1958 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form2 = rawRow1958 := by decide +kernel

def row1958 : Integer.Sparse Key := [(key2588, 2), (key2599, -2), (key2767, -2), (key2888, 2), (key2930, 2), (key2967, -2)]

theorem rowCheck1958 : row1958 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1958 := by decide +kernel

theorem rowEval1958 (x : Key → ℝ) : Integer.Sparse.eval row1958 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1958, Integer.Sparse.eval_collectBalanced, rawRowCheck1958]

def rawRow1959 : Integer.Sparse Key := [(key2988, -2), (key2967, -2), (key2967, -2), (key2988, 1), (key2967, 1), (key2988, 1), (key2930, 1), (key2967, 1), (key2930, 1), (key2909, 2), (key2888, 2), (key2888, 2), (key2909, -1), (key2888, -1), (key2909, -1), (key2599, -1), (key2888, -1), (key2599, -1), (key2875, -1), (key2844, -1), (key2875, -1), (key2767, -1), (key2844, -1), (key2767, -1), (key2875, 1), (key2844, 1), (key2875, 1), (key2588, 1), (key2844, 1), (key2588, 1)]

theorem rawRowCheck1959 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form2 = rawRow1959 := by decide +kernel

def row1959 : Integer.Sparse Key := [(key2588, 2), (key2599, -2), (key2767, -2), (key2888, 2), (key2930, 2), (key2967, -2)]

theorem rowCheck1959 : row1959 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1959 := by decide +kernel

theorem rowEval1959 (x : Key → ℝ) : Integer.Sparse.eval row1959 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form2) x := by
  rw [rowCheck1959, Integer.Sparse.eval_collectBalanced, rawRowCheck1959]

def rawRow1960 : Integer.Sparse Key := [(key972, -2), (key977, -2), (key977, -2), (key977, 6), (key1086, 2), (key1091, 2), (key1091, 2), (key1091, -2), (key1091, -2), (key1181, -2), (key1162, -6), (key1162, 2), (key1162, 2), (key1218, 2)]

theorem rawRowCheck1960 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form3 = rawRow1960 := by decide +kernel

def row1960 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1162, -2), (key1181, -2), (key1218, 2)]

theorem rowCheck1960 : row1960 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1960 := by decide +kernel

theorem rowEval1960 (x : Key → ℝ) : Integer.Sparse.eval row1960 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1960, Integer.Sparse.eval_collectBalanced, rawRowCheck1960]

def rawRow1961 : Integer.Sparse Key := [(key977, -2), (key972, -2), (key977, -2), (key977, 6), (key1091, 2), (key1086, 2), (key1091, 2), (key1091, -2), (key1181, -2), (key1091, -2), (key1162, -6), (key1162, 2), (key1218, 2), (key1162, 2)]

theorem rawRowCheck1961 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form3 = rawRow1961 := by decide +kernel

def row1961 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1162, -2), (key1181, -2), (key1218, 2)]

theorem rowCheck1961 : row1961 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1961 := by decide +kernel

theorem rowEval1961 (x : Key → ℝ) : Integer.Sparse.eval row1961 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1961, Integer.Sparse.eval_collectBalanced, rawRowCheck1961]

def rawRow1962 : Integer.Sparse Key := [(key977, -2), (key977, -2), (key972, -2), (key977, 6), (key1091, 2), (key1091, 2), (key1086, 2), (key1181, -2), (key1091, -2), (key1091, -2), (key1162, -6), (key1218, 2), (key1162, 2), (key1162, 2)]

theorem rawRowCheck1962 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form3 = rawRow1962 := by decide +kernel

def row1962 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1162, -2), (key1181, -2), (key1218, 2)]

theorem rowCheck1962 : row1962 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1962 := by decide +kernel

theorem rowEval1962 (x : Key → ℝ) : Integer.Sparse.eval row1962 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1962, Integer.Sparse.eval_collectBalanced, rawRowCheck1962]

def rawRow1963 : Integer.Sparse Key := [(key977, -2), (key977, -2), (key977, -2), (key972, 6), (key1181, 2), (key1181, 2), (key1181, 2), (key1086, -2), (key1086, -2), (key1086, -2), (key1218, -6), (key1162, 2), (key1162, 2), (key1162, 2)]

theorem rawRowCheck1963 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form3 = rawRow1963 := by decide +kernel

def row1963 : Integer.Sparse Key := [(key972, 6), (key977, -6), (key1086, -6), (key1162, 6), (key1181, 6), (key1218, -6)]

theorem rowCheck1963 : row1963 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1963 := by decide +kernel

theorem rowEval1963 (x : Key → ℝ) : Integer.Sparse.eval row1963 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1963, Integer.Sparse.eval_collectBalanced, rawRowCheck1963]

def rawRow1964 : Integer.Sparse Key := [(key1086, -2), (key1091, -2), (key1091, -2), (key1162, 6), (key972, 2), (key977, 2), (key977, 2), (key1162, -2), (key1162, -2), (key1218, -2), (key977, -6), (key1091, 2), (key1091, 2), (key1181, 2)]

theorem rawRowCheck1964 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form3 = rawRow1964 := by decide +kernel

def row1964 : Integer.Sparse Key := [(key972, 2), (key977, -2), (key1086, -2), (key1162, 2), (key1181, 2), (key1218, -2)]

theorem rowCheck1964 : row1964 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1964 := by decide +kernel

theorem rowEval1964 (x : Key → ℝ) : Integer.Sparse.eval row1964 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1964, Integer.Sparse.eval_collectBalanced, rawRowCheck1964]

def rawRow1965 : Integer.Sparse Key := [(key1091, -2), (key1086, -2), (key1091, -2), (key1162, 6), (key977, 2), (key972, 2), (key977, 2), (key1162, -2), (key1218, -2), (key1162, -2), (key977, -6), (key1091, 2), (key1181, 2), (key1091, 2)]

theorem rawRowCheck1965 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form3 = rawRow1965 := by decide +kernel

def row1965 : Integer.Sparse Key := [(key972, 2), (key977, -2), (key1086, -2), (key1162, 2), (key1181, 2), (key1218, -2)]

theorem rowCheck1965 : row1965 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1965 := by decide +kernel

theorem rowEval1965 (x : Key → ℝ) : Integer.Sparse.eval row1965 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1965, Integer.Sparse.eval_collectBalanced, rawRowCheck1965]

def rawRow1966 : Integer.Sparse Key := [(key1091, -2), (key1091, -2), (key1086, -2), (key1162, 6), (key977, 2), (key977, 2), (key972, 2), (key1218, -2), (key1162, -2), (key1162, -2), (key977, -6), (key1181, 2), (key1091, 2), (key1091, 2)]

theorem rawRowCheck1966 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form3 = rawRow1966 := by decide +kernel

def row1966 : Integer.Sparse Key := [(key972, 2), (key977, -2), (key1086, -2), (key1162, 2), (key1181, 2), (key1218, -2)]

theorem rowCheck1966 : row1966 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1966 := by decide +kernel

theorem rowEval1966 (x : Key → ℝ) : Integer.Sparse.eval row1966 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1966, Integer.Sparse.eval_collectBalanced, rawRowCheck1966]

def rawRow1967 : Integer.Sparse Key := [(key1091, -2), (key1091, -2), (key1162, -2), (key1086, 6), (key1181, 2), (key1181, 2), (key1218, 2), (key972, -2), (key1086, -2), (key1086, -2), (key1181, -6), (key977, 2), (key1091, 2), (key1091, 2)]

theorem rawRowCheck1967 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form3 = rawRow1967 := by decide +kernel

def row1967 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1162, -2), (key1181, -2), (key1218, 2)]

theorem rowCheck1967 : row1967 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1967 := by decide +kernel

theorem rowEval1967 (x : Key → ℝ) : Integer.Sparse.eval row1967 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1967, Integer.Sparse.eval_collectBalanced, rawRowCheck1967]

def rawRow1968 : Integer.Sparse Key := [(key1091, -2), (key1162, -2), (key1091, -2), (key1086, 6), (key1181, 2), (key1218, 2), (key1181, 2), (key1086, -2), (key972, -2), (key1086, -2), (key1181, -6), (key1091, 2), (key977, 2), (key1091, 2)]

theorem rawRowCheck1968 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form3 = rawRow1968 := by decide +kernel

def row1968 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1162, -2), (key1181, -2), (key1218, 2)]

theorem rowCheck1968 : row1968 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1968 := by decide +kernel

theorem rowEval1968 (x : Key → ℝ) : Integer.Sparse.eval row1968 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1968, Integer.Sparse.eval_collectBalanced, rawRowCheck1968]

def rawRow1969 : Integer.Sparse Key := [(key1162, -2), (key1091, -2), (key1091, -2), (key1086, 6), (key1218, 2), (key1181, 2), (key1181, 2), (key1086, -2), (key1086, -2), (key972, -2), (key1181, -6), (key1091, 2), (key1091, 2), (key977, 2)]

theorem rawRowCheck1969 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form3 = rawRow1969 := by decide +kernel

def row1969 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1162, -2), (key1181, -2), (key1218, 2)]

theorem rowCheck1969 : row1969 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1969 := by decide +kernel

theorem rowEval1969 (x : Key → ℝ) : Integer.Sparse.eval row1969 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form3) x := by
  rw [rowCheck1969, Integer.Sparse.eval_collectBalanced, rawRowCheck1969]

def rawRow1970 : Integer.Sparse Key := [(key1181, -2), (key1181, -2), (key1181, -2), (key1218, 6), (key977, 2), (key977, 2), (key977, 2), (key1162, -2), (key1162, -2), (key1162, -2), (key972, -6), (key1086, 2), (key1086, 2), (key1086, 2)]

theorem rawRowCheck1970 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form3 = rawRow1970 := by decide +kernel

def row1970 : Integer.Sparse Key := [(key972, -6), (key977, 6), (key1086, 6), (key1162, -6), (key1181, -6), (key1218, 6)]

theorem rowCheck1970 : row1970 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1970 := by decide +kernel

theorem rowEval1970 (x : Key → ℝ) : Integer.Sparse.eval row1970 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1970, Integer.Sparse.eval_collectBalanced, rawRowCheck1970]

def rawRow1971 : Integer.Sparse Key := [(key1181, -2), (key1181, -2), (key1218, -2), (key1181, 6), (key1091, 2), (key1091, 2), (key1162, 2), (key977, -2), (key1091, -2), (key1091, -2), (key1086, -6), (key972, 2), (key1086, 2), (key1086, 2)]

theorem rawRowCheck1971 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form3 = rawRow1971 := by decide +kernel

def row1971 : Integer.Sparse Key := [(key972, 2), (key977, -2), (key1086, -2), (key1162, 2), (key1181, 2), (key1218, -2)]

theorem rowCheck1971 : row1971 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1971 := by decide +kernel

theorem rowEval1971 (x : Key → ℝ) : Integer.Sparse.eval row1971 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1971, Integer.Sparse.eval_collectBalanced, rawRowCheck1971]

def rawRow1972 : Integer.Sparse Key := [(key1181, -2), (key1218, -2), (key1181, -2), (key1181, 6), (key1091, 2), (key1162, 2), (key1091, 2), (key1091, -2), (key977, -2), (key1091, -2), (key1086, -6), (key1086, 2), (key972, 2), (key1086, 2)]

theorem rawRowCheck1972 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form3 = rawRow1972 := by decide +kernel

def row1972 : Integer.Sparse Key := [(key972, 2), (key977, -2), (key1086, -2), (key1162, 2), (key1181, 2), (key1218, -2)]

theorem rowCheck1972 : row1972 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1972 := by decide +kernel

theorem rowEval1972 (x : Key → ℝ) : Integer.Sparse.eval row1972 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1972, Integer.Sparse.eval_collectBalanced, rawRowCheck1972]

def rawRow1973 : Integer.Sparse Key := [(key1218, -2), (key1181, -2), (key1181, -2), (key1181, 6), (key1162, 2), (key1091, 2), (key1091, 2), (key1091, -2), (key1091, -2), (key977, -2), (key1086, -6), (key1086, 2), (key1086, 2), (key972, 2)]

theorem rawRowCheck1973 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form3 = rawRow1973 := by decide +kernel

def row1973 : Integer.Sparse Key := [(key972, 2), (key977, -2), (key1086, -2), (key1162, 2), (key1181, 2), (key1218, -2)]

theorem rowCheck1973 : row1973 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1973 := by decide +kernel

theorem rowEval1973 (x : Key → ℝ) : Integer.Sparse.eval row1973 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form3) x := by
  rw [rowCheck1973, Integer.Sparse.eval_collectBalanced, rawRowCheck1973]

def rawRow1974 : Integer.Sparse Key := [(key2369, -6), (key2369, 2), (key2369, 2), (key2384, 2), (key2397, 6), (key2397, -2), (key2397, -2), (key2431, -2), (key2463, -2), (key2463, -2), (key2474, -2), (key2463, 2), (key2463, 2), (key2497, 2)]

theorem rawRowCheck1974 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form4 = rawRow1974 := by decide +kernel

def row1974 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 2), (key2431, -2), (key2474, -2), (key2497, 2)]

theorem rowCheck1974 : row1974 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1974 := by decide +kernel

theorem rowEval1974 (x : Key → ℝ) : Integer.Sparse.eval row1974 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1974, Integer.Sparse.eval_collectBalanced, rawRowCheck1974]

def rawRow1975 : Integer.Sparse Key := [(key2369, -6), (key2369, 2), (key2384, 2), (key2369, 2), (key2397, 6), (key2397, -2), (key2431, -2), (key2397, -2), (key2463, -2), (key2474, -2), (key2463, -2), (key2463, 2), (key2497, 2), (key2463, 2)]

theorem rawRowCheck1975 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form4 = rawRow1975 := by decide +kernel

def row1975 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 2), (key2431, -2), (key2474, -2), (key2497, 2)]

theorem rowCheck1975 : row1975 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1975 := by decide +kernel

theorem rowEval1975 (x : Key → ℝ) : Integer.Sparse.eval row1975 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1975, Integer.Sparse.eval_collectBalanced, rawRowCheck1975]

def rawRow1976 : Integer.Sparse Key := [(key2369, -6), (key2384, 2), (key2369, 2), (key2369, 2), (key2397, 6), (key2431, -2), (key2397, -2), (key2397, -2), (key2474, -2), (key2463, -2), (key2463, -2), (key2497, 2), (key2463, 2), (key2463, 2)]

theorem rawRowCheck1976 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form4 = rawRow1976 := by decide +kernel

def row1976 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 2), (key2431, -2), (key2474, -2), (key2497, 2)]

theorem rowCheck1976 : row1976 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1976 := by decide +kernel

theorem rowEval1976 (x : Key → ℝ) : Integer.Sparse.eval row1976 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1976, Integer.Sparse.eval_collectBalanced, rawRowCheck1976]

def rawRow1977 : Integer.Sparse Key := [(key2384, -6), (key2369, 2), (key2369, 2), (key2369, 2), (key2431, 6), (key2397, -2), (key2397, -2), (key2397, -2), (key2497, -2), (key2497, -2), (key2497, -2), (key2474, 2), (key2474, 2), (key2474, 2)]

theorem rawRowCheck1977 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form4 = rawRow1977 := by decide +kernel

def row1977 : Integer.Sparse Key := [(key2369, 6), (key2384, -6), (key2397, -6), (key2431, 6), (key2474, 6), (key2497, -6)]

theorem rowCheck1977 : row1977 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1977 := by decide +kernel

theorem rowEval1977 (x : Key → ℝ) : Integer.Sparse.eval row1977 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1977, Integer.Sparse.eval_collectBalanced, rawRowCheck1977]

def rawRow1978 : Integer.Sparse Key := [(key2397, -6), (key2463, 2), (key2463, 2), (key2474, 2), (key2369, 6), (key2463, -2), (key2463, -2), (key2497, -2), (key2369, -2), (key2369, -2), (key2384, -2), (key2397, 2), (key2397, 2), (key2431, 2)]

theorem rawRowCheck1978 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form4 = rawRow1978 := by decide +kernel

def row1978 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, -2), (key2431, 2), (key2474, 2), (key2497, -2)]

theorem rowCheck1978 : row1978 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1978 := by decide +kernel

theorem rowEval1978 (x : Key → ℝ) : Integer.Sparse.eval row1978 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1978, Integer.Sparse.eval_collectBalanced, rawRowCheck1978]

def rawRow1979 : Integer.Sparse Key := [(key2397, -6), (key2463, 2), (key2474, 2), (key2463, 2), (key2369, 6), (key2463, -2), (key2497, -2), (key2463, -2), (key2369, -2), (key2384, -2), (key2369, -2), (key2397, 2), (key2431, 2), (key2397, 2)]

theorem rawRowCheck1979 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form4 = rawRow1979 := by decide +kernel

def row1979 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, -2), (key2431, 2), (key2474, 2), (key2497, -2)]

theorem rowCheck1979 : row1979 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1979 := by decide +kernel

theorem rowEval1979 (x : Key → ℝ) : Integer.Sparse.eval row1979 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1979, Integer.Sparse.eval_collectBalanced, rawRowCheck1979]

def rawRow1980 : Integer.Sparse Key := [(key2397, -6), (key2474, 2), (key2463, 2), (key2463, 2), (key2369, 6), (key2497, -2), (key2463, -2), (key2463, -2), (key2384, -2), (key2369, -2), (key2369, -2), (key2431, 2), (key2397, 2), (key2397, 2)]

theorem rawRowCheck1980 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form4 = rawRow1980 := by decide +kernel

def row1980 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, -2), (key2431, 2), (key2474, 2), (key2497, -2)]

theorem rowCheck1980 : row1980 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1980 := by decide +kernel

theorem rowEval1980 (x : Key → ℝ) : Integer.Sparse.eval row1980 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1980, Integer.Sparse.eval_collectBalanced, rawRowCheck1980]

def rawRow1981 : Integer.Sparse Key := [(key2474, -6), (key2397, 2), (key2463, 2), (key2463, 2), (key2497, 6), (key2369, -2), (key2463, -2), (key2463, -2), (key2431, -2), (key2497, -2), (key2497, -2), (key2384, 2), (key2474, 2), (key2474, 2)]

theorem rawRowCheck1981 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form4 = rawRow1981 := by decide +kernel

def row1981 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 2), (key2431, -2), (key2474, -2), (key2497, 2)]

theorem rowCheck1981 : row1981 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1981 := by decide +kernel

theorem rowEval1981 (x : Key → ℝ) : Integer.Sparse.eval row1981 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1981, Integer.Sparse.eval_collectBalanced, rawRowCheck1981]

def rawRow1982 : Integer.Sparse Key := [(key2474, -6), (key2463, 2), (key2397, 2), (key2463, 2), (key2497, 6), (key2463, -2), (key2369, -2), (key2463, -2), (key2497, -2), (key2431, -2), (key2497, -2), (key2474, 2), (key2384, 2), (key2474, 2)]

theorem rawRowCheck1982 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form4 = rawRow1982 := by decide +kernel

def row1982 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 2), (key2431, -2), (key2474, -2), (key2497, 2)]

theorem rowCheck1982 : row1982 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1982 := by decide +kernel

theorem rowEval1982 (x : Key → ℝ) : Integer.Sparse.eval row1982 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1982, Integer.Sparse.eval_collectBalanced, rawRowCheck1982]

def rawRow1983 : Integer.Sparse Key := [(key2474, -6), (key2463, 2), (key2463, 2), (key2397, 2), (key2497, 6), (key2463, -2), (key2463, -2), (key2369, -2), (key2497, -2), (key2497, -2), (key2431, -2), (key2474, 2), (key2474, 2), (key2384, 2)]

theorem rawRowCheck1983 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form4 = rawRow1983 := by decide +kernel

def row1983 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 2), (key2431, -2), (key2474, -2), (key2497, 2)]

theorem rowCheck1983 : row1983 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1983 := by decide +kernel

theorem rowEval1983 (x : Key → ℝ) : Integer.Sparse.eval row1983 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form4) x := by
  rw [rowCheck1983, Integer.Sparse.eval_collectBalanced, rawRowCheck1983]

def rawRow1984 : Integer.Sparse Key := [(key2431, -6), (key2497, 2), (key2497, 2), (key2497, 2), (key2384, 6), (key2474, -2), (key2474, -2), (key2474, -2), (key2369, -2), (key2369, -2), (key2369, -2), (key2397, 2), (key2397, 2), (key2397, 2)]

theorem rawRowCheck1984 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form4 = rawRow1984 := by decide +kernel

def row1984 : Integer.Sparse Key := [(key2369, -6), (key2384, 6), (key2397, 6), (key2431, -6), (key2474, -6), (key2497, 6)]

theorem rowCheck1984 : row1984 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1984 := by decide +kernel

theorem rowEval1984 (x : Key → ℝ) : Integer.Sparse.eval row1984 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1984, Integer.Sparse.eval_collectBalanced, rawRowCheck1984]

def rawRow1985 : Integer.Sparse Key := [(key2497, -6), (key2431, 2), (key2497, 2), (key2497, 2), (key2474, 6), (key2384, -2), (key2474, -2), (key2474, -2), (key2397, -2), (key2463, -2), (key2463, -2), (key2369, 2), (key2463, 2), (key2463, 2)]

theorem rawRowCheck1985 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form4 = rawRow1985 := by decide +kernel

def row1985 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, -2), (key2431, 2), (key2474, 2), (key2497, -2)]

theorem rowCheck1985 : row1985 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1985 := by decide +kernel

theorem rowEval1985 (x : Key → ℝ) : Integer.Sparse.eval row1985 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1985, Integer.Sparse.eval_collectBalanced, rawRowCheck1985]

def rawRow1986 : Integer.Sparse Key := [(key2497, -6), (key2497, 2), (key2431, 2), (key2497, 2), (key2474, 6), (key2474, -2), (key2384, -2), (key2474, -2), (key2463, -2), (key2397, -2), (key2463, -2), (key2463, 2), (key2369, 2), (key2463, 2)]

theorem rawRowCheck1986 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form4 = rawRow1986 := by decide +kernel

def row1986 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, -2), (key2431, 2), (key2474, 2), (key2497, -2)]

theorem rowCheck1986 : row1986 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1986 := by decide +kernel

theorem rowEval1986 (x : Key → ℝ) : Integer.Sparse.eval row1986 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1986, Integer.Sparse.eval_collectBalanced, rawRowCheck1986]

def rawRow1987 : Integer.Sparse Key := [(key2497, -6), (key2497, 2), (key2497, 2), (key2431, 2), (key2474, 6), (key2474, -2), (key2474, -2), (key2384, -2), (key2463, -2), (key2463, -2), (key2397, -2), (key2463, 2), (key2463, 2), (key2369, 2)]

theorem rawRowCheck1987 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form4 = rawRow1987 := by decide +kernel

def row1987 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, -2), (key2431, 2), (key2474, 2), (key2497, -2)]

theorem rowCheck1987 : row1987 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1987 := by decide +kernel

theorem rowEval1987 (x : Key → ℝ) : Integer.Sparse.eval row1987 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form4) x := by
  rw [rowCheck1987, Integer.Sparse.eval_collectBalanced, rawRowCheck1987]

def rawRow1988 : Integer.Sparse Key := [(key1527, -1), (key1532, -1), (key1527, -1), (key1766, -1), (key1532, -1), (key1766, -1), (key1532, 2), (key1532, 2), (key1766, 2), (key1605, 1), (key1610, 1), (key1605, 1), (key1807, 1), (key1610, 1), (key1807, 1), (key1610, -1), (key1649, -1), (key1610, -1), (key1807, -1), (key1649, -1), (key1807, -1), (key1638, -2), (key1638, -2), (key1830, -2), (key1638, 1), (key1672, 1), (key1638, 1), (key1830, 1), (key1672, 1), (key1830, 1)]

theorem rawRowCheck1988 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form5 = rawRow1988 := by decide +kernel

def row1988 : Integer.Sparse Key := [(key1527, -2), (key1532, 2), (key1605, 2), (key1638, -2), (key1649, -2), (key1672, 2)]

theorem rowCheck1988 : row1988 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1988 := by decide +kernel

theorem rowEval1988 (x : Key → ℝ) : Integer.Sparse.eval row1988 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1988, Integer.Sparse.eval_collectBalanced, rawRowCheck1988]

def rawRow1989 : Integer.Sparse Key := [(key1532, -1), (key1527, -1), (key1766, -1), (key1527, -1), (key1766, -1), (key1532, -1), (key1532, 2), (key1766, 2), (key1532, 2), (key1610, 1), (key1605, 1), (key1807, 1), (key1605, 1), (key1807, 1), (key1610, 1), (key1649, -1), (key1610, -1), (key1807, -1), (key1610, -1), (key1807, -1), (key1649, -1), (key1638, -2), (key1830, -2), (key1638, -2), (key1672, 1), (key1638, 1), (key1830, 1), (key1638, 1), (key1830, 1), (key1672, 1)]

theorem rawRowCheck1989 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form5 = rawRow1989 := by decide +kernel

def row1989 : Integer.Sparse Key := [(key1527, -2), (key1532, 2), (key1605, 2), (key1638, -2), (key1649, -2), (key1672, 2)]

theorem rowCheck1989 : row1989 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1989 := by decide +kernel

theorem rowEval1989 (x : Key → ℝ) : Integer.Sparse.eval row1989 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1989, Integer.Sparse.eval_collectBalanced, rawRowCheck1989]

def rawRow1990 : Integer.Sparse Key := [(key1766, -1), (key1766, -1), (key1532, -1), (key1532, -1), (key1527, -1), (key1527, -1), (key1766, 2), (key1532, 2), (key1532, 2), (key1807, 1), (key1807, 1), (key1610, 1), (key1610, 1), (key1605, 1), (key1605, 1), (key1807, -1), (key1807, -1), (key1649, -1), (key1649, -1), (key1610, -1), (key1610, -1), (key1830, -2), (key1638, -2), (key1638, -2), (key1830, 1), (key1830, 1), (key1672, 1), (key1672, 1), (key1638, 1), (key1638, 1)]

theorem rawRowCheck1990 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form5 = rawRow1990 := by decide +kernel

def row1990 : Integer.Sparse Key := [(key1527, -2), (key1532, 2), (key1605, 2), (key1638, -2), (key1649, -2), (key1672, 2)]

theorem rowCheck1990 : row1990 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1990 := by decide +kernel

theorem rowEval1990 (x : Key → ℝ) : Integer.Sparse.eval row1990 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1990, Integer.Sparse.eval_collectBalanced, rawRowCheck1990]

def rawRow1991 : Integer.Sparse Key := [(key1532, -1), (key1532, -1), (key1532, -1), (key1532, -1), (key1532, -1), (key1532, -1), (key1527, 2), (key1527, 2), (key1527, 2), (key1649, 1), (key1649, 1), (key1649, 1), (key1649, 1), (key1649, 1), (key1649, 1), (key1605, -1), (key1605, -1), (key1605, -1), (key1605, -1), (key1605, -1), (key1605, -1), (key1672, -2), (key1672, -2), (key1672, -2), (key1638, 1), (key1638, 1), (key1638, 1), (key1638, 1), (key1638, 1), (key1638, 1)]

theorem rawRowCheck1991 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form5 = rawRow1991 := by decide +kernel

def row1991 : Integer.Sparse Key := [(key1527, 6), (key1532, -6), (key1605, -6), (key1638, 6), (key1649, 6), (key1672, -6)]

theorem rowCheck1991 : row1991 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1991 := by decide +kernel

theorem rowEval1991 (x : Key → ℝ) : Integer.Sparse.eval row1991 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1991, Integer.Sparse.eval_collectBalanced, rawRowCheck1991]

def rawRow1992 : Integer.Sparse Key := [(key1605, -1), (key1610, -1), (key1605, -1), (key1807, -1), (key1610, -1), (key1807, -1), (key1638, 2), (key1638, 2), (key1830, 2), (key1527, 1), (key1532, 1), (key1527, 1), (key1766, 1), (key1532, 1), (key1766, 1), (key1638, -1), (key1672, -1), (key1638, -1), (key1830, -1), (key1672, -1), (key1830, -1), (key1532, -2), (key1532, -2), (key1766, -2), (key1610, 1), (key1649, 1), (key1610, 1), (key1807, 1), (key1649, 1), (key1807, 1)]

theorem rawRowCheck1992 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form5 = rawRow1992 := by decide +kernel

def row1992 : Integer.Sparse Key := [(key1527, 2), (key1532, -2), (key1605, -2), (key1638, 2), (key1649, 2), (key1672, -2)]

theorem rowCheck1992 : row1992 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1992 := by decide +kernel

theorem rowEval1992 (x : Key → ℝ) : Integer.Sparse.eval row1992 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1992, Integer.Sparse.eval_collectBalanced, rawRowCheck1992]

def rawRow1993 : Integer.Sparse Key := [(key1610, -1), (key1605, -1), (key1807, -1), (key1605, -1), (key1807, -1), (key1610, -1), (key1638, 2), (key1830, 2), (key1638, 2), (key1532, 1), (key1527, 1), (key1766, 1), (key1527, 1), (key1766, 1), (key1532, 1), (key1672, -1), (key1638, -1), (key1830, -1), (key1638, -1), (key1830, -1), (key1672, -1), (key1532, -2), (key1766, -2), (key1532, -2), (key1649, 1), (key1610, 1), (key1807, 1), (key1610, 1), (key1807, 1), (key1649, 1)]

theorem rawRowCheck1993 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form5 = rawRow1993 := by decide +kernel

def row1993 : Integer.Sparse Key := [(key1527, 2), (key1532, -2), (key1605, -2), (key1638, 2), (key1649, 2), (key1672, -2)]

theorem rowCheck1993 : row1993 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1993 := by decide +kernel

theorem rowEval1993 (x : Key → ℝ) : Integer.Sparse.eval row1993 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1993, Integer.Sparse.eval_collectBalanced, rawRowCheck1993]

def rawRow1994 : Integer.Sparse Key := [(key1807, -1), (key1807, -1), (key1610, -1), (key1610, -1), (key1605, -1), (key1605, -1), (key1830, 2), (key1638, 2), (key1638, 2), (key1766, 1), (key1766, 1), (key1532, 1), (key1532, 1), (key1527, 1), (key1527, 1), (key1830, -1), (key1830, -1), (key1672, -1), (key1672, -1), (key1638, -1), (key1638, -1), (key1766, -2), (key1532, -2), (key1532, -2), (key1807, 1), (key1807, 1), (key1649, 1), (key1649, 1), (key1610, 1), (key1610, 1)]

theorem rawRowCheck1994 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form5 = rawRow1994 := by decide +kernel

def row1994 : Integer.Sparse Key := [(key1527, 2), (key1532, -2), (key1605, -2), (key1638, 2), (key1649, 2), (key1672, -2)]

theorem rowCheck1994 : row1994 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1994 := by decide +kernel

theorem rowEval1994 (x : Key → ℝ) : Integer.Sparse.eval row1994 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1994, Integer.Sparse.eval_collectBalanced, rawRowCheck1994]

def rawRow1995 : Integer.Sparse Key := [(key1257, -1), (key1257, -1), (key1610, -1), (key1610, -1), (key1638, -1), (key1638, -1), (key1252, 2), (key1605, 2), (key1605, 2), (key1266, 1), (key1266, 1), (key1649, 1), (key1649, 1), (key1672, 1), (key1672, 1), (key1252, -1), (key1252, -1), (key1527, -1), (key1527, -1), (key1605, -1), (key1605, -1), (key1266, -2), (key1649, -2), (key1649, -2), (key1257, 1), (key1257, 1), (key1532, 1), (key1532, 1), (key1610, 1), (key1610, 1)]

theorem rawRowCheck1995 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form5 = rawRow1995 := by decide +kernel

def row1995 : Integer.Sparse Key := [(key1527, -2), (key1532, 2), (key1605, 2), (key1638, -2), (key1649, -2), (key1672, 2)]

theorem rowCheck1995 : row1995 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1995 := by decide +kernel

theorem rowEval1995 (x : Key → ℝ) : Integer.Sparse.eval row1995 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1995, Integer.Sparse.eval_collectBalanced, rawRowCheck1995]

def rawRow1996 : Integer.Sparse Key := [(key1610, -1), (key1638, -1), (key1257, -1), (key1638, -1), (key1257, -1), (key1610, -1), (key1605, 2), (key1252, 2), (key1605, 2), (key1649, 1), (key1672, 1), (key1266, 1), (key1672, 1), (key1266, 1), (key1649, 1), (key1527, -1), (key1605, -1), (key1252, -1), (key1605, -1), (key1252, -1), (key1527, -1), (key1649, -2), (key1266, -2), (key1649, -2), (key1532, 1), (key1610, 1), (key1257, 1), (key1610, 1), (key1257, 1), (key1532, 1)]

theorem rawRowCheck1996 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form5 = rawRow1996 := by decide +kernel

def row1996 : Integer.Sparse Key := [(key1527, -2), (key1532, 2), (key1605, 2), (key1638, -2), (key1649, -2), (key1672, 2)]

theorem rowCheck1996 : row1996 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1996 := by decide +kernel

theorem rowEval1996 (x : Key → ℝ) : Integer.Sparse.eval row1996 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1996, Integer.Sparse.eval_collectBalanced, rawRowCheck1996]

def rawRow1997 : Integer.Sparse Key := [(key1638, -1), (key1610, -1), (key1638, -1), (key1257, -1), (key1610, -1), (key1257, -1), (key1605, 2), (key1605, 2), (key1252, 2), (key1672, 1), (key1649, 1), (key1672, 1), (key1266, 1), (key1649, 1), (key1266, 1), (key1605, -1), (key1527, -1), (key1605, -1), (key1252, -1), (key1527, -1), (key1252, -1), (key1649, -2), (key1649, -2), (key1266, -2), (key1610, 1), (key1532, 1), (key1610, 1), (key1257, 1), (key1532, 1), (key1257, 1)]

theorem rawRowCheck1997 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form5 = rawRow1997 := by decide +kernel

def row1997 : Integer.Sparse Key := [(key1527, -2), (key1532, 2), (key1605, 2), (key1638, -2), (key1649, -2), (key1672, 2)]

theorem rowCheck1997 : row1997 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1997 := by decide +kernel

theorem rowEval1997 (x : Key → ℝ) : Integer.Sparse.eval row1997 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form5) x := by
  rw [rowCheck1997, Integer.Sparse.eval_collectBalanced, rawRowCheck1997]

def rawRow1998 : Integer.Sparse Key := [(key1649, -1), (key1649, -1), (key1649, -1), (key1649, -1), (key1649, -1), (key1649, -1), (key1672, 2), (key1672, 2), (key1672, 2), (key1532, 1), (key1532, 1), (key1532, 1), (key1532, 1), (key1532, 1), (key1532, 1), (key1638, -1), (key1638, -1), (key1638, -1), (key1638, -1), (key1638, -1), (key1638, -1), (key1527, -2), (key1527, -2), (key1527, -2), (key1605, 1), (key1605, 1), (key1605, 1), (key1605, 1), (key1605, 1), (key1605, 1)]

theorem rawRowCheck1998 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form5 = rawRow1998 := by decide +kernel

def row1998 : Integer.Sparse Key := [(key1527, -6), (key1532, 6), (key1605, 6), (key1638, -6), (key1649, -6), (key1672, 6)]

theorem rowCheck1998 : row1998 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1998 := by decide +kernel

theorem rowEval1998 (x : Key → ℝ) : Integer.Sparse.eval row1998 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1998, Integer.Sparse.eval_collectBalanced, rawRowCheck1998]

def rawRow1999 : Integer.Sparse Key := [(key1266, -1), (key1266, -1), (key1649, -1), (key1649, -1), (key1672, -1), (key1672, -1), (key1266, 2), (key1649, 2), (key1649, 2), (key1257, 1), (key1257, 1), (key1610, 1), (key1610, 1), (key1638, 1), (key1638, 1), (key1257, -1), (key1257, -1), (key1532, -1), (key1532, -1), (key1610, -1), (key1610, -1), (key1252, -2), (key1605, -2), (key1605, -2), (key1252, 1), (key1252, 1), (key1527, 1), (key1527, 1), (key1605, 1), (key1605, 1)]

theorem rawRowCheck1999 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form5 = rawRow1999 := by decide +kernel

def row1999 : Integer.Sparse Key := [(key1527, 2), (key1532, -2), (key1605, -2), (key1638, 2), (key1649, 2), (key1672, -2)]

theorem rowCheck1999 : row1999 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1999 := by decide +kernel

theorem rowEval1999 (x : Key → ℝ) : Integer.Sparse.eval row1999 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1999, Integer.Sparse.eval_collectBalanced, rawRowCheck1999]

def rawRow2000 : Integer.Sparse Key := [(key1649, -1), (key1672, -1), (key1266, -1), (key1672, -1), (key1266, -1), (key1649, -1), (key1649, 2), (key1266, 2), (key1649, 2), (key1610, 1), (key1638, 1), (key1257, 1), (key1638, 1), (key1257, 1), (key1610, 1), (key1532, -1), (key1610, -1), (key1257, -1), (key1610, -1), (key1257, -1), (key1532, -1), (key1605, -2), (key1252, -2), (key1605, -2), (key1527, 1), (key1605, 1), (key1252, 1), (key1605, 1), (key1252, 1), (key1527, 1)]

theorem rawRowCheck2000 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form5 = rawRow2000 := by decide +kernel

def row2000 : Integer.Sparse Key := [(key1527, 2), (key1532, -2), (key1605, -2), (key1638, 2), (key1649, 2), (key1672, -2)]

theorem rowCheck2000 : row2000 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2000 := by decide +kernel

theorem rowEval2000 (x : Key → ℝ) : Integer.Sparse.eval row2000 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2000, Integer.Sparse.eval_collectBalanced, rawRowCheck2000]

def rawRow2001 : Integer.Sparse Key := [(key1672, -1), (key1649, -1), (key1672, -1), (key1266, -1), (key1649, -1), (key1266, -1), (key1649, 2), (key1649, 2), (key1266, 2), (key1638, 1), (key1610, 1), (key1638, 1), (key1257, 1), (key1610, 1), (key1257, 1), (key1610, -1), (key1532, -1), (key1610, -1), (key1257, -1), (key1532, -1), (key1257, -1), (key1605, -2), (key1605, -2), (key1252, -2), (key1605, 1), (key1527, 1), (key1605, 1), (key1252, 1), (key1527, 1), (key1252, 1)]

theorem rawRowCheck2001 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form5 = rawRow2001 := by decide +kernel

def row2001 : Integer.Sparse Key := [(key1527, 2), (key1532, -2), (key1605, -2), (key1638, 2), (key1649, 2), (key1672, -2)]

theorem rowCheck2001 : row2001 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2001 := by decide +kernel

theorem rowEval2001 (x : Key → ℝ) : Integer.Sparse.eval row2001 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form5) x := by
  rw [rowCheck2001, Integer.Sparse.eval_collectBalanced, rawRowCheck2001]

def rawRow2002 : Integer.Sparse Key := [(key3034, -2), (key3041, -2), (key3041, -2), (key3037, 2), (key3041, 2), (key3041, 2), (key3121, 2), (key3133, 2), (key3133, 2), (key3133, -6), (key3129, -2), (key3139, -2), (key3139, -2), (key3139, 6)]

theorem rawRowCheck2002 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form6 = rawRow2002 := by decide +kernel

def row2002 : Integer.Sparse Key := [(key3034, -2), (key3037, 2), (key3121, 2), (key3129, -2), (key3133, -2), (key3139, 2)]

theorem rowCheck2002 : row2002 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2002 := by decide +kernel

theorem rowEval2002 (x : Key → ℝ) : Integer.Sparse.eval row2002 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2002, Integer.Sparse.eval_collectBalanced, rawRowCheck2002]

def rawRow2003 : Integer.Sparse Key := [(key3041, -2), (key3034, -2), (key3041, -2), (key3041, 2), (key3037, 2), (key3041, 2), (key3133, 2), (key3121, 2), (key3133, 2), (key3133, -6), (key3139, -2), (key3129, -2), (key3139, -2), (key3139, 6)]

theorem rawRowCheck2003 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form6 = rawRow2003 := by decide +kernel

def row2003 : Integer.Sparse Key := [(key3034, -2), (key3037, 2), (key3121, 2), (key3129, -2), (key3133, -2), (key3139, 2)]

theorem rowCheck2003 : row2003 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2003 := by decide +kernel

theorem rowEval2003 (x : Key → ℝ) : Integer.Sparse.eval row2003 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2003, Integer.Sparse.eval_collectBalanced, rawRowCheck2003]

def rawRow2004 : Integer.Sparse Key := [(key3041, -2), (key3041, -2), (key3034, -2), (key3041, 2), (key3041, 2), (key3037, 2), (key3133, 2), (key3133, 2), (key3121, 2), (key3133, -6), (key3139, -2), (key3139, -2), (key3129, -2), (key3139, 6)]

theorem rawRowCheck2004 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form6 = rawRow2004 := by decide +kernel

def row2004 : Integer.Sparse Key := [(key3034, -2), (key3037, 2), (key3121, 2), (key3129, -2), (key3133, -2), (key3139, 2)]

theorem rowCheck2004 : row2004 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2004 := by decide +kernel

theorem rowEval2004 (x : Key → ℝ) : Integer.Sparse.eval row2004 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2004, Integer.Sparse.eval_collectBalanced, rawRowCheck2004]

def rawRow2005 : Integer.Sparse Key := [(key3037, -2), (key3037, -2), (key3037, -2), (key3034, 2), (key3034, 2), (key3034, 2), (key3133, 2), (key3133, 2), (key3133, 2), (key3121, -6), (key3139, -2), (key3139, -2), (key3139, -2), (key3129, 6)]

theorem rawRowCheck2005 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form6 = rawRow2005 := by decide +kernel

def row2005 : Integer.Sparse Key := [(key3034, 6), (key3037, -6), (key3121, -6), (key3129, 6), (key3133, 6), (key3139, -6)]

theorem rowCheck2005 : row2005 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2005 := by decide +kernel

theorem rowEval2005 (x : Key → ℝ) : Integer.Sparse.eval row2005 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2005, Integer.Sparse.eval_collectBalanced, rawRowCheck2005]

def rawRow2006 : Integer.Sparse Key := [(key3121, -2), (key3133, -2), (key3133, -2), (key3129, 2), (key3139, 2), (key3139, 2), (key3034, 2), (key3041, 2), (key3041, 2), (key3139, -6), (key3037, -2), (key3041, -2), (key3041, -2), (key3133, 6)]

theorem rawRowCheck2006 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form6 = rawRow2006 := by decide +kernel

def row2006 : Integer.Sparse Key := [(key3034, 2), (key3037, -2), (key3121, -2), (key3129, 2), (key3133, 2), (key3139, -2)]

theorem rowCheck2006 : row2006 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2006 := by decide +kernel

theorem rowEval2006 (x : Key → ℝ) : Integer.Sparse.eval row2006 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2006, Integer.Sparse.eval_collectBalanced, rawRowCheck2006]

def rawRow2007 : Integer.Sparse Key := [(key3133, -2), (key3121, -2), (key3133, -2), (key3139, 2), (key3129, 2), (key3139, 2), (key3041, 2), (key3034, 2), (key3041, 2), (key3139, -6), (key3041, -2), (key3037, -2), (key3041, -2), (key3133, 6)]

theorem rawRowCheck2007 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form6 = rawRow2007 := by decide +kernel

def row2007 : Integer.Sparse Key := [(key3034, 2), (key3037, -2), (key3121, -2), (key3129, 2), (key3133, 2), (key3139, -2)]

theorem rowCheck2007 : row2007 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2007 := by decide +kernel

theorem rowEval2007 (x : Key → ℝ) : Integer.Sparse.eval row2007 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2007, Integer.Sparse.eval_collectBalanced, rawRowCheck2007]

def rawRow2008 : Integer.Sparse Key := [(key3133, -2), (key3133, -2), (key3121, -2), (key3139, 2), (key3139, 2), (key3129, 2), (key3041, 2), (key3041, 2), (key3034, 2), (key3139, -6), (key3041, -2), (key3041, -2), (key3037, -2), (key3133, 6)]

theorem rawRowCheck2008 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form6 = rawRow2008 := by decide +kernel

def row2008 : Integer.Sparse Key := [(key3034, 2), (key3037, -2), (key3121, -2), (key3129, 2), (key3133, 2), (key3139, -2)]

theorem rowCheck2008 : row2008 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2008 := by decide +kernel

theorem rowEval2008 (x : Key → ℝ) : Integer.Sparse.eval row2008 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2008, Integer.Sparse.eval_collectBalanced, rawRowCheck2008]

def rawRow2009 : Integer.Sparse Key := [(key3037, -2), (key3037, -2), (key3129, -2), (key3034, 2), (key3034, 2), (key3121, 2), (key3041, 2), (key3041, 2), (key3139, 2), (key3034, -6), (key3041, -2), (key3041, -2), (key3133, -2), (key3037, 6)]

theorem rawRowCheck2009 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form6 = rawRow2009 := by decide +kernel

def row2009 : Integer.Sparse Key := [(key3034, -2), (key3037, 2), (key3121, 2), (key3129, -2), (key3133, -2), (key3139, 2)]

theorem rowCheck2009 : row2009 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2009 := by decide +kernel

theorem rowEval2009 (x : Key → ℝ) : Integer.Sparse.eval row2009 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2009, Integer.Sparse.eval_collectBalanced, rawRowCheck2009]

def rawRow2010 : Integer.Sparse Key := [(key3037, -2), (key3129, -2), (key3037, -2), (key3034, 2), (key3121, 2), (key3034, 2), (key3041, 2), (key3139, 2), (key3041, 2), (key3034, -6), (key3041, -2), (key3133, -2), (key3041, -2), (key3037, 6)]

theorem rawRowCheck2010 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form6 = rawRow2010 := by decide +kernel

def row2010 : Integer.Sparse Key := [(key3034, -2), (key3037, 2), (key3121, 2), (key3129, -2), (key3133, -2), (key3139, 2)]

theorem rowCheck2010 : row2010 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2010 := by decide +kernel

theorem rowEval2010 (x : Key → ℝ) : Integer.Sparse.eval row2010 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2010, Integer.Sparse.eval_collectBalanced, rawRowCheck2010]

def rawRow2011 : Integer.Sparse Key := [(key3129, -2), (key3037, -2), (key3037, -2), (key3121, 2), (key3034, 2), (key3034, 2), (key3139, 2), (key3041, 2), (key3041, 2), (key3034, -6), (key3133, -2), (key3041, -2), (key3041, -2), (key3037, 6)]

theorem rawRowCheck2011 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form6 = rawRow2011 := by decide +kernel

def row2011 : Integer.Sparse Key := [(key3034, -2), (key3037, 2), (key3121, 2), (key3129, -2), (key3133, -2), (key3139, 2)]

theorem rowCheck2011 : row2011 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2011 := by decide +kernel

theorem rowEval2011 (x : Key → ℝ) : Integer.Sparse.eval row2011 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form6) x := by
  rw [rowCheck2011, Integer.Sparse.eval_collectBalanced, rawRowCheck2011]

def rawRow2012 : Integer.Sparse Key := [(key3133, -2), (key3133, -2), (key3133, -2), (key3139, 2), (key3139, 2), (key3139, 2), (key3037, 2), (key3037, 2), (key3037, 2), (key3129, -6), (key3034, -2), (key3034, -2), (key3034, -2), (key3121, 6)]

theorem rawRowCheck2012 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form6 = rawRow2012 := by decide +kernel

def row2012 : Integer.Sparse Key := [(key3034, -6), (key3037, 6), (key3121, 6), (key3129, -6), (key3133, -6), (key3139, 6)]

theorem rowCheck2012 : row2012 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2012 := by decide +kernel

theorem rowEval2012 (x : Key → ℝ) : Integer.Sparse.eval row2012 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2012, Integer.Sparse.eval_collectBalanced, rawRowCheck2012]

def rawRow2013 : Integer.Sparse Key := [(key3041, -2), (key3041, -2), (key3139, -2), (key3041, 2), (key3041, 2), (key3133, 2), (key3037, 2), (key3037, 2), (key3129, 2), (key3037, -6), (key3034, -2), (key3034, -2), (key3121, -2), (key3034, 6)]

theorem rawRowCheck2013 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form6 = rawRow2013 := by decide +kernel

def row2013 : Integer.Sparse Key := [(key3034, 2), (key3037, -2), (key3121, -2), (key3129, 2), (key3133, 2), (key3139, -2)]

theorem rowCheck2013 : row2013 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2013 := by decide +kernel

theorem rowEval2013 (x : Key → ℝ) : Integer.Sparse.eval row2013 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2013, Integer.Sparse.eval_collectBalanced, rawRowCheck2013]

def rawRow2014 : Integer.Sparse Key := [(key3041, -2), (key3139, -2), (key3041, -2), (key3041, 2), (key3133, 2), (key3041, 2), (key3037, 2), (key3129, 2), (key3037, 2), (key3037, -6), (key3034, -2), (key3121, -2), (key3034, -2), (key3034, 6)]

theorem rawRowCheck2014 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form6 = rawRow2014 := by decide +kernel

def row2014 : Integer.Sparse Key := [(key3034, 2), (key3037, -2), (key3121, -2), (key3129, 2), (key3133, 2), (key3139, -2)]

theorem rowCheck2014 : row2014 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2014 := by decide +kernel

theorem rowEval2014 (x : Key → ℝ) : Integer.Sparse.eval row2014 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2014, Integer.Sparse.eval_collectBalanced, rawRowCheck2014]

def rawRow2015 : Integer.Sparse Key := [(key3139, -2), (key3041, -2), (key3041, -2), (key3133, 2), (key3041, 2), (key3041, 2), (key3129, 2), (key3037, 2), (key3037, 2), (key3037, -6), (key3121, -2), (key3034, -2), (key3034, -2), (key3034, 6)]

theorem rawRowCheck2015 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form6 = rawRow2015 := by decide +kernel

def row2015 : Integer.Sparse Key := [(key3034, 2), (key3037, -2), (key3121, -2), (key3129, 2), (key3133, 2), (key3139, -2)]

theorem rowCheck2015 : row2015 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2015 := by decide +kernel

theorem rowEval2015 (x : Key → ℝ) : Integer.Sparse.eval row2015 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form6) x := by
  rw [rowCheck2015, Integer.Sparse.eval_collectBalanced, rawRowCheck2015]

def rawRow2016 : Integer.Sparse Key := [(key1252, -2), (key1257, -2), (key1257, -2), (key1252, 1), (key1257, 1), (key1252, 1), (key1266, 1), (key1257, 1), (key1266, 1), (key1527, 2), (key1532, 2), (key1532, 2), (key1527, -1), (key1532, -1), (key1527, -1), (key1766, -1), (key1532, -1), (key1766, -1), (key1605, -1), (key1610, -1), (key1605, -1), (key1649, -1), (key1610, -1), (key1649, -1), (key1605, 1), (key1610, 1), (key1605, 1), (key1807, 1), (key1610, 1), (key1807, 1)]

theorem rawRowCheck2016 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form7 = rawRow2016 := by decide +kernel

def row2016 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1532, 2), (key1649, -2), (key1766, -2), (key1807, 2)]

theorem rowCheck2016 : row2016 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2016 := by decide +kernel

theorem rowEval2016 (x : Key → ℝ) : Integer.Sparse.eval row2016 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck2016, Integer.Sparse.eval_collectBalanced, rawRowCheck2016]

def rawRow2017 : Integer.Sparse Key := [(key1257, -2), (key1252, -2), (key1257, -2), (key1257, 1), (key1252, 1), (key1266, 1), (key1252, 1), (key1266, 1), (key1257, 1), (key1532, 2), (key1527, 2), (key1532, 2), (key1532, -1), (key1527, -1), (key1766, -1), (key1527, -1), (key1766, -1), (key1532, -1), (key1610, -1), (key1605, -1), (key1649, -1), (key1605, -1), (key1649, -1), (key1610, -1), (key1610, 1), (key1605, 1), (key1807, 1), (key1605, 1), (key1807, 1), (key1610, 1)]

theorem rawRowCheck2017 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form7 = rawRow2017 := by decide +kernel

def row2017 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1532, 2), (key1649, -2), (key1766, -2), (key1807, 2)]

theorem rowCheck2017 : row2017 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2017 := by decide +kernel

theorem rowEval2017 (x : Key → ℝ) : Integer.Sparse.eval row2017 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2017, Integer.Sparse.eval_collectBalanced, rawRowCheck2017]

def rawRow2018 : Integer.Sparse Key := [(key1257, -2), (key1257, -2), (key1252, -2), (key1266, 1), (key1266, 1), (key1257, 1), (key1257, 1), (key1252, 1), (key1252, 1), (key1532, 2), (key1532, 2), (key1527, 2), (key1766, -1), (key1766, -1), (key1532, -1), (key1532, -1), (key1527, -1), (key1527, -1), (key1649, -1), (key1649, -1), (key1610, -1), (key1610, -1), (key1605, -1), (key1605, -1), (key1807, 1), (key1807, 1), (key1610, 1), (key1610, 1), (key1605, 1), (key1605, 1)]

theorem rawRowCheck2018 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form7 = rawRow2018 := by decide +kernel

def row2018 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1532, 2), (key1649, -2), (key1766, -2), (key1807, 2)]

theorem rowCheck2018 : row2018 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2018 := by decide +kernel

theorem rowEval2018 (x : Key → ℝ) : Integer.Sparse.eval row2018 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2018, Integer.Sparse.eval_collectBalanced, rawRowCheck2018]

def rawRow2019 : Integer.Sparse Key := [(key1266, -2), (key1266, -2), (key1266, -2), (key1257, 1), (key1257, 1), (key1257, 1), (key1257, 1), (key1257, 1), (key1257, 1), (key1766, 2), (key1766, 2), (key1766, 2), (key1532, -1), (key1532, -1), (key1532, -1), (key1532, -1), (key1532, -1), (key1532, -1), (key1807, -1), (key1807, -1), (key1807, -1), (key1807, -1), (key1807, -1), (key1807, -1), (key1649, 1), (key1649, 1), (key1649, 1), (key1649, 1), (key1649, 1), (key1649, 1)]

theorem rawRowCheck2019 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form7 = rawRow2019 := by decide +kernel

def row2019 : Integer.Sparse Key := [(key1257, 6), (key1266, -6), (key1532, -6), (key1649, 6), (key1766, 6), (key1807, -6)]

theorem rowCheck2019 : row2019 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2019 := by decide +kernel

theorem rowEval2019 (x : Key → ℝ) : Integer.Sparse.eval row2019 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2019, Integer.Sparse.eval_collectBalanced, rawRowCheck2019]

def rawRow2020 : Integer.Sparse Key := [(key1527, -2), (key1532, -2), (key1532, -2), (key1605, 1), (key1610, 1), (key1605, 1), (key1649, 1), (key1610, 1), (key1649, 1), (key1252, 2), (key1257, 2), (key1257, 2), (key1605, -1), (key1610, -1), (key1605, -1), (key1807, -1), (key1610, -1), (key1807, -1), (key1252, -1), (key1257, -1), (key1252, -1), (key1266, -1), (key1257, -1), (key1266, -1), (key1527, 1), (key1532, 1), (key1527, 1), (key1766, 1), (key1532, 1), (key1766, 1)]

theorem rawRowCheck2020 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form7 = rawRow2020 := by decide +kernel

def row2020 : Integer.Sparse Key := [(key1257, 2), (key1266, -2), (key1532, -2), (key1649, 2), (key1766, 2), (key1807, -2)]

theorem rowCheck2020 : row2020 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2020 := by decide +kernel

theorem rowEval2020 (x : Key → ℝ) : Integer.Sparse.eval row2020 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck2020, Integer.Sparse.eval_collectBalanced, rawRowCheck2020]

def rawRow2021 : Integer.Sparse Key := [(key1532, -2), (key1527, -2), (key1532, -2), (key1610, 1), (key1605, 1), (key1649, 1), (key1605, 1), (key1649, 1), (key1610, 1), (key1257, 2), (key1252, 2), (key1257, 2), (key1610, -1), (key1605, -1), (key1807, -1), (key1605, -1), (key1807, -1), (key1610, -1), (key1257, -1), (key1252, -1), (key1266, -1), (key1252, -1), (key1266, -1), (key1257, -1), (key1532, 1), (key1527, 1), (key1766, 1), (key1527, 1), (key1766, 1), (key1532, 1)]

theorem rawRowCheck2021 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form7 = rawRow2021 := by decide +kernel

def row2021 : Integer.Sparse Key := [(key1257, 2), (key1266, -2), (key1532, -2), (key1649, 2), (key1766, 2), (key1807, -2)]

theorem rowCheck2021 : row2021 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2021 := by decide +kernel

theorem rowEval2021 (x : Key → ℝ) : Integer.Sparse.eval row2021 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2021, Integer.Sparse.eval_collectBalanced, rawRowCheck2021]

def rawRow2022 : Integer.Sparse Key := [(key1532, -2), (key1532, -2), (key1527, -2), (key1649, 1), (key1649, 1), (key1610, 1), (key1610, 1), (key1605, 1), (key1605, 1), (key1257, 2), (key1257, 2), (key1252, 2), (key1807, -1), (key1807, -1), (key1610, -1), (key1610, -1), (key1605, -1), (key1605, -1), (key1266, -1), (key1266, -1), (key1257, -1), (key1257, -1), (key1252, -1), (key1252, -1), (key1766, 1), (key1766, 1), (key1532, 1), (key1532, 1), (key1527, 1), (key1527, 1)]

theorem rawRowCheck2022 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form7 = rawRow2022 := by decide +kernel

def row2022 : Integer.Sparse Key := [(key1257, 2), (key1266, -2), (key1532, -2), (key1649, 2), (key1766, 2), (key1807, -2)]

theorem rowCheck2022 : row2022 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2022 := by decide +kernel

theorem rowEval2022 (x : Key → ℝ) : Integer.Sparse.eval row2022 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2022, Integer.Sparse.eval_collectBalanced, rawRowCheck2022]

def rawRow2023 : Integer.Sparse Key := [(key1649, -2), (key1649, -2), (key1672, -2), (key1532, 1), (key1532, 1), (key1610, 1), (key1610, 1), (key1638, 1), (key1638, 1), (key1807, 2), (key1807, 2), (key1830, 2), (key1257, -1), (key1257, -1), (key1610, -1), (key1610, -1), (key1638, -1), (key1638, -1), (key1766, -1), (key1766, -1), (key1807, -1), (key1807, -1), (key1830, -1), (key1830, -1), (key1266, 1), (key1266, 1), (key1649, 1), (key1649, 1), (key1672, 1), (key1672, 1)]

theorem rawRowCheck2023 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form7 = rawRow2023 := by decide +kernel

def row2023 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1532, 2), (key1649, -2), (key1766, -2), (key1807, 2)]

theorem rowCheck2023 : row2023 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2023 := by decide +kernel

theorem rowEval2023 (x : Key → ℝ) : Integer.Sparse.eval row2023 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2023, Integer.Sparse.eval_collectBalanced, rawRowCheck2023]

def rawRow2024 : Integer.Sparse Key := [(key1649, -2), (key1672, -2), (key1649, -2), (key1610, 1), (key1638, 1), (key1532, 1), (key1638, 1), (key1532, 1), (key1610, 1), (key1807, 2), (key1830, 2), (key1807, 2), (key1610, -1), (key1638, -1), (key1257, -1), (key1638, -1), (key1257, -1), (key1610, -1), (key1807, -1), (key1830, -1), (key1766, -1), (key1830, -1), (key1766, -1), (key1807, -1), (key1649, 1), (key1672, 1), (key1266, 1), (key1672, 1), (key1266, 1), (key1649, 1)]

theorem rawRowCheck2024 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form7 = rawRow2024 := by decide +kernel

def row2024 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1532, 2), (key1649, -2), (key1766, -2), (key1807, 2)]

theorem rowCheck2024 : row2024 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2024 := by decide +kernel

theorem rowEval2024 (x : Key → ℝ) : Integer.Sparse.eval row2024 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2024, Integer.Sparse.eval_collectBalanced, rawRowCheck2024]

def rawRow2025 : Integer.Sparse Key := [(key1672, -2), (key1649, -2), (key1649, -2), (key1638, 1), (key1610, 1), (key1638, 1), (key1532, 1), (key1610, 1), (key1532, 1), (key1830, 2), (key1807, 2), (key1807, 2), (key1638, -1), (key1610, -1), (key1638, -1), (key1257, -1), (key1610, -1), (key1257, -1), (key1830, -1), (key1807, -1), (key1830, -1), (key1766, -1), (key1807, -1), (key1766, -1), (key1672, 1), (key1649, 1), (key1672, 1), (key1266, 1), (key1649, 1), (key1266, 1)]

theorem rawRowCheck2025 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form7 = rawRow2025 := by decide +kernel

def row2025 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1532, 2), (key1649, -2), (key1766, -2), (key1807, 2)]

theorem rowCheck2025 : row2025 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2025 := by decide +kernel

theorem rowEval2025 (x : Key → ℝ) : Integer.Sparse.eval row2025 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form7) x := by
  rw [rowCheck2025, Integer.Sparse.eval_collectBalanced, rawRowCheck2025]

def rawRow2026 : Integer.Sparse Key := [(key1766, -2), (key1766, -2), (key1766, -2), (key1807, 1), (key1807, 1), (key1807, 1), (key1807, 1), (key1807, 1), (key1807, 1), (key1266, 2), (key1266, 2), (key1266, 2), (key1649, -1), (key1649, -1), (key1649, -1), (key1649, -1), (key1649, -1), (key1649, -1), (key1257, -1), (key1257, -1), (key1257, -1), (key1257, -1), (key1257, -1), (key1257, -1), (key1532, 1), (key1532, 1), (key1532, 1), (key1532, 1), (key1532, 1), (key1532, 1)]

theorem rawRowCheck2026 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form7 = rawRow2026 := by decide +kernel

def row2026 : Integer.Sparse Key := [(key1257, -6), (key1266, 6), (key1532, 6), (key1649, -6), (key1766, -6), (key1807, 6)]

theorem rowCheck2026 : row2026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2026 := by decide +kernel

theorem rowEval2026 (x : Key → ℝ) : Integer.Sparse.eval row2026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2026, Integer.Sparse.eval_collectBalanced, rawRowCheck2026]

def rawRow2027 : Integer.Sparse Key := [(key1807, -2), (key1807, -2), (key1830, -2), (key1766, 1), (key1766, 1), (key1807, 1), (key1807, 1), (key1830, 1), (key1830, 1), (key1649, 2), (key1649, 2), (key1672, 2), (key1266, -1), (key1266, -1), (key1649, -1), (key1649, -1), (key1672, -1), (key1672, -1), (key1532, -1), (key1532, -1), (key1610, -1), (key1610, -1), (key1638, -1), (key1638, -1), (key1257, 1), (key1257, 1), (key1610, 1), (key1610, 1), (key1638, 1), (key1638, 1)]

theorem rawRowCheck2027 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form7 = rawRow2027 := by decide +kernel

def row2027 : Integer.Sparse Key := [(key1257, 2), (key1266, -2), (key1532, -2), (key1649, 2), (key1766, 2), (key1807, -2)]

theorem rowCheck2027 : row2027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2027 := by decide +kernel

theorem rowEval2027 (x : Key → ℝ) : Integer.Sparse.eval row2027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2027, Integer.Sparse.eval_collectBalanced, rawRowCheck2027]

def rawRow2028 : Integer.Sparse Key := [(key1807, -2), (key1830, -2), (key1807, -2), (key1807, 1), (key1830, 1), (key1766, 1), (key1830, 1), (key1766, 1), (key1807, 1), (key1649, 2), (key1672, 2), (key1649, 2), (key1649, -1), (key1672, -1), (key1266, -1), (key1672, -1), (key1266, -1), (key1649, -1), (key1610, -1), (key1638, -1), (key1532, -1), (key1638, -1), (key1532, -1), (key1610, -1), (key1610, 1), (key1638, 1), (key1257, 1), (key1638, 1), (key1257, 1), (key1610, 1)]

theorem rawRowCheck2028 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form7 = rawRow2028 := by decide +kernel

def row2028 : Integer.Sparse Key := [(key1257, 2), (key1266, -2), (key1532, -2), (key1649, 2), (key1766, 2), (key1807, -2)]

theorem rowCheck2028 : row2028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2028 := by decide +kernel

theorem rowEval2028 (x : Key → ℝ) : Integer.Sparse.eval row2028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2028, Integer.Sparse.eval_collectBalanced, rawRowCheck2028]

def rawRow2029 : Integer.Sparse Key := [(key1830, -2), (key1807, -2), (key1807, -2), (key1830, 1), (key1807, 1), (key1830, 1), (key1766, 1), (key1807, 1), (key1766, 1), (key1672, 2), (key1649, 2), (key1649, 2), (key1672, -1), (key1649, -1), (key1672, -1), (key1266, -1), (key1649, -1), (key1266, -1), (key1638, -1), (key1610, -1), (key1638, -1), (key1532, -1), (key1610, -1), (key1532, -1), (key1638, 1), (key1610, 1), (key1638, 1), (key1257, 1), (key1610, 1), (key1257, 1)]

theorem rawRowCheck2029 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form7 = rawRow2029 := by decide +kernel

def row2029 : Integer.Sparse Key := [(key1257, 2), (key1266, -2), (key1532, -2), (key1649, 2), (key1766, 2), (key1807, -2)]

theorem rowCheck2029 : row2029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2029 := by decide +kernel

theorem rowEval2029 (x : Key → ℝ) : Integer.Sparse.eval row2029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form7) x := by
  rw [rowCheck2029, Integer.Sparse.eval_collectBalanced, rawRowCheck2029]

def rawRow2030 : Integer.Sparse Key := [(key971, -2), (key975, -2), (key975, -2), (key975, 6), (key1085, 2), (key1089, 2), (key1089, 2), (key1089, -2), (key1089, -2), (key1179, -2), (key1161, -6), (key1161, 2), (key1161, 2), (key1217, 2)]

theorem rawRowCheck2030 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form8 = rawRow2030 := by decide +kernel

def row2030 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1161, -2), (key1179, -2), (key1217, 2)]

theorem rowCheck2030 : row2030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2030 := by decide +kernel

theorem rowEval2030 (x : Key → ℝ) : Integer.Sparse.eval row2030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2030, Integer.Sparse.eval_collectBalanced, rawRowCheck2030]

def rawRow2031 : Integer.Sparse Key := [(key975, -2), (key971, -2), (key975, -2), (key975, 6), (key1089, 2), (key1085, 2), (key1089, 2), (key1089, -2), (key1179, -2), (key1089, -2), (key1161, -6), (key1161, 2), (key1217, 2), (key1161, 2)]

theorem rawRowCheck2031 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form8 = rawRow2031 := by decide +kernel

def row2031 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1161, -2), (key1179, -2), (key1217, 2)]

theorem rowCheck2031 : row2031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2031 := by decide +kernel

theorem rowEval2031 (x : Key → ℝ) : Integer.Sparse.eval row2031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2031, Integer.Sparse.eval_collectBalanced, rawRowCheck2031]

def rawRow2032 : Integer.Sparse Key := [(key975, -2), (key975, -2), (key971, -2), (key975, 6), (key1089, 2), (key1089, 2), (key1085, 2), (key1179, -2), (key1089, -2), (key1089, -2), (key1161, -6), (key1217, 2), (key1161, 2), (key1161, 2)]

theorem rawRowCheck2032 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form8 = rawRow2032 := by decide +kernel

def row2032 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1161, -2), (key1179, -2), (key1217, 2)]

theorem rowCheck2032 : row2032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2032 := by decide +kernel

theorem rowEval2032 (x : Key → ℝ) : Integer.Sparse.eval row2032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2032, Integer.Sparse.eval_collectBalanced, rawRowCheck2032]

def rawRow2033 : Integer.Sparse Key := [(key975, -2), (key975, -2), (key975, -2), (key971, 6), (key1179, 2), (key1179, 2), (key1179, 2), (key1085, -2), (key1085, -2), (key1085, -2), (key1217, -6), (key1161, 2), (key1161, 2), (key1161, 2)]

theorem rawRowCheck2033 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form8 = rawRow2033 := by decide +kernel

def row2033 : Integer.Sparse Key := [(key971, 6), (key975, -6), (key1085, -6), (key1161, 6), (key1179, 6), (key1217, -6)]

theorem rowCheck2033 : row2033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2033 := by decide +kernel

theorem rowEval2033 (x : Key → ℝ) : Integer.Sparse.eval row2033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2033, Integer.Sparse.eval_collectBalanced, rawRowCheck2033]

def rawRow2034 : Integer.Sparse Key := [(key1085, -2), (key1089, -2), (key1089, -2), (key1161, 6), (key971, 2), (key975, 2), (key975, 2), (key1161, -2), (key1161, -2), (key1217, -2), (key975, -6), (key1089, 2), (key1089, 2), (key1179, 2)]

theorem rawRowCheck2034 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form8 = rawRow2034 := by decide +kernel

def row2034 : Integer.Sparse Key := [(key971, 2), (key975, -2), (key1085, -2), (key1161, 2), (key1179, 2), (key1217, -2)]

theorem rowCheck2034 : row2034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2034 := by decide +kernel

theorem rowEval2034 (x : Key → ℝ) : Integer.Sparse.eval row2034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2034, Integer.Sparse.eval_collectBalanced, rawRowCheck2034]

def rawRow2035 : Integer.Sparse Key := [(key1089, -2), (key1085, -2), (key1089, -2), (key1161, 6), (key975, 2), (key971, 2), (key975, 2), (key1161, -2), (key1217, -2), (key1161, -2), (key975, -6), (key1089, 2), (key1179, 2), (key1089, 2)]

theorem rawRowCheck2035 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form8 = rawRow2035 := by decide +kernel

def row2035 : Integer.Sparse Key := [(key971, 2), (key975, -2), (key1085, -2), (key1161, 2), (key1179, 2), (key1217, -2)]

theorem rowCheck2035 : row2035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2035 := by decide +kernel

theorem rowEval2035 (x : Key → ℝ) : Integer.Sparse.eval row2035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2035, Integer.Sparse.eval_collectBalanced, rawRowCheck2035]

def rawRow2036 : Integer.Sparse Key := [(key1089, -2), (key1089, -2), (key1085, -2), (key1161, 6), (key975, 2), (key975, 2), (key971, 2), (key1217, -2), (key1161, -2), (key1161, -2), (key975, -6), (key1179, 2), (key1089, 2), (key1089, 2)]

theorem rawRowCheck2036 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form8 = rawRow2036 := by decide +kernel

def row2036 : Integer.Sparse Key := [(key971, 2), (key975, -2), (key1085, -2), (key1161, 2), (key1179, 2), (key1217, -2)]

theorem rowCheck2036 : row2036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2036 := by decide +kernel

theorem rowEval2036 (x : Key → ℝ) : Integer.Sparse.eval row2036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2036, Integer.Sparse.eval_collectBalanced, rawRowCheck2036]

def rawRow2037 : Integer.Sparse Key := [(key1089, -2), (key1089, -2), (key1161, -2), (key1085, 6), (key1179, 2), (key1179, 2), (key1217, 2), (key971, -2), (key1085, -2), (key1085, -2), (key1179, -6), (key975, 2), (key1089, 2), (key1089, 2)]

theorem rawRowCheck2037 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form8 = rawRow2037 := by decide +kernel

def row2037 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1161, -2), (key1179, -2), (key1217, 2)]

theorem rowCheck2037 : row2037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2037 := by decide +kernel

theorem rowEval2037 (x : Key → ℝ) : Integer.Sparse.eval row2037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2037, Integer.Sparse.eval_collectBalanced, rawRowCheck2037]

def rawRow2038 : Integer.Sparse Key := [(key1089, -2), (key1161, -2), (key1089, -2), (key1085, 6), (key1179, 2), (key1217, 2), (key1179, 2), (key1085, -2), (key971, -2), (key1085, -2), (key1179, -6), (key1089, 2), (key975, 2), (key1089, 2)]

theorem rawRowCheck2038 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form8 = rawRow2038 := by decide +kernel

def row2038 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1161, -2), (key1179, -2), (key1217, 2)]

theorem rowCheck2038 : row2038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2038 := by decide +kernel

theorem rowEval2038 (x : Key → ℝ) : Integer.Sparse.eval row2038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2038, Integer.Sparse.eval_collectBalanced, rawRowCheck2038]

def rawRow2039 : Integer.Sparse Key := [(key1161, -2), (key1089, -2), (key1089, -2), (key1085, 6), (key1217, 2), (key1179, 2), (key1179, 2), (key1085, -2), (key1085, -2), (key971, -2), (key1179, -6), (key1089, 2), (key1089, 2), (key975, 2)]

theorem rawRowCheck2039 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form8 = rawRow2039 := by decide +kernel

def row2039 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1161, -2), (key1179, -2), (key1217, 2)]

theorem rowCheck2039 : row2039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2039 := by decide +kernel

theorem rowEval2039 (x : Key → ℝ) : Integer.Sparse.eval row2039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form8) x := by
  rw [rowCheck2039, Integer.Sparse.eval_collectBalanced, rawRowCheck2039]

def rawRow2040 : Integer.Sparse Key := [(key1179, -2), (key1179, -2), (key1179, -2), (key1217, 6), (key975, 2), (key975, 2), (key975, 2), (key1161, -2), (key1161, -2), (key1161, -2), (key971, -6), (key1085, 2), (key1085, 2), (key1085, 2)]

theorem rawRowCheck2040 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form8 = rawRow2040 := by decide +kernel

def row2040 : Integer.Sparse Key := [(key971, -6), (key975, 6), (key1085, 6), (key1161, -6), (key1179, -6), (key1217, 6)]

theorem rowCheck2040 : row2040 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2040 := by decide +kernel

theorem rowEval2040 (x : Key → ℝ) : Integer.Sparse.eval row2040 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2040, Integer.Sparse.eval_collectBalanced, rawRowCheck2040]

def rawRow2041 : Integer.Sparse Key := [(key1179, -2), (key1179, -2), (key1217, -2), (key1179, 6), (key1089, 2), (key1089, 2), (key1161, 2), (key975, -2), (key1089, -2), (key1089, -2), (key1085, -6), (key971, 2), (key1085, 2), (key1085, 2)]

theorem rawRowCheck2041 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form8 = rawRow2041 := by decide +kernel

def row2041 : Integer.Sparse Key := [(key971, 2), (key975, -2), (key1085, -2), (key1161, 2), (key1179, 2), (key1217, -2)]

theorem rowCheck2041 : row2041 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2041 := by decide +kernel

theorem rowEval2041 (x : Key → ℝ) : Integer.Sparse.eval row2041 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2041, Integer.Sparse.eval_collectBalanced, rawRowCheck2041]

def rawRow2042 : Integer.Sparse Key := [(key1179, -2), (key1217, -2), (key1179, -2), (key1179, 6), (key1089, 2), (key1161, 2), (key1089, 2), (key1089, -2), (key975, -2), (key1089, -2), (key1085, -6), (key1085, 2), (key971, 2), (key1085, 2)]

theorem rawRowCheck2042 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form8 = rawRow2042 := by decide +kernel

def row2042 : Integer.Sparse Key := [(key971, 2), (key975, -2), (key1085, -2), (key1161, 2), (key1179, 2), (key1217, -2)]

theorem rowCheck2042 : row2042 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2042 := by decide +kernel

theorem rowEval2042 (x : Key → ℝ) : Integer.Sparse.eval row2042 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2042, Integer.Sparse.eval_collectBalanced, rawRowCheck2042]

def rawRow2043 : Integer.Sparse Key := [(key1217, -2), (key1179, -2), (key1179, -2), (key1179, 6), (key1161, 2), (key1089, 2), (key1089, 2), (key1089, -2), (key1089, -2), (key975, -2), (key1085, -6), (key1085, 2), (key1085, 2), (key971, 2)]

theorem rawRowCheck2043 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form8 = rawRow2043 := by decide +kernel

def row2043 : Integer.Sparse Key := [(key971, 2), (key975, -2), (key1085, -2), (key1161, 2), (key1179, 2), (key1217, -2)]

theorem rowCheck2043 : row2043 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2043 := by decide +kernel

theorem rowEval2043 (x : Key → ℝ) : Integer.Sparse.eval row2043 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form8) x := by
  rw [rowCheck2043, Integer.Sparse.eval_collectBalanced, rawRowCheck2043]

def rawRow2044 : Integer.Sparse Key := [(key2591, -2), (key2591, -2), (key2601, -2), (key2591, 1), (key2594, 1), (key2591, 1), (key2601, 1), (key2594, 1), (key2601, 1), (key2847, 2), (key2847, 2), (key2890, 2), (key2847, -1), (key2890, -1), (key2847, -1), (key2969, -1), (key2890, -1), (key2969, -1), (key2878, -1), (key2881, -1), (key2878, -1), (key2911, -1), (key2881, -1), (key2911, -1), (key2878, 1), (key2911, 1), (key2878, 1), (key2990, 1), (key2911, 1), (key2990, 1)]

theorem rawRowCheck2044 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form9 = rawRow2044 := by decide +kernel

def row2044 : Integer.Sparse Key := [(key2591, -2), (key2594, 2), (key2847, 2), (key2881, -2), (key2969, -2), (key2990, 2)]

theorem rowCheck2044 : row2044 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2044 := by decide +kernel

theorem rowEval2044 (x : Key → ℝ) : Integer.Sparse.eval row2044 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck2044, Integer.Sparse.eval_collectBalanced, rawRowCheck2044]

def rawRow2045 : Integer.Sparse Key := [(key2591, -2), (key2601, -2), (key2591, -2), (key2594, 1), (key2591, 1), (key2601, 1), (key2591, 1), (key2601, 1), (key2594, 1), (key2847, 2), (key2890, 2), (key2847, 2), (key2890, -1), (key2847, -1), (key2969, -1), (key2847, -1), (key2969, -1), (key2890, -1), (key2881, -1), (key2878, -1), (key2911, -1), (key2878, -1), (key2911, -1), (key2881, -1), (key2911, 1), (key2878, 1), (key2990, 1), (key2878, 1), (key2990, 1), (key2911, 1)]

theorem rawRowCheck2045 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form9 = rawRow2045 := by decide +kernel

def row2045 : Integer.Sparse Key := [(key2591, -2), (key2594, 2), (key2847, 2), (key2881, -2), (key2969, -2), (key2990, 2)]

theorem rowCheck2045 : row2045 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2045 := by decide +kernel

theorem rowEval2045 (x : Key → ℝ) : Integer.Sparse.eval row2045 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2045, Integer.Sparse.eval_collectBalanced, rawRowCheck2045]

def rawRow2046 : Integer.Sparse Key := [(key2601, -2), (key2591, -2), (key2591, -2), (key2601, 1), (key2601, 1), (key2594, 1), (key2594, 1), (key2591, 1), (key2591, 1), (key2890, 2), (key2847, 2), (key2847, 2), (key2969, -1), (key2969, -1), (key2890, -1), (key2890, -1), (key2847, -1), (key2847, -1), (key2911, -1), (key2911, -1), (key2881, -1), (key2881, -1), (key2878, -1), (key2878, -1), (key2990, 1), (key2990, 1), (key2911, 1), (key2911, 1), (key2878, 1), (key2878, 1)]

theorem rawRowCheck2046 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form9 = rawRow2046 := by decide +kernel

def row2046 : Integer.Sparse Key := [(key2591, -2), (key2594, 2), (key2847, 2), (key2881, -2), (key2969, -2), (key2990, 2)]

theorem rowCheck2046 : row2046 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2046 := by decide +kernel

theorem rowEval2046 (x : Key → ℝ) : Integer.Sparse.eval row2046 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2046, Integer.Sparse.eval_collectBalanced, rawRowCheck2046]

def rawRow2047 : Integer.Sparse Key := [(key2594, -2), (key2594, -2), (key2594, -2), (key2591, 1), (key2591, 1), (key2591, 1), (key2591, 1), (key2591, 1), (key2591, 1), (key2969, 2), (key2969, 2), (key2969, 2), (key2847, -1), (key2847, -1), (key2847, -1), (key2847, -1), (key2847, -1), (key2847, -1), (key2990, -1), (key2990, -1), (key2990, -1), (key2990, -1), (key2990, -1), (key2990, -1), (key2881, 1), (key2881, 1), (key2881, 1), (key2881, 1), (key2881, 1), (key2881, 1)]

theorem rawRowCheck2047 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form9 = rawRow2047 := by decide +kernel

def row2047 : Integer.Sparse Key := [(key2591, 6), (key2594, -6), (key2847, -6), (key2881, 6), (key2969, 6), (key2990, -6)]

theorem rowCheck2047 : row2047 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2047 := by decide +kernel

theorem rowEval2047 (x : Key → ℝ) : Integer.Sparse.eval row2047 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2047, Integer.Sparse.eval_collectBalanced, rawRowCheck2047]

end MUB6.Certificate.GramRows

end OAI
