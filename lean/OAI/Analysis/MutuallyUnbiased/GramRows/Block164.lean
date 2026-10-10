import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block6
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow17920 : Integer.Sparse Key := [(key802, 4), (key807, 4), (key812, 4), (key777, -2), (key782, -2), (key802, -2), (key821, -2), (key812, -2), (key824, -2), (key802, -2), (key807, -2), (key872, -2), (key905, -2), (key877, -2), (key907, -2), (key802, 4), (key821, 4), (key907, 4)]

theorem rawRowCheck17920 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form17 = rawRow17920 := by decide +kernel

def row17920 : Integer.Sparse Key := [(key777, -2), (key782, -2), (key802, 4), (key807, 2), (key812, 2), (key821, 2), (key824, -2), (key872, -2), (key877, -2), (key905, -2), (key907, 2)]

theorem rowCheck17920 : row17920 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17920 := by decide +kernel

theorem rowEval17920 (x : Key → ℝ) : Integer.Sparse.eval row17920 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17920, Integer.Sparse.eval_collectBalanced, rawRowCheck17920]

def rawRow17921 : Integer.Sparse Key := [(key807, 4), (key802, 4), (key812, 4), (key782, -2), (key777, -2), (key821, -2), (key802, -2), (key824, -2), (key812, -2), (key807, -2), (key802, -2), (key905, -2), (key872, -2), (key907, -2), (key877, -2), (key821, 4), (key802, 4), (key907, 4)]

theorem rawRowCheck17921 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form17 = rawRow17921 := by decide +kernel

def row17921 : Integer.Sparse Key := [(key777, -2), (key782, -2), (key802, 4), (key807, 2), (key812, 2), (key821, 2), (key824, -2), (key872, -2), (key877, -2), (key905, -2), (key907, 2)]

theorem rowCheck17921 : row17921 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17921 := by decide +kernel

theorem rowEval17921 (x : Key → ℝ) : Integer.Sparse.eval row17921 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17921, Integer.Sparse.eval_collectBalanced, rawRowCheck17921]

def rawRow17922 : Integer.Sparse Key := [(key802, 4), (key812, 4), (key807, 4), (key802, -2), (key812, -2), (key777, -2), (key824, -2), (key782, -2), (key821, -2), (key872, -2), (key877, -2), (key802, -2), (key907, -2), (key807, -2), (key905, -2), (key802, 4), (key907, 4), (key821, 4)]

theorem rawRowCheck17922 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form17 = rawRow17922 := by decide +kernel

def row17922 : Integer.Sparse Key := [(key777, -2), (key782, -2), (key802, 4), (key807, 2), (key812, 2), (key821, 2), (key824, -2), (key872, -2), (key877, -2), (key905, -2), (key907, 2)]

theorem rowCheck17922 : row17922 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17922 := by decide +kernel

theorem rowEval17922 (x : Key → ℝ) : Integer.Sparse.eval row17922 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17922, Integer.Sparse.eval_collectBalanced, rawRowCheck17922]

def rawRow17923 : Integer.Sparse Key := [(key812, 4), (key802, 4), (key807, 4), (key812, -2), (key802, -2), (key824, -2), (key777, -2), (key821, -2), (key782, -2), (key877, -2), (key872, -2), (key907, -2), (key802, -2), (key905, -2), (key807, -2), (key907, 4), (key802, 4), (key821, 4)]

theorem rawRowCheck17923 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form17 = rawRow17923 := by decide +kernel

def row17923 : Integer.Sparse Key := [(key777, -2), (key782, -2), (key802, 4), (key807, 2), (key812, 2), (key821, 2), (key824, -2), (key872, -2), (key877, -2), (key905, -2), (key907, 2)]

theorem rowCheck17923 : row17923 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17923 := by decide +kernel

theorem rowEval17923 (x : Key → ℝ) : Integer.Sparse.eval row17923 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17923, Integer.Sparse.eval_collectBalanced, rawRowCheck17923]

def rawRow17924 : Integer.Sparse Key := [(key807, 4), (key812, 4), (key802, 4), (key821, -2), (key824, -2), (key782, -2), (key812, -2), (key777, -2), (key802, -2), (key905, -2), (key907, -2), (key807, -2), (key877, -2), (key802, -2), (key872, -2), (key821, 4), (key907, 4), (key802, 4)]

theorem rawRowCheck17924 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form17 = rawRow17924 := by decide +kernel

def row17924 : Integer.Sparse Key := [(key777, -2), (key782, -2), (key802, 4), (key807, 2), (key812, 2), (key821, 2), (key824, -2), (key872, -2), (key877, -2), (key905, -2), (key907, 2)]

theorem rowCheck17924 : row17924 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17924 := by decide +kernel

theorem rowEval17924 (x : Key → ℝ) : Integer.Sparse.eval row17924 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17924, Integer.Sparse.eval_collectBalanced, rawRowCheck17924]

def rawRow17925 : Integer.Sparse Key := [(key812, 4), (key807, 4), (key802, 4), (key824, -2), (key821, -2), (key812, -2), (key782, -2), (key802, -2), (key777, -2), (key907, -2), (key905, -2), (key877, -2), (key807, -2), (key872, -2), (key802, -2), (key907, 4), (key821, 4), (key802, 4)]

theorem rawRowCheck17925 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form17 = rawRow17925 := by decide +kernel

def row17925 : Integer.Sparse Key := [(key777, -2), (key782, -2), (key802, 4), (key807, 2), (key812, 2), (key821, 2), (key824, -2), (key872, -2), (key877, -2), (key905, -2), (key907, 2)]

theorem rowCheck17925 : row17925 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17925 := by decide +kernel

theorem rowEval17925 (x : Key → ℝ) : Integer.Sparse.eval row17925 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17925, Integer.Sparse.eval_collectBalanced, rawRowCheck17925]

def rawRow17926 : Integer.Sparse Key := [(key802, 4), (key807, 4), (key812, 4), (key802, -2), (key807, -2), (key872, -2), (key905, -2), (key877, -2), (key907, -2), (key777, -2), (key782, -2), (key802, -2), (key821, -2), (key812, -2), (key824, -2), (key802, 4), (key821, 4), (key907, 4)]

theorem rawRowCheck17926 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form17 = rawRow17926 := by decide +kernel

def row17926 : Integer.Sparse Key := [(key777, -2), (key782, -2), (key802, 4), (key807, 2), (key812, 2), (key821, 2), (key824, -2), (key872, -2), (key877, -2), (key905, -2), (key907, 2)]

theorem rowCheck17926 : row17926 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17926 := by decide +kernel

theorem rowEval17926 (x : Key → ℝ) : Integer.Sparse.eval row17926 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17926, Integer.Sparse.eval_collectBalanced, rawRowCheck17926]

def rawRow17927 : Integer.Sparse Key := [(key807, 4), (key802, 4), (key812, 4), (key807, -2), (key802, -2), (key905, -2), (key872, -2), (key907, -2), (key877, -2), (key782, -2), (key777, -2), (key821, -2), (key802, -2), (key824, -2), (key812, -2), (key821, 4), (key802, 4), (key907, 4)]

theorem rawRowCheck17927 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form17 = rawRow17927 := by decide +kernel

def row17927 : Integer.Sparse Key := [(key777, -2), (key782, -2), (key802, 4), (key807, 2), (key812, 2), (key821, 2), (key824, -2), (key872, -2), (key877, -2), (key905, -2), (key907, 2)]

theorem rowCheck17927 : row17927 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17927 := by decide +kernel

theorem rowEval17927 (x : Key → ℝ) : Integer.Sparse.eval row17927 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17927, Integer.Sparse.eval_collectBalanced, rawRowCheck17927]

def rawRow17928 : Integer.Sparse Key := [(key802, 4), (key812, 4), (key807, 4), (key872, -2), (key877, -2), (key802, -2), (key907, -2), (key807, -2), (key905, -2), (key802, -2), (key812, -2), (key777, -2), (key824, -2), (key782, -2), (key821, -2), (key802, 4), (key907, 4), (key821, 4)]

theorem rawRowCheck17928 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form17 = rawRow17928 := by decide +kernel

def row17928 : Integer.Sparse Key := [(key777, -2), (key782, -2), (key802, 4), (key807, 2), (key812, 2), (key821, 2), (key824, -2), (key872, -2), (key877, -2), (key905, -2), (key907, 2)]

theorem rowCheck17928 : row17928 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17928 := by decide +kernel

theorem rowEval17928 (x : Key → ℝ) : Integer.Sparse.eval row17928 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17928, Integer.Sparse.eval_collectBalanced, rawRowCheck17928]

def rawRow17929 : Integer.Sparse Key := [(key812, 4), (key802, 4), (key807, 4), (key877, -2), (key872, -2), (key907, -2), (key802, -2), (key905, -2), (key807, -2), (key812, -2), (key802, -2), (key824, -2), (key777, -2), (key821, -2), (key782, -2), (key907, 4), (key802, 4), (key821, 4)]

theorem rawRowCheck17929 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form17 = rawRow17929 := by decide +kernel

def row17929 : Integer.Sparse Key := [(key777, -2), (key782, -2), (key802, 4), (key807, 2), (key812, 2), (key821, 2), (key824, -2), (key872, -2), (key877, -2), (key905, -2), (key907, 2)]

theorem rowCheck17929 : row17929 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17929 := by decide +kernel

theorem rowEval17929 (x : Key → ℝ) : Integer.Sparse.eval row17929 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17929, Integer.Sparse.eval_collectBalanced, rawRowCheck17929]

def rawRow17930 : Integer.Sparse Key := [(key807, 4), (key812, 4), (key802, 4), (key905, -2), (key907, -2), (key807, -2), (key877, -2), (key802, -2), (key872, -2), (key821, -2), (key824, -2), (key782, -2), (key812, -2), (key777, -2), (key802, -2), (key821, 4), (key907, 4), (key802, 4)]

theorem rawRowCheck17930 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form17 = rawRow17930 := by decide +kernel

def row17930 : Integer.Sparse Key := [(key777, -2), (key782, -2), (key802, 4), (key807, 2), (key812, 2), (key821, 2), (key824, -2), (key872, -2), (key877, -2), (key905, -2), (key907, 2)]

theorem rowCheck17930 : row17930 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17930 := by decide +kernel

theorem rowEval17930 (x : Key → ℝ) : Integer.Sparse.eval row17930 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17930, Integer.Sparse.eval_collectBalanced, rawRowCheck17930]

def rawRow17931 : Integer.Sparse Key := [(key812, 4), (key807, 4), (key802, 4), (key907, -2), (key905, -2), (key877, -2), (key807, -2), (key872, -2), (key802, -2), (key824, -2), (key821, -2), (key812, -2), (key782, -2), (key802, -2), (key777, -2), (key907, 4), (key821, 4), (key802, 4)]

theorem rawRowCheck17931 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form17 = rawRow17931 := by decide +kernel

def row17931 : Integer.Sparse Key := [(key777, -2), (key782, -2), (key802, 4), (key807, 2), (key812, 2), (key821, 2), (key824, -2), (key872, -2), (key877, -2), (key905, -2), (key907, 2)]

theorem rowCheck17931 : row17931 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17931 := by decide +kernel

theorem rowEval17931 (x : Key → ℝ) : Integer.Sparse.eval row17931 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17931, Integer.Sparse.eval_collectBalanced, rawRowCheck17931]

def rawRow17932 : Integer.Sparse Key := [(key872, 4), (key877, 4), (key877, 4), (key802, -2), (key812, -2), (key802, -2), (key907, -2), (key812, -2), (key907, -2), (key802, -2), (key812, -2), (key802, -2), (key907, -2), (key812, -2), (key907, -2), (key777, 4), (key824, 4), (key824, 4)]

theorem rawRowCheck17932 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form17 = rawRow17932 := by decide +kernel

def row17932 : Integer.Sparse Key := [(key777, 4), (key802, -8), (key812, -8), (key824, 8), (key872, 4), (key877, 8), (key907, -8)]

theorem rowCheck17932 : row17932 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17932 := by decide +kernel

theorem rowEval17932 (x : Key → ℝ) : Integer.Sparse.eval row17932 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17932, Integer.Sparse.eval_collectBalanced, rawRowCheck17932]

def rawRow17933 : Integer.Sparse Key := [(key877, 4), (key872, 4), (key877, 4), (key812, -2), (key802, -2), (key907, -2), (key802, -2), (key907, -2), (key812, -2), (key812, -2), (key802, -2), (key907, -2), (key802, -2), (key907, -2), (key812, -2), (key824, 4), (key777, 4), (key824, 4)]

theorem rawRowCheck17933 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form17 = rawRow17933 := by decide +kernel

def row17933 : Integer.Sparse Key := [(key777, 4), (key802, -8), (key812, -8), (key824, 8), (key872, 4), (key877, 8), (key907, -8)]

theorem rowCheck17933 : row17933 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17933 := by decide +kernel

theorem rowEval17933 (x : Key → ℝ) : Integer.Sparse.eval row17933 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17933, Integer.Sparse.eval_collectBalanced, rawRowCheck17933]

def rawRow17934 : Integer.Sparse Key := [(key877, 4), (key877, 4), (key872, 4), (key907, -2), (key907, -2), (key812, -2), (key812, -2), (key802, -2), (key802, -2), (key907, -2), (key907, -2), (key812, -2), (key812, -2), (key802, -2), (key802, -2), (key824, 4), (key824, 4), (key777, 4)]

theorem rawRowCheck17934 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form17 = rawRow17934 := by decide +kernel

def row17934 : Integer.Sparse Key := [(key777, 4), (key802, -8), (key812, -8), (key824, 8), (key872, 4), (key877, 8), (key907, -8)]

theorem rowCheck17934 : row17934 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17934 := by decide +kernel

theorem rowEval17934 (x : Key → ℝ) : Integer.Sparse.eval row17934 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17934, Integer.Sparse.eval_collectBalanced, rawRowCheck17934]

def rawRow17935 : Integer.Sparse Key := [(key763, -2), (key765, -2), (key763, -2), (key785, -2), (key775, -2), (key785, -2), (key800, 2), (key810, 2), (key810, 2), (key835, 2), (key838, 2), (key838, 2), (key800, 2), (key810, 2), (key810, 2), (key933, -6), (key835, 2), (key838, 2), (key838, 2), (key933, -6)]

theorem rawRowCheck17935 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form18 = rawRow17935 := by decide +kernel

def row17935 : Integer.Sparse Key := [(key763, -4), (key765, -2), (key775, -2), (key785, -4), (key800, 4), (key810, 8), (key835, 4), (key838, 8), (key933, -12)]

theorem rowCheck17935 : row17935 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17935 := by decide +kernel

theorem rowEval17935 (x : Key → ℝ) : Integer.Sparse.eval row17935 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17935, Integer.Sparse.eval_collectBalanced, rawRowCheck17935]

def rawRow17936 : Integer.Sparse Key := [(key765, -2), (key763, -2), (key767, -2), (key773, -2), (key785, -2), (key775, -2), (key810, 2), (key800, 2), (key810, 2), (key838, 2), (key835, 2), (key838, 2), (key810, 2), (key800, 2), (key810, 2), (key933, -6), (key838, 2), (key835, 2), (key838, 2), (key933, -6)]

theorem rawRowCheck17936 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form18 = rawRow17936 := by decide +kernel

def row17936 : Integer.Sparse Key := [(key763, -2), (key765, -2), (key767, -2), (key773, -2), (key775, -2), (key785, -2), (key800, 4), (key810, 8), (key835, 4), (key838, 8), (key933, -12)]

theorem rowCheck17936 : row17936 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17936 := by decide +kernel

theorem rowEval17936 (x : Key → ℝ) : Integer.Sparse.eval row17936 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck17936, Integer.Sparse.eval_collectBalanced, rawRowCheck17936]

def rawRow17937 : Integer.Sparse Key := [(key767, -2), (key767, -2), (key765, -2), (key765, -2), (key773, -2), (key773, -2), (key810, 2), (key810, 2), (key800, 2), (key838, 2), (key838, 2), (key835, 2), (key810, 2), (key810, 2), (key800, 2), (key933, -6), (key838, 2), (key838, 2), (key835, 2), (key933, -6)]

theorem rawRowCheck17937 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form18 = rawRow17937 := by decide +kernel

def row17937 : Integer.Sparse Key := [(key765, -4), (key767, -4), (key773, -4), (key800, 4), (key810, 8), (key835, 4), (key838, 8), (key933, -12)]

theorem rowCheck17937 : row17937 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17937 := by decide +kernel

theorem rowEval17937 (x : Key → ℝ) : Integer.Sparse.eval row17937 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck17937, Integer.Sparse.eval_collectBalanced, rawRowCheck17937]

def rawRow17938 : Integer.Sparse Key := [(key763, -2), (key765, -2), (key788, -2), (key791, -2), (key790, -2), (key792, -2), (key763, 2), (key785, 2), (key838, 2), (key775, 2), (key785, 2), (key810, 2), (key800, 2), (key810, 2), (key933, 2), (key810, -6), (key835, 2), (key838, 2), (key933, 2), (key838, -6)]

theorem rawRowCheck17938 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form18 = rawRow17938 := by decide +kernel

def row17938 : Integer.Sparse Key := [(key765, -2), (key775, 2), (key785, 4), (key788, -2), (key790, -2), (key791, -2), (key792, -2), (key800, 2), (key810, -2), (key835, 2), (key838, -2), (key933, 4)]

theorem rowCheck17938 : row17938 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17938 := by decide +kernel

theorem rowEval17938 (x : Key → ℝ) : Integer.Sparse.eval row17938 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17938, Integer.Sparse.eval_collectBalanced, rawRowCheck17938]

def rawRow17939 : Integer.Sparse Key := [(key765, -2), (key763, -2), (key791, -2), (key788, -2), (key792, -2), (key790, -2), (key767, 2), (key773, 2), (key838, 2), (key785, 2), (key775, 2), (key810, 2), (key810, 2), (key800, 2), (key933, 2), (key810, -6), (key838, 2), (key835, 2), (key933, 2), (key838, -6)]

theorem rawRowCheck17939 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form18 = rawRow17939 := by decide +kernel

def row17939 : Integer.Sparse Key := [(key763, -2), (key765, -2), (key767, 2), (key773, 2), (key775, 2), (key785, 2), (key788, -2), (key790, -2), (key791, -2), (key792, -2), (key800, 2), (key810, -2), (key835, 2), (key838, -2), (key933, 4)]

theorem rowCheck17939 : row17939 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17939 := by decide +kernel

theorem rowEval17939 (x : Key → ℝ) : Integer.Sparse.eval row17939 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck17939, Integer.Sparse.eval_collectBalanced, rawRowCheck17939]

def rawRow17940 : Integer.Sparse Key := [(key788, -2), (key790, -2), (key763, -2), (key792, -2), (key765, -2), (key791, -2), (key763, 2), (key792, 2), (key785, 2), (key775, 2), (key810, 2), (key785, 2), (key800, 2), (key933, 2), (key810, 2), (key810, -6), (key835, 2), (key933, 2), (key838, 2), (key838, -6)]

theorem rawRowCheck17940 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form18 = rawRow17940 := by decide +kernel

def row17940 : Integer.Sparse Key := [(key765, -2), (key775, 2), (key785, 4), (key788, -2), (key790, -2), (key791, -2), (key800, 2), (key810, -2), (key835, 2), (key838, -4), (key933, 4)]

theorem rowCheck17940 : row17940 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17940 := by decide +kernel

theorem rowEval17940 (x : Key → ℝ) : Integer.Sparse.eval row17940 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17940, Integer.Sparse.eval_collectBalanced, rawRowCheck17940]

def rawRow17941 : Integer.Sparse Key := [(key790, -2), (key788, -2), (key792, -2), (key763, -2), (key791, -2), (key765, -2), (key792, 2), (key763, 2), (key785, 2), (key810, 2), (key775, 2), (key785, 2), (key933, 2), (key800, 2), (key810, 2), (key810, -6), (key933, 2), (key835, 2), (key838, 2), (key838, -6)]

theorem rawRowCheck17941 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form18 = rawRow17941 := by decide +kernel

def row17941 : Integer.Sparse Key := [(key765, -2), (key775, 2), (key785, 4), (key788, -2), (key790, -2), (key791, -2), (key800, 2), (key810, -2), (key835, 2), (key838, -4), (key933, 4)]

theorem rowCheck17941 : row17941 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17941 := by decide +kernel

theorem rowEval17941 (x : Key → ℝ) : Integer.Sparse.eval row17941 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17941, Integer.Sparse.eval_collectBalanced, rawRowCheck17941]

def rawRow17942 : Integer.Sparse Key := [(key791, -2), (key792, -2), (key765, -2), (key790, -2), (key763, -2), (key788, -2), (key767, 2), (key792, 2), (key773, 2), (key785, 2), (key810, 2), (key775, 2), (key810, 2), (key933, 2), (key800, 2), (key810, -6), (key838, 2), (key933, 2), (key835, 2), (key838, -6)]

theorem rawRowCheck17942 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form18 = rawRow17942 := by decide +kernel

def row17942 : Integer.Sparse Key := [(key763, -2), (key765, -2), (key767, 2), (key773, 2), (key775, 2), (key785, 2), (key788, -2), (key790, -2), (key791, -2), (key800, 2), (key810, -2), (key835, 2), (key838, -4), (key933, 4)]

theorem rowCheck17942 : row17942 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17942 := by decide +kernel

theorem rowEval17942 (x : Key → ℝ) : Integer.Sparse.eval row17942 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck17942, Integer.Sparse.eval_collectBalanced, rawRowCheck17942]

def rawRow17943 : Integer.Sparse Key := [(key792, -2), (key791, -2), (key790, -2), (key765, -2), (key788, -2), (key763, -2), (key792, 2), (key767, 2), (key773, 2), (key810, 2), (key785, 2), (key775, 2), (key933, 2), (key810, 2), (key800, 2), (key810, -6), (key933, 2), (key838, 2), (key835, 2), (key838, -6)]

theorem rawRowCheck17943 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form18 = rawRow17943 := by decide +kernel

def row17943 : Integer.Sparse Key := [(key763, -2), (key765, -2), (key767, 2), (key773, 2), (key775, 2), (key785, 2), (key788, -2), (key790, -2), (key791, -2), (key800, 2), (key810, -2), (key835, 2), (key838, -4), (key933, 4)]

theorem rowCheck17943 : row17943 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17943 := by decide +kernel

theorem rowEval17943 (x : Key → ℝ) : Integer.Sparse.eval row17943 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17943, Integer.Sparse.eval_collectBalanced, rawRowCheck17943]

def rawRow17944 : Integer.Sparse Key := [(key763, -2), (key765, -2), (key788, -2), (key791, -2), (key790, -2), (key792, -2), (key788, 2), (key791, 2), (key851, 2), (key790, 2), (key792, 2), (key851, 2), (key763, 2), (key785, 2), (key838, 2), (key838, -6), (key775, 2), (key785, 2), (key810, 2), (key810, -6)]

theorem rawRowCheck17944 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form18 = rawRow17944 := by decide +kernel

def row17944 : Integer.Sparse Key := [(key765, -2), (key775, 2), (key785, 4), (key810, -4), (key838, -4), (key851, 4)]

theorem rowCheck17944 : row17944 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17944 := by decide +kernel

theorem rowEval17944 (x : Key → ℝ) : Integer.Sparse.eval row17944 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17944, Integer.Sparse.eval_collectBalanced, rawRowCheck17944]

def rawRow17945 : Integer.Sparse Key := [(key765, -2), (key763, -2), (key791, -2), (key788, -2), (key792, -2), (key790, -2), (key791, 2), (key788, 2), (key851, 2), (key792, 2), (key790, 2), (key851, 2), (key767, 2), (key773, 2), (key838, 2), (key838, -6), (key785, 2), (key775, 2), (key810, 2), (key810, -6)]

theorem rawRowCheck17945 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form18 = rawRow17945 := by decide +kernel

def row17945 : Integer.Sparse Key := [(key763, -2), (key765, -2), (key767, 2), (key773, 2), (key775, 2), (key785, 2), (key810, -4), (key838, -4), (key851, 4)]

theorem rowCheck17945 : row17945 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17945 := by decide +kernel

theorem rowEval17945 (x : Key → ℝ) : Integer.Sparse.eval row17945 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck17945, Integer.Sparse.eval_collectBalanced, rawRowCheck17945]

def rawRow17946 : Integer.Sparse Key := [(key788, -2), (key790, -2), (key763, -2), (key792, -2), (key765, -2), (key791, -2), (key788, 2), (key851, 2), (key791, 2), (key790, 2), (key851, 2), (key792, 2), (key763, 2), (key792, 2), (key785, 2), (key838, -6), (key775, 2), (key810, 2), (key785, 2), (key810, -6)]

theorem rawRowCheck17946 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form18 = rawRow17946 := by decide +kernel

def row17946 : Integer.Sparse Key := [(key765, -2), (key775, 2), (key785, 4), (key792, 2), (key810, -4), (key838, -6), (key851, 4)]

theorem rowCheck17946 : row17946 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17946 := by decide +kernel

theorem rowEval17946 (x : Key → ℝ) : Integer.Sparse.eval row17946 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17946, Integer.Sparse.eval_collectBalanced, rawRowCheck17946]

def rawRow17947 : Integer.Sparse Key := [(key790, -2), (key788, -2), (key792, -2), (key763, -2), (key791, -2), (key765, -2), (key851, 2), (key788, 2), (key791, 2), (key851, 2), (key790, 2), (key792, 2), (key792, 2), (key763, 2), (key785, 2), (key838, -6), (key810, 2), (key775, 2), (key785, 2), (key810, -6)]

theorem rawRowCheck17947 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form18 = rawRow17947 := by decide +kernel

def row17947 : Integer.Sparse Key := [(key765, -2), (key775, 2), (key785, 4), (key792, 2), (key810, -4), (key838, -6), (key851, 4)]

theorem rowCheck17947 : row17947 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17947 := by decide +kernel

theorem rowEval17947 (x : Key → ℝ) : Integer.Sparse.eval row17947 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17947, Integer.Sparse.eval_collectBalanced, rawRowCheck17947]

def rawRow17948 : Integer.Sparse Key := [(key791, -2), (key792, -2), (key765, -2), (key790, -2), (key763, -2), (key788, -2), (key791, 2), (key851, 2), (key788, 2), (key792, 2), (key851, 2), (key790, 2), (key767, 2), (key792, 2), (key773, 2), (key838, -6), (key785, 2), (key810, 2), (key775, 2), (key810, -6)]

theorem rawRowCheck17948 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form18 = rawRow17948 := by decide +kernel

def row17948 : Integer.Sparse Key := [(key763, -2), (key765, -2), (key767, 2), (key773, 2), (key775, 2), (key785, 2), (key792, 2), (key810, -4), (key838, -6), (key851, 4)]

theorem rowCheck17948 : row17948 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17948 := by decide +kernel

theorem rowEval17948 (x : Key → ℝ) : Integer.Sparse.eval row17948 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck17948, Integer.Sparse.eval_collectBalanced, rawRowCheck17948]

def rawRow17949 : Integer.Sparse Key := [(key792, -2), (key791, -2), (key790, -2), (key765, -2), (key788, -2), (key763, -2), (key851, 2), (key791, 2), (key788, 2), (key851, 2), (key792, 2), (key790, 2), (key792, 2), (key767, 2), (key773, 2), (key838, -6), (key810, 2), (key785, 2), (key775, 2), (key810, -6)]

theorem rawRowCheck17949 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form18 = rawRow17949 := by decide +kernel

def row17949 : Integer.Sparse Key := [(key763, -2), (key765, -2), (key767, 2), (key773, 2), (key775, 2), (key785, 2), (key792, 2), (key810, -4), (key838, -6), (key851, 4)]

theorem rowCheck17949 : row17949 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17949 := by decide +kernel

theorem rowEval17949 (x : Key → ℝ) : Integer.Sparse.eval row17949 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17949, Integer.Sparse.eval_collectBalanced, rawRowCheck17949]

def rawRow17950 : Integer.Sparse Key := [(key788, -2), (key790, -2), (key788, -2), (key851, -2), (key790, -2), (key851, -2), (key763, 2), (key792, 2), (key792, 2), (key765, 2), (key791, 2), (key791, 2), (key763, 2), (key792, 2), (key792, 2), (key785, -6), (key775, 2), (key810, 2), (key810, 2), (key785, -6)]

theorem rawRowCheck17950 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form18 = rawRow17950 := by decide +kernel

def row17950 : Integer.Sparse Key := [(key763, 4), (key765, 2), (key775, 2), (key785, -12), (key788, -4), (key790, -4), (key791, 4), (key792, 8), (key810, 4), (key851, -4)]

theorem rowCheck17950 : row17950 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17950 := by decide +kernel

theorem rowEval17950 (x : Key → ℝ) : Integer.Sparse.eval row17950 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17950, Integer.Sparse.eval_collectBalanced, rawRowCheck17950]

def rawRow17951 : Integer.Sparse Key := [(key790, -2), (key788, -2), (key851, -2), (key788, -2), (key851, -2), (key790, -2), (key792, 2), (key763, 2), (key792, 2), (key791, 2), (key765, 2), (key791, 2), (key792, 2), (key763, 2), (key792, 2), (key785, -6), (key810, 2), (key775, 2), (key810, 2), (key785, -6)]

theorem rawRowCheck17951 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form18 = rawRow17951 := by decide +kernel

def row17951 : Integer.Sparse Key := [(key763, 4), (key765, 2), (key775, 2), (key785, -12), (key788, -4), (key790, -4), (key791, 4), (key792, 8), (key810, 4), (key851, -4)]

theorem rowCheck17951 : row17951 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17951 := by decide +kernel

theorem rowEval17951 (x : Key → ℝ) : Integer.Sparse.eval row17951 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17951, Integer.Sparse.eval_collectBalanced, rawRowCheck17951]

def rawRow17952 : Integer.Sparse Key := [(key851, -2), (key851, -2), (key790, -2), (key790, -2), (key788, -2), (key788, -2), (key792, 2), (key792, 2), (key763, 2), (key791, 2), (key791, 2), (key765, 2), (key792, 2), (key792, 2), (key763, 2), (key785, -6), (key810, 2), (key810, 2), (key775, 2), (key785, -6)]

theorem rawRowCheck17952 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form18 = rawRow17952 := by decide +kernel

def row17952 : Integer.Sparse Key := [(key763, 4), (key765, 2), (key775, 2), (key785, -12), (key788, -4), (key790, -4), (key791, 4), (key792, 8), (key810, 4), (key851, -4)]

theorem rowCheck17952 : row17952 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17952 := by decide +kernel

theorem rowEval17952 (x : Key → ℝ) : Integer.Sparse.eval row17952 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17952, Integer.Sparse.eval_collectBalanced, rawRowCheck17952]

def rawRow17953 : Integer.Sparse Key := [(key636, 4), (key636, 4), (key637, 4), (key642, -4), (key643, -4), (key643, -4), (key642, -4), (key643, -4), (key643, -4), (key651, 12)]

theorem rawRowCheck17953 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form19 = rawRow17953 := by decide +kernel

def row17953 : Integer.Sparse Key := [(key636, 8), (key637, 4), (key642, -8), (key643, -16), (key651, 12)]

theorem rowCheck17953 : row17953 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17953 := by decide +kernel

theorem rowEval17953 (x : Key → ℝ) : Integer.Sparse.eval row17953 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17953, Integer.Sparse.eval_collectBalanced, rawRowCheck17953]

def rawRow17954 : Integer.Sparse Key := [(key636, 4), (key637, 4), (key636, 4), (key643, -4), (key642, -4), (key643, -4), (key643, -4), (key642, -4), (key643, -4), (key651, 12)]

theorem rawRowCheck17954 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form19 = rawRow17954 := by decide +kernel

def row17954 : Integer.Sparse Key := [(key636, 8), (key637, 4), (key642, -8), (key643, -16), (key651, 12)]

theorem rowCheck17954 : row17954 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17954 := by decide +kernel

theorem rowEval17954 (x : Key → ℝ) : Integer.Sparse.eval row17954 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form19) x := by
  rw [rowCheck17954, Integer.Sparse.eval_collectBalanced, rawRowCheck17954]

def rawRow17955 : Integer.Sparse Key := [(key637, 4), (key636, 4), (key636, 4), (key643, -4), (key643, -4), (key642, -4), (key643, -4), (key643, -4), (key642, -4), (key651, 12)]

theorem rawRowCheck17955 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form19 = rawRow17955 := by decide +kernel

def row17955 : Integer.Sparse Key := [(key636, 8), (key637, 4), (key642, -8), (key643, -16), (key651, 12)]

theorem rowCheck17955 : row17955 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17955 := by decide +kernel

theorem rowEval17955 (x : Key → ℝ) : Integer.Sparse.eval row17955 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form19) x := by
  rw [rowCheck17955, Integer.Sparse.eval_collectBalanced, rawRowCheck17955]

def rawRow17956 : Integer.Sparse Key := [(key636, 4), (key642, 4), (key643, 4), (key636, -4), (key637, -4), (key643, -4), (key642, -4), (key643, -4), (key651, -4), (key643, 12)]

theorem rawRowCheck17956 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form19 = rawRow17956 := by decide +kernel

def row17956 : Integer.Sparse Key := [(key637, -4), (key643, 8), (key651, -4)]

theorem rowCheck17956 : row17956 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17956 := by decide +kernel

theorem rowEval17956 (x : Key → ℝ) : Integer.Sparse.eval row17956 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17956, Integer.Sparse.eval_collectBalanced, rawRowCheck17956]

def rawRow17957 : Integer.Sparse Key := [(key636, 4), (key643, 4), (key642, 4), (key637, -4), (key636, -4), (key643, -4), (key643, -4), (key642, -4), (key651, -4), (key643, 12)]

theorem rawRowCheck17957 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form19 = rawRow17957 := by decide +kernel

def row17957 : Integer.Sparse Key := [(key637, -4), (key643, 8), (key651, -4)]

theorem rowCheck17957 : row17957 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17957 := by decide +kernel

theorem rowEval17957 (x : Key → ℝ) : Integer.Sparse.eval row17957 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form19) x := by
  rw [rowCheck17957, Integer.Sparse.eval_collectBalanced, rawRowCheck17957]

def rawRow17958 : Integer.Sparse Key := [(key642, 4), (key636, 4), (key643, 4), (key636, -4), (key643, -4), (key637, -4), (key642, -4), (key651, -4), (key643, -4), (key643, 12)]

theorem rawRowCheck17958 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form19 = rawRow17958 := by decide +kernel

def row17958 : Integer.Sparse Key := [(key637, -4), (key643, 8), (key651, -4)]

theorem rowCheck17958 : row17958 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17958 := by decide +kernel

theorem rowEval17958 (x : Key → ℝ) : Integer.Sparse.eval row17958 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17958, Integer.Sparse.eval_collectBalanced, rawRowCheck17958]

def rawRow17959 : Integer.Sparse Key := [(key642, 4), (key643, 4), (key636, 4), (key643, -4), (key636, -4), (key637, -4), (key651, -4), (key642, -4), (key643, -4), (key643, 12)]

theorem rawRowCheck17959 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form19 = rawRow17959 := by decide +kernel

def row17959 : Integer.Sparse Key := [(key637, -4), (key643, 8), (key651, -4)]

theorem rowCheck17959 : row17959 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17959 := by decide +kernel

theorem rowEval17959 (x : Key → ℝ) : Integer.Sparse.eval row17959 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17959, Integer.Sparse.eval_collectBalanced, rawRowCheck17959]

def rawRow17960 : Integer.Sparse Key := [(key643, 4), (key636, 4), (key642, 4), (key637, -4), (key643, -4), (key636, -4), (key643, -4), (key651, -4), (key642, -4), (key643, 12)]

theorem rawRowCheck17960 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form19 = rawRow17960 := by decide +kernel

def row17960 : Integer.Sparse Key := [(key637, -4), (key643, 8), (key651, -4)]

theorem rowCheck17960 : row17960 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17960 := by decide +kernel

theorem rowEval17960 (x : Key → ℝ) : Integer.Sparse.eval row17960 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form19) x := by
  rw [rowCheck17960, Integer.Sparse.eval_collectBalanced, rawRowCheck17960]

def rawRow17961 : Integer.Sparse Key := [(key643, 4), (key642, 4), (key636, 4), (key643, -4), (key637, -4), (key636, -4), (key651, -4), (key643, -4), (key642, -4), (key643, 12)]

theorem rawRowCheck17961 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form19 = rawRow17961 := by decide +kernel

def row17961 : Integer.Sparse Key := [(key637, -4), (key643, 8), (key651, -4)]

theorem rowCheck17961 : row17961 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17961 := by decide +kernel

theorem rowEval17961 (x : Key → ℝ) : Integer.Sparse.eval row17961 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17961, Integer.Sparse.eval_collectBalanced, rawRowCheck17961]

def rawRow17962 : Integer.Sparse Key := [(key636, 4), (key642, 4), (key643, 4), (key642, -4), (key643, -4), (key651, -4), (key636, -4), (key637, -4), (key643, -4), (key643, 12)]

theorem rawRowCheck17962 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form19 = rawRow17962 := by decide +kernel

def row17962 : Integer.Sparse Key := [(key637, -4), (key643, 8), (key651, -4)]

theorem rowCheck17962 : row17962 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17962 := by decide +kernel

theorem rowEval17962 (x : Key → ℝ) : Integer.Sparse.eval row17962 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17962, Integer.Sparse.eval_collectBalanced, rawRowCheck17962]

def rawRow17963 : Integer.Sparse Key := [(key636, 4), (key643, 4), (key642, 4), (key643, -4), (key642, -4), (key651, -4), (key637, -4), (key636, -4), (key643, -4), (key643, 12)]

theorem rawRowCheck17963 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form19 = rawRow17963 := by decide +kernel

def row17963 : Integer.Sparse Key := [(key637, -4), (key643, 8), (key651, -4)]

theorem rowCheck17963 : row17963 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17963 := by decide +kernel

theorem rowEval17963 (x : Key → ℝ) : Integer.Sparse.eval row17963 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form19) x := by
  rw [rowCheck17963, Integer.Sparse.eval_collectBalanced, rawRowCheck17963]

def rawRow17964 : Integer.Sparse Key := [(key642, 4), (key636, 4), (key643, 4), (key642, -4), (key651, -4), (key643, -4), (key636, -4), (key643, -4), (key637, -4), (key643, 12)]

theorem rawRowCheck17964 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form19 = rawRow17964 := by decide +kernel

def row17964 : Integer.Sparse Key := [(key637, -4), (key643, 8), (key651, -4)]

theorem rowCheck17964 : row17964 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17964 := by decide +kernel

theorem rowEval17964 (x : Key → ℝ) : Integer.Sparse.eval row17964 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17964, Integer.Sparse.eval_collectBalanced, rawRowCheck17964]

def rawRow17965 : Integer.Sparse Key := [(key642, 4), (key643, 4), (key636, 4), (key651, -4), (key642, -4), (key643, -4), (key643, -4), (key636, -4), (key637, -4), (key643, 12)]

theorem rawRowCheck17965 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form19 = rawRow17965 := by decide +kernel

def row17965 : Integer.Sparse Key := [(key637, -4), (key643, 8), (key651, -4)]

theorem rowCheck17965 : row17965 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17965 := by decide +kernel

theorem rowEval17965 (x : Key → ℝ) : Integer.Sparse.eval row17965 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17965, Integer.Sparse.eval_collectBalanced, rawRowCheck17965]

def rawRow17966 : Integer.Sparse Key := [(key643, 4), (key636, 4), (key642, 4), (key643, -4), (key651, -4), (key642, -4), (key637, -4), (key643, -4), (key636, -4), (key643, 12)]

theorem rawRowCheck17966 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form19 = rawRow17966 := by decide +kernel

def row17966 : Integer.Sparse Key := [(key637, -4), (key643, 8), (key651, -4)]

theorem rowCheck17966 : row17966 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17966 := by decide +kernel

theorem rowEval17966 (x : Key → ℝ) : Integer.Sparse.eval row17966 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form19) x := by
  rw [rowCheck17966, Integer.Sparse.eval_collectBalanced, rawRowCheck17966]

def rawRow17967 : Integer.Sparse Key := [(key643, 4), (key642, 4), (key636, 4), (key651, -4), (key643, -4), (key642, -4), (key643, -4), (key637, -4), (key636, -4), (key643, 12)]

theorem rawRowCheck17967 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form19 = rawRow17967 := by decide +kernel

def row17967 : Integer.Sparse Key := [(key637, -4), (key643, 8), (key651, -4)]

theorem rowCheck17967 : row17967 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17967 := by decide +kernel

theorem rowEval17967 (x : Key → ℝ) : Integer.Sparse.eval row17967 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17967, Integer.Sparse.eval_collectBalanced, rawRowCheck17967]

def rawRow17968 : Integer.Sparse Key := [(key642, 4), (key642, 4), (key651, 4), (key636, -4), (key643, -4), (key643, -4), (key636, -4), (key643, -4), (key643, -4), (key637, 12)]

theorem rawRowCheck17968 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form19 = rawRow17968 := by decide +kernel

def row17968 : Integer.Sparse Key := [(key636, -8), (key637, 12), (key642, 8), (key643, -16), (key651, 4)]

theorem rowCheck17968 : row17968 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17968 := by decide +kernel

theorem rowEval17968 (x : Key → ℝ) : Integer.Sparse.eval row17968 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17968, Integer.Sparse.eval_collectBalanced, rawRowCheck17968]

def rawRow17969 : Integer.Sparse Key := [(key642, 4), (key651, 4), (key642, 4), (key643, -4), (key636, -4), (key643, -4), (key643, -4), (key636, -4), (key643, -4), (key637, 12)]

theorem rawRowCheck17969 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form19 = rawRow17969 := by decide +kernel

def row17969 : Integer.Sparse Key := [(key636, -8), (key637, 12), (key642, 8), (key643, -16), (key651, 4)]

theorem rowCheck17969 : row17969 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17969 := by decide +kernel

theorem rowEval17969 (x : Key → ℝ) : Integer.Sparse.eval row17969 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17969, Integer.Sparse.eval_collectBalanced, rawRowCheck17969]

def rawRow17970 : Integer.Sparse Key := [(key651, 4), (key642, 4), (key642, 4), (key643, -4), (key643, -4), (key636, -4), (key643, -4), (key643, -4), (key636, -4), (key637, 12)]

theorem rawRowCheck17970 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form19 = rawRow17970 := by decide +kernel

def row17970 : Integer.Sparse Key := [(key636, -8), (key637, 12), (key642, 8), (key643, -16), (key651, 4)]

theorem rowCheck17970 : row17970 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17970 := by decide +kernel

theorem rowEval17970 (x : Key → ℝ) : Integer.Sparse.eval row17970 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17970, Integer.Sparse.eval_collectBalanced, rawRowCheck17970]

def rawRow17971 : Integer.Sparse Key := [(key781, 4), (key784, 4), (key784, 4), (key806, -2), (key809, -2), (key806, -2), (key814, -2), (key809, -2), (key814, -2), (key806, -2), (key809, -2), (key806, -2), (key814, -2), (key809, -2), (key814, -2), (key875, 4), (key879, 4), (key879, 4)]

theorem rawRowCheck17971 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form20 = rawRow17971 := by decide +kernel

def row17971 : Integer.Sparse Key := [(key781, 4), (key784, 8), (key806, -8), (key809, -8), (key814, -8), (key875, 4), (key879, 8)]

theorem rowCheck17971 : row17971 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17971 := by decide +kernel

theorem rowEval17971 (x : Key → ℝ) : Integer.Sparse.eval row17971 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form20) x := by
  rw [rowCheck17971, Integer.Sparse.eval_collectBalanced, rawRowCheck17971]

def rawRow17972 : Integer.Sparse Key := [(key784, 4), (key781, 4), (key784, 4), (key809, -2), (key806, -2), (key814, -2), (key806, -2), (key814, -2), (key809, -2), (key809, -2), (key806, -2), (key814, -2), (key806, -2), (key814, -2), (key809, -2), (key879, 4), (key875, 4), (key879, 4)]

theorem rawRowCheck17972 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form20 = rawRow17972 := by decide +kernel

def row17972 : Integer.Sparse Key := [(key781, 4), (key784, 8), (key806, -8), (key809, -8), (key814, -8), (key875, 4), (key879, 8)]

theorem rowCheck17972 : row17972 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17972 := by decide +kernel

theorem rowEval17972 (x : Key → ℝ) : Integer.Sparse.eval row17972 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form20) x := by
  rw [rowCheck17972, Integer.Sparse.eval_collectBalanced, rawRowCheck17972]

def rawRow17973 : Integer.Sparse Key := [(key784, 4), (key784, 4), (key781, 4), (key814, -2), (key814, -2), (key809, -2), (key809, -2), (key806, -2), (key806, -2), (key814, -2), (key814, -2), (key809, -2), (key809, -2), (key806, -2), (key806, -2), (key879, 4), (key879, 4), (key875, 4)]

theorem rawRowCheck17973 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form20 = rawRow17973 := by decide +kernel

def row17973 : Integer.Sparse Key := [(key781, 4), (key784, 8), (key806, -8), (key809, -8), (key814, -8), (key875, 4), (key879, 8)]

theorem rowCheck17973 : row17973 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17973 := by decide +kernel

theorem rowEval17973 (x : Key → ℝ) : Integer.Sparse.eval row17973 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form20) x := by
  rw [rowCheck17973, Integer.Sparse.eval_collectBalanced, rawRowCheck17973]

def rawRow17974 : Integer.Sparse Key := [(key806, 4), (key809, 4), (key814, 4), (key781, -2), (key784, -2), (key806, -2), (key814, -2), (key822, -2), (key827, -2), (key806, -2), (key809, -2), (key875, -2), (key879, -2), (key906, -2), (key910, -2), (key806, 4), (key814, 4), (key910, 4)]

theorem rawRowCheck17974 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form20 = rawRow17974 := by decide +kernel

def row17974 : Integer.Sparse Key := [(key781, -2), (key784, -2), (key806, 4), (key809, 2), (key814, 6), (key822, -2), (key827, -2), (key875, -2), (key879, -2), (key906, -2), (key910, 2)]

theorem rowCheck17974 : row17974 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17974 := by decide +kernel

theorem rowEval17974 (x : Key → ℝ) : Integer.Sparse.eval row17974 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form20) x := by
  rw [rowCheck17974, Integer.Sparse.eval_collectBalanced, rawRowCheck17974]

def rawRow17975 : Integer.Sparse Key := [(key809, 4), (key806, 4), (key814, 4), (key784, -2), (key781, -2), (key814, -2), (key806, -2), (key827, -2), (key822, -2), (key809, -2), (key806, -2), (key879, -2), (key875, -2), (key910, -2), (key906, -2), (key814, 4), (key806, 4), (key910, 4)]

theorem rawRowCheck17975 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form20 = rawRow17975 := by decide +kernel

def row17975 : Integer.Sparse Key := [(key781, -2), (key784, -2), (key806, 4), (key809, 2), (key814, 6), (key822, -2), (key827, -2), (key875, -2), (key879, -2), (key906, -2), (key910, 2)]

theorem rowCheck17975 : row17975 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17975 := by decide +kernel

theorem rowEval17975 (x : Key → ℝ) : Integer.Sparse.eval row17975 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form20) x := by
  rw [rowCheck17975, Integer.Sparse.eval_collectBalanced, rawRowCheck17975]

def rawRow17976 : Integer.Sparse Key := [(key806, 4), (key814, 4), (key809, 4), (key806, -2), (key814, -2), (key781, -2), (key827, -2), (key784, -2), (key814, -2), (key875, -2), (key906, -2), (key806, -2), (key910, -2), (key809, -2), (key879, -2), (key806, 4), (key910, 4), (key814, 4)]

theorem rawRowCheck17976 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form20 = rawRow17976 := by decide +kernel

def row17976 : Integer.Sparse Key := [(key781, -2), (key784, -2), (key806, 4), (key809, 2), (key814, 4), (key827, -2), (key875, -2), (key879, -2), (key906, -2), (key910, 2)]

theorem rowCheck17976 : row17976 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17976 := by decide +kernel

theorem rowEval17976 (x : Key → ℝ) : Integer.Sparse.eval row17976 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form20) x := by
  rw [rowCheck17976, Integer.Sparse.eval_collectBalanced, rawRowCheck17976]

def rawRow17977 : Integer.Sparse Key := [(key814, 4), (key806, 4), (key809, 4), (key814, -2), (key806, -2), (key827, -2), (key781, -2), (key814, -2), (key784, -2), (key906, -2), (key875, -2), (key910, -2), (key806, -2), (key879, -2), (key809, -2), (key910, 4), (key806, 4), (key814, 4)]

theorem rawRowCheck17977 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form20 = rawRow17977 := by decide +kernel

def row17977 : Integer.Sparse Key := [(key781, -2), (key784, -2), (key806, 4), (key809, 2), (key814, 4), (key827, -2), (key875, -2), (key879, -2), (key906, -2), (key910, 2)]

theorem rowCheck17977 : row17977 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17977 := by decide +kernel

theorem rowEval17977 (x : Key → ℝ) : Integer.Sparse.eval row17977 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck17977, Integer.Sparse.eval_collectBalanced, rawRowCheck17977]

def rawRow17978 : Integer.Sparse Key := [(key809, 4), (key814, 4), (key806, 4), (key822, -2), (key827, -2), (key784, -2), (key814, -2), (key781, -2), (key806, -2), (key879, -2), (key910, -2), (key809, -2), (key906, -2), (key806, -2), (key875, -2), (key814, 4), (key910, 4), (key806, 4)]

theorem rawRowCheck17978 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form20 = rawRow17978 := by decide +kernel

def row17978 : Integer.Sparse Key := [(key781, -2), (key784, -2), (key806, 4), (key809, 2), (key814, 6), (key822, -2), (key827, -2), (key875, -2), (key879, -2), (key906, -2), (key910, 2)]

theorem rowCheck17978 : row17978 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17978 := by decide +kernel

theorem rowEval17978 (x : Key → ℝ) : Integer.Sparse.eval row17978 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form20) x := by
  rw [rowCheck17978, Integer.Sparse.eval_collectBalanced, rawRowCheck17978]

def rawRow17979 : Integer.Sparse Key := [(key814, 4), (key809, 4), (key806, 4), (key827, -2), (key822, -2), (key814, -2), (key784, -2), (key806, -2), (key781, -2), (key910, -2), (key879, -2), (key906, -2), (key809, -2), (key875, -2), (key806, -2), (key910, 4), (key814, 4), (key806, 4)]

theorem rawRowCheck17979 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form20 = rawRow17979 := by decide +kernel

def row17979 : Integer.Sparse Key := [(key781, -2), (key784, -2), (key806, 4), (key809, 2), (key814, 6), (key822, -2), (key827, -2), (key875, -2), (key879, -2), (key906, -2), (key910, 2)]

theorem rowCheck17979 : row17979 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17979 := by decide +kernel

theorem rowEval17979 (x : Key → ℝ) : Integer.Sparse.eval row17979 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck17979, Integer.Sparse.eval_collectBalanced, rawRowCheck17979]

def rawRow17980 : Integer.Sparse Key := [(key806, 4), (key809, 4), (key814, 4), (key806, -2), (key809, -2), (key875, -2), (key906, -2), (key879, -2), (key910, -2), (key781, -2), (key784, -2), (key806, -2), (key814, -2), (key822, -2), (key827, -2), (key806, 4), (key814, 4), (key910, 4)]

theorem rawRowCheck17980 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form20 = rawRow17980 := by decide +kernel

def row17980 : Integer.Sparse Key := [(key781, -2), (key784, -2), (key806, 4), (key809, 2), (key814, 6), (key822, -2), (key827, -2), (key875, -2), (key879, -2), (key906, -2), (key910, 2)]

theorem rowCheck17980 : row17980 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17980 := by decide +kernel

theorem rowEval17980 (x : Key → ℝ) : Integer.Sparse.eval row17980 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form20) x := by
  rw [rowCheck17980, Integer.Sparse.eval_collectBalanced, rawRowCheck17980]

def rawRow17981 : Integer.Sparse Key := [(key809, 4), (key806, 4), (key814, 4), (key809, -2), (key806, -2), (key906, -2), (key875, -2), (key910, -2), (key879, -2), (key784, -2), (key781, -2), (key814, -2), (key806, -2), (key827, -2), (key822, -2), (key814, 4), (key806, 4), (key910, 4)]

theorem rawRowCheck17981 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form20 = rawRow17981 := by decide +kernel

def row17981 : Integer.Sparse Key := [(key781, -2), (key784, -2), (key806, 4), (key809, 2), (key814, 6), (key822, -2), (key827, -2), (key875, -2), (key879, -2), (key906, -2), (key910, 2)]

theorem rowCheck17981 : row17981 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17981 := by decide +kernel

theorem rowEval17981 (x : Key → ℝ) : Integer.Sparse.eval row17981 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form20) x := by
  rw [rowCheck17981, Integer.Sparse.eval_collectBalanced, rawRowCheck17981]

def rawRow17982 : Integer.Sparse Key := [(key806, 4), (key814, 4), (key809, 4), (key875, -2), (key879, -2), (key806, -2), (key910, -2), (key809, -2), (key906, -2), (key806, -2), (key814, -2), (key781, -2), (key827, -2), (key784, -2), (key814, -2), (key806, 4), (key910, 4), (key814, 4)]

theorem rawRowCheck17982 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form20 = rawRow17982 := by decide +kernel

def row17982 : Integer.Sparse Key := [(key781, -2), (key784, -2), (key806, 4), (key809, 2), (key814, 4), (key827, -2), (key875, -2), (key879, -2), (key906, -2), (key910, 2)]

theorem rowCheck17982 : row17982 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17982 := by decide +kernel

theorem rowEval17982 (x : Key → ℝ) : Integer.Sparse.eval row17982 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form20) x := by
  rw [rowCheck17982, Integer.Sparse.eval_collectBalanced, rawRowCheck17982]

def rawRow17983 : Integer.Sparse Key := [(key814, 4), (key806, 4), (key809, 4), (key879, -2), (key875, -2), (key910, -2), (key806, -2), (key906, -2), (key809, -2), (key814, -2), (key806, -2), (key827, -2), (key781, -2), (key814, -2), (key784, -2), (key910, 4), (key806, 4), (key814, 4)]

theorem rawRowCheck17983 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form20 = rawRow17983 := by decide +kernel

def row17983 : Integer.Sparse Key := [(key781, -2), (key784, -2), (key806, 4), (key809, 2), (key814, 4), (key827, -2), (key875, -2), (key879, -2), (key906, -2), (key910, 2)]

theorem rowCheck17983 : row17983 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17983 := by decide +kernel

theorem rowEval17983 (x : Key → ℝ) : Integer.Sparse.eval row17983 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck17983, Integer.Sparse.eval_collectBalanced, rawRowCheck17983]

def rawRow17984 : Integer.Sparse Key := [(key809, 4), (key814, 4), (key806, 4), (key906, -2), (key910, -2), (key809, -2), (key879, -2), (key806, -2), (key875, -2), (key822, -2), (key827, -2), (key784, -2), (key814, -2), (key781, -2), (key806, -2), (key814, 4), (key910, 4), (key806, 4)]

theorem rawRowCheck17984 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form20 = rawRow17984 := by decide +kernel

def row17984 : Integer.Sparse Key := [(key781, -2), (key784, -2), (key806, 4), (key809, 2), (key814, 6), (key822, -2), (key827, -2), (key875, -2), (key879, -2), (key906, -2), (key910, 2)]

theorem rowCheck17984 : row17984 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17984 := by decide +kernel

theorem rowEval17984 (x : Key → ℝ) : Integer.Sparse.eval row17984 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form20) x := by
  rw [rowCheck17984, Integer.Sparse.eval_collectBalanced, rawRowCheck17984]

def rawRow17985 : Integer.Sparse Key := [(key814, 4), (key809, 4), (key806, 4), (key910, -2), (key906, -2), (key879, -2), (key809, -2), (key875, -2), (key806, -2), (key827, -2), (key822, -2), (key814, -2), (key784, -2), (key806, -2), (key781, -2), (key910, 4), (key814, 4), (key806, 4)]

theorem rawRowCheck17985 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form20 = rawRow17985 := by decide +kernel

def row17985 : Integer.Sparse Key := [(key781, -2), (key784, -2), (key806, 4), (key809, 2), (key814, 6), (key822, -2), (key827, -2), (key875, -2), (key879, -2), (key906, -2), (key910, 2)]

theorem rowCheck17985 : row17985 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17985 := by decide +kernel

theorem rowEval17985 (x : Key → ℝ) : Integer.Sparse.eval row17985 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck17985, Integer.Sparse.eval_collectBalanced, rawRowCheck17985]

def rawRow17986 : Integer.Sparse Key := [(key875, 4), (key879, 4), (key879, 4), (key806, -2), (key814, -2), (key806, -2), (key910, -2), (key814, -2), (key910, -2), (key806, -2), (key814, -2), (key806, -2), (key910, -2), (key814, -2), (key910, -2), (key781, 4), (key827, 4), (key827, 4)]

theorem rawRowCheck17986 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form20 = rawRow17986 := by decide +kernel

def row17986 : Integer.Sparse Key := [(key781, 4), (key806, -8), (key814, -8), (key827, 8), (key875, 4), (key879, 8), (key910, -8)]

theorem rowCheck17986 : row17986 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17986 := by decide +kernel

theorem rowEval17986 (x : Key → ℝ) : Integer.Sparse.eval row17986 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form20) x := by
  rw [rowCheck17986, Integer.Sparse.eval_collectBalanced, rawRowCheck17986]

def rawRow17987 : Integer.Sparse Key := [(key879, 4), (key875, 4), (key879, 4), (key814, -2), (key806, -2), (key910, -2), (key806, -2), (key910, -2), (key814, -2), (key814, -2), (key806, -2), (key910, -2), (key806, -2), (key910, -2), (key814, -2), (key827, 4), (key781, 4), (key827, 4)]

theorem rawRowCheck17987 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form20 = rawRow17987 := by decide +kernel

def row17987 : Integer.Sparse Key := [(key781, 4), (key806, -8), (key814, -8), (key827, 8), (key875, 4), (key879, 8), (key910, -8)]

theorem rowCheck17987 : row17987 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17987 := by decide +kernel

theorem rowEval17987 (x : Key → ℝ) : Integer.Sparse.eval row17987 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck17987, Integer.Sparse.eval_collectBalanced, rawRowCheck17987]

def rawRow17988 : Integer.Sparse Key := [(key879, 4), (key879, 4), (key875, 4), (key910, -2), (key910, -2), (key814, -2), (key814, -2), (key806, -2), (key806, -2), (key910, -2), (key910, -2), (key814, -2), (key814, -2), (key806, -2), (key806, -2), (key827, 4), (key827, 4), (key781, 4)]

theorem rawRowCheck17988 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form20 = rawRow17988 := by decide +kernel

def row17988 : Integer.Sparse Key := [(key781, 4), (key806, -8), (key814, -8), (key827, 8), (key875, 4), (key879, 8), (key910, -8)]

theorem rowCheck17988 : row17988 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17988 := by decide +kernel

theorem rowEval17988 (x : Key → ℝ) : Integer.Sparse.eval row17988 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck17988, Integer.Sparse.eval_collectBalanced, rawRowCheck17988]

def rawRow17989 : Integer.Sparse Key := [(key2421, 4), (key2496, 4), (key2550, 4), (key2428, -2), (key2429, -2), (key2496, -2), (key2550, -2), (key2508, -2), (key2556, -2), (key2428, -2), (key2429, -2), (key2496, -2), (key2550, -2), (key2508, -2), (key2556, -2), (key2442, 4), (key2508, 4), (key2556, 4)]

theorem rawRowCheck17989 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form0 = rawRow17989 := by decide +kernel

def row17989 : Integer.Sparse Key := [(key2421, 4), (key2428, -4), (key2429, -4), (key2442, 4)]

theorem rowCheck17989 : row17989 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17989 := by decide +kernel

theorem rowEval17989 (x : Key → ℝ) : Integer.Sparse.eval row17989 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17989, Integer.Sparse.eval_collectBalanced, rawRowCheck17989]

def rawRow17990 : Integer.Sparse Key := [(key2421, 4), (key2550, 4), (key2496, 4), (key2429, -2), (key2428, -2), (key2550, -2), (key2496, -2), (key2556, -2), (key2508, -2), (key2429, -2), (key2428, -2), (key2550, -2), (key2496, -2), (key2556, -2), (key2508, -2), (key2442, 4), (key2556, 4), (key2508, 4)]

theorem rawRowCheck17990 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form0 = rawRow17990 := by decide +kernel

def row17990 : Integer.Sparse Key := [(key2421, 4), (key2428, -4), (key2429, -4), (key2442, 4)]

theorem rowCheck17990 : row17990 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17990 := by decide +kernel

theorem rowEval17990 (x : Key → ℝ) : Integer.Sparse.eval row17990 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17990, Integer.Sparse.eval_collectBalanced, rawRowCheck17990]

def rawRow17991 : Integer.Sparse Key := [(key2496, 4), (key2421, 4), (key2550, 4), (key2496, -2), (key2508, -2), (key2428, -2), (key2556, -2), (key2429, -2), (key2550, -2), (key2496, -2), (key2508, -2), (key2428, -2), (key2556, -2), (key2429, -2), (key2550, -2), (key2508, 4), (key2442, 4), (key2556, 4)]

theorem rawRowCheck17991 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form0 = rawRow17991 := by decide +kernel

def row17991 : Integer.Sparse Key := [(key2421, 4), (key2428, -4), (key2429, -4), (key2442, 4)]

theorem rowCheck17991 : row17991 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17991 := by decide +kernel

theorem rowEval17991 (x : Key → ℝ) : Integer.Sparse.eval row17991 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17991, Integer.Sparse.eval_collectBalanced, rawRowCheck17991]

def rawRow17992 : Integer.Sparse Key := [(key2496, 4), (key2550, 4), (key2421, 4), (key2508, -2), (key2496, -2), (key2556, -2), (key2428, -2), (key2550, -2), (key2429, -2), (key2508, -2), (key2496, -2), (key2556, -2), (key2428, -2), (key2550, -2), (key2429, -2), (key2508, 4), (key2556, 4), (key2442, 4)]

theorem rawRowCheck17992 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form0 = rawRow17992 := by decide +kernel

def row17992 : Integer.Sparse Key := [(key2421, 4), (key2428, -4), (key2429, -4), (key2442, 4)]

theorem rowCheck17992 : row17992 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17992 := by decide +kernel

theorem rowEval17992 (x : Key → ℝ) : Integer.Sparse.eval row17992 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17992, Integer.Sparse.eval_collectBalanced, rawRowCheck17992]

def rawRow17993 : Integer.Sparse Key := [(key2550, 4), (key2421, 4), (key2496, 4), (key2550, -2), (key2556, -2), (key2429, -2), (key2508, -2), (key2428, -2), (key2496, -2), (key2550, -2), (key2556, -2), (key2429, -2), (key2508, -2), (key2428, -2), (key2496, -2), (key2556, 4), (key2442, 4), (key2508, 4)]

theorem rawRowCheck17993 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form0 = rawRow17993 := by decide +kernel

def row17993 : Integer.Sparse Key := [(key2421, 4), (key2428, -4), (key2429, -4), (key2442, 4)]

theorem rowCheck17993 : row17993 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17993 := by decide +kernel

theorem rowEval17993 (x : Key → ℝ) : Integer.Sparse.eval row17993 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17993, Integer.Sparse.eval_collectBalanced, rawRowCheck17993]

def rawRow17994 : Integer.Sparse Key := [(key2550, 4), (key2496, 4), (key2421, 4), (key2556, -2), (key2550, -2), (key2508, -2), (key2429, -2), (key2496, -2), (key2428, -2), (key2556, -2), (key2550, -2), (key2508, -2), (key2429, -2), (key2496, -2), (key2428, -2), (key2556, 4), (key2508, 4), (key2442, 4)]

theorem rawRowCheck17994 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form0 = rawRow17994 := by decide +kernel

def row17994 : Integer.Sparse Key := [(key2421, 4), (key2428, -4), (key2429, -4), (key2442, 4)]

theorem rowCheck17994 : row17994 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17994 := by decide +kernel

theorem rowEval17994 (x : Key → ℝ) : Integer.Sparse.eval row17994 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17994, Integer.Sparse.eval_collectBalanced, rawRowCheck17994]

def rawRow17995 : Integer.Sparse Key := [(key2428, 4), (key2428, 4), (key2556, 4), (key2421, -2), (key2429, -2), (key2421, -2), (key2550, -2), (key2429, -2), (key2550, -2), (key2428, -2), (key2442, -2), (key2428, -2), (key2556, -2), (key2442, -2), (key2556, -2), (key2429, 4), (key2429, 4), (key2550, 4)]

theorem rawRowCheck17995 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form0 = rawRow17995 := by decide +kernel

def row17995 : Integer.Sparse Key := [(key2421, -4), (key2428, 4), (key2429, 4), (key2442, -4)]

theorem rowCheck17995 : row17995 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17995 := by decide +kernel

theorem rowEval17995 (x : Key → ℝ) : Integer.Sparse.eval row17995 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17995, Integer.Sparse.eval_collectBalanced, rawRowCheck17995]

def rawRow17996 : Integer.Sparse Key := [(key2428, 4), (key2556, 4), (key2428, 4), (key2429, -2), (key2421, -2), (key2550, -2), (key2421, -2), (key2550, -2), (key2429, -2), (key2442, -2), (key2428, -2), (key2556, -2), (key2428, -2), (key2556, -2), (key2442, -2), (key2429, 4), (key2550, 4), (key2429, 4)]

theorem rawRowCheck17996 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form0 = rawRow17996 := by decide +kernel

def row17996 : Integer.Sparse Key := [(key2421, -4), (key2428, 4), (key2429, 4), (key2442, -4)]

theorem rowCheck17996 : row17996 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17996 := by decide +kernel

theorem rowEval17996 (x : Key → ℝ) : Integer.Sparse.eval row17996 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17996, Integer.Sparse.eval_collectBalanced, rawRowCheck17996]

def rawRow17997 : Integer.Sparse Key := [(key2556, 4), (key2428, 4), (key2428, 4), (key2550, -2), (key2550, -2), (key2429, -2), (key2429, -2), (key2421, -2), (key2421, -2), (key2556, -2), (key2556, -2), (key2442, -2), (key2442, -2), (key2428, -2), (key2428, -2), (key2550, 4), (key2429, 4), (key2429, 4)]

theorem rawRowCheck17997 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form0 = rawRow17997 := by decide +kernel

def row17997 : Integer.Sparse Key := [(key2421, -4), (key2428, 4), (key2429, 4), (key2442, -4)]

theorem rowCheck17997 : row17997 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17997 := by decide +kernel

theorem rowEval17997 (x : Key → ℝ) : Integer.Sparse.eval row17997 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17997, Integer.Sparse.eval_collectBalanced, rawRowCheck17997]

def rawRow17998 : Integer.Sparse Key := [(key2429, 4), (key2429, 4), (key2508, 4), (key2421, -2), (key2428, -2), (key2421, -2), (key2496, -2), (key2428, -2), (key2496, -2), (key2429, -2), (key2442, -2), (key2429, -2), (key2508, -2), (key2442, -2), (key2508, -2), (key2428, 4), (key2428, 4), (key2496, 4)]

theorem rawRowCheck17998 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form0 = rawRow17998 := by decide +kernel

def row17998 : Integer.Sparse Key := [(key2421, -4), (key2428, 4), (key2429, 4), (key2442, -4)]

theorem rowCheck17998 : row17998 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17998 := by decide +kernel

theorem rowEval17998 (x : Key → ℝ) : Integer.Sparse.eval row17998 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17998, Integer.Sparse.eval_collectBalanced, rawRowCheck17998]

def rawRow17999 : Integer.Sparse Key := [(key2429, 4), (key2508, 4), (key2429, 4), (key2428, -2), (key2421, -2), (key2496, -2), (key2421, -2), (key2496, -2), (key2428, -2), (key2442, -2), (key2429, -2), (key2508, -2), (key2429, -2), (key2508, -2), (key2442, -2), (key2428, 4), (key2496, 4), (key2428, 4)]

theorem rawRowCheck17999 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form0 = rawRow17999 := by decide +kernel

def row17999 : Integer.Sparse Key := [(key2421, -4), (key2428, 4), (key2429, 4), (key2442, -4)]

theorem rowCheck17999 : row17999 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17999 := by decide +kernel

theorem rowEval17999 (x : Key → ℝ) : Integer.Sparse.eval row17999 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17999, Integer.Sparse.eval_collectBalanced, rawRowCheck17999]

def rawRow18000 : Integer.Sparse Key := [(key2508, 4), (key2429, 4), (key2429, 4), (key2496, -2), (key2496, -2), (key2428, -2), (key2428, -2), (key2421, -2), (key2421, -2), (key2508, -2), (key2508, -2), (key2442, -2), (key2442, -2), (key2429, -2), (key2429, -2), (key2496, 4), (key2428, 4), (key2428, 4)]

theorem rawRowCheck18000 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form0 = rawRow18000 := by decide +kernel

def row18000 : Integer.Sparse Key := [(key2421, -4), (key2428, 4), (key2429, 4), (key2442, -4)]

theorem rowCheck18000 : row18000 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18000 := by decide +kernel

theorem rowEval18000 (x : Key → ℝ) : Integer.Sparse.eval row18000 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck18000, Integer.Sparse.eval_collectBalanced, rawRowCheck18000]

def rawRow18001 : Integer.Sparse Key := [(key2428, 4), (key2428, 4), (key2556, 4), (key2428, -2), (key2442, -2), (key2428, -2), (key2556, -2), (key2442, -2), (key2556, -2), (key2421, -2), (key2429, -2), (key2421, -2), (key2550, -2), (key2429, -2), (key2550, -2), (key2429, 4), (key2429, 4), (key2550, 4)]

theorem rawRowCheck18001 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form0 = rawRow18001 := by decide +kernel

def row18001 : Integer.Sparse Key := [(key2421, -4), (key2428, 4), (key2429, 4), (key2442, -4)]

theorem rowCheck18001 : row18001 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18001 := by decide +kernel

theorem rowEval18001 (x : Key → ℝ) : Integer.Sparse.eval row18001 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck18001, Integer.Sparse.eval_collectBalanced, rawRowCheck18001]

def rawRow18002 : Integer.Sparse Key := [(key2428, 4), (key2556, 4), (key2428, 4), (key2442, -2), (key2428, -2), (key2556, -2), (key2428, -2), (key2556, -2), (key2442, -2), (key2429, -2), (key2421, -2), (key2550, -2), (key2421, -2), (key2550, -2), (key2429, -2), (key2429, 4), (key2550, 4), (key2429, 4)]

theorem rawRowCheck18002 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form0 = rawRow18002 := by decide +kernel

def row18002 : Integer.Sparse Key := [(key2421, -4), (key2428, 4), (key2429, 4), (key2442, -4)]

theorem rowCheck18002 : row18002 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18002 := by decide +kernel

theorem rowEval18002 (x : Key → ℝ) : Integer.Sparse.eval row18002 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck18002, Integer.Sparse.eval_collectBalanced, rawRowCheck18002]

def rawRow18003 : Integer.Sparse Key := [(key2556, 4), (key2428, 4), (key2428, 4), (key2556, -2), (key2556, -2), (key2442, -2), (key2442, -2), (key2428, -2), (key2428, -2), (key2550, -2), (key2550, -2), (key2429, -2), (key2429, -2), (key2421, -2), (key2421, -2), (key2550, 4), (key2429, 4), (key2429, 4)]

theorem rawRowCheck18003 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form0 = rawRow18003 := by decide +kernel

def row18003 : Integer.Sparse Key := [(key2421, -4), (key2428, 4), (key2429, 4), (key2442, -4)]

theorem rowCheck18003 : row18003 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18003 := by decide +kernel

theorem rowEval18003 (x : Key → ℝ) : Integer.Sparse.eval row18003 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck18003, Integer.Sparse.eval_collectBalanced, rawRowCheck18003]

def rawRow18004 : Integer.Sparse Key := [(key2442, 4), (key2442, 4), (key2442, 4), (key2428, -2), (key2428, -2), (key2428, -2), (key2428, -2), (key2428, -2), (key2428, -2), (key2429, -2), (key2429, -2), (key2429, -2), (key2429, -2), (key2429, -2), (key2429, -2), (key2421, 4), (key2421, 4), (key2421, 4)]

theorem rawRowCheck18004 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form0 = rawRow18004 := by decide +kernel

def row18004 : Integer.Sparse Key := [(key2421, 12), (key2428, -12), (key2429, -12), (key2442, 12)]

theorem rowCheck18004 : row18004 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18004 := by decide +kernel

theorem rowEval18004 (x : Key → ℝ) : Integer.Sparse.eval row18004 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck18004, Integer.Sparse.eval_collectBalanced, rawRowCheck18004]

def rawRow18005 : Integer.Sparse Key := [(key2429, 4), (key2429, 4), (key2508, 4), (key2429, -2), (key2442, -2), (key2429, -2), (key2508, -2), (key2442, -2), (key2508, -2), (key2421, -2), (key2428, -2), (key2421, -2), (key2496, -2), (key2428, -2), (key2496, -2), (key2428, 4), (key2428, 4), (key2496, 4)]

theorem rawRowCheck18005 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form0 = rawRow18005 := by decide +kernel

def row18005 : Integer.Sparse Key := [(key2421, -4), (key2428, 4), (key2429, 4), (key2442, -4)]

theorem rowCheck18005 : row18005 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18005 := by decide +kernel

theorem rowEval18005 (x : Key → ℝ) : Integer.Sparse.eval row18005 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck18005, Integer.Sparse.eval_collectBalanced, rawRowCheck18005]

def rawRow18006 : Integer.Sparse Key := [(key2429, 4), (key2508, 4), (key2429, 4), (key2442, -2), (key2429, -2), (key2508, -2), (key2429, -2), (key2508, -2), (key2442, -2), (key2428, -2), (key2421, -2), (key2496, -2), (key2421, -2), (key2496, -2), (key2428, -2), (key2428, 4), (key2496, 4), (key2428, 4)]

theorem rawRowCheck18006 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form0 = rawRow18006 := by decide +kernel

def row18006 : Integer.Sparse Key := [(key2421, -4), (key2428, 4), (key2429, 4), (key2442, -4)]

theorem rowCheck18006 : row18006 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18006 := by decide +kernel

theorem rowEval18006 (x : Key → ℝ) : Integer.Sparse.eval row18006 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck18006, Integer.Sparse.eval_collectBalanced, rawRowCheck18006]

def rawRow18007 : Integer.Sparse Key := [(key2508, 4), (key2429, 4), (key2429, 4), (key2508, -2), (key2508, -2), (key2442, -2), (key2442, -2), (key2429, -2), (key2429, -2), (key2496, -2), (key2496, -2), (key2428, -2), (key2428, -2), (key2421, -2), (key2421, -2), (key2496, 4), (key2428, 4), (key2428, 4)]

theorem rawRowCheck18007 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form0 = rawRow18007 := by decide +kernel

def row18007 : Integer.Sparse Key := [(key2421, -4), (key2428, 4), (key2429, 4), (key2442, -4)]

theorem rowCheck18007 : row18007 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18007 := by decide +kernel

theorem rowEval18007 (x : Key → ℝ) : Integer.Sparse.eval row18007 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck18007, Integer.Sparse.eval_collectBalanced, rawRowCheck18007]

def rawRow18008 : Integer.Sparse Key := [(key2442, 4), (key2442, 4), (key2442, 4), (key2429, -2), (key2429, -2), (key2429, -2), (key2429, -2), (key2429, -2), (key2429, -2), (key2428, -2), (key2428, -2), (key2428, -2), (key2428, -2), (key2428, -2), (key2428, -2), (key2421, 4), (key2421, 4), (key2421, 4)]

theorem rawRowCheck18008 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form0 = rawRow18008 := by decide +kernel

def row18008 : Integer.Sparse Key := [(key2421, 12), (key2428, -12), (key2429, -12), (key2442, 12)]

theorem rowCheck18008 : row18008 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18008 := by decide +kernel

theorem rowEval18008 (x : Key → ℝ) : Integer.Sparse.eval row18008 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck18008, Integer.Sparse.eval_collectBalanced, rawRowCheck18008]

def rawRow18009 : Integer.Sparse Key := [(key1049, -2), (key1052, -2), (key1060, -2), (key1060, 6), (key1049, -2), (key1052, -2), (key1060, -2), (key1049, 2), (key1052, 2), (key1135, 2), (key1205, 2), (key1140, 2), (key1207, 2), (key1060, -2), (key1140, -2), (key1207, -2), (key1060, 6), (key1060, -2), (key1140, -2), (key1207, -2)]

theorem rawRowCheck18009 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form1 = rawRow18009 := by decide +kernel

def row18009 : Integer.Sparse Key := [(key1049, -2), (key1052, -2), (key1060, 4), (key1135, 2), (key1140, -2), (key1205, 2), (key1207, -2)]

theorem rowCheck18009 : row18009 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18009 := by decide +kernel

theorem rowEval18009 (x : Key → ℝ) : Integer.Sparse.eval row18009 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18009, Integer.Sparse.eval_collectBalanced, rawRowCheck18009]

def rawRow18010 : Integer.Sparse Key := [(key1052, -2), (key1049, -2), (key1060, -2), (key1060, 6), (key1052, -2), (key1049, -2), (key1060, -2), (key1052, 2), (key1049, 2), (key1205, 2), (key1135, 2), (key1207, 2), (key1140, 2), (key1060, -2), (key1207, -2), (key1140, -2), (key1060, 6), (key1060, -2), (key1207, -2), (key1140, -2)]

theorem rawRowCheck18010 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form1 = rawRow18010 := by decide +kernel

def row18010 : Integer.Sparse Key := [(key1049, -2), (key1052, -2), (key1060, 4), (key1135, 2), (key1140, -2), (key1205, 2), (key1207, -2)]

theorem rowCheck18010 : row18010 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18010 := by decide +kernel

theorem rowEval18010 (x : Key → ℝ) : Integer.Sparse.eval row18010 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck18010, Integer.Sparse.eval_collectBalanced, rawRowCheck18010]

def rawRow18011 : Integer.Sparse Key := [(key1049, -2), (key1060, -2), (key1052, -2), (key1060, 6), (key1049, -2), (key1060, -2), (key1052, -2), (key1135, 2), (key1140, 2), (key1049, 2), (key1207, 2), (key1052, 2), (key1205, 2), (key1140, -2), (key1060, -2), (key1207, -2), (key1060, 6), (key1140, -2), (key1060, -2), (key1207, -2)]

theorem rawRowCheck18011 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form1 = rawRow18011 := by decide +kernel

def row18011 : Integer.Sparse Key := [(key1049, -2), (key1052, -2), (key1060, 4), (key1135, 2), (key1140, -2), (key1205, 2), (key1207, -2)]

theorem rowCheck18011 : row18011 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18011 := by decide +kernel

theorem rowEval18011 (x : Key → ℝ) : Integer.Sparse.eval row18011 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18011, Integer.Sparse.eval_collectBalanced, rawRowCheck18011]

def rawRow18012 : Integer.Sparse Key := [(key1060, -2), (key1049, -2), (key1052, -2), (key1060, 6), (key1060, -2), (key1049, -2), (key1052, -2), (key1140, 2), (key1135, 2), (key1207, 2), (key1049, 2), (key1205, 2), (key1052, 2), (key1140, -2), (key1207, -2), (key1060, -2), (key1060, 6), (key1140, -2), (key1207, -2), (key1060, -2)]

theorem rawRowCheck18012 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form1 = rawRow18012 := by decide +kernel

def row18012 : Integer.Sparse Key := [(key1049, -2), (key1052, -2), (key1060, 4), (key1135, 2), (key1140, -2), (key1205, 2), (key1207, -2)]

theorem rowCheck18012 : row18012 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18012 := by decide +kernel

theorem rowEval18012 (x : Key → ℝ) : Integer.Sparse.eval row18012 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18012, Integer.Sparse.eval_collectBalanced, rawRowCheck18012]

def rawRow18013 : Integer.Sparse Key := [(key1052, -2), (key1060, -2), (key1049, -2), (key1060, 6), (key1052, -2), (key1060, -2), (key1049, -2), (key1205, 2), (key1207, 2), (key1052, 2), (key1140, 2), (key1049, 2), (key1135, 2), (key1207, -2), (key1060, -2), (key1140, -2), (key1060, 6), (key1207, -2), (key1060, -2), (key1140, -2)]

theorem rawRowCheck18013 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form1 = rawRow18013 := by decide +kernel

def row18013 : Integer.Sparse Key := [(key1049, -2), (key1052, -2), (key1060, 4), (key1135, 2), (key1140, -2), (key1205, 2), (key1207, -2)]

theorem rowCheck18013 : row18013 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18013 := by decide +kernel

theorem rowEval18013 (x : Key → ℝ) : Integer.Sparse.eval row18013 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck18013, Integer.Sparse.eval_collectBalanced, rawRowCheck18013]

def rawRow18014 : Integer.Sparse Key := [(key1060, -2), (key1052, -2), (key1049, -2), (key1060, 6), (key1060, -2), (key1052, -2), (key1049, -2), (key1207, 2), (key1205, 2), (key1140, 2), (key1052, 2), (key1135, 2), (key1049, 2), (key1207, -2), (key1140, -2), (key1060, -2), (key1060, 6), (key1207, -2), (key1140, -2), (key1060, -2)]

theorem rawRowCheck18014 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form1 = rawRow18014 := by decide +kernel

def row18014 : Integer.Sparse Key := [(key1049, -2), (key1052, -2), (key1060, 4), (key1135, 2), (key1140, -2), (key1205, 2), (key1207, -2)]

theorem rowCheck18014 : row18014 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18014 := by decide +kernel

theorem rowEval18014 (x : Key → ℝ) : Integer.Sparse.eval row18014 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18014, Integer.Sparse.eval_collectBalanced, rawRowCheck18014]

def rawRow18015 : Integer.Sparse Key := [(key1049, -2), (key1060, -2), (key1060, -2), (key1052, 6), (key1135, -2), (key1140, -2), (key1140, -2), (key1049, 2), (key1060, 2), (key1049, 2), (key1207, 2), (key1060, 2), (key1207, 2), (key1052, -2), (key1052, -2), (key1205, -2), (key1140, 6), (key1060, -2), (key1060, -2), (key1207, -2)]

theorem rawRowCheck18015 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form1 = rawRow18015 := by decide +kernel

def row18015 : Integer.Sparse Key := [(key1049, 2), (key1052, 2), (key1060, -4), (key1135, -2), (key1140, 2), (key1205, -2), (key1207, 2)]

theorem rowCheck18015 : row18015 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18015 := by decide +kernel

theorem rowEval18015 (x : Key → ℝ) : Integer.Sparse.eval row18015 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18015, Integer.Sparse.eval_collectBalanced, rawRowCheck18015]

def rawRow18016 : Integer.Sparse Key := [(key1060, -2), (key1049, -2), (key1060, -2), (key1052, 6), (key1140, -2), (key1135, -2), (key1140, -2), (key1060, 2), (key1049, 2), (key1207, 2), (key1049, 2), (key1207, 2), (key1060, 2), (key1052, -2), (key1205, -2), (key1052, -2), (key1140, 6), (key1060, -2), (key1207, -2), (key1060, -2)]

theorem rawRowCheck18016 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form1 = rawRow18016 := by decide +kernel

def row18016 : Integer.Sparse Key := [(key1049, 2), (key1052, 2), (key1060, -4), (key1135, -2), (key1140, 2), (key1205, -2), (key1207, 2)]

theorem rowCheck18016 : row18016 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18016 := by decide +kernel

theorem rowEval18016 (x : Key → ℝ) : Integer.Sparse.eval row18016 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18016, Integer.Sparse.eval_collectBalanced, rawRowCheck18016]

def rawRow18017 : Integer.Sparse Key := [(key1060, -2), (key1060, -2), (key1049, -2), (key1052, 6), (key1140, -2), (key1140, -2), (key1135, -2), (key1207, 2), (key1207, 2), (key1060, 2), (key1060, 2), (key1049, 2), (key1049, 2), (key1205, -2), (key1052, -2), (key1052, -2), (key1140, 6), (key1207, -2), (key1060, -2), (key1060, -2)]

theorem rawRowCheck18017 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form1 = rawRow18017 := by decide +kernel

def row18017 : Integer.Sparse Key := [(key1049, 2), (key1052, 2), (key1060, -4), (key1135, -2), (key1140, 2), (key1205, -2), (key1207, 2)]

theorem rowCheck18017 : row18017 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18017 := by decide +kernel

theorem rowEval18017 (x : Key → ℝ) : Integer.Sparse.eval row18017 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18017, Integer.Sparse.eval_collectBalanced, rawRowCheck18017]

def rawRow18018 : Integer.Sparse Key := [(key1052, -2), (key1060, -2), (key1060, -2), (key1049, 6), (key1205, -2), (key1207, -2), (key1207, -2), (key1052, 2), (key1060, 2), (key1052, 2), (key1140, 2), (key1060, 2), (key1140, 2), (key1049, -2), (key1049, -2), (key1135, -2), (key1207, 6), (key1060, -2), (key1060, -2), (key1140, -2)]

theorem rawRowCheck18018 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form1 = rawRow18018 := by decide +kernel

def row18018 : Integer.Sparse Key := [(key1049, 2), (key1052, 2), (key1060, -4), (key1135, -2), (key1140, 2), (key1205, -2), (key1207, 2)]

theorem rowCheck18018 : row18018 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18018 := by decide +kernel

theorem rowEval18018 (x : Key → ℝ) : Integer.Sparse.eval row18018 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck18018, Integer.Sparse.eval_collectBalanced, rawRowCheck18018]

def rawRow18019 : Integer.Sparse Key := [(key1060, -2), (key1052, -2), (key1060, -2), (key1049, 6), (key1207, -2), (key1205, -2), (key1207, -2), (key1060, 2), (key1052, 2), (key1140, 2), (key1052, 2), (key1140, 2), (key1060, 2), (key1049, -2), (key1135, -2), (key1049, -2), (key1207, 6), (key1060, -2), (key1140, -2), (key1060, -2)]

theorem rawRowCheck18019 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form1 = rawRow18019 := by decide +kernel

def row18019 : Integer.Sparse Key := [(key1049, 2), (key1052, 2), (key1060, -4), (key1135, -2), (key1140, 2), (key1205, -2), (key1207, 2)]

theorem rowCheck18019 : row18019 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18019 := by decide +kernel

theorem rowEval18019 (x : Key → ℝ) : Integer.Sparse.eval row18019 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18019, Integer.Sparse.eval_collectBalanced, rawRowCheck18019]

def rawRow18020 : Integer.Sparse Key := [(key1060, -2), (key1060, -2), (key1052, -2), (key1049, 6), (key1207, -2), (key1207, -2), (key1205, -2), (key1140, 2), (key1140, 2), (key1060, 2), (key1060, 2), (key1052, 2), (key1052, 2), (key1135, -2), (key1049, -2), (key1049, -2), (key1207, 6), (key1140, -2), (key1060, -2), (key1060, -2)]

theorem rawRowCheck18020 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form1 = rawRow18020 := by decide +kernel

def row18020 : Integer.Sparse Key := [(key1049, 2), (key1052, 2), (key1060, -4), (key1135, -2), (key1140, 2), (key1205, -2), (key1207, 2)]

theorem rowCheck18020 : row18020 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18020 := by decide +kernel

theorem rowEval18020 (x : Key → ℝ) : Integer.Sparse.eval row18020 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18020, Integer.Sparse.eval_collectBalanced, rawRowCheck18020]

def rawRow18021 : Integer.Sparse Key := [(key1135, -2), (key1140, -2), (key1140, -2), (key1140, 6), (key1049, -2), (key1060, -2), (key1060, -2), (key1049, 2), (key1060, 2), (key1049, 2), (key1207, 2), (key1060, 2), (key1207, 2), (key1060, -2), (key1060, -2), (key1207, -2), (key1052, 6), (key1052, -2), (key1052, -2), (key1205, -2)]

theorem rawRowCheck18021 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form1 = rawRow18021 := by decide +kernel

def row18021 : Integer.Sparse Key := [(key1049, 2), (key1052, 2), (key1060, -4), (key1135, -2), (key1140, 2), (key1205, -2), (key1207, 2)]

theorem rowCheck18021 : row18021 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18021 := by decide +kernel

theorem rowEval18021 (x : Key → ℝ) : Integer.Sparse.eval row18021 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18021, Integer.Sparse.eval_collectBalanced, rawRowCheck18021]

def rawRow18022 : Integer.Sparse Key := [(key1140, -2), (key1135, -2), (key1140, -2), (key1140, 6), (key1060, -2), (key1049, -2), (key1060, -2), (key1060, 2), (key1049, 2), (key1207, 2), (key1049, 2), (key1207, 2), (key1060, 2), (key1060, -2), (key1207, -2), (key1060, -2), (key1052, 6), (key1052, -2), (key1205, -2), (key1052, -2)]

theorem rawRowCheck18022 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form1 = rawRow18022 := by decide +kernel

def row18022 : Integer.Sparse Key := [(key1049, 2), (key1052, 2), (key1060, -4), (key1135, -2), (key1140, 2), (key1205, -2), (key1207, 2)]

theorem rowCheck18022 : row18022 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18022 := by decide +kernel

theorem rowEval18022 (x : Key → ℝ) : Integer.Sparse.eval row18022 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18022, Integer.Sparse.eval_collectBalanced, rawRowCheck18022]

def rawRow18023 : Integer.Sparse Key := [(key1140, -2), (key1140, -2), (key1135, -2), (key1140, 6), (key1060, -2), (key1060, -2), (key1049, -2), (key1207, 2), (key1207, 2), (key1060, 2), (key1060, 2), (key1049, 2), (key1049, 2), (key1207, -2), (key1060, -2), (key1060, -2), (key1052, 6), (key1205, -2), (key1052, -2), (key1052, -2)]

theorem rawRowCheck18023 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form1 = rawRow18023 := by decide +kernel

def row18023 : Integer.Sparse Key := [(key1049, 2), (key1052, 2), (key1060, -4), (key1135, -2), (key1140, 2), (key1205, -2), (key1207, 2)]

theorem rowCheck18023 : row18023 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18023 := by decide +kernel

theorem rowEval18023 (x : Key → ℝ) : Integer.Sparse.eval row18023 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18023, Integer.Sparse.eval_collectBalanced, rawRowCheck18023]

def rawRow18024 : Integer.Sparse Key := [(key1140, -2), (key1140, -2), (key1140, -2), (key1135, 6), (key1207, -2), (key1207, -2), (key1207, -2), (key1060, 2), (key1060, 2), (key1060, 2), (key1060, 2), (key1060, 2), (key1060, 2), (key1049, -2), (key1049, -2), (key1049, -2), (key1205, 6), (key1052, -2), (key1052, -2), (key1052, -2)]

theorem rawRowCheck18024 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form1 = rawRow18024 := by decide +kernel

def row18024 : Integer.Sparse Key := [(key1049, -6), (key1052, -6), (key1060, 12), (key1135, 6), (key1140, -6), (key1205, 6), (key1207, -6)]

theorem rowCheck18024 : row18024 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18024 := by decide +kernel

theorem rowEval18024 (x : Key → ℝ) : Integer.Sparse.eval row18024 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18024, Integer.Sparse.eval_collectBalanced, rawRowCheck18024]

def rawRow18025 : Integer.Sparse Key := [(key1205, -2), (key1207, -2), (key1207, -2), (key1207, 6), (key1052, -2), (key1060, -2), (key1060, -2), (key1052, 2), (key1060, 2), (key1052, 2), (key1140, 2), (key1060, 2), (key1140, 2), (key1060, -2), (key1060, -2), (key1140, -2), (key1049, 6), (key1049, -2), (key1049, -2), (key1135, -2)]

theorem rawRowCheck18025 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form1 = rawRow18025 := by decide +kernel

def row18025 : Integer.Sparse Key := [(key1049, 2), (key1052, 2), (key1060, -4), (key1135, -2), (key1140, 2), (key1205, -2), (key1207, 2)]

theorem rowCheck18025 : row18025 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18025 := by decide +kernel

theorem rowEval18025 (x : Key → ℝ) : Integer.Sparse.eval row18025 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck18025, Integer.Sparse.eval_collectBalanced, rawRowCheck18025]

def rawRow18026 : Integer.Sparse Key := [(key1207, -2), (key1205, -2), (key1207, -2), (key1207, 6), (key1060, -2), (key1052, -2), (key1060, -2), (key1060, 2), (key1052, 2), (key1140, 2), (key1052, 2), (key1140, 2), (key1060, 2), (key1060, -2), (key1140, -2), (key1060, -2), (key1049, 6), (key1049, -2), (key1135, -2), (key1049, -2)]

theorem rawRowCheck18026 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form1 = rawRow18026 := by decide +kernel

def row18026 : Integer.Sparse Key := [(key1049, 2), (key1052, 2), (key1060, -4), (key1135, -2), (key1140, 2), (key1205, -2), (key1207, 2)]

theorem rowCheck18026 : row18026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18026 := by decide +kernel

theorem rowEval18026 (x : Key → ℝ) : Integer.Sparse.eval row18026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18026, Integer.Sparse.eval_collectBalanced, rawRowCheck18026]

def rawRow18027 : Integer.Sparse Key := [(key1207, -2), (key1207, -2), (key1205, -2), (key1207, 6), (key1060, -2), (key1060, -2), (key1052, -2), (key1140, 2), (key1140, 2), (key1060, 2), (key1060, 2), (key1052, 2), (key1052, 2), (key1140, -2), (key1060, -2), (key1060, -2), (key1049, 6), (key1135, -2), (key1049, -2), (key1049, -2)]

theorem rawRowCheck18027 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form1 = rawRow18027 := by decide +kernel

def row18027 : Integer.Sparse Key := [(key1049, 2), (key1052, 2), (key1060, -4), (key1135, -2), (key1140, 2), (key1205, -2), (key1207, 2)]

theorem rowCheck18027 : row18027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18027 := by decide +kernel

theorem rowEval18027 (x : Key → ℝ) : Integer.Sparse.eval row18027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18027, Integer.Sparse.eval_collectBalanced, rawRowCheck18027]

def rawRow18028 : Integer.Sparse Key := [(key1207, -2), (key1207, -2), (key1207, -2), (key1205, 6), (key1140, -2), (key1140, -2), (key1140, -2), (key1060, 2), (key1060, 2), (key1060, 2), (key1060, 2), (key1060, 2), (key1060, 2), (key1052, -2), (key1052, -2), (key1052, -2), (key1135, 6), (key1049, -2), (key1049, -2), (key1049, -2)]

theorem rawRowCheck18028 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form1 = rawRow18028 := by decide +kernel

def row18028 : Integer.Sparse Key := [(key1049, -6), (key1052, -6), (key1060, 12), (key1135, 6), (key1140, -6), (key1205, 6), (key1207, -6)]

theorem rowCheck18028 : row18028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18028 := by decide +kernel

theorem rowEval18028 (x : Key → ℝ) : Integer.Sparse.eval row18028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck18028, Integer.Sparse.eval_collectBalanced, rawRowCheck18028]

def rawRow18029 : Integer.Sparse Key := [(key2415, -2), (key2418, -2), (key2425, -2), (key2425, 6), (key2415, -2), (key2418, -2), (key2425, -2), (key2415, 2), (key2418, 2), (key2488, 2), (key2547, 2), (key2493, 2), (key2549, 2), (key2425, -2), (key2493, -2), (key2549, -2), (key2425, 6), (key2425, -2), (key2493, -2), (key2549, -2)]

theorem rawRowCheck18029 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form2 = rawRow18029 := by decide +kernel

def row18029 : Integer.Sparse Key := [(key2415, -2), (key2418, -2), (key2425, 4), (key2488, 2), (key2493, -2), (key2547, 2), (key2549, -2)]

theorem rowCheck18029 : row18029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18029 := by decide +kernel

theorem rowEval18029 (x : Key → ℝ) : Integer.Sparse.eval row18029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18029, Integer.Sparse.eval_collectBalanced, rawRowCheck18029]

def rawRow18030 : Integer.Sparse Key := [(key2418, -2), (key2415, -2), (key2425, -2), (key2425, 6), (key2418, -2), (key2415, -2), (key2425, -2), (key2418, 2), (key2415, 2), (key2547, 2), (key2488, 2), (key2549, 2), (key2493, 2), (key2425, -2), (key2549, -2), (key2493, -2), (key2425, 6), (key2425, -2), (key2549, -2), (key2493, -2)]

theorem rawRowCheck18030 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form2 = rawRow18030 := by decide +kernel

def row18030 : Integer.Sparse Key := [(key2415, -2), (key2418, -2), (key2425, 4), (key2488, 2), (key2493, -2), (key2547, 2), (key2549, -2)]

theorem rowCheck18030 : row18030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18030 := by decide +kernel

theorem rowEval18030 (x : Key → ℝ) : Integer.Sparse.eval row18030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck18030, Integer.Sparse.eval_collectBalanced, rawRowCheck18030]

def rawRow18031 : Integer.Sparse Key := [(key2415, -2), (key2425, -2), (key2418, -2), (key2425, 6), (key2415, -2), (key2425, -2), (key2418, -2), (key2488, 2), (key2493, 2), (key2415, 2), (key2549, 2), (key2418, 2), (key2547, 2), (key2493, -2), (key2425, -2), (key2549, -2), (key2425, 6), (key2493, -2), (key2425, -2), (key2549, -2)]

theorem rawRowCheck18031 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form2 = rawRow18031 := by decide +kernel

def row18031 : Integer.Sparse Key := [(key2415, -2), (key2418, -2), (key2425, 4), (key2488, 2), (key2493, -2), (key2547, 2), (key2549, -2)]

theorem rowCheck18031 : row18031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18031 := by decide +kernel

theorem rowEval18031 (x : Key → ℝ) : Integer.Sparse.eval row18031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18031, Integer.Sparse.eval_collectBalanced, rawRowCheck18031]

def rawRow18032 : Integer.Sparse Key := [(key2425, -2), (key2415, -2), (key2418, -2), (key2425, 6), (key2425, -2), (key2415, -2), (key2418, -2), (key2493, 2), (key2488, 2), (key2549, 2), (key2415, 2), (key2547, 2), (key2418, 2), (key2493, -2), (key2549, -2), (key2425, -2), (key2425, 6), (key2493, -2), (key2549, -2), (key2425, -2)]

theorem rawRowCheck18032 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form2 = rawRow18032 := by decide +kernel

def row18032 : Integer.Sparse Key := [(key2415, -2), (key2418, -2), (key2425, 4), (key2488, 2), (key2493, -2), (key2547, 2), (key2549, -2)]

theorem rowCheck18032 : row18032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18032 := by decide +kernel

theorem rowEval18032 (x : Key → ℝ) : Integer.Sparse.eval row18032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18032, Integer.Sparse.eval_collectBalanced, rawRowCheck18032]

def rawRow18033 : Integer.Sparse Key := [(key2418, -2), (key2425, -2), (key2415, -2), (key2425, 6), (key2418, -2), (key2425, -2), (key2415, -2), (key2547, 2), (key2549, 2), (key2418, 2), (key2493, 2), (key2415, 2), (key2488, 2), (key2549, -2), (key2425, -2), (key2493, -2), (key2425, 6), (key2549, -2), (key2425, -2), (key2493, -2)]

theorem rawRowCheck18033 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form2 = rawRow18033 := by decide +kernel

def row18033 : Integer.Sparse Key := [(key2415, -2), (key2418, -2), (key2425, 4), (key2488, 2), (key2493, -2), (key2547, 2), (key2549, -2)]

theorem rowCheck18033 : row18033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18033 := by decide +kernel

theorem rowEval18033 (x : Key → ℝ) : Integer.Sparse.eval row18033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck18033, Integer.Sparse.eval_collectBalanced, rawRowCheck18033]

def rawRow18034 : Integer.Sparse Key := [(key2425, -2), (key2418, -2), (key2415, -2), (key2425, 6), (key2425, -2), (key2418, -2), (key2415, -2), (key2549, 2), (key2547, 2), (key2493, 2), (key2418, 2), (key2488, 2), (key2415, 2), (key2549, -2), (key2493, -2), (key2425, -2), (key2425, 6), (key2549, -2), (key2493, -2), (key2425, -2)]

theorem rawRowCheck18034 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form2 = rawRow18034 := by decide +kernel

def row18034 : Integer.Sparse Key := [(key2415, -2), (key2418, -2), (key2425, 4), (key2488, 2), (key2493, -2), (key2547, 2), (key2549, -2)]

theorem rowCheck18034 : row18034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18034 := by decide +kernel

theorem rowEval18034 (x : Key → ℝ) : Integer.Sparse.eval row18034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18034, Integer.Sparse.eval_collectBalanced, rawRowCheck18034]

def rawRow18035 : Integer.Sparse Key := [(key2415, -2), (key2425, -2), (key2425, -2), (key2418, 6), (key2488, -2), (key2493, -2), (key2493, -2), (key2415, 2), (key2425, 2), (key2415, 2), (key2549, 2), (key2425, 2), (key2549, 2), (key2418, -2), (key2418, -2), (key2547, -2), (key2493, 6), (key2425, -2), (key2425, -2), (key2549, -2)]

theorem rawRowCheck18035 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form2 = rawRow18035 := by decide +kernel

def row18035 : Integer.Sparse Key := [(key2415, 2), (key2418, 2), (key2425, -4), (key2488, -2), (key2493, 2), (key2547, -2), (key2549, 2)]

theorem rowCheck18035 : row18035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18035 := by decide +kernel

theorem rowEval18035 (x : Key → ℝ) : Integer.Sparse.eval row18035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18035, Integer.Sparse.eval_collectBalanced, rawRowCheck18035]

def rawRow18036 : Integer.Sparse Key := [(key2425, -2), (key2415, -2), (key2425, -2), (key2418, 6), (key2493, -2), (key2488, -2), (key2493, -2), (key2425, 2), (key2415, 2), (key2549, 2), (key2415, 2), (key2549, 2), (key2425, 2), (key2418, -2), (key2547, -2), (key2418, -2), (key2493, 6), (key2425, -2), (key2549, -2), (key2425, -2)]

theorem rawRowCheck18036 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form2 = rawRow18036 := by decide +kernel

def row18036 : Integer.Sparse Key := [(key2415, 2), (key2418, 2), (key2425, -4), (key2488, -2), (key2493, 2), (key2547, -2), (key2549, 2)]

theorem rowCheck18036 : row18036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18036 := by decide +kernel

theorem rowEval18036 (x : Key → ℝ) : Integer.Sparse.eval row18036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18036, Integer.Sparse.eval_collectBalanced, rawRowCheck18036]

def rawRow18037 : Integer.Sparse Key := [(key2425, -2), (key2425, -2), (key2415, -2), (key2418, 6), (key2493, -2), (key2493, -2), (key2488, -2), (key2549, 2), (key2549, 2), (key2425, 2), (key2425, 2), (key2415, 2), (key2415, 2), (key2547, -2), (key2418, -2), (key2418, -2), (key2493, 6), (key2549, -2), (key2425, -2), (key2425, -2)]

theorem rawRowCheck18037 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form2 = rawRow18037 := by decide +kernel

def row18037 : Integer.Sparse Key := [(key2415, 2), (key2418, 2), (key2425, -4), (key2488, -2), (key2493, 2), (key2547, -2), (key2549, 2)]

theorem rowCheck18037 : row18037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18037 := by decide +kernel

theorem rowEval18037 (x : Key → ℝ) : Integer.Sparse.eval row18037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18037, Integer.Sparse.eval_collectBalanced, rawRowCheck18037]

def rawRow18038 : Integer.Sparse Key := [(key2418, -2), (key2425, -2), (key2425, -2), (key2415, 6), (key2547, -2), (key2549, -2), (key2549, -2), (key2418, 2), (key2425, 2), (key2418, 2), (key2493, 2), (key2425, 2), (key2493, 2), (key2415, -2), (key2415, -2), (key2488, -2), (key2549, 6), (key2425, -2), (key2425, -2), (key2493, -2)]

theorem rawRowCheck18038 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form2 = rawRow18038 := by decide +kernel

def row18038 : Integer.Sparse Key := [(key2415, 2), (key2418, 2), (key2425, -4), (key2488, -2), (key2493, 2), (key2547, -2), (key2549, 2)]

theorem rowCheck18038 : row18038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18038 := by decide +kernel

theorem rowEval18038 (x : Key → ℝ) : Integer.Sparse.eval row18038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck18038, Integer.Sparse.eval_collectBalanced, rawRowCheck18038]

def rawRow18039 : Integer.Sparse Key := [(key2425, -2), (key2418, -2), (key2425, -2), (key2415, 6), (key2549, -2), (key2547, -2), (key2549, -2), (key2425, 2), (key2418, 2), (key2493, 2), (key2418, 2), (key2493, 2), (key2425, 2), (key2415, -2), (key2488, -2), (key2415, -2), (key2549, 6), (key2425, -2), (key2493, -2), (key2425, -2)]

theorem rawRowCheck18039 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form2 = rawRow18039 := by decide +kernel

def row18039 : Integer.Sparse Key := [(key2415, 2), (key2418, 2), (key2425, -4), (key2488, -2), (key2493, 2), (key2547, -2), (key2549, 2)]

theorem rowCheck18039 : row18039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18039 := by decide +kernel

theorem rowEval18039 (x : Key → ℝ) : Integer.Sparse.eval row18039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18039, Integer.Sparse.eval_collectBalanced, rawRowCheck18039]

def rawRow18040 : Integer.Sparse Key := [(key2425, -2), (key2425, -2), (key2418, -2), (key2415, 6), (key2549, -2), (key2549, -2), (key2547, -2), (key2493, 2), (key2493, 2), (key2425, 2), (key2425, 2), (key2418, 2), (key2418, 2), (key2488, -2), (key2415, -2), (key2415, -2), (key2549, 6), (key2493, -2), (key2425, -2), (key2425, -2)]

theorem rawRowCheck18040 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form2 = rawRow18040 := by decide +kernel

def row18040 : Integer.Sparse Key := [(key2415, 2), (key2418, 2), (key2425, -4), (key2488, -2), (key2493, 2), (key2547, -2), (key2549, 2)]

theorem rowCheck18040 : row18040 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18040 := by decide +kernel

theorem rowEval18040 (x : Key → ℝ) : Integer.Sparse.eval row18040 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18040, Integer.Sparse.eval_collectBalanced, rawRowCheck18040]

def rawRow18041 : Integer.Sparse Key := [(key2488, -2), (key2493, -2), (key2493, -2), (key2493, 6), (key2415, -2), (key2425, -2), (key2425, -2), (key2415, 2), (key2425, 2), (key2415, 2), (key2549, 2), (key2425, 2), (key2549, 2), (key2425, -2), (key2425, -2), (key2549, -2), (key2418, 6), (key2418, -2), (key2418, -2), (key2547, -2)]

theorem rawRowCheck18041 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form2 = rawRow18041 := by decide +kernel

def row18041 : Integer.Sparse Key := [(key2415, 2), (key2418, 2), (key2425, -4), (key2488, -2), (key2493, 2), (key2547, -2), (key2549, 2)]

theorem rowCheck18041 : row18041 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18041 := by decide +kernel

theorem rowEval18041 (x : Key → ℝ) : Integer.Sparse.eval row18041 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18041, Integer.Sparse.eval_collectBalanced, rawRowCheck18041]

def rawRow18042 : Integer.Sparse Key := [(key2493, -2), (key2488, -2), (key2493, -2), (key2493, 6), (key2425, -2), (key2415, -2), (key2425, -2), (key2425, 2), (key2415, 2), (key2549, 2), (key2415, 2), (key2549, 2), (key2425, 2), (key2425, -2), (key2549, -2), (key2425, -2), (key2418, 6), (key2418, -2), (key2547, -2), (key2418, -2)]

theorem rawRowCheck18042 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form2 = rawRow18042 := by decide +kernel

def row18042 : Integer.Sparse Key := [(key2415, 2), (key2418, 2), (key2425, -4), (key2488, -2), (key2493, 2), (key2547, -2), (key2549, 2)]

theorem rowCheck18042 : row18042 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18042 := by decide +kernel

theorem rowEval18042 (x : Key → ℝ) : Integer.Sparse.eval row18042 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18042, Integer.Sparse.eval_collectBalanced, rawRowCheck18042]

def rawRow18043 : Integer.Sparse Key := [(key2493, -2), (key2493, -2), (key2488, -2), (key2493, 6), (key2425, -2), (key2425, -2), (key2415, -2), (key2549, 2), (key2549, 2), (key2425, 2), (key2425, 2), (key2415, 2), (key2415, 2), (key2549, -2), (key2425, -2), (key2425, -2), (key2418, 6), (key2547, -2), (key2418, -2), (key2418, -2)]

theorem rawRowCheck18043 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form2 = rawRow18043 := by decide +kernel

def row18043 : Integer.Sparse Key := [(key2415, 2), (key2418, 2), (key2425, -4), (key2488, -2), (key2493, 2), (key2547, -2), (key2549, 2)]

theorem rowCheck18043 : row18043 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18043 := by decide +kernel

theorem rowEval18043 (x : Key → ℝ) : Integer.Sparse.eval row18043 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18043, Integer.Sparse.eval_collectBalanced, rawRowCheck18043]

def rawRow18044 : Integer.Sparse Key := [(key2493, -2), (key2493, -2), (key2493, -2), (key2488, 6), (key2549, -2), (key2549, -2), (key2549, -2), (key2425, 2), (key2425, 2), (key2425, 2), (key2425, 2), (key2425, 2), (key2425, 2), (key2415, -2), (key2415, -2), (key2415, -2), (key2547, 6), (key2418, -2), (key2418, -2), (key2418, -2)]

theorem rawRowCheck18044 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form2 = rawRow18044 := by decide +kernel

def row18044 : Integer.Sparse Key := [(key2415, -6), (key2418, -6), (key2425, 12), (key2488, 6), (key2493, -6), (key2547, 6), (key2549, -6)]

theorem rowCheck18044 : row18044 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18044 := by decide +kernel

theorem rowEval18044 (x : Key → ℝ) : Integer.Sparse.eval row18044 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18044, Integer.Sparse.eval_collectBalanced, rawRowCheck18044]

def rawRow18045 : Integer.Sparse Key := [(key2547, -2), (key2549, -2), (key2549, -2), (key2549, 6), (key2418, -2), (key2425, -2), (key2425, -2), (key2418, 2), (key2425, 2), (key2418, 2), (key2493, 2), (key2425, 2), (key2493, 2), (key2425, -2), (key2425, -2), (key2493, -2), (key2415, 6), (key2415, -2), (key2415, -2), (key2488, -2)]

theorem rawRowCheck18045 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form2 = rawRow18045 := by decide +kernel

def row18045 : Integer.Sparse Key := [(key2415, 2), (key2418, 2), (key2425, -4), (key2488, -2), (key2493, 2), (key2547, -2), (key2549, 2)]

theorem rowCheck18045 : row18045 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18045 := by decide +kernel

theorem rowEval18045 (x : Key → ℝ) : Integer.Sparse.eval row18045 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck18045, Integer.Sparse.eval_collectBalanced, rawRowCheck18045]

def rawRow18046 : Integer.Sparse Key := [(key2549, -2), (key2547, -2), (key2549, -2), (key2549, 6), (key2425, -2), (key2418, -2), (key2425, -2), (key2425, 2), (key2418, 2), (key2493, 2), (key2418, 2), (key2493, 2), (key2425, 2), (key2425, -2), (key2493, -2), (key2425, -2), (key2415, 6), (key2415, -2), (key2488, -2), (key2415, -2)]

theorem rawRowCheck18046 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form2 = rawRow18046 := by decide +kernel

def row18046 : Integer.Sparse Key := [(key2415, 2), (key2418, 2), (key2425, -4), (key2488, -2), (key2493, 2), (key2547, -2), (key2549, 2)]

theorem rowCheck18046 : row18046 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18046 := by decide +kernel

theorem rowEval18046 (x : Key → ℝ) : Integer.Sparse.eval row18046 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18046, Integer.Sparse.eval_collectBalanced, rawRowCheck18046]

def rawRow18047 : Integer.Sparse Key := [(key2549, -2), (key2549, -2), (key2547, -2), (key2549, 6), (key2425, -2), (key2425, -2), (key2418, -2), (key2493, 2), (key2493, 2), (key2425, 2), (key2425, 2), (key2418, 2), (key2418, 2), (key2493, -2), (key2425, -2), (key2425, -2), (key2415, 6), (key2488, -2), (key2415, -2), (key2415, -2)]

theorem rawRowCheck18047 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form2 = rawRow18047 := by decide +kernel

def row18047 : Integer.Sparse Key := [(key2415, 2), (key2418, 2), (key2425, -4), (key2488, -2), (key2493, 2), (key2547, -2), (key2549, 2)]

theorem rowCheck18047 : row18047 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18047 := by decide +kernel

theorem rowEval18047 (x : Key → ℝ) : Integer.Sparse.eval row18047 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck18047, Integer.Sparse.eval_collectBalanced, rawRowCheck18047]

end MUB6.Certificate.GramRows

end OAI
