import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
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

def rawRow7808 : Integer.Sparse Key := [(key2837, -6), (key2837, -6), (key2581, -6), (key2837, -6), (key2837, 2), (key2760, 2), (key2837, 2), (key2837, 2), (key2581, 2), (key2837, 2), (key2760, 2), (key2837, 2), (key2581, 2), (key2837, 2), (key2368, 2), (key2396, 2)]

theorem rawRowCheck7808 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form3 = rawRow7808 := by decide +kernel

def row7808 : Integer.Sparse Key := [(key2368, 2), (key2396, 2), (key2581, -2), (key2760, 4), (key2837, -6)]

theorem rowCheck7808 : row7808 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7808 := by decide +kernel

theorem rowEval7808 (x : Key → ℝ) : Integer.Sparse.eval row7808 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7808, Integer.Sparse.eval_collectBalanced, rawRowCheck7808]

def rawRow7809 : Integer.Sparse Key := [(key2837, -6), (key2837, -6), (key2837, -6), (key2581, -6), (key2837, 2), (key2837, 2), (key2760, 2), (key2837, 2), (key2837, 2), (key2581, 2), (key2837, 2), (key2760, 2), (key2837, 2), (key2581, 2), (key2760, 2), (key2581, 2)]

theorem rawRowCheck7809 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form3 = rawRow7809 := by decide +kernel

def row7809 : Integer.Sparse Key := [(key2760, 6), (key2837, -6)]

theorem rowCheck7809 : row7809 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7809 := by decide +kernel

theorem rowEval7809 (x : Key → ℝ) : Integer.Sparse.eval row7809 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck7809, Integer.Sparse.eval_collectBalanced, rawRowCheck7809]

def rawRow7810 : Integer.Sparse Key := [(key2355, -6), (key2355, -6), (key2355, -6), (key2355, -6), (key2450, 2), (key2450, 2), (key2450, 2), (key2450, 2), (key2450, 2), (key2450, 2), (key2450, 2), (key2450, 2), (key2450, 2), (key2450, 2), (key2450, 2), (key2450, 2)]

theorem rawRowCheck7810 : GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form4 = rawRow7810 := by decide +kernel

def row7810 : Integer.Sparse Key := [(key2355, -24), (key2450, 24)]

theorem rowCheck7810 : row7810 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7810 := by decide +kernel

theorem rowEval7810 (x : Key → ℝ) : Integer.Sparse.eval row7810 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7810, Integer.Sparse.eval_collectBalanced, rawRowCheck7810]

def rawRow7811 : Integer.Sparse Key := [(key2450, -6), (key2450, -6), (key2450, -6), (key2512, -6), (key2355, 2), (key2355, 2), (key2355, 2), (key2450, 2), (key2450, 2), (key2450, 2), (key2450, 2), (key2450, 2), (key2450, 2), (key2512, 2), (key2512, 2), (key2512, 2)]

theorem rawRowCheck7811 : GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form4 = rawRow7811 := by decide +kernel

def row7811 : Integer.Sparse Key := [(key2355, 6), (key2450, -6)]

theorem rowCheck7811 : row7811 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7811 := by decide +kernel

theorem rowEval7811 (x : Key → ℝ) : Integer.Sparse.eval row7811 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7811, Integer.Sparse.eval_collectBalanced, rawRowCheck7811]

def rawRow7812 : Integer.Sparse Key := [(key2450, -6), (key2450, -6), (key2512, -6), (key2450, -6), (key2450, 2), (key2450, 2), (key2512, 2), (key2355, 2), (key2355, 2), (key2450, 2), (key2450, 2), (key2512, 2), (key2512, 2), (key2355, 2), (key2450, 2), (key2450, 2)]

theorem rawRowCheck7812 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form4 = rawRow7812 := by decide +kernel

def row7812 : Integer.Sparse Key := [(key2355, 6), (key2450, -6)]

theorem rowCheck7812 : row7812 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7812 := by decide +kernel

theorem rowEval7812 (x : Key → ℝ) : Integer.Sparse.eval row7812 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7812, Integer.Sparse.eval_collectBalanced, rawRowCheck7812]

def rawRow7813 : Integer.Sparse Key := [(key2450, -6), (key2512, -6), (key2450, -6), (key2450, -6), (key2450, 2), (key2512, 2), (key2450, 2), (key2450, 2), (key2512, 2), (key2355, 2), (key2512, 2), (key2355, 2), (key2450, 2), (key2450, 2), (key2355, 2), (key2450, 2)]

theorem rawRowCheck7813 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form4 = rawRow7813 := by decide +kernel

def row7813 : Integer.Sparse Key := [(key2355, 6), (key2450, -6)]

theorem rowCheck7813 : row7813 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7813 := by decide +kernel

theorem rowEval7813 (x : Key → ℝ) : Integer.Sparse.eval row7813 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7813, Integer.Sparse.eval_collectBalanced, rawRowCheck7813]

def rawRow7814 : Integer.Sparse Key := [(key2512, -6), (key2450, -6), (key2450, -6), (key2450, -6), (key2512, 2), (key2450, 2), (key2450, 2), (key2512, 2), (key2450, 2), (key2512, 2), (key2355, 2), (key2450, 2), (key2355, 2), (key2450, 2), (key2450, 2), (key2355, 2)]

theorem rawRowCheck7814 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form4 = rawRow7814 := by decide +kernel

def row7814 : Integer.Sparse Key := [(key2355, 6), (key2450, -6)]

theorem rowCheck7814 : row7814 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7814 := by decide +kernel

theorem rowEval7814 (x : Key → ℝ) : Integer.Sparse.eval row7814 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck7814, Integer.Sparse.eval_collectBalanced, rawRowCheck7814]

def rawRow7815 : Integer.Sparse Key := [(key2764, -2), (key2764, -2), (key2764, -2), (key2764, -2), (key2764, -2), (key2764, -2), (key2764, -2), (key2764, -2), (key2764, -2), (key2764, -2), (key2764, -2), (key2764, -2), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1)]

theorem rawRowCheck7815 : GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form5 = rawRow7815 := by decide +kernel

def row7815 : Integer.Sparse Key := [(key2764, -24), (key2841, 24)]

theorem rowCheck7815 : row7815 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7815 := by decide +kernel

theorem rowEval7815 (x : Key → ℝ) : Integer.Sparse.eval row7815 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck7815, Integer.Sparse.eval_collectBalanced, rawRowCheck7815]

def rawRow7816 : Integer.Sparse Key := [(key2585, -2), (key2585, -2), (key2585, -2), (key2841, -2), (key2841, -2), (key2841, -2), (key2841, -2), (key2841, -2), (key2841, -2), (key2873, -2), (key2873, -2), (key2873, -2), (key2585, 1), (key2585, 1), (key2585, 1), (key2585, 1), (key2585, 1), (key2585, 1), (key2764, 1), (key2764, 1), (key2764, 1), (key2764, 1), (key2764, 1), (key2764, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2873, 1), (key2873, 1), (key2873, 1), (key2873, 1), (key2873, 1), (key2873, 1)]

theorem rawRowCheck7816 : GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form5 = rawRow7816 := by decide +kernel

def row7816 : Integer.Sparse Key := [(key2764, 6), (key2841, -6)]

theorem rowCheck7816 : row7816 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7816 := by decide +kernel

theorem rowEval7816 (x : Key → ℝ) : Integer.Sparse.eval row7816 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck7816, Integer.Sparse.eval_collectBalanced, rawRowCheck7816]

def rawRow7817 : Integer.Sparse Key := [(key2841, -2), (key2841, -2), (key2873, -2), (key2585, -2), (key2585, -2), (key2841, -2), (key2841, -2), (key2873, -2), (key2873, -2), (key2585, -2), (key2841, -2), (key2841, -2), (key2764, 1), (key2764, 1), (key2841, 1), (key2841, 1), (key2873, 1), (key2873, 1), (key2585, 1), (key2585, 1), (key2841, 1), (key2841, 1), (key2873, 1), (key2873, 1), (key2585, 1), (key2585, 1), (key2764, 1), (key2764, 1), (key2873, 1), (key2873, 1), (key2585, 1), (key2585, 1), (key2764, 1), (key2764, 1), (key2841, 1), (key2841, 1)]

theorem rawRowCheck7817 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form5 = rawRow7817 := by decide +kernel

def row7817 : Integer.Sparse Key := [(key2764, 6), (key2841, -6)]

theorem rowCheck7817 : row7817 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7817 := by decide +kernel

theorem rowEval7817 (x : Key → ℝ) : Integer.Sparse.eval row7817 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck7817, Integer.Sparse.eval_collectBalanced, rawRowCheck7817]

def rawRow7818 : Integer.Sparse Key := [(key2841, -2), (key2873, -2), (key2841, -2), (key2841, -2), (key2873, -2), (key2585, -2), (key2873, -2), (key2585, -2), (key2841, -2), (key2841, -2), (key2585, -2), (key2841, -2), (key2841, 1), (key2873, 1), (key2764, 1), (key2873, 1), (key2764, 1), (key2841, 1), (key2841, 1), (key2873, 1), (key2585, 1), (key2873, 1), (key2585, 1), (key2841, 1), (key2764, 1), (key2873, 1), (key2585, 1), (key2873, 1), (key2585, 1), (key2764, 1), (key2764, 1), (key2841, 1), (key2585, 1), (key2841, 1), (key2585, 1), (key2764, 1)]

theorem rawRowCheck7818 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form5 = rawRow7818 := by decide +kernel

def row7818 : Integer.Sparse Key := [(key2764, 6), (key2841, -6)]

theorem rowCheck7818 : row7818 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7818 := by decide +kernel

theorem rowEval7818 (x : Key → ℝ) : Integer.Sparse.eval row7818 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck7818, Integer.Sparse.eval_collectBalanced, rawRowCheck7818]

def rawRow7819 : Integer.Sparse Key := [(key2873, -2), (key2841, -2), (key2841, -2), (key2873, -2), (key2841, -2), (key2873, -2), (key2585, -2), (key2841, -2), (key2585, -2), (key2841, -2), (key2841, -2), (key2585, -2), (key2873, 1), (key2841, 1), (key2873, 1), (key2764, 1), (key2841, 1), (key2764, 1), (key2873, 1), (key2841, 1), (key2873, 1), (key2585, 1), (key2841, 1), (key2585, 1), (key2873, 1), (key2764, 1), (key2873, 1), (key2585, 1), (key2764, 1), (key2585, 1), (key2841, 1), (key2764, 1), (key2841, 1), (key2585, 1), (key2764, 1), (key2585, 1)]

theorem rawRowCheck7819 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form5 = rawRow7819 := by decide +kernel

def row7819 : Integer.Sparse Key := [(key2764, 6), (key2841, -6)]

theorem rowCheck7819 : row7819 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7819 := by decide +kernel

theorem rowEval7819 (x : Key → ℝ) : Integer.Sparse.eval row7819 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form5) x := by
  rw [rowCheck7819, Integer.Sparse.eval_collectBalanced, rawRowCheck7819]

def rawRow7820 : Integer.Sparse Key := [(key2351, -24), (key2446, 6), (key2446, 6), (key2446, 6), (key2446, 6)]

theorem rawRowCheck7820 : GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form6 = rawRow7820 := by decide +kernel

def row7820 : Integer.Sparse Key := [(key2351, -24), (key2446, 24)]

theorem rowCheck7820 : row7820 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7820 := by decide +kernel

theorem rowEval7820 (x : Key → ℝ) : Integer.Sparse.eval row7820 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck7820, Integer.Sparse.eval_collectBalanced, rawRowCheck7820]

def rawRow7821 : Integer.Sparse Key := [(key2446, -24), (key2351, 6), (key2446, 6), (key2446, 6), (key2446, 6)]

theorem rawRowCheck7821 : GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form6 = rawRow7821 := by decide +kernel

def row7821 : Integer.Sparse Key := [(key2351, 6), (key2446, -6)]

theorem rowCheck7821 : row7821 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7821 := by decide +kernel

theorem rowEval7821 (x : Key → ℝ) : Integer.Sparse.eval row7821 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck7821, Integer.Sparse.eval_collectBalanced, rawRowCheck7821]

def rawRow7822 : Integer.Sparse Key := [(key2446, -24), (key2446, 6), (key2351, 6), (key2446, 6), (key2446, 6)]

theorem rawRowCheck7822 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form6 = rawRow7822 := by decide +kernel

def row7822 : Integer.Sparse Key := [(key2351, 6), (key2446, -6)]

theorem rowCheck7822 : row7822 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7822 := by decide +kernel

theorem rowEval7822 (x : Key → ℝ) : Integer.Sparse.eval row7822 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck7822, Integer.Sparse.eval_collectBalanced, rawRowCheck7822]

def rawRow7823 : Integer.Sparse Key := [(key2446, -24), (key2446, 6), (key2446, 6), (key2351, 6), (key2446, 6)]

theorem rawRowCheck7823 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form6 = rawRow7823 := by decide +kernel

def row7823 : Integer.Sparse Key := [(key2351, 6), (key2446, -6)]

theorem rowCheck7823 : row7823 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7823 := by decide +kernel

theorem rowEval7823 (x : Key → ℝ) : Integer.Sparse.eval row7823 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck7823, Integer.Sparse.eval_collectBalanced, rawRowCheck7823]

def rawRow7824 : Integer.Sparse Key := [(key2446, -24), (key2446, 6), (key2446, 6), (key2446, 6), (key2351, 6)]

theorem rawRowCheck7824 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form6 = rawRow7824 := by decide +kernel

def row7824 : Integer.Sparse Key := [(key2351, 6), (key2446, -6)]

theorem rowCheck7824 : row7824 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7824 := by decide +kernel

theorem rowEval7824 (x : Key → ℝ) : Integer.Sparse.eval row7824 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form6) x := by
  rw [rowCheck7824, Integer.Sparse.eval_collectBalanced, rawRowCheck7824]

def rawRow7825 : Integer.Sparse Key := [(key2766, 2), (key2766, 2), (key2772, 2), (key2843, 2), (key2843, 2), (key2880, 2), (key2887, 2), (key2889, 2), (key2887, 2), (key2910, 2), (key2889, 2), (key2910, 2), (key2929, -2), (key2931, -2), (key2931, -2), (key2966, -2), (key2968, -2), (key2966, -2), (key2989, -2), (key2968, -2), (key2989, -2), (key2995, -2), (key2995, -2), (key3002, -2)]

theorem rawRowCheck7825 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block3.form0 = rawRow7825 := by decide +kernel

def row7825 : Integer.Sparse Key := [(key2766, 4), (key2772, 2), (key2843, 4), (key2880, 2), (key2887, 4), (key2889, 4), (key2910, 4), (key2929, -2), (key2931, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, -4), (key3002, -2)]

theorem rowCheck7825 : row7825 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7825 := by decide +kernel

theorem rowEval7825 (x : Key → ℝ) : Integer.Sparse.eval row7825 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7825, Integer.Sparse.eval_collectBalanced, rawRowCheck7825]

def rawRow7826 : Integer.Sparse Key := [(key2766, 2), (key2772, 2), (key2766, 2), (key2843, 2), (key2880, 2), (key2843, 2), (key2889, 2), (key2887, 2), (key2910, 2), (key2887, 2), (key2910, 2), (key2889, 2), (key2931, -2), (key2929, -2), (key2931, -2), (key2968, -2), (key2966, -2), (key2989, -2), (key2966, -2), (key2989, -2), (key2968, -2), (key2995, -2), (key3002, -2), (key2995, -2)]

theorem rawRowCheck7826 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block3.form0 = rawRow7826 := by decide +kernel

def row7826 : Integer.Sparse Key := [(key2766, 4), (key2772, 2), (key2843, 4), (key2880, 2), (key2887, 4), (key2889, 4), (key2910, 4), (key2929, -2), (key2931, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, -4), (key3002, -2)]

theorem rowCheck7826 : row7826 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7826 := by decide +kernel

theorem rowEval7826 (x : Key → ℝ) : Integer.Sparse.eval row7826 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7826, Integer.Sparse.eval_collectBalanced, rawRowCheck7826]

def rawRow7827 : Integer.Sparse Key := [(key2772, 2), (key2766, 2), (key2766, 2), (key2880, 2), (key2843, 2), (key2843, 2), (key2910, 2), (key2910, 2), (key2889, 2), (key2889, 2), (key2887, 2), (key2887, 2), (key2931, -2), (key2931, -2), (key2929, -2), (key2989, -2), (key2989, -2), (key2968, -2), (key2968, -2), (key2966, -2), (key2966, -2), (key3002, -2), (key2995, -2), (key2995, -2)]

theorem rawRowCheck7827 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block3.form0 = rawRow7827 := by decide +kernel

def row7827 : Integer.Sparse Key := [(key2766, 4), (key2772, 2), (key2843, 4), (key2880, 2), (key2887, 4), (key2889, 4), (key2910, 4), (key2929, -2), (key2931, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, -4), (key3002, -2)]

theorem rowCheck7827 : row7827 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7827 := by decide +kernel

theorem rowEval7827 (x : Key → ℝ) : Integer.Sparse.eval row7827 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7827, Integer.Sparse.eval_collectBalanced, rawRowCheck7827]

def rawRow7828 : Integer.Sparse Key := [(key2843, 2), (key2887, 2), (key2889, 2), (key2766, 2), (key2887, 2), (key2910, 2), (key2766, 2), (key2772, 2), (key2843, 2), (key2880, 2), (key2889, 2), (key2910, 2), (key2966, -2), (key2968, -2), (key2995, -2), (key2929, -2), (key2931, -2), (key2966, -2), (key2989, -2), (key2995, -2), (key3002, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

theorem rawRowCheck7828 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block3.form0 = rawRow7828 := by decide +kernel

def row7828 : Integer.Sparse Key := [(key2766, 4), (key2772, 2), (key2843, 4), (key2880, 2), (key2887, 4), (key2889, 4), (key2910, 4), (key2929, -2), (key2931, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, -4), (key3002, -2)]

theorem rowCheck7828 : row7828 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7828 := by decide +kernel

theorem rowEval7828 (x : Key → ℝ) : Integer.Sparse.eval row7828 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7828, Integer.Sparse.eval_collectBalanced, rawRowCheck7828]

def rawRow7829 : Integer.Sparse Key := [(key2843, 2), (key2889, 2), (key2887, 2), (key2766, 2), (key2910, 2), (key2887, 2), (key2772, 2), (key2766, 2), (key2880, 2), (key2843, 2), (key2910, 2), (key2889, 2), (key2968, -2), (key2966, -2), (key2995, -2), (key2931, -2), (key2929, -2), (key2989, -2), (key2966, -2), (key3002, -2), (key2995, -2), (key2931, -2), (key2989, -2), (key2968, -2)]

theorem rawRowCheck7829 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block3.form0 = rawRow7829 := by decide +kernel

def row7829 : Integer.Sparse Key := [(key2766, 4), (key2772, 2), (key2843, 4), (key2880, 2), (key2887, 4), (key2889, 4), (key2910, 4), (key2929, -2), (key2931, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, -4), (key3002, -2)]

theorem rowCheck7829 : row7829 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7829 := by decide +kernel

theorem rowEval7829 (x : Key → ℝ) : Integer.Sparse.eval row7829 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7829, Integer.Sparse.eval_collectBalanced, rawRowCheck7829]

def rawRow7830 : Integer.Sparse Key := [(key2887, 2), (key2843, 2), (key2889, 2), (key2887, 2), (key2766, 2), (key2910, 2), (key2843, 2), (key2889, 2), (key2766, 2), (key2910, 2), (key2772, 2), (key2880, 2), (key2966, -2), (key2995, -2), (key2968, -2), (key2966, -2), (key2995, -2), (key2929, -2), (key3002, -2), (key2931, -2), (key2989, -2), (key2968, -2), (key2931, -2), (key2989, -2)]

theorem rawRowCheck7830 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block3.form0 = rawRow7830 := by decide +kernel

def row7830 : Integer.Sparse Key := [(key2766, 4), (key2772, 2), (key2843, 4), (key2880, 2), (key2887, 4), (key2889, 4), (key2910, 4), (key2929, -2), (key2931, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, -4), (key3002, -2)]

theorem rowCheck7830 : row7830 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7830 := by decide +kernel

theorem rowEval7830 (x : Key → ℝ) : Integer.Sparse.eval row7830 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7830, Integer.Sparse.eval_collectBalanced, rawRowCheck7830]

def rawRow7831 : Integer.Sparse Key := [(key2887, 2), (key2889, 2), (key2843, 2), (key2887, 2), (key2910, 2), (key2766, 2), (key2889, 2), (key2843, 2), (key2910, 2), (key2766, 2), (key2880, 2), (key2772, 2), (key2995, -2), (key2966, -2), (key2968, -2), (key2995, -2), (key2966, -2), (key3002, -2), (key2929, -2), (key2989, -2), (key2931, -2), (key2968, -2), (key2989, -2), (key2931, -2)]

theorem rawRowCheck7831 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block3.form0 = rawRow7831 := by decide +kernel

def row7831 : Integer.Sparse Key := [(key2766, 4), (key2772, 2), (key2843, 4), (key2880, 2), (key2887, 4), (key2889, 4), (key2910, 4), (key2929, -2), (key2931, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, -4), (key3002, -2)]

theorem rowCheck7831 : row7831 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7831 := by decide +kernel

theorem rowEval7831 (x : Key → ℝ) : Integer.Sparse.eval row7831 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7831, Integer.Sparse.eval_collectBalanced, rawRowCheck7831]

def rawRow7832 : Integer.Sparse Key := [(key2889, 2), (key2843, 2), (key2887, 2), (key2910, 2), (key2766, 2), (key2887, 2), (key2880, 2), (key2910, 2), (key2772, 2), (key2889, 2), (key2766, 2), (key2843, 2), (key2968, -2), (key2995, -2), (key2966, -2), (key2989, -2), (key3002, -2), (key2931, -2), (key2995, -2), (key2929, -2), (key2966, -2), (key2989, -2), (key2931, -2), (key2968, -2)]

theorem rawRowCheck7832 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block3.form0 = rawRow7832 := by decide +kernel

def row7832 : Integer.Sparse Key := [(key2766, 4), (key2772, 2), (key2843, 4), (key2880, 2), (key2887, 4), (key2889, 4), (key2910, 4), (key2929, -2), (key2931, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, -4), (key3002, -2)]

theorem rowCheck7832 : row7832 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7832 := by decide +kernel

theorem rowEval7832 (x : Key → ℝ) : Integer.Sparse.eval row7832 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7832, Integer.Sparse.eval_collectBalanced, rawRowCheck7832]

def rawRow7833 : Integer.Sparse Key := [(key2889, 2), (key2887, 2), (key2843, 2), (key2910, 2), (key2887, 2), (key2766, 2), (key2910, 2), (key2880, 2), (key2889, 2), (key2772, 2), (key2843, 2), (key2766, 2), (key2995, -2), (key2968, -2), (key2966, -2), (key3002, -2), (key2989, -2), (key2995, -2), (key2931, -2), (key2966, -2), (key2929, -2), (key2989, -2), (key2968, -2), (key2931, -2)]

theorem rawRowCheck7833 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block3.form0 = rawRow7833 := by decide +kernel

def row7833 : Integer.Sparse Key := [(key2766, 4), (key2772, 2), (key2843, 4), (key2880, 2), (key2887, 4), (key2889, 4), (key2910, 4), (key2929, -2), (key2931, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, -4), (key3002, -2)]

theorem rowCheck7833 : row7833 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7833 := by decide +kernel

theorem rowEval7833 (x : Key → ℝ) : Integer.Sparse.eval row7833 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7833, Integer.Sparse.eval_collectBalanced, rawRowCheck7833]

def rawRow7834 : Integer.Sparse Key := [(key2880, 2), (key2910, 2), (key2910, 2), (key2772, 2), (key2889, 2), (key2889, 2), (key2766, 2), (key2766, 2), (key2843, 2), (key2843, 2), (key2887, 2), (key2887, 2), (key2989, -2), (key2989, -2), (key3002, -2), (key2931, -2), (key2931, -2), (key2968, -2), (key2968, -2), (key2995, -2), (key2995, -2), (key2929, -2), (key2966, -2), (key2966, -2)]

theorem rawRowCheck7834 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block3.form0 = rawRow7834 := by decide +kernel

def row7834 : Integer.Sparse Key := [(key2766, 4), (key2772, 2), (key2843, 4), (key2880, 2), (key2887, 4), (key2889, 4), (key2910, 4), (key2929, -2), (key2931, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, -4), (key3002, -2)]

theorem rowCheck7834 : row7834 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7834 := by decide +kernel

theorem rowEval7834 (x : Key → ℝ) : Integer.Sparse.eval row7834 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7834, Integer.Sparse.eval_collectBalanced, rawRowCheck7834]

def rawRow7835 : Integer.Sparse Key := [(key2910, 2), (key2880, 2), (key2910, 2), (key2889, 2), (key2772, 2), (key2889, 2), (key2843, 2), (key2887, 2), (key2766, 2), (key2887, 2), (key2766, 2), (key2843, 2), (key2989, -2), (key3002, -2), (key2989, -2), (key2968, -2), (key2995, -2), (key2931, -2), (key2995, -2), (key2931, -2), (key2968, -2), (key2966, -2), (key2929, -2), (key2966, -2)]

theorem rawRowCheck7835 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block3.form0 = rawRow7835 := by decide +kernel

def row7835 : Integer.Sparse Key := [(key2766, 4), (key2772, 2), (key2843, 4), (key2880, 2), (key2887, 4), (key2889, 4), (key2910, 4), (key2929, -2), (key2931, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, -4), (key3002, -2)]

theorem rowCheck7835 : row7835 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7835 := by decide +kernel

theorem rowEval7835 (x : Key → ℝ) : Integer.Sparse.eval row7835 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7835, Integer.Sparse.eval_collectBalanced, rawRowCheck7835]

def rawRow7836 : Integer.Sparse Key := [(key2910, 2), (key2910, 2), (key2880, 2), (key2889, 2), (key2889, 2), (key2772, 2), (key2887, 2), (key2843, 2), (key2887, 2), (key2766, 2), (key2843, 2), (key2766, 2), (key3002, -2), (key2989, -2), (key2989, -2), (key2995, -2), (key2968, -2), (key2995, -2), (key2931, -2), (key2968, -2), (key2931, -2), (key2966, -2), (key2966, -2), (key2929, -2)]

theorem rawRowCheck7836 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block3.form0 = rawRow7836 := by decide +kernel

def row7836 : Integer.Sparse Key := [(key2766, 4), (key2772, 2), (key2843, 4), (key2880, 2), (key2887, 4), (key2889, 4), (key2910, 4), (key2929, -2), (key2931, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, -4), (key3002, -2)]

theorem rowCheck7836 : row7836 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7836 := by decide +kernel

theorem rowEval7836 (x : Key → ℝ) : Integer.Sparse.eval row7836 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7836, Integer.Sparse.eval_collectBalanced, rawRowCheck7836]

def rawRow7837 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 6), (key1104, 6), (key1230, 6)]

theorem rawRowCheck7837 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block3.form1 = rawRow7837 := by decide +kernel

def row7837 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 12), (key1230, 6)]

theorem rowCheck7837 : row7837 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7837 := by decide +kernel

theorem rowEval7837 (x : Key → ℝ) : Integer.Sparse.eval row7837 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7837, Integer.Sparse.eval_collectBalanced, rawRowCheck7837]

def rawRow7838 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 6), (key1230, 6), (key1104, 6)]

theorem rawRowCheck7838 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block3.form1 = rawRow7838 := by decide +kernel

def row7838 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 12), (key1230, 6)]

theorem rowCheck7838 : row7838 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7838 := by decide +kernel

theorem rowEval7838 (x : Key → ℝ) : Integer.Sparse.eval row7838 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7838, Integer.Sparse.eval_collectBalanced, rawRowCheck7838]

def rawRow7839 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1230, 6), (key1104, 6), (key1104, 6)]

theorem rawRowCheck7839 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block3.form1 = rawRow7839 := by decide +kernel

def row7839 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 12), (key1230, 6)]

theorem rowCheck7839 : row7839 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7839 := by decide +kernel

theorem rowEval7839 (x : Key → ℝ) : Integer.Sparse.eval row7839 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7839, Integer.Sparse.eval_collectBalanced, rawRowCheck7839]

def rawRow7840 : Integer.Sparse Key := [(key991, -24), (key1104, 6), (key1026, 6), (key1104, 6), (key1230, 6)]

theorem rawRowCheck7840 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block3.form1 = rawRow7840 := by decide +kernel

def row7840 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 12), (key1230, 6)]

theorem rowCheck7840 : row7840 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7840 := by decide +kernel

theorem rowEval7840 (x : Key → ℝ) : Integer.Sparse.eval row7840 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7840, Integer.Sparse.eval_collectBalanced, rawRowCheck7840]

def rawRow7841 : Integer.Sparse Key := [(key991, -24), (key1104, 6), (key1026, 6), (key1230, 6), (key1104, 6)]

theorem rawRowCheck7841 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block3.form1 = rawRow7841 := by decide +kernel

def row7841 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 12), (key1230, 6)]

theorem rowCheck7841 : row7841 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7841 := by decide +kernel

theorem rowEval7841 (x : Key → ℝ) : Integer.Sparse.eval row7841 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7841, Integer.Sparse.eval_collectBalanced, rawRowCheck7841]

def rawRow7842 : Integer.Sparse Key := [(key991, -24), (key1104, 6), (key1104, 6), (key1026, 6), (key1230, 6)]

theorem rawRowCheck7842 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block3.form1 = rawRow7842 := by decide +kernel

def row7842 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 12), (key1230, 6)]

theorem rowCheck7842 : row7842 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7842 := by decide +kernel

theorem rowEval7842 (x : Key → ℝ) : Integer.Sparse.eval row7842 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7842, Integer.Sparse.eval_collectBalanced, rawRowCheck7842]

def rawRow7843 : Integer.Sparse Key := [(key991, -24), (key1104, 6), (key1104, 6), (key1230, 6), (key1026, 6)]

theorem rawRowCheck7843 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block3.form1 = rawRow7843 := by decide +kernel

def row7843 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 12), (key1230, 6)]

theorem rowCheck7843 : row7843 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7843 := by decide +kernel

theorem rowEval7843 (x : Key → ℝ) : Integer.Sparse.eval row7843 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck7843, Integer.Sparse.eval_collectBalanced, rawRowCheck7843]

def rawRow7844 : Integer.Sparse Key := [(key991, -24), (key1104, 6), (key1230, 6), (key1026, 6), (key1104, 6)]

theorem rawRowCheck7844 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block3.form1 = rawRow7844 := by decide +kernel

def row7844 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 12), (key1230, 6)]

theorem rowCheck7844 : row7844 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7844 := by decide +kernel

theorem rowEval7844 (x : Key → ℝ) : Integer.Sparse.eval row7844 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7844, Integer.Sparse.eval_collectBalanced, rawRowCheck7844]

def rawRow7845 : Integer.Sparse Key := [(key991, -24), (key1104, 6), (key1230, 6), (key1104, 6), (key1026, 6)]

theorem rawRowCheck7845 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block3.form1 = rawRow7845 := by decide +kernel

def row7845 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 12), (key1230, 6)]

theorem rowCheck7845 : row7845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7845 := by decide +kernel

theorem rowEval7845 (x : Key → ℝ) : Integer.Sparse.eval row7845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck7845, Integer.Sparse.eval_collectBalanced, rawRowCheck7845]

def rawRow7846 : Integer.Sparse Key := [(key991, -24), (key1230, 6), (key1026, 6), (key1104, 6), (key1104, 6)]

theorem rawRowCheck7846 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block3.form1 = rawRow7846 := by decide +kernel

def row7846 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 12), (key1230, 6)]

theorem rowCheck7846 : row7846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7846 := by decide +kernel

theorem rowEval7846 (x : Key → ℝ) : Integer.Sparse.eval row7846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7846, Integer.Sparse.eval_collectBalanced, rawRowCheck7846]

def rawRow7847 : Integer.Sparse Key := [(key991, -24), (key1230, 6), (key1104, 6), (key1026, 6), (key1104, 6)]

theorem rawRowCheck7847 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block3.form1 = rawRow7847 := by decide +kernel

def row7847 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 12), (key1230, 6)]

theorem rowCheck7847 : row7847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7847 := by decide +kernel

theorem rowEval7847 (x : Key → ℝ) : Integer.Sparse.eval row7847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7847, Integer.Sparse.eval_collectBalanced, rawRowCheck7847]

def rawRow7848 : Integer.Sparse Key := [(key991, -24), (key1230, 6), (key1104, 6), (key1104, 6), (key1026, 6)]

theorem rawRowCheck7848 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block3.form1 = rawRow7848 := by decide +kernel

def row7848 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 12), (key1230, 6)]

theorem rowCheck7848 : row7848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7848 := by decide +kernel

theorem rowEval7848 (x : Key → ℝ) : Integer.Sparse.eval row7848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck7848, Integer.Sparse.eval_collectBalanced, rawRowCheck7848]

def rawRow7849 : Integer.Sparse Key := [(key993, -6), (key1001, -6), (key1001, -6), (key1015, -6), (key1028, 2), (key1036, 2), (key1036, 2), (key1106, 2), (key1114, 2), (key1106, 2), (key1232, 2), (key1114, 2), (key1232, 2), (key1123, 2), (key1123, 2), (key1235, 2)]

theorem rawRowCheck7849 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block3.form2 = rawRow7849 := by decide +kernel

def row7849 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 2), (key1036, 4), (key1106, 4), (key1114, 4), (key1123, 4), (key1232, 4), (key1235, 2)]

theorem rowCheck7849 : row7849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7849 := by decide +kernel

theorem rowEval7849 (x : Key → ℝ) : Integer.Sparse.eval row7849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7849, Integer.Sparse.eval_collectBalanced, rawRowCheck7849]

def rawRow7850 : Integer.Sparse Key := [(key1001, -6), (key993, -6), (key1001, -6), (key1015, -6), (key1036, 2), (key1028, 2), (key1036, 2), (key1114, 2), (key1106, 2), (key1232, 2), (key1106, 2), (key1232, 2), (key1114, 2), (key1123, 2), (key1235, 2), (key1123, 2)]

theorem rawRowCheck7850 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block3.form2 = rawRow7850 := by decide +kernel

def row7850 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 2), (key1036, 4), (key1106, 4), (key1114, 4), (key1123, 4), (key1232, 4), (key1235, 2)]

theorem rowCheck7850 : row7850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7850 := by decide +kernel

theorem rowEval7850 (x : Key → ℝ) : Integer.Sparse.eval row7850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7850, Integer.Sparse.eval_collectBalanced, rawRowCheck7850]

def rawRow7851 : Integer.Sparse Key := [(key1001, -6), (key1001, -6), (key993, -6), (key1015, -6), (key1036, 2), (key1036, 2), (key1028, 2), (key1232, 2), (key1232, 2), (key1114, 2), (key1114, 2), (key1106, 2), (key1106, 2), (key1235, 2), (key1123, 2), (key1123, 2)]

theorem rawRowCheck7851 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block3.form2 = rawRow7851 := by decide +kernel

def row7851 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 2), (key1036, 4), (key1106, 4), (key1114, 4), (key1123, 4), (key1232, 4), (key1235, 2)]

theorem rowCheck7851 : row7851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7851 := by decide +kernel

theorem rowEval7851 (x : Key → ℝ) : Integer.Sparse.eval row7851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7851, Integer.Sparse.eval_collectBalanced, rawRowCheck7851]

def rawRow7852 : Integer.Sparse Key := [(key993, -6), (key1001, -6), (key1015, -6), (key1001, -6), (key1106, 2), (key1114, 2), (key1123, 2), (key1028, 2), (key1036, 2), (key1106, 2), (key1232, 2), (key1123, 2), (key1235, 2), (key1036, 2), (key1114, 2), (key1232, 2)]

theorem rawRowCheck7852 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block3.form2 = rawRow7852 := by decide +kernel

def row7852 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 2), (key1036, 4), (key1106, 4), (key1114, 4), (key1123, 4), (key1232, 4), (key1235, 2)]

theorem rowCheck7852 : row7852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7852 := by decide +kernel

theorem rowEval7852 (x : Key → ℝ) : Integer.Sparse.eval row7852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7852, Integer.Sparse.eval_collectBalanced, rawRowCheck7852]

def rawRow7853 : Integer.Sparse Key := [(key1001, -6), (key993, -6), (key1015, -6), (key1001, -6), (key1114, 2), (key1106, 2), (key1123, 2), (key1036, 2), (key1028, 2), (key1232, 2), (key1106, 2), (key1235, 2), (key1123, 2), (key1036, 2), (key1232, 2), (key1114, 2)]

theorem rawRowCheck7853 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block3.form2 = rawRow7853 := by decide +kernel

def row7853 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 2), (key1036, 4), (key1106, 4), (key1114, 4), (key1123, 4), (key1232, 4), (key1235, 2)]

theorem rowCheck7853 : row7853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7853 := by decide +kernel

theorem rowEval7853 (x : Key → ℝ) : Integer.Sparse.eval row7853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7853, Integer.Sparse.eval_collectBalanced, rawRowCheck7853]

def rawRow7854 : Integer.Sparse Key := [(key993, -6), (key1015, -6), (key1001, -6), (key1001, -6), (key1106, 2), (key1123, 2), (key1114, 2), (key1106, 2), (key1123, 2), (key1028, 2), (key1235, 2), (key1036, 2), (key1232, 2), (key1114, 2), (key1036, 2), (key1232, 2)]

theorem rawRowCheck7854 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block3.form2 = rawRow7854 := by decide +kernel

def row7854 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 2), (key1036, 4), (key1106, 4), (key1114, 4), (key1123, 4), (key1232, 4), (key1235, 2)]

theorem rowCheck7854 : row7854 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7854 := by decide +kernel

theorem rowEval7854 (x : Key → ℝ) : Integer.Sparse.eval row7854 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7854, Integer.Sparse.eval_collectBalanced, rawRowCheck7854]

def rawRow7855 : Integer.Sparse Key := [(key1015, -6), (key993, -6), (key1001, -6), (key1001, -6), (key1123, 2), (key1106, 2), (key1114, 2), (key1123, 2), (key1106, 2), (key1235, 2), (key1028, 2), (key1232, 2), (key1036, 2), (key1114, 2), (key1232, 2), (key1036, 2)]

theorem rawRowCheck7855 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block3.form2 = rawRow7855 := by decide +kernel

def row7855 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 2), (key1036, 4), (key1106, 4), (key1114, 4), (key1123, 4), (key1232, 4), (key1235, 2)]

theorem rowCheck7855 : row7855 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7855 := by decide +kernel

theorem rowEval7855 (x : Key → ℝ) : Integer.Sparse.eval row7855 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck7855, Integer.Sparse.eval_collectBalanced, rawRowCheck7855]

def rawRow7856 : Integer.Sparse Key := [(key1001, -6), (key1015, -6), (key993, -6), (key1001, -6), (key1114, 2), (key1123, 2), (key1106, 2), (key1232, 2), (key1235, 2), (key1036, 2), (key1123, 2), (key1028, 2), (key1106, 2), (key1232, 2), (key1036, 2), (key1114, 2)]

theorem rawRowCheck7856 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block3.form2 = rawRow7856 := by decide +kernel

def row7856 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 2), (key1036, 4), (key1106, 4), (key1114, 4), (key1123, 4), (key1232, 4), (key1235, 2)]

theorem rowCheck7856 : row7856 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7856 := by decide +kernel

theorem rowEval7856 (x : Key → ℝ) : Integer.Sparse.eval row7856 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7856, Integer.Sparse.eval_collectBalanced, rawRowCheck7856]

def rawRow7857 : Integer.Sparse Key := [(key1015, -6), (key1001, -6), (key993, -6), (key1001, -6), (key1123, 2), (key1114, 2), (key1106, 2), (key1235, 2), (key1232, 2), (key1123, 2), (key1036, 2), (key1106, 2), (key1028, 2), (key1232, 2), (key1114, 2), (key1036, 2)]

theorem rawRowCheck7857 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block3.form2 = rawRow7857 := by decide +kernel

def row7857 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 2), (key1036, 4), (key1106, 4), (key1114, 4), (key1123, 4), (key1232, 4), (key1235, 2)]

theorem rowCheck7857 : row7857 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7857 := by decide +kernel

theorem rowEval7857 (x : Key → ℝ) : Integer.Sparse.eval row7857 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck7857, Integer.Sparse.eval_collectBalanced, rawRowCheck7857]

def rawRow7858 : Integer.Sparse Key := [(key1001, -6), (key1001, -6), (key1015, -6), (key993, -6), (key1232, 2), (key1232, 2), (key1235, 2), (key1036, 2), (key1036, 2), (key1114, 2), (key1114, 2), (key1123, 2), (key1123, 2), (key1028, 2), (key1106, 2), (key1106, 2)]

theorem rawRowCheck7858 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block3.form2 = rawRow7858 := by decide +kernel

def row7858 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 2), (key1036, 4), (key1106, 4), (key1114, 4), (key1123, 4), (key1232, 4), (key1235, 2)]

theorem rowCheck7858 : row7858 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7858 := by decide +kernel

theorem rowEval7858 (x : Key → ℝ) : Integer.Sparse.eval row7858 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7858, Integer.Sparse.eval_collectBalanced, rawRowCheck7858]

def rawRow7859 : Integer.Sparse Key := [(key1001, -6), (key1015, -6), (key1001, -6), (key993, -6), (key1232, 2), (key1235, 2), (key1232, 2), (key1114, 2), (key1123, 2), (key1036, 2), (key1123, 2), (key1036, 2), (key1114, 2), (key1106, 2), (key1028, 2), (key1106, 2)]

theorem rawRowCheck7859 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block3.form2 = rawRow7859 := by decide +kernel

def row7859 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 2), (key1036, 4), (key1106, 4), (key1114, 4), (key1123, 4), (key1232, 4), (key1235, 2)]

theorem rowCheck7859 : row7859 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7859 := by decide +kernel

theorem rowEval7859 (x : Key → ℝ) : Integer.Sparse.eval row7859 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7859, Integer.Sparse.eval_collectBalanced, rawRowCheck7859]

def rawRow7860 : Integer.Sparse Key := [(key1015, -6), (key1001, -6), (key1001, -6), (key993, -6), (key1235, 2), (key1232, 2), (key1232, 2), (key1123, 2), (key1114, 2), (key1123, 2), (key1036, 2), (key1114, 2), (key1036, 2), (key1106, 2), (key1106, 2), (key1028, 2)]

theorem rawRowCheck7860 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block3.form2 = rawRow7860 := by decide +kernel

def row7860 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 2), (key1036, 4), (key1106, 4), (key1114, 4), (key1123, 4), (key1232, 4), (key1235, 2)]

theorem rowCheck7860 : row7860 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7860 := by decide +kernel

theorem rowEval7860 (x : Key → ℝ) : Integer.Sparse.eval row7860 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck7860, Integer.Sparse.eval_collectBalanced, rawRowCheck7860]

def rawRow7861 : Integer.Sparse Key := [(key2665, -6), (key2700, -6), (key2700, -6), (key2721, -6), (key2780, 2), (key2780, 2), (key2789, 2), (key2803, 2), (key2803, 2), (key2824, 2), (key2853, 2), (key2855, 2), (key2853, 2), (key2865, 2), (key2855, 2), (key2865, 2)]

theorem rawRowCheck7861 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block3.form3 = rawRow7861 := by decide +kernel

def row7861 : Integer.Sparse Key := [(key2665, -6), (key2700, -12), (key2721, -6), (key2780, 4), (key2789, 2), (key2803, 4), (key2824, 2), (key2853, 4), (key2855, 4), (key2865, 4)]

theorem rowCheck7861 : row7861 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7861 := by decide +kernel

theorem rowEval7861 (x : Key → ℝ) : Integer.Sparse.eval row7861 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7861, Integer.Sparse.eval_collectBalanced, rawRowCheck7861]

def rawRow7862 : Integer.Sparse Key := [(key2665, -6), (key2700, -6), (key2721, -6), (key2700, -6), (key2780, 2), (key2789, 2), (key2780, 2), (key2803, 2), (key2824, 2), (key2803, 2), (key2855, 2), (key2853, 2), (key2865, 2), (key2853, 2), (key2865, 2), (key2855, 2)]

theorem rawRowCheck7862 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block3.form3 = rawRow7862 := by decide +kernel

def row7862 : Integer.Sparse Key := [(key2665, -6), (key2700, -12), (key2721, -6), (key2780, 4), (key2789, 2), (key2803, 4), (key2824, 2), (key2853, 4), (key2855, 4), (key2865, 4)]

theorem rowCheck7862 : row7862 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7862 := by decide +kernel

theorem rowEval7862 (x : Key → ℝ) : Integer.Sparse.eval row7862 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7862, Integer.Sparse.eval_collectBalanced, rawRowCheck7862]

def rawRow7863 : Integer.Sparse Key := [(key2665, -6), (key2721, -6), (key2700, -6), (key2700, -6), (key2789, 2), (key2780, 2), (key2780, 2), (key2824, 2), (key2803, 2), (key2803, 2), (key2865, 2), (key2865, 2), (key2855, 2), (key2855, 2), (key2853, 2), (key2853, 2)]

theorem rawRowCheck7863 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block3.form3 = rawRow7863 := by decide +kernel

def row7863 : Integer.Sparse Key := [(key2665, -6), (key2700, -12), (key2721, -6), (key2780, 4), (key2789, 2), (key2803, 4), (key2824, 2), (key2853, 4), (key2855, 4), (key2865, 4)]

theorem rowCheck7863 : row7863 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7863 := by decide +kernel

theorem rowEval7863 (x : Key → ℝ) : Integer.Sparse.eval row7863 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7863, Integer.Sparse.eval_collectBalanced, rawRowCheck7863]

def rawRow7864 : Integer.Sparse Key := [(key2700, -6), (key2665, -6), (key2700, -6), (key2721, -6), (key2803, 2), (key2853, 2), (key2855, 2), (key2780, 2), (key2853, 2), (key2865, 2), (key2780, 2), (key2789, 2), (key2803, 2), (key2824, 2), (key2855, 2), (key2865, 2)]

theorem rawRowCheck7864 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block3.form3 = rawRow7864 := by decide +kernel

def row7864 : Integer.Sparse Key := [(key2665, -6), (key2700, -12), (key2721, -6), (key2780, 4), (key2789, 2), (key2803, 4), (key2824, 2), (key2853, 4), (key2855, 4), (key2865, 4)]

theorem rowCheck7864 : row7864 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7864 := by decide +kernel

theorem rowEval7864 (x : Key → ℝ) : Integer.Sparse.eval row7864 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7864, Integer.Sparse.eval_collectBalanced, rawRowCheck7864]

def rawRow7865 : Integer.Sparse Key := [(key2700, -6), (key2665, -6), (key2721, -6), (key2700, -6), (key2803, 2), (key2855, 2), (key2853, 2), (key2780, 2), (key2865, 2), (key2853, 2), (key2789, 2), (key2780, 2), (key2824, 2), (key2803, 2), (key2865, 2), (key2855, 2)]

theorem rawRowCheck7865 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block3.form3 = rawRow7865 := by decide +kernel

def row7865 : Integer.Sparse Key := [(key2665, -6), (key2700, -12), (key2721, -6), (key2780, 4), (key2789, 2), (key2803, 4), (key2824, 2), (key2853, 4), (key2855, 4), (key2865, 4)]

theorem rowCheck7865 : row7865 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7865 := by decide +kernel

theorem rowEval7865 (x : Key → ℝ) : Integer.Sparse.eval row7865 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7865, Integer.Sparse.eval_collectBalanced, rawRowCheck7865]

def rawRow7866 : Integer.Sparse Key := [(key2700, -6), (key2700, -6), (key2665, -6), (key2721, -6), (key2853, 2), (key2803, 2), (key2855, 2), (key2853, 2), (key2780, 2), (key2865, 2), (key2803, 2), (key2855, 2), (key2780, 2), (key2865, 2), (key2789, 2), (key2824, 2)]

theorem rawRowCheck7866 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block3.form3 = rawRow7866 := by decide +kernel

def row7866 : Integer.Sparse Key := [(key2665, -6), (key2700, -12), (key2721, -6), (key2780, 4), (key2789, 2), (key2803, 4), (key2824, 2), (key2853, 4), (key2855, 4), (key2865, 4)]

theorem rowCheck7866 : row7866 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7866 := by decide +kernel

theorem rowEval7866 (x : Key → ℝ) : Integer.Sparse.eval row7866 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7866, Integer.Sparse.eval_collectBalanced, rawRowCheck7866]

def rawRow7867 : Integer.Sparse Key := [(key2700, -6), (key2700, -6), (key2721, -6), (key2665, -6), (key2853, 2), (key2855, 2), (key2803, 2), (key2853, 2), (key2865, 2), (key2780, 2), (key2855, 2), (key2803, 2), (key2865, 2), (key2780, 2), (key2824, 2), (key2789, 2)]

theorem rawRowCheck7867 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block3.form3 = rawRow7867 := by decide +kernel

def row7867 : Integer.Sparse Key := [(key2665, -6), (key2700, -12), (key2721, -6), (key2780, 4), (key2789, 2), (key2803, 4), (key2824, 2), (key2853, 4), (key2855, 4), (key2865, 4)]

theorem rowCheck7867 : row7867 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7867 := by decide +kernel

theorem rowEval7867 (x : Key → ℝ) : Integer.Sparse.eval row7867 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck7867, Integer.Sparse.eval_collectBalanced, rawRowCheck7867]

def rawRow7868 : Integer.Sparse Key := [(key2700, -6), (key2721, -6), (key2665, -6), (key2700, -6), (key2855, 2), (key2803, 2), (key2853, 2), (key2865, 2), (key2780, 2), (key2853, 2), (key2824, 2), (key2865, 2), (key2789, 2), (key2855, 2), (key2780, 2), (key2803, 2)]

theorem rawRowCheck7868 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block3.form3 = rawRow7868 := by decide +kernel

def row7868 : Integer.Sparse Key := [(key2665, -6), (key2700, -12), (key2721, -6), (key2780, 4), (key2789, 2), (key2803, 4), (key2824, 2), (key2853, 4), (key2855, 4), (key2865, 4)]

theorem rowCheck7868 : row7868 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7868 := by decide +kernel

theorem rowEval7868 (x : Key → ℝ) : Integer.Sparse.eval row7868 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7868, Integer.Sparse.eval_collectBalanced, rawRowCheck7868]

def rawRow7869 : Integer.Sparse Key := [(key2700, -6), (key2721, -6), (key2700, -6), (key2665, -6), (key2855, 2), (key2853, 2), (key2803, 2), (key2865, 2), (key2853, 2), (key2780, 2), (key2865, 2), (key2824, 2), (key2855, 2), (key2789, 2), (key2803, 2), (key2780, 2)]

theorem rawRowCheck7869 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block3.form3 = rawRow7869 := by decide +kernel

def row7869 : Integer.Sparse Key := [(key2665, -6), (key2700, -12), (key2721, -6), (key2780, 4), (key2789, 2), (key2803, 4), (key2824, 2), (key2853, 4), (key2855, 4), (key2865, 4)]

theorem rowCheck7869 : row7869 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7869 := by decide +kernel

theorem rowEval7869 (x : Key → ℝ) : Integer.Sparse.eval row7869 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck7869, Integer.Sparse.eval_collectBalanced, rawRowCheck7869]

def rawRow7870 : Integer.Sparse Key := [(key2721, -6), (key2665, -6), (key2700, -6), (key2700, -6), (key2824, 2), (key2865, 2), (key2865, 2), (key2789, 2), (key2855, 2), (key2855, 2), (key2780, 2), (key2780, 2), (key2803, 2), (key2803, 2), (key2853, 2), (key2853, 2)]

theorem rawRowCheck7870 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block3.form3 = rawRow7870 := by decide +kernel

def row7870 : Integer.Sparse Key := [(key2665, -6), (key2700, -12), (key2721, -6), (key2780, 4), (key2789, 2), (key2803, 4), (key2824, 2), (key2853, 4), (key2855, 4), (key2865, 4)]

theorem rowCheck7870 : row7870 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7870 := by decide +kernel

theorem rowEval7870 (x : Key → ℝ) : Integer.Sparse.eval row7870 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7870, Integer.Sparse.eval_collectBalanced, rawRowCheck7870]

def rawRow7871 : Integer.Sparse Key := [(key2721, -6), (key2700, -6), (key2665, -6), (key2700, -6), (key2865, 2), (key2824, 2), (key2865, 2), (key2855, 2), (key2789, 2), (key2855, 2), (key2803, 2), (key2853, 2), (key2780, 2), (key2853, 2), (key2780, 2), (key2803, 2)]

theorem rawRowCheck7871 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block3.form3 = rawRow7871 := by decide +kernel

def row7871 : Integer.Sparse Key := [(key2665, -6), (key2700, -12), (key2721, -6), (key2780, 4), (key2789, 2), (key2803, 4), (key2824, 2), (key2853, 4), (key2855, 4), (key2865, 4)]

theorem rowCheck7871 : row7871 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7871 := by decide +kernel

theorem rowEval7871 (x : Key → ℝ) : Integer.Sparse.eval row7871 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7871, Integer.Sparse.eval_collectBalanced, rawRowCheck7871]

def rawRow7872 : Integer.Sparse Key := [(key2721, -6), (key2700, -6), (key2700, -6), (key2665, -6), (key2865, 2), (key2865, 2), (key2824, 2), (key2855, 2), (key2855, 2), (key2789, 2), (key2853, 2), (key2803, 2), (key2853, 2), (key2780, 2), (key2803, 2), (key2780, 2)]

theorem rawRowCheck7872 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block3.form3 = rawRow7872 := by decide +kernel

def row7872 : Integer.Sparse Key := [(key2665, -6), (key2700, -12), (key2721, -6), (key2780, 4), (key2789, 2), (key2803, 4), (key2824, 2), (key2853, 4), (key2855, 4), (key2865, 4)]

theorem rowCheck7872 : row7872 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7872 := by decide +kernel

theorem rowEval7872 (x : Key → ℝ) : Integer.Sparse.eval row7872 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck7872, Integer.Sparse.eval_collectBalanced, rawRowCheck7872]

def rawRow7873 : Integer.Sparse Key := [(key2370, -6), (key2376, -6), (key2376, -6), (key2388, -6), (key2762, 2), (key2768, 2), (key2768, 2), (key2839, 2), (key2845, 2), (key2839, 2), (key2876, 2), (key2845, 2), (key2876, 2), (key2916, 2), (key2916, 2), (key2925, 2)]

theorem rawRowCheck7873 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block3.form4 = rawRow7873 := by decide +kernel

def row7873 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2762, 2), (key2768, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, 4), (key2925, 2)]

theorem rowCheck7873 : row7873 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7873 := by decide +kernel

theorem rowEval7873 (x : Key → ℝ) : Integer.Sparse.eval row7873 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck7873, Integer.Sparse.eval_collectBalanced, rawRowCheck7873]

def rawRow7874 : Integer.Sparse Key := [(key2376, -6), (key2370, -6), (key2376, -6), (key2388, -6), (key2768, 2), (key2762, 2), (key2768, 2), (key2845, 2), (key2839, 2), (key2876, 2), (key2839, 2), (key2876, 2), (key2845, 2), (key2916, 2), (key2925, 2), (key2916, 2)]

theorem rawRowCheck7874 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block3.form4 = rawRow7874 := by decide +kernel

def row7874 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2762, 2), (key2768, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, 4), (key2925, 2)]

theorem rowCheck7874 : row7874 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7874 := by decide +kernel

theorem rowEval7874 (x : Key → ℝ) : Integer.Sparse.eval row7874 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7874, Integer.Sparse.eval_collectBalanced, rawRowCheck7874]

def rawRow7875 : Integer.Sparse Key := [(key2376, -6), (key2376, -6), (key2370, -6), (key2388, -6), (key2768, 2), (key2768, 2), (key2762, 2), (key2876, 2), (key2876, 2), (key2845, 2), (key2845, 2), (key2839, 2), (key2839, 2), (key2925, 2), (key2916, 2), (key2916, 2)]

theorem rawRowCheck7875 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block3.form4 = rawRow7875 := by decide +kernel

def row7875 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2762, 2), (key2768, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, 4), (key2925, 2)]

theorem rowCheck7875 : row7875 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7875 := by decide +kernel

theorem rowEval7875 (x : Key → ℝ) : Integer.Sparse.eval row7875 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7875, Integer.Sparse.eval_collectBalanced, rawRowCheck7875]

def rawRow7876 : Integer.Sparse Key := [(key2370, -6), (key2376, -6), (key2388, -6), (key2376, -6), (key2839, 2), (key2845, 2), (key2916, 2), (key2762, 2), (key2768, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key2768, 2), (key2845, 2), (key2876, 2)]

theorem rawRowCheck7876 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block3.form4 = rawRow7876 := by decide +kernel

def row7876 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2762, 2), (key2768, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, 4), (key2925, 2)]

theorem rowCheck7876 : row7876 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7876 := by decide +kernel

theorem rowEval7876 (x : Key → ℝ) : Integer.Sparse.eval row7876 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck7876, Integer.Sparse.eval_collectBalanced, rawRowCheck7876]

def rawRow7877 : Integer.Sparse Key := [(key2376, -6), (key2370, -6), (key2388, -6), (key2376, -6), (key2845, 2), (key2839, 2), (key2916, 2), (key2768, 2), (key2762, 2), (key2876, 2), (key2839, 2), (key2925, 2), (key2916, 2), (key2768, 2), (key2876, 2), (key2845, 2)]

theorem rawRowCheck7877 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block3.form4 = rawRow7877 := by decide +kernel

def row7877 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2762, 2), (key2768, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, 4), (key2925, 2)]

theorem rowCheck7877 : row7877 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7877 := by decide +kernel

theorem rowEval7877 (x : Key → ℝ) : Integer.Sparse.eval row7877 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7877, Integer.Sparse.eval_collectBalanced, rawRowCheck7877]

def rawRow7878 : Integer.Sparse Key := [(key2370, -6), (key2388, -6), (key2376, -6), (key2376, -6), (key2839, 2), (key2916, 2), (key2845, 2), (key2839, 2), (key2916, 2), (key2762, 2), (key2925, 2), (key2768, 2), (key2876, 2), (key2845, 2), (key2768, 2), (key2876, 2)]

theorem rawRowCheck7878 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block3.form4 = rawRow7878 := by decide +kernel

def row7878 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2762, 2), (key2768, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, 4), (key2925, 2)]

theorem rowCheck7878 : row7878 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7878 := by decide +kernel

theorem rowEval7878 (x : Key → ℝ) : Integer.Sparse.eval row7878 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck7878, Integer.Sparse.eval_collectBalanced, rawRowCheck7878]

def rawRow7879 : Integer.Sparse Key := [(key2388, -6), (key2370, -6), (key2376, -6), (key2376, -6), (key2916, 2), (key2839, 2), (key2845, 2), (key2916, 2), (key2839, 2), (key2925, 2), (key2762, 2), (key2876, 2), (key2768, 2), (key2845, 2), (key2876, 2), (key2768, 2)]

theorem rawRowCheck7879 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block3.form4 = rawRow7879 := by decide +kernel

def row7879 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2762, 2), (key2768, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, 4), (key2925, 2)]

theorem rowCheck7879 : row7879 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7879 := by decide +kernel

theorem rowEval7879 (x : Key → ℝ) : Integer.Sparse.eval row7879 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck7879, Integer.Sparse.eval_collectBalanced, rawRowCheck7879]

def rawRow7880 : Integer.Sparse Key := [(key2376, -6), (key2388, -6), (key2370, -6), (key2376, -6), (key2845, 2), (key2916, 2), (key2839, 2), (key2876, 2), (key2925, 2), (key2768, 2), (key2916, 2), (key2762, 2), (key2839, 2), (key2876, 2), (key2768, 2), (key2845, 2)]

theorem rawRowCheck7880 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block3.form4 = rawRow7880 := by decide +kernel

def row7880 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2762, 2), (key2768, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, 4), (key2925, 2)]

theorem rowCheck7880 : row7880 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7880 := by decide +kernel

theorem rowEval7880 (x : Key → ℝ) : Integer.Sparse.eval row7880 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7880, Integer.Sparse.eval_collectBalanced, rawRowCheck7880]

def rawRow7881 : Integer.Sparse Key := [(key2388, -6), (key2376, -6), (key2370, -6), (key2376, -6), (key2916, 2), (key2845, 2), (key2839, 2), (key2925, 2), (key2876, 2), (key2916, 2), (key2768, 2), (key2839, 2), (key2762, 2), (key2876, 2), (key2845, 2), (key2768, 2)]

theorem rawRowCheck7881 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block3.form4 = rawRow7881 := by decide +kernel

def row7881 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2762, 2), (key2768, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, 4), (key2925, 2)]

theorem rowCheck7881 : row7881 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7881 := by decide +kernel

theorem rowEval7881 (x : Key → ℝ) : Integer.Sparse.eval row7881 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck7881, Integer.Sparse.eval_collectBalanced, rawRowCheck7881]

def rawRow7882 : Integer.Sparse Key := [(key2376, -6), (key2376, -6), (key2388, -6), (key2370, -6), (key2876, 2), (key2876, 2), (key2925, 2), (key2768, 2), (key2768, 2), (key2845, 2), (key2845, 2), (key2916, 2), (key2916, 2), (key2762, 2), (key2839, 2), (key2839, 2)]

theorem rawRowCheck7882 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block3.form4 = rawRow7882 := by decide +kernel

def row7882 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2762, 2), (key2768, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, 4), (key2925, 2)]

theorem rowCheck7882 : row7882 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7882 := by decide +kernel

theorem rowEval7882 (x : Key → ℝ) : Integer.Sparse.eval row7882 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7882, Integer.Sparse.eval_collectBalanced, rawRowCheck7882]

def rawRow7883 : Integer.Sparse Key := [(key2376, -6), (key2388, -6), (key2376, -6), (key2370, -6), (key2876, 2), (key2925, 2), (key2876, 2), (key2845, 2), (key2916, 2), (key2768, 2), (key2916, 2), (key2768, 2), (key2845, 2), (key2839, 2), (key2762, 2), (key2839, 2)]

theorem rawRowCheck7883 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block3.form4 = rawRow7883 := by decide +kernel

def row7883 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2762, 2), (key2768, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, 4), (key2925, 2)]

theorem rowCheck7883 : row7883 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7883 := by decide +kernel

theorem rowEval7883 (x : Key → ℝ) : Integer.Sparse.eval row7883 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7883, Integer.Sparse.eval_collectBalanced, rawRowCheck7883]

def rawRow7884 : Integer.Sparse Key := [(key2388, -6), (key2376, -6), (key2376, -6), (key2370, -6), (key2925, 2), (key2876, 2), (key2876, 2), (key2916, 2), (key2845, 2), (key2916, 2), (key2768, 2), (key2845, 2), (key2768, 2), (key2839, 2), (key2839, 2), (key2762, 2)]

theorem rawRowCheck7884 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block3.form4 = rawRow7884 := by decide +kernel

def row7884 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2762, 2), (key2768, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, 4), (key2925, 2)]

theorem rowCheck7884 : row7884 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7884 := by decide +kernel

theorem rowEval7884 (x : Key → ℝ) : Integer.Sparse.eval row7884 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck7884, Integer.Sparse.eval_collectBalanced, rawRowCheck7884]

def rawRow7885 : Integer.Sparse Key := [(key2663, -2), (key2669, -2), (key2669, -2), (key2698, -2), (key2704, -2), (key2698, -2), (key2724, -2), (key2704, -2), (key2724, -2), (key2752, -2), (key2752, -2), (key2757, -2), (key2778, 1), (key2784, 1), (key2778, 1), (key2792, 1), (key2784, 1), (key2792, 1), (key2801, 1), (key2807, 1), (key2801, 1), (key2827, 1), (key2807, 1), (key2827, 1), (key2851, 1), (key2858, 1), (key2851, 1), (key2868, 1), (key2858, 1), (key2868, 1), (key2918, 1), (key2919, 1), (key2918, 1), (key2922, 1), (key2919, 1), (key2922, 1)]

theorem rawRowCheck7885 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block3.form5 = rawRow7885 := by decide +kernel

def row7885 : Integer.Sparse Key := [(key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2778, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, 2), (key2868, 2), (key2918, 2), (key2919, 2), (key2922, 2)]

theorem rowCheck7885 : row7885 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7885 := by decide +kernel

theorem rowEval7885 (x : Key → ℝ) : Integer.Sparse.eval row7885 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck7885, Integer.Sparse.eval_collectBalanced, rawRowCheck7885]

def rawRow7886 : Integer.Sparse Key := [(key2669, -2), (key2663, -2), (key2669, -2), (key2704, -2), (key2698, -2), (key2724, -2), (key2698, -2), (key2724, -2), (key2704, -2), (key2752, -2), (key2757, -2), (key2752, -2), (key2784, 1), (key2778, 1), (key2792, 1), (key2778, 1), (key2792, 1), (key2784, 1), (key2807, 1), (key2801, 1), (key2827, 1), (key2801, 1), (key2827, 1), (key2807, 1), (key2858, 1), (key2851, 1), (key2868, 1), (key2851, 1), (key2868, 1), (key2858, 1), (key2919, 1), (key2918, 1), (key2922, 1), (key2918, 1), (key2922, 1), (key2919, 1)]

theorem rawRowCheck7886 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block3.form5 = rawRow7886 := by decide +kernel

def row7886 : Integer.Sparse Key := [(key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2778, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, 2), (key2868, 2), (key2918, 2), (key2919, 2), (key2922, 2)]

theorem rowCheck7886 : row7886 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7886 := by decide +kernel

theorem rowEval7886 (x : Key → ℝ) : Integer.Sparse.eval row7886 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck7886, Integer.Sparse.eval_collectBalanced, rawRowCheck7886]

def rawRow7887 : Integer.Sparse Key := [(key2669, -2), (key2669, -2), (key2663, -2), (key2724, -2), (key2724, -2), (key2704, -2), (key2704, -2), (key2698, -2), (key2698, -2), (key2757, -2), (key2752, -2), (key2752, -2), (key2792, 1), (key2792, 1), (key2784, 1), (key2784, 1), (key2778, 1), (key2778, 1), (key2827, 1), (key2827, 1), (key2807, 1), (key2807, 1), (key2801, 1), (key2801, 1), (key2868, 1), (key2868, 1), (key2858, 1), (key2858, 1), (key2851, 1), (key2851, 1), (key2922, 1), (key2922, 1), (key2919, 1), (key2919, 1), (key2918, 1), (key2918, 1)]

theorem rawRowCheck7887 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block3.form5 = rawRow7887 := by decide +kernel

def row7887 : Integer.Sparse Key := [(key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2778, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, 2), (key2868, 2), (key2918, 2), (key2919, 2), (key2922, 2)]

theorem rowCheck7887 : row7887 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7887 := by decide +kernel

theorem rowEval7887 (x : Key → ℝ) : Integer.Sparse.eval row7887 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck7887, Integer.Sparse.eval_collectBalanced, rawRowCheck7887]

def rawRow7888 : Integer.Sparse Key := [(key2698, -2), (key2704, -2), (key2752, -2), (key2663, -2), (key2669, -2), (key2698, -2), (key2724, -2), (key2752, -2), (key2757, -2), (key2669, -2), (key2704, -2), (key2724, -2), (key2801, 1), (key2807, 1), (key2851, 1), (key2858, 1), (key2918, 1), (key2919, 1), (key2778, 1), (key2784, 1), (key2851, 1), (key2868, 1), (key2918, 1), (key2922, 1), (key2778, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2919, 1), (key2922, 1), (key2784, 1), (key2792, 1), (key2807, 1), (key2827, 1), (key2858, 1), (key2868, 1)]

theorem rawRowCheck7888 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block3.form5 = rawRow7888 := by decide +kernel

def row7888 : Integer.Sparse Key := [(key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2778, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, 2), (key2868, 2), (key2918, 2), (key2919, 2), (key2922, 2)]

theorem rowCheck7888 : row7888 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7888 := by decide +kernel

theorem rowEval7888 (x : Key → ℝ) : Integer.Sparse.eval row7888 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck7888, Integer.Sparse.eval_collectBalanced, rawRowCheck7888]

def rawRow7889 : Integer.Sparse Key := [(key2704, -2), (key2698, -2), (key2752, -2), (key2669, -2), (key2663, -2), (key2724, -2), (key2698, -2), (key2757, -2), (key2752, -2), (key2669, -2), (key2724, -2), (key2704, -2), (key2807, 1), (key2801, 1), (key2858, 1), (key2851, 1), (key2919, 1), (key2918, 1), (key2784, 1), (key2778, 1), (key2868, 1), (key2851, 1), (key2922, 1), (key2918, 1), (key2792, 1), (key2778, 1), (key2827, 1), (key2801, 1), (key2922, 1), (key2919, 1), (key2792, 1), (key2784, 1), (key2827, 1), (key2807, 1), (key2868, 1), (key2858, 1)]

theorem rawRowCheck7889 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block3.form5 = rawRow7889 := by decide +kernel

def row7889 : Integer.Sparse Key := [(key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2778, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, 2), (key2868, 2), (key2918, 2), (key2919, 2), (key2922, 2)]

theorem rowCheck7889 : row7889 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7889 := by decide +kernel

theorem rowEval7889 (x : Key → ℝ) : Integer.Sparse.eval row7889 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck7889, Integer.Sparse.eval_collectBalanced, rawRowCheck7889]

def rawRow7890 : Integer.Sparse Key := [(key2698, -2), (key2752, -2), (key2704, -2), (key2698, -2), (key2752, -2), (key2663, -2), (key2757, -2), (key2669, -2), (key2724, -2), (key2704, -2), (key2669, -2), (key2724, -2), (key2851, 1), (key2918, 1), (key2801, 1), (key2919, 1), (key2807, 1), (key2858, 1), (key2851, 1), (key2918, 1), (key2778, 1), (key2922, 1), (key2784, 1), (key2868, 1), (key2801, 1), (key2919, 1), (key2778, 1), (key2922, 1), (key2792, 1), (key2827, 1), (key2807, 1), (key2858, 1), (key2784, 1), (key2868, 1), (key2792, 1), (key2827, 1)]

theorem rawRowCheck7890 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block3.form5 = rawRow7890 := by decide +kernel

def row7890 : Integer.Sparse Key := [(key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2778, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, 2), (key2868, 2), (key2918, 2), (key2919, 2), (key2922, 2)]

theorem rowCheck7890 : row7890 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7890 := by decide +kernel

theorem rowEval7890 (x : Key → ℝ) : Integer.Sparse.eval row7890 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck7890, Integer.Sparse.eval_collectBalanced, rawRowCheck7890]

def rawRow7891 : Integer.Sparse Key := [(key2752, -2), (key2698, -2), (key2704, -2), (key2752, -2), (key2698, -2), (key2757, -2), (key2663, -2), (key2724, -2), (key2669, -2), (key2704, -2), (key2724, -2), (key2669, -2), (key2918, 1), (key2851, 1), (key2919, 1), (key2801, 1), (key2858, 1), (key2807, 1), (key2918, 1), (key2851, 1), (key2922, 1), (key2778, 1), (key2868, 1), (key2784, 1), (key2919, 1), (key2801, 1), (key2922, 1), (key2778, 1), (key2827, 1), (key2792, 1), (key2858, 1), (key2807, 1), (key2868, 1), (key2784, 1), (key2827, 1), (key2792, 1)]

theorem rawRowCheck7891 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block3.form5 = rawRow7891 := by decide +kernel

def row7891 : Integer.Sparse Key := [(key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2778, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, 2), (key2868, 2), (key2918, 2), (key2919, 2), (key2922, 2)]

theorem rowCheck7891 : row7891 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7891 := by decide +kernel

theorem rowEval7891 (x : Key → ℝ) : Integer.Sparse.eval row7891 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck7891, Integer.Sparse.eval_collectBalanced, rawRowCheck7891]

def rawRow7892 : Integer.Sparse Key := [(key2704, -2), (key2752, -2), (key2698, -2), (key2724, -2), (key2757, -2), (key2669, -2), (key2752, -2), (key2663, -2), (key2698, -2), (key2724, -2), (key2669, -2), (key2704, -2), (key2858, 1), (key2919, 1), (key2807, 1), (key2918, 1), (key2801, 1), (key2851, 1), (key2868, 1), (key2922, 1), (key2784, 1), (key2918, 1), (key2778, 1), (key2851, 1), (key2827, 1), (key2922, 1), (key2792, 1), (key2919, 1), (key2778, 1), (key2801, 1), (key2827, 1), (key2868, 1), (key2792, 1), (key2858, 1), (key2784, 1), (key2807, 1)]

theorem rawRowCheck7892 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block3.form5 = rawRow7892 := by decide +kernel

def row7892 : Integer.Sparse Key := [(key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2778, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, 2), (key2868, 2), (key2918, 2), (key2919, 2), (key2922, 2)]

theorem rowCheck7892 : row7892 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7892 := by decide +kernel

theorem rowEval7892 (x : Key → ℝ) : Integer.Sparse.eval row7892 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck7892, Integer.Sparse.eval_collectBalanced, rawRowCheck7892]

def rawRow7893 : Integer.Sparse Key := [(key2752, -2), (key2704, -2), (key2698, -2), (key2757, -2), (key2724, -2), (key2752, -2), (key2669, -2), (key2698, -2), (key2663, -2), (key2724, -2), (key2704, -2), (key2669, -2), (key2919, 1), (key2858, 1), (key2918, 1), (key2807, 1), (key2851, 1), (key2801, 1), (key2922, 1), (key2868, 1), (key2918, 1), (key2784, 1), (key2851, 1), (key2778, 1), (key2922, 1), (key2827, 1), (key2919, 1), (key2792, 1), (key2801, 1), (key2778, 1), (key2868, 1), (key2827, 1), (key2858, 1), (key2792, 1), (key2807, 1), (key2784, 1)]

theorem rawRowCheck7893 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block3.form5 = rawRow7893 := by decide +kernel

def row7893 : Integer.Sparse Key := [(key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2778, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, 2), (key2868, 2), (key2918, 2), (key2919, 2), (key2922, 2)]

theorem rowCheck7893 : row7893 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7893 := by decide +kernel

theorem rowEval7893 (x : Key → ℝ) : Integer.Sparse.eval row7893 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck7893, Integer.Sparse.eval_collectBalanced, rawRowCheck7893]

def rawRow7894 : Integer.Sparse Key := [(key2724, -2), (key2724, -2), (key2757, -2), (key2669, -2), (key2669, -2), (key2704, -2), (key2704, -2), (key2752, -2), (key2752, -2), (key2663, -2), (key2698, -2), (key2698, -2), (key2827, 1), (key2827, 1), (key2868, 1), (key2868, 1), (key2922, 1), (key2922, 1), (key2792, 1), (key2792, 1), (key2858, 1), (key2858, 1), (key2919, 1), (key2919, 1), (key2784, 1), (key2784, 1), (key2807, 1), (key2807, 1), (key2918, 1), (key2918, 1), (key2778, 1), (key2778, 1), (key2801, 1), (key2801, 1), (key2851, 1), (key2851, 1)]

theorem rawRowCheck7894 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block3.form5 = rawRow7894 := by decide +kernel

def row7894 : Integer.Sparse Key := [(key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2778, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, 2), (key2868, 2), (key2918, 2), (key2919, 2), (key2922, 2)]

theorem rowCheck7894 : row7894 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7894 := by decide +kernel

theorem rowEval7894 (x : Key → ℝ) : Integer.Sparse.eval row7894 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck7894, Integer.Sparse.eval_collectBalanced, rawRowCheck7894]

def rawRow7895 : Integer.Sparse Key := [(key2724, -2), (key2757, -2), (key2724, -2), (key2704, -2), (key2752, -2), (key2669, -2), (key2752, -2), (key2669, -2), (key2704, -2), (key2698, -2), (key2663, -2), (key2698, -2), (key2868, 1), (key2922, 1), (key2827, 1), (key2922, 1), (key2827, 1), (key2868, 1), (key2858, 1), (key2919, 1), (key2792, 1), (key2919, 1), (key2792, 1), (key2858, 1), (key2807, 1), (key2918, 1), (key2784, 1), (key2918, 1), (key2784, 1), (key2807, 1), (key2801, 1), (key2851, 1), (key2778, 1), (key2851, 1), (key2778, 1), (key2801, 1)]

theorem rawRowCheck7895 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block3.form5 = rawRow7895 := by decide +kernel

def row7895 : Integer.Sparse Key := [(key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2778, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, 2), (key2868, 2), (key2918, 2), (key2919, 2), (key2922, 2)]

theorem rowCheck7895 : row7895 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7895 := by decide +kernel

theorem rowEval7895 (x : Key → ℝ) : Integer.Sparse.eval row7895 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck7895, Integer.Sparse.eval_collectBalanced, rawRowCheck7895]

def rawRow7896 : Integer.Sparse Key := [(key2757, -2), (key2724, -2), (key2724, -2), (key2752, -2), (key2704, -2), (key2752, -2), (key2669, -2), (key2704, -2), (key2669, -2), (key2698, -2), (key2698, -2), (key2663, -2), (key2922, 1), (key2868, 1), (key2922, 1), (key2827, 1), (key2868, 1), (key2827, 1), (key2919, 1), (key2858, 1), (key2919, 1), (key2792, 1), (key2858, 1), (key2792, 1), (key2918, 1), (key2807, 1), (key2918, 1), (key2784, 1), (key2807, 1), (key2784, 1), (key2851, 1), (key2801, 1), (key2851, 1), (key2778, 1), (key2801, 1), (key2778, 1)]

theorem rawRowCheck7896 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block3.form5 = rawRow7896 := by decide +kernel

def row7896 : Integer.Sparse Key := [(key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2778, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, 2), (key2868, 2), (key2918, 2), (key2919, 2), (key2922, 2)]

theorem rowCheck7896 : row7896 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7896 := by decide +kernel

theorem rowEval7896 (x : Key → ℝ) : Integer.Sparse.eval row7896 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck7896, Integer.Sparse.eval_collectBalanced, rawRowCheck7896]

def rawRow7897 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 6), (key2841, 6), (key2873, 6)]

theorem rawRowCheck7897 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block3.form6 = rawRow7897 := by decide +kernel

def row7897 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 12), (key2873, 6)]

theorem rowCheck7897 : row7897 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7897 := by decide +kernel

theorem rowEval7897 (x : Key → ℝ) : Integer.Sparse.eval row7897 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck7897, Integer.Sparse.eval_collectBalanced, rawRowCheck7897]

def rawRow7898 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 6), (key2873, 6), (key2841, 6)]

theorem rawRowCheck7898 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block3.form6 = rawRow7898 := by decide +kernel

def row7898 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 12), (key2873, 6)]

theorem rowCheck7898 : row7898 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7898 := by decide +kernel

theorem rowEval7898 (x : Key → ℝ) : Integer.Sparse.eval row7898 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck7898, Integer.Sparse.eval_collectBalanced, rawRowCheck7898]

def rawRow7899 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2873, 6), (key2841, 6), (key2841, 6)]

theorem rawRowCheck7899 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block3.form6 = rawRow7899 := by decide +kernel

def row7899 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 12), (key2873, 6)]

theorem rowCheck7899 : row7899 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7899 := by decide +kernel

theorem rowEval7899 (x : Key → ℝ) : Integer.Sparse.eval row7899 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck7899, Integer.Sparse.eval_collectBalanced, rawRowCheck7899]

def rawRow7900 : Integer.Sparse Key := [(key2585, -24), (key2841, 6), (key2764, 6), (key2841, 6), (key2873, 6)]

theorem rawRowCheck7900 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block3.form6 = rawRow7900 := by decide +kernel

def row7900 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 12), (key2873, 6)]

theorem rowCheck7900 : row7900 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7900 := by decide +kernel

theorem rowEval7900 (x : Key → ℝ) : Integer.Sparse.eval row7900 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck7900, Integer.Sparse.eval_collectBalanced, rawRowCheck7900]

def rawRow7901 : Integer.Sparse Key := [(key2585, -24), (key2841, 6), (key2764, 6), (key2873, 6), (key2841, 6)]

theorem rawRowCheck7901 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block3.form6 = rawRow7901 := by decide +kernel

def row7901 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 12), (key2873, 6)]

theorem rowCheck7901 : row7901 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7901 := by decide +kernel

theorem rowEval7901 (x : Key → ℝ) : Integer.Sparse.eval row7901 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck7901, Integer.Sparse.eval_collectBalanced, rawRowCheck7901]

def rawRow7902 : Integer.Sparse Key := [(key2585, -24), (key2841, 6), (key2841, 6), (key2764, 6), (key2873, 6)]

theorem rawRowCheck7902 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block3.form6 = rawRow7902 := by decide +kernel

def row7902 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 12), (key2873, 6)]

theorem rowCheck7902 : row7902 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7902 := by decide +kernel

theorem rowEval7902 (x : Key → ℝ) : Integer.Sparse.eval row7902 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck7902, Integer.Sparse.eval_collectBalanced, rawRowCheck7902]

def rawRow7903 : Integer.Sparse Key := [(key2585, -24), (key2841, 6), (key2841, 6), (key2873, 6), (key2764, 6)]

theorem rawRowCheck7903 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block3.form6 = rawRow7903 := by decide +kernel

def row7903 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 12), (key2873, 6)]

theorem rowCheck7903 : row7903 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7903 := by decide +kernel

theorem rowEval7903 (x : Key → ℝ) : Integer.Sparse.eval row7903 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck7903, Integer.Sparse.eval_collectBalanced, rawRowCheck7903]

def rawRow7904 : Integer.Sparse Key := [(key2585, -24), (key2841, 6), (key2873, 6), (key2764, 6), (key2841, 6)]

theorem rawRowCheck7904 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block3.form6 = rawRow7904 := by decide +kernel

def row7904 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 12), (key2873, 6)]

theorem rowCheck7904 : row7904 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7904 := by decide +kernel

theorem rowEval7904 (x : Key → ℝ) : Integer.Sparse.eval row7904 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck7904, Integer.Sparse.eval_collectBalanced, rawRowCheck7904]

def rawRow7905 : Integer.Sparse Key := [(key2585, -24), (key2841, 6), (key2873, 6), (key2841, 6), (key2764, 6)]

theorem rawRowCheck7905 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block3.form6 = rawRow7905 := by decide +kernel

def row7905 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 12), (key2873, 6)]

theorem rowCheck7905 : row7905 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7905 := by decide +kernel

theorem rowEval7905 (x : Key → ℝ) : Integer.Sparse.eval row7905 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck7905, Integer.Sparse.eval_collectBalanced, rawRowCheck7905]

def rawRow7906 : Integer.Sparse Key := [(key2585, -24), (key2873, 6), (key2764, 6), (key2841, 6), (key2841, 6)]

theorem rawRowCheck7906 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block3.form6 = rawRow7906 := by decide +kernel

def row7906 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 12), (key2873, 6)]

theorem rowCheck7906 : row7906 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7906 := by decide +kernel

theorem rowEval7906 (x : Key → ℝ) : Integer.Sparse.eval row7906 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck7906, Integer.Sparse.eval_collectBalanced, rawRowCheck7906]

def rawRow7907 : Integer.Sparse Key := [(key2585, -24), (key2873, 6), (key2841, 6), (key2764, 6), (key2841, 6)]

theorem rawRowCheck7907 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block3.form6 = rawRow7907 := by decide +kernel

def row7907 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 12), (key2873, 6)]

theorem rowCheck7907 : row7907 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7907 := by decide +kernel

theorem rowEval7907 (x : Key → ℝ) : Integer.Sparse.eval row7907 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck7907, Integer.Sparse.eval_collectBalanced, rawRowCheck7907]

def rawRow7908 : Integer.Sparse Key := [(key2585, -24), (key2873, 6), (key2841, 6), (key2841, 6), (key2764, 6)]

theorem rawRowCheck7908 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block3.form6 = rawRow7908 := by decide +kernel

def row7908 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 12), (key2873, 6)]

theorem rowCheck7908 : row7908 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7908 := by decide +kernel

theorem rowEval7908 (x : Key → ℝ) : Integer.Sparse.eval row7908 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck7908, Integer.Sparse.eval_collectBalanced, rawRowCheck7908]

def rawRow7909 : Integer.Sparse Key := [(key2764, -24), (key2585, 6), (key2841, 6), (key2841, 6), (key2873, 6)]

theorem rawRowCheck7909 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form6 = rawRow7909 := by decide +kernel

def row7909 : Integer.Sparse Key := [(key2585, 6), (key2764, -24), (key2841, 12), (key2873, 6)]

theorem rowCheck7909 : row7909 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7909 := by decide +kernel

theorem rowEval7909 (x : Key → ℝ) : Integer.Sparse.eval row7909 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck7909, Integer.Sparse.eval_collectBalanced, rawRowCheck7909]

def rawRow7910 : Integer.Sparse Key := [(key2764, -24), (key2585, 6), (key2841, 6), (key2873, 6), (key2841, 6)]

theorem rawRowCheck7910 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form6 = rawRow7910 := by decide +kernel

def row7910 : Integer.Sparse Key := [(key2585, 6), (key2764, -24), (key2841, 12), (key2873, 6)]

theorem rowCheck7910 : row7910 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7910 := by decide +kernel

theorem rowEval7910 (x : Key → ℝ) : Integer.Sparse.eval row7910 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck7910, Integer.Sparse.eval_collectBalanced, rawRowCheck7910]

def rawRow7911 : Integer.Sparse Key := [(key2764, -24), (key2585, 6), (key2873, 6), (key2841, 6), (key2841, 6)]

theorem rawRowCheck7911 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form6 = rawRow7911 := by decide +kernel

def row7911 : Integer.Sparse Key := [(key2585, 6), (key2764, -24), (key2841, 12), (key2873, 6)]

theorem rowCheck7911 : row7911 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7911 := by decide +kernel

theorem rowEval7911 (x : Key → ℝ) : Integer.Sparse.eval row7911 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck7911, Integer.Sparse.eval_collectBalanced, rawRowCheck7911]

def rawRow7912 : Integer.Sparse Key := [(key2764, -24), (key2841, 6), (key2585, 6), (key2841, 6), (key2873, 6)]

theorem rawRowCheck7912 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form6 = rawRow7912 := by decide +kernel

def row7912 : Integer.Sparse Key := [(key2585, 6), (key2764, -24), (key2841, 12), (key2873, 6)]

theorem rowCheck7912 : row7912 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7912 := by decide +kernel

theorem rowEval7912 (x : Key → ℝ) : Integer.Sparse.eval row7912 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck7912, Integer.Sparse.eval_collectBalanced, rawRowCheck7912]

def rawRow7913 : Integer.Sparse Key := [(key2764, -24), (key2841, 6), (key2585, 6), (key2873, 6), (key2841, 6)]

theorem rawRowCheck7913 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form6 = rawRow7913 := by decide +kernel

def row7913 : Integer.Sparse Key := [(key2585, 6), (key2764, -24), (key2841, 12), (key2873, 6)]

theorem rowCheck7913 : row7913 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7913 := by decide +kernel

theorem rowEval7913 (x : Key → ℝ) : Integer.Sparse.eval row7913 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck7913, Integer.Sparse.eval_collectBalanced, rawRowCheck7913]

def rawRow7914 : Integer.Sparse Key := [(key2764, -24), (key2841, 6), (key2841, 6), (key2585, 6), (key2873, 6)]

theorem rawRowCheck7914 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form6 = rawRow7914 := by decide +kernel

def row7914 : Integer.Sparse Key := [(key2585, 6), (key2764, -24), (key2841, 12), (key2873, 6)]

theorem rowCheck7914 : row7914 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7914 := by decide +kernel

theorem rowEval7914 (x : Key → ℝ) : Integer.Sparse.eval row7914 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck7914, Integer.Sparse.eval_collectBalanced, rawRowCheck7914]

def rawRow7915 : Integer.Sparse Key := [(key2764, -24), (key2841, 6), (key2841, 6), (key2873, 6), (key2585, 6)]

theorem rawRowCheck7915 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form6 = rawRow7915 := by decide +kernel

def row7915 : Integer.Sparse Key := [(key2585, 6), (key2764, -24), (key2841, 12), (key2873, 6)]

theorem rowCheck7915 : row7915 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7915 := by decide +kernel

theorem rowEval7915 (x : Key → ℝ) : Integer.Sparse.eval row7915 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck7915, Integer.Sparse.eval_collectBalanced, rawRowCheck7915]

def rawRow7916 : Integer.Sparse Key := [(key2764, -24), (key2841, 6), (key2873, 6), (key2585, 6), (key2841, 6)]

theorem rawRowCheck7916 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form6 = rawRow7916 := by decide +kernel

def row7916 : Integer.Sparse Key := [(key2585, 6), (key2764, -24), (key2841, 12), (key2873, 6)]

theorem rowCheck7916 : row7916 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7916 := by decide +kernel

theorem rowEval7916 (x : Key → ℝ) : Integer.Sparse.eval row7916 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck7916, Integer.Sparse.eval_collectBalanced, rawRowCheck7916]

def rawRow7917 : Integer.Sparse Key := [(key2764, -24), (key2841, 6), (key2873, 6), (key2841, 6), (key2585, 6)]

theorem rawRowCheck7917 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form6 = rawRow7917 := by decide +kernel

def row7917 : Integer.Sparse Key := [(key2585, 6), (key2764, -24), (key2841, 12), (key2873, 6)]

theorem rowCheck7917 : row7917 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7917 := by decide +kernel

theorem rowEval7917 (x : Key → ℝ) : Integer.Sparse.eval row7917 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck7917, Integer.Sparse.eval_collectBalanced, rawRowCheck7917]

def rawRow7918 : Integer.Sparse Key := [(key2764, -24), (key2873, 6), (key2585, 6), (key2841, 6), (key2841, 6)]

theorem rawRowCheck7918 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form6 = rawRow7918 := by decide +kernel

def row7918 : Integer.Sparse Key := [(key2585, 6), (key2764, -24), (key2841, 12), (key2873, 6)]

theorem rowCheck7918 : row7918 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7918 := by decide +kernel

theorem rowEval7918 (x : Key → ℝ) : Integer.Sparse.eval row7918 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck7918, Integer.Sparse.eval_collectBalanced, rawRowCheck7918]

def rawRow7919 : Integer.Sparse Key := [(key2764, -24), (key2873, 6), (key2841, 6), (key2585, 6), (key2841, 6)]

theorem rawRowCheck7919 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form6 = rawRow7919 := by decide +kernel

def row7919 : Integer.Sparse Key := [(key2585, 6), (key2764, -24), (key2841, 12), (key2873, 6)]

theorem rowCheck7919 : row7919 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7919 := by decide +kernel

theorem rowEval7919 (x : Key → ℝ) : Integer.Sparse.eval row7919 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck7919, Integer.Sparse.eval_collectBalanced, rawRowCheck7919]

def rawRow7920 : Integer.Sparse Key := [(key2764, -24), (key2873, 6), (key2841, 6), (key2841, 6), (key2585, 6)]

theorem rawRowCheck7920 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form6 = rawRow7920 := by decide +kernel

def row7920 : Integer.Sparse Key := [(key2585, 6), (key2764, -24), (key2841, 12), (key2873, 6)]

theorem rowCheck7920 : row7920 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7920 := by decide +kernel

theorem rowEval7920 (x : Key → ℝ) : Integer.Sparse.eval row7920 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck7920, Integer.Sparse.eval_collectBalanced, rawRowCheck7920]

def rawRow7921 : Integer.Sparse Key := [(key2608, -2), (key2614, -2), (key2614, -2), (key2624, -2), (key2630, -2), (key2624, -2), (key2638, -2), (key2630, -2), (key2638, -2), (key2657, -2), (key2657, -2), (key2659, -2), (key2663, 2), (key2669, 2), (key2669, 2), (key2698, 2), (key2704, 2), (key2698, 2), (key2724, 2), (key2704, 2), (key2724, 2), (key2752, 2), (key2752, 2), (key2757, 2)]

theorem rawRowCheck7921 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block3.form7 = rawRow7921 := by decide +kernel

def row7921 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, -4), (key2630, -4), (key2638, -4), (key2657, -4), (key2659, -2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2)]

theorem rowCheck7921 : row7921 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7921 := by decide +kernel

theorem rowEval7921 (x : Key → ℝ) : Integer.Sparse.eval row7921 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck7921, Integer.Sparse.eval_collectBalanced, rawRowCheck7921]

def rawRow7922 : Integer.Sparse Key := [(key2614, -2), (key2608, -2), (key2614, -2), (key2630, -2), (key2624, -2), (key2638, -2), (key2624, -2), (key2638, -2), (key2630, -2), (key2657, -2), (key2659, -2), (key2657, -2), (key2669, 2), (key2663, 2), (key2669, 2), (key2704, 2), (key2698, 2), (key2724, 2), (key2698, 2), (key2724, 2), (key2704, 2), (key2752, 2), (key2757, 2), (key2752, 2)]

theorem rawRowCheck7922 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block3.form7 = rawRow7922 := by decide +kernel

def row7922 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, -4), (key2630, -4), (key2638, -4), (key2657, -4), (key2659, -2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2)]

theorem rowCheck7922 : row7922 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7922 := by decide +kernel

theorem rowEval7922 (x : Key → ℝ) : Integer.Sparse.eval row7922 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck7922, Integer.Sparse.eval_collectBalanced, rawRowCheck7922]

def rawRow7923 : Integer.Sparse Key := [(key2614, -2), (key2614, -2), (key2608, -2), (key2638, -2), (key2638, -2), (key2630, -2), (key2630, -2), (key2624, -2), (key2624, -2), (key2659, -2), (key2657, -2), (key2657, -2), (key2669, 2), (key2669, 2), (key2663, 2), (key2724, 2), (key2724, 2), (key2704, 2), (key2704, 2), (key2698, 2), (key2698, 2), (key2757, 2), (key2752, 2), (key2752, 2)]

theorem rawRowCheck7923 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block3.form7 = rawRow7923 := by decide +kernel

def row7923 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, -4), (key2630, -4), (key2638, -4), (key2657, -4), (key2659, -2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2)]

theorem rowCheck7923 : row7923 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7923 := by decide +kernel

theorem rowEval7923 (x : Key → ℝ) : Integer.Sparse.eval row7923 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck7923, Integer.Sparse.eval_collectBalanced, rawRowCheck7923]

def rawRow7924 : Integer.Sparse Key := [(key2624, -2), (key2630, -2), (key2638, -2), (key2608, -2), (key2614, -2), (key2624, -2), (key2638, -2), (key2657, -2), (key2659, -2), (key2614, -2), (key2630, -2), (key2638, -2), (key2698, 2), (key2704, 2), (key2752, 2), (key2663, 2), (key2669, 2), (key2698, 2), (key2724, 2), (key2752, 2), (key2757, 2), (key2669, 2), (key2704, 2), (key2724, 2)]

theorem rawRowCheck7924 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block3.form7 = rawRow7924 := by decide +kernel

def row7924 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, -4), (key2630, -4), (key2638, -6), (key2657, -2), (key2659, -2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2)]

theorem rowCheck7924 : row7924 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7924 := by decide +kernel

theorem rowEval7924 (x : Key → ℝ) : Integer.Sparse.eval row7924 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck7924, Integer.Sparse.eval_collectBalanced, rawRowCheck7924]

def rawRow7925 : Integer.Sparse Key := [(key2630, -2), (key2624, -2), (key2638, -2), (key2614, -2), (key2608, -2), (key2638, -2), (key2624, -2), (key2659, -2), (key2657, -2), (key2614, -2), (key2638, -2), (key2630, -2), (key2704, 2), (key2698, 2), (key2752, 2), (key2669, 2), (key2663, 2), (key2724, 2), (key2698, 2), (key2757, 2), (key2752, 2), (key2669, 2), (key2724, 2), (key2704, 2)]

theorem rawRowCheck7925 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block3.form7 = rawRow7925 := by decide +kernel

def row7925 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, -4), (key2630, -4), (key2638, -6), (key2657, -2), (key2659, -2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2)]

theorem rowCheck7925 : row7925 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7925 := by decide +kernel

theorem rowEval7925 (x : Key → ℝ) : Integer.Sparse.eval row7925 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck7925, Integer.Sparse.eval_collectBalanced, rawRowCheck7925]

def rawRow7926 : Integer.Sparse Key := [(key2624, -2), (key2638, -2), (key2630, -2), (key2624, -2), (key2638, -2), (key2608, -2), (key2659, -2), (key2614, -2), (key2638, -2), (key2630, -2), (key2614, -2), (key2638, -2), (key2698, 2), (key2752, 2), (key2704, 2), (key2698, 2), (key2752, 2), (key2663, 2), (key2757, 2), (key2669, 2), (key2724, 2), (key2704, 2), (key2669, 2), (key2724, 2)]

theorem rawRowCheck7926 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block3.form7 = rawRow7926 := by decide +kernel

def row7926 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, -4), (key2630, -4), (key2638, -8), (key2659, -2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2)]

theorem rowCheck7926 : row7926 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7926 := by decide +kernel

theorem rowEval7926 (x : Key → ℝ) : Integer.Sparse.eval row7926 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck7926, Integer.Sparse.eval_collectBalanced, rawRowCheck7926]

def rawRow7927 : Integer.Sparse Key := [(key2638, -2), (key2624, -2), (key2630, -2), (key2638, -2), (key2624, -2), (key2659, -2), (key2608, -2), (key2638, -2), (key2614, -2), (key2630, -2), (key2638, -2), (key2614, -2), (key2752, 2), (key2698, 2), (key2704, 2), (key2752, 2), (key2698, 2), (key2757, 2), (key2663, 2), (key2724, 2), (key2669, 2), (key2704, 2), (key2724, 2), (key2669, 2)]

theorem rawRowCheck7927 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block3.form7 = rawRow7927 := by decide +kernel

def row7927 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, -4), (key2630, -4), (key2638, -8), (key2659, -2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2)]

theorem rowCheck7927 : row7927 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7927 := by decide +kernel

theorem rowEval7927 (x : Key → ℝ) : Integer.Sparse.eval row7927 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck7927, Integer.Sparse.eval_collectBalanced, rawRowCheck7927]

def rawRow7928 : Integer.Sparse Key := [(key2630, -2), (key2638, -2), (key2624, -2), (key2657, -2), (key2659, -2), (key2614, -2), (key2638, -2), (key2608, -2), (key2624, -2), (key2638, -2), (key2614, -2), (key2630, -2), (key2704, 2), (key2752, 2), (key2698, 2), (key2724, 2), (key2757, 2), (key2669, 2), (key2752, 2), (key2663, 2), (key2698, 2), (key2724, 2), (key2669, 2), (key2704, 2)]

theorem rawRowCheck7928 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block3.form7 = rawRow7928 := by decide +kernel

def row7928 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, -4), (key2630, -4), (key2638, -6), (key2657, -2), (key2659, -2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2)]

theorem rowCheck7928 : row7928 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7928 := by decide +kernel

theorem rowEval7928 (x : Key → ℝ) : Integer.Sparse.eval row7928 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck7928, Integer.Sparse.eval_collectBalanced, rawRowCheck7928]

def rawRow7929 : Integer.Sparse Key := [(key2638, -2), (key2630, -2), (key2624, -2), (key2659, -2), (key2657, -2), (key2638, -2), (key2614, -2), (key2624, -2), (key2608, -2), (key2638, -2), (key2630, -2), (key2614, -2), (key2752, 2), (key2704, 2), (key2698, 2), (key2757, 2), (key2724, 2), (key2752, 2), (key2669, 2), (key2698, 2), (key2663, 2), (key2724, 2), (key2704, 2), (key2669, 2)]

theorem rawRowCheck7929 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block3.form7 = rawRow7929 := by decide +kernel

def row7929 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, -4), (key2630, -4), (key2638, -6), (key2657, -2), (key2659, -2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2)]

theorem rowCheck7929 : row7929 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7929 := by decide +kernel

theorem rowEval7929 (x : Key → ℝ) : Integer.Sparse.eval row7929 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck7929, Integer.Sparse.eval_collectBalanced, rawRowCheck7929]

def rawRow7930 : Integer.Sparse Key := [(key2657, -2), (key2657, -2), (key2659, -2), (key2614, -2), (key2614, -2), (key2630, -2), (key2630, -2), (key2638, -2), (key2638, -2), (key2608, -2), (key2624, -2), (key2624, -2), (key2724, 2), (key2724, 2), (key2757, 2), (key2669, 2), (key2669, 2), (key2704, 2), (key2704, 2), (key2752, 2), (key2752, 2), (key2663, 2), (key2698, 2), (key2698, 2)]

theorem rawRowCheck7930 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block3.form7 = rawRow7930 := by decide +kernel

def row7930 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, -4), (key2630, -4), (key2638, -4), (key2657, -4), (key2659, -2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2)]

theorem rowCheck7930 : row7930 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7930 := by decide +kernel

theorem rowEval7930 (x : Key → ℝ) : Integer.Sparse.eval row7930 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck7930, Integer.Sparse.eval_collectBalanced, rawRowCheck7930]

def rawRow7931 : Integer.Sparse Key := [(key2657, -2), (key2659, -2), (key2657, -2), (key2630, -2), (key2638, -2), (key2614, -2), (key2638, -2), (key2614, -2), (key2630, -2), (key2624, -2), (key2608, -2), (key2624, -2), (key2724, 2), (key2757, 2), (key2724, 2), (key2704, 2), (key2752, 2), (key2669, 2), (key2752, 2), (key2669, 2), (key2704, 2), (key2698, 2), (key2663, 2), (key2698, 2)]

theorem rawRowCheck7931 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block3.form7 = rawRow7931 := by decide +kernel

def row7931 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, -4), (key2630, -4), (key2638, -4), (key2657, -4), (key2659, -2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2)]

theorem rowCheck7931 : row7931 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7931 := by decide +kernel

theorem rowEval7931 (x : Key → ℝ) : Integer.Sparse.eval row7931 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck7931, Integer.Sparse.eval_collectBalanced, rawRowCheck7931]

def rawRow7932 : Integer.Sparse Key := [(key2659, -2), (key2657, -2), (key2657, -2), (key2638, -2), (key2630, -2), (key2638, -2), (key2614, -2), (key2630, -2), (key2614, -2), (key2624, -2), (key2624, -2), (key2608, -2), (key2757, 2), (key2724, 2), (key2724, 2), (key2752, 2), (key2704, 2), (key2752, 2), (key2669, 2), (key2704, 2), (key2669, 2), (key2698, 2), (key2698, 2), (key2663, 2)]

theorem rawRowCheck7932 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block3.form7 = rawRow7932 := by decide +kernel

def row7932 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, -4), (key2630, -4), (key2638, -4), (key2657, -4), (key2659, -2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2)]

theorem rowCheck7932 : row7932 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7932 := by decide +kernel

theorem rowEval7932 (x : Key → ℝ) : Integer.Sparse.eval row7932 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck7932, Integer.Sparse.eval_collectBalanced, rawRowCheck7932]

def rawRow7933 : Integer.Sparse Key := [(key2663, -2), (key2669, -2), (key2669, -2), (key2698, -2), (key2704, -2), (key2698, -2), (key2752, -2), (key2704, -2), (key2752, -2), (key2724, -2), (key2724, -2), (key2757, -2), (key2608, 2), (key2614, 2), (key2614, 2), (key2801, 2), (key2807, 2), (key2801, 2), (key2827, 2), (key2807, 2), (key2827, 2), (key3011, 2), (key3011, 2), (key3016, 2)]

theorem rawRowCheck7933 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form7 = rawRow7933 := by decide +kernel

def row7933 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2801, 4), (key2807, 4), (key2827, 4), (key3011, 4), (key3016, 2)]

theorem rowCheck7933 : row7933 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7933 := by decide +kernel

theorem rowEval7933 (x : Key → ℝ) : Integer.Sparse.eval row7933 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck7933, Integer.Sparse.eval_collectBalanced, rawRowCheck7933]

def rawRow7934 : Integer.Sparse Key := [(key2669, -2), (key2663, -2), (key2669, -2), (key2704, -2), (key2698, -2), (key2752, -2), (key2698, -2), (key2752, -2), (key2704, -2), (key2724, -2), (key2757, -2), (key2724, -2), (key2614, 2), (key2608, 2), (key2614, 2), (key2807, 2), (key2801, 2), (key2827, 2), (key2801, 2), (key2827, 2), (key2807, 2), (key3011, 2), (key3016, 2), (key3011, 2)]

theorem rawRowCheck7934 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form7 = rawRow7934 := by decide +kernel

def row7934 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2801, 4), (key2807, 4), (key2827, 4), (key3011, 4), (key3016, 2)]

theorem rowCheck7934 : row7934 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7934 := by decide +kernel

theorem rowEval7934 (x : Key → ℝ) : Integer.Sparse.eval row7934 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck7934, Integer.Sparse.eval_collectBalanced, rawRowCheck7934]

def rawRow7935 : Integer.Sparse Key := [(key2669, -2), (key2669, -2), (key2663, -2), (key2752, -2), (key2752, -2), (key2704, -2), (key2704, -2), (key2698, -2), (key2698, -2), (key2757, -2), (key2724, -2), (key2724, -2), (key2614, 2), (key2614, 2), (key2608, 2), (key2827, 2), (key2827, 2), (key2807, 2), (key2807, 2), (key2801, 2), (key2801, 2), (key3016, 2), (key3011, 2), (key3011, 2)]

theorem rawRowCheck7935 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form7 = rawRow7935 := by decide +kernel

def row7935 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2801, 4), (key2807, 4), (key2827, 4), (key3011, 4), (key3016, 2)]

theorem rowCheck7935 : row7935 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7935 := by decide +kernel

theorem rowEval7935 (x : Key → ℝ) : Integer.Sparse.eval row7935 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck7935, Integer.Sparse.eval_collectBalanced, rawRowCheck7935]

end MUB6.Certificate.GramRows

end OAI
