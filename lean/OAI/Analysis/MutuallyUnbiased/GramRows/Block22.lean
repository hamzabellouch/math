import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow800 : Integer.Sparse Key := [(key111, -6), (key102, 2), (key45, 2), (key102, 2), (key133, 6), (key102, -2), (key20, -2), (key102, -2), (key133, -2), (key70, -2), (key133, -2), (key111, 2), (key31, 2), (key111, 2)]

theorem rawRowCheck800 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form1 = rawRow800 := by decide +kernel

def row800 : Integer.Sparse Key := [(key20, -2), (key31, 2), (key45, 2), (key70, -2), (key111, -2), (key133, 2)]

theorem rowCheck800 : row800 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow800 := by decide +kernel

theorem rowEval800 (x : Key → ℝ) : Integer.Sparse.eval row800 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck800, Integer.Sparse.eval_collectBalanced, rawRowCheck800]

def rawRow801 : Integer.Sparse Key := [(key111, -6), (key102, 2), (key102, 2), (key45, 2), (key133, 6), (key102, -2), (key102, -2), (key20, -2), (key133, -2), (key133, -2), (key70, -2), (key111, 2), (key111, 2), (key31, 2)]

theorem rawRowCheck801 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form1 = rawRow801 := by decide +kernel

def row801 : Integer.Sparse Key := [(key20, -2), (key31, 2), (key45, 2), (key70, -2), (key111, -2), (key133, 2)]

theorem rowCheck801 : row801 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow801 := by decide +kernel

theorem rowEval801 (x : Key → ℝ) : Integer.Sparse.eval row801 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form1) x := by
  rw [rowCheck801, Integer.Sparse.eval_collectBalanced, rawRowCheck801]

def rawRow802 : Integer.Sparse Key := [(key70, -6), (key133, 2), (key133, 2), (key133, 2), (key31, 6), (key111, -2), (key111, -2), (key111, -2), (key20, -2), (key20, -2), (key20, -2), (key45, 2), (key45, 2), (key45, 2)]

theorem rawRowCheck802 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form1 = rawRow802 := by decide +kernel

def row802 : Integer.Sparse Key := [(key20, -6), (key31, 6), (key45, 6), (key70, -6), (key111, -6), (key133, 6)]

theorem rowCheck802 : row802 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow802 := by decide +kernel

theorem rowEval802 (x : Key → ℝ) : Integer.Sparse.eval row802 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck802, Integer.Sparse.eval_collectBalanced, rawRowCheck802]

def rawRow803 : Integer.Sparse Key := [(key133, -6), (key70, 2), (key133, 2), (key133, 2), (key111, 6), (key31, -2), (key111, -2), (key111, -2), (key45, -2), (key102, -2), (key102, -2), (key20, 2), (key102, 2), (key102, 2)]

theorem rawRowCheck803 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form1 = rawRow803 := by decide +kernel

def row803 : Integer.Sparse Key := [(key20, 2), (key31, -2), (key45, -2), (key70, 2), (key111, 2), (key133, -2)]

theorem rowCheck803 : row803 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow803 := by decide +kernel

theorem rowEval803 (x : Key → ℝ) : Integer.Sparse.eval row803 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck803, Integer.Sparse.eval_collectBalanced, rawRowCheck803]

def rawRow804 : Integer.Sparse Key := [(key133, -6), (key133, 2), (key70, 2), (key133, 2), (key111, 6), (key111, -2), (key31, -2), (key111, -2), (key102, -2), (key45, -2), (key102, -2), (key102, 2), (key20, 2), (key102, 2)]

theorem rawRowCheck804 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form1 = rawRow804 := by decide +kernel

def row804 : Integer.Sparse Key := [(key20, 2), (key31, -2), (key45, -2), (key70, 2), (key111, 2), (key133, -2)]

theorem rowCheck804 : row804 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow804 := by decide +kernel

theorem rowEval804 (x : Key → ℝ) : Integer.Sparse.eval row804 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck804, Integer.Sparse.eval_collectBalanced, rawRowCheck804]

def rawRow805 : Integer.Sparse Key := [(key133, -6), (key133, 2), (key133, 2), (key70, 2), (key111, 6), (key111, -2), (key111, -2), (key31, -2), (key102, -2), (key102, -2), (key45, -2), (key102, 2), (key102, 2), (key20, 2)]

theorem rawRowCheck805 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form1 = rawRow805 := by decide +kernel

def row805 : Integer.Sparse Key := [(key20, 2), (key31, -2), (key45, -2), (key70, 2), (key111, 2), (key133, -2)]

theorem rowCheck805 : row805 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow805 := by decide +kernel

theorem rowEval805 (x : Key → ℝ) : Integer.Sparse.eval row805 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form1) x := by
  rw [rowCheck805, Integer.Sparse.eval_collectBalanced, rawRowCheck805]

def rawRow806 : Integer.Sparse Key := [(key993, -2), (key1001, -2), (key1001, -2), (key993, 1), (key1001, 1), (key993, 1), (key1015, 1), (key1001, 1), (key1015, 1), (key1028, 2), (key1036, 2), (key1036, 2), (key1028, -1), (key1036, -1), (key1028, -1), (key1071, -1), (key1036, -1), (key1071, -1), (key1106, -1), (key1114, -1), (key1106, -1), (key1123, -1), (key1114, -1), (key1123, -1), (key1106, 1), (key1114, 1), (key1106, 1), (key1150, 1), (key1114, 1), (key1150, 1)]

theorem rawRowCheck806 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form2 = rawRow806 := by decide +kernel

def row806 : Integer.Sparse Key := [(key1001, -2), (key1015, 2), (key1036, 2), (key1071, -2), (key1123, -2), (key1150, 2)]

theorem rowCheck806 : row806 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow806 := by decide +kernel

theorem rowEval806 (x : Key → ℝ) : Integer.Sparse.eval row806 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck806, Integer.Sparse.eval_collectBalanced, rawRowCheck806]

def rawRow807 : Integer.Sparse Key := [(key1001, -2), (key993, -2), (key1001, -2), (key1001, 1), (key993, 1), (key1015, 1), (key993, 1), (key1015, 1), (key1001, 1), (key1036, 2), (key1028, 2), (key1036, 2), (key1036, -1), (key1028, -1), (key1071, -1), (key1028, -1), (key1071, -1), (key1036, -1), (key1114, -1), (key1106, -1), (key1123, -1), (key1106, -1), (key1123, -1), (key1114, -1), (key1114, 1), (key1106, 1), (key1150, 1), (key1106, 1), (key1150, 1), (key1114, 1)]

theorem rawRowCheck807 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form2 = rawRow807 := by decide +kernel

def row807 : Integer.Sparse Key := [(key1001, -2), (key1015, 2), (key1036, 2), (key1071, -2), (key1123, -2), (key1150, 2)]

theorem rowCheck807 : row807 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow807 := by decide +kernel

theorem rowEval807 (x : Key → ℝ) : Integer.Sparse.eval row807 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck807, Integer.Sparse.eval_collectBalanced, rawRowCheck807]

def rawRow808 : Integer.Sparse Key := [(key1001, -2), (key1001, -2), (key993, -2), (key1015, 1), (key1015, 1), (key1001, 1), (key1001, 1), (key993, 1), (key993, 1), (key1036, 2), (key1036, 2), (key1028, 2), (key1071, -1), (key1071, -1), (key1036, -1), (key1036, -1), (key1028, -1), (key1028, -1), (key1123, -1), (key1123, -1), (key1114, -1), (key1114, -1), (key1106, -1), (key1106, -1), (key1150, 1), (key1150, 1), (key1114, 1), (key1114, 1), (key1106, 1), (key1106, 1)]

theorem rawRowCheck808 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form2 = rawRow808 := by decide +kernel

def row808 : Integer.Sparse Key := [(key1001, -2), (key1015, 2), (key1036, 2), (key1071, -2), (key1123, -2), (key1150, 2)]

theorem rowCheck808 : row808 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow808 := by decide +kernel

theorem rowEval808 (x : Key → ℝ) : Integer.Sparse.eval row808 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck808, Integer.Sparse.eval_collectBalanced, rawRowCheck808]

def rawRow809 : Integer.Sparse Key := [(key1015, -2), (key1015, -2), (key1015, -2), (key1001, 1), (key1001, 1), (key1001, 1), (key1001, 1), (key1001, 1), (key1001, 1), (key1071, 2), (key1071, 2), (key1071, 2), (key1036, -1), (key1036, -1), (key1036, -1), (key1036, -1), (key1036, -1), (key1036, -1), (key1150, -1), (key1150, -1), (key1150, -1), (key1150, -1), (key1150, -1), (key1150, -1), (key1123, 1), (key1123, 1), (key1123, 1), (key1123, 1), (key1123, 1), (key1123, 1)]

theorem rawRowCheck809 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form2 = rawRow809 := by decide +kernel

def row809 : Integer.Sparse Key := [(key1001, 6), (key1015, -6), (key1036, -6), (key1071, 6), (key1123, 6), (key1150, -6)]

theorem rowCheck809 : row809 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow809 := by decide +kernel

theorem rowEval809 (x : Key → ℝ) : Integer.Sparse.eval row809 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck809, Integer.Sparse.eval_collectBalanced, rawRowCheck809]

def rawRow810 : Integer.Sparse Key := [(key1028, -2), (key1036, -2), (key1036, -2), (key1106, 1), (key1114, 1), (key1106, 1), (key1123, 1), (key1114, 1), (key1123, 1), (key993, 2), (key1001, 2), (key1001, 2), (key1106, -1), (key1114, -1), (key1106, -1), (key1150, -1), (key1114, -1), (key1150, -1), (key993, -1), (key1001, -1), (key993, -1), (key1015, -1), (key1001, -1), (key1015, -1), (key1028, 1), (key1036, 1), (key1028, 1), (key1071, 1), (key1036, 1), (key1071, 1)]

theorem rawRowCheck810 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form2 = rawRow810 := by decide +kernel

def row810 : Integer.Sparse Key := [(key1001, 2), (key1015, -2), (key1036, -2), (key1071, 2), (key1123, 2), (key1150, -2)]

theorem rowCheck810 : row810 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow810 := by decide +kernel

theorem rowEval810 (x : Key → ℝ) : Integer.Sparse.eval row810 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck810, Integer.Sparse.eval_collectBalanced, rawRowCheck810]

def rawRow811 : Integer.Sparse Key := [(key1036, -2), (key1028, -2), (key1036, -2), (key1114, 1), (key1106, 1), (key1123, 1), (key1106, 1), (key1123, 1), (key1114, 1), (key1001, 2), (key993, 2), (key1001, 2), (key1114, -1), (key1106, -1), (key1150, -1), (key1106, -1), (key1150, -1), (key1114, -1), (key1001, -1), (key993, -1), (key1015, -1), (key993, -1), (key1015, -1), (key1001, -1), (key1036, 1), (key1028, 1), (key1071, 1), (key1028, 1), (key1071, 1), (key1036, 1)]

theorem rawRowCheck811 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form2 = rawRow811 := by decide +kernel

def row811 : Integer.Sparse Key := [(key1001, 2), (key1015, -2), (key1036, -2), (key1071, 2), (key1123, 2), (key1150, -2)]

theorem rowCheck811 : row811 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow811 := by decide +kernel

theorem rowEval811 (x : Key → ℝ) : Integer.Sparse.eval row811 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck811, Integer.Sparse.eval_collectBalanced, rawRowCheck811]

def rawRow812 : Integer.Sparse Key := [(key1036, -2), (key1036, -2), (key1028, -2), (key1123, 1), (key1123, 1), (key1114, 1), (key1114, 1), (key1106, 1), (key1106, 1), (key1001, 2), (key1001, 2), (key993, 2), (key1150, -1), (key1150, -1), (key1114, -1), (key1114, -1), (key1106, -1), (key1106, -1), (key1015, -1), (key1015, -1), (key1001, -1), (key1001, -1), (key993, -1), (key993, -1), (key1071, 1), (key1071, 1), (key1036, 1), (key1036, 1), (key1028, 1), (key1028, 1)]

theorem rawRowCheck812 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form2 = rawRow812 := by decide +kernel

def row812 : Integer.Sparse Key := [(key1001, 2), (key1015, -2), (key1036, -2), (key1071, 2), (key1123, 2), (key1150, -2)]

theorem rowCheck812 : row812 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow812 := by decide +kernel

theorem rowEval812 (x : Key → ℝ) : Integer.Sparse.eval row812 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck812, Integer.Sparse.eval_collectBalanced, rawRowCheck812]

def rawRow813 : Integer.Sparse Key := [(key1123, -2), (key1123, -2), (key1235, -2), (key1036, 1), (key1036, 1), (key1114, 1), (key1114, 1), (key1232, 1), (key1232, 1), (key1150, 2), (key1150, 2), (key1242, 2), (key1001, -1), (key1001, -1), (key1114, -1), (key1114, -1), (key1232, -1), (key1232, -1), (key1071, -1), (key1071, -1), (key1150, -1), (key1150, -1), (key1242, -1), (key1242, -1), (key1015, 1), (key1015, 1), (key1123, 1), (key1123, 1), (key1235, 1), (key1235, 1)]

theorem rawRowCheck813 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form2 = rawRow813 := by decide +kernel

def row813 : Integer.Sparse Key := [(key1001, -2), (key1015, 2), (key1036, 2), (key1071, -2), (key1123, -2), (key1150, 2)]

theorem rowCheck813 : row813 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow813 := by decide +kernel

theorem rowEval813 (x : Key → ℝ) : Integer.Sparse.eval row813 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck813, Integer.Sparse.eval_collectBalanced, rawRowCheck813]

def rawRow814 : Integer.Sparse Key := [(key1123, -2), (key1235, -2), (key1123, -2), (key1114, 1), (key1232, 1), (key1036, 1), (key1232, 1), (key1036, 1), (key1114, 1), (key1150, 2), (key1242, 2), (key1150, 2), (key1114, -1), (key1232, -1), (key1001, -1), (key1232, -1), (key1001, -1), (key1114, -1), (key1150, -1), (key1242, -1), (key1071, -1), (key1242, -1), (key1071, -1), (key1150, -1), (key1123, 1), (key1235, 1), (key1015, 1), (key1235, 1), (key1015, 1), (key1123, 1)]

theorem rawRowCheck814 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form2 = rawRow814 := by decide +kernel

def row814 : Integer.Sparse Key := [(key1001, -2), (key1015, 2), (key1036, 2), (key1071, -2), (key1123, -2), (key1150, 2)]

theorem rowCheck814 : row814 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow814 := by decide +kernel

theorem rowEval814 (x : Key → ℝ) : Integer.Sparse.eval row814 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck814, Integer.Sparse.eval_collectBalanced, rawRowCheck814]

def rawRow815 : Integer.Sparse Key := [(key1235, -2), (key1123, -2), (key1123, -2), (key1232, 1), (key1114, 1), (key1232, 1), (key1036, 1), (key1114, 1), (key1036, 1), (key1242, 2), (key1150, 2), (key1150, 2), (key1232, -1), (key1114, -1), (key1232, -1), (key1001, -1), (key1114, -1), (key1001, -1), (key1242, -1), (key1150, -1), (key1242, -1), (key1071, -1), (key1150, -1), (key1071, -1), (key1235, 1), (key1123, 1), (key1235, 1), (key1015, 1), (key1123, 1), (key1015, 1)]

theorem rawRowCheck815 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form2 = rawRow815 := by decide +kernel

def row815 : Integer.Sparse Key := [(key1001, -2), (key1015, 2), (key1036, 2), (key1071, -2), (key1123, -2), (key1150, 2)]

theorem rowCheck815 : row815 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow815 := by decide +kernel

theorem rowEval815 (x : Key → ℝ) : Integer.Sparse.eval row815 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form2) x := by
  rw [rowCheck815, Integer.Sparse.eval_collectBalanced, rawRowCheck815]

def rawRow816 : Integer.Sparse Key := [(key1071, -2), (key1071, -2), (key1071, -2), (key1150, 1), (key1150, 1), (key1150, 1), (key1150, 1), (key1150, 1), (key1150, 1), (key1015, 2), (key1015, 2), (key1015, 2), (key1123, -1), (key1123, -1), (key1123, -1), (key1123, -1), (key1123, -1), (key1123, -1), (key1001, -1), (key1001, -1), (key1001, -1), (key1001, -1), (key1001, -1), (key1001, -1), (key1036, 1), (key1036, 1), (key1036, 1), (key1036, 1), (key1036, 1), (key1036, 1)]

theorem rawRowCheck816 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form2 = rawRow816 := by decide +kernel

def row816 : Integer.Sparse Key := [(key1001, -6), (key1015, 6), (key1036, 6), (key1071, -6), (key1123, -6), (key1150, 6)]

theorem rowCheck816 : row816 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow816 := by decide +kernel

theorem rowEval816 (x : Key → ℝ) : Integer.Sparse.eval row816 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck816, Integer.Sparse.eval_collectBalanced, rawRowCheck816]

def rawRow817 : Integer.Sparse Key := [(key1150, -2), (key1150, -2), (key1242, -2), (key1071, 1), (key1071, 1), (key1150, 1), (key1150, 1), (key1242, 1), (key1242, 1), (key1123, 2), (key1123, 2), (key1235, 2), (key1015, -1), (key1015, -1), (key1123, -1), (key1123, -1), (key1235, -1), (key1235, -1), (key1036, -1), (key1036, -1), (key1114, -1), (key1114, -1), (key1232, -1), (key1232, -1), (key1001, 1), (key1001, 1), (key1114, 1), (key1114, 1), (key1232, 1), (key1232, 1)]

theorem rawRowCheck817 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form2 = rawRow817 := by decide +kernel

def row817 : Integer.Sparse Key := [(key1001, 2), (key1015, -2), (key1036, -2), (key1071, 2), (key1123, 2), (key1150, -2)]

theorem rowCheck817 : row817 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow817 := by decide +kernel

theorem rowEval817 (x : Key → ℝ) : Integer.Sparse.eval row817 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck817, Integer.Sparse.eval_collectBalanced, rawRowCheck817]

def rawRow818 : Integer.Sparse Key := [(key1150, -2), (key1242, -2), (key1150, -2), (key1150, 1), (key1242, 1), (key1071, 1), (key1242, 1), (key1071, 1), (key1150, 1), (key1123, 2), (key1235, 2), (key1123, 2), (key1123, -1), (key1235, -1), (key1015, -1), (key1235, -1), (key1015, -1), (key1123, -1), (key1114, -1), (key1232, -1), (key1036, -1), (key1232, -1), (key1036, -1), (key1114, -1), (key1114, 1), (key1232, 1), (key1001, 1), (key1232, 1), (key1001, 1), (key1114, 1)]

theorem rawRowCheck818 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form2 = rawRow818 := by decide +kernel

def row818 : Integer.Sparse Key := [(key1001, 2), (key1015, -2), (key1036, -2), (key1071, 2), (key1123, 2), (key1150, -2)]

theorem rowCheck818 : row818 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow818 := by decide +kernel

theorem rowEval818 (x : Key → ℝ) : Integer.Sparse.eval row818 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck818, Integer.Sparse.eval_collectBalanced, rawRowCheck818]

def rawRow819 : Integer.Sparse Key := [(key1242, -2), (key1150, -2), (key1150, -2), (key1242, 1), (key1150, 1), (key1242, 1), (key1071, 1), (key1150, 1), (key1071, 1), (key1235, 2), (key1123, 2), (key1123, 2), (key1235, -1), (key1123, -1), (key1235, -1), (key1015, -1), (key1123, -1), (key1015, -1), (key1232, -1), (key1114, -1), (key1232, -1), (key1036, -1), (key1114, -1), (key1036, -1), (key1232, 1), (key1114, 1), (key1232, 1), (key1001, 1), (key1114, 1), (key1001, 1)]

theorem rawRowCheck819 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form2 = rawRow819 := by decide +kernel

def row819 : Integer.Sparse Key := [(key1001, 2), (key1015, -2), (key1036, -2), (key1071, 2), (key1123, 2), (key1150, -2)]

theorem rowCheck819 : row819 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow819 := by decide +kernel

theorem rowEval819 (x : Key → ℝ) : Integer.Sparse.eval row819 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form2) x := by
  rw [rowCheck819, Integer.Sparse.eval_collectBalanced, rawRowCheck819]

def rawRow820 : Integer.Sparse Key := [(key1, -2), (key7, -2), (key7, -2), (key7, 6), (key84, 2), (key90, 2), (key90, 2), (key90, -2), (key90, -2), (key151, -2), (key193, -6), (key193, 2), (key193, 2), (key202, 2)]

theorem rawRowCheck820 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form3 = rawRow820 := by decide +kernel

def row820 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key151, -2), (key193, -2), (key202, 2)]

theorem rowCheck820 : row820 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow820 := by decide +kernel

theorem rowEval820 (x : Key → ℝ) : Integer.Sparse.eval row820 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck820, Integer.Sparse.eval_collectBalanced, rawRowCheck820]

def rawRow821 : Integer.Sparse Key := [(key7, -2), (key1, -2), (key7, -2), (key7, 6), (key90, 2), (key84, 2), (key90, 2), (key90, -2), (key151, -2), (key90, -2), (key193, -6), (key193, 2), (key202, 2), (key193, 2)]

theorem rawRowCheck821 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form3 = rawRow821 := by decide +kernel

def row821 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key151, -2), (key193, -2), (key202, 2)]

theorem rowCheck821 : row821 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow821 := by decide +kernel

theorem rowEval821 (x : Key → ℝ) : Integer.Sparse.eval row821 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck821, Integer.Sparse.eval_collectBalanced, rawRowCheck821]

def rawRow822 : Integer.Sparse Key := [(key7, -2), (key7, -2), (key1, -2), (key7, 6), (key90, 2), (key90, 2), (key84, 2), (key151, -2), (key90, -2), (key90, -2), (key193, -6), (key202, 2), (key193, 2), (key193, 2)]

theorem rawRowCheck822 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form3 = rawRow822 := by decide +kernel

def row822 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key151, -2), (key193, -2), (key202, 2)]

theorem rowCheck822 : row822 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow822 := by decide +kernel

theorem rowEval822 (x : Key → ℝ) : Integer.Sparse.eval row822 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck822, Integer.Sparse.eval_collectBalanced, rawRowCheck822]

def rawRow823 : Integer.Sparse Key := [(key7, -2), (key7, -2), (key7, -2), (key1, 6), (key151, 2), (key151, 2), (key151, 2), (key84, -2), (key84, -2), (key84, -2), (key202, -6), (key193, 2), (key193, 2), (key193, 2)]

theorem rawRowCheck823 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form3 = rawRow823 := by decide +kernel

def row823 : Integer.Sparse Key := [(key1, 6), (key7, -6), (key84, -6), (key151, 6), (key193, 6), (key202, -6)]

theorem rowCheck823 : row823 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow823 := by decide +kernel

theorem rowEval823 (x : Key → ℝ) : Integer.Sparse.eval row823 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck823, Integer.Sparse.eval_collectBalanced, rawRowCheck823]

def rawRow824 : Integer.Sparse Key := [(key84, -2), (key90, -2), (key90, -2), (key151, 6), (key1, 2), (key7, 2), (key7, 2), (key193, -2), (key193, -2), (key202, -2), (key7, -6), (key90, 2), (key90, 2), (key151, 2)]

theorem rawRowCheck824 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form3 = rawRow824 := by decide +kernel

def row824 : Integer.Sparse Key := [(key1, 2), (key7, -2), (key84, -2), (key151, 8), (key193, -4), (key202, -2)]

theorem rowCheck824 : row824 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow824 := by decide +kernel

theorem rowEval824 (x : Key → ℝ) : Integer.Sparse.eval row824 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck824, Integer.Sparse.eval_collectBalanced, rawRowCheck824]

def rawRow825 : Integer.Sparse Key := [(key90, -2), (key84, -2), (key90, -2), (key151, 6), (key7, 2), (key1, 2), (key7, 2), (key193, -2), (key202, -2), (key193, -2), (key7, -6), (key90, 2), (key151, 2), (key90, 2)]

theorem rawRowCheck825 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form3 = rawRow825 := by decide +kernel

def row825 : Integer.Sparse Key := [(key1, 2), (key7, -2), (key84, -2), (key151, 8), (key193, -4), (key202, -2)]

theorem rowCheck825 : row825 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow825 := by decide +kernel

theorem rowEval825 (x : Key → ℝ) : Integer.Sparse.eval row825 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck825, Integer.Sparse.eval_collectBalanced, rawRowCheck825]

def rawRow826 : Integer.Sparse Key := [(key90, -2), (key90, -2), (key84, -2), (key151, 6), (key7, 2), (key7, 2), (key1, 2), (key202, -2), (key193, -2), (key193, -2), (key7, -6), (key151, 2), (key90, 2), (key90, 2)]

theorem rawRowCheck826 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form3 = rawRow826 := by decide +kernel

def row826 : Integer.Sparse Key := [(key1, 2), (key7, -2), (key84, -2), (key151, 8), (key193, -4), (key202, -2)]

theorem rowCheck826 : row826 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow826 := by decide +kernel

theorem rowEval826 (x : Key → ℝ) : Integer.Sparse.eval row826 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck826, Integer.Sparse.eval_collectBalanced, rawRowCheck826]

def rawRow827 : Integer.Sparse Key := [(key90, -2), (key90, -2), (key151, -2), (key84, 6), (key193, 2), (key193, 2), (key202, 2), (key1, -2), (key84, -2), (key84, -2), (key151, -6), (key7, 2), (key90, 2), (key90, 2)]

theorem rawRowCheck827 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form3 = rawRow827 := by decide +kernel

def row827 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key151, -8), (key193, 4), (key202, 2)]

theorem rowCheck827 : row827 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow827 := by decide +kernel

theorem rowEval827 (x : Key → ℝ) : Integer.Sparse.eval row827 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck827, Integer.Sparse.eval_collectBalanced, rawRowCheck827]

def rawRow828 : Integer.Sparse Key := [(key90, -2), (key151, -2), (key90, -2), (key84, 6), (key193, 2), (key202, 2), (key193, 2), (key84, -2), (key1, -2), (key84, -2), (key151, -6), (key90, 2), (key7, 2), (key90, 2)]

theorem rawRowCheck828 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form3 = rawRow828 := by decide +kernel

def row828 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key151, -8), (key193, 4), (key202, 2)]

theorem rowCheck828 : row828 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow828 := by decide +kernel

theorem rowEval828 (x : Key → ℝ) : Integer.Sparse.eval row828 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck828, Integer.Sparse.eval_collectBalanced, rawRowCheck828]

def rawRow829 : Integer.Sparse Key := [(key151, -2), (key90, -2), (key90, -2), (key84, 6), (key202, 2), (key193, 2), (key193, 2), (key84, -2), (key84, -2), (key1, -2), (key151, -6), (key90, 2), (key90, 2), (key7, 2)]

theorem rawRowCheck829 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form3 = rawRow829 := by decide +kernel

def row829 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key151, -8), (key193, 4), (key202, 2)]

theorem rowCheck829 : row829 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow829 := by decide +kernel

theorem rowEval829 (x : Key → ℝ) : Integer.Sparse.eval row829 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form3) x := by
  rw [rowCheck829, Integer.Sparse.eval_collectBalanced, rawRowCheck829]

def rawRow830 : Integer.Sparse Key := [(key193, -2), (key193, -2), (key193, -2), (key202, 6), (key7, 2), (key7, 2), (key7, 2), (key151, -2), (key151, -2), (key151, -2), (key1, -6), (key84, 2), (key84, 2), (key84, 2)]

theorem rawRowCheck830 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form3 = rawRow830 := by decide +kernel

def row830 : Integer.Sparse Key := [(key1, -6), (key7, 6), (key84, 6), (key151, -6), (key193, -6), (key202, 6)]

theorem rowCheck830 : row830 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow830 := by decide +kernel

theorem rowEval830 (x : Key → ℝ) : Integer.Sparse.eval row830 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck830, Integer.Sparse.eval_collectBalanced, rawRowCheck830]

def rawRow831 : Integer.Sparse Key := [(key193, -2), (key193, -2), (key202, -2), (key193, 6), (key90, 2), (key90, 2), (key151, 2), (key7, -2), (key90, -2), (key90, -2), (key84, -6), (key1, 2), (key84, 2), (key84, 2)]

theorem rawRowCheck831 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form3 = rawRow831 := by decide +kernel

def row831 : Integer.Sparse Key := [(key1, 2), (key7, -2), (key84, -2), (key151, 2), (key193, 2), (key202, -2)]

theorem rowCheck831 : row831 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow831 := by decide +kernel

theorem rowEval831 (x : Key → ℝ) : Integer.Sparse.eval row831 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck831, Integer.Sparse.eval_collectBalanced, rawRowCheck831]

end MUB6.Certificate.GramRows

end OAI
