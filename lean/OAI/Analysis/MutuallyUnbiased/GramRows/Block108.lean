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

def rawRow10752 : Integer.Sparse Key := [(key1103, -24), (key1187, 6), (key1103, 6), (key990, 6), (key1025, 6)]

theorem rawRowCheck10752 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form1 = rawRow10752 := by decide +kernel

def row10752 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

theorem rowCheck10752 : row10752 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10752 := by decide +kernel

theorem rowEval10752 (x : Key → ℝ) : Integer.Sparse.eval row10752 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10752, Integer.Sparse.eval_collectBalanced, rawRowCheck10752]

def rawRow10753 : Integer.Sparse Key := [(key1103, -24), (key1187, 6), (key1103, 6), (key1025, 6), (key990, 6)]

theorem rawRowCheck10753 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form1 = rawRow10753 := by decide +kernel

def row10753 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

theorem rowCheck10753 : row10753 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10753 := by decide +kernel

theorem rowEval10753 (x : Key → ℝ) : Integer.Sparse.eval row10753 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck10753, Integer.Sparse.eval_collectBalanced, rawRowCheck10753]

def rawRow10754 : Integer.Sparse Key := [(key1187, -24), (key990, 6), (key1025, 6), (key1103, 6), (key1103, 6)]

theorem rawRowCheck10754 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form1 = rawRow10754 := by decide +kernel

def row10754 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, 12), (key1187, -24)]

theorem rowCheck10754 : row10754 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10754 := by decide +kernel

theorem rowEval10754 (x : Key → ℝ) : Integer.Sparse.eval row10754 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10754, Integer.Sparse.eval_collectBalanced, rawRowCheck10754]

def rawRow10755 : Integer.Sparse Key := [(key1187, -24), (key990, 6), (key1103, 6), (key1025, 6), (key1103, 6)]

theorem rawRowCheck10755 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form1 = rawRow10755 := by decide +kernel

def row10755 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, 12), (key1187, -24)]

theorem rowCheck10755 : row10755 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10755 := by decide +kernel

theorem rowEval10755 (x : Key → ℝ) : Integer.Sparse.eval row10755 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10755, Integer.Sparse.eval_collectBalanced, rawRowCheck10755]

def rawRow10756 : Integer.Sparse Key := [(key1187, -24), (key990, 6), (key1103, 6), (key1103, 6), (key1025, 6)]

theorem rawRowCheck10756 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form1 = rawRow10756 := by decide +kernel

def row10756 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, 12), (key1187, -24)]

theorem rowCheck10756 : row10756 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10756 := by decide +kernel

theorem rowEval10756 (x : Key → ℝ) : Integer.Sparse.eval row10756 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10756, Integer.Sparse.eval_collectBalanced, rawRowCheck10756]

def rawRow10757 : Integer.Sparse Key := [(key1187, -24), (key1025, 6), (key990, 6), (key1103, 6), (key1103, 6)]

theorem rawRowCheck10757 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form1 = rawRow10757 := by decide +kernel

def row10757 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, 12), (key1187, -24)]

theorem rowCheck10757 : row10757 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10757 := by decide +kernel

theorem rowEval10757 (x : Key → ℝ) : Integer.Sparse.eval row10757 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10757, Integer.Sparse.eval_collectBalanced, rawRowCheck10757]

def rawRow10758 : Integer.Sparse Key := [(key1187, -24), (key1025, 6), (key1103, 6), (key990, 6), (key1103, 6)]

theorem rawRowCheck10758 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form1 = rawRow10758 := by decide +kernel

def row10758 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, 12), (key1187, -24)]

theorem rowCheck10758 : row10758 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10758 := by decide +kernel

theorem rowEval10758 (x : Key → ℝ) : Integer.Sparse.eval row10758 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10758, Integer.Sparse.eval_collectBalanced, rawRowCheck10758]

def rawRow10759 : Integer.Sparse Key := [(key1187, -24), (key1025, 6), (key1103, 6), (key1103, 6), (key990, 6)]

theorem rawRowCheck10759 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form1 = rawRow10759 := by decide +kernel

def row10759 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, 12), (key1187, -24)]

theorem rowCheck10759 : row10759 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10759 := by decide +kernel

theorem rowEval10759 (x : Key → ℝ) : Integer.Sparse.eval row10759 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck10759, Integer.Sparse.eval_collectBalanced, rawRowCheck10759]

def rawRow10760 : Integer.Sparse Key := [(key1187, -24), (key1103, 6), (key990, 6), (key1025, 6), (key1103, 6)]

theorem rawRowCheck10760 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form1 = rawRow10760 := by decide +kernel

def row10760 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, 12), (key1187, -24)]

theorem rowCheck10760 : row10760 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10760 := by decide +kernel

theorem rowEval10760 (x : Key → ℝ) : Integer.Sparse.eval row10760 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10760, Integer.Sparse.eval_collectBalanced, rawRowCheck10760]

def rawRow10761 : Integer.Sparse Key := [(key1187, -24), (key1103, 6), (key990, 6), (key1103, 6), (key1025, 6)]

theorem rawRowCheck10761 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form1 = rawRow10761 := by decide +kernel

def row10761 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, 12), (key1187, -24)]

theorem rowCheck10761 : row10761 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10761 := by decide +kernel

theorem rowEval10761 (x : Key → ℝ) : Integer.Sparse.eval row10761 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10761, Integer.Sparse.eval_collectBalanced, rawRowCheck10761]

def rawRow10762 : Integer.Sparse Key := [(key1187, -24), (key1103, 6), (key1025, 6), (key990, 6), (key1103, 6)]

theorem rawRowCheck10762 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form1 = rawRow10762 := by decide +kernel

def row10762 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, 12), (key1187, -24)]

theorem rowCheck10762 : row10762 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10762 := by decide +kernel

theorem rowEval10762 (x : Key → ℝ) : Integer.Sparse.eval row10762 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10762, Integer.Sparse.eval_collectBalanced, rawRowCheck10762]

def rawRow10763 : Integer.Sparse Key := [(key1187, -24), (key1103, 6), (key1025, 6), (key1103, 6), (key990, 6)]

theorem rawRowCheck10763 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form1 = rawRow10763 := by decide +kernel

def row10763 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, 12), (key1187, -24)]

theorem rowCheck10763 : row10763 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10763 := by decide +kernel

theorem rowEval10763 (x : Key → ℝ) : Integer.Sparse.eval row10763 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck10763, Integer.Sparse.eval_collectBalanced, rawRowCheck10763]

def rawRow10764 : Integer.Sparse Key := [(key1187, -24), (key1103, 6), (key1103, 6), (key990, 6), (key1025, 6)]

theorem rawRowCheck10764 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form1 = rawRow10764 := by decide +kernel

def row10764 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, 12), (key1187, -24)]

theorem rowCheck10764 : row10764 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10764 := by decide +kernel

theorem rowEval10764 (x : Key → ℝ) : Integer.Sparse.eval row10764 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10764, Integer.Sparse.eval_collectBalanced, rawRowCheck10764]

def rawRow10765 : Integer.Sparse Key := [(key1187, -24), (key1103, 6), (key1103, 6), (key1025, 6), (key990, 6)]

theorem rawRowCheck10765 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form1 = rawRow10765 := by decide +kernel

def row10765 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, 12), (key1187, -24)]

theorem rowCheck10765 : row10765 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10765 := by decide +kernel

theorem rowEval10765 (x : Key → ℝ) : Integer.Sparse.eval row10765 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck10765, Integer.Sparse.eval_collectBalanced, rawRowCheck10765]

def rawRow10766 : Integer.Sparse Key := [(key1107, -6), (key1112, -6), (key1121, -6), (key1148, -6), (key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1107, 2), (key1191, 2), (key1121, 2), (key1197, 2), (key1069, 2), (key1148, 2), (key1210, 2)]

theorem rawRowCheck10766 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form2 = rawRow10766 := by decide +kernel

def row10766 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

theorem rowCheck10766 : row10766 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10766 := by decide +kernel

theorem rowEval10766 (x : Key → ℝ) : Integer.Sparse.eval row10766 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck10766, Integer.Sparse.eval_collectBalanced, rawRowCheck10766]

def rawRow10767 : Integer.Sparse Key := [(key1112, -6), (key1107, -6), (key1121, -6), (key1148, -6), (key999, 2), (key994, 2), (key1013, 2), (key1034, 2), (key1029, 2), (key1191, 2), (key1107, 2), (key1197, 2), (key1121, 2), (key1069, 2), (key1210, 2), (key1148, 2)]

theorem rawRowCheck10767 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form2 = rawRow10767 := by decide +kernel

def row10767 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

theorem rowCheck10767 : row10767 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10767 := by decide +kernel

theorem rowEval10767 (x : Key → ℝ) : Integer.Sparse.eval row10767 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10767, Integer.Sparse.eval_collectBalanced, rawRowCheck10767]

def rawRow10768 : Integer.Sparse Key := [(key1107, -6), (key1121, -6), (key1112, -6), (key1148, -6), (key994, 2), (key1013, 2), (key999, 2), (key1107, 2), (key1121, 2), (key1029, 2), (key1197, 2), (key1034, 2), (key1191, 2), (key1148, 2), (key1069, 2), (key1210, 2)]

theorem rawRowCheck10768 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form2 = rawRow10768 := by decide +kernel

def row10768 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

theorem rowCheck10768 : row10768 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10768 := by decide +kernel

theorem rowEval10768 (x : Key → ℝ) : Integer.Sparse.eval row10768 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck10768, Integer.Sparse.eval_collectBalanced, rawRowCheck10768]

def rawRow10769 : Integer.Sparse Key := [(key1121, -6), (key1107, -6), (key1112, -6), (key1148, -6), (key1013, 2), (key994, 2), (key999, 2), (key1121, 2), (key1107, 2), (key1197, 2), (key1029, 2), (key1191, 2), (key1034, 2), (key1148, 2), (key1210, 2), (key1069, 2)]

theorem rawRowCheck10769 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form2 = rawRow10769 := by decide +kernel

def row10769 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

theorem rowCheck10769 : row10769 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10769 := by decide +kernel

theorem rowEval10769 (x : Key → ℝ) : Integer.Sparse.eval row10769 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck10769, Integer.Sparse.eval_collectBalanced, rawRowCheck10769]

def rawRow10770 : Integer.Sparse Key := [(key1112, -6), (key1121, -6), (key1107, -6), (key1148, -6), (key999, 2), (key1013, 2), (key994, 2), (key1191, 2), (key1197, 2), (key1034, 2), (key1121, 2), (key1029, 2), (key1107, 2), (key1210, 2), (key1069, 2), (key1148, 2)]

theorem rawRowCheck10770 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form2 = rawRow10770 := by decide +kernel

def row10770 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

theorem rowCheck10770 : row10770 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10770 := by decide +kernel

theorem rowEval10770 (x : Key → ℝ) : Integer.Sparse.eval row10770 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10770, Integer.Sparse.eval_collectBalanced, rawRowCheck10770]

def rawRow10771 : Integer.Sparse Key := [(key1121, -6), (key1112, -6), (key1107, -6), (key1148, -6), (key1013, 2), (key999, 2), (key994, 2), (key1197, 2), (key1191, 2), (key1121, 2), (key1034, 2), (key1107, 2), (key1029, 2), (key1210, 2), (key1148, 2), (key1069, 2)]

theorem rawRowCheck10771 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form2 = rawRow10771 := by decide +kernel

def row10771 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

theorem rowCheck10771 : row10771 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10771 := by decide +kernel

theorem rowEval10771 (x : Key → ℝ) : Integer.Sparse.eval row10771 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck10771, Integer.Sparse.eval_collectBalanced, rawRowCheck10771]

def rawRow10772 : Integer.Sparse Key := [(key1107, -6), (key1112, -6), (key1148, -6), (key1121, -6), (key1029, 2), (key1034, 2), (key1069, 2), (key994, 2), (key999, 2), (key1107, 2), (key1191, 2), (key1148, 2), (key1210, 2), (key1013, 2), (key1121, 2), (key1197, 2)]

theorem rawRowCheck10772 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form2 = rawRow10772 := by decide +kernel

def row10772 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

theorem rowCheck10772 : row10772 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10772 := by decide +kernel

theorem rowEval10772 (x : Key → ℝ) : Integer.Sparse.eval row10772 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck10772, Integer.Sparse.eval_collectBalanced, rawRowCheck10772]

def rawRow10773 : Integer.Sparse Key := [(key1112, -6), (key1107, -6), (key1148, -6), (key1121, -6), (key1034, 2), (key1029, 2), (key1069, 2), (key999, 2), (key994, 2), (key1191, 2), (key1107, 2), (key1210, 2), (key1148, 2), (key1013, 2), (key1197, 2), (key1121, 2)]

theorem rawRowCheck10773 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form2 = rawRow10773 := by decide +kernel

def row10773 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

theorem rowCheck10773 : row10773 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10773 := by decide +kernel

theorem rowEval10773 (x : Key → ℝ) : Integer.Sparse.eval row10773 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10773, Integer.Sparse.eval_collectBalanced, rawRowCheck10773]

def rawRow10774 : Integer.Sparse Key := [(key1107, -6), (key1148, -6), (key1112, -6), (key1121, -6), (key1029, 2), (key1069, 2), (key1034, 2), (key1107, 2), (key1148, 2), (key994, 2), (key1210, 2), (key999, 2), (key1191, 2), (key1121, 2), (key1013, 2), (key1197, 2)]

theorem rawRowCheck10774 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form2 = rawRow10774 := by decide +kernel

def row10774 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

theorem rowCheck10774 : row10774 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10774 := by decide +kernel

theorem rowEval10774 (x : Key → ℝ) : Integer.Sparse.eval row10774 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck10774, Integer.Sparse.eval_collectBalanced, rawRowCheck10774]

def rawRow10775 : Integer.Sparse Key := [(key1148, -6), (key1107, -6), (key1112, -6), (key1121, -6), (key1069, 2), (key1029, 2), (key1034, 2), (key1148, 2), (key1107, 2), (key1210, 2), (key994, 2), (key1191, 2), (key999, 2), (key1121, 2), (key1197, 2), (key1013, 2)]

theorem rawRowCheck10775 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form2 = rawRow10775 := by decide +kernel

def row10775 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

theorem rowCheck10775 : row10775 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10775 := by decide +kernel

theorem rowEval10775 (x : Key → ℝ) : Integer.Sparse.eval row10775 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck10775, Integer.Sparse.eval_collectBalanced, rawRowCheck10775]

def rawRow10776 : Integer.Sparse Key := [(key1112, -6), (key1148, -6), (key1107, -6), (key1121, -6), (key1034, 2), (key1069, 2), (key1029, 2), (key1191, 2), (key1210, 2), (key999, 2), (key1148, 2), (key994, 2), (key1107, 2), (key1197, 2), (key1013, 2), (key1121, 2)]

theorem rawRowCheck10776 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form2 = rawRow10776 := by decide +kernel

def row10776 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

theorem rowCheck10776 : row10776 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10776 := by decide +kernel

theorem rowEval10776 (x : Key → ℝ) : Integer.Sparse.eval row10776 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10776, Integer.Sparse.eval_collectBalanced, rawRowCheck10776]

def rawRow10777 : Integer.Sparse Key := [(key1148, -6), (key1112, -6), (key1107, -6), (key1121, -6), (key1069, 2), (key1034, 2), (key1029, 2), (key1210, 2), (key1191, 2), (key1148, 2), (key999, 2), (key1107, 2), (key994, 2), (key1197, 2), (key1121, 2), (key1013, 2)]

theorem rawRowCheck10777 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form2 = rawRow10777 := by decide +kernel

def row10777 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

theorem rowCheck10777 : row10777 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10777 := by decide +kernel

theorem rowEval10777 (x : Key → ℝ) : Integer.Sparse.eval row10777 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck10777, Integer.Sparse.eval_collectBalanced, rawRowCheck10777]

def rawRow10778 : Integer.Sparse Key := [(key1107, -6), (key1121, -6), (key1148, -6), (key1112, -6), (key1107, 2), (key1121, 2), (key1148, 2), (key994, 2), (key1013, 2), (key1029, 2), (key1197, 2), (key1069, 2), (key1210, 2), (key999, 2), (key1034, 2), (key1191, 2)]

theorem rawRowCheck10778 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form2 = rawRow10778 := by decide +kernel

def row10778 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

theorem rowCheck10778 : row10778 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10778 := by decide +kernel

theorem rowEval10778 (x : Key → ℝ) : Integer.Sparse.eval row10778 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck10778, Integer.Sparse.eval_collectBalanced, rawRowCheck10778]

def rawRow10779 : Integer.Sparse Key := [(key1121, -6), (key1107, -6), (key1148, -6), (key1112, -6), (key1121, 2), (key1107, 2), (key1148, 2), (key1013, 2), (key994, 2), (key1197, 2), (key1029, 2), (key1210, 2), (key1069, 2), (key999, 2), (key1191, 2), (key1034, 2)]

theorem rawRowCheck10779 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form2 = rawRow10779 := by decide +kernel

def row10779 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

theorem rowCheck10779 : row10779 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10779 := by decide +kernel

theorem rowEval10779 (x : Key → ℝ) : Integer.Sparse.eval row10779 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck10779, Integer.Sparse.eval_collectBalanced, rawRowCheck10779]

def rawRow10780 : Integer.Sparse Key := [(key1107, -6), (key1148, -6), (key1121, -6), (key1112, -6), (key1107, 2), (key1148, 2), (key1121, 2), (key1029, 2), (key1069, 2), (key994, 2), (key1210, 2), (key1013, 2), (key1197, 2), (key1034, 2), (key999, 2), (key1191, 2)]

theorem rawRowCheck10780 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form2 = rawRow10780 := by decide +kernel

def row10780 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

theorem rowCheck10780 : row10780 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10780 := by decide +kernel

theorem rowEval10780 (x : Key → ℝ) : Integer.Sparse.eval row10780 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck10780, Integer.Sparse.eval_collectBalanced, rawRowCheck10780]

def rawRow10781 : Integer.Sparse Key := [(key1148, -6), (key1107, -6), (key1121, -6), (key1112, -6), (key1148, 2), (key1107, 2), (key1121, 2), (key1069, 2), (key1029, 2), (key1210, 2), (key994, 2), (key1197, 2), (key1013, 2), (key1034, 2), (key1191, 2), (key999, 2)]

theorem rawRowCheck10781 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form2 = rawRow10781 := by decide +kernel

def row10781 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

theorem rowCheck10781 : row10781 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10781 := by decide +kernel

theorem rowEval10781 (x : Key → ℝ) : Integer.Sparse.eval row10781 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck10781, Integer.Sparse.eval_collectBalanced, rawRowCheck10781]

def rawRow10782 : Integer.Sparse Key := [(key1121, -6), (key1148, -6), (key1107, -6), (key1112, -6), (key1121, 2), (key1148, 2), (key1107, 2), (key1197, 2), (key1210, 2), (key1013, 2), (key1069, 2), (key994, 2), (key1029, 2), (key1191, 2), (key999, 2), (key1034, 2)]

theorem rawRowCheck10782 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form2 = rawRow10782 := by decide +kernel

def row10782 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

theorem rowCheck10782 : row10782 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10782 := by decide +kernel

theorem rowEval10782 (x : Key → ℝ) : Integer.Sparse.eval row10782 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck10782, Integer.Sparse.eval_collectBalanced, rawRowCheck10782]

def rawRow10783 : Integer.Sparse Key := [(key1148, -6), (key1121, -6), (key1107, -6), (key1112, -6), (key1148, 2), (key1121, 2), (key1107, 2), (key1210, 2), (key1197, 2), (key1069, 2), (key1013, 2), (key1029, 2), (key994, 2), (key1191, 2), (key1034, 2), (key999, 2)]

theorem rawRowCheck10783 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form2 = rawRow10783 := by decide +kernel

def row10783 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

theorem rowCheck10783 : row10783 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10783 := by decide +kernel

theorem rowEval10783 (x : Key → ℝ) : Integer.Sparse.eval row10783 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck10783, Integer.Sparse.eval_collectBalanced, rawRowCheck10783]

def rawRow10784 : Integer.Sparse Key := [(key1112, -6), (key1121, -6), (key1148, -6), (key1107, -6), (key1191, 2), (key1197, 2), (key1210, 2), (key999, 2), (key1013, 2), (key1034, 2), (key1121, 2), (key1069, 2), (key1148, 2), (key994, 2), (key1029, 2), (key1107, 2)]

theorem rawRowCheck10784 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form2 = rawRow10784 := by decide +kernel

def row10784 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

theorem rowCheck10784 : row10784 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10784 := by decide +kernel

theorem rowEval10784 (x : Key → ℝ) : Integer.Sparse.eval row10784 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10784, Integer.Sparse.eval_collectBalanced, rawRowCheck10784]

def rawRow10785 : Integer.Sparse Key := [(key1121, -6), (key1112, -6), (key1148, -6), (key1107, -6), (key1197, 2), (key1191, 2), (key1210, 2), (key1013, 2), (key999, 2), (key1121, 2), (key1034, 2), (key1148, 2), (key1069, 2), (key994, 2), (key1107, 2), (key1029, 2)]

theorem rawRowCheck10785 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form2 = rawRow10785 := by decide +kernel

def row10785 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

theorem rowCheck10785 : row10785 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10785 := by decide +kernel

theorem rowEval10785 (x : Key → ℝ) : Integer.Sparse.eval row10785 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck10785, Integer.Sparse.eval_collectBalanced, rawRowCheck10785]

def rawRow10786 : Integer.Sparse Key := [(key1112, -6), (key1148, -6), (key1121, -6), (key1107, -6), (key1191, 2), (key1210, 2), (key1197, 2), (key1034, 2), (key1069, 2), (key999, 2), (key1148, 2), (key1013, 2), (key1121, 2), (key1029, 2), (key994, 2), (key1107, 2)]

theorem rawRowCheck10786 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form2 = rawRow10786 := by decide +kernel

def row10786 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

theorem rowCheck10786 : row10786 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10786 := by decide +kernel

theorem rowEval10786 (x : Key → ℝ) : Integer.Sparse.eval row10786 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10786, Integer.Sparse.eval_collectBalanced, rawRowCheck10786]

def rawRow10787 : Integer.Sparse Key := [(key1148, -6), (key1112, -6), (key1121, -6), (key1107, -6), (key1210, 2), (key1191, 2), (key1197, 2), (key1069, 2), (key1034, 2), (key1148, 2), (key999, 2), (key1121, 2), (key1013, 2), (key1029, 2), (key1107, 2), (key994, 2)]

theorem rawRowCheck10787 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form2 = rawRow10787 := by decide +kernel

def row10787 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

theorem rowCheck10787 : row10787 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10787 := by decide +kernel

theorem rowEval10787 (x : Key → ℝ) : Integer.Sparse.eval row10787 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck10787, Integer.Sparse.eval_collectBalanced, rawRowCheck10787]

def rawRow10788 : Integer.Sparse Key := [(key1121, -6), (key1148, -6), (key1112, -6), (key1107, -6), (key1197, 2), (key1210, 2), (key1191, 2), (key1121, 2), (key1148, 2), (key1013, 2), (key1069, 2), (key999, 2), (key1034, 2), (key1107, 2), (key994, 2), (key1029, 2)]

theorem rawRowCheck10788 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form2 = rawRow10788 := by decide +kernel

def row10788 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

theorem rowCheck10788 : row10788 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10788 := by decide +kernel

theorem rowEval10788 (x : Key → ℝ) : Integer.Sparse.eval row10788 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck10788, Integer.Sparse.eval_collectBalanced, rawRowCheck10788]

def rawRow10789 : Integer.Sparse Key := [(key1148, -6), (key1121, -6), (key1112, -6), (key1107, -6), (key1210, 2), (key1197, 2), (key1191, 2), (key1148, 2), (key1121, 2), (key1069, 2), (key1013, 2), (key1034, 2), (key999, 2), (key1107, 2), (key1029, 2), (key994, 2)]

theorem rawRowCheck10789 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form2 = rawRow10789 := by decide +kernel

def row10789 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

theorem rowCheck10789 : row10789 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10789 := by decide +kernel

theorem rowEval10789 (x : Key → ℝ) : Integer.Sparse.eval row10789 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck10789, Integer.Sparse.eval_collectBalanced, rawRowCheck10789]

def rawRow10790 : Integer.Sparse Key := [(key1191, -6), (key1191, -6), (key1197, -6), (key1210, -6), (key999, 2), (key999, 2), (key1013, 2), (key1034, 2), (key1034, 2), (key1112, 2), (key1112, 2), (key1121, 2), (key1121, 2), (key1069, 2), (key1148, 2), (key1148, 2)]

theorem rawRowCheck10790 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form2 = rawRow10790 := by decide +kernel

def row10790 : Integer.Sparse Key := [(key999, 4), (key1013, 2), (key1034, 4), (key1069, 2), (key1112, 4), (key1121, 4), (key1148, 4), (key1191, -12), (key1197, -6), (key1210, -6)]

theorem rowCheck10790 : row10790 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10790 := by decide +kernel

theorem rowEval10790 (x : Key → ℝ) : Integer.Sparse.eval row10790 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10790, Integer.Sparse.eval_collectBalanced, rawRowCheck10790]

def rawRow10791 : Integer.Sparse Key := [(key1191, -6), (key1197, -6), (key1191, -6), (key1210, -6), (key999, 2), (key1013, 2), (key999, 2), (key1112, 2), (key1121, 2), (key1034, 2), (key1121, 2), (key1034, 2), (key1112, 2), (key1148, 2), (key1069, 2), (key1148, 2)]

theorem rawRowCheck10791 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form2 = rawRow10791 := by decide +kernel

def row10791 : Integer.Sparse Key := [(key999, 4), (key1013, 2), (key1034, 4), (key1069, 2), (key1112, 4), (key1121, 4), (key1148, 4), (key1191, -12), (key1197, -6), (key1210, -6)]

theorem rowCheck10791 : row10791 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10791 := by decide +kernel

theorem rowEval10791 (x : Key → ℝ) : Integer.Sparse.eval row10791 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10791, Integer.Sparse.eval_collectBalanced, rawRowCheck10791]

def rawRow10792 : Integer.Sparse Key := [(key1197, -6), (key1191, -6), (key1191, -6), (key1210, -6), (key1013, 2), (key999, 2), (key999, 2), (key1121, 2), (key1112, 2), (key1121, 2), (key1034, 2), (key1112, 2), (key1034, 2), (key1148, 2), (key1148, 2), (key1069, 2)]

theorem rawRowCheck10792 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form2 = rawRow10792 := by decide +kernel

def row10792 : Integer.Sparse Key := [(key999, 4), (key1013, 2), (key1034, 4), (key1069, 2), (key1112, 4), (key1121, 4), (key1148, 4), (key1191, -12), (key1197, -6), (key1210, -6)]

theorem rowCheck10792 : row10792 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10792 := by decide +kernel

theorem rowEval10792 (x : Key → ℝ) : Integer.Sparse.eval row10792 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck10792, Integer.Sparse.eval_collectBalanced, rawRowCheck10792]

def rawRow10793 : Integer.Sparse Key := [(key1191, -6), (key1191, -6), (key1210, -6), (key1197, -6), (key1034, 2), (key1034, 2), (key1069, 2), (key999, 2), (key999, 2), (key1112, 2), (key1112, 2), (key1148, 2), (key1148, 2), (key1013, 2), (key1121, 2), (key1121, 2)]

theorem rawRowCheck10793 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form2 = rawRow10793 := by decide +kernel

def row10793 : Integer.Sparse Key := [(key999, 4), (key1013, 2), (key1034, 4), (key1069, 2), (key1112, 4), (key1121, 4), (key1148, 4), (key1191, -12), (key1197, -6), (key1210, -6)]

theorem rowCheck10793 : row10793 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10793 := by decide +kernel

theorem rowEval10793 (x : Key → ℝ) : Integer.Sparse.eval row10793 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10793, Integer.Sparse.eval_collectBalanced, rawRowCheck10793]

def rawRow10794 : Integer.Sparse Key := [(key1191, -6), (key1210, -6), (key1191, -6), (key1197, -6), (key1034, 2), (key1069, 2), (key1034, 2), (key1112, 2), (key1148, 2), (key999, 2), (key1148, 2), (key999, 2), (key1112, 2), (key1121, 2), (key1013, 2), (key1121, 2)]

theorem rawRowCheck10794 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form2 = rawRow10794 := by decide +kernel

def row10794 : Integer.Sparse Key := [(key999, 4), (key1013, 2), (key1034, 4), (key1069, 2), (key1112, 4), (key1121, 4), (key1148, 4), (key1191, -12), (key1197, -6), (key1210, -6)]

theorem rowCheck10794 : row10794 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10794 := by decide +kernel

theorem rowEval10794 (x : Key → ℝ) : Integer.Sparse.eval row10794 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10794, Integer.Sparse.eval_collectBalanced, rawRowCheck10794]

def rawRow10795 : Integer.Sparse Key := [(key1210, -6), (key1191, -6), (key1191, -6), (key1197, -6), (key1069, 2), (key1034, 2), (key1034, 2), (key1148, 2), (key1112, 2), (key1148, 2), (key999, 2), (key1112, 2), (key999, 2), (key1121, 2), (key1121, 2), (key1013, 2)]

theorem rawRowCheck10795 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form2 = rawRow10795 := by decide +kernel

def row10795 : Integer.Sparse Key := [(key999, 4), (key1013, 2), (key1034, 4), (key1069, 2), (key1112, 4), (key1121, 4), (key1148, 4), (key1191, -12), (key1197, -6), (key1210, -6)]

theorem rowCheck10795 : row10795 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10795 := by decide +kernel

theorem rowEval10795 (x : Key → ℝ) : Integer.Sparse.eval row10795 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck10795, Integer.Sparse.eval_collectBalanced, rawRowCheck10795]

def rawRow10796 : Integer.Sparse Key := [(key1191, -6), (key1197, -6), (key1210, -6), (key1191, -6), (key1112, 2), (key1121, 2), (key1148, 2), (key999, 2), (key1013, 2), (key1034, 2), (key1121, 2), (key1069, 2), (key1148, 2), (key999, 2), (key1034, 2), (key1112, 2)]

theorem rawRowCheck10796 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form2 = rawRow10796 := by decide +kernel

def row10796 : Integer.Sparse Key := [(key999, 4), (key1013, 2), (key1034, 4), (key1069, 2), (key1112, 4), (key1121, 4), (key1148, 4), (key1191, -12), (key1197, -6), (key1210, -6)]

theorem rowCheck10796 : row10796 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10796 := by decide +kernel

theorem rowEval10796 (x : Key → ℝ) : Integer.Sparse.eval row10796 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10796, Integer.Sparse.eval_collectBalanced, rawRowCheck10796]

def rawRow10797 : Integer.Sparse Key := [(key1197, -6), (key1191, -6), (key1210, -6), (key1191, -6), (key1121, 2), (key1112, 2), (key1148, 2), (key1013, 2), (key999, 2), (key1121, 2), (key1034, 2), (key1148, 2), (key1069, 2), (key999, 2), (key1112, 2), (key1034, 2)]

theorem rawRowCheck10797 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form2 = rawRow10797 := by decide +kernel

def row10797 : Integer.Sparse Key := [(key999, 4), (key1013, 2), (key1034, 4), (key1069, 2), (key1112, 4), (key1121, 4), (key1148, 4), (key1191, -12), (key1197, -6), (key1210, -6)]

theorem rowCheck10797 : row10797 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10797 := by decide +kernel

theorem rowEval10797 (x : Key → ℝ) : Integer.Sparse.eval row10797 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck10797, Integer.Sparse.eval_collectBalanced, rawRowCheck10797]

def rawRow10798 : Integer.Sparse Key := [(key1191, -6), (key1210, -6), (key1197, -6), (key1191, -6), (key1112, 2), (key1148, 2), (key1121, 2), (key1034, 2), (key1069, 2), (key999, 2), (key1148, 2), (key1013, 2), (key1121, 2), (key1034, 2), (key999, 2), (key1112, 2)]

theorem rawRowCheck10798 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form2 = rawRow10798 := by decide +kernel

def row10798 : Integer.Sparse Key := [(key999, 4), (key1013, 2), (key1034, 4), (key1069, 2), (key1112, 4), (key1121, 4), (key1148, 4), (key1191, -12), (key1197, -6), (key1210, -6)]

theorem rowCheck10798 : row10798 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10798 := by decide +kernel

theorem rowEval10798 (x : Key → ℝ) : Integer.Sparse.eval row10798 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10798, Integer.Sparse.eval_collectBalanced, rawRowCheck10798]

def rawRow10799 : Integer.Sparse Key := [(key1210, -6), (key1191, -6), (key1197, -6), (key1191, -6), (key1148, 2), (key1112, 2), (key1121, 2), (key1069, 2), (key1034, 2), (key1148, 2), (key999, 2), (key1121, 2), (key1013, 2), (key1034, 2), (key1112, 2), (key999, 2)]

theorem rawRowCheck10799 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form2 = rawRow10799 := by decide +kernel

def row10799 : Integer.Sparse Key := [(key999, 4), (key1013, 2), (key1034, 4), (key1069, 2), (key1112, 4), (key1121, 4), (key1148, 4), (key1191, -12), (key1197, -6), (key1210, -6)]

theorem rowCheck10799 : row10799 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10799 := by decide +kernel

theorem rowEval10799 (x : Key → ℝ) : Integer.Sparse.eval row10799 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck10799, Integer.Sparse.eval_collectBalanced, rawRowCheck10799]

def rawRow10800 : Integer.Sparse Key := [(key1197, -6), (key1210, -6), (key1191, -6), (key1191, -6), (key1121, 2), (key1148, 2), (key1112, 2), (key1121, 2), (key1148, 2), (key1013, 2), (key1069, 2), (key999, 2), (key1034, 2), (key1112, 2), (key999, 2), (key1034, 2)]

theorem rawRowCheck10800 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form2 = rawRow10800 := by decide +kernel

def row10800 : Integer.Sparse Key := [(key999, 4), (key1013, 2), (key1034, 4), (key1069, 2), (key1112, 4), (key1121, 4), (key1148, 4), (key1191, -12), (key1197, -6), (key1210, -6)]

theorem rowCheck10800 : row10800 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10800 := by decide +kernel

theorem rowEval10800 (x : Key → ℝ) : Integer.Sparse.eval row10800 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck10800, Integer.Sparse.eval_collectBalanced, rawRowCheck10800]

def rawRow10801 : Integer.Sparse Key := [(key1210, -6), (key1197, -6), (key1191, -6), (key1191, -6), (key1148, 2), (key1121, 2), (key1112, 2), (key1148, 2), (key1121, 2), (key1069, 2), (key1013, 2), (key1034, 2), (key999, 2), (key1112, 2), (key1034, 2), (key999, 2)]

theorem rawRowCheck10801 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form2 = rawRow10801 := by decide +kernel

def row10801 : Integer.Sparse Key := [(key999, 4), (key1013, 2), (key1034, 4), (key1069, 2), (key1112, 4), (key1121, 4), (key1148, 4), (key1191, -12), (key1197, -6), (key1210, -6)]

theorem rowCheck10801 : row10801 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10801 := by decide +kernel

theorem rowEval10801 (x : Key → ℝ) : Integer.Sparse.eval row10801 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck10801, Integer.Sparse.eval_collectBalanced, rawRowCheck10801]

def rawRow10802 : Integer.Sparse Key := [(key2623, -6), (key2777, -6), (key2850, -6), (key2864, -6), (key2607, 2), (key2623, 2), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, 2), (key2788, 2), (key2800, 2), (key2823, 2), (key2854, 2), (key2864, 2)]

theorem rawRowCheck10802 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form3 = rawRow10802 := by decide +kernel

def row10802 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

theorem rowCheck10802 : row10802 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10802 := by decide +kernel

theorem rowEval10802 (x : Key → ℝ) : Integer.Sparse.eval row10802 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10802, Integer.Sparse.eval_collectBalanced, rawRowCheck10802]

def rawRow10803 : Integer.Sparse Key := [(key2623, -6), (key2777, -6), (key2864, -6), (key2850, -6), (key2607, 2), (key2634, 2), (key2623, 2), (key2662, 2), (key2720, 2), (key2697, 2), (key2788, 2), (key2777, 2), (key2823, 2), (key2800, 2), (key2864, 2), (key2854, 2)]

theorem rawRowCheck10803 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form3 = rawRow10803 := by decide +kernel

def row10803 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

theorem rowCheck10803 : row10803 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10803 := by decide +kernel

theorem rowEval10803 (x : Key → ℝ) : Integer.Sparse.eval row10803 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10803, Integer.Sparse.eval_collectBalanced, rawRowCheck10803]

def rawRow10804 : Integer.Sparse Key := [(key2623, -6), (key2850, -6), (key2777, -6), (key2864, -6), (key2623, 2), (key2607, 2), (key2634, 2), (key2697, 2), (key2662, 2), (key2720, 2), (key2800, 2), (key2854, 2), (key2777, 2), (key2864, 2), (key2788, 2), (key2823, 2)]

theorem rawRowCheck10804 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form3 = rawRow10804 := by decide +kernel

def row10804 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

theorem rowCheck10804 : row10804 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10804 := by decide +kernel

theorem rowEval10804 (x : Key → ℝ) : Integer.Sparse.eval row10804 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10804, Integer.Sparse.eval_collectBalanced, rawRowCheck10804]

def rawRow10805 : Integer.Sparse Key := [(key2623, -6), (key2850, -6), (key2864, -6), (key2777, -6), (key2623, 2), (key2634, 2), (key2607, 2), (key2697, 2), (key2720, 2), (key2662, 2), (key2854, 2), (key2800, 2), (key2864, 2), (key2777, 2), (key2823, 2), (key2788, 2)]

theorem rawRowCheck10805 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form3 = rawRow10805 := by decide +kernel

def row10805 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

theorem rowCheck10805 : row10805 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10805 := by decide +kernel

theorem rowEval10805 (x : Key → ℝ) : Integer.Sparse.eval row10805 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10805, Integer.Sparse.eval_collectBalanced, rawRowCheck10805]

def rawRow10806 : Integer.Sparse Key := [(key2623, -6), (key2864, -6), (key2777, -6), (key2850, -6), (key2634, 2), (key2607, 2), (key2623, 2), (key2720, 2), (key2662, 2), (key2697, 2), (key2823, 2), (key2864, 2), (key2788, 2), (key2854, 2), (key2777, 2), (key2800, 2)]

theorem rawRowCheck10806 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form3 = rawRow10806 := by decide +kernel

def row10806 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

theorem rowCheck10806 : row10806 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10806 := by decide +kernel

theorem rowEval10806 (x : Key → ℝ) : Integer.Sparse.eval row10806 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10806, Integer.Sparse.eval_collectBalanced, rawRowCheck10806]

def rawRow10807 : Integer.Sparse Key := [(key2623, -6), (key2864, -6), (key2850, -6), (key2777, -6), (key2634, 2), (key2623, 2), (key2607, 2), (key2720, 2), (key2697, 2), (key2662, 2), (key2864, 2), (key2823, 2), (key2854, 2), (key2788, 2), (key2800, 2), (key2777, 2)]

theorem rawRowCheck10807 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form3 = rawRow10807 := by decide +kernel

def row10807 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

theorem rowCheck10807 : row10807 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10807 := by decide +kernel

theorem rowEval10807 (x : Key → ℝ) : Integer.Sparse.eval row10807 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10807, Integer.Sparse.eval_collectBalanced, rawRowCheck10807]

def rawRow10808 : Integer.Sparse Key := [(key2777, -6), (key2623, -6), (key2850, -6), (key2864, -6), (key2662, 2), (key2777, 2), (key2788, 2), (key2607, 2), (key2800, 2), (key2823, 2), (key2623, 2), (key2634, 2), (key2697, 2), (key2720, 2), (key2854, 2), (key2864, 2)]

theorem rawRowCheck10808 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form3 = rawRow10808 := by decide +kernel

def row10808 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

theorem rowCheck10808 : row10808 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10808 := by decide +kernel

theorem rowEval10808 (x : Key → ℝ) : Integer.Sparse.eval row10808 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10808, Integer.Sparse.eval_collectBalanced, rawRowCheck10808]

def rawRow10809 : Integer.Sparse Key := [(key2777, -6), (key2623, -6), (key2864, -6), (key2850, -6), (key2662, 2), (key2788, 2), (key2777, 2), (key2607, 2), (key2823, 2), (key2800, 2), (key2634, 2), (key2623, 2), (key2720, 2), (key2697, 2), (key2864, 2), (key2854, 2)]

theorem rawRowCheck10809 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form3 = rawRow10809 := by decide +kernel

def row10809 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

theorem rowCheck10809 : row10809 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10809 := by decide +kernel

theorem rowEval10809 (x : Key → ℝ) : Integer.Sparse.eval row10809 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10809, Integer.Sparse.eval_collectBalanced, rawRowCheck10809]

def rawRow10810 : Integer.Sparse Key := [(key2777, -6), (key2850, -6), (key2623, -6), (key2864, -6), (key2777, 2), (key2662, 2), (key2788, 2), (key2800, 2), (key2607, 2), (key2823, 2), (key2697, 2), (key2854, 2), (key2623, 2), (key2864, 2), (key2634, 2), (key2720, 2)]

theorem rawRowCheck10810 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form3 = rawRow10810 := by decide +kernel

def row10810 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

theorem rowCheck10810 : row10810 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10810 := by decide +kernel

theorem rowEval10810 (x : Key → ℝ) : Integer.Sparse.eval row10810 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10810, Integer.Sparse.eval_collectBalanced, rawRowCheck10810]

def rawRow10811 : Integer.Sparse Key := [(key2777, -6), (key2850, -6), (key2864, -6), (key2623, -6), (key2777, 2), (key2788, 2), (key2662, 2), (key2800, 2), (key2823, 2), (key2607, 2), (key2854, 2), (key2697, 2), (key2864, 2), (key2623, 2), (key2720, 2), (key2634, 2)]

theorem rawRowCheck10811 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form3 = rawRow10811 := by decide +kernel

def row10811 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

theorem rowCheck10811 : row10811 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10811 := by decide +kernel

theorem rowEval10811 (x : Key → ℝ) : Integer.Sparse.eval row10811 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck10811, Integer.Sparse.eval_collectBalanced, rawRowCheck10811]

def rawRow10812 : Integer.Sparse Key := [(key2777, -6), (key2864, -6), (key2623, -6), (key2850, -6), (key2788, 2), (key2662, 2), (key2777, 2), (key2823, 2), (key2607, 2), (key2800, 2), (key2720, 2), (key2864, 2), (key2634, 2), (key2854, 2), (key2623, 2), (key2697, 2)]

theorem rawRowCheck10812 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form3 = rawRow10812 := by decide +kernel

def row10812 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

theorem rowCheck10812 : row10812 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10812 := by decide +kernel

theorem rowEval10812 (x : Key → ℝ) : Integer.Sparse.eval row10812 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10812, Integer.Sparse.eval_collectBalanced, rawRowCheck10812]

def rawRow10813 : Integer.Sparse Key := [(key2777, -6), (key2864, -6), (key2850, -6), (key2623, -6), (key2788, 2), (key2777, 2), (key2662, 2), (key2823, 2), (key2800, 2), (key2607, 2), (key2864, 2), (key2720, 2), (key2854, 2), (key2634, 2), (key2697, 2), (key2623, 2)]

theorem rawRowCheck10813 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form3 = rawRow10813 := by decide +kernel

def row10813 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

theorem rowCheck10813 : row10813 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10813 := by decide +kernel

theorem rowEval10813 (x : Key → ℝ) : Integer.Sparse.eval row10813 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck10813, Integer.Sparse.eval_collectBalanced, rawRowCheck10813]

def rawRow10814 : Integer.Sparse Key := [(key2850, -6), (key2623, -6), (key2777, -6), (key2864, -6), (key2697, 2), (key2800, 2), (key2854, 2), (key2623, 2), (key2777, 2), (key2864, 2), (key2607, 2), (key2634, 2), (key2662, 2), (key2720, 2), (key2788, 2), (key2823, 2)]

theorem rawRowCheck10814 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form3 = rawRow10814 := by decide +kernel

def row10814 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

theorem rowCheck10814 : row10814 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10814 := by decide +kernel

theorem rowEval10814 (x : Key → ℝ) : Integer.Sparse.eval row10814 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10814, Integer.Sparse.eval_collectBalanced, rawRowCheck10814]

def rawRow10815 : Integer.Sparse Key := [(key2850, -6), (key2623, -6), (key2864, -6), (key2777, -6), (key2697, 2), (key2854, 2), (key2800, 2), (key2623, 2), (key2864, 2), (key2777, 2), (key2634, 2), (key2607, 2), (key2720, 2), (key2662, 2), (key2823, 2), (key2788, 2)]

theorem rawRowCheck10815 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form3 = rawRow10815 := by decide +kernel

def row10815 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

theorem rowCheck10815 : row10815 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10815 := by decide +kernel

theorem rowEval10815 (x : Key → ℝ) : Integer.Sparse.eval row10815 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10815, Integer.Sparse.eval_collectBalanced, rawRowCheck10815]

def rawRow10816 : Integer.Sparse Key := [(key2850, -6), (key2777, -6), (key2623, -6), (key2864, -6), (key2800, 2), (key2697, 2), (key2854, 2), (key2777, 2), (key2623, 2), (key2864, 2), (key2662, 2), (key2788, 2), (key2607, 2), (key2823, 2), (key2634, 2), (key2720, 2)]

theorem rawRowCheck10816 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form3 = rawRow10816 := by decide +kernel

def row10816 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

theorem rowCheck10816 : row10816 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10816 := by decide +kernel

theorem rowEval10816 (x : Key → ℝ) : Integer.Sparse.eval row10816 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10816, Integer.Sparse.eval_collectBalanced, rawRowCheck10816]

def rawRow10817 : Integer.Sparse Key := [(key2850, -6), (key2777, -6), (key2864, -6), (key2623, -6), (key2800, 2), (key2854, 2), (key2697, 2), (key2777, 2), (key2864, 2), (key2623, 2), (key2788, 2), (key2662, 2), (key2823, 2), (key2607, 2), (key2720, 2), (key2634, 2)]

theorem rawRowCheck10817 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form3 = rawRow10817 := by decide +kernel

def row10817 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

theorem rowCheck10817 : row10817 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10817 := by decide +kernel

theorem rowEval10817 (x : Key → ℝ) : Integer.Sparse.eval row10817 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck10817, Integer.Sparse.eval_collectBalanced, rawRowCheck10817]

def rawRow10818 : Integer.Sparse Key := [(key2850, -6), (key2864, -6), (key2623, -6), (key2777, -6), (key2854, 2), (key2697, 2), (key2800, 2), (key2864, 2), (key2623, 2), (key2777, 2), (key2720, 2), (key2823, 2), (key2634, 2), (key2788, 2), (key2607, 2), (key2662, 2)]

theorem rawRowCheck10818 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form3 = rawRow10818 := by decide +kernel

def row10818 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

theorem rowCheck10818 : row10818 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10818 := by decide +kernel

theorem rowEval10818 (x : Key → ℝ) : Integer.Sparse.eval row10818 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10818, Integer.Sparse.eval_collectBalanced, rawRowCheck10818]

def rawRow10819 : Integer.Sparse Key := [(key2850, -6), (key2864, -6), (key2777, -6), (key2623, -6), (key2854, 2), (key2800, 2), (key2697, 2), (key2864, 2), (key2777, 2), (key2623, 2), (key2823, 2), (key2720, 2), (key2788, 2), (key2634, 2), (key2662, 2), (key2607, 2)]

theorem rawRowCheck10819 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form3 = rawRow10819 := by decide +kernel

def row10819 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

theorem rowCheck10819 : row10819 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10819 := by decide +kernel

theorem rowEval10819 (x : Key → ℝ) : Integer.Sparse.eval row10819 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck10819, Integer.Sparse.eval_collectBalanced, rawRowCheck10819]

def rawRow10820 : Integer.Sparse Key := [(key2864, -6), (key2623, -6), (key2777, -6), (key2850, -6), (key2720, 2), (key2823, 2), (key2864, 2), (key2634, 2), (key2788, 2), (key2854, 2), (key2607, 2), (key2623, 2), (key2662, 2), (key2697, 2), (key2777, 2), (key2800, 2)]

theorem rawRowCheck10820 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form3 = rawRow10820 := by decide +kernel

def row10820 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

theorem rowCheck10820 : row10820 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10820 := by decide +kernel

theorem rowEval10820 (x : Key → ℝ) : Integer.Sparse.eval row10820 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10820, Integer.Sparse.eval_collectBalanced, rawRowCheck10820]

def rawRow10821 : Integer.Sparse Key := [(key2864, -6), (key2623, -6), (key2850, -6), (key2777, -6), (key2720, 2), (key2864, 2), (key2823, 2), (key2634, 2), (key2854, 2), (key2788, 2), (key2623, 2), (key2607, 2), (key2697, 2), (key2662, 2), (key2800, 2), (key2777, 2)]

theorem rawRowCheck10821 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form3 = rawRow10821 := by decide +kernel

def row10821 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

theorem rowCheck10821 : row10821 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10821 := by decide +kernel

theorem rowEval10821 (x : Key → ℝ) : Integer.Sparse.eval row10821 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10821, Integer.Sparse.eval_collectBalanced, rawRowCheck10821]

def rawRow10822 : Integer.Sparse Key := [(key2864, -6), (key2777, -6), (key2623, -6), (key2850, -6), (key2823, 2), (key2720, 2), (key2864, 2), (key2788, 2), (key2634, 2), (key2854, 2), (key2662, 2), (key2777, 2), (key2607, 2), (key2800, 2), (key2623, 2), (key2697, 2)]

theorem rawRowCheck10822 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form3 = rawRow10822 := by decide +kernel

def row10822 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

theorem rowCheck10822 : row10822 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10822 := by decide +kernel

theorem rowEval10822 (x : Key → ℝ) : Integer.Sparse.eval row10822 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10822, Integer.Sparse.eval_collectBalanced, rawRowCheck10822]

def rawRow10823 : Integer.Sparse Key := [(key2864, -6), (key2777, -6), (key2850, -6), (key2623, -6), (key2823, 2), (key2864, 2), (key2720, 2), (key2788, 2), (key2854, 2), (key2634, 2), (key2777, 2), (key2662, 2), (key2800, 2), (key2607, 2), (key2697, 2), (key2623, 2)]

theorem rawRowCheck10823 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form3 = rawRow10823 := by decide +kernel

def row10823 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

theorem rowCheck10823 : row10823 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10823 := by decide +kernel

theorem rowEval10823 (x : Key → ℝ) : Integer.Sparse.eval row10823 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck10823, Integer.Sparse.eval_collectBalanced, rawRowCheck10823]

def rawRow10824 : Integer.Sparse Key := [(key2864, -6), (key2850, -6), (key2623, -6), (key2777, -6), (key2864, 2), (key2720, 2), (key2823, 2), (key2854, 2), (key2634, 2), (key2788, 2), (key2697, 2), (key2800, 2), (key2623, 2), (key2777, 2), (key2607, 2), (key2662, 2)]

theorem rawRowCheck10824 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form3 = rawRow10824 := by decide +kernel

def row10824 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

theorem rowCheck10824 : row10824 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10824 := by decide +kernel

theorem rowEval10824 (x : Key → ℝ) : Integer.Sparse.eval row10824 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10824, Integer.Sparse.eval_collectBalanced, rawRowCheck10824]

def rawRow10825 : Integer.Sparse Key := [(key2864, -6), (key2850, -6), (key2777, -6), (key2623, -6), (key2864, 2), (key2823, 2), (key2720, 2), (key2854, 2), (key2788, 2), (key2634, 2), (key2800, 2), (key2697, 2), (key2777, 2), (key2623, 2), (key2662, 2), (key2607, 2)]

theorem rawRowCheck10825 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form3 = rawRow10825 := by decide +kernel

def row10825 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

theorem rowCheck10825 : row10825 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10825 := by decide +kernel

theorem rowEval10825 (x : Key → ℝ) : Integer.Sparse.eval row10825 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck10825, Integer.Sparse.eval_collectBalanced, rawRowCheck10825]

def rawRow10826 : Integer.Sparse Key := [(key2634, -6), (key2788, -6), (key2854, -6), (key2854, -6), (key2607, 2), (key2623, 2), (key2623, 2), (key2662, 2), (key2697, 2), (key2697, 2), (key2777, 2), (key2777, 2), (key2800, 2), (key2800, 2), (key2850, 2), (key2850, 2)]

theorem rawRowCheck10826 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form3 = rawRow10826 := by decide +kernel

def row10826 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, 2), (key2697, 4), (key2777, 4), (key2788, -6), (key2800, 4), (key2850, 4), (key2854, -12)]

theorem rowCheck10826 : row10826 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10826 := by decide +kernel

theorem rowEval10826 (x : Key → ℝ) : Integer.Sparse.eval row10826 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10826, Integer.Sparse.eval_collectBalanced, rawRowCheck10826]

def rawRow10827 : Integer.Sparse Key := [(key2634, -6), (key2854, -6), (key2788, -6), (key2854, -6), (key2623, 2), (key2607, 2), (key2623, 2), (key2697, 2), (key2662, 2), (key2697, 2), (key2800, 2), (key2850, 2), (key2777, 2), (key2850, 2), (key2777, 2), (key2800, 2)]

theorem rawRowCheck10827 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form3 = rawRow10827 := by decide +kernel

def row10827 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, 2), (key2697, 4), (key2777, 4), (key2788, -6), (key2800, 4), (key2850, 4), (key2854, -12)]

theorem rowCheck10827 : row10827 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10827 := by decide +kernel

theorem rowEval10827 (x : Key → ℝ) : Integer.Sparse.eval row10827 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10827, Integer.Sparse.eval_collectBalanced, rawRowCheck10827]

def rawRow10828 : Integer.Sparse Key := [(key2634, -6), (key2854, -6), (key2854, -6), (key2788, -6), (key2623, 2), (key2623, 2), (key2607, 2), (key2697, 2), (key2697, 2), (key2662, 2), (key2850, 2), (key2800, 2), (key2850, 2), (key2777, 2), (key2800, 2), (key2777, 2)]

theorem rawRowCheck10828 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form3 = rawRow10828 := by decide +kernel

def row10828 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, 2), (key2697, 4), (key2777, 4), (key2788, -6), (key2800, 4), (key2850, 4), (key2854, -12)]

theorem rowCheck10828 : row10828 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10828 := by decide +kernel

theorem rowEval10828 (x : Key → ℝ) : Integer.Sparse.eval row10828 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10828, Integer.Sparse.eval_collectBalanced, rawRowCheck10828]

def rawRow10829 : Integer.Sparse Key := [(key2788, -6), (key2634, -6), (key2854, -6), (key2854, -6), (key2662, 2), (key2777, 2), (key2777, 2), (key2607, 2), (key2800, 2), (key2800, 2), (key2623, 2), (key2623, 2), (key2697, 2), (key2697, 2), (key2850, 2), (key2850, 2)]

theorem rawRowCheck10829 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form3 = rawRow10829 := by decide +kernel

def row10829 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, 2), (key2697, 4), (key2777, 4), (key2788, -6), (key2800, 4), (key2850, 4), (key2854, -12)]

theorem rowCheck10829 : row10829 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10829 := by decide +kernel

theorem rowEval10829 (x : Key → ℝ) : Integer.Sparse.eval row10829 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10829, Integer.Sparse.eval_collectBalanced, rawRowCheck10829]

def rawRow10830 : Integer.Sparse Key := [(key2788, -6), (key2854, -6), (key2634, -6), (key2854, -6), (key2777, 2), (key2662, 2), (key2777, 2), (key2800, 2), (key2607, 2), (key2800, 2), (key2697, 2), (key2850, 2), (key2623, 2), (key2850, 2), (key2623, 2), (key2697, 2)]

theorem rawRowCheck10830 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form3 = rawRow10830 := by decide +kernel

def row10830 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, 2), (key2697, 4), (key2777, 4), (key2788, -6), (key2800, 4), (key2850, 4), (key2854, -12)]

theorem rowCheck10830 : row10830 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10830 := by decide +kernel

theorem rowEval10830 (x : Key → ℝ) : Integer.Sparse.eval row10830 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10830, Integer.Sparse.eval_collectBalanced, rawRowCheck10830]

def rawRow10831 : Integer.Sparse Key := [(key2788, -6), (key2854, -6), (key2854, -6), (key2634, -6), (key2777, 2), (key2777, 2), (key2662, 2), (key2800, 2), (key2800, 2), (key2607, 2), (key2850, 2), (key2697, 2), (key2850, 2), (key2623, 2), (key2697, 2), (key2623, 2)]

theorem rawRowCheck10831 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form3 = rawRow10831 := by decide +kernel

def row10831 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, 2), (key2697, 4), (key2777, 4), (key2788, -6), (key2800, 4), (key2850, 4), (key2854, -12)]

theorem rowCheck10831 : row10831 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10831 := by decide +kernel

theorem rowEval10831 (x : Key → ℝ) : Integer.Sparse.eval row10831 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck10831, Integer.Sparse.eval_collectBalanced, rawRowCheck10831]

def rawRow10832 : Integer.Sparse Key := [(key2854, -6), (key2634, -6), (key2788, -6), (key2854, -6), (key2697, 2), (key2800, 2), (key2850, 2), (key2623, 2), (key2777, 2), (key2850, 2), (key2607, 2), (key2623, 2), (key2662, 2), (key2697, 2), (key2777, 2), (key2800, 2)]

theorem rawRowCheck10832 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form3 = rawRow10832 := by decide +kernel

def row10832 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, 2), (key2697, 4), (key2777, 4), (key2788, -6), (key2800, 4), (key2850, 4), (key2854, -12)]

theorem rowCheck10832 : row10832 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10832 := by decide +kernel

theorem rowEval10832 (x : Key → ℝ) : Integer.Sparse.eval row10832 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10832, Integer.Sparse.eval_collectBalanced, rawRowCheck10832]

def rawRow10833 : Integer.Sparse Key := [(key2854, -6), (key2634, -6), (key2854, -6), (key2788, -6), (key2697, 2), (key2850, 2), (key2800, 2), (key2623, 2), (key2850, 2), (key2777, 2), (key2623, 2), (key2607, 2), (key2697, 2), (key2662, 2), (key2800, 2), (key2777, 2)]

theorem rawRowCheck10833 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form3 = rawRow10833 := by decide +kernel

def row10833 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, 2), (key2697, 4), (key2777, 4), (key2788, -6), (key2800, 4), (key2850, 4), (key2854, -12)]

theorem rowCheck10833 : row10833 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10833 := by decide +kernel

theorem rowEval10833 (x : Key → ℝ) : Integer.Sparse.eval row10833 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10833, Integer.Sparse.eval_collectBalanced, rawRowCheck10833]

def rawRow10834 : Integer.Sparse Key := [(key2854, -6), (key2788, -6), (key2634, -6), (key2854, -6), (key2800, 2), (key2697, 2), (key2850, 2), (key2777, 2), (key2623, 2), (key2850, 2), (key2662, 2), (key2777, 2), (key2607, 2), (key2800, 2), (key2623, 2), (key2697, 2)]

theorem rawRowCheck10834 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form3 = rawRow10834 := by decide +kernel

def row10834 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, 2), (key2697, 4), (key2777, 4), (key2788, -6), (key2800, 4), (key2850, 4), (key2854, -12)]

theorem rowCheck10834 : row10834 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10834 := by decide +kernel

theorem rowEval10834 (x : Key → ℝ) : Integer.Sparse.eval row10834 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10834, Integer.Sparse.eval_collectBalanced, rawRowCheck10834]

def rawRow10835 : Integer.Sparse Key := [(key2854, -6), (key2788, -6), (key2854, -6), (key2634, -6), (key2800, 2), (key2850, 2), (key2697, 2), (key2777, 2), (key2850, 2), (key2623, 2), (key2777, 2), (key2662, 2), (key2800, 2), (key2607, 2), (key2697, 2), (key2623, 2)]

theorem rawRowCheck10835 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form3 = rawRow10835 := by decide +kernel

def row10835 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, 2), (key2697, 4), (key2777, 4), (key2788, -6), (key2800, 4), (key2850, 4), (key2854, -12)]

theorem rowCheck10835 : row10835 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10835 := by decide +kernel

theorem rowEval10835 (x : Key → ℝ) : Integer.Sparse.eval row10835 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck10835, Integer.Sparse.eval_collectBalanced, rawRowCheck10835]

def rawRow10836 : Integer.Sparse Key := [(key2854, -6), (key2854, -6), (key2634, -6), (key2788, -6), (key2850, 2), (key2697, 2), (key2800, 2), (key2850, 2), (key2623, 2), (key2777, 2), (key2697, 2), (key2800, 2), (key2623, 2), (key2777, 2), (key2607, 2), (key2662, 2)]

theorem rawRowCheck10836 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form3 = rawRow10836 := by decide +kernel

def row10836 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, 2), (key2697, 4), (key2777, 4), (key2788, -6), (key2800, 4), (key2850, 4), (key2854, -12)]

theorem rowCheck10836 : row10836 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10836 := by decide +kernel

theorem rowEval10836 (x : Key → ℝ) : Integer.Sparse.eval row10836 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10836, Integer.Sparse.eval_collectBalanced, rawRowCheck10836]

def rawRow10837 : Integer.Sparse Key := [(key2854, -6), (key2854, -6), (key2788, -6), (key2634, -6), (key2850, 2), (key2800, 2), (key2697, 2), (key2850, 2), (key2777, 2), (key2623, 2), (key2800, 2), (key2697, 2), (key2777, 2), (key2623, 2), (key2662, 2), (key2607, 2)]

theorem rawRowCheck10837 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form3 = rawRow10837 := by decide +kernel

def row10837 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, 2), (key2697, 4), (key2777, 4), (key2788, -6), (key2800, 4), (key2850, 4), (key2854, -12)]

theorem rowCheck10837 : row10837 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10837 := by decide +kernel

theorem rowEval10837 (x : Key → ℝ) : Integer.Sparse.eval row10837 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck10837, Integer.Sparse.eval_collectBalanced, rawRowCheck10837]

def rawRow10838 : Integer.Sparse Key := [(key2465, -6), (key2469, -6), (key2477, -6), (key2500, -6), (key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2465, 2), (key2536, 2), (key2477, 2), (key2541, 2), (key2434, 2), (key2500, 2), (key2552, 2)]

theorem rawRowCheck10838 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form4 = rawRow10838 := by decide +kernel

def row10838 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

theorem rowCheck10838 : row10838 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10838 := by decide +kernel

theorem rowEval10838 (x : Key → ℝ) : Integer.Sparse.eval row10838 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10838, Integer.Sparse.eval_collectBalanced, rawRowCheck10838]

def rawRow10839 : Integer.Sparse Key := [(key2469, -6), (key2465, -6), (key2477, -6), (key2500, -6), (key2375, 2), (key2371, 2), (key2387, 2), (key2403, 2), (key2399, 2), (key2536, 2), (key2465, 2), (key2541, 2), (key2477, 2), (key2434, 2), (key2552, 2), (key2500, 2)]

theorem rawRowCheck10839 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form4 = rawRow10839 := by decide +kernel

def row10839 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

theorem rowCheck10839 : row10839 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10839 := by decide +kernel

theorem rowEval10839 (x : Key → ℝ) : Integer.Sparse.eval row10839 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10839, Integer.Sparse.eval_collectBalanced, rawRowCheck10839]

def rawRow10840 : Integer.Sparse Key := [(key2465, -6), (key2477, -6), (key2469, -6), (key2500, -6), (key2371, 2), (key2387, 2), (key2375, 2), (key2465, 2), (key2477, 2), (key2399, 2), (key2541, 2), (key2403, 2), (key2536, 2), (key2500, 2), (key2434, 2), (key2552, 2)]

theorem rawRowCheck10840 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form4 = rawRow10840 := by decide +kernel

def row10840 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

theorem rowCheck10840 : row10840 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10840 := by decide +kernel

theorem rowEval10840 (x : Key → ℝ) : Integer.Sparse.eval row10840 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10840, Integer.Sparse.eval_collectBalanced, rawRowCheck10840]

def rawRow10841 : Integer.Sparse Key := [(key2477, -6), (key2465, -6), (key2469, -6), (key2500, -6), (key2387, 2), (key2371, 2), (key2375, 2), (key2477, 2), (key2465, 2), (key2541, 2), (key2399, 2), (key2536, 2), (key2403, 2), (key2500, 2), (key2552, 2), (key2434, 2)]

theorem rawRowCheck10841 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form4 = rawRow10841 := by decide +kernel

def row10841 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

theorem rowCheck10841 : row10841 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10841 := by decide +kernel

theorem rowEval10841 (x : Key → ℝ) : Integer.Sparse.eval row10841 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10841, Integer.Sparse.eval_collectBalanced, rawRowCheck10841]

def rawRow10842 : Integer.Sparse Key := [(key2469, -6), (key2477, -6), (key2465, -6), (key2500, -6), (key2375, 2), (key2387, 2), (key2371, 2), (key2536, 2), (key2541, 2), (key2403, 2), (key2477, 2), (key2399, 2), (key2465, 2), (key2552, 2), (key2434, 2), (key2500, 2)]

theorem rawRowCheck10842 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form4 = rawRow10842 := by decide +kernel

def row10842 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

theorem rowCheck10842 : row10842 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10842 := by decide +kernel

theorem rowEval10842 (x : Key → ℝ) : Integer.Sparse.eval row10842 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10842, Integer.Sparse.eval_collectBalanced, rawRowCheck10842]

def rawRow10843 : Integer.Sparse Key := [(key2477, -6), (key2469, -6), (key2465, -6), (key2500, -6), (key2387, 2), (key2375, 2), (key2371, 2), (key2541, 2), (key2536, 2), (key2477, 2), (key2403, 2), (key2465, 2), (key2399, 2), (key2552, 2), (key2500, 2), (key2434, 2)]

theorem rawRowCheck10843 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form4 = rawRow10843 := by decide +kernel

def row10843 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

theorem rowCheck10843 : row10843 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10843 := by decide +kernel

theorem rowEval10843 (x : Key → ℝ) : Integer.Sparse.eval row10843 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10843, Integer.Sparse.eval_collectBalanced, rawRowCheck10843]

def rawRow10844 : Integer.Sparse Key := [(key2465, -6), (key2469, -6), (key2500, -6), (key2477, -6), (key2399, 2), (key2403, 2), (key2434, 2), (key2371, 2), (key2375, 2), (key2465, 2), (key2536, 2), (key2500, 2), (key2552, 2), (key2387, 2), (key2477, 2), (key2541, 2)]

theorem rawRowCheck10844 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form4 = rawRow10844 := by decide +kernel

def row10844 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

theorem rowCheck10844 : row10844 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10844 := by decide +kernel

theorem rowEval10844 (x : Key → ℝ) : Integer.Sparse.eval row10844 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10844, Integer.Sparse.eval_collectBalanced, rawRowCheck10844]

def rawRow10845 : Integer.Sparse Key := [(key2469, -6), (key2465, -6), (key2500, -6), (key2477, -6), (key2403, 2), (key2399, 2), (key2434, 2), (key2375, 2), (key2371, 2), (key2536, 2), (key2465, 2), (key2552, 2), (key2500, 2), (key2387, 2), (key2541, 2), (key2477, 2)]

theorem rawRowCheck10845 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form4 = rawRow10845 := by decide +kernel

def row10845 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

theorem rowCheck10845 : row10845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10845 := by decide +kernel

theorem rowEval10845 (x : Key → ℝ) : Integer.Sparse.eval row10845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10845, Integer.Sparse.eval_collectBalanced, rawRowCheck10845]

def rawRow10846 : Integer.Sparse Key := [(key2465, -6), (key2500, -6), (key2469, -6), (key2477, -6), (key2399, 2), (key2434, 2), (key2403, 2), (key2465, 2), (key2500, 2), (key2371, 2), (key2552, 2), (key2375, 2), (key2536, 2), (key2477, 2), (key2387, 2), (key2541, 2)]

theorem rawRowCheck10846 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form4 = rawRow10846 := by decide +kernel

def row10846 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

theorem rowCheck10846 : row10846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10846 := by decide +kernel

theorem rowEval10846 (x : Key → ℝ) : Integer.Sparse.eval row10846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10846, Integer.Sparse.eval_collectBalanced, rawRowCheck10846]

def rawRow10847 : Integer.Sparse Key := [(key2500, -6), (key2465, -6), (key2469, -6), (key2477, -6), (key2434, 2), (key2399, 2), (key2403, 2), (key2500, 2), (key2465, 2), (key2552, 2), (key2371, 2), (key2536, 2), (key2375, 2), (key2477, 2), (key2541, 2), (key2387, 2)]

theorem rawRowCheck10847 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form4 = rawRow10847 := by decide +kernel

def row10847 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

theorem rowCheck10847 : row10847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10847 := by decide +kernel

theorem rowEval10847 (x : Key → ℝ) : Integer.Sparse.eval row10847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck10847, Integer.Sparse.eval_collectBalanced, rawRowCheck10847]

def rawRow10848 : Integer.Sparse Key := [(key2469, -6), (key2500, -6), (key2465, -6), (key2477, -6), (key2403, 2), (key2434, 2), (key2399, 2), (key2536, 2), (key2552, 2), (key2375, 2), (key2500, 2), (key2371, 2), (key2465, 2), (key2541, 2), (key2387, 2), (key2477, 2)]

theorem rawRowCheck10848 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form4 = rawRow10848 := by decide +kernel

def row10848 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

theorem rowCheck10848 : row10848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10848 := by decide +kernel

theorem rowEval10848 (x : Key → ℝ) : Integer.Sparse.eval row10848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10848, Integer.Sparse.eval_collectBalanced, rawRowCheck10848]

def rawRow10849 : Integer.Sparse Key := [(key2500, -6), (key2469, -6), (key2465, -6), (key2477, -6), (key2434, 2), (key2403, 2), (key2399, 2), (key2552, 2), (key2536, 2), (key2500, 2), (key2375, 2), (key2465, 2), (key2371, 2), (key2541, 2), (key2477, 2), (key2387, 2)]

theorem rawRowCheck10849 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form4 = rawRow10849 := by decide +kernel

def row10849 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

theorem rowCheck10849 : row10849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10849 := by decide +kernel

theorem rowEval10849 (x : Key → ℝ) : Integer.Sparse.eval row10849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck10849, Integer.Sparse.eval_collectBalanced, rawRowCheck10849]

def rawRow10850 : Integer.Sparse Key := [(key2465, -6), (key2477, -6), (key2500, -6), (key2469, -6), (key2465, 2), (key2477, 2), (key2500, 2), (key2371, 2), (key2387, 2), (key2399, 2), (key2541, 2), (key2434, 2), (key2552, 2), (key2375, 2), (key2403, 2), (key2536, 2)]

theorem rawRowCheck10850 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form4 = rawRow10850 := by decide +kernel

def row10850 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

theorem rowCheck10850 : row10850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10850 := by decide +kernel

theorem rowEval10850 (x : Key → ℝ) : Integer.Sparse.eval row10850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10850, Integer.Sparse.eval_collectBalanced, rawRowCheck10850]

def rawRow10851 : Integer.Sparse Key := [(key2477, -6), (key2465, -6), (key2500, -6), (key2469, -6), (key2477, 2), (key2465, 2), (key2500, 2), (key2387, 2), (key2371, 2), (key2541, 2), (key2399, 2), (key2552, 2), (key2434, 2), (key2375, 2), (key2536, 2), (key2403, 2)]

theorem rawRowCheck10851 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form4 = rawRow10851 := by decide +kernel

def row10851 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

theorem rowCheck10851 : row10851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10851 := by decide +kernel

theorem rowEval10851 (x : Key → ℝ) : Integer.Sparse.eval row10851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10851, Integer.Sparse.eval_collectBalanced, rawRowCheck10851]

def rawRow10852 : Integer.Sparse Key := [(key2465, -6), (key2500, -6), (key2477, -6), (key2469, -6), (key2465, 2), (key2500, 2), (key2477, 2), (key2399, 2), (key2434, 2), (key2371, 2), (key2552, 2), (key2387, 2), (key2541, 2), (key2403, 2), (key2375, 2), (key2536, 2)]

theorem rawRowCheck10852 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form4 = rawRow10852 := by decide +kernel

def row10852 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

theorem rowCheck10852 : row10852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10852 := by decide +kernel

theorem rowEval10852 (x : Key → ℝ) : Integer.Sparse.eval row10852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10852, Integer.Sparse.eval_collectBalanced, rawRowCheck10852]

def rawRow10853 : Integer.Sparse Key := [(key2500, -6), (key2465, -6), (key2477, -6), (key2469, -6), (key2500, 2), (key2465, 2), (key2477, 2), (key2434, 2), (key2399, 2), (key2552, 2), (key2371, 2), (key2541, 2), (key2387, 2), (key2403, 2), (key2536, 2), (key2375, 2)]

theorem rawRowCheck10853 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form4 = rawRow10853 := by decide +kernel

def row10853 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

theorem rowCheck10853 : row10853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10853 := by decide +kernel

theorem rowEval10853 (x : Key → ℝ) : Integer.Sparse.eval row10853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck10853, Integer.Sparse.eval_collectBalanced, rawRowCheck10853]

def rawRow10854 : Integer.Sparse Key := [(key2477, -6), (key2500, -6), (key2465, -6), (key2469, -6), (key2477, 2), (key2500, 2), (key2465, 2), (key2541, 2), (key2552, 2), (key2387, 2), (key2434, 2), (key2371, 2), (key2399, 2), (key2536, 2), (key2375, 2), (key2403, 2)]

theorem rawRowCheck10854 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form4 = rawRow10854 := by decide +kernel

def row10854 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

theorem rowCheck10854 : row10854 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10854 := by decide +kernel

theorem rowEval10854 (x : Key → ℝ) : Integer.Sparse.eval row10854 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10854, Integer.Sparse.eval_collectBalanced, rawRowCheck10854]

def rawRow10855 : Integer.Sparse Key := [(key2500, -6), (key2477, -6), (key2465, -6), (key2469, -6), (key2500, 2), (key2477, 2), (key2465, 2), (key2552, 2), (key2541, 2), (key2434, 2), (key2387, 2), (key2399, 2), (key2371, 2), (key2536, 2), (key2403, 2), (key2375, 2)]

theorem rawRowCheck10855 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form4 = rawRow10855 := by decide +kernel

def row10855 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

theorem rowCheck10855 : row10855 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10855 := by decide +kernel

theorem rowEval10855 (x : Key → ℝ) : Integer.Sparse.eval row10855 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck10855, Integer.Sparse.eval_collectBalanced, rawRowCheck10855]

def rawRow10856 : Integer.Sparse Key := [(key2469, -6), (key2477, -6), (key2500, -6), (key2465, -6), (key2536, 2), (key2541, 2), (key2552, 2), (key2375, 2), (key2387, 2), (key2403, 2), (key2477, 2), (key2434, 2), (key2500, 2), (key2371, 2), (key2399, 2), (key2465, 2)]

theorem rawRowCheck10856 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form4 = rawRow10856 := by decide +kernel

def row10856 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

theorem rowCheck10856 : row10856 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10856 := by decide +kernel

theorem rowEval10856 (x : Key → ℝ) : Integer.Sparse.eval row10856 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10856, Integer.Sparse.eval_collectBalanced, rawRowCheck10856]

def rawRow10857 : Integer.Sparse Key := [(key2477, -6), (key2469, -6), (key2500, -6), (key2465, -6), (key2541, 2), (key2536, 2), (key2552, 2), (key2387, 2), (key2375, 2), (key2477, 2), (key2403, 2), (key2500, 2), (key2434, 2), (key2371, 2), (key2465, 2), (key2399, 2)]

theorem rawRowCheck10857 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form4 = rawRow10857 := by decide +kernel

def row10857 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

theorem rowCheck10857 : row10857 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10857 := by decide +kernel

theorem rowEval10857 (x : Key → ℝ) : Integer.Sparse.eval row10857 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10857, Integer.Sparse.eval_collectBalanced, rawRowCheck10857]

def rawRow10858 : Integer.Sparse Key := [(key2469, -6), (key2500, -6), (key2477, -6), (key2465, -6), (key2536, 2), (key2552, 2), (key2541, 2), (key2403, 2), (key2434, 2), (key2375, 2), (key2500, 2), (key2387, 2), (key2477, 2), (key2399, 2), (key2371, 2), (key2465, 2)]

theorem rawRowCheck10858 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form4 = rawRow10858 := by decide +kernel

def row10858 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

theorem rowCheck10858 : row10858 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10858 := by decide +kernel

theorem rowEval10858 (x : Key → ℝ) : Integer.Sparse.eval row10858 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10858, Integer.Sparse.eval_collectBalanced, rawRowCheck10858]

def rawRow10859 : Integer.Sparse Key := [(key2500, -6), (key2469, -6), (key2477, -6), (key2465, -6), (key2552, 2), (key2536, 2), (key2541, 2), (key2434, 2), (key2403, 2), (key2500, 2), (key2375, 2), (key2477, 2), (key2387, 2), (key2399, 2), (key2465, 2), (key2371, 2)]

theorem rawRowCheck10859 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form4 = rawRow10859 := by decide +kernel

def row10859 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

theorem rowCheck10859 : row10859 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10859 := by decide +kernel

theorem rowEval10859 (x : Key → ℝ) : Integer.Sparse.eval row10859 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck10859, Integer.Sparse.eval_collectBalanced, rawRowCheck10859]

def rawRow10860 : Integer.Sparse Key := [(key2477, -6), (key2500, -6), (key2469, -6), (key2465, -6), (key2541, 2), (key2552, 2), (key2536, 2), (key2477, 2), (key2500, 2), (key2387, 2), (key2434, 2), (key2375, 2), (key2403, 2), (key2465, 2), (key2371, 2), (key2399, 2)]

theorem rawRowCheck10860 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form4 = rawRow10860 := by decide +kernel

def row10860 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

theorem rowCheck10860 : row10860 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10860 := by decide +kernel

theorem rowEval10860 (x : Key → ℝ) : Integer.Sparse.eval row10860 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10860, Integer.Sparse.eval_collectBalanced, rawRowCheck10860]

def rawRow10861 : Integer.Sparse Key := [(key2500, -6), (key2477, -6), (key2469, -6), (key2465, -6), (key2552, 2), (key2541, 2), (key2536, 2), (key2500, 2), (key2477, 2), (key2434, 2), (key2387, 2), (key2403, 2), (key2375, 2), (key2465, 2), (key2399, 2), (key2371, 2)]

theorem rawRowCheck10861 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form4 = rawRow10861 := by decide +kernel

def row10861 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

theorem rowCheck10861 : row10861 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10861 := by decide +kernel

theorem rowEval10861 (x : Key → ℝ) : Integer.Sparse.eval row10861 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck10861, Integer.Sparse.eval_collectBalanced, rawRowCheck10861]

def rawRow10862 : Integer.Sparse Key := [(key2536, -6), (key2536, -6), (key2541, -6), (key2552, -6), (key2375, 2), (key2375, 2), (key2387, 2), (key2403, 2), (key2403, 2), (key2469, 2), (key2469, 2), (key2477, 2), (key2477, 2), (key2434, 2), (key2500, 2), (key2500, 2)]

theorem rawRowCheck10862 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form4 = rawRow10862 := by decide +kernel

def row10862 : Integer.Sparse Key := [(key2375, 4), (key2387, 2), (key2403, 4), (key2434, 2), (key2469, 4), (key2477, 4), (key2500, 4), (key2536, -12), (key2541, -6), (key2552, -6)]

theorem rowCheck10862 : row10862 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10862 := by decide +kernel

theorem rowEval10862 (x : Key → ℝ) : Integer.Sparse.eval row10862 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10862, Integer.Sparse.eval_collectBalanced, rawRowCheck10862]

def rawRow10863 : Integer.Sparse Key := [(key2536, -6), (key2541, -6), (key2536, -6), (key2552, -6), (key2375, 2), (key2387, 2), (key2375, 2), (key2469, 2), (key2477, 2), (key2403, 2), (key2477, 2), (key2403, 2), (key2469, 2), (key2500, 2), (key2434, 2), (key2500, 2)]

theorem rawRowCheck10863 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form4 = rawRow10863 := by decide +kernel

def row10863 : Integer.Sparse Key := [(key2375, 4), (key2387, 2), (key2403, 4), (key2434, 2), (key2469, 4), (key2477, 4), (key2500, 4), (key2536, -12), (key2541, -6), (key2552, -6)]

theorem rowCheck10863 : row10863 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10863 := by decide +kernel

theorem rowEval10863 (x : Key → ℝ) : Integer.Sparse.eval row10863 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10863, Integer.Sparse.eval_collectBalanced, rawRowCheck10863]

def rawRow10864 : Integer.Sparse Key := [(key2541, -6), (key2536, -6), (key2536, -6), (key2552, -6), (key2387, 2), (key2375, 2), (key2375, 2), (key2477, 2), (key2469, 2), (key2477, 2), (key2403, 2), (key2469, 2), (key2403, 2), (key2500, 2), (key2500, 2), (key2434, 2)]

theorem rawRowCheck10864 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form4 = rawRow10864 := by decide +kernel

def row10864 : Integer.Sparse Key := [(key2375, 4), (key2387, 2), (key2403, 4), (key2434, 2), (key2469, 4), (key2477, 4), (key2500, 4), (key2536, -12), (key2541, -6), (key2552, -6)]

theorem rowCheck10864 : row10864 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10864 := by decide +kernel

theorem rowEval10864 (x : Key → ℝ) : Integer.Sparse.eval row10864 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10864, Integer.Sparse.eval_collectBalanced, rawRowCheck10864]

def rawRow10865 : Integer.Sparse Key := [(key2536, -6), (key2536, -6), (key2552, -6), (key2541, -6), (key2403, 2), (key2403, 2), (key2434, 2), (key2375, 2), (key2375, 2), (key2469, 2), (key2469, 2), (key2500, 2), (key2500, 2), (key2387, 2), (key2477, 2), (key2477, 2)]

theorem rawRowCheck10865 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form4 = rawRow10865 := by decide +kernel

def row10865 : Integer.Sparse Key := [(key2375, 4), (key2387, 2), (key2403, 4), (key2434, 2), (key2469, 4), (key2477, 4), (key2500, 4), (key2536, -12), (key2541, -6), (key2552, -6)]

theorem rowCheck10865 : row10865 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10865 := by decide +kernel

theorem rowEval10865 (x : Key → ℝ) : Integer.Sparse.eval row10865 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10865, Integer.Sparse.eval_collectBalanced, rawRowCheck10865]

def rawRow10866 : Integer.Sparse Key := [(key2536, -6), (key2552, -6), (key2536, -6), (key2541, -6), (key2403, 2), (key2434, 2), (key2403, 2), (key2469, 2), (key2500, 2), (key2375, 2), (key2500, 2), (key2375, 2), (key2469, 2), (key2477, 2), (key2387, 2), (key2477, 2)]

theorem rawRowCheck10866 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form4 = rawRow10866 := by decide +kernel

def row10866 : Integer.Sparse Key := [(key2375, 4), (key2387, 2), (key2403, 4), (key2434, 2), (key2469, 4), (key2477, 4), (key2500, 4), (key2536, -12), (key2541, -6), (key2552, -6)]

theorem rowCheck10866 : row10866 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10866 := by decide +kernel

theorem rowEval10866 (x : Key → ℝ) : Integer.Sparse.eval row10866 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10866, Integer.Sparse.eval_collectBalanced, rawRowCheck10866]

def rawRow10867 : Integer.Sparse Key := [(key2552, -6), (key2536, -6), (key2536, -6), (key2541, -6), (key2434, 2), (key2403, 2), (key2403, 2), (key2500, 2), (key2469, 2), (key2500, 2), (key2375, 2), (key2469, 2), (key2375, 2), (key2477, 2), (key2477, 2), (key2387, 2)]

theorem rawRowCheck10867 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form4 = rawRow10867 := by decide +kernel

def row10867 : Integer.Sparse Key := [(key2375, 4), (key2387, 2), (key2403, 4), (key2434, 2), (key2469, 4), (key2477, 4), (key2500, 4), (key2536, -12), (key2541, -6), (key2552, -6)]

theorem rowCheck10867 : row10867 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10867 := by decide +kernel

theorem rowEval10867 (x : Key → ℝ) : Integer.Sparse.eval row10867 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck10867, Integer.Sparse.eval_collectBalanced, rawRowCheck10867]

def rawRow10868 : Integer.Sparse Key := [(key2536, -6), (key2541, -6), (key2552, -6), (key2536, -6), (key2469, 2), (key2477, 2), (key2500, 2), (key2375, 2), (key2387, 2), (key2403, 2), (key2477, 2), (key2434, 2), (key2500, 2), (key2375, 2), (key2403, 2), (key2469, 2)]

theorem rawRowCheck10868 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form4 = rawRow10868 := by decide +kernel

def row10868 : Integer.Sparse Key := [(key2375, 4), (key2387, 2), (key2403, 4), (key2434, 2), (key2469, 4), (key2477, 4), (key2500, 4), (key2536, -12), (key2541, -6), (key2552, -6)]

theorem rowCheck10868 : row10868 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10868 := by decide +kernel

theorem rowEval10868 (x : Key → ℝ) : Integer.Sparse.eval row10868 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10868, Integer.Sparse.eval_collectBalanced, rawRowCheck10868]

def rawRow10869 : Integer.Sparse Key := [(key2541, -6), (key2536, -6), (key2552, -6), (key2536, -6), (key2477, 2), (key2469, 2), (key2500, 2), (key2387, 2), (key2375, 2), (key2477, 2), (key2403, 2), (key2500, 2), (key2434, 2), (key2375, 2), (key2469, 2), (key2403, 2)]

theorem rawRowCheck10869 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form4 = rawRow10869 := by decide +kernel

def row10869 : Integer.Sparse Key := [(key2375, 4), (key2387, 2), (key2403, 4), (key2434, 2), (key2469, 4), (key2477, 4), (key2500, 4), (key2536, -12), (key2541, -6), (key2552, -6)]

theorem rowCheck10869 : row10869 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10869 := by decide +kernel

theorem rowEval10869 (x : Key → ℝ) : Integer.Sparse.eval row10869 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10869, Integer.Sparse.eval_collectBalanced, rawRowCheck10869]

def rawRow10870 : Integer.Sparse Key := [(key2536, -6), (key2552, -6), (key2541, -6), (key2536, -6), (key2469, 2), (key2500, 2), (key2477, 2), (key2403, 2), (key2434, 2), (key2375, 2), (key2500, 2), (key2387, 2), (key2477, 2), (key2403, 2), (key2375, 2), (key2469, 2)]

theorem rawRowCheck10870 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form4 = rawRow10870 := by decide +kernel

def row10870 : Integer.Sparse Key := [(key2375, 4), (key2387, 2), (key2403, 4), (key2434, 2), (key2469, 4), (key2477, 4), (key2500, 4), (key2536, -12), (key2541, -6), (key2552, -6)]

theorem rowCheck10870 : row10870 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10870 := by decide +kernel

theorem rowEval10870 (x : Key → ℝ) : Integer.Sparse.eval row10870 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10870, Integer.Sparse.eval_collectBalanced, rawRowCheck10870]

def rawRow10871 : Integer.Sparse Key := [(key2552, -6), (key2536, -6), (key2541, -6), (key2536, -6), (key2500, 2), (key2469, 2), (key2477, 2), (key2434, 2), (key2403, 2), (key2500, 2), (key2375, 2), (key2477, 2), (key2387, 2), (key2403, 2), (key2469, 2), (key2375, 2)]

theorem rawRowCheck10871 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form4 = rawRow10871 := by decide +kernel

def row10871 : Integer.Sparse Key := [(key2375, 4), (key2387, 2), (key2403, 4), (key2434, 2), (key2469, 4), (key2477, 4), (key2500, 4), (key2536, -12), (key2541, -6), (key2552, -6)]

theorem rowCheck10871 : row10871 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10871 := by decide +kernel

theorem rowEval10871 (x : Key → ℝ) : Integer.Sparse.eval row10871 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck10871, Integer.Sparse.eval_collectBalanced, rawRowCheck10871]

def rawRow10872 : Integer.Sparse Key := [(key2541, -6), (key2552, -6), (key2536, -6), (key2536, -6), (key2477, 2), (key2500, 2), (key2469, 2), (key2477, 2), (key2500, 2), (key2387, 2), (key2434, 2), (key2375, 2), (key2403, 2), (key2469, 2), (key2375, 2), (key2403, 2)]

theorem rawRowCheck10872 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form4 = rawRow10872 := by decide +kernel

def row10872 : Integer.Sparse Key := [(key2375, 4), (key2387, 2), (key2403, 4), (key2434, 2), (key2469, 4), (key2477, 4), (key2500, 4), (key2536, -12), (key2541, -6), (key2552, -6)]

theorem rowCheck10872 : row10872 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10872 := by decide +kernel

theorem rowEval10872 (x : Key → ℝ) : Integer.Sparse.eval row10872 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10872, Integer.Sparse.eval_collectBalanced, rawRowCheck10872]

def rawRow10873 : Integer.Sparse Key := [(key2552, -6), (key2541, -6), (key2536, -6), (key2536, -6), (key2500, 2), (key2477, 2), (key2469, 2), (key2500, 2), (key2477, 2), (key2434, 2), (key2387, 2), (key2403, 2), (key2375, 2), (key2469, 2), (key2403, 2), (key2375, 2)]

theorem rawRowCheck10873 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form4 = rawRow10873 := by decide +kernel

def row10873 : Integer.Sparse Key := [(key2375, 4), (key2387, 2), (key2403, 4), (key2434, 2), (key2469, 4), (key2477, 4), (key2500, 4), (key2536, -12), (key2541, -6), (key2552, -6)]

theorem rowCheck10873 : row10873 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10873 := by decide +kernel

theorem rowEval10873 (x : Key → ℝ) : Integer.Sparse.eval row10873 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck10873, Integer.Sparse.eval_collectBalanced, rawRowCheck10873]

def rawRow10874 : Integer.Sparse Key := [(key2625, -2), (key2629, -2), (key2637, -2), (key2699, -2), (key2703, -2), (key2852, -2), (key2973, -2), (key2857, -2), (key2975, -2), (key2723, -2), (key2867, -2), (key2982, -2), (key2609, 1), (key2613, 1), (key2625, 1), (key2647, 1), (key2637, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2779, 1), (key2937, 1), (key2791, 1), (key2942, 1), (key2699, 1), (key2736, 1), (key2802, 1), (key2949, 1), (key2896, 1), (key2975, 1), (key2723, 1), (key2746, 1), (key2826, 1), (key2959, 1), (key2903, 1), (key2982, 1)]

theorem rawRowCheck10874 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form5 = rawRow10874 := by decide +kernel

def row10874 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

theorem rowCheck10874 : row10874 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10874 := by decide +kernel

theorem rowEval10874 (x : Key → ℝ) : Integer.Sparse.eval row10874 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck10874, Integer.Sparse.eval_collectBalanced, rawRowCheck10874]

def rawRow10875 : Integer.Sparse Key := [(key2629, -2), (key2625, -2), (key2637, -2), (key2703, -2), (key2699, -2), (key2973, -2), (key2852, -2), (key2975, -2), (key2857, -2), (key2723, -2), (key2982, -2), (key2867, -2), (key2613, 1), (key2609, 1), (key2647, 1), (key2625, 1), (key2652, 1), (key2637, 1), (key2668, 1), (key2664, 1), (key2937, 1), (key2779, 1), (key2942, 1), (key2791, 1), (key2736, 1), (key2699, 1), (key2949, 1), (key2802, 1), (key2975, 1), (key2896, 1), (key2746, 1), (key2723, 1), (key2959, 1), (key2826, 1), (key2982, 1), (key2903, 1)]

theorem rawRowCheck10875 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form5 = rawRow10875 := by decide +kernel

def row10875 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

theorem rowCheck10875 : row10875 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10875 := by decide +kernel

theorem rowEval10875 (x : Key → ℝ) : Integer.Sparse.eval row10875 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck10875, Integer.Sparse.eval_collectBalanced, rawRowCheck10875]

def rawRow10876 : Integer.Sparse Key := [(key2625, -2), (key2637, -2), (key2629, -2), (key2852, -2), (key2857, -2), (key2699, -2), (key2975, -2), (key2703, -2), (key2973, -2), (key2867, -2), (key2723, -2), (key2982, -2), (key2625, 1), (key2637, 1), (key2609, 1), (key2652, 1), (key2613, 1), (key2647, 1), (key2779, 1), (key2791, 1), (key2664, 1), (key2942, 1), (key2668, 1), (key2937, 1), (key2802, 1), (key2896, 1), (key2699, 1), (key2975, 1), (key2736, 1), (key2949, 1), (key2826, 1), (key2903, 1), (key2723, 1), (key2982, 1), (key2746, 1), (key2959, 1)]

theorem rawRowCheck10876 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form5 = rawRow10876 := by decide +kernel

def row10876 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

theorem rowCheck10876 : row10876 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10876 := by decide +kernel

theorem rowEval10876 (x : Key → ℝ) : Integer.Sparse.eval row10876 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck10876, Integer.Sparse.eval_collectBalanced, rawRowCheck10876]

def rawRow10877 : Integer.Sparse Key := [(key2637, -2), (key2625, -2), (key2629, -2), (key2857, -2), (key2852, -2), (key2975, -2), (key2699, -2), (key2973, -2), (key2703, -2), (key2867, -2), (key2982, -2), (key2723, -2), (key2637, 1), (key2625, 1), (key2652, 1), (key2609, 1), (key2647, 1), (key2613, 1), (key2791, 1), (key2779, 1), (key2942, 1), (key2664, 1), (key2937, 1), (key2668, 1), (key2896, 1), (key2802, 1), (key2975, 1), (key2699, 1), (key2949, 1), (key2736, 1), (key2903, 1), (key2826, 1), (key2982, 1), (key2723, 1), (key2959, 1), (key2746, 1)]

theorem rawRowCheck10877 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form5 = rawRow10877 := by decide +kernel

def row10877 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

theorem rowCheck10877 : row10877 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10877 := by decide +kernel

theorem rowEval10877 (x : Key → ℝ) : Integer.Sparse.eval row10877 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck10877, Integer.Sparse.eval_collectBalanced, rawRowCheck10877]

def rawRow10878 : Integer.Sparse Key := [(key2629, -2), (key2637, -2), (key2625, -2), (key2973, -2), (key2975, -2), (key2703, -2), (key2857, -2), (key2699, -2), (key2852, -2), (key2982, -2), (key2723, -2), (key2867, -2), (key2647, 1), (key2652, 1), (key2613, 1), (key2637, 1), (key2609, 1), (key2625, 1), (key2937, 1), (key2942, 1), (key2668, 1), (key2791, 1), (key2664, 1), (key2779, 1), (key2949, 1), (key2975, 1), (key2736, 1), (key2896, 1), (key2699, 1), (key2802, 1), (key2959, 1), (key2982, 1), (key2746, 1), (key2903, 1), (key2723, 1), (key2826, 1)]

theorem rawRowCheck10878 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form5 = rawRow10878 := by decide +kernel

def row10878 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

theorem rowCheck10878 : row10878 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10878 := by decide +kernel

theorem rowEval10878 (x : Key → ℝ) : Integer.Sparse.eval row10878 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck10878, Integer.Sparse.eval_collectBalanced, rawRowCheck10878]

def rawRow10879 : Integer.Sparse Key := [(key2637, -2), (key2629, -2), (key2625, -2), (key2975, -2), (key2973, -2), (key2857, -2), (key2703, -2), (key2852, -2), (key2699, -2), (key2982, -2), (key2867, -2), (key2723, -2), (key2652, 1), (key2647, 1), (key2637, 1), (key2613, 1), (key2625, 1), (key2609, 1), (key2942, 1), (key2937, 1), (key2791, 1), (key2668, 1), (key2779, 1), (key2664, 1), (key2975, 1), (key2949, 1), (key2896, 1), (key2736, 1), (key2802, 1), (key2699, 1), (key2982, 1), (key2959, 1), (key2903, 1), (key2746, 1), (key2826, 1), (key2723, 1)]

theorem rawRowCheck10879 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form5 = rawRow10879 := by decide +kernel

def row10879 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

theorem rowCheck10879 : row10879 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10879 := by decide +kernel

theorem rowEval10879 (x : Key → ℝ) : Integer.Sparse.eval row10879 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck10879, Integer.Sparse.eval_collectBalanced, rawRowCheck10879]

end MUB6.Certificate.GramRows

end OAI
