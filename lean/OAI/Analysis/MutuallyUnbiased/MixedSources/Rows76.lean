import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources44

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1216 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1216 (mixedVector B) = 0 := by
  have h776 : mixedVector B (Sum.inr 776) = Sparse.eval nodeValue776 (mixedVector B) := by
    change mixedMoment B node776 node776Labels = _
    exact sound776 B hB hF
  have h778 : mixedVector B (Sum.inr 778) = Sparse.eval nodeValue778 (mixedVector B) := by
    change mixedMoment B node778 node778Labels = _
    exact sound778 B hB hF
  have h783 : mixedVector B (Sum.inr 783) = Sparse.eval nodeValue783 (mixedVector B) := by
    change mixedMoment B node783 node783Labels = _
    exact sound783 B hB hF
  have h1698 : mixedVector B (Sum.inr 1698) = Sparse.eval nodeValue1698 (mixedVector B) := by
    change mixedMoment B node1698 node1698Labels = _
    exact sound1698 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1415, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h776, h778, h783, h1698, h4068, reducedSource1216] using sourceEq1415 B hB

theorem rowSound1216 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1216 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1216, numericCheck1216, reducedZero1216 B hB hF, mul_zero]

theorem reducedZero1217 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1217 (mixedVector B) = 0 := by
  have h787 : mixedVector B (Sum.inr 787) = Sparse.eval nodeValue787 (mixedVector B) := by
    change mixedMoment B node787 node787Labels = _
    exact sound787 B hB hF
  have h1593 : mixedVector B (Sum.inr 1593) = Sparse.eval nodeValue1593 (mixedVector B) := by
    change mixedMoment B node1593 node1593Labels = _
    exact sound1593 B hB hF
  have h1639 : mixedVector B (Sum.inr 1639) = Sparse.eval nodeValue1639 (mixedVector B) := by
    change mixedMoment B node1639 node1639Labels = _
    exact sound1639 B hB hF
  have h1700 : mixedVector B (Sum.inr 1700) = Sparse.eval nodeValue1700 (mixedVector B) := by
    change mixedMoment B node1700 node1700Labels = _
    exact sound1700 B hB hF
  have h1708 : mixedVector B (Sum.inr 1708) = Sparse.eval nodeValue1708 (mixedVector B) := by
    change mixedMoment B node1708 node1708Labels = _
    exact sound1708 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1417, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h787, h1593, h1639, h1700, h1708, h4068, reducedSource1217] using sourceEq1417 B hB

theorem rowSound1217 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1217 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1217, numericCheck1217, reducedZero1217 B hB hF, mul_zero]

theorem reducedZero1218 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1218 (mixedVector B) = 0 := by
  have h542 : mixedVector B (Sum.inr 542) = Sparse.eval nodeValue542 (mixedVector B) := by
    change mixedMoment B node542 node542Labels = _
    exact sound542 B hB hF
  have h702 : mixedVector B (Sum.inr 702) = Sparse.eval nodeValue702 (mixedVector B) := by
    change mixedMoment B node702 node702Labels = _
    exact sound702 B hB hF
  have h737 : mixedVector B (Sum.inr 737) = Sparse.eval nodeValue737 (mixedVector B) := by
    change mixedMoment B node737 node737Labels = _
    exact sound737 B hB hF
  have h787 : mixedVector B (Sum.inr 787) = Sparse.eval nodeValue787 (mixedVector B) := by
    change mixedMoment B node787 node787Labels = _
    exact sound787 B hB hF
  have h810 : mixedVector B (Sum.inr 810) = Sparse.eval nodeValue810 (mixedVector B) := by
    change mixedMoment B node810 node810Labels = _
    exact sound810 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1418, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h542, h702, h737, h787, h810, h4068, reducedSource1218] using sourceEq1418 B hB

theorem rowSound1218 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1218 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1218, numericCheck1218, reducedZero1218 B hB hF, mul_zero]

theorem reducedZero1219 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1219 (mixedVector B) = 0 := by
  have h783 : mixedVector B (Sum.inr 783) = Sparse.eval nodeValue783 (mixedVector B) := by
    change mixedMoment B node783 node783Labels = _
    exact sound783 B hB hF
  have h787 : mixedVector B (Sum.inr 787) = Sparse.eval nodeValue787 (mixedVector B) := by
    change mixedMoment B node787 node787Labels = _
    exact sound787 B hB hF
  have h790 : mixedVector B (Sum.inr 790) = Sparse.eval nodeValue790 (mixedVector B) := by
    change mixedMoment B node790 node790Labels = _
    exact sound790 B hB hF
  have h810 : mixedVector B (Sum.inr 810) = Sparse.eval nodeValue810 (mixedVector B) := by
    change mixedMoment B node810 node810Labels = _
    exact sound810 B hB hF
  have h1708 : mixedVector B (Sum.inr 1708) = Sparse.eval nodeValue1708 (mixedVector B) := by
    change mixedMoment B node1708 node1708Labels = _
    exact sound1708 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1419, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h783, h787, h790, h810, h1708, h4068, reducedSource1219] using sourceEq1419 B hB

theorem rowSound1219 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1219 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1219, numericCheck1219, reducedZero1219 B hB hF, mul_zero]

theorem reducedZero1220 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1220 (mixedVector B) = 0 := by
  have h785 : mixedVector B (Sum.inr 785) = Sparse.eval nodeValue785 (mixedVector B) := by
    change mixedMoment B node785 node785Labels = _
    exact sound785 B hB hF
  have h1592 : mixedVector B (Sum.inr 1592) = Sparse.eval nodeValue1592 (mixedVector B) := by
    change mixedMoment B node1592 node1592Labels = _
    exact sound1592 B hB hF
  have h1637 : mixedVector B (Sum.inr 1637) = Sparse.eval nodeValue1637 (mixedVector B) := by
    change mixedMoment B node1637 node1637Labels = _
    exact sound1637 B hB hF
  have h1707 : mixedVector B (Sum.inr 1707) = Sparse.eval nodeValue1707 (mixedVector B) := by
    change mixedMoment B node1707 node1707Labels = _
    exact sound1707 B hB hF
  have h1710 : mixedVector B (Sum.inr 1710) = Sparse.eval nodeValue1710 (mixedVector B) := by
    change mixedMoment B node1710 node1710Labels = _
    exact sound1710 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1421, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h785, h1592, h1637, h1707, h1710, h4069, reducedSource1220] using sourceEq1421 B hB

theorem rowSound1220 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1220 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1220, numericCheck1220, reducedZero1220 B hB hF, mul_zero]

theorem reducedZero1221 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1221 (mixedVector B) = 0 := by
  have h538 : mixedVector B (Sum.inr 538) = Sparse.eval nodeValue538 (mixedVector B) := by
    change mixedMoment B node538 node538Labels = _
    exact sound538 B hB hF
  have h699 : mixedVector B (Sum.inr 699) = Sparse.eval nodeValue699 (mixedVector B) := by
    change mixedMoment B node699 node699Labels = _
    exact sound699 B hB hF
  have h733 : mixedVector B (Sum.inr 733) = Sparse.eval nodeValue733 (mixedVector B) := by
    change mixedMoment B node733 node733Labels = _
    exact sound733 B hB hF
  have h785 : mixedVector B (Sum.inr 785) = Sparse.eval nodeValue785 (mixedVector B) := by
    change mixedMoment B node785 node785Labels = _
    exact sound785 B hB hF
  have h806 : mixedVector B (Sum.inr 806) = Sparse.eval nodeValue806 (mixedVector B) := by
    change mixedMoment B node806 node806Labels = _
    exact sound806 B hB hF
  have h812 : mixedVector B (Sum.inr 812) = Sparse.eval nodeValue812 (mixedVector B) := by
    change mixedMoment B node812 node812Labels = _
    exact sound812 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1422, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h538, h699, h733, h785, h806, h812, h4069, reducedSource1221] using sourceEq1422 B hB

theorem rowSound1221 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1221 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1221, numericCheck1221, reducedZero1221 B hB hF, mul_zero]

theorem reducedZero1222 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1222 (mixedVector B) = 0 := by
  have h782 : mixedVector B (Sum.inr 782) = Sparse.eval nodeValue782 (mixedVector B) := by
    change mixedMoment B node782 node782Labels = _
    exact sound782 B hB hF
  have h785 : mixedVector B (Sum.inr 785) = Sparse.eval nodeValue785 (mixedVector B) := by
    change mixedMoment B node785 node785Labels = _
    exact sound785 B hB hF
  have h789 : mixedVector B (Sum.inr 789) = Sparse.eval nodeValue789 (mixedVector B) := by
    change mixedMoment B node789 node789Labels = _
    exact sound789 B hB hF
  have h806 : mixedVector B (Sum.inr 806) = Sparse.eval nodeValue806 (mixedVector B) := by
    change mixedMoment B node806 node806Labels = _
    exact sound806 B hB hF
  have h1707 : mixedVector B (Sum.inr 1707) = Sparse.eval nodeValue1707 (mixedVector B) := by
    change mixedMoment B node1707 node1707Labels = _
    exact sound1707 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1423, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h782, h785, h789, h806, h1707, h4069, reducedSource1222] using sourceEq1423 B hB

theorem rowSound1222 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1222 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1222, numericCheck1222, reducedZero1222 B hB hF, mul_zero]

theorem reducedZero1223 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1223 (mixedVector B) = 0 := by
  have h536 : mixedVector B (Sum.inr 536) = Sparse.eval nodeValue536 (mixedVector B) := by
    change mixedMoment B node536 node536Labels = _
    exact sound536 B hB hF
  have h698 : mixedVector B (Sum.inr 698) = Sparse.eval nodeValue698 (mixedVector B) := by
    change mixedMoment B node698 node698Labels = _
    exact sound698 B hB hF
  have h731 : mixedVector B (Sum.inr 731) = Sparse.eval nodeValue731 (mixedVector B) := by
    change mixedMoment B node731 node731Labels = _
    exact sound731 B hB hF
  have h804 : mixedVector B (Sum.inr 804) = Sparse.eval nodeValue804 (mixedVector B) := by
    change mixedMoment B node804 node804Labels = _
    exact sound804 B hB hF
  have h809 : mixedVector B (Sum.inr 809) = Sparse.eval nodeValue809 (mixedVector B) := by
    change mixedMoment B node809 node809Labels = _
    exact sound809 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1424, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h536, h698, h731, h804, h809, h4070, reducedSource1223] using sourceEq1424 B hB

theorem rowSound1223 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1223 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1223, numericCheck1223, reducedZero1223 B hB hF, mul_zero]

theorem reducedZero1224 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1224 (mixedVector B) = 0 := by
  have h813 : mixedVector B (Sum.inr 813) = Sparse.eval nodeValue813 (mixedVector B) := by
    change mixedMoment B node813 node813Labels = _
    exact sound813 B hB hF
  have h1603 : mixedVector B (Sum.inr 1603) = Sparse.eval nodeValue1603 (mixedVector B) := by
    change mixedMoment B node1603 node1603Labels = _
    exact sound1603 B hB hF
  have h1651 : mixedVector B (Sum.inr 1651) = Sparse.eval nodeValue1651 (mixedVector B) := by
    change mixedMoment B node1651 node1651Labels = _
    exact sound1651 B hB hF
  have h1716 : mixedVector B (Sum.inr 1716) = Sparse.eval nodeValue1716 (mixedVector B) := by
    change mixedMoment B node1716 node1716Labels = _
    exact sound1716 B hB hF
  have h1728 : mixedVector B (Sum.inr 1728) = Sparse.eval nodeValue1728 (mixedVector B) := by
    change mixedMoment B node1728 node1728Labels = _
    exact sound1728 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1425, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h813, h1603, h1651, h1716, h1728, h4069, reducedSource1224] using sourceEq1425 B hB

theorem rowSound1224 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1224 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1224, numericCheck1224, reducedZero1224 B hB hF, mul_zero]

theorem reducedZero1225 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1225 (mixedVector B) = 0 := by
  have h548 : mixedVector B (Sum.inr 548) = Sparse.eval nodeValue548 (mixedVector B) := by
    change mixedMoment B node548 node548Labels = _
    exact sound548 B hB hF
  have h708 : mixedVector B (Sum.inr 708) = Sparse.eval nodeValue708 (mixedVector B) := by
    change mixedMoment B node708 node708Labels = _
    exact sound708 B hB hF
  have h743 : mixedVector B (Sum.inr 743) = Sparse.eval nodeValue743 (mixedVector B) := by
    change mixedMoment B node743 node743Labels = _
    exact sound743 B hB hF
  have h813 : mixedVector B (Sum.inr 813) = Sparse.eval nodeValue813 (mixedVector B) := by
    change mixedMoment B node813 node813Labels = _
    exact sound813 B hB hF
  have h816 : mixedVector B (Sum.inr 816) = Sparse.eval nodeValue816 (mixedVector B) := by
    change mixedMoment B node816 node816Labels = _
    exact sound816 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1426, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h548, h708, h743, h813, h816, h4069, reducedSource1225] using sourceEq1426 B hB

theorem rowSound1225 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1225 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1225, numericCheck1225, reducedZero1225 B hB hF, mul_zero]

theorem reducedZero1226 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1226 (mixedVector B) = 0 := by
  have h807 : mixedVector B (Sum.inr 807) = Sparse.eval nodeValue807 (mixedVector B) := by
    change mixedMoment B node807 node807Labels = _
    exact sound807 B hB hF
  have h813 : mixedVector B (Sum.inr 813) = Sparse.eval nodeValue813 (mixedVector B) := by
    change mixedMoment B node813 node813Labels = _
    exact sound813 B hB hF
  have h816 : mixedVector B (Sum.inr 816) = Sparse.eval nodeValue816 (mixedVector B) := by
    change mixedMoment B node816 node816Labels = _
    exact sound816 B hB hF
  have h856 : mixedVector B (Sum.inr 856) = Sparse.eval nodeValue856 (mixedVector B) := by
    change mixedMoment B node856 node856Labels = _
    exact sound856 B hB hF
  have h1728 : mixedVector B (Sum.inr 1728) = Sparse.eval nodeValue1728 (mixedVector B) := by
    change mixedMoment B node1728 node1728Labels = _
    exact sound1728 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1427, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h807, h813, h816, h856, h1728, h4069, reducedSource1226] using sourceEq1427 B hB

theorem rowSound1226 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1226 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1226, numericCheck1226, reducedZero1226 B hB hF, mul_zero]

theorem reducedZero1227 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1227 (mixedVector B) = 0 := by
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  have h4101 : mixedVector B (Sum.inr 4101) = Sparse.eval nodeValue4101 (mixedVector B) := by
    change mixedMoment B node4101 node4101Labels = _
    exact sound4101 B hB hF
  have h4108 : mixedVector B (Sum.inr 4108) = Sparse.eval nodeValue4108 (mixedVector B) := by
    change mixedMoment B node4108 node4108Labels = _
    exact sound4108 B hB hF
  have h4110 : mixedVector B (Sum.inr 4110) = Sparse.eval nodeValue4110 (mixedVector B) := by
    change mixedMoment B node4110 node4110Labels = _
    exact sound4110 B hB hF
  have h4127 : mixedVector B (Sum.inr 4127) = Sparse.eval nodeValue4127 (mixedVector B) := by
    change mixedMoment B node4127 node4127Labels = _
    exact sound4127 B hB hF
  have h4196 : mixedVector B (Sum.inr 4196) = Sparse.eval nodeValue4196 (mixedVector B) := by
    change mixedMoment B node4196 node4196Labels = _
    exact sound4196 B hB hF
  have h4202 : mixedVector B (Sum.inr 4202) = Sparse.eval nodeValue4202 (mixedVector B) := by
    change mixedMoment B node4202 node4202Labels = _
    exact sound4202 B hB hF
  have h4204 : mixedVector B (Sum.inr 4204) = Sparse.eval nodeValue4204 (mixedVector B) := by
    change mixedMoment B node4204 node4204Labels = _
    exact sound4204 B hB hF
  have h4218 : mixedVector B (Sum.inr 4218) = Sparse.eval nodeValue4218 (mixedVector B) := by
    change mixedMoment B node4218 node4218Labels = _
    exact sound4218 B hB hF
  have h4233 : mixedVector B (Sum.inr 4233) = Sparse.eval nodeValue4233 (mixedVector B) := by
    change mixedMoment B node4233 node4233Labels = _
    exact sound4233 B hB hF
  have h4240 : mixedVector B (Sum.inr 4240) = Sparse.eval nodeValue4240 (mixedVector B) := by
    change mixedMoment B node4240 node4240Labels = _
    exact sound4240 B hB hF
  have h4242 : mixedVector B (Sum.inr 4242) = Sparse.eval nodeValue4242 (mixedVector B) := by
    change mixedMoment B node4242 node4242Labels = _
    exact sound4242 B hB hF
  have h4251 : mixedVector B (Sum.inr 4251) = Sparse.eval nodeValue4251 (mixedVector B) := by
    change mixedMoment B node4251 node4251Labels = _
    exact sound4251 B hB hF
  have h4257 : mixedVector B (Sum.inr 4257) = Sparse.eval nodeValue4257 (mixedVector B) := by
    change mixedMoment B node4257 node4257Labels = _
    exact sound4257 B hB hF
  have h4264 : mixedVector B (Sum.inr 4264) = Sparse.eval nodeValue4264 (mixedVector B) := by
    change mixedMoment B node4264 node4264Labels = _
    exact sound4264 B hB hF
  have h4269 : mixedVector B (Sum.inr 4269) = Sparse.eval nodeValue4269 (mixedVector B) := by
    change mixedMoment B node4269 node4269Labels = _
    exact sound4269 B hB hF
  have h4273 : mixedVector B (Sum.inr 4273) = Sparse.eval nodeValue4273 (mixedVector B) := by
    change mixedMoment B node4273 node4273Labels = _
    exact sound4273 B hB hF
  have h4418 : mixedVector B (Sum.inr 4418) = Sparse.eval nodeValue4418 (mixedVector B) := by
    change mixedMoment B node4418 node4418Labels = _
    exact sound4418 B hB hF
  have h4490 : mixedVector B (Sum.inr 4490) = Sparse.eval nodeValue4490 (mixedVector B) := by
    change mixedMoment B node4490 node4490Labels = _
    exact sound4490 B hB hF
  have h4496 : mixedVector B (Sum.inr 4496) = Sparse.eval nodeValue4496 (mixedVector B) := by
    change mixedMoment B node4496 node4496Labels = _
    exact sound4496 B hB hF
  have h4498 : mixedVector B (Sum.inr 4498) = Sparse.eval nodeValue4498 (mixedVector B) := by
    change mixedMoment B node4498 node4498Labels = _
    exact sound4498 B hB hF
  simpa only [sourceForm1429, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4069, h4101, h4108, h4110, h4127, h4196, h4202, h4204, h4218, h4233, h4240, h4242, h4251, h4257, h4264, h4269, h4273, h4418, h4490, h4496, h4498, reducedSource1227] using sourceEq1429 B hB

theorem rowSound1227 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1227 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1227, numericCheck1227, reducedZero1227 B hB hF, mul_zero]

theorem reducedZero1228 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1228 (mixedVector B) = 0 := by
  have h663 : mixedVector B (Sum.inr 663) = Sparse.eval nodeValue663 (mixedVector B) := by
    change mixedMoment B node663 node663Labels = _
    exact sound663 B hB hF
  have h683 : mixedVector B (Sum.inr 683) = Sparse.eval nodeValue683 (mixedVector B) := by
    change mixedMoment B node683 node683Labels = _
    exact sound683 B hB hF
  have h684 : mixedVector B (Sum.inr 684) = Sparse.eval nodeValue684 (mixedVector B) := by
    change mixedMoment B node684 node684Labels = _
    exact sound684 B hB hF
  have h688 : mixedVector B (Sum.inr 688) = Sparse.eval nodeValue688 (mixedVector B) := by
    change mixedMoment B node688 node688Labels = _
    exact sound688 B hB hF
  have h748 : mixedVector B (Sum.inr 748) = Sparse.eval nodeValue748 (mixedVector B) := by
    change mixedMoment B node748 node748Labels = _
    exact sound748 B hB hF
  have h762 : mixedVector B (Sum.inr 762) = Sparse.eval nodeValue762 (mixedVector B) := by
    change mixedMoment B node762 node762Labels = _
    exact sound762 B hB hF
  have h763 : mixedVector B (Sum.inr 763) = Sparse.eval nodeValue763 (mixedVector B) := by
    change mixedMoment B node763 node763Labels = _
    exact sound763 B hB hF
  have h767 : mixedVector B (Sum.inr 767) = Sparse.eval nodeValue767 (mixedVector B) := by
    change mixedMoment B node767 node767Labels = _
    exact sound767 B hB hF
  have h799 : mixedVector B (Sum.inr 799) = Sparse.eval nodeValue799 (mixedVector B) := by
    change mixedMoment B node799 node799Labels = _
    exact sound799 B hB hF
  have h804 : mixedVector B (Sum.inr 804) = Sparse.eval nodeValue804 (mixedVector B) := by
    change mixedMoment B node804 node804Labels = _
    exact sound804 B hB hF
  have h806 : mixedVector B (Sum.inr 806) = Sparse.eval nodeValue806 (mixedVector B) := by
    change mixedMoment B node806 node806Labels = _
    exact sound806 B hB hF
  have h842 : mixedVector B (Sum.inr 842) = Sparse.eval nodeValue842 (mixedVector B) := by
    change mixedMoment B node842 node842Labels = _
    exact sound842 B hB hF
  have h843 : mixedVector B (Sum.inr 843) = Sparse.eval nodeValue843 (mixedVector B) := by
    change mixedMoment B node843 node843Labels = _
    exact sound843 B hB hF
  have h849 : mixedVector B (Sum.inr 849) = Sparse.eval nodeValue849 (mixedVector B) := by
    change mixedMoment B node849 node849Labels = _
    exact sound849 B hB hF
  have h851 : mixedVector B (Sum.inr 851) = Sparse.eval nodeValue851 (mixedVector B) := by
    change mixedMoment B node851 node851Labels = _
    exact sound851 B hB hF
  have h852 : mixedVector B (Sum.inr 852) = Sparse.eval nodeValue852 (mixedVector B) := by
    change mixedMoment B node852 node852Labels = _
    exact sound852 B hB hF
  have h999 : mixedVector B (Sum.inr 999) = Sparse.eval nodeValue999 (mixedVector B) := by
    change mixedMoment B node999 node999Labels = _
    exact sound999 B hB hF
  have h1074 : mixedVector B (Sum.inr 1074) = Sparse.eval nodeValue1074 (mixedVector B) := by
    change mixedMoment B node1074 node1074Labels = _
    exact sound1074 B hB hF
  have h1080 : mixedVector B (Sum.inr 1080) = Sparse.eval nodeValue1080 (mixedVector B) := by
    change mixedMoment B node1080 node1080Labels = _
    exact sound1080 B hB hF
  have h1082 : mixedVector B (Sum.inr 1082) = Sparse.eval nodeValue1082 (mixedVector B) := by
    change mixedMoment B node1082 node1082Labels = _
    exact sound1082 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1430, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h663, h683, h684, h688, h748, h762, h763, h767, h799, h804, h806, h842, h843, h849, h851, h852, h999, h1074, h1080, h1082, h4069, reducedSource1228] using sourceEq1430 B hB

theorem rowSound1228 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1228 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1228, numericCheck1228, reducedZero1228 B hB hF, mul_zero]

theorem reducedZero1229 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1229 (mixedVector B) = 0 := by
  have h812 : mixedVector B (Sum.inr 812) = Sparse.eval nodeValue812 (mixedVector B) := by
    change mixedMoment B node812 node812Labels = _
    exact sound812 B hB hF
  have h1602 : mixedVector B (Sum.inr 1602) = Sparse.eval nodeValue1602 (mixedVector B) := by
    change mixedMoment B node1602 node1602Labels = _
    exact sound1602 B hB hF
  have h1650 : mixedVector B (Sum.inr 1650) = Sparse.eval nodeValue1650 (mixedVector B) := by
    change mixedMoment B node1650 node1650Labels = _
    exact sound1650 B hB hF
  have h1710 : mixedVector B (Sum.inr 1710) = Sparse.eval nodeValue1710 (mixedVector B) := by
    change mixedMoment B node1710 node1710Labels = _
    exact sound1710 B hB hF
  have h1727 : mixedVector B (Sum.inr 1727) = Sparse.eval nodeValue1727 (mixedVector B) := by
    change mixedMoment B node1727 node1727Labels = _
    exact sound1727 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1431, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h812, h1602, h1650, h1710, h1727, h4069, reducedSource1229] using sourceEq1431 B hB

theorem rowSound1229 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1229 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1229, numericCheck1229, reducedZero1229 B hB hF, mul_zero]

theorem reducedZero1230 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1230 (mixedVector B) = 0 := by
  have h733 : mixedVector B (Sum.inr 733) = Sparse.eval nodeValue733 (mixedVector B) := by
    change mixedMoment B node733 node733Labels = _
    exact sound733 B hB hF
  have h740 : mixedVector B (Sum.inr 740) = Sparse.eval nodeValue740 (mixedVector B) := by
    change mixedMoment B node740 node740Labels = _
    exact sound740 B hB hF
  have h742 : mixedVector B (Sum.inr 742) = Sparse.eval nodeValue742 (mixedVector B) := by
    change mixedMoment B node742 node742Labels = _
    exact sound742 B hB hF
  have h812 : mixedVector B (Sum.inr 812) = Sparse.eval nodeValue812 (mixedVector B) := by
    change mixedMoment B node812 node812Labels = _
    exact sound812 B hB hF
  have h1650 : mixedVector B (Sum.inr 1650) = Sparse.eval nodeValue1650 (mixedVector B) := by
    change mixedMoment B node1650 node1650Labels = _
    exact sound1650 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1433, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h733, h740, h742, h812, h1650, h4069, reducedSource1230] using sourceEq1433 B hB

theorem rowSound1230 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1230 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1230, numericCheck1230, reducedZero1230 B hB hF, mul_zero]

theorem reducedZero1231 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1231 (mixedVector B) = 0 := by
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  have h4099 : mixedVector B (Sum.inr 4099) = Sparse.eval nodeValue4099 (mixedVector B) := by
    change mixedMoment B node4099 node4099Labels = _
    exact sound4099 B hB hF
  have h4103 : mixedVector B (Sum.inr 4103) = Sparse.eval nodeValue4103 (mixedVector B) := by
    change mixedMoment B node4103 node4103Labels = _
    exact sound4103 B hB hF
  have h4109 : mixedVector B (Sum.inr 4109) = Sparse.eval nodeValue4109 (mixedVector B) := by
    change mixedMoment B node4109 node4109Labels = _
    exact sound4109 B hB hF
  have h4120 : mixedVector B (Sum.inr 4120) = Sparse.eval nodeValue4120 (mixedVector B) := by
    change mixedMoment B node4120 node4120Labels = _
    exact sound4120 B hB hF
  have h4195 : mixedVector B (Sum.inr 4195) = Sparse.eval nodeValue4195 (mixedVector B) := by
    change mixedMoment B node4195 node4195Labels = _
    exact sound4195 B hB hF
  have h4198 : mixedVector B (Sum.inr 4198) = Sparse.eval nodeValue4198 (mixedVector B) := by
    change mixedMoment B node4198 node4198Labels = _
    exact sound4198 B hB hF
  have h4203 : mixedVector B (Sum.inr 4203) = Sparse.eval nodeValue4203 (mixedVector B) := by
    change mixedMoment B node4203 node4203Labels = _
    exact sound4203 B hB hF
  have h4211 : mixedVector B (Sum.inr 4211) = Sparse.eval nodeValue4211 (mixedVector B) := by
    change mixedMoment B node4211 node4211Labels = _
    exact sound4211 B hB hF
  have h4231 : mixedVector B (Sum.inr 4231) = Sparse.eval nodeValue4231 (mixedVector B) := by
    change mixedMoment B node4231 node4231Labels = _
    exact sound4231 B hB hF
  have h4235 : mixedVector B (Sum.inr 4235) = Sparse.eval nodeValue4235 (mixedVector B) := by
    change mixedMoment B node4235 node4235Labels = _
    exact sound4235 B hB hF
  have h4241 : mixedVector B (Sum.inr 4241) = Sparse.eval nodeValue4241 (mixedVector B) := by
    change mixedMoment B node4241 node4241Labels = _
    exact sound4241 B hB hF
  have h4251 : mixedVector B (Sum.inr 4251) = Sparse.eval nodeValue4251 (mixedVector B) := by
    change mixedMoment B node4251 node4251Labels = _
    exact sound4251 B hB hF
  have h4266 : mixedVector B (Sum.inr 4266) = Sparse.eval nodeValue4266 (mixedVector B) := by
    change mixedMoment B node4266 node4266Labels = _
    exact sound4266 B hB hF
  have h4269 : mixedVector B (Sum.inr 4269) = Sparse.eval nodeValue4269 (mixedVector B) := by
    change mixedMoment B node4269 node4269Labels = _
    exact sound4269 B hB hF
  have h4272 : mixedVector B (Sum.inr 4272) = Sparse.eval nodeValue4272 (mixedVector B) := by
    change mixedMoment B node4272 node4272Labels = _
    exact sound4272 B hB hF
  have h4274 : mixedVector B (Sum.inr 4274) = Sparse.eval nodeValue4274 (mixedVector B) := by
    change mixedMoment B node4274 node4274Labels = _
    exact sound4274 B hB hF
  have h4398 : mixedVector B (Sum.inr 4398) = Sparse.eval nodeValue4398 (mixedVector B) := by
    change mixedMoment B node4398 node4398Labels = _
    exact sound4398 B hB hF
  have h4454 : mixedVector B (Sum.inr 4454) = Sparse.eval nodeValue4454 (mixedVector B) := by
    change mixedMoment B node4454 node4454Labels = _
    exact sound4454 B hB hF
  have h4460 : mixedVector B (Sum.inr 4460) = Sparse.eval nodeValue4460 (mixedVector B) := by
    change mixedMoment B node4460 node4460Labels = _
    exact sound4460 B hB hF
  have h4501 : mixedVector B (Sum.inr 4501) = Sparse.eval nodeValue4501 (mixedVector B) := by
    change mixedMoment B node4501 node4501Labels = _
    exact sound4501 B hB hF
  simpa only [sourceForm1435, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4070, h4099, h4103, h4109, h4120, h4195, h4198, h4203, h4211, h4231, h4235, h4241, h4251, h4266, h4269, h4272, h4274, h4398, h4454, h4460, h4501, reducedSource1231] using sourceEq1435 B hB

theorem rowSound1231 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1231 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1231, numericCheck1231, reducedZero1231 B hB hF, mul_zero]

theorem sourceRowsAt1216 : MixedData.sourceRows (1216 : Fin 2425) =
    MixedData.row1216 := by decide +kernel

theorem sourceRowsAt1217 : MixedData.sourceRows (1217 : Fin 2425) =
    MixedData.row1217 := by decide +kernel

theorem sourceRowsAt1218 : MixedData.sourceRows (1218 : Fin 2425) =
    MixedData.row1218 := by decide +kernel

theorem sourceRowsAt1219 : MixedData.sourceRows (1219 : Fin 2425) =
    MixedData.row1219 := by decide +kernel

theorem sourceRowsAt1220 : MixedData.sourceRows (1220 : Fin 2425) =
    MixedData.row1220 := by decide +kernel

theorem sourceRowsAt1221 : MixedData.sourceRows (1221 : Fin 2425) =
    MixedData.row1221 := by decide +kernel

theorem sourceRowsAt1222 : MixedData.sourceRows (1222 : Fin 2425) =
    MixedData.row1222 := by decide +kernel

theorem sourceRowsAt1223 : MixedData.sourceRows (1223 : Fin 2425) =
    MixedData.row1223 := by decide +kernel

theorem sourceRowsAt1224 : MixedData.sourceRows (1224 : Fin 2425) =
    MixedData.row1224 := by decide +kernel

theorem sourceRowsAt1225 : MixedData.sourceRows (1225 : Fin 2425) =
    MixedData.row1225 := by decide +kernel

theorem sourceRowsAt1226 : MixedData.sourceRows (1226 : Fin 2425) =
    MixedData.row1226 := by decide +kernel

theorem sourceRowsAt1227 : MixedData.sourceRows (1227 : Fin 2425) =
    MixedData.row1227 := by decide +kernel

theorem sourceRowsAt1228 : MixedData.sourceRows (1228 : Fin 2425) =
    MixedData.row1228 := by decide +kernel

theorem sourceRowsAt1229 : MixedData.sourceRows (1229 : Fin 2425) =
    MixedData.row1229 := by decide +kernel

theorem sourceRowsAt1230 : MixedData.sourceRows (1230 : Fin 2425) =
    MixedData.row1230 := by decide +kernel

theorem sourceRowsAt1231 : MixedData.sourceRows (1231 : Fin 2425) =
    MixedData.row1231 := by decide +kernel

theorem chunkSound76 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 76) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1216 ∨ k.val = 1217 ∨ k.val = 1218 ∨ k.val = 1219 ∨ k.val = 1220 ∨ k.val = 1221 ∨ k.val = 1222 ∨ k.val = 1223 ∨ k.val = 1224 ∨ k.val = 1225 ∨ k.val = 1226 ∨ k.val = 1227 ∨ k.val = 1228 ∨ k.val = 1229 ∨ k.val = 1230 ∨ k.val = 1231 := by omega
  rcases heq with h1216 | h1217 | h1218 | h1219 | h1220 | h1221 | h1222 | h1223 | h1224 | h1225 | h1226 | h1227 | h1228 | h1229 | h1230 | h1231
  · have he : k = (1216 : Fin 2425) := Fin.ext h1216
    subst k
    rw [sourceRowsAt1216]
    exact rowSound1216 B hB hF
  · have he : k = (1217 : Fin 2425) := Fin.ext h1217
    subst k
    rw [sourceRowsAt1217]
    exact rowSound1217 B hB hF
  · have he : k = (1218 : Fin 2425) := Fin.ext h1218
    subst k
    rw [sourceRowsAt1218]
    exact rowSound1218 B hB hF
  · have he : k = (1219 : Fin 2425) := Fin.ext h1219
    subst k
    rw [sourceRowsAt1219]
    exact rowSound1219 B hB hF
  · have he : k = (1220 : Fin 2425) := Fin.ext h1220
    subst k
    rw [sourceRowsAt1220]
    exact rowSound1220 B hB hF
  · have he : k = (1221 : Fin 2425) := Fin.ext h1221
    subst k
    rw [sourceRowsAt1221]
    exact rowSound1221 B hB hF
  · have he : k = (1222 : Fin 2425) := Fin.ext h1222
    subst k
    rw [sourceRowsAt1222]
    exact rowSound1222 B hB hF
  · have he : k = (1223 : Fin 2425) := Fin.ext h1223
    subst k
    rw [sourceRowsAt1223]
    exact rowSound1223 B hB hF
  · have he : k = (1224 : Fin 2425) := Fin.ext h1224
    subst k
    rw [sourceRowsAt1224]
    exact rowSound1224 B hB hF
  · have he : k = (1225 : Fin 2425) := Fin.ext h1225
    subst k
    rw [sourceRowsAt1225]
    exact rowSound1225 B hB hF
  · have he : k = (1226 : Fin 2425) := Fin.ext h1226
    subst k
    rw [sourceRowsAt1226]
    exact rowSound1226 B hB hF
  · have he : k = (1227 : Fin 2425) := Fin.ext h1227
    subst k
    rw [sourceRowsAt1227]
    exact rowSound1227 B hB hF
  · have he : k = (1228 : Fin 2425) := Fin.ext h1228
    subst k
    rw [sourceRowsAt1228]
    exact rowSound1228 B hB hF
  · have he : k = (1229 : Fin 2425) := Fin.ext h1229
    subst k
    rw [sourceRowsAt1229]
    exact rowSound1229 B hB hF
  · have he : k = (1230 : Fin 2425) := Fin.ext h1230
    subst k
    rw [sourceRowsAt1230]
    exact rowSound1230 B hB hF
  · have he : k = (1231 : Fin 2425) := Fin.ext h1231
    subst k
    rw [sourceRowsAt1231]
    exact rowSound1231 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
