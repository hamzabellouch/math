import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources46

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1248 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1248 (mixedVector B) = 0 := by
  have h1655 : mixedVector B (Sum.inr 1655) = Sparse.eval nodeValue1655 (mixedVector B) := by
    change mixedMoment B node1655 node1655Labels = _
    exact sound1655 B hB hF
  have h1657 : mixedVector B (Sum.inr 1657) = Sparse.eval nodeValue1657 (mixedVector B) := by
    change mixedMoment B node1657 node1657Labels = _
    exact sound1657 B hB hF
  have h1660 : mixedVector B (Sum.inr 1660) = Sparse.eval nodeValue1660 (mixedVector B) := by
    change mixedMoment B node1660 node1660Labels = _
    exact sound1660 B hB hF
  have h1738 : mixedVector B (Sum.inr 1738) = Sparse.eval nodeValue1738 (mixedVector B) := by
    change mixedMoment B node1738 node1738Labels = _
    exact sound1738 B hB hF
  have h2683 : mixedVector B (Sum.inr 2683) = Sparse.eval nodeValue2683 (mixedVector B) := by
    change mixedMoment B node2683 node2683Labels = _
    exact sound2683 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1459, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1655, h1657, h1660, h1738, h2683, h4071, reducedSource1248] using sourceEq1459 B hB

theorem rowSound1248 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1248 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1248, numericCheck1248, reducedZero1248 B hB hF, mul_zero]

theorem reducedZero1249 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1249 (mixedVector B) = 0 := by
  have h1741 : mixedVector B (Sum.inr 1741) = Sparse.eval nodeValue1741 (mixedVector B) := by
    change mixedMoment B node1741 node1741Labels = _
    exact sound1741 B hB hF
  have h2683 : mixedVector B (Sum.inr 2683) = Sparse.eval nodeValue2683 (mixedVector B) := by
    change mixedMoment B node2683 node2683Labels = _
    exact sound2683 B hB hF
  have h2780 : mixedVector B (Sum.inr 2780) = Sparse.eval nodeValue2780 (mixedVector B) := by
    change mixedMoment B node2780 node2780Labels = _
    exact sound2780 B hB hF
  have h3311 : mixedVector B (Sum.inr 3311) = Sparse.eval nodeValue3311 (mixedVector B) := by
    change mixedMoment B node3311 node3311Labels = _
    exact sound3311 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1460, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1741, h2683, h2780, h3311, h4071, reducedSource1249] using sourceEq1460 B hB

theorem rowSound1249 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1249 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1249, numericCheck1249, reducedZero1249 B hB hF, mul_zero]

theorem reducedZero1250 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1250 (mixedVector B) = 0 := by
  have h1627 : mixedVector B (Sum.inr 1627) = Sparse.eval nodeValue1627 (mixedVector B) := by
    change mixedMoment B node1627 node1627Labels = _
    exact sound1627 B hB hF
  have h2397 : mixedVector B (Sum.inr 2397) = Sparse.eval nodeValue2397 (mixedVector B) := by
    change mixedMoment B node2397 node2397Labels = _
    exact sound2397 B hB hF
  have h2409 : mixedVector B (Sum.inr 2409) = Sparse.eval nodeValue2409 (mixedVector B) := by
    change mixedMoment B node2409 node2409Labels = _
    exact sound2409 B hB hF
  have h2683 : mixedVector B (Sum.inr 2683) = Sparse.eval nodeValue2683 (mixedVector B) := by
    change mixedMoment B node2683 node2683Labels = _
    exact sound2683 B hB hF
  have h3301 : mixedVector B (Sum.inr 3301) = Sparse.eval nodeValue3301 (mixedVector B) := by
    change mixedMoment B node3301 node3301Labels = _
    exact sound3301 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1461, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1627, h2397, h2409, h2683, h3301, h4071, reducedSource1250] using sourceEq1461 B hB

theorem rowSound1250 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1250 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1250, numericCheck1250, reducedZero1250 B hB hF, mul_zero]

theorem reducedZero1251 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1251 (mixedVector B) = 0 := by
  have h1738 : mixedVector B (Sum.inr 1738) = Sparse.eval nodeValue1738 (mixedVector B) := by
    change mixedMoment B node1738 node1738Labels = _
    exact sound1738 B hB hF
  have h2683 : mixedVector B (Sum.inr 2683) = Sparse.eval nodeValue2683 (mixedVector B) := by
    change mixedMoment B node2683 node2683Labels = _
    exact sound2683 B hB hF
  have h3295 : mixedVector B (Sum.inr 3295) = Sparse.eval nodeValue3295 (mixedVector B) := by
    change mixedMoment B node3295 node3295Labels = _
    exact sound3295 B hB hF
  have h3301 : mixedVector B (Sum.inr 3301) = Sparse.eval nodeValue3301 (mixedVector B) := by
    change mixedMoment B node3301 node3301Labels = _
    exact sound3301 B hB hF
  have h3311 : mixedVector B (Sum.inr 3311) = Sparse.eval nodeValue3311 (mixedVector B) := by
    change mixedMoment B node3311 node3311Labels = _
    exact sound3311 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1462, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1738, h2683, h3295, h3301, h3311, h4071, reducedSource1251] using sourceEq1462 B hB

theorem rowSound1251 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1251 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1251, numericCheck1251, reducedZero1251 B hB hF, mul_zero]

theorem reducedZero1252 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1252 (mixedVector B) = 0 := by
  have h1113 : mixedVector B (Sum.inr 1113) = Sparse.eval nodeValue1113 (mixedVector B) := by
    change mixedMoment B node1113 node1113Labels = _
    exact sound1113 B hB hF
  have h1119 : mixedVector B (Sum.inr 1119) = Sparse.eval nodeValue1119 (mixedVector B) := by
    change mixedMoment B node1119 node1119Labels = _
    exact sound1119 B hB hF
  have h1121 : mixedVector B (Sum.inr 1121) = Sparse.eval nodeValue1121 (mixedVector B) := by
    change mixedMoment B node1121 node1121Labels = _
    exact sound1121 B hB hF
  have h1138 : mixedVector B (Sum.inr 1138) = Sparse.eval nodeValue1138 (mixedVector B) := by
    change mixedMoment B node1138 node1138Labels = _
    exact sound1138 B hB hF
  have h1219 : mixedVector B (Sum.inr 1219) = Sparse.eval nodeValue1219 (mixedVector B) := by
    change mixedMoment B node1219 node1219Labels = _
    exact sound1219 B hB hF
  have h2488 : mixedVector B (Sum.inr 2488) = Sparse.eval nodeValue2488 (mixedVector B) := by
    change mixedMoment B node2488 node2488Labels = _
    exact sound2488 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1463, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1113, h1119, h1121, h1138, h1219, h2488, h4092, reducedSource1252] using sourceEq1463 B hB

theorem rowSound1252 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1252 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1252, numericCheck1252, reducedZero1252 B hB hF, mul_zero]

theorem reducedZero1253 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1253 (mixedVector B) = 0 := by
  have h631 : mixedVector B (Sum.inr 631) = Sparse.eval nodeValue631 (mixedVector B) := by
    change mixedMoment B node631 node631Labels = _
    exact sound631 B hB hF
  have h1138 : mixedVector B (Sum.inr 1138) = Sparse.eval nodeValue1138 (mixedVector B) := by
    change mixedMoment B node1138 node1138Labels = _
    exact sound1138 B hB hF
  have h1151 : mixedVector B (Sum.inr 1151) = Sparse.eval nodeValue1151 (mixedVector B) := by
    change mixedMoment B node1151 node1151Labels = _
    exact sound1151 B hB hF
  have h1219 : mixedVector B (Sum.inr 1219) = Sparse.eval nodeValue1219 (mixedVector B) := by
    change mixedMoment B node1219 node1219Labels = _
    exact sound1219 B hB hF
  have h1236 : mixedVector B (Sum.inr 1236) = Sparse.eval nodeValue1236 (mixedVector B) := by
    change mixedMoment B node1236 node1236Labels = _
    exact sound1236 B hB hF
  have h1241 : mixedVector B (Sum.inr 1241) = Sparse.eval nodeValue1241 (mixedVector B) := by
    change mixedMoment B node1241 node1241Labels = _
    exact sound1241 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1464, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h631, h1138, h1151, h1219, h1236, h1241, h4092, reducedSource1253] using sourceEq1464 B hB

theorem rowSound1253 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1253 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1253, numericCheck1253, reducedZero1253 B hB hF, mul_zero]

theorem reducedZero1254 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1254 (mixedVector B) = 0 := by
  have h1606 : mixedVector B (Sum.inr 1606) = Sparse.eval nodeValue1606 (mixedVector B) := by
    change mixedMoment B node1606 node1606Labels = _
    exact sound1606 B hB hF
  have h1608 : mixedVector B (Sum.inr 1608) = Sparse.eval nodeValue1608 (mixedVector B) := by
    change mixedMoment B node1608 node1608Labels = _
    exact sound1608 B hB hF
  have h1611 : mixedVector B (Sum.inr 1611) = Sparse.eval nodeValue1611 (mixedVector B) := by
    change mixedMoment B node1611 node1611Labels = _
    exact sound1611 B hB hF
  have h1618 : mixedVector B (Sum.inr 1618) = Sparse.eval nodeValue1618 (mixedVector B) := by
    change mixedMoment B node1618 node1618Labels = _
    exact sound1618 B hB hF
  have h1738 : mixedVector B (Sum.inr 1738) = Sparse.eval nodeValue1738 (mixedVector B) := by
    change mixedMoment B node1738 node1738Labels = _
    exact sound1738 B hB hF
  have h3295 : mixedVector B (Sum.inr 3295) = Sparse.eval nodeValue3295 (mixedVector B) := by
    change mixedMoment B node3295 node3295Labels = _
    exact sound3295 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1465, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1606, h1608, h1611, h1618, h1738, h3295, h4071, reducedSource1254] using sourceEq1465 B hB

theorem rowSound1254 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1254 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1254, numericCheck1254, reducedZero1254 B hB hF, mul_zero]

theorem reducedZero1255 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1255 (mixedVector B) = 0 := by
  have h1114 : mixedVector B (Sum.inr 1114) = Sparse.eval nodeValue1114 (mixedVector B) := by
    change mixedMoment B node1114 node1114Labels = _
    exact sound1114 B hB hF
  have h1120 : mixedVector B (Sum.inr 1120) = Sparse.eval nodeValue1120 (mixedVector B) := by
    change mixedMoment B node1120 node1120Labels = _
    exact sound1120 B hB hF
  have h1139 : mixedVector B (Sum.inr 1139) = Sparse.eval nodeValue1139 (mixedVector B) := by
    change mixedMoment B node1139 node1139Labels = _
    exact sound1139 B hB hF
  have h1220 : mixedVector B (Sum.inr 1220) = Sparse.eval nodeValue1220 (mixedVector B) := by
    change mixedMoment B node1220 node1220Labels = _
    exact sound1220 B hB hF
  have h2489 : mixedVector B (Sum.inr 2489) = Sparse.eval nodeValue2489 (mixedVector B) := by
    change mixedMoment B node2489 node2489Labels = _
    exact sound2489 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1467, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1114, h1120, h1139, h1220, h2489, h4091, reducedSource1255] using sourceEq1467 B hB

theorem rowSound1255 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1255 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1255, numericCheck1255, reducedZero1255 B hB hF, mul_zero]

theorem reducedZero1256 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1256 (mixedVector B) = 0 := by
  have h632 : mixedVector B (Sum.inr 632) = Sparse.eval nodeValue632 (mixedVector B) := by
    change mixedMoment B node632 node632Labels = _
    exact sound632 B hB hF
  have h1139 : mixedVector B (Sum.inr 1139) = Sparse.eval nodeValue1139 (mixedVector B) := by
    change mixedMoment B node1139 node1139Labels = _
    exact sound1139 B hB hF
  have h1152 : mixedVector B (Sum.inr 1152) = Sparse.eval nodeValue1152 (mixedVector B) := by
    change mixedMoment B node1152 node1152Labels = _
    exact sound1152 B hB hF
  have h1220 : mixedVector B (Sum.inr 1220) = Sparse.eval nodeValue1220 (mixedVector B) := by
    change mixedMoment B node1220 node1220Labels = _
    exact sound1220 B hB hF
  have h1240 : mixedVector B (Sum.inr 1240) = Sparse.eval nodeValue1240 (mixedVector B) := by
    change mixedMoment B node1240 node1240Labels = _
    exact sound1240 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1468, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h632, h1139, h1152, h1220, h1240, h4091, reducedSource1256] using sourceEq1468 B hB

theorem rowSound1256 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1256 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1256, numericCheck1256, reducedZero1256 B hB hF, mul_zero]

theorem reducedZero1257 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1257 (mixedVector B) = 0 := by
  have h1614 : mixedVector B (Sum.inr 1614) = Sparse.eval nodeValue1614 (mixedVector B) := by
    change mixedMoment B node1614 node1614Labels = _
    exact sound1614 B hB hF
  have h1618 : mixedVector B (Sum.inr 1618) = Sparse.eval nodeValue1618 (mixedVector B) := by
    change mixedMoment B node1618 node1618Labels = _
    exact sound1618 B hB hF
  have h1626 : mixedVector B (Sum.inr 1626) = Sparse.eval nodeValue1626 (mixedVector B) := by
    change mixedMoment B node1626 node1626Labels = _
    exact sound1626 B hB hF
  have h1751 : mixedVector B (Sum.inr 1751) = Sparse.eval nodeValue1751 (mixedVector B) := by
    change mixedMoment B node1751 node1751Labels = _
    exact sound1751 B hB hF
  have h3297 : mixedVector B (Sum.inr 3297) = Sparse.eval nodeValue3297 (mixedVector B) := by
    change mixedMoment B node3297 node3297Labels = _
    exact sound3297 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1469, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1614, h1618, h1626, h1751, h3297, h4071, reducedSource1257] using sourceEq1469 B hB

theorem rowSound1257 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1257 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1257, numericCheck1257, reducedZero1257 B hB hF, mul_zero]

theorem reducedZero1258 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1258 (mixedVector B) = 0 := by
  have h1751 : mixedVector B (Sum.inr 1751) = Sparse.eval nodeValue1751 (mixedVector B) := by
    change mixedMoment B node1751 node1751Labels = _
    exact sound1751 B hB hF
  have h3297 : mixedVector B (Sum.inr 3297) = Sparse.eval nodeValue3297 (mixedVector B) := by
    change mixedMoment B node3297 node3297Labels = _
    exact sound3297 B hB hF
  have h3301 : mixedVector B (Sum.inr 3301) = Sparse.eval nodeValue3301 (mixedVector B) := by
    change mixedMoment B node3301 node3301Labels = _
    exact sound3301 B hB hF
  have h3312 : mixedVector B (Sum.inr 3312) = Sparse.eval nodeValue3312 (mixedVector B) := by
    change mixedMoment B node3312 node3312Labels = _
    exact sound3312 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1470, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1751, h3297, h3301, h3312, h4071, reducedSource1258] using sourceEq1470 B hB

theorem rowSound1258 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1258 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1258, numericCheck1258, reducedZero1258 B hB hF, mul_zero]

theorem reducedZero1259 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1259 (mixedVector B) = 0 := by
  have h1182 : mixedVector B (Sum.inr 1182) = Sparse.eval nodeValue1182 (mixedVector B) := by
    change mixedMoment B node1182 node1182Labels = _
    exact sound1182 B hB hF
  have h2388 : mixedVector B (Sum.inr 2388) = Sparse.eval nodeValue2388 (mixedVector B) := by
    change mixedMoment B node2388 node2388Labels = _
    exact sound2388 B hB hF
  have h2533 : mixedVector B (Sum.inr 2533) = Sparse.eval nodeValue2533 (mixedVector B) := by
    change mixedMoment B node2533 node2533Labels = _
    exact sound2533 B hB hF
  have h2608 : mixedVector B (Sum.inr 2608) = Sparse.eval nodeValue2608 (mixedVector B) := by
    change mixedMoment B node2608 node2608Labels = _
    exact sound2608 B hB hF
  have h2672 : mixedVector B (Sum.inr 2672) = Sparse.eval nodeValue2672 (mixedVector B) := by
    change mixedMoment B node2672 node2672Labels = _
    exact sound2672 B hB hF
  have h2673 : mixedVector B (Sum.inr 2673) = Sparse.eval nodeValue2673 (mixedVector B) := by
    change mixedMoment B node2673 node2673Labels = _
    exact sound2673 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm1471, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1182, h2388, h2533, h2608, h2672, h2673, h4088, reducedSource1259] using sourceEq1471 B hB

theorem rowSound1259 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1259 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1259, numericCheck1259, reducedZero1259 B hB hF, mul_zero]

theorem reducedZero1260 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1260 (mixedVector B) = 0 := by
  have h1196 : mixedVector B (Sum.inr 1196) = Sparse.eval nodeValue1196 (mixedVector B) := by
    change mixedMoment B node1196 node1196Labels = _
    exact sound1196 B hB hF
  have h2452 : mixedVector B (Sum.inr 2452) = Sparse.eval nodeValue2452 (mixedVector B) := by
    change mixedMoment B node2452 node2452Labels = _
    exact sound2452 B hB hF
  have h2609 : mixedVector B (Sum.inr 2609) = Sparse.eval nodeValue2609 (mixedVector B) := by
    change mixedMoment B node2609 node2609Labels = _
    exact sound2609 B hB hF
  have h2694 : mixedVector B (Sum.inr 2694) = Sparse.eval nodeValue2694 (mixedVector B) := by
    change mixedMoment B node2694 node2694Labels = _
    exact sound2694 B hB hF
  have h2695 : mixedVector B (Sum.inr 2695) = Sparse.eval nodeValue2695 (mixedVector B) := by
    change mixedMoment B node2695 node2695Labels = _
    exact sound2695 B hB hF
  have h4090 : mixedVector B (Sum.inr 4090) = Sparse.eval nodeValue4090 (mixedVector B) := by
    change mixedMoment B node4090 node4090Labels = _
    exact sound4090 B hB hF
  simpa only [sourceForm1472, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1196, h2452, h2609, h2694, h2695, h4090, reducedSource1260] using sourceEq1472 B hB

theorem rowSound1260 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1260 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1260, numericCheck1260, reducedZero1260 B hB hF, mul_zero]

theorem reducedZero1261 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1261 (mixedVector B) = 0 := by
  have h4185 : mixedVector B (Sum.inr 4185) = Sparse.eval nodeValue4185 (mixedVector B) := by
    change mixedMoment B node4185 node4185Labels = _
    exact sound4185 B hB hF
  have h4190 : mixedVector B (Sum.inr 4190) = Sparse.eval nodeValue4190 (mixedVector B) := by
    change mixedMoment B node4190 node4190Labels = _
    exact sound4190 B hB hF
  have h4192 : mixedVector B (Sum.inr 4192) = Sparse.eval nodeValue4192 (mixedVector B) := by
    change mixedMoment B node4192 node4192Labels = _
    exact sound4192 B hB hF
  have h4553 : mixedVector B (Sum.inr 4553) = Sparse.eval nodeValue4553 (mixedVector B) := by
    change mixedMoment B node4553 node4553Labels = _
    exact sound4553 B hB hF
  have h4557 : mixedVector B (Sum.inr 4557) = Sparse.eval nodeValue4557 (mixedVector B) := by
    change mixedMoment B node4557 node4557Labels = _
    exact sound4557 B hB hF
  have h4559 : mixedVector B (Sum.inr 4559) = Sparse.eval nodeValue4559 (mixedVector B) := by
    change mixedMoment B node4559 node4559Labels = _
    exact sound4559 B hB hF
  have h4619 : mixedVector B (Sum.inr 4619) = Sparse.eval nodeValue4619 (mixedVector B) := by
    change mixedMoment B node4619 node4619Labels = _
    exact sound4619 B hB hF
  have h4621 : mixedVector B (Sum.inr 4621) = Sparse.eval nodeValue4621 (mixedVector B) := by
    change mixedMoment B node4621 node4621Labels = _
    exact sound4621 B hB hF
  have h4623 : mixedVector B (Sum.inr 4623) = Sparse.eval nodeValue4623 (mixedVector B) := by
    change mixedMoment B node4623 node4623Labels = _
    exact sound4623 B hB hF
  have h4625 : mixedVector B (Sum.inr 4625) = Sparse.eval nodeValue4625 (mixedVector B) := by
    change mixedMoment B node4625 node4625Labels = _
    exact sound4625 B hB hF
  have h5176 : mixedVector B (Sum.inr 5176) = Sparse.eval nodeValue5176 (mixedVector B) := by
    change mixedMoment B node5176 node5176Labels = _
    exact sound5176 B hB hF
  have h5308 : mixedVector B (Sum.inr 5308) = Sparse.eval nodeValue5308 (mixedVector B) := by
    change mixedMoment B node5308 node5308Labels = _
    exact sound5308 B hB hF
  have h5310 : mixedVector B (Sum.inr 5310) = Sparse.eval nodeValue5310 (mixedVector B) := by
    change mixedMoment B node5310 node5310Labels = _
    exact sound5310 B hB hF
  simpa only [sourceForm1473, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4185, h4190, h4192, h4553, h4557, h4559, h4619, h4621, h4623, h4625, h5176, h5308, h5310, reducedSource1261] using sourceEq1473 B hB

theorem rowSound1261 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1261 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1261, numericCheck1261, reducedZero1261 B hB hF, mul_zero]

theorem reducedZero1262 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1262 (mixedVector B) = 0 := by
  have h613 : mixedVector B (Sum.inr 613) = Sparse.eval nodeValue613 (mixedVector B) := by
    change mixedMoment B node613 node613Labels = _
    exact sound613 B hB hF
  have h618 : mixedVector B (Sum.inr 618) = Sparse.eval nodeValue618 (mixedVector B) := by
    change mixedMoment B node618 node618Labels = _
    exact sound618 B hB hF
  have h620 : mixedVector B (Sum.inr 620) = Sparse.eval nodeValue620 (mixedVector B) := by
    change mixedMoment B node620 node620Labels = _
    exact sound620 B hB hF
  have h1138 : mixedVector B (Sum.inr 1138) = Sparse.eval nodeValue1138 (mixedVector B) := by
    change mixedMoment B node1138 node1138Labels = _
    exact sound1138 B hB hF
  have h1143 : mixedVector B (Sum.inr 1143) = Sparse.eval nodeValue1143 (mixedVector B) := by
    change mixedMoment B node1143 node1143Labels = _
    exact sound1143 B hB hF
  have h1145 : mixedVector B (Sum.inr 1145) = Sparse.eval nodeValue1145 (mixedVector B) := by
    change mixedMoment B node1145 node1145Labels = _
    exact sound1145 B hB hF
  have h1294 : mixedVector B (Sum.inr 1294) = Sparse.eval nodeValue1294 (mixedVector B) := by
    change mixedMoment B node1294 node1294Labels = _
    exact sound1294 B hB hF
  have h1297 : mixedVector B (Sum.inr 1297) = Sparse.eval nodeValue1297 (mixedVector B) := by
    change mixedMoment B node1297 node1297Labels = _
    exact sound1297 B hB hF
  have h1305 : mixedVector B (Sum.inr 1305) = Sparse.eval nodeValue1305 (mixedVector B) := by
    change mixedMoment B node1305 node1305Labels = _
    exact sound1305 B hB hF
  have h1307 : mixedVector B (Sum.inr 1307) = Sparse.eval nodeValue1307 (mixedVector B) := by
    change mixedMoment B node1307 node1307Labels = _
    exact sound1307 B hB hF
  have h2968 : mixedVector B (Sum.inr 2968) = Sparse.eval nodeValue2968 (mixedVector B) := by
    change mixedMoment B node2968 node2968Labels = _
    exact sound2968 B hB hF
  have h3121 : mixedVector B (Sum.inr 3121) = Sparse.eval nodeValue3121 (mixedVector B) := by
    change mixedMoment B node3121 node3121Labels = _
    exact sound3121 B hB hF
  have h3124 : mixedVector B (Sum.inr 3124) = Sparse.eval nodeValue3124 (mixedVector B) := by
    change mixedMoment B node3124 node3124Labels = _
    exact sound3124 B hB hF
  simpa only [sourceForm1474, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h613, h618, h620, h1138, h1143, h1145, h1294, h1297, h1305, h1307, h2968, h3121, h3124, reducedSource1262] using sourceEq1474 B hB

theorem rowSound1262 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1262 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1262, numericCheck1262, reducedZero1262 B hB hF, mul_zero]

theorem reducedZero1263 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1263 (mixedVector B) = 0 := by
  have h4466 : mixedVector B (Sum.inr 4466) = Sparse.eval nodeValue4466 (mixedVector B) := by
    change mixedMoment B node4466 node4466Labels = _
    exact sound4466 B hB hF
  have h4510 : mixedVector B (Sum.inr 4510) = Sparse.eval nodeValue4510 (mixedVector B) := by
    change mixedMoment B node4510 node4510Labels = _
    exact sound4510 B hB hF
  have h4511 : mixedVector B (Sum.inr 4511) = Sparse.eval nodeValue4511 (mixedVector B) := by
    change mixedMoment B node4511 node4511Labels = _
    exact sound4511 B hB hF
  have h4592 : mixedVector B (Sum.inr 4592) = Sparse.eval nodeValue4592 (mixedVector B) := by
    change mixedMoment B node4592 node4592Labels = _
    exact sound4592 B hB hF
  have h4611 : mixedVector B (Sum.inr 4611) = Sparse.eval nodeValue4611 (mixedVector B) := by
    change mixedMoment B node4611 node4611Labels = _
    exact sound4611 B hB hF
  have h4612 : mixedVector B (Sum.inr 4612) = Sparse.eval nodeValue4612 (mixedVector B) := by
    change mixedMoment B node4612 node4612Labels = _
    exact sound4612 B hB hF
  have h4626 : mixedVector B (Sum.inr 4626) = Sparse.eval nodeValue4626 (mixedVector B) := by
    change mixedMoment B node4626 node4626Labels = _
    exact sound4626 B hB hF
  have h4628 : mixedVector B (Sum.inr 4628) = Sparse.eval nodeValue4628 (mixedVector B) := by
    change mixedMoment B node4628 node4628Labels = _
    exact sound4628 B hB hF
  simpa only [sourceForm1475, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4466, h4510, h4511, h4592, h4611, h4612, h4626, h4628, reducedSource1263] using sourceEq1475 B hB

theorem rowSound1263 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1263 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1263, numericCheck1263, reducedZero1263 B hB hF, mul_zero]

theorem sourceRowsAt1248 : MixedData.sourceRows (1248 : Fin 2425) =
    MixedData.row1248 := by decide +kernel

theorem sourceRowsAt1249 : MixedData.sourceRows (1249 : Fin 2425) =
    MixedData.row1249 := by decide +kernel

theorem sourceRowsAt1250 : MixedData.sourceRows (1250 : Fin 2425) =
    MixedData.row1250 := by decide +kernel

theorem sourceRowsAt1251 : MixedData.sourceRows (1251 : Fin 2425) =
    MixedData.row1251 := by decide +kernel

theorem sourceRowsAt1252 : MixedData.sourceRows (1252 : Fin 2425) =
    MixedData.row1252 := by decide +kernel

theorem sourceRowsAt1253 : MixedData.sourceRows (1253 : Fin 2425) =
    MixedData.row1253 := by decide +kernel

theorem sourceRowsAt1254 : MixedData.sourceRows (1254 : Fin 2425) =
    MixedData.row1254 := by decide +kernel

theorem sourceRowsAt1255 : MixedData.sourceRows (1255 : Fin 2425) =
    MixedData.row1255 := by decide +kernel

theorem sourceRowsAt1256 : MixedData.sourceRows (1256 : Fin 2425) =
    MixedData.row1256 := by decide +kernel

theorem sourceRowsAt1257 : MixedData.sourceRows (1257 : Fin 2425) =
    MixedData.row1257 := by decide +kernel

theorem sourceRowsAt1258 : MixedData.sourceRows (1258 : Fin 2425) =
    MixedData.row1258 := by decide +kernel

theorem sourceRowsAt1259 : MixedData.sourceRows (1259 : Fin 2425) =
    MixedData.row1259 := by decide +kernel

theorem sourceRowsAt1260 : MixedData.sourceRows (1260 : Fin 2425) =
    MixedData.row1260 := by decide +kernel

theorem sourceRowsAt1261 : MixedData.sourceRows (1261 : Fin 2425) =
    MixedData.row1261 := by decide +kernel

theorem sourceRowsAt1262 : MixedData.sourceRows (1262 : Fin 2425) =
    MixedData.row1262 := by decide +kernel

theorem sourceRowsAt1263 : MixedData.sourceRows (1263 : Fin 2425) =
    MixedData.row1263 := by decide +kernel

theorem chunkSound78 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 78) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1248 ∨ k.val = 1249 ∨ k.val = 1250 ∨ k.val = 1251 ∨ k.val = 1252 ∨ k.val = 1253 ∨ k.val = 1254 ∨ k.val = 1255 ∨ k.val = 1256 ∨ k.val = 1257 ∨ k.val = 1258 ∨ k.val = 1259 ∨ k.val = 1260 ∨ k.val = 1261 ∨ k.val = 1262 ∨ k.val = 1263 := by omega
  rcases heq with h1248 | h1249 | h1250 | h1251 | h1252 | h1253 | h1254 | h1255 | h1256 | h1257 | h1258 | h1259 | h1260 | h1261 | h1262 | h1263
  · have he : k = (1248 : Fin 2425) := Fin.ext h1248
    subst k
    rw [sourceRowsAt1248]
    exact rowSound1248 B hB hF
  · have he : k = (1249 : Fin 2425) := Fin.ext h1249
    subst k
    rw [sourceRowsAt1249]
    exact rowSound1249 B hB hF
  · have he : k = (1250 : Fin 2425) := Fin.ext h1250
    subst k
    rw [sourceRowsAt1250]
    exact rowSound1250 B hB hF
  · have he : k = (1251 : Fin 2425) := Fin.ext h1251
    subst k
    rw [sourceRowsAt1251]
    exact rowSound1251 B hB hF
  · have he : k = (1252 : Fin 2425) := Fin.ext h1252
    subst k
    rw [sourceRowsAt1252]
    exact rowSound1252 B hB hF
  · have he : k = (1253 : Fin 2425) := Fin.ext h1253
    subst k
    rw [sourceRowsAt1253]
    exact rowSound1253 B hB hF
  · have he : k = (1254 : Fin 2425) := Fin.ext h1254
    subst k
    rw [sourceRowsAt1254]
    exact rowSound1254 B hB hF
  · have he : k = (1255 : Fin 2425) := Fin.ext h1255
    subst k
    rw [sourceRowsAt1255]
    exact rowSound1255 B hB hF
  · have he : k = (1256 : Fin 2425) := Fin.ext h1256
    subst k
    rw [sourceRowsAt1256]
    exact rowSound1256 B hB hF
  · have he : k = (1257 : Fin 2425) := Fin.ext h1257
    subst k
    rw [sourceRowsAt1257]
    exact rowSound1257 B hB hF
  · have he : k = (1258 : Fin 2425) := Fin.ext h1258
    subst k
    rw [sourceRowsAt1258]
    exact rowSound1258 B hB hF
  · have he : k = (1259 : Fin 2425) := Fin.ext h1259
    subst k
    rw [sourceRowsAt1259]
    exact rowSound1259 B hB hF
  · have he : k = (1260 : Fin 2425) := Fin.ext h1260
    subst k
    rw [sourceRowsAt1260]
    exact rowSound1260 B hB hF
  · have he : k = (1261 : Fin 2425) := Fin.ext h1261
    subst k
    rw [sourceRowsAt1261]
    exact rowSound1261 B hB hF
  · have he : k = (1262 : Fin 2425) := Fin.ext h1262
    subst k
    rw [sourceRowsAt1262]
    exact rowSound1262 B hB hF
  · have he : k = (1263 : Fin 2425) := Fin.ext h1263
    subst k
    rw [sourceRowsAt1263]
    exact rowSound1263 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
