import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources40

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1104 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1104 (mixedVector B) = 0 := by
  have h1530 : mixedVector B (Sum.inr 1530) = Sparse.eval nodeValue1530 (mixedVector B) := by
    change mixedMoment B node1530 node1530Labels = _
    exact sound1530 B hB hF
  have h1531 : mixedVector B (Sum.inr 1531) = Sparse.eval nodeValue1531 (mixedVector B) := by
    change mixedMoment B node1531 node1531Labels = _
    exact sound1531 B hB hF
  have h1540 : mixedVector B (Sum.inr 1540) = Sparse.eval nodeValue1540 (mixedVector B) := by
    change mixedMoment B node1540 node1540Labels = _
    exact sound1540 B hB hF
  have h1722 : mixedVector B (Sum.inr 1722) = Sparse.eval nodeValue1722 (mixedVector B) := by
    change mixedMoment B node1722 node1722Labels = _
    exact sound1722 B hB hF
  have h1752 : mixedVector B (Sum.inr 1752) = Sparse.eval nodeValue1752 (mixedVector B) := by
    change mixedMoment B node1752 node1752Labels = _
    exact sound1752 B hB hF
  have h2200 : mixedVector B (Sum.inr 2200) = Sparse.eval nodeValue2200 (mixedVector B) := by
    change mixedMoment B node2200 node2200Labels = _
    exact sound2200 B hB hF
  have h2226 : mixedVector B (Sum.inr 2226) = Sparse.eval nodeValue2226 (mixedVector B) := by
    change mixedMoment B node2226 node2226Labels = _
    exact sound2226 B hB hF
  have h2258 : mixedVector B (Sum.inr 2258) = Sparse.eval nodeValue2258 (mixedVector B) := by
    change mixedMoment B node2258 node2258Labels = _
    exact sound2258 B hB hF
  have h2261 : mixedVector B (Sum.inr 2261) = Sparse.eval nodeValue2261 (mixedVector B) := by
    change mixedMoment B node2261 node2261Labels = _
    exact sound2261 B hB hF
  have h2292 : mixedVector B (Sum.inr 2292) = Sparse.eval nodeValue2292 (mixedVector B) := by
    change mixedMoment B node2292 node2292Labels = _
    exact sound2292 B hB hF
  have h2737 : mixedVector B (Sum.inr 2737) = Sparse.eval nodeValue2737 (mixedVector B) := by
    change mixedMoment B node2737 node2737Labels = _
    exact sound2737 B hB hF
  have h2780 : mixedVector B (Sum.inr 2780) = Sparse.eval nodeValue2780 (mixedVector B) := by
    change mixedMoment B node2780 node2780Labels = _
    exact sound2780 B hB hF
  have h2783 : mixedVector B (Sum.inr 2783) = Sparse.eval nodeValue2783 (mixedVector B) := by
    change mixedMoment B node2783 node2783Labels = _
    exact sound2783 B hB hF
  simpa only [sourceForm1274, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1530, h1531, h1540, h1722, h1752, h2200, h2226, h2258, h2261, h2292, h2737, h2780, h2783, reducedSource1104] using sourceEq1274 B hB

theorem rowSound1104 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1104 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1104, numericCheck1104, reducedZero1104 B hB hF, mul_zero]

theorem reducedZero1105 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1105 (mixedVector B) = 0 := by
  have h639 : mixedVector B (Sum.inr 639) = Sparse.eval nodeValue639 (mixedVector B) := by
    change mixedMoment B node639 node639Labels = _
    exact sound639 B hB hF
  have h643 : mixedVector B (Sum.inr 643) = Sparse.eval nodeValue643 (mixedVector B) := by
    change mixedMoment B node643 node643Labels = _
    exact sound643 B hB hF
  have h654 : mixedVector B (Sum.inr 654) = Sparse.eval nodeValue654 (mixedVector B) := by
    change mixedMoment B node654 node654Labels = _
    exact sound654 B hB hF
  have h1297 : mixedVector B (Sum.inr 1297) = Sparse.eval nodeValue1297 (mixedVector B) := by
    change mixedMoment B node1297 node1297Labels = _
    exact sound1297 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1275, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h639, h643, h654, h1297, h4084, reducedSource1105] using sourceEq1275 B hB

theorem rowSound1105 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1105 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1105, numericCheck1105, reducedZero1105 B hB hF, mul_zero]

theorem reducedZero1106 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1106 (mixedVector B) = 0 := by
  have h639 : mixedVector B (Sum.inr 639) = Sparse.eval nodeValue639 (mixedVector B) := by
    change mixedMoment B node639 node639Labels = _
    exact sound639 B hB hF
  have h1157 : mixedVector B (Sum.inr 1157) = Sparse.eval nodeValue1157 (mixedVector B) := by
    change mixedMoment B node1157 node1157Labels = _
    exact sound1157 B hB hF
  have h1239 : mixedVector B (Sum.inr 1239) = Sparse.eval nodeValue1239 (mixedVector B) := by
    change mixedMoment B node1239 node1239Labels = _
    exact sound1239 B hB hF
  have h1292 : mixedVector B (Sum.inr 1292) = Sparse.eval nodeValue1292 (mixedVector B) := by
    change mixedMoment B node1292 node1292Labels = _
    exact sound1292 B hB hF
  have h1297 : mixedVector B (Sum.inr 1297) = Sparse.eval nodeValue1297 (mixedVector B) := by
    change mixedMoment B node1297 node1297Labels = _
    exact sound1297 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1276, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h639, h1157, h1239, h1292, h1297, h4084, reducedSource1106] using sourceEq1276 B hB

theorem rowSound1106 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1106 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1106, numericCheck1106, reducedZero1106 B hB hF, mul_zero]

theorem reducedZero1107 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1107 (mixedVector B) = 0 := by
  have h948 : mixedVector B (Sum.inr 948) = Sparse.eval nodeValue948 (mixedVector B) := by
    change mixedMoment B node948 node948Labels = _
    exact sound948 B hB hF
  have h1157 : mixedVector B (Sum.inr 1157) = Sparse.eval nodeValue1157 (mixedVector B) := by
    change mixedMoment B node1157 node1157Labels = _
    exact sound1157 B hB hF
  have h1174 : mixedVector B (Sum.inr 1174) = Sparse.eval nodeValue1174 (mixedVector B) := by
    change mixedMoment B node1174 node1174Labels = _
    exact sound1174 B hB hF
  have h1297 : mixedVector B (Sum.inr 1297) = Sparse.eval nodeValue1297 (mixedVector B) := by
    change mixedMoment B node1297 node1297Labels = _
    exact sound1297 B hB hF
  have h2109 : mixedVector B (Sum.inr 2109) = Sparse.eval nodeValue2109 (mixedVector B) := by
    change mixedMoment B node2109 node2109Labels = _
    exact sound2109 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1277, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h948, h1157, h1174, h1297, h2109, h4084, reducedSource1107] using sourceEq1277 B hB

theorem rowSound1107 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1107 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1107, numericCheck1107, reducedZero1107 B hB hF, mul_zero]

theorem reducedZero1108 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1108 (mixedVector B) = 0 := by
  have h4166 : mixedVector B (Sum.inr 4166) = Sparse.eval nodeValue4166 (mixedVector B) := by
    change mixedMoment B node4166 node4166Labels = _
    exact sound4166 B hB hF
  have h4168 : mixedVector B (Sum.inr 4168) = Sparse.eval nodeValue4168 (mixedVector B) := by
    change mixedMoment B node4168 node4168Labels = _
    exact sound4168 B hB hF
  have h4190 : mixedVector B (Sum.inr 4190) = Sparse.eval nodeValue4190 (mixedVector B) := by
    change mixedMoment B node4190 node4190Labels = _
    exact sound4190 B hB hF
  have h4240 : mixedVector B (Sum.inr 4240) = Sparse.eval nodeValue4240 (mixedVector B) := by
    change mixedMoment B node4240 node4240Labels = _
    exact sound4240 B hB hF
  have h4280 : mixedVector B (Sum.inr 4280) = Sparse.eval nodeValue4280 (mixedVector B) := by
    change mixedMoment B node4280 node4280Labels = _
    exact sound4280 B hB hF
  have h4538 : mixedVector B (Sum.inr 4538) = Sparse.eval nodeValue4538 (mixedVector B) := by
    change mixedMoment B node4538 node4538Labels = _
    exact sound4538 B hB hF
  have h4557 : mixedVector B (Sum.inr 4557) = Sparse.eval nodeValue4557 (mixedVector B) := by
    change mixedMoment B node4557 node4557Labels = _
    exact sound4557 B hB hF
  have h4572 : mixedVector B (Sum.inr 4572) = Sparse.eval nodeValue4572 (mixedVector B) := by
    change mixedMoment B node4572 node4572Labels = _
    exact sound4572 B hB hF
  have h4619 : mixedVector B (Sum.inr 4619) = Sparse.eval nodeValue4619 (mixedVector B) := by
    change mixedMoment B node4619 node4619Labels = _
    exact sound4619 B hB hF
  have h4627 : mixedVector B (Sum.inr 4627) = Sparse.eval nodeValue4627 (mixedVector B) := by
    change mixedMoment B node4627 node4627Labels = _
    exact sound4627 B hB hF
  have h4871 : mixedVector B (Sum.inr 4871) = Sparse.eval nodeValue4871 (mixedVector B) := by
    change mixedMoment B node4871 node4871Labels = _
    exact sound4871 B hB hF
  have h4899 : mixedVector B (Sum.inr 4899) = Sparse.eval nodeValue4899 (mixedVector B) := by
    change mixedMoment B node4899 node4899Labels = _
    exact sound4899 B hB hF
  have h5310 : mixedVector B (Sum.inr 5310) = Sparse.eval nodeValue5310 (mixedVector B) := by
    change mixedMoment B node5310 node5310Labels = _
    exact sound5310 B hB hF
  simpa only [sourceForm1278, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4166, h4168, h4190, h4240, h4280, h4538, h4557, h4572, h4619, h4627, h4871, h4899, h5310, reducedSource1108] using sourceEq1278 B hB

theorem rowSound1108 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1108 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1108, numericCheck1108, reducedZero1108 B hB hF, mul_zero]

theorem reducedZero1109 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1109 (mixedVector B) = 0 := by
  have h594 : mixedVector B (Sum.inr 594) = Sparse.eval nodeValue594 (mixedVector B) := by
    change mixedMoment B node594 node594Labels = _
    exact sound594 B hB hF
  have h596 : mixedVector B (Sum.inr 596) = Sparse.eval nodeValue596 (mixedVector B) := by
    change mixedMoment B node596 node596Labels = _
    exact sound596 B hB hF
  have h618 : mixedVector B (Sum.inr 618) = Sparse.eval nodeValue618 (mixedVector B) := by
    change mixedMoment B node618 node618Labels = _
    exact sound618 B hB hF
  have h740 : mixedVector B (Sum.inr 740) = Sparse.eval nodeValue740 (mixedVector B) := by
    change mixedMoment B node740 node740Labels = _
    exact sound740 B hB hF
  have h832 : mixedVector B (Sum.inr 832) = Sparse.eval nodeValue832 (mixedVector B) := by
    change mixedMoment B node832 node832Labels = _
    exact sound832 B hB hF
  have h1123 : mixedVector B (Sum.inr 1123) = Sparse.eval nodeValue1123 (mixedVector B) := by
    change mixedMoment B node1123 node1123Labels = _
    exact sound1123 B hB hF
  have h1143 : mixedVector B (Sum.inr 1143) = Sparse.eval nodeValue1143 (mixedVector B) := by
    change mixedMoment B node1143 node1143Labels = _
    exact sound1143 B hB hF
  have h1190 : mixedVector B (Sum.inr 1190) = Sparse.eval nodeValue1190 (mixedVector B) := by
    change mixedMoment B node1190 node1190Labels = _
    exact sound1190 B hB hF
  have h1294 : mixedVector B (Sum.inr 1294) = Sparse.eval nodeValue1294 (mixedVector B) := by
    change mixedMoment B node1294 node1294Labels = _
    exact sound1294 B hB hF
  have h1311 : mixedVector B (Sum.inr 1311) = Sparse.eval nodeValue1311 (mixedVector B) := by
    change mixedMoment B node1311 node1311Labels = _
    exact sound1311 B hB hF
  have h2112 : mixedVector B (Sum.inr 2112) = Sparse.eval nodeValue2112 (mixedVector B) := by
    change mixedMoment B node2112 node2112Labels = _
    exact sound2112 B hB hF
  have h2281 : mixedVector B (Sum.inr 2281) = Sparse.eval nodeValue2281 (mixedVector B) := by
    change mixedMoment B node2281 node2281Labels = _
    exact sound2281 B hB hF
  have h3121 : mixedVector B (Sum.inr 3121) = Sparse.eval nodeValue3121 (mixedVector B) := by
    change mixedMoment B node3121 node3121Labels = _
    exact sound3121 B hB hF
  simpa only [sourceForm1279, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h594, h596, h618, h740, h832, h1123, h1143, h1190, h1294, h1311, h2112, h2281, h3121, reducedSource1109] using sourceEq1279 B hB

theorem rowSound1109 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1109 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1109, numericCheck1109, reducedZero1109 B hB hF, mul_zero]

theorem reducedZero1110 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1110 (mixedVector B) = 0 := by
  have h1037 : mixedVector B (Sum.inr 1037) = Sparse.eval nodeValue1037 (mixedVector B) := by
    change mixedMoment B node1037 node1037Labels = _
    exact sound1037 B hB hF
  have h1077 : mixedVector B (Sum.inr 1077) = Sparse.eval nodeValue1077 (mixedVector B) := by
    change mixedMoment B node1077 node1077Labels = _
    exact sound1077 B hB hF
  have h1085 : mixedVector B (Sum.inr 1085) = Sparse.eval nodeValue1085 (mixedVector B) := by
    change mixedMoment B node1085 node1085Labels = _
    exact sound1085 B hB hF
  have h1211 : mixedVector B (Sum.inr 1211) = Sparse.eval nodeValue1211 (mixedVector B) := by
    change mixedMoment B node1211 node1211Labels = _
    exact sound1211 B hB hF
  have h1231 : mixedVector B (Sum.inr 1231) = Sparse.eval nodeValue1231 (mixedVector B) := by
    change mixedMoment B node1231 node1231Labels = _
    exact sound1231 B hB hF
  have h1239 : mixedVector B (Sum.inr 1239) = Sparse.eval nodeValue1239 (mixedVector B) := by
    change mixedMoment B node1239 node1239Labels = _
    exact sound1239 B hB hF
  have h1258 : mixedVector B (Sum.inr 1258) = Sparse.eval nodeValue1258 (mixedVector B) := by
    change mixedMoment B node1258 node1258Labels = _
    exact sound1258 B hB hF
  have h1264 : mixedVector B (Sum.inr 1264) = Sparse.eval nodeValue1264 (mixedVector B) := by
    change mixedMoment B node1264 node1264Labels = _
    exact sound1264 B hB hF
  have h1289 : mixedVector B (Sum.inr 1289) = Sparse.eval nodeValue1289 (mixedVector B) := by
    change mixedMoment B node1289 node1289Labels = _
    exact sound1289 B hB hF
  have h1304 : mixedVector B (Sum.inr 1304) = Sparse.eval nodeValue1304 (mixedVector B) := by
    change mixedMoment B node1304 node1304Labels = _
    exact sound1304 B hB hF
  have h1408 : mixedVector B (Sum.inr 1408) = Sparse.eval nodeValue1408 (mixedVector B) := by
    change mixedMoment B node1408 node1408Labels = _
    exact sound1408 B hB hF
  have h1438 : mixedVector B (Sum.inr 1438) = Sparse.eval nodeValue1438 (mixedVector B) := by
    change mixedMoment B node1438 node1438Labels = _
    exact sound1438 B hB hF
  have h1445 : mixedVector B (Sum.inr 1445) = Sparse.eval nodeValue1445 (mixedVector B) := by
    change mixedMoment B node1445 node1445Labels = _
    exact sound1445 B hB hF
  simpa only [sourceForm1281, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1037, h1077, h1085, h1211, h1231, h1239, h1258, h1264, h1289, h1304, h1408, h1438, h1445, reducedSource1110] using sourceEq1281 B hB

theorem rowSound1110 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1110 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1110, numericCheck1110, reducedZero1110 B hB hF, mul_zero]

theorem reducedZero1111 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1111 (mixedVector B) = 0 := by
  have h1047 : mixedVector B (Sum.inr 1047) = Sparse.eval nodeValue1047 (mixedVector B) := by
    change mixedMoment B node1047 node1047Labels = _
    exact sound1047 B hB hF
  have h1091 : mixedVector B (Sum.inr 1091) = Sparse.eval nodeValue1091 (mixedVector B) := by
    change mixedMoment B node1091 node1091Labels = _
    exact sound1091 B hB hF
  have h1092 : mixedVector B (Sum.inr 1092) = Sparse.eval nodeValue1092 (mixedVector B) := by
    change mixedMoment B node1092 node1092Labels = _
    exact sound1092 B hB hF
  have h1218 : mixedVector B (Sum.inr 1218) = Sparse.eval nodeValue1218 (mixedVector B) := by
    change mixedMoment B node1218 node1218Labels = _
    exact sound1218 B hB hF
  have h1243 : mixedVector B (Sum.inr 1243) = Sparse.eval nodeValue1243 (mixedVector B) := by
    change mixedMoment B node1243 node1243Labels = _
    exact sound1243 B hB hF
  have h1244 : mixedVector B (Sum.inr 1244) = Sparse.eval nodeValue1244 (mixedVector B) := by
    change mixedMoment B node1244 node1244Labels = _
    exact sound1244 B hB hF
  have h1271 : mixedVector B (Sum.inr 1271) = Sparse.eval nodeValue1271 (mixedVector B) := by
    change mixedMoment B node1271 node1271Labels = _
    exact sound1271 B hB hF
  have h1272 : mixedVector B (Sum.inr 1272) = Sparse.eval nodeValue1272 (mixedVector B) := by
    change mixedMoment B node1272 node1272Labels = _
    exact sound1272 B hB hF
  have h1307 : mixedVector B (Sum.inr 1307) = Sparse.eval nodeValue1307 (mixedVector B) := by
    change mixedMoment B node1307 node1307Labels = _
    exact sound1307 B hB hF
  have h1309 : mixedVector B (Sum.inr 1309) = Sparse.eval nodeValue1309 (mixedVector B) := by
    change mixedMoment B node1309 node1309Labels = _
    exact sound1309 B hB hF
  have h1417 : mixedVector B (Sum.inr 1417) = Sparse.eval nodeValue1417 (mixedVector B) := by
    change mixedMoment B node1417 node1417Labels = _
    exact sound1417 B hB hF
  have h1452 : mixedVector B (Sum.inr 1452) = Sparse.eval nodeValue1452 (mixedVector B) := by
    change mixedMoment B node1452 node1452Labels = _
    exact sound1452 B hB hF
  have h1453 : mixedVector B (Sum.inr 1453) = Sparse.eval nodeValue1453 (mixedVector B) := by
    change mixedMoment B node1453 node1453Labels = _
    exact sound1453 B hB hF
  simpa only [sourceForm1282, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1047, h1091, h1092, h1218, h1243, h1244, h1271, h1272, h1307, h1309, h1417, h1452, h1453, reducedSource1111] using sourceEq1282 B hB

theorem rowSound1111 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1111 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1111, numericCheck1111, reducedZero1111 B hB hF, mul_zero]

theorem reducedZero1112 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1112 (mixedVector B) = 0 := by
  have h1077 : mixedVector B (Sum.inr 1077) = Sparse.eval nodeValue1077 (mixedVector B) := by
    change mixedMoment B node1077 node1077Labels = _
    exact sound1077 B hB hF
  have h1647 : mixedVector B (Sum.inr 1647) = Sparse.eval nodeValue1647 (mixedVector B) := by
    change mixedMoment B node1647 node1647Labels = _
    exact sound1647 B hB hF
  have h1730 : mixedVector B (Sum.inr 1730) = Sparse.eval nodeValue1730 (mixedVector B) := by
    change mixedMoment B node1730 node1730Labels = _
    exact sound1730 B hB hF
  have h2289 : mixedVector B (Sum.inr 2289) = Sparse.eval nodeValue2289 (mixedVector B) := by
    change mixedMoment B node2289 node2289Labels = _
    exact sound2289 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1283, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1077, h1647, h1730, h2289, h4070, reducedSource1112] using sourceEq1283 B hB

theorem rowSound1112 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1112 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1112, numericCheck1112, reducedZero1112 B hB hF, mul_zero]

theorem reducedZero1113 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1113 (mixedVector B) = 0 := by
  have h1289 : mixedVector B (Sum.inr 1289) = Sparse.eval nodeValue1289 (mixedVector B) := by
    change mixedMoment B node1289 node1289Labels = _
    exact sound1289 B hB hF
  have h1657 : mixedVector B (Sum.inr 1657) = Sparse.eval nodeValue1657 (mixedVector B) := by
    change mixedMoment B node1657 node1657Labels = _
    exact sound1657 B hB hF
  have h1741 : mixedVector B (Sum.inr 1741) = Sparse.eval nodeValue1741 (mixedVector B) := by
    change mixedMoment B node1741 node1741Labels = _
    exact sound1741 B hB hF
  have h2780 : mixedVector B (Sum.inr 2780) = Sparse.eval nodeValue2780 (mixedVector B) := by
    change mixedMoment B node2780 node2780Labels = _
    exact sound2780 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1284, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1289, h1657, h1741, h2780, h4071, reducedSource1113] using sourceEq1284 B hB

theorem rowSound1113 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1113 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1113, numericCheck1113, reducedZero1113 B hB hF, mul_zero]

theorem reducedZero1114 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1114 (mixedVector B) = 0 := by
  have h4153 : mixedVector B (Sum.inr 4153) = Sparse.eval nodeValue4153 (mixedVector B) := by
    change mixedMoment B node4153 node4153Labels = _
    exact sound4153 B hB hF
  have h4156 : mixedVector B (Sum.inr 4156) = Sparse.eval nodeValue4156 (mixedVector B) := by
    change mixedMoment B node4156 node4156Labels = _
    exact sound4156 B hB hF
  have h4161 : mixedVector B (Sum.inr 4161) = Sparse.eval nodeValue4161 (mixedVector B) := by
    change mixedMoment B node4161 node4161Labels = _
    exact sound4161 B hB hF
  have h4178 : mixedVector B (Sum.inr 4178) = Sparse.eval nodeValue4178 (mixedVector B) := by
    change mixedMoment B node4178 node4178Labels = _
    exact sound4178 B hB hF
  have h4528 : mixedVector B (Sum.inr 4528) = Sparse.eval nodeValue4528 (mixedVector B) := by
    change mixedMoment B node4528 node4528Labels = _
    exact sound4528 B hB hF
  have h4531 : mixedVector B (Sum.inr 4531) = Sparse.eval nodeValue4531 (mixedVector B) := by
    change mixedMoment B node4531 node4531Labels = _
    exact sound4531 B hB hF
  have h4535 : mixedVector B (Sum.inr 4535) = Sparse.eval nodeValue4535 (mixedVector B) := by
    change mixedMoment B node4535 node4535Labels = _
    exact sound4535 B hB hF
  have h4546 : mixedVector B (Sum.inr 4546) = Sparse.eval nodeValue4546 (mixedVector B) := by
    change mixedMoment B node4546 node4546Labels = _
    exact sound4546 B hB hF
  have h4547 : mixedVector B (Sum.inr 4547) = Sparse.eval nodeValue4547 (mixedVector B) := by
    change mixedMoment B node4547 node4547Labels = _
    exact sound4547 B hB hF
  have h4555 : mixedVector B (Sum.inr 4555) = Sparse.eval nodeValue4555 (mixedVector B) := by
    change mixedMoment B node4555 node4555Labels = _
    exact sound4555 B hB hF
  have h4558 : mixedVector B (Sum.inr 4558) = Sparse.eval nodeValue4558 (mixedVector B) := by
    change mixedMoment B node4558 node4558Labels = _
    exact sound4558 B hB hF
  have h4591 : mixedVector B (Sum.inr 4591) = Sparse.eval nodeValue4591 (mixedVector B) := by
    change mixedMoment B node4591 node4591Labels = _
    exact sound4591 B hB hF
  have h4594 : mixedVector B (Sum.inr 4594) = Sparse.eval nodeValue4594 (mixedVector B) := by
    change mixedMoment B node4594 node4594Labels = _
    exact sound4594 B hB hF
  have h4602 : mixedVector B (Sum.inr 4602) = Sparse.eval nodeValue4602 (mixedVector B) := by
    change mixedMoment B node4602 node4602Labels = _
    exact sound4602 B hB hF
  have h4609 : mixedVector B (Sum.inr 4609) = Sparse.eval nodeValue4609 (mixedVector B) := by
    change mixedMoment B node4609 node4609Labels = _
    exact sound4609 B hB hF
  have h4612 : mixedVector B (Sum.inr 4612) = Sparse.eval nodeValue4612 (mixedVector B) := by
    change mixedMoment B node4612 node4612Labels = _
    exact sound4612 B hB hF
  have h4619 : mixedVector B (Sum.inr 4619) = Sparse.eval nodeValue4619 (mixedVector B) := by
    change mixedMoment B node4619 node4619Labels = _
    exact sound4619 B hB hF
  have h5075 : mixedVector B (Sum.inr 5075) = Sparse.eval nodeValue5075 (mixedVector B) := by
    change mixedMoment B node5075 node5075Labels = _
    exact sound5075 B hB hF
  have h5107 : mixedVector B (Sum.inr 5107) = Sparse.eval nodeValue5107 (mixedVector B) := by
    change mixedMoment B node5107 node5107Labels = _
    exact sound5107 B hB hF
  have h5261 : mixedVector B (Sum.inr 5261) = Sparse.eval nodeValue5261 (mixedVector B) := by
    change mixedMoment B node5261 node5261Labels = _
    exact sound5261 B hB hF
  have h5274 : mixedVector B (Sum.inr 5274) = Sparse.eval nodeValue5274 (mixedVector B) := by
    change mixedMoment B node5274 node5274Labels = _
    exact sound5274 B hB hF
  simpa only [sourceForm1285, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4153, h4156, h4161, h4178, h4528, h4531, h4535, h4546, h4547, h4555, h4558, h4591, h4594, h4602, h4609, h4612, h4619, h5075, h5107, h5261, h5274, reducedSource1114] using sourceEq1285 B hB

theorem rowSound1114 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1114 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1114, numericCheck1114, reducedZero1114 B hB hF, mul_zero]

theorem reducedZero1115 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1115 (mixedVector B) = 0 := by
  have h581 : mixedVector B (Sum.inr 581) = Sparse.eval nodeValue581 (mixedVector B) := by
    change mixedMoment B node581 node581Labels = _
    exact sound581 B hB hF
  have h584 : mixedVector B (Sum.inr 584) = Sparse.eval nodeValue584 (mixedVector B) := by
    change mixedMoment B node584 node584Labels = _
    exact sound584 B hB hF
  have h589 : mixedVector B (Sum.inr 589) = Sparse.eval nodeValue589 (mixedVector B) := by
    change mixedMoment B node589 node589Labels = _
    exact sound589 B hB hF
  have h606 : mixedVector B (Sum.inr 606) = Sparse.eval nodeValue606 (mixedVector B) := by
    change mixedMoment B node606 node606Labels = _
    exact sound606 B hB hF
  have h1112 : mixedVector B (Sum.inr 1112) = Sparse.eval nodeValue1112 (mixedVector B) := by
    change mixedMoment B node1112 node1112Labels = _
    exact sound1112 B hB hF
  have h1115 : mixedVector B (Sum.inr 1115) = Sparse.eval nodeValue1115 (mixedVector B) := by
    change mixedMoment B node1115 node1115Labels = _
    exact sound1115 B hB hF
  have h1120 : mixedVector B (Sum.inr 1120) = Sparse.eval nodeValue1120 (mixedVector B) := by
    change mixedMoment B node1120 node1120Labels = _
    exact sound1120 B hB hF
  have h1132 : mixedVector B (Sum.inr 1132) = Sparse.eval nodeValue1132 (mixedVector B) := by
    change mixedMoment B node1132 node1132Labels = _
    exact sound1132 B hB hF
  have h1165 : mixedVector B (Sum.inr 1165) = Sparse.eval nodeValue1165 (mixedVector B) := by
    change mixedMoment B node1165 node1165Labels = _
    exact sound1165 B hB hF
  have h1168 : mixedVector B (Sum.inr 1168) = Sparse.eval nodeValue1168 (mixedVector B) := by
    change mixedMoment B node1168 node1168Labels = _
    exact sound1168 B hB hF
  have h1176 : mixedVector B (Sum.inr 1176) = Sparse.eval nodeValue1176 (mixedVector B) := by
    change mixedMoment B node1176 node1176Labels = _
    exact sound1176 B hB hF
  have h1217 : mixedVector B (Sum.inr 1217) = Sparse.eval nodeValue1217 (mixedVector B) := by
    change mixedMoment B node1217 node1217Labels = _
    exact sound1217 B hB hF
  have h1221 : mixedVector B (Sum.inr 1221) = Sparse.eval nodeValue1221 (mixedVector B) := by
    change mixedMoment B node1221 node1221Labels = _
    exact sound1221 B hB hF
  have h1243 : mixedVector B (Sum.inr 1243) = Sparse.eval nodeValue1243 (mixedVector B) := by
    change mixedMoment B node1243 node1243Labels = _
    exact sound1243 B hB hF
  have h1267 : mixedVector B (Sum.inr 1267) = Sparse.eval nodeValue1267 (mixedVector B) := by
    change mixedMoment B node1267 node1267Labels = _
    exact sound1267 B hB hF
  have h1274 : mixedVector B (Sum.inr 1274) = Sparse.eval nodeValue1274 (mixedVector B) := by
    change mixedMoment B node1274 node1274Labels = _
    exact sound1274 B hB hF
  have h1302 : mixedVector B (Sum.inr 1302) = Sparse.eval nodeValue1302 (mixedVector B) := by
    change mixedMoment B node1302 node1302Labels = _
    exact sound1302 B hB hF
  have h2939 : mixedVector B (Sum.inr 2939) = Sparse.eval nodeValue2939 (mixedVector B) := by
    change mixedMoment B node2939 node2939Labels = _
    exact sound2939 B hB hF
  have h3002 : mixedVector B (Sum.inr 3002) = Sparse.eval nodeValue3002 (mixedVector B) := by
    change mixedMoment B node3002 node3002Labels = _
    exact sound3002 B hB hF
  have h3090 : mixedVector B (Sum.inr 3090) = Sparse.eval nodeValue3090 (mixedVector B) := by
    change mixedMoment B node3090 node3090Labels = _
    exact sound3090 B hB hF
  have h3112 : mixedVector B (Sum.inr 3112) = Sparse.eval nodeValue3112 (mixedVector B) := by
    change mixedMoment B node3112 node3112Labels = _
    exact sound3112 B hB hF
  simpa only [sourceForm1286, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h581, h584, h589, h606, h1112, h1115, h1120, h1132, h1165, h1168, h1176, h1217, h1221, h1243, h1267, h1274, h1302, h2939, h3002, h3090, h3112, reducedSource1115] using sourceEq1286 B hB

theorem rowSound1115 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1115 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1115, numericCheck1115, reducedZero1115 B hB hF, mul_zero]

theorem reducedZero1116 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1116 (mixedVector B) = 0 := by
  have h1514 : mixedVector B (Sum.inr 1514) = Sparse.eval nodeValue1514 (mixedVector B) := by
    change mixedMoment B node1514 node1514Labels = _
    exact sound1514 B hB hF
  have h1516 : mixedVector B (Sum.inr 1516) = Sparse.eval nodeValue1516 (mixedVector B) := by
    change mixedMoment B node1516 node1516Labels = _
    exact sound1516 B hB hF
  have h1520 : mixedVector B (Sum.inr 1520) = Sparse.eval nodeValue1520 (mixedVector B) := by
    change mixedMoment B node1520 node1520Labels = _
    exact sound1520 B hB hF
  have h1533 : mixedVector B (Sum.inr 1533) = Sparse.eval nodeValue1533 (mixedVector B) := by
    change mixedMoment B node1533 node1533Labels = _
    exact sound1533 B hB hF
  have h3260 : mixedVector B (Sum.inr 3260) = Sparse.eval nodeValue3260 (mixedVector B) := by
    change mixedMoment B node3260 node3260Labels = _
    exact sound3260 B hB hF
  have h3262 : mixedVector B (Sum.inr 3262) = Sparse.eval nodeValue3262 (mixedVector B) := by
    change mixedMoment B node3262 node3262Labels = _
    exact sound3262 B hB hF
  have h3264 : mixedVector B (Sum.inr 3264) = Sparse.eval nodeValue3264 (mixedVector B) := by
    change mixedMoment B node3264 node3264Labels = _
    exact sound3264 B hB hF
  have h3266 : mixedVector B (Sum.inr 3266) = Sparse.eval nodeValue3266 (mixedVector B) := by
    change mixedMoment B node3266 node3266Labels = _
    exact sound3266 B hB hF
  have h3272 : mixedVector B (Sum.inr 3272) = Sparse.eval nodeValue3272 (mixedVector B) := by
    change mixedMoment B node3272 node3272Labels = _
    exact sound3272 B hB hF
  have h3275 : mixedVector B (Sum.inr 3275) = Sparse.eval nodeValue3275 (mixedVector B) := by
    change mixedMoment B node3275 node3275Labels = _
    exact sound3275 B hB hF
  have h3276 : mixedVector B (Sum.inr 3276) = Sparse.eval nodeValue3276 (mixedVector B) := by
    change mixedMoment B node3276 node3276Labels = _
    exact sound3276 B hB hF
  have h3291 : mixedVector B (Sum.inr 3291) = Sparse.eval nodeValue3291 (mixedVector B) := by
    change mixedMoment B node3291 node3291Labels = _
    exact sound3291 B hB hF
  have h3293 : mixedVector B (Sum.inr 3293) = Sparse.eval nodeValue3293 (mixedVector B) := by
    change mixedMoment B node3293 node3293Labels = _
    exact sound3293 B hB hF
  have h3298 : mixedVector B (Sum.inr 3298) = Sparse.eval nodeValue3298 (mixedVector B) := by
    change mixedMoment B node3298 node3298Labels = _
    exact sound3298 B hB hF
  have h3301 : mixedVector B (Sum.inr 3301) = Sparse.eval nodeValue3301 (mixedVector B) := by
    change mixedMoment B node3301 node3301Labels = _
    exact sound3301 B hB hF
  have h3302 : mixedVector B (Sum.inr 3302) = Sparse.eval nodeValue3302 (mixedVector B) := by
    change mixedMoment B node3302 node3302Labels = _
    exact sound3302 B hB hF
  have h3305 : mixedVector B (Sum.inr 3305) = Sparse.eval nodeValue3305 (mixedVector B) := by
    change mixedMoment B node3305 node3305Labels = _
    exact sound3305 B hB hF
  have h3468 : mixedVector B (Sum.inr 3468) = Sparse.eval nodeValue3468 (mixedVector B) := by
    change mixedMoment B node3468 node3468Labels = _
    exact sound3468 B hB hF
  have h3484 : mixedVector B (Sum.inr 3484) = Sparse.eval nodeValue3484 (mixedVector B) := by
    change mixedMoment B node3484 node3484Labels = _
    exact sound3484 B hB hF
  have h3545 : mixedVector B (Sum.inr 3545) = Sparse.eval nodeValue3545 (mixedVector B) := by
    change mixedMoment B node3545 node3545Labels = _
    exact sound3545 B hB hF
  have h3547 : mixedVector B (Sum.inr 3547) = Sparse.eval nodeValue3547 (mixedVector B) := by
    change mixedMoment B node3547 node3547Labels = _
    exact sound3547 B hB hF
  simpa only [sourceForm1287, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1514, h1516, h1520, h1533, h3260, h3262, h3264, h3266, h3272, h3275, h3276, h3291, h3293, h3298, h3301, h3302, h3305, h3468, h3484, h3545, h3547, reducedSource1116] using sourceEq1287 B hB

theorem rowSound1116 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1116 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1116, numericCheck1116, reducedZero1116 B hB hF, mul_zero]

theorem reducedZero1117 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1117 (mixedVector B) = 0 := by
  have h626 : mixedVector B (Sum.inr 626) = Sparse.eval nodeValue626 (mixedVector B) := by
    change mixedMoment B node626 node626Labels = _
    exact sound626 B hB hF
  have h633 : mixedVector B (Sum.inr 633) = Sparse.eval nodeValue633 (mixedVector B) := by
    change mixedMoment B node633 node633Labels = _
    exact sound633 B hB hF
  have h635 : mixedVector B (Sum.inr 635) = Sparse.eval nodeValue635 (mixedVector B) := by
    change mixedMoment B node635 node635Labels = _
    exact sound635 B hB hF
  have h641 : mixedVector B (Sum.inr 641) = Sparse.eval nodeValue641 (mixedVector B) := by
    change mixedMoment B node641 node641Labels = _
    exact sound641 B hB hF
  have h1242 : mixedVector B (Sum.inr 1242) = Sparse.eval nodeValue1242 (mixedVector B) := by
    change mixedMoment B node1242 node1242Labels = _
    exact sound1242 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1288, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h626, h633, h635, h641, h1242, h4092, reducedSource1117] using sourceEq1288 B hB

theorem rowSound1117 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1117 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1117, numericCheck1117, reducedZero1117 B hB hF, mul_zero]

theorem reducedZero1118 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1118 (mixedVector B) = 0 := by
  have h1115 : mixedVector B (Sum.inr 1115) = Sparse.eval nodeValue1115 (mixedVector B) := by
    change mixedMoment B node1115 node1115Labels = _
    exact sound1115 B hB hF
  have h1148 : mixedVector B (Sum.inr 1148) = Sparse.eval nodeValue1148 (mixedVector B) := by
    change mixedMoment B node1148 node1148Labels = _
    exact sound1148 B hB hF
  have h1154 : mixedVector B (Sum.inr 1154) = Sparse.eval nodeValue1154 (mixedVector B) := by
    change mixedMoment B node1154 node1154Labels = _
    exact sound1154 B hB hF
  have h1159 : mixedVector B (Sum.inr 1159) = Sparse.eval nodeValue1159 (mixedVector B) := by
    change mixedMoment B node1159 node1159Labels = _
    exact sound1159 B hB hF
  have h1242 : mixedVector B (Sum.inr 1242) = Sparse.eval nodeValue1242 (mixedVector B) := by
    change mixedMoment B node1242 node1242Labels = _
    exact sound1242 B hB hF
  have h2482 : mixedVector B (Sum.inr 2482) = Sparse.eval nodeValue2482 (mixedVector B) := by
    change mixedMoment B node2482 node2482Labels = _
    exact sound2482 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1289, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1115, h1148, h1154, h1159, h1242, h2482, h4092, reducedSource1118] using sourceEq1289 B hB

theorem rowSound1118 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1118 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1118, numericCheck1118, reducedZero1118 B hB hF, mul_zero]

theorem reducedZero1119 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1119 (mixedVector B) = 0 := by
  have h1131 : mixedVector B (Sum.inr 1131) = Sparse.eval nodeValue1131 (mixedVector B) := by
    change mixedMoment B node1131 node1131Labels = _
    exact sound1131 B hB hF
  have h1140 : mixedVector B (Sum.inr 1140) = Sparse.eval nodeValue1140 (mixedVector B) := by
    change mixedMoment B node1140 node1140Labels = _
    exact sound1140 B hB hF
  have h1144 : mixedVector B (Sum.inr 1144) = Sparse.eval nodeValue1144 (mixedVector B) := by
    change mixedMoment B node1144 node1144Labels = _
    exact sound1144 B hB hF
  have h1242 : mixedVector B (Sum.inr 1242) = Sparse.eval nodeValue1242 (mixedVector B) := by
    change mixedMoment B node1242 node1242Labels = _
    exact sound1242 B hB hF
  have h2517 : mixedVector B (Sum.inr 2517) = Sparse.eval nodeValue2517 (mixedVector B) := by
    change mixedMoment B node2517 node2517Labels = _
    exact sound2517 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1290, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1131, h1140, h1144, h1242, h2517, h4092, reducedSource1119] using sourceEq1290 B hB

theorem rowSound1119 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1119 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1119, numericCheck1119, reducedZero1119 B hB hF, mul_zero]

theorem sourceRowsAt1104 : MixedData.sourceRows (1104 : Fin 2425) =
    MixedData.row1104 := by decide +kernel

theorem sourceRowsAt1105 : MixedData.sourceRows (1105 : Fin 2425) =
    MixedData.row1105 := by decide +kernel

theorem sourceRowsAt1106 : MixedData.sourceRows (1106 : Fin 2425) =
    MixedData.row1106 := by decide +kernel

theorem sourceRowsAt1107 : MixedData.sourceRows (1107 : Fin 2425) =
    MixedData.row1107 := by decide +kernel

theorem sourceRowsAt1108 : MixedData.sourceRows (1108 : Fin 2425) =
    MixedData.row1108 := by decide +kernel

theorem sourceRowsAt1109 : MixedData.sourceRows (1109 : Fin 2425) =
    MixedData.row1109 := by decide +kernel

theorem sourceRowsAt1110 : MixedData.sourceRows (1110 : Fin 2425) =
    MixedData.row1110 := by decide +kernel

theorem sourceRowsAt1111 : MixedData.sourceRows (1111 : Fin 2425) =
    MixedData.row1111 := by decide +kernel

theorem sourceRowsAt1112 : MixedData.sourceRows (1112 : Fin 2425) =
    MixedData.row1112 := by decide +kernel

theorem sourceRowsAt1113 : MixedData.sourceRows (1113 : Fin 2425) =
    MixedData.row1113 := by decide +kernel

theorem sourceRowsAt1114 : MixedData.sourceRows (1114 : Fin 2425) =
    MixedData.row1114 := by decide +kernel

theorem sourceRowsAt1115 : MixedData.sourceRows (1115 : Fin 2425) =
    MixedData.row1115 := by decide +kernel

theorem sourceRowsAt1116 : MixedData.sourceRows (1116 : Fin 2425) =
    MixedData.row1116 := by decide +kernel

theorem sourceRowsAt1117 : MixedData.sourceRows (1117 : Fin 2425) =
    MixedData.row1117 := by decide +kernel

theorem sourceRowsAt1118 : MixedData.sourceRows (1118 : Fin 2425) =
    MixedData.row1118 := by decide +kernel

theorem sourceRowsAt1119 : MixedData.sourceRows (1119 : Fin 2425) =
    MixedData.row1119 := by decide +kernel

theorem chunkSound69 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 69) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1104 ∨ k.val = 1105 ∨ k.val = 1106 ∨ k.val = 1107 ∨ k.val = 1108 ∨ k.val = 1109 ∨ k.val = 1110 ∨ k.val = 1111 ∨ k.val = 1112 ∨ k.val = 1113 ∨ k.val = 1114 ∨ k.val = 1115 ∨ k.val = 1116 ∨ k.val = 1117 ∨ k.val = 1118 ∨ k.val = 1119 := by omega
  rcases heq with h1104 | h1105 | h1106 | h1107 | h1108 | h1109 | h1110 | h1111 | h1112 | h1113 | h1114 | h1115 | h1116 | h1117 | h1118 | h1119
  · have he : k = (1104 : Fin 2425) := Fin.ext h1104
    subst k
    rw [sourceRowsAt1104]
    exact rowSound1104 B hB hF
  · have he : k = (1105 : Fin 2425) := Fin.ext h1105
    subst k
    rw [sourceRowsAt1105]
    exact rowSound1105 B hB hF
  · have he : k = (1106 : Fin 2425) := Fin.ext h1106
    subst k
    rw [sourceRowsAt1106]
    exact rowSound1106 B hB hF
  · have he : k = (1107 : Fin 2425) := Fin.ext h1107
    subst k
    rw [sourceRowsAt1107]
    exact rowSound1107 B hB hF
  · have he : k = (1108 : Fin 2425) := Fin.ext h1108
    subst k
    rw [sourceRowsAt1108]
    exact rowSound1108 B hB hF
  · have he : k = (1109 : Fin 2425) := Fin.ext h1109
    subst k
    rw [sourceRowsAt1109]
    exact rowSound1109 B hB hF
  · have he : k = (1110 : Fin 2425) := Fin.ext h1110
    subst k
    rw [sourceRowsAt1110]
    exact rowSound1110 B hB hF
  · have he : k = (1111 : Fin 2425) := Fin.ext h1111
    subst k
    rw [sourceRowsAt1111]
    exact rowSound1111 B hB hF
  · have he : k = (1112 : Fin 2425) := Fin.ext h1112
    subst k
    rw [sourceRowsAt1112]
    exact rowSound1112 B hB hF
  · have he : k = (1113 : Fin 2425) := Fin.ext h1113
    subst k
    rw [sourceRowsAt1113]
    exact rowSound1113 B hB hF
  · have he : k = (1114 : Fin 2425) := Fin.ext h1114
    subst k
    rw [sourceRowsAt1114]
    exact rowSound1114 B hB hF
  · have he : k = (1115 : Fin 2425) := Fin.ext h1115
    subst k
    rw [sourceRowsAt1115]
    exact rowSound1115 B hB hF
  · have he : k = (1116 : Fin 2425) := Fin.ext h1116
    subst k
    rw [sourceRowsAt1116]
    exact rowSound1116 B hB hF
  · have he : k = (1117 : Fin 2425) := Fin.ext h1117
    subst k
    rw [sourceRowsAt1117]
    exact rowSound1117 B hB hF
  · have he : k = (1118 : Fin 2425) := Fin.ext h1118
    subst k
    rw [sourceRowsAt1118]
    exact rowSound1118 B hB hF
  · have he : k = (1119 : Fin 2425) := Fin.ext h1119
    subst k
    rw [sourceRowsAt1119]
    exact rowSound1119 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
