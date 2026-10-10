import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources44

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1200 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1200 (mixedVector B) = 0 := by
  have h602 : mixedVector B (Sum.inr 602) = Sparse.eval nodeValue602 (mixedVector B) := by
    change mixedMoment B node602 node602Labels = _
    exact sound602 B hB hF
  have h921 : mixedVector B (Sum.inr 921) = Sparse.eval nodeValue921 (mixedVector B) := by
    change mixedMoment B node921 node921Labels = _
    exact sound921 B hB hF
  have h1080 : mixedVector B (Sum.inr 1080) = Sparse.eval nodeValue1080 (mixedVector B) := by
    change mixedMoment B node1080 node1080Labels = _
    exact sound1080 B hB hF
  have h1085 : mixedVector B (Sum.inr 1085) = Sparse.eval nodeValue1085 (mixedVector B) := by
    change mixedMoment B node1085 node1085Labels = _
    exact sound1085 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm1390, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h602, h921, h1080, h1085, h4085, reducedSource1200] using sourceEq1390 B hB

theorem rowSound1200 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1200 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1200, numericCheck1200, reducedZero1200 B hB hF, mul_zero]

theorem reducedZero1201 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1201 (mixedVector B) = 0 := by
  have h1010 : mixedVector B (Sum.inr 1010) = Sparse.eval nodeValue1010 (mixedVector B) := by
    change mixedMoment B node1010 node1010Labels = _
    exact sound1010 B hB hF
  have h1951 : mixedVector B (Sum.inr 1951) = Sparse.eval nodeValue1951 (mixedVector B) := by
    change mixedMoment B node1951 node1951Labels = _
    exact sound1951 B hB hF
  have h2004 : mixedVector B (Sum.inr 2004) = Sparse.eval nodeValue2004 (mixedVector B) := by
    change mixedMoment B node2004 node2004Labels = _
    exact sound2004 B hB hF
  have h2222 : mixedVector B (Sum.inr 2222) = Sparse.eval nodeValue2222 (mixedVector B) := by
    change mixedMoment B node2222 node2222Labels = _
    exact sound2222 B hB hF
  have h2230 : mixedVector B (Sum.inr 2230) = Sparse.eval nodeValue2230 (mixedVector B) := by
    change mixedMoment B node2230 node2230Labels = _
    exact sound2230 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1391, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1010, h1951, h2004, h2222, h2230, h4081, reducedSource1201] using sourceEq1391 B hB

theorem rowSound1201 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1201 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1201, numericCheck1201, reducedZero1201 B hB hF, mul_zero]

theorem reducedZero1202 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1202 (mixedVector B) = 0 := by
  have h1001 : mixedVector B (Sum.inr 1001) = Sparse.eval nodeValue1001 (mixedVector B) := by
    change mixedMoment B node1001 node1001Labels = _
    exact sound1001 B hB hF
  have h1010 : mixedVector B (Sum.inr 1010) = Sparse.eval nodeValue1010 (mixedVector B) := by
    change mixedMoment B node1010 node1010Labels = _
    exact sound1010 B hB hF
  have h1012 : mixedVector B (Sum.inr 1012) = Sparse.eval nodeValue1012 (mixedVector B) := by
    change mixedMoment B node1012 node1012Labels = _
    exact sound1012 B hB hF
  have h1076 : mixedVector B (Sum.inr 1076) = Sparse.eval nodeValue1076 (mixedVector B) := by
    change mixedMoment B node1076 node1076Labels = _
    exact sound1076 B hB hF
  have h2230 : mixedVector B (Sum.inr 2230) = Sparse.eval nodeValue2230 (mixedVector B) := by
    change mixedMoment B node2230 node2230Labels = _
    exact sound2230 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1392, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1001, h1010, h1012, h1076, h2230, h4081, reducedSource1202] using sourceEq1392 B hB

theorem rowSound1202 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1202 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1202, numericCheck1202, reducedZero1202 B hB hF, mul_zero]

theorem reducedZero1203 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1203 (mixedVector B) = 0 := by
  have h1009 : mixedVector B (Sum.inr 1009) = Sparse.eval nodeValue1009 (mixedVector B) := by
    change mixedMoment B node1009 node1009Labels = _
    exact sound1009 B hB hF
  have h1950 : mixedVector B (Sum.inr 1950) = Sparse.eval nodeValue1950 (mixedVector B) := by
    change mixedMoment B node1950 node1950Labels = _
    exact sound1950 B hB hF
  have h2003 : mixedVector B (Sum.inr 2003) = Sparse.eval nodeValue2003 (mixedVector B) := by
    change mixedMoment B node2003 node2003Labels = _
    exact sound2003 B hB hF
  have h2218 : mixedVector B (Sum.inr 2218) = Sparse.eval nodeValue2218 (mixedVector B) := by
    change mixedMoment B node2218 node2218Labels = _
    exact sound2218 B hB hF
  have h2229 : mixedVector B (Sum.inr 2229) = Sparse.eval nodeValue2229 (mixedVector B) := by
    change mixedMoment B node2229 node2229Labels = _
    exact sound2229 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1393, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1009, h1950, h2003, h2218, h2229, h4082, reducedSource1203] using sourceEq1393 B hB

theorem rowSound1203 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1203 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1203, numericCheck1203, reducedZero1203 B hB hF, mul_zero]

theorem reducedZero1204 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1204 (mixedVector B) = 0 := by
  have h1000 : mixedVector B (Sum.inr 1000) = Sparse.eval nodeValue1000 (mixedVector B) := by
    change mixedMoment B node1000 node1000Labels = _
    exact sound1000 B hB hF
  have h1009 : mixedVector B (Sum.inr 1009) = Sparse.eval nodeValue1009 (mixedVector B) := by
    change mixedMoment B node1009 node1009Labels = _
    exact sound1009 B hB hF
  have h1013 : mixedVector B (Sum.inr 1013) = Sparse.eval nodeValue1013 (mixedVector B) := by
    change mixedMoment B node1013 node1013Labels = _
    exact sound1013 B hB hF
  have h1075 : mixedVector B (Sum.inr 1075) = Sparse.eval nodeValue1075 (mixedVector B) := by
    change mixedMoment B node1075 node1075Labels = _
    exact sound1075 B hB hF
  have h2229 : mixedVector B (Sum.inr 2229) = Sparse.eval nodeValue2229 (mixedVector B) := by
    change mixedMoment B node2229 node2229Labels = _
    exact sound2229 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1396, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1000, h1009, h1013, h1075, h2229, h4082, reducedSource1204] using sourceEq1396 B hB

theorem rowSound1204 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1204 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1204, numericCheck1204, reducedZero1204 B hB hF, mul_zero]

theorem reducedZero1205 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1205 (mixedVector B) = 0 := by
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  have h4140 : mixedVector B (Sum.inr 4140) = Sparse.eval nodeValue4140 (mixedVector B) := by
    change mixedMoment B node4140 node4140Labels = _
    exact sound4140 B hB hF
  have h4146 : mixedVector B (Sum.inr 4146) = Sparse.eval nodeValue4146 (mixedVector B) := by
    change mixedMoment B node4146 node4146Labels = _
    exact sound4146 B hB hF
  have h4147 : mixedVector B (Sum.inr 4147) = Sparse.eval nodeValue4147 (mixedVector B) := by
    change mixedMoment B node4147 node4147Labels = _
    exact sound4147 B hB hF
  have h4166 : mixedVector B (Sum.inr 4166) = Sparse.eval nodeValue4166 (mixedVector B) := by
    change mixedMoment B node4166 node4166Labels = _
    exact sound4166 B hB hF
  have h4289 : mixedVector B (Sum.inr 4289) = Sparse.eval nodeValue4289 (mixedVector B) := by
    change mixedMoment B node4289 node4289Labels = _
    exact sound4289 B hB hF
  have h4302 : mixedVector B (Sum.inr 4302) = Sparse.eval nodeValue4302 (mixedVector B) := by
    change mixedMoment B node4302 node4302Labels = _
    exact sound4302 B hB hF
  have h4312 : mixedVector B (Sum.inr 4312) = Sparse.eval nodeValue4312 (mixedVector B) := by
    change mixedMoment B node4312 node4312Labels = _
    exact sound4312 B hB hF
  have h4317 : mixedVector B (Sum.inr 4317) = Sparse.eval nodeValue4317 (mixedVector B) := by
    change mixedMoment B node4317 node4317Labels = _
    exact sound4317 B hB hF
  have h4320 : mixedVector B (Sum.inr 4320) = Sparse.eval nodeValue4320 (mixedVector B) := by
    change mixedMoment B node4320 node4320Labels = _
    exact sound4320 B hB hF
  have h4324 : mixedVector B (Sum.inr 4324) = Sparse.eval nodeValue4324 (mixedVector B) := by
    change mixedMoment B node4324 node4324Labels = _
    exact sound4324 B hB hF
  have h4338 : mixedVector B (Sum.inr 4338) = Sparse.eval nodeValue4338 (mixedVector B) := by
    change mixedMoment B node4338 node4338Labels = _
    exact sound4338 B hB hF
  have h4398 : mixedVector B (Sum.inr 4398) = Sparse.eval nodeValue4398 (mixedVector B) := by
    change mixedMoment B node4398 node4398Labels = _
    exact sound4398 B hB hF
  have h4405 : mixedVector B (Sum.inr 4405) = Sparse.eval nodeValue4405 (mixedVector B) := by
    change mixedMoment B node4405 node4405Labels = _
    exact sound4405 B hB hF
  have h4418 : mixedVector B (Sum.inr 4418) = Sparse.eval nodeValue4418 (mixedVector B) := by
    change mixedMoment B node4418 node4418Labels = _
    exact sound4418 B hB hF
  have h4431 : mixedVector B (Sum.inr 4431) = Sparse.eval nodeValue4431 (mixedVector B) := by
    change mixedMoment B node4431 node4431Labels = _
    exact sound4431 B hB hF
  have h4454 : mixedVector B (Sum.inr 4454) = Sparse.eval nodeValue4454 (mixedVector B) := by
    change mixedMoment B node4454 node4454Labels = _
    exact sound4454 B hB hF
  have h4490 : mixedVector B (Sum.inr 4490) = Sparse.eval nodeValue4490 (mixedVector B) := by
    change mixedMoment B node4490 node4490Labels = _
    exact sound4490 B hB hF
  have h4738 : mixedVector B (Sum.inr 4738) = Sparse.eval nodeValue4738 (mixedVector B) := by
    change mixedMoment B node4738 node4738Labels = _
    exact sound4738 B hB hF
  have h4837 : mixedVector B (Sum.inr 4837) = Sparse.eval nodeValue4837 (mixedVector B) := by
    change mixedMoment B node4837 node4837Labels = _
    exact sound4837 B hB hF
  have h4841 : mixedVector B (Sum.inr 4841) = Sparse.eval nodeValue4841 (mixedVector B) := by
    change mixedMoment B node4841 node4841Labels = _
    exact sound4841 B hB hF
  simpa only [sourceForm1399, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4081, h4140, h4146, h4147, h4166, h4289, h4302, h4312, h4317, h4320, h4324, h4338, h4398, h4405, h4418, h4431, h4454, h4490, h4738, h4837, h4841, reducedSource1205] using sourceEq1399 B hB

theorem rowSound1205 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1205 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1205, numericCheck1205, reducedZero1205 B hB hF, mul_zero]

theorem reducedZero1206 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1206 (mixedVector B) = 0 := by
  have h1489 : mixedVector B (Sum.inr 1489) = Sparse.eval nodeValue1489 (mixedVector B) := by
    change mixedMoment B node1489 node1489Labels = _
    exact sound1489 B hB hF
  have h1494 : mixedVector B (Sum.inr 1494) = Sparse.eval nodeValue1494 (mixedVector B) := by
    change mixedMoment B node1494 node1494Labels = _
    exact sound1494 B hB hF
  have h1495 : mixedVector B (Sum.inr 1495) = Sparse.eval nodeValue1495 (mixedVector B) := by
    change mixedMoment B node1495 node1495Labels = _
    exact sound1495 B hB hF
  have h1499 : mixedVector B (Sum.inr 1499) = Sparse.eval nodeValue1499 (mixedVector B) := by
    change mixedMoment B node1499 node1499Labels = _
    exact sound1499 B hB hF
  have h1555 : mixedVector B (Sum.inr 1555) = Sparse.eval nodeValue1555 (mixedVector B) := by
    change mixedMoment B node1555 node1555Labels = _
    exact sound1555 B hB hF
  have h1557 : mixedVector B (Sum.inr 1557) = Sparse.eval nodeValue1557 (mixedVector B) := by
    change mixedMoment B node1557 node1557Labels = _
    exact sound1557 B hB hF
  have h1574 : mixedVector B (Sum.inr 1574) = Sparse.eval nodeValue1574 (mixedVector B) := by
    change mixedMoment B node1574 node1574Labels = _
    exact sound1574 B hB hF
  have h1576 : mixedVector B (Sum.inr 1576) = Sparse.eval nodeValue1576 (mixedVector B) := by
    change mixedMoment B node1576 node1576Labels = _
    exact sound1576 B hB hF
  have h1586 : mixedVector B (Sum.inr 1586) = Sparse.eval nodeValue1586 (mixedVector B) := by
    change mixedMoment B node1586 node1586Labels = _
    exact sound1586 B hB hF
  have h1590 : mixedVector B (Sum.inr 1590) = Sparse.eval nodeValue1590 (mixedVector B) := by
    change mixedMoment B node1590 node1590Labels = _
    exact sound1590 B hB hF
  have h1599 : mixedVector B (Sum.inr 1599) = Sparse.eval nodeValue1599 (mixedVector B) := by
    change mixedMoment B node1599 node1599Labels = _
    exact sound1599 B hB hF
  have h1602 : mixedVector B (Sum.inr 1602) = Sparse.eval nodeValue1602 (mixedVector B) := by
    change mixedMoment B node1602 node1602Labels = _
    exact sound1602 B hB hF
  have h1620 : mixedVector B (Sum.inr 1620) = Sparse.eval nodeValue1620 (mixedVector B) := by
    change mixedMoment B node1620 node1620Labels = _
    exact sound1620 B hB hF
  have h1627 : mixedVector B (Sum.inr 1627) = Sparse.eval nodeValue1627 (mixedVector B) := by
    change mixedMoment B node1627 node1627Labels = _
    exact sound1627 B hB hF
  have h1633 : mixedVector B (Sum.inr 1633) = Sparse.eval nodeValue1633 (mixedVector B) := by
    change mixedMoment B node1633 node1633Labels = _
    exact sound1633 B hB hF
  have h1647 : mixedVector B (Sum.inr 1647) = Sparse.eval nodeValue1647 (mixedVector B) := by
    change mixedMoment B node1647 node1647Labels = _
    exact sound1647 B hB hF
  have h1650 : mixedVector B (Sum.inr 1650) = Sparse.eval nodeValue1650 (mixedVector B) := by
    change mixedMoment B node1650 node1650Labels = _
    exact sound1650 B hB hF
  have h1911 : mixedVector B (Sum.inr 1911) = Sparse.eval nodeValue1911 (mixedVector B) := by
    change mixedMoment B node1911 node1911Labels = _
    exact sound1911 B hB hF
  have h2056 : mixedVector B (Sum.inr 2056) = Sparse.eval nodeValue2056 (mixedVector B) := by
    change mixedMoment B node2056 node2056Labels = _
    exact sound2056 B hB hF
  have h2060 : mixedVector B (Sum.inr 2060) = Sparse.eval nodeValue2060 (mixedVector B) := by
    change mixedMoment B node2060 node2060Labels = _
    exact sound2060 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1400, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1489, h1494, h1495, h1499, h1555, h1557, h1574, h1576, h1586, h1590, h1599, h1602, h1620, h1627, h1633, h1647, h1650, h1911, h2056, h2060, h4081, reducedSource1206] using sourceEq1400 B hB

theorem rowSound1206 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1206 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1206, numericCheck1206, reducedZero1206 B hB hF, mul_zero]

theorem reducedZero1207 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1207 (mixedVector B) = 0 := by
  have h867 : mixedVector B (Sum.inr 867) = Sparse.eval nodeValue867 (mixedVector B) := by
    change mixedMoment B node867 node867Labels = _
    exact sound867 B hB hF
  have h898 : mixedVector B (Sum.inr 898) = Sparse.eval nodeValue898 (mixedVector B) := by
    change mixedMoment B node898 node898Labels = _
    exact sound898 B hB hF
  have h902 : mixedVector B (Sum.inr 902) = Sparse.eval nodeValue902 (mixedVector B) := by
    change mixedMoment B node902 node902Labels = _
    exact sound902 B hB hF
  have h916 : mixedVector B (Sum.inr 916) = Sparse.eval nodeValue916 (mixedVector B) := by
    change mixedMoment B node916 node916Labels = _
    exact sound916 B hB hF
  have h1007 : mixedVector B (Sum.inr 1007) = Sparse.eval nodeValue1007 (mixedVector B) := by
    change mixedMoment B node1007 node1007Labels = _
    exact sound1007 B hB hF
  have h1911 : mixedVector B (Sum.inr 1911) = Sparse.eval nodeValue1911 (mixedVector B) := by
    change mixedMoment B node1911 node1911Labels = _
    exact sound1911 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1401, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h867, h898, h902, h916, h1007, h1911, h4081, reducedSource1207] using sourceEq1401 B hB

theorem rowSound1207 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1207 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1207, numericCheck1207, reducedZero1207 B hB hF, mul_zero]

theorem reducedZero1208 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1208 (mixedVector B) = 0 := by
  have h793 : mixedVector B (Sum.inr 793) = Sparse.eval nodeValue793 (mixedVector B) := by
    change mixedMoment B node793 node793Labels = _
    exact sound793 B hB hF
  have h795 : mixedVector B (Sum.inr 795) = Sparse.eval nodeValue795 (mixedVector B) := by
    change mixedMoment B node795 node795Labels = _
    exact sound795 B hB hF
  have h796 : mixedVector B (Sum.inr 796) = Sparse.eval nodeValue796 (mixedVector B) := by
    change mixedMoment B node796 node796Labels = _
    exact sound796 B hB hF
  have h811 : mixedVector B (Sum.inr 811) = Sparse.eval nodeValue811 (mixedVector B) := by
    change mixedMoment B node811 node811Labels = _
    exact sound811 B hB hF
  have h827 : mixedVector B (Sum.inr 827) = Sparse.eval nodeValue827 (mixedVector B) := by
    change mixedMoment B node827 node827Labels = _
    exact sound827 B hB hF
  have h1715 : mixedVector B (Sum.inr 1715) = Sparse.eval nodeValue1715 (mixedVector B) := by
    change mixedMoment B node1715 node1715Labels = _
    exact sound1715 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1403, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h793, h795, h796, h811, h827, h1715, h4069, reducedSource1208] using sourceEq1403 B hB

theorem rowSound1208 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1208 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1208, numericCheck1208, reducedZero1208 B hB hF, mul_zero]

theorem reducedZero1209 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1209 (mixedVector B) = 0 := by
  have h825 : mixedVector B (Sum.inr 825) = Sparse.eval nodeValue825 (mixedVector B) := by
    change mixedMoment B node825 node825Labels = _
    exact sound825 B hB hF
  have h829 : mixedVector B (Sum.inr 829) = Sparse.eval nodeValue829 (mixedVector B) := by
    change mixedMoment B node829 node829Labels = _
    exact sound829 B hB hF
  have h830 : mixedVector B (Sum.inr 830) = Sparse.eval nodeValue830 (mixedVector B) := by
    change mixedMoment B node830 node830Labels = _
    exact sound830 B hB hF
  have h858 : mixedVector B (Sum.inr 858) = Sparse.eval nodeValue858 (mixedVector B) := by
    change mixedMoment B node858 node858Labels = _
    exact sound858 B hB hF
  have h1740 : mixedVector B (Sum.inr 1740) = Sparse.eval nodeValue1740 (mixedVector B) := by
    change mixedMoment B node1740 node1740Labels = _
    exact sound1740 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1405, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h825, h829, h830, h858, h1740, h4071, reducedSource1209] using sourceEq1405 B hB

theorem rowSound1209 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1209 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1209, numericCheck1209, reducedZero1209 B hB hF, mul_zero]

theorem reducedZero1210 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1210 (mixedVector B) = 0 := by
  have h828 : mixedVector B (Sum.inr 828) = Sparse.eval nodeValue828 (mixedVector B) := by
    change mixedMoment B node828 node828Labels = _
    exact sound828 B hB hF
  have h1610 : mixedVector B (Sum.inr 1610) = Sparse.eval nodeValue1610 (mixedVector B) := by
    change mixedMoment B node1610 node1610Labels = _
    exact sound1610 B hB hF
  have h1659 : mixedVector B (Sum.inr 1659) = Sparse.eval nodeValue1659 (mixedVector B) := by
    change mixedMoment B node1659 node1659Labels = _
    exact sound1659 B hB hF
  have h1716 : mixedVector B (Sum.inr 1716) = Sparse.eval nodeValue1716 (mixedVector B) := by
    change mixedMoment B node1716 node1716Labels = _
    exact sound1716 B hB hF
  have h1739 : mixedVector B (Sum.inr 1739) = Sparse.eval nodeValue1739 (mixedVector B) := by
    change mixedMoment B node1739 node1739Labels = _
    exact sound1739 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1406, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h828, h1610, h1659, h1716, h1739, h4069, reducedSource1210] using sourceEq1406 B hB

theorem rowSound1210 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1210 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1210, numericCheck1210, reducedZero1210 B hB hF, mul_zero]

theorem reducedZero1211 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1211 (mixedVector B) = 0 := by
  have h824 : mixedVector B (Sum.inr 824) = Sparse.eval nodeValue824 (mixedVector B) := by
    change mixedMoment B node824 node824Labels = _
    exact sound824 B hB hF
  have h828 : mixedVector B (Sum.inr 828) = Sparse.eval nodeValue828 (mixedVector B) := by
    change mixedMoment B node828 node828Labels = _
    exact sound828 B hB hF
  have h831 : mixedVector B (Sum.inr 831) = Sparse.eval nodeValue831 (mixedVector B) := by
    change mixedMoment B node831 node831Labels = _
    exact sound831 B hB hF
  have h856 : mixedVector B (Sum.inr 856) = Sparse.eval nodeValue856 (mixedVector B) := by
    change mixedMoment B node856 node856Labels = _
    exact sound856 B hB hF
  have h1739 : mixedVector B (Sum.inr 1739) = Sparse.eval nodeValue1739 (mixedVector B) := by
    change mixedMoment B node1739 node1739Labels = _
    exact sound1739 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1408, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h824, h828, h831, h856, h1739, h4069, reducedSource1211] using sourceEq1408 B hB

theorem rowSound1211 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1211 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1211, numericCheck1211, reducedZero1211 B hB hF, mul_zero]

theorem reducedZero1212 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1212 (mixedVector B) = 0 := by
  have h826 : mixedVector B (Sum.inr 826) = Sparse.eval nodeValue826 (mixedVector B) := by
    change mixedMoment B node826 node826Labels = _
    exact sound826 B hB hF
  have h1608 : mixedVector B (Sum.inr 1608) = Sparse.eval nodeValue1608 (mixedVector B) := by
    change mixedMoment B node1608 node1608Labels = _
    exact sound1608 B hB hF
  have h1657 : mixedVector B (Sum.inr 1657) = Sparse.eval nodeValue1657 (mixedVector B) := by
    change mixedMoment B node1657 node1657Labels = _
    exact sound1657 B hB hF
  have h1738 : mixedVector B (Sum.inr 1738) = Sparse.eval nodeValue1738 (mixedVector B) := by
    change mixedMoment B node1738 node1738Labels = _
    exact sound1738 B hB hF
  have h1741 : mixedVector B (Sum.inr 1741) = Sparse.eval nodeValue1741 (mixedVector B) := by
    change mixedMoment B node1741 node1741Labels = _
    exact sound1741 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1410, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h826, h1608, h1657, h1738, h1741, h4071, reducedSource1212] using sourceEq1410 B hB

theorem rowSound1212 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1212 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1212, numericCheck1212, reducedZero1212 B hB hF, mul_zero]

theorem reducedZero1213 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1213 (mixedVector B) = 0 := by
  have h555 : mixedVector B (Sum.inr 555) = Sparse.eval nodeValue555 (mixedVector B) := by
    change mixedMoment B node555 node555Labels = _
    exact sound555 B hB hF
  have h715 : mixedVector B (Sum.inr 715) = Sparse.eval nodeValue715 (mixedVector B) := by
    change mixedMoment B node715 node715Labels = _
    exact sound715 B hB hF
  have h826 : mixedVector B (Sum.inr 826) = Sparse.eval nodeValue826 (mixedVector B) := by
    change mixedMoment B node826 node826Labels = _
    exact sound826 B hB hF
  have h852 : mixedVector B (Sum.inr 852) = Sparse.eval nodeValue852 (mixedVector B) := by
    change mixedMoment B node852 node852Labels = _
    exact sound852 B hB hF
  have h859 : mixedVector B (Sum.inr 859) = Sparse.eval nodeValue859 (mixedVector B) := by
    change mixedMoment B node859 node859Labels = _
    exact sound859 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1411, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h555, h715, h826, h852, h859, h4071, reducedSource1213] using sourceEq1411 B hB

theorem rowSound1213 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1213 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1213, numericCheck1213, reducedZero1213 B hB hF, mul_zero]

theorem reducedZero1214 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1214 (mixedVector B) = 0 := by
  have h823 : mixedVector B (Sum.inr 823) = Sparse.eval nodeValue823 (mixedVector B) := by
    change mixedMoment B node823 node823Labels = _
    exact sound823 B hB hF
  have h826 : mixedVector B (Sum.inr 826) = Sparse.eval nodeValue826 (mixedVector B) := by
    change mixedMoment B node826 node826Labels = _
    exact sound826 B hB hF
  have h830 : mixedVector B (Sum.inr 830) = Sparse.eval nodeValue830 (mixedVector B) := by
    change mixedMoment B node830 node830Labels = _
    exact sound830 B hB hF
  have h852 : mixedVector B (Sum.inr 852) = Sparse.eval nodeValue852 (mixedVector B) := by
    change mixedMoment B node852 node852Labels = _
    exact sound852 B hB hF
  have h1738 : mixedVector B (Sum.inr 1738) = Sparse.eval nodeValue1738 (mixedVector B) := by
    change mixedMoment B node1738 node1738Labels = _
    exact sound1738 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1412, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h823, h826, h830, h852, h1738, h4071, reducedSource1214] using sourceEq1412 B hB

theorem rowSound1214 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1214 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1214, numericCheck1214, reducedZero1214 B hB hF, mul_zero]

theorem reducedZero1215 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1215 (mixedVector B) = 0 := by
  have h546 : mixedVector B (Sum.inr 546) = Sparse.eval nodeValue546 (mixedVector B) := by
    change mixedMoment B node546 node546Labels = _
    exact sound546 B hB hF
  have h706 : mixedVector B (Sum.inr 706) = Sparse.eval nodeValue706 (mixedVector B) := by
    change mixedMoment B node706 node706Labels = _
    exact sound706 B hB hF
  have h741 : mixedVector B (Sum.inr 741) = Sparse.eval nodeValue741 (mixedVector B) := by
    change mixedMoment B node741 node741Labels = _
    exact sound741 B hB hF
  have h809 : mixedVector B (Sum.inr 809) = Sparse.eval nodeValue809 (mixedVector B) := by
    change mixedMoment B node809 node809Labels = _
    exact sound809 B hB hF
  have h815 : mixedVector B (Sum.inr 815) = Sparse.eval nodeValue815 (mixedVector B) := by
    change mixedMoment B node815 node815Labels = _
    exact sound815 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1413, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h546, h706, h741, h809, h815, h4070, reducedSource1215] using sourceEq1413 B hB

theorem rowSound1215 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1215 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1215, numericCheck1215, reducedZero1215 B hB hF, mul_zero]

theorem sourceRowsAt1200 : MixedData.sourceRows (1200 : Fin 2425) =
    MixedData.row1200 := by decide +kernel

theorem sourceRowsAt1201 : MixedData.sourceRows (1201 : Fin 2425) =
    MixedData.row1201 := by decide +kernel

theorem sourceRowsAt1202 : MixedData.sourceRows (1202 : Fin 2425) =
    MixedData.row1202 := by decide +kernel

theorem sourceRowsAt1203 : MixedData.sourceRows (1203 : Fin 2425) =
    MixedData.row1203 := by decide +kernel

theorem sourceRowsAt1204 : MixedData.sourceRows (1204 : Fin 2425) =
    MixedData.row1204 := by decide +kernel

theorem sourceRowsAt1205 : MixedData.sourceRows (1205 : Fin 2425) =
    MixedData.row1205 := by decide +kernel

theorem sourceRowsAt1206 : MixedData.sourceRows (1206 : Fin 2425) =
    MixedData.row1206 := by decide +kernel

theorem sourceRowsAt1207 : MixedData.sourceRows (1207 : Fin 2425) =
    MixedData.row1207 := by decide +kernel

theorem sourceRowsAt1208 : MixedData.sourceRows (1208 : Fin 2425) =
    MixedData.row1208 := by decide +kernel

theorem sourceRowsAt1209 : MixedData.sourceRows (1209 : Fin 2425) =
    MixedData.row1209 := by decide +kernel

theorem sourceRowsAt1210 : MixedData.sourceRows (1210 : Fin 2425) =
    MixedData.row1210 := by decide +kernel

theorem sourceRowsAt1211 : MixedData.sourceRows (1211 : Fin 2425) =
    MixedData.row1211 := by decide +kernel

theorem sourceRowsAt1212 : MixedData.sourceRows (1212 : Fin 2425) =
    MixedData.row1212 := by decide +kernel

theorem sourceRowsAt1213 : MixedData.sourceRows (1213 : Fin 2425) =
    MixedData.row1213 := by decide +kernel

theorem sourceRowsAt1214 : MixedData.sourceRows (1214 : Fin 2425) =
    MixedData.row1214 := by decide +kernel

theorem sourceRowsAt1215 : MixedData.sourceRows (1215 : Fin 2425) =
    MixedData.row1215 := by decide +kernel

theorem chunkSound75 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 75) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1200 ∨ k.val = 1201 ∨ k.val = 1202 ∨ k.val = 1203 ∨ k.val = 1204 ∨ k.val = 1205 ∨ k.val = 1206 ∨ k.val = 1207 ∨ k.val = 1208 ∨ k.val = 1209 ∨ k.val = 1210 ∨ k.val = 1211 ∨ k.val = 1212 ∨ k.val = 1213 ∨ k.val = 1214 ∨ k.val = 1215 := by omega
  rcases heq with h1200 | h1201 | h1202 | h1203 | h1204 | h1205 | h1206 | h1207 | h1208 | h1209 | h1210 | h1211 | h1212 | h1213 | h1214 | h1215
  · have he : k = (1200 : Fin 2425) := Fin.ext h1200
    subst k
    rw [sourceRowsAt1200]
    exact rowSound1200 B hB hF
  · have he : k = (1201 : Fin 2425) := Fin.ext h1201
    subst k
    rw [sourceRowsAt1201]
    exact rowSound1201 B hB hF
  · have he : k = (1202 : Fin 2425) := Fin.ext h1202
    subst k
    rw [sourceRowsAt1202]
    exact rowSound1202 B hB hF
  · have he : k = (1203 : Fin 2425) := Fin.ext h1203
    subst k
    rw [sourceRowsAt1203]
    exact rowSound1203 B hB hF
  · have he : k = (1204 : Fin 2425) := Fin.ext h1204
    subst k
    rw [sourceRowsAt1204]
    exact rowSound1204 B hB hF
  · have he : k = (1205 : Fin 2425) := Fin.ext h1205
    subst k
    rw [sourceRowsAt1205]
    exact rowSound1205 B hB hF
  · have he : k = (1206 : Fin 2425) := Fin.ext h1206
    subst k
    rw [sourceRowsAt1206]
    exact rowSound1206 B hB hF
  · have he : k = (1207 : Fin 2425) := Fin.ext h1207
    subst k
    rw [sourceRowsAt1207]
    exact rowSound1207 B hB hF
  · have he : k = (1208 : Fin 2425) := Fin.ext h1208
    subst k
    rw [sourceRowsAt1208]
    exact rowSound1208 B hB hF
  · have he : k = (1209 : Fin 2425) := Fin.ext h1209
    subst k
    rw [sourceRowsAt1209]
    exact rowSound1209 B hB hF
  · have he : k = (1210 : Fin 2425) := Fin.ext h1210
    subst k
    rw [sourceRowsAt1210]
    exact rowSound1210 B hB hF
  · have he : k = (1211 : Fin 2425) := Fin.ext h1211
    subst k
    rw [sourceRowsAt1211]
    exact rowSound1211 B hB hF
  · have he : k = (1212 : Fin 2425) := Fin.ext h1212
    subst k
    rw [sourceRowsAt1212]
    exact rowSound1212 B hB hF
  · have he : k = (1213 : Fin 2425) := Fin.ext h1213
    subst k
    rw [sourceRowsAt1213]
    exact rowSound1213 B hB hF
  · have he : k = (1214 : Fin 2425) := Fin.ext h1214
    subst k
    rw [sourceRowsAt1214]
    exact rowSound1214 B hB hF
  · have he : k = (1215 : Fin 2425) := Fin.ext h1215
    subst k
    rw [sourceRowsAt1215]
    exact rowSound1215 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
