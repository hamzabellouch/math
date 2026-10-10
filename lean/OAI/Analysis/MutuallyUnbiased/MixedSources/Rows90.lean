import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic90
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources53

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1440 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1440 (mixedVector B) = 0 := by
  have h1148 : mixedVector B (Sum.inr 1148) = Sparse.eval nodeValue1148 (mixedVector B) := by
    change mixedMoment B node1148 node1148Labels = _
    exact sound1148 B hB hF
  have h1149 : mixedVector B (Sum.inr 1149) = Sparse.eval nodeValue1149 (mixedVector B) := by
    change mixedMoment B node1149 node1149Labels = _
    exact sound1149 B hB hF
  have h1151 : mixedVector B (Sum.inr 1151) = Sparse.eval nodeValue1151 (mixedVector B) := by
    change mixedMoment B node1151 node1151Labels = _
    exact sound1151 B hB hF
  have h1156 : mixedVector B (Sum.inr 1156) = Sparse.eval nodeValue1156 (mixedVector B) := by
    change mixedMoment B node1156 node1156Labels = _
    exact sound1156 B hB hF
  have h1236 : mixedVector B (Sum.inr 1236) = Sparse.eval nodeValue1236 (mixedVector B) := by
    change mixedMoment B node1236 node1236Labels = _
    exact sound1236 B hB hF
  have h2553 : mixedVector B (Sum.inr 2553) = Sparse.eval nodeValue2553 (mixedVector B) := by
    change mixedMoment B node2553 node2553Labels = _
    exact sound2553 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1682, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1148, h1149, h1151, h1156, h1236, h2553, h4092, reducedSource1440] using sourceEq1682 B hB

theorem rowSound1440 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1440 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1440, numericCheck1440, reducedZero1440 B hB hF, mul_zero]

theorem reducedZero1441 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1441 (mixedVector B) = 0 := by
  have h4139 : mixedVector B (Sum.inr 4139) = Sparse.eval nodeValue4139 (mixedVector B) := by
    change mixedMoment B node4139 node4139Labels = _
    exact sound4139 B hB hF
  have h4140 : mixedVector B (Sum.inr 4140) = Sparse.eval nodeValue4140 (mixedVector B) := by
    change mixedMoment B node4140 node4140Labels = _
    exact sound4140 B hB hF
  have h4141 : mixedVector B (Sum.inr 4141) = Sparse.eval nodeValue4141 (mixedVector B) := by
    change mixedMoment B node4141 node4141Labels = _
    exact sound4141 B hB hF
  have h4145 : mixedVector B (Sum.inr 4145) = Sparse.eval nodeValue4145 (mixedVector B) := by
    change mixedMoment B node4145 node4145Labels = _
    exact sound4145 B hB hF
  have h4172 : mixedVector B (Sum.inr 4172) = Sparse.eval nodeValue4172 (mixedVector B) := by
    change mixedMoment B node4172 node4172Labels = _
    exact sound4172 B hB hF
  have h4513 : mixedVector B (Sum.inr 4513) = Sparse.eval nodeValue4513 (mixedVector B) := by
    change mixedMoment B node4513 node4513Labels = _
    exact sound4513 B hB hF
  have h4514 : mixedVector B (Sum.inr 4514) = Sparse.eval nodeValue4514 (mixedVector B) := by
    change mixedMoment B node4514 node4514Labels = _
    exact sound4514 B hB hF
  have h4515 : mixedVector B (Sum.inr 4515) = Sparse.eval nodeValue4515 (mixedVector B) := by
    change mixedMoment B node4515 node4515Labels = _
    exact sound4515 B hB hF
  have h4518 : mixedVector B (Sum.inr 4518) = Sparse.eval nodeValue4518 (mixedVector B) := by
    change mixedMoment B node4518 node4518Labels = _
    exact sound4518 B hB hF
  have h4521 : mixedVector B (Sum.inr 4521) = Sparse.eval nodeValue4521 (mixedVector B) := by
    change mixedMoment B node4521 node4521Labels = _
    exact sound4521 B hB hF
  have h4522 : mixedVector B (Sum.inr 4522) = Sparse.eval nodeValue4522 (mixedVector B) := by
    change mixedMoment B node4522 node4522Labels = _
    exact sound4522 B hB hF
  have h4524 : mixedVector B (Sum.inr 4524) = Sparse.eval nodeValue4524 (mixedVector B) := by
    change mixedMoment B node4524 node4524Labels = _
    exact sound4524 B hB hF
  have h4541 : mixedVector B (Sum.inr 4541) = Sparse.eval nodeValue4541 (mixedVector B) := by
    change mixedMoment B node4541 node4541Labels = _
    exact sound4541 B hB hF
  have h4581 : mixedVector B (Sum.inr 4581) = Sparse.eval nodeValue4581 (mixedVector B) := by
    change mixedMoment B node4581 node4581Labels = _
    exact sound4581 B hB hF
  have h4583 : mixedVector B (Sum.inr 4583) = Sparse.eval nodeValue4583 (mixedVector B) := by
    change mixedMoment B node4583 node4583Labels = _
    exact sound4583 B hB hF
  have h4586 : mixedVector B (Sum.inr 4586) = Sparse.eval nodeValue4586 (mixedVector B) := by
    change mixedMoment B node4586 node4586Labels = _
    exact sound4586 B hB hF
  have h4601 : mixedVector B (Sum.inr 4601) = Sparse.eval nodeValue4601 (mixedVector B) := by
    change mixedMoment B node4601 node4601Labels = _
    exact sound4601 B hB hF
  have h4602 : mixedVector B (Sum.inr 4602) = Sparse.eval nodeValue4602 (mixedVector B) := by
    change mixedMoment B node4602 node4602Labels = _
    exact sound4602 B hB hF
  have h4605 : mixedVector B (Sum.inr 4605) = Sparse.eval nodeValue4605 (mixedVector B) := by
    change mixedMoment B node4605 node4605Labels = _
    exact sound4605 B hB hF
  have h4606 : mixedVector B (Sum.inr 4606) = Sparse.eval nodeValue4606 (mixedVector B) := by
    change mixedMoment B node4606 node4606Labels = _
    exact sound4606 B hB hF
  have h4612 : mixedVector B (Sum.inr 4612) = Sparse.eval nodeValue4612 (mixedVector B) := by
    change mixedMoment B node4612 node4612Labels = _
    exact sound4612 B hB hF
  have h4622 : mixedVector B (Sum.inr 4622) = Sparse.eval nodeValue4622 (mixedVector B) := by
    change mixedMoment B node4622 node4622Labels = _
    exact sound4622 B hB hF
  have h4623 : mixedVector B (Sum.inr 4623) = Sparse.eval nodeValue4623 (mixedVector B) := by
    change mixedMoment B node4623 node4623Labels = _
    exact sound4623 B hB hF
  have h5149 : mixedVector B (Sum.inr 5149) = Sparse.eval nodeValue5149 (mixedVector B) := by
    change mixedMoment B node5149 node5149Labels = _
    exact sound5149 B hB hF
  have h5204 : mixedVector B (Sum.inr 5204) = Sparse.eval nodeValue5204 (mixedVector B) := by
    change mixedMoment B node5204 node5204Labels = _
    exact sound5204 B hB hF
  have h5284 : mixedVector B (Sum.inr 5284) = Sparse.eval nodeValue5284 (mixedVector B) := by
    change mixedMoment B node5284 node5284Labels = _
    exact sound5284 B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292 B hB hF
  have h5294 : mixedVector B (Sum.inr 5294) = Sparse.eval nodeValue5294 (mixedVector B) := by
    change mixedMoment B node5294 node5294Labels = _
    exact sound5294 B hB hF
  simpa only [sourceForm1683, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4139, h4140, h4141, h4145, h4172, h4513, h4514, h4515, h4518, h4521, h4522, h4524, h4541, h4581, h4583, h4586, h4601, h4602, h4605, h4606, h4612, h4622, h4623, h5149, h5204, h5284, h5292, h5294, reducedSource1441] using sourceEq1683 B hB

theorem rowSound1441 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1441 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1441, numericCheck1441, reducedZero1441 B hB hF, mul_zero]

theorem reducedZero1442 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1442 (mixedVector B) = 0 := by
  have h567 : mixedVector B (Sum.inr 567) = Sparse.eval nodeValue567 (mixedVector B) := by
    change mixedMoment B node567 node567Labels = _
    exact sound567 B hB hF
  have h568 : mixedVector B (Sum.inr 568) = Sparse.eval nodeValue568 (mixedVector B) := by
    change mixedMoment B node568 node568Labels = _
    exact sound568 B hB hF
  have h569 : mixedVector B (Sum.inr 569) = Sparse.eval nodeValue569 (mixedVector B) := by
    change mixedMoment B node569 node569Labels = _
    exact sound569 B hB hF
  have h573 : mixedVector B (Sum.inr 573) = Sparse.eval nodeValue573 (mixedVector B) := by
    change mixedMoment B node573 node573Labels = _
    exact sound573 B hB hF
  have h600 : mixedVector B (Sum.inr 600) = Sparse.eval nodeValue600 (mixedVector B) := by
    change mixedMoment B node600 node600Labels = _
    exact sound600 B hB hF
  have h1097 : mixedVector B (Sum.inr 1097) = Sparse.eval nodeValue1097 (mixedVector B) := by
    change mixedMoment B node1097 node1097Labels = _
    exact sound1097 B hB hF
  have h1098 : mixedVector B (Sum.inr 1098) = Sparse.eval nodeValue1098 (mixedVector B) := by
    change mixedMoment B node1098 node1098Labels = _
    exact sound1098 B hB hF
  have h1099 : mixedVector B (Sum.inr 1099) = Sparse.eval nodeValue1099 (mixedVector B) := by
    change mixedMoment B node1099 node1099Labels = _
    exact sound1099 B hB hF
  have h1102 : mixedVector B (Sum.inr 1102) = Sparse.eval nodeValue1102 (mixedVector B) := by
    change mixedMoment B node1102 node1102Labels = _
    exact sound1102 B hB hF
  have h1105 : mixedVector B (Sum.inr 1105) = Sparse.eval nodeValue1105 (mixedVector B) := by
    change mixedMoment B node1105 node1105Labels = _
    exact sound1105 B hB hF
  have h1106 : mixedVector B (Sum.inr 1106) = Sparse.eval nodeValue1106 (mixedVector B) := by
    change mixedMoment B node1106 node1106Labels = _
    exact sound1106 B hB hF
  have h1108 : mixedVector B (Sum.inr 1108) = Sparse.eval nodeValue1108 (mixedVector B) := by
    change mixedMoment B node1108 node1108Labels = _
    exact sound1108 B hB hF
  have h1126 : mixedVector B (Sum.inr 1126) = Sparse.eval nodeValue1126 (mixedVector B) := by
    change mixedMoment B node1126 node1126Labels = _
    exact sound1126 B hB hF
  have h1200 : mixedVector B (Sum.inr 1200) = Sparse.eval nodeValue1200 (mixedVector B) := by
    change mixedMoment B node1200 node1200Labels = _
    exact sound1200 B hB hF
  have h1202 : mixedVector B (Sum.inr 1202) = Sparse.eval nodeValue1202 (mixedVector B) := by
    change mixedMoment B node1202 node1202Labels = _
    exact sound1202 B hB hF
  have h1205 : mixedVector B (Sum.inr 1205) = Sparse.eval nodeValue1205 (mixedVector B) := by
    change mixedMoment B node1205 node1205Labels = _
    exact sound1205 B hB hF
  have h1235 : mixedVector B (Sum.inr 1235) = Sparse.eval nodeValue1235 (mixedVector B) := by
    change mixedMoment B node1235 node1235Labels = _
    exact sound1235 B hB hF
  have h1236 : mixedVector B (Sum.inr 1236) = Sparse.eval nodeValue1236 (mixedVector B) := by
    change mixedMoment B node1236 node1236Labels = _
    exact sound1236 B hB hF
  have h1239 : mixedVector B (Sum.inr 1239) = Sparse.eval nodeValue1239 (mixedVector B) := by
    change mixedMoment B node1239 node1239Labels = _
    exact sound1239 B hB hF
  have h1240 : mixedVector B (Sum.inr 1240) = Sparse.eval nodeValue1240 (mixedVector B) := by
    change mixedMoment B node1240 node1240Labels = _
    exact sound1240 B hB hF
  have h1246 : mixedVector B (Sum.inr 1246) = Sparse.eval nodeValue1246 (mixedVector B) := by
    change mixedMoment B node1246 node1246Labels = _
    exact sound1246 B hB hF
  have h1299 : mixedVector B (Sum.inr 1299) = Sparse.eval nodeValue1299 (mixedVector B) := by
    change mixedMoment B node1299 node1299Labels = _
    exact sound1299 B hB hF
  have h1300 : mixedVector B (Sum.inr 1300) = Sparse.eval nodeValue1300 (mixedVector B) := by
    change mixedMoment B node1300 node1300Labels = _
    exact sound1300 B hB hF
  have h2881 : mixedVector B (Sum.inr 2881) = Sparse.eval nodeValue2881 (mixedVector B) := by
    change mixedMoment B node2881 node2881Labels = _
    exact sound2881 B hB hF
  have h2924 : mixedVector B (Sum.inr 2924) = Sparse.eval nodeValue2924 (mixedVector B) := by
    change mixedMoment B node2924 node2924Labels = _
    exact sound2924 B hB hF
  have h3077 : mixedVector B (Sum.inr 3077) = Sparse.eval nodeValue3077 (mixedVector B) := by
    change mixedMoment B node3077 node3077Labels = _
    exact sound3077 B hB hF
  have h3100 : mixedVector B (Sum.inr 3100) = Sparse.eval nodeValue3100 (mixedVector B) := by
    change mixedMoment B node3100 node3100Labels = _
    exact sound3100 B hB hF
  have h3101 : mixedVector B (Sum.inr 3101) = Sparse.eval nodeValue3101 (mixedVector B) := by
    change mixedMoment B node3101 node3101Labels = _
    exact sound3101 B hB hF
  simpa only [sourceForm1684, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h567, h568, h569, h573, h600, h1097, h1098, h1099, h1102, h1105, h1106, h1108, h1126, h1200, h1202, h1205, h1235, h1236, h1239, h1240, h1246, h1299, h1300, h2881, h2924, h3077, h3100, h3101, reducedSource1442] using sourceEq1684 B hB

theorem rowSound1442 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1442 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1442, numericCheck1442, reducedZero1442 B hB hF, mul_zero]

theorem reducedZero1443 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1443 (mixedVector B) = 0 := by
  have h1229 : mixedVector B (Sum.inr 1229) = Sparse.eval nodeValue1229 (mixedVector B) := by
    change mixedMoment B node1229 node1229Labels = _
    exact sound1229 B hB hF
  have h2504 : mixedVector B (Sum.inr 2504) = Sparse.eval nodeValue2504 (mixedVector B) := by
    change mixedMoment B node2504 node2504Labels = _
    exact sound2504 B hB hF
  have h2550 : mixedVector B (Sum.inr 2550) = Sparse.eval nodeValue2550 (mixedVector B) := by
    change mixedMoment B node2550 node2550Labels = _
    exact sound2550 B hB hF
  have h2704 : mixedVector B (Sum.inr 2704) = Sparse.eval nodeValue2704 (mixedVector B) := by
    change mixedMoment B node2704 node2704Labels = _
    exact sound2704 B hB hF
  have h2719 : mixedVector B (Sum.inr 2719) = Sparse.eval nodeValue2719 (mixedVector B) := by
    change mixedMoment B node2719 node2719Labels = _
    exact sound2719 B hB hF
  have h2735 : mixedVector B (Sum.inr 2735) = Sparse.eval nodeValue2735 (mixedVector B) := by
    change mixedMoment B node2735 node2735Labels = _
    exact sound2735 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1686, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1229, h2504, h2550, h2704, h2719, h2735, h4080, reducedSource1443] using sourceEq1686 B hB

theorem rowSound1443 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1443 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1443, numericCheck1443, reducedZero1443 B hB hF, mul_zero]

theorem reducedZero1444 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1444 (mixedVector B) = 0 := by
  have h1183 : mixedVector B (Sum.inr 1183) = Sparse.eval nodeValue1183 (mixedVector B) := by
    change mixedMoment B node1183 node1183Labels = _
    exact sound1183 B hB hF
  have h1188 : mixedVector B (Sum.inr 1188) = Sparse.eval nodeValue1188 (mixedVector B) := by
    change mixedMoment B node1188 node1188Labels = _
    exact sound1188 B hB hF
  have h1189 : mixedVector B (Sum.inr 1189) = Sparse.eval nodeValue1189 (mixedVector B) := by
    change mixedMoment B node1189 node1189Labels = _
    exact sound1189 B hB hF
  have h1286 : mixedVector B (Sum.inr 1286) = Sparse.eval nodeValue1286 (mixedVector B) := by
    change mixedMoment B node1286 node1286Labels = _
    exact sound1286 B hB hF
  have h2684 : mixedVector B (Sum.inr 2684) = Sparse.eval nodeValue2684 (mixedVector B) := by
    change mixedMoment B node2684 node2684Labels = _
    exact sound2684 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm1688, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1183, h1188, h1189, h1286, h2684, h4088, reducedSource1444] using sourceEq1688 B hB

theorem rowSound1444 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1444 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1444, numericCheck1444, reducedZero1444 B hB hF, mul_zero]

theorem reducedZero1445 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1445 (mixedVector B) = 0 := by
  have h1185 : mixedVector B (Sum.inr 1185) = Sparse.eval nodeValue1185 (mixedVector B) := by
    change mixedMoment B node1185 node1185Labels = _
    exact sound1185 B hB hF
  have h2400 : mixedVector B (Sum.inr 2400) = Sparse.eval nodeValue2400 (mixedVector B) := by
    change mixedMoment B node2400 node2400Labels = _
    exact sound2400 B hB hF
  have h2535 : mixedVector B (Sum.inr 2535) = Sparse.eval nodeValue2535 (mixedVector B) := by
    change mixedMoment B node2535 node2535Labels = _
    exact sound2535 B hB hF
  have h2677 : mixedVector B (Sum.inr 2677) = Sparse.eval nodeValue2677 (mixedVector B) := by
    change mixedMoment B node2677 node2677Labels = _
    exact sound2677 B hB hF
  have h2682 : mixedVector B (Sum.inr 2682) = Sparse.eval nodeValue2682 (mixedVector B) := by
    change mixedMoment B node2682 node2682Labels = _
    exact sound2682 B hB hF
  have h2686 : mixedVector B (Sum.inr 2686) = Sparse.eval nodeValue2686 (mixedVector B) := by
    change mixedMoment B node2686 node2686Labels = _
    exact sound2686 B hB hF
  have h4089 : mixedVector B (Sum.inr 4089) = Sparse.eval nodeValue4089 (mixedVector B) := by
    change mixedMoment B node4089 node4089Labels = _
    exact sound4089 B hB hF
  simpa only [sourceForm1689, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1185, h2400, h2535, h2677, h2682, h2686, h4089, reducedSource1445] using sourceEq1689 B hB

theorem rowSound1445 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1445 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1445, numericCheck1445, reducedZero1445 B hB hF, mul_zero]

theorem reducedZero1446 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1446 (mixedVector B) = 0 := by
  have h1188 : mixedVector B (Sum.inr 1188) = Sparse.eval nodeValue1188 (mixedVector B) := by
    change mixedMoment B node1188 node1188Labels = _
    exact sound1188 B hB hF
  have h2403 : mixedVector B (Sum.inr 2403) = Sparse.eval nodeValue2403 (mixedVector B) := by
    change mixedMoment B node2403 node2403Labels = _
    exact sound2403 B hB hF
  have h2536 : mixedVector B (Sum.inr 2536) = Sparse.eval nodeValue2536 (mixedVector B) := by
    change mixedMoment B node2536 node2536Labels = _
    exact sound2536 B hB hF
  have h2672 : mixedVector B (Sum.inr 2672) = Sparse.eval nodeValue2672 (mixedVector B) := by
    change mixedMoment B node2672 node2672Labels = _
    exact sound2672 B hB hF
  have h2684 : mixedVector B (Sum.inr 2684) = Sparse.eval nodeValue2684 (mixedVector B) := by
    change mixedMoment B node2684 node2684Labels = _
    exact sound2684 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm1690, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1188, h2403, h2536, h2672, h2684, h4088, reducedSource1446] using sourceEq1690 B hB

theorem rowSound1446 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1446 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1446, numericCheck1446, reducedZero1446 B hB hF, mul_zero]

theorem reducedZero1447 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1447 (mixedVector B) = 0 := by
  have h1184 : mixedVector B (Sum.inr 1184) = Sparse.eval nodeValue1184 (mixedVector B) := by
    change mixedMoment B node1184 node1184Labels = _
    exact sound1184 B hB hF
  have h2399 : mixedVector B (Sum.inr 2399) = Sparse.eval nodeValue2399 (mixedVector B) := by
    change mixedMoment B node2399 node2399Labels = _
    exact sound2399 B hB hF
  have h2534 : mixedVector B (Sum.inr 2534) = Sparse.eval nodeValue2534 (mixedVector B) := by
    change mixedMoment B node2534 node2534Labels = _
    exact sound2534 B hB hF
  have h2670 : mixedVector B (Sum.inr 2670) = Sparse.eval nodeValue2670 (mixedVector B) := by
    change mixedMoment B node2670 node2670Labels = _
    exact sound2670 B hB hF
  have h2681 : mixedVector B (Sum.inr 2681) = Sparse.eval nodeValue2681 (mixedVector B) := by
    change mixedMoment B node2681 node2681Labels = _
    exact sound2681 B hB hF
  have h2685 : mixedVector B (Sum.inr 2685) = Sparse.eval nodeValue2685 (mixedVector B) := by
    change mixedMoment B node2685 node2685Labels = _
    exact sound2685 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1693, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1184, h2399, h2534, h2670, h2681, h2685, h4082, reducedSource1447] using sourceEq1693 B hB

theorem rowSound1447 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1447 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1447, numericCheck1447, reducedZero1447 B hB hF, mul_zero]

theorem reducedZero1448 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1448 (mixedVector B) = 0 := by
  have h1200 : mixedVector B (Sum.inr 1200) = Sparse.eval nodeValue1200 (mixedVector B) := by
    change mixedMoment B node1200 node1200Labels = _
    exact sound1200 B hB hF
  have h1201 : mixedVector B (Sum.inr 1201) = Sparse.eval nodeValue1201 (mixedVector B) := by
    change mixedMoment B node1201 node1201Labels = _
    exact sound1201 B hB hF
  have h1228 : mixedVector B (Sum.inr 1228) = Sparse.eval nodeValue1228 (mixedVector B) := by
    change mixedMoment B node1228 node1228Labels = _
    exact sound1228 B hB hF
  have h2703 : mixedVector B (Sum.inr 2703) = Sparse.eval nodeValue2703 (mixedVector B) := by
    change mixedMoment B node2703 node2703Labels = _
    exact sound2703 B hB hF
  have h4090 : mixedVector B (Sum.inr 4090) = Sparse.eval nodeValue4090 (mixedVector B) := by
    change mixedMoment B node4090 node4090Labels = _
    exact sound4090 B hB hF
  simpa only [sourceForm1695, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1200, h1201, h1228, h2703, h4090, reducedSource1448] using sourceEq1695 B hB

theorem rowSound1448 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1448 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1448, numericCheck1448, reducedZero1448 B hB hF, mul_zero]

theorem reducedZero1449 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1449 (mixedVector B) = 0 := by
  have h1198 : mixedVector B (Sum.inr 1198) = Sparse.eval nodeValue1198 (mixedVector B) := by
    change mixedMoment B node1198 node1198Labels = _
    exact sound1198 B hB hF
  have h2459 : mixedVector B (Sum.inr 2459) = Sparse.eval nodeValue2459 (mixedVector B) := by
    change mixedMoment B node2459 node2459Labels = _
    exact sound2459 B hB hF
  have h2697 : mixedVector B (Sum.inr 2697) = Sparse.eval nodeValue2697 (mixedVector B) := by
    change mixedMoment B node2697 node2697Labels = _
    exact sound2697 B hB hF
  have h2701 : mixedVector B (Sum.inr 2701) = Sparse.eval nodeValue2701 (mixedVector B) := by
    change mixedMoment B node2701 node2701Labels = _
    exact sound2701 B hB hF
  have h2705 : mixedVector B (Sum.inr 2705) = Sparse.eval nodeValue2705 (mixedVector B) := by
    change mixedMoment B node2705 node2705Labels = _
    exact sound2705 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm1696, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1198, h2459, h2697, h2701, h2705, h4088, reducedSource1449] using sourceEq1696 B hB

theorem rowSound1449 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1449 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1449, numericCheck1449, reducedZero1449 B hB hF, mul_zero]

theorem reducedZero1450 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1450 (mixedVector B) = 0 := by
  have h1200 : mixedVector B (Sum.inr 1200) = Sparse.eval nodeValue1200 (mixedVector B) := by
    change mixedMoment B node1200 node1200Labels = _
    exact sound1200 B hB hF
  have h2461 : mixedVector B (Sum.inr 2461) = Sparse.eval nodeValue2461 (mixedVector B) := by
    change mixedMoment B node2461 node2461Labels = _
    exact sound2461 B hB hF
  have h2694 : mixedVector B (Sum.inr 2694) = Sparse.eval nodeValue2694 (mixedVector B) := by
    change mixedMoment B node2694 node2694Labels = _
    exact sound2694 B hB hF
  have h2703 : mixedVector B (Sum.inr 2703) = Sparse.eval nodeValue2703 (mixedVector B) := by
    change mixedMoment B node2703 node2703Labels = _
    exact sound2703 B hB hF
  have h4090 : mixedVector B (Sum.inr 4090) = Sparse.eval nodeValue4090 (mixedVector B) := by
    change mixedMoment B node4090 node4090Labels = _
    exact sound4090 B hB hF
  simpa only [sourceForm1697, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1200, h2461, h2694, h2703, h4090, reducedSource1450] using sourceEq1697 B hB

theorem rowSound1450 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1450 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1450, numericCheck1450, reducedZero1450 B hB hF, mul_zero]

theorem reducedZero1451 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1451 (mixedVector B) = 0 := by
  have h1197 : mixedVector B (Sum.inr 1197) = Sparse.eval nodeValue1197 (mixedVector B) := by
    change mixedMoment B node1197 node1197Labels = _
    exact sound1197 B hB hF
  have h2458 : mixedVector B (Sum.inr 2458) = Sparse.eval nodeValue2458 (mixedVector B) := by
    change mixedMoment B node2458 node2458Labels = _
    exact sound2458 B hB hF
  have h2693 : mixedVector B (Sum.inr 2693) = Sparse.eval nodeValue2693 (mixedVector B) := by
    change mixedMoment B node2693 node2693Labels = _
    exact sound2693 B hB hF
  have h2700 : mixedVector B (Sum.inr 2700) = Sparse.eval nodeValue2700 (mixedVector B) := by
    change mixedMoment B node2700 node2700Labels = _
    exact sound2700 B hB hF
  have h2704 : mixedVector B (Sum.inr 2704) = Sparse.eval nodeValue2704 (mixedVector B) := by
    change mixedMoment B node2704 node2704Labels = _
    exact sound2704 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1700, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1197, h2458, h2693, h2700, h2704, h4080, reducedSource1451] using sourceEq1700 B hB

theorem rowSound1451 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1451 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1451, numericCheck1451, reducedZero1451 B hB hF, mul_zero]

theorem reducedZero1452 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1452 (mixedVector B) = 0 := by
  have h1052 : mixedVector B (Sum.inr 1052) = Sparse.eval nodeValue1052 (mixedVector B) := by
    change mixedMoment B node1052 node1052Labels = _
    exact sound1052 B hB hF
  have h1054 : mixedVector B (Sum.inr 1054) = Sparse.eval nodeValue1054 (mixedVector B) := by
    change mixedMoment B node1054 node1054Labels = _
    exact sound1054 B hB hF
  have h1060 : mixedVector B (Sum.inr 1060) = Sparse.eval nodeValue1060 (mixedVector B) := by
    change mixedMoment B node1060 node1060Labels = _
    exact sound1060 B hB hF
  have h1073 : mixedVector B (Sum.inr 1073) = Sparse.eval nodeValue1073 (mixedVector B) := by
    change mixedMoment B node1073 node1073Labels = _
    exact sound1073 B hB hF
  have h2275 : mixedVector B (Sum.inr 2275) = Sparse.eval nodeValue2275 (mixedVector B) := by
    change mixedMoment B node2275 node2275Labels = _
    exact sound2275 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1702, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1052, h1054, h1060, h1073, h2275, h4080, reducedSource1452] using sourceEq1702 B hB

theorem rowSound1452 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1452 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1452, numericCheck1452, reducedZero1452 B hB hF, mul_zero]

theorem reducedZero1453 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1453 (mixedVector B) = 0 := by
  have h1054 : mixedVector B (Sum.inr 1054) = Sparse.eval nodeValue1054 (mixedVector B) := by
    change mixedMoment B node1054 node1054Labels = _
    exact sound1054 B hB hF
  have h2031 : mixedVector B (Sum.inr 2031) = Sparse.eval nodeValue2031 (mixedVector B) := by
    change mixedMoment B node2031 node2031Labels = _
    exact sound2031 B hB hF
  have h2129 : mixedVector B (Sum.inr 2129) = Sparse.eval nodeValue2129 (mixedVector B) := by
    change mixedMoment B node2129 node2129Labels = _
    exact sound2129 B hB hF
  have h2216 : mixedVector B (Sum.inr 2216) = Sparse.eval nodeValue2216 (mixedVector B) := by
    change mixedMoment B node2216 node2216Labels = _
    exact sound2216 B hB hF
  have h2251 : mixedVector B (Sum.inr 2251) = Sparse.eval nodeValue2251 (mixedVector B) := by
    change mixedMoment B node2251 node2251Labels = _
    exact sound2251 B hB hF
  have h2275 : mixedVector B (Sum.inr 2275) = Sparse.eval nodeValue2275 (mixedVector B) := by
    change mixedMoment B node2275 node2275Labels = _
    exact sound2275 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1703, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1054, h2031, h2129, h2216, h2251, h2275, h4080, reducedSource1453] using sourceEq1703 B hB

theorem rowSound1453 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1453 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1453, numericCheck1453, reducedZero1453 B hB hF, mul_zero]

theorem reducedZero1454 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1454 (mixedVector B) = 0 := by
  have h1053 : mixedVector B (Sum.inr 1053) = Sparse.eval nodeValue1053 (mixedVector B) := by
    change mixedMoment B node1053 node1053Labels = _
    exact sound1053 B hB hF
  have h2030 : mixedVector B (Sum.inr 2030) = Sparse.eval nodeValue2030 (mixedVector B) := by
    change mixedMoment B node2030 node2030Labels = _
    exact sound2030 B hB hF
  have h2128 : mixedVector B (Sum.inr 2128) = Sparse.eval nodeValue2128 (mixedVector B) := by
    change mixedMoment B node2128 node2128Labels = _
    exact sound2128 B hB hF
  have h2215 : mixedVector B (Sum.inr 2215) = Sparse.eval nodeValue2215 (mixedVector B) := by
    change mixedMoment B node2215 node2215Labels = _
    exact sound2215 B hB hF
  have h2274 : mixedVector B (Sum.inr 2274) = Sparse.eval nodeValue2274 (mixedVector B) := by
    change mixedMoment B node2274 node2274Labels = _
    exact sound2274 B hB hF
  have h2276 : mixedVector B (Sum.inr 2276) = Sparse.eval nodeValue2276 (mixedVector B) := by
    change mixedMoment B node2276 node2276Labels = _
    exact sound2276 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1704, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1053, h2030, h2128, h2215, h2274, h2276, h4082, reducedSource1454] using sourceEq1704 B hB

theorem rowSound1454 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1454 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1454, numericCheck1454, reducedZero1454 B hB hF, mul_zero]

theorem reducedZero1455 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1455 (mixedVector B) = 0 := by
  have h988 : mixedVector B (Sum.inr 988) = Sparse.eval nodeValue988 (mixedVector B) := by
    change mixedMoment B node988 node988Labels = _
    exact sound988 B hB hF
  have h990 : mixedVector B (Sum.inr 990) = Sparse.eval nodeValue990 (mixedVector B) := by
    change mixedMoment B node990 node990Labels = _
    exact sound990 B hB hF
  have h998 : mixedVector B (Sum.inr 998) = Sparse.eval nodeValue998 (mixedVector B) := by
    change mixedMoment B node998 node998Labels = _
    exact sound998 B hB hF
  have h1052 : mixedVector B (Sum.inr 1052) = Sparse.eval nodeValue1052 (mixedVector B) := by
    change mixedMoment B node1052 node1052Labels = _
    exact sound1052 B hB hF
  have h2214 : mixedVector B (Sum.inr 2214) = Sparse.eval nodeValue2214 (mixedVector B) := by
    change mixedMoment B node2214 node2214Labels = _
    exact sound2214 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1706, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h988, h990, h998, h1052, h2214, h4080, reducedSource1455] using sourceEq1706 B hB

theorem rowSound1455 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1455 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1455, numericCheck1455, reducedZero1455 B hB hF, mul_zero]

theorem sourceRowsAt1440 : MixedData.sourceRows (1440 : Fin 2425) =
    MixedData.row1440 := by decide +kernel

theorem sourceRowsAt1441 : MixedData.sourceRows (1441 : Fin 2425) =
    MixedData.row1441 := by decide +kernel

theorem sourceRowsAt1442 : MixedData.sourceRows (1442 : Fin 2425) =
    MixedData.row1442 := by decide +kernel

theorem sourceRowsAt1443 : MixedData.sourceRows (1443 : Fin 2425) =
    MixedData.row1443 := by decide +kernel

theorem sourceRowsAt1444 : MixedData.sourceRows (1444 : Fin 2425) =
    MixedData.row1444 := by decide +kernel

theorem sourceRowsAt1445 : MixedData.sourceRows (1445 : Fin 2425) =
    MixedData.row1445 := by decide +kernel

theorem sourceRowsAt1446 : MixedData.sourceRows (1446 : Fin 2425) =
    MixedData.row1446 := by decide +kernel

theorem sourceRowsAt1447 : MixedData.sourceRows (1447 : Fin 2425) =
    MixedData.row1447 := by decide +kernel

theorem sourceRowsAt1448 : MixedData.sourceRows (1448 : Fin 2425) =
    MixedData.row1448 := by decide +kernel

theorem sourceRowsAt1449 : MixedData.sourceRows (1449 : Fin 2425) =
    MixedData.row1449 := by decide +kernel

theorem sourceRowsAt1450 : MixedData.sourceRows (1450 : Fin 2425) =
    MixedData.row1450 := by decide +kernel

theorem sourceRowsAt1451 : MixedData.sourceRows (1451 : Fin 2425) =
    MixedData.row1451 := by decide +kernel

theorem sourceRowsAt1452 : MixedData.sourceRows (1452 : Fin 2425) =
    MixedData.row1452 := by decide +kernel

theorem sourceRowsAt1453 : MixedData.sourceRows (1453 : Fin 2425) =
    MixedData.row1453 := by decide +kernel

theorem sourceRowsAt1454 : MixedData.sourceRows (1454 : Fin 2425) =
    MixedData.row1454 := by decide +kernel

theorem sourceRowsAt1455 : MixedData.sourceRows (1455 : Fin 2425) =
    MixedData.row1455 := by decide +kernel

theorem chunkSound90 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 90) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1440 ∨ k.val = 1441 ∨ k.val = 1442 ∨ k.val = 1443 ∨ k.val = 1444 ∨ k.val = 1445 ∨ k.val = 1446 ∨ k.val = 1447 ∨ k.val = 1448 ∨ k.val = 1449 ∨ k.val = 1450 ∨ k.val = 1451 ∨ k.val = 1452 ∨ k.val = 1453 ∨ k.val = 1454 ∨ k.val = 1455 := by omega
  rcases heq with h1440 | h1441 | h1442 | h1443 | h1444 | h1445 | h1446 | h1447 | h1448 | h1449 | h1450 | h1451 | h1452 | h1453 | h1454 | h1455
  · have he : k = (1440 : Fin 2425) := Fin.ext h1440
    subst k
    rw [sourceRowsAt1440]
    exact rowSound1440 B hB hF
  · have he : k = (1441 : Fin 2425) := Fin.ext h1441
    subst k
    rw [sourceRowsAt1441]
    exact rowSound1441 B hB hF
  · have he : k = (1442 : Fin 2425) := Fin.ext h1442
    subst k
    rw [sourceRowsAt1442]
    exact rowSound1442 B hB hF
  · have he : k = (1443 : Fin 2425) := Fin.ext h1443
    subst k
    rw [sourceRowsAt1443]
    exact rowSound1443 B hB hF
  · have he : k = (1444 : Fin 2425) := Fin.ext h1444
    subst k
    rw [sourceRowsAt1444]
    exact rowSound1444 B hB hF
  · have he : k = (1445 : Fin 2425) := Fin.ext h1445
    subst k
    rw [sourceRowsAt1445]
    exact rowSound1445 B hB hF
  · have he : k = (1446 : Fin 2425) := Fin.ext h1446
    subst k
    rw [sourceRowsAt1446]
    exact rowSound1446 B hB hF
  · have he : k = (1447 : Fin 2425) := Fin.ext h1447
    subst k
    rw [sourceRowsAt1447]
    exact rowSound1447 B hB hF
  · have he : k = (1448 : Fin 2425) := Fin.ext h1448
    subst k
    rw [sourceRowsAt1448]
    exact rowSound1448 B hB hF
  · have he : k = (1449 : Fin 2425) := Fin.ext h1449
    subst k
    rw [sourceRowsAt1449]
    exact rowSound1449 B hB hF
  · have he : k = (1450 : Fin 2425) := Fin.ext h1450
    subst k
    rw [sourceRowsAt1450]
    exact rowSound1450 B hB hF
  · have he : k = (1451 : Fin 2425) := Fin.ext h1451
    subst k
    rw [sourceRowsAt1451]
    exact rowSound1451 B hB hF
  · have he : k = (1452 : Fin 2425) := Fin.ext h1452
    subst k
    rw [sourceRowsAt1452]
    exact rowSound1452 B hB hF
  · have he : k = (1453 : Fin 2425) := Fin.ext h1453
    subst k
    rw [sourceRowsAt1453]
    exact rowSound1453 B hB hF
  · have he : k = (1454 : Fin 2425) := Fin.ext h1454
    subst k
    rw [sourceRowsAt1454]
    exact rowSound1454 B hB hF
  · have he : k = (1455 : Fin 2425) := Fin.ext h1455
    subst k
    rw [sourceRowsAt1455]
    exact rowSound1455 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
