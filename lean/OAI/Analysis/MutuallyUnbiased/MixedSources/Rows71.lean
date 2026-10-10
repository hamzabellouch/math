import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources41

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1136 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1136 (mixedVector B) = 0 := by
  have h1190 : mixedVector B (Sum.inr 1190) = Sparse.eval nodeValue1190 (mixedVector B) := by
    change mixedMoment B node1190 node1190Labels = _
    exact sound1190 B hB hF
  have h1924 : mixedVector B (Sum.inr 1924) = Sparse.eval nodeValue1924 (mixedVector B) := by
    change mixedMoment B node1924 node1924Labels = _
    exact sound1924 B hB hF
  have h1950 : mixedVector B (Sum.inr 1950) = Sparse.eval nodeValue1950 (mixedVector B) := by
    change mixedMoment B node1950 node1950Labels = _
    exact sound1950 B hB hF
  have h2218 : mixedVector B (Sum.inr 2218) = Sparse.eval nodeValue2218 (mixedVector B) := by
    change mixedMoment B node2218 node2218Labels = _
    exact sound2218 B hB hF
  have h2685 : mixedVector B (Sum.inr 2685) = Sparse.eval nodeValue2685 (mixedVector B) := by
    change mixedMoment B node2685 node2685Labels = _
    exact sound2685 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1311, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1190, h1924, h1950, h2218, h2685, h4082, reducedSource1136] using sourceEq1311 B hB

theorem rowSound1136 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1136 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1136, numericCheck1136, reducedZero1136 B hB hF, mul_zero]

theorem reducedZero1137 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1137 (mixedVector B) = 0 := by
  have h893 : mixedVector B (Sum.inr 893) = Sparse.eval nodeValue893 (mixedVector B) := by
    change mixedMoment B node893 node893Labels = _
    exact sound893 B hB hF
  have h1098 : mixedVector B (Sum.inr 1098) = Sparse.eval nodeValue1098 (mixedVector B) := by
    change mixedMoment B node1098 node1098Labels = _
    exact sound1098 B hB hF
  have h1103 : mixedVector B (Sum.inr 1103) = Sparse.eval nodeValue1103 (mixedVector B) := by
    change mixedMoment B node1103 node1103Labels = _
    exact sound1103 B hB hF
  have h1190 : mixedVector B (Sum.inr 1190) = Sparse.eval nodeValue1190 (mixedVector B) := by
    change mixedMoment B node1190 node1190Labels = _
    exact sound1190 B hB hF
  have h1950 : mixedVector B (Sum.inr 1950) = Sparse.eval nodeValue1950 (mixedVector B) := by
    change mixedMoment B node1950 node1950Labels = _
    exact sound1950 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1312, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h893, h1098, h1103, h1190, h1950, h4082, reducedSource1137] using sourceEq1312 B hB

theorem rowSound1137 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1137 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1137, numericCheck1137, reducedZero1137 B hB hF, mul_zero]

theorem reducedZero1138 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1138 (mixedVector B) = 0 := by
  have h1184 : mixedVector B (Sum.inr 1184) = Sparse.eval nodeValue1184 (mixedVector B) := by
    change mixedMoment B node1184 node1184Labels = _
    exact sound1184 B hB hF
  have h1190 : mixedVector B (Sum.inr 1190) = Sparse.eval nodeValue1190 (mixedVector B) := by
    change mixedMoment B node1190 node1190Labels = _
    exact sound1190 B hB hF
  have h1192 : mixedVector B (Sum.inr 1192) = Sparse.eval nodeValue1192 (mixedVector B) := by
    change mixedMoment B node1192 node1192Labels = _
    exact sound1192 B hB hF
  have h1287 : mixedVector B (Sum.inr 1287) = Sparse.eval nodeValue1287 (mixedVector B) := by
    change mixedMoment B node1287 node1287Labels = _
    exact sound1287 B hB hF
  have h2685 : mixedVector B (Sum.inr 2685) = Sparse.eval nodeValue2685 (mixedVector B) := by
    change mixedMoment B node2685 node2685Labels = _
    exact sound2685 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1313, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1184, h1190, h1192, h1287, h2685, h4082, reducedSource1138] using sourceEq1313 B hB

theorem rowSound1138 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1138 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1138, numericCheck1138, reducedZero1138 B hB hF, mul_zero]

theorem reducedZero1139 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1139 (mixedVector B) = 0 := by
  have h1186 : mixedVector B (Sum.inr 1186) = Sparse.eval nodeValue1186 (mixedVector B) := by
    change mixedMoment B node1186 node1186Labels = _
    exact sound1186 B hB hF
  have h1608 : mixedVector B (Sum.inr 1608) = Sparse.eval nodeValue1608 (mixedVector B) := by
    change mixedMoment B node1608 node1608Labels = _
    exact sound1608 B hB hF
  have h1627 : mixedVector B (Sum.inr 1627) = Sparse.eval nodeValue1627 (mixedVector B) := by
    change mixedMoment B node1627 node1627Labels = _
    exact sound1627 B hB hF
  have h1741 : mixedVector B (Sum.inr 1741) = Sparse.eval nodeValue1741 (mixedVector B) := by
    change mixedMoment B node1741 node1741Labels = _
    exact sound1741 B hB hF
  have h2683 : mixedVector B (Sum.inr 2683) = Sparse.eval nodeValue2683 (mixedVector B) := by
    change mixedMoment B node2683 node2683Labels = _
    exact sound2683 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1315, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1186, h1608, h1627, h1741, h2683, h4071, reducedSource1139] using sourceEq1315 B hB

theorem rowSound1139 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1139 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1139, numericCheck1139, reducedZero1139 B hB hF, mul_zero]

theorem reducedZero1140 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1140 (mixedVector B) = 0 := by
  have h1203 : mixedVector B (Sum.inr 1203) = Sparse.eval nodeValue1203 (mixedVector B) := by
    change mixedMoment B node1203 node1203Labels = _
    exact sound1203 B hB hF
  have h2377 : mixedVector B (Sum.inr 2377) = Sparse.eval nodeValue2377 (mixedVector B) := by
    change mixedMoment B node2377 node2377Labels = _
    exact sound2377 B hB hF
  have h2385 : mixedVector B (Sum.inr 2385) = Sparse.eval nodeValue2385 (mixedVector B) := by
    change mixedMoment B node2385 node2385Labels = _
    exact sound2385 B hB hF
  have h2664 : mixedVector B (Sum.inr 2664) = Sparse.eval nodeValue2664 (mixedVector B) := by
    change mixedMoment B node2664 node2664Labels = _
    exact sound2664 B hB hF
  have h2705 : mixedVector B (Sum.inr 2705) = Sparse.eval nodeValue2705 (mixedVector B) := by
    change mixedMoment B node2705 node2705Labels = _
    exact sound2705 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm1316, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1203, h2377, h2385, h2664, h2705, h4088, reducedSource1140] using sourceEq1316 B hB

theorem rowSound1140 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1140 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1140, numericCheck1140, reducedZero1140 B hB hF, mul_zero]

theorem reducedZero1141 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1141 (mixedVector B) = 0 := by
  have h1198 : mixedVector B (Sum.inr 1198) = Sparse.eval nodeValue1198 (mixedVector B) := by
    change mixedMoment B node1198 node1198Labels = _
    exact sound1198 B hB hF
  have h1203 : mixedVector B (Sum.inr 1203) = Sparse.eval nodeValue1203 (mixedVector B) := by
    change mixedMoment B node1203 node1203Labels = _
    exact sound1203 B hB hF
  have h1205 : mixedVector B (Sum.inr 1205) = Sparse.eval nodeValue1205 (mixedVector B) := by
    change mixedMoment B node1205 node1205Labels = _
    exact sound1205 B hB hF
  have h1230 : mixedVector B (Sum.inr 1230) = Sparse.eval nodeValue1230 (mixedVector B) := by
    change mixedMoment B node1230 node1230Labels = _
    exact sound1230 B hB hF
  have h2705 : mixedVector B (Sum.inr 2705) = Sparse.eval nodeValue2705 (mixedVector B) := by
    change mixedMoment B node2705 node2705Labels = _
    exact sound2705 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm1317, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1198, h1203, h1205, h1230, h2705, h4088, reducedSource1141] using sourceEq1317 B hB

theorem rowSound1141 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1141 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1141, numericCheck1141, reducedZero1141 B hB hF, mul_zero]

theorem reducedZero1142 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1142 (mixedVector B) = 0 := by
  have h1202 : mixedVector B (Sum.inr 1202) = Sparse.eval nodeValue1202 (mixedVector B) := by
    change mixedMoment B node1202 node1202Labels = _
    exact sound1202 B hB hF
  have h1897 : mixedVector B (Sum.inr 1897) = Sparse.eval nodeValue1897 (mixedVector B) := by
    change mixedMoment B node1897 node1897Labels = _
    exact sound1897 B hB hF
  have h1914 : mixedVector B (Sum.inr 1914) = Sparse.eval nodeValue1914 (mixedVector B) := by
    change mixedMoment B node1914 node1914Labels = _
    exact sound1914 B hB hF
  have h2193 : mixedVector B (Sum.inr 2193) = Sparse.eval nodeValue2193 (mixedVector B) := by
    change mixedMoment B node2193 node2193Labels = _
    exact sound2193 B hB hF
  have h2704 : mixedVector B (Sum.inr 2704) = Sparse.eval nodeValue2704 (mixedVector B) := by
    change mixedMoment B node2704 node2704Labels = _
    exact sound2704 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1318, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1202, h1897, h1914, h2193, h2704, h4080, reducedSource1142] using sourceEq1318 B hB

theorem rowSound1142 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1142 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1142, numericCheck1142, reducedZero1142 B hB hF, mul_zero]

theorem reducedZero1143 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1143 (mixedVector B) = 0 := by
  have h871 : mixedVector B (Sum.inr 871) = Sparse.eval nodeValue871 (mixedVector B) := by
    change mixedMoment B node871 node871Labels = _
    exact sound871 B hB hF
  have h1105 : mixedVector B (Sum.inr 1105) = Sparse.eval nodeValue1105 (mixedVector B) := by
    change mixedMoment B node1105 node1105Labels = _
    exact sound1105 B hB hF
  have h1109 : mixedVector B (Sum.inr 1109) = Sparse.eval nodeValue1109 (mixedVector B) := by
    change mixedMoment B node1109 node1109Labels = _
    exact sound1109 B hB hF
  have h1123 : mixedVector B (Sum.inr 1123) = Sparse.eval nodeValue1123 (mixedVector B) := by
    change mixedMoment B node1123 node1123Labels = _
    exact sound1123 B hB hF
  have h1202 : mixedVector B (Sum.inr 1202) = Sparse.eval nodeValue1202 (mixedVector B) := by
    change mixedMoment B node1202 node1202Labels = _
    exact sound1202 B hB hF
  have h1914 : mixedVector B (Sum.inr 1914) = Sparse.eval nodeValue1914 (mixedVector B) := by
    change mixedMoment B node1914 node1914Labels = _
    exact sound1914 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1319, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h871, h1105, h1109, h1123, h1202, h1914, h4080, reducedSource1143] using sourceEq1319 B hB

theorem rowSound1143 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1143 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1143, numericCheck1143, reducedZero1143 B hB hF, mul_zero]

theorem reducedZero1144 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1144 (mixedVector B) = 0 := by
  have h1197 : mixedVector B (Sum.inr 1197) = Sparse.eval nodeValue1197 (mixedVector B) := by
    change mixedMoment B node1197 node1197Labels = _
    exact sound1197 B hB hF
  have h1202 : mixedVector B (Sum.inr 1202) = Sparse.eval nodeValue1202 (mixedVector B) := by
    change mixedMoment B node1202 node1202Labels = _
    exact sound1202 B hB hF
  have h1204 : mixedVector B (Sum.inr 1204) = Sparse.eval nodeValue1204 (mixedVector B) := by
    change mixedMoment B node1204 node1204Labels = _
    exact sound1204 B hB hF
  have h1229 : mixedVector B (Sum.inr 1229) = Sparse.eval nodeValue1229 (mixedVector B) := by
    change mixedMoment B node1229 node1229Labels = _
    exact sound1229 B hB hF
  have h2704 : mixedVector B (Sum.inr 2704) = Sparse.eval nodeValue2704 (mixedVector B) := by
    change mixedMoment B node2704 node2704Labels = _
    exact sound2704 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1320, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1197, h1202, h1204, h1229, h2704, h4080, reducedSource1144] using sourceEq1320 B hB

theorem rowSound1144 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1144 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1144, numericCheck1144, reducedZero1144 B hB hF, mul_zero]

theorem reducedZero1145 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1145 (mixedVector B) = 0 := by
  have h1199 : mixedVector B (Sum.inr 1199) = Sparse.eval nodeValue1199 (mixedVector B) := by
    change mixedMoment B node1199 node1199Labels = _
    exact sound1199 B hB hF
  have h1592 : mixedVector B (Sum.inr 1592) = Sparse.eval nodeValue1592 (mixedVector B) := by
    change mixedMoment B node1592 node1592Labels = _
    exact sound1592 B hB hF
  have h1602 : mixedVector B (Sum.inr 1602) = Sparse.eval nodeValue1602 (mixedVector B) := by
    change mixedMoment B node1602 node1602Labels = _
    exact sound1602 B hB hF
  have h1710 : mixedVector B (Sum.inr 1710) = Sparse.eval nodeValue1710 (mixedVector B) := by
    change mixedMoment B node1710 node1710Labels = _
    exact sound1710 B hB hF
  have h2702 : mixedVector B (Sum.inr 2702) = Sparse.eval nodeValue2702 (mixedVector B) := by
    change mixedMoment B node2702 node2702Labels = _
    exact sound2702 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1322, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1199, h1592, h1602, h1710, h2702, h4069, reducedSource1145] using sourceEq1322 B hB

theorem rowSound1145 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1145 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1145, numericCheck1145, reducedZero1145 B hB hF, mul_zero]

theorem reducedZero1146 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1146 (mixedVector B) = 0 := by
  have h1055 : mixedVector B (Sum.inr 1055) = Sparse.eval nodeValue1055 (mixedVector B) := by
    change mixedMoment B node1055 node1055Labels = _
    exact sound1055 B hB hF
  have h2032 : mixedVector B (Sum.inr 2032) = Sparse.eval nodeValue2032 (mixedVector B) := by
    change mixedMoment B node2032 node2032Labels = _
    exact sound2032 B hB hF
  have h2130 : mixedVector B (Sum.inr 2130) = Sparse.eval nodeValue2130 (mixedVector B) := by
    change mixedMoment B node2130 node2130Labels = _
    exact sound2130 B hB hF
  have h2218 : mixedVector B (Sum.inr 2218) = Sparse.eval nodeValue2218 (mixedVector B) := by
    change mixedMoment B node2218 node2218Labels = _
    exact sound2218 B hB hF
  have h2276 : mixedVector B (Sum.inr 2276) = Sparse.eval nodeValue2276 (mixedVector B) := by
    change mixedMoment B node2276 node2276Labels = _
    exact sound2276 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1323, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1055, h2032, h2130, h2218, h2276, h4082, reducedSource1146] using sourceEq1323 B hB

theorem rowSound1146 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1146 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1146, numericCheck1146, reducedZero1146 B hB hF, mul_zero]

theorem reducedZero1147 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1147 (mixedVector B) = 0 := by
  have h1053 : mixedVector B (Sum.inr 1053) = Sparse.eval nodeValue1053 (mixedVector B) := by
    change mixedMoment B node1053 node1053Labels = _
    exact sound1053 B hB hF
  have h1055 : mixedVector B (Sum.inr 1055) = Sparse.eval nodeValue1055 (mixedVector B) := by
    change mixedMoment B node1055 node1055Labels = _
    exact sound1055 B hB hF
  have h1062 : mixedVector B (Sum.inr 1062) = Sparse.eval nodeValue1062 (mixedVector B) := by
    change mixedMoment B node1062 node1062Labels = _
    exact sound1062 B hB hF
  have h1075 : mixedVector B (Sum.inr 1075) = Sparse.eval nodeValue1075 (mixedVector B) := by
    change mixedMoment B node1075 node1075Labels = _
    exact sound1075 B hB hF
  have h2276 : mixedVector B (Sum.inr 2276) = Sparse.eval nodeValue2276 (mixedVector B) := by
    change mixedMoment B node2276 node2276Labels = _
    exact sound2276 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1324, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1053, h1055, h1062, h1075, h2276, h4082, reducedSource1147] using sourceEq1324 B hB

theorem rowSound1147 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1147 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1147, numericCheck1147, reducedZero1147 B hB hF, mul_zero]

theorem reducedZero1148 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1148 (mixedVector B) = 0 := by
  have h991 : mixedVector B (Sum.inr 991) = Sparse.eval nodeValue991 (mixedVector B) := by
    change mixedMoment B node991 node991Labels = _
    exact sound991 B hB hF
  have h1926 : mixedVector B (Sum.inr 1926) = Sparse.eval nodeValue1926 (mixedVector B) := by
    change mixedMoment B node1926 node1926Labels = _
    exact sound1926 B hB hF
  have h1992 : mixedVector B (Sum.inr 1992) = Sparse.eval nodeValue1992 (mixedVector B) := by
    change mixedMoment B node1992 node1992Labels = _
    exact sound1992 B hB hF
  have h2121 : mixedVector B (Sum.inr 2121) = Sparse.eval nodeValue2121 (mixedVector B) := by
    change mixedMoment B node2121 node2121Labels = _
    exact sound2121 B hB hF
  have h2197 : mixedVector B (Sum.inr 2197) = Sparse.eval nodeValue2197 (mixedVector B) := by
    change mixedMoment B node2197 node2197Labels = _
    exact sound2197 B hB hF
  have h2216 : mixedVector B (Sum.inr 2216) = Sparse.eval nodeValue2216 (mixedVector B) := by
    change mixedMoment B node2216 node2216Labels = _
    exact sound2216 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1325, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h991, h1926, h1992, h2121, h2197, h2216, h4080, reducedSource1148] using sourceEq1325 B hB

theorem rowSound1148 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1148 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1148, numericCheck1148, reducedZero1148 B hB hF, mul_zero]

theorem reducedZero1149 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1149 (mixedVector B) = 0 := by
  have h988 : mixedVector B (Sum.inr 988) = Sparse.eval nodeValue988 (mixedVector B) := by
    change mixedMoment B node988 node988Labels = _
    exact sound988 B hB hF
  have h991 : mixedVector B (Sum.inr 991) = Sparse.eval nodeValue991 (mixedVector B) := by
    change mixedMoment B node991 node991Labels = _
    exact sound991 B hB hF
  have h993 : mixedVector B (Sum.inr 993) = Sparse.eval nodeValue993 (mixedVector B) := by
    change mixedMoment B node993 node993Labels = _
    exact sound993 B hB hF
  have h1005 : mixedVector B (Sum.inr 1005) = Sparse.eval nodeValue1005 (mixedVector B) := by
    change mixedMoment B node1005 node1005Labels = _
    exact sound1005 B hB hF
  have h1054 : mixedVector B (Sum.inr 1054) = Sparse.eval nodeValue1054 (mixedVector B) := by
    change mixedMoment B node1054 node1054Labels = _
    exact sound1054 B hB hF
  have h2216 : mixedVector B (Sum.inr 2216) = Sparse.eval nodeValue2216 (mixedVector B) := by
    change mixedMoment B node2216 node2216Labels = _
    exact sound2216 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1326, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h988, h991, h993, h1005, h1054, h2216, h4080, reducedSource1149] using sourceEq1326 B hB

theorem rowSound1149 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1149 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1149, numericCheck1149, reducedZero1149 B hB hF, mul_zero]

theorem reducedZero1150 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1150 (mixedVector B) = 0 := by
  have h989 : mixedVector B (Sum.inr 989) = Sparse.eval nodeValue989 (mixedVector B) := by
    change mixedMoment B node989 node989Labels = _
    exact sound989 B hB hF
  have h1924 : mixedVector B (Sum.inr 1924) = Sparse.eval nodeValue1924 (mixedVector B) := by
    change mixedMoment B node1924 node1924Labels = _
    exact sound1924 B hB hF
  have h1991 : mixedVector B (Sum.inr 1991) = Sparse.eval nodeValue1991 (mixedVector B) := by
    change mixedMoment B node1991 node1991Labels = _
    exact sound1991 B hB hF
  have h2119 : mixedVector B (Sum.inr 2119) = Sparse.eval nodeValue2119 (mixedVector B) := by
    change mixedMoment B node2119 node2119Labels = _
    exact sound2119 B hB hF
  have h2215 : mixedVector B (Sum.inr 2215) = Sparse.eval nodeValue2215 (mixedVector B) := by
    change mixedMoment B node2215 node2215Labels = _
    exact sound2215 B hB hF
  have h2218 : mixedVector B (Sum.inr 2218) = Sparse.eval nodeValue2218 (mixedVector B) := by
    change mixedMoment B node2218 node2218Labels = _
    exact sound2218 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1327, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h989, h1924, h1991, h2119, h2215, h2218, h4082, reducedSource1150] using sourceEq1327 B hB

theorem rowSound1150 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1150 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1150, numericCheck1150, reducedZero1150 B hB hF, mul_zero]

theorem reducedZero1151 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1151 (mixedVector B) = 0 := by
  have h987 : mixedVector B (Sum.inr 987) = Sparse.eval nodeValue987 (mixedVector B) := by
    change mixedMoment B node987 node987Labels = _
    exact sound987 B hB hF
  have h989 : mixedVector B (Sum.inr 989) = Sparse.eval nodeValue989 (mixedVector B) := by
    change mixedMoment B node989 node989Labels = _
    exact sound989 B hB hF
  have h992 : mixedVector B (Sum.inr 992) = Sparse.eval nodeValue992 (mixedVector B) := by
    change mixedMoment B node992 node992Labels = _
    exact sound992 B hB hF
  have h1000 : mixedVector B (Sum.inr 1000) = Sparse.eval nodeValue1000 (mixedVector B) := by
    change mixedMoment B node1000 node1000Labels = _
    exact sound1000 B hB hF
  have h1053 : mixedVector B (Sum.inr 1053) = Sparse.eval nodeValue1053 (mixedVector B) := by
    change mixedMoment B node1053 node1053Labels = _
    exact sound1053 B hB hF
  have h2215 : mixedVector B (Sum.inr 2215) = Sparse.eval nodeValue2215 (mixedVector B) := by
    change mixedMoment B node2215 node2215Labels = _
    exact sound2215 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1328, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h987, h989, h992, h1000, h1053, h2215, h4082, reducedSource1151] using sourceEq1328 B hB

theorem rowSound1151 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1151 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1151, numericCheck1151, reducedZero1151 B hB hF, mul_zero]

theorem sourceRowsAt1136 : MixedData.sourceRows (1136 : Fin 2425) =
    MixedData.row1136 := by decide +kernel

theorem sourceRowsAt1137 : MixedData.sourceRows (1137 : Fin 2425) =
    MixedData.row1137 := by decide +kernel

theorem sourceRowsAt1138 : MixedData.sourceRows (1138 : Fin 2425) =
    MixedData.row1138 := by decide +kernel

theorem sourceRowsAt1139 : MixedData.sourceRows (1139 : Fin 2425) =
    MixedData.row1139 := by decide +kernel

theorem sourceRowsAt1140 : MixedData.sourceRows (1140 : Fin 2425) =
    MixedData.row1140 := by decide +kernel

theorem sourceRowsAt1141 : MixedData.sourceRows (1141 : Fin 2425) =
    MixedData.row1141 := by decide +kernel

theorem sourceRowsAt1142 : MixedData.sourceRows (1142 : Fin 2425) =
    MixedData.row1142 := by decide +kernel

theorem sourceRowsAt1143 : MixedData.sourceRows (1143 : Fin 2425) =
    MixedData.row1143 := by decide +kernel

theorem sourceRowsAt1144 : MixedData.sourceRows (1144 : Fin 2425) =
    MixedData.row1144 := by decide +kernel

theorem sourceRowsAt1145 : MixedData.sourceRows (1145 : Fin 2425) =
    MixedData.row1145 := by decide +kernel

theorem sourceRowsAt1146 : MixedData.sourceRows (1146 : Fin 2425) =
    MixedData.row1146 := by decide +kernel

theorem sourceRowsAt1147 : MixedData.sourceRows (1147 : Fin 2425) =
    MixedData.row1147 := by decide +kernel

theorem sourceRowsAt1148 : MixedData.sourceRows (1148 : Fin 2425) =
    MixedData.row1148 := by decide +kernel

theorem sourceRowsAt1149 : MixedData.sourceRows (1149 : Fin 2425) =
    MixedData.row1149 := by decide +kernel

theorem sourceRowsAt1150 : MixedData.sourceRows (1150 : Fin 2425) =
    MixedData.row1150 := by decide +kernel

theorem sourceRowsAt1151 : MixedData.sourceRows (1151 : Fin 2425) =
    MixedData.row1151 := by decide +kernel

theorem chunkSound71 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 71) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1136 ∨ k.val = 1137 ∨ k.val = 1138 ∨ k.val = 1139 ∨ k.val = 1140 ∨ k.val = 1141 ∨ k.val = 1142 ∨ k.val = 1143 ∨ k.val = 1144 ∨ k.val = 1145 ∨ k.val = 1146 ∨ k.val = 1147 ∨ k.val = 1148 ∨ k.val = 1149 ∨ k.val = 1150 ∨ k.val = 1151 := by omega
  rcases heq with h1136 | h1137 | h1138 | h1139 | h1140 | h1141 | h1142 | h1143 | h1144 | h1145 | h1146 | h1147 | h1148 | h1149 | h1150 | h1151
  · have he : k = (1136 : Fin 2425) := Fin.ext h1136
    subst k
    rw [sourceRowsAt1136]
    exact rowSound1136 B hB hF
  · have he : k = (1137 : Fin 2425) := Fin.ext h1137
    subst k
    rw [sourceRowsAt1137]
    exact rowSound1137 B hB hF
  · have he : k = (1138 : Fin 2425) := Fin.ext h1138
    subst k
    rw [sourceRowsAt1138]
    exact rowSound1138 B hB hF
  · have he : k = (1139 : Fin 2425) := Fin.ext h1139
    subst k
    rw [sourceRowsAt1139]
    exact rowSound1139 B hB hF
  · have he : k = (1140 : Fin 2425) := Fin.ext h1140
    subst k
    rw [sourceRowsAt1140]
    exact rowSound1140 B hB hF
  · have he : k = (1141 : Fin 2425) := Fin.ext h1141
    subst k
    rw [sourceRowsAt1141]
    exact rowSound1141 B hB hF
  · have he : k = (1142 : Fin 2425) := Fin.ext h1142
    subst k
    rw [sourceRowsAt1142]
    exact rowSound1142 B hB hF
  · have he : k = (1143 : Fin 2425) := Fin.ext h1143
    subst k
    rw [sourceRowsAt1143]
    exact rowSound1143 B hB hF
  · have he : k = (1144 : Fin 2425) := Fin.ext h1144
    subst k
    rw [sourceRowsAt1144]
    exact rowSound1144 B hB hF
  · have he : k = (1145 : Fin 2425) := Fin.ext h1145
    subst k
    rw [sourceRowsAt1145]
    exact rowSound1145 B hB hF
  · have he : k = (1146 : Fin 2425) := Fin.ext h1146
    subst k
    rw [sourceRowsAt1146]
    exact rowSound1146 B hB hF
  · have he : k = (1147 : Fin 2425) := Fin.ext h1147
    subst k
    rw [sourceRowsAt1147]
    exact rowSound1147 B hB hF
  · have he : k = (1148 : Fin 2425) := Fin.ext h1148
    subst k
    rw [sourceRowsAt1148]
    exact rowSound1148 B hB hF
  · have he : k = (1149 : Fin 2425) := Fin.ext h1149
    subst k
    rw [sourceRowsAt1149]
    exact rowSound1149 B hB hF
  · have he : k = (1150 : Fin 2425) := Fin.ext h1150
    subst k
    rw [sourceRowsAt1150]
    exact rowSound1150 B hB hF
  · have he : k = (1151 : Fin 2425) := Fin.ext h1151
    subst k
    rw [sourceRowsAt1151]
    exact rowSound1151 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
