import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources39

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1088 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1088 (mixedVector B) = 0 := by
  have h1178 : mixedVector B (Sum.inr 1178) = Sparse.eval nodeValue1178 (mixedVector B) := by
    change mixedMoment B node1178 node1178Labels = _
    exact sound1178 B hB hF
  have h1181 : mixedVector B (Sum.inr 1181) = Sparse.eval nodeValue1181 (mixedVector B) := by
    change mixedMoment B node1181 node1181Labels = _
    exact sound1181 B hB hF
  have h1182 : mixedVector B (Sum.inr 1182) = Sparse.eval nodeValue1182 (mixedVector B) := by
    change mixedMoment B node1182 node1182Labels = _
    exact sound1182 B hB hF
  have h1188 : mixedVector B (Sum.inr 1188) = Sparse.eval nodeValue1188 (mixedVector B) := by
    change mixedMoment B node1188 node1188Labels = _
    exact sound1188 B hB hF
  have h1257 : mixedVector B (Sum.inr 1257) = Sparse.eval nodeValue1257 (mixedVector B) := by
    change mixedMoment B node1257 node1257Labels = _
    exact sound1257 B hB hF
  have h2672 : mixedVector B (Sum.inr 2672) = Sparse.eval nodeValue2672 (mixedVector B) := by
    change mixedMoment B node2672 node2672Labels = _
    exact sound2672 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm1258, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1178, h1181, h1182, h1188, h1257, h2672, h4088, reducedSource1088] using sourceEq1258 B hB

theorem rowSound1088 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1088 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1088, numericCheck1088, reducedZero1088 B hB hF, mul_zero]

theorem reducedZero1089 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1089 (mixedVector B) = 0 := by
  have h1179 : mixedVector B (Sum.inr 1179) = Sparse.eval nodeValue1179 (mixedVector B) := by
    change mixedMoment B node1179 node1179Labels = _
    exact sound1179 B hB hF
  have h1991 : mixedVector B (Sum.inr 1991) = Sparse.eval nodeValue1991 (mixedVector B) := by
    change mixedMoment B node1991 node1991Labels = _
    exact sound1991 B hB hF
  have h2003 : mixedVector B (Sum.inr 2003) = Sparse.eval nodeValue2003 (mixedVector B) := by
    change mixedMoment B node2003 node2003Labels = _
    exact sound2003 B hB hF
  have h2032 : mixedVector B (Sum.inr 2032) = Sparse.eval nodeValue2032 (mixedVector B) := by
    change mixedMoment B node2032 node2032Labels = _
    exact sound2032 B hB hF
  have h2218 : mixedVector B (Sum.inr 2218) = Sparse.eval nodeValue2218 (mixedVector B) := by
    change mixedMoment B node2218 node2218Labels = _
    exact sound2218 B hB hF
  have h2670 : mixedVector B (Sum.inr 2670) = Sparse.eval nodeValue2670 (mixedVector B) := by
    change mixedMoment B node2670 node2670Labels = _
    exact sound2670 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1259, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1179, h1991, h2003, h2032, h2218, h2670, h4082, reducedSource1089] using sourceEq1259 B hB

theorem rowSound1089 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1089 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1089, numericCheck1089, reducedZero1089 B hB hF, mul_zero]

theorem reducedZero1090 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1090 (mixedVector B) = 0 := by
  have h1195 : mixedVector B (Sum.inr 1195) = Sparse.eval nodeValue1195 (mixedVector B) := by
    change mixedMoment B node1195 node1195Labels = _
    exact sound1195 B hB hF
  have h2449 : mixedVector B (Sum.inr 2449) = Sparse.eval nodeValue2449 (mixedVector B) := by
    change mixedMoment B node2449 node2449Labels = _
    exact sound2449 B hB hF
  have h2469 : mixedVector B (Sum.inr 2469) = Sparse.eval nodeValue2469 (mixedVector B) := by
    change mixedMoment B node2469 node2469Labels = _
    exact sound2469 B hB hF
  have h2691 : mixedVector B (Sum.inr 2691) = Sparse.eval nodeValue2691 (mixedVector B) := by
    change mixedMoment B node2691 node2691Labels = _
    exact sound2691 B hB hF
  have h2694 : mixedVector B (Sum.inr 2694) = Sparse.eval nodeValue2694 (mixedVector B) := by
    change mixedMoment B node2694 node2694Labels = _
    exact sound2694 B hB hF
  have h4090 : mixedVector B (Sum.inr 4090) = Sparse.eval nodeValue4090 (mixedVector B) := by
    change mixedMoment B node4090 node4090Labels = _
    exact sound4090 B hB hF
  simpa only [sourceForm1260, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1195, h2449, h2469, h2691, h2694, h4090, reducedSource1090] using sourceEq1260 B hB

theorem rowSound1090 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1090 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1090, numericCheck1090, reducedZero1090 B hB hF, mul_zero]

theorem reducedZero1091 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1091 (mixedVector B) = 0 := by
  have h1195 : mixedVector B (Sum.inr 1195) = Sparse.eval nodeValue1195 (mixedVector B) := by
    change mixedMoment B node1195 node1195Labels = _
    exact sound1195 B hB hF
  have h1196 : mixedVector B (Sum.inr 1196) = Sparse.eval nodeValue1196 (mixedVector B) := by
    change mixedMoment B node1196 node1196Labels = _
    exact sound1196 B hB hF
  have h1200 : mixedVector B (Sum.inr 1200) = Sparse.eval nodeValue1200 (mixedVector B) := by
    change mixedMoment B node1200 node1200Labels = _
    exact sound1200 B hB hF
  have h1210 : mixedVector B (Sum.inr 1210) = Sparse.eval nodeValue1210 (mixedVector B) := by
    change mixedMoment B node1210 node1210Labels = _
    exact sound1210 B hB hF
  have h2694 : mixedVector B (Sum.inr 2694) = Sparse.eval nodeValue2694 (mixedVector B) := by
    change mixedMoment B node2694 node2694Labels = _
    exact sound2694 B hB hF
  have h4090 : mixedVector B (Sum.inr 4090) = Sparse.eval nodeValue4090 (mixedVector B) := by
    change mixedMoment B node4090 node4090Labels = _
    exact sound4090 B hB hF
  simpa only [sourceForm1261, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1195, h1196, h1200, h1210, h2694, h4090, reducedSource1091] using sourceEq1261 B hB

theorem rowSound1091 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1091 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1091, numericCheck1091, reducedZero1091 B hB hF, mul_zero]

theorem reducedZero1092 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1092 (mixedVector B) = 0 := by
  have h1194 : mixedVector B (Sum.inr 1194) = Sparse.eval nodeValue1194 (mixedVector B) := by
    change mixedMoment B node1194 node1194Labels = _
    exact sound1194 B hB hF
  have h1987 : mixedVector B (Sum.inr 1987) = Sparse.eval nodeValue1987 (mixedVector B) := by
    change mixedMoment B node1987 node1987Labels = _
    exact sound1987 B hB hF
  have h2008 : mixedVector B (Sum.inr 2008) = Sparse.eval nodeValue2008 (mixedVector B) := by
    change mixedMoment B node2008 node2008Labels = _
    exact sound2008 B hB hF
  have h2193 : mixedVector B (Sum.inr 2193) = Sparse.eval nodeValue2193 (mixedVector B) := by
    change mixedMoment B node2193 node2193Labels = _
    exact sound2193 B hB hF
  have h2693 : mixedVector B (Sum.inr 2693) = Sparse.eval nodeValue2693 (mixedVector B) := by
    change mixedMoment B node2693 node2693Labels = _
    exact sound2693 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1262, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1194, h1987, h2008, h2193, h2693, h4080, reducedSource1092] using sourceEq1262 B hB

theorem rowSound1092 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1092 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1092, numericCheck1092, reducedZero1092 B hB hF, mul_zero]

theorem reducedZero1093 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1093 (mixedVector B) = 0 := by
  have h4183 : mixedVector B (Sum.inr 4183) = Sparse.eval nodeValue4183 (mixedVector B) := by
    change mixedMoment B node4183 node4183Labels = _
    exact sound4183 B hB hF
  have h4187 : mixedVector B (Sum.inr 4187) = Sparse.eval nodeValue4187 (mixedVector B) := by
    change mixedMoment B node4187 node4187Labels = _
    exact sound4187 B hB hF
  have h4192 : mixedVector B (Sum.inr 4192) = Sparse.eval nodeValue4192 (mixedVector B) := by
    change mixedMoment B node4192 node4192Labels = _
    exact sound4192 B hB hF
  have h4551 : mixedVector B (Sum.inr 4551) = Sparse.eval nodeValue4551 (mixedVector B) := by
    change mixedMoment B node4551 node4551Labels = _
    exact sound4551 B hB hF
  have h4555 : mixedVector B (Sum.inr 4555) = Sparse.eval nodeValue4555 (mixedVector B) := by
    change mixedMoment B node4555 node4555Labels = _
    exact sound4555 B hB hF
  have h4559 : mixedVector B (Sum.inr 4559) = Sparse.eval nodeValue4559 (mixedVector B) := by
    change mixedMoment B node4559 node4559Labels = _
    exact sound4559 B hB hF
  have h4623 : mixedVector B (Sum.inr 4623) = Sparse.eval nodeValue4623 (mixedVector B) := by
    change mixedMoment B node4623 node4623Labels = _
    exact sound4623 B hB hF
  have h4625 : mixedVector B (Sum.inr 4625) = Sparse.eval nodeValue4625 (mixedVector B) := by
    change mixedMoment B node4625 node4625Labels = _
    exact sound4625 B hB hF
  have h4627 : mixedVector B (Sum.inr 4627) = Sparse.eval nodeValue4627 (mixedVector B) := by
    change mixedMoment B node4627 node4627Labels = _
    exact sound4627 B hB hF
  have h4629 : mixedVector B (Sum.inr 4629) = Sparse.eval nodeValue4629 (mixedVector B) := by
    change mixedMoment B node4629 node4629Labels = _
    exact sound4629 B hB hF
  have h5171 : mixedVector B (Sum.inr 5171) = Sparse.eval nodeValue5171 (mixedVector B) := by
    change mixedMoment B node5171 node5171Labels = _
    exact sound5171 B hB hF
  have h5308 : mixedVector B (Sum.inr 5308) = Sparse.eval nodeValue5308 (mixedVector B) := by
    change mixedMoment B node5308 node5308Labels = _
    exact sound5308 B hB hF
  have h5312 : mixedVector B (Sum.inr 5312) = Sparse.eval nodeValue5312 (mixedVector B) := by
    change mixedMoment B node5312 node5312Labels = _
    exact sound5312 B hB hF
  simpa only [sourceForm1263, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4183, h4187, h4192, h4551, h4555, h4559, h4623, h4625, h4627, h4629, h5171, h5308, h5312, reducedSource1093] using sourceEq1263 B hB

theorem rowSound1093 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1093 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1093, numericCheck1093, reducedZero1093 B hB hF, mul_zero]

theorem reducedZero1094 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1094 (mixedVector B) = 0 := by
  have h611 : mixedVector B (Sum.inr 611) = Sparse.eval nodeValue611 (mixedVector B) := by
    change mixedMoment B node611 node611Labels = _
    exact sound611 B hB hF
  have h615 : mixedVector B (Sum.inr 615) = Sparse.eval nodeValue615 (mixedVector B) := by
    change mixedMoment B node615 node615Labels = _
    exact sound615 B hB hF
  have h620 : mixedVector B (Sum.inr 620) = Sparse.eval nodeValue620 (mixedVector B) := by
    change mixedMoment B node620 node620Labels = _
    exact sound620 B hB hF
  have h1136 : mixedVector B (Sum.inr 1136) = Sparse.eval nodeValue1136 (mixedVector B) := by
    change mixedMoment B node1136 node1136Labels = _
    exact sound1136 B hB hF
  have h1140 : mixedVector B (Sum.inr 1140) = Sparse.eval nodeValue1140 (mixedVector B) := by
    change mixedMoment B node1140 node1140Labels = _
    exact sound1140 B hB hF
  have h1145 : mixedVector B (Sum.inr 1145) = Sparse.eval nodeValue1145 (mixedVector B) := by
    change mixedMoment B node1145 node1145Labels = _
    exact sound1145 B hB hF
  have h1305 : mixedVector B (Sum.inr 1305) = Sparse.eval nodeValue1305 (mixedVector B) := by
    change mixedMoment B node1305 node1305Labels = _
    exact sound1305 B hB hF
  have h1307 : mixedVector B (Sum.inr 1307) = Sparse.eval nodeValue1307 (mixedVector B) := by
    change mixedMoment B node1307 node1307Labels = _
    exact sound1307 B hB hF
  have h1311 : mixedVector B (Sum.inr 1311) = Sparse.eval nodeValue1311 (mixedVector B) := by
    change mixedMoment B node1311 node1311Labels = _
    exact sound1311 B hB hF
  have h1313 : mixedVector B (Sum.inr 1313) = Sparse.eval nodeValue1313 (mixedVector B) := by
    change mixedMoment B node1313 node1313Labels = _
    exact sound1313 B hB hF
  have h2965 : mixedVector B (Sum.inr 2965) = Sparse.eval nodeValue2965 (mixedVector B) := by
    change mixedMoment B node2965 node2965Labels = _
    exact sound2965 B hB hF
  have h3124 : mixedVector B (Sum.inr 3124) = Sparse.eval nodeValue3124 (mixedVector B) := by
    change mixedMoment B node3124 node3124Labels = _
    exact sound3124 B hB hF
  have h3126 : mixedVector B (Sum.inr 3126) = Sparse.eval nodeValue3126 (mixedVector B) := by
    change mixedMoment B node3126 node3126Labels = _
    exact sound3126 B hB hF
  simpa only [sourceForm1264, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h611, h615, h620, h1136, h1140, h1145, h1305, h1307, h1311, h1313, h2965, h3124, h3126, reducedSource1094] using sourceEq1264 B hB

theorem rowSound1094 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1094 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1094, numericCheck1094, reducedZero1094 B hB hF, mul_zero]

theorem reducedZero1095 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1095 (mixedVector B) = 0 := by
  have h4177 : mixedVector B (Sum.inr 4177) = Sparse.eval nodeValue4177 (mixedVector B) := by
    change mixedMoment B node4177 node4177Labels = _
    exact sound4177 B hB hF
  have h4181 : mixedVector B (Sum.inr 4181) = Sparse.eval nodeValue4181 (mixedVector B) := by
    change mixedMoment B node4181 node4181Labels = _
    exact sound4181 B hB hF
  have h4191 : mixedVector B (Sum.inr 4191) = Sparse.eval nodeValue4191 (mixedVector B) := by
    change mixedMoment B node4191 node4191Labels = _
    exact sound4191 B hB hF
  have h4356 : mixedVector B (Sum.inr 4356) = Sparse.eval nodeValue4356 (mixedVector B) := by
    change mixedMoment B node4356 node4356Labels = _
    exact sound4356 B hB hF
  have h4468 : mixedVector B (Sum.inr 4468) = Sparse.eval nodeValue4468 (mixedVector B) := by
    change mixedMoment B node4468 node4468Labels = _
    exact sound4468 B hB hF
  have h4546 : mixedVector B (Sum.inr 4546) = Sparse.eval nodeValue4546 (mixedVector B) := by
    change mixedMoment B node4546 node4546Labels = _
    exact sound4546 B hB hF
  have h4558 : mixedVector B (Sum.inr 4558) = Sparse.eval nodeValue4558 (mixedVector B) := by
    change mixedMoment B node4558 node4558Labels = _
    exact sound4558 B hB hF
  have h4608 : mixedVector B (Sum.inr 4608) = Sparse.eval nodeValue4608 (mixedVector B) := by
    change mixedMoment B node4608 node4608Labels = _
    exact sound4608 B hB hF
  have h4624 : mixedVector B (Sum.inr 4624) = Sparse.eval nodeValue4624 (mixedVector B) := by
    change mixedMoment B node4624 node4624Labels = _
    exact sound4624 B hB hF
  have h4628 : mixedVector B (Sum.inr 4628) = Sparse.eval nodeValue4628 (mixedVector B) := by
    change mixedMoment B node4628 node4628Labels = _
    exact sound4628 B hB hF
  have h5174 : mixedVector B (Sum.inr 5174) = Sparse.eval nodeValue5174 (mixedVector B) := by
    change mixedMoment B node5174 node5174Labels = _
    exact sound5174 B hB hF
  have h5296 : mixedVector B (Sum.inr 5296) = Sparse.eval nodeValue5296 (mixedVector B) := by
    change mixedMoment B node5296 node5296Labels = _
    exact sound5296 B hB hF
  have h5309 : mixedVector B (Sum.inr 5309) = Sparse.eval nodeValue5309 (mixedVector B) := by
    change mixedMoment B node5309 node5309Labels = _
    exact sound5309 B hB hF
  simpa only [sourceForm1265, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4177, h4181, h4191, h4356, h4468, h4546, h4558, h4608, h4624, h4628, h5174, h5296, h5309, reducedSource1095] using sourceEq1265 B hB

theorem rowSound1095 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1095 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1095, numericCheck1095, reducedZero1095 B hB hF, mul_zero]

theorem reducedZero1096 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1096 (mixedVector B) = 0 := by
  have h605 : mixedVector B (Sum.inr 605) = Sparse.eval nodeValue605 (mixedVector B) := by
    change mixedMoment B node605 node605Labels = _
    exact sound605 B hB hF
  have h609 : mixedVector B (Sum.inr 609) = Sparse.eval nodeValue609 (mixedVector B) := by
    change mixedMoment B node609 node609Labels = _
    exact sound609 B hB hF
  have h619 : mixedVector B (Sum.inr 619) = Sparse.eval nodeValue619 (mixedVector B) := by
    change mixedMoment B node619 node619Labels = _
    exact sound619 B hB hF
  have h934 : mixedVector B (Sum.inr 934) = Sparse.eval nodeValue934 (mixedVector B) := by
    change mixedMoment B node934 node934Labels = _
    exact sound934 B hB hF
  have h1051 : mixedVector B (Sum.inr 1051) = Sparse.eval nodeValue1051 (mixedVector B) := by
    change mixedMoment B node1051 node1051Labels = _
    exact sound1051 B hB hF
  have h1131 : mixedVector B (Sum.inr 1131) = Sparse.eval nodeValue1131 (mixedVector B) := by
    change mixedMoment B node1131 node1131Labels = _
    exact sound1131 B hB hF
  have h1144 : mixedVector B (Sum.inr 1144) = Sparse.eval nodeValue1144 (mixedVector B) := by
    change mixedMoment B node1144 node1144Labels = _
    exact sound1144 B hB hF
  have h1242 : mixedVector B (Sum.inr 1242) = Sparse.eval nodeValue1242 (mixedVector B) := by
    change mixedMoment B node1242 node1242Labels = _
    exact sound1242 B hB hF
  have h1301 : mixedVector B (Sum.inr 1301) = Sparse.eval nodeValue1301 (mixedVector B) := by
    change mixedMoment B node1301 node1301Labels = _
    exact sound1301 B hB hF
  have h1312 : mixedVector B (Sum.inr 1312) = Sparse.eval nodeValue1312 (mixedVector B) := by
    change mixedMoment B node1312 node1312Labels = _
    exact sound1312 B hB hF
  have h2601 : mixedVector B (Sum.inr 2601) = Sparse.eval nodeValue2601 (mixedVector B) := by
    change mixedMoment B node2601 node2601Labels = _
    exact sound2601 B hB hF
  have h2770 : mixedVector B (Sum.inr 2770) = Sparse.eval nodeValue2770 (mixedVector B) := by
    change mixedMoment B node2770 node2770Labels = _
    exact sound2770 B hB hF
  have h3123 : mixedVector B (Sum.inr 3123) = Sparse.eval nodeValue3123 (mixedVector B) := by
    change mixedMoment B node3123 node3123Labels = _
    exact sound3123 B hB hF
  simpa only [sourceForm1266, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h605, h609, h619, h934, h1051, h1131, h1144, h1242, h1301, h1312, h2601, h2770, h3123, reducedSource1096] using sourceEq1266 B hB

theorem rowSound1096 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1096 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1096, numericCheck1096, reducedZero1096 B hB hF, mul_zero]

theorem reducedZero1097 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1097 (mixedVector B) = 0 := by
  have h4460 : mixedVector B (Sum.inr 4460) = Sparse.eval nodeValue4460 (mixedVector B) := by
    change mixedMoment B node4460 node4460Labels = _
    exact sound4460 B hB hF
  have h4463 : mixedVector B (Sum.inr 4463) = Sparse.eval nodeValue4463 (mixedVector B) := by
    change mixedMoment B node4463 node4463Labels = _
    exact sound4463 B hB hF
  have h4501 : mixedVector B (Sum.inr 4501) = Sparse.eval nodeValue4501 (mixedVector B) := by
    change mixedMoment B node4501 node4501Labels = _
    exact sound4501 B hB hF
  have h4505 : mixedVector B (Sum.inr 4505) = Sparse.eval nodeValue4505 (mixedVector B) := by
    change mixedMoment B node4505 node4505Labels = _
    exact sound4505 B hB hF
  have h4507 : mixedVector B (Sum.inr 4507) = Sparse.eval nodeValue4507 (mixedVector B) := by
    change mixedMoment B node4507 node4507Labels = _
    exact sound4507 B hB hF
  have h4591 : mixedVector B (Sum.inr 4591) = Sparse.eval nodeValue4591 (mixedVector B) := by
    change mixedMoment B node4591 node4591Labels = _
    exact sound4591 B hB hF
  have h4605 : mixedVector B (Sum.inr 4605) = Sparse.eval nodeValue4605 (mixedVector B) := by
    change mixedMoment B node4605 node4605Labels = _
    exact sound4605 B hB hF
  have h4608 : mixedVector B (Sum.inr 4608) = Sparse.eval nodeValue4608 (mixedVector B) := by
    change mixedMoment B node4608 node4608Labels = _
    exact sound4608 B hB hF
  have h4609 : mixedVector B (Sum.inr 4609) = Sparse.eval nodeValue4609 (mixedVector B) := by
    change mixedMoment B node4609 node4609Labels = _
    exact sound4609 B hB hF
  have h4621 : mixedVector B (Sum.inr 4621) = Sparse.eval nodeValue4621 (mixedVector B) := by
    change mixedMoment B node4621 node4621Labels = _
    exact sound4621 B hB hF
  have h4625 : mixedVector B (Sum.inr 4625) = Sparse.eval nodeValue4625 (mixedVector B) := by
    change mixedMoment B node4625 node4625Labels = _
    exact sound4625 B hB hF
  simpa only [sourceForm1267, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4460, h4463, h4501, h4505, h4507, h4591, h4605, h4608, h4609, h4621, h4625, reducedSource1097] using sourceEq1267 B hB

theorem rowSound1097 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1097 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1097, numericCheck1097, reducedZero1097 B hB hF, mul_zero]

theorem reducedZero1098 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1098 (mixedVector B) = 0 := by
  have h1046 : mixedVector B (Sum.inr 1046) = Sparse.eval nodeValue1046 (mixedVector B) := by
    change mixedMoment B node1046 node1046Labels = _
    exact sound1046 B hB hF
  have h1089 : mixedVector B (Sum.inr 1089) = Sparse.eval nodeValue1089 (mixedVector B) := by
    change mixedMoment B node1089 node1089Labels = _
    exact sound1089 B hB hF
  have h1091 : mixedVector B (Sum.inr 1091) = Sparse.eval nodeValue1091 (mixedVector B) := by
    change mixedMoment B node1091 node1091Labels = _
    exact sound1091 B hB hF
  have h1217 : mixedVector B (Sum.inr 1217) = Sparse.eval nodeValue1217 (mixedVector B) := by
    change mixedMoment B node1217 node1217Labels = _
    exact sound1217 B hB hF
  have h1242 : mixedVector B (Sum.inr 1242) = Sparse.eval nodeValue1242 (mixedVector B) := by
    change mixedMoment B node1242 node1242Labels = _
    exact sound1242 B hB hF
  have h1243 : mixedVector B (Sum.inr 1243) = Sparse.eval nodeValue1243 (mixedVector B) := by
    change mixedMoment B node1243 node1243Labels = _
    exact sound1243 B hB hF
  have h1269 : mixedVector B (Sum.inr 1269) = Sparse.eval nodeValue1269 (mixedVector B) := by
    change mixedMoment B node1269 node1269Labels = _
    exact sound1269 B hB hF
  have h1271 : mixedVector B (Sum.inr 1271) = Sparse.eval nodeValue1271 (mixedVector B) := by
    change mixedMoment B node1271 node1271Labels = _
    exact sound1271 B hB hF
  have h1304 : mixedVector B (Sum.inr 1304) = Sparse.eval nodeValue1304 (mixedVector B) := by
    change mixedMoment B node1304 node1304Labels = _
    exact sound1304 B hB hF
  have h1308 : mixedVector B (Sum.inr 1308) = Sparse.eval nodeValue1308 (mixedVector B) := by
    change mixedMoment B node1308 node1308Labels = _
    exact sound1308 B hB hF
  have h1416 : mixedVector B (Sum.inr 1416) = Sparse.eval nodeValue1416 (mixedVector B) := by
    change mixedMoment B node1416 node1416Labels = _
    exact sound1416 B hB hF
  have h1450 : mixedVector B (Sum.inr 1450) = Sparse.eval nodeValue1450 (mixedVector B) := by
    change mixedMoment B node1450 node1450Labels = _
    exact sound1450 B hB hF
  have h1452 : mixedVector B (Sum.inr 1452) = Sparse.eval nodeValue1452 (mixedVector B) := by
    change mixedMoment B node1452 node1452Labels = _
    exact sound1452 B hB hF
  simpa only [sourceForm1268, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1046, h1089, h1091, h1217, h1242, h1243, h1269, h1271, h1304, h1308, h1416, h1450, h1452, reducedSource1098] using sourceEq1268 B hB

theorem rowSound1098 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1098 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1098, numericCheck1098, reducedZero1098 B hB hF, mul_zero]

theorem reducedZero1099 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1099 (mixedVector B) = 0 := by
  have h1750 : mixedVector B (Sum.inr 1750) = Sparse.eval nodeValue1750 (mixedVector B) := by
    change mixedMoment B node1750 node1750Labels = _
    exact sound1750 B hB hF
  have h1754 : mixedVector B (Sum.inr 1754) = Sparse.eval nodeValue1754 (mixedVector B) := by
    change mixedMoment B node1754 node1754Labels = _
    exact sound1754 B hB hF
  have h1756 : mixedVector B (Sum.inr 1756) = Sparse.eval nodeValue1756 (mixedVector B) := by
    change mixedMoment B node1756 node1756Labels = _
    exact sound1756 B hB hF
  have h3310 : mixedVector B (Sum.inr 3310) = Sparse.eval nodeValue3310 (mixedVector B) := by
    change mixedMoment B node3310 node3310Labels = _
    exact sound3310 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1269, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1750, h1754, h1756, h3310, h4070, reducedSource1099] using sourceEq1269 B hB

theorem rowSound1099 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1099 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1099, numericCheck1099, reducedZero1099 B hB hF, mul_zero]

theorem reducedZero1100 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1100 (mixedVector B) = 0 := by
  have h1725 : mixedVector B (Sum.inr 1725) = Sparse.eval nodeValue1725 (mixedVector B) := by
    change mixedMoment B node1725 node1725Labels = _
    exact sound1725 B hB hF
  have h1730 : mixedVector B (Sum.inr 1730) = Sparse.eval nodeValue1730 (mixedVector B) := by
    change mixedMoment B node1730 node1730Labels = _
    exact sound1730 B hB hF
  have h1754 : mixedVector B (Sum.inr 1754) = Sparse.eval nodeValue1754 (mixedVector B) := by
    change mixedMoment B node1754 node1754Labels = _
    exact sound1754 B hB hF
  have h3310 : mixedVector B (Sum.inr 3310) = Sparse.eval nodeValue3310 (mixedVector B) := by
    change mixedMoment B node3310 node3310Labels = _
    exact sound3310 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1270, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1725, h1730, h1754, h3310, h4070, reducedSource1100] using sourceEq1270 B hB

theorem rowSound1100 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1100 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1100, numericCheck1100, reducedZero1100 B hB hF, mul_zero]

theorem reducedZero1101 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1101 (mixedVector B) = 0 := by
  have h1754 : mixedVector B (Sum.inr 1754) = Sparse.eval nodeValue1754 (mixedVector B) := by
    change mixedMoment B node1754 node1754Labels = _
    exact sound1754 B hB hF
  have h3300 : mixedVector B (Sum.inr 3300) = Sparse.eval nodeValue3300 (mixedVector B) := by
    change mixedMoment B node3300 node3300Labels = _
    exact sound3300 B hB hF
  have h3310 : mixedVector B (Sum.inr 3310) = Sparse.eval nodeValue3310 (mixedVector B) := by
    change mixedMoment B node3310 node3310Labels = _
    exact sound3310 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1271, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1754, h3300, h3310, h4070, reducedSource1101] using sourceEq1271 B hB

theorem rowSound1101 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1101 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1101, numericCheck1101, reducedZero1101 B hB hF, mul_zero]

theorem reducedZero1102 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1102 (mixedVector B) = 0 := by
  have h4184 : mixedVector B (Sum.inr 4184) = Sparse.eval nodeValue4184 (mixedVector B) := by
    change mixedMoment B node4184 node4184Labels = _
    exact sound4184 B hB hF
  have h4189 : mixedVector B (Sum.inr 4189) = Sparse.eval nodeValue4189 (mixedVector B) := by
    change mixedMoment B node4189 node4189Labels = _
    exact sound4189 B hB hF
  have h4193 : mixedVector B (Sum.inr 4193) = Sparse.eval nodeValue4193 (mixedVector B) := by
    change mixedMoment B node4193 node4193Labels = _
    exact sound4193 B hB hF
  have h4370 : mixedVector B (Sum.inr 4370) = Sparse.eval nodeValue4370 (mixedVector B) := by
    change mixedMoment B node4370 node4370Labels = _
    exact sound4370 B hB hF
  have h4468 : mixedVector B (Sum.inr 4468) = Sparse.eval nodeValue4468 (mixedVector B) := by
    change mixedMoment B node4468 node4468Labels = _
    exact sound4468 B hB hF
  have h4552 : mixedVector B (Sum.inr 4552) = Sparse.eval nodeValue4552 (mixedVector B) := by
    change mixedMoment B node4552 node4552Labels = _
    exact sound4552 B hB hF
  have h4560 : mixedVector B (Sum.inr 4560) = Sparse.eval nodeValue4560 (mixedVector B) := by
    change mixedMoment B node4560 node4560Labels = _
    exact sound4560 B hB hF
  have h4605 : mixedVector B (Sum.inr 4605) = Sparse.eval nodeValue4605 (mixedVector B) := by
    change mixedMoment B node4605 node4605Labels = _
    exact sound4605 B hB hF
  have h4617 : mixedVector B (Sum.inr 4617) = Sparse.eval nodeValue4617 (mixedVector B) := by
    change mixedMoment B node4617 node4617Labels = _
    exact sound4617 B hB hF
  have h4626 : mixedVector B (Sum.inr 4626) = Sparse.eval nodeValue4626 (mixedVector B) := by
    change mixedMoment B node4626 node4626Labels = _
    exact sound4626 B hB hF
  have h4868 : mixedVector B (Sum.inr 4868) = Sparse.eval nodeValue4868 (mixedVector B) := by
    change mixedMoment B node4868 node4868Labels = _
    exact sound4868 B hB hF
  have h4897 : mixedVector B (Sum.inr 4897) = Sparse.eval nodeValue4897 (mixedVector B) := by
    change mixedMoment B node4897 node4897Labels = _
    exact sound4897 B hB hF
  have h5305 : mixedVector B (Sum.inr 5305) = Sparse.eval nodeValue5305 (mixedVector B) := by
    change mixedMoment B node5305 node5305Labels = _
    exact sound5305 B hB hF
  simpa only [sourceForm1272, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4184, h4189, h4193, h4370, h4468, h4552, h4560, h4605, h4617, h4626, h4868, h4897, h5305, reducedSource1102] using sourceEq1272 B hB

theorem rowSound1102 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1102 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1102, numericCheck1102, reducedZero1102 B hB hF, mul_zero]

theorem reducedZero1103 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1103 (mixedVector B) = 0 := by
  have h612 : mixedVector B (Sum.inr 612) = Sparse.eval nodeValue612 (mixedVector B) := by
    change mixedMoment B node612 node612Labels = _
    exact sound612 B hB hF
  have h617 : mixedVector B (Sum.inr 617) = Sparse.eval nodeValue617 (mixedVector B) := by
    change mixedMoment B node617 node617Labels = _
    exact sound617 B hB hF
  have h621 : mixedVector B (Sum.inr 621) = Sparse.eval nodeValue621 (mixedVector B) := by
    change mixedMoment B node621 node621Labels = _
    exact sound621 B hB hF
  have h1137 : mixedVector B (Sum.inr 1137) = Sparse.eval nodeValue1137 (mixedVector B) := by
    change mixedMoment B node1137 node1137Labels = _
    exact sound1137 B hB hF
  have h1142 : mixedVector B (Sum.inr 1142) = Sparse.eval nodeValue1142 (mixedVector B) := by
    change mixedMoment B node1142 node1142Labels = _
    exact sound1142 B hB hF
  have h1146 : mixedVector B (Sum.inr 1146) = Sparse.eval nodeValue1146 (mixedVector B) := by
    change mixedMoment B node1146 node1146Labels = _
    exact sound1146 B hB hF
  have h1271 : mixedVector B (Sum.inr 1271) = Sparse.eval nodeValue1271 (mixedVector B) := by
    change mixedMoment B node1271 node1271Labels = _
    exact sound1271 B hB hF
  have h1275 : mixedVector B (Sum.inr 1275) = Sparse.eval nodeValue1275 (mixedVector B) := by
    change mixedMoment B node1275 node1275Labels = _
    exact sound1275 B hB hF
  have h1306 : mixedVector B (Sum.inr 1306) = Sparse.eval nodeValue1306 (mixedVector B) := by
    change mixedMoment B node1306 node1306Labels = _
    exact sound1306 B hB hF
  have h1310 : mixedVector B (Sum.inr 1310) = Sparse.eval nodeValue1310 (mixedVector B) := by
    change mixedMoment B node1310 node1310Labels = _
    exact sound1310 B hB hF
  have h2966 : mixedVector B (Sum.inr 2966) = Sparse.eval nodeValue2966 (mixedVector B) := by
    change mixedMoment B node2966 node2966Labels = _
    exact sound2966 B hB hF
  have h3114 : mixedVector B (Sum.inr 3114) = Sparse.eval nodeValue3114 (mixedVector B) := by
    change mixedMoment B node3114 node3114Labels = _
    exact sound3114 B hB hF
  have h3125 : mixedVector B (Sum.inr 3125) = Sparse.eval nodeValue3125 (mixedVector B) := by
    change mixedMoment B node3125 node3125Labels = _
    exact sound3125 B hB hF
  simpa only [sourceForm1273, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h612, h617, h621, h1137, h1142, h1146, h1271, h1275, h1306, h1310, h2966, h3114, h3125, reducedSource1103] using sourceEq1273 B hB

theorem rowSound1103 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1103 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1103, numericCheck1103, reducedZero1103 B hB hF, mul_zero]

theorem sourceRowsAt1088 : MixedData.sourceRows (1088 : Fin 2425) =
    MixedData.row1088 := by decide +kernel

theorem sourceRowsAt1089 : MixedData.sourceRows (1089 : Fin 2425) =
    MixedData.row1089 := by decide +kernel

theorem sourceRowsAt1090 : MixedData.sourceRows (1090 : Fin 2425) =
    MixedData.row1090 := by decide +kernel

theorem sourceRowsAt1091 : MixedData.sourceRows (1091 : Fin 2425) =
    MixedData.row1091 := by decide +kernel

theorem sourceRowsAt1092 : MixedData.sourceRows (1092 : Fin 2425) =
    MixedData.row1092 := by decide +kernel

theorem sourceRowsAt1093 : MixedData.sourceRows (1093 : Fin 2425) =
    MixedData.row1093 := by decide +kernel

theorem sourceRowsAt1094 : MixedData.sourceRows (1094 : Fin 2425) =
    MixedData.row1094 := by decide +kernel

theorem sourceRowsAt1095 : MixedData.sourceRows (1095 : Fin 2425) =
    MixedData.row1095 := by decide +kernel

theorem sourceRowsAt1096 : MixedData.sourceRows (1096 : Fin 2425) =
    MixedData.row1096 := by decide +kernel

theorem sourceRowsAt1097 : MixedData.sourceRows (1097 : Fin 2425) =
    MixedData.row1097 := by decide +kernel

theorem sourceRowsAt1098 : MixedData.sourceRows (1098 : Fin 2425) =
    MixedData.row1098 := by decide +kernel

theorem sourceRowsAt1099 : MixedData.sourceRows (1099 : Fin 2425) =
    MixedData.row1099 := by decide +kernel

theorem sourceRowsAt1100 : MixedData.sourceRows (1100 : Fin 2425) =
    MixedData.row1100 := by decide +kernel

theorem sourceRowsAt1101 : MixedData.sourceRows (1101 : Fin 2425) =
    MixedData.row1101 := by decide +kernel

theorem sourceRowsAt1102 : MixedData.sourceRows (1102 : Fin 2425) =
    MixedData.row1102 := by decide +kernel

theorem sourceRowsAt1103 : MixedData.sourceRows (1103 : Fin 2425) =
    MixedData.row1103 := by decide +kernel

theorem chunkSound68 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 68) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1088 ∨ k.val = 1089 ∨ k.val = 1090 ∨ k.val = 1091 ∨ k.val = 1092 ∨ k.val = 1093 ∨ k.val = 1094 ∨ k.val = 1095 ∨ k.val = 1096 ∨ k.val = 1097 ∨ k.val = 1098 ∨ k.val = 1099 ∨ k.val = 1100 ∨ k.val = 1101 ∨ k.val = 1102 ∨ k.val = 1103 := by omega
  rcases heq with h1088 | h1089 | h1090 | h1091 | h1092 | h1093 | h1094 | h1095 | h1096 | h1097 | h1098 | h1099 | h1100 | h1101 | h1102 | h1103
  · have he : k = (1088 : Fin 2425) := Fin.ext h1088
    subst k
    rw [sourceRowsAt1088]
    exact rowSound1088 B hB hF
  · have he : k = (1089 : Fin 2425) := Fin.ext h1089
    subst k
    rw [sourceRowsAt1089]
    exact rowSound1089 B hB hF
  · have he : k = (1090 : Fin 2425) := Fin.ext h1090
    subst k
    rw [sourceRowsAt1090]
    exact rowSound1090 B hB hF
  · have he : k = (1091 : Fin 2425) := Fin.ext h1091
    subst k
    rw [sourceRowsAt1091]
    exact rowSound1091 B hB hF
  · have he : k = (1092 : Fin 2425) := Fin.ext h1092
    subst k
    rw [sourceRowsAt1092]
    exact rowSound1092 B hB hF
  · have he : k = (1093 : Fin 2425) := Fin.ext h1093
    subst k
    rw [sourceRowsAt1093]
    exact rowSound1093 B hB hF
  · have he : k = (1094 : Fin 2425) := Fin.ext h1094
    subst k
    rw [sourceRowsAt1094]
    exact rowSound1094 B hB hF
  · have he : k = (1095 : Fin 2425) := Fin.ext h1095
    subst k
    rw [sourceRowsAt1095]
    exact rowSound1095 B hB hF
  · have he : k = (1096 : Fin 2425) := Fin.ext h1096
    subst k
    rw [sourceRowsAt1096]
    exact rowSound1096 B hB hF
  · have he : k = (1097 : Fin 2425) := Fin.ext h1097
    subst k
    rw [sourceRowsAt1097]
    exact rowSound1097 B hB hF
  · have he : k = (1098 : Fin 2425) := Fin.ext h1098
    subst k
    rw [sourceRowsAt1098]
    exact rowSound1098 B hB hF
  · have he : k = (1099 : Fin 2425) := Fin.ext h1099
    subst k
    rw [sourceRowsAt1099]
    exact rowSound1099 B hB hF
  · have he : k = (1100 : Fin 2425) := Fin.ext h1100
    subst k
    rw [sourceRowsAt1100]
    exact rowSound1100 B hB hF
  · have he : k = (1101 : Fin 2425) := Fin.ext h1101
    subst k
    rw [sourceRowsAt1101]
    exact rowSound1101 B hB hF
  · have he : k = (1102 : Fin 2425) := Fin.ext h1102
    subst k
    rw [sourceRowsAt1102]
    exact rowSound1102 B hB hF
  · have he : k = (1103 : Fin 2425) := Fin.ext h1103
    subst k
    rw [sourceRowsAt1103]
    exact rowSound1103 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
