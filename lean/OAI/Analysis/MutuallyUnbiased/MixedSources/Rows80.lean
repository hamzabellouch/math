import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources47

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1280 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1280 (mixedVector B) = 0 := by
  have h1192 : mixedVector B (Sum.inr 1192) = Sparse.eval nodeValue1192 (mixedVector B) := by
    change mixedMoment B node1192 node1192Labels = _
    exact sound1192 B hB hF
  have h2410 : mixedVector B (Sum.inr 2410) = Sparse.eval nodeValue2410 (mixedVector B) := by
    change mixedMoment B node2410 node2410Labels = _
    exact sound2410 B hB hF
  have h2538 : mixedVector B (Sum.inr 2538) = Sparse.eval nodeValue2538 (mixedVector B) := by
    change mixedMoment B node2538 node2538Labels = _
    exact sound2538 B hB hF
  have h2685 : mixedVector B (Sum.inr 2685) = Sparse.eval nodeValue2685 (mixedVector B) := by
    change mixedMoment B node2685 node2685Labels = _
    exact sound2685 B hB hF
  have h2687 : mixedVector B (Sum.inr 2687) = Sparse.eval nodeValue2687 (mixedVector B) := by
    change mixedMoment B node2687 node2687Labels = _
    exact sound2687 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1495, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1192, h2410, h2538, h2685, h2687, h4082, reducedSource1280] using sourceEq1495 B hB

theorem rowSound1280 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1280 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1280, numericCheck1280, reducedZero1280 B hB hF, mul_zero]

theorem reducedZero1281 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1281 (mixedVector B) = 0 := by
  have h1193 : mixedVector B (Sum.inr 1193) = Sparse.eval nodeValue1193 (mixedVector B) := by
    change mixedMoment B node1193 node1193Labels = _
    exact sound1193 B hB hF
  have h2411 : mixedVector B (Sum.inr 2411) = Sparse.eval nodeValue2411 (mixedVector B) := by
    change mixedMoment B node2411 node2411Labels = _
    exact sound2411 B hB hF
  have h2539 : mixedVector B (Sum.inr 2539) = Sparse.eval nodeValue2539 (mixedVector B) := by
    change mixedMoment B node2539 node2539Labels = _
    exact sound2539 B hB hF
  have h2686 : mixedVector B (Sum.inr 2686) = Sparse.eval nodeValue2686 (mixedVector B) := by
    change mixedMoment B node2686 node2686Labels = _
    exact sound2686 B hB hF
  have h4089 : mixedVector B (Sum.inr 4089) = Sparse.eval nodeValue4089 (mixedVector B) := by
    change mixedMoment B node4089 node4089Labels = _
    exact sound4089 B hB hF
  simpa only [sourceForm1496, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1193, h2411, h2539, h2686, h4089, reducedSource1281] using sourceEq1496 B hB

theorem rowSound1281 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1281 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1281, numericCheck1281, reducedZero1281 B hB hF, mul_zero]

theorem reducedZero1282 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1282 (mixedVector B) = 0 := by
  have h1099 : mixedVector B (Sum.inr 1099) = Sparse.eval nodeValue1099 (mixedVector B) := by
    change mixedMoment B node1099 node1099Labels = _
    exact sound1099 B hB hF
  have h1104 : mixedVector B (Sum.inr 1104) = Sparse.eval nodeValue1104 (mixedVector B) := by
    change mixedMoment B node1104 node1104Labels = _
    exact sound1104 B hB hF
  have h1193 : mixedVector B (Sum.inr 1193) = Sparse.eval nodeValue1193 (mixedVector B) := by
    change mixedMoment B node1193 node1193Labels = _
    exact sound1193 B hB hF
  have h2411 : mixedVector B (Sum.inr 2411) = Sparse.eval nodeValue2411 (mixedVector B) := by
    change mixedMoment B node2411 node2411Labels = _
    exact sound2411 B hB hF
  have h4089 : mixedVector B (Sum.inr 4089) = Sparse.eval nodeValue4089 (mixedVector B) := by
    change mixedMoment B node4089 node4089Labels = _
    exact sound4089 B hB hF
  simpa only [sourceForm1497, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1099, h1104, h1193, h2411, h4089, reducedSource1282] using sourceEq1497 B hB

theorem rowSound1282 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1282 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1282, numericCheck1282, reducedZero1282 B hB hF, mul_zero]

theorem reducedZero1283 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1283 (mixedVector B) = 0 := by
  have h1204 : mixedVector B (Sum.inr 1204) = Sparse.eval nodeValue1204 (mixedVector B) := by
    change mixedMoment B node1204 node1204Labels = _
    exact sound1204 B hB hF
  have h2467 : mixedVector B (Sum.inr 2467) = Sparse.eval nodeValue2467 (mixedVector B) := by
    change mixedMoment B node2467 node2467Labels = _
    exact sound2467 B hB hF
  have h2540 : mixedVector B (Sum.inr 2540) = Sparse.eval nodeValue2540 (mixedVector B) := by
    change mixedMoment B node2540 node2540Labels = _
    exact sound2540 B hB hF
  have h2704 : mixedVector B (Sum.inr 2704) = Sparse.eval nodeValue2704 (mixedVector B) := by
    change mixedMoment B node2704 node2704Labels = _
    exact sound2704 B hB hF
  have h2706 : mixedVector B (Sum.inr 2706) = Sparse.eval nodeValue2706 (mixedVector B) := by
    change mixedMoment B node2706 node2706Labels = _
    exact sound2706 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1499, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1204, h2467, h2540, h2704, h2706, h4080, reducedSource1283] using sourceEq1499 B hB

theorem rowSound1283 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1283 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1283, numericCheck1283, reducedZero1283 B hB hF, mul_zero]

theorem reducedZero1284 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1284 (mixedVector B) = 0 := by
  have h1205 : mixedVector B (Sum.inr 1205) = Sparse.eval nodeValue1205 (mixedVector B) := by
    change mixedMoment B node1205 node1205Labels = _
    exact sound1205 B hB hF
  have h2468 : mixedVector B (Sum.inr 2468) = Sparse.eval nodeValue2468 (mixedVector B) := by
    change mixedMoment B node2468 node2468Labels = _
    exact sound2468 B hB hF
  have h2541 : mixedVector B (Sum.inr 2541) = Sparse.eval nodeValue2541 (mixedVector B) := by
    change mixedMoment B node2541 node2541Labels = _
    exact sound2541 B hB hF
  have h2705 : mixedVector B (Sum.inr 2705) = Sparse.eval nodeValue2705 (mixedVector B) := by
    change mixedMoment B node2705 node2705Labels = _
    exact sound2705 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm1500, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1205, h2468, h2541, h2705, h4088, reducedSource1284] using sourceEq1500 B hB

theorem rowSound1284 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1284 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1284, numericCheck1284, reducedZero1284 B hB hF, mul_zero]

theorem reducedZero1285 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1285 (mixedVector B) = 0 := by
  have h1106 : mixedVector B (Sum.inr 1106) = Sparse.eval nodeValue1106 (mixedVector B) := by
    change mixedMoment B node1106 node1106Labels = _
    exact sound1106 B hB hF
  have h1110 : mixedVector B (Sum.inr 1110) = Sparse.eval nodeValue1110 (mixedVector B) := by
    change mixedMoment B node1110 node1110Labels = _
    exact sound1110 B hB hF
  have h1124 : mixedVector B (Sum.inr 1124) = Sparse.eval nodeValue1124 (mixedVector B) := by
    change mixedMoment B node1124 node1124Labels = _
    exact sound1124 B hB hF
  have h1205 : mixedVector B (Sum.inr 1205) = Sparse.eval nodeValue1205 (mixedVector B) := by
    change mixedMoment B node1205 node1205Labels = _
    exact sound1205 B hB hF
  have h2468 : mixedVector B (Sum.inr 2468) = Sparse.eval nodeValue2468 (mixedVector B) := by
    change mixedMoment B node2468 node2468Labels = _
    exact sound2468 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm1501, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1106, h1110, h1124, h1205, h2468, h4088, reducedSource1285] using sourceEq1501 B hB

theorem rowSound1285 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1285 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1285, numericCheck1285, reducedZero1285 B hB hF, mul_zero]

theorem reducedZero1286 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1286 (mixedVector B) = 0 := by
  have h1062 : mixedVector B (Sum.inr 1062) = Sparse.eval nodeValue1062 (mixedVector B) := by
    change mixedMoment B node1062 node1062Labels = _
    exact sound1062 B hB hF
  have h2038 : mixedVector B (Sum.inr 2038) = Sparse.eval nodeValue2038 (mixedVector B) := by
    change mixedMoment B node2038 node2038Labels = _
    exact sound2038 B hB hF
  have h2137 : mixedVector B (Sum.inr 2137) = Sparse.eval nodeValue2137 (mixedVector B) := by
    change mixedMoment B node2137 node2137Labels = _
    exact sound2137 B hB hF
  have h2276 : mixedVector B (Sum.inr 2276) = Sparse.eval nodeValue2276 (mixedVector B) := by
    change mixedMoment B node2276 node2276Labels = _
    exact sound2276 B hB hF
  have h2280 : mixedVector B (Sum.inr 2280) = Sparse.eval nodeValue2280 (mixedVector B) := by
    change mixedMoment B node2280 node2280Labels = _
    exact sound2280 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1503, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1062, h2038, h2137, h2276, h2280, h4082, reducedSource1286] using sourceEq1503 B hB

theorem rowSound1286 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1286 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1286, numericCheck1286, reducedZero1286 B hB hF, mul_zero]

theorem reducedZero1287 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1287 (mixedVector B) = 0 := by
  have h992 : mixedVector B (Sum.inr 992) = Sparse.eval nodeValue992 (mixedVector B) := by
    change mixedMoment B node992 node992Labels = _
    exact sound992 B hB hF
  have h1928 : mixedVector B (Sum.inr 1928) = Sparse.eval nodeValue1928 (mixedVector B) := by
    change mixedMoment B node1928 node1928Labels = _
    exact sound1928 B hB hF
  have h1993 : mixedVector B (Sum.inr 1993) = Sparse.eval nodeValue1993 (mixedVector B) := by
    change mixedMoment B node1993 node1993Labels = _
    exact sound1993 B hB hF
  have h2122 : mixedVector B (Sum.inr 2122) = Sparse.eval nodeValue2122 (mixedVector B) := by
    change mixedMoment B node2122 node2122Labels = _
    exact sound2122 B hB hF
  have h2215 : mixedVector B (Sum.inr 2215) = Sparse.eval nodeValue2215 (mixedVector B) := by
    change mixedMoment B node2215 node2215Labels = _
    exact sound2215 B hB hF
  have h2217 : mixedVector B (Sum.inr 2217) = Sparse.eval nodeValue2217 (mixedVector B) := by
    change mixedMoment B node2217 node2217Labels = _
    exact sound2217 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1504, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h992, h1928, h1993, h2122, h2215, h2217, h4082, reducedSource1287] using sourceEq1504 B hB

theorem rowSound1287 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1287 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1287, numericCheck1287, reducedZero1287 B hB hF, mul_zero]

theorem reducedZero1288 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1288 (mixedVector B) = 0 := by
  have h993 : mixedVector B (Sum.inr 993) = Sparse.eval nodeValue993 (mixedVector B) := by
    change mixedMoment B node993 node993Labels = _
    exact sound993 B hB hF
  have h1929 : mixedVector B (Sum.inr 1929) = Sparse.eval nodeValue1929 (mixedVector B) := by
    change mixedMoment B node1929 node1929Labels = _
    exact sound1929 B hB hF
  have h1994 : mixedVector B (Sum.inr 1994) = Sparse.eval nodeValue1994 (mixedVector B) := by
    change mixedMoment B node1994 node1994Labels = _
    exact sound1994 B hB hF
  have h2123 : mixedVector B (Sum.inr 2123) = Sparse.eval nodeValue2123 (mixedVector B) := by
    change mixedMoment B node2123 node2123Labels = _
    exact sound2123 B hB hF
  have h2216 : mixedVector B (Sum.inr 2216) = Sparse.eval nodeValue2216 (mixedVector B) := by
    change mixedMoment B node2216 node2216Labels = _
    exact sound2216 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1505, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h993, h1929, h1994, h2123, h2216, h4080, reducedSource1288] using sourceEq1505 B hB

theorem rowSound1288 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1288 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1288, numericCheck1288, reducedZero1288 B hB hF, mul_zero]

theorem reducedZero1289 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1289 (mixedVector B) = 0 := by
  have h1025 : mixedVector B (Sum.inr 1025) = Sparse.eval nodeValue1025 (mixedVector B) := by
    change mixedMoment B node1025 node1025Labels = _
    exact sound1025 B hB hF
  have h2011 : mixedVector B (Sum.inr 2011) = Sparse.eval nodeValue2011 (mixedVector B) := by
    change mixedMoment B node2011 node2011Labels = _
    exact sound2011 B hB hF
  have h2093 : mixedVector B (Sum.inr 2093) = Sparse.eval nodeValue2093 (mixedVector B) := by
    change mixedMoment B node2093 node2093Labels = _
    exact sound2093 B hB hF
  have h2242 : mixedVector B (Sum.inr 2242) = Sparse.eval nodeValue2242 (mixedVector B) := by
    change mixedMoment B node2242 node2242Labels = _
    exact sound2242 B hB hF
  have h2246 : mixedVector B (Sum.inr 2246) = Sparse.eval nodeValue2246 (mixedVector B) := by
    change mixedMoment B node2246 node2246Labels = _
    exact sound2246 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1506, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1025, h2011, h2093, h2242, h2246, h4080, reducedSource1289] using sourceEq1506 B hB

theorem rowSound1289 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1289 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1289, numericCheck1289, reducedZero1289 B hB hF, mul_zero]

theorem reducedZero1290 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1290 (mixedVector B) = 0 := by
  have h973 : mixedVector B (Sum.inr 973) = Sparse.eval nodeValue973 (mixedVector B) := by
    change mixedMoment B node973 node973Labels = _
    exact sound973 B hB hF
  have h1900 : mixedVector B (Sum.inr 1900) = Sparse.eval nodeValue1900 (mixedVector B) := by
    change mixedMoment B node1900 node1900Labels = _
    exact sound1900 B hB hF
  have h2072 : mixedVector B (Sum.inr 2072) = Sparse.eval nodeValue2072 (mixedVector B) := by
    change mixedMoment B node2072 node2072Labels = _
    exact sound2072 B hB hF
  have h2190 : mixedVector B (Sum.inr 2190) = Sparse.eval nodeValue2190 (mixedVector B) := by
    change mixedMoment B node2190 node2190Labels = _
    exact sound2190 B hB hF
  have h2192 : mixedVector B (Sum.inr 2192) = Sparse.eval nodeValue2192 (mixedVector B) := by
    change mixedMoment B node2192 node2192Labels = _
    exact sound2192 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1507, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h973, h1900, h2072, h2190, h2192, h4080, reducedSource1290] using sourceEq1507 B hB

theorem rowSound1290 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1290 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1290, numericCheck1290, reducedZero1290 B hB hF, mul_zero]

theorem reducedZero1291 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1291 (mixedVector B) = 0 := by
  have h974 : mixedVector B (Sum.inr 974) = Sparse.eval nodeValue974 (mixedVector B) := by
    change mixedMoment B node974 node974Labels = _
    exact sound974 B hB hF
  have h1901 : mixedVector B (Sum.inr 1901) = Sparse.eval nodeValue1901 (mixedVector B) := by
    change mixedMoment B node1901 node1901Labels = _
    exact sound1901 B hB hF
  have h2073 : mixedVector B (Sum.inr 2073) = Sparse.eval nodeValue2073 (mixedVector B) := by
    change mixedMoment B node2073 node2073Labels = _
    exact sound2073 B hB hF
  have h2191 : mixedVector B (Sum.inr 2191) = Sparse.eval nodeValue2191 (mixedVector B) := by
    change mixedMoment B node2191 node2191Labels = _
    exact sound2191 B hB hF
  have h4079 : mixedVector B (Sum.inr 4079) = Sparse.eval nodeValue4079 (mixedVector B) := by
    change mixedMoment B node4079 node4079Labels = _
    exact sound4079 B hB hF
  simpa only [sourceForm1508, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h974, h1901, h2073, h2191, h4079, reducedSource1291] using sourceEq1508 B hB

theorem rowSound1291 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1291 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1291, numericCheck1291, reducedZero1291 B hB hF, mul_zero]

theorem reducedZero1292 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1292 (mixedVector B) = 0 := by
  have h1048 : mixedVector B (Sum.inr 1048) = Sparse.eval nodeValue1048 (mixedVector B) := by
    change mixedMoment B node1048 node1048Labels = _
    exact sound1048 B hB hF
  have h2027 : mixedVector B (Sum.inr 2027) = Sparse.eval nodeValue2027 (mixedVector B) := by
    change mixedMoment B node2027 node2027Labels = _
    exact sound2027 B hB hF
  have h2114 : mixedVector B (Sum.inr 2114) = Sparse.eval nodeValue2114 (mixedVector B) := by
    change mixedMoment B node2114 node2114Labels = _
    exact sound2114 B hB hF
  have h2261 : mixedVector B (Sum.inr 2261) = Sparse.eval nodeValue2261 (mixedVector B) := by
    change mixedMoment B node2261 node2261Labels = _
    exact sound2261 B hB hF
  have h2267 : mixedVector B (Sum.inr 2267) = Sparse.eval nodeValue2267 (mixedVector B) := by
    change mixedMoment B node2267 node2267Labels = _
    exact sound2267 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1509, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1048, h2027, h2114, h2261, h2267, h4081, reducedSource1292] using sourceEq1509 B hB

theorem rowSound1292 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1292 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1292, numericCheck1292, reducedZero1292 B hB hF, mul_zero]

theorem reducedZero1293 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1293 (mixedVector B) = 0 := by
  have h4154 : mixedVector B (Sum.inr 4154) = Sparse.eval nodeValue4154 (mixedVector B) := by
    change mixedMoment B node4154 node4154Labels = _
    exact sound4154 B hB hF
  have h4160 : mixedVector B (Sum.inr 4160) = Sparse.eval nodeValue4160 (mixedVector B) := by
    change mixedMoment B node4160 node4160Labels = _
    exact sound4160 B hB hF
  have h4162 : mixedVector B (Sum.inr 4162) = Sparse.eval nodeValue4162 (mixedVector B) := by
    change mixedMoment B node4162 node4162Labels = _
    exact sound4162 B hB hF
  have h4185 : mixedVector B (Sum.inr 4185) = Sparse.eval nodeValue4185 (mixedVector B) := by
    change mixedMoment B node4185 node4185Labels = _
    exact sound4185 B hB hF
  have h4328 : mixedVector B (Sum.inr 4328) = Sparse.eval nodeValue4328 (mixedVector B) := by
    change mixedMoment B node4328 node4328Labels = _
    exact sound4328 B hB hF
  have h4334 : mixedVector B (Sum.inr 4334) = Sparse.eval nodeValue4334 (mixedVector B) := by
    change mixedMoment B node4334 node4334Labels = _
    exact sound4334 B hB hF
  have h4336 : mixedVector B (Sum.inr 4336) = Sparse.eval nodeValue4336 (mixedVector B) := by
    change mixedMoment B node4336 node4336Labels = _
    exact sound4336 B hB hF
  have h4354 : mixedVector B (Sum.inr 4354) = Sparse.eval nodeValue4354 (mixedVector B) := by
    change mixedMoment B node4354 node4354Labels = _
    exact sound4354 B hB hF
  have h4368 : mixedVector B (Sum.inr 4368) = Sparse.eval nodeValue4368 (mixedVector B) := by
    change mixedMoment B node4368 node4368Labels = _
    exact sound4368 B hB hF
  have h4373 : mixedVector B (Sum.inr 4373) = Sparse.eval nodeValue4373 (mixedVector B) := by
    change mixedMoment B node4373 node4373Labels = _
    exact sound4373 B hB hF
  have h4375 : mixedVector B (Sum.inr 4375) = Sparse.eval nodeValue4375 (mixedVector B) := by
    change mixedMoment B node4375 node4375Labels = _
    exact sound4375 B hB hF
  have h4457 : mixedVector B (Sum.inr 4457) = Sparse.eval nodeValue4457 (mixedVector B) := by
    change mixedMoment B node4457 node4457Labels = _
    exact sound4457 B hB hF
  have h4459 : mixedVector B (Sum.inr 4459) = Sparse.eval nodeValue4459 (mixedVector B) := by
    change mixedMoment B node4459 node4459Labels = _
    exact sound4459 B hB hF
  have h4460 : mixedVector B (Sum.inr 4460) = Sparse.eval nodeValue4460 (mixedVector B) := by
    change mixedMoment B node4460 node4460Labels = _
    exact sound4460 B hB hF
  have h4464 : mixedVector B (Sum.inr 4464) = Sparse.eval nodeValue4464 (mixedVector B) := by
    change mixedMoment B node4464 node4464Labels = _
    exact sound4464 B hB hF
  have h4498 : mixedVector B (Sum.inr 4498) = Sparse.eval nodeValue4498 (mixedVector B) := by
    change mixedMoment B node4498 node4498Labels = _
    exact sound4498 B hB hF
  have h4503 : mixedVector B (Sum.inr 4503) = Sparse.eval nodeValue4503 (mixedVector B) := by
    change mixedMoment B node4503 node4503Labels = _
    exact sound4503 B hB hF
  have h4810 : mixedVector B (Sum.inr 4810) = Sparse.eval nodeValue4810 (mixedVector B) := by
    change mixedMoment B node4810 node4810Labels = _
    exact sound4810 B hB hF
  have h4874 : mixedVector B (Sum.inr 4874) = Sparse.eval nodeValue4874 (mixedVector B) := by
    change mixedMoment B node4874 node4874Labels = _
    exact sound4874 B hB hF
  have h4894 : mixedVector B (Sum.inr 4894) = Sparse.eval nodeValue4894 (mixedVector B) := by
    change mixedMoment B node4894 node4894Labels = _
    exact sound4894 B hB hF
  have h4896 : mixedVector B (Sum.inr 4896) = Sparse.eval nodeValue4896 (mixedVector B) := by
    change mixedMoment B node4896 node4896Labels = _
    exact sound4896 B hB hF
  simpa only [sourceForm1510, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4154, h4160, h4162, h4185, h4328, h4334, h4336, h4354, h4368, h4373, h4375, h4457, h4459, h4460, h4464, h4498, h4503, h4810, h4874, h4894, h4896, reducedSource1293] using sourceEq1510 B hB

theorem rowSound1293 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1293 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1293, numericCheck1293, reducedZero1293 B hB hF, mul_zero]

theorem reducedZero1294 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1294 (mixedVector B) = 0 := by
  have h631 : mixedVector B (Sum.inr 631) = Sparse.eval nodeValue631 (mixedVector B) := by
    change mixedMoment B node631 node631Labels = _
    exact sound631 B hB hF
  have h634 : mixedVector B (Sum.inr 634) = Sparse.eval nodeValue634 (mixedVector B) := by
    change mixedMoment B node634 node634Labels = _
    exact sound634 B hB hF
  have h636 : mixedVector B (Sum.inr 636) = Sparse.eval nodeValue636 (mixedVector B) := by
    change mixedMoment B node636 node636Labels = _
    exact sound636 B hB hF
  have h648 : mixedVector B (Sum.inr 648) = Sparse.eval nodeValue648 (mixedVector B) := by
    change mixedMoment B node648 node648Labels = _
    exact sound648 B hB hF
  have h1321 : mixedVector B (Sum.inr 1321) = Sparse.eval nodeValue1321 (mixedVector B) := by
    change mixedMoment B node1321 node1321Labels = _
    exact sound1321 B hB hF
  have h1323 : mixedVector B (Sum.inr 1323) = Sparse.eval nodeValue1323 (mixedVector B) := by
    change mixedMoment B node1323 node1323Labels = _
    exact sound1323 B hB hF
  have h1325 : mixedVector B (Sum.inr 1325) = Sparse.eval nodeValue1325 (mixedVector B) := by
    change mixedMoment B node1325 node1325Labels = _
    exact sound1325 B hB hF
  have h1330 : mixedVector B (Sum.inr 1330) = Sparse.eval nodeValue1330 (mixedVector B) := by
    change mixedMoment B node1330 node1330Labels = _
    exact sound1330 B hB hF
  have h1332 : mixedVector B (Sum.inr 1332) = Sparse.eval nodeValue1332 (mixedVector B) := by
    change mixedMoment B node1332 node1332Labels = _
    exact sound1332 B hB hF
  have h1334 : mixedVector B (Sum.inr 1334) = Sparse.eval nodeValue1334 (mixedVector B) := by
    change mixedMoment B node1334 node1334Labels = _
    exact sound1334 B hB hF
  have h1343 : mixedVector B (Sum.inr 1343) = Sparse.eval nodeValue1343 (mixedVector B) := by
    change mixedMoment B node1343 node1343Labels = _
    exact sound1343 B hB hF
  have h1406 : mixedVector B (Sum.inr 1406) = Sparse.eval nodeValue1406 (mixedVector B) := by
    change mixedMoment B node1406 node1406Labels = _
    exact sound1406 B hB hF
  have h1408 : mixedVector B (Sum.inr 1408) = Sparse.eval nodeValue1408 (mixedVector B) := by
    change mixedMoment B node1408 node1408Labels = _
    exact sound1408 B hB hF
  have h1414 : mixedVector B (Sum.inr 1414) = Sparse.eval nodeValue1414 (mixedVector B) := by
    change mixedMoment B node1414 node1414Labels = _
    exact sound1414 B hB hF
  have h1416 : mixedVector B (Sum.inr 1416) = Sparse.eval nodeValue1416 (mixedVector B) := by
    change mixedMoment B node1416 node1416Labels = _
    exact sound1416 B hB hF
  have h1442 : mixedVector B (Sum.inr 1442) = Sparse.eval nodeValue1442 (mixedVector B) := by
    change mixedMoment B node1442 node1442Labels = _
    exact sound1442 B hB hF
  have h1448 : mixedVector B (Sum.inr 1448) = Sparse.eval nodeValue1448 (mixedVector B) := by
    change mixedMoment B node1448 node1448Labels = _
    exact sound1448 B hB hF
  have h3187 : mixedVector B (Sum.inr 3187) = Sparse.eval nodeValue3187 (mixedVector B) := by
    change mixedMoment B node3187 node3187Labels = _
    exact sound3187 B hB hF
  have h3206 : mixedVector B (Sum.inr 3206) = Sparse.eval nodeValue3206 (mixedVector B) := by
    change mixedMoment B node3206 node3206Labels = _
    exact sound3206 B hB hF
  have h3225 : mixedVector B (Sum.inr 3225) = Sparse.eval nodeValue3225 (mixedVector B) := by
    change mixedMoment B node3225 node3225Labels = _
    exact sound3225 B hB hF
  have h3230 : mixedVector B (Sum.inr 3230) = Sparse.eval nodeValue3230 (mixedVector B) := by
    change mixedMoment B node3230 node3230Labels = _
    exact sound3230 B hB hF
  simpa only [sourceForm1511, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h631, h634, h636, h648, h1321, h1323, h1325, h1330, h1332, h1334, h1343, h1406, h1408, h1414, h1416, h1442, h1448, h3187, h3206, h3225, h3230, reducedSource1294] using sourceEq1511 B hB

theorem rowSound1294 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1294 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1294, numericCheck1294, reducedZero1294 B hB hF, mul_zero]

theorem reducedZero1295 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1295 (mixedVector B) = 0 := by
  have h1511 : mixedVector B (Sum.inr 1511) = Sparse.eval nodeValue1511 (mixedVector B) := by
    change mixedMoment B node1511 node1511Labels = _
    exact sound1511 B hB hF
  have h1523 : mixedVector B (Sum.inr 1523) = Sparse.eval nodeValue1523 (mixedVector B) := by
    change mixedMoment B node1523 node1523Labels = _
    exact sound1523 B hB hF
  have h1525 : mixedVector B (Sum.inr 1525) = Sparse.eval nodeValue1525 (mixedVector B) := by
    change mixedMoment B node1525 node1525Labels = _
    exact sound1525 B hB hF
  have h1529 : mixedVector B (Sum.inr 1529) = Sparse.eval nodeValue1529 (mixedVector B) := by
    change mixedMoment B node1529 node1529Labels = _
    exact sound1529 B hB hF
  have h1667 : mixedVector B (Sum.inr 1667) = Sparse.eval nodeValue1667 (mixedVector B) := by
    change mixedMoment B node1667 node1667Labels = _
    exact sound1667 B hB hF
  have h1679 : mixedVector B (Sum.inr 1679) = Sparse.eval nodeValue1679 (mixedVector B) := by
    change mixedMoment B node1679 node1679Labels = _
    exact sound1679 B hB hF
  have h1681 : mixedVector B (Sum.inr 1681) = Sparse.eval nodeValue1681 (mixedVector B) := by
    change mixedMoment B node1681 node1681Labels = _
    exact sound1681 B hB hF
  have h1685 : mixedVector B (Sum.inr 1685) = Sparse.eval nodeValue1685 (mixedVector B) := by
    change mixedMoment B node1685 node1685Labels = _
    exact sound1685 B hB hF
  have h1707 : mixedVector B (Sum.inr 1707) = Sparse.eval nodeValue1707 (mixedVector B) := by
    change mixedMoment B node1707 node1707Labels = _
    exact sound1707 B hB hF
  have h1712 : mixedVector B (Sum.inr 1712) = Sparse.eval nodeValue1712 (mixedVector B) := by
    change mixedMoment B node1712 node1712Labels = _
    exact sound1712 B hB hF
  have h1714 : mixedVector B (Sum.inr 1714) = Sparse.eval nodeValue1714 (mixedVector B) := by
    change mixedMoment B node1714 node1714Labels = _
    exact sound1714 B hB hF
  have h1725 : mixedVector B (Sum.inr 1725) = Sparse.eval nodeValue1725 (mixedVector B) := by
    change mixedMoment B node1725 node1725Labels = _
    exact sound1725 B hB hF
  have h1727 : mixedVector B (Sum.inr 1727) = Sparse.eval nodeValue1727 (mixedVector B) := by
    change mixedMoment B node1727 node1727Labels = _
    exact sound1727 B hB hF
  have h1735 : mixedVector B (Sum.inr 1735) = Sparse.eval nodeValue1735 (mixedVector B) := by
    change mixedMoment B node1735 node1735Labels = _
    exact sound1735 B hB hF
  have h1739 : mixedVector B (Sum.inr 1739) = Sparse.eval nodeValue1739 (mixedVector B) := by
    change mixedMoment B node1739 node1739Labels = _
    exact sound1739 B hB hF
  have h1743 : mixedVector B (Sum.inr 1743) = Sparse.eval nodeValue1743 (mixedVector B) := by
    change mixedMoment B node1743 node1743Labels = _
    exact sound1743 B hB hF
  have h1745 : mixedVector B (Sum.inr 1745) = Sparse.eval nodeValue1745 (mixedVector B) := by
    change mixedMoment B node1745 node1745Labels = _
    exact sound1745 B hB hF
  have h2215 : mixedVector B (Sum.inr 2215) = Sparse.eval nodeValue2215 (mixedVector B) := by
    change mixedMoment B node2215 node2215Labels = _
    exact sound2215 B hB hF
  have h2264 : mixedVector B (Sum.inr 2264) = Sparse.eval nodeValue2264 (mixedVector B) := by
    change mixedMoment B node2264 node2264Labels = _
    exact sound2264 B hB hF
  have h2276 : mixedVector B (Sum.inr 2276) = Sparse.eval nodeValue2276 (mixedVector B) := by
    change mixedMoment B node2276 node2276Labels = _
    exact sound2276 B hB hF
  have h2278 : mixedVector B (Sum.inr 2278) = Sparse.eval nodeValue2278 (mixedVector B) := by
    change mixedMoment B node2278 node2278Labels = _
    exact sound2278 B hB hF
  simpa only [sourceForm1512, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1511, h1523, h1525, h1529, h1667, h1679, h1681, h1685, h1707, h1712, h1714, h1725, h1727, h1735, h1739, h1743, h1745, h2215, h2264, h2276, h2278, reducedSource1295] using sourceEq1512 B hB

theorem rowSound1295 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1295 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1295, numericCheck1295, reducedZero1295 B hB hF, mul_zero]

theorem sourceRowsAt1280 : MixedData.sourceRows (1280 : Fin 2425) =
    MixedData.row1280 := by decide +kernel

theorem sourceRowsAt1281 : MixedData.sourceRows (1281 : Fin 2425) =
    MixedData.row1281 := by decide +kernel

theorem sourceRowsAt1282 : MixedData.sourceRows (1282 : Fin 2425) =
    MixedData.row1282 := by decide +kernel

theorem sourceRowsAt1283 : MixedData.sourceRows (1283 : Fin 2425) =
    MixedData.row1283 := by decide +kernel

theorem sourceRowsAt1284 : MixedData.sourceRows (1284 : Fin 2425) =
    MixedData.row1284 := by decide +kernel

theorem sourceRowsAt1285 : MixedData.sourceRows (1285 : Fin 2425) =
    MixedData.row1285 := by decide +kernel

theorem sourceRowsAt1286 : MixedData.sourceRows (1286 : Fin 2425) =
    MixedData.row1286 := by decide +kernel

theorem sourceRowsAt1287 : MixedData.sourceRows (1287 : Fin 2425) =
    MixedData.row1287 := by decide +kernel

theorem sourceRowsAt1288 : MixedData.sourceRows (1288 : Fin 2425) =
    MixedData.row1288 := by decide +kernel

theorem sourceRowsAt1289 : MixedData.sourceRows (1289 : Fin 2425) =
    MixedData.row1289 := by decide +kernel

theorem sourceRowsAt1290 : MixedData.sourceRows (1290 : Fin 2425) =
    MixedData.row1290 := by decide +kernel

theorem sourceRowsAt1291 : MixedData.sourceRows (1291 : Fin 2425) =
    MixedData.row1291 := by decide +kernel

theorem sourceRowsAt1292 : MixedData.sourceRows (1292 : Fin 2425) =
    MixedData.row1292 := by decide +kernel

theorem sourceRowsAt1293 : MixedData.sourceRows (1293 : Fin 2425) =
    MixedData.row1293 := by decide +kernel

theorem sourceRowsAt1294 : MixedData.sourceRows (1294 : Fin 2425) =
    MixedData.row1294 := by decide +kernel

theorem sourceRowsAt1295 : MixedData.sourceRows (1295 : Fin 2425) =
    MixedData.row1295 := by decide +kernel

theorem chunkSound80 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 80) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1280 ∨ k.val = 1281 ∨ k.val = 1282 ∨ k.val = 1283 ∨ k.val = 1284 ∨ k.val = 1285 ∨ k.val = 1286 ∨ k.val = 1287 ∨ k.val = 1288 ∨ k.val = 1289 ∨ k.val = 1290 ∨ k.val = 1291 ∨ k.val = 1292 ∨ k.val = 1293 ∨ k.val = 1294 ∨ k.val = 1295 := by omega
  rcases heq with h1280 | h1281 | h1282 | h1283 | h1284 | h1285 | h1286 | h1287 | h1288 | h1289 | h1290 | h1291 | h1292 | h1293 | h1294 | h1295
  · have he : k = (1280 : Fin 2425) := Fin.ext h1280
    subst k
    rw [sourceRowsAt1280]
    exact rowSound1280 B hB hF
  · have he : k = (1281 : Fin 2425) := Fin.ext h1281
    subst k
    rw [sourceRowsAt1281]
    exact rowSound1281 B hB hF
  · have he : k = (1282 : Fin 2425) := Fin.ext h1282
    subst k
    rw [sourceRowsAt1282]
    exact rowSound1282 B hB hF
  · have he : k = (1283 : Fin 2425) := Fin.ext h1283
    subst k
    rw [sourceRowsAt1283]
    exact rowSound1283 B hB hF
  · have he : k = (1284 : Fin 2425) := Fin.ext h1284
    subst k
    rw [sourceRowsAt1284]
    exact rowSound1284 B hB hF
  · have he : k = (1285 : Fin 2425) := Fin.ext h1285
    subst k
    rw [sourceRowsAt1285]
    exact rowSound1285 B hB hF
  · have he : k = (1286 : Fin 2425) := Fin.ext h1286
    subst k
    rw [sourceRowsAt1286]
    exact rowSound1286 B hB hF
  · have he : k = (1287 : Fin 2425) := Fin.ext h1287
    subst k
    rw [sourceRowsAt1287]
    exact rowSound1287 B hB hF
  · have he : k = (1288 : Fin 2425) := Fin.ext h1288
    subst k
    rw [sourceRowsAt1288]
    exact rowSound1288 B hB hF
  · have he : k = (1289 : Fin 2425) := Fin.ext h1289
    subst k
    rw [sourceRowsAt1289]
    exact rowSound1289 B hB hF
  · have he : k = (1290 : Fin 2425) := Fin.ext h1290
    subst k
    rw [sourceRowsAt1290]
    exact rowSound1290 B hB hF
  · have he : k = (1291 : Fin 2425) := Fin.ext h1291
    subst k
    rw [sourceRowsAt1291]
    exact rowSound1291 B hB hF
  · have he : k = (1292 : Fin 2425) := Fin.ext h1292
    subst k
    rw [sourceRowsAt1292]
    exact rowSound1292 B hB hF
  · have he : k = (1293 : Fin 2425) := Fin.ext h1293
    subst k
    rw [sourceRowsAt1293]
    exact rowSound1293 B hB hF
  · have he : k = (1294 : Fin 2425) := Fin.ext h1294
    subst k
    rw [sourceRowsAt1294]
    exact rowSound1294 B hB hF
  · have he : k = (1295 : Fin 2425) := Fin.ext h1295
    subst k
    rw [sourceRowsAt1295]
    exact rowSound1295 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
