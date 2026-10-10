import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources4
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources5

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero128 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource128 (mixedVector B) = 0 := by
  have h1080 : mixedVector B (Sum.inr 1080) = Sparse.eval nodeValue1080 (mixedVector B) := by
    change mixedMoment B node1080 node1080Labels = _
    exact sound1080 B hB hF
  have h2052 : mixedVector B (Sum.inr 2052) = Sparse.eval nodeValue2052 (mixedVector B) := by
    change mixedMoment B node2052 node2052Labels = _
    exact sound2052 B hB hF
  have h2290 : mixedVector B (Sum.inr 2290) = Sparse.eval nodeValue2290 (mixedVector B) := by
    change mixedMoment B node2290 node2290Labels = _
    exact sound2290 B hB hF
  have h2292 : mixedVector B (Sum.inr 2292) = Sparse.eval nodeValue2292 (mixedVector B) := by
    change mixedMoment B node2292 node2292Labels = _
    exact sound2292 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm148, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1080, h2052, h2290, h2292, h4085, reducedSource128] using sourceEq148 B hB

theorem rowSound128 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row128 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck128, numericCheck128, reducedZero128 B hB hF, mul_zero]

theorem reducedZero129 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource129 (mixedVector B) = 0 := by
  have h4591 : mixedVector B (Sum.inr 4591) = Sparse.eval nodeValue4591 (mixedVector B) := by
    change mixedMoment B node4591 node4591Labels = _
    exact sound4591 B hB hF
  have h4594 : mixedVector B (Sum.inr 4594) = Sparse.eval nodeValue4594 (mixedVector B) := by
    change mixedMoment B node4594 node4594Labels = _
    exact sound4594 B hB hF
  have h4608 : mixedVector B (Sum.inr 4608) = Sparse.eval nodeValue4608 (mixedVector B) := by
    change mixedMoment B node4608 node4608Labels = _
    exact sound4608 B hB hF
  have h4609 : mixedVector B (Sum.inr 4609) = Sparse.eval nodeValue4609 (mixedVector B) := by
    change mixedMoment B node4609 node4609Labels = _
    exact sound4609 B hB hF
  have h5075 : mixedVector B (Sum.inr 5075) = Sparse.eval nodeValue5075 (mixedVector B) := by
    change mixedMoment B node5075 node5075Labels = _
    exact sound5075 B hB hF
  have h5107 : mixedVector B (Sum.inr 5107) = Sparse.eval nodeValue5107 (mixedVector B) := by
    change mixedMoment B node5107 node5107Labels = _
    exact sound5107 B hB hF
  have h5127 : mixedVector B (Sum.inr 5127) = Sparse.eval nodeValue5127 (mixedVector B) := by
    change mixedMoment B node5127 node5127Labels = _
    exact sound5127 B hB hF
  have h5147 : mixedVector B (Sum.inr 5147) = Sparse.eval nodeValue5147 (mixedVector B) := by
    change mixedMoment B node5147 node5147Labels = _
    exact sound5147 B hB hF
  have h5201 : mixedVector B (Sum.inr 5201) = Sparse.eval nodeValue5201 (mixedVector B) := by
    change mixedMoment B node5201 node5201Labels = _
    exact sound5201 B hB hF
  have h5258 : mixedVector B (Sum.inr 5258) = Sparse.eval nodeValue5258 (mixedVector B) := by
    change mixedMoment B node5258 node5258Labels = _
    exact sound5258 B hB hF
  have h5274 : mixedVector B (Sum.inr 5274) = Sparse.eval nodeValue5274 (mixedVector B) := by
    change mixedMoment B node5274 node5274Labels = _
    exact sound5274 B hB hF
  have h5291 : mixedVector B (Sum.inr 5291) = Sparse.eval nodeValue5291 (mixedVector B) := by
    change mixedMoment B node5291 node5291Labels = _
    exact sound5291 B hB hF
  have h5441 : mixedVector B (Sum.inr 5441) = Sparse.eval nodeValue5441 (mixedVector B) := by
    change mixedMoment B node5441 node5441Labels = _
    exact sound5441 B hB hF
  simpa only [sourceForm149, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4591, h4594, h4608, h4609, h5075, h5107, h5127, h5147, h5201, h5258, h5274, h5291, h5441, reducedSource129] using sourceEq149 B hB

theorem rowSound129 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row129 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck129, numericCheck129, reducedZero129 B hB hF, mul_zero]

theorem reducedZero130 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource130 (mixedVector B) = 0 := by
  have h1217 : mixedVector B (Sum.inr 1217) = Sparse.eval nodeValue1217 (mixedVector B) := by
    change mixedMoment B node1217 node1217Labels = _
    exact sound1217 B hB hF
  have h1221 : mixedVector B (Sum.inr 1221) = Sparse.eval nodeValue1221 (mixedVector B) := by
    change mixedMoment B node1221 node1221Labels = _
    exact sound1221 B hB hF
  have h1243 : mixedVector B (Sum.inr 1243) = Sparse.eval nodeValue1243 (mixedVector B) := by
    change mixedMoment B node1243 node1243Labels = _
    exact sound1243 B hB hF
  have h1269 : mixedVector B (Sum.inr 1269) = Sparse.eval nodeValue1269 (mixedVector B) := by
    change mixedMoment B node1269 node1269Labels = _
    exact sound1269 B hB hF
  have h2865 : mixedVector B (Sum.inr 2865) = Sparse.eval nodeValue2865 (mixedVector B) := by
    change mixedMoment B node2865 node2865Labels = _
    exact sound2865 B hB hF
  have h2886 : mixedVector B (Sum.inr 2886) = Sparse.eval nodeValue2886 (mixedVector B) := by
    change mixedMoment B node2886 node2886Labels = _
    exact sound2886 B hB hF
  have h2914 : mixedVector B (Sum.inr 2914) = Sparse.eval nodeValue2914 (mixedVector B) := by
    change mixedMoment B node2914 node2914Labels = _
    exact sound2914 B hB hF
  have h2939 : mixedVector B (Sum.inr 2939) = Sparse.eval nodeValue2939 (mixedVector B) := by
    change mixedMoment B node2939 node2939Labels = _
    exact sound2939 B hB hF
  have h3002 : mixedVector B (Sum.inr 3002) = Sparse.eval nodeValue3002 (mixedVector B) := by
    change mixedMoment B node3002 node3002Labels = _
    exact sound3002 B hB hF
  have h3089 : mixedVector B (Sum.inr 3089) = Sparse.eval nodeValue3089 (mixedVector B) := by
    change mixedMoment B node3089 node3089Labels = _
    exact sound3089 B hB hF
  have h3103 : mixedVector B (Sum.inr 3103) = Sparse.eval nodeValue3103 (mixedVector B) := by
    change mixedMoment B node3103 node3103Labels = _
    exact sound3103 B hB hF
  have h3112 : mixedVector B (Sum.inr 3112) = Sparse.eval nodeValue3112 (mixedVector B) := by
    change mixedMoment B node3112 node3112Labels = _
    exact sound3112 B hB hF
  have h4037 : mixedVector B (Sum.inr 4037) = Sparse.eval nodeValue4037 (mixedVector B) := by
    change mixedMoment B node4037 node4037Labels = _
    exact sound4037 B hB hF
  simpa only [sourceForm150, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1217, h1221, h1243, h1269, h2865, h2886, h2914, h2939, h3002, h3089, h3103, h3112, h4037, reducedSource130] using sourceEq150 B hB

theorem rowSound130 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row130 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck130, numericCheck130, reducedZero130 B hB hF, mul_zero]

theorem reducedZero131 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource131 (mixedVector B) = 0 := by
  have h3291 : mixedVector B (Sum.inr 3291) = Sparse.eval nodeValue3291 (mixedVector B) := by
    change mixedMoment B node3291 node3291Labels = _
    exact sound3291 B hB hF
  have h3298 : mixedVector B (Sum.inr 3298) = Sparse.eval nodeValue3298 (mixedVector B) := by
    change mixedMoment B node3298 node3298Labels = _
    exact sound3298 B hB hF
  have h3300 : mixedVector B (Sum.inr 3300) = Sparse.eval nodeValue3300 (mixedVector B) := by
    change mixedMoment B node3300 node3300Labels = _
    exact sound3300 B hB hF
  have h3302 : mixedVector B (Sum.inr 3302) = Sparse.eval nodeValue3302 (mixedVector B) := by
    change mixedMoment B node3302 node3302Labels = _
    exact sound3302 B hB hF
  have h3468 : mixedVector B (Sum.inr 3468) = Sparse.eval nodeValue3468 (mixedVector B) := by
    change mixedMoment B node3468 node3468Labels = _
    exact sound3468 B hB hF
  have h3484 : mixedVector B (Sum.inr 3484) = Sparse.eval nodeValue3484 (mixedVector B) := by
    change mixedMoment B node3484 node3484Labels = _
    exact sound3484 B hB hF
  have h3513 : mixedVector B (Sum.inr 3513) = Sparse.eval nodeValue3513 (mixedVector B) := by
    change mixedMoment B node3513 node3513Labels = _
    exact sound3513 B hB hF
  have h3530 : mixedVector B (Sum.inr 3530) = Sparse.eval nodeValue3530 (mixedVector B) := by
    change mixedMoment B node3530 node3530Labels = _
    exact sound3530 B hB hF
  have h3533 : mixedVector B (Sum.inr 3533) = Sparse.eval nodeValue3533 (mixedVector B) := by
    change mixedMoment B node3533 node3533Labels = _
    exact sound3533 B hB hF
  have h3547 : mixedVector B (Sum.inr 3547) = Sparse.eval nodeValue3547 (mixedVector B) := by
    change mixedMoment B node3547 node3547Labels = _
    exact sound3547 B hB hF
  have h3579 : mixedVector B (Sum.inr 3579) = Sparse.eval nodeValue3579 (mixedVector B) := by
    change mixedMoment B node3579 node3579Labels = _
    exact sound3579 B hB hF
  have h3582 : mixedVector B (Sum.inr 3582) = Sparse.eval nodeValue3582 (mixedVector B) := by
    change mixedMoment B node3582 node3582Labels = _
    exact sound3582 B hB hF
  have h3860 : mixedVector B (Sum.inr 3860) = Sparse.eval nodeValue3860 (mixedVector B) := by
    change mixedMoment B node3860 node3860Labels = _
    exact sound3860 B hB hF
  simpa only [sourceForm151, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3291, h3298, h3300, h3302, h3468, h3484, h3513, h3530, h3533, h3547, h3579, h3582, h3860, reducedSource131] using sourceEq151 B hB

theorem rowSound131 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row131 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck131, numericCheck131, reducedZero131 B hB hF, mul_zero]

theorem reducedZero132 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource132 (mixedVector B) = 0 := by
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  have h2726 : mixedVector B (Sum.inr 2726) = Sparse.eval nodeValue2726 (mixedVector B) := by
    change mixedMoment B node2726 node2726Labels = _
    exact sound2726 B hB hF
  have h2742 : mixedVector B (Sum.inr 2742) = Sparse.eval nodeValue2742 (mixedVector B) := by
    change mixedMoment B node2742 node2742Labels = _
    exact sound2742 B hB hF
  have h2765 : mixedVector B (Sum.inr 2765) = Sparse.eval nodeValue2765 (mixedVector B) := by
    change mixedMoment B node2765 node2765Labels = _
    exact sound2765 B hB hF
  have h3905 : mixedVector B (Sum.inr 3905) = Sparse.eval nodeValue3905 (mixedVector B) := by
    change mixedMoment B node3905 node3905Labels = _
    exact sound3905 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm152, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2722, h2726, h2742, h2765, h3905, h4092, reducedSource132] using sourceEq152 B hB

theorem rowSound132 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row132 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck132, numericCheck132, reducedZero132 B hB hF, mul_zero]

theorem reducedZero133 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource133 (mixedVector B) = 0 := by
  have h1215 : mixedVector B (Sum.inr 1215) = Sparse.eval nodeValue1215 (mixedVector B) := by
    change mixedMoment B node1215 node1215Labels = _
    exact sound1215 B hB hF
  have h1221 : mixedVector B (Sum.inr 1221) = Sparse.eval nodeValue1221 (mixedVector B) := by
    change mixedMoment B node1221 node1221Labels = _
    exact sound1221 B hB hF
  have h1242 : mixedVector B (Sum.inr 1242) = Sparse.eval nodeValue1242 (mixedVector B) := by
    change mixedMoment B node1242 node1242Labels = _
    exact sound1242 B hB hF
  have h1264 : mixedVector B (Sum.inr 1264) = Sparse.eval nodeValue1264 (mixedVector B) := by
    change mixedMoment B node1264 node1264Labels = _
    exact sound1264 B hB hF
  have h2726 : mixedVector B (Sum.inr 2726) = Sparse.eval nodeValue2726 (mixedVector B) := by
    change mixedMoment B node2726 node2726Labels = _
    exact sound2726 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm153, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1215, h1221, h1242, h1264, h2726, h4092, reducedSource133] using sourceEq153 B hB

theorem rowSound133 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row133 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck133, numericCheck133, reducedZero133 B hB hF, mul_zero]

theorem reducedZero134 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource134 (mixedVector B) = 0 := by
  have h1242 : mixedVector B (Sum.inr 1242) = Sparse.eval nodeValue1242 (mixedVector B) := by
    change mixedMoment B node1242 node1242Labels = _
    exact sound1242 B hB hF
  have h2482 : mixedVector B (Sum.inr 2482) = Sparse.eval nodeValue2482 (mixedVector B) := by
    change mixedMoment B node2482 node2482Labels = _
    exact sound2482 B hB hF
  have h2517 : mixedVector B (Sum.inr 2517) = Sparse.eval nodeValue2517 (mixedVector B) := by
    change mixedMoment B node2517 node2517Labels = _
    exact sound2517 B hB hF
  have h2726 : mixedVector B (Sum.inr 2726) = Sparse.eval nodeValue2726 (mixedVector B) := by
    change mixedMoment B node2726 node2726Labels = _
    exact sound2726 B hB hF
  have h2742 : mixedVector B (Sum.inr 2742) = Sparse.eval nodeValue2742 (mixedVector B) := by
    change mixedMoment B node2742 node2742Labels = _
    exact sound2742 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm154, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1242, h2482, h2517, h2726, h2742, h4092, reducedSource134] using sourceEq154 B hB

theorem rowSound134 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row134 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck134, numericCheck134, reducedZero134 B hB hF, mul_zero]

theorem reducedZero135 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource135 (mixedVector B) = 0 := by
  have h1264 : mixedVector B (Sum.inr 1264) = Sparse.eval nodeValue1264 (mixedVector B) := by
    change mixedMoment B node1264 node1264Labels = _
    exact sound1264 B hB hF
  have h2569 : mixedVector B (Sum.inr 2569) = Sparse.eval nodeValue2569 (mixedVector B) := by
    change mixedMoment B node2569 node2569Labels = _
    exact sound2569 B hB hF
  have h2635 : mixedVector B (Sum.inr 2635) = Sparse.eval nodeValue2635 (mixedVector B) := by
    change mixedMoment B node2635 node2635Labels = _
    exact sound2635 B hB hF
  have h2726 : mixedVector B (Sum.inr 2726) = Sparse.eval nodeValue2726 (mixedVector B) := by
    change mixedMoment B node2726 node2726Labels = _
    exact sound2726 B hB hF
  have h2765 : mixedVector B (Sum.inr 2765) = Sparse.eval nodeValue2765 (mixedVector B) := by
    change mixedMoment B node2765 node2765Labels = _
    exact sound2765 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm155, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1264, h2569, h2635, h2726, h2765, h4092, reducedSource135] using sourceEq155 B hB

theorem rowSound135 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row135 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck135, numericCheck135, reducedZero135 B hB hF, mul_zero]

theorem reducedZero136 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource136 (mixedVector B) = 0 := by
  have h1215 : mixedVector B (Sum.inr 1215) = Sparse.eval nodeValue1215 (mixedVector B) := by
    change mixedMoment B node1215 node1215Labels = _
    exact sound1215 B hB hF
  have h2482 : mixedVector B (Sum.inr 2482) = Sparse.eval nodeValue2482 (mixedVector B) := by
    change mixedMoment B node2482 node2482Labels = _
    exact sound2482 B hB hF
  have h2542 : mixedVector B (Sum.inr 2542) = Sparse.eval nodeValue2542 (mixedVector B) := by
    change mixedMoment B node2542 node2542Labels = _
    exact sound2542 B hB hF
  have h2569 : mixedVector B (Sum.inr 2569) = Sparse.eval nodeValue2569 (mixedVector B) := by
    change mixedMoment B node2569 node2569Labels = _
    exact sound2569 B hB hF
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  have h2726 : mixedVector B (Sum.inr 2726) = Sparse.eval nodeValue2726 (mixedVector B) := by
    change mixedMoment B node2726 node2726Labels = _
    exact sound2726 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm156, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1215, h2482, h2542, h2569, h2722, h2726, h4092, reducedSource136] using sourceEq156 B hB

theorem rowSound136 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row136 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck136, numericCheck136, reducedZero136 B hB hF, mul_zero]

theorem reducedZero137 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource137 (mixedVector B) = 0 := by
  have h4401 : mixedVector B (Sum.inr 4401) = Sparse.eval nodeValue4401 (mixedVector B) := by
    change mixedMoment B node4401 node4401Labels = _
    exact sound4401 B hB hF
  have h4405 : mixedVector B (Sum.inr 4405) = Sparse.eval nodeValue4405 (mixedVector B) := by
    change mixedMoment B node4405 node4405Labels = _
    exact sound4405 B hB hF
  have h4428 : mixedVector B (Sum.inr 4428) = Sparse.eval nodeValue4428 (mixedVector B) := by
    change mixedMoment B node4428 node4428Labels = _
    exact sound4428 B hB hF
  have h4460 : mixedVector B (Sum.inr 4460) = Sparse.eval nodeValue4460 (mixedVector B) := by
    change mixedMoment B node4460 node4460Labels = _
    exact sound4460 B hB hF
  have h5000 : mixedVector B (Sum.inr 5000) = Sparse.eval nodeValue5000 (mixedVector B) := by
    change mixedMoment B node5000 node5000Labels = _
    exact sound5000 B hB hF
  have h5021 : mixedVector B (Sum.inr 5021) = Sparse.eval nodeValue5021 (mixedVector B) := by
    change mixedMoment B node5021 node5021Labels = _
    exact sound5021 B hB hF
  have h5047 : mixedVector B (Sum.inr 5047) = Sparse.eval nodeValue5047 (mixedVector B) := by
    change mixedMoment B node5047 node5047Labels = _
    exact sound5047 B hB hF
  have h5075 : mixedVector B (Sum.inr 5075) = Sparse.eval nodeValue5075 (mixedVector B) := by
    change mixedMoment B node5075 node5075Labels = _
    exact sound5075 B hB hF
  have h5171 : mixedVector B (Sum.inr 5171) = Sparse.eval nodeValue5171 (mixedVector B) := by
    change mixedMoment B node5171 node5171Labels = _
    exact sound5171 B hB hF
  have h5259 : mixedVector B (Sum.inr 5259) = Sparse.eval nodeValue5259 (mixedVector B) := by
    change mixedMoment B node5259 node5259Labels = _
    exact sound5259 B hB hF
  have h5275 : mixedVector B (Sum.inr 5275) = Sparse.eval nodeValue5275 (mixedVector B) := by
    change mixedMoment B node5275 node5275Labels = _
    exact sound5275 B hB hF
  have h5293 : mixedVector B (Sum.inr 5293) = Sparse.eval nodeValue5293 (mixedVector B) := by
    change mixedMoment B node5293 node5293Labels = _
    exact sound5293 B hB hF
  have h5491 : mixedVector B (Sum.inr 5491) = Sparse.eval nodeValue5491 (mixedVector B) := by
    change mixedMoment B node5491 node5491Labels = _
    exact sound5491 B hB hF
  simpa only [sourceForm157, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4401, h4405, h4428, h4460, h5000, h5021, h5047, h5075, h5171, h5259, h5275, h5293, h5491, reducedSource137] using sourceEq157 B hB

theorem rowSound137 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row137 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck137, numericCheck137, reducedZero137 B hB hF, mul_zero]

theorem reducedZero138 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource138 (mixedVector B) = 0 := by
  have h982 : mixedVector B (Sum.inr 982) = Sparse.eval nodeValue982 (mixedVector B) := by
    change mixedMoment B node982 node982Labels = _
    exact sound982 B hB hF
  have h986 : mixedVector B (Sum.inr 986) = Sparse.eval nodeValue986 (mixedVector B) := by
    change mixedMoment B node986 node986Labels = _
    exact sound986 B hB hF
  have h1009 : mixedVector B (Sum.inr 1009) = Sparse.eval nodeValue1009 (mixedVector B) := by
    change mixedMoment B node1009 node1009Labels = _
    exact sound1009 B hB hF
  have h1043 : mixedVector B (Sum.inr 1043) = Sparse.eval nodeValue1043 (mixedVector B) := by
    change mixedMoment B node1043 node1043Labels = _
    exact sound1043 B hB hF
  have h2385 : mixedVector B (Sum.inr 2385) = Sparse.eval nodeValue2385 (mixedVector B) := by
    change mixedMoment B node2385 node2385Labels = _
    exact sound2385 B hB hF
  have h2407 : mixedVector B (Sum.inr 2407) = Sparse.eval nodeValue2407 (mixedVector B) := by
    change mixedMoment B node2407 node2407Labels = _
    exact sound2407 B hB hF
  have h2449 : mixedVector B (Sum.inr 2449) = Sparse.eval nodeValue2449 (mixedVector B) := by
    change mixedMoment B node2449 node2449Labels = _
    exact sound2449 B hB hF
  have h2482 : mixedVector B (Sum.inr 2482) = Sparse.eval nodeValue2482 (mixedVector B) := by
    change mixedMoment B node2482 node2482Labels = _
    exact sound2482 B hB hF
  have h2598 : mixedVector B (Sum.inr 2598) = Sparse.eval nodeValue2598 (mixedVector B) := by
    change mixedMoment B node2598 node2598Labels = _
    exact sound2598 B hB hF
  have h2723 : mixedVector B (Sum.inr 2723) = Sparse.eval nodeValue2723 (mixedVector B) := by
    change mixedMoment B node2723 node2723Labels = _
    exact sound2723 B hB hF
  have h2743 : mixedVector B (Sum.inr 2743) = Sparse.eval nodeValue2743 (mixedVector B) := by
    change mixedMoment B node2743 node2743Labels = _
    exact sound2743 B hB hF
  have h2767 : mixedVector B (Sum.inr 2767) = Sparse.eval nodeValue2767 (mixedVector B) := by
    change mixedMoment B node2767 node2767Labels = _
    exact sound2767 B hB hF
  have h4014 : mixedVector B (Sum.inr 4014) = Sparse.eval nodeValue4014 (mixedVector B) := by
    change mixedMoment B node4014 node4014Labels = _
    exact sound4014 B hB hF
  simpa only [sourceForm158, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h982, h986, h1009, h1043, h2385, h2407, h2449, h2482, h2598, h2723, h2743, h2767, h4014, reducedSource138] using sourceEq158 B hB

theorem rowSound138 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row138 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck138, numericCheck138, reducedZero138 B hB hF, mul_zero]

theorem reducedZero139 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource139 (mixedVector B) = 0 := by
  have h4832 : mixedVector B (Sum.inr 4832) = Sparse.eval nodeValue4832 (mixedVector B) := by
    change mixedMoment B node4832 node4832Labels = _
    exact sound4832 B hB hF
  have h4837 : mixedVector B (Sum.inr 4837) = Sparse.eval nodeValue4837 (mixedVector B) := by
    change mixedMoment B node4837 node4837Labels = _
    exact sound4837 B hB hF
  have h4845 : mixedVector B (Sum.inr 4845) = Sparse.eval nodeValue4845 (mixedVector B) := by
    change mixedMoment B node4845 node4845Labels = _
    exact sound4845 B hB hF
  have h4897 : mixedVector B (Sum.inr 4897) = Sparse.eval nodeValue4897 (mixedVector B) := by
    change mixedMoment B node4897 node4897Labels = _
    exact sound4897 B hB hF
  have h5222 : mixedVector B (Sum.inr 5222) = Sparse.eval nodeValue5222 (mixedVector B) := by
    change mixedMoment B node5222 node5222Labels = _
    exact sound5222 B hB hF
  have h5235 : mixedVector B (Sum.inr 5235) = Sparse.eval nodeValue5235 (mixedVector B) := by
    change mixedMoment B node5235 node5235Labels = _
    exact sound5235 B hB hF
  have h5239 : mixedVector B (Sum.inr 5239) = Sparse.eval nodeValue5239 (mixedVector B) := by
    change mixedMoment B node5239 node5239Labels = _
    exact sound5239 B hB hF
  have h5252 : mixedVector B (Sum.inr 5252) = Sparse.eval nodeValue5252 (mixedVector B) := by
    change mixedMoment B node5252 node5252Labels = _
    exact sound5252 B hB hF
  have h5261 : mixedVector B (Sum.inr 5261) = Sparse.eval nodeValue5261 (mixedVector B) := by
    change mixedMoment B node5261 node5261Labels = _
    exact sound5261 B hB hF
  have h5268 : mixedVector B (Sum.inr 5268) = Sparse.eval nodeValue5268 (mixedVector B) := by
    change mixedMoment B node5268 node5268Labels = _
    exact sound5268 B hB hF
  have h5296 : mixedVector B (Sum.inr 5296) = Sparse.eval nodeValue5296 (mixedVector B) := by
    change mixedMoment B node5296 node5296Labels = _
    exact sound5296 B hB hF
  have h5312 : mixedVector B (Sum.inr 5312) = Sparse.eval nodeValue5312 (mixedVector B) := by
    change mixedMoment B node5312 node5312Labels = _
    exact sound5312 B hB hF
  simpa only [sourceForm159, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4832, h4837, h4845, h4897, h5222, h5235, h5239, h5252, h5261, h5268, h5296, h5312, reducedSource139] using sourceEq159 B hB

theorem rowSound139 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row139 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck139, numericCheck139, reducedZero139 B hB hF, mul_zero]

theorem reducedZero140 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource140 (mixedVector B) = 0 := by
  have h2193 : mixedVector B (Sum.inr 2193) = Sparse.eval nodeValue2193 (mixedVector B) := by
    change mixedMoment B node2193 node2193Labels = _
    exact sound2193 B hB hF
  have h2208 : mixedVector B (Sum.inr 2208) = Sparse.eval nodeValue2208 (mixedVector B) := by
    change mixedMoment B node2208 node2208Labels = _
    exact sound2208 B hB hF
  have h2218 : mixedVector B (Sum.inr 2218) = Sparse.eval nodeValue2218 (mixedVector B) := by
    change mixedMoment B node2218 node2218Labels = _
    exact sound2218 B hB hF
  have h2268 : mixedVector B (Sum.inr 2268) = Sparse.eval nodeValue2268 (mixedVector B) := by
    change mixedMoment B node2268 node2268Labels = _
    exact sound2268 B hB hF
  have h2664 : mixedVector B (Sum.inr 2664) = Sparse.eval nodeValue2664 (mixedVector B) := by
    change mixedMoment B node2664 node2664Labels = _
    exact sound2664 B hB hF
  have h2680 : mixedVector B (Sum.inr 2680) = Sparse.eval nodeValue2680 (mixedVector B) := by
    change mixedMoment B node2680 node2680Labels = _
    exact sound2680 B hB hF
  have h2691 : mixedVector B (Sum.inr 2691) = Sparse.eval nodeValue2691 (mixedVector B) := by
    change mixedMoment B node2691 node2691Labels = _
    exact sound2691 B hB hF
  have h2712 : mixedVector B (Sum.inr 2712) = Sparse.eval nodeValue2712 (mixedVector B) := by
    change mixedMoment B node2712 node2712Labels = _
    exact sound2712 B hB hF
  have h2726 : mixedVector B (Sum.inr 2726) = Sparse.eval nodeValue2726 (mixedVector B) := by
    change mixedMoment B node2726 node2726Labels = _
    exact sound2726 B hB hF
  have h2734 : mixedVector B (Sum.inr 2734) = Sparse.eval nodeValue2734 (mixedVector B) := by
    change mixedMoment B node2734 node2734Labels = _
    exact sound2734 B hB hF
  have h2770 : mixedVector B (Sum.inr 2770) = Sparse.eval nodeValue2770 (mixedVector B) := by
    change mixedMoment B node2770 node2770Labels = _
    exact sound2770 B hB hF
  have h2790 : mixedVector B (Sum.inr 2790) = Sparse.eval nodeValue2790 (mixedVector B) := by
    change mixedMoment B node2790 node2790Labels = _
    exact sound2790 B hB hF
  have h3090 : mixedVector B (Sum.inr 3090) = Sparse.eval nodeValue3090 (mixedVector B) := by
    change mixedMoment B node3090 node3090Labels = _
    exact sound3090 B hB hF
  simpa only [sourceForm160, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2193, h2208, h2218, h2268, h2664, h2680, h2691, h2712, h2726, h2734, h2770, h2790, h3090, reducedSource140] using sourceEq160 B hB

theorem rowSound140 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row140 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck140, numericCheck140, reducedZero140 B hB hF, mul_zero]

theorem reducedZero141 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource141 (mixedVector B) = 0 := by
  have h2712 : mixedVector B (Sum.inr 2712) = Sparse.eval nodeValue2712 (mixedVector B) := by
    change mixedMoment B node2712 node2712Labels = _
    exact sound2712 B hB hF
  have h2726 : mixedVector B (Sum.inr 2726) = Sparse.eval nodeValue2726 (mixedVector B) := by
    change mixedMoment B node2726 node2726Labels = _
    exact sound2726 B hB hF
  have h2734 : mixedVector B (Sum.inr 2734) = Sparse.eval nodeValue2734 (mixedVector B) := by
    change mixedMoment B node2734 node2734Labels = _
    exact sound2734 B hB hF
  have h2770 : mixedVector B (Sum.inr 2770) = Sparse.eval nodeValue2770 (mixedVector B) := by
    change mixedMoment B node2770 node2770Labels = _
    exact sound2770 B hB hF
  have h3031 : mixedVector B (Sum.inr 3031) = Sparse.eval nodeValue3031 (mixedVector B) := by
    change mixedMoment B node3031 node3031Labels = _
    exact sound3031 B hB hF
  have h3046 : mixedVector B (Sum.inr 3046) = Sparse.eval nodeValue3046 (mixedVector B) := by
    change mixedMoment B node3046 node3046Labels = _
    exact sound3046 B hB hF
  have h3061 : mixedVector B (Sum.inr 3061) = Sparse.eval nodeValue3061 (mixedVector B) := by
    change mixedMoment B node3061 node3061Labels = _
    exact sound3061 B hB hF
  have h3082 : mixedVector B (Sum.inr 3082) = Sparse.eval nodeValue3082 (mixedVector B) := by
    change mixedMoment B node3082 node3082Labels = _
    exact sound3082 B hB hF
  have h3090 : mixedVector B (Sum.inr 3090) = Sparse.eval nodeValue3090 (mixedVector B) := by
    change mixedMoment B node3090 node3090Labels = _
    exact sound3090 B hB hF
  have h3095 : mixedVector B (Sum.inr 3095) = Sparse.eval nodeValue3095 (mixedVector B) := by
    change mixedMoment B node3095 node3095Labels = _
    exact sound3095 B hB hF
  have h3114 : mixedVector B (Sum.inr 3114) = Sparse.eval nodeValue3114 (mixedVector B) := by
    change mixedMoment B node3114 node3114Labels = _
    exact sound3114 B hB hF
  have h3126 : mixedVector B (Sum.inr 3126) = Sparse.eval nodeValue3126 (mixedVector B) := by
    change mixedMoment B node3126 node3126Labels = _
    exact sound3126 B hB hF
  have h3215 : mixedVector B (Sum.inr 3215) = Sparse.eval nodeValue3215 (mixedVector B) := by
    change mixedMoment B node3215 node3215Labels = _
    exact sound3215 B hB hF
  simpa only [sourceForm161, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2712, h2726, h2734, h2770, h3031, h3046, h3061, h3082, h3090, h3095, h3114, h3126, h3215, reducedSource141] using sourceEq161 B hB

theorem rowSound141 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row141 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck141, numericCheck141, reducedZero141 B hB hF, mul_zero]

theorem reducedZero142 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource142 (mixedVector B) = 0 := by
  have h2052 : mixedVector B (Sum.inr 2052) = Sparse.eval nodeValue2052 (mixedVector B) := by
    change mixedMoment B node2052 node2052Labels = _
    exact sound2052 B hB hF
  have h2056 : mixedVector B (Sum.inr 2056) = Sparse.eval nodeValue2056 (mixedVector B) := by
    change mixedMoment B node2056 node2056Labels = _
    exact sound2056 B hB hF
  have h2065 : mixedVector B (Sum.inr 2065) = Sparse.eval nodeValue2065 (mixedVector B) := by
    change mixedMoment B node2065 node2065Labels = _
    exact sound2065 B hB hF
  have h2292 : mixedVector B (Sum.inr 2292) = Sparse.eval nodeValue2292 (mixedVector B) := by
    change mixedMoment B node2292 node2292Labels = _
    exact sound2292 B hB hF
  have h3545 : mixedVector B (Sum.inr 3545) = Sparse.eval nodeValue3545 (mixedVector B) := by
    change mixedMoment B node3545 node3545Labels = _
    exact sound3545 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm162, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2052, h2056, h2065, h2292, h3545, h4085, reducedSource142] using sourceEq162 B hB

theorem rowSound142 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row142 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck142, numericCheck142, reducedZero142 B hB hF, mul_zero]

theorem reducedZero143 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource143 (mixedVector B) = 0 := by
  have h4094 : mixedVector B (Sum.inr 4094) = Sparse.eval nodeValue4094 (mixedVector B) := by
    change mixedMoment B node4094 node4094Labels = _
    exact sound4094 B hB hF
  have h4625 : mixedVector B (Sum.inr 4625) = Sparse.eval nodeValue4625 (mixedVector B) := by
    change mixedMoment B node4625 node4625Labels = _
    exact sound4625 B hB hF
  have h4629 : mixedVector B (Sum.inr 4629) = Sparse.eval nodeValue4629 (mixedVector B) := by
    change mixedMoment B node4629 node4629Labels = _
    exact sound4629 B hB hF
  have h5171 : mixedVector B (Sum.inr 5171) = Sparse.eval nodeValue5171 (mixedVector B) := by
    change mixedMoment B node5171 node5171Labels = _
    exact sound5171 B hB hF
  have h5308 : mixedVector B (Sum.inr 5308) = Sparse.eval nodeValue5308 (mixedVector B) := by
    change mixedMoment B node5308 node5308Labels = _
    exact sound5308 B hB hF
  simpa only [sourceForm163, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4094, h4625, h4629, h5171, h5308, reducedSource143] using sourceEq163 B hB

theorem rowSound143 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row143 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck143, numericCheck143, reducedZero143 B hB hF, mul_zero]

theorem sourceRowsAt128 : MixedData.sourceRows (128 : Fin 2425) =
    MixedData.row128 := by decide +kernel

theorem sourceRowsAt129 : MixedData.sourceRows (129 : Fin 2425) =
    MixedData.row129 := by decide +kernel

theorem sourceRowsAt130 : MixedData.sourceRows (130 : Fin 2425) =
    MixedData.row130 := by decide +kernel

theorem sourceRowsAt131 : MixedData.sourceRows (131 : Fin 2425) =
    MixedData.row131 := by decide +kernel

theorem sourceRowsAt132 : MixedData.sourceRows (132 : Fin 2425) =
    MixedData.row132 := by decide +kernel

theorem sourceRowsAt133 : MixedData.sourceRows (133 : Fin 2425) =
    MixedData.row133 := by decide +kernel

theorem sourceRowsAt134 : MixedData.sourceRows (134 : Fin 2425) =
    MixedData.row134 := by decide +kernel

theorem sourceRowsAt135 : MixedData.sourceRows (135 : Fin 2425) =
    MixedData.row135 := by decide +kernel

theorem sourceRowsAt136 : MixedData.sourceRows (136 : Fin 2425) =
    MixedData.row136 := by decide +kernel

theorem sourceRowsAt137 : MixedData.sourceRows (137 : Fin 2425) =
    MixedData.row137 := by decide +kernel

theorem sourceRowsAt138 : MixedData.sourceRows (138 : Fin 2425) =
    MixedData.row138 := by decide +kernel

theorem sourceRowsAt139 : MixedData.sourceRows (139 : Fin 2425) =
    MixedData.row139 := by decide +kernel

theorem sourceRowsAt140 : MixedData.sourceRows (140 : Fin 2425) =
    MixedData.row140 := by decide +kernel

theorem sourceRowsAt141 : MixedData.sourceRows (141 : Fin 2425) =
    MixedData.row141 := by decide +kernel

theorem sourceRowsAt142 : MixedData.sourceRows (142 : Fin 2425) =
    MixedData.row142 := by decide +kernel

theorem sourceRowsAt143 : MixedData.sourceRows (143 : Fin 2425) =
    MixedData.row143 := by decide +kernel

theorem chunkSound8 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 8) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 128 ∨ k.val = 129 ∨ k.val = 130 ∨ k.val = 131 ∨ k.val = 132 ∨ k.val = 133 ∨ k.val = 134 ∨ k.val = 135 ∨ k.val = 136 ∨ k.val = 137 ∨ k.val = 138 ∨ k.val = 139 ∨ k.val = 140 ∨ k.val = 141 ∨ k.val = 142 ∨ k.val = 143 := by omega
  rcases heq with h128 | h129 | h130 | h131 | h132 | h133 | h134 | h135 | h136 | h137 | h138 | h139 | h140 | h141 | h142 | h143
  · have he : k = (128 : Fin 2425) := Fin.ext h128
    subst k
    rw [sourceRowsAt128]
    exact rowSound128 B hB hF
  · have he : k = (129 : Fin 2425) := Fin.ext h129
    subst k
    rw [sourceRowsAt129]
    exact rowSound129 B hB hF
  · have he : k = (130 : Fin 2425) := Fin.ext h130
    subst k
    rw [sourceRowsAt130]
    exact rowSound130 B hB hF
  · have he : k = (131 : Fin 2425) := Fin.ext h131
    subst k
    rw [sourceRowsAt131]
    exact rowSound131 B hB hF
  · have he : k = (132 : Fin 2425) := Fin.ext h132
    subst k
    rw [sourceRowsAt132]
    exact rowSound132 B hB hF
  · have he : k = (133 : Fin 2425) := Fin.ext h133
    subst k
    rw [sourceRowsAt133]
    exact rowSound133 B hB hF
  · have he : k = (134 : Fin 2425) := Fin.ext h134
    subst k
    rw [sourceRowsAt134]
    exact rowSound134 B hB hF
  · have he : k = (135 : Fin 2425) := Fin.ext h135
    subst k
    rw [sourceRowsAt135]
    exact rowSound135 B hB hF
  · have he : k = (136 : Fin 2425) := Fin.ext h136
    subst k
    rw [sourceRowsAt136]
    exact rowSound136 B hB hF
  · have he : k = (137 : Fin 2425) := Fin.ext h137
    subst k
    rw [sourceRowsAt137]
    exact rowSound137 B hB hF
  · have he : k = (138 : Fin 2425) := Fin.ext h138
    subst k
    rw [sourceRowsAt138]
    exact rowSound138 B hB hF
  · have he : k = (139 : Fin 2425) := Fin.ext h139
    subst k
    rw [sourceRowsAt139]
    exact rowSound139 B hB hF
  · have he : k = (140 : Fin 2425) := Fin.ext h140
    subst k
    rw [sourceRowsAt140]
    exact rowSound140 B hB hF
  · have he : k = (141 : Fin 2425) := Fin.ext h141
    subst k
    rw [sourceRowsAt141]
    exact rowSound141 B hB hF
  · have he : k = (142 : Fin 2425) := Fin.ext h142
    subst k
    rw [sourceRowsAt142]
    exact rowSound142 B hB hF
  · have he : k = (143 : Fin 2425) := Fin.ext h143
    subst k
    rw [sourceRowsAt143]
    exact rowSound143 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
