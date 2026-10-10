import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic103
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources61

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1648 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1648 (mixedVector B) = 0 := by
  have h4551 : mixedVector B (Sum.inr 4551) = Sparse.eval nodeValue4551 (mixedVector B) := by
    change mixedMoment B node4551 node4551Labels = _
    exact sound4551 B hB hF
  have h4555 : mixedVector B (Sum.inr 4555) = Sparse.eval nodeValue4555 (mixedVector B) := by
    change mixedMoment B node4555 node4555Labels = _
    exact sound4555 B hB hF
  have h4559 : mixedVector B (Sum.inr 4559) = Sparse.eval nodeValue4559 (mixedVector B) := by
    change mixedMoment B node4559 node4559Labels = _
    exact sound4559 B hB hF
  have h4625 : mixedVector B (Sum.inr 4625) = Sparse.eval nodeValue4625 (mixedVector B) := by
    change mixedMoment B node4625 node4625Labels = _
    exact sound4625 B hB hF
  have h4970 : mixedVector B (Sum.inr 4970) = Sparse.eval nodeValue4970 (mixedVector B) := by
    change mixedMoment B node4970 node4970Labels = _
    exact sound4970 B hB hF
  have h4979 : mixedVector B (Sum.inr 4979) = Sparse.eval nodeValue4979 (mixedVector B) := by
    change mixedMoment B node4979 node4979Labels = _
    exact sound4979 B hB hF
  have h5113 : mixedVector B (Sum.inr 5113) = Sparse.eval nodeValue5113 (mixedVector B) := by
    change mixedMoment B node5113 node5113Labels = _
    exact sound5113 B hB hF
  have h5168 : mixedVector B (Sum.inr 5168) = Sparse.eval nodeValue5168 (mixedVector B) := by
    change mixedMoment B node5168 node5168Labels = _
    exact sound5168 B hB hF
  have h5171 : mixedVector B (Sum.inr 5171) = Sparse.eval nodeValue5171 (mixedVector B) := by
    change mixedMoment B node5171 node5171Labels = _
    exact sound5171 B hB hF
  have h5176 : mixedVector B (Sum.inr 5176) = Sparse.eval nodeValue5176 (mixedVector B) := by
    change mixedMoment B node5176 node5176Labels = _
    exact sound5176 B hB hF
  have h5308 : mixedVector B (Sum.inr 5308) = Sparse.eval nodeValue5308 (mixedVector B) := by
    change mixedMoment B node5308 node5308Labels = _
    exact sound5308 B hB hF
  have h5312 : mixedVector B (Sum.inr 5312) = Sparse.eval nodeValue5312 (mixedVector B) := by
    change mixedMoment B node5312 node5312Labels = _
    exact sound5312 B hB hF
  have h5441 : mixedVector B (Sum.inr 5441) = Sparse.eval nodeValue5441 (mixedVector B) := by
    change mixedMoment B node5441 node5441Labels = _
    exact sound5441 B hB hF
  simpa only [sourceForm1943, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4551, h4555, h4559, h4625, h4970, h4979, h5113, h5168, h5171, h5176, h5308, h5312, h5441, reducedSource1648] using sourceEq1943 B hB

theorem rowSound1648 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1648 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1648, numericCheck1648, reducedZero1648 B hB hF, mul_zero]

theorem reducedZero1649 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1649 (mixedVector B) = 0 := by
  have h1136 : mixedVector B (Sum.inr 1136) = Sparse.eval nodeValue1136 (mixedVector B) := by
    change mixedMoment B node1136 node1136Labels = _
    exact sound1136 B hB hF
  have h1140 : mixedVector B (Sum.inr 1140) = Sparse.eval nodeValue1140 (mixedVector B) := by
    change mixedMoment B node1140 node1140Labels = _
    exact sound1140 B hB hF
  have h1145 : mixedVector B (Sum.inr 1145) = Sparse.eval nodeValue1145 (mixedVector B) := by
    change mixedMoment B node1145 node1145Labels = _
    exact sound1145 B hB hF
  have h1307 : mixedVector B (Sum.inr 1307) = Sparse.eval nodeValue1307 (mixedVector B) := by
    change mixedMoment B node1307 node1307Labels = _
    exact sound1307 B hB hF
  have h2815 : mixedVector B (Sum.inr 2815) = Sparse.eval nodeValue2815 (mixedVector B) := by
    change mixedMoment B node2815 node2815Labels = _
    exact sound2815 B hB hF
  have h2820 : mixedVector B (Sum.inr 2820) = Sparse.eval nodeValue2820 (mixedVector B) := by
    change mixedMoment B node2820 node2820Labels = _
    exact sound2820 B hB hF
  have h2894 : mixedVector B (Sum.inr 2894) = Sparse.eval nodeValue2894 (mixedVector B) := by
    change mixedMoment B node2894 node2894Labels = _
    exact sound2894 B hB hF
  have h2963 : mixedVector B (Sum.inr 2963) = Sparse.eval nodeValue2963 (mixedVector B) := by
    change mixedMoment B node2963 node2963Labels = _
    exact sound2963 B hB hF
  have h2965 : mixedVector B (Sum.inr 2965) = Sparse.eval nodeValue2965 (mixedVector B) := by
    change mixedMoment B node2965 node2965Labels = _
    exact sound2965 B hB hF
  have h2968 : mixedVector B (Sum.inr 2968) = Sparse.eval nodeValue2968 (mixedVector B) := by
    change mixedMoment B node2968 node2968Labels = _
    exact sound2968 B hB hF
  have h3124 : mixedVector B (Sum.inr 3124) = Sparse.eval nodeValue3124 (mixedVector B) := by
    change mixedMoment B node3124 node3124Labels = _
    exact sound3124 B hB hF
  have h3126 : mixedVector B (Sum.inr 3126) = Sparse.eval nodeValue3126 (mixedVector B) := by
    change mixedMoment B node3126 node3126Labels = _
    exact sound3126 B hB hF
  have h4037 : mixedVector B (Sum.inr 4037) = Sparse.eval nodeValue4037 (mixedVector B) := by
    change mixedMoment B node4037 node4037Labels = _
    exact sound4037 B hB hF
  simpa only [sourceForm1944, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1136, h1140, h1145, h1307, h2815, h2820, h2894, h2963, h2965, h2968, h3124, h3126, h4037, reducedSource1649] using sourceEq1944 B hB

theorem rowSound1649 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1649 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1649, numericCheck1649, reducedZero1649 B hB hF, mul_zero]

theorem reducedZero1650 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1650 (mixedVector B) = 0 := by
  have h4346 : mixedVector B (Sum.inr 4346) = Sparse.eval nodeValue4346 (mixedVector B) := by
    change mixedMoment B node4346 node4346Labels = _
    exact sound4346 B hB hF
  have h4350 : mixedVector B (Sum.inr 4350) = Sparse.eval nodeValue4350 (mixedVector B) := by
    change mixedMoment B node4350 node4350Labels = _
    exact sound4350 B hB hF
  have h4360 : mixedVector B (Sum.inr 4360) = Sparse.eval nodeValue4360 (mixedVector B) := by
    change mixedMoment B node4360 node4360Labels = _
    exact sound4360 B hB hF
  have h4460 : mixedVector B (Sum.inr 4460) = Sparse.eval nodeValue4460 (mixedVector B) := by
    change mixedMoment B node4460 node4460Labels = _
    exact sound4460 B hB hF
  have h4943 : mixedVector B (Sum.inr 4943) = Sparse.eval nodeValue4943 (mixedVector B) := by
    change mixedMoment B node4943 node4943Labels = _
    exact sound4943 B hB hF
  have h4952 : mixedVector B (Sum.inr 4952) = Sparse.eval nodeValue4952 (mixedVector B) := by
    change mixedMoment B node4952 node4952Labels = _
    exact sound4952 B hB hF
  have h5033 : mixedVector B (Sum.inr 5033) = Sparse.eval nodeValue5033 (mixedVector B) := by
    change mixedMoment B node5033 node5033Labels = _
    exact sound5033 B hB hF
  have h5075 : mixedVector B (Sum.inr 5075) = Sparse.eval nodeValue5075 (mixedVector B) := by
    change mixedMoment B node5075 node5075Labels = _
    exact sound5075 B hB hF
  have h5169 : mixedVector B (Sum.inr 5169) = Sparse.eval nodeValue5169 (mixedVector B) := by
    change mixedMoment B node5169 node5169Labels = _
    exact sound5169 B hB hF
  have h5177 : mixedVector B (Sum.inr 5177) = Sparse.eval nodeValue5177 (mixedVector B) := by
    change mixedMoment B node5177 node5177Labels = _
    exact sound5177 B hB hF
  have h5261 : mixedVector B (Sum.inr 5261) = Sparse.eval nodeValue5261 (mixedVector B) := by
    change mixedMoment B node5261 node5261Labels = _
    exact sound5261 B hB hF
  have h5293 : mixedVector B (Sum.inr 5293) = Sparse.eval nodeValue5293 (mixedVector B) := by
    change mixedMoment B node5293 node5293Labels = _
    exact sound5293 B hB hF
  have h5487 : mixedVector B (Sum.inr 5487) = Sparse.eval nodeValue5487 (mixedVector B) := by
    change mixedMoment B node5487 node5487Labels = _
    exact sound5487 B hB hF
  simpa only [sourceForm1945, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4346, h4350, h4360, h4460, h4943, h4952, h5033, h5075, h5169, h5177, h5261, h5293, h5487, reducedSource1650] using sourceEq1945 B hB

theorem rowSound1650 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1650 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1650, numericCheck1650, reducedZero1650 B hB hF, mul_zero]

theorem reducedZero1651 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1651 (mixedVector B) = 0 := by
  have h924 : mixedVector B (Sum.inr 924) = Sparse.eval nodeValue924 (mixedVector B) := by
    change mixedMoment B node924 node924Labels = _
    exact sound924 B hB hF
  have h928 : mixedVector B (Sum.inr 928) = Sparse.eval nodeValue928 (mixedVector B) := by
    change mixedMoment B node928 node928Labels = _
    exact sound928 B hB hF
  have h938 : mixedVector B (Sum.inr 938) = Sparse.eval nodeValue938 (mixedVector B) := by
    change mixedMoment B node938 node938Labels = _
    exact sound938 B hB hF
  have h1043 : mixedVector B (Sum.inr 1043) = Sparse.eval nodeValue1043 (mixedVector B) := by
    change mixedMoment B node1043 node1043Labels = _
    exact sound1043 B hB hF
  have h2334 : mixedVector B (Sum.inr 2334) = Sparse.eval nodeValue2334 (mixedVector B) := by
    change mixedMoment B node2334 node2334Labels = _
    exact sound2334 B hB hF
  have h2344 : mixedVector B (Sum.inr 2344) = Sparse.eval nodeValue2344 (mixedVector B) := by
    change mixedMoment B node2344 node2344Labels = _
    exact sound2344 B hB hF
  have h2425 : mixedVector B (Sum.inr 2425) = Sparse.eval nodeValue2425 (mixedVector B) := by
    change mixedMoment B node2425 node2425Labels = _
    exact sound2425 B hB hF
  have h2482 : mixedVector B (Sum.inr 2482) = Sparse.eval nodeValue2482 (mixedVector B) := by
    change mixedMoment B node2482 node2482Labels = _
    exact sound2482 B hB hF
  have h2595 : mixedVector B (Sum.inr 2595) = Sparse.eval nodeValue2595 (mixedVector B) := by
    change mixedMoment B node2595 node2595Labels = _
    exact sound2595 B hB hF
  have h2605 : mixedVector B (Sum.inr 2605) = Sparse.eval nodeValue2605 (mixedVector B) := by
    change mixedMoment B node2605 node2605Labels = _
    exact sound2605 B hB hF
  have h2726 : mixedVector B (Sum.inr 2726) = Sparse.eval nodeValue2726 (mixedVector B) := by
    change mixedMoment B node2726 node2726Labels = _
    exact sound2726 B hB hF
  have h2767 : mixedVector B (Sum.inr 2767) = Sparse.eval nodeValue2767 (mixedVector B) := by
    change mixedMoment B node2767 node2767Labels = _
    exact sound2767 B hB hF
  have h4000 : mixedVector B (Sum.inr 4000) = Sparse.eval nodeValue4000 (mixedVector B) := by
    change mixedMoment B node4000 node4000Labels = _
    exact sound4000 B hB hF
  simpa only [sourceForm1946, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h924, h928, h938, h1043, h2334, h2344, h2425, h2482, h2595, h2605, h2726, h2767, h4000, reducedSource1651] using sourceEq1946 B hB

theorem rowSound1651 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1651 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1651, numericCheck1651, reducedZero1651 B hB hF, mul_zero]

theorem reducedZero1652 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1652 (mixedVector B) = 0 := by
  have h4352 : mixedVector B (Sum.inr 4352) = Sparse.eval nodeValue4352 (mixedVector B) := by
    change mixedMoment B node4352 node4352Labels = _
    exact sound4352 B hB hF
  have h4356 : mixedVector B (Sum.inr 4356) = Sparse.eval nodeValue4356 (mixedVector B) := by
    change mixedMoment B node4356 node4356Labels = _
    exact sound4356 B hB hF
  have h4361 : mixedVector B (Sum.inr 4361) = Sparse.eval nodeValue4361 (mixedVector B) := by
    change mixedMoment B node4361 node4361Labels = _
    exact sound4361 B hB hF
  have h4463 : mixedVector B (Sum.inr 4463) = Sparse.eval nodeValue4463 (mixedVector B) := by
    change mixedMoment B node4463 node4463Labels = _
    exact sound4463 B hB hF
  have h4546 : mixedVector B (Sum.inr 4546) = Sparse.eval nodeValue4546 (mixedVector B) := by
    change mixedMoment B node4546 node4546Labels = _
    exact sound4546 B hB hF
  have h4558 : mixedVector B (Sum.inr 4558) = Sparse.eval nodeValue4558 (mixedVector B) := by
    change mixedMoment B node4558 node4558Labels = _
    exact sound4558 B hB hF
  have h4625 : mixedVector B (Sum.inr 4625) = Sparse.eval nodeValue4625 (mixedVector B) := by
    change mixedMoment B node4625 node4625Labels = _
    exact sound4625 B hB hF
  have h4948 : mixedVector B (Sum.inr 4948) = Sparse.eval nodeValue4948 (mixedVector B) := by
    change mixedMoment B node4948 node4948Labels = _
    exact sound4948 B hB hF
  have h4953 : mixedVector B (Sum.inr 4953) = Sparse.eval nodeValue4953 (mixedVector B) := by
    change mixedMoment B node4953 node4953Labels = _
    exact sound4953 B hB hF
  have h4972 : mixedVector B (Sum.inr 4972) = Sparse.eval nodeValue4972 (mixedVector B) := by
    change mixedMoment B node4972 node4972Labels = _
    exact sound4972 B hB hF
  have h5037 : mixedVector B (Sum.inr 5037) = Sparse.eval nodeValue5037 (mixedVector B) := by
    change mixedMoment B node5037 node5037Labels = _
    exact sound5037 B hB hF
  have h5078 : mixedVector B (Sum.inr 5078) = Sparse.eval nodeValue5078 (mixedVector B) := by
    change mixedMoment B node5078 node5078Labels = _
    exact sound5078 B hB hF
  have h5169 : mixedVector B (Sum.inr 5169) = Sparse.eval nodeValue5169 (mixedVector B) := by
    change mixedMoment B node5169 node5169Labels = _
    exact sound5169 B hB hF
  have h5172 : mixedVector B (Sum.inr 5172) = Sparse.eval nodeValue5172 (mixedVector B) := by
    change mixedMoment B node5172 node5172Labels = _
    exact sound5172 B hB hF
  have h5174 : mixedVector B (Sum.inr 5174) = Sparse.eval nodeValue5174 (mixedVector B) := by
    change mixedMoment B node5174 node5174Labels = _
    exact sound5174 B hB hF
  have h5176 : mixedVector B (Sum.inr 5176) = Sparse.eval nodeValue5176 (mixedVector B) := by
    change mixedMoment B node5176 node5176Labels = _
    exact sound5176 B hB hF
  have h5177 : mixedVector B (Sum.inr 5177) = Sparse.eval nodeValue5177 (mixedVector B) := by
    change mixedMoment B node5177 node5177Labels = _
    exact sound5177 B hB hF
  have h5294 : mixedVector B (Sum.inr 5294) = Sparse.eval nodeValue5294 (mixedVector B) := by
    change mixedMoment B node5294 node5294Labels = _
    exact sound5294 B hB hF
  have h5296 : mixedVector B (Sum.inr 5296) = Sparse.eval nodeValue5296 (mixedVector B) := by
    change mixedMoment B node5296 node5296Labels = _
    exact sound5296 B hB hF
  have h5309 : mixedVector B (Sum.inr 5309) = Sparse.eval nodeValue5309 (mixedVector B) := by
    change mixedMoment B node5309 node5309Labels = _
    exact sound5309 B hB hF
  have h5442 : mixedVector B (Sum.inr 5442) = Sparse.eval nodeValue5442 (mixedVector B) := by
    change mixedMoment B node5442 node5442Labels = _
    exact sound5442 B hB hF
  simpa only [sourceForm1947, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4352, h4356, h4361, h4463, h4546, h4558, h4625, h4948, h4953, h4972, h5037, h5078, h5169, h5172, h5174, h5176, h5177, h5294, h5296, h5309, h5442, reducedSource1652] using sourceEq1947 B hB

theorem rowSound1652 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1652 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1652, numericCheck1652, reducedZero1652 B hB hF, mul_zero]

theorem reducedZero1653 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1653 (mixedVector B) = 0 := by
  have h930 : mixedVector B (Sum.inr 930) = Sparse.eval nodeValue930 (mixedVector B) := by
    change mixedMoment B node930 node930Labels = _
    exact sound930 B hB hF
  have h934 : mixedVector B (Sum.inr 934) = Sparse.eval nodeValue934 (mixedVector B) := by
    change mixedMoment B node934 node934Labels = _
    exact sound934 B hB hF
  have h939 : mixedVector B (Sum.inr 939) = Sparse.eval nodeValue939 (mixedVector B) := by
    change mixedMoment B node939 node939Labels = _
    exact sound939 B hB hF
  have h1046 : mixedVector B (Sum.inr 1046) = Sparse.eval nodeValue1046 (mixedVector B) := by
    change mixedMoment B node1046 node1046Labels = _
    exact sound1046 B hB hF
  have h1131 : mixedVector B (Sum.inr 1131) = Sparse.eval nodeValue1131 (mixedVector B) := by
    change mixedMoment B node1131 node1131Labels = _
    exact sound1131 B hB hF
  have h1144 : mixedVector B (Sum.inr 1144) = Sparse.eval nodeValue1144 (mixedVector B) := by
    change mixedMoment B node1144 node1144Labels = _
    exact sound1144 B hB hF
  have h1304 : mixedVector B (Sum.inr 1304) = Sparse.eval nodeValue1304 (mixedVector B) := by
    change mixedMoment B node1304 node1304Labels = _
    exact sound1304 B hB hF
  have h2339 : mixedVector B (Sum.inr 2339) = Sparse.eval nodeValue2339 (mixedVector B) := by
    change mixedMoment B node2339 node2339Labels = _
    exact sound2339 B hB hF
  have h2345 : mixedVector B (Sum.inr 2345) = Sparse.eval nodeValue2345 (mixedVector B) := by
    change mixedMoment B node2345 node2345Labels = _
    exact sound2345 B hB hF
  have h2429 : mixedVector B (Sum.inr 2429) = Sparse.eval nodeValue2429 (mixedVector B) := by
    change mixedMoment B node2429 node2429Labels = _
    exact sound2429 B hB hF
  have h2434 : mixedVector B (Sum.inr 2434) = Sparse.eval nodeValue2434 (mixedVector B) := by
    change mixedMoment B node2434 node2434Labels = _
    exact sound2434 B hB hF
  have h2485 : mixedVector B (Sum.inr 2485) = Sparse.eval nodeValue2485 (mixedVector B) := by
    change mixedMoment B node2485 node2485Labels = _
    exact sound2485 B hB hF
  have h2599 : mixedVector B (Sum.inr 2599) = Sparse.eval nodeValue2599 (mixedVector B) := by
    change mixedMoment B node2599 node2599Labels = _
    exact sound2599 B hB hF
  have h2601 : mixedVector B (Sum.inr 2601) = Sparse.eval nodeValue2601 (mixedVector B) := by
    change mixedMoment B node2601 node2601Labels = _
    exact sound2601 B hB hF
  have h2604 : mixedVector B (Sum.inr 2604) = Sparse.eval nodeValue2604 (mixedVector B) := by
    change mixedMoment B node2604 node2604Labels = _
    exact sound2604 B hB hF
  have h2768 : mixedVector B (Sum.inr 2768) = Sparse.eval nodeValue2768 (mixedVector B) := by
    change mixedMoment B node2768 node2768Labels = _
    exact sound2768 B hB hF
  have h2770 : mixedVector B (Sum.inr 2770) = Sparse.eval nodeValue2770 (mixedVector B) := by
    change mixedMoment B node2770 node2770Labels = _
    exact sound2770 B hB hF
  have h2960 : mixedVector B (Sum.inr 2960) = Sparse.eval nodeValue2960 (mixedVector B) := by
    change mixedMoment B node2960 node2960Labels = _
    exact sound2960 B hB hF
  have h2969 : mixedVector B (Sum.inr 2969) = Sparse.eval nodeValue2969 (mixedVector B) := by
    change mixedMoment B node2969 node2969Labels = _
    exact sound2969 B hB hF
  have h3123 : mixedVector B (Sum.inr 3123) = Sparse.eval nodeValue3123 (mixedVector B) := by
    change mixedMoment B node3123 node3123Labels = _
    exact sound3123 B hB hF
  have h4001 : mixedVector B (Sum.inr 4001) = Sparse.eval nodeValue4001 (mixedVector B) := by
    change mixedMoment B node4001 node4001Labels = _
    exact sound4001 B hB hF
  simpa only [sourceForm1948, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h930, h934, h939, h1046, h1131, h1144, h1304, h2339, h2345, h2429, h2434, h2485, h2599, h2601, h2604, h2768, h2770, h2960, h2969, h3123, h4001, reducedSource1653] using sourceEq1948 B hB

theorem rowSound1653 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1653 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1653, numericCheck1653, reducedZero1653 B hB hF, mul_zero]

theorem reducedZero1654 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1654 (mixedVector B) = 0 := by
  have h4807 : mixedVector B (Sum.inr 4807) = Sparse.eval nodeValue4807 (mixedVector B) := by
    change mixedMoment B node4807 node4807Labels = _
    exact sound4807 B hB hF
  have h4841 : mixedVector B (Sum.inr 4841) = Sparse.eval nodeValue4841 (mixedVector B) := by
    change mixedMoment B node4841 node4841Labels = _
    exact sound4841 B hB hF
  have h4843 : mixedVector B (Sum.inr 4843) = Sparse.eval nodeValue4843 (mixedVector B) := by
    change mixedMoment B node4843 node4843Labels = _
    exact sound4843 B hB hF
  have h4871 : mixedVector B (Sum.inr 4871) = Sparse.eval nodeValue4871 (mixedVector B) := by
    change mixedMoment B node4871 node4871Labels = _
    exact sound4871 B hB hF
  have h5075 : mixedVector B (Sum.inr 5075) = Sparse.eval nodeValue5075 (mixedVector B) := by
    change mixedMoment B node5075 node5075Labels = _
    exact sound5075 B hB hF
  have h5078 : mixedVector B (Sum.inr 5078) = Sparse.eval nodeValue5078 (mixedVector B) := by
    change mixedMoment B node5078 node5078Labels = _
    exact sound5078 B hB hF
  have h5107 : mixedVector B (Sum.inr 5107) = Sparse.eval nodeValue5107 (mixedVector B) := by
    change mixedMoment B node5107 node5107Labels = _
    exact sound5107 B hB hF
  have h5109 : mixedVector B (Sum.inr 5109) = Sparse.eval nodeValue5109 (mixedVector B) := by
    change mixedMoment B node5109 node5109Labels = _
    exact sound5109 B hB hF
  have h5128 : mixedVector B (Sum.inr 5128) = Sparse.eval nodeValue5128 (mixedVector B) := by
    change mixedMoment B node5128 node5128Labels = _
    exact sound5128 B hB hF
  have h5139 : mixedVector B (Sum.inr 5139) = Sparse.eval nodeValue5139 (mixedVector B) := by
    change mixedMoment B node5139 node5139Labels = _
    exact sound5139 B hB hF
  have h5171 : mixedVector B (Sum.inr 5171) = Sparse.eval nodeValue5171 (mixedVector B) := by
    change mixedMoment B node5171 node5171Labels = _
    exact sound5171 B hB hF
  simpa only [sourceForm1949, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4807, h4841, h4843, h4871, h5075, h5078, h5107, h5109, h5128, h5139, h5171, reducedSource1654] using sourceEq1949 B hB

theorem rowSound1654 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1654 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1654, numericCheck1654, reducedZero1654 B hB hF, mul_zero]

theorem reducedZero1655 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1655 (mixedVector B) = 0 := by
  have h4237 : mixedVector B (Sum.inr 4237) = Sparse.eval nodeValue4237 (mixedVector B) := by
    change mixedMoment B node4237 node4237Labels = _
    exact sound4237 B hB hF
  have h4240 : mixedVector B (Sum.inr 4240) = Sparse.eval nodeValue4240 (mixedVector B) := by
    change mixedMoment B node4240 node4240Labels = _
    exact sound4240 B hB hF
  have h4243 : mixedVector B (Sum.inr 4243) = Sparse.eval nodeValue4243 (mixedVector B) := by
    change mixedMoment B node4243 node4243Labels = _
    exact sound4243 B hB hF
  have h4276 : mixedVector B (Sum.inr 4276) = Sparse.eval nodeValue4276 (mixedVector B) := by
    change mixedMoment B node4276 node4276Labels = _
    exact sound4276 B hB hF
  have h4538 : mixedVector B (Sum.inr 4538) = Sparse.eval nodeValue4538 (mixedVector B) := by
    change mixedMoment B node4538 node4538Labels = _
    exact sound4538 B hB hF
  have h4557 : mixedVector B (Sum.inr 4557) = Sparse.eval nodeValue4557 (mixedVector B) := by
    change mixedMoment B node4557 node4557Labels = _
    exact sound4557 B hB hF
  have h4621 : mixedVector B (Sum.inr 4621) = Sparse.eval nodeValue4621 (mixedVector B) := by
    change mixedMoment B node4621 node4621Labels = _
    exact sound4621 B hB hF
  have h4686 : mixedVector B (Sum.inr 4686) = Sparse.eval nodeValue4686 (mixedVector B) := by
    change mixedMoment B node4686 node4686Labels = _
    exact sound4686 B hB hF
  have h4693 : mixedVector B (Sum.inr 4693) = Sparse.eval nodeValue4693 (mixedVector B) := by
    change mixedMoment B node4693 node4693Labels = _
    exact sound4693 B hB hF
  have h4723 : mixedVector B (Sum.inr 4723) = Sparse.eval nodeValue4723 (mixedVector B) := by
    change mixedMoment B node4723 node4723Labels = _
    exact sound4723 B hB hF
  have h4727 : mixedVector B (Sum.inr 4727) = Sparse.eval nodeValue4727 (mixedVector B) := by
    change mixedMoment B node4727 node4727Labels = _
    exact sound4727 B hB hF
  have h4747 : mixedVector B (Sum.inr 4747) = Sparse.eval nodeValue4747 (mixedVector B) := by
    change mixedMoment B node4747 node4747Labels = _
    exact sound4747 B hB hF
  have h4869 : mixedVector B (Sum.inr 4869) = Sparse.eval nodeValue4869 (mixedVector B) := by
    change mixedMoment B node4869 node4869Labels = _
    exact sound4869 B hB hF
  have h4871 : mixedVector B (Sum.inr 4871) = Sparse.eval nodeValue4871 (mixedVector B) := by
    change mixedMoment B node4871 node4871Labels = _
    exact sound4871 B hB hF
  have h4874 : mixedVector B (Sum.inr 4874) = Sparse.eval nodeValue4874 (mixedVector B) := by
    change mixedMoment B node4874 node4874Labels = _
    exact sound4874 B hB hF
  have h4898 : mixedVector B (Sum.inr 4898) = Sparse.eval nodeValue4898 (mixedVector B) := by
    change mixedMoment B node4898 node4898Labels = _
    exact sound4898 B hB hF
  have h4899 : mixedVector B (Sum.inr 4899) = Sparse.eval nodeValue4899 (mixedVector B) := by
    change mixedMoment B node4899 node4899Labels = _
    exact sound4899 B hB hF
  have h5170 : mixedVector B (Sum.inr 5170) = Sparse.eval nodeValue5170 (mixedVector B) := by
    change mixedMoment B node5170 node5170Labels = _
    exact sound5170 B hB hF
  have h5176 : mixedVector B (Sum.inr 5176) = Sparse.eval nodeValue5176 (mixedVector B) := by
    change mixedMoment B node5176 node5176Labels = _
    exact sound5176 B hB hF
  have h5310 : mixedVector B (Sum.inr 5310) = Sparse.eval nodeValue5310 (mixedVector B) := by
    change mixedMoment B node5310 node5310Labels = _
    exact sound5310 B hB hF
  have h5443 : mixedVector B (Sum.inr 5443) = Sparse.eval nodeValue5443 (mixedVector B) := by
    change mixedMoment B node5443 node5443Labels = _
    exact sound5443 B hB hF
  simpa only [sourceForm1950, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4237, h4240, h4243, h4276, h4538, h4557, h4621, h4686, h4693, h4723, h4727, h4747, h4869, h4871, h4874, h4898, h4899, h5170, h5176, h5310, h5443, reducedSource1655] using sourceEq1950 B hB

theorem rowSound1655 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1655 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1655, numericCheck1655, reducedZero1655 B hB hF, mul_zero]

theorem reducedZero1656 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1656 (mixedVector B) = 0 := by
  have h737 : mixedVector B (Sum.inr 737) = Sparse.eval nodeValue737 (mixedVector B) := by
    change mixedMoment B node737 node737Labels = _
    exact sound737 B hB hF
  have h740 : mixedVector B (Sum.inr 740) = Sparse.eval nodeValue740 (mixedVector B) := by
    change mixedMoment B node740 node740Labels = _
    exact sound740 B hB hF
  have h743 : mixedVector B (Sum.inr 743) = Sparse.eval nodeValue743 (mixedVector B) := by
    change mixedMoment B node743 node743Labels = _
    exact sound743 B hB hF
  have h828 : mixedVector B (Sum.inr 828) = Sparse.eval nodeValue828 (mixedVector B) := by
    change mixedMoment B node828 node828Labels = _
    exact sound828 B hB hF
  have h1123 : mixedVector B (Sum.inr 1123) = Sparse.eval nodeValue1123 (mixedVector B) := by
    change mixedMoment B node1123 node1123Labels = _
    exact sound1123 B hB hF
  have h1143 : mixedVector B (Sum.inr 1143) = Sparse.eval nodeValue1143 (mixedVector B) := by
    change mixedMoment B node1143 node1143Labels = _
    exact sound1143 B hB hF
  have h1297 : mixedVector B (Sum.inr 1297) = Sparse.eval nodeValue1297 (mixedVector B) := by
    change mixedMoment B node1297 node1297Labels = _
    exact sound1297 B hB hF
  have h1812 : mixedVector B (Sum.inr 1812) = Sparse.eval nodeValue1812 (mixedVector B) := by
    change mixedMoment B node1812 node1812Labels = _
    exact sound1812 B hB hF
  have h1819 : mixedVector B (Sum.inr 1819) = Sparse.eval nodeValue1819 (mixedVector B) := by
    change mixedMoment B node1819 node1819Labels = _
    exact sound1819 B hB hF
  have h1877 : mixedVector B (Sum.inr 1877) = Sparse.eval nodeValue1877 (mixedVector B) := by
    change mixedMoment B node1877 node1877Labels = _
    exact sound1877 B hB hF
  have h1881 : mixedVector B (Sum.inr 1881) = Sparse.eval nodeValue1881 (mixedVector B) := by
    change mixedMoment B node1881 node1881Labels = _
    exact sound1881 B hB hF
  have h1926 : mixedVector B (Sum.inr 1926) = Sparse.eval nodeValue1926 (mixedVector B) := by
    change mixedMoment B node1926 node1926Labels = _
    exact sound1926 B hB hF
  have h2110 : mixedVector B (Sum.inr 2110) = Sparse.eval nodeValue2110 (mixedVector B) := by
    change mixedMoment B node2110 node2110Labels = _
    exact sound2110 B hB hF
  have h2112 : mixedVector B (Sum.inr 2112) = Sparse.eval nodeValue2112 (mixedVector B) := by
    change mixedMoment B node2112 node2112Labels = _
    exact sound2112 B hB hF
  have h2115 : mixedVector B (Sum.inr 2115) = Sparse.eval nodeValue2115 (mixedVector B) := by
    change mixedMoment B node2115 node2115Labels = _
    exact sound2115 B hB hF
  have h2279 : mixedVector B (Sum.inr 2279) = Sparse.eval nodeValue2279 (mixedVector B) := by
    change mixedMoment B node2279 node2279Labels = _
    exact sound2279 B hB hF
  have h2281 : mixedVector B (Sum.inr 2281) = Sparse.eval nodeValue2281 (mixedVector B) := by
    change mixedMoment B node2281 node2281Labels = _
    exact sound2281 B hB hF
  have h2954 : mixedVector B (Sum.inr 2954) = Sparse.eval nodeValue2954 (mixedVector B) := by
    change mixedMoment B node2954 node2954Labels = _
    exact sound2954 B hB hF
  have h2968 : mixedVector B (Sum.inr 2968) = Sparse.eval nodeValue2968 (mixedVector B) := by
    change mixedMoment B node2968 node2968Labels = _
    exact sound2968 B hB hF
  have h3121 : mixedVector B (Sum.inr 3121) = Sparse.eval nodeValue3121 (mixedVector B) := by
    change mixedMoment B node3121 node3121Labels = _
    exact sound3121 B hB hF
  have h3889 : mixedVector B (Sum.inr 3889) = Sparse.eval nodeValue3889 (mixedVector B) := by
    change mixedMoment B node3889 node3889Labels = _
    exact sound3889 B hB hF
  simpa only [sourceForm1951, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h737, h740, h743, h828, h1123, h1143, h1297, h1812, h1819, h1877, h1881, h1926, h2110, h2112, h2115, h2279, h2281, h2954, h2968, h3121, h3889, reducedSource1656] using sourceEq1951 B hB

theorem rowSound1656 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1656 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1656, numericCheck1656, reducedZero1656 B hB hF, mul_zero]

theorem reducedZero1657 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1657 (mixedVector B) = 0 := by
  have h4353 : mixedVector B (Sum.inr 4353) = Sparse.eval nodeValue4353 (mixedVector B) := by
    change mixedMoment B node4353 node4353Labels = _
    exact sound4353 B hB hF
  have h4358 : mixedVector B (Sum.inr 4358) = Sparse.eval nodeValue4358 (mixedVector B) := by
    change mixedMoment B node4358 node4358Labels = _
    exact sound4358 B hB hF
  have h4362 : mixedVector B (Sum.inr 4362) = Sparse.eval nodeValue4362 (mixedVector B) := by
    change mixedMoment B node4362 node4362Labels = _
    exact sound4362 B hB hF
  have h4367 : mixedVector B (Sum.inr 4367) = Sparse.eval nodeValue4367 (mixedVector B) := by
    change mixedMoment B node4367 node4367Labels = _
    exact sound4367 B hB hF
  have h4374 : mixedVector B (Sum.inr 4374) = Sparse.eval nodeValue4374 (mixedVector B) := by
    change mixedMoment B node4374 node4374Labels = _
    exact sound4374 B hB hF
  have h4463 : mixedVector B (Sum.inr 4463) = Sparse.eval nodeValue4463 (mixedVector B) := by
    change mixedMoment B node4463 node4463Labels = _
    exact sound4463 B hB hF
  have h4464 : mixedVector B (Sum.inr 4464) = Sparse.eval nodeValue4464 (mixedVector B) := by
    change mixedMoment B node4464 node4464Labels = _
    exact sound4464 B hB hF
  have h4699 : mixedVector B (Sum.inr 4699) = Sparse.eval nodeValue4699 (mixedVector B) := by
    change mixedMoment B node4699 node4699Labels = _
    exact sound4699 B hB hF
  have h4705 : mixedVector B (Sum.inr 4705) = Sparse.eval nodeValue4705 (mixedVector B) := by
    change mixedMoment B node4705 node4705Labels = _
    exact sound4705 B hB hF
  have h4772 : mixedVector B (Sum.inr 4772) = Sparse.eval nodeValue4772 (mixedVector B) := by
    change mixedMoment B node4772 node4772Labels = _
    exact sound4772 B hB hF
  have h4777 : mixedVector B (Sum.inr 4777) = Sparse.eval nodeValue4777 (mixedVector B) := by
    change mixedMoment B node4777 node4777Labels = _
    exact sound4777 B hB hF
  have h4807 : mixedVector B (Sum.inr 4807) = Sparse.eval nodeValue4807 (mixedVector B) := by
    change mixedMoment B node4807 node4807Labels = _
    exact sound4807 B hB hF
  have h4853 : mixedVector B (Sum.inr 4853) = Sparse.eval nodeValue4853 (mixedVector B) := by
    change mixedMoment B node4853 node4853Labels = _
    exact sound4853 B hB hF
  have h4866 : mixedVector B (Sum.inr 4866) = Sparse.eval nodeValue4866 (mixedVector B) := by
    change mixedMoment B node4866 node4866Labels = _
    exact sound4866 B hB hF
  have h4875 : mixedVector B (Sum.inr 4875) = Sparse.eval nodeValue4875 (mixedVector B) := by
    change mixedMoment B node4875 node4875Labels = _
    exact sound4875 B hB hF
  have h4890 : mixedVector B (Sum.inr 4890) = Sparse.eval nodeValue4890 (mixedVector B) := by
    change mixedMoment B node4890 node4890Labels = _
    exact sound4890 B hB hF
  have h4895 : mixedVector B (Sum.inr 4895) = Sparse.eval nodeValue4895 (mixedVector B) := by
    change mixedMoment B node4895 node4895Labels = _
    exact sound4895 B hB hF
  have h5173 : mixedVector B (Sum.inr 5173) = Sparse.eval nodeValue5173 (mixedVector B) := by
    change mixedMoment B node5173 node5173Labels = _
    exact sound5173 B hB hF
  have h5175 : mixedVector B (Sum.inr 5175) = Sparse.eval nodeValue5175 (mixedVector B) := by
    change mixedMoment B node5175 node5175Labels = _
    exact sound5175 B hB hF
  have h5295 : mixedVector B (Sum.inr 5295) = Sparse.eval nodeValue5295 (mixedVector B) := by
    change mixedMoment B node5295 node5295Labels = _
    exact sound5295 B hB hF
  have h5304 : mixedVector B (Sum.inr 5304) = Sparse.eval nodeValue5304 (mixedVector B) := by
    change mixedMoment B node5304 node5304Labels = _
    exact sound5304 B hB hF
  simpa only [sourceForm1952, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4353, h4358, h4362, h4367, h4374, h4463, h4464, h4699, h4705, h4772, h4777, h4807, h4853, h4866, h4875, h4890, h4895, h5173, h5175, h5295, h5304, reducedSource1657] using sourceEq1952 B hB

theorem rowSound1657 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1657 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1657, numericCheck1657, reducedZero1657 B hB hF, mul_zero]

theorem reducedZero1658 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1658 (mixedVector B) = 0 := by
  have h1686 : mixedVector B (Sum.inr 1686) = Sparse.eval nodeValue1686 (mixedVector B) := by
    change mixedMoment B node1686 node1686Labels = _
    exact sound1686 B hB hF
  have h1687 : mixedVector B (Sum.inr 1687) = Sparse.eval nodeValue1687 (mixedVector B) := by
    change mixedMoment B node1687 node1687Labels = _
    exact sound1687 B hB hF
  have h1695 : mixedVector B (Sum.inr 1695) = Sparse.eval nodeValue1695 (mixedVector B) := by
    change mixedMoment B node1695 node1695Labels = _
    exact sound1695 B hB hF
  have h1720 : mixedVector B (Sum.inr 1720) = Sparse.eval nodeValue1720 (mixedVector B) := by
    change mixedMoment B node1720 node1720Labels = _
    exact sound1720 B hB hF
  have h1745 : mixedVector B (Sum.inr 1745) = Sparse.eval nodeValue1745 (mixedVector B) := by
    change mixedMoment B node1745 node1745Labels = _
    exact sound1745 B hB hF
  have h1748 : mixedVector B (Sum.inr 1748) = Sparse.eval nodeValue1748 (mixedVector B) := by
    change mixedMoment B node1748 node1748Labels = _
    exact sound1748 B hB hF
  have h1750 : mixedVector B (Sum.inr 1750) = Sparse.eval nodeValue1750 (mixedVector B) := by
    change mixedMoment B node1750 node1750Labels = _
    exact sound1750 B hB hF
  have h2198 : mixedVector B (Sum.inr 2198) = Sparse.eval nodeValue2198 (mixedVector B) := by
    change mixedMoment B node2198 node2198Labels = _
    exact sound2198 B hB hF
  have h2223 : mixedVector B (Sum.inr 2223) = Sparse.eval nodeValue2223 (mixedVector B) := by
    change mixedMoment B node2223 node2223Labels = _
    exact sound2223 B hB hF
  have h2224 : mixedVector B (Sum.inr 2224) = Sparse.eval nodeValue2224 (mixedVector B) := by
    change mixedMoment B node2224 node2224Labels = _
    exact sound2224 B hB hF
  have h2256 : mixedVector B (Sum.inr 2256) = Sparse.eval nodeValue2256 (mixedVector B) := by
    change mixedMoment B node2256 node2256Labels = _
    exact sound2256 B hB hF
  have h2259 : mixedVector B (Sum.inr 2259) = Sparse.eval nodeValue2259 (mixedVector B) := by
    change mixedMoment B node2259 node2259Labels = _
    exact sound2259 B hB hF
  have h2260 : mixedVector B (Sum.inr 2260) = Sparse.eval nodeValue2260 (mixedVector B) := by
    change mixedMoment B node2260 node2260Labels = _
    exact sound2260 B hB hF
  have h2286 : mixedVector B (Sum.inr 2286) = Sparse.eval nodeValue2286 (mixedVector B) := by
    change mixedMoment B node2286 node2286Labels = _
    exact sound2286 B hB hF
  have h2288 : mixedVector B (Sum.inr 2288) = Sparse.eval nodeValue2288 (mixedVector B) := by
    change mixedMoment B node2288 node2288Labels = _
    exact sound2288 B hB hF
  have h2290 : mixedVector B (Sum.inr 2290) = Sparse.eval nodeValue2290 (mixedVector B) := by
    change mixedMoment B node2290 node2290Labels = _
    exact sound2290 B hB hF
  have h2291 : mixedVector B (Sum.inr 2291) = Sparse.eval nodeValue2291 (mixedVector B) := by
    change mixedMoment B node2291 node2291Labels = _
    exact sound2291 B hB hF
  have h2735 : mixedVector B (Sum.inr 2735) = Sparse.eval nodeValue2735 (mixedVector B) := by
    change mixedMoment B node2735 node2735Labels = _
    exact sound2735 B hB hF
  have h2761 : mixedVector B (Sum.inr 2761) = Sparse.eval nodeValue2761 (mixedVector B) := by
    change mixedMoment B node2761 node2761Labels = _
    exact sound2761 B hB hF
  have h2781 : mixedVector B (Sum.inr 2781) = Sparse.eval nodeValue2781 (mixedVector B) := by
    change mixedMoment B node2781 node2781Labels = _
    exact sound2781 B hB hF
  have h2782 : mixedVector B (Sum.inr 2782) = Sparse.eval nodeValue2782 (mixedVector B) := by
    change mixedMoment B node2782 node2782Labels = _
    exact sound2782 B hB hF
  simpa only [sourceForm1953, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1686, h1687, h1695, h1720, h1745, h1748, h1750, h2198, h2223, h2224, h2256, h2259, h2260, h2286, h2288, h2290, h2291, h2735, h2761, h2781, h2782, reducedSource1658] using sourceEq1953 B hB

theorem rowSound1658 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1658 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1658, numericCheck1658, reducedZero1658 B hB hF, mul_zero]

theorem reducedZero1659 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1659 (mixedVector B) = 0 := by
  have h953 : mixedVector B (Sum.inr 953) = Sparse.eval nodeValue953 (mixedVector B) := by
    change mixedMoment B node953 node953Labels = _
    exact sound953 B hB hF
  have h1831 : mixedVector B (Sum.inr 1831) = Sparse.eval nodeValue1831 (mixedVector B) := by
    change mixedMoment B node1831 node1831Labels = _
    exact sound1831 B hB hF
  have h1979 : mixedVector B (Sum.inr 1979) = Sparse.eval nodeValue1979 (mixedVector B) := by
    change mixedMoment B node1979 node1979Labels = _
    exact sound1979 B hB hF
  have h2112 : mixedVector B (Sum.inr 2112) = Sparse.eval nodeValue2112 (mixedVector B) := by
    change mixedMoment B node2112 node2112Labels = _
    exact sound2112 B hB hF
  have h2116 : mixedVector B (Sum.inr 2116) = Sparse.eval nodeValue2116 (mixedVector B) := by
    change mixedMoment B node2116 node2116Labels = _
    exact sound2116 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1954, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h953, h1831, h1979, h2112, h2116, h4083, reducedSource1659] using sourceEq1954 B hB

theorem rowSound1659 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1659 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1659, numericCheck1659, reducedZero1659 B hB hF, mul_zero]

theorem reducedZero1660 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1660 (mixedVector B) = 0 := by
  have h1336 : mixedVector B (Sum.inr 1336) = Sparse.eval nodeValue1336 (mixedVector B) := by
    change mixedMoment B node1336 node1336Labels = _
    exact sound1336 B hB hF
  have h1973 : mixedVector B (Sum.inr 1973) = Sparse.eval nodeValue1973 (mixedVector B) := by
    change mixedMoment B node1973 node1973Labels = _
    exact sound1973 B hB hF
  have h1979 : mixedVector B (Sum.inr 1979) = Sparse.eval nodeValue1979 (mixedVector B) := by
    change mixedMoment B node1979 node1979Labels = _
    exact sound1979 B hB hF
  have h2025 : mixedVector B (Sum.inr 2025) = Sparse.eval nodeValue2025 (mixedVector B) := by
    change mixedMoment B node2025 node2025Labels = _
    exact sound2025 B hB hF
  have h2112 : mixedVector B (Sum.inr 2112) = Sparse.eval nodeValue2112 (mixedVector B) := by
    change mixedMoment B node2112 node2112Labels = _
    exact sound2112 B hB hF
  have h2952 : mixedVector B (Sum.inr 2952) = Sparse.eval nodeValue2952 (mixedVector B) := by
    change mixedMoment B node2952 node2952Labels = _
    exact sound2952 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1955, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1336, h1973, h1979, h2025, h2112, h2952, h4083, reducedSource1660] using sourceEq1955 B hB

theorem rowSound1660 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1660 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1660, numericCheck1660, reducedZero1660 B hB hF, mul_zero]

theorem reducedZero1661 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1661 (mixedVector B) = 0 := by
  have h4486 : mixedVector B (Sum.inr 4486) = Sparse.eval nodeValue4486 (mixedVector B) := by
    change mixedMoment B node4486 node4486Labels = _
    exact sound4486 B hB hF
  have h4490 : mixedVector B (Sum.inr 4490) = Sparse.eval nodeValue4490 (mixedVector B) := by
    change mixedMoment B node4490 node4490Labels = _
    exact sound4490 B hB hF
  have h4492 : mixedVector B (Sum.inr 4492) = Sparse.eval nodeValue4492 (mixedVector B) := by
    change mixedMoment B node4492 node4492Labels = _
    exact sound4492 B hB hF
  have h4504 : mixedVector B (Sum.inr 4504) = Sparse.eval nodeValue4504 (mixedVector B) := by
    change mixedMoment B node4504 node4504Labels = _
    exact sound4504 B hB hF
  have h4807 : mixedVector B (Sum.inr 4807) = Sparse.eval nodeValue4807 (mixedVector B) := by
    change mixedMoment B node4807 node4807Labels = _
    exact sound4807 B hB hF
  have h4808 : mixedVector B (Sum.inr 4808) = Sparse.eval nodeValue4808 (mixedVector B) := by
    change mixedMoment B node4808 node4808Labels = _
    exact sound4808 B hB hF
  have h4824 : mixedVector B (Sum.inr 4824) = Sparse.eval nodeValue4824 (mixedVector B) := by
    change mixedMoment B node4824 node4824Labels = _
    exact sound4824 B hB hF
  have h4827 : mixedVector B (Sum.inr 4827) = Sparse.eval nodeValue4827 (mixedVector B) := by
    change mixedMoment B node4827 node4827Labels = _
    exact sound4827 B hB hF
  have h4829 : mixedVector B (Sum.inr 4829) = Sparse.eval nodeValue4829 (mixedVector B) := by
    change mixedMoment B node4829 node4829Labels = _
    exact sound4829 B hB hF
  have h4840 : mixedVector B (Sum.inr 4840) = Sparse.eval nodeValue4840 (mixedVector B) := by
    change mixedMoment B node4840 node4840Labels = _
    exact sound4840 B hB hF
  have h4841 : mixedVector B (Sum.inr 4841) = Sparse.eval nodeValue4841 (mixedVector B) := by
    change mixedMoment B node4841 node4841Labels = _
    exact sound4841 B hB hF
  have h4843 : mixedVector B (Sum.inr 4843) = Sparse.eval nodeValue4843 (mixedVector B) := by
    change mixedMoment B node4843 node4843Labels = _
    exact sound4843 B hB hF
  have h4844 : mixedVector B (Sum.inr 4844) = Sparse.eval nodeValue4844 (mixedVector B) := by
    change mixedMoment B node4844 node4844Labels = _
    exact sound4844 B hB hF
  have h4853 : mixedVector B (Sum.inr 4853) = Sparse.eval nodeValue4853 (mixedVector B) := by
    change mixedMoment B node4853 node4853Labels = _
    exact sound4853 B hB hF
  have h4868 : mixedVector B (Sum.inr 4868) = Sparse.eval nodeValue4868 (mixedVector B) := by
    change mixedMoment B node4868 node4868Labels = _
    exact sound4868 B hB hF
  have h4872 : mixedVector B (Sum.inr 4872) = Sparse.eval nodeValue4872 (mixedVector B) := by
    change mixedMoment B node4872 node4872Labels = _
    exact sound4872 B hB hF
  have h4881 : mixedVector B (Sum.inr 4881) = Sparse.eval nodeValue4881 (mixedVector B) := by
    change mixedMoment B node4881 node4881Labels = _
    exact sound4881 B hB hF
  have h5109 : mixedVector B (Sum.inr 5109) = Sparse.eval nodeValue5109 (mixedVector B) := by
    change mixedMoment B node5109 node5109Labels = _
    exact sound5109 B hB hF
  have h5139 : mixedVector B (Sum.inr 5139) = Sparse.eval nodeValue5139 (mixedVector B) := by
    change mixedMoment B node5139 node5139Labels = _
    exact sound5139 B hB hF
  have h5174 : mixedVector B (Sum.inr 5174) = Sparse.eval nodeValue5174 (mixedVector B) := by
    change mixedMoment B node5174 node5174Labels = _
    exact sound5174 B hB hF
  simpa only [sourceForm1956, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4486, h4490, h4492, h4504, h4807, h4808, h4824, h4827, h4829, h4840, h4841, h4843, h4844, h4853, h4868, h4872, h4881, h5109, h5139, h5174, reducedSource1661] using sourceEq1956 B hB

theorem rowSound1661 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1661 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1661, numericCheck1661, reducedZero1661 B hB hF, mul_zero]

theorem reducedZero1662 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1662 (mixedVector B) = 0 := by
  have h1639 : mixedVector B (Sum.inr 1639) = Sparse.eval nodeValue1639 (mixedVector B) := by
    change mixedMoment B node1639 node1639Labels = _
    exact sound1639 B hB hF
  have h1650 : mixedVector B (Sum.inr 1650) = Sparse.eval nodeValue1650 (mixedVector B) := by
    change mixedMoment B node1650 node1650Labels = _
    exact sound1650 B hB hF
  have h1651 : mixedVector B (Sum.inr 1651) = Sparse.eval nodeValue1651 (mixedVector B) := by
    change mixedMoment B node1651 node1651Labels = _
    exact sound1651 B hB hF
  have h1659 : mixedVector B (Sum.inr 1659) = Sparse.eval nodeValue1659 (mixedVector B) := by
    change mixedMoment B node1659 node1659Labels = _
    exact sound1659 B hB hF
  have h2025 : mixedVector B (Sum.inr 2025) = Sparse.eval nodeValue2025 (mixedVector B) := by
    change mixedMoment B node2025 node2025Labels = _
    exact sound2025 B hB hF
  have h2060 : mixedVector B (Sum.inr 2060) = Sparse.eval nodeValue2060 (mixedVector B) := by
    change mixedMoment B node2060 node2060Labels = _
    exact sound2060 B hB hF
  have h2062 : mixedVector B (Sum.inr 2062) = Sparse.eval nodeValue2062 (mixedVector B) := by
    change mixedMoment B node2062 node2062Labels = _
    exact sound2062 B hB hF
  have h2071 : mixedVector B (Sum.inr 2071) = Sparse.eval nodeValue2071 (mixedVector B) := by
    change mixedMoment B node2071 node2071Labels = _
    exact sound2071 B hB hF
  have h2079 : mixedVector B (Sum.inr 2079) = Sparse.eval nodeValue2079 (mixedVector B) := by
    change mixedMoment B node2079 node2079Labels = _
    exact sound2079 B hB hF
  have h2080 : mixedVector B (Sum.inr 2080) = Sparse.eval nodeValue2080 (mixedVector B) := by
    change mixedMoment B node2080 node2080Labels = _
    exact sound2080 B hB hF
  have h2090 : mixedVector B (Sum.inr 2090) = Sparse.eval nodeValue2090 (mixedVector B) := by
    change mixedMoment B node2090 node2090Labels = _
    exact sound2090 B hB hF
  have h2092 : mixedVector B (Sum.inr 2092) = Sparse.eval nodeValue2092 (mixedVector B) := by
    change mixedMoment B node2092 node2092Labels = _
    exact sound2092 B hB hF
  have h2109 : mixedVector B (Sum.inr 2109) = Sparse.eval nodeValue2109 (mixedVector B) := by
    change mixedMoment B node2109 node2109Labels = _
    exact sound2109 B hB hF
  have h2113 : mixedVector B (Sum.inr 2113) = Sparse.eval nodeValue2113 (mixedVector B) := by
    change mixedMoment B node2113 node2113Labels = _
    exact sound2113 B hB hF
  have h2121 : mixedVector B (Sum.inr 2121) = Sparse.eval nodeValue2121 (mixedVector B) := by
    change mixedMoment B node2121 node2121Labels = _
    exact sound2121 B hB hF
  have h2134 : mixedVector B (Sum.inr 2134) = Sparse.eval nodeValue2134 (mixedVector B) := by
    change mixedMoment B node2134 node2134Labels = _
    exact sound2134 B hB hF
  have h2136 : mixedVector B (Sum.inr 2136) = Sparse.eval nodeValue2136 (mixedVector B) := by
    change mixedMoment B node2136 node2136Labels = _
    exact sound2136 B hB hF
  have h2601 : mixedVector B (Sum.inr 2601) = Sparse.eval nodeValue2601 (mixedVector B) := by
    change mixedMoment B node2601 node2601Labels = _
    exact sound2601 B hB hF
  have h2618 : mixedVector B (Sum.inr 2618) = Sparse.eval nodeValue2618 (mixedVector B) := by
    change mixedMoment B node2618 node2618Labels = _
    exact sound2618 B hB hF
  have h2640 : mixedVector B (Sum.inr 2640) = Sparse.eval nodeValue2640 (mixedVector B) := by
    change mixedMoment B node2640 node2640Labels = _
    exact sound2640 B hB hF
  have h2642 : mixedVector B (Sum.inr 2642) = Sparse.eval nodeValue2642 (mixedVector B) := by
    change mixedMoment B node2642 node2642Labels = _
    exact sound2642 B hB hF
  simpa only [sourceForm1957, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1639, h1650, h1651, h1659, h2025, h2060, h2062, h2071, h2079, h2080, h2090, h2092, h2109, h2113, h2121, h2134, h2136, h2601, h2618, h2640, h2642, reducedSource1662] using sourceEq1957 B hB

theorem rowSound1662 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1662 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1662, numericCheck1662, reducedZero1662 B hB hF, mul_zero]

theorem reducedZero1663 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1663 (mixedVector B) = 0 := by
  have h1159 : mixedVector B (Sum.inr 1159) = Sparse.eval nodeValue1159 (mixedVector B) := by
    change mixedMoment B node1159 node1159Labels = _
    exact sound1159 B hB hF
  have h2355 : mixedVector B (Sum.inr 2355) = Sparse.eval nodeValue2355 (mixedVector B) := by
    change mixedMoment B node2355 node2355Labels = _
    exact sound2355 B hB hF
  have h2436 : mixedVector B (Sum.inr 2436) = Sparse.eval nodeValue2436 (mixedVector B) := by
    change mixedMoment B node2436 node2436Labels = _
    exact sound2436 B hB hF
  have h2482 : mixedVector B (Sum.inr 2482) = Sparse.eval nodeValue2482 (mixedVector B) := by
    change mixedMoment B node2482 node2482Labels = _
    exact sound2482 B hB hF
  have h2569 : mixedVector B (Sum.inr 2569) = Sparse.eval nodeValue2569 (mixedVector B) := by
    change mixedMoment B node2569 node2569Labels = _
    exact sound2569 B hB hF
  have h2590 : mixedVector B (Sum.inr 2590) = Sparse.eval nodeValue2590 (mixedVector B) := by
    change mixedMoment B node2590 node2590Labels = _
    exact sound2590 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1958, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1159, h2355, h2436, h2482, h2569, h2590, h4092, reducedSource1663] using sourceEq1958 B hB

theorem rowSound1663 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1663 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1663, numericCheck1663, reducedZero1663 B hB hF, mul_zero]

theorem sourceRowsAt1648 : MixedData.sourceRows (1648 : Fin 2425) =
    MixedData.row1648 := by decide +kernel

theorem sourceRowsAt1649 : MixedData.sourceRows (1649 : Fin 2425) =
    MixedData.row1649 := by decide +kernel

theorem sourceRowsAt1650 : MixedData.sourceRows (1650 : Fin 2425) =
    MixedData.row1650 := by decide +kernel

theorem sourceRowsAt1651 : MixedData.sourceRows (1651 : Fin 2425) =
    MixedData.row1651 := by decide +kernel

theorem sourceRowsAt1652 : MixedData.sourceRows (1652 : Fin 2425) =
    MixedData.row1652 := by decide +kernel

theorem sourceRowsAt1653 : MixedData.sourceRows (1653 : Fin 2425) =
    MixedData.row1653 := by decide +kernel

theorem sourceRowsAt1654 : MixedData.sourceRows (1654 : Fin 2425) =
    MixedData.row1654 := by decide +kernel

theorem sourceRowsAt1655 : MixedData.sourceRows (1655 : Fin 2425) =
    MixedData.row1655 := by decide +kernel

theorem sourceRowsAt1656 : MixedData.sourceRows (1656 : Fin 2425) =
    MixedData.row1656 := by decide +kernel

theorem sourceRowsAt1657 : MixedData.sourceRows (1657 : Fin 2425) =
    MixedData.row1657 := by decide +kernel

theorem sourceRowsAt1658 : MixedData.sourceRows (1658 : Fin 2425) =
    MixedData.row1658 := by decide +kernel

theorem sourceRowsAt1659 : MixedData.sourceRows (1659 : Fin 2425) =
    MixedData.row1659 := by decide +kernel

theorem sourceRowsAt1660 : MixedData.sourceRows (1660 : Fin 2425) =
    MixedData.row1660 := by decide +kernel

theorem sourceRowsAt1661 : MixedData.sourceRows (1661 : Fin 2425) =
    MixedData.row1661 := by decide +kernel

theorem sourceRowsAt1662 : MixedData.sourceRows (1662 : Fin 2425) =
    MixedData.row1662 := by decide +kernel

theorem sourceRowsAt1663 : MixedData.sourceRows (1663 : Fin 2425) =
    MixedData.row1663 := by decide +kernel

theorem chunkSound103 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 103) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1648 ∨ k.val = 1649 ∨ k.val = 1650 ∨ k.val = 1651 ∨ k.val = 1652 ∨ k.val = 1653 ∨ k.val = 1654 ∨ k.val = 1655 ∨ k.val = 1656 ∨ k.val = 1657 ∨ k.val = 1658 ∨ k.val = 1659 ∨ k.val = 1660 ∨ k.val = 1661 ∨ k.val = 1662 ∨ k.val = 1663 := by omega
  rcases heq with h1648 | h1649 | h1650 | h1651 | h1652 | h1653 | h1654 | h1655 | h1656 | h1657 | h1658 | h1659 | h1660 | h1661 | h1662 | h1663
  · have he : k = (1648 : Fin 2425) := Fin.ext h1648
    subst k
    rw [sourceRowsAt1648]
    exact rowSound1648 B hB hF
  · have he : k = (1649 : Fin 2425) := Fin.ext h1649
    subst k
    rw [sourceRowsAt1649]
    exact rowSound1649 B hB hF
  · have he : k = (1650 : Fin 2425) := Fin.ext h1650
    subst k
    rw [sourceRowsAt1650]
    exact rowSound1650 B hB hF
  · have he : k = (1651 : Fin 2425) := Fin.ext h1651
    subst k
    rw [sourceRowsAt1651]
    exact rowSound1651 B hB hF
  · have he : k = (1652 : Fin 2425) := Fin.ext h1652
    subst k
    rw [sourceRowsAt1652]
    exact rowSound1652 B hB hF
  · have he : k = (1653 : Fin 2425) := Fin.ext h1653
    subst k
    rw [sourceRowsAt1653]
    exact rowSound1653 B hB hF
  · have he : k = (1654 : Fin 2425) := Fin.ext h1654
    subst k
    rw [sourceRowsAt1654]
    exact rowSound1654 B hB hF
  · have he : k = (1655 : Fin 2425) := Fin.ext h1655
    subst k
    rw [sourceRowsAt1655]
    exact rowSound1655 B hB hF
  · have he : k = (1656 : Fin 2425) := Fin.ext h1656
    subst k
    rw [sourceRowsAt1656]
    exact rowSound1656 B hB hF
  · have he : k = (1657 : Fin 2425) := Fin.ext h1657
    subst k
    rw [sourceRowsAt1657]
    exact rowSound1657 B hB hF
  · have he : k = (1658 : Fin 2425) := Fin.ext h1658
    subst k
    rw [sourceRowsAt1658]
    exact rowSound1658 B hB hF
  · have he : k = (1659 : Fin 2425) := Fin.ext h1659
    subst k
    rw [sourceRowsAt1659]
    exact rowSound1659 B hB hF
  · have he : k = (1660 : Fin 2425) := Fin.ext h1660
    subst k
    rw [sourceRowsAt1660]
    exact rowSound1660 B hB hF
  · have he : k = (1661 : Fin 2425) := Fin.ext h1661
    subst k
    rw [sourceRowsAt1661]
    exact rowSound1661 B hB hF
  · have he : k = (1662 : Fin 2425) := Fin.ext h1662
    subst k
    rw [sourceRowsAt1662]
    exact rowSound1662 B hB hF
  · have he : k = (1663 : Fin 2425) := Fin.ext h1663
    subst k
    rw [sourceRowsAt1663]
    exact rowSound1663 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
