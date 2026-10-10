import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic131
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources82

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2096 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2096 (mixedVector B) = 0 := by
  have h4090 : mixedVector B (Sum.inr 4090) = Sparse.eval nodeValue4090 (mixedVector B) := by
    change mixedMoment B node4090 node4090Labels = _
    exact sound4090 B hB hF
  have h4927 : mixedVector B (Sum.inr 4927) = Sparse.eval nodeValue4927 (mixedVector B) := by
    change mixedMoment B node4927 node4927Labels = _
    exact sound4927 B hB hF
  have h4928 : mixedVector B (Sum.inr 4928) = Sparse.eval nodeValue4928 (mixedVector B) := by
    change mixedMoment B node4928 node4928Labels = _
    exact sound4928 B hB hF
  have h4936 : mixedVector B (Sum.inr 4936) = Sparse.eval nodeValue4936 (mixedVector B) := by
    change mixedMoment B node4936 node4936Labels = _
    exact sound4936 B hB hF
  have h4960 : mixedVector B (Sum.inr 4960) = Sparse.eval nodeValue4960 (mixedVector B) := by
    change mixedMoment B node4960 node4960Labels = _
    exact sound4960 B hB hF
  have h4961 : mixedVector B (Sum.inr 4961) = Sparse.eval nodeValue4961 (mixedVector B) := by
    change mixedMoment B node4961 node4961Labels = _
    exact sound4961 B hB hF
  have h4969 : mixedVector B (Sum.inr 4969) = Sparse.eval nodeValue4969 (mixedVector B) := by
    change mixedMoment B node4969 node4969Labels = _
    exact sound4969 B hB hF
  have h5029 : mixedVector B (Sum.inr 5029) = Sparse.eval nodeValue5029 (mixedVector B) := by
    change mixedMoment B node5029 node5029Labels = _
    exact sound5029 B hB hF
  have h5050 : mixedVector B (Sum.inr 5050) = Sparse.eval nodeValue5050 (mixedVector B) := by
    change mixedMoment B node5050 node5050Labels = _
    exact sound5050 B hB hF
  have h5058 : mixedVector B (Sum.inr 5058) = Sparse.eval nodeValue5058 (mixedVector B) := by
    change mixedMoment B node5058 node5058Labels = _
    exact sound5058 B hB hF
  have h5192 : mixedVector B (Sum.inr 5192) = Sparse.eval nodeValue5192 (mixedVector B) := by
    change mixedMoment B node5192 node5192Labels = _
    exact sound5192 B hB hF
  have h5332 : mixedVector B (Sum.inr 5332) = Sparse.eval nodeValue5332 (mixedVector B) := by
    change mixedMoment B node5332 node5332Labels = _
    exact sound5332 B hB hF
  have h5341 : mixedVector B (Sum.inr 5341) = Sparse.eval nodeValue5341 (mixedVector B) := by
    change mixedMoment B node5341 node5341Labels = _
    exact sound5341 B hB hF
  have h5346 : mixedVector B (Sum.inr 5346) = Sparse.eval nodeValue5346 (mixedVector B) := by
    change mixedMoment B node5346 node5346Labels = _
    exact sound5346 B hB hF
  have h5349 : mixedVector B (Sum.inr 5349) = Sparse.eval nodeValue5349 (mixedVector B) := by
    change mixedMoment B node5349 node5349Labels = _
    exact sound5349 B hB hF
  have h5363 : mixedVector B (Sum.inr 5363) = Sparse.eval nodeValue5363 (mixedVector B) := by
    change mixedMoment B node5363 node5363Labels = _
    exact sound5363 B hB hF
  have h5392 : mixedVector B (Sum.inr 5392) = Sparse.eval nodeValue5392 (mixedVector B) := by
    change mixedMoment B node5392 node5392Labels = _
    exact sound5392 B hB hF
  have h5394 : mixedVector B (Sum.inr 5394) = Sparse.eval nodeValue5394 (mixedVector B) := by
    change mixedMoment B node5394 node5394Labels = _
    exact sound5394 B hB hF
  have h5395 : mixedVector B (Sum.inr 5395) = Sparse.eval nodeValue5395 (mixedVector B) := by
    change mixedMoment B node5395 node5395Labels = _
    exact sound5395 B hB hF
  have h5396 : mixedVector B (Sum.inr 5396) = Sparse.eval nodeValue5396 (mixedVector B) := by
    change mixedMoment B node5396 node5396Labels = _
    exact sound5396 B hB hF
  have h5469 : mixedVector B (Sum.inr 5469) = Sparse.eval nodeValue5469 (mixedVector B) := by
    change mixedMoment B node5469 node5469Labels = _
    exact sound5469 B hB hF
  simpa only [sourceForm2632, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4090, h4927, h4928, h4936, h4960, h4961, h4969, h5029, h5050, h5058, h5192, h5332, h5341, h5346, h5349, h5363, h5392, h5394, h5395, h5396, h5469, reducedSource2096] using sourceEq2632 B hB

theorem rowSound2096 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2096 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2096, numericCheck2096, reducedZero2096 B hB hF, mul_zero]

theorem reducedZero2097 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2097 (mixedVector B) = 0 := by
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  have h4986 : mixedVector B (Sum.inr 4986) = Sparse.eval nodeValue4986 (mixedVector B) := by
    change mixedMoment B node4986 node4986Labels = _
    exact sound4986 B hB hF
  have h4987 : mixedVector B (Sum.inr 4987) = Sparse.eval nodeValue4987 (mixedVector B) := by
    change mixedMoment B node4987 node4987Labels = _
    exact sound4987 B hB hF
  have h5017 : mixedVector B (Sum.inr 5017) = Sparse.eval nodeValue5017 (mixedVector B) := by
    change mixedMoment B node5017 node5017Labels = _
    exact sound5017 B hB hF
  have h5025 : mixedVector B (Sum.inr 5025) = Sparse.eval nodeValue5025 (mixedVector B) := by
    change mixedMoment B node5025 node5025Labels = _
    exact sound5025 B hB hF
  have h5030 : mixedVector B (Sum.inr 5030) = Sparse.eval nodeValue5030 (mixedVector B) := by
    change mixedMoment B node5030 node5030Labels = _
    exact sound5030 B hB hF
  have h5056 : mixedVector B (Sum.inr 5056) = Sparse.eval nodeValue5056 (mixedVector B) := by
    change mixedMoment B node5056 node5056Labels = _
    exact sound5056 B hB hF
  have h5123 : mixedVector B (Sum.inr 5123) = Sparse.eval nodeValue5123 (mixedVector B) := by
    change mixedMoment B node5123 node5123Labels = _
    exact sound5123 B hB hF
  have h5314 : mixedVector B (Sum.inr 5314) = Sparse.eval nodeValue5314 (mixedVector B) := by
    change mixedMoment B node5314 node5314Labels = _
    exact sound5314 B hB hF
  have h5333 : mixedVector B (Sum.inr 5333) = Sparse.eval nodeValue5333 (mixedVector B) := by
    change mixedMoment B node5333 node5333Labels = _
    exact sound5333 B hB hF
  have h5344 : mixedVector B (Sum.inr 5344) = Sparse.eval nodeValue5344 (mixedVector B) := by
    change mixedMoment B node5344 node5344Labels = _
    exact sound5344 B hB hF
  have h5345 : mixedVector B (Sum.inr 5345) = Sparse.eval nodeValue5345 (mixedVector B) := by
    change mixedMoment B node5345 node5345Labels = _
    exact sound5345 B hB hF
  have h5346 : mixedVector B (Sum.inr 5346) = Sparse.eval nodeValue5346 (mixedVector B) := by
    change mixedMoment B node5346 node5346Labels = _
    exact sound5346 B hB hF
  have h5367 : mixedVector B (Sum.inr 5367) = Sparse.eval nodeValue5367 (mixedVector B) := by
    change mixedMoment B node5367 node5367Labels = _
    exact sound5367 B hB hF
  have h5369 : mixedVector B (Sum.inr 5369) = Sparse.eval nodeValue5369 (mixedVector B) := by
    change mixedMoment B node5369 node5369Labels = _
    exact sound5369 B hB hF
  have h5374 : mixedVector B (Sum.inr 5374) = Sparse.eval nodeValue5374 (mixedVector B) := by
    change mixedMoment B node5374 node5374Labels = _
    exact sound5374 B hB hF
  have h5378 : mixedVector B (Sum.inr 5378) = Sparse.eval nodeValue5378 (mixedVector B) := by
    change mixedMoment B node5378 node5378Labels = _
    exact sound5378 B hB hF
  have h5380 : mixedVector B (Sum.inr 5380) = Sparse.eval nodeValue5380 (mixedVector B) := by
    change mixedMoment B node5380 node5380Labels = _
    exact sound5380 B hB hF
  have h5391 : mixedVector B (Sum.inr 5391) = Sparse.eval nodeValue5391 (mixedVector B) := by
    change mixedMoment B node5391 node5391Labels = _
    exact sound5391 B hB hF
  have h5393 : mixedVector B (Sum.inr 5393) = Sparse.eval nodeValue5393 (mixedVector B) := by
    change mixedMoment B node5393 node5393Labels = _
    exact sound5393 B hB hF
  have h5460 : mixedVector B (Sum.inr 5460) = Sparse.eval nodeValue5460 (mixedVector B) := by
    change mixedMoment B node5460 node5460Labels = _
    exact sound5460 B hB hF
  simpa only [sourceForm2633, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4088, h4986, h4987, h5017, h5025, h5030, h5056, h5123, h5314, h5333, h5344, h5345, h5346, h5367, h5369, h5374, h5378, h5380, h5391, h5393, h5460, reducedSource2097] using sourceEq2633 B hB

theorem rowSound2097 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2097 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2097, numericCheck2097, reducedZero2097 B hB hF, mul_zero]

theorem reducedZero2098 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2098 (mixedVector B) = 0 := by
  have h4073 : mixedVector B (Sum.inr 4073) = Sparse.eval nodeValue4073 (mixedVector B) := by
    change mixedMoment B node4073 node4073Labels = _
    exact sound4073 B hB hF
  have h4074 : mixedVector B (Sum.inr 4074) = Sparse.eval nodeValue4074 (mixedVector B) := by
    change mixedMoment B node4074 node4074Labels = _
    exact sound4074 B hB hF
  have h4075 : mixedVector B (Sum.inr 4075) = Sparse.eval nodeValue4075 (mixedVector B) := by
    change mixedMoment B node4075 node4075Labels = _
    exact sound4075 B hB hF
  have h4078 : mixedVector B (Sum.inr 4078) = Sparse.eval nodeValue4078 (mixedVector B) := by
    change mixedMoment B node4078 node4078Labels = _
    exact sound4078 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  have h4086 : mixedVector B (Sum.inr 4086) = Sparse.eval nodeValue4086 (mixedVector B) := by
    change mixedMoment B node4086 node4086Labels = _
    exact sound4086 B hB hF
  have h4087 : mixedVector B (Sum.inr 4087) = Sparse.eval nodeValue4087 (mixedVector B) := by
    change mixedMoment B node4087 node4087Labels = _
    exact sound4087 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  have h4089 : mixedVector B (Sum.inr 4089) = Sparse.eval nodeValue4089 (mixedVector B) := by
    change mixedMoment B node4089 node4089Labels = _
    exact sound4089 B hB hF
  have h4090 : mixedVector B (Sum.inr 4090) = Sparse.eval nodeValue4090 (mixedVector B) := by
    change mixedMoment B node4090 node4090Labels = _
    exact sound4090 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2638, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4073, h4074, h4075, h4078, h4080, h4082, h4086, h4087, h4088, h4089, h4090, h4091, h4092, reducedSource2098] using sourceEq2638 B hB

theorem rowSound2098 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2098 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2098, numericCheck2098, reducedZero2098 B hB hF, mul_zero]

theorem reducedZero2099 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2099 (mixedVector B) = 0 := by
  have h4672 : mixedVector B (Sum.inr 4672) = Sparse.eval nodeValue4672 (mixedVector B) := by
    change mixedMoment B node4672 node4672Labels = _
    exact sound4672 B hB hF
  have h4685 : mixedVector B (Sum.inr 4685) = Sparse.eval nodeValue4685 (mixedVector B) := by
    change mixedMoment B node4685 node4685Labels = _
    exact sound4685 B hB hF
  have h4859 : mixedVector B (Sum.inr 4859) = Sparse.eval nodeValue4859 (mixedVector B) := by
    change mixedMoment B node4859 node4859Labels = _
    exact sound4859 B hB hF
  have h4967 : mixedVector B (Sum.inr 4967) = Sparse.eval nodeValue4967 (mixedVector B) := by
    change mixedMoment B node4967 node4967Labels = _
    exact sound4967 B hB hF
  have h4969 : mixedVector B (Sum.inr 4969) = Sparse.eval nodeValue4969 (mixedVector B) := by
    change mixedMoment B node4969 node4969Labels = _
    exact sound4969 B hB hF
  have h5166 : mixedVector B (Sum.inr 5166) = Sparse.eval nodeValue5166 (mixedVector B) := by
    change mixedMoment B node5166 node5166Labels = _
    exact sound5166 B hB hF
  have h5374 : mixedVector B (Sum.inr 5374) = Sparse.eval nodeValue5374 (mixedVector B) := by
    change mixedMoment B node5374 node5374Labels = _
    exact sound5374 B hB hF
  have h5383 : mixedVector B (Sum.inr 5383) = Sparse.eval nodeValue5383 (mixedVector B) := by
    change mixedMoment B node5383 node5383Labels = _
    exact sound5383 B hB hF
  have h5384 : mixedVector B (Sum.inr 5384) = Sparse.eval nodeValue5384 (mixedVector B) := by
    change mixedMoment B node5384 node5384Labels = _
    exact sound5384 B hB hF
  have h5387 : mixedVector B (Sum.inr 5387) = Sparse.eval nodeValue5387 (mixedVector B) := by
    change mixedMoment B node5387 node5387Labels = _
    exact sound5387 B hB hF
  have h5437 : mixedVector B (Sum.inr 5437) = Sparse.eval nodeValue5437 (mixedVector B) := by
    change mixedMoment B node5437 node5437Labels = _
    exact sound5437 B hB hF
  have h5439 : mixedVector B (Sum.inr 5439) = Sparse.eval nodeValue5439 (mixedVector B) := by
    change mixedMoment B node5439 node5439Labels = _
    exact sound5439 B hB hF
  have h5448 : mixedVector B (Sum.inr 5448) = Sparse.eval nodeValue5448 (mixedVector B) := by
    change mixedMoment B node5448 node5448Labels = _
    exact sound5448 B hB hF
  simpa only [sourceForm2639, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4672, h4685, h4859, h4967, h4969, h5166, h5374, h5383, h5384, h5387, h5437, h5439, h5448, reducedSource2099] using sourceEq2639 B hB

theorem rowSound2099 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2099 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2099, numericCheck2099, reducedZero2099 B hB hF, mul_zero]

theorem reducedZero2100 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2100 (mixedVector B) = 0 := by
  have h4675 : mixedVector B (Sum.inr 4675) = Sparse.eval nodeValue4675 (mixedVector B) := by
    change mixedMoment B node4675 node4675Labels = _
    exact sound4675 B hB hF
  have h4677 : mixedVector B (Sum.inr 4677) = Sparse.eval nodeValue4677 (mixedVector B) := by
    change mixedMoment B node4677 node4677Labels = _
    exact sound4677 B hB hF
  have h4863 : mixedVector B (Sum.inr 4863) = Sparse.eval nodeValue4863 (mixedVector B) := by
    change mixedMoment B node4863 node4863Labels = _
    exact sound4863 B hB hF
  have h4964 : mixedVector B (Sum.inr 4964) = Sparse.eval nodeValue4964 (mixedVector B) := by
    change mixedMoment B node4964 node4964Labels = _
    exact sound4964 B hB hF
  have h4975 : mixedVector B (Sum.inr 4975) = Sparse.eval nodeValue4975 (mixedVector B) := by
    change mixedMoment B node4975 node4975Labels = _
    exact sound4975 B hB hF
  have h5162 : mixedVector B (Sum.inr 5162) = Sparse.eval nodeValue5162 (mixedVector B) := by
    change mixedMoment B node5162 node5162Labels = _
    exact sound5162 B hB hF
  have h5243 : mixedVector B (Sum.inr 5243) = Sparse.eval nodeValue5243 (mixedVector B) := by
    change mixedMoment B node5243 node5243Labels = _
    exact sound5243 B hB hF
  have h5379 : mixedVector B (Sum.inr 5379) = Sparse.eval nodeValue5379 (mixedVector B) := by
    change mixedMoment B node5379 node5379Labels = _
    exact sound5379 B hB hF
  have h5380 : mixedVector B (Sum.inr 5380) = Sparse.eval nodeValue5380 (mixedVector B) := by
    change mixedMoment B node5380 node5380Labels = _
    exact sound5380 B hB hF
  have h5427 : mixedVector B (Sum.inr 5427) = Sparse.eval nodeValue5427 (mixedVector B) := by
    change mixedMoment B node5427 node5427Labels = _
    exact sound5427 B hB hF
  have h5429 : mixedVector B (Sum.inr 5429) = Sparse.eval nodeValue5429 (mixedVector B) := by
    change mixedMoment B node5429 node5429Labels = _
    exact sound5429 B hB hF
  have h5431 : mixedVector B (Sum.inr 5431) = Sparse.eval nodeValue5431 (mixedVector B) := by
    change mixedMoment B node5431 node5431Labels = _
    exact sound5431 B hB hF
  have h5447 : mixedVector B (Sum.inr 5447) = Sparse.eval nodeValue5447 (mixedVector B) := by
    change mixedMoment B node5447 node5447Labels = _
    exact sound5447 B hB hF
  simpa only [sourceForm2640, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4675, h4677, h4863, h4964, h4975, h5162, h5243, h5379, h5380, h5427, h5429, h5431, h5447, reducedSource2100] using sourceEq2640 B hB

theorem rowSound2100 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2100 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2100, numericCheck2100, reducedZero2100 B hB hF, mul_zero]

theorem reducedZero2101 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2101 (mixedVector B) = 0 := by
  have h2139 : mixedVector B (Sum.inr 2139) = Sparse.eval nodeValue2139 (mixedVector B) := by
    change mixedMoment B node2139 node2139Labels = _
    exact sound2139 B hB hF
  have h2142 : mixedVector B (Sum.inr 2142) = Sparse.eval nodeValue2142 (mixedVector B) := by
    change mixedMoment B node2142 node2142Labels = _
    exact sound2142 B hB hF
  have h2232 : mixedVector B (Sum.inr 2232) = Sparse.eval nodeValue2232 (mixedVector B) := by
    change mixedMoment B node2232 node2232Labels = _
    exact sound2232 B hB hF
  have h2690 : mixedVector B (Sum.inr 2690) = Sparse.eval nodeValue2690 (mixedVector B) := by
    change mixedMoment B node2690 node2690Labels = _
    exact sound2690 B hB hF
  have h2697 : mixedVector B (Sum.inr 2697) = Sparse.eval nodeValue2697 (mixedVector B) := by
    change mixedMoment B node2697 node2697Labels = _
    exact sound2697 B hB hF
  have h3554 : mixedVector B (Sum.inr 3554) = Sparse.eval nodeValue3554 (mixedVector B) := by
    change mixedMoment B node3554 node3554Labels = _
    exact sound3554 B hB hF
  have h3563 : mixedVector B (Sum.inr 3563) = Sparse.eval nodeValue3563 (mixedVector B) := by
    change mixedMoment B node3563 node3563Labels = _
    exact sound3563 B hB hF
  have h3832 : mixedVector B (Sum.inr 3832) = Sparse.eval nodeValue3832 (mixedVector B) := by
    change mixedMoment B node3832 node3832Labels = _
    exact sound3832 B hB hF
  have h3836 : mixedVector B (Sum.inr 3836) = Sparse.eval nodeValue3836 (mixedVector B) := by
    change mixedMoment B node3836 node3836Labels = _
    exact sound3836 B hB hF
  have h3844 : mixedVector B (Sum.inr 3844) = Sparse.eval nodeValue3844 (mixedVector B) := by
    change mixedMoment B node3844 node3844Labels = _
    exact sound3844 B hB hF
  have h3846 : mixedVector B (Sum.inr 3846) = Sparse.eval nodeValue3846 (mixedVector B) := by
    change mixedMoment B node3846 node3846Labels = _
    exact sound3846 B hB hF
  have h3875 : mixedVector B (Sum.inr 3875) = Sparse.eval nodeValue3875 (mixedVector B) := by
    change mixedMoment B node3875 node3875Labels = _
    exact sound3875 B hB hF
  have h3909 : mixedVector B (Sum.inr 3909) = Sparse.eval nodeValue3909 (mixedVector B) := by
    change mixedMoment B node3909 node3909Labels = _
    exact sound3909 B hB hF
  simpa only [sourceForm2641, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2139, h2142, h2232, h2690, h2697, h3554, h3563, h3832, h3836, h3844, h3846, h3875, h3909, reducedSource2101] using sourceEq2641 B hB

theorem rowSound2101 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2101 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2101, numericCheck2101, reducedZero2101 B hB hF, mul_zero]

theorem reducedZero2102 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2102 (mixedVector B) = 0 := by
  have h4676 : mixedVector B (Sum.inr 4676) = Sparse.eval nodeValue4676 (mixedVector B) := by
    change mixedMoment B node4676 node4676Labels = _
    exact sound4676 B hB hF
  have h4679 : mixedVector B (Sum.inr 4679) = Sparse.eval nodeValue4679 (mixedVector B) := by
    change mixedMoment B node4679 node4679Labels = _
    exact sound4679 B hB hF
  have h4864 : mixedVector B (Sum.inr 4864) = Sparse.eval nodeValue4864 (mixedVector B) := by
    change mixedMoment B node4864 node4864Labels = _
    exact sound4864 B hB hF
  have h4968 : mixedVector B (Sum.inr 4968) = Sparse.eval nodeValue4968 (mixedVector B) := by
    change mixedMoment B node4968 node4968Labels = _
    exact sound4968 B hB hF
  have h4971 : mixedVector B (Sum.inr 4971) = Sparse.eval nodeValue4971 (mixedVector B) := by
    change mixedMoment B node4971 node4971Labels = _
    exact sound4971 B hB hF
  have h5167 : mixedVector B (Sum.inr 5167) = Sparse.eval nodeValue5167 (mixedVector B) := by
    change mixedMoment B node5167 node5167Labels = _
    exact sound5167 B hB hF
  have h5378 : mixedVector B (Sum.inr 5378) = Sparse.eval nodeValue5378 (mixedVector B) := by
    change mixedMoment B node5378 node5378Labels = _
    exact sound5378 B hB hF
  have h5380 : mixedVector B (Sum.inr 5380) = Sparse.eval nodeValue5380 (mixedVector B) := by
    change mixedMoment B node5380 node5380Labels = _
    exact sound5380 B hB hF
  have h5387 : mixedVector B (Sum.inr 5387) = Sparse.eval nodeValue5387 (mixedVector B) := by
    change mixedMoment B node5387 node5387Labels = _
    exact sound5387 B hB hF
  have h5388 : mixedVector B (Sum.inr 5388) = Sparse.eval nodeValue5388 (mixedVector B) := by
    change mixedMoment B node5388 node5388Labels = _
    exact sound5388 B hB hF
  have h5431 : mixedVector B (Sum.inr 5431) = Sparse.eval nodeValue5431 (mixedVector B) := by
    change mixedMoment B node5431 node5431Labels = _
    exact sound5431 B hB hF
  have h5433 : mixedVector B (Sum.inr 5433) = Sparse.eval nodeValue5433 (mixedVector B) := by
    change mixedMoment B node5433 node5433Labels = _
    exact sound5433 B hB hF
  have h5440 : mixedVector B (Sum.inr 5440) = Sparse.eval nodeValue5440 (mixedVector B) := by
    change mixedMoment B node5440 node5440Labels = _
    exact sound5440 B hB hF
  have h5450 : mixedVector B (Sum.inr 5450) = Sparse.eval nodeValue5450 (mixedVector B) := by
    change mixedMoment B node5450 node5450Labels = _
    exact sound5450 B hB hF
  simpa only [sourceForm2642, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4676, h4679, h4864, h4968, h4971, h5167, h5378, h5380, h5387, h5388, h5431, h5433, h5440, h5450, reducedSource2102] using sourceEq2642 B hB

theorem rowSound2102 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2102 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2102, numericCheck2102, reducedZero2102 B hB hF, mul_zero]

theorem reducedZero2103 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2103 (mixedVector B) = 0 := by
  have h4679 : mixedVector B (Sum.inr 4679) = Sparse.eval nodeValue4679 (mixedVector B) := by
    change mixedMoment B node4679 node4679Labels = _
    exact sound4679 B hB hF
  have h4685 : mixedVector B (Sum.inr 4685) = Sparse.eval nodeValue4685 (mixedVector B) := by
    change mixedMoment B node4685 node4685Labels = _
    exact sound4685 B hB hF
  have h4695 : mixedVector B (Sum.inr 4695) = Sparse.eval nodeValue4695 (mixedVector B) := by
    change mixedMoment B node4695 node4695Labels = _
    exact sound4695 B hB hF
  have h4696 : mixedVector B (Sum.inr 4696) = Sparse.eval nodeValue4696 (mixedVector B) := by
    change mixedMoment B node4696 node4696Labels = _
    exact sound4696 B hB hF
  have h4833 : mixedVector B (Sum.inr 4833) = Sparse.eval nodeValue4833 (mixedVector B) := by
    change mixedMoment B node4833 node4833Labels = _
    exact sound4833 B hB hF
  have h4878 : mixedVector B (Sum.inr 4878) = Sparse.eval nodeValue4878 (mixedVector B) := by
    change mixedMoment B node4878 node4878Labels = _
    exact sound4878 B hB hF
  have h5226 : mixedVector B (Sum.inr 5226) = Sparse.eval nodeValue5226 (mixedVector B) := by
    change mixedMoment B node5226 node5226Labels = _
    exact sound5226 B hB hF
  have h5231 : mixedVector B (Sum.inr 5231) = Sparse.eval nodeValue5231 (mixedVector B) := by
    change mixedMoment B node5231 node5231Labels = _
    exact sound5231 B hB hF
  have h5237 : mixedVector B (Sum.inr 5237) = Sparse.eval nodeValue5237 (mixedVector B) := by
    change mixedMoment B node5237 node5237Labels = _
    exact sound5237 B hB hF
  have h5257 : mixedVector B (Sum.inr 5257) = Sparse.eval nodeValue5257 (mixedVector B) := by
    change mixedMoment B node5257 node5257Labels = _
    exact sound5257 B hB hF
  have h5265 : mixedVector B (Sum.inr 5265) = Sparse.eval nodeValue5265 (mixedVector B) := by
    change mixedMoment B node5265 node5265Labels = _
    exact sound5265 B hB hF
  have h5273 : mixedVector B (Sum.inr 5273) = Sparse.eval nodeValue5273 (mixedVector B) := by
    change mixedMoment B node5273 node5273Labels = _
    exact sound5273 B hB hF
  have h5301 : mixedVector B (Sum.inr 5301) = Sparse.eval nodeValue5301 (mixedVector B) := by
    change mixedMoment B node5301 node5301Labels = _
    exact sound5301 B hB hF
  simpa only [sourceForm2644, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4679, h4685, h4695, h4696, h4833, h4878, h5226, h5231, h5237, h5257, h5265, h5273, h5301, reducedSource2103] using sourceEq2644 B hB

theorem rowSound2103 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2103 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2103, numericCheck2103, reducedZero2103 B hB hF, mul_zero]

theorem reducedZero2104 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2104 (mixedVector B) = 0 := by
  have h2150 : mixedVector B (Sum.inr 2150) = Sparse.eval nodeValue2150 (mixedVector B) := by
    change mixedMoment B node2150 node2150Labels = _
    exact sound2150 B hB hF
  have h2156 : mixedVector B (Sum.inr 2156) = Sparse.eval nodeValue2156 (mixedVector B) := by
    change mixedMoment B node2156 node2156Labels = _
    exact sound2156 B hB hF
  have h2204 : mixedVector B (Sum.inr 2204) = Sparse.eval nodeValue2204 (mixedVector B) := by
    change mixedMoment B node2204 node2204Labels = _
    exact sound2204 B hB hF
  have h2231 : mixedVector B (Sum.inr 2231) = Sparse.eval nodeValue2231 (mixedVector B) := by
    change mixedMoment B node2231 node2231Labels = _
    exact sound2231 B hB hF
  have h2234 : mixedVector B (Sum.inr 2234) = Sparse.eval nodeValue2234 (mixedVector B) := by
    change mixedMoment B node2234 node2234Labels = _
    exact sound2234 B hB hF
  have h2238 : mixedVector B (Sum.inr 2238) = Sparse.eval nodeValue2238 (mixedVector B) := by
    change mixedMoment B node2238 node2238Labels = _
    exact sound2238 B hB hF
  have h2669 : mixedVector B (Sum.inr 2669) = Sparse.eval nodeValue2669 (mixedVector B) := by
    change mixedMoment B node2669 node2669Labels = _
    exact sound2669 B hB hF
  have h2676 : mixedVector B (Sum.inr 2676) = Sparse.eval nodeValue2676 (mixedVector B) := by
    change mixedMoment B node2676 node2676Labels = _
    exact sound2676 B hB hF
  have h2684 : mixedVector B (Sum.inr 2684) = Sparse.eval nodeValue2684 (mixedVector B) := by
    change mixedMoment B node2684 node2684Labels = _
    exact sound2684 B hB hF
  have h2721 : mixedVector B (Sum.inr 2721) = Sparse.eval nodeValue2721 (mixedVector B) := by
    change mixedMoment B node2721 node2721Labels = _
    exact sound2721 B hB hF
  have h2741 : mixedVector B (Sum.inr 2741) = Sparse.eval nodeValue2741 (mixedVector B) := by
    change mixedMoment B node2741 node2741Labels = _
    exact sound2741 B hB hF
  have h3037 : mixedVector B (Sum.inr 3037) = Sparse.eval nodeValue3037 (mixedVector B) := by
    change mixedMoment B node3037 node3037Labels = _
    exact sound3037 B hB hF
  have h3053 : mixedVector B (Sum.inr 3053) = Sparse.eval nodeValue3053 (mixedVector B) := by
    change mixedMoment B node3053 node3053Labels = _
    exact sound3053 B hB hF
  simpa only [sourceForm2645, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2150, h2156, h2204, h2231, h2234, h2238, h2669, h2676, h2684, h2721, h2741, h3037, h3053, reducedSource2104] using sourceEq2645 B hB

theorem rowSound2104 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2104 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2104, numericCheck2104, reducedZero2104 B hB hF, mul_zero]

theorem reducedZero2105 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2105 (mixedVector B) = 0 := by
  have h4939 : mixedVector B (Sum.inr 4939) = Sparse.eval nodeValue4939 (mixedVector B) := by
    change mixedMoment B node4939 node4939Labels = _
    exact sound4939 B hB hF
  have h4941 : mixedVector B (Sum.inr 4941) = Sparse.eval nodeValue4941 (mixedVector B) := by
    change mixedMoment B node4941 node4941Labels = _
    exact sound4941 B hB hF
  have h5167 : mixedVector B (Sum.inr 5167) = Sparse.eval nodeValue5167 (mixedVector B) := by
    change mixedMoment B node5167 node5167Labels = _
    exact sound5167 B hB hF
  have h5393 : mixedVector B (Sum.inr 5393) = Sparse.eval nodeValue5393 (mixedVector B) := by
    change mixedMoment B node5393 node5393Labels = _
    exact sound5393 B hB hF
  have h5418 : mixedVector B (Sum.inr 5418) = Sparse.eval nodeValue5418 (mixedVector B) := by
    change mixedMoment B node5418 node5418Labels = _
    exact sound5418 B hB hF
  have h5460 : mixedVector B (Sum.inr 5460) = Sparse.eval nodeValue5460 (mixedVector B) := by
    change mixedMoment B node5460 node5460Labels = _
    exact sound5460 B hB hF
  have h5465 : mixedVector B (Sum.inr 5465) = Sparse.eval nodeValue5465 (mixedVector B) := by
    change mixedMoment B node5465 node5465Labels = _
    exact sound5465 B hB hF
  have h5482 : mixedVector B (Sum.inr 5482) = Sparse.eval nodeValue5482 (mixedVector B) := by
    change mixedMoment B node5482 node5482Labels = _
    exact sound5482 B hB hF
  have h5486 : mixedVector B (Sum.inr 5486) = Sparse.eval nodeValue5486 (mixedVector B) := by
    change mixedMoment B node5486 node5486Labels = _
    exact sound5486 B hB hF
  simpa only [sourceForm2647, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4939, h4941, h5167, h5393, h5418, h5460, h5465, h5482, h5486, reducedSource2105] using sourceEq2647 B hB

theorem rowSound2105 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2105 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2105, numericCheck2105, reducedZero2105 B hB hF, mul_zero]

theorem reducedZero2106 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2106 (mixedVector B) = 0 := by
  have h4073 : mixedVector B (Sum.inr 4073) = Sparse.eval nodeValue4073 (mixedVector B) := by
    change mixedMoment B node4073 node4073Labels = _
    exact sound4073 B hB hF
  have h4079 : mixedVector B (Sum.inr 4079) = Sparse.eval nodeValue4079 (mixedVector B) := by
    change mixedMoment B node4079 node4079Labels = _
    exact sound4079 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2649, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4073, h4079, h4088, h4091, reducedSource2106] using sourceEq2649 B hB

theorem rowSound2106 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2106 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2106, numericCheck2106, reducedZero2106 B hB hF, mul_zero]

theorem reducedZero2107 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2107 (mixedVector B) = 0 := by
  have h5113 : mixedVector B (Sum.inr 5113) = Sparse.eval nodeValue5113 (mixedVector B) := by
    change mixedMoment B node5113 node5113Labels = _
    exact sound5113 B hB hF
  have h5114 : mixedVector B (Sum.inr 5114) = Sparse.eval nodeValue5114 (mixedVector B) := by
    change mixedMoment B node5114 node5114Labels = _
    exact sound5114 B hB hF
  have h5168 : mixedVector B (Sum.inr 5168) = Sparse.eval nodeValue5168 (mixedVector B) := by
    change mixedMoment B node5168 node5168Labels = _
    exact sound5168 B hB hF
  have h5372 : mixedVector B (Sum.inr 5372) = Sparse.eval nodeValue5372 (mixedVector B) := by
    change mixedMoment B node5372 node5372Labels = _
    exact sound5372 B hB hF
  have h5387 : mixedVector B (Sum.inr 5387) = Sparse.eval nodeValue5387 (mixedVector B) := by
    change mixedMoment B node5387 node5387Labels = _
    exact sound5387 B hB hF
  have h5403 : mixedVector B (Sum.inr 5403) = Sparse.eval nodeValue5403 (mixedVector B) := by
    change mixedMoment B node5403 node5403Labels = _
    exact sound5403 B hB hF
  have h5439 : mixedVector B (Sum.inr 5439) = Sparse.eval nodeValue5439 (mixedVector B) := by
    change mixedMoment B node5439 node5439Labels = _
    exact sound5439 B hB hF
  have h5441 : mixedVector B (Sum.inr 5441) = Sparse.eval nodeValue5441 (mixedVector B) := by
    change mixedMoment B node5441 node5441Labels = _
    exact sound5441 B hB hF
  have h5488 : mixedVector B (Sum.inr 5488) = Sparse.eval nodeValue5488 (mixedVector B) := by
    change mixedMoment B node5488 node5488Labels = _
    exact sound5488 B hB hF
  simpa only [sourceForm2650, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5113, h5114, h5168, h5372, h5387, h5403, h5439, h5441, h5488, reducedSource2107] using sourceEq2650 B hB

theorem rowSound2107 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2107 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2107, numericCheck2107, reducedZero2107 B hB hF, mul_zero]

theorem reducedZero2108 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2108 (mixedVector B) = 0 := by
  have h4759 : mixedVector B (Sum.inr 4759) = Sparse.eval nodeValue4759 (mixedVector B) := by
    change mixedMoment B node4759 node4759Labels = _
    exact sound4759 B hB hF
  have h4763 : mixedVector B (Sum.inr 4763) = Sparse.eval nodeValue4763 (mixedVector B) := by
    change mixedMoment B node4763 node4763Labels = _
    exact sound4763 B hB hF
  have h4801 : mixedVector B (Sum.inr 4801) = Sparse.eval nodeValue4801 (mixedVector B) := by
    change mixedMoment B node4801 node4801Labels = _
    exact sound4801 B hB hF
  have h5335 : mixedVector B (Sum.inr 5335) = Sparse.eval nodeValue5335 (mixedVector B) := by
    change mixedMoment B node5335 node5335Labels = _
    exact sound5335 B hB hF
  have h5351 : mixedVector B (Sum.inr 5351) = Sparse.eval nodeValue5351 (mixedVector B) := by
    change mixedMoment B node5351 node5351Labels = _
    exact sound5351 B hB hF
  have h5416 : mixedVector B (Sum.inr 5416) = Sparse.eval nodeValue5416 (mixedVector B) := by
    change mixedMoment B node5416 node5416Labels = _
    exact sound5416 B hB hF
  have h5423 : mixedVector B (Sum.inr 5423) = Sparse.eval nodeValue5423 (mixedVector B) := by
    change mixedMoment B node5423 node5423Labels = _
    exact sound5423 B hB hF
  have h5433 : mixedVector B (Sum.inr 5433) = Sparse.eval nodeValue5433 (mixedVector B) := by
    change mixedMoment B node5433 node5433Labels = _
    exact sound5433 B hB hF
  have h5497 : mixedVector B (Sum.inr 5497) = Sparse.eval nodeValue5497 (mixedVector B) := by
    change mixedMoment B node5497 node5497Labels = _
    exact sound5497 B hB hF
  simpa only [sourceForm2651, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4759, h4763, h4801, h5335, h5351, h5416, h5423, h5433, h5497, reducedSource2108] using sourceEq2651 B hB

theorem rowSound2108 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2108 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2108, numericCheck2108, reducedZero2108 B hB hF, mul_zero]

theorem reducedZero2109 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2109 (mixedVector B) = 0 := by
  have h4761 : mixedVector B (Sum.inr 4761) = Sparse.eval nodeValue4761 (mixedVector B) := by
    change mixedMoment B node4761 node4761Labels = _
    exact sound4761 B hB hF
  have h4762 : mixedVector B (Sum.inr 4762) = Sparse.eval nodeValue4762 (mixedVector B) := by
    change mixedMoment B node4762 node4762Labels = _
    exact sound4762 B hB hF
  have h4768 : mixedVector B (Sum.inr 4768) = Sparse.eval nodeValue4768 (mixedVector B) := by
    change mixedMoment B node4768 node4768Labels = _
    exact sound4768 B hB hF
  have h4803 : mixedVector B (Sum.inr 4803) = Sparse.eval nodeValue4803 (mixedVector B) := by
    change mixedMoment B node4803 node4803Labels = _
    exact sound4803 B hB hF
  have h5044 : mixedVector B (Sum.inr 5044) = Sparse.eval nodeValue5044 (mixedVector B) := by
    change mixedMoment B node5044 node5044Labels = _
    exact sound5044 B hB hF
  have h5076 : mixedVector B (Sum.inr 5076) = Sparse.eval nodeValue5076 (mixedVector B) := by
    change mixedMoment B node5076 node5076Labels = _
    exact sound5076 B hB hF
  have h5187 : mixedVector B (Sum.inr 5187) = Sparse.eval nodeValue5187 (mixedVector B) := by
    change mixedMoment B node5187 node5187Labels = _
    exact sound5187 B hB hF
  have h5215 : mixedVector B (Sum.inr 5215) = Sparse.eval nodeValue5215 (mixedVector B) := by
    change mixedMoment B node5215 node5215Labels = _
    exact sound5215 B hB hF
  have h5219 : mixedVector B (Sum.inr 5219) = Sparse.eval nodeValue5219 (mixedVector B) := by
    change mixedMoment B node5219 node5219Labels = _
    exact sound5219 B hB hF
  have h5249 : mixedVector B (Sum.inr 5249) = Sparse.eval nodeValue5249 (mixedVector B) := by
    change mixedMoment B node5249 node5249Labels = _
    exact sound5249 B hB hF
  have h5338 : mixedVector B (Sum.inr 5338) = Sparse.eval nodeValue5338 (mixedVector B) := by
    change mixedMoment B node5338 node5338Labels = _
    exact sound5338 B hB hF
  have h5353 : mixedVector B (Sum.inr 5353) = Sparse.eval nodeValue5353 (mixedVector B) := by
    change mixedMoment B node5353 node5353Labels = _
    exact sound5353 B hB hF
  have h5354 : mixedVector B (Sum.inr 5354) = Sparse.eval nodeValue5354 (mixedVector B) := by
    change mixedMoment B node5354 node5354Labels = _
    exact sound5354 B hB hF
  have h5401 : mixedVector B (Sum.inr 5401) = Sparse.eval nodeValue5401 (mixedVector B) := by
    change mixedMoment B node5401 node5401Labels = _
    exact sound5401 B hB hF
  have h5406 : mixedVector B (Sum.inr 5406) = Sparse.eval nodeValue5406 (mixedVector B) := by
    change mixedMoment B node5406 node5406Labels = _
    exact sound5406 B hB hF
  have h5408 : mixedVector B (Sum.inr 5408) = Sparse.eval nodeValue5408 (mixedVector B) := by
    change mixedMoment B node5408 node5408Labels = _
    exact sound5408 B hB hF
  have h5414 : mixedVector B (Sum.inr 5414) = Sparse.eval nodeValue5414 (mixedVector B) := by
    change mixedMoment B node5414 node5414Labels = _
    exact sound5414 B hB hF
  have h5425 : mixedVector B (Sum.inr 5425) = Sparse.eval nodeValue5425 (mixedVector B) := by
    change mixedMoment B node5425 node5425Labels = _
    exact sound5425 B hB hF
  have h5430 : mixedVector B (Sum.inr 5430) = Sparse.eval nodeValue5430 (mixedVector B) := by
    change mixedMoment B node5430 node5430Labels = _
    exact sound5430 B hB hF
  have h5431 : mixedVector B (Sum.inr 5431) = Sparse.eval nodeValue5431 (mixedVector B) := by
    change mixedMoment B node5431 node5431Labels = _
    exact sound5431 B hB hF
  have h5481 : mixedVector B (Sum.inr 5481) = Sparse.eval nodeValue5481 (mixedVector B) := by
    change mixedMoment B node5481 node5481Labels = _
    exact sound5481 B hB hF
  simpa only [sourceForm2652, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4761, h4762, h4768, h4803, h5044, h5076, h5187, h5215, h5219, h5249, h5338, h5353, h5354, h5401, h5406, h5408, h5414, h5425, h5430, h5431, h5481, reducedSource2109] using sourceEq2652 B hB

theorem rowSound2109 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2109 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2109, numericCheck2109, reducedZero2109 B hB hF, mul_zero]

theorem reducedZero2110 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2110 (mixedVector B) = 0 := by
  have h2171 : mixedVector B (Sum.inr 2171) = Sparse.eval nodeValue2171 (mixedVector B) := by
    change mixedMoment B node2171 node2171Labels = _
    exact sound2171 B hB hF
  have h2175 : mixedVector B (Sum.inr 2175) = Sparse.eval nodeValue2175 (mixedVector B) := by
    change mixedMoment B node2175 node2175Labels = _
    exact sound2175 B hB hF
  have h2178 : mixedVector B (Sum.inr 2178) = Sparse.eval nodeValue2178 (mixedVector B) := by
    change mixedMoment B node2178 node2178Labels = _
    exact sound2178 B hB hF
  have h2195 : mixedVector B (Sum.inr 2195) = Sparse.eval nodeValue2195 (mixedVector B) := by
    change mixedMoment B node2195 node2195Labels = _
    exact sound2195 B hB hF
  have h2653 : mixedVector B (Sum.inr 2653) = Sparse.eval nodeValue2653 (mixedVector B) := by
    change mixedMoment B node2653 node2653Labels = _
    exact sound2653 B hB hF
  have h2661 : mixedVector B (Sum.inr 2661) = Sparse.eval nodeValue2661 (mixedVector B) := by
    change mixedMoment B node2661 node2661Labels = _
    exact sound2661 B hB hF
  have h2708 : mixedVector B (Sum.inr 2708) = Sparse.eval nodeValue2708 (mixedVector B) := by
    change mixedMoment B node2708 node2708Labels = _
    exact sound2708 B hB hF
  have h3474 : mixedVector B (Sum.inr 3474) = Sparse.eval nodeValue3474 (mixedVector B) := by
    change mixedMoment B node3474 node3474Labels = _
    exact sound3474 B hB hF
  have h3477 : mixedVector B (Sum.inr 3477) = Sparse.eval nodeValue3477 (mixedVector B) := by
    change mixedMoment B node3477 node3477Labels = _
    exact sound3477 B hB hF
  have h3537 : mixedVector B (Sum.inr 3537) = Sparse.eval nodeValue3537 (mixedVector B) := by
    change mixedMoment B node3537 node3537Labels = _
    exact sound3537 B hB hF
  have h3755 : mixedVector B (Sum.inr 3755) = Sparse.eval nodeValue3755 (mixedVector B) := by
    change mixedMoment B node3755 node3755Labels = _
    exact sound3755 B hB hF
  have h3761 : mixedVector B (Sum.inr 3761) = Sparse.eval nodeValue3761 (mixedVector B) := by
    change mixedMoment B node3761 node3761Labels = _
    exact sound3761 B hB hF
  have h3769 : mixedVector B (Sum.inr 3769) = Sparse.eval nodeValue3769 (mixedVector B) := by
    change mixedMoment B node3769 node3769Labels = _
    exact sound3769 B hB hF
  have h3804 : mixedVector B (Sum.inr 3804) = Sparse.eval nodeValue3804 (mixedVector B) := by
    change mixedMoment B node3804 node3804Labels = _
    exact sound3804 B hB hF
  have h3806 : mixedVector B (Sum.inr 3806) = Sparse.eval nodeValue3806 (mixedVector B) := by
    change mixedMoment B node3806 node3806Labels = _
    exact sound3806 B hB hF
  have h3812 : mixedVector B (Sum.inr 3812) = Sparse.eval nodeValue3812 (mixedVector B) := by
    change mixedMoment B node3812 node3812Labels = _
    exact sound3812 B hB hF
  have h3840 : mixedVector B (Sum.inr 3840) = Sparse.eval nodeValue3840 (mixedVector B) := by
    change mixedMoment B node3840 node3840Labels = _
    exact sound3840 B hB hF
  have h3849 : mixedVector B (Sum.inr 3849) = Sparse.eval nodeValue3849 (mixedVector B) := by
    change mixedMoment B node3849 node3849Labels = _
    exact sound3849 B hB hF
  have h3869 : mixedVector B (Sum.inr 3869) = Sparse.eval nodeValue3869 (mixedVector B) := by
    change mixedMoment B node3869 node3869Labels = _
    exact sound3869 B hB hF
  have h3871 : mixedVector B (Sum.inr 3871) = Sparse.eval nodeValue3871 (mixedVector B) := by
    change mixedMoment B node3871 node3871Labels = _
    exact sound3871 B hB hF
  have h3979 : mixedVector B (Sum.inr 3979) = Sparse.eval nodeValue3979 (mixedVector B) := by
    change mixedMoment B node3979 node3979Labels = _
    exact sound3979 B hB hF
  simpa only [sourceForm2653, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2171, h2175, h2178, h2195, h2653, h2661, h2708, h3474, h3477, h3537, h3755, h3761, h3769, h3804, h3806, h3812, h3840, h3849, h3869, h3871, h3979, reducedSource2110] using sourceEq2653 B hB

theorem rowSound2110 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2110 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2110, numericCheck2110, reducedZero2110 B hB hF, mul_zero]

theorem reducedZero2111 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2111 (mixedVector B) = 0 := by
  have h4077 : mixedVector B (Sum.inr 4077) = Sparse.eval nodeValue4077 (mixedVector B) := by
    change mixedMoment B node4077 node4077Labels = _
    exact sound4077 B hB hF
  have h4078 : mixedVector B (Sum.inr 4078) = Sparse.eval nodeValue4078 (mixedVector B) := by
    change mixedMoment B node4078 node4078Labels = _
    exact sound4078 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  have h4086 : mixedVector B (Sum.inr 4086) = Sparse.eval nodeValue4086 (mixedVector B) := by
    change mixedMoment B node4086 node4086Labels = _
    exact sound4086 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  have h4090 : mixedVector B (Sum.inr 4090) = Sparse.eval nodeValue4090 (mixedVector B) := by
    change mixedMoment B node4090 node4090Labels = _
    exact sound4090 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  have h4095 : mixedVector B (Sum.inr 4095) = Sparse.eval nodeValue4095 (mixedVector B) := by
    change mixedMoment B node4095 node4095Labels = _
    exact sound4095 B hB hF
  simpa only [sourceForm2654, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4077, h4078, h4080, h4086, h4088, h4090, h4091, h4092, h4095, reducedSource2111] using sourceEq2654 B hB

theorem rowSound2111 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2111 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2111, numericCheck2111, reducedZero2111 B hB hF, mul_zero]

theorem sourceRowsAt2096 : MixedData.sourceRows (2096 : Fin 2425) =
    MixedData.row2096 := by decide +kernel

theorem sourceRowsAt2097 : MixedData.sourceRows (2097 : Fin 2425) =
    MixedData.row2097 := by decide +kernel

theorem sourceRowsAt2098 : MixedData.sourceRows (2098 : Fin 2425) =
    MixedData.row2098 := by decide +kernel

theorem sourceRowsAt2099 : MixedData.sourceRows (2099 : Fin 2425) =
    MixedData.row2099 := by decide +kernel

theorem sourceRowsAt2100 : MixedData.sourceRows (2100 : Fin 2425) =
    MixedData.row2100 := by decide +kernel

theorem sourceRowsAt2101 : MixedData.sourceRows (2101 : Fin 2425) =
    MixedData.row2101 := by decide +kernel

theorem sourceRowsAt2102 : MixedData.sourceRows (2102 : Fin 2425) =
    MixedData.row2102 := by decide +kernel

theorem sourceRowsAt2103 : MixedData.sourceRows (2103 : Fin 2425) =
    MixedData.row2103 := by decide +kernel

theorem sourceRowsAt2104 : MixedData.sourceRows (2104 : Fin 2425) =
    MixedData.row2104 := by decide +kernel

theorem sourceRowsAt2105 : MixedData.sourceRows (2105 : Fin 2425) =
    MixedData.row2105 := by decide +kernel

theorem sourceRowsAt2106 : MixedData.sourceRows (2106 : Fin 2425) =
    MixedData.row2106 := by decide +kernel

theorem sourceRowsAt2107 : MixedData.sourceRows (2107 : Fin 2425) =
    MixedData.row2107 := by decide +kernel

theorem sourceRowsAt2108 : MixedData.sourceRows (2108 : Fin 2425) =
    MixedData.row2108 := by decide +kernel

theorem sourceRowsAt2109 : MixedData.sourceRows (2109 : Fin 2425) =
    MixedData.row2109 := by decide +kernel

theorem sourceRowsAt2110 : MixedData.sourceRows (2110 : Fin 2425) =
    MixedData.row2110 := by decide +kernel

theorem sourceRowsAt2111 : MixedData.sourceRows (2111 : Fin 2425) =
    MixedData.row2111 := by decide +kernel

theorem chunkSound131 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 131) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 2096 ∨ k.val = 2097 ∨ k.val = 2098 ∨ k.val = 2099 ∨ k.val = 2100 ∨ k.val = 2101 ∨ k.val = 2102 ∨ k.val = 2103 ∨ k.val = 2104 ∨ k.val = 2105 ∨ k.val = 2106 ∨ k.val = 2107 ∨ k.val = 2108 ∨ k.val = 2109 ∨ k.val = 2110 ∨ k.val = 2111 := by omega
  rcases heq with h2096 | h2097 | h2098 | h2099 | h2100 | h2101 | h2102 | h2103 | h2104 | h2105 | h2106 | h2107 | h2108 | h2109 | h2110 | h2111
  · have he : k = (2096 : Fin 2425) := Fin.ext h2096
    subst k
    rw [sourceRowsAt2096]
    exact rowSound2096 B hB hF
  · have he : k = (2097 : Fin 2425) := Fin.ext h2097
    subst k
    rw [sourceRowsAt2097]
    exact rowSound2097 B hB hF
  · have he : k = (2098 : Fin 2425) := Fin.ext h2098
    subst k
    rw [sourceRowsAt2098]
    exact rowSound2098 B hB hF
  · have he : k = (2099 : Fin 2425) := Fin.ext h2099
    subst k
    rw [sourceRowsAt2099]
    exact rowSound2099 B hB hF
  · have he : k = (2100 : Fin 2425) := Fin.ext h2100
    subst k
    rw [sourceRowsAt2100]
    exact rowSound2100 B hB hF
  · have he : k = (2101 : Fin 2425) := Fin.ext h2101
    subst k
    rw [sourceRowsAt2101]
    exact rowSound2101 B hB hF
  · have he : k = (2102 : Fin 2425) := Fin.ext h2102
    subst k
    rw [sourceRowsAt2102]
    exact rowSound2102 B hB hF
  · have he : k = (2103 : Fin 2425) := Fin.ext h2103
    subst k
    rw [sourceRowsAt2103]
    exact rowSound2103 B hB hF
  · have he : k = (2104 : Fin 2425) := Fin.ext h2104
    subst k
    rw [sourceRowsAt2104]
    exact rowSound2104 B hB hF
  · have he : k = (2105 : Fin 2425) := Fin.ext h2105
    subst k
    rw [sourceRowsAt2105]
    exact rowSound2105 B hB hF
  · have he : k = (2106 : Fin 2425) := Fin.ext h2106
    subst k
    rw [sourceRowsAt2106]
    exact rowSound2106 B hB hF
  · have he : k = (2107 : Fin 2425) := Fin.ext h2107
    subst k
    rw [sourceRowsAt2107]
    exact rowSound2107 B hB hF
  · have he : k = (2108 : Fin 2425) := Fin.ext h2108
    subst k
    rw [sourceRowsAt2108]
    exact rowSound2108 B hB hF
  · have he : k = (2109 : Fin 2425) := Fin.ext h2109
    subst k
    rw [sourceRowsAt2109]
    exact rowSound2109 B hB hF
  · have he : k = (2110 : Fin 2425) := Fin.ext h2110
    subst k
    rw [sourceRowsAt2110]
    exact rowSound2110 B hB hF
  · have he : k = (2111 : Fin 2425) := Fin.ext h2111
    subst k
    rw [sourceRowsAt2111]
    exact rowSound2111 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
