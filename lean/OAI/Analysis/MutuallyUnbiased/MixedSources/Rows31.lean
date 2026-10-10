import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic31
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources18

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero496 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource496 (mixedVector B) = 0 := by
  have h1220 : mixedVector B (Sum.inr 1220) = Sparse.eval nodeValue1220 (mixedVector B) := by
    change mixedMoment B node1220 node1220Labels = _
    exact sound1220 B hB hF
  have h2489 : mixedVector B (Sum.inr 2489) = Sparse.eval nodeValue2489 (mixedVector B) := by
    change mixedMoment B node2489 node2489Labels = _
    exact sound2489 B hB hF
  have h2546 : mixedVector B (Sum.inr 2546) = Sparse.eval nodeValue2546 (mixedVector B) := by
    change mixedMoment B node2546 node2546Labels = _
    exact sound2546 B hB hF
  have h2621 : mixedVector B (Sum.inr 2621) = Sparse.eval nodeValue2621 (mixedVector B) := by
    change mixedMoment B node2621 node2621Labels = _
    exact sound2621 B hB hF
  have h2723 : mixedVector B (Sum.inr 2723) = Sparse.eval nodeValue2723 (mixedVector B) := by
    change mixedMoment B node2723 node2723Labels = _
    exact sound2723 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm587, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1220, h2489, h2546, h2621, h2723, h4091, reducedSource496] using sourceEq587 B hB

theorem rowSound496 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row496 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck496, numericCheck496, reducedZero496 B hB hF, mul_zero]

theorem reducedZero497 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource497 (mixedVector B) = 0 := by
  have h4399 : mixedVector B (Sum.inr 4399) = Sparse.eval nodeValue4399 (mixedVector B) := by
    change mixedMoment B node4399 node4399Labels = _
    exact sound4399 B hB hF
  have h4401 : mixedVector B (Sum.inr 4401) = Sparse.eval nodeValue4401 (mixedVector B) := by
    change mixedMoment B node4401 node4401Labels = _
    exact sound4401 B hB hF
  have h4404 : mixedVector B (Sum.inr 4404) = Sparse.eval nodeValue4404 (mixedVector B) := by
    change mixedMoment B node4404 node4404Labels = _
    exact sound4404 B hB hF
  have h4424 : mixedVector B (Sum.inr 4424) = Sparse.eval nodeValue4424 (mixedVector B) := by
    change mixedMoment B node4424 node4424Labels = _
    exact sound4424 B hB hF
  have h4458 : mixedVector B (Sum.inr 4458) = Sparse.eval nodeValue4458 (mixedVector B) := by
    change mixedMoment B node4458 node4458Labels = _
    exact sound4458 B hB hF
  have h4998 : mixedVector B (Sum.inr 4998) = Sparse.eval nodeValue4998 (mixedVector B) := by
    change mixedMoment B node4998 node4998Labels = _
    exact sound4998 B hB hF
  have h5000 : mixedVector B (Sum.inr 5000) = Sparse.eval nodeValue5000 (mixedVector B) := by
    change mixedMoment B node5000 node5000Labels = _
    exact sound5000 B hB hF
  have h5003 : mixedVector B (Sum.inr 5003) = Sparse.eval nodeValue5003 (mixedVector B) := by
    change mixedMoment B node5003 node5003Labels = _
    exact sound5003 B hB hF
  have h5018 : mixedVector B (Sum.inr 5018) = Sparse.eval nodeValue5018 (mixedVector B) := by
    change mixedMoment B node5018 node5018Labels = _
    exact sound5018 B hB hF
  have h5047 : mixedVector B (Sum.inr 5047) = Sparse.eval nodeValue5047 (mixedVector B) := by
    change mixedMoment B node5047 node5047Labels = _
    exact sound5047 B hB hF
  have h5050 : mixedVector B (Sum.inr 5050) = Sparse.eval nodeValue5050 (mixedVector B) := by
    change mixedMoment B node5050 node5050Labels = _
    exact sound5050 B hB hF
  have h5059 : mixedVector B (Sum.inr 5059) = Sparse.eval nodeValue5059 (mixedVector B) := by
    change mixedMoment B node5059 node5059Labels = _
    exact sound5059 B hB hF
  have h5073 : mixedVector B (Sum.inr 5073) = Sparse.eval nodeValue5073 (mixedVector B) := by
    change mixedMoment B node5073 node5073Labels = _
    exact sound5073 B hB hF
  have h5075 : mixedVector B (Sum.inr 5075) = Sparse.eval nodeValue5075 (mixedVector B) := by
    change mixedMoment B node5075 node5075Labels = _
    exact sound5075 B hB hF
  have h5137 : mixedVector B (Sum.inr 5137) = Sparse.eval nodeValue5137 (mixedVector B) := by
    change mixedMoment B node5137 node5137Labels = _
    exact sound5137 B hB hF
  have h5141 : mixedVector B (Sum.inr 5141) = Sparse.eval nodeValue5141 (mixedVector B) := by
    change mixedMoment B node5141 node5141Labels = _
    exact sound5141 B hB hF
  have h5169 : mixedVector B (Sum.inr 5169) = Sparse.eval nodeValue5169 (mixedVector B) := by
    change mixedMoment B node5169 node5169Labels = _
    exact sound5169 B hB hF
  have h5257 : mixedVector B (Sum.inr 5257) = Sparse.eval nodeValue5257 (mixedVector B) := by
    change mixedMoment B node5257 node5257Labels = _
    exact sound5257 B hB hF
  have h5258 : mixedVector B (Sum.inr 5258) = Sparse.eval nodeValue5258 (mixedVector B) := by
    change mixedMoment B node5258 node5258Labels = _
    exact sound5258 B hB hF
  have h5259 : mixedVector B (Sum.inr 5259) = Sparse.eval nodeValue5259 (mixedVector B) := by
    change mixedMoment B node5259 node5259Labels = _
    exact sound5259 B hB hF
  have h5261 : mixedVector B (Sum.inr 5261) = Sparse.eval nodeValue5261 (mixedVector B) := by
    change mixedMoment B node5261 node5261Labels = _
    exact sound5261 B hB hF
  have h5271 : mixedVector B (Sum.inr 5271) = Sparse.eval nodeValue5271 (mixedVector B) := by
    change mixedMoment B node5271 node5271Labels = _
    exact sound5271 B hB hF
  have h5275 : mixedVector B (Sum.inr 5275) = Sparse.eval nodeValue5275 (mixedVector B) := by
    change mixedMoment B node5275 node5275Labels = _
    exact sound5275 B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292 B hB hF
  have h5293 : mixedVector B (Sum.inr 5293) = Sparse.eval nodeValue5293 (mixedVector B) := by
    change mixedMoment B node5293 node5293Labels = _
    exact sound5293 B hB hF
  have h5473 : mixedVector B (Sum.inr 5473) = Sparse.eval nodeValue5473 (mixedVector B) := by
    change mixedMoment B node5473 node5473Labels = _
    exact sound5473 B hB hF
  have h5477 : mixedVector B (Sum.inr 5477) = Sparse.eval nodeValue5477 (mixedVector B) := by
    change mixedMoment B node5477 node5477Labels = _
    exact sound5477 B hB hF
  have h5483 : mixedVector B (Sum.inr 5483) = Sparse.eval nodeValue5483 (mixedVector B) := by
    change mixedMoment B node5483 node5483Labels = _
    exact sound5483 B hB hF
  have h5490 : mixedVector B (Sum.inr 5490) = Sparse.eval nodeValue5490 (mixedVector B) := by
    change mixedMoment B node5490 node5490Labels = _
    exact sound5490 B hB hF
  have h5491 : mixedVector B (Sum.inr 5491) = Sparse.eval nodeValue5491 (mixedVector B) := by
    change mixedMoment B node5491 node5491Labels = _
    exact sound5491 B hB hF
  simpa only [sourceForm588, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4399, h4401, h4404, h4424, h4458, h4998, h5000, h5003, h5018, h5047, h5050, h5059, h5073, h5075, h5137, h5141, h5169, h5257, h5258, h5259, h5261, h5271, h5275, h5292, h5293, h5473, h5477, h5483, h5490, h5491, reducedSource497] using sourceEq588 B hB

theorem rowSound497 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row497 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck497, numericCheck497, reducedZero497 B hB hF, mul_zero]

theorem reducedZero498 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource498 (mixedVector B) = 0 := by
  have h980 : mixedVector B (Sum.inr 980) = Sparse.eval nodeValue980 (mixedVector B) := by
    change mixedMoment B node980 node980Labels = _
    exact sound980 B hB hF
  have h982 : mixedVector B (Sum.inr 982) = Sparse.eval nodeValue982 (mixedVector B) := by
    change mixedMoment B node982 node982Labels = _
    exact sound982 B hB hF
  have h985 : mixedVector B (Sum.inr 985) = Sparse.eval nodeValue985 (mixedVector B) := by
    change mixedMoment B node985 node985Labels = _
    exact sound985 B hB hF
  have h1005 : mixedVector B (Sum.inr 1005) = Sparse.eval nodeValue1005 (mixedVector B) := by
    change mixedMoment B node1005 node1005Labels = _
    exact sound1005 B hB hF
  have h1041 : mixedVector B (Sum.inr 1041) = Sparse.eval nodeValue1041 (mixedVector B) := by
    change mixedMoment B node1041 node1041Labels = _
    exact sound1041 B hB hF
  have h2383 : mixedVector B (Sum.inr 2383) = Sparse.eval nodeValue2383 (mixedVector B) := by
    change mixedMoment B node2383 node2383Labels = _
    exact sound2383 B hB hF
  have h2385 : mixedVector B (Sum.inr 2385) = Sparse.eval nodeValue2385 (mixedVector B) := by
    change mixedMoment B node2385 node2385Labels = _
    exact sound2385 B hB hF
  have h2388 : mixedVector B (Sum.inr 2388) = Sparse.eval nodeValue2388 (mixedVector B) := by
    change mixedMoment B node2388 node2388Labels = _
    exact sound2388 B hB hF
  have h2404 : mixedVector B (Sum.inr 2404) = Sparse.eval nodeValue2404 (mixedVector B) := by
    change mixedMoment B node2404 node2404Labels = _
    exact sound2404 B hB hF
  have h2449 : mixedVector B (Sum.inr 2449) = Sparse.eval nodeValue2449 (mixedVector B) := by
    change mixedMoment B node2449 node2449Labels = _
    exact sound2449 B hB hF
  have h2452 : mixedVector B (Sum.inr 2452) = Sparse.eval nodeValue2452 (mixedVector B) := by
    change mixedMoment B node2452 node2452Labels = _
    exact sound2452 B hB hF
  have h2462 : mixedVector B (Sum.inr 2462) = Sparse.eval nodeValue2462 (mixedVector B) := by
    change mixedMoment B node2462 node2462Labels = _
    exact sound2462 B hB hF
  have h2480 : mixedVector B (Sum.inr 2480) = Sparse.eval nodeValue2480 (mixedVector B) := by
    change mixedMoment B node2480 node2480Labels = _
    exact sound2480 B hB hF
  have h2482 : mixedVector B (Sum.inr 2482) = Sparse.eval nodeValue2482 (mixedVector B) := by
    change mixedMoment B node2482 node2482Labels = _
    exact sound2482 B hB hF
  have h2556 : mixedVector B (Sum.inr 2556) = Sparse.eval nodeValue2556 (mixedVector B) := by
    change mixedMoment B node2556 node2556Labels = _
    exact sound2556 B hB hF
  have h2561 : mixedVector B (Sum.inr 2561) = Sparse.eval nodeValue2561 (mixedVector B) := by
    change mixedMoment B node2561 node2561Labels = _
    exact sound2561 B hB hF
  have h2595 : mixedVector B (Sum.inr 2595) = Sparse.eval nodeValue2595 (mixedVector B) := by
    change mixedMoment B node2595 node2595Labels = _
    exact sound2595 B hB hF
  have h2721 : mixedVector B (Sum.inr 2721) = Sparse.eval nodeValue2721 (mixedVector B) := by
    change mixedMoment B node2721 node2721Labels = _
    exact sound2721 B hB hF
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  have h2723 : mixedVector B (Sum.inr 2723) = Sparse.eval nodeValue2723 (mixedVector B) := by
    change mixedMoment B node2723 node2723Labels = _
    exact sound2723 B hB hF
  have h2726 : mixedVector B (Sum.inr 2726) = Sparse.eval nodeValue2726 (mixedVector B) := by
    change mixedMoment B node2726 node2726Labels = _
    exact sound2726 B hB hF
  have h2739 : mixedVector B (Sum.inr 2739) = Sparse.eval nodeValue2739 (mixedVector B) := by
    change mixedMoment B node2739 node2739Labels = _
    exact sound2739 B hB hF
  have h2743 : mixedVector B (Sum.inr 2743) = Sparse.eval nodeValue2743 (mixedVector B) := by
    change mixedMoment B node2743 node2743Labels = _
    exact sound2743 B hB hF
  have h2766 : mixedVector B (Sum.inr 2766) = Sparse.eval nodeValue2766 (mixedVector B) := by
    change mixedMoment B node2766 node2766Labels = _
    exact sound2766 B hB hF
  have h2767 : mixedVector B (Sum.inr 2767) = Sparse.eval nodeValue2767 (mixedVector B) := by
    change mixedMoment B node2767 node2767Labels = _
    exact sound2767 B hB hF
  have h3958 : mixedVector B (Sum.inr 3958) = Sparse.eval nodeValue3958 (mixedVector B) := by
    change mixedMoment B node3958 node3958Labels = _
    exact sound3958 B hB hF
  have h3971 : mixedVector B (Sum.inr 3971) = Sparse.eval nodeValue3971 (mixedVector B) := by
    change mixedMoment B node3971 node3971Labels = _
    exact sound3971 B hB hF
  have h3981 : mixedVector B (Sum.inr 3981) = Sparse.eval nodeValue3981 (mixedVector B) := by
    change mixedMoment B node3981 node3981Labels = _
    exact sound3981 B hB hF
  have h4013 : mixedVector B (Sum.inr 4013) = Sparse.eval nodeValue4013 (mixedVector B) := by
    change mixedMoment B node4013 node4013Labels = _
    exact sound4013 B hB hF
  have h4014 : mixedVector B (Sum.inr 4014) = Sparse.eval nodeValue4014 (mixedVector B) := by
    change mixedMoment B node4014 node4014Labels = _
    exact sound4014 B hB hF
  simpa only [sourceForm589, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h980, h982, h985, h1005, h1041, h2383, h2385, h2388, h2404, h2449, h2452, h2462, h2480, h2482, h2556, h2561, h2595, h2721, h2722, h2723, h2726, h2739, h2743, h2766, h2767, h3958, h3971, h3981, h4013, h4014, reducedSource498] using sourceEq589 B hB

theorem rowSound498 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row498 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck498, numericCheck498, reducedZero498 B hB hF, mul_zero]

theorem reducedZero499 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource499 (mixedVector B) = 0 := by
  have h4831 : mixedVector B (Sum.inr 4831) = Sparse.eval nodeValue4831 (mixedVector B) := by
    change mixedMoment B node4831 node4831Labels = _
    exact sound4831 B hB hF
  have h4834 : mixedVector B (Sum.inr 4834) = Sparse.eval nodeValue4834 (mixedVector B) := by
    change mixedMoment B node4834 node4834Labels = _
    exact sound4834 B hB hF
  have h4835 : mixedVector B (Sum.inr 4835) = Sparse.eval nodeValue4835 (mixedVector B) := by
    change mixedMoment B node4835 node4835Labels = _
    exact sound4835 B hB hF
  have h4839 : mixedVector B (Sum.inr 4839) = Sparse.eval nodeValue4839 (mixedVector B) := by
    change mixedMoment B node4839 node4839Labels = _
    exact sound4839 B hB hF
  have h4895 : mixedVector B (Sum.inr 4895) = Sparse.eval nodeValue4895 (mixedVector B) := by
    change mixedMoment B node4895 node4895Labels = _
    exact sound4895 B hB hF
  have h5220 : mixedVector B (Sum.inr 5220) = Sparse.eval nodeValue5220 (mixedVector B) := by
    change mixedMoment B node5220 node5220Labels = _
    exact sound5220 B hB hF
  have h5228 : mixedVector B (Sum.inr 5228) = Sparse.eval nodeValue5228 (mixedVector B) := by
    change mixedMoment B node5228 node5228Labels = _
    exact sound5228 B hB hF
  have h5229 : mixedVector B (Sum.inr 5229) = Sparse.eval nodeValue5229 (mixedVector B) := by
    change mixedMoment B node5229 node5229Labels = _
    exact sound5229 B hB hF
  have h5233 : mixedVector B (Sum.inr 5233) = Sparse.eval nodeValue5233 (mixedVector B) := by
    change mixedMoment B node5233 node5233Labels = _
    exact sound5233 B hB hF
  have h5241 : mixedVector B (Sum.inr 5241) = Sparse.eval nodeValue5241 (mixedVector B) := by
    change mixedMoment B node5241 node5241Labels = _
    exact sound5241 B hB hF
  have h5242 : mixedVector B (Sum.inr 5242) = Sparse.eval nodeValue5242 (mixedVector B) := by
    change mixedMoment B node5242 node5242Labels = _
    exact sound5242 B hB hF
  have h5244 : mixedVector B (Sum.inr 5244) = Sparse.eval nodeValue5244 (mixedVector B) := by
    change mixedMoment B node5244 node5244Labels = _
    exact sound5244 B hB hF
  have h5250 : mixedVector B (Sum.inr 5250) = Sparse.eval nodeValue5250 (mixedVector B) := by
    change mixedMoment B node5250 node5250Labels = _
    exact sound5250 B hB hF
  have h5251 : mixedVector B (Sum.inr 5251) = Sparse.eval nodeValue5251 (mixedVector B) := by
    change mixedMoment B node5251 node5251Labels = _
    exact sound5251 B hB hF
  have h5258 : mixedVector B (Sum.inr 5258) = Sparse.eval nodeValue5258 (mixedVector B) := by
    change mixedMoment B node5258 node5258Labels = _
    exact sound5258 B hB hF
  have h5259 : mixedVector B (Sum.inr 5259) = Sparse.eval nodeValue5259 (mixedVector B) := by
    change mixedMoment B node5259 node5259Labels = _
    exact sound5259 B hB hF
  have h5260 : mixedVector B (Sum.inr 5260) = Sparse.eval nodeValue5260 (mixedVector B) := by
    change mixedMoment B node5260 node5260Labels = _
    exact sound5260 B hB hF
  have h5266 : mixedVector B (Sum.inr 5266) = Sparse.eval nodeValue5266 (mixedVector B) := by
    change mixedMoment B node5266 node5266Labels = _
    exact sound5266 B hB hF
  have h5267 : mixedVector B (Sum.inr 5267) = Sparse.eval nodeValue5267 (mixedVector B) := by
    change mixedMoment B node5267 node5267Labels = _
    exact sound5267 B hB hF
  have h5274 : mixedVector B (Sum.inr 5274) = Sparse.eval nodeValue5274 (mixedVector B) := by
    change mixedMoment B node5274 node5274Labels = _
    exact sound5274 B hB hF
  have h5275 : mixedVector B (Sum.inr 5275) = Sparse.eval nodeValue5275 (mixedVector B) := by
    change mixedMoment B node5275 node5275Labels = _
    exact sound5275 B hB hF
  have h5293 : mixedVector B (Sum.inr 5293) = Sparse.eval nodeValue5293 (mixedVector B) := by
    change mixedMoment B node5293 node5293Labels = _
    exact sound5293 B hB hF
  have h5294 : mixedVector B (Sum.inr 5294) = Sparse.eval nodeValue5294 (mixedVector B) := by
    change mixedMoment B node5294 node5294Labels = _
    exact sound5294 B hB hF
  have h5309 : mixedVector B (Sum.inr 5309) = Sparse.eval nodeValue5309 (mixedVector B) := by
    change mixedMoment B node5309 node5309Labels = _
    exact sound5309 B hB hF
  simpa only [sourceForm590, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4831, h4834, h4835, h4839, h4895, h5220, h5228, h5229, h5233, h5241, h5242, h5244, h5250, h5251, h5258, h5259, h5260, h5266, h5267, h5274, h5275, h5293, h5294, h5309, reducedSource499] using sourceEq590 B hB

theorem rowSound499 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row499 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck499, numericCheck499, reducedZero499 B hB hF, mul_zero]

theorem reducedZero500 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource500 (mixedVector B) = 0 := by
  have h2191 : mixedVector B (Sum.inr 2191) = Sparse.eval nodeValue2191 (mixedVector B) := by
    change mixedMoment B node2191 node2191Labels = _
    exact sound2191 B hB hF
  have h2205 : mixedVector B (Sum.inr 2205) = Sparse.eval nodeValue2205 (mixedVector B) := by
    change mixedMoment B node2205 node2205Labels = _
    exact sound2205 B hB hF
  have h2206 : mixedVector B (Sum.inr 2206) = Sparse.eval nodeValue2206 (mixedVector B) := by
    change mixedMoment B node2206 node2206Labels = _
    exact sound2206 B hB hF
  have h2216 : mixedVector B (Sum.inr 2216) = Sparse.eval nodeValue2216 (mixedVector B) := by
    change mixedMoment B node2216 node2216Labels = _
    exact sound2216 B hB hF
  have h2265 : mixedVector B (Sum.inr 2265) = Sparse.eval nodeValue2265 (mixedVector B) := by
    change mixedMoment B node2265 node2265Labels = _
    exact sound2265 B hB hF
  have h2662 : mixedVector B (Sum.inr 2662) = Sparse.eval nodeValue2662 (mixedVector B) := by
    change mixedMoment B node2662 node2662Labels = _
    exact sound2662 B hB hF
  have h2672 : mixedVector B (Sum.inr 2672) = Sparse.eval nodeValue2672 (mixedVector B) := by
    change mixedMoment B node2672 node2672Labels = _
    exact sound2672 B hB hF
  have h2673 : mixedVector B (Sum.inr 2673) = Sparse.eval nodeValue2673 (mixedVector B) := by
    change mixedMoment B node2673 node2673Labels = _
    exact sound2673 B hB hF
  have h2678 : mixedVector B (Sum.inr 2678) = Sparse.eval nodeValue2678 (mixedVector B) := by
    change mixedMoment B node2678 node2678Labels = _
    exact sound2678 B hB hF
  have h2694 : mixedVector B (Sum.inr 2694) = Sparse.eval nodeValue2694 (mixedVector B) := by
    change mixedMoment B node2694 node2694Labels = _
    exact sound2694 B hB hF
  have h2695 : mixedVector B (Sum.inr 2695) = Sparse.eval nodeValue2695 (mixedVector B) := by
    change mixedMoment B node2695 node2695Labels = _
    exact sound2695 B hB hF
  have h2698 : mixedVector B (Sum.inr 2698) = Sparse.eval nodeValue2698 (mixedVector B) := by
    change mixedMoment B node2698 node2698Labels = _
    exact sound2698 B hB hF
  have h2709 : mixedVector B (Sum.inr 2709) = Sparse.eval nodeValue2709 (mixedVector B) := by
    change mixedMoment B node2709 node2709Labels = _
    exact sound2709 B hB hF
  have h2710 : mixedVector B (Sum.inr 2710) = Sparse.eval nodeValue2710 (mixedVector B) := by
    change mixedMoment B node2710 node2710Labels = _
    exact sound2710 B hB hF
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  have h2723 : mixedVector B (Sum.inr 2723) = Sparse.eval nodeValue2723 (mixedVector B) := by
    change mixedMoment B node2723 node2723Labels = _
    exact sound2723 B hB hF
  have h2724 : mixedVector B (Sum.inr 2724) = Sparse.eval nodeValue2724 (mixedVector B) := by
    change mixedMoment B node2724 node2724Labels = _
    exact sound2724 B hB hF
  have h2731 : mixedVector B (Sum.inr 2731) = Sparse.eval nodeValue2731 (mixedVector B) := by
    change mixedMoment B node2731 node2731Labels = _
    exact sound2731 B hB hF
  have h2732 : mixedVector B (Sum.inr 2732) = Sparse.eval nodeValue2732 (mixedVector B) := by
    change mixedMoment B node2732 node2732Labels = _
    exact sound2732 B hB hF
  have h2742 : mixedVector B (Sum.inr 2742) = Sparse.eval nodeValue2742 (mixedVector B) := by
    change mixedMoment B node2742 node2742Labels = _
    exact sound2742 B hB hF
  have h2743 : mixedVector B (Sum.inr 2743) = Sparse.eval nodeValue2743 (mixedVector B) := by
    change mixedMoment B node2743 node2743Labels = _
    exact sound2743 B hB hF
  have h2767 : mixedVector B (Sum.inr 2767) = Sparse.eval nodeValue2767 (mixedVector B) := by
    change mixedMoment B node2767 node2767Labels = _
    exact sound2767 B hB hF
  have h2768 : mixedVector B (Sum.inr 2768) = Sparse.eval nodeValue2768 (mixedVector B) := by
    change mixedMoment B node2768 node2768Labels = _
    exact sound2768 B hB hF
  have h2787 : mixedVector B (Sum.inr 2787) = Sparse.eval nodeValue2787 (mixedVector B) := by
    change mixedMoment B node2787 node2787Labels = _
    exact sound2787 B hB hF
  have h3039 : mixedVector B (Sum.inr 3039) = Sparse.eval nodeValue3039 (mixedVector B) := by
    change mixedMoment B node3039 node3039Labels = _
    exact sound3039 B hB hF
  have h3065 : mixedVector B (Sum.inr 3065) = Sparse.eval nodeValue3065 (mixedVector B) := by
    change mixedMoment B node3065 node3065Labels = _
    exact sound3065 B hB hF
  have h3088 : mixedVector B (Sum.inr 3088) = Sparse.eval nodeValue3088 (mixedVector B) := by
    change mixedMoment B node3088 node3088Labels = _
    exact sound3088 B hB hF
  have h3089 : mixedVector B (Sum.inr 3089) = Sparse.eval nodeValue3089 (mixedVector B) := by
    change mixedMoment B node3089 node3089Labels = _
    exact sound3089 B hB hF
  have h3102 : mixedVector B (Sum.inr 3102) = Sparse.eval nodeValue3102 (mixedVector B) := by
    change mixedMoment B node3102 node3102Labels = _
    exact sound3102 B hB hF
  simpa only [sourceForm591, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2191, h2205, h2206, h2216, h2265, h2662, h2672, h2673, h2678, h2694, h2695, h2698, h2709, h2710, h2722, h2723, h2724, h2731, h2732, h2742, h2743, h2767, h2768, h2787, h3039, h3065, h3088, h3089, h3102, reducedSource500] using sourceEq591 B hB

theorem rowSound500 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row500 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck500, numericCheck500, reducedZero500 B hB hF, mul_zero]

theorem reducedZero501 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource501 (mixedVector B) = 0 := by
  have h2709 : mixedVector B (Sum.inr 2709) = Sparse.eval nodeValue2709 (mixedVector B) := by
    change mixedMoment B node2709 node2709Labels = _
    exact sound2709 B hB hF
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  have h2723 : mixedVector B (Sum.inr 2723) = Sparse.eval nodeValue2723 (mixedVector B) := by
    change mixedMoment B node2723 node2723Labels = _
    exact sound2723 B hB hF
  have h2731 : mixedVector B (Sum.inr 2731) = Sparse.eval nodeValue2731 (mixedVector B) := by
    change mixedMoment B node2731 node2731Labels = _
    exact sound2731 B hB hF
  have h2767 : mixedVector B (Sum.inr 2767) = Sparse.eval nodeValue2767 (mixedVector B) := by
    change mixedMoment B node2767 node2767Labels = _
    exact sound2767 B hB hF
  have h3029 : mixedVector B (Sum.inr 3029) = Sparse.eval nodeValue3029 (mixedVector B) := by
    change mixedMoment B node3029 node3029Labels = _
    exact sound3029 B hB hF
  have h3038 : mixedVector B (Sum.inr 3038) = Sparse.eval nodeValue3038 (mixedVector B) := by
    change mixedMoment B node3038 node3038Labels = _
    exact sound3038 B hB hF
  have h3039 : mixedVector B (Sum.inr 3039) = Sparse.eval nodeValue3039 (mixedVector B) := by
    change mixedMoment B node3039 node3039Labels = _
    exact sound3039 B hB hF
  have h3044 : mixedVector B (Sum.inr 3044) = Sparse.eval nodeValue3044 (mixedVector B) := by
    change mixedMoment B node3044 node3044Labels = _
    exact sound3044 B hB hF
  have h3064 : mixedVector B (Sum.inr 3064) = Sparse.eval nodeValue3064 (mixedVector B) := by
    change mixedMoment B node3064 node3064Labels = _
    exact sound3064 B hB hF
  have h3065 : mixedVector B (Sum.inr 3065) = Sparse.eval nodeValue3065 (mixedVector B) := by
    change mixedMoment B node3065 node3065Labels = _
    exact sound3065 B hB hF
  have h3068 : mixedVector B (Sum.inr 3068) = Sparse.eval nodeValue3068 (mixedVector B) := by
    change mixedMoment B node3068 node3068Labels = _
    exact sound3068 B hB hF
  have h3080 : mixedVector B (Sum.inr 3080) = Sparse.eval nodeValue3080 (mixedVector B) := by
    change mixedMoment B node3080 node3080Labels = _
    exact sound3080 B hB hF
  have h3081 : mixedVector B (Sum.inr 3081) = Sparse.eval nodeValue3081 (mixedVector B) := by
    change mixedMoment B node3081 node3081Labels = _
    exact sound3081 B hB hF
  have h3086 : mixedVector B (Sum.inr 3086) = Sparse.eval nodeValue3086 (mixedVector B) := by
    change mixedMoment B node3086 node3086Labels = _
    exact sound3086 B hB hF
  have h3088 : mixedVector B (Sum.inr 3088) = Sparse.eval nodeValue3088 (mixedVector B) := by
    change mixedMoment B node3088 node3088Labels = _
    exact sound3088 B hB hF
  have h3089 : mixedVector B (Sum.inr 3089) = Sparse.eval nodeValue3089 (mixedVector B) := by
    change mixedMoment B node3089 node3089Labels = _
    exact sound3089 B hB hF
  have h3092 : mixedVector B (Sum.inr 3092) = Sparse.eval nodeValue3092 (mixedVector B) := by
    change mixedMoment B node3092 node3092Labels = _
    exact sound3092 B hB hF
  have h3094 : mixedVector B (Sum.inr 3094) = Sparse.eval nodeValue3094 (mixedVector B) := by
    change mixedMoment B node3094 node3094Labels = _
    exact sound3094 B hB hF
  have h3101 : mixedVector B (Sum.inr 3101) = Sparse.eval nodeValue3101 (mixedVector B) := by
    change mixedMoment B node3101 node3101Labels = _
    exact sound3101 B hB hF
  have h3102 : mixedVector B (Sum.inr 3102) = Sparse.eval nodeValue3102 (mixedVector B) := by
    change mixedMoment B node3102 node3102Labels = _
    exact sound3102 B hB hF
  have h3110 : mixedVector B (Sum.inr 3110) = Sparse.eval nodeValue3110 (mixedVector B) := by
    change mixedMoment B node3110 node3110Labels = _
    exact sound3110 B hB hF
  have h3112 : mixedVector B (Sum.inr 3112) = Sparse.eval nodeValue3112 (mixedVector B) := by
    change mixedMoment B node3112 node3112Labels = _
    exact sound3112 B hB hF
  have h3123 : mixedVector B (Sum.inr 3123) = Sparse.eval nodeValue3123 (mixedVector B) := by
    change mixedMoment B node3123 node3123Labels = _
    exact sound3123 B hB hF
  have h3209 : mixedVector B (Sum.inr 3209) = Sparse.eval nodeValue3209 (mixedVector B) := by
    change mixedMoment B node3209 node3209Labels = _
    exact sound3209 B hB hF
  have h3210 : mixedVector B (Sum.inr 3210) = Sparse.eval nodeValue3210 (mixedVector B) := by
    change mixedMoment B node3210 node3210Labels = _
    exact sound3210 B hB hF
  have h3211 : mixedVector B (Sum.inr 3211) = Sparse.eval nodeValue3211 (mixedVector B) := by
    change mixedMoment B node3211 node3211Labels = _
    exact sound3211 B hB hF
  have h3214 : mixedVector B (Sum.inr 3214) = Sparse.eval nodeValue3214 (mixedVector B) := by
    change mixedMoment B node3214 node3214Labels = _
    exact sound3214 B hB hF
  have h3229 : mixedVector B (Sum.inr 3229) = Sparse.eval nodeValue3229 (mixedVector B) := by
    change mixedMoment B node3229 node3229Labels = _
    exact sound3229 B hB hF
  simpa only [sourceForm592, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2709, h2722, h2723, h2731, h2767, h3029, h3038, h3039, h3044, h3064, h3065, h3068, h3080, h3081, h3086, h3088, h3089, h3092, h3094, h3101, h3102, h3110, h3112, h3123, h3209, h3210, h3211, h3214, h3229, reducedSource501] using sourceEq592 B hB

theorem rowSound501 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row501 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck501, numericCheck501, reducedZero501 B hB hF, mul_zero]

theorem reducedZero502 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource502 (mixedVector B) = 0 := by
  have h2051 : mixedVector B (Sum.inr 2051) = Sparse.eval nodeValue2051 (mixedVector B) := by
    change mixedMoment B node2051 node2051Labels = _
    exact sound2051 B hB hF
  have h2053 : mixedVector B (Sum.inr 2053) = Sparse.eval nodeValue2053 (mixedVector B) := by
    change mixedMoment B node2053 node2053Labels = _
    exact sound2053 B hB hF
  have h2054 : mixedVector B (Sum.inr 2054) = Sparse.eval nodeValue2054 (mixedVector B) := by
    change mixedMoment B node2054 node2054Labels = _
    exact sound2054 B hB hF
  have h2058 : mixedVector B (Sum.inr 2058) = Sparse.eval nodeValue2058 (mixedVector B) := by
    change mixedMoment B node2058 node2058Labels = _
    exact sound2058 B hB hF
  have h2291 : mixedVector B (Sum.inr 2291) = Sparse.eval nodeValue2291 (mixedVector B) := by
    change mixedMoment B node2291 node2291Labels = _
    exact sound2291 B hB hF
  have h3544 : mixedVector B (Sum.inr 3544) = Sparse.eval nodeValue3544 (mixedVector B) := by
    change mixedMoment B node3544 node3544Labels = _
    exact sound3544 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm593, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2051, h2053, h2054, h2058, h2291, h3544, h4084, reducedSource502] using sourceEq593 B hB

theorem rowSound502 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row502 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck502, numericCheck502, reducedZero502 B hB hF, mul_zero]

theorem reducedZero503 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource503 (mixedVector B) = 0 := by
  have h4589 : mixedVector B (Sum.inr 4589) = Sparse.eval nodeValue4589 (mixedVector B) := by
    change mixedMoment B node4589 node4589Labels = _
    exact sound4589 B hB hF
  have h4591 : mixedVector B (Sum.inr 4591) = Sparse.eval nodeValue4591 (mixedVector B) := by
    change mixedMoment B node4591 node4591Labels = _
    exact sound4591 B hB hF
  have h4592 : mixedVector B (Sum.inr 4592) = Sparse.eval nodeValue4592 (mixedVector B) := by
    change mixedMoment B node4592 node4592Labels = _
    exact sound4592 B hB hF
  have h4602 : mixedVector B (Sum.inr 4602) = Sparse.eval nodeValue4602 (mixedVector B) := by
    change mixedMoment B node4602 node4602Labels = _
    exact sound4602 B hB hF
  have h4607 : mixedVector B (Sum.inr 4607) = Sparse.eval nodeValue4607 (mixedVector B) := by
    change mixedMoment B node4607 node4607Labels = _
    exact sound4607 B hB hF
  have h5072 : mixedVector B (Sum.inr 5072) = Sparse.eval nodeValue5072 (mixedVector B) := by
    change mixedMoment B node5072 node5072Labels = _
    exact sound5072 B hB hF
  have h5075 : mixedVector B (Sum.inr 5075) = Sparse.eval nodeValue5075 (mixedVector B) := by
    change mixedMoment B node5075 node5075Labels = _
    exact sound5075 B hB hF
  have h5080 : mixedVector B (Sum.inr 5080) = Sparse.eval nodeValue5080 (mixedVector B) := by
    change mixedMoment B node5080 node5080Labels = _
    exact sound5080 B hB hF
  have h5101 : mixedVector B (Sum.inr 5101) = Sparse.eval nodeValue5101 (mixedVector B) := by
    change mixedMoment B node5101 node5101Labels = _
    exact sound5101 B hB hF
  have h5127 : mixedVector B (Sum.inr 5127) = Sparse.eval nodeValue5127 (mixedVector B) := by
    change mixedMoment B node5127 node5127Labels = _
    exact sound5127 B hB hF
  have h5129 : mixedVector B (Sum.inr 5129) = Sparse.eval nodeValue5129 (mixedVector B) := by
    change mixedMoment B node5129 node5129Labels = _
    exact sound5129 B hB hF
  have h5134 : mixedVector B (Sum.inr 5134) = Sparse.eval nodeValue5134 (mixedVector B) := by
    change mixedMoment B node5134 node5134Labels = _
    exact sound5134 B hB hF
  have h5144 : mixedVector B (Sum.inr 5144) = Sparse.eval nodeValue5144 (mixedVector B) := by
    change mixedMoment B node5144 node5144Labels = _
    exact sound5144 B hB hF
  have h5147 : mixedVector B (Sum.inr 5147) = Sparse.eval nodeValue5147 (mixedVector B) := by
    change mixedMoment B node5147 node5147Labels = _
    exact sound5147 B hB hF
  have h5184 : mixedVector B (Sum.inr 5184) = Sparse.eval nodeValue5184 (mixedVector B) := by
    change mixedMoment B node5184 node5184Labels = _
    exact sound5184 B hB hF
  have h5188 : mixedVector B (Sum.inr 5188) = Sparse.eval nodeValue5188 (mixedVector B) := by
    change mixedMoment B node5188 node5188Labels = _
    exact sound5188 B hB hF
  have h5198 : mixedVector B (Sum.inr 5198) = Sparse.eval nodeValue5198 (mixedVector B) := by
    change mixedMoment B node5198 node5198Labels = _
    exact sound5198 B hB hF
  have h5256 : mixedVector B (Sum.inr 5256) = Sparse.eval nodeValue5256 (mixedVector B) := by
    change mixedMoment B node5256 node5256Labels = _
    exact sound5256 B hB hF
  have h5258 : mixedVector B (Sum.inr 5258) = Sparse.eval nodeValue5258 (mixedVector B) := by
    change mixedMoment B node5258 node5258Labels = _
    exact sound5258 B hB hF
  have h5260 : mixedVector B (Sum.inr 5260) = Sparse.eval nodeValue5260 (mixedVector B) := by
    change mixedMoment B node5260 node5260Labels = _
    exact sound5260 B hB hF
  have h5261 : mixedVector B (Sum.inr 5261) = Sparse.eval nodeValue5261 (mixedVector B) := by
    change mixedMoment B node5261 node5261Labels = _
    exact sound5261 B hB hF
  have h5271 : mixedVector B (Sum.inr 5271) = Sparse.eval nodeValue5271 (mixedVector B) := by
    change mixedMoment B node5271 node5271Labels = _
    exact sound5271 B hB hF
  have h5274 : mixedVector B (Sum.inr 5274) = Sparse.eval nodeValue5274 (mixedVector B) := by
    change mixedMoment B node5274 node5274Labels = _
    exact sound5274 B hB hF
  have h5289 : mixedVector B (Sum.inr 5289) = Sparse.eval nodeValue5289 (mixedVector B) := by
    change mixedMoment B node5289 node5289Labels = _
    exact sound5289 B hB hF
  have h5291 : mixedVector B (Sum.inr 5291) = Sparse.eval nodeValue5291 (mixedVector B) := by
    change mixedMoment B node5291 node5291Labels = _
    exact sound5291 B hB hF
  have h5409 : mixedVector B (Sum.inr 5409) = Sparse.eval nodeValue5409 (mixedVector B) := by
    change mixedMoment B node5409 node5409Labels = _
    exact sound5409 B hB hF
  have h5423 : mixedVector B (Sum.inr 5423) = Sparse.eval nodeValue5423 (mixedVector B) := by
    change mixedMoment B node5423 node5423Labels = _
    exact sound5423 B hB hF
  have h5432 : mixedVector B (Sum.inr 5432) = Sparse.eval nodeValue5432 (mixedVector B) := by
    change mixedMoment B node5432 node5432Labels = _
    exact sound5432 B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434 B hB hF
  have h5441 : mixedVector B (Sum.inr 5441) = Sparse.eval nodeValue5441 (mixedVector B) := by
    change mixedMoment B node5441 node5441Labels = _
    exact sound5441 B hB hF
  simpa only [sourceForm594, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4589, h4591, h4592, h4602, h4607, h5072, h5075, h5080, h5101, h5127, h5129, h5134, h5144, h5147, h5184, h5188, h5198, h5256, h5258, h5260, h5261, h5271, h5274, h5289, h5291, h5409, h5423, h5432, h5434, h5441, reducedSource503] using sourceEq594 B hB

theorem rowSound503 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row503 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck503, numericCheck503, reducedZero503 B hB hF, mul_zero]

theorem reducedZero504 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource504 (mixedVector B) = 0 := by
  have h1216 : mixedVector B (Sum.inr 1216) = Sparse.eval nodeValue1216 (mixedVector B) := by
    change mixedMoment B node1216 node1216Labels = _
    exact sound1216 B hB hF
  have h1217 : mixedVector B (Sum.inr 1217) = Sparse.eval nodeValue1217 (mixedVector B) := by
    change mixedMoment B node1217 node1217Labels = _
    exact sound1217 B hB hF
  have h1219 : mixedVector B (Sum.inr 1219) = Sparse.eval nodeValue1219 (mixedVector B) := by
    change mixedMoment B node1219 node1219Labels = _
    exact sound1219 B hB hF
  have h1241 : mixedVector B (Sum.inr 1241) = Sparse.eval nodeValue1241 (mixedVector B) := by
    change mixedMoment B node1241 node1241Labels = _
    exact sound1241 B hB hF
  have h1267 : mixedVector B (Sum.inr 1267) = Sparse.eval nodeValue1267 (mixedVector B) := by
    change mixedMoment B node1267 node1267Labels = _
    exact sound1267 B hB hF
  have h2864 : mixedVector B (Sum.inr 2864) = Sparse.eval nodeValue2864 (mixedVector B) := by
    change mixedMoment B node2864 node2864Labels = _
    exact sound2864 B hB hF
  have h2865 : mixedVector B (Sum.inr 2865) = Sparse.eval nodeValue2865 (mixedVector B) := by
    change mixedMoment B node2865 node2865Labels = _
    exact sound2865 B hB hF
  have h2867 : mixedVector B (Sum.inr 2867) = Sparse.eval nodeValue2867 (mixedVector B) := by
    change mixedMoment B node2867 node2867Labels = _
    exact sound2867 B hB hF
  have h2885 : mixedVector B (Sum.inr 2885) = Sparse.eval nodeValue2885 (mixedVector B) := by
    change mixedMoment B node2885 node2885Labels = _
    exact sound2885 B hB hF
  have h2914 : mixedVector B (Sum.inr 2914) = Sparse.eval nodeValue2914 (mixedVector B) := by
    change mixedMoment B node2914 node2914Labels = _
    exact sound2914 B hB hF
  have h2916 : mixedVector B (Sum.inr 2916) = Sparse.eval nodeValue2916 (mixedVector B) := by
    change mixedMoment B node2916 node2916Labels = _
    exact sound2916 B hB hF
  have h2928 : mixedVector B (Sum.inr 2928) = Sparse.eval nodeValue2928 (mixedVector B) := by
    change mixedMoment B node2928 node2928Labels = _
    exact sound2928 B hB hF
  have h2937 : mixedVector B (Sum.inr 2937) = Sparse.eval nodeValue2937 (mixedVector B) := by
    change mixedMoment B node2937 node2937Labels = _
    exact sound2937 B hB hF
  have h2939 : mixedVector B (Sum.inr 2939) = Sparse.eval nodeValue2939 (mixedVector B) := by
    change mixedMoment B node2939 node2939Labels = _
    exact sound2939 B hB hF
  have h2988 : mixedVector B (Sum.inr 2988) = Sparse.eval nodeValue2988 (mixedVector B) := by
    change mixedMoment B node2988 node2988Labels = _
    exact sound2988 B hB hF
  have h2990 : mixedVector B (Sum.inr 2990) = Sparse.eval nodeValue2990 (mixedVector B) := by
    change mixedMoment B node2990 node2990Labels = _
    exact sound2990 B hB hF
  have h3001 : mixedVector B (Sum.inr 3001) = Sparse.eval nodeValue3001 (mixedVector B) := by
    change mixedMoment B node3001 node3001Labels = _
    exact sound3001 B hB hF
  have h3085 : mixedVector B (Sum.inr 3085) = Sparse.eval nodeValue3085 (mixedVector B) := by
    change mixedMoment B node3085 node3085Labels = _
    exact sound3085 B hB hF
  have h3086 : mixedVector B (Sum.inr 3086) = Sparse.eval nodeValue3086 (mixedVector B) := by
    change mixedMoment B node3086 node3086Labels = _
    exact sound3086 B hB hF
  have h3089 : mixedVector B (Sum.inr 3089) = Sparse.eval nodeValue3089 (mixedVector B) := by
    change mixedMoment B node3089 node3089Labels = _
    exact sound3089 B hB hF
  have h3090 : mixedVector B (Sum.inr 3090) = Sparse.eval nodeValue3090 (mixedVector B) := by
    change mixedMoment B node3090 node3090Labels = _
    exact sound3090 B hB hF
  have h3097 : mixedVector B (Sum.inr 3097) = Sparse.eval nodeValue3097 (mixedVector B) := by
    change mixedMoment B node3097 node3097Labels = _
    exact sound3097 B hB hF
  have h3103 : mixedVector B (Sum.inr 3103) = Sparse.eval nodeValue3103 (mixedVector B) := by
    change mixedMoment B node3103 node3103Labels = _
    exact sound3103 B hB hF
  have h3109 : mixedVector B (Sum.inr 3109) = Sparse.eval nodeValue3109 (mixedVector B) := by
    change mixedMoment B node3109 node3109Labels = _
    exact sound3109 B hB hF
  have h3112 : mixedVector B (Sum.inr 3112) = Sparse.eval nodeValue3112 (mixedVector B) := by
    change mixedMoment B node3112 node3112Labels = _
    exact sound3112 B hB hF
  have h3982 : mixedVector B (Sum.inr 3982) = Sparse.eval nodeValue3982 (mixedVector B) := by
    change mixedMoment B node3982 node3982Labels = _
    exact sound3982 B hB hF
  have h4027 : mixedVector B (Sum.inr 4027) = Sparse.eval nodeValue4027 (mixedVector B) := by
    change mixedMoment B node4027 node4027Labels = _
    exact sound4027 B hB hF
  have h4032 : mixedVector B (Sum.inr 4032) = Sparse.eval nodeValue4032 (mixedVector B) := by
    change mixedMoment B node4032 node4032Labels = _
    exact sound4032 B hB hF
  have h4035 : mixedVector B (Sum.inr 4035) = Sparse.eval nodeValue4035 (mixedVector B) := by
    change mixedMoment B node4035 node4035Labels = _
    exact sound4035 B hB hF
  have h4037 : mixedVector B (Sum.inr 4037) = Sparse.eval nodeValue4037 (mixedVector B) := by
    change mixedMoment B node4037 node4037Labels = _
    exact sound4037 B hB hF
  simpa only [sourceForm595, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1216, h1217, h1219, h1241, h1267, h2864, h2865, h2867, h2885, h2914, h2916, h2928, h2937, h2939, h2988, h2990, h3001, h3085, h3086, h3089, h3090, h3097, h3103, h3109, h3112, h3982, h4027, h4032, h4035, h4037, reducedSource504] using sourceEq595 B hB

theorem rowSound504 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row504 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck504, numericCheck504, reducedZero504 B hB hF, mul_zero]

theorem reducedZero505 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource505 (mixedVector B) = 0 := by
  have h3288 : mixedVector B (Sum.inr 3288) = Sparse.eval nodeValue3288 (mixedVector B) := by
    change mixedMoment B node3288 node3288Labels = _
    exact sound3288 B hB hF
  have h3291 : mixedVector B (Sum.inr 3291) = Sparse.eval nodeValue3291 (mixedVector B) := by
    change mixedMoment B node3291 node3291Labels = _
    exact sound3291 B hB hF
  have h3293 : mixedVector B (Sum.inr 3293) = Sparse.eval nodeValue3293 (mixedVector B) := by
    change mixedMoment B node3293 node3293Labels = _
    exact sound3293 B hB hF
  have h3295 : mixedVector B (Sum.inr 3295) = Sparse.eval nodeValue3295 (mixedVector B) := by
    change mixedMoment B node3295 node3295Labels = _
    exact sound3295 B hB hF
  have h3296 : mixedVector B (Sum.inr 3296) = Sparse.eval nodeValue3296 (mixedVector B) := by
    change mixedMoment B node3296 node3296Labels = _
    exact sound3296 B hB hF
  have h3459 : mixedVector B (Sum.inr 3459) = Sparse.eval nodeValue3459 (mixedVector B) := by
    change mixedMoment B node3459 node3459Labels = _
    exact sound3459 B hB hF
  have h3468 : mixedVector B (Sum.inr 3468) = Sparse.eval nodeValue3468 (mixedVector B) := by
    change mixedMoment B node3468 node3468Labels = _
    exact sound3468 B hB hF
  have h3470 : mixedVector B (Sum.inr 3470) = Sparse.eval nodeValue3470 (mixedVector B) := by
    change mixedMoment B node3470 node3470Labels = _
    exact sound3470 B hB hF
  have h3478 : mixedVector B (Sum.inr 3478) = Sparse.eval nodeValue3478 (mixedVector B) := by
    change mixedMoment B node3478 node3478Labels = _
    exact sound3478 B hB hF
  have h3513 : mixedVector B (Sum.inr 3513) = Sparse.eval nodeValue3513 (mixedVector B) := by
    change mixedMoment B node3513 node3513Labels = _
    exact sound3513 B hB hF
  have h3514 : mixedVector B (Sum.inr 3514) = Sparse.eval nodeValue3514 (mixedVector B) := by
    change mixedMoment B node3514 node3514Labels = _
    exact sound3514 B hB hF
  have h3516 : mixedVector B (Sum.inr 3516) = Sparse.eval nodeValue3516 (mixedVector B) := by
    change mixedMoment B node3516 node3516Labels = _
    exact sound3516 B hB hF
  have h3524 : mixedVector B (Sum.inr 3524) = Sparse.eval nodeValue3524 (mixedVector B) := by
    change mixedMoment B node3524 node3524Labels = _
    exact sound3524 B hB hF
  have h3525 : mixedVector B (Sum.inr 3525) = Sparse.eval nodeValue3525 (mixedVector B) := by
    change mixedMoment B node3525 node3525Labels = _
    exact sound3525 B hB hF
  have h3530 : mixedVector B (Sum.inr 3530) = Sparse.eval nodeValue3530 (mixedVector B) := by
    change mixedMoment B node3530 node3530Labels = _
    exact sound3530 B hB hF
  have h3533 : mixedVector B (Sum.inr 3533) = Sparse.eval nodeValue3533 (mixedVector B) := by
    change mixedMoment B node3533 node3533Labels = _
    exact sound3533 B hB hF
  have h3534 : mixedVector B (Sum.inr 3534) = Sparse.eval nodeValue3534 (mixedVector B) := by
    change mixedMoment B node3534 node3534Labels = _
    exact sound3534 B hB hF
  have h3538 : mixedVector B (Sum.inr 3538) = Sparse.eval nodeValue3538 (mixedVector B) := by
    change mixedMoment B node3538 node3538Labels = _
    exact sound3538 B hB hF
  have h3540 : mixedVector B (Sum.inr 3540) = Sparse.eval nodeValue3540 (mixedVector B) := by
    change mixedMoment B node3540 node3540Labels = _
    exact sound3540 B hB hF
  have h3545 : mixedVector B (Sum.inr 3545) = Sparse.eval nodeValue3545 (mixedVector B) := by
    change mixedMoment B node3545 node3545Labels = _
    exact sound3545 B hB hF
  have h3547 : mixedVector B (Sum.inr 3547) = Sparse.eval nodeValue3547 (mixedVector B) := by
    change mixedMoment B node3547 node3547Labels = _
    exact sound3547 B hB hF
  have h3557 : mixedVector B (Sum.inr 3557) = Sparse.eval nodeValue3557 (mixedVector B) := by
    change mixedMoment B node3557 node3557Labels = _
    exact sound3557 B hB hF
  have h3570 : mixedVector B (Sum.inr 3570) = Sparse.eval nodeValue3570 (mixedVector B) := by
    change mixedMoment B node3570 node3570Labels = _
    exact sound3570 B hB hF
  have h3572 : mixedVector B (Sum.inr 3572) = Sparse.eval nodeValue3572 (mixedVector B) := by
    change mixedMoment B node3572 node3572Labels = _
    exact sound3572 B hB hF
  have h3582 : mixedVector B (Sum.inr 3582) = Sparse.eval nodeValue3582 (mixedVector B) := by
    change mixedMoment B node3582 node3582Labels = _
    exact sound3582 B hB hF
  have h3807 : mixedVector B (Sum.inr 3807) = Sparse.eval nodeValue3807 (mixedVector B) := by
    change mixedMoment B node3807 node3807Labels = _
    exact sound3807 B hB hF
  have h3837 : mixedVector B (Sum.inr 3837) = Sparse.eval nodeValue3837 (mixedVector B) := by
    change mixedMoment B node3837 node3837Labels = _
    exact sound3837 B hB hF
  have h3850 : mixedVector B (Sum.inr 3850) = Sparse.eval nodeValue3850 (mixedVector B) := by
    change mixedMoment B node3850 node3850Labels = _
    exact sound3850 B hB hF
  have h3852 : mixedVector B (Sum.inr 3852) = Sparse.eval nodeValue3852 (mixedVector B) := by
    change mixedMoment B node3852 node3852Labels = _
    exact sound3852 B hB hF
  have h3860 : mixedVector B (Sum.inr 3860) = Sparse.eval nodeValue3860 (mixedVector B) := by
    change mixedMoment B node3860 node3860Labels = _
    exact sound3860 B hB hF
  simpa only [sourceForm596, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3288, h3291, h3293, h3295, h3296, h3459, h3468, h3470, h3478, h3513, h3514, h3516, h3524, h3525, h3530, h3533, h3534, h3538, h3540, h3545, h3547, h3557, h3570, h3572, h3582, h3807, h3837, h3850, h3852, h3860, reducedSource505] using sourceEq596 B hB

theorem rowSound505 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row505 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck505, numericCheck505, reducedZero505 B hB hF, mul_zero]

theorem reducedZero506 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource506 (mixedVector B) = 0 := by
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  have h3807 : mixedVector B (Sum.inr 3807) = Sparse.eval nodeValue3807 (mixedVector B) := by
    change mixedMoment B node3807 node3807Labels = _
    exact sound3807 B hB hF
  have h3837 : mixedVector B (Sum.inr 3837) = Sparse.eval nodeValue3837 (mixedVector B) := by
    change mixedMoment B node3837 node3837Labels = _
    exact sound3837 B hB hF
  have h3850 : mixedVector B (Sum.inr 3850) = Sparse.eval nodeValue3850 (mixedVector B) := by
    change mixedMoment B node3850 node3850Labels = _
    exact sound3850 B hB hF
  have h3903 : mixedVector B (Sum.inr 3903) = Sparse.eval nodeValue3903 (mixedVector B) := by
    change mixedMoment B node3903 node3903Labels = _
    exact sound3903 B hB hF
  have h3905 : mixedVector B (Sum.inr 3905) = Sparse.eval nodeValue3905 (mixedVector B) := by
    change mixedMoment B node3905 node3905Labels = _
    exact sound3905 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm597, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2722, h3807, h3837, h3850, h3903, h3905, h4092, reducedSource506] using sourceEq597 B hB

theorem rowSound506 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row506 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck506, numericCheck506, reducedZero506 B hB hF, mul_zero]

theorem reducedZero507 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource507 (mixedVector B) = 0 := by
  have h1212 : mixedVector B (Sum.inr 1212) = Sparse.eval nodeValue1212 (mixedVector B) := by
    change mixedMoment B node1212 node1212Labels = _
    exact sound1212 B hB hF
  have h1215 : mixedVector B (Sum.inr 1215) = Sparse.eval nodeValue1215 (mixedVector B) := by
    change mixedMoment B node1215 node1215Labels = _
    exact sound1215 B hB hF
  have h1219 : mixedVector B (Sum.inr 1219) = Sparse.eval nodeValue1219 (mixedVector B) := by
    change mixedMoment B node1219 node1219Labels = _
    exact sound1219 B hB hF
  have h1236 : mixedVector B (Sum.inr 1236) = Sparse.eval nodeValue1236 (mixedVector B) := by
    change mixedMoment B node1236 node1236Labels = _
    exact sound1236 B hB hF
  have h1261 : mixedVector B (Sum.inr 1261) = Sparse.eval nodeValue1261 (mixedVector B) := by
    change mixedMoment B node1261 node1261Labels = _
    exact sound1261 B hB hF
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm598, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1212, h1215, h1219, h1236, h1261, h2722, h4092, reducedSource507] using sourceEq598 B hB

theorem rowSound507 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row507 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck507, numericCheck507, reducedZero507 B hB hF, mul_zero]

theorem reducedZero508 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource508 (mixedVector B) = 0 := by
  have h1236 : mixedVector B (Sum.inr 1236) = Sparse.eval nodeValue1236 (mixedVector B) := by
    change mixedMoment B node1236 node1236Labels = _
    exact sound1236 B hB hF
  have h2511 : mixedVector B (Sum.inr 2511) = Sparse.eval nodeValue2511 (mixedVector B) := by
    change mixedMoment B node2511 node2511Labels = _
    exact sound2511 B hB hF
  have h2553 : mixedVector B (Sum.inr 2553) = Sparse.eval nodeValue2553 (mixedVector B) := by
    change mixedMoment B node2553 node2553Labels = _
    exact sound2553 B hB hF
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  have h2739 : mixedVector B (Sum.inr 2739) = Sparse.eval nodeValue2739 (mixedVector B) := by
    change mixedMoment B node2739 node2739Labels = _
    exact sound2739 B hB hF
  have h2742 : mixedVector B (Sum.inr 2742) = Sparse.eval nodeValue2742 (mixedVector B) := by
    change mixedMoment B node2742 node2742Labels = _
    exact sound2742 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm599, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1236, h2511, h2553, h2722, h2739, h2742, h4092, reducedSource508] using sourceEq599 B hB

theorem rowSound508 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row508 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck508, numericCheck508, reducedZero508 B hB hF, mul_zero]

theorem reducedZero509 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource509 (mixedVector B) = 0 := by
  have h2569 : mixedVector B (Sum.inr 2569) = Sparse.eval nodeValue2569 (mixedVector B) := by
    change mixedMoment B node2569 node2569Labels = _
    exact sound2569 B hB hF
  have h2614 : mixedVector B (Sum.inr 2614) = Sparse.eval nodeValue2614 (mixedVector B) := by
    change mixedMoment B node2614 node2614Labels = _
    exact sound2614 B hB hF
  have h2620 : mixedVector B (Sum.inr 2620) = Sparse.eval nodeValue2620 (mixedVector B) := by
    change mixedMoment B node2620 node2620Labels = _
    exact sound2620 B hB hF
  have h2632 : mixedVector B (Sum.inr 2632) = Sparse.eval nodeValue2632 (mixedVector B) := by
    change mixedMoment B node2632 node2632Labels = _
    exact sound2632 B hB hF
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  have h3850 : mixedVector B (Sum.inr 3850) = Sparse.eval nodeValue3850 (mixedVector B) := by
    change mixedMoment B node3850 node3850Labels = _
    exact sound3850 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm600, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2569, h2614, h2620, h2632, h2722, h3850, h4092, reducedSource509] using sourceEq600 B hB

theorem rowSound509 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row509 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck509, numericCheck509, reducedZero509 B hB hF, mul_zero]

theorem reducedZero510 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource510 (mixedVector B) = 0 := by
  have h1212 : mixedVector B (Sum.inr 1212) = Sparse.eval nodeValue1212 (mixedVector B) := by
    change mixedMoment B node1212 node1212Labels = _
    exact sound1212 B hB hF
  have h2479 : mixedVector B (Sum.inr 2479) = Sparse.eval nodeValue2479 (mixedVector B) := by
    change mixedMoment B node2479 node2479Labels = _
    exact sound2479 B hB hF
  have h2614 : mixedVector B (Sum.inr 2614) = Sparse.eval nodeValue2614 (mixedVector B) := by
    change mixedMoment B node2614 node2614Labels = _
    exact sound2614 B hB hF
  have h2720 : mixedVector B (Sum.inr 2720) = Sparse.eval nodeValue2720 (mixedVector B) := by
    change mixedMoment B node2720 node2720Labels = _
    exact sound2720 B hB hF
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm601, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1212, h2479, h2614, h2720, h2722, h4092, reducedSource510] using sourceEq601 B hB

theorem rowSound510 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row510 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck510, numericCheck510, reducedZero510 B hB hF, mul_zero]

theorem reducedZero511 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource511 (mixedVector B) = 0 := by
  have h2542 : mixedVector B (Sum.inr 2542) = Sparse.eval nodeValue2542 (mixedVector B) := by
    change mixedMoment B node2542 node2542Labels = _
    exact sound2542 B hB hF
  have h2545 : mixedVector B (Sum.inr 2545) = Sparse.eval nodeValue2545 (mixedVector B) := by
    change mixedMoment B node2545 node2545Labels = _
    exact sound2545 B hB hF
  have h2553 : mixedVector B (Sum.inr 2553) = Sparse.eval nodeValue2553 (mixedVector B) := by
    change mixedMoment B node2553 node2553Labels = _
    exact sound2553 B hB hF
  have h2566 : mixedVector B (Sum.inr 2566) = Sparse.eval nodeValue2566 (mixedVector B) := by
    change mixedMoment B node2566 node2566Labels = _
    exact sound2566 B hB hF
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  have h3837 : mixedVector B (Sum.inr 3837) = Sparse.eval nodeValue3837 (mixedVector B) := by
    change mixedMoment B node3837 node3837Labels = _
    exact sound3837 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm602, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2542, h2545, h2553, h2566, h2722, h3837, h4092, reducedSource511] using sourceEq602 B hB

theorem rowSound511 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row511 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck511, numericCheck511, reducedZero511 B hB hF, mul_zero]

theorem sourceRowsAt496 : MixedData.sourceRows (496 : Fin 2425) =
    MixedData.row496 := by decide +kernel

theorem sourceRowsAt497 : MixedData.sourceRows (497 : Fin 2425) =
    MixedData.row497 := by decide +kernel

theorem sourceRowsAt498 : MixedData.sourceRows (498 : Fin 2425) =
    MixedData.row498 := by decide +kernel

theorem sourceRowsAt499 : MixedData.sourceRows (499 : Fin 2425) =
    MixedData.row499 := by decide +kernel

theorem sourceRowsAt500 : MixedData.sourceRows (500 : Fin 2425) =
    MixedData.row500 := by decide +kernel

theorem sourceRowsAt501 : MixedData.sourceRows (501 : Fin 2425) =
    MixedData.row501 := by decide +kernel

theorem sourceRowsAt502 : MixedData.sourceRows (502 : Fin 2425) =
    MixedData.row502 := by decide +kernel

theorem sourceRowsAt503 : MixedData.sourceRows (503 : Fin 2425) =
    MixedData.row503 := by decide +kernel

theorem sourceRowsAt504 : MixedData.sourceRows (504 : Fin 2425) =
    MixedData.row504 := by decide +kernel

theorem sourceRowsAt505 : MixedData.sourceRows (505 : Fin 2425) =
    MixedData.row505 := by decide +kernel

theorem sourceRowsAt506 : MixedData.sourceRows (506 : Fin 2425) =
    MixedData.row506 := by decide +kernel

theorem sourceRowsAt507 : MixedData.sourceRows (507 : Fin 2425) =
    MixedData.row507 := by decide +kernel

theorem sourceRowsAt508 : MixedData.sourceRows (508 : Fin 2425) =
    MixedData.row508 := by decide +kernel

theorem sourceRowsAt509 : MixedData.sourceRows (509 : Fin 2425) =
    MixedData.row509 := by decide +kernel

theorem sourceRowsAt510 : MixedData.sourceRows (510 : Fin 2425) =
    MixedData.row510 := by decide +kernel

theorem sourceRowsAt511 : MixedData.sourceRows (511 : Fin 2425) =
    MixedData.row511 := by decide +kernel

theorem chunkSound31 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 31) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 496 ∨ k.val = 497 ∨ k.val = 498 ∨ k.val = 499 ∨ k.val = 500 ∨ k.val = 501 ∨ k.val = 502 ∨ k.val = 503 ∨ k.val = 504 ∨ k.val = 505 ∨ k.val = 506 ∨ k.val = 507 ∨ k.val = 508 ∨ k.val = 509 ∨ k.val = 510 ∨ k.val = 511 := by omega
  rcases heq with h496 | h497 | h498 | h499 | h500 | h501 | h502 | h503 | h504 | h505 | h506 | h507 | h508 | h509 | h510 | h511
  · have he : k = (496 : Fin 2425) := Fin.ext h496
    subst k
    rw [sourceRowsAt496]
    exact rowSound496 B hB hF
  · have he : k = (497 : Fin 2425) := Fin.ext h497
    subst k
    rw [sourceRowsAt497]
    exact rowSound497 B hB hF
  · have he : k = (498 : Fin 2425) := Fin.ext h498
    subst k
    rw [sourceRowsAt498]
    exact rowSound498 B hB hF
  · have he : k = (499 : Fin 2425) := Fin.ext h499
    subst k
    rw [sourceRowsAt499]
    exact rowSound499 B hB hF
  · have he : k = (500 : Fin 2425) := Fin.ext h500
    subst k
    rw [sourceRowsAt500]
    exact rowSound500 B hB hF
  · have he : k = (501 : Fin 2425) := Fin.ext h501
    subst k
    rw [sourceRowsAt501]
    exact rowSound501 B hB hF
  · have he : k = (502 : Fin 2425) := Fin.ext h502
    subst k
    rw [sourceRowsAt502]
    exact rowSound502 B hB hF
  · have he : k = (503 : Fin 2425) := Fin.ext h503
    subst k
    rw [sourceRowsAt503]
    exact rowSound503 B hB hF
  · have he : k = (504 : Fin 2425) := Fin.ext h504
    subst k
    rw [sourceRowsAt504]
    exact rowSound504 B hB hF
  · have he : k = (505 : Fin 2425) := Fin.ext h505
    subst k
    rw [sourceRowsAt505]
    exact rowSound505 B hB hF
  · have he : k = (506 : Fin 2425) := Fin.ext h506
    subst k
    rw [sourceRowsAt506]
    exact rowSound506 B hB hF
  · have he : k = (507 : Fin 2425) := Fin.ext h507
    subst k
    rw [sourceRowsAt507]
    exact rowSound507 B hB hF
  · have he : k = (508 : Fin 2425) := Fin.ext h508
    subst k
    rw [sourceRowsAt508]
    exact rowSound508 B hB hF
  · have he : k = (509 : Fin 2425) := Fin.ext h509
    subst k
    rw [sourceRowsAt509]
    exact rowSound509 B hB hF
  · have he : k = (510 : Fin 2425) := Fin.ext h510
    subst k
    rw [sourceRowsAt510]
    exact rowSound510 B hB hF
  · have he : k = (511 : Fin 2425) := Fin.ext h511
    subst k
    rw [sourceRowsAt511]
    exact rowSound511 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
