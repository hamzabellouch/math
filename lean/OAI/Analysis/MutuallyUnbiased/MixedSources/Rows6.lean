import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic6
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources3
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources4

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero96 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource96 (mixedVector B) = 0 := by
  have h2290 : mixedVector B (Sum.inr 2290) = Sparse.eval nodeValue2290 (mixedVector B) := by
    change mixedMoment B node2290 node2290Labels = _
    exact sound2290 B hB hF
  have h2292 : mixedVector B (Sum.inr 2292) = Sparse.eval nodeValue2292 (mixedVector B) := by
    change mixedMoment B node2292 node2292Labels = _
    exact sound2292 B hB hF
  have h2294 : mixedVector B (Sum.inr 2294) = Sparse.eval nodeValue2294 (mixedVector B) := by
    change mixedMoment B node2294 node2294Labels = _
    exact sound2294 B hB hF
  have h3634 : mixedVector B (Sum.inr 3634) = Sparse.eval nodeValue3634 (mixedVector B) := by
    change mixedMoment B node3634 node3634Labels = _
    exact sound3634 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm116, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2290, h2292, h2294, h3634, h4085, reducedSource96] using sourceEq116 B hB

theorem rowSound96 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row96 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck96, numericCheck96, reducedZero96 B hB hF, mul_zero]

theorem reducedZero97 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource97 (mixedVector B) = 0 := by
  have h4276 : mixedVector B (Sum.inr 4276) = Sparse.eval nodeValue4276 (mixedVector B) := by
    change mixedMoment B node4276 node4276Labels = _
    exact sound4276 B hB hF
  have h4280 : mixedVector B (Sum.inr 4280) = Sparse.eval nodeValue4280 (mixedVector B) := by
    change mixedMoment B node4280 node4280Labels = _
    exact sound4280 B hB hF
  have h4285 : mixedVector B (Sum.inr 4285) = Sparse.eval nodeValue4285 (mixedVector B) := by
    change mixedMoment B node4285 node4285Labels = _
    exact sound4285 B hB hF
  have h4572 : mixedVector B (Sum.inr 4572) = Sparse.eval nodeValue4572 (mixedVector B) := by
    change mixedMoment B node4572 node4572Labels = _
    exact sound4572 B hB hF
  have h4621 : mixedVector B (Sum.inr 4621) = Sparse.eval nodeValue4621 (mixedVector B) := by
    change mixedMoment B node4621 node4621Labels = _
    exact sound4621 B hB hF
  have h4747 : mixedVector B (Sum.inr 4747) = Sparse.eval nodeValue4747 (mixedVector B) := by
    change mixedMoment B node4747 node4747Labels = _
    exact sound4747 B hB hF
  have h4754 : mixedVector B (Sum.inr 4754) = Sparse.eval nodeValue4754 (mixedVector B) := by
    change mixedMoment B node4754 node4754Labels = _
    exact sound4754 B hB hF
  have h4871 : mixedVector B (Sum.inr 4871) = Sparse.eval nodeValue4871 (mixedVector B) := by
    change mixedMoment B node4871 node4871Labels = _
    exact sound4871 B hB hF
  have h4898 : mixedVector B (Sum.inr 4898) = Sparse.eval nodeValue4898 (mixedVector B) := by
    change mixedMoment B node4898 node4898Labels = _
    exact sound4898 B hB hF
  have h4899 : mixedVector B (Sum.inr 4899) = Sparse.eval nodeValue4899 (mixedVector B) := by
    change mixedMoment B node4899 node4899Labels = _
    exact sound4899 B hB hF
  have h5302 : mixedVector B (Sum.inr 5302) = Sparse.eval nodeValue5302 (mixedVector B) := by
    change mixedMoment B node5302 node5302Labels = _
    exact sound5302 B hB hF
  have h5310 : mixedVector B (Sum.inr 5310) = Sparse.eval nodeValue5310 (mixedVector B) := by
    change mixedMoment B node5310 node5310Labels = _
    exact sound5310 B hB hF
  have h5456 : mixedVector B (Sum.inr 5456) = Sparse.eval nodeValue5456 (mixedVector B) := by
    change mixedMoment B node5456 node5456Labels = _
    exact sound5456 B hB hF
  simpa only [sourceForm117, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4276, h4280, h4285, h4572, h4621, h4747, h4754, h4871, h4898, h4899, h5302, h5310, h5456, reducedSource97] using sourceEq117 B hB

theorem rowSound97 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row97 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck97, numericCheck97, reducedZero97 B hB hF, mul_zero]

theorem reducedZero98 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource98 (mixedVector B) = 0 := by
  have h828 : mixedVector B (Sum.inr 828) = Sparse.eval nodeValue828 (mixedVector B) := by
    change mixedMoment B node828 node828Labels = _
    exact sound828 B hB hF
  have h832 : mixedVector B (Sum.inr 832) = Sparse.eval nodeValue832 (mixedVector B) := by
    change mixedMoment B node832 node832Labels = _
    exact sound832 B hB hF
  have h860 : mixedVector B (Sum.inr 860) = Sparse.eval nodeValue860 (mixedVector B) := by
    change mixedMoment B node860 node860Labels = _
    exact sound860 B hB hF
  have h1190 : mixedVector B (Sum.inr 1190) = Sparse.eval nodeValue1190 (mixedVector B) := by
    change mixedMoment B node1190 node1190Labels = _
    exact sound1190 B hB hF
  have h1297 : mixedVector B (Sum.inr 1297) = Sparse.eval nodeValue1297 (mixedVector B) := by
    change mixedMoment B node1297 node1297Labels = _
    exact sound1297 B hB hF
  have h1926 : mixedVector B (Sum.inr 1926) = Sparse.eval nodeValue1926 (mixedVector B) := by
    change mixedMoment B node1926 node1926Labels = _
    exact sound1926 B hB hF
  have h1951 : mixedVector B (Sum.inr 1951) = Sparse.eval nodeValue1951 (mixedVector B) := by
    change mixedMoment B node1951 node1951Labels = _
    exact sound1951 B hB hF
  have h2112 : mixedVector B (Sum.inr 2112) = Sparse.eval nodeValue2112 (mixedVector B) := by
    change mixedMoment B node2112 node2112Labels = _
    exact sound2112 B hB hF
  have h2279 : mixedVector B (Sum.inr 2279) = Sparse.eval nodeValue2279 (mixedVector B) := by
    change mixedMoment B node2279 node2279Labels = _
    exact sound2279 B hB hF
  have h2294 : mixedVector B (Sum.inr 2294) = Sparse.eval nodeValue2294 (mixedVector B) := by
    change mixedMoment B node2294 node2294Labels = _
    exact sound2294 B hB hF
  have h3054 : mixedVector B (Sum.inr 3054) = Sparse.eval nodeValue3054 (mixedVector B) := by
    change mixedMoment B node3054 node3054Labels = _
    exact sound3054 B hB hF
  have h3121 : mixedVector B (Sum.inr 3121) = Sparse.eval nodeValue3121 (mixedVector B) := by
    change mixedMoment B node3121 node3121Labels = _
    exact sound3121 B hB hF
  have h3916 : mixedVector B (Sum.inr 3916) = Sparse.eval nodeValue3916 (mixedVector B) := by
    change mixedMoment B node3916 node3916Labels = _
    exact sound3916 B hB hF
  simpa only [sourceForm118, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h828, h832, h860, h1190, h1297, h1926, h1951, h2112, h2279, h2294, h3054, h3121, h3916, reducedSource98] using sourceEq118 B hB

theorem rowSound98 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row98 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck98, numericCheck98, reducedZero98 B hB hF, mul_zero]

theorem reducedZero99 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource99 (mixedVector B) = 0 := by
  have h4476 : mixedVector B (Sum.inr 4476) = Sparse.eval nodeValue4476 (mixedVector B) := by
    change mixedMoment B node4476 node4476Labels = _
    exact sound4476 B hB hF
  have h4478 : mixedVector B (Sum.inr 4478) = Sparse.eval nodeValue4478 (mixedVector B) := by
    change mixedMoment B node4478 node4478Labels = _
    exact sound4478 B hB hF
  have h4481 : mixedVector B (Sum.inr 4481) = Sparse.eval nodeValue4481 (mixedVector B) := by
    change mixedMoment B node4481 node4481Labels = _
    exact sound4481 B hB hF
  have h4507 : mixedVector B (Sum.inr 4507) = Sparse.eval nodeValue4507 (mixedVector B) := by
    change mixedMoment B node4507 node4507Labels = _
    exact sound4507 B hB hF
  have h4508 : mixedVector B (Sum.inr 4508) = Sparse.eval nodeValue4508 (mixedVector B) := by
    change mixedMoment B node4508 node4508Labels = _
    exact sound4508 B hB hF
  have h4817 : mixedVector B (Sum.inr 4817) = Sparse.eval nodeValue4817 (mixedVector B) := by
    change mixedMoment B node4817 node4817Labels = _
    exact sound4817 B hB hF
  have h4843 : mixedVector B (Sum.inr 4843) = Sparse.eval nodeValue4843 (mixedVector B) := by
    change mixedMoment B node4843 node4843Labels = _
    exact sound4843 B hB hF
  have h4881 : mixedVector B (Sum.inr 4881) = Sparse.eval nodeValue4881 (mixedVector B) := by
    change mixedMoment B node4881 node4881Labels = _
    exact sound4881 B hB hF
  have h4896 : mixedVector B (Sum.inr 4896) = Sparse.eval nodeValue4896 (mixedVector B) := by
    change mixedMoment B node4896 node4896Labels = _
    exact sound4896 B hB hF
  have h4901 : mixedVector B (Sum.inr 4901) = Sparse.eval nodeValue4901 (mixedVector B) := by
    change mixedMoment B node4901 node4901Labels = _
    exact sound4901 B hB hF
  have h5276 : mixedVector B (Sum.inr 5276) = Sparse.eval nodeValue5276 (mixedVector B) := by
    change mixedMoment B node5276 node5276Labels = _
    exact sound5276 B hB hF
  have h5310 : mixedVector B (Sum.inr 5310) = Sparse.eval nodeValue5310 (mixedVector B) := by
    change mixedMoment B node5310 node5310Labels = _
    exact sound5310 B hB hF
  have h5311 : mixedVector B (Sum.inr 5311) = Sparse.eval nodeValue5311 (mixedVector B) := by
    change mixedMoment B node5311 node5311Labels = _
    exact sound5311 B hB hF
  simpa only [sourceForm119, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4476, h4478, h4481, h4507, h4508, h4817, h4843, h4881, h4896, h4901, h5276, h5310, h5311, reducedSource99] using sourceEq119 B hB

theorem rowSound99 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row99 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck99, numericCheck99, reducedZero99 B hB hF, mul_zero]

theorem reducedZero100 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource100 (mixedVector B) = 0 := by
  have h1061 : mixedVector B (Sum.inr 1061) = Sparse.eval nodeValue1061 (mixedVector B) := by
    change mixedMoment B node1061 node1061Labels = _
    exact sound1061 B hB hF
  have h1064 : mixedVector B (Sum.inr 1064) = Sparse.eval nodeValue1064 (mixedVector B) := by
    change mixedMoment B node1064 node1064Labels = _
    exact sound1064 B hB hF
  have h1092 : mixedVector B (Sum.inr 1092) = Sparse.eval nodeValue1092 (mixedVector B) := by
    change mixedMoment B node1092 node1092Labels = _
    exact sound1092 B hB hF
  have h1372 : mixedVector B (Sum.inr 1372) = Sparse.eval nodeValue1372 (mixedVector B) := by
    change mixedMoment B node1372 node1372Labels = _
    exact sound1372 B hB hF
  have h1445 : mixedVector B (Sum.inr 1445) = Sparse.eval nodeValue1445 (mixedVector B) := by
    change mixedMoment B node1445 node1445Labels = _
    exact sound1445 B hB hF
  have h2497 : mixedVector B (Sum.inr 2497) = Sparse.eval nodeValue2497 (mixedVector B) := by
    change mixedMoment B node2497 node2497Labels = _
    exact sound2497 B hB hF
  have h2520 : mixedVector B (Sum.inr 2520) = Sparse.eval nodeValue2520 (mixedVector B) := by
    change mixedMoment B node2520 node2520Labels = _
    exact sound2520 B hB hF
  have h2642 : mixedVector B (Sum.inr 2642) = Sparse.eval nodeValue2642 (mixedVector B) := by
    change mixedMoment B node2642 node2642Labels = _
    exact sound2642 B hB hF
  have h2777 : mixedVector B (Sum.inr 2777) = Sparse.eval nodeValue2777 (mixedVector B) := by
    change mixedMoment B node2777 node2777Labels = _
    exact sound2777 B hB hF
  have h2789 : mixedVector B (Sum.inr 2789) = Sparse.eval nodeValue2789 (mixedVector B) := by
    change mixedMoment B node2789 node2789Labels = _
    exact sound2789 B hB hF
  have h3121 : mixedVector B (Sum.inr 3121) = Sparse.eval nodeValue3121 (mixedVector B) := by
    change mixedMoment B node3121 node3121Labels = _
    exact sound3121 B hB hF
  have h3225 : mixedVector B (Sum.inr 3225) = Sparse.eval nodeValue3225 (mixedVector B) := by
    change mixedMoment B node3225 node3225Labels = _
    exact sound3225 B hB hF
  have h3231 : mixedVector B (Sum.inr 3231) = Sparse.eval nodeValue3231 (mixedVector B) := by
    change mixedMoment B node3231 node3231Labels = _
    exact sound3231 B hB hF
  simpa only [sourceForm120, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1061, h1064, h1092, h1372, h1445, h2497, h2520, h2642, h2777, h2789, h3121, h3225, h3231, reducedSource100] using sourceEq120 B hB

theorem rowSound100 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row100 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck100, numericCheck100, reducedZero100 B hB hF, mul_zero]

theorem reducedZero101 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource101 (mixedVector B) = 0 := by
  have h1729 : mixedVector B (Sum.inr 1729) = Sparse.eval nodeValue1729 (mixedVector B) := by
    change mixedMoment B node1729 node1729Labels = _
    exact sound1729 B hB hF
  have h1746 : mixedVector B (Sum.inr 1746) = Sparse.eval nodeValue1746 (mixedVector B) := by
    change mixedMoment B node1746 node1746Labels = _
    exact sound1746 B hB hF
  have h1747 : mixedVector B (Sum.inr 1747) = Sparse.eval nodeValue1747 (mixedVector B) := by
    change mixedMoment B node1747 node1747Labels = _
    exact sound1747 B hB hF
  have h1756 : mixedVector B (Sum.inr 1756) = Sparse.eval nodeValue1756 (mixedVector B) := by
    change mixedMoment B node1756 node1756Labels = _
    exact sound1756 B hB hF
  have h1757 : mixedVector B (Sum.inr 1757) = Sparse.eval nodeValue1757 (mixedVector B) := by
    change mixedMoment B node1757 node1757Labels = _
    exact sound1757 B hB hF
  have h2207 : mixedVector B (Sum.inr 2207) = Sparse.eval nodeValue2207 (mixedVector B) := by
    change mixedMoment B node2207 node2207Labels = _
    exact sound2207 B hB hF
  have h2230 : mixedVector B (Sum.inr 2230) = Sparse.eval nodeValue2230 (mixedVector B) := by
    change mixedMoment B node2230 node2230Labels = _
    exact sound2230 B hB hF
  have h2266 : mixedVector B (Sum.inr 2266) = Sparse.eval nodeValue2266 (mixedVector B) := by
    change mixedMoment B node2266 node2266Labels = _
    exact sound2266 B hB hF
  have h2267 : mixedVector B (Sum.inr 2267) = Sparse.eval nodeValue2267 (mixedVector B) := by
    change mixedMoment B node2267 node2267Labels = _
    exact sound2267 B hB hF
  have h2293 : mixedVector B (Sum.inr 2293) = Sparse.eval nodeValue2293 (mixedVector B) := by
    change mixedMoment B node2293 node2293Labels = _
    exact sound2293 B hB hF
  have h2744 : mixedVector B (Sum.inr 2744) = Sparse.eval nodeValue2744 (mixedVector B) := by
    change mixedMoment B node2744 node2744Labels = _
    exact sound2744 B hB hF
  have h2788 : mixedVector B (Sum.inr 2788) = Sparse.eval nodeValue2788 (mixedVector B) := by
    change mixedMoment B node2788 node2788Labels = _
    exact sound2788 B hB hF
  have h2789 : mixedVector B (Sum.inr 2789) = Sparse.eval nodeValue2789 (mixedVector B) := by
    change mixedMoment B node2789 node2789Labels = _
    exact sound2789 B hB hF
  simpa only [sourceForm121, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1729, h1746, h1747, h1756, h1757, h2207, h2230, h2266, h2267, h2293, h2744, h2788, h2789, reducedSource101] using sourceEq121 B hB

theorem rowSound101 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row101 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck101, numericCheck101, reducedZero101 B hB hF, mul_zero]

theorem reducedZero102 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource102 (mixedVector B) = 0 := by
  have h2278 : mixedVector B (Sum.inr 2278) = Sparse.eval nodeValue2278 (mixedVector B) := by
    change mixedMoment B node2278 node2278Labels = _
    exact sound2278 B hB hF
  have h2281 : mixedVector B (Sum.inr 2281) = Sparse.eval nodeValue2281 (mixedVector B) := by
    change mixedMoment B node2281 node2281Labels = _
    exact sound2281 B hB hF
  have h2293 : mixedVector B (Sum.inr 2293) = Sparse.eval nodeValue2293 (mixedVector B) := by
    change mixedMoment B node2293 node2293Labels = _
    exact sound2293 B hB hF
  have h3633 : mixedVector B (Sum.inr 3633) = Sparse.eval nodeValue3633 (mixedVector B) := by
    change mixedMoment B node3633 node3633Labels = _
    exact sound3633 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm122, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2278, h2281, h2293, h3633, h4084, reducedSource102] using sourceEq122 B hB

theorem rowSound102 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row102 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck102, numericCheck102, reducedZero102 B hB hF, mul_zero]

theorem reducedZero103 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource103 (mixedVector B) = 0 := by
  have h1064 : mixedVector B (Sum.inr 1064) = Sparse.eval nodeValue1064 (mixedVector B) := by
    change mixedMoment B node1064 node1064Labels = _
    exact sound1064 B hB hF
  have h1369 : mixedVector B (Sum.inr 1369) = Sparse.eval nodeValue1369 (mixedVector B) := by
    change mixedMoment B node1369 node1369Labels = _
    exact sound1369 B hB hF
  have h1438 : mixedVector B (Sum.inr 1438) = Sparse.eval nodeValue1438 (mixedVector B) := by
    change mixedMoment B node1438 node1438Labels = _
    exact sound1438 B hB hF
  have h2281 : mixedVector B (Sum.inr 2281) = Sparse.eval nodeValue2281 (mixedVector B) := by
    change mixedMoment B node2281 node2281Labels = _
    exact sound2281 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm123, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1064, h1369, h1438, h2281, h4084, reducedSource103] using sourceEq123 B hB

theorem rowSound103 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row103 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck103, numericCheck103, reducedZero103 B hB hF, mul_zero]

theorem reducedZero104 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource104 (mixedVector B) = 0 := by
  have h1369 : mixedVector B (Sum.inr 1369) = Sparse.eval nodeValue1369 (mixedVector B) := by
    change mixedMoment B node1369 node1369Labels = _
    exact sound1369 B hB hF
  have h2035 : mixedVector B (Sum.inr 2035) = Sparse.eval nodeValue2035 (mixedVector B) := by
    change mixedMoment B node2035 node2035Labels = _
    exact sound2035 B hB hF
  have h2062 : mixedVector B (Sum.inr 2062) = Sparse.eval nodeValue2062 (mixedVector B) := by
    change mixedMoment B node2062 node2062Labels = _
    exact sound2062 B hB hF
  have h2281 : mixedVector B (Sum.inr 2281) = Sparse.eval nodeValue2281 (mixedVector B) := by
    change mixedMoment B node2281 node2281Labels = _
    exact sound2281 B hB hF
  have h3052 : mixedVector B (Sum.inr 3052) = Sparse.eval nodeValue3052 (mixedVector B) := by
    change mixedMoment B node3052 node3052Labels = _
    exact sound3052 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm124, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1369, h2035, h2062, h2281, h3052, h4084, reducedSource104] using sourceEq124 B hB

theorem rowSound104 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row104 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck104, numericCheck104, reducedZero104 B hB hF, mul_zero]

theorem reducedZero105 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource105 (mixedVector B) = 0 := by
  have h1059 : mixedVector B (Sum.inr 1059) = Sparse.eval nodeValue1059 (mixedVector B) := by
    change mixedMoment B node1059 node1059Labels = _
    exact sound1059 B hB hF
  have h2035 : mixedVector B (Sum.inr 2035) = Sparse.eval nodeValue2035 (mixedVector B) := by
    change mixedMoment B node2035 node2035Labels = _
    exact sound2035 B hB hF
  have h2134 : mixedVector B (Sum.inr 2134) = Sparse.eval nodeValue2134 (mixedVector B) := by
    change mixedMoment B node2134 node2134Labels = _
    exact sound2134 B hB hF
  have h2278 : mixedVector B (Sum.inr 2278) = Sparse.eval nodeValue2278 (mixedVector B) := by
    change mixedMoment B node2278 node2278Labels = _
    exact sound2278 B hB hF
  have h2281 : mixedVector B (Sum.inr 2281) = Sparse.eval nodeValue2281 (mixedVector B) := by
    change mixedMoment B node2281 node2281Labels = _
    exact sound2281 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm125, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1059, h2035, h2134, h2278, h2281, h4084, reducedSource105] using sourceEq125 B hB

theorem rowSound105 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row105 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck105, numericCheck105, reducedZero105 B hB hF, mul_zero]

theorem reducedZero106 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource106 (mixedVector B) = 0 := by
  have h1438 : mixedVector B (Sum.inr 1438) = Sparse.eval nodeValue1438 (mixedVector B) := by
    change mixedMoment B node1438 node1438Labels = _
    exact sound1438 B hB hF
  have h2134 : mixedVector B (Sum.inr 2134) = Sparse.eval nodeValue2134 (mixedVector B) := by
    change mixedMoment B node2134 node2134Labels = _
    exact sound2134 B hB hF
  have h2281 : mixedVector B (Sum.inr 2281) = Sparse.eval nodeValue2281 (mixedVector B) := by
    change mixedMoment B node2281 node2281Labels = _
    exact sound2281 B hB hF
  have h2789 : mixedVector B (Sum.inr 2789) = Sparse.eval nodeValue2789 (mixedVector B) := by
    change mixedMoment B node2789 node2789Labels = _
    exact sound2789 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm126, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1438, h2134, h2281, h2789, h4084, reducedSource106] using sourceEq126 B hB

theorem rowSound106 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row106 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck106, numericCheck106, reducedZero106 B hB hF, mul_zero]

theorem reducedZero107 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource107 (mixedVector B) = 0 := by
  have h1091 : mixedVector B (Sum.inr 1091) = Sparse.eval nodeValue1091 (mixedVector B) := by
    change mixedMoment B node1091 node1091Labels = _
    exact sound1091 B hB hF
  have h2062 : mixedVector B (Sum.inr 2062) = Sparse.eval nodeValue2062 (mixedVector B) := by
    change mixedMoment B node2062 node2062Labels = _
    exact sound2062 B hB hF
  have h2281 : mixedVector B (Sum.inr 2281) = Sparse.eval nodeValue2281 (mixedVector B) := by
    change mixedMoment B node2281 node2281Labels = _
    exact sound2281 B hB hF
  have h2293 : mixedVector B (Sum.inr 2293) = Sparse.eval nodeValue2293 (mixedVector B) := by
    change mixedMoment B node2293 node2293Labels = _
    exact sound2293 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm127, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1091, h2062, h2281, h2293, h4084, reducedSource107] using sourceEq127 B hB

theorem rowSound107 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row107 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck107, numericCheck107, reducedZero107 B hB hF, mul_zero]

theorem reducedZero108 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource108 (mixedVector B) = 0 := by
  have h1059 : mixedVector B (Sum.inr 1059) = Sparse.eval nodeValue1059 (mixedVector B) := by
    change mixedMoment B node1059 node1059Labels = _
    exact sound1059 B hB hF
  have h1064 : mixedVector B (Sum.inr 1064) = Sparse.eval nodeValue1064 (mixedVector B) := by
    change mixedMoment B node1064 node1064Labels = _
    exact sound1064 B hB hF
  have h1091 : mixedVector B (Sum.inr 1091) = Sparse.eval nodeValue1091 (mixedVector B) := by
    change mixedMoment B node1091 node1091Labels = _
    exact sound1091 B hB hF
  have h2281 : mixedVector B (Sum.inr 2281) = Sparse.eval nodeValue2281 (mixedVector B) := by
    change mixedMoment B node2281 node2281Labels = _
    exact sound2281 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm128, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1059, h1064, h1091, h2281, h4084, reducedSource108] using sourceEq128 B hB

theorem rowSound108 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row108 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck108, numericCheck108, reducedZero108 B hB hF, mul_zero]

theorem reducedZero109 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource109 (mixedVector B) = 0 := by
  have h4500 : mixedVector B (Sum.inr 4500) = Sparse.eval nodeValue4500 (mixedVector B) := by
    change mixedMoment B node4500 node4500Labels = _
    exact sound4500 B hB hF
  have h4508 : mixedVector B (Sum.inr 4508) = Sparse.eval nodeValue4508 (mixedVector B) := by
    change mixedMoment B node4508 node4508Labels = _
    exact sound4508 B hB hF
  have h4510 : mixedVector B (Sum.inr 4510) = Sparse.eval nodeValue4510 (mixedVector B) := by
    change mixedMoment B node4510 node4510Labels = _
    exact sound4510 B hB hF
  have h4836 : mixedVector B (Sum.inr 4836) = Sparse.eval nodeValue4836 (mixedVector B) := by
    change mixedMoment B node4836 node4836Labels = _
    exact sound4836 B hB hF
  have h4844 : mixedVector B (Sum.inr 4844) = Sparse.eval nodeValue4844 (mixedVector B) := by
    change mixedMoment B node4844 node4844Labels = _
    exact sound4844 B hB hF
  have h4845 : mixedVector B (Sum.inr 4845) = Sparse.eval nodeValue4845 (mixedVector B) := by
    change mixedMoment B node4845 node4845Labels = _
    exact sound4845 B hB hF
  have h4890 : mixedVector B (Sum.inr 4890) = Sparse.eval nodeValue4890 (mixedVector B) := by
    change mixedMoment B node4890 node4890Labels = _
    exact sound4890 B hB hF
  have h4892 : mixedVector B (Sum.inr 4892) = Sparse.eval nodeValue4892 (mixedVector B) := by
    change mixedMoment B node4892 node4892Labels = _
    exact sound4892 B hB hF
  have h4897 : mixedVector B (Sum.inr 4897) = Sparse.eval nodeValue4897 (mixedVector B) := by
    change mixedMoment B node4897 node4897Labels = _
    exact sound4897 B hB hF
  have h4899 : mixedVector B (Sum.inr 4899) = Sparse.eval nodeValue4899 (mixedVector B) := by
    change mixedMoment B node4899 node4899Labels = _
    exact sound4899 B hB hF
  have h4900 : mixedVector B (Sum.inr 4900) = Sparse.eval nodeValue4900 (mixedVector B) := by
    change mixedMoment B node4900 node4900Labels = _
    exact sound4900 B hB hF
  have h5268 : mixedVector B (Sum.inr 5268) = Sparse.eval nodeValue5268 (mixedVector B) := by
    change mixedMoment B node5268 node5268Labels = _
    exact sound5268 B hB hF
  have h5296 : mixedVector B (Sum.inr 5296) = Sparse.eval nodeValue5296 (mixedVector B) := by
    change mixedMoment B node5296 node5296Labels = _
    exact sound5296 B hB hF
  simpa only [sourceForm129, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4500, h4508, h4510, h4836, h4844, h4845, h4890, h4892, h4897, h4899, h4900, h5268, h5296, reducedSource109] using sourceEq129 B hB

theorem rowSound109 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row109 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck109, numericCheck109, reducedZero109 B hB hF, mul_zero]

theorem reducedZero110 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource110 (mixedVector B) = 0 := by
  have h1436 : mixedVector B (Sum.inr 1436) = Sparse.eval nodeValue1436 (mixedVector B) := by
    change mixedMoment B node1436 node1436Labels = _
    exact sound1436 B hB hF
  have h1438 : mixedVector B (Sum.inr 1438) = Sparse.eval nodeValue1438 (mixedVector B) := by
    change mixedMoment B node1438 node1438Labels = _
    exact sound1438 B hB hF
  have h1454 : mixedVector B (Sum.inr 1454) = Sparse.eval nodeValue1454 (mixedVector B) := by
    change mixedMoment B node1454 node1454Labels = _
    exact sound1454 B hB hF
  have h2136 : mixedVector B (Sum.inr 2136) = Sparse.eval nodeValue2136 (mixedVector B) := by
    change mixedMoment B node2136 node2136Labels = _
    exact sound2136 B hB hF
  have h2255 : mixedVector B (Sum.inr 2255) = Sparse.eval nodeValue2255 (mixedVector B) := by
    change mixedMoment B node2255 node2255Labels = _
    exact sound2255 B hB hF
  have h2281 : mixedVector B (Sum.inr 2281) = Sparse.eval nodeValue2281 (mixedVector B) := by
    change mixedMoment B node2281 node2281Labels = _
    exact sound2281 B hB hF
  have h2285 : mixedVector B (Sum.inr 2285) = Sparse.eval nodeValue2285 (mixedVector B) := by
    change mixedMoment B node2285 node2285Labels = _
    exact sound2285 B hB hF
  have h2716 : mixedVector B (Sum.inr 2716) = Sparse.eval nodeValue2716 (mixedVector B) := by
    change mixedMoment B node2716 node2716Labels = _
    exact sound2716 B hB hF
  have h2734 : mixedVector B (Sum.inr 2734) = Sparse.eval nodeValue2734 (mixedVector B) := by
    change mixedMoment B node2734 node2734Labels = _
    exact sound2734 B hB hF
  have h2755 : mixedVector B (Sum.inr 2755) = Sparse.eval nodeValue2755 (mixedVector B) := by
    change mixedMoment B node2755 node2755Labels = _
    exact sound2755 B hB hF
  have h2770 : mixedVector B (Sum.inr 2770) = Sparse.eval nodeValue2770 (mixedVector B) := by
    change mixedMoment B node2770 node2770Labels = _
    exact sound2770 B hB hF
  have h3095 : mixedVector B (Sum.inr 3095) = Sparse.eval nodeValue3095 (mixedVector B) := by
    change mixedMoment B node3095 node3095Labels = _
    exact sound3095 B hB hF
  have h3114 : mixedVector B (Sum.inr 3114) = Sparse.eval nodeValue3114 (mixedVector B) := by
    change mixedMoment B node3114 node3114Labels = _
    exact sound3114 B hB hF
  simpa only [sourceForm130, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1436, h1438, h1454, h2136, h2255, h2281, h2285, h2716, h2734, h2755, h2770, h3095, h3114, reducedSource110] using sourceEq130 B hB

theorem rowSound110 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row110 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck110, numericCheck110, reducedZero110 B hB hF, mul_zero]

theorem reducedZero111 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource111 (mixedVector B) = 0 := by
  have h1716 : mixedVector B (Sum.inr 1716) = Sparse.eval nodeValue1716 (mixedVector B) := by
    change mixedMoment B node1716 node1716Labels = _
    exact sound1716 B hB hF
  have h1741 : mixedVector B (Sum.inr 1741) = Sparse.eval nodeValue1741 (mixedVector B) := by
    change mixedMoment B node1741 node1741Labels = _
    exact sound1741 B hB hF
  have h1747 : mixedVector B (Sum.inr 1747) = Sparse.eval nodeValue1747 (mixedVector B) := by
    change mixedMoment B node1747 node1747Labels = _
    exact sound1747 B hB hF
  have h2197 : mixedVector B (Sum.inr 2197) = Sparse.eval nodeValue2197 (mixedVector B) := by
    change mixedMoment B node2197 node2197Labels = _
    exact sound2197 B hB hF
  have h2218 : mixedVector B (Sum.inr 2218) = Sparse.eval nodeValue2218 (mixedVector B) := by
    change mixedMoment B node2218 node2218Labels = _
    exact sound2218 B hB hF
  have h2222 : mixedVector B (Sum.inr 2222) = Sparse.eval nodeValue2222 (mixedVector B) := by
    change mixedMoment B node2222 node2222Labels = _
    exact sound2222 B hB hF
  have h2247 : mixedVector B (Sum.inr 2247) = Sparse.eval nodeValue2247 (mixedVector B) := by
    change mixedMoment B node2247 node2247Labels = _
    exact sound2247 B hB hF
  have h2255 : mixedVector B (Sum.inr 2255) = Sparse.eval nodeValue2255 (mixedVector B) := by
    change mixedMoment B node2255 node2255Labels = _
    exact sound2255 B hB hF
  have h2268 : mixedVector B (Sum.inr 2268) = Sparse.eval nodeValue2268 (mixedVector B) := by
    change mixedMoment B node2268 node2268Labels = _
    exact sound2268 B hB hF
  have h2285 : mixedVector B (Sum.inr 2285) = Sparse.eval nodeValue2285 (mixedVector B) := by
    change mixedMoment B node2285 node2285Labels = _
    exact sound2285 B hB hF
  have h2734 : mixedVector B (Sum.inr 2734) = Sparse.eval nodeValue2734 (mixedVector B) := by
    change mixedMoment B node2734 node2734Labels = _
    exact sound2734 B hB hF
  have h2770 : mixedVector B (Sum.inr 2770) = Sparse.eval nodeValue2770 (mixedVector B) := by
    change mixedMoment B node2770 node2770Labels = _
    exact sound2770 B hB hF
  have h2778 : mixedVector B (Sum.inr 2778) = Sparse.eval nodeValue2778 (mixedVector B) := by
    change mixedMoment B node2778 node2778Labels = _
    exact sound2778 B hB hF
  simpa only [sourceForm131, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1716, h1741, h1747, h2197, h2218, h2222, h2247, h2255, h2268, h2285, h2734, h2770, h2778, reducedSource111] using sourceEq131 B hB

theorem rowSound111 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row111 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck111, numericCheck111, reducedZero111 B hB hF, mul_zero]

theorem sourceRowsAt96 : MixedData.sourceRows (96 : Fin 2425) =
    MixedData.row96 := by decide +kernel

theorem sourceRowsAt97 : MixedData.sourceRows (97 : Fin 2425) =
    MixedData.row97 := by decide +kernel

theorem sourceRowsAt98 : MixedData.sourceRows (98 : Fin 2425) =
    MixedData.row98 := by decide +kernel

theorem sourceRowsAt99 : MixedData.sourceRows (99 : Fin 2425) =
    MixedData.row99 := by decide +kernel

theorem sourceRowsAt100 : MixedData.sourceRows (100 : Fin 2425) =
    MixedData.row100 := by decide +kernel

theorem sourceRowsAt101 : MixedData.sourceRows (101 : Fin 2425) =
    MixedData.row101 := by decide +kernel

theorem sourceRowsAt102 : MixedData.sourceRows (102 : Fin 2425) =
    MixedData.row102 := by decide +kernel

theorem sourceRowsAt103 : MixedData.sourceRows (103 : Fin 2425) =
    MixedData.row103 := by decide +kernel

theorem sourceRowsAt104 : MixedData.sourceRows (104 : Fin 2425) =
    MixedData.row104 := by decide +kernel

theorem sourceRowsAt105 : MixedData.sourceRows (105 : Fin 2425) =
    MixedData.row105 := by decide +kernel

theorem sourceRowsAt106 : MixedData.sourceRows (106 : Fin 2425) =
    MixedData.row106 := by decide +kernel

theorem sourceRowsAt107 : MixedData.sourceRows (107 : Fin 2425) =
    MixedData.row107 := by decide +kernel

theorem sourceRowsAt108 : MixedData.sourceRows (108 : Fin 2425) =
    MixedData.row108 := by decide +kernel

theorem sourceRowsAt109 : MixedData.sourceRows (109 : Fin 2425) =
    MixedData.row109 := by decide +kernel

theorem sourceRowsAt110 : MixedData.sourceRows (110 : Fin 2425) =
    MixedData.row110 := by decide +kernel

theorem sourceRowsAt111 : MixedData.sourceRows (111 : Fin 2425) =
    MixedData.row111 := by decide +kernel

theorem chunkSound6 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 6) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 96 ∨ k.val = 97 ∨ k.val = 98 ∨ k.val = 99 ∨ k.val = 100 ∨ k.val = 101 ∨ k.val = 102 ∨ k.val = 103 ∨ k.val = 104 ∨ k.val = 105 ∨ k.val = 106 ∨ k.val = 107 ∨ k.val = 108 ∨ k.val = 109 ∨ k.val = 110 ∨ k.val = 111 := by omega
  rcases heq with h96 | h97 | h98 | h99 | h100 | h101 | h102 | h103 | h104 | h105 | h106 | h107 | h108 | h109 | h110 | h111
  · have he : k = (96 : Fin 2425) := Fin.ext h96
    subst k
    rw [sourceRowsAt96]
    exact rowSound96 B hB hF
  · have he : k = (97 : Fin 2425) := Fin.ext h97
    subst k
    rw [sourceRowsAt97]
    exact rowSound97 B hB hF
  · have he : k = (98 : Fin 2425) := Fin.ext h98
    subst k
    rw [sourceRowsAt98]
    exact rowSound98 B hB hF
  · have he : k = (99 : Fin 2425) := Fin.ext h99
    subst k
    rw [sourceRowsAt99]
    exact rowSound99 B hB hF
  · have he : k = (100 : Fin 2425) := Fin.ext h100
    subst k
    rw [sourceRowsAt100]
    exact rowSound100 B hB hF
  · have he : k = (101 : Fin 2425) := Fin.ext h101
    subst k
    rw [sourceRowsAt101]
    exact rowSound101 B hB hF
  · have he : k = (102 : Fin 2425) := Fin.ext h102
    subst k
    rw [sourceRowsAt102]
    exact rowSound102 B hB hF
  · have he : k = (103 : Fin 2425) := Fin.ext h103
    subst k
    rw [sourceRowsAt103]
    exact rowSound103 B hB hF
  · have he : k = (104 : Fin 2425) := Fin.ext h104
    subst k
    rw [sourceRowsAt104]
    exact rowSound104 B hB hF
  · have he : k = (105 : Fin 2425) := Fin.ext h105
    subst k
    rw [sourceRowsAt105]
    exact rowSound105 B hB hF
  · have he : k = (106 : Fin 2425) := Fin.ext h106
    subst k
    rw [sourceRowsAt106]
    exact rowSound106 B hB hF
  · have he : k = (107 : Fin 2425) := Fin.ext h107
    subst k
    rw [sourceRowsAt107]
    exact rowSound107 B hB hF
  · have he : k = (108 : Fin 2425) := Fin.ext h108
    subst k
    rw [sourceRowsAt108]
    exact rowSound108 B hB hF
  · have he : k = (109 : Fin 2425) := Fin.ext h109
    subst k
    rw [sourceRowsAt109]
    exact rowSound109 B hB hF
  · have he : k = (110 : Fin 2425) := Fin.ext h110
    subst k
    rw [sourceRowsAt110]
    exact rowSound110 B hB hF
  · have he : k = (111 : Fin 2425) := Fin.ext h111
    subst k
    rw [sourceRowsAt111]
    exact rowSound111 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
