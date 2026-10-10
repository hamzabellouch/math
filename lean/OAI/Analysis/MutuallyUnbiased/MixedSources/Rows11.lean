import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources6
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources7

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero176 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource176 (mixedVector B) = 0 := by
  have h776 : mixedVector B (Sum.inr 776) = Sparse.eval nodeValue776 (mixedVector B) := by
    change mixedMoment B node776 node776Labels = _
    exact sound776 B hB hF
  have h778 : mixedVector B (Sum.inr 778) = Sparse.eval nodeValue778 (mixedVector B) := by
    change mixedMoment B node778 node778Labels = _
    exact sound778 B hB hF
  have h784 : mixedVector B (Sum.inr 784) = Sparse.eval nodeValue784 (mixedVector B) := by
    change mixedMoment B node784 node784Labels = _
    exact sound784 B hB hF
  have h2009 : mixedVector B (Sum.inr 2009) = Sparse.eval nodeValue2009 (mixedVector B) := by
    change mixedMoment B node2009 node2009Labels = _
    exact sound2009 B hB hF
  have h2012 : mixedVector B (Sum.inr 2012) = Sparse.eval nodeValue2012 (mixedVector B) := by
    change mixedMoment B node2012 node2012Labels = _
    exact sound2012 B hB hF
  have h2021 : mixedVector B (Sum.inr 2021) = Sparse.eval nodeValue2021 (mixedVector B) := by
    change mixedMoment B node2021 node2021Labels = _
    exact sound2021 B hB hF
  have h2187 : mixedVector B (Sum.inr 2187) = Sparse.eval nodeValue2187 (mixedVector B) := by
    change mixedMoment B node2187 node2187Labels = _
    exact sound2187 B hB hF
  have h2192 : mixedVector B (Sum.inr 2192) = Sparse.eval nodeValue2192 (mixedVector B) := by
    change mixedMoment B node2192 node2192Labels = _
    exact sound2192 B hB hF
  have h2232 : mixedVector B (Sum.inr 2232) = Sparse.eval nodeValue2232 (mixedVector B) := by
    change mixedMoment B node2232 node2232Labels = _
    exact sound2232 B hB hF
  have h2240 : mixedVector B (Sum.inr 2240) = Sparse.eval nodeValue2240 (mixedVector B) := by
    change mixedMoment B node2240 node2240Labels = _
    exact sound2240 B hB hF
  have h3847 : mixedVector B (Sum.inr 3847) = Sparse.eval nodeValue3847 (mixedVector B) := by
    change mixedMoment B node3847 node3847Labels = _
    exact sound3847 B hB hF
  have h3899 : mixedVector B (Sum.inr 3899) = Sparse.eval nodeValue3899 (mixedVector B) := by
    change mixedMoment B node3899 node3899Labels = _
    exact sound3899 B hB hF
  have h3909 : mixedVector B (Sum.inr 3909) = Sparse.eval nodeValue3909 (mixedVector B) := by
    change mixedMoment B node3909 node3909Labels = _
    exact sound3909 B hB hF
  simpa only [sourceForm203, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h776, h778, h784, h2009, h2012, h2021, h2187, h2192, h2232, h2240, h3847, h3899, h3909, reducedSource176] using sourceEq203 B hB

theorem rowSound176 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row176 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck176, numericCheck176, reducedZero176 B hB hF, mul_zero]

theorem reducedZero177 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource177 (mixedVector B) = 0 := by
  have h3221 : mixedVector B (Sum.inr 3221) = Sparse.eval nodeValue3221 (mixedVector B) := by
    change mixedMoment B node3221 node3221Labels = _
    exact sound3221 B hB hF
  have h3801 : mixedVector B (Sum.inr 3801) = Sparse.eval nodeValue3801 (mixedVector B) := by
    change mixedMoment B node3801 node3801Labels = _
    exact sound3801 B hB hF
  have h3899 : mixedVector B (Sum.inr 3899) = Sparse.eval nodeValue3899 (mixedVector B) := by
    change mixedMoment B node3899 node3899Labels = _
    exact sound3899 B hB hF
  have h4025 : mixedVector B (Sum.inr 4025) = Sparse.eval nodeValue4025 (mixedVector B) := by
    change mixedMoment B node4025 node4025Labels = _
    exact sound4025 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm205, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3221, h3801, h3899, h4025, h4091, reducedSource177] using sourceEq205 B hB

theorem rowSound177 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row177 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck177, numericCheck177, reducedZero177 B hB hF, mul_zero]

theorem reducedZero178 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource178 (mixedVector B) = 0 := by
  have h1464 : mixedVector B (Sum.inr 1464) = Sparse.eval nodeValue1464 (mixedVector B) := by
    change mixedMoment B node1464 node1464Labels = _
    exact sound1464 B hB hF
  have h1467 : mixedVector B (Sum.inr 1467) = Sparse.eval nodeValue1467 (mixedVector B) := by
    change mixedMoment B node1467 node1467Labels = _
    exact sound1467 B hB hF
  have h1474 : mixedVector B (Sum.inr 1474) = Sparse.eval nodeValue1474 (mixedVector B) := by
    change mixedMoment B node1474 node1474Labels = _
    exact sound1474 B hB hF
  have h3221 : mixedVector B (Sum.inr 3221) = Sparse.eval nodeValue3221 (mixedVector B) := by
    change mixedMoment B node3221 node3221Labels = _
    exact sound3221 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm206, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1464, h1467, h1474, h3221, h4091, reducedSource178] using sourceEq206 B hB

theorem rowSound178 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row178 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck178, numericCheck178, reducedZero178 B hB hF, mul_zero]

theorem reducedZero179 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource179 (mixedVector B) = 0 := by
  have h1464 : mixedVector B (Sum.inr 1464) = Sparse.eval nodeValue1464 (mixedVector B) := by
    change mixedMoment B node1464 node1464Labels = _
    exact sound1464 B hB hF
  have h3172 : mixedVector B (Sum.inr 3172) = Sparse.eval nodeValue3172 (mixedVector B) := by
    change mixedMoment B node3172 node3172Labels = _
    exact sound3172 B hB hF
  have h3197 : mixedVector B (Sum.inr 3197) = Sparse.eval nodeValue3197 (mixedVector B) := by
    change mixedMoment B node3197 node3197Labels = _
    exact sound3197 B hB hF
  have h3202 : mixedVector B (Sum.inr 3202) = Sparse.eval nodeValue3202 (mixedVector B) := by
    change mixedMoment B node3202 node3202Labels = _
    exact sound3202 B hB hF
  have h3221 : mixedVector B (Sum.inr 3221) = Sparse.eval nodeValue3221 (mixedVector B) := by
    change mixedMoment B node3221 node3221Labels = _
    exact sound3221 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm207, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1464, h3172, h3197, h3202, h3221, h4091, reducedSource179] using sourceEq207 B hB

theorem rowSound179 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row179 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck179, numericCheck179, reducedZero179 B hB hF, mul_zero]

theorem reducedZero180 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource180 (mixedVector B) = 0 := by
  have h2471 : mixedVector B (Sum.inr 2471) = Sparse.eval nodeValue2471 (mixedVector B) := by
    change mixedMoment B node2471 node2471Labels = _
    exact sound2471 B hB hF
  have h3199 : mixedVector B (Sum.inr 3199) = Sparse.eval nodeValue3199 (mixedVector B) := by
    change mixedMoment B node3199 node3199Labels = _
    exact sound3199 B hB hF
  have h3202 : mixedVector B (Sum.inr 3202) = Sparse.eval nodeValue3202 (mixedVector B) := by
    change mixedMoment B node3202 node3202Labels = _
    exact sound3202 B hB hF
  have h3221 : mixedVector B (Sum.inr 3221) = Sparse.eval nodeValue3221 (mixedVector B) := by
    change mixedMoment B node3221 node3221Labels = _
    exact sound3221 B hB hF
  have h3801 : mixedVector B (Sum.inr 3801) = Sparse.eval nodeValue3801 (mixedVector B) := by
    change mixedMoment B node3801 node3801Labels = _
    exact sound3801 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm208, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2471, h3199, h3202, h3221, h3801, h4091, reducedSource180] using sourceEq208 B hB

theorem rowSound180 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row180 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck180, numericCheck180, reducedZero180 B hB hF, mul_zero]

theorem reducedZero181 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource181 (mixedVector B) = 0 := by
  have h1467 : mixedVector B (Sum.inr 1467) = Sparse.eval nodeValue1467 (mixedVector B) := by
    change mixedMoment B node1467 node1467Labels = _
    exact sound1467 B hB hF
  have h3179 : mixedVector B (Sum.inr 3179) = Sparse.eval nodeValue3179 (mixedVector B) := by
    change mixedMoment B node3179 node3179Labels = _
    exact sound3179 B hB hF
  have h3199 : mixedVector B (Sum.inr 3199) = Sparse.eval nodeValue3199 (mixedVector B) := by
    change mixedMoment B node3199 node3199Labels = _
    exact sound3199 B hB hF
  have h3221 : mixedVector B (Sum.inr 3221) = Sparse.eval nodeValue3221 (mixedVector B) := by
    change mixedMoment B node3221 node3221Labels = _
    exact sound3221 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm209, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1467, h3179, h3199, h3221, h4091, reducedSource181] using sourceEq209 B hB

theorem rowSound181 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row181 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck181, numericCheck181, reducedZero181 B hB hF, mul_zero]

theorem reducedZero182 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource182 (mixedVector B) = 0 := by
  have h2707 : mixedVector B (Sum.inr 2707) = Sparse.eval nodeValue2707 (mixedVector B) := by
    change mixedMoment B node2707 node2707Labels = _
    exact sound2707 B hB hF
  have h3197 : mixedVector B (Sum.inr 3197) = Sparse.eval nodeValue3197 (mixedVector B) := by
    change mixedMoment B node3197 node3197Labels = _
    exact sound3197 B hB hF
  have h3221 : mixedVector B (Sum.inr 3221) = Sparse.eval nodeValue3221 (mixedVector B) := by
    change mixedMoment B node3221 node3221Labels = _
    exact sound3221 B hB hF
  have h3899 : mixedVector B (Sum.inr 3899) = Sparse.eval nodeValue3899 (mixedVector B) := by
    change mixedMoment B node3899 node3899Labels = _
    exact sound3899 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm210, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2707, h3197, h3221, h3899, h4091, reducedSource182] using sourceEq210 B hB

theorem rowSound182 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row182 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck182, numericCheck182, reducedZero182 B hB hF, mul_zero]

theorem reducedZero183 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource183 (mixedVector B) = 0 := by
  have h1474 : mixedVector B (Sum.inr 1474) = Sparse.eval nodeValue1474 (mixedVector B) := by
    change mixedMoment B node1474 node1474Labels = _
    exact sound1474 B hB hF
  have h2471 : mixedVector B (Sum.inr 2471) = Sparse.eval nodeValue2471 (mixedVector B) := by
    change mixedMoment B node2471 node2471Labels = _
    exact sound2471 B hB hF
  have h2707 : mixedVector B (Sum.inr 2707) = Sparse.eval nodeValue2707 (mixedVector B) := by
    change mixedMoment B node2707 node2707Labels = _
    exact sound2707 B hB hF
  have h3221 : mixedVector B (Sum.inr 3221) = Sparse.eval nodeValue3221 (mixedVector B) := by
    change mixedMoment B node3221 node3221Labels = _
    exact sound3221 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm211, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1474, h2471, h2707, h3221, h4091, reducedSource183] using sourceEq211 B hB

theorem rowSound183 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row183 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck183, numericCheck183, reducedZero183 B hB hF, mul_zero]

theorem reducedZero184 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource184 (mixedVector B) = 0 := by
  have h1354 : mixedVector B (Sum.inr 1354) = Sparse.eval nodeValue1354 (mixedVector B) := by
    change mixedMoment B node1354 node1354Labels = _
    exact sound1354 B hB hF
  have h1366 : mixedVector B (Sum.inr 1366) = Sparse.eval nodeValue1366 (mixedVector B) := by
    change mixedMoment B node1366 node1366Labels = _
    exact sound1366 B hB hF
  have h1405 : mixedVector B (Sum.inr 1405) = Sparse.eval nodeValue1405 (mixedVector B) := by
    change mixedMoment B node1405 node1405Labels = _
    exact sound1405 B hB hF
  have h3058 : mixedVector B (Sum.inr 3058) = Sparse.eval nodeValue3058 (mixedVector B) := by
    change mixedMoment B node3058 node3058Labels = _
    exact sound3058 B hB hF
  have h3059 : mixedVector B (Sum.inr 3059) = Sparse.eval nodeValue3059 (mixedVector B) := by
    change mixedMoment B node3059 node3059Labels = _
    exact sound3059 B hB hF
  have h3077 : mixedVector B (Sum.inr 3077) = Sparse.eval nodeValue3077 (mixedVector B) := by
    change mixedMoment B node3077 node3077Labels = _
    exact sound3077 B hB hF
  have h3146 : mixedVector B (Sum.inr 3146) = Sparse.eval nodeValue3146 (mixedVector B) := by
    change mixedMoment B node3146 node3146Labels = _
    exact sound3146 B hB hF
  have h3155 : mixedVector B (Sum.inr 3155) = Sparse.eval nodeValue3155 (mixedVector B) := by
    change mixedMoment B node3155 node3155Labels = _
    exact sound3155 B hB hF
  have h3165 : mixedVector B (Sum.inr 3165) = Sparse.eval nodeValue3165 (mixedVector B) := by
    change mixedMoment B node3165 node3165Labels = _
    exact sound3165 B hB hF
  have h3179 : mixedVector B (Sum.inr 3179) = Sparse.eval nodeValue3179 (mixedVector B) := by
    change mixedMoment B node3179 node3179Labels = _
    exact sound3179 B hB hF
  have h3222 : mixedVector B (Sum.inr 3222) = Sparse.eval nodeValue3222 (mixedVector B) := by
    change mixedMoment B node3222 node3222Labels = _
    exact sound3222 B hB hF
  have h3223 : mixedVector B (Sum.inr 3223) = Sparse.eval nodeValue3223 (mixedVector B) := by
    change mixedMoment B node3223 node3223Labels = _
    exact sound3223 B hB hF
  have h3227 : mixedVector B (Sum.inr 3227) = Sparse.eval nodeValue3227 (mixedVector B) := by
    change mixedMoment B node3227 node3227Labels = _
    exact sound3227 B hB hF
  simpa only [sourceForm214, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1354, h1366, h1405, h3058, h3059, h3077, h3146, h3155, h3165, h3179, h3222, h3223, h3227, reducedSource184] using sourceEq214 B hB

theorem rowSound184 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row184 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck184, numericCheck184, reducedZero184 B hB hF, mul_zero]

theorem reducedZero185 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource185 (mixedVector B) = 0 := by
  have h2252 : mixedVector B (Sum.inr 2252) = Sparse.eval nodeValue2252 (mixedVector B) := by
    change mixedMoment B node2252 node2252Labels = _
    exact sound2252 B hB hF
  have h2507 : mixedVector B (Sum.inr 2507) = Sparse.eval nodeValue2507 (mixedVector B) := by
    change mixedMoment B node2507 node2507Labels = _
    exact sound2507 B hB hF
  have h3576 : mixedVector B (Sum.inr 3576) = Sparse.eval nodeValue3576 (mixedVector B) := by
    change mixedMoment B node3576 node3576Labels = _
    exact sound3576 B hB hF
  have h3625 : mixedVector B (Sum.inr 3625) = Sparse.eval nodeValue3625 (mixedVector B) := by
    change mixedMoment B node3625 node3625Labels = _
    exact sound3625 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm215, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2252, h2507, h3576, h3625, h4084, reducedSource185] using sourceEq215 B hB

theorem rowSound185 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row185 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck185, numericCheck185, reducedZero185 B hB hF, mul_zero]

theorem reducedZero186 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource186 (mixedVector B) = 0 := by
  have h1056 : mixedVector B (Sum.inr 1056) = Sparse.eval nodeValue1056 (mixedVector B) := by
    change mixedMoment B node1056 node1056Labels = _
    exact sound1056 B hB hF
  have h2131 : mixedVector B (Sum.inr 2131) = Sparse.eval nodeValue2131 (mixedVector B) := by
    change mixedMoment B node2131 node2131Labels = _
    exact sound2131 B hB hF
  have h2252 : mixedVector B (Sum.inr 2252) = Sparse.eval nodeValue2252 (mixedVector B) := by
    change mixedMoment B node2252 node2252Labels = _
    exact sound2252 B hB hF
  have h2277 : mixedVector B (Sum.inr 2277) = Sparse.eval nodeValue2277 (mixedVector B) := by
    change mixedMoment B node2277 node2277Labels = _
    exact sound2277 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm217, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1056, h2131, h2252, h2277, h4084, reducedSource186] using sourceEq217 B hB

theorem rowSound186 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row186 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck186, numericCheck186, reducedZero186 B hB hF, mul_zero]

theorem reducedZero187 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource187 (mixedVector B) = 0 := by
  have h1038 : mixedVector B (Sum.inr 1038) = Sparse.eval nodeValue1038 (mixedVector B) := by
    change mixedMoment B node1038 node1038Labels = _
    exact sound1038 B hB hF
  have h2104 : mixedVector B (Sum.inr 2104) = Sparse.eval nodeValue2104 (mixedVector B) := by
    change mixedMoment B node2104 node2104Labels = _
    exact sound2104 B hB hF
  have h2252 : mixedVector B (Sum.inr 2252) = Sparse.eval nodeValue2252 (mixedVector B) := by
    change mixedMoment B node2252 node2252Labels = _
    exact sound2252 B hB hF
  have h2262 : mixedVector B (Sum.inr 2262) = Sparse.eval nodeValue2262 (mixedVector B) := by
    change mixedMoment B node2262 node2262Labels = _
    exact sound2262 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm219, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1038, h2104, h2252, h2262, h4084, reducedSource187] using sourceEq219 B hB

theorem rowSound187 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row187 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck187, numericCheck187, reducedZero187 B hB hF, mul_zero]

theorem reducedZero188 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource188 (mixedVector B) = 0 := by
  have h2059 : mixedVector B (Sum.inr 2059) = Sparse.eval nodeValue2059 (mixedVector B) := by
    change mixedMoment B node2059 node2059Labels = _
    exact sound2059 B hB hF
  have h2063 : mixedVector B (Sum.inr 2063) = Sparse.eval nodeValue2063 (mixedVector B) := by
    change mixedMoment B node2063 node2063Labels = _
    exact sound2063 B hB hF
  have h2064 : mixedVector B (Sum.inr 2064) = Sparse.eval nodeValue2064 (mixedVector B) := by
    change mixedMoment B node2064 node2064Labels = _
    exact sound2064 B hB hF
  have h2267 : mixedVector B (Sum.inr 2267) = Sparse.eval nodeValue2267 (mixedVector B) := by
    change mixedMoment B node2267 node2267Labels = _
    exact sound2267 B hB hF
  have h2670 : mixedVector B (Sum.inr 2670) = Sparse.eval nodeValue2670 (mixedVector B) := by
    change mixedMoment B node2670 node2670Labels = _
    exact sound2670 B hB hF
  have h2683 : mixedVector B (Sum.inr 2683) = Sparse.eval nodeValue2683 (mixedVector B) := by
    change mixedMoment B node2683 node2683Labels = _
    exact sound2683 B hB hF
  have h2685 : mixedVector B (Sum.inr 2685) = Sparse.eval nodeValue2685 (mixedVector B) := by
    change mixedMoment B node2685 node2685Labels = _
    exact sound2685 B hB hF
  have h2740 : mixedVector B (Sum.inr 2740) = Sparse.eval nodeValue2740 (mixedVector B) := by
    change mixedMoment B node2740 node2740Labels = _
    exact sound2740 B hB hF
  have h3015 : mixedVector B (Sum.inr 3015) = Sparse.eval nodeValue3015 (mixedVector B) := by
    change mixedMoment B node3015 node3015Labels = _
    exact sound3015 B hB hF
  have h3022 : mixedVector B (Sum.inr 3022) = Sparse.eval nodeValue3022 (mixedVector B) := by
    change mixedMoment B node3022 node3022Labels = _
    exact sound3022 B hB hF
  have h3024 : mixedVector B (Sum.inr 3024) = Sparse.eval nodeValue3024 (mixedVector B) := by
    change mixedMoment B node3024 node3024Labels = _
    exact sound3024 B hB hF
  have h3035 : mixedVector B (Sum.inr 3035) = Sparse.eval nodeValue3035 (mixedVector B) := by
    change mixedMoment B node3035 node3035Labels = _
    exact sound3035 B hB hF
  have h3038 : mixedVector B (Sum.inr 3038) = Sparse.eval nodeValue3038 (mixedVector B) := by
    change mixedMoment B node3038 node3038Labels = _
    exact sound3038 B hB hF
  have h3049 : mixedVector B (Sum.inr 3049) = Sparse.eval nodeValue3049 (mixedVector B) := by
    change mixedMoment B node3049 node3049Labels = _
    exact sound3049 B hB hF
  have h3054 : mixedVector B (Sum.inr 3054) = Sparse.eval nodeValue3054 (mixedVector B) := by
    change mixedMoment B node3054 node3054Labels = _
    exact sound3054 B hB hF
  have h3075 : mixedVector B (Sum.inr 3075) = Sparse.eval nodeValue3075 (mixedVector B) := by
    change mixedMoment B node3075 node3075Labels = _
    exact sound3075 B hB hF
  have h3098 : mixedVector B (Sum.inr 3098) = Sparse.eval nodeValue3098 (mixedVector B) := by
    change mixedMoment B node3098 node3098Labels = _
    exact sound3098 B hB hF
  have h3101 : mixedVector B (Sum.inr 3101) = Sparse.eval nodeValue3101 (mixedVector B) := by
    change mixedMoment B node3101 node3101Labels = _
    exact sound3101 B hB hF
  have h3156 : mixedVector B (Sum.inr 3156) = Sparse.eval nodeValue3156 (mixedVector B) := by
    change mixedMoment B node3156 node3156Labels = _
    exact sound3156 B hB hF
  have h3161 : mixedVector B (Sum.inr 3161) = Sparse.eval nodeValue3161 (mixedVector B) := by
    change mixedMoment B node3161 node3161Labels = _
    exact sound3161 B hB hF
  have h3224 : mixedVector B (Sum.inr 3224) = Sparse.eval nodeValue3224 (mixedVector B) := by
    change mixedMoment B node3224 node3224Labels = _
    exact sound3224 B hB hF
  simpa only [sourceForm222, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2059, h2063, h2064, h2267, h2670, h2683, h2685, h2740, h3015, h3022, h3024, h3035, h3038, h3049, h3054, h3075, h3098, h3101, h3156, h3161, h3224, reducedSource188] using sourceEq222 B hB

theorem rowSound188 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row188 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck188, numericCheck188, reducedZero188 B hB hF, mul_zero]

theorem reducedZero189 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource189 (mixedVector B) = 0 := by
  have h2279 : mixedVector B (Sum.inr 2279) = Sparse.eval nodeValue2279 (mixedVector B) := by
    change mixedMoment B node2279 node2279Labels = _
    exact sound2279 B hB hF
  have h2744 : mixedVector B (Sum.inr 2744) = Sparse.eval nodeValue2744 (mixedVector B) := by
    change mixedMoment B node2744 node2744Labels = _
    exact sound2744 B hB hF
  have h3541 : mixedVector B (Sum.inr 3541) = Sparse.eval nodeValue3541 (mixedVector B) := by
    change mixedMoment B node3541 node3541Labels = _
    exact sound3541 B hB hF
  have h3626 : mixedVector B (Sum.inr 3626) = Sparse.eval nodeValue3626 (mixedVector B) := by
    change mixedMoment B node3626 node3626Labels = _
    exact sound3626 B hB hF
  have h3632 : mixedVector B (Sum.inr 3632) = Sparse.eval nodeValue3632 (mixedVector B) := by
    change mixedMoment B node3632 node3632Labels = _
    exact sound3632 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm223, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2279, h2744, h3541, h3626, h3632, h4084, reducedSource189] using sourceEq223 B hB

theorem rowSound189 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row189 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck189, numericCheck189, reducedZero189 B hB hF, mul_zero]

theorem reducedZero190 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource190 (mixedVector B) = 0 := by
  have h1238 : mixedVector B (Sum.inr 1238) = Sparse.eval nodeValue1238 (mixedVector B) := by
    change mixedMoment B node1238 node1238Labels = _
    exact sound1238 B hB hF
  have h1244 : mixedVector B (Sum.inr 1244) = Sparse.eval nodeValue1244 (mixedVector B) := by
    change mixedMoment B node1244 node1244Labels = _
    exact sound1244 B hB hF
  have h1245 : mixedVector B (Sum.inr 1245) = Sparse.eval nodeValue1245 (mixedVector B) := by
    change mixedMoment B node1245 node1245Labels = _
    exact sound1245 B hB hF
  have h1296 : mixedVector B (Sum.inr 1296) = Sparse.eval nodeValue1296 (mixedVector B) := by
    change mixedMoment B node1296 node1296Labels = _
    exact sound1296 B hB hF
  have h2744 : mixedVector B (Sum.inr 2744) = Sparse.eval nodeValue2744 (mixedVector B) := by
    change mixedMoment B node2744 node2744Labels = _
    exact sound2744 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm224, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1238, h1244, h1245, h1296, h2744, h4084, reducedSource190] using sourceEq224 B hB

theorem rowSound190 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row190 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck190, numericCheck190, reducedZero190 B hB hF, mul_zero]

theorem reducedZero191 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource191 (mixedVector B) = 0 := by
  have h1296 : mixedVector B (Sum.inr 1296) = Sparse.eval nodeValue1296 (mixedVector B) := by
    change mixedMoment B node1296 node1296Labels = _
    exact sound1296 B hB hF
  have h2138 : mixedVector B (Sum.inr 2138) = Sparse.eval nodeValue2138 (mixedVector B) := by
    change mixedMoment B node2138 node2138Labels = _
    exact sound2138 B hB hF
  have h2592 : mixedVector B (Sum.inr 2592) = Sparse.eval nodeValue2592 (mixedVector B) := by
    change mixedMoment B node2592 node2592Labels = _
    exact sound2592 B hB hF
  have h2744 : mixedVector B (Sum.inr 2744) = Sparse.eval nodeValue2744 (mixedVector B) := by
    change mixedMoment B node2744 node2744Labels = _
    exact sound2744 B hB hF
  have h2781 : mixedVector B (Sum.inr 2781) = Sparse.eval nodeValue2781 (mixedVector B) := by
    change mixedMoment B node2781 node2781Labels = _
    exact sound2781 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm225, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1296, h2138, h2592, h2744, h2781, h4084, reducedSource191] using sourceEq225 B hB

theorem rowSound191 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row191 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck191, numericCheck191, reducedZero191 B hB hF, mul_zero]

theorem sourceRowsAt176 : MixedData.sourceRows (176 : Fin 2425) =
    MixedData.row176 := by decide +kernel

theorem sourceRowsAt177 : MixedData.sourceRows (177 : Fin 2425) =
    MixedData.row177 := by decide +kernel

theorem sourceRowsAt178 : MixedData.sourceRows (178 : Fin 2425) =
    MixedData.row178 := by decide +kernel

theorem sourceRowsAt179 : MixedData.sourceRows (179 : Fin 2425) =
    MixedData.row179 := by decide +kernel

theorem sourceRowsAt180 : MixedData.sourceRows (180 : Fin 2425) =
    MixedData.row180 := by decide +kernel

theorem sourceRowsAt181 : MixedData.sourceRows (181 : Fin 2425) =
    MixedData.row181 := by decide +kernel

theorem sourceRowsAt182 : MixedData.sourceRows (182 : Fin 2425) =
    MixedData.row182 := by decide +kernel

theorem sourceRowsAt183 : MixedData.sourceRows (183 : Fin 2425) =
    MixedData.row183 := by decide +kernel

theorem sourceRowsAt184 : MixedData.sourceRows (184 : Fin 2425) =
    MixedData.row184 := by decide +kernel

theorem sourceRowsAt185 : MixedData.sourceRows (185 : Fin 2425) =
    MixedData.row185 := by decide +kernel

theorem sourceRowsAt186 : MixedData.sourceRows (186 : Fin 2425) =
    MixedData.row186 := by decide +kernel

theorem sourceRowsAt187 : MixedData.sourceRows (187 : Fin 2425) =
    MixedData.row187 := by decide +kernel

theorem sourceRowsAt188 : MixedData.sourceRows (188 : Fin 2425) =
    MixedData.row188 := by decide +kernel

theorem sourceRowsAt189 : MixedData.sourceRows (189 : Fin 2425) =
    MixedData.row189 := by decide +kernel

theorem sourceRowsAt190 : MixedData.sourceRows (190 : Fin 2425) =
    MixedData.row190 := by decide +kernel

theorem sourceRowsAt191 : MixedData.sourceRows (191 : Fin 2425) =
    MixedData.row191 := by decide +kernel

theorem chunkSound11 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 11) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 176 ∨ k.val = 177 ∨ k.val = 178 ∨ k.val = 179 ∨ k.val = 180 ∨ k.val = 181 ∨ k.val = 182 ∨ k.val = 183 ∨ k.val = 184 ∨ k.val = 185 ∨ k.val = 186 ∨ k.val = 187 ∨ k.val = 188 ∨ k.val = 189 ∨ k.val = 190 ∨ k.val = 191 := by omega
  rcases heq with h176 | h177 | h178 | h179 | h180 | h181 | h182 | h183 | h184 | h185 | h186 | h187 | h188 | h189 | h190 | h191
  · have he : k = (176 : Fin 2425) := Fin.ext h176
    subst k
    rw [sourceRowsAt176]
    exact rowSound176 B hB hF
  · have he : k = (177 : Fin 2425) := Fin.ext h177
    subst k
    rw [sourceRowsAt177]
    exact rowSound177 B hB hF
  · have he : k = (178 : Fin 2425) := Fin.ext h178
    subst k
    rw [sourceRowsAt178]
    exact rowSound178 B hB hF
  · have he : k = (179 : Fin 2425) := Fin.ext h179
    subst k
    rw [sourceRowsAt179]
    exact rowSound179 B hB hF
  · have he : k = (180 : Fin 2425) := Fin.ext h180
    subst k
    rw [sourceRowsAt180]
    exact rowSound180 B hB hF
  · have he : k = (181 : Fin 2425) := Fin.ext h181
    subst k
    rw [sourceRowsAt181]
    exact rowSound181 B hB hF
  · have he : k = (182 : Fin 2425) := Fin.ext h182
    subst k
    rw [sourceRowsAt182]
    exact rowSound182 B hB hF
  · have he : k = (183 : Fin 2425) := Fin.ext h183
    subst k
    rw [sourceRowsAt183]
    exact rowSound183 B hB hF
  · have he : k = (184 : Fin 2425) := Fin.ext h184
    subst k
    rw [sourceRowsAt184]
    exact rowSound184 B hB hF
  · have he : k = (185 : Fin 2425) := Fin.ext h185
    subst k
    rw [sourceRowsAt185]
    exact rowSound185 B hB hF
  · have he : k = (186 : Fin 2425) := Fin.ext h186
    subst k
    rw [sourceRowsAt186]
    exact rowSound186 B hB hF
  · have he : k = (187 : Fin 2425) := Fin.ext h187
    subst k
    rw [sourceRowsAt187]
    exact rowSound187 B hB hF
  · have he : k = (188 : Fin 2425) := Fin.ext h188
    subst k
    rw [sourceRowsAt188]
    exact rowSound188 B hB hF
  · have he : k = (189 : Fin 2425) := Fin.ext h189
    subst k
    rw [sourceRowsAt189]
    exact rowSound189 B hB hF
  · have he : k = (190 : Fin 2425) := Fin.ext h190
    subst k
    rw [sourceRowsAt190]
    exact rowSound190 B hB hF
  · have he : k = (191 : Fin 2425) := Fin.ext h191
    subst k
    rw [sourceRowsAt191]
    exact rowSound191 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
