import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources9

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero256 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource256 (mixedVector B) = 0 := by
  have h3039 : mixedVector B (Sum.inr 3039) = Sparse.eval nodeValue3039 (mixedVector B) := by
    change mixedMoment B node3039 node3039Labels = _
    exact sound3039 B hB hF
  have h3880 : mixedVector B (Sum.inr 3880) = Sparse.eval nodeValue3880 (mixedVector B) := by
    change mixedMoment B node3880 node3880Labels = _
    exact sound3880 B hB hF
  have h3881 : mixedVector B (Sum.inr 3881) = Sparse.eval nodeValue3881 (mixedVector B) := by
    change mixedMoment B node3881 node3881Labels = _
    exact sound3881 B hB hF
  have h3885 : mixedVector B (Sum.inr 3885) = Sparse.eval nodeValue3885 (mixedVector B) := by
    change mixedMoment B node3885 node3885Labels = _
    exact sound3885 B hB hF
  have h3910 : mixedVector B (Sum.inr 3910) = Sparse.eval nodeValue3910 (mixedVector B) := by
    change mixedMoment B node3910 node3910Labels = _
    exact sound3910 B hB hF
  have h3958 : mixedVector B (Sum.inr 3958) = Sparse.eval nodeValue3958 (mixedVector B) := by
    change mixedMoment B node3958 node3958Labels = _
    exact sound3958 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm305, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3039, h3880, h3881, h3885, h3910, h3958, h4091, reducedSource256] using sourceEq305 B hB

theorem rowSound256 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row256 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck256, numericCheck256, reducedZero256 B hB hF, mul_zero]

theorem reducedZero257 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource257 (mixedVector B) = 0 := by
  have h1358 : mixedVector B (Sum.inr 1358) = Sparse.eval nodeValue1358 (mixedVector B) := by
    change mixedMoment B node1358 node1358Labels = _
    exact sound1358 B hB hF
  have h1361 : mixedVector B (Sum.inr 1361) = Sparse.eval nodeValue1361 (mixedVector B) := by
    change mixedMoment B node1361 node1361Labels = _
    exact sound1361 B hB hF
  have h1363 : mixedVector B (Sum.inr 1363) = Sparse.eval nodeValue1363 (mixedVector B) := by
    change mixedMoment B node1363 node1363Labels = _
    exact sound1363 B hB hF
  have h1370 : mixedVector B (Sum.inr 1370) = Sparse.eval nodeValue1370 (mixedVector B) := by
    change mixedMoment B node1370 node1370Labels = _
    exact sound1370 B hB hF
  have h1423 : mixedVector B (Sum.inr 1423) = Sparse.eval nodeValue1423 (mixedVector B) := by
    change mixedMoment B node1423 node1423Labels = _
    exact sound1423 B hB hF
  have h3039 : mixedVector B (Sum.inr 3039) = Sparse.eval nodeValue3039 (mixedVector B) := by
    change mixedMoment B node3039 node3039Labels = _
    exact sound3039 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm306, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1358, h1361, h1363, h1370, h1423, h3039, h4091, reducedSource257] using sourceEq306 B hB

theorem rowSound257 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row257 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck257, numericCheck257, reducedZero257 B hB hF, mul_zero]

theorem reducedZero258 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource258 (mixedVector B) = 0 := by
  have h1370 : mixedVector B (Sum.inr 1370) = Sparse.eval nodeValue1370 (mixedVector B) := by
    change mixedMoment B node1370 node1370Labels = _
    exact sound1370 B hB hF
  have h2884 : mixedVector B (Sum.inr 2884) = Sparse.eval nodeValue2884 (mixedVector B) := by
    change mixedMoment B node2884 node2884Labels = _
    exact sound2884 B hB hF
  have h2976 : mixedVector B (Sum.inr 2976) = Sparse.eval nodeValue2976 (mixedVector B) := by
    change mixedMoment B node2976 node2976Labels = _
    exact sound2976 B hB hF
  have h3039 : mixedVector B (Sum.inr 3039) = Sparse.eval nodeValue3039 (mixedVector B) := by
    change mixedMoment B node3039 node3039Labels = _
    exact sound3039 B hB hF
  have h3053 : mixedVector B (Sum.inr 3053) = Sparse.eval nodeValue3053 (mixedVector B) := by
    change mixedMoment B node3053 node3053Labels = _
    exact sound3053 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm307, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1370, h2884, h2976, h3039, h3053, h4091, reducedSource258] using sourceEq307 B hB

theorem rowSound258 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row258 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck258, numericCheck258, reducedZero258 B hB hF, mul_zero]

theorem reducedZero259 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource259 (mixedVector B) = 0 := by
  have h2627 : mixedVector B (Sum.inr 2627) = Sparse.eval nodeValue2627 (mixedVector B) := by
    change mixedMoment B node2627 node2627Labels = _
    exact sound2627 B hB hF
  have h2946 : mixedVector B (Sum.inr 2946) = Sparse.eval nodeValue2946 (mixedVector B) := by
    change mixedMoment B node2946 node2946Labels = _
    exact sound2946 B hB hF
  have h3008 : mixedVector B (Sum.inr 3008) = Sparse.eval nodeValue3008 (mixedVector B) := by
    change mixedMoment B node3008 node3008Labels = _
    exact sound3008 B hB hF
  have h3011 : mixedVector B (Sum.inr 3011) = Sparse.eval nodeValue3011 (mixedVector B) := by
    change mixedMoment B node3011 node3011Labels = _
    exact sound3011 B hB hF
  have h3039 : mixedVector B (Sum.inr 3039) = Sparse.eval nodeValue3039 (mixedVector B) := by
    change mixedMoment B node3039 node3039Labels = _
    exact sound3039 B hB hF
  have h3881 : mixedVector B (Sum.inr 3881) = Sparse.eval nodeValue3881 (mixedVector B) := by
    change mixedMoment B node3881 node3881Labels = _
    exact sound3881 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm308, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2627, h2946, h3008, h3011, h3039, h3881, h4091, reducedSource259] using sourceEq308 B hB

theorem rowSound259 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row259 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck259, numericCheck259, reducedZero259 B hB hF, mul_zero]

theorem reducedZero260 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource260 (mixedVector B) = 0 := by
  have h1358 : mixedVector B (Sum.inr 1358) = Sparse.eval nodeValue1358 (mixedVector B) := by
    change mixedMoment B node1358 node1358Labels = _
    exact sound1358 B hB hF
  have h2862 : mixedVector B (Sum.inr 2862) = Sparse.eval nodeValue2862 (mixedVector B) := by
    change mixedMoment B node2862 node2862Labels = _
    exact sound2862 B hB hF
  have h3008 : mixedVector B (Sum.inr 3008) = Sparse.eval nodeValue3008 (mixedVector B) := by
    change mixedMoment B node3008 node3008Labels = _
    exact sound3008 B hB hF
  have h3029 : mixedVector B (Sum.inr 3029) = Sparse.eval nodeValue3029 (mixedVector B) := by
    change mixedMoment B node3029 node3029Labels = _
    exact sound3029 B hB hF
  have h3037 : mixedVector B (Sum.inr 3037) = Sparse.eval nodeValue3037 (mixedVector B) := by
    change mixedMoment B node3037 node3037Labels = _
    exact sound3037 B hB hF
  have h3039 : mixedVector B (Sum.inr 3039) = Sparse.eval nodeValue3039 (mixedVector B) := by
    change mixedMoment B node3039 node3039Labels = _
    exact sound3039 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm309, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1358, h2862, h3008, h3029, h3037, h3039, h4091, reducedSource260] using sourceEq309 B hB

theorem rowSound260 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row260 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck260, numericCheck260, reducedZero260 B hB hF, mul_zero]

theorem reducedZero261 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource261 (mixedVector B) = 0 := by
  have h2625 : mixedVector B (Sum.inr 2625) = Sparse.eval nodeValue2625 (mixedVector B) := by
    change mixedMoment B node2625 node2625Labels = _
    exact sound2625 B hB hF
  have h2918 : mixedVector B (Sum.inr 2918) = Sparse.eval nodeValue2918 (mixedVector B) := by
    change mixedMoment B node2918 node2918Labels = _
    exact sound2918 B hB hF
  have h2972 : mixedVector B (Sum.inr 2972) = Sparse.eval nodeValue2972 (mixedVector B) := by
    change mixedMoment B node2972 node2972Labels = _
    exact sound2972 B hB hF
  have h2976 : mixedVector B (Sum.inr 2976) = Sparse.eval nodeValue2976 (mixedVector B) := by
    change mixedMoment B node2976 node2976Labels = _
    exact sound2976 B hB hF
  have h3039 : mixedVector B (Sum.inr 3039) = Sparse.eval nodeValue3039 (mixedVector B) := by
    change mixedMoment B node3039 node3039Labels = _
    exact sound3039 B hB hF
  have h3880 : mixedVector B (Sum.inr 3880) = Sparse.eval nodeValue3880 (mixedVector B) := by
    change mixedMoment B node3880 node3880Labels = _
    exact sound3880 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm310, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2625, h2918, h2972, h2976, h3039, h3880, h4091, reducedSource261] using sourceEq310 B hB

theorem rowSound261 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row261 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck261, numericCheck261, reducedZero261 B hB hF, mul_zero]

theorem reducedZero262 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource262 (mixedVector B) = 0 := by
  have h1423 : mixedVector B (Sum.inr 1423) = Sparse.eval nodeValue1423 (mixedVector B) := by
    change mixedMoment B node1423 node1423Labels = _
    exact sound1423 B hB hF
  have h2625 : mixedVector B (Sum.inr 2625) = Sparse.eval nodeValue2625 (mixedVector B) := by
    change mixedMoment B node2625 node2625Labels = _
    exact sound2625 B hB hF
  have h2627 : mixedVector B (Sum.inr 2627) = Sparse.eval nodeValue2627 (mixedVector B) := by
    change mixedMoment B node2627 node2627Labels = _
    exact sound2627 B hB hF
  have h2641 : mixedVector B (Sum.inr 2641) = Sparse.eval nodeValue2641 (mixedVector B) := by
    change mixedMoment B node2641 node2641Labels = _
    exact sound2641 B hB hF
  have h2754 : mixedVector B (Sum.inr 2754) = Sparse.eval nodeValue2754 (mixedVector B) := by
    change mixedMoment B node2754 node2754Labels = _
    exact sound2754 B hB hF
  have h3039 : mixedVector B (Sum.inr 3039) = Sparse.eval nodeValue3039 (mixedVector B) := by
    change mixedMoment B node3039 node3039Labels = _
    exact sound3039 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm311, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1423, h2625, h2627, h2641, h2754, h3039, h4091, reducedSource262] using sourceEq311 B hB

theorem rowSound262 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row262 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck262, numericCheck262, reducedZero262 B hB hF, mul_zero]

theorem reducedZero263 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource263 (mixedVector B) = 0 := by
  have h2862 : mixedVector B (Sum.inr 2862) = Sparse.eval nodeValue2862 (mixedVector B) := by
    change mixedMoment B node2862 node2862Labels = _
    exact sound2862 B hB hF
  have h2865 : mixedVector B (Sum.inr 2865) = Sparse.eval nodeValue2865 (mixedVector B) := by
    change mixedMoment B node2865 node2865Labels = _
    exact sound2865 B hB hF
  have h2868 : mixedVector B (Sum.inr 2868) = Sparse.eval nodeValue2868 (mixedVector B) := by
    change mixedMoment B node2868 node2868Labels = _
    exact sound2868 B hB hF
  have h2884 : mixedVector B (Sum.inr 2884) = Sparse.eval nodeValue2884 (mixedVector B) := by
    change mixedMoment B node2884 node2884Labels = _
    exact sound2884 B hB hF
  have h3039 : mixedVector B (Sum.inr 3039) = Sparse.eval nodeValue3039 (mixedVector B) := by
    change mixedMoment B node3039 node3039Labels = _
    exact sound3039 B hB hF
  have h3958 : mixedVector B (Sum.inr 3958) = Sparse.eval nodeValue3958 (mixedVector B) := by
    change mixedMoment B node3958 node3958Labels = _
    exact sound3958 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm312, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2862, h2865, h2868, h2884, h3039, h3958, h4091, reducedSource263] using sourceEq312 B hB

theorem rowSound263 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row263 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck263, numericCheck263, reducedZero263 B hB hF, mul_zero]

theorem reducedZero264 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource264 (mixedVector B) = 0 := by
  have h1363 : mixedVector B (Sum.inr 1363) = Sparse.eval nodeValue1363 (mixedVector B) := by
    change mixedMoment B node1363 node1363Labels = _
    exact sound1363 B hB hF
  have h2868 : mixedVector B (Sum.inr 2868) = Sparse.eval nodeValue2868 (mixedVector B) := by
    change mixedMoment B node2868 node2868Labels = _
    exact sound2868 B hB hF
  have h2972 : mixedVector B (Sum.inr 2972) = Sparse.eval nodeValue2972 (mixedVector B) := by
    change mixedMoment B node2972 node2972Labels = _
    exact sound2972 B hB hF
  have h3011 : mixedVector B (Sum.inr 3011) = Sparse.eval nodeValue3011 (mixedVector B) := by
    change mixedMoment B node3011 node3011Labels = _
    exact sound3011 B hB hF
  have h3039 : mixedVector B (Sum.inr 3039) = Sparse.eval nodeValue3039 (mixedVector B) := by
    change mixedMoment B node3039 node3039Labels = _
    exact sound3039 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm313, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1363, h2868, h2972, h3011, h3039, h4091, reducedSource264] using sourceEq313 B hB

theorem rowSound264 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row264 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck264, numericCheck264, reducedZero264 B hB hF, mul_zero]

theorem reducedZero265 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource265 (mixedVector B) = 0 := by
  have h2641 : mixedVector B (Sum.inr 2641) = Sparse.eval nodeValue2641 (mixedVector B) := by
    change mixedMoment B node2641 node2641Labels = _
    exact sound2641 B hB hF
  have h3029 : mixedVector B (Sum.inr 3029) = Sparse.eval nodeValue3029 (mixedVector B) := by
    change mixedMoment B node3029 node3029Labels = _
    exact sound3029 B hB hF
  have h3031 : mixedVector B (Sum.inr 3031) = Sparse.eval nodeValue3031 (mixedVector B) := by
    change mixedMoment B node3031 node3031Labels = _
    exact sound3031 B hB hF
  have h3039 : mixedVector B (Sum.inr 3039) = Sparse.eval nodeValue3039 (mixedVector B) := by
    change mixedMoment B node3039 node3039Labels = _
    exact sound3039 B hB hF
  have h3885 : mixedVector B (Sum.inr 3885) = Sparse.eval nodeValue3885 (mixedVector B) := by
    change mixedMoment B node3885 node3885Labels = _
    exact sound3885 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm314, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2641, h3029, h3031, h3039, h3885, h4091, reducedSource265] using sourceEq314 B hB

theorem rowSound265 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row265 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck265, numericCheck265, reducedZero265 B hB hF, mul_zero]

theorem reducedZero266 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource266 (mixedVector B) = 0 := by
  have h1361 : mixedVector B (Sum.inr 1361) = Sparse.eval nodeValue1361 (mixedVector B) := by
    change mixedMoment B node1361 node1361Labels = _
    exact sound1361 B hB hF
  have h2865 : mixedVector B (Sum.inr 2865) = Sparse.eval nodeValue2865 (mixedVector B) := by
    change mixedMoment B node2865 node2865Labels = _
    exact sound2865 B hB hF
  have h2918 : mixedVector B (Sum.inr 2918) = Sparse.eval nodeValue2918 (mixedVector B) := by
    change mixedMoment B node2918 node2918Labels = _
    exact sound2918 B hB hF
  have h2946 : mixedVector B (Sum.inr 2946) = Sparse.eval nodeValue2946 (mixedVector B) := by
    change mixedMoment B node2946 node2946Labels = _
    exact sound2946 B hB hF
  have h3031 : mixedVector B (Sum.inr 3031) = Sparse.eval nodeValue3031 (mixedVector B) := by
    change mixedMoment B node3031 node3031Labels = _
    exact sound3031 B hB hF
  have h3039 : mixedVector B (Sum.inr 3039) = Sparse.eval nodeValue3039 (mixedVector B) := by
    change mixedMoment B node3039 node3039Labels = _
    exact sound3039 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm315, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1361, h2865, h2918, h2946, h3031, h3039, h4091, reducedSource266] using sourceEq315 B hB

theorem rowSound266 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row266 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck266, numericCheck266, reducedZero266 B hB hF, mul_zero]

theorem reducedZero267 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource267 (mixedVector B) = 0 := by
  have h4803 : mixedVector B (Sum.inr 4803) = Sparse.eval nodeValue4803 (mixedVector B) := by
    change mixedMoment B node4803 node4803Labels = _
    exact sound4803 B hB hF
  have h4808 : mixedVector B (Sum.inr 4808) = Sparse.eval nodeValue4808 (mixedVector B) := by
    change mixedMoment B node4808 node4808Labels = _
    exact sound4808 B hB hF
  have h4810 : mixedVector B (Sum.inr 4810) = Sparse.eval nodeValue4810 (mixedVector B) := by
    change mixedMoment B node4810 node4810Labels = _
    exact sound4810 B hB hF
  have h4839 : mixedVector B (Sum.inr 4839) = Sparse.eval nodeValue4839 (mixedVector B) := by
    change mixedMoment B node4839 node4839Labels = _
    exact sound4839 B hB hF
  have h4854 : mixedVector B (Sum.inr 4854) = Sparse.eval nodeValue4854 (mixedVector B) := by
    change mixedMoment B node4854 node4854Labels = _
    exact sound4854 B hB hF
  have h4855 : mixedVector B (Sum.inr 4855) = Sparse.eval nodeValue4855 (mixedVector B) := by
    change mixedMoment B node4855 node4855Labels = _
    exact sound4855 B hB hF
  have h4870 : mixedVector B (Sum.inr 4870) = Sparse.eval nodeValue4870 (mixedVector B) := by
    change mixedMoment B node4870 node4870Labels = _
    exact sound4870 B hB hF
  have h4880 : mixedVector B (Sum.inr 4880) = Sparse.eval nodeValue4880 (mixedVector B) := by
    change mixedMoment B node4880 node4880Labels = _
    exact sound4880 B hB hF
  have h4896 : mixedVector B (Sum.inr 4896) = Sparse.eval nodeValue4896 (mixedVector B) := by
    change mixedMoment B node4896 node4896Labels = _
    exact sound4896 B hB hF
  have h5220 : mixedVector B (Sum.inr 5220) = Sparse.eval nodeValue5220 (mixedVector B) := by
    change mixedMoment B node5220 node5220Labels = _
    exact sound5220 B hB hF
  have h5223 : mixedVector B (Sum.inr 5223) = Sparse.eval nodeValue5223 (mixedVector B) := by
    change mixedMoment B node5223 node5223Labels = _
    exact sound5223 B hB hF
  have h5228 : mixedVector B (Sum.inr 5228) = Sparse.eval nodeValue5228 (mixedVector B) := by
    change mixedMoment B node5228 node5228Labels = _
    exact sound5228 B hB hF
  have h5229 : mixedVector B (Sum.inr 5229) = Sparse.eval nodeValue5229 (mixedVector B) := by
    change mixedMoment B node5229 node5229Labels = _
    exact sound5229 B hB hF
  have h5232 : mixedVector B (Sum.inr 5232) = Sparse.eval nodeValue5232 (mixedVector B) := by
    change mixedMoment B node5232 node5232Labels = _
    exact sound5232 B hB hF
  have h5233 : mixedVector B (Sum.inr 5233) = Sparse.eval nodeValue5233 (mixedVector B) := by
    change mixedMoment B node5233 node5233Labels = _
    exact sound5233 B hB hF
  have h5243 : mixedVector B (Sum.inr 5243) = Sparse.eval nodeValue5243 (mixedVector B) := by
    change mixedMoment B node5243 node5243Labels = _
    exact sound5243 B hB hF
  have h5244 : mixedVector B (Sum.inr 5244) = Sparse.eval nodeValue5244 (mixedVector B) := by
    change mixedMoment B node5244 node5244Labels = _
    exact sound5244 B hB hF
  have h5250 : mixedVector B (Sum.inr 5250) = Sparse.eval nodeValue5250 (mixedVector B) := by
    change mixedMoment B node5250 node5250Labels = _
    exact sound5250 B hB hF
  have h5253 : mixedVector B (Sum.inr 5253) = Sparse.eval nodeValue5253 (mixedVector B) := by
    change mixedMoment B node5253 node5253Labels = _
    exact sound5253 B hB hF
  have h5254 : mixedVector B (Sum.inr 5254) = Sparse.eval nodeValue5254 (mixedVector B) := by
    change mixedMoment B node5254 node5254Labels = _
    exact sound5254 B hB hF
  have h5258 : mixedVector B (Sum.inr 5258) = Sparse.eval nodeValue5258 (mixedVector B) := by
    change mixedMoment B node5258 node5258Labels = _
    exact sound5258 B hB hF
  have h5259 : mixedVector B (Sum.inr 5259) = Sparse.eval nodeValue5259 (mixedVector B) := by
    change mixedMoment B node5259 node5259Labels = _
    exact sound5259 B hB hF
  have h5264 : mixedVector B (Sum.inr 5264) = Sparse.eval nodeValue5264 (mixedVector B) := by
    change mixedMoment B node5264 node5264Labels = _
    exact sound5264 B hB hF
  have h5266 : mixedVector B (Sum.inr 5266) = Sparse.eval nodeValue5266 (mixedVector B) := by
    change mixedMoment B node5266 node5266Labels = _
    exact sound5266 B hB hF
  have h5267 : mixedVector B (Sum.inr 5267) = Sparse.eval nodeValue5267 (mixedVector B) := by
    change mixedMoment B node5267 node5267Labels = _
    exact sound5267 B hB hF
  have h5293 : mixedVector B (Sum.inr 5293) = Sparse.eval nodeValue5293 (mixedVector B) := by
    change mixedMoment B node5293 node5293Labels = _
    exact sound5293 B hB hF
  have h5300 : mixedVector B (Sum.inr 5300) = Sparse.eval nodeValue5300 (mixedVector B) := by
    change mixedMoment B node5300 node5300Labels = _
    exact sound5300 B hB hF
  have h5302 : mixedVector B (Sum.inr 5302) = Sparse.eval nodeValue5302 (mixedVector B) := by
    change mixedMoment B node5302 node5302Labels = _
    exact sound5302 B hB hF
  simpa only [sourceForm316, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4803, h4808, h4810, h4839, h4854, h4855, h4870, h4880, h4896, h5220, h5223, h5228, h5229, h5232, h5233, h5243, h5244, h5250, h5253, h5254, h5258, h5259, h5264, h5266, h5267, h5293, h5300, h5302, reducedSource267] using sourceEq316 B hB

theorem rowSound267 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row267 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck267, numericCheck267, reducedZero267 B hB hF, mul_zero]

theorem reducedZero268 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource268 (mixedVector B) = 0 := by
  have h2127 : mixedVector B (Sum.inr 2127) = Sparse.eval nodeValue2127 (mixedVector B) := by
    change mixedMoment B node2127 node2127Labels = _
    exact sound2127 B hB hF
  have h2128 : mixedVector B (Sum.inr 2128) = Sparse.eval nodeValue2128 (mixedVector B) := by
    change mixedMoment B node2128 node2128Labels = _
    exact sound2128 B hB hF
  have h2129 : mixedVector B (Sum.inr 2129) = Sparse.eval nodeValue2129 (mixedVector B) := by
    change mixedMoment B node2129 node2129Labels = _
    exact sound2129 B hB hF
  have h2133 : mixedVector B (Sum.inr 2133) = Sparse.eval nodeValue2133 (mixedVector B) := by
    change mixedMoment B node2133 node2133Labels = _
    exact sound2133 B hB hF
  have h2195 : mixedVector B (Sum.inr 2195) = Sparse.eval nodeValue2195 (mixedVector B) := by
    change mixedMoment B node2195 node2195Labels = _
    exact sound2195 B hB hF
  have h2215 : mixedVector B (Sum.inr 2215) = Sparse.eval nodeValue2215 (mixedVector B) := by
    change mixedMoment B node2215 node2215Labels = _
    exact sound2215 B hB hF
  have h2216 : mixedVector B (Sum.inr 2216) = Sparse.eval nodeValue2216 (mixedVector B) := by
    change mixedMoment B node2216 node2216Labels = _
    exact sound2216 B hB hF
  have h2220 : mixedVector B (Sum.inr 2220) = Sparse.eval nodeValue2220 (mixedVector B) := by
    change mixedMoment B node2220 node2220Labels = _
    exact sound2220 B hB hF
  have h2278 : mixedVector B (Sum.inr 2278) = Sparse.eval nodeValue2278 (mixedVector B) := by
    change mixedMoment B node2278 node2278Labels = _
    exact sound2278 B hB hF
  have h2665 : mixedVector B (Sum.inr 2665) = Sparse.eval nodeValue2665 (mixedVector B) := by
    change mixedMoment B node2665 node2665Labels = _
    exact sound2665 B hB hF
  have h2677 : mixedVector B (Sum.inr 2677) = Sparse.eval nodeValue2677 (mixedVector B) := by
    change mixedMoment B node2677 node2677Labels = _
    exact sound2677 B hB hF
  have h2678 : mixedVector B (Sum.inr 2678) = Sparse.eval nodeValue2678 (mixedVector B) := by
    change mixedMoment B node2678 node2678Labels = _
    exact sound2678 B hB hF
  have h2697 : mixedVector B (Sum.inr 2697) = Sparse.eval nodeValue2697 (mixedVector B) := by
    change mixedMoment B node2697 node2697Labels = _
    exact sound2697 B hB hF
  have h2698 : mixedVector B (Sum.inr 2698) = Sparse.eval nodeValue2698 (mixedVector B) := by
    change mixedMoment B node2698 node2698Labels = _
    exact sound2698 B hB hF
  have h2709 : mixedVector B (Sum.inr 2709) = Sparse.eval nodeValue2709 (mixedVector B) := by
    change mixedMoment B node2709 node2709Labels = _
    exact sound2709 B hB hF
  have h2713 : mixedVector B (Sum.inr 2713) = Sparse.eval nodeValue2713 (mixedVector B) := by
    change mixedMoment B node2713 node2713Labels = _
    exact sound2713 B hB hF
  have h2714 : mixedVector B (Sum.inr 2714) = Sparse.eval nodeValue2714 (mixedVector B) := by
    change mixedMoment B node2714 node2714Labels = _
    exact sound2714 B hB hF
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  have h2723 : mixedVector B (Sum.inr 2723) = Sparse.eval nodeValue2723 (mixedVector B) := by
    change mixedMoment B node2723 node2723Labels = _
    exact sound2723 B hB hF
  have h2729 : mixedVector B (Sum.inr 2729) = Sparse.eval nodeValue2729 (mixedVector B) := by
    change mixedMoment B node2729 node2729Labels = _
    exact sound2729 B hB hF
  have h2731 : mixedVector B (Sum.inr 2731) = Sparse.eval nodeValue2731 (mixedVector B) := by
    change mixedMoment B node2731 node2731Labels = _
    exact sound2731 B hB hF
  have h2732 : mixedVector B (Sum.inr 2732) = Sparse.eval nodeValue2732 (mixedVector B) := by
    change mixedMoment B node2732 node2732Labels = _
    exact sound2732 B hB hF
  have h2767 : mixedVector B (Sum.inr 2767) = Sparse.eval nodeValue2767 (mixedVector B) := by
    change mixedMoment B node2767 node2767Labels = _
    exact sound2767 B hB hF
  have h2774 : mixedVector B (Sum.inr 2774) = Sparse.eval nodeValue2774 (mixedVector B) := by
    change mixedMoment B node2774 node2774Labels = _
    exact sound2774 B hB hF
  have h2776 : mixedVector B (Sum.inr 2776) = Sparse.eval nodeValue2776 (mixedVector B) := by
    change mixedMoment B node2776 node2776Labels = _
    exact sound2776 B hB hF
  have h3044 : mixedVector B (Sum.inr 3044) = Sparse.eval nodeValue3044 (mixedVector B) := by
    change mixedMoment B node3044 node3044Labels = _
    exact sound3044 B hB hF
  have h3068 : mixedVector B (Sum.inr 3068) = Sparse.eval nodeValue3068 (mixedVector B) := by
    change mixedMoment B node3068 node3068Labels = _
    exact sound3068 B hB hF
  have h3088 : mixedVector B (Sum.inr 3088) = Sparse.eval nodeValue3088 (mixedVector B) := by
    change mixedMoment B node3088 node3088Labels = _
    exact sound3088 B hB hF
  have h3092 : mixedVector B (Sum.inr 3092) = Sparse.eval nodeValue3092 (mixedVector B) := by
    change mixedMoment B node3092 node3092Labels = _
    exact sound3092 B hB hF
  have h3094 : mixedVector B (Sum.inr 3094) = Sparse.eval nodeValue3094 (mixedVector B) := by
    change mixedMoment B node3094 node3094Labels = _
    exact sound3094 B hB hF
  simpa only [sourceForm317, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2127, h2128, h2129, h2133, h2195, h2215, h2216, h2220, h2278, h2665, h2677, h2678, h2697, h2698, h2709, h2713, h2714, h2722, h2723, h2729, h2731, h2732, h2767, h2774, h2776, h3044, h3068, h3088, h3092, h3094, reducedSource268] using sourceEq317 B hB

theorem rowSound268 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row268 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck268, numericCheck268, reducedZero268 B hB hF, mul_zero]

theorem reducedZero269 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource269 (mixedVector B) = 0 := by
  have h2091 : mixedVector B (Sum.inr 2091) = Sparse.eval nodeValue2091 (mixedVector B) := by
    change mixedMoment B node2091 node2091Labels = _
    exact sound2091 B hB hF
  have h2092 : mixedVector B (Sum.inr 2092) = Sparse.eval nodeValue2092 (mixedVector B) := by
    change mixedMoment B node2092 node2092Labels = _
    exact sound2092 B hB hF
  have h2093 : mixedVector B (Sum.inr 2093) = Sparse.eval nodeValue2093 (mixedVector B) := by
    change mixedMoment B node2093 node2093Labels = _
    exact sound2093 B hB hF
  have h2111 : mixedVector B (Sum.inr 2111) = Sparse.eval nodeValue2111 (mixedVector B) := by
    change mixedMoment B node2111 node2111Labels = _
    exact sound2111 B hB hF
  have h2254 : mixedVector B (Sum.inr 2254) = Sparse.eval nodeValue2254 (mixedVector B) := by
    change mixedMoment B node2254 node2254Labels = _
    exact sound2254 B hB hF
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
  have h2723 : mixedVector B (Sum.inr 2723) = Sparse.eval nodeValue2723 (mixedVector B) := by
    change mixedMoment B node2723 node2723Labels = _
    exact sound2723 B hB hF
  have h3016 : mixedVector B (Sum.inr 3016) = Sparse.eval nodeValue3016 (mixedVector B) := by
    change mixedMoment B node3016 node3016Labels = _
    exact sound3016 B hB hF
  have h3017 : mixedVector B (Sum.inr 3017) = Sparse.eval nodeValue3017 (mixedVector B) := by
    change mixedMoment B node3017 node3017Labels = _
    exact sound3017 B hB hF
  have h3019 : mixedVector B (Sum.inr 3019) = Sparse.eval nodeValue3019 (mixedVector B) := by
    change mixedMoment B node3019 node3019Labels = _
    exact sound3019 B hB hF
  have h3029 : mixedVector B (Sum.inr 3029) = Sparse.eval nodeValue3029 (mixedVector B) := by
    change mixedMoment B node3029 node3029Labels = _
    exact sound3029 B hB hF
  have h3030 : mixedVector B (Sum.inr 3030) = Sparse.eval nodeValue3030 (mixedVector B) := by
    change mixedMoment B node3030 node3030Labels = _
    exact sound3030 B hB hF
  have h3038 : mixedVector B (Sum.inr 3038) = Sparse.eval nodeValue3038 (mixedVector B) := by
    change mixedMoment B node3038 node3038Labels = _
    exact sound3038 B hB hF
  have h3039 : mixedVector B (Sum.inr 3039) = Sparse.eval nodeValue3039 (mixedVector B) := by
    change mixedMoment B node3039 node3039Labels = _
    exact sound3039 B hB hF
  have h3040 : mixedVector B (Sum.inr 3040) = Sparse.eval nodeValue3040 (mixedVector B) := by
    change mixedMoment B node3040 node3040Labels = _
    exact sound3040 B hB hF
  have h3044 : mixedVector B (Sum.inr 3044) = Sparse.eval nodeValue3044 (mixedVector B) := by
    change mixedMoment B node3044 node3044Labels = _
    exact sound3044 B hB hF
  have h3045 : mixedVector B (Sum.inr 3045) = Sparse.eval nodeValue3045 (mixedVector B) := by
    change mixedMoment B node3045 node3045Labels = _
    exact sound3045 B hB hF
  have h3054 : mixedVector B (Sum.inr 3054) = Sparse.eval nodeValue3054 (mixedVector B) := by
    change mixedMoment B node3054 node3054Labels = _
    exact sound3054 B hB hF
  have h3055 : mixedVector B (Sum.inr 3055) = Sparse.eval nodeValue3055 (mixedVector B) := by
    change mixedMoment B node3055 node3055Labels = _
    exact sound3055 B hB hF
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
  have h3202 : mixedVector B (Sum.inr 3202) = Sparse.eval nodeValue3202 (mixedVector B) := by
    change mixedMoment B node3202 node3202Labels = _
    exact sound3202 B hB hF
  have h3206 : mixedVector B (Sum.inr 3206) = Sparse.eval nodeValue3206 (mixedVector B) := by
    change mixedMoment B node3206 node3206Labels = _
    exact sound3206 B hB hF
  have h3210 : mixedVector B (Sum.inr 3210) = Sparse.eval nodeValue3210 (mixedVector B) := by
    change mixedMoment B node3210 node3210Labels = _
    exact sound3210 B hB hF
  have h3225 : mixedVector B (Sum.inr 3225) = Sparse.eval nodeValue3225 (mixedVector B) := by
    change mixedMoment B node3225 node3225Labels = _
    exact sound3225 B hB hF
  simpa only [sourceForm318, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2091, h2092, h2093, h2111, h2254, h2662, h2672, h2673, h2678, h2723, h3016, h3017, h3019, h3029, h3030, h3038, h3039, h3040, h3044, h3045, h3054, h3055, h3065, h3088, h3089, h3102, h3202, h3206, h3210, h3225, reducedSource269] using sourceEq318 B hB

theorem rowSound269 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row269 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck269, numericCheck269, reducedZero269 B hB hF, mul_zero]

theorem reducedZero270 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource270 (mixedVector B) = 0 := by
  have h3388 : mixedVector B (Sum.inr 3388) = Sparse.eval nodeValue3388 (mixedVector B) := by
    change mixedMoment B node3388 node3388Labels = _
    exact sound3388 B hB hF
  have h3391 : mixedVector B (Sum.inr 3391) = Sparse.eval nodeValue3391 (mixedVector B) := by
    change mixedMoment B node3391 node3391Labels = _
    exact sound3391 B hB hF
  have h3392 : mixedVector B (Sum.inr 3392) = Sparse.eval nodeValue3392 (mixedVector B) := by
    change mixedMoment B node3392 node3392Labels = _
    exact sound3392 B hB hF
  have h3395 : mixedVector B (Sum.inr 3395) = Sparse.eval nodeValue3395 (mixedVector B) := by
    change mixedMoment B node3395 node3395Labels = _
    exact sound3395 B hB hF
  have h3535 : mixedVector B (Sum.inr 3535) = Sparse.eval nodeValue3535 (mixedVector B) := by
    change mixedMoment B node3535 node3535Labels = _
    exact sound3535 B hB hF
  have h3544 : mixedVector B (Sum.inr 3544) = Sparse.eval nodeValue3544 (mixedVector B) := by
    change mixedMoment B node3544 node3544Labels = _
    exact sound3544 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm319, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3388, h3391, h3392, h3395, h3535, h3544, h4084, reducedSource270] using sourceEq319 B hB

theorem rowSound270 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row270 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck270, numericCheck270, reducedZero270 B hB hF, mul_zero]

theorem reducedZero271 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource271 (mixedVector B) = 0 := by
  have h2021 : mixedVector B (Sum.inr 2021) = Sparse.eval nodeValue2021 (mixedVector B) := by
    change mixedMoment B node2021 node2021Labels = _
    exact sound2021 B hB hF
  have h2026 : mixedVector B (Sum.inr 2026) = Sparse.eval nodeValue2026 (mixedVector B) := by
    change mixedMoment B node2026 node2026Labels = _
    exact sound2026 B hB hF
  have h2028 : mixedVector B (Sum.inr 2028) = Sparse.eval nodeValue2028 (mixedVector B) := by
    change mixedMoment B node2028 node2028Labels = _
    exact sound2028 B hB hF
  have h2058 : mixedVector B (Sum.inr 2058) = Sparse.eval nodeValue2058 (mixedVector B) := by
    change mixedMoment B node2058 node2058Labels = _
    exact sound2058 B hB hF
  have h2266 : mixedVector B (Sum.inr 2266) = Sparse.eval nodeValue2266 (mixedVector B) := by
    change mixedMoment B node2266 node2266Labels = _
    exact sound2266 B hB hF
  have h3535 : mixedVector B (Sum.inr 3535) = Sparse.eval nodeValue3535 (mixedVector B) := by
    change mixedMoment B node3535 node3535Labels = _
    exact sound3535 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm320, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2021, h2026, h2028, h2058, h2266, h3535, h4084, reducedSource271] using sourceEq320 B hB

theorem rowSound271 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row271 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck271, numericCheck271, reducedZero271 B hB hF, mul_zero]

theorem sourceRowsAt256 : MixedData.sourceRows (256 : Fin 2425) =
    MixedData.row256 := by decide +kernel

theorem sourceRowsAt257 : MixedData.sourceRows (257 : Fin 2425) =
    MixedData.row257 := by decide +kernel

theorem sourceRowsAt258 : MixedData.sourceRows (258 : Fin 2425) =
    MixedData.row258 := by decide +kernel

theorem sourceRowsAt259 : MixedData.sourceRows (259 : Fin 2425) =
    MixedData.row259 := by decide +kernel

theorem sourceRowsAt260 : MixedData.sourceRows (260 : Fin 2425) =
    MixedData.row260 := by decide +kernel

theorem sourceRowsAt261 : MixedData.sourceRows (261 : Fin 2425) =
    MixedData.row261 := by decide +kernel

theorem sourceRowsAt262 : MixedData.sourceRows (262 : Fin 2425) =
    MixedData.row262 := by decide +kernel

theorem sourceRowsAt263 : MixedData.sourceRows (263 : Fin 2425) =
    MixedData.row263 := by decide +kernel

theorem sourceRowsAt264 : MixedData.sourceRows (264 : Fin 2425) =
    MixedData.row264 := by decide +kernel

theorem sourceRowsAt265 : MixedData.sourceRows (265 : Fin 2425) =
    MixedData.row265 := by decide +kernel

theorem sourceRowsAt266 : MixedData.sourceRows (266 : Fin 2425) =
    MixedData.row266 := by decide +kernel

theorem sourceRowsAt267 : MixedData.sourceRows (267 : Fin 2425) =
    MixedData.row267 := by decide +kernel

theorem sourceRowsAt268 : MixedData.sourceRows (268 : Fin 2425) =
    MixedData.row268 := by decide +kernel

theorem sourceRowsAt269 : MixedData.sourceRows (269 : Fin 2425) =
    MixedData.row269 := by decide +kernel

theorem sourceRowsAt270 : MixedData.sourceRows (270 : Fin 2425) =
    MixedData.row270 := by decide +kernel

theorem sourceRowsAt271 : MixedData.sourceRows (271 : Fin 2425) =
    MixedData.row271 := by decide +kernel

theorem chunkSound16 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 16) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 256 ∨ k.val = 257 ∨ k.val = 258 ∨ k.val = 259 ∨ k.val = 260 ∨ k.val = 261 ∨ k.val = 262 ∨ k.val = 263 ∨ k.val = 264 ∨ k.val = 265 ∨ k.val = 266 ∨ k.val = 267 ∨ k.val = 268 ∨ k.val = 269 ∨ k.val = 270 ∨ k.val = 271 := by omega
  rcases heq with h256 | h257 | h258 | h259 | h260 | h261 | h262 | h263 | h264 | h265 | h266 | h267 | h268 | h269 | h270 | h271
  · have he : k = (256 : Fin 2425) := Fin.ext h256
    subst k
    rw [sourceRowsAt256]
    exact rowSound256 B hB hF
  · have he : k = (257 : Fin 2425) := Fin.ext h257
    subst k
    rw [sourceRowsAt257]
    exact rowSound257 B hB hF
  · have he : k = (258 : Fin 2425) := Fin.ext h258
    subst k
    rw [sourceRowsAt258]
    exact rowSound258 B hB hF
  · have he : k = (259 : Fin 2425) := Fin.ext h259
    subst k
    rw [sourceRowsAt259]
    exact rowSound259 B hB hF
  · have he : k = (260 : Fin 2425) := Fin.ext h260
    subst k
    rw [sourceRowsAt260]
    exact rowSound260 B hB hF
  · have he : k = (261 : Fin 2425) := Fin.ext h261
    subst k
    rw [sourceRowsAt261]
    exact rowSound261 B hB hF
  · have he : k = (262 : Fin 2425) := Fin.ext h262
    subst k
    rw [sourceRowsAt262]
    exact rowSound262 B hB hF
  · have he : k = (263 : Fin 2425) := Fin.ext h263
    subst k
    rw [sourceRowsAt263]
    exact rowSound263 B hB hF
  · have he : k = (264 : Fin 2425) := Fin.ext h264
    subst k
    rw [sourceRowsAt264]
    exact rowSound264 B hB hF
  · have he : k = (265 : Fin 2425) := Fin.ext h265
    subst k
    rw [sourceRowsAt265]
    exact rowSound265 B hB hF
  · have he : k = (266 : Fin 2425) := Fin.ext h266
    subst k
    rw [sourceRowsAt266]
    exact rowSound266 B hB hF
  · have he : k = (267 : Fin 2425) := Fin.ext h267
    subst k
    rw [sourceRowsAt267]
    exact rowSound267 B hB hF
  · have he : k = (268 : Fin 2425) := Fin.ext h268
    subst k
    rw [sourceRowsAt268]
    exact rowSound268 B hB hF
  · have he : k = (269 : Fin 2425) := Fin.ext h269
    subst k
    rw [sourceRowsAt269]
    exact rowSound269 B hB hF
  · have he : k = (270 : Fin 2425) := Fin.ext h270
    subst k
    rw [sourceRowsAt270]
    exact rowSound270 B hB hF
  · have he : k = (271 : Fin 2425) := Fin.ext h271
    subst k
    rw [sourceRowsAt271]
    exact rowSound271 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
