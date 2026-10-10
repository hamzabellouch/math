import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources27

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero752 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource752 (mixedVector B) = 0 := by
  have h2481 : mixedVector B (Sum.inr 2481) = Sparse.eval nodeValue2481 (mixedVector B) := by
    change mixedMoment B node2481 node2481Labels = _
    exact sound2481 B hB hF
  have h3691 : mixedVector B (Sum.inr 3691) = Sparse.eval nodeValue3691 (mixedVector B) := by
    change mixedMoment B node3691 node3691Labels = _
    exact sound3691 B hB hF
  have h3788 : mixedVector B (Sum.inr 3788) = Sparse.eval nodeValue3788 (mixedVector B) := by
    change mixedMoment B node3788 node3788Labels = _
    exact sound3788 B hB hF
  have h3803 : mixedVector B (Sum.inr 3803) = Sparse.eval nodeValue3803 (mixedVector B) := by
    change mixedMoment B node3803 node3803Labels = _
    exact sound3803 B hB hF
  have h3805 : mixedVector B (Sum.inr 3805) = Sparse.eval nodeValue3805 (mixedVector B) := by
    change mixedMoment B node3805 node3805Labels = _
    exact sound3805 B hB hF
  have h3809 : mixedVector B (Sum.inr 3809) = Sparse.eval nodeValue3809 (mixedVector B) := by
    change mixedMoment B node3809 node3809Labels = _
    exact sound3809 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm863, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2481, h3691, h3788, h3803, h3805, h3809, h4092, reducedSource752] using sourceEq863 B hB

theorem rowSound752 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row752 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck752, numericCheck752, reducedZero752 B hB hF, mul_zero]

theorem reducedZero753 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource753 (mixedVector B) = 0 := by
  have h2474 : mixedVector B (Sum.inr 2474) = Sparse.eval nodeValue2474 (mixedVector B) := by
    change mixedMoment B node2474 node2474Labels = _
    exact sound2474 B hB hF
  have h2475 : mixedVector B (Sum.inr 2475) = Sparse.eval nodeValue2475 (mixedVector B) := by
    change mixedMoment B node2475 node2475Labels = _
    exact sound2475 B hB hF
  have h2481 : mixedVector B (Sum.inr 2481) = Sparse.eval nodeValue2481 (mixedVector B) := by
    change mixedMoment B node2481 node2481Labels = _
    exact sound2481 B hB hF
  have h2494 : mixedVector B (Sum.inr 2494) = Sparse.eval nodeValue2494 (mixedVector B) := by
    change mixedMoment B node2494 node2494Labels = _
    exact sound2494 B hB hF
  have h2714 : mixedVector B (Sum.inr 2714) = Sparse.eval nodeValue2714 (mixedVector B) := by
    change mixedMoment B node2714 node2714Labels = _
    exact sound2714 B hB hF
  have h3803 : mixedVector B (Sum.inr 3803) = Sparse.eval nodeValue3803 (mixedVector B) := by
    change mixedMoment B node3803 node3803Labels = _
    exact sound3803 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm864, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2474, h2475, h2481, h2494, h2714, h3803, h4092, reducedSource753] using sourceEq864 B hB

theorem rowSound753 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row753 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck753, numericCheck753, reducedZero753 B hB hF, mul_zero]

theorem reducedZero754 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource754 (mixedVector B) = 0 := by
  have h2494 : mixedVector B (Sum.inr 2494) = Sparse.eval nodeValue2494 (mixedVector B) := by
    change mixedMoment B node2494 node2494Labels = _
    exact sound2494 B hB hF
  have h2714 : mixedVector B (Sum.inr 2714) = Sparse.eval nodeValue2714 (mixedVector B) := by
    change mixedMoment B node2714 node2714Labels = _
    exact sound2714 B hB hF
  have h3698 : mixedVector B (Sum.inr 3698) = Sparse.eval nodeValue3698 (mixedVector B) := by
    change mixedMoment B node3698 node3698Labels = _
    exact sound3698 B hB hF
  have h3803 : mixedVector B (Sum.inr 3803) = Sparse.eval nodeValue3803 (mixedVector B) := by
    change mixedMoment B node3803 node3803Labels = _
    exact sound3803 B hB hF
  have h3812 : mixedVector B (Sum.inr 3812) = Sparse.eval nodeValue3812 (mixedVector B) := by
    change mixedMoment B node3812 node3812Labels = _
    exact sound3812 B hB hF
  have h3814 : mixedVector B (Sum.inr 3814) = Sparse.eval nodeValue3814 (mixedVector B) := by
    change mixedMoment B node3814 node3814Labels = _
    exact sound3814 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm865, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2494, h2714, h3698, h3803, h3812, h3814, h4092, reducedSource754] using sourceEq865 B hB

theorem rowSound754 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row754 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck754, numericCheck754, reducedZero754 B hB hF, mul_zero]

theorem reducedZero755 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource755 (mixedVector B) = 0 := by
  have h3217 : mixedVector B (Sum.inr 3217) = Sparse.eval nodeValue3217 (mixedVector B) := by
    change mixedMoment B node3217 node3217Labels = _
    exact sound3217 B hB hF
  have h3686 : mixedVector B (Sum.inr 3686) = Sparse.eval nodeValue3686 (mixedVector B) := by
    change mixedMoment B node3686 node3686Labels = _
    exact sound3686 B hB hF
  have h3691 : mixedVector B (Sum.inr 3691) = Sparse.eval nodeValue3691 (mixedVector B) := by
    change mixedMoment B node3691 node3691Labels = _
    exact sound3691 B hB hF
  have h3698 : mixedVector B (Sum.inr 3698) = Sparse.eval nodeValue3698 (mixedVector B) := by
    change mixedMoment B node3698 node3698Labels = _
    exact sound3698 B hB hF
  have h3788 : mixedVector B (Sum.inr 3788) = Sparse.eval nodeValue3788 (mixedVector B) := by
    change mixedMoment B node3788 node3788Labels = _
    exact sound3788 B hB hF
  have h3803 : mixedVector B (Sum.inr 3803) = Sparse.eval nodeValue3803 (mixedVector B) := by
    change mixedMoment B node3803 node3803Labels = _
    exact sound3803 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm866, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3217, h3686, h3691, h3698, h3788, h3803, h4092, reducedSource755] using sourceEq866 B hB

theorem rowSound755 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row755 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck755, numericCheck755, reducedZero755 B hB hF, mul_zero]

theorem reducedZero756 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource756 (mixedVector B) = 0 := by
  have h2475 : mixedVector B (Sum.inr 2475) = Sparse.eval nodeValue2475 (mixedVector B) := by
    change mixedMoment B node2475 node2475Labels = _
    exact sound2475 B hB hF
  have h3686 : mixedVector B (Sum.inr 3686) = Sparse.eval nodeValue3686 (mixedVector B) := by
    change mixedMoment B node3686 node3686Labels = _
    exact sound3686 B hB hF
  have h3803 : mixedVector B (Sum.inr 3803) = Sparse.eval nodeValue3803 (mixedVector B) := by
    change mixedMoment B node3803 node3803Labels = _
    exact sound3803 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm867, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2475, h3686, h3803, h4092, reducedSource756] using sourceEq867 B hB

theorem rowSound756 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row756 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck756, numericCheck756, reducedZero756 B hB hF, mul_zero]

theorem reducedZero757 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource757 (mixedVector B) = 0 := by
  have h4812 : mixedVector B (Sum.inr 4812) = Sparse.eval nodeValue4812 (mixedVector B) := by
    change mixedMoment B node4812 node4812Labels = _
    exact sound4812 B hB hF
  have h4813 : mixedVector B (Sum.inr 4813) = Sparse.eval nodeValue4813 (mixedVector B) := by
    change mixedMoment B node4813 node4813Labels = _
    exact sound4813 B hB hF
  have h4816 : mixedVector B (Sum.inr 4816) = Sparse.eval nodeValue4816 (mixedVector B) := by
    change mixedMoment B node4816 node4816Labels = _
    exact sound4816 B hB hF
  have h4824 : mixedVector B (Sum.inr 4824) = Sparse.eval nodeValue4824 (mixedVector B) := by
    change mixedMoment B node4824 node4824Labels = _
    exact sound4824 B hB hF
  have h4852 : mixedVector B (Sum.inr 4852) = Sparse.eval nodeValue4852 (mixedVector B) := by
    change mixedMoment B node4852 node4852Labels = _
    exact sound4852 B hB hF
  have h5129 : mixedVector B (Sum.inr 5129) = Sparse.eval nodeValue5129 (mixedVector B) := by
    change mixedMoment B node5129 node5129Labels = _
    exact sound5129 B hB hF
  have h5138 : mixedVector B (Sum.inr 5138) = Sparse.eval nodeValue5138 (mixedVector B) := by
    change mixedMoment B node5138 node5138Labels = _
    exact sound5138 B hB hF
  have h5146 : mixedVector B (Sum.inr 5146) = Sparse.eval nodeValue5146 (mixedVector B) := by
    change mixedMoment B node5146 node5146Labels = _
    exact sound5146 B hB hF
  have h5260 : mixedVector B (Sum.inr 5260) = Sparse.eval nodeValue5260 (mixedVector B) := by
    change mixedMoment B node5260 node5260Labels = _
    exact sound5260 B hB hF
  have h5357 : mixedVector B (Sum.inr 5357) = Sparse.eval nodeValue5357 (mixedVector B) := by
    change mixedMoment B node5357 node5357Labels = _
    exact sound5357 B hB hF
  have h5358 : mixedVector B (Sum.inr 5358) = Sparse.eval nodeValue5358 (mixedVector B) := by
    change mixedMoment B node5358 node5358Labels = _
    exact sound5358 B hB hF
  have h5360 : mixedVector B (Sum.inr 5360) = Sparse.eval nodeValue5360 (mixedVector B) := by
    change mixedMoment B node5360 node5360Labels = _
    exact sound5360 B hB hF
  have h5376 : mixedVector B (Sum.inr 5376) = Sparse.eval nodeValue5376 (mixedVector B) := by
    change mixedMoment B node5376 node5376Labels = _
    exact sound5376 B hB hF
  have h5378 : mixedVector B (Sum.inr 5378) = Sparse.eval nodeValue5378 (mixedVector B) := by
    change mixedMoment B node5378 node5378Labels = _
    exact sound5378 B hB hF
  have h5381 : mixedVector B (Sum.inr 5381) = Sparse.eval nodeValue5381 (mixedVector B) := by
    change mixedMoment B node5381 node5381Labels = _
    exact sound5381 B hB hF
  have h5397 : mixedVector B (Sum.inr 5397) = Sparse.eval nodeValue5397 (mixedVector B) := by
    change mixedMoment B node5397 node5397Labels = _
    exact sound5397 B hB hF
  have h5411 : mixedVector B (Sum.inr 5411) = Sparse.eval nodeValue5411 (mixedVector B) := by
    change mixedMoment B node5411 node5411Labels = _
    exact sound5411 B hB hF
  have h5412 : mixedVector B (Sum.inr 5412) = Sparse.eval nodeValue5412 (mixedVector B) := by
    change mixedMoment B node5412 node5412Labels = _
    exact sound5412 B hB hF
  have h5420 : mixedVector B (Sum.inr 5420) = Sparse.eval nodeValue5420 (mixedVector B) := by
    change mixedMoment B node5420 node5420Labels = _
    exact sound5420 B hB hF
  have h5421 : mixedVector B (Sum.inr 5421) = Sparse.eval nodeValue5421 (mixedVector B) := by
    change mixedMoment B node5421 node5421Labels = _
    exact sound5421 B hB hF
  have h5423 : mixedVector B (Sum.inr 5423) = Sparse.eval nodeValue5423 (mixedVector B) := by
    change mixedMoment B node5423 node5423Labels = _
    exact sound5423 B hB hF
  have h5424 : mixedVector B (Sum.inr 5424) = Sparse.eval nodeValue5424 (mixedVector B) := by
    change mixedMoment B node5424 node5424Labels = _
    exact sound5424 B hB hF
  have h5426 : mixedVector B (Sum.inr 5426) = Sparse.eval nodeValue5426 (mixedVector B) := by
    change mixedMoment B node5426 node5426Labels = _
    exact sound5426 B hB hF
  have h5430 : mixedVector B (Sum.inr 5430) = Sparse.eval nodeValue5430 (mixedVector B) := by
    change mixedMoment B node5430 node5430Labels = _
    exact sound5430 B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434 B hB hF
  have h5436 : mixedVector B (Sum.inr 5436) = Sparse.eval nodeValue5436 (mixedVector B) := by
    change mixedMoment B node5436 node5436Labels = _
    exact sound5436 B hB hF
  have h5445 : mixedVector B (Sum.inr 5445) = Sparse.eval nodeValue5445 (mixedVector B) := by
    change mixedMoment B node5445 node5445Labels = _
    exact sound5445 B hB hF
  have h5477 : mixedVector B (Sum.inr 5477) = Sparse.eval nodeValue5477 (mixedVector B) := by
    change mixedMoment B node5477 node5477Labels = _
    exact sound5477 B hB hF
  simpa only [sourceForm868, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4812, h4813, h4816, h4824, h4852, h5129, h5138, h5146, h5260, h5357, h5358, h5360, h5376, h5378, h5381, h5397, h5411, h5412, h5420, h5421, h5423, h5424, h5426, h5430, h5434, h5436, h5445, h5477, reducedSource757] using sourceEq868 B hB

theorem rowSound757 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row757 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck757, numericCheck757, reducedZero757 B hB hF, mul_zero]

theorem reducedZero758 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource758 (mixedVector B) = 0 := by
  have h2071 : mixedVector B (Sum.inr 2071) = Sparse.eval nodeValue2071 (mixedVector B) := by
    change mixedMoment B node2071 node2071Labels = _
    exact sound2071 B hB hF
  have h2072 : mixedVector B (Sum.inr 2072) = Sparse.eval nodeValue2072 (mixedVector B) := by
    change mixedMoment B node2072 node2072Labels = _
    exact sound2072 B hB hF
  have h2078 : mixedVector B (Sum.inr 2078) = Sparse.eval nodeValue2078 (mixedVector B) := by
    change mixedMoment B node2078 node2078Labels = _
    exact sound2078 B hB hF
  have h2089 : mixedVector B (Sum.inr 2089) = Sparse.eval nodeValue2089 (mixedVector B) := by
    change mixedMoment B node2089 node2089Labels = _
    exact sound2089 B hB hF
  have h2196 : mixedVector B (Sum.inr 2196) = Sparse.eval nodeValue2196 (mixedVector B) := by
    change mixedMoment B node2196 node2196Labels = _
    exact sound2196 B hB hF
  have h2916 : mixedVector B (Sum.inr 2916) = Sparse.eval nodeValue2916 (mixedVector B) := by
    change mixedMoment B node2916 node2916Labels = _
    exact sound2916 B hB hF
  have h2922 : mixedVector B (Sum.inr 2922) = Sparse.eval nodeValue2922 (mixedVector B) := by
    change mixedMoment B node2922 node2922Labels = _
    exact sound2922 B hB hF
  have h2933 : mixedVector B (Sum.inr 2933) = Sparse.eval nodeValue2933 (mixedVector B) := by
    change mixedMoment B node2933 node2933Labels = _
    exact sound2933 B hB hF
  have h3086 : mixedVector B (Sum.inr 3086) = Sparse.eval nodeValue3086 (mixedVector B) := by
    change mixedMoment B node3086 node3086Labels = _
    exact sound3086 B hB hF
  have h3715 : mixedVector B (Sum.inr 3715) = Sparse.eval nodeValue3715 (mixedVector B) := by
    change mixedMoment B node3715 node3715Labels = _
    exact sound3715 B hB hF
  have h3718 : mixedVector B (Sum.inr 3718) = Sparse.eval nodeValue3718 (mixedVector B) := by
    change mixedMoment B node3718 node3718Labels = _
    exact sound3718 B hB hF
  have h3722 : mixedVector B (Sum.inr 3722) = Sparse.eval nodeValue3722 (mixedVector B) := by
    change mixedMoment B node3722 node3722Labels = _
    exact sound3722 B hB hF
  have h3723 : mixedVector B (Sum.inr 3723) = Sparse.eval nodeValue3723 (mixedVector B) := by
    change mixedMoment B node3723 node3723Labels = _
    exact sound3723 B hB hF
  have h3727 : mixedVector B (Sum.inr 3727) = Sparse.eval nodeValue3727 (mixedVector B) := by
    change mixedMoment B node3727 node3727Labels = _
    exact sound3727 B hB hF
  have h3752 : mixedVector B (Sum.inr 3752) = Sparse.eval nodeValue3752 (mixedVector B) := by
    change mixedMoment B node3752 node3752Labels = _
    exact sound3752 B hB hF
  have h3762 : mixedVector B (Sum.inr 3762) = Sparse.eval nodeValue3762 (mixedVector B) := by
    change mixedMoment B node3762 node3762Labels = _
    exact sound3762 B hB hF
  have h3796 : mixedVector B (Sum.inr 3796) = Sparse.eval nodeValue3796 (mixedVector B) := by
    change mixedMoment B node3796 node3796Labels = _
    exact sound3796 B hB hF
  have h3814 : mixedVector B (Sum.inr 3814) = Sparse.eval nodeValue3814 (mixedVector B) := by
    change mixedMoment B node3814 node3814Labels = _
    exact sound3814 B hB hF
  have h3830 : mixedVector B (Sum.inr 3830) = Sparse.eval nodeValue3830 (mixedVector B) := by
    change mixedMoment B node3830 node3830Labels = _
    exact sound3830 B hB hF
  have h3841 : mixedVector B (Sum.inr 3841) = Sparse.eval nodeValue3841 (mixedVector B) := by
    change mixedMoment B node3841 node3841Labels = _
    exact sound3841 B hB hF
  have h3870 : mixedVector B (Sum.inr 3870) = Sparse.eval nodeValue3870 (mixedVector B) := by
    change mixedMoment B node3870 node3870Labels = _
    exact sound3870 B hB hF
  have h3873 : mixedVector B (Sum.inr 3873) = Sparse.eval nodeValue3873 (mixedVector B) := by
    change mixedMoment B node3873 node3873Labels = _
    exact sound3873 B hB hF
  have h3877 : mixedVector B (Sum.inr 3877) = Sparse.eval nodeValue3877 (mixedVector B) := by
    change mixedMoment B node3877 node3877Labels = _
    exact sound3877 B hB hF
  have h3880 : mixedVector B (Sum.inr 3880) = Sparse.eval nodeValue3880 (mixedVector B) := by
    change mixedMoment B node3880 node3880Labels = _
    exact sound3880 B hB hF
  have h3883 : mixedVector B (Sum.inr 3883) = Sparse.eval nodeValue3883 (mixedVector B) := by
    change mixedMoment B node3883 node3883Labels = _
    exact sound3883 B hB hF
  have h3971 : mixedVector B (Sum.inr 3971) = Sparse.eval nodeValue3971 (mixedVector B) := by
    change mixedMoment B node3971 node3971Labels = _
    exact sound3971 B hB hF
  have h3972 : mixedVector B (Sum.inr 3972) = Sparse.eval nodeValue3972 (mixedVector B) := by
    change mixedMoment B node3972 node3972Labels = _
    exact sound3972 B hB hF
  have h3982 : mixedVector B (Sum.inr 3982) = Sparse.eval nodeValue3982 (mixedVector B) := by
    change mixedMoment B node3982 node3982Labels = _
    exact sound3982 B hB hF
  have h3990 : mixedVector B (Sum.inr 3990) = Sparse.eval nodeValue3990 (mixedVector B) := by
    change mixedMoment B node3990 node3990Labels = _
    exact sound3990 B hB hF
  have h4032 : mixedVector B (Sum.inr 4032) = Sparse.eval nodeValue4032 (mixedVector B) := by
    change mixedMoment B node4032 node4032Labels = _
    exact sound4032 B hB hF
  simpa only [sourceForm869, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2071, h2072, h2078, h2089, h2196, h2916, h2922, h2933, h3086, h3715, h3718, h3722, h3723, h3727, h3752, h3762, h3796, h3814, h3830, h3841, h3870, h3873, h3877, h3880, h3883, h3971, h3972, h3982, h3990, h4032, reducedSource758] using sourceEq869 B hB

theorem rowSound758 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row758 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck758, numericCheck758, reducedZero758 B hB hF, mul_zero]

theorem reducedZero759 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource759 (mixedVector B) = 0 := by
  have h2030 : mixedVector B (Sum.inr 2030) = Sparse.eval nodeValue2030 (mixedVector B) := by
    change mixedMoment B node2030 node2030Labels = _
    exact sound2030 B hB hF
  have h2031 : mixedVector B (Sum.inr 2031) = Sparse.eval nodeValue2031 (mixedVector B) := by
    change mixedMoment B node2031 node2031Labels = _
    exact sound2031 B hB hF
  have h2034 : mixedVector B (Sum.inr 2034) = Sparse.eval nodeValue2034 (mixedVector B) := by
    change mixedMoment B node2034 node2034Labels = _
    exact sound2034 B hB hF
  have h2043 : mixedVector B (Sum.inr 2043) = Sparse.eval nodeValue2043 (mixedVector B) := by
    change mixedMoment B node2043 node2043Labels = _
    exact sound2043 B hB hF
  have h2250 : mixedVector B (Sum.inr 2250) = Sparse.eval nodeValue2250 (mixedVector B) := by
    change mixedMoment B node2250 node2250Labels = _
    exact sound2250 B hB hF
  have h3516 : mixedVector B (Sum.inr 3516) = Sparse.eval nodeValue3516 (mixedVector B) := by
    change mixedMoment B node3516 node3516Labels = _
    exact sound3516 B hB hF
  have h3517 : mixedVector B (Sum.inr 3517) = Sparse.eval nodeValue3517 (mixedVector B) := by
    change mixedMoment B node3517 node3517Labels = _
    exact sound3517 B hB hF
  have h3540 : mixedVector B (Sum.inr 3540) = Sparse.eval nodeValue3540 (mixedVector B) := by
    change mixedMoment B node3540 node3540Labels = _
    exact sound3540 B hB hF
  have h3560 : mixedVector B (Sum.inr 3560) = Sparse.eval nodeValue3560 (mixedVector B) := by
    change mixedMoment B node3560 node3560Labels = _
    exact sound3560 B hB hF
  have h3695 : mixedVector B (Sum.inr 3695) = Sparse.eval nodeValue3695 (mixedVector B) := by
    change mixedMoment B node3695 node3695Labels = _
    exact sound3695 B hB hF
  have h3696 : mixedVector B (Sum.inr 3696) = Sparse.eval nodeValue3696 (mixedVector B) := by
    change mixedMoment B node3696 node3696Labels = _
    exact sound3696 B hB hF
  have h3698 : mixedVector B (Sum.inr 3698) = Sparse.eval nodeValue3698 (mixedVector B) := by
    change mixedMoment B node3698 node3698Labels = _
    exact sound3698 B hB hF
  have h3795 : mixedVector B (Sum.inr 3795) = Sparse.eval nodeValue3795 (mixedVector B) := by
    change mixedMoment B node3795 node3795Labels = _
    exact sound3795 B hB hF
  have h3796 : mixedVector B (Sum.inr 3796) = Sparse.eval nodeValue3796 (mixedVector B) := by
    change mixedMoment B node3796 node3796Labels = _
    exact sound3796 B hB hF
  have h3813 : mixedVector B (Sum.inr 3813) = Sparse.eval nodeValue3813 (mixedVector B) := by
    change mixedMoment B node3813 node3813Labels = _
    exact sound3813 B hB hF
  have h3826 : mixedVector B (Sum.inr 3826) = Sparse.eval nodeValue3826 (mixedVector B) := by
    change mixedMoment B node3826 node3826Labels = _
    exact sound3826 B hB hF
  have h3827 : mixedVector B (Sum.inr 3827) = Sparse.eval nodeValue3827 (mixedVector B) := by
    change mixedMoment B node3827 node3827Labels = _
    exact sound3827 B hB hF
  have h3830 : mixedVector B (Sum.inr 3830) = Sparse.eval nodeValue3830 (mixedVector B) := by
    change mixedMoment B node3830 node3830Labels = _
    exact sound3830 B hB hF
  have h3833 : mixedVector B (Sum.inr 3833) = Sparse.eval nodeValue3833 (mixedVector B) := by
    change mixedMoment B node3833 node3833Labels = _
    exact sound3833 B hB hF
  have h3834 : mixedVector B (Sum.inr 3834) = Sparse.eval nodeValue3834 (mixedVector B) := by
    change mixedMoment B node3834 node3834Labels = _
    exact sound3834 B hB hF
  have h3837 : mixedVector B (Sum.inr 3837) = Sparse.eval nodeValue3837 (mixedVector B) := by
    change mixedMoment B node3837 node3837Labels = _
    exact sound3837 B hB hF
  have h3838 : mixedVector B (Sum.inr 3838) = Sparse.eval nodeValue3838 (mixedVector B) := by
    change mixedMoment B node3838 node3838Labels = _
    exact sound3838 B hB hF
  have h3841 : mixedVector B (Sum.inr 3841) = Sparse.eval nodeValue3841 (mixedVector B) := by
    change mixedMoment B node3841 node3841Labels = _
    exact sound3841 B hB hF
  have h3852 : mixedVector B (Sum.inr 3852) = Sparse.eval nodeValue3852 (mixedVector B) := by
    change mixedMoment B node3852 node3852Labels = _
    exact sound3852 B hB hF
  have h3854 : mixedVector B (Sum.inr 3854) = Sparse.eval nodeValue3854 (mixedVector B) := by
    change mixedMoment B node3854 node3854Labels = _
    exact sound3854 B hB hF
  have h3856 : mixedVector B (Sum.inr 3856) = Sparse.eval nodeValue3856 (mixedVector B) := by
    change mixedMoment B node3856 node3856Labels = _
    exact sound3856 B hB hF
  have h3871 : mixedVector B (Sum.inr 3871) = Sparse.eval nodeValue3871 (mixedVector B) := by
    change mixedMoment B node3871 node3871Labels = _
    exact sound3871 B hB hF
  have h3880 : mixedVector B (Sum.inr 3880) = Sparse.eval nodeValue3880 (mixedVector B) := by
    change mixedMoment B node3880 node3880Labels = _
    exact sound3880 B hB hF
  have h3989 : mixedVector B (Sum.inr 3989) = Sparse.eval nodeValue3989 (mixedVector B) := by
    change mixedMoment B node3989 node3989Labels = _
    exact sound3989 B hB hF
  simpa only [sourceForm870, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2030, h2031, h2034, h2043, h2250, h3516, h3517, h3540, h3560, h3695, h3696, h3698, h3795, h3796, h3813, h3826, h3827, h3830, h3833, h3834, h3837, h3838, h3841, h3852, h3854, h3856, h3871, h3880, h3989, reducedSource759] using sourceEq870 B hB

theorem rowSound759 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row759 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck759, numericCheck759, reducedZero759 B hB hF, mul_zero]

theorem reducedZero760 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource760 (mixedVector B) = 0 := by
  have h3782 : mixedVector B (Sum.inr 3782) = Sparse.eval nodeValue3782 (mixedVector B) := by
    change mixedMoment B node3782 node3782Labels = _
    exact sound3782 B hB hF
  have h3839 : mixedVector B (Sum.inr 3839) = Sparse.eval nodeValue3839 (mixedVector B) := by
    change mixedMoment B node3839 node3839Labels = _
    exact sound3839 B hB hF
  have h3946 : mixedVector B (Sum.inr 3946) = Sparse.eval nodeValue3946 (mixedVector B) := by
    change mixedMoment B node3946 node3946Labels = _
    exact sound3946 B hB hF
  have h4022 : mixedVector B (Sum.inr 4022) = Sparse.eval nodeValue4022 (mixedVector B) := by
    change mixedMoment B node4022 node4022Labels = _
    exact sound4022 B hB hF
  have h4024 : mixedVector B (Sum.inr 4024) = Sparse.eval nodeValue4024 (mixedVector B) := by
    change mixedMoment B node4024 node4024Labels = _
    exact sound4024 B hB hF
  have h4044 : mixedVector B (Sum.inr 4044) = Sparse.eval nodeValue4044 (mixedVector B) := by
    change mixedMoment B node4044 node4044Labels = _
    exact sound4044 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm871, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3782, h3839, h3946, h4022, h4024, h4044, h4092, reducedSource760] using sourceEq871 B hB

theorem rowSound760 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row760 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck760, numericCheck760, reducedZero760 B hB hF, mul_zero]

theorem reducedZero761 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource761 (mixedVector B) = 0 := by
  have h3168 : mixedVector B (Sum.inr 3168) = Sparse.eval nodeValue3168 (mixedVector B) := by
    change mixedMoment B node3168 node3168Labels = _
    exact sound3168 B hB hF
  have h3715 : mixedVector B (Sum.inr 3715) = Sparse.eval nodeValue3715 (mixedVector B) := by
    change mixedMoment B node3715 node3715Labels = _
    exact sound3715 B hB hF
  have h3722 : mixedVector B (Sum.inr 3722) = Sparse.eval nodeValue3722 (mixedVector B) := by
    change mixedMoment B node3722 node3722Labels = _
    exact sound3722 B hB hF
  have h3725 : mixedVector B (Sum.inr 3725) = Sparse.eval nodeValue3725 (mixedVector B) := by
    change mixedMoment B node3725 node3725Labels = _
    exact sound3725 B hB hF
  have h3839 : mixedVector B (Sum.inr 3839) = Sparse.eval nodeValue3839 (mixedVector B) := by
    change mixedMoment B node3839 node3839Labels = _
    exact sound3839 B hB hF
  have h4022 : mixedVector B (Sum.inr 4022) = Sparse.eval nodeValue4022 (mixedVector B) := by
    change mixedMoment B node4022 node4022Labels = _
    exact sound4022 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm872, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3168, h3715, h3722, h3725, h3839, h4022, h4092, reducedSource761] using sourceEq872 B hB

theorem rowSound761 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row761 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck761, numericCheck761, reducedZero761 B hB hF, mul_zero]

theorem reducedZero762 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource762 (mixedVector B) = 0 := by
  have h2568 : mixedVector B (Sum.inr 2568) = Sparse.eval nodeValue2568 (mixedVector B) := by
    change mixedMoment B node2568 node2568Labels = _
    exact sound2568 B hB hF
  have h3725 : mixedVector B (Sum.inr 3725) = Sparse.eval nodeValue3725 (mixedVector B) := by
    change mixedMoment B node3725 node3725Labels = _
    exact sound3725 B hB hF
  have h3780 : mixedVector B (Sum.inr 3780) = Sparse.eval nodeValue3780 (mixedVector B) := by
    change mixedMoment B node3780 node3780Labels = _
    exact sound3780 B hB hF
  have h3828 : mixedVector B (Sum.inr 3828) = Sparse.eval nodeValue3828 (mixedVector B) := by
    change mixedMoment B node3828 node3828Labels = _
    exact sound3828 B hB hF
  have h3839 : mixedVector B (Sum.inr 3839) = Sparse.eval nodeValue3839 (mixedVector B) := by
    change mixedMoment B node3839 node3839Labels = _
    exact sound3839 B hB hF
  have h3848 : mixedVector B (Sum.inr 3848) = Sparse.eval nodeValue3848 (mixedVector B) := by
    change mixedMoment B node3848 node3848Labels = _
    exact sound3848 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm873, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2568, h3725, h3780, h3828, h3839, h3848, h4092, reducedSource762] using sourceEq873 B hB

theorem rowSound762 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row762 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck762, numericCheck762, reducedZero762 B hB hF, mul_zero]

theorem reducedZero763 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource763 (mixedVector B) = 0 := by
  have h3170 : mixedVector B (Sum.inr 3170) = Sparse.eval nodeValue3170 (mixedVector B) := by
    change mixedMoment B node3170 node3170Labels = _
    exact sound3170 B hB hF
  have h3719 : mixedVector B (Sum.inr 3719) = Sparse.eval nodeValue3719 (mixedVector B) := by
    change mixedMoment B node3719 node3719Labels = _
    exact sound3719 B hB hF
  have h3782 : mixedVector B (Sum.inr 3782) = Sparse.eval nodeValue3782 (mixedVector B) := by
    change mixedMoment B node3782 node3782Labels = _
    exact sound3782 B hB hF
  have h3809 : mixedVector B (Sum.inr 3809) = Sparse.eval nodeValue3809 (mixedVector B) := by
    change mixedMoment B node3809 node3809Labels = _
    exact sound3809 B hB hF
  have h3839 : mixedVector B (Sum.inr 3839) = Sparse.eval nodeValue3839 (mixedVector B) := by
    change mixedMoment B node3839 node3839Labels = _
    exact sound3839 B hB hF
  have h4024 : mixedVector B (Sum.inr 4024) = Sparse.eval nodeValue4024 (mixedVector B) := by
    change mixedMoment B node4024 node4024Labels = _
    exact sound4024 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm874, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3170, h3719, h3782, h3809, h3839, h4024, h4092, reducedSource763] using sourceEq874 B hB

theorem rowSound763 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row763 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck763, numericCheck763, reducedZero763 B hB hF, mul_zero]

theorem reducedZero764 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource764 (mixedVector B) = 0 := by
  have h2557 : mixedVector B (Sum.inr 2557) = Sparse.eval nodeValue2557 (mixedVector B) := by
    change mixedMoment B node2557 node2557Labels = _
    exact sound2557 B hB hF
  have h3722 : mixedVector B (Sum.inr 3722) = Sparse.eval nodeValue3722 (mixedVector B) := by
    change mixedMoment B node3722 node3722Labels = _
    exact sound3722 B hB hF
  have h3782 : mixedVector B (Sum.inr 3782) = Sparse.eval nodeValue3782 (mixedVector B) := by
    change mixedMoment B node3782 node3782Labels = _
    exact sound3782 B hB hF
  have h3839 : mixedVector B (Sum.inr 3839) = Sparse.eval nodeValue3839 (mixedVector B) := by
    change mixedMoment B node3839 node3839Labels = _
    exact sound3839 B hB hF
  have h3841 : mixedVector B (Sum.inr 3841) = Sparse.eval nodeValue3841 (mixedVector B) := by
    change mixedMoment B node3841 node3841Labels = _
    exact sound3841 B hB hF
  have h3843 : mixedVector B (Sum.inr 3843) = Sparse.eval nodeValue3843 (mixedVector B) := by
    change mixedMoment B node3843 node3843Labels = _
    exact sound3843 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm875, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2557, h3722, h3782, h3839, h3841, h3843, h4092, reducedSource764] using sourceEq875 B hB

theorem rowSound764 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row764 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck764, numericCheck764, reducedZero764 B hB hF, mul_zero]

theorem reducedZero765 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource765 (mixedVector B) = 0 := by
  have h3175 : mixedVector B (Sum.inr 3175) = Sparse.eval nodeValue3175 (mixedVector B) := by
    change mixedMoment B node3175 node3175Labels = _
    exact sound3175 B hB hF
  have h3723 : mixedVector B (Sum.inr 3723) = Sparse.eval nodeValue3723 (mixedVector B) := by
    change mixedMoment B node3723 node3723Labels = _
    exact sound3723 B hB hF
  have h3828 : mixedVector B (Sum.inr 3828) = Sparse.eval nodeValue3828 (mixedVector B) := by
    change mixedMoment B node3828 node3828Labels = _
    exact sound3828 B hB hF
  have h3839 : mixedVector B (Sum.inr 3839) = Sparse.eval nodeValue3839 (mixedVector B) := by
    change mixedMoment B node3839 node3839Labels = _
    exact sound3839 B hB hF
  have h3877 : mixedVector B (Sum.inr 3877) = Sparse.eval nodeValue3877 (mixedVector B) := by
    change mixedMoment B node3877 node3877Labels = _
    exact sound3877 B hB hF
  have h3946 : mixedVector B (Sum.inr 3946) = Sparse.eval nodeValue3946 (mixedVector B) := by
    change mixedMoment B node3946 node3946Labels = _
    exact sound3946 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm876, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3175, h3723, h3828, h3839, h3877, h3946, h4092, reducedSource765] using sourceEq876 B hB

theorem rowSound765 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row765 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck765, numericCheck765, reducedZero765 B hB hF, mul_zero]

theorem reducedZero766 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource766 (mixedVector B) = 0 := by
  have h2545 : mixedVector B (Sum.inr 2545) = Sparse.eval nodeValue2545 (mixedVector B) := by
    change mixedMoment B node2545 node2545Labels = _
    exact sound2545 B hB hF
  have h3715 : mixedVector B (Sum.inr 3715) = Sparse.eval nodeValue3715 (mixedVector B) := by
    change mixedMoment B node3715 node3715Labels = _
    exact sound3715 B hB hF
  have h3719 : mixedVector B (Sum.inr 3719) = Sparse.eval nodeValue3719 (mixedVector B) := by
    change mixedMoment B node3719 node3719Labels = _
    exact sound3719 B hB hF
  have h3723 : mixedVector B (Sum.inr 3723) = Sparse.eval nodeValue3723 (mixedVector B) := by
    change mixedMoment B node3723 node3723Labels = _
    exact sound3723 B hB hF
  have h3837 : mixedVector B (Sum.inr 3837) = Sparse.eval nodeValue3837 (mixedVector B) := by
    change mixedMoment B node3837 node3837Labels = _
    exact sound3837 B hB hF
  have h3839 : mixedVector B (Sum.inr 3839) = Sparse.eval nodeValue3839 (mixedVector B) := by
    change mixedMoment B node3839 node3839Labels = _
    exact sound3839 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm877, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2545, h3715, h3719, h3723, h3837, h3839, h4092, reducedSource766] using sourceEq877 B hB

theorem rowSound766 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row766 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck766, numericCheck766, reducedZero766 B hB hF, mul_zero]

theorem reducedZero767 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource767 (mixedVector B) = 0 := by
  have h3196 : mixedVector B (Sum.inr 3196) = Sparse.eval nodeValue3196 (mixedVector B) := by
    change mixedMoment B node3196 node3196Labels = _
    exact sound3196 B hB hF
  have h3780 : mixedVector B (Sum.inr 3780) = Sparse.eval nodeValue3780 (mixedVector B) := by
    change mixedMoment B node3780 node3780Labels = _
    exact sound3780 B hB hF
  have h3782 : mixedVector B (Sum.inr 3782) = Sparse.eval nodeValue3782 (mixedVector B) := by
    change mixedMoment B node3782 node3782Labels = _
    exact sound3782 B hB hF
  have h3814 : mixedVector B (Sum.inr 3814) = Sparse.eval nodeValue3814 (mixedVector B) := by
    change mixedMoment B node3814 node3814Labels = _
    exact sound3814 B hB hF
  have h3839 : mixedVector B (Sum.inr 3839) = Sparse.eval nodeValue3839 (mixedVector B) := by
    change mixedMoment B node3839 node3839Labels = _
    exact sound3839 B hB hF
  have h3841 : mixedVector B (Sum.inr 3841) = Sparse.eval nodeValue3841 (mixedVector B) := by
    change mixedMoment B node3841 node3841Labels = _
    exact sound3841 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm878, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3196, h3780, h3782, h3814, h3839, h3841, h4092, reducedSource767] using sourceEq878 B hB

theorem rowSound767 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row767 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck767, numericCheck767, reducedZero767 B hB hF, mul_zero]

theorem sourceRowsAt752 : MixedData.sourceRows (752 : Fin 2425) =
    MixedData.row752 := by decide +kernel

theorem sourceRowsAt753 : MixedData.sourceRows (753 : Fin 2425) =
    MixedData.row753 := by decide +kernel

theorem sourceRowsAt754 : MixedData.sourceRows (754 : Fin 2425) =
    MixedData.row754 := by decide +kernel

theorem sourceRowsAt755 : MixedData.sourceRows (755 : Fin 2425) =
    MixedData.row755 := by decide +kernel

theorem sourceRowsAt756 : MixedData.sourceRows (756 : Fin 2425) =
    MixedData.row756 := by decide +kernel

theorem sourceRowsAt757 : MixedData.sourceRows (757 : Fin 2425) =
    MixedData.row757 := by decide +kernel

theorem sourceRowsAt758 : MixedData.sourceRows (758 : Fin 2425) =
    MixedData.row758 := by decide +kernel

theorem sourceRowsAt759 : MixedData.sourceRows (759 : Fin 2425) =
    MixedData.row759 := by decide +kernel

theorem sourceRowsAt760 : MixedData.sourceRows (760 : Fin 2425) =
    MixedData.row760 := by decide +kernel

theorem sourceRowsAt761 : MixedData.sourceRows (761 : Fin 2425) =
    MixedData.row761 := by decide +kernel

theorem sourceRowsAt762 : MixedData.sourceRows (762 : Fin 2425) =
    MixedData.row762 := by decide +kernel

theorem sourceRowsAt763 : MixedData.sourceRows (763 : Fin 2425) =
    MixedData.row763 := by decide +kernel

theorem sourceRowsAt764 : MixedData.sourceRows (764 : Fin 2425) =
    MixedData.row764 := by decide +kernel

theorem sourceRowsAt765 : MixedData.sourceRows (765 : Fin 2425) =
    MixedData.row765 := by decide +kernel

theorem sourceRowsAt766 : MixedData.sourceRows (766 : Fin 2425) =
    MixedData.row766 := by decide +kernel

theorem sourceRowsAt767 : MixedData.sourceRows (767 : Fin 2425) =
    MixedData.row767 := by decide +kernel

theorem chunkSound47 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 47) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 752 ∨ k.val = 753 ∨ k.val = 754 ∨ k.val = 755 ∨ k.val = 756 ∨ k.val = 757 ∨ k.val = 758 ∨ k.val = 759 ∨ k.val = 760 ∨ k.val = 761 ∨ k.val = 762 ∨ k.val = 763 ∨ k.val = 764 ∨ k.val = 765 ∨ k.val = 766 ∨ k.val = 767 := by omega
  rcases heq with h752 | h753 | h754 | h755 | h756 | h757 | h758 | h759 | h760 | h761 | h762 | h763 | h764 | h765 | h766 | h767
  · have he : k = (752 : Fin 2425) := Fin.ext h752
    subst k
    rw [sourceRowsAt752]
    exact rowSound752 B hB hF
  · have he : k = (753 : Fin 2425) := Fin.ext h753
    subst k
    rw [sourceRowsAt753]
    exact rowSound753 B hB hF
  · have he : k = (754 : Fin 2425) := Fin.ext h754
    subst k
    rw [sourceRowsAt754]
    exact rowSound754 B hB hF
  · have he : k = (755 : Fin 2425) := Fin.ext h755
    subst k
    rw [sourceRowsAt755]
    exact rowSound755 B hB hF
  · have he : k = (756 : Fin 2425) := Fin.ext h756
    subst k
    rw [sourceRowsAt756]
    exact rowSound756 B hB hF
  · have he : k = (757 : Fin 2425) := Fin.ext h757
    subst k
    rw [sourceRowsAt757]
    exact rowSound757 B hB hF
  · have he : k = (758 : Fin 2425) := Fin.ext h758
    subst k
    rw [sourceRowsAt758]
    exact rowSound758 B hB hF
  · have he : k = (759 : Fin 2425) := Fin.ext h759
    subst k
    rw [sourceRowsAt759]
    exact rowSound759 B hB hF
  · have he : k = (760 : Fin 2425) := Fin.ext h760
    subst k
    rw [sourceRowsAt760]
    exact rowSound760 B hB hF
  · have he : k = (761 : Fin 2425) := Fin.ext h761
    subst k
    rw [sourceRowsAt761]
    exact rowSound761 B hB hF
  · have he : k = (762 : Fin 2425) := Fin.ext h762
    subst k
    rw [sourceRowsAt762]
    exact rowSound762 B hB hF
  · have he : k = (763 : Fin 2425) := Fin.ext h763
    subst k
    rw [sourceRowsAt763]
    exact rowSound763 B hB hF
  · have he : k = (764 : Fin 2425) := Fin.ext h764
    subst k
    rw [sourceRowsAt764]
    exact rowSound764 B hB hF
  · have he : k = (765 : Fin 2425) := Fin.ext h765
    subst k
    rw [sourceRowsAt765]
    exact rowSound765 B hB hF
  · have he : k = (766 : Fin 2425) := Fin.ext h766
    subst k
    rw [sourceRowsAt766]
    exact rowSound766 B hB hF
  · have he : k = (767 : Fin 2425) := Fin.ext h767
    subst k
    rw [sourceRowsAt767]
    exact rowSound767 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
