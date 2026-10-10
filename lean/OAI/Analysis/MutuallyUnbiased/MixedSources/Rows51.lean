import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources29

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero816 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource816 (mixedVector B) = 0 := by
  have h4992 : mixedVector B (Sum.inr 4992) = Sparse.eval nodeValue4992 (mixedVector B) := by
    change mixedMoment B node4992 node4992Labels = _
    exact sound4992 B hB hF
  have h4993 : mixedVector B (Sum.inr 4993) = Sparse.eval nodeValue4993 (mixedVector B) := by
    change mixedMoment B node4993 node4993Labels = _
    exact sound4993 B hB hF
  have h4999 : mixedVector B (Sum.inr 4999) = Sparse.eval nodeValue4999 (mixedVector B) := by
    change mixedMoment B node4999 node4999Labels = _
    exact sound4999 B hB hF
  have h5004 : mixedVector B (Sum.inr 5004) = Sparse.eval nodeValue5004 (mixedVector B) := by
    change mixedMoment B node5004 node5004Labels = _
    exact sound5004 B hB hF
  have h5005 : mixedVector B (Sum.inr 5005) = Sparse.eval nodeValue5005 (mixedVector B) := by
    change mixedMoment B node5005 node5005Labels = _
    exact sound5005 B hB hF
  have h5011 : mixedVector B (Sum.inr 5011) = Sparse.eval nodeValue5011 (mixedVector B) := by
    change mixedMoment B node5011 node5011Labels = _
    exact sound5011 B hB hF
  have h5145 : mixedVector B (Sum.inr 5145) = Sparse.eval nodeValue5145 (mixedVector B) := by
    change mixedMoment B node5145 node5145Labels = _
    exact sound5145 B hB hF
  have h5251 : mixedVector B (Sum.inr 5251) = Sparse.eval nodeValue5251 (mixedVector B) := by
    change mixedMoment B node5251 node5251Labels = _
    exact sound5251 B hB hF
  have h5265 : mixedVector B (Sum.inr 5265) = Sparse.eval nodeValue5265 (mixedVector B) := by
    change mixedMoment B node5265 node5265Labels = _
    exact sound5265 B hB hF
  have h5282 : mixedVector B (Sum.inr 5282) = Sparse.eval nodeValue5282 (mixedVector B) := by
    change mixedMoment B node5282 node5282Labels = _
    exact sound5282 B hB hF
  have h5379 : mixedVector B (Sum.inr 5379) = Sparse.eval nodeValue5379 (mixedVector B) := by
    change mixedMoment B node5379 node5379Labels = _
    exact sound5379 B hB hF
  have h5414 : mixedVector B (Sum.inr 5414) = Sparse.eval nodeValue5414 (mixedVector B) := by
    change mixedMoment B node5414 node5414Labels = _
    exact sound5414 B hB hF
  have h5421 : mixedVector B (Sum.inr 5421) = Sparse.eval nodeValue5421 (mixedVector B) := by
    change mixedMoment B node5421 node5421Labels = _
    exact sound5421 B hB hF
  have h5424 : mixedVector B (Sum.inr 5424) = Sparse.eval nodeValue5424 (mixedVector B) := by
    change mixedMoment B node5424 node5424Labels = _
    exact sound5424 B hB hF
  have h5431 : mixedVector B (Sum.inr 5431) = Sparse.eval nodeValue5431 (mixedVector B) := by
    change mixedMoment B node5431 node5431Labels = _
    exact sound5431 B hB hF
  have h5439 : mixedVector B (Sum.inr 5439) = Sparse.eval nodeValue5439 (mixedVector B) := by
    change mixedMoment B node5439 node5439Labels = _
    exact sound5439 B hB hF
  have h5446 : mixedVector B (Sum.inr 5446) = Sparse.eval nodeValue5446 (mixedVector B) := by
    change mixedMoment B node5446 node5446Labels = _
    exact sound5446 B hB hF
  have h5450 : mixedVector B (Sum.inr 5450) = Sparse.eval nodeValue5450 (mixedVector B) := by
    change mixedMoment B node5450 node5450Labels = _
    exact sound5450 B hB hF
  have h5470 : mixedVector B (Sum.inr 5470) = Sparse.eval nodeValue5470 (mixedVector B) := by
    change mixedMoment B node5470 node5470Labels = _
    exact sound5470 B hB hF
  have h5472 : mixedVector B (Sum.inr 5472) = Sparse.eval nodeValue5472 (mixedVector B) := by
    change mixedMoment B node5472 node5472Labels = _
    exact sound5472 B hB hF
  have h5481 : mixedVector B (Sum.inr 5481) = Sparse.eval nodeValue5481 (mixedVector B) := by
    change mixedMoment B node5481 node5481Labels = _
    exact sound5481 B hB hF
  simpa only [sourceForm935, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4992, h4993, h4999, h5004, h5005, h5011, h5145, h5251, h5265, h5282, h5379, h5414, h5421, h5424, h5431, h5439, h5446, h5450, h5470, h5472, h5481, reducedSource816] using sourceEq935 B hB

theorem rowSound816 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row816 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck816, numericCheck816, reducedZero816 B hB hF, mul_zero]

theorem reducedZero817 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource817 (mixedVector B) = 0 := by
  have h2378 : mixedVector B (Sum.inr 2378) = Sparse.eval nodeValue2378 (mixedVector B) := by
    change mixedMoment B node2378 node2378Labels = _
    exact sound2378 B hB hF
  have h2379 : mixedVector B (Sum.inr 2379) = Sparse.eval nodeValue2379 (mixedVector B) := by
    change mixedMoment B node2379 node2379Labels = _
    exact sound2379 B hB hF
  have h2384 : mixedVector B (Sum.inr 2384) = Sparse.eval nodeValue2384 (mixedVector B) := by
    change mixedMoment B node2384 node2384Labels = _
    exact sound2384 B hB hF
  have h2710 : mixedVector B (Sum.inr 2710) = Sparse.eval nodeValue2710 (mixedVector B) := by
    change mixedMoment B node2710 node2710Labels = _
    exact sound2710 B hB hF
  have h2912 : mixedVector B (Sum.inr 2912) = Sparse.eval nodeValue2912 (mixedVector B) := by
    change mixedMoment B node2912 node2912Labels = _
    exact sound2912 B hB hF
  have h2925 : mixedVector B (Sum.inr 2925) = Sparse.eval nodeValue2925 (mixedVector B) := by
    change mixedMoment B node2925 node2925Labels = _
    exact sound2925 B hB hF
  have h3078 : mixedVector B (Sum.inr 3078) = Sparse.eval nodeValue3078 (mixedVector B) := by
    change mixedMoment B node3078 node3078Labels = _
    exact sound3078 B hB hF
  have h3337 : mixedVector B (Sum.inr 3337) = Sparse.eval nodeValue3337 (mixedVector B) := by
    change mixedMoment B node3337 node3337Labels = _
    exact sound3337 B hB hF
  have h3342 : mixedVector B (Sum.inr 3342) = Sparse.eval nodeValue3342 (mixedVector B) := by
    change mixedMoment B node3342 node3342Labels = _
    exact sound3342 B hB hF
  have h3526 : mixedVector B (Sum.inr 3526) = Sparse.eval nodeValue3526 (mixedVector B) := by
    change mixedMoment B node3526 node3526Labels = _
    exact sound3526 B hB hF
  have h3720 : mixedVector B (Sum.inr 3720) = Sparse.eval nodeValue3720 (mixedVector B) := by
    change mixedMoment B node3720 node3720Labels = _
    exact sound3720 B hB hF
  have h3869 : mixedVector B (Sum.inr 3869) = Sparse.eval nodeValue3869 (mixedVector B) := by
    change mixedMoment B node3869 node3869Labels = _
    exact sound3869 B hB hF
  have h3946 : mixedVector B (Sum.inr 3946) = Sparse.eval nodeValue3946 (mixedVector B) := by
    change mixedMoment B node3946 node3946Labels = _
    exact sound3946 B hB hF
  have h3955 : mixedVector B (Sum.inr 3955) = Sparse.eval nodeValue3955 (mixedVector B) := by
    change mixedMoment B node3955 node3955Labels = _
    exact sound3955 B hB hF
  have h3957 : mixedVector B (Sum.inr 3957) = Sparse.eval nodeValue3957 (mixedVector B) := by
    change mixedMoment B node3957 node3957Labels = _
    exact sound3957 B hB hF
  have h3959 : mixedVector B (Sum.inr 3959) = Sparse.eval nodeValue3959 (mixedVector B) := by
    change mixedMoment B node3959 node3959Labels = _
    exact sound3959 B hB hF
  have h3979 : mixedVector B (Sum.inr 3979) = Sparse.eval nodeValue3979 (mixedVector B) := by
    change mixedMoment B node3979 node3979Labels = _
    exact sound3979 B hB hF
  have h3990 : mixedVector B (Sum.inr 3990) = Sparse.eval nodeValue3990 (mixedVector B) := by
    change mixedMoment B node3990 node3990Labels = _
    exact sound3990 B hB hF
  have h4012 : mixedVector B (Sum.inr 4012) = Sparse.eval nodeValue4012 (mixedVector B) := by
    change mixedMoment B node4012 node4012Labels = _
    exact sound4012 B hB hF
  have h4026 : mixedVector B (Sum.inr 4026) = Sparse.eval nodeValue4026 (mixedVector B) := by
    change mixedMoment B node4026 node4026Labels = _
    exact sound4026 B hB hF
  have h4029 : mixedVector B (Sum.inr 4029) = Sparse.eval nodeValue4029 (mixedVector B) := by
    change mixedMoment B node4029 node4029Labels = _
    exact sound4029 B hB hF
  simpa only [sourceForm936, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2378, h2379, h2384, h2710, h2912, h2925, h3078, h3337, h3342, h3526, h3720, h3869, h3946, h3955, h3957, h3959, h3979, h3990, h4012, h4026, h4029, reducedSource817] using sourceEq936 B hB

theorem rowSound817 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row817 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck817, numericCheck817, reducedZero817 B hB hF, mul_zero]

theorem reducedZero818 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource818 (mixedVector B) = 0 := by
  have h2389 : mixedVector B (Sum.inr 2389) = Sparse.eval nodeValue2389 (mixedVector B) := by
    change mixedMoment B node2389 node2389Labels = _
    exact sound2389 B hB hF
  have h2390 : mixedVector B (Sum.inr 2390) = Sparse.eval nodeValue2390 (mixedVector B) := by
    change mixedMoment B node2390 node2390Labels = _
    exact sound2390 B hB hF
  have h2396 : mixedVector B (Sum.inr 2396) = Sparse.eval nodeValue2396 (mixedVector B) := by
    change mixedMoment B node2396 node2396Labels = _
    exact sound2396 B hB hF
  have h2730 : mixedVector B (Sum.inr 2730) = Sparse.eval nodeValue2730 (mixedVector B) := by
    change mixedMoment B node2730 node2730Labels = _
    exact sound2730 B hB hF
  have h3345 : mixedVector B (Sum.inr 3345) = Sparse.eval nodeValue3345 (mixedVector B) := by
    change mixedMoment B node3345 node3345Labels = _
    exact sound3345 B hB hF
  have h3346 : mixedVector B (Sum.inr 3346) = Sparse.eval nodeValue3346 (mixedVector B) := by
    change mixedMoment B node3346 node3346Labels = _
    exact sound3346 B hB hF
  have h3350 : mixedVector B (Sum.inr 3350) = Sparse.eval nodeValue3350 (mixedVector B) := by
    change mixedMoment B node3350 node3350Labels = _
    exact sound3350 B hB hF
  have h3539 : mixedVector B (Sum.inr 3539) = Sparse.eval nodeValue3539 (mixedVector B) := by
    change mixedMoment B node3539 node3539Labels = _
    exact sound3539 B hB hF
  have h3562 : mixedVector B (Sum.inr 3562) = Sparse.eval nodeValue3562 (mixedVector B) := by
    change mixedMoment B node3562 node3562Labels = _
    exact sound3562 B hB hF
  have h3580 : mixedVector B (Sum.inr 3580) = Sparse.eval nodeValue3580 (mixedVector B) := by
    change mixedMoment B node3580 node3580Labels = _
    exact sound3580 B hB hF
  have h3819 : mixedVector B (Sum.inr 3819) = Sparse.eval nodeValue3819 (mixedVector B) := by
    change mixedMoment B node3819 node3819Labels = _
    exact sound3819 B hB hF
  have h3832 : mixedVector B (Sum.inr 3832) = Sparse.eval nodeValue3832 (mixedVector B) := by
    change mixedMoment B node3832 node3832Labels = _
    exact sound3832 B hB hF
  have h3843 : mixedVector B (Sum.inr 3843) = Sparse.eval nodeValue3843 (mixedVector B) := by
    change mixedMoment B node3843 node3843Labels = _
    exact sound3843 B hB hF
  have h3858 : mixedVector B (Sum.inr 3858) = Sparse.eval nodeValue3858 (mixedVector B) := by
    change mixedMoment B node3858 node3858Labels = _
    exact sound3858 B hB hF
  have h3873 : mixedVector B (Sum.inr 3873) = Sparse.eval nodeValue3873 (mixedVector B) := by
    change mixedMoment B node3873 node3873Labels = _
    exact sound3873 B hB hF
  have h3875 : mixedVector B (Sum.inr 3875) = Sparse.eval nodeValue3875 (mixedVector B) := by
    change mixedMoment B node3875 node3875Labels = _
    exact sound3875 B hB hF
  have h3884 : mixedVector B (Sum.inr 3884) = Sparse.eval nodeValue3884 (mixedVector B) := by
    change mixedMoment B node3884 node3884Labels = _
    exact sound3884 B hB hF
  have h3887 : mixedVector B (Sum.inr 3887) = Sparse.eval nodeValue3887 (mixedVector B) := by
    change mixedMoment B node3887 node3887Labels = _
    exact sound3887 B hB hF
  have h3947 : mixedVector B (Sum.inr 3947) = Sparse.eval nodeValue3947 (mixedVector B) := by
    change mixedMoment B node3947 node3947Labels = _
    exact sound3947 B hB hF
  have h3991 : mixedVector B (Sum.inr 3991) = Sparse.eval nodeValue3991 (mixedVector B) := by
    change mixedMoment B node3991 node3991Labels = _
    exact sound3991 B hB hF
  have h4002 : mixedVector B (Sum.inr 4002) = Sparse.eval nodeValue4002 (mixedVector B) := by
    change mixedMoment B node4002 node4002Labels = _
    exact sound4002 B hB hF
  simpa only [sourceForm937, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2389, h2390, h2396, h2730, h3345, h3346, h3350, h3539, h3562, h3580, h3819, h3832, h3843, h3858, h3873, h3875, h3884, h3887, h3947, h3991, h4002, reducedSource818] using sourceEq937 B hB

theorem rowSound818 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row818 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck818, numericCheck818, reducedZero818 B hB hF, mul_zero]

theorem reducedZero819 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource819 (mixedVector B) = 0 := by
  have h3846 : mixedVector B (Sum.inr 3846) = Sparse.eval nodeValue3846 (mixedVector B) := by
    change mixedMoment B node3846 node3846Labels = _
    exact sound3846 B hB hF
  have h3947 : mixedVector B (Sum.inr 3947) = Sparse.eval nodeValue3947 (mixedVector B) := by
    change mixedMoment B node3947 node3947Labels = _
    exact sound3947 B hB hF
  have h3949 : mixedVector B (Sum.inr 3949) = Sparse.eval nodeValue3949 (mixedVector B) := by
    change mixedMoment B node3949 node3949Labels = _
    exact sound3949 B hB hF
  have h3957 : mixedVector B (Sum.inr 3957) = Sparse.eval nodeValue3957 (mixedVector B) := by
    change mixedMoment B node3957 node3957Labels = _
    exact sound3957 B hB hF
  have h4008 : mixedVector B (Sum.inr 4008) = Sparse.eval nodeValue4008 (mixedVector B) := by
    change mixedMoment B node4008 node4008Labels = _
    exact sound4008 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm938, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3846, h3947, h3949, h3957, h4008, h4091, reducedSource819] using sourceEq938 B hB

theorem rowSound819 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row819 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck819, numericCheck819, reducedZero819 B hB hF, mul_zero]

theorem reducedZero820 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource820 (mixedVector B) = 0 := by
  have h2567 : mixedVector B (Sum.inr 2567) = Sparse.eval nodeValue2567 (mixedVector B) := by
    change mixedMoment B node2567 node2567Labels = _
    exact sound2567 B hB hF
  have h3724 : mixedVector B (Sum.inr 3724) = Sparse.eval nodeValue3724 (mixedVector B) := by
    change mixedMoment B node3724 node3724Labels = _
    exact sound3724 B hB hF
  have h3827 : mixedVector B (Sum.inr 3827) = Sparse.eval nodeValue3827 (mixedVector B) := by
    change mixedMoment B node3827 node3827Labels = _
    exact sound3827 B hB hF
  have h3838 : mixedVector B (Sum.inr 3838) = Sparse.eval nodeValue3838 (mixedVector B) := by
    change mixedMoment B node3838 node3838Labels = _
    exact sound3838 B hB hF
  have h3846 : mixedVector B (Sum.inr 3846) = Sparse.eval nodeValue3846 (mixedVector B) := by
    change mixedMoment B node3846 node3846Labels = _
    exact sound3846 B hB hF
  have h3849 : mixedVector B (Sum.inr 3849) = Sparse.eval nodeValue3849 (mixedVector B) := by
    change mixedMoment B node3849 node3849Labels = _
    exact sound3849 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm940, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2567, h3724, h3827, h3838, h3846, h3849, h4091, reducedSource820] using sourceEq940 B hB

theorem rowSound820 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row820 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck820, numericCheck820, reducedZero820 B hB hF, mul_zero]

theorem reducedZero821 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource821 (mixedVector B) = 0 := by
  have h4791 : mixedVector B (Sum.inr 4791) = Sparse.eval nodeValue4791 (mixedVector B) := by
    change mixedMoment B node4791 node4791Labels = _
    exact sound4791 B hB hF
  have h4795 : mixedVector B (Sum.inr 4795) = Sparse.eval nodeValue4795 (mixedVector B) := by
    change mixedMoment B node4795 node4795Labels = _
    exact sound4795 B hB hF
  have h4799 : mixedVector B (Sum.inr 4799) = Sparse.eval nodeValue4799 (mixedVector B) := by
    change mixedMoment B node4799 node4799Labels = _
    exact sound4799 B hB hF
  have h4863 : mixedVector B (Sum.inr 4863) = Sparse.eval nodeValue4863 (mixedVector B) := by
    change mixedMoment B node4863 node4863Labels = _
    exact sound4863 B hB hF
  have h5181 : mixedVector B (Sum.inr 5181) = Sparse.eval nodeValue5181 (mixedVector B) := by
    change mixedMoment B node5181 node5181Labels = _
    exact sound5181 B hB hF
  have h5184 : mixedVector B (Sum.inr 5184) = Sparse.eval nodeValue5184 (mixedVector B) := by
    change mixedMoment B node5184 node5184Labels = _
    exact sound5184 B hB hF
  have h5243 : mixedVector B (Sum.inr 5243) = Sparse.eval nodeValue5243 (mixedVector B) := by
    change mixedMoment B node5243 node5243Labels = _
    exact sound5243 B hB hF
  have h5348 : mixedVector B (Sum.inr 5348) = Sparse.eval nodeValue5348 (mixedVector B) := by
    change mixedMoment B node5348 node5348Labels = _
    exact sound5348 B hB hF
  have h5350 : mixedVector B (Sum.inr 5350) = Sparse.eval nodeValue5350 (mixedVector B) := by
    change mixedMoment B node5350 node5350Labels = _
    exact sound5350 B hB hF
  have h5354 : mixedVector B (Sum.inr 5354) = Sparse.eval nodeValue5354 (mixedVector B) := by
    change mixedMoment B node5354 node5354Labels = _
    exact sound5354 B hB hF
  have h5379 : mixedVector B (Sum.inr 5379) = Sparse.eval nodeValue5379 (mixedVector B) := by
    change mixedMoment B node5379 node5379Labels = _
    exact sound5379 B hB hF
  have h5383 : mixedVector B (Sum.inr 5383) = Sparse.eval nodeValue5383 (mixedVector B) := by
    change mixedMoment B node5383 node5383Labels = _
    exact sound5383 B hB hF
  have h5406 : mixedVector B (Sum.inr 5406) = Sparse.eval nodeValue5406 (mixedVector B) := by
    change mixedMoment B node5406 node5406Labels = _
    exact sound5406 B hB hF
  have h5414 : mixedVector B (Sum.inr 5414) = Sparse.eval nodeValue5414 (mixedVector B) := by
    change mixedMoment B node5414 node5414Labels = _
    exact sound5414 B hB hF
  have h5429 : mixedVector B (Sum.inr 5429) = Sparse.eval nodeValue5429 (mixedVector B) := by
    change mixedMoment B node5429 node5429Labels = _
    exact sound5429 B hB hF
  have h5430 : mixedVector B (Sum.inr 5430) = Sparse.eval nodeValue5430 (mixedVector B) := by
    change mixedMoment B node5430 node5430Labels = _
    exact sound5430 B hB hF
  have h5431 : mixedVector B (Sum.inr 5431) = Sparse.eval nodeValue5431 (mixedVector B) := by
    change mixedMoment B node5431 node5431Labels = _
    exact sound5431 B hB hF
  have h5447 : mixedVector B (Sum.inr 5447) = Sparse.eval nodeValue5447 (mixedVector B) := by
    change mixedMoment B node5447 node5447Labels = _
    exact sound5447 B hB hF
  have h5471 : mixedVector B (Sum.inr 5471) = Sparse.eval nodeValue5471 (mixedVector B) := by
    change mixedMoment B node5471 node5471Labels = _
    exact sound5471 B hB hF
  have h5472 : mixedVector B (Sum.inr 5472) = Sparse.eval nodeValue5472 (mixedVector B) := by
    change mixedMoment B node5472 node5472Labels = _
    exact sound5472 B hB hF
  have h5482 : mixedVector B (Sum.inr 5482) = Sparse.eval nodeValue5482 (mixedVector B) := by
    change mixedMoment B node5482 node5482Labels = _
    exact sound5482 B hB hF
  simpa only [sourceForm941, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4791, h4795, h4799, h4863, h5181, h5184, h5243, h5348, h5350, h5354, h5379, h5383, h5406, h5414, h5429, h5430, h5431, h5447, h5471, h5472, h5482, reducedSource821] using sourceEq941 B hB

theorem rowSound821 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row821 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck821, numericCheck821, reducedZero821 B hB hF, mul_zero]

theorem reducedZero822 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource822 (mixedVector B) = 0 := by
  have h2008 : mixedVector B (Sum.inr 2008) = Sparse.eval nodeValue2008 (mixedVector B) := by
    change mixedMoment B node2008 node2008Labels = _
    exact sound2008 B hB hF
  have h2012 : mixedVector B (Sum.inr 2012) = Sparse.eval nodeValue2012 (mixedVector B) := by
    change mixedMoment B node2012 node2012Labels = _
    exact sound2012 B hB hF
  have h2017 : mixedVector B (Sum.inr 2017) = Sparse.eval nodeValue2017 (mixedVector B) := by
    change mixedMoment B node2017 node2017Labels = _
    exact sound2017 B hB hF
  have h2232 : mixedVector B (Sum.inr 2232) = Sparse.eval nodeValue2232 (mixedVector B) := by
    change mixedMoment B node2232 node2232Labels = _
    exact sound2232 B hB hF
  have h2609 : mixedVector B (Sum.inr 2609) = Sparse.eval nodeValue2609 (mixedVector B) := by
    change mixedMoment B node2609 node2609Labels = _
    exact sound2609 B hB hF
  have h2614 : mixedVector B (Sum.inr 2614) = Sparse.eval nodeValue2614 (mixedVector B) := by
    change mixedMoment B node2614 node2614Labels = _
    exact sound2614 B hB hF
  have h2697 : mixedVector B (Sum.inr 2697) = Sparse.eval nodeValue2697 (mixedVector B) := by
    change mixedMoment B node2697 node2697Labels = _
    exact sound2697 B hB hF
  have h3685 : mixedVector B (Sum.inr 3685) = Sparse.eval nodeValue3685 (mixedVector B) := by
    change mixedMoment B node3685 node3685Labels = _
    exact sound3685 B hB hF
  have h3688 : mixedVector B (Sum.inr 3688) = Sparse.eval nodeValue3688 (mixedVector B) := by
    change mixedMoment B node3688 node3688Labels = _
    exact sound3688 B hB hF
  have h3818 : mixedVector B (Sum.inr 3818) = Sparse.eval nodeValue3818 (mixedVector B) := by
    change mixedMoment B node3818 node3818Labels = _
    exact sound3818 B hB hF
  have h3819 : mixedVector B (Sum.inr 3819) = Sparse.eval nodeValue3819 (mixedVector B) := by
    change mixedMoment B node3819 node3819Labels = _
    exact sound3819 B hB hF
  have h3832 : mixedVector B (Sum.inr 3832) = Sparse.eval nodeValue3832 (mixedVector B) := by
    change mixedMoment B node3832 node3832Labels = _
    exact sound3832 B hB hF
  have h3846 : mixedVector B (Sum.inr 3846) = Sparse.eval nodeValue3846 (mixedVector B) := by
    change mixedMoment B node3846 node3846Labels = _
    exact sound3846 B hB hF
  have h3847 : mixedVector B (Sum.inr 3847) = Sparse.eval nodeValue3847 (mixedVector B) := by
    change mixedMoment B node3847 node3847Labels = _
    exact sound3847 B hB hF
  have h3848 : mixedVector B (Sum.inr 3848) = Sparse.eval nodeValue3848 (mixedVector B) := by
    change mixedMoment B node3848 node3848Labels = _
    exact sound3848 B hB hF
  have h3867 : mixedVector B (Sum.inr 3867) = Sparse.eval nodeValue3867 (mixedVector B) := by
    change mixedMoment B node3867 node3867Labels = _
    exact sound3867 B hB hF
  have h3875 : mixedVector B (Sum.inr 3875) = Sparse.eval nodeValue3875 (mixedVector B) := by
    change mixedMoment B node3875 node3875Labels = _
    exact sound3875 B hB hF
  have h3909 : mixedVector B (Sum.inr 3909) = Sparse.eval nodeValue3909 (mixedVector B) := by
    change mixedMoment B node3909 node3909Labels = _
    exact sound3909 B hB hF
  have h3976 : mixedVector B (Sum.inr 3976) = Sparse.eval nodeValue3976 (mixedVector B) := by
    change mixedMoment B node3976 node3976Labels = _
    exact sound3976 B hB hF
  have h3992 : mixedVector B (Sum.inr 3992) = Sparse.eval nodeValue3992 (mixedVector B) := by
    change mixedMoment B node3992 node3992Labels = _
    exact sound3992 B hB hF
  have h4002 : mixedVector B (Sum.inr 4002) = Sparse.eval nodeValue4002 (mixedVector B) := by
    change mixedMoment B node4002 node4002Labels = _
    exact sound4002 B hB hF
  simpa only [sourceForm942, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2008, h2012, h2017, h2232, h2609, h2614, h2697, h3685, h3688, h3818, h3819, h3832, h3846, h3847, h3848, h3867, h3875, h3909, h3976, h3992, h4002, reducedSource822] using sourceEq942 B hB

theorem rowSound822 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row822 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck822, numericCheck822, reducedZero822 B hB hF, mul_zero]

theorem reducedZero823 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource823 (mixedVector B) = 0 := by
  have h2074 : mixedVector B (Sum.inr 2074) = Sparse.eval nodeValue2074 (mixedVector B) := by
    change mixedMoment B node2074 node2074Labels = _
    exact sound2074 B hB hF
  have h2076 : mixedVector B (Sum.inr 2076) = Sparse.eval nodeValue2076 (mixedVector B) := by
    change mixedMoment B node2076 node2076Labels = _
    exact sound2076 B hB hF
  have h2104 : mixedVector B (Sum.inr 2104) = Sparse.eval nodeValue2104 (mixedVector B) := by
    change mixedMoment B node2104 node2104Labels = _
    exact sound2104 B hB hF
  have h2213 : mixedVector B (Sum.inr 2213) = Sparse.eval nodeValue2213 (mixedVector B) := by
    change mixedMoment B node2213 node2213Labels = _
    exact sound2213 B hB hF
  have h3488 : mixedVector B (Sum.inr 3488) = Sparse.eval nodeValue3488 (mixedVector B) := by
    change mixedMoment B node3488 node3488Labels = _
    exact sound3488 B hB hF
  have h3491 : mixedVector B (Sum.inr 3491) = Sparse.eval nodeValue3491 (mixedVector B) := by
    change mixedMoment B node3491 node3491Labels = _
    exact sound3491 B hB hF
  have h3524 : mixedVector B (Sum.inr 3524) = Sparse.eval nodeValue3524 (mixedVector B) := by
    change mixedMoment B node3524 node3524Labels = _
    exact sound3524 B hB hF
  have h3720 : mixedVector B (Sum.inr 3720) = Sparse.eval nodeValue3720 (mixedVector B) := by
    change mixedMoment B node3720 node3720Labels = _
    exact sound3720 B hB hF
  have h3734 : mixedVector B (Sum.inr 3734) = Sparse.eval nodeValue3734 (mixedVector B) := by
    change mixedMoment B node3734 node3734Labels = _
    exact sound3734 B hB hF
  have h3750 : mixedVector B (Sum.inr 3750) = Sparse.eval nodeValue3750 (mixedVector B) := by
    change mixedMoment B node3750 node3750Labels = _
    exact sound3750 B hB hF
  have h3768 : mixedVector B (Sum.inr 3768) = Sparse.eval nodeValue3768 (mixedVector B) := by
    change mixedMoment B node3768 node3768Labels = _
    exact sound3768 B hB hF
  have h3769 : mixedVector B (Sum.inr 3769) = Sparse.eval nodeValue3769 (mixedVector B) := by
    change mixedMoment B node3769 node3769Labels = _
    exact sound3769 B hB hF
  have h3812 : mixedVector B (Sum.inr 3812) = Sparse.eval nodeValue3812 (mixedVector B) := by
    change mixedMoment B node3812 node3812Labels = _
    exact sound3812 B hB hF
  have h3869 : mixedVector B (Sum.inr 3869) = Sparse.eval nodeValue3869 (mixedVector B) := by
    change mixedMoment B node3869 node3869Labels = _
    exact sound3869 B hB hF
  have h3871 : mixedVector B (Sum.inr 3871) = Sparse.eval nodeValue3871 (mixedVector B) := by
    change mixedMoment B node3871 node3871Labels = _
    exact sound3871 B hB hF
  have h3874 : mixedVector B (Sum.inr 3874) = Sparse.eval nodeValue3874 (mixedVector B) := by
    change mixedMoment B node3874 node3874Labels = _
    exact sound3874 B hB hF
  have h3882 : mixedVector B (Sum.inr 3882) = Sparse.eval nodeValue3882 (mixedVector B) := by
    change mixedMoment B node3882 node3882Labels = _
    exact sound3882 B hB hF
  have h3956 : mixedVector B (Sum.inr 3956) = Sparse.eval nodeValue3956 (mixedVector B) := by
    change mixedMoment B node3956 node3956Labels = _
    exact sound3956 B hB hF
  have h3957 : mixedVector B (Sum.inr 3957) = Sparse.eval nodeValue3957 (mixedVector B) := by
    change mixedMoment B node3957 node3957Labels = _
    exact sound3957 B hB hF
  have h3980 : mixedVector B (Sum.inr 3980) = Sparse.eval nodeValue3980 (mixedVector B) := by
    change mixedMoment B node3980 node3980Labels = _
    exact sound3980 B hB hF
  have h4026 : mixedVector B (Sum.inr 4026) = Sparse.eval nodeValue4026 (mixedVector B) := by
    change mixedMoment B node4026 node4026Labels = _
    exact sound4026 B hB hF
  simpa only [sourceForm943, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2074, h2076, h2104, h2213, h3488, h3491, h3524, h3720, h3734, h3750, h3768, h3769, h3812, h3869, h3871, h3874, h3882, h3956, h3957, h3980, h4026, reducedSource823] using sourceEq943 B hB

theorem rowSound823 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row823 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck823, numericCheck823, reducedZero823 B hB hF, mul_zero]

theorem reducedZero824 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource824 (mixedVector B) = 0 := by
  have h3849 : mixedVector B (Sum.inr 3849) = Sparse.eval nodeValue3849 (mixedVector B) := by
    change mixedMoment B node3849 node3849Labels = _
    exact sound3849 B hB hF
  have h3953 : mixedVector B (Sum.inr 3953) = Sparse.eval nodeValue3953 (mixedVector B) := by
    change mixedMoment B node3953 node3953Labels = _
    exact sound3953 B hB hF
  have h3954 : mixedVector B (Sum.inr 3954) = Sparse.eval nodeValue3954 (mixedVector B) := by
    change mixedMoment B node3954 node3954Labels = _
    exact sound3954 B hB hF
  have h3957 : mixedVector B (Sum.inr 3957) = Sparse.eval nodeValue3957 (mixedVector B) := by
    change mixedMoment B node3957 node3957Labels = _
    exact sound3957 B hB hF
  have h4046 : mixedVector B (Sum.inr 4046) = Sparse.eval nodeValue4046 (mixedVector B) := by
    change mixedMoment B node4046 node4046Labels = _
    exact sound4046 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm944, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3849, h3953, h3954, h3957, h4046, h4091, reducedSource824] using sourceEq944 B hB

theorem rowSound824 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row824 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck824, numericCheck824, reducedZero824 B hB hF, mul_zero]

theorem reducedZero825 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource825 (mixedVector B) = 0 := by
  have h2858 : mixedVector B (Sum.inr 2858) = Sparse.eval nodeValue2858 (mixedVector B) := by
    change mixedMoment B node2858 node2858Labels = _
    exact sound2858 B hB hF
  have h3176 : mixedVector B (Sum.inr 3176) = Sparse.eval nodeValue3176 (mixedVector B) := by
    change mixedMoment B node3176 node3176Labels = _
    exact sound3176 B hB hF
  have h3179 : mixedVector B (Sum.inr 3179) = Sparse.eval nodeValue3179 (mixedVector B) := by
    change mixedMoment B node3179 node3179Labels = _
    exact sound3179 B hB hF
  have h3199 : mixedVector B (Sum.inr 3199) = Sparse.eval nodeValue3199 (mixedVector B) := by
    change mixedMoment B node3199 node3199Labels = _
    exact sound3199 B hB hF
  have h3954 : mixedVector B (Sum.inr 3954) = Sparse.eval nodeValue3954 (mixedVector B) := by
    change mixedMoment B node3954 node3954Labels = _
    exact sound3954 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm945, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2858, h3176, h3179, h3199, h3954, h4091, reducedSource825] using sourceEq945 B hB

theorem rowSound825 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row825 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck825, numericCheck825, reducedZero825 B hB hF, mul_zero]

theorem reducedZero826 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource826 (mixedVector B) = 0 := by
  have h3179 : mixedVector B (Sum.inr 3179) = Sparse.eval nodeValue3179 (mixedVector B) := by
    change mixedMoment B node3179 node3179Labels = _
    exact sound3179 B hB hF
  have h3731 : mixedVector B (Sum.inr 3731) = Sparse.eval nodeValue3731 (mixedVector B) := by
    change mixedMoment B node3731 node3731Labels = _
    exact sound3731 B hB hF
  have h3954 : mixedVector B (Sum.inr 3954) = Sparse.eval nodeValue3954 (mixedVector B) := by
    change mixedMoment B node3954 node3954Labels = _
    exact sound3954 B hB hF
  have h4025 : mixedVector B (Sum.inr 4025) = Sparse.eval nodeValue4025 (mixedVector B) := by
    change mixedMoment B node4025 node4025Labels = _
    exact sound4025 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm946, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3179, h3731, h3954, h4025, h4091, reducedSource826] using sourceEq946 B hB

theorem rowSound826 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row826 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck826, numericCheck826, reducedZero826 B hB hF, mul_zero]

theorem reducedZero827 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource827 (mixedVector B) = 0 := by
  have h2859 : mixedVector B (Sum.inr 2859) = Sparse.eval nodeValue2859 (mixedVector B) := by
    change mixedMoment B node2859 node2859Labels = _
    exact sound2859 B hB hF
  have h3685 : mixedVector B (Sum.inr 3685) = Sparse.eval nodeValue3685 (mixedVector B) := by
    change mixedMoment B node3685 node3685Labels = _
    exact sound3685 B hB hF
  have h3935 : mixedVector B (Sum.inr 3935) = Sparse.eval nodeValue3935 (mixedVector B) := by
    change mixedMoment B node3935 node3935Labels = _
    exact sound3935 B hB hF
  have h3953 : mixedVector B (Sum.inr 3953) = Sparse.eval nodeValue3953 (mixedVector B) := by
    change mixedMoment B node3953 node3953Labels = _
    exact sound3953 B hB hF
  have h3954 : mixedVector B (Sum.inr 3954) = Sparse.eval nodeValue3954 (mixedVector B) := by
    change mixedMoment B node3954 node3954Labels = _
    exact sound3954 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm947, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2859, h3685, h3935, h3953, h3954, h4091, reducedSource827] using sourceEq947 B hB

theorem rowSound827 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row827 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck827, numericCheck827, reducedZero827 B hB hF, mul_zero]

theorem reducedZero828 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource828 (mixedVector B) = 0 := by
  have h3176 : mixedVector B (Sum.inr 3176) = Sparse.eval nodeValue3176 (mixedVector B) := by
    change mixedMoment B node3176 node3176Labels = _
    exact sound3176 B hB hF
  have h3724 : mixedVector B (Sum.inr 3724) = Sparse.eval nodeValue3724 (mixedVector B) := by
    change mixedMoment B node3724 node3724Labels = _
    exact sound3724 B hB hF
  have h3935 : mixedVector B (Sum.inr 3935) = Sparse.eval nodeValue3935 (mixedVector B) := by
    change mixedMoment B node3935 node3935Labels = _
    exact sound3935 B hB hF
  have h3949 : mixedVector B (Sum.inr 3949) = Sparse.eval nodeValue3949 (mixedVector B) := by
    change mixedMoment B node3949 node3949Labels = _
    exact sound3949 B hB hF
  have h3954 : mixedVector B (Sum.inr 3954) = Sparse.eval nodeValue3954 (mixedVector B) := by
    change mixedMoment B node3954 node3954Labels = _
    exact sound3954 B hB hF
  have h3972 : mixedVector B (Sum.inr 3972) = Sparse.eval nodeValue3972 (mixedVector B) := by
    change mixedMoment B node3972 node3972Labels = _
    exact sound3972 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm948, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3176, h3724, h3935, h3949, h3954, h3972, h4091, reducedSource828] using sourceEq948 B hB

theorem rowSound828 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row828 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck828, numericCheck828, reducedZero828 B hB hF, mul_zero]

theorem reducedZero829 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource829 (mixedVector B) = 0 := by
  have h2864 : mixedVector B (Sum.inr 2864) = Sparse.eval nodeValue2864 (mixedVector B) := by
    change mixedMoment B node2864 node2864Labels = _
    exact sound2864 B hB hF
  have h3692 : mixedVector B (Sum.inr 3692) = Sparse.eval nodeValue3692 (mixedVector B) := by
    change mixedMoment B node3692 node3692Labels = _
    exact sound3692 B hB hF
  have h3949 : mixedVector B (Sum.inr 3949) = Sparse.eval nodeValue3949 (mixedVector B) := by
    change mixedMoment B node3949 node3949Labels = _
    exact sound3949 B hB hF
  have h3954 : mixedVector B (Sum.inr 3954) = Sparse.eval nodeValue3954 (mixedVector B) := by
    change mixedMoment B node3954 node3954Labels = _
    exact sound3954 B hB hF
  have h3957 : mixedVector B (Sum.inr 3957) = Sparse.eval nodeValue3957 (mixedVector B) := by
    change mixedMoment B node3957 node3957Labels = _
    exact sound3957 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm949, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2864, h3692, h3949, h3954, h3957, h4091, reducedSource829] using sourceEq949 B hB

theorem rowSound829 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row829 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck829, numericCheck829, reducedZero829 B hB hF, mul_zero]

theorem reducedZero830 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource830 (mixedVector B) = 0 := by
  have h3199 : mixedVector B (Sum.inr 3199) = Sparse.eval nodeValue3199 (mixedVector B) := by
    change mixedMoment B node3199 node3199Labels = _
    exact sound3199 B hB hF
  have h3685 : mixedVector B (Sum.inr 3685) = Sparse.eval nodeValue3685 (mixedVector B) := by
    change mixedMoment B node3685 node3685Labels = _
    exact sound3685 B hB hF
  have h3692 : mixedVector B (Sum.inr 3692) = Sparse.eval nodeValue3692 (mixedVector B) := by
    change mixedMoment B node3692 node3692Labels = _
    exact sound3692 B hB hF
  have h3801 : mixedVector B (Sum.inr 3801) = Sparse.eval nodeValue3801 (mixedVector B) := by
    change mixedMoment B node3801 node3801Labels = _
    exact sound3801 B hB hF
  have h3954 : mixedVector B (Sum.inr 3954) = Sparse.eval nodeValue3954 (mixedVector B) := by
    change mixedMoment B node3954 node3954Labels = _
    exact sound3954 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm950, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3199, h3685, h3692, h3801, h3954, h4091, reducedSource830] using sourceEq950 B hB

theorem rowSound830 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row830 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck830, numericCheck830, reducedZero830 B hB hF, mul_zero]

theorem reducedZero831 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource831 (mixedVector B) = 0 := by
  have h3030 : mixedVector B (Sum.inr 3030) = Sparse.eval nodeValue3030 (mixedVector B) := by
    change mixedMoment B node3030 node3030Labels = _
    exact sound3030 B hB hF
  have h3724 : mixedVector B (Sum.inr 3724) = Sparse.eval nodeValue3724 (mixedVector B) := by
    change mixedMoment B node3724 node3724Labels = _
    exact sound3724 B hB hF
  have h3731 : mixedVector B (Sum.inr 3731) = Sparse.eval nodeValue3731 (mixedVector B) := by
    change mixedMoment B node3731 node3731Labels = _
    exact sound3731 B hB hF
  have h3849 : mixedVector B (Sum.inr 3849) = Sparse.eval nodeValue3849 (mixedVector B) := by
    change mixedMoment B node3849 node3849Labels = _
    exact sound3849 B hB hF
  have h3954 : mixedVector B (Sum.inr 3954) = Sparse.eval nodeValue3954 (mixedVector B) := by
    change mixedMoment B node3954 node3954Labels = _
    exact sound3954 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm951, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3030, h3724, h3731, h3849, h3954, h4091, reducedSource831] using sourceEq951 B hB

theorem rowSound831 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row831 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck831, numericCheck831, reducedZero831 B hB hF, mul_zero]

theorem sourceRowsAt816 : MixedData.sourceRows (816 : Fin 2425) =
    MixedData.row816 := by decide +kernel

theorem sourceRowsAt817 : MixedData.sourceRows (817 : Fin 2425) =
    MixedData.row817 := by decide +kernel

theorem sourceRowsAt818 : MixedData.sourceRows (818 : Fin 2425) =
    MixedData.row818 := by decide +kernel

theorem sourceRowsAt819 : MixedData.sourceRows (819 : Fin 2425) =
    MixedData.row819 := by decide +kernel

theorem sourceRowsAt820 : MixedData.sourceRows (820 : Fin 2425) =
    MixedData.row820 := by decide +kernel

theorem sourceRowsAt821 : MixedData.sourceRows (821 : Fin 2425) =
    MixedData.row821 := by decide +kernel

theorem sourceRowsAt822 : MixedData.sourceRows (822 : Fin 2425) =
    MixedData.row822 := by decide +kernel

theorem sourceRowsAt823 : MixedData.sourceRows (823 : Fin 2425) =
    MixedData.row823 := by decide +kernel

theorem sourceRowsAt824 : MixedData.sourceRows (824 : Fin 2425) =
    MixedData.row824 := by decide +kernel

theorem sourceRowsAt825 : MixedData.sourceRows (825 : Fin 2425) =
    MixedData.row825 := by decide +kernel

theorem sourceRowsAt826 : MixedData.sourceRows (826 : Fin 2425) =
    MixedData.row826 := by decide +kernel

theorem sourceRowsAt827 : MixedData.sourceRows (827 : Fin 2425) =
    MixedData.row827 := by decide +kernel

theorem sourceRowsAt828 : MixedData.sourceRows (828 : Fin 2425) =
    MixedData.row828 := by decide +kernel

theorem sourceRowsAt829 : MixedData.sourceRows (829 : Fin 2425) =
    MixedData.row829 := by decide +kernel

theorem sourceRowsAt830 : MixedData.sourceRows (830 : Fin 2425) =
    MixedData.row830 := by decide +kernel

theorem sourceRowsAt831 : MixedData.sourceRows (831 : Fin 2425) =
    MixedData.row831 := by decide +kernel

theorem chunkSound51 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 51) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 816 ∨ k.val = 817 ∨ k.val = 818 ∨ k.val = 819 ∨ k.val = 820 ∨ k.val = 821 ∨ k.val = 822 ∨ k.val = 823 ∨ k.val = 824 ∨ k.val = 825 ∨ k.val = 826 ∨ k.val = 827 ∨ k.val = 828 ∨ k.val = 829 ∨ k.val = 830 ∨ k.val = 831 := by omega
  rcases heq with h816 | h817 | h818 | h819 | h820 | h821 | h822 | h823 | h824 | h825 | h826 | h827 | h828 | h829 | h830 | h831
  · have he : k = (816 : Fin 2425) := Fin.ext h816
    subst k
    rw [sourceRowsAt816]
    exact rowSound816 B hB hF
  · have he : k = (817 : Fin 2425) := Fin.ext h817
    subst k
    rw [sourceRowsAt817]
    exact rowSound817 B hB hF
  · have he : k = (818 : Fin 2425) := Fin.ext h818
    subst k
    rw [sourceRowsAt818]
    exact rowSound818 B hB hF
  · have he : k = (819 : Fin 2425) := Fin.ext h819
    subst k
    rw [sourceRowsAt819]
    exact rowSound819 B hB hF
  · have he : k = (820 : Fin 2425) := Fin.ext h820
    subst k
    rw [sourceRowsAt820]
    exact rowSound820 B hB hF
  · have he : k = (821 : Fin 2425) := Fin.ext h821
    subst k
    rw [sourceRowsAt821]
    exact rowSound821 B hB hF
  · have he : k = (822 : Fin 2425) := Fin.ext h822
    subst k
    rw [sourceRowsAt822]
    exact rowSound822 B hB hF
  · have he : k = (823 : Fin 2425) := Fin.ext h823
    subst k
    rw [sourceRowsAt823]
    exact rowSound823 B hB hF
  · have he : k = (824 : Fin 2425) := Fin.ext h824
    subst k
    rw [sourceRowsAt824]
    exact rowSound824 B hB hF
  · have he : k = (825 : Fin 2425) := Fin.ext h825
    subst k
    rw [sourceRowsAt825]
    exact rowSound825 B hB hF
  · have he : k = (826 : Fin 2425) := Fin.ext h826
    subst k
    rw [sourceRowsAt826]
    exact rowSound826 B hB hF
  · have he : k = (827 : Fin 2425) := Fin.ext h827
    subst k
    rw [sourceRowsAt827]
    exact rowSound827 B hB hF
  · have he : k = (828 : Fin 2425) := Fin.ext h828
    subst k
    rw [sourceRowsAt828]
    exact rowSound828 B hB hF
  · have he : k = (829 : Fin 2425) := Fin.ext h829
    subst k
    rw [sourceRowsAt829]
    exact rowSound829 B hB hF
  · have he : k = (830 : Fin 2425) := Fin.ext h830
    subst k
    rw [sourceRowsAt830]
    exact rowSound830 B hB hF
  · have he : k = (831 : Fin 2425) := Fin.ext h831
    subst k
    rw [sourceRowsAt831]
    exact rowSound831 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
