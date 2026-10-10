import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound53
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources31

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero848 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource848 (mixedVector B) = 0 := by
  have h2951 : mixedVector B (Sum.inr 2951) = Sparse.eval nodeValue2951 (mixedVector B) := by
    change mixedMoment B node2951 node2951Labels = _
    exact sound2951 B hB hF
  have h3871 : mixedVector B (Sum.inr 3871) = Sparse.eval nodeValue3871 (mixedVector B) := by
    change mixedMoment B node3871 node3871Labels = _
    exact sound3871 B hB hF
  have h3927 : mixedVector B (Sum.inr 3927) = Sparse.eval nodeValue3927 (mixedVector B) := by
    change mixedMoment B node3927 node3927Labels = _
    exact sound3927 B hB hF
  have h3974 : mixedVector B (Sum.inr 3974) = Sparse.eval nodeValue3974 (mixedVector B) := by
    change mixedMoment B node3974 node3974Labels = _
    exact sound3974 B hB hF
  have h3978 : mixedVector B (Sum.inr 3978) = Sparse.eval nodeValue3978 (mixedVector B) := by
    change mixedMoment B node3978 node3978Labels = _
    exact sound3978 B hB hF
  have h3983 : mixedVector B (Sum.inr 3983) = Sparse.eval nodeValue3983 (mixedVector B) := by
    change mixedMoment B node3983 node3983Labels = _
    exact sound3983 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm973, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2951, h3871, h3927, h3974, h3978, h3983, h4091, reducedSource848] using sourceEq973 B hB

theorem rowSound848 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row848 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck848, numericCheck848, reducedZero848 B hB hF, mul_zero]

theorem reducedZero849 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource849 (mixedVector B) = 0 := by
  have h2984 : mixedVector B (Sum.inr 2984) = Sparse.eval nodeValue2984 (mixedVector B) := by
    change mixedMoment B node2984 node2984Labels = _
    exact sound2984 B hB hF
  have h3783 : mixedVector B (Sum.inr 3783) = Sparse.eval nodeValue3783 (mixedVector B) := by
    change mixedMoment B node3783 node3783Labels = _
    exact sound3783 B hB hF
  have h3787 : mixedVector B (Sum.inr 3787) = Sparse.eval nodeValue3787 (mixedVector B) := by
    change mixedMoment B node3787 node3787Labels = _
    exact sound3787 B hB hF
  have h3800 : mixedVector B (Sum.inr 3800) = Sparse.eval nodeValue3800 (mixedVector B) := by
    change mixedMoment B node3800 node3800Labels = _
    exact sound3800 B hB hF
  have h3871 : mixedVector B (Sum.inr 3871) = Sparse.eval nodeValue3871 (mixedVector B) := by
    change mixedMoment B node3871 node3871Labels = _
    exact sound3871 B hB hF
  have h3978 : mixedVector B (Sum.inr 3978) = Sparse.eval nodeValue3978 (mixedVector B) := by
    change mixedMoment B node3978 node3978Labels = _
    exact sound3978 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm976, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2984, h3783, h3787, h3800, h3871, h3978, h4091, reducedSource849] using sourceEq976 B hB

theorem rowSound849 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row849 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck849, numericCheck849, reducedZero849 B hB hF, mul_zero]

theorem reducedZero850 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource850 (mixedVector B) = 0 := by
  have h2615 : mixedVector B (Sum.inr 2615) = Sparse.eval nodeValue2615 (mixedVector B) := by
    change mixedMoment B node2615 node2615Labels = _
    exact sound2615 B hB hF
  have h3091 : mixedVector B (Sum.inr 3091) = Sparse.eval nodeValue3091 (mixedVector B) := by
    change mixedMoment B node3091 node3091Labels = _
    exact sound3091 B hB hF
  have h3787 : mixedVector B (Sum.inr 3787) = Sparse.eval nodeValue3787 (mixedVector B) := by
    change mixedMoment B node3787 node3787Labels = _
    exact sound3787 B hB hF
  have h3871 : mixedVector B (Sum.inr 3871) = Sparse.eval nodeValue3871 (mixedVector B) := by
    change mixedMoment B node3871 node3871Labels = _
    exact sound3871 B hB hF
  have h3875 : mixedVector B (Sum.inr 3875) = Sparse.eval nodeValue3875 (mixedVector B) := by
    change mixedMoment B node3875 node3875Labels = _
    exact sound3875 B hB hF
  have h3876 : mixedVector B (Sum.inr 3876) = Sparse.eval nodeValue3876 (mixedVector B) := by
    change mixedMoment B node3876 node3876Labels = _
    exact sound3876 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm977, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2615, h3091, h3787, h3871, h3875, h3876, h4091, reducedSource850] using sourceEq977 B hB

theorem rowSound850 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row850 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck850, numericCheck850, reducedZero850 B hB hF, mul_zero]

theorem reducedZero851 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource851 (mixedVector B) = 0 := by
  have h4797 : mixedVector B (Sum.inr 4797) = Sparse.eval nodeValue4797 (mixedVector B) := by
    change mixedMoment B node4797 node4797Labels = _
    exact sound4797 B hB hF
  have h4799 : mixedVector B (Sum.inr 4799) = Sparse.eval nodeValue4799 (mixedVector B) := by
    change mixedMoment B node4799 node4799Labels = _
    exact sound4799 B hB hF
  have h4803 : mixedVector B (Sum.inr 4803) = Sparse.eval nodeValue4803 (mixedVector B) := by
    change mixedMoment B node4803 node4803Labels = _
    exact sound4803 B hB hF
  have h4825 : mixedVector B (Sum.inr 4825) = Sparse.eval nodeValue4825 (mixedVector B) := by
    change mixedMoment B node4825 node4825Labels = _
    exact sound4825 B hB hF
  have h4851 : mixedVector B (Sum.inr 4851) = Sparse.eval nodeValue4851 (mixedVector B) := by
    change mixedMoment B node4851 node4851Labels = _
    exact sound4851 B hB hF
  have h5129 : mixedVector B (Sum.inr 5129) = Sparse.eval nodeValue5129 (mixedVector B) := by
    change mixedMoment B node5129 node5129Labels = _
    exact sound5129 B hB hF
  have h5132 : mixedVector B (Sum.inr 5132) = Sparse.eval nodeValue5132 (mixedVector B) := by
    change mixedMoment B node5132 node5132Labels = _
    exact sound5132 B hB hF
  have h5144 : mixedVector B (Sum.inr 5144) = Sparse.eval nodeValue5144 (mixedVector B) := by
    change mixedMoment B node5144 node5144Labels = _
    exact sound5144 B hB hF
  have h5249 : mixedVector B (Sum.inr 5249) = Sparse.eval nodeValue5249 (mixedVector B) := by
    change mixedMoment B node5249 node5249Labels = _
    exact sound5249 B hB hF
  have h5350 : mixedVector B (Sum.inr 5350) = Sparse.eval nodeValue5350 (mixedVector B) := by
    change mixedMoment B node5350 node5350Labels = _
    exact sound5350 B hB hF
  have h5353 : mixedVector B (Sum.inr 5353) = Sparse.eval nodeValue5353 (mixedVector B) := by
    change mixedMoment B node5353 node5353Labels = _
    exact sound5353 B hB hF
  have h5362 : mixedVector B (Sum.inr 5362) = Sparse.eval nodeValue5362 (mixedVector B) := by
    change mixedMoment B node5362 node5362Labels = _
    exact sound5362 B hB hF
  have h5377 : mixedVector B (Sum.inr 5377) = Sparse.eval nodeValue5377 (mixedVector B) := by
    change mixedMoment B node5377 node5377Labels = _
    exact sound5377 B hB hF
  have h5379 : mixedVector B (Sum.inr 5379) = Sparse.eval nodeValue5379 (mixedVector B) := by
    change mixedMoment B node5379 node5379Labels = _
    exact sound5379 B hB hF
  have h5380 : mixedVector B (Sum.inr 5380) = Sparse.eval nodeValue5380 (mixedVector B) := by
    change mixedMoment B node5380 node5380Labels = _
    exact sound5380 B hB hF
  have h5403 : mixedVector B (Sum.inr 5403) = Sparse.eval nodeValue5403 (mixedVector B) := by
    change mixedMoment B node5403 node5403Labels = _
    exact sound5403 B hB hF
  have h5406 : mixedVector B (Sum.inr 5406) = Sparse.eval nodeValue5406 (mixedVector B) := by
    change mixedMoment B node5406 node5406Labels = _
    exact sound5406 B hB hF
  have h5414 : mixedVector B (Sum.inr 5414) = Sparse.eval nodeValue5414 (mixedVector B) := by
    change mixedMoment B node5414 node5414Labels = _
    exact sound5414 B hB hF
  have h5419 : mixedVector B (Sum.inr 5419) = Sparse.eval nodeValue5419 (mixedVector B) := by
    change mixedMoment B node5419 node5419Labels = _
    exact sound5419 B hB hF
  have h5422 : mixedVector B (Sum.inr 5422) = Sparse.eval nodeValue5422 (mixedVector B) := by
    change mixedMoment B node5422 node5422Labels = _
    exact sound5422 B hB hF
  have h5424 : mixedVector B (Sum.inr 5424) = Sparse.eval nodeValue5424 (mixedVector B) := by
    change mixedMoment B node5424 node5424Labels = _
    exact sound5424 B hB hF
  have h5425 : mixedVector B (Sum.inr 5425) = Sparse.eval nodeValue5425 (mixedVector B) := by
    change mixedMoment B node5425 node5425Labels = _
    exact sound5425 B hB hF
  have h5429 : mixedVector B (Sum.inr 5429) = Sparse.eval nodeValue5429 (mixedVector B) := by
    change mixedMoment B node5429 node5429Labels = _
    exact sound5429 B hB hF
  have h5430 : mixedVector B (Sum.inr 5430) = Sparse.eval nodeValue5430 (mixedVector B) := by
    change mixedMoment B node5430 node5430Labels = _
    exact sound5430 B hB hF
  have h5447 : mixedVector B (Sum.inr 5447) = Sparse.eval nodeValue5447 (mixedVector B) := by
    change mixedMoment B node5447 node5447Labels = _
    exact sound5447 B hB hF
  have h5478 : mixedVector B (Sum.inr 5478) = Sparse.eval nodeValue5478 (mixedVector B) := by
    change mixedMoment B node5478 node5478Labels = _
    exact sound5478 B hB hF
  have h5480 : mixedVector B (Sum.inr 5480) = Sparse.eval nodeValue5480 (mixedVector B) := by
    change mixedMoment B node5480 node5480Labels = _
    exact sound5480 B hB hF
  have h5481 : mixedVector B (Sum.inr 5481) = Sparse.eval nodeValue5481 (mixedVector B) := by
    change mixedMoment B node5481 node5481Labels = _
    exact sound5481 B hB hF
  have h5482 : mixedVector B (Sum.inr 5482) = Sparse.eval nodeValue5482 (mixedVector B) := by
    change mixedMoment B node5482 node5482Labels = _
    exact sound5482 B hB hF
  simpa only [sourceForm978, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4797, h4799, h4803, h4825, h4851, h5129, h5132, h5144, h5249, h5350, h5353, h5362, h5377, h5379, h5380, h5403, h5406, h5414, h5419, h5422, h5424, h5425, h5429, h5430, h5447, h5478, h5480, h5481, h5482, reducedSource851] using sourceEq978 B hB

theorem rowSound851 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row851 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck851, numericCheck851, reducedZero851 B hB hF, mul_zero]

theorem reducedZero852 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource852 (mixedVector B) = 0 := by
  have h2070 : mixedVector B (Sum.inr 2070) = Sparse.eval nodeValue2070 (mixedVector B) := by
    change mixedMoment B node2070 node2070Labels = _
    exact sound2070 B hB hF
  have h2073 : mixedVector B (Sum.inr 2073) = Sparse.eval nodeValue2073 (mixedVector B) := by
    change mixedMoment B node2073 node2073Labels = _
    exact sound2073 B hB hF
  have h2076 : mixedVector B (Sum.inr 2076) = Sparse.eval nodeValue2076 (mixedVector B) := by
    change mixedMoment B node2076 node2076Labels = _
    exact sound2076 B hB hF
  have h2088 : mixedVector B (Sum.inr 2088) = Sparse.eval nodeValue2088 (mixedVector B) := by
    change mixedMoment B node2088 node2088Labels = _
    exact sound2088 B hB hF
  have h2195 : mixedVector B (Sum.inr 2195) = Sparse.eval nodeValue2195 (mixedVector B) := by
    change mixedMoment B node2195 node2195Labels = _
    exact sound2195 B hB hF
  have h2545 : mixedVector B (Sum.inr 2545) = Sparse.eval nodeValue2545 (mixedVector B) := by
    change mixedMoment B node2545 node2545Labels = _
    exact sound2545 B hB hF
  have h2551 : mixedVector B (Sum.inr 2551) = Sparse.eval nodeValue2551 (mixedVector B) := by
    change mixedMoment B node2551 node2551Labels = _
    exact sound2551 B hB hF
  have h2566 : mixedVector B (Sum.inr 2566) = Sparse.eval nodeValue2566 (mixedVector B) := by
    change mixedMoment B node2566 node2566Labels = _
    exact sound2566 B hB hF
  have h2708 : mixedVector B (Sum.inr 2708) = Sparse.eval nodeValue2708 (mixedVector B) := by
    change mixedMoment B node2708 node2708Labels = _
    exact sound2708 B hB hF
  have h3716 : mixedVector B (Sum.inr 3716) = Sparse.eval nodeValue3716 (mixedVector B) := by
    change mixedMoment B node3716 node3716Labels = _
    exact sound3716 B hB hF
  have h3720 : mixedVector B (Sum.inr 3720) = Sparse.eval nodeValue3720 (mixedVector B) := by
    change mixedMoment B node3720 node3720Labels = _
    exact sound3720 B hB hF
  have h3726 : mixedVector B (Sum.inr 3726) = Sparse.eval nodeValue3726 (mixedVector B) := by
    change mixedMoment B node3726 node3726Labels = _
    exact sound3726 B hB hF
  have h3748 : mixedVector B (Sum.inr 3748) = Sparse.eval nodeValue3748 (mixedVector B) := by
    change mixedMoment B node3748 node3748Labels = _
    exact sound3748 B hB hF
  have h3750 : mixedVector B (Sum.inr 3750) = Sparse.eval nodeValue3750 (mixedVector B) := by
    change mixedMoment B node3750 node3750Labels = _
    exact sound3750 B hB hF
  have h3761 : mixedVector B (Sum.inr 3761) = Sparse.eval nodeValue3761 (mixedVector B) := by
    change mixedMoment B node3761 node3761Labels = _
    exact sound3761 B hB hF
  have h3810 : mixedVector B (Sum.inr 3810) = Sparse.eval nodeValue3810 (mixedVector B) := by
    change mixedMoment B node3810 node3810Labels = _
    exact sound3810 B hB hF
  have h3812 : mixedVector B (Sum.inr 3812) = Sparse.eval nodeValue3812 (mixedVector B) := by
    change mixedMoment B node3812 node3812Labels = _
    exact sound3812 B hB hF
  have h3825 : mixedVector B (Sum.inr 3825) = Sparse.eval nodeValue3825 (mixedVector B) := by
    change mixedMoment B node3825 node3825Labels = _
    exact sound3825 B hB hF
  have h3829 : mixedVector B (Sum.inr 3829) = Sparse.eval nodeValue3829 (mixedVector B) := by
    change mixedMoment B node3829 node3829Labels = _
    exact sound3829 B hB hF
  have h3840 : mixedVector B (Sum.inr 3840) = Sparse.eval nodeValue3840 (mixedVector B) := by
    change mixedMoment B node3840 node3840Labels = _
    exact sound3840 B hB hF
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
  have h3978 : mixedVector B (Sum.inr 3978) = Sparse.eval nodeValue3978 (mixedVector B) := by
    change mixedMoment B node3978 node3978Labels = _
    exact sound3978 B hB hF
  have h3979 : mixedVector B (Sum.inr 3979) = Sparse.eval nodeValue3979 (mixedVector B) := by
    change mixedMoment B node3979 node3979Labels = _
    exact sound3979 B hB hF
  have h3980 : mixedVector B (Sum.inr 3980) = Sparse.eval nodeValue3980 (mixedVector B) := by
    change mixedMoment B node3980 node3980Labels = _
    exact sound3980 B hB hF
  have h3990 : mixedVector B (Sum.inr 3990) = Sparse.eval nodeValue3990 (mixedVector B) := by
    change mixedMoment B node3990 node3990Labels = _
    exact sound3990 B hB hF
  have h3994 : mixedVector B (Sum.inr 3994) = Sparse.eval nodeValue3994 (mixedVector B) := by
    change mixedMoment B node3994 node3994Labels = _
    exact sound3994 B hB hF
  simpa only [sourceForm979, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2070, h2073, h2076, h2088, h2195, h2545, h2551, h2566, h2708, h3716, h3720, h3726, h3748, h3750, h3761, h3810, h3812, h3825, h3829, h3840, h3869, h3871, h3874, h3882, h3978, h3979, h3980, h3990, h3994, reducedSource852] using sourceEq979 B hB

theorem rowSound852 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row852 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck852, numericCheck852, reducedZero852 B hB hF, mul_zero]

theorem reducedZero853 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource853 (mixedVector B) = 0 := by
  have h2015 : mixedVector B (Sum.inr 2015) = Sparse.eval nodeValue2015 (mixedVector B) := by
    change mixedMoment B node2015 node2015Labels = _
    exact sound2015 B hB hF
  have h2017 : mixedVector B (Sum.inr 2017) = Sparse.eval nodeValue2017 (mixedVector B) := by
    change mixedMoment B node2017 node2017Labels = _
    exact sound2017 B hB hF
  have h2021 : mixedVector B (Sum.inr 2021) = Sparse.eval nodeValue2021 (mixedVector B) := by
    change mixedMoment B node2021 node2021Labels = _
    exact sound2021 B hB hF
  have h2044 : mixedVector B (Sum.inr 2044) = Sparse.eval nodeValue2044 (mixedVector B) := by
    change mixedMoment B node2044 node2044Labels = _
    exact sound2044 B hB hF
  have h2240 : mixedVector B (Sum.inr 2240) = Sparse.eval nodeValue2240 (mixedVector B) := by
    change mixedMoment B node2240 node2240Labels = _
    exact sound2240 B hB hF
  have h3499 : mixedVector B (Sum.inr 3499) = Sparse.eval nodeValue3499 (mixedVector B) := by
    change mixedMoment B node3499 node3499Labels = _
    exact sound3499 B hB hF
  have h3502 : mixedVector B (Sum.inr 3502) = Sparse.eval nodeValue3502 (mixedVector B) := by
    change mixedMoment B node3502 node3502Labels = _
    exact sound3502 B hB hF
  have h3516 : mixedVector B (Sum.inr 3516) = Sparse.eval nodeValue3516 (mixedVector B) := by
    change mixedMoment B node3516 node3516Labels = _
    exact sound3516 B hB hF
  have h3557 : mixedVector B (Sum.inr 3557) = Sparse.eval nodeValue3557 (mixedVector B) := by
    change mixedMoment B node3557 node3557Labels = _
    exact sound3557 B hB hF
  have h3688 : mixedVector B (Sum.inr 3688) = Sparse.eval nodeValue3688 (mixedVector B) := by
    change mixedMoment B node3688 node3688Labels = _
    exact sound3688 B hB hF
  have h3691 : mixedVector B (Sum.inr 3691) = Sparse.eval nodeValue3691 (mixedVector B) := by
    change mixedMoment B node3691 node3691Labels = _
    exact sound3691 B hB hF
  have h3700 : mixedVector B (Sum.inr 3700) = Sparse.eval nodeValue3700 (mixedVector B) := by
    change mixedMoment B node3700 node3700Labels = _
    exact sound3700 B hB hF
  have h3819 : mixedVector B (Sum.inr 3819) = Sparse.eval nodeValue3819 (mixedVector B) := by
    change mixedMoment B node3819 node3819Labels = _
    exact sound3819 B hB hF
  have h3822 : mixedVector B (Sum.inr 3822) = Sparse.eval nodeValue3822 (mixedVector B) := by
    change mixedMoment B node3822 node3822Labels = _
    exact sound3822 B hB hF
  have h3832 : mixedVector B (Sum.inr 3832) = Sparse.eval nodeValue3832 (mixedVector B) := by
    change mixedMoment B node3832 node3832Labels = _
    exact sound3832 B hB hF
  have h3835 : mixedVector B (Sum.inr 3835) = Sparse.eval nodeValue3835 (mixedVector B) := by
    change mixedMoment B node3835 node3835Labels = _
    exact sound3835 B hB hF
  have h3836 : mixedVector B (Sum.inr 3836) = Sparse.eval nodeValue3836 (mixedVector B) := by
    change mixedMoment B node3836 node3836Labels = _
    exact sound3836 B hB hF
  have h3839 : mixedVector B (Sum.inr 3839) = Sparse.eval nodeValue3839 (mixedVector B) := by
    change mixedMoment B node3839 node3839Labels = _
    exact sound3839 B hB hF
  have h3842 : mixedVector B (Sum.inr 3842) = Sparse.eval nodeValue3842 (mixedVector B) := by
    change mixedMoment B node3842 node3842Labels = _
    exact sound3842 B hB hF
  have h3843 : mixedVector B (Sum.inr 3843) = Sparse.eval nodeValue3843 (mixedVector B) := by
    change mixedMoment B node3843 node3843Labels = _
    exact sound3843 B hB hF
  have h3846 : mixedVector B (Sum.inr 3846) = Sparse.eval nodeValue3846 (mixedVector B) := by
    change mixedMoment B node3846 node3846Labels = _
    exact sound3846 B hB hF
  have h3847 : mixedVector B (Sum.inr 3847) = Sparse.eval nodeValue3847 (mixedVector B) := by
    change mixedMoment B node3847 node3847Labels = _
    exact sound3847 B hB hF
  have h3848 : mixedVector B (Sum.inr 3848) = Sparse.eval nodeValue3848 (mixedVector B) := by
    change mixedMoment B node3848 node3848Labels = _
    exact sound3848 B hB hF
  have h3900 : mixedVector B (Sum.inr 3900) = Sparse.eval nodeValue3900 (mixedVector B) := by
    change mixedMoment B node3900 node3900Labels = _
    exact sound3900 B hB hF
  have h3909 : mixedVector B (Sum.inr 3909) = Sparse.eval nodeValue3909 (mixedVector B) := by
    change mixedMoment B node3909 node3909Labels = _
    exact sound3909 B hB hF
  have h3974 : mixedVector B (Sum.inr 3974) = Sparse.eval nodeValue3974 (mixedVector B) := by
    change mixedMoment B node3974 node3974Labels = _
    exact sound3974 B hB hF
  have h3978 : mixedVector B (Sum.inr 3978) = Sparse.eval nodeValue3978 (mixedVector B) := by
    change mixedMoment B node3978 node3978Labels = _
    exact sound3978 B hB hF
  have h3991 : mixedVector B (Sum.inr 3991) = Sparse.eval nodeValue3991 (mixedVector B) := by
    change mixedMoment B node3991 node3991Labels = _
    exact sound3991 B hB hF
  have h3992 : mixedVector B (Sum.inr 3992) = Sparse.eval nodeValue3992 (mixedVector B) := by
    change mixedMoment B node3992 node3992Labels = _
    exact sound3992 B hB hF
  simpa only [sourceForm980, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2015, h2017, h2021, h2044, h2240, h3499, h3502, h3516, h3557, h3688, h3691, h3700, h3819, h3822, h3832, h3835, h3836, h3839, h3842, h3843, h3846, h3847, h3848, h3900, h3909, h3974, h3978, h3991, h3992, reducedSource853] using sourceEq980 B hB

theorem rowSound853 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row853 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck853, numericCheck853, reducedZero853 B hB hF, mul_zero]

theorem reducedZero854 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource854 (mixedVector B) = 0 := by
  have h2916 : mixedVector B (Sum.inr 2916) = Sparse.eval nodeValue2916 (mixedVector B) := by
    change mixedMoment B node2916 node2916Labels = _
    exact sound2916 B hB hF
  have h3716 : mixedVector B (Sum.inr 3716) = Sparse.eval nodeValue3716 (mixedVector B) := by
    change mixedMoment B node3716 node3716Labels = _
    exact sound3716 B hB hF
  have h3721 : mixedVector B (Sum.inr 3721) = Sparse.eval nodeValue3721 (mixedVector B) := by
    change mixedMoment B node3721 node3721Labels = _
    exact sound3721 B hB hF
  have h3724 : mixedVector B (Sum.inr 3724) = Sparse.eval nodeValue3724 (mixedVector B) := by
    change mixedMoment B node3724 node3724Labels = _
    exact sound3724 B hB hF
  have h3838 : mixedVector B (Sum.inr 3838) = Sparse.eval nodeValue3838 (mixedVector B) := by
    change mixedMoment B node3838 node3838Labels = _
    exact sound3838 B hB hF
  have h3972 : mixedVector B (Sum.inr 3972) = Sparse.eval nodeValue3972 (mixedVector B) := by
    change mixedMoment B node3972 node3972Labels = _
    exact sound3972 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm982, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2916, h3716, h3721, h3724, h3838, h3972, h4091, reducedSource854] using sourceEq982 B hB

theorem rowSound854 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row854 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck854, numericCheck854, reducedZero854 B hB hF, mul_zero]

theorem reducedZero855 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource855 (mixedVector B) = 0 := by
  have h3172 : mixedVector B (Sum.inr 3172) = Sparse.eval nodeValue3172 (mixedVector B) := by
    change mixedMoment B node3172 node3172Labels = _
    exact sound3172 B hB hF
  have h3721 : mixedVector B (Sum.inr 3721) = Sparse.eval nodeValue3721 (mixedVector B) := by
    change mixedMoment B node3721 node3721Labels = _
    exact sound3721 B hB hF
  have h3964 : mixedVector B (Sum.inr 3964) = Sparse.eval nodeValue3964 (mixedVector B) := by
    change mixedMoment B node3964 node3964Labels = _
    exact sound3964 B hB hF
  have h3972 : mixedVector B (Sum.inr 3972) = Sparse.eval nodeValue3972 (mixedVector B) := by
    change mixedMoment B node3972 node3972Labels = _
    exact sound3972 B hB hF
  have h4025 : mixedVector B (Sum.inr 4025) = Sparse.eval nodeValue4025 (mixedVector B) := by
    change mixedMoment B node4025 node4025Labels = _
    exact sound4025 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm983, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3172, h3721, h3964, h3972, h4025, h4091, reducedSource855] using sourceEq983 B hB

theorem rowSound855 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row855 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck855, numericCheck855, reducedZero855 B hB hF, mul_zero]

theorem reducedZero856 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource856 (mixedVector B) = 0 := by
  have h3066 : mixedVector B (Sum.inr 3066) = Sparse.eval nodeValue3066 (mixedVector B) := by
    change mixedMoment B node3066 node3066Labels = _
    exact sound3066 B hB hF
  have h3789 : mixedVector B (Sum.inr 3789) = Sparse.eval nodeValue3789 (mixedVector B) := by
    change mixedMoment B node3789 node3789Labels = _
    exact sound3789 B hB hF
  have h3949 : mixedVector B (Sum.inr 3949) = Sparse.eval nodeValue3949 (mixedVector B) := by
    change mixedMoment B node3949 node3949Labels = _
    exact sound3949 B hB hF
  have h3972 : mixedVector B (Sum.inr 3972) = Sparse.eval nodeValue3972 (mixedVector B) := by
    change mixedMoment B node3972 node3972Labels = _
    exact sound3972 B hB hF
  have h4008 : mixedVector B (Sum.inr 4008) = Sparse.eval nodeValue4008 (mixedVector B) := by
    change mixedMoment B node4008 node4008Labels = _
    exact sound4008 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm986, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3066, h3789, h3949, h3972, h4008, h4091, reducedSource856] using sourceEq986 B hB

theorem rowSound856 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row856 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck856, numericCheck856, reducedZero856 B hB hF, mul_zero]

theorem reducedZero857 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource857 (mixedVector B) = 0 := by
  have h5082 : mixedVector B (Sum.inr 5082) = Sparse.eval nodeValue5082 (mixedVector B) := by
    change mixedMoment B node5082 node5082Labels = _
    exact sound5082 B hB hF
  have h5083 : mixedVector B (Sum.inr 5083) = Sparse.eval nodeValue5083 (mixedVector B) := by
    change mixedMoment B node5083 node5083Labels = _
    exact sound5083 B hB hF
  have h5086 : mixedVector B (Sum.inr 5086) = Sparse.eval nodeValue5086 (mixedVector B) := by
    change mixedMoment B node5086 node5086Labels = _
    exact sound5086 B hB hF
  have h5091 : mixedVector B (Sum.inr 5091) = Sparse.eval nodeValue5091 (mixedVector B) := by
    change mixedMoment B node5091 node5091Labels = _
    exact sound5091 B hB hF
  have h5144 : mixedVector B (Sum.inr 5144) = Sparse.eval nodeValue5144 (mixedVector B) := by
    change mixedMoment B node5144 node5144Labels = _
    exact sound5144 B hB hF
  have h5146 : mixedVector B (Sum.inr 5146) = Sparse.eval nodeValue5146 (mixedVector B) := by
    change mixedMoment B node5146 node5146Labels = _
    exact sound5146 B hB hF
  have h5160 : mixedVector B (Sum.inr 5160) = Sparse.eval nodeValue5160 (mixedVector B) := by
    change mixedMoment B node5160 node5160Labels = _
    exact sound5160 B hB hF
  have h5289 : mixedVector B (Sum.inr 5289) = Sparse.eval nodeValue5289 (mixedVector B) := by
    change mixedMoment B node5289 node5289Labels = _
    exact sound5289 B hB hF
  have h5299 : mixedVector B (Sum.inr 5299) = Sparse.eval nodeValue5299 (mixedVector B) := by
    change mixedMoment B node5299 node5299Labels = _
    exact sound5299 B hB hF
  have h5357 : mixedVector B (Sum.inr 5357) = Sparse.eval nodeValue5357 (mixedVector B) := by
    change mixedMoment B node5357 node5357Labels = _
    exact sound5357 B hB hF
  have h5358 : mixedVector B (Sum.inr 5358) = Sparse.eval nodeValue5358 (mixedVector B) := by
    change mixedMoment B node5358 node5358Labels = _
    exact sound5358 B hB hF
  have h5360 : mixedVector B (Sum.inr 5360) = Sparse.eval nodeValue5360 (mixedVector B) := by
    change mixedMoment B node5360 node5360Labels = _
    exact sound5360 B hB hF
  have h5381 : mixedVector B (Sum.inr 5381) = Sparse.eval nodeValue5381 (mixedVector B) := by
    change mixedMoment B node5381 node5381Labels = _
    exact sound5381 B hB hF
  have h5382 : mixedVector B (Sum.inr 5382) = Sparse.eval nodeValue5382 (mixedVector B) := by
    change mixedMoment B node5382 node5382Labels = _
    exact sound5382 B hB hF
  have h5395 : mixedVector B (Sum.inr 5395) = Sparse.eval nodeValue5395 (mixedVector B) := by
    change mixedMoment B node5395 node5395Labels = _
    exact sound5395 B hB hF
  have h5411 : mixedVector B (Sum.inr 5411) = Sparse.eval nodeValue5411 (mixedVector B) := by
    change mixedMoment B node5411 node5411Labels = _
    exact sound5411 B hB hF
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
  have h5425 : mixedVector B (Sum.inr 5425) = Sparse.eval nodeValue5425 (mixedVector B) := by
    change mixedMoment B node5425 node5425Labels = _
    exact sound5425 B hB hF
  have h5432 : mixedVector B (Sum.inr 5432) = Sparse.eval nodeValue5432 (mixedVector B) := by
    change mixedMoment B node5432 node5432Labels = _
    exact sound5432 B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434 B hB hF
  have h5438 : mixedVector B (Sum.inr 5438) = Sparse.eval nodeValue5438 (mixedVector B) := by
    change mixedMoment B node5438 node5438Labels = _
    exact sound5438 B hB hF
  have h5446 : mixedVector B (Sum.inr 5446) = Sparse.eval nodeValue5446 (mixedVector B) := by
    change mixedMoment B node5446 node5446Labels = _
    exact sound5446 B hB hF
  have h5451 : mixedVector B (Sum.inr 5451) = Sparse.eval nodeValue5451 (mixedVector B) := by
    change mixedMoment B node5451 node5451Labels = _
    exact sound5451 B hB hF
  have h5468 : mixedVector B (Sum.inr 5468) = Sparse.eval nodeValue5468 (mixedVector B) := by
    change mixedMoment B node5468 node5468Labels = _
    exact sound5468 B hB hF
  have h5473 : mixedVector B (Sum.inr 5473) = Sparse.eval nodeValue5473 (mixedVector B) := by
    change mixedMoment B node5473 node5473Labels = _
    exact sound5473 B hB hF
  have h5477 : mixedVector B (Sum.inr 5477) = Sparse.eval nodeValue5477 (mixedVector B) := by
    change mixedMoment B node5477 node5477Labels = _
    exact sound5477 B hB hF
  simpa only [sourceForm987, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5082, h5083, h5086, h5091, h5144, h5146, h5160, h5289, h5299, h5357, h5358, h5360, h5381, h5382, h5395, h5411, h5420, h5421, h5423, h5424, h5425, h5432, h5434, h5438, h5446, h5451, h5468, h5473, h5477, reducedSource857] using sourceEq987 B hB

theorem rowSound857 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row857 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck857, numericCheck857, reducedZero857 B hB hF, mul_zero]

theorem reducedZero858 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource858 (mixedVector B) = 0 := by
  have h2490 : mixedVector B (Sum.inr 2490) = Sparse.eval nodeValue2490 (mixedVector B) := by
    change mixedMoment B node2490 node2490Labels = _
    exact sound2490 B hB hF
  have h2491 : mixedVector B (Sum.inr 2491) = Sparse.eval nodeValue2491 (mixedVector B) := by
    change mixedMoment B node2491 node2491Labels = _
    exact sound2491 B hB hF
  have h2494 : mixedVector B (Sum.inr 2494) = Sparse.eval nodeValue2494 (mixedVector B) := by
    change mixedMoment B node2494 node2494Labels = _
    exact sound2494 B hB hF
  have h2500 : mixedVector B (Sum.inr 2500) = Sparse.eval nodeValue2500 (mixedVector B) := by
    change mixedMoment B node2500 node2500Labels = _
    exact sound2500 B hB hF
  have h2773 : mixedVector B (Sum.inr 2773) = Sparse.eval nodeValue2773 (mixedVector B) := by
    change mixedMoment B node2773 node2773Labels = _
    exact sound2773 B hB hF
  have h3557 : mixedVector B (Sum.inr 3557) = Sparse.eval nodeValue3557 (mixedVector B) := by
    change mixedMoment B node3557 node3557Labels = _
    exact sound3557 B hB hF
  have h3558 : mixedVector B (Sum.inr 3558) = Sparse.eval nodeValue3558 (mixedVector B) := by
    change mixedMoment B node3558 node3558Labels = _
    exact sound3558 B hB hF
  have h3560 : mixedVector B (Sum.inr 3560) = Sparse.eval nodeValue3560 (mixedVector B) := by
    change mixedMoment B node3560 node3560Labels = _
    exact sound3560 B hB hF
  have h3572 : mixedVector B (Sum.inr 3572) = Sparse.eval nodeValue3572 (mixedVector B) := by
    change mixedMoment B node3572 node3572Labels = _
    exact sound3572 B hB hF
  have h3695 : mixedVector B (Sum.inr 3695) = Sparse.eval nodeValue3695 (mixedVector B) := by
    change mixedMoment B node3695 node3695Labels = _
    exact sound3695 B hB hF
  have h3696 : mixedVector B (Sum.inr 3696) = Sparse.eval nodeValue3696 (mixedVector B) := by
    change mixedMoment B node3696 node3696Labels = _
    exact sound3696 B hB hF
  have h3698 : mixedVector B (Sum.inr 3698) = Sparse.eval nodeValue3698 (mixedVector B) := by
    change mixedMoment B node3698 node3698Labels = _
    exact sound3698 B hB hF
  have h3827 : mixedVector B (Sum.inr 3827) = Sparse.eval nodeValue3827 (mixedVector B) := by
    change mixedMoment B node3827 node3827Labels = _
    exact sound3827 B hB hF
  have h3834 : mixedVector B (Sum.inr 3834) = Sparse.eval nodeValue3834 (mixedVector B) := by
    change mixedMoment B node3834 node3834Labels = _
    exact sound3834 B hB hF
  have h3837 : mixedVector B (Sum.inr 3837) = Sparse.eval nodeValue3837 (mixedVector B) := by
    change mixedMoment B node3837 node3837Labels = _
    exact sound3837 B hB hF
  have h3838 : mixedVector B (Sum.inr 3838) = Sparse.eval nodeValue3838 (mixedVector B) := by
    change mixedMoment B node3838 node3838Labels = _
    exact sound3838 B hB hF
  have h3840 : mixedVector B (Sum.inr 3840) = Sparse.eval nodeValue3840 (mixedVector B) := by
    change mixedMoment B node3840 node3840Labels = _
    exact sound3840 B hB hF
  have h3850 : mixedVector B (Sum.inr 3850) = Sparse.eval nodeValue3850 (mixedVector B) := by
    change mixedMoment B node3850 node3850Labels = _
    exact sound3850 B hB hF
  have h3852 : mixedVector B (Sum.inr 3852) = Sparse.eval nodeValue3852 (mixedVector B) := by
    change mixedMoment B node3852 node3852Labels = _
    exact sound3852 B hB hF
  have h3866 : mixedVector B (Sum.inr 3866) = Sparse.eval nodeValue3866 (mixedVector B) := by
    change mixedMoment B node3866 node3866Labels = _
    exact sound3866 B hB hF
  have h3870 : mixedVector B (Sum.inr 3870) = Sparse.eval nodeValue3870 (mixedVector B) := by
    change mixedMoment B node3870 node3870Labels = _
    exact sound3870 B hB hF
  have h3872 : mixedVector B (Sum.inr 3872) = Sparse.eval nodeValue3872 (mixedVector B) := by
    change mixedMoment B node3872 node3872Labels = _
    exact sound3872 B hB hF
  have h3876 : mixedVector B (Sum.inr 3876) = Sparse.eval nodeValue3876 (mixedVector B) := by
    change mixedMoment B node3876 node3876Labels = _
    exact sound3876 B hB hF
  have h3881 : mixedVector B (Sum.inr 3881) = Sparse.eval nodeValue3881 (mixedVector B) := by
    change mixedMoment B node3881 node3881Labels = _
    exact sound3881 B hB hF
  have h3883 : mixedVector B (Sum.inr 3883) = Sparse.eval nodeValue3883 (mixedVector B) := by
    change mixedMoment B node3883 node3883Labels = _
    exact sound3883 B hB hF
  have h3888 : mixedVector B (Sum.inr 3888) = Sparse.eval nodeValue3888 (mixedVector B) := by
    change mixedMoment B node3888 node3888Labels = _
    exact sound3888 B hB hF
  have h3968 : mixedVector B (Sum.inr 3968) = Sparse.eval nodeValue3968 (mixedVector B) := by
    change mixedMoment B node3968 node3968Labels = _
    exact sound3968 B hB hF
  have h3970 : mixedVector B (Sum.inr 3970) = Sparse.eval nodeValue3970 (mixedVector B) := by
    change mixedMoment B node3970 node3970Labels = _
    exact sound3970 B hB hF
  have h3989 : mixedVector B (Sum.inr 3989) = Sparse.eval nodeValue3989 (mixedVector B) := by
    change mixedMoment B node3989 node3989Labels = _
    exact sound3989 B hB hF
  have h3995 : mixedVector B (Sum.inr 3995) = Sparse.eval nodeValue3995 (mixedVector B) := by
    change mixedMoment B node3995 node3995Labels = _
    exact sound3995 B hB hF
  simpa only [sourceForm988, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2490, h2491, h2494, h2500, h2773, h3557, h3558, h3560, h3572, h3695, h3696, h3698, h3827, h3834, h3837, h3838, h3840, h3850, h3852, h3866, h3870, h3872, h3876, h3881, h3883, h3888, h3968, h3970, h3989, h3995, reducedSource858] using sourceEq988 B hB

theorem rowSound858 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row858 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck858, numericCheck858, reducedZero858 B hB hF, mul_zero]

theorem reducedZero859 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource859 (mixedVector B) = 0 := by
  have h2921 : mixedVector B (Sum.inr 2921) = Sparse.eval nodeValue2921 (mixedVector B) := by
    change mixedMoment B node2921 node2921Labels = _
    exact sound2921 B hB hF
  have h2922 : mixedVector B (Sum.inr 2922) = Sparse.eval nodeValue2922 (mixedVector B) := by
    change mixedMoment B node2922 node2922Labels = _
    exact sound2922 B hB hF
  have h2928 : mixedVector B (Sum.inr 2928) = Sparse.eval nodeValue2928 (mixedVector B) := by
    change mixedMoment B node2928 node2928Labels = _
    exact sound2928 B hB hF
  have h2951 : mixedVector B (Sum.inr 2951) = Sparse.eval nodeValue2951 (mixedVector B) := by
    change mixedMoment B node2951 node2951Labels = _
    exact sound2951 B hB hF
  have h3097 : mixedVector B (Sum.inr 3097) = Sparse.eval nodeValue3097 (mixedVector B) := by
    change mixedMoment B node3097 node3097Labels = _
    exact sound3097 B hB hF
  have h3441 : mixedVector B (Sum.inr 3441) = Sparse.eval nodeValue3441 (mixedVector B) := by
    change mixedMoment B node3441 node3441Labels = _
    exact sound3441 B hB hF
  have h3447 : mixedVector B (Sum.inr 3447) = Sparse.eval nodeValue3447 (mixedVector B) := by
    change mixedMoment B node3447 node3447Labels = _
    exact sound3447 B hB hF
  have h3464 : mixedVector B (Sum.inr 3464) = Sparse.eval nodeValue3464 (mixedVector B) := by
    change mixedMoment B node3464 node3464Labels = _
    exact sound3464 B hB hF
  have h3573 : mixedVector B (Sum.inr 3573) = Sparse.eval nodeValue3573 (mixedVector B) := by
    change mixedMoment B node3573 node3573Labels = _
    exact sound3573 B hB hF
  have h3718 : mixedVector B (Sum.inr 3718) = Sparse.eval nodeValue3718 (mixedVector B) := by
    change mixedMoment B node3718 node3718Labels = _
    exact sound3718 B hB hF
  have h3722 : mixedVector B (Sum.inr 3722) = Sparse.eval nodeValue3722 (mixedVector B) := by
    change mixedMoment B node3722 node3722Labels = _
    exact sound3722 B hB hF
  have h3730 : mixedVector B (Sum.inr 3730) = Sparse.eval nodeValue3730 (mixedVector B) := by
    change mixedMoment B node3730 node3730Labels = _
    exact sound3730 B hB hF
  have h3752 : mixedVector B (Sum.inr 3752) = Sparse.eval nodeValue3752 (mixedVector B) := by
    change mixedMoment B node3752 node3752Labels = _
    exact sound3752 B hB hF
  have h3762 : mixedVector B (Sum.inr 3762) = Sparse.eval nodeValue3762 (mixedVector B) := by
    change mixedMoment B node3762 node3762Labels = _
    exact sound3762 B hB hF
  have h3794 : mixedVector B (Sum.inr 3794) = Sparse.eval nodeValue3794 (mixedVector B) := by
    change mixedMoment B node3794 node3794Labels = _
    exact sound3794 B hB hF
  have h3809 : mixedVector B (Sum.inr 3809) = Sparse.eval nodeValue3809 (mixedVector B) := by
    change mixedMoment B node3809 node3809Labels = _
    exact sound3809 B hB hF
  have h3839 : mixedVector B (Sum.inr 3839) = Sparse.eval nodeValue3839 (mixedVector B) := by
    change mixedMoment B node3839 node3839Labels = _
    exact sound3839 B hB hF
  have h3872 : mixedVector B (Sum.inr 3872) = Sparse.eval nodeValue3872 (mixedVector B) := by
    change mixedMoment B node3872 node3872Labels = _
    exact sound3872 B hB hF
  have h3873 : mixedVector B (Sum.inr 3873) = Sparse.eval nodeValue3873 (mixedVector B) := by
    change mixedMoment B node3873 node3873Labels = _
    exact sound3873 B hB hF
  have h3950 : mixedVector B (Sum.inr 3950) = Sparse.eval nodeValue3950 (mixedVector B) := by
    change mixedMoment B node3950 node3950Labels = _
    exact sound3950 B hB hF
  have h3958 : mixedVector B (Sum.inr 3958) = Sparse.eval nodeValue3958 (mixedVector B) := by
    change mixedMoment B node3958 node3958Labels = _
    exact sound3958 B hB hF
  have h3959 : mixedVector B (Sum.inr 3959) = Sparse.eval nodeValue3959 (mixedVector B) := by
    change mixedMoment B node3959 node3959Labels = _
    exact sound3959 B hB hF
  have h3971 : mixedVector B (Sum.inr 3971) = Sparse.eval nodeValue3971 (mixedVector B) := by
    change mixedMoment B node3971 node3971Labels = _
    exact sound3971 B hB hF
  have h3982 : mixedVector B (Sum.inr 3982) = Sparse.eval nodeValue3982 (mixedVector B) := by
    change mixedMoment B node3982 node3982Labels = _
    exact sound3982 B hB hF
  have h3987 : mixedVector B (Sum.inr 3987) = Sparse.eval nodeValue3987 (mixedVector B) := by
    change mixedMoment B node3987 node3987Labels = _
    exact sound3987 B hB hF
  have h3990 : mixedVector B (Sum.inr 3990) = Sparse.eval nodeValue3990 (mixedVector B) := by
    change mixedMoment B node3990 node3990Labels = _
    exact sound3990 B hB hF
  have h3993 : mixedVector B (Sum.inr 3993) = Sparse.eval nodeValue3993 (mixedVector B) := by
    change mixedMoment B node3993 node3993Labels = _
    exact sound3993 B hB hF
  have h4022 : mixedVector B (Sum.inr 4022) = Sparse.eval nodeValue4022 (mixedVector B) := by
    change mixedMoment B node4022 node4022Labels = _
    exact sound4022 B hB hF
  have h4027 : mixedVector B (Sum.inr 4027) = Sparse.eval nodeValue4027 (mixedVector B) := by
    change mixedMoment B node4027 node4027Labels = _
    exact sound4027 B hB hF
  have h4032 : mixedVector B (Sum.inr 4032) = Sparse.eval nodeValue4032 (mixedVector B) := by
    change mixedMoment B node4032 node4032Labels = _
    exact sound4032 B hB hF
  simpa only [sourceForm989, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2921, h2922, h2928, h2951, h3097, h3441, h3447, h3464, h3573, h3718, h3722, h3730, h3752, h3762, h3794, h3809, h3839, h3872, h3873, h3950, h3958, h3959, h3971, h3982, h3987, h3990, h3993, h4022, h4027, h4032, reducedSource859] using sourceEq989 B hB

theorem rowSound859 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row859 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck859, numericCheck859, reducedZero859 B hB hF, mul_zero]

theorem reducedZero860 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource860 (mixedVector B) = 0 := by
  have h3781 : mixedVector B (Sum.inr 3781) = Sparse.eval nodeValue3781 (mixedVector B) := by
    change mixedMoment B node3781 node3781Labels = _
    exact sound3781 B hB hF
  have h3848 : mixedVector B (Sum.inr 3848) = Sparse.eval nodeValue3848 (mixedVector B) := by
    change mixedMoment B node3848 node3848Labels = _
    exact sound3848 B hB hF
  have h3944 : mixedVector B (Sum.inr 3944) = Sparse.eval nodeValue3944 (mixedVector B) := by
    change mixedMoment B node3944 node3944Labels = _
    exact sound3944 B hB hF
  have h3946 : mixedVector B (Sum.inr 3946) = Sparse.eval nodeValue3946 (mixedVector B) := by
    change mixedMoment B node3946 node3946Labels = _
    exact sound3946 B hB hF
  have h3961 : mixedVector B (Sum.inr 3961) = Sparse.eval nodeValue3961 (mixedVector B) := by
    change mixedMoment B node3961 node3961Labels = _
    exact sound3961 B hB hF
  have h4044 : mixedVector B (Sum.inr 4044) = Sparse.eval nodeValue4044 (mixedVector B) := by
    change mixedMoment B node4044 node4044Labels = _
    exact sound4044 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm990, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3781, h3848, h3944, h3946, h3961, h4044, h4092, reducedSource860] using sourceEq990 B hB

theorem rowSound860 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row860 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck860, numericCheck860, reducedZero860 B hB hF, mul_zero]

theorem reducedZero861 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource861 (mixedVector B) = 0 := by
  have h2977 : mixedVector B (Sum.inr 2977) = Sparse.eval nodeValue2977 (mixedVector B) := by
    change mixedMoment B node2977 node2977Labels = _
    exact sound2977 B hB hF
  have h3723 : mixedVector B (Sum.inr 3723) = Sparse.eval nodeValue3723 (mixedVector B) := by
    change mixedMoment B node3723 node3723Labels = _
    exact sound3723 B hB hF
  have h3725 : mixedVector B (Sum.inr 3725) = Sparse.eval nodeValue3725 (mixedVector B) := by
    change mixedMoment B node3725 node3725Labels = _
    exact sound3725 B hB hF
  have h3730 : mixedVector B (Sum.inr 3730) = Sparse.eval nodeValue3730 (mixedVector B) := by
    change mixedMoment B node3730 node3730Labels = _
    exact sound3730 B hB hF
  have h3848 : mixedVector B (Sum.inr 3848) = Sparse.eval nodeValue3848 (mixedVector B) := by
    change mixedMoment B node3848 node3848Labels = _
    exact sound3848 B hB hF
  have h3946 : mixedVector B (Sum.inr 3946) = Sparse.eval nodeValue3946 (mixedVector B) := by
    change mixedMoment B node3946 node3946Labels = _
    exact sound3946 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm991, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2977, h3723, h3725, h3730, h3848, h3946, h4092, reducedSource861] using sourceEq991 B hB

theorem rowSound861 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row861 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck861, numericCheck861, reducedZero861 B hB hF, mul_zero]

theorem reducedZero862 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource862 (mixedVector B) = 0 := by
  have h2975 : mixedVector B (Sum.inr 2975) = Sparse.eval nodeValue2975 (mixedVector B) := by
    change mixedMoment B node2975 node2975Labels = _
    exact sound2975 B hB hF
  have h3826 : mixedVector B (Sum.inr 3826) = Sparse.eval nodeValue3826 (mixedVector B) := by
    change mixedMoment B node3826 node3826Labels = _
    exact sound3826 B hB hF
  have h3828 : mixedVector B (Sum.inr 3828) = Sparse.eval nodeValue3828 (mixedVector B) := by
    change mixedMoment B node3828 node3828Labels = _
    exact sound3828 B hB hF
  have h3848 : mixedVector B (Sum.inr 3848) = Sparse.eval nodeValue3848 (mixedVector B) := by
    change mixedMoment B node3848 node3848Labels = _
    exact sound3848 B hB hF
  have h3884 : mixedVector B (Sum.inr 3884) = Sparse.eval nodeValue3884 (mixedVector B) := by
    change mixedMoment B node3884 node3884Labels = _
    exact sound3884 B hB hF
  have h3944 : mixedVector B (Sum.inr 3944) = Sparse.eval nodeValue3944 (mixedVector B) := by
    change mixedMoment B node3944 node3944Labels = _
    exact sound3944 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm992, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2975, h3826, h3828, h3848, h3884, h3944, h4092, reducedSource862] using sourceEq992 B hB

theorem rowSound862 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row862 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck862, numericCheck862, reducedZero862 B hB hF, mul_zero]

theorem reducedZero863 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource863 (mixedVector B) = 0 := by
  have h5105 : mixedVector B (Sum.inr 5105) = Sparse.eval nodeValue5105 (mixedVector B) := by
    change mixedMoment B node5105 node5105Labels = _
    exact sound5105 B hB hF
  have h5109 : mixedVector B (Sum.inr 5109) = Sparse.eval nodeValue5109 (mixedVector B) := by
    change mixedMoment B node5109 node5109Labels = _
    exact sound5109 B hB hF
  have h5110 : mixedVector B (Sum.inr 5110) = Sparse.eval nodeValue5110 (mixedVector B) := by
    change mixedMoment B node5110 node5110Labels = _
    exact sound5110 B hB hF
  have h5203 : mixedVector B (Sum.inr 5203) = Sparse.eval nodeValue5203 (mixedVector B) := by
    change mixedMoment B node5203 node5203Labels = _
    exact sound5203 B hB hF
  have h5207 : mixedVector B (Sum.inr 5207) = Sparse.eval nodeValue5207 (mixedVector B) := by
    change mixedMoment B node5207 node5207Labels = _
    exact sound5207 B hB hF
  have h5237 : mixedVector B (Sum.inr 5237) = Sparse.eval nodeValue5237 (mixedVector B) := by
    change mixedMoment B node5237 node5237Labels = _
    exact sound5237 B hB hF
  have h5238 : mixedVector B (Sum.inr 5238) = Sparse.eval nodeValue5238 (mixedVector B) := by
    change mixedMoment B node5238 node5238Labels = _
    exact sound5238 B hB hF
  have h5293 : mixedVector B (Sum.inr 5293) = Sparse.eval nodeValue5293 (mixedVector B) := by
    change mixedMoment B node5293 node5293Labels = _
    exact sound5293 B hB hF
  have h5304 : mixedVector B (Sum.inr 5304) = Sparse.eval nodeValue5304 (mixedVector B) := by
    change mixedMoment B node5304 node5304Labels = _
    exact sound5304 B hB hF
  have h5310 : mixedVector B (Sum.inr 5310) = Sparse.eval nodeValue5310 (mixedVector B) := by
    change mixedMoment B node5310 node5310Labels = _
    exact sound5310 B hB hF
  have h5370 : mixedVector B (Sum.inr 5370) = Sparse.eval nodeValue5370 (mixedVector B) := by
    change mixedMoment B node5370 node5370Labels = _
    exact sound5370 B hB hF
  have h5422 : mixedVector B (Sum.inr 5422) = Sparse.eval nodeValue5422 (mixedVector B) := by
    change mixedMoment B node5422 node5422Labels = _
    exact sound5422 B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434 B hB hF
  have h5443 : mixedVector B (Sum.inr 5443) = Sparse.eval nodeValue5443 (mixedVector B) := by
    change mixedMoment B node5443 node5443Labels = _
    exact sound5443 B hB hF
  have h5450 : mixedVector B (Sum.inr 5450) = Sparse.eval nodeValue5450 (mixedVector B) := by
    change mixedMoment B node5450 node5450Labels = _
    exact sound5450 B hB hF
  have h5451 : mixedVector B (Sum.inr 5451) = Sparse.eval nodeValue5451 (mixedVector B) := by
    change mixedMoment B node5451 node5451Labels = _
    exact sound5451 B hB hF
  have h5454 : mixedVector B (Sum.inr 5454) = Sparse.eval nodeValue5454 (mixedVector B) := by
    change mixedMoment B node5454 node5454Labels = _
    exact sound5454 B hB hF
  have h5455 : mixedVector B (Sum.inr 5455) = Sparse.eval nodeValue5455 (mixedVector B) := by
    change mixedMoment B node5455 node5455Labels = _
    exact sound5455 B hB hF
  have h5484 : mixedVector B (Sum.inr 5484) = Sparse.eval nodeValue5484 (mixedVector B) := by
    change mixedMoment B node5484 node5484Labels = _
    exact sound5484 B hB hF
  have h5492 : mixedVector B (Sum.inr 5492) = Sparse.eval nodeValue5492 (mixedVector B) := by
    change mixedMoment B node5492 node5492Labels = _
    exact sound5492 B hB hF
  have h5494 : mixedVector B (Sum.inr 5494) = Sparse.eval nodeValue5494 (mixedVector B) := by
    change mixedMoment B node5494 node5494Labels = _
    exact sound5494 B hB hF
  simpa only [sourceForm993, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5105, h5109, h5110, h5203, h5207, h5237, h5238, h5293, h5304, h5310, h5370, h5422, h5434, h5443, h5450, h5451, h5454, h5455, h5484, h5492, h5494, reducedSource863] using sourceEq993 B hB

theorem rowSound863 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row863 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck863, numericCheck863, reducedZero863 B hB hF, mul_zero]

theorem sourceRowsAt848 : MixedData.sourceRows (848 : Fin 2425) =
    MixedData.row848 := by decide +kernel

theorem sourceRowsAt849 : MixedData.sourceRows (849 : Fin 2425) =
    MixedData.row849 := by decide +kernel

theorem sourceRowsAt850 : MixedData.sourceRows (850 : Fin 2425) =
    MixedData.row850 := by decide +kernel

theorem sourceRowsAt851 : MixedData.sourceRows (851 : Fin 2425) =
    MixedData.row851 := by decide +kernel

theorem sourceRowsAt852 : MixedData.sourceRows (852 : Fin 2425) =
    MixedData.row852 := by decide +kernel

theorem sourceRowsAt853 : MixedData.sourceRows (853 : Fin 2425) =
    MixedData.row853 := by decide +kernel

theorem sourceRowsAt854 : MixedData.sourceRows (854 : Fin 2425) =
    MixedData.row854 := by decide +kernel

theorem sourceRowsAt855 : MixedData.sourceRows (855 : Fin 2425) =
    MixedData.row855 := by decide +kernel

theorem sourceRowsAt856 : MixedData.sourceRows (856 : Fin 2425) =
    MixedData.row856 := by decide +kernel

theorem sourceRowsAt857 : MixedData.sourceRows (857 : Fin 2425) =
    MixedData.row857 := by decide +kernel

theorem sourceRowsAt858 : MixedData.sourceRows (858 : Fin 2425) =
    MixedData.row858 := by decide +kernel

theorem sourceRowsAt859 : MixedData.sourceRows (859 : Fin 2425) =
    MixedData.row859 := by decide +kernel

theorem sourceRowsAt860 : MixedData.sourceRows (860 : Fin 2425) =
    MixedData.row860 := by decide +kernel

theorem sourceRowsAt861 : MixedData.sourceRows (861 : Fin 2425) =
    MixedData.row861 := by decide +kernel

theorem sourceRowsAt862 : MixedData.sourceRows (862 : Fin 2425) =
    MixedData.row862 := by decide +kernel

theorem sourceRowsAt863 : MixedData.sourceRows (863 : Fin 2425) =
    MixedData.row863 := by decide +kernel

theorem chunkSound53 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 53) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 848 ∨ k.val = 849 ∨ k.val = 850 ∨ k.val = 851 ∨ k.val = 852 ∨ k.val = 853 ∨ k.val = 854 ∨ k.val = 855 ∨ k.val = 856 ∨ k.val = 857 ∨ k.val = 858 ∨ k.val = 859 ∨ k.val = 860 ∨ k.val = 861 ∨ k.val = 862 ∨ k.val = 863 := by omega
  rcases heq with h848 | h849 | h850 | h851 | h852 | h853 | h854 | h855 | h856 | h857 | h858 | h859 | h860 | h861 | h862 | h863
  · have he : k = (848 : Fin 2425) := Fin.ext h848
    subst k
    rw [sourceRowsAt848]
    exact rowSound848 B hB hF
  · have he : k = (849 : Fin 2425) := Fin.ext h849
    subst k
    rw [sourceRowsAt849]
    exact rowSound849 B hB hF
  · have he : k = (850 : Fin 2425) := Fin.ext h850
    subst k
    rw [sourceRowsAt850]
    exact rowSound850 B hB hF
  · have he : k = (851 : Fin 2425) := Fin.ext h851
    subst k
    rw [sourceRowsAt851]
    exact rowSound851 B hB hF
  · have he : k = (852 : Fin 2425) := Fin.ext h852
    subst k
    rw [sourceRowsAt852]
    exact rowSound852 B hB hF
  · have he : k = (853 : Fin 2425) := Fin.ext h853
    subst k
    rw [sourceRowsAt853]
    exact rowSound853 B hB hF
  · have he : k = (854 : Fin 2425) := Fin.ext h854
    subst k
    rw [sourceRowsAt854]
    exact rowSound854 B hB hF
  · have he : k = (855 : Fin 2425) := Fin.ext h855
    subst k
    rw [sourceRowsAt855]
    exact rowSound855 B hB hF
  · have he : k = (856 : Fin 2425) := Fin.ext h856
    subst k
    rw [sourceRowsAt856]
    exact rowSound856 B hB hF
  · have he : k = (857 : Fin 2425) := Fin.ext h857
    subst k
    rw [sourceRowsAt857]
    exact rowSound857 B hB hF
  · have he : k = (858 : Fin 2425) := Fin.ext h858
    subst k
    rw [sourceRowsAt858]
    exact rowSound858 B hB hF
  · have he : k = (859 : Fin 2425) := Fin.ext h859
    subst k
    rw [sourceRowsAt859]
    exact rowSound859 B hB hF
  · have he : k = (860 : Fin 2425) := Fin.ext h860
    subst k
    rw [sourceRowsAt860]
    exact rowSound860 B hB hF
  · have he : k = (861 : Fin 2425) := Fin.ext h861
    subst k
    rw [sourceRowsAt861]
    exact rowSound861 B hB hF
  · have he : k = (862 : Fin 2425) := Fin.ext h862
    subst k
    rw [sourceRowsAt862]
    exact rowSound862 B hB hF
  · have he : k = (863 : Fin 2425) := Fin.ext h863
    subst k
    rw [sourceRowsAt863]
    exact rowSound863 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
