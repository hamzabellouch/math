import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources29

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero800 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource800 (mixedVector B) = 0 := by
  have h2023 : mixedVector B (Sum.inr 2023) = Sparse.eval nodeValue2023 (mixedVector B) := by
    change mixedMoment B node2023 node2023Labels = _
    exact sound2023 B hB hF
  have h2025 : mixedVector B (Sum.inr 2025) = Sparse.eval nodeValue2025 (mixedVector B) := by
    change mixedMoment B node2025 node2025Labels = _
    exact sound2025 B hB hF
  have h2028 : mixedVector B (Sum.inr 2028) = Sparse.eval nodeValue2028 (mixedVector B) := by
    change mixedMoment B node2028 node2028Labels = _
    exact sound2028 B hB hF
  have h2058 : mixedVector B (Sum.inr 2058) = Sparse.eval nodeValue2058 (mixedVector B) := by
    change mixedMoment B node2058 node2058Labels = _
    exact sound2058 B hB hF
  have h2245 : mixedVector B (Sum.inr 2245) = Sparse.eval nodeValue2245 (mixedVector B) := by
    change mixedMoment B node2245 node2245Labels = _
    exact sound2245 B hB hF
  have h2924 : mixedVector B (Sum.inr 2924) = Sparse.eval nodeValue2924 (mixedVector B) := by
    change mixedMoment B node2924 node2924Labels = _
    exact sound2924 B hB hF
  have h2931 : mixedVector B (Sum.inr 2931) = Sparse.eval nodeValue2931 (mixedVector B) := by
    change mixedMoment B node2931 node2931Labels = _
    exact sound2931 B hB hF
  have h2959 : mixedVector B (Sum.inr 2959) = Sparse.eval nodeValue2959 (mixedVector B) := by
    change mixedMoment B node2959 node2959Labels = _
    exact sound2959 B hB hF
  have h3101 : mixedVector B (Sum.inr 3101) = Sparse.eval nodeValue3101 (mixedVector B) := by
    change mixedMoment B node3101 node3101Labels = _
    exact sound3101 B hB hF
  have h3692 : mixedVector B (Sum.inr 3692) = Sparse.eval nodeValue3692 (mixedVector B) := by
    change mixedMoment B node3692 node3692Labels = _
    exact sound3692 B hB hF
  have h3693 : mixedVector B (Sum.inr 3693) = Sparse.eval nodeValue3693 (mixedVector B) := by
    change mixedMoment B node3693 node3693Labels = _
    exact sound3693 B hB hF
  have h3706 : mixedVector B (Sum.inr 3706) = Sparse.eval nodeValue3706 (mixedVector B) := by
    change mixedMoment B node3706 node3706Labels = _
    exact sound3706 B hB hF
  have h3719 : mixedVector B (Sum.inr 3719) = Sparse.eval nodeValue3719 (mixedVector B) := by
    change mixedMoment B node3719 node3719Labels = _
    exact sound3719 B hB hF
  have h3736 : mixedVector B (Sum.inr 3736) = Sparse.eval nodeValue3736 (mixedVector B) := by
    change mixedMoment B node3736 node3736Labels = _
    exact sound3736 B hB hF
  have h3782 : mixedVector B (Sum.inr 3782) = Sparse.eval nodeValue3782 (mixedVector B) := by
    change mixedMoment B node3782 node3782Labels = _
    exact sound3782 B hB hF
  have h3801 : mixedVector B (Sum.inr 3801) = Sparse.eval nodeValue3801 (mixedVector B) := by
    change mixedMoment B node3801 node3801Labels = _
    exact sound3801 B hB hF
  have h3823 : mixedVector B (Sum.inr 3823) = Sparse.eval nodeValue3823 (mixedVector B) := by
    change mixedMoment B node3823 node3823Labels = _
    exact sound3823 B hB hF
  have h3849 : mixedVector B (Sum.inr 3849) = Sparse.eval nodeValue3849 (mixedVector B) := by
    change mixedMoment B node3849 node3849Labels = _
    exact sound3849 B hB hF
  have h3850 : mixedVector B (Sum.inr 3850) = Sparse.eval nodeValue3850 (mixedVector B) := by
    change mixedMoment B node3850 node3850Labels = _
    exact sound3850 B hB hF
  have h3853 : mixedVector B (Sum.inr 3853) = Sparse.eval nodeValue3853 (mixedVector B) := by
    change mixedMoment B node3853 node3853Labels = _
    exact sound3853 B hB hF
  have h3857 : mixedVector B (Sum.inr 3857) = Sparse.eval nodeValue3857 (mixedVector B) := by
    change mixedMoment B node3857 node3857Labels = _
    exact sound3857 B hB hF
  have h3862 : mixedVector B (Sum.inr 3862) = Sparse.eval nodeValue3862 (mixedVector B) := by
    change mixedMoment B node3862 node3862Labels = _
    exact sound3862 B hB hF
  have h3910 : mixedVector B (Sum.inr 3910) = Sparse.eval nodeValue3910 (mixedVector B) := by
    change mixedMoment B node3910 node3910Labels = _
    exact sound3910 B hB hF
  have h3912 : mixedVector B (Sum.inr 3912) = Sparse.eval nodeValue3912 (mixedVector B) := by
    change mixedMoment B node3912 node3912Labels = _
    exact sound3912 B hB hF
  have h3982 : mixedVector B (Sum.inr 3982) = Sparse.eval nodeValue3982 (mixedVector B) := by
    change mixedMoment B node3982 node3982Labels = _
    exact sound3982 B hB hF
  have h4013 : mixedVector B (Sum.inr 4013) = Sparse.eval nodeValue4013 (mixedVector B) := by
    change mixedMoment B node4013 node4013Labels = _
    exact sound4013 B hB hF
  have h4033 : mixedVector B (Sum.inr 4033) = Sparse.eval nodeValue4033 (mixedVector B) := by
    change mixedMoment B node4033 node4033Labels = _
    exact sound4033 B hB hF
  have h4036 : mixedVector B (Sum.inr 4036) = Sparse.eval nodeValue4036 (mixedVector B) := by
    change mixedMoment B node4036 node4036Labels = _
    exact sound4036 B hB hF
  have h4040 : mixedVector B (Sum.inr 4040) = Sparse.eval nodeValue4040 (mixedVector B) := by
    change mixedMoment B node4040 node4040Labels = _
    exact sound4040 B hB hF
  simpa only [sourceForm916, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2023, h2025, h2028, h2058, h2245, h2924, h2931, h2959, h3101, h3692, h3693, h3706, h3719, h3736, h3782, h3801, h3823, h3849, h3850, h3853, h3857, h3862, h3910, h3912, h3982, h4013, h4033, h4036, h4040, reducedSource800] using sourceEq916 B hB

theorem rowSound800 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row800 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck800, numericCheck800, reducedZero800 B hB hF, mul_zero]

theorem reducedZero801 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource801 (mixedVector B) = 0 := by
  have h5265 : mixedVector B (Sum.inr 5265) = Sparse.eval nodeValue5265 (mixedVector B) := by
    change mixedMoment B node5265 node5265Labels = _
    exact sound5265 B hB hF
  have h5266 : mixedVector B (Sum.inr 5266) = Sparse.eval nodeValue5266 (mixedVector B) := by
    change mixedMoment B node5266 node5266Labels = _
    exact sound5266 B hB hF
  have h5267 : mixedVector B (Sum.inr 5267) = Sparse.eval nodeValue5267 (mixedVector B) := by
    change mixedMoment B node5267 node5267Labels = _
    exact sound5267 B hB hF
  have h5271 : mixedVector B (Sum.inr 5271) = Sparse.eval nodeValue5271 (mixedVector B) := by
    change mixedMoment B node5271 node5271Labels = _
    exact sound5271 B hB hF
  have h5299 : mixedVector B (Sum.inr 5299) = Sparse.eval nodeValue5299 (mixedVector B) := by
    change mixedMoment B node5299 node5299Labels = _
    exact sound5299 B hB hF
  have h5406 : mixedVector B (Sum.inr 5406) = Sparse.eval nodeValue5406 (mixedVector B) := by
    change mixedMoment B node5406 node5406Labels = _
    exact sound5406 B hB hF
  have h5410 : mixedVector B (Sum.inr 5410) = Sparse.eval nodeValue5410 (mixedVector B) := by
    change mixedMoment B node5410 node5410Labels = _
    exact sound5410 B hB hF
  have h5411 : mixedVector B (Sum.inr 5411) = Sparse.eval nodeValue5411 (mixedVector B) := by
    change mixedMoment B node5411 node5411Labels = _
    exact sound5411 B hB hF
  have h5412 : mixedVector B (Sum.inr 5412) = Sparse.eval nodeValue5412 (mixedVector B) := by
    change mixedMoment B node5412 node5412Labels = _
    exact sound5412 B hB hF
  have h5424 : mixedVector B (Sum.inr 5424) = Sparse.eval nodeValue5424 (mixedVector B) := by
    change mixedMoment B node5424 node5424Labels = _
    exact sound5424 B hB hF
  have h5425 : mixedVector B (Sum.inr 5425) = Sparse.eval nodeValue5425 (mixedVector B) := by
    change mixedMoment B node5425 node5425Labels = _
    exact sound5425 B hB hF
  have h5426 : mixedVector B (Sum.inr 5426) = Sparse.eval nodeValue5426 (mixedVector B) := by
    change mixedMoment B node5426 node5426Labels = _
    exact sound5426 B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434 B hB hF
  have h5435 : mixedVector B (Sum.inr 5435) = Sparse.eval nodeValue5435 (mixedVector B) := by
    change mixedMoment B node5435 node5435Labels = _
    exact sound5435 B hB hF
  have h5442 : mixedVector B (Sum.inr 5442) = Sparse.eval nodeValue5442 (mixedVector B) := by
    change mixedMoment B node5442 node5442Labels = _
    exact sound5442 B hB hF
  have h5443 : mixedVector B (Sum.inr 5443) = Sparse.eval nodeValue5443 (mixedVector B) := by
    change mixedMoment B node5443 node5443Labels = _
    exact sound5443 B hB hF
  simpa only [sourceForm917, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5265, h5266, h5267, h5271, h5299, h5406, h5410, h5411, h5412, h5424, h5425, h5426, h5434, h5435, h5442, h5443, reducedSource801] using sourceEq917 B hB

theorem rowSound801 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row801 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck801, numericCheck801, reducedZero801 B hB hF, mul_zero]

theorem reducedZero802 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource802 (mixedVector B) = 0 := by
  have h2392 : mixedVector B (Sum.inr 2392) = Sparse.eval nodeValue2392 (mixedVector B) := by
    change mixedMoment B node2392 node2392Labels = _
    exact sound2392 B hB hF
  have h2393 : mixedVector B (Sum.inr 2393) = Sparse.eval nodeValue2393 (mixedVector B) := by
    change mixedMoment B node2393 node2393Labels = _
    exact sound2393 B hB hF
  have h2394 : mixedVector B (Sum.inr 2394) = Sparse.eval nodeValue2394 (mixedVector B) := by
    change mixedMoment B node2394 node2394Labels = _
    exact sound2394 B hB hF
  have h2405 : mixedVector B (Sum.inr 2405) = Sparse.eval nodeValue2405 (mixedVector B) := by
    change mixedMoment B node2405 node2405Labels = _
    exact sound2405 B hB hF
  have h2732 : mixedVector B (Sum.inr 2732) = Sparse.eval nodeValue2732 (mixedVector B) := by
    change mixedMoment B node2732 node2732Labels = _
    exact sound2732 B hB hF
  have h2909 : mixedVector B (Sum.inr 2909) = Sparse.eval nodeValue2909 (mixedVector B) := by
    change mixedMoment B node2909 node2909Labels = _
    exact sound2909 B hB hF
  have h2910 : mixedVector B (Sum.inr 2910) = Sparse.eval nodeValue2910 (mixedVector B) := by
    change mixedMoment B node2910 node2910Labels = _
    exact sound2910 B hB hF
  have h2955 : mixedVector B (Sum.inr 2955) = Sparse.eval nodeValue2955 (mixedVector B) := by
    change mixedMoment B node2955 node2955Labels = _
    exact sound2955 B hB hF
  have h3055 : mixedVector B (Sum.inr 3055) = Sparse.eval nodeValue3055 (mixedVector B) := by
    change mixedMoment B node3055 node3055Labels = _
    exact sound3055 B hB hF
  have h3347 : mixedVector B (Sum.inr 3347) = Sparse.eval nodeValue3347 (mixedVector B) := by
    change mixedMoment B node3347 node3347Labels = _
    exact sound3347 B hB hF
  have h3348 : mixedVector B (Sum.inr 3348) = Sparse.eval nodeValue3348 (mixedVector B) := by
    change mixedMoment B node3348 node3348Labels = _
    exact sound3348 B hB hF
  have h3358 : mixedVector B (Sum.inr 3358) = Sparse.eval nodeValue3358 (mixedVector B) := by
    change mixedMoment B node3358 node3358Labels = _
    exact sound3358 B hB hF
  have h3541 : mixedVector B (Sum.inr 3541) = Sparse.eval nodeValue3541 (mixedVector B) := by
    change mixedMoment B node3541 node3541Labels = _
    exact sound3541 B hB hF
  have h3559 : mixedVector B (Sum.inr 3559) = Sparse.eval nodeValue3559 (mixedVector B) := by
    change mixedMoment B node3559 node3559Labels = _
    exact sound3559 B hB hF
  have h3565 : mixedVector B (Sum.inr 3565) = Sparse.eval nodeValue3565 (mixedVector B) := by
    change mixedMoment B node3565 node3565Labels = _
    exact sound3565 B hB hF
  have h3584 : mixedVector B (Sum.inr 3584) = Sparse.eval nodeValue3584 (mixedVector B) := by
    change mixedMoment B node3584 node3584Labels = _
    exact sound3584 B hB hF
  have h3714 : mixedVector B (Sum.inr 3714) = Sparse.eval nodeValue3714 (mixedVector B) := by
    change mixedMoment B node3714 node3714Labels = _
    exact sound3714 B hB hF
  have h3733 : mixedVector B (Sum.inr 3733) = Sparse.eval nodeValue3733 (mixedVector B) := by
    change mixedMoment B node3733 node3733Labels = _
    exact sound3733 B hB hF
  have h3839 : mixedVector B (Sum.inr 3839) = Sparse.eval nodeValue3839 (mixedVector B) := by
    change mixedMoment B node3839 node3839Labels = _
    exact sound3839 B hB hF
  have h3845 : mixedVector B (Sum.inr 3845) = Sparse.eval nodeValue3845 (mixedVector B) := by
    change mixedMoment B node3845 node3845Labels = _
    exact sound3845 B hB hF
  have h3862 : mixedVector B (Sum.inr 3862) = Sparse.eval nodeValue3862 (mixedVector B) := by
    change mixedMoment B node3862 node3862Labels = _
    exact sound3862 B hB hF
  have h3868 : mixedVector B (Sum.inr 3868) = Sparse.eval nodeValue3868 (mixedVector B) := by
    change mixedMoment B node3868 node3868Labels = _
    exact sound3868 B hB hF
  have h3869 : mixedVector B (Sum.inr 3869) = Sparse.eval nodeValue3869 (mixedVector B) := by
    change mixedMoment B node3869 node3869Labels = _
    exact sound3869 B hB hF
  have h3872 : mixedVector B (Sum.inr 3872) = Sparse.eval nodeValue3872 (mixedVector B) := by
    change mixedMoment B node3872 node3872Labels = _
    exact sound3872 B hB hF
  have h3876 : mixedVector B (Sum.inr 3876) = Sparse.eval nodeValue3876 (mixedVector B) := by
    change mixedMoment B node3876 node3876Labels = _
    exact sound3876 B hB hF
  have h3877 : mixedVector B (Sum.inr 3877) = Sparse.eval nodeValue3877 (mixedVector B) := by
    change mixedMoment B node3877 node3877Labels = _
    exact sound3877 B hB hF
  have h3889 : mixedVector B (Sum.inr 3889) = Sparse.eval nodeValue3889 (mixedVector B) := by
    change mixedMoment B node3889 node3889Labels = _
    exact sound3889 B hB hF
  have h3949 : mixedVector B (Sum.inr 3949) = Sparse.eval nodeValue3949 (mixedVector B) := by
    change mixedMoment B node3949 node3949Labels = _
    exact sound3949 B hB hF
  have h3993 : mixedVector B (Sum.inr 3993) = Sparse.eval nodeValue3993 (mixedVector B) := by
    change mixedMoment B node3993 node3993Labels = _
    exact sound3993 B hB hF
  have h4003 : mixedVector B (Sum.inr 4003) = Sparse.eval nodeValue4003 (mixedVector B) := by
    change mixedMoment B node4003 node4003Labels = _
    exact sound4003 B hB hF
  simpa only [sourceForm919, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2392, h2393, h2394, h2405, h2732, h2909, h2910, h2955, h3055, h3347, h3348, h3358, h3541, h3559, h3565, h3584, h3714, h3733, h3839, h3845, h3862, h3868, h3869, h3872, h3876, h3877, h3889, h3949, h3993, h4003, reducedSource802] using sourceEq919 B hB

theorem rowSound802 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row802 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck802, numericCheck802, reducedZero802 B hB hF, mul_zero]

theorem reducedZero803 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource803 (mixedVector B) = 0 := by
  have h2591 : mixedVector B (Sum.inr 2591) = Sparse.eval nodeValue2591 (mixedVector B) := by
    change mixedMoment B node2591 node2591Labels = _
    exact sound2591 B hB hF
  have h3733 : mixedVector B (Sum.inr 3733) = Sparse.eval nodeValue3733 (mixedVector B) := by
    change mixedMoment B node3733 node3733Labels = _
    exact sound3733 B hB hF
  have h3819 : mixedVector B (Sum.inr 3819) = Sparse.eval nodeValue3819 (mixedVector B) := by
    change mixedMoment B node3819 node3819Labels = _
    exact sound3819 B hB hF
  have h3845 : mixedVector B (Sum.inr 3845) = Sparse.eval nodeValue3845 (mixedVector B) := by
    change mixedMoment B node3845 node3845Labels = _
    exact sound3845 B hB hF
  have h3854 : mixedVector B (Sum.inr 3854) = Sparse.eval nodeValue3854 (mixedVector B) := by
    change mixedMoment B node3854 node3854Labels = _
    exact sound3854 B hB hF
  have h3857 : mixedVector B (Sum.inr 3857) = Sparse.eval nodeValue3857 (mixedVector B) := by
    change mixedMoment B node3857 node3857Labels = _
    exact sound3857 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm920, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2591, h3733, h3819, h3845, h3854, h3857, h4092, reducedSource803] using sourceEq920 B hB

theorem rowSound803 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row803 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck803, numericCheck803, reducedZero803 B hB hF, mul_zero]

theorem reducedZero804 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource804 (mixedVector B) = 0 := by
  have h2031 : mixedVector B (Sum.inr 2031) = Sparse.eval nodeValue2031 (mixedVector B) := by
    change mixedMoment B node2031 node2031Labels = _
    exact sound2031 B hB hF
  have h2032 : mixedVector B (Sum.inr 2032) = Sparse.eval nodeValue2032 (mixedVector B) := by
    change mixedMoment B node2032 node2032Labels = _
    exact sound2032 B hB hF
  have h2039 : mixedVector B (Sum.inr 2039) = Sparse.eval nodeValue2039 (mixedVector B) := by
    change mixedMoment B node2039 node2039Labels = _
    exact sound2039 B hB hF
  have h2049 : mixedVector B (Sum.inr 2049) = Sparse.eval nodeValue2049 (mixedVector B) := by
    change mixedMoment B node2049 node2049Labels = _
    exact sound2049 B hB hF
  have h2251 : mixedVector B (Sum.inr 2251) = Sparse.eval nodeValue2251 (mixedVector B) := by
    change mixedMoment B node2251 node2251Labels = _
    exact sound2251 B hB hF
  have h2606 : mixedVector B (Sum.inr 2606) = Sparse.eval nodeValue2606 (mixedVector B) := by
    change mixedMoment B node2606 node2606Labels = _
    exact sound2606 B hB hF
  have h2608 : mixedVector B (Sum.inr 2608) = Sparse.eval nodeValue2608 (mixedVector B) := by
    change mixedMoment B node2608 node2608Labels = _
    exact sound2608 B hB hF
  have h2632 : mixedVector B (Sum.inr 2632) = Sparse.eval nodeValue2632 (mixedVector B) := by
    change mixedMoment B node2632 node2632Labels = _
    exact sound2632 B hB hF
  have h2677 : mixedVector B (Sum.inr 2677) = Sparse.eval nodeValue2677 (mixedVector B) := by
    change mixedMoment B node2677 node2677Labels = _
    exact sound2677 B hB hF
  have h3527 : mixedVector B (Sum.inr 3527) = Sparse.eval nodeValue3527 (mixedVector B) := by
    change mixedMoment B node3527 node3527Labels = _
    exact sound3527 B hB hF
  have h3538 : mixedVector B (Sum.inr 3538) = Sparse.eval nodeValue3538 (mixedVector B) := by
    change mixedMoment B node3538 node3538Labels = _
    exact sound3538 B hB hF
  have h3540 : mixedVector B (Sum.inr 3540) = Sparse.eval nodeValue3540 (mixedVector B) := by
    change mixedMoment B node3540 node3540Labels = _
    exact sound3540 B hB hF
  have h3575 : mixedVector B (Sum.inr 3575) = Sparse.eval nodeValue3575 (mixedVector B) := by
    change mixedMoment B node3575 node3575Labels = _
    exact sound3575 B hB hF
  have h3696 : mixedVector B (Sum.inr 3696) = Sparse.eval nodeValue3696 (mixedVector B) := by
    change mixedMoment B node3696 node3696Labels = _
    exact sound3696 B hB hF
  have h3699 : mixedVector B (Sum.inr 3699) = Sparse.eval nodeValue3699 (mixedVector B) := by
    change mixedMoment B node3699 node3699Labels = _
    exact sound3699 B hB hF
  have h3780 : mixedVector B (Sum.inr 3780) = Sparse.eval nodeValue3780 (mixedVector B) := by
    change mixedMoment B node3780 node3780Labels = _
    exact sound3780 B hB hF
  have h3802 : mixedVector B (Sum.inr 3802) = Sparse.eval nodeValue3802 (mixedVector B) := by
    change mixedMoment B node3802 node3802Labels = _
    exact sound3802 B hB hF
  have h3811 : mixedVector B (Sum.inr 3811) = Sparse.eval nodeValue3811 (mixedVector B) := by
    change mixedMoment B node3811 node3811Labels = _
    exact sound3811 B hB hF
  have h3813 : mixedVector B (Sum.inr 3813) = Sparse.eval nodeValue3813 (mixedVector B) := by
    change mixedMoment B node3813 node3813Labels = _
    exact sound3813 B hB hF
  have h3827 : mixedVector B (Sum.inr 3827) = Sparse.eval nodeValue3827 (mixedVector B) := by
    change mixedMoment B node3827 node3827Labels = _
    exact sound3827 B hB hF
  have h3831 : mixedVector B (Sum.inr 3831) = Sparse.eval nodeValue3831 (mixedVector B) := by
    change mixedMoment B node3831 node3831Labels = _
    exact sound3831 B hB hF
  have h3834 : mixedVector B (Sum.inr 3834) = Sparse.eval nodeValue3834 (mixedVector B) := by
    change mixedMoment B node3834 node3834Labels = _
    exact sound3834 B hB hF
  have h3840 : mixedVector B (Sum.inr 3840) = Sparse.eval nodeValue3840 (mixedVector B) := by
    change mixedMoment B node3840 node3840Labels = _
    exact sound3840 B hB hF
  have h3846 : mixedVector B (Sum.inr 3846) = Sparse.eval nodeValue3846 (mixedVector B) := by
    change mixedMoment B node3846 node3846Labels = _
    exact sound3846 B hB hF
  have h3850 : mixedVector B (Sum.inr 3850) = Sparse.eval nodeValue3850 (mixedVector B) := by
    change mixedMoment B node3850 node3850Labels = _
    exact sound3850 B hB hF
  have h3852 : mixedVector B (Sum.inr 3852) = Sparse.eval nodeValue3852 (mixedVector B) := by
    change mixedMoment B node3852 node3852Labels = _
    exact sound3852 B hB hF
  have h3856 : mixedVector B (Sum.inr 3856) = Sparse.eval nodeValue3856 (mixedVector B) := by
    change mixedMoment B node3856 node3856Labels = _
    exact sound3856 B hB hF
  have h3881 : mixedVector B (Sum.inr 3881) = Sparse.eval nodeValue3881 (mixedVector B) := by
    change mixedMoment B node3881 node3881Labels = _
    exact sound3881 B hB hF
  have h3995 : mixedVector B (Sum.inr 3995) = Sparse.eval nodeValue3995 (mixedVector B) := by
    change mixedMoment B node3995 node3995Labels = _
    exact sound3995 B hB hF
  simpa only [sourceForm923, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2031, h2032, h2039, h2049, h2251, h2606, h2608, h2632, h2677, h3527, h3538, h3540, h3575, h3696, h3699, h3780, h3802, h3811, h3813, h3827, h3831, h3834, h3840, h3846, h3850, h3852, h3856, h3881, h3995, reducedSource804] using sourceEq923 B hB

theorem rowSound804 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row804 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck804, numericCheck804, reducedZero804 B hB hF, mul_zero]

theorem reducedZero805 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource805 (mixedVector B) = 0 := by
  have h2078 : mixedVector B (Sum.inr 2078) = Sparse.eval nodeValue2078 (mixedVector B) := by
    change mixedMoment B node2078 node2078Labels = _
    exact sound2078 B hB hF
  have h2080 : mixedVector B (Sum.inr 2080) = Sparse.eval nodeValue2080 (mixedVector B) := by
    change mixedMoment B node2080 node2080Labels = _
    exact sound2080 B hB hF
  have h2081 : mixedVector B (Sum.inr 2081) = Sparse.eval nodeValue2081 (mixedVector B) := by
    change mixedMoment B node2081 node2081Labels = _
    exact sound2081 B hB hF
  have h2108 : mixedVector B (Sum.inr 2108) = Sparse.eval nodeValue2108 (mixedVector B) := by
    change mixedMoment B node2108 node2108Labels = _
    exact sound2108 B hB hF
  have h2217 : mixedVector B (Sum.inr 2217) = Sparse.eval nodeValue2217 (mixedVector B) := by
    change mixedMoment B node2217 node2217Labels = _
    exact sound2217 B hB hF
  have h2860 : mixedVector B (Sum.inr 2860) = Sparse.eval nodeValue2860 (mixedVector B) := by
    change mixedMoment B node2860 node2860Labels = _
    exact sound2860 B hB hF
  have h2867 : mixedVector B (Sum.inr 2867) = Sparse.eval nodeValue2867 (mixedVector B) := by
    change mixedMoment B node2867 node2867Labels = _
    exact sound2867 B hB hF
  have h2876 : mixedVector B (Sum.inr 2876) = Sparse.eval nodeValue2876 (mixedVector B) := by
    change mixedMoment B node2876 node2876Labels = _
    exact sound2876 B hB hF
  have h3086 : mixedVector B (Sum.inr 3086) = Sparse.eval nodeValue3086 (mixedVector B) := by
    change mixedMoment B node3086 node3086Labels = _
    exact sound3086 B hB hF
  have h3374 : mixedVector B (Sum.inr 3374) = Sparse.eval nodeValue3374 (mixedVector B) := by
    change mixedMoment B node3374 node3374Labels = _
    exact sound3374 B hB hF
  have h3379 : mixedVector B (Sum.inr 3379) = Sparse.eval nodeValue3379 (mixedVector B) := by
    change mixedMoment B node3379 node3379Labels = _
    exact sound3379 B hB hF
  have h3386 : mixedVector B (Sum.inr 3386) = Sparse.eval nodeValue3386 (mixedVector B) := by
    change mixedMoment B node3386 node3386Labels = _
    exact sound3386 B hB hF
  have h3570 : mixedVector B (Sum.inr 3570) = Sparse.eval nodeValue3570 (mixedVector B) := by
    change mixedMoment B node3570 node3570Labels = _
    exact sound3570 B hB hF
  have h3722 : mixedVector B (Sum.inr 3722) = Sparse.eval nodeValue3722 (mixedVector B) := by
    change mixedMoment B node3722 node3722Labels = _
    exact sound3722 B hB hF
  have h3738 : mixedVector B (Sum.inr 3738) = Sparse.eval nodeValue3738 (mixedVector B) := by
    change mixedMoment B node3738 node3738Labels = _
    exact sound3738 B hB hF
  have h3752 : mixedVector B (Sum.inr 3752) = Sparse.eval nodeValue3752 (mixedVector B) := by
    change mixedMoment B node3752 node3752Labels = _
    exact sound3752 B hB hF
  have h3762 : mixedVector B (Sum.inr 3762) = Sparse.eval nodeValue3762 (mixedVector B) := by
    change mixedMoment B node3762 node3762Labels = _
    exact sound3762 B hB hF
  have h3771 : mixedVector B (Sum.inr 3771) = Sparse.eval nodeValue3771 (mixedVector B) := by
    change mixedMoment B node3771 node3771Labels = _
    exact sound3771 B hB hF
  have h3772 : mixedVector B (Sum.inr 3772) = Sparse.eval nodeValue3772 (mixedVector B) := by
    change mixedMoment B node3772 node3772Labels = _
    exact sound3772 B hB hF
  have h3788 : mixedVector B (Sum.inr 3788) = Sparse.eval nodeValue3788 (mixedVector B) := by
    change mixedMoment B node3788 node3788Labels = _
    exact sound3788 B hB hF
  have h3814 : mixedVector B (Sum.inr 3814) = Sparse.eval nodeValue3814 (mixedVector B) := by
    change mixedMoment B node3814 node3814Labels = _
    exact sound3814 B hB hF
  have h3872 : mixedVector B (Sum.inr 3872) = Sparse.eval nodeValue3872 (mixedVector B) := by
    change mixedMoment B node3872 node3872Labels = _
    exact sound3872 B hB hF
  have h3873 : mixedVector B (Sum.inr 3873) = Sparse.eval nodeValue3873 (mixedVector B) := by
    change mixedMoment B node3873 node3873Labels = _
    exact sound3873 B hB hF
  have h3883 : mixedVector B (Sum.inr 3883) = Sparse.eval nodeValue3883 (mixedVector B) := by
    change mixedMoment B node3883 node3883Labels = _
    exact sound3883 B hB hF
  have h3884 : mixedVector B (Sum.inr 3884) = Sparse.eval nodeValue3884 (mixedVector B) := by
    change mixedMoment B node3884 node3884Labels = _
    exact sound3884 B hB hF
  have h3954 : mixedVector B (Sum.inr 3954) = Sparse.eval nodeValue3954 (mixedVector B) := by
    change mixedMoment B node3954 node3954Labels = _
    exact sound3954 B hB hF
  have h3958 : mixedVector B (Sum.inr 3958) = Sparse.eval nodeValue3958 (mixedVector B) := by
    change mixedMoment B node3958 node3958Labels = _
    exact sound3958 B hB hF
  have h3959 : mixedVector B (Sum.inr 3959) = Sparse.eval nodeValue3959 (mixedVector B) := by
    change mixedMoment B node3959 node3959Labels = _
    exact sound3959 B hB hF
  have h3982 : mixedVector B (Sum.inr 3982) = Sparse.eval nodeValue3982 (mixedVector B) := by
    change mixedMoment B node3982 node3982Labels = _
    exact sound3982 B hB hF
  have h4027 : mixedVector B (Sum.inr 4027) = Sparse.eval nodeValue4027 (mixedVector B) := by
    change mixedMoment B node4027 node4027Labels = _
    exact sound4027 B hB hF
  simpa only [sourceForm924, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2078, h2080, h2081, h2108, h2217, h2860, h2867, h2876, h3086, h3374, h3379, h3386, h3570, h3722, h3738, h3752, h3762, h3771, h3772, h3788, h3814, h3872, h3873, h3883, h3884, h3954, h3958, h3959, h3982, h4027, reducedSource805] using sourceEq924 B hB

theorem rowSound805 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row805 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck805, numericCheck805, reducedZero805 B hB hF, mul_zero]

theorem reducedZero806 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource806 (mixedVector B) = 0 := by
  have h2619 : mixedVector B (Sum.inr 2619) = Sparse.eval nodeValue2619 (mixedVector B) := by
    change mixedMoment B node2619 node2619Labels = _
    exact sound2619 B hB hF
  have h2872 : mixedVector B (Sum.inr 2872) = Sparse.eval nodeValue2872 (mixedVector B) := by
    change mixedMoment B node2872 node2872Labels = _
    exact sound2872 B hB hF
  have h3175 : mixedVector B (Sum.inr 3175) = Sparse.eval nodeValue3175 (mixedVector B) := by
    change mixedMoment B node3175 node3175Labels = _
    exact sound3175 B hB hF
  have h3180 : mixedVector B (Sum.inr 3180) = Sparse.eval nodeValue3180 (mixedVector B) := by
    change mixedMoment B node3180 node3180Labels = _
    exact sound3180 B hB hF
  have h3198 : mixedVector B (Sum.inr 3198) = Sparse.eval nodeValue3198 (mixedVector B) := by
    change mixedMoment B node3198 node3198Labels = _
    exact sound3198 B hB hF
  have h3877 : mixedVector B (Sum.inr 3877) = Sparse.eval nodeValue3877 (mixedVector B) := by
    change mixedMoment B node3877 node3877Labels = _
    exact sound3877 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm925, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2619, h2872, h3175, h3180, h3198, h3877, h4092, reducedSource806] using sourceEq925 B hB

theorem rowSound806 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row806 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck806, numericCheck806, reducedZero806 B hB hF, mul_zero]

theorem reducedZero807 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource807 (mixedVector B) = 0 := by
  have h3180 : mixedVector B (Sum.inr 3180) = Sparse.eval nodeValue3180 (mixedVector B) := by
    change mixedMoment B node3180 node3180Labels = _
    exact sound3180 B hB hF
  have h3732 : mixedVector B (Sum.inr 3732) = Sparse.eval nodeValue3732 (mixedVector B) := by
    change mixedMoment B node3732 node3732Labels = _
    exact sound3732 B hB hF
  have h3788 : mixedVector B (Sum.inr 3788) = Sparse.eval nodeValue3788 (mixedVector B) := by
    change mixedMoment B node3788 node3788Labels = _
    exact sound3788 B hB hF
  have h3809 : mixedVector B (Sum.inr 3809) = Sparse.eval nodeValue3809 (mixedVector B) := by
    change mixedMoment B node3809 node3809Labels = _
    exact sound3809 B hB hF
  have h3877 : mixedVector B (Sum.inr 3877) = Sparse.eval nodeValue3877 (mixedVector B) := by
    change mixedMoment B node3877 node3877Labels = _
    exact sound3877 B hB hF
  have h3959 : mixedVector B (Sum.inr 3959) = Sparse.eval nodeValue3959 (mixedVector B) := by
    change mixedMoment B node3959 node3959Labels = _
    exact sound3959 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm926, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3180, h3732, h3788, h3809, h3877, h3959, h4092, reducedSource807] using sourceEq926 B hB

theorem rowSound807 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row807 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck807, numericCheck807, reducedZero807 B hB hF, mul_zero]

theorem reducedZero808 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource808 (mixedVector B) = 0 := by
  have h2634 : mixedVector B (Sum.inr 2634) = Sparse.eval nodeValue2634 (mixedVector B) := by
    change mixedMoment B node2634 node2634Labels = _
    exact sound2634 B hB hF
  have h2873 : mixedVector B (Sum.inr 2873) = Sparse.eval nodeValue2873 (mixedVector B) := by
    change mixedMoment B node2873 node2873Labels = _
    exact sound2873 B hB hF
  have h3699 : mixedVector B (Sum.inr 3699) = Sparse.eval nodeValue3699 (mixedVector B) := by
    change mixedMoment B node3699 node3699Labels = _
    exact sound3699 B hB hF
  have h3828 : mixedVector B (Sum.inr 3828) = Sparse.eval nodeValue3828 (mixedVector B) := by
    change mixedMoment B node3828 node3828Labels = _
    exact sound3828 B hB hF
  have h3877 : mixedVector B (Sum.inr 3877) = Sparse.eval nodeValue3877 (mixedVector B) := by
    change mixedMoment B node3877 node3877Labels = _
    exact sound3877 B hB hF
  have h3884 : mixedVector B (Sum.inr 3884) = Sparse.eval nodeValue3884 (mixedVector B) := by
    change mixedMoment B node3884 node3884Labels = _
    exact sound3884 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm927, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2634, h2873, h3699, h3828, h3877, h3884, h4092, reducedSource808] using sourceEq927 B hB

theorem rowSound808 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row808 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck808, numericCheck808, reducedZero808 B hB hF, mul_zero]

theorem reducedZero809 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource809 (mixedVector B) = 0 := by
  have h2616 : mixedVector B (Sum.inr 2616) = Sparse.eval nodeValue2616 (mixedVector B) := by
    change mixedMoment B node2616 node2616Labels = _
    exact sound2616 B hB hF
  have h2870 : mixedVector B (Sum.inr 2870) = Sparse.eval nodeValue2870 (mixedVector B) := by
    change mixedMoment B node2870 node2870Labels = _
    exact sound2870 B hB hF
  have h3698 : mixedVector B (Sum.inr 3698) = Sparse.eval nodeValue3698 (mixedVector B) := by
    change mixedMoment B node3698 node3698Labels = _
    exact sound3698 B hB hF
  have h3788 : mixedVector B (Sum.inr 3788) = Sparse.eval nodeValue3788 (mixedVector B) := by
    change mixedMoment B node3788 node3788Labels = _
    exact sound3788 B hB hF
  have h3874 : mixedVector B (Sum.inr 3874) = Sparse.eval nodeValue3874 (mixedVector B) := by
    change mixedMoment B node3874 node3874Labels = _
    exact sound3874 B hB hF
  have h3877 : mixedVector B (Sum.inr 3877) = Sparse.eval nodeValue3877 (mixedVector B) := by
    change mixedMoment B node3877 node3877Labels = _
    exact sound3877 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm928, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2616, h2870, h3698, h3788, h3874, h3877, h4092, reducedSource809] using sourceEq928 B hB

theorem rowSound809 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row809 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck809, numericCheck809, reducedZero809 B hB hF, mul_zero]

theorem reducedZero810 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource810 (mixedVector B) = 0 := by
  have h2885 : mixedVector B (Sum.inr 2885) = Sparse.eval nodeValue2885 (mixedVector B) := by
    change mixedMoment B node2885 node2885Labels = _
    exact sound2885 B hB hF
  have h3706 : mixedVector B (Sum.inr 3706) = Sparse.eval nodeValue3706 (mixedVector B) := by
    change mixedMoment B node3706 node3706Labels = _
    exact sound3706 B hB hF
  have h3877 : mixedVector B (Sum.inr 3877) = Sparse.eval nodeValue3877 (mixedVector B) := by
    change mixedMoment B node3877 node3877Labels = _
    exact sound3877 B hB hF
  have h3946 : mixedVector B (Sum.inr 3946) = Sparse.eval nodeValue3946 (mixedVector B) := by
    change mixedMoment B node3946 node3946Labels = _
    exact sound3946 B hB hF
  have h3959 : mixedVector B (Sum.inr 3959) = Sparse.eval nodeValue3959 (mixedVector B) := by
    change mixedMoment B node3959 node3959Labels = _
    exact sound3959 B hB hF
  have h3961 : mixedVector B (Sum.inr 3961) = Sparse.eval nodeValue3961 (mixedVector B) := by
    change mixedMoment B node3961 node3961Labels = _
    exact sound3961 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm929, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2885, h3706, h3877, h3946, h3959, h3961, h4092, reducedSource810] using sourceEq929 B hB

theorem rowSound810 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row810 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck810, numericCheck810, reducedZero810 B hB hF, mul_zero]

theorem reducedZero811 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource811 (mixedVector B) = 0 := by
  have h3198 : mixedVector B (Sum.inr 3198) = Sparse.eval nodeValue3198 (mixedVector B) := by
    change mixedMoment B node3198 node3198Labels = _
    exact sound3198 B hB hF
  have h3698 : mixedVector B (Sum.inr 3698) = Sparse.eval nodeValue3698 (mixedVector B) := by
    change mixedMoment B node3698 node3698Labels = _
    exact sound3698 B hB hF
  have h3699 : mixedVector B (Sum.inr 3699) = Sparse.eval nodeValue3699 (mixedVector B) := by
    change mixedMoment B node3699 node3699Labels = _
    exact sound3699 B hB hF
  have h3706 : mixedVector B (Sum.inr 3706) = Sparse.eval nodeValue3706 (mixedVector B) := by
    change mixedMoment B node3706 node3706Labels = _
    exact sound3706 B hB hF
  have h3814 : mixedVector B (Sum.inr 3814) = Sparse.eval nodeValue3814 (mixedVector B) := by
    change mixedMoment B node3814 node3814Labels = _
    exact sound3814 B hB hF
  have h3877 : mixedVector B (Sum.inr 3877) = Sparse.eval nodeValue3877 (mixedVector B) := by
    change mixedMoment B node3877 node3877Labels = _
    exact sound3877 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm930, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3198, h3698, h3699, h3706, h3814, h3877, h4092, reducedSource811] using sourceEq930 B hB

theorem rowSound811 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row811 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck811, numericCheck811, reducedZero811 B hB hF, mul_zero]

theorem reducedZero812 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource812 (mixedVector B) = 0 := by
  have h2620 : mixedVector B (Sum.inr 2620) = Sparse.eval nodeValue2620 (mixedVector B) := by
    change mixedMoment B node2620 node2620Labels = _
    exact sound2620 B hB hF
  have h3045 : mixedVector B (Sum.inr 3045) = Sparse.eval nodeValue3045 (mixedVector B) := by
    change mixedMoment B node3045 node3045Labels = _
    exact sound3045 B hB hF
  have h3723 : mixedVector B (Sum.inr 3723) = Sparse.eval nodeValue3723 (mixedVector B) := by
    change mixedMoment B node3723 node3723Labels = _
    exact sound3723 B hB hF
  have h3732 : mixedVector B (Sum.inr 3732) = Sparse.eval nodeValue3732 (mixedVector B) := by
    change mixedMoment B node3732 node3732Labels = _
    exact sound3732 B hB hF
  have h3850 : mixedVector B (Sum.inr 3850) = Sparse.eval nodeValue3850 (mixedVector B) := by
    change mixedMoment B node3850 node3850Labels = _
    exact sound3850 B hB hF
  have h3877 : mixedVector B (Sum.inr 3877) = Sparse.eval nodeValue3877 (mixedVector B) := by
    change mixedMoment B node3877 node3877Labels = _
    exact sound3877 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm931, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2620, h3045, h3723, h3732, h3850, h3877, h4092, reducedSource812] using sourceEq931 B hB

theorem rowSound812 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row812 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck812, numericCheck812, reducedZero812 B hB hF, mul_zero]

theorem reducedZero813 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource813 (mixedVector B) = 0 := by
  have h4746 : mixedVector B (Sum.inr 4746) = Sparse.eval nodeValue4746 (mixedVector B) := by
    change mixedMoment B node4746 node4746Labels = _
    exact sound4746 B hB hF
  have h4747 : mixedVector B (Sum.inr 4747) = Sparse.eval nodeValue4747 (mixedVector B) := by
    change mixedMoment B node4747 node4747Labels = _
    exact sound4747 B hB hF
  have h4749 : mixedVector B (Sum.inr 4749) = Sparse.eval nodeValue4749 (mixedVector B) := by
    change mixedMoment B node4749 node4749Labels = _
    exact sound4749 B hB hF
  have h4898 : mixedVector B (Sum.inr 4898) = Sparse.eval nodeValue4898 (mixedVector B) := by
    change mixedMoment B node4898 node4898Labels = _
    exact sound4898 B hB hF
  have h5155 : mixedVector B (Sum.inr 5155) = Sparse.eval nodeValue5155 (mixedVector B) := by
    change mixedMoment B node5155 node5155Labels = _
    exact sound5155 B hB hF
  have h5156 : mixedVector B (Sum.inr 5156) = Sparse.eval nodeValue5156 (mixedVector B) := by
    change mixedMoment B node5156 node5156Labels = _
    exact sound5156 B hB hF
  have h5170 : mixedVector B (Sum.inr 5170) = Sparse.eval nodeValue5170 (mixedVector B) := by
    change mixedMoment B node5170 node5170Labels = _
    exact sound5170 B hB hF
  have h5302 : mixedVector B (Sum.inr 5302) = Sparse.eval nodeValue5302 (mixedVector B) := by
    change mixedMoment B node5302 node5302Labels = _
    exact sound5302 B hB hF
  have h5328 : mixedVector B (Sum.inr 5328) = Sparse.eval nodeValue5328 (mixedVector B) := by
    change mixedMoment B node5328 node5328Labels = _
    exact sound5328 B hB hF
  have h5329 : mixedVector B (Sum.inr 5329) = Sparse.eval nodeValue5329 (mixedVector B) := by
    change mixedMoment B node5329 node5329Labels = _
    exact sound5329 B hB hF
  have h5374 : mixedVector B (Sum.inr 5374) = Sparse.eval nodeValue5374 (mixedVector B) := by
    change mixedMoment B node5374 node5374Labels = _
    exact sound5374 B hB hF
  have h5384 : mixedVector B (Sum.inr 5384) = Sparse.eval nodeValue5384 (mixedVector B) := by
    change mixedMoment B node5384 node5384Labels = _
    exact sound5384 B hB hF
  have h5403 : mixedVector B (Sum.inr 5403) = Sparse.eval nodeValue5403 (mixedVector B) := by
    change mixedMoment B node5403 node5403Labels = _
    exact sound5403 B hB hF
  have h5412 : mixedVector B (Sum.inr 5412) = Sparse.eval nodeValue5412 (mixedVector B) := by
    change mixedMoment B node5412 node5412Labels = _
    exact sound5412 B hB hF
  have h5437 : mixedVector B (Sum.inr 5437) = Sparse.eval nodeValue5437 (mixedVector B) := by
    change mixedMoment B node5437 node5437Labels = _
    exact sound5437 B hB hF
  have h5439 : mixedVector B (Sum.inr 5439) = Sparse.eval nodeValue5439 (mixedVector B) := by
    change mixedMoment B node5439 node5439Labels = _
    exact sound5439 B hB hF
  have h5443 : mixedVector B (Sum.inr 5443) = Sparse.eval nodeValue5443 (mixedVector B) := by
    change mixedMoment B node5443 node5443Labels = _
    exact sound5443 B hB hF
  have h5453 : mixedVector B (Sum.inr 5453) = Sparse.eval nodeValue5453 (mixedVector B) := by
    change mixedMoment B node5453 node5453Labels = _
    exact sound5453 B hB hF
  have h5456 : mixedVector B (Sum.inr 5456) = Sparse.eval nodeValue5456 (mixedVector B) := by
    change mixedMoment B node5456 node5456Labels = _
    exact sound5456 B hB hF
  simpa only [sourceForm932, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4746, h4747, h4749, h4898, h5155, h5156, h5170, h5302, h5328, h5329, h5374, h5384, h5403, h5412, h5437, h5439, h5443, h5453, h5456, reducedSource813] using sourceEq932 B hB

theorem rowSound813 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row813 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck813, numericCheck813, reducedZero813 B hB hF, mul_zero]

theorem reducedZero814 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource814 (mixedVector B) = 0 := by
  have h4816 : mixedVector B (Sum.inr 4816) = Sparse.eval nodeValue4816 (mixedVector B) := by
    change mixedMoment B node4816 node4816Labels = _
    exact sound4816 B hB hF
  have h4817 : mixedVector B (Sum.inr 4817) = Sparse.eval nodeValue4817 (mixedVector B) := by
    change mixedMoment B node4817 node4817Labels = _
    exact sound4817 B hB hF
  have h4821 : mixedVector B (Sum.inr 4821) = Sparse.eval nodeValue4821 (mixedVector B) := by
    change mixedMoment B node4821 node4821Labels = _
    exact sound4821 B hB hF
  have h4836 : mixedVector B (Sum.inr 4836) = Sparse.eval nodeValue4836 (mixedVector B) := by
    change mixedMoment B node4836 node4836Labels = _
    exact sound4836 B hB hF
  have h4891 : mixedVector B (Sum.inr 4891) = Sparse.eval nodeValue4891 (mixedVector B) := by
    change mixedMoment B node4891 node4891Labels = _
    exact sound4891 B hB hF
  have h5086 : mixedVector B (Sum.inr 5086) = Sparse.eval nodeValue5086 (mixedVector B) := by
    change mixedMoment B node5086 node5086Labels = _
    exact sound5086 B hB hF
  have h5090 : mixedVector B (Sum.inr 5090) = Sparse.eval nodeValue5090 (mixedVector B) := by
    change mixedMoment B node5090 node5090Labels = _
    exact sound5090 B hB hF
  have h5105 : mixedVector B (Sum.inr 5105) = Sparse.eval nodeValue5105 (mixedVector B) := by
    change mixedMoment B node5105 node5105Labels = _
    exact sound5105 B hB hF
  have h5254 : mixedVector B (Sum.inr 5254) = Sparse.eval nodeValue5254 (mixedVector B) := by
    change mixedMoment B node5254 node5254Labels = _
    exact sound5254 B hB hF
  have h5260 : mixedVector B (Sum.inr 5260) = Sparse.eval nodeValue5260 (mixedVector B) := by
    change mixedMoment B node5260 node5260Labels = _
    exact sound5260 B hB hF
  have h5267 : mixedVector B (Sum.inr 5267) = Sparse.eval nodeValue5267 (mixedVector B) := by
    change mixedMoment B node5267 node5267Labels = _
    exact sound5267 B hB hF
  have h5287 : mixedVector B (Sum.inr 5287) = Sparse.eval nodeValue5287 (mixedVector B) := by
    change mixedMoment B node5287 node5287Labels = _
    exact sound5287 B hB hF
  have h5360 : mixedVector B (Sum.inr 5360) = Sparse.eval nodeValue5360 (mixedVector B) := by
    change mixedMoment B node5360 node5360Labels = _
    exact sound5360 B hB hF
  have h5361 : mixedVector B (Sum.inr 5361) = Sparse.eval nodeValue5361 (mixedVector B) := by
    change mixedMoment B node5361 node5361Labels = _
    exact sound5361 B hB hF
  have h5370 : mixedVector B (Sum.inr 5370) = Sparse.eval nodeValue5370 (mixedVector B) := by
    change mixedMoment B node5370 node5370Labels = _
    exact sound5370 B hB hF
  have h5397 : mixedVector B (Sum.inr 5397) = Sparse.eval nodeValue5397 (mixedVector B) := by
    change mixedMoment B node5397 node5397Labels = _
    exact sound5397 B hB hF
  have h5406 : mixedVector B (Sum.inr 5406) = Sparse.eval nodeValue5406 (mixedVector B) := by
    change mixedMoment B node5406 node5406Labels = _
    exact sound5406 B hB hF
  have h5407 : mixedVector B (Sum.inr 5407) = Sparse.eval nodeValue5407 (mixedVector B) := by
    change mixedMoment B node5407 node5407Labels = _
    exact sound5407 B hB hF
  have h5410 : mixedVector B (Sum.inr 5410) = Sparse.eval nodeValue5410 (mixedVector B) := by
    change mixedMoment B node5410 node5410Labels = _
    exact sound5410 B hB hF
  have h5411 : mixedVector B (Sum.inr 5411) = Sparse.eval nodeValue5411 (mixedVector B) := by
    change mixedMoment B node5411 node5411Labels = _
    exact sound5411 B hB hF
  have h5412 : mixedVector B (Sum.inr 5412) = Sparse.eval nodeValue5412 (mixedVector B) := by
    change mixedMoment B node5412 node5412Labels = _
    exact sound5412 B hB hF
  have h5425 : mixedVector B (Sum.inr 5425) = Sparse.eval nodeValue5425 (mixedVector B) := by
    change mixedMoment B node5425 node5425Labels = _
    exact sound5425 B hB hF
  have h5426 : mixedVector B (Sum.inr 5426) = Sparse.eval nodeValue5426 (mixedVector B) := by
    change mixedMoment B node5426 node5426Labels = _
    exact sound5426 B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434 B hB hF
  have h5435 : mixedVector B (Sum.inr 5435) = Sparse.eval nodeValue5435 (mixedVector B) := by
    change mixedMoment B node5435 node5435Labels = _
    exact sound5435 B hB hF
  have h5436 : mixedVector B (Sum.inr 5436) = Sparse.eval nodeValue5436 (mixedVector B) := by
    change mixedMoment B node5436 node5436Labels = _
    exact sound5436 B hB hF
  simpa only [sourceForm933, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4816, h4817, h4821, h4836, h4891, h5086, h5090, h5105, h5254, h5260, h5267, h5287, h5360, h5361, h5370, h5397, h5406, h5407, h5410, h5411, h5412, h5425, h5426, h5434, h5435, h5436, reducedSource814] using sourceEq933 B hB

theorem rowSound814 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row814 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck814, numericCheck814, reducedZero814 B hB hF, mul_zero]

theorem reducedZero815 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource815 (mixedVector B) = 0 := by
  have h2196 : mixedVector B (Sum.inr 2196) = Sparse.eval nodeValue2196 (mixedVector B) := by
    change mixedMoment B node2196 node2196Labels = _
    exact sound2196 B hB hF
  have h2197 : mixedVector B (Sum.inr 2197) = Sparse.eval nodeValue2197 (mixedVector B) := by
    change mixedMoment B node2197 node2197Labels = _
    exact sound2197 B hB hF
  have h2207 : mixedVector B (Sum.inr 2207) = Sparse.eval nodeValue2207 (mixedVector B) := by
    change mixedMoment B node2207 node2207Labels = _
    exact sound2207 B hB hF
  have h2217 : mixedVector B (Sum.inr 2217) = Sparse.eval nodeValue2217 (mixedVector B) := by
    change mixedMoment B node2217 node2217Labels = _
    exact sound2217 B hB hF
  have h2253 : mixedVector B (Sum.inr 2253) = Sparse.eval nodeValue2253 (mixedVector B) := by
    change mixedMoment B node2253 node2253Labels = _
    exact sound2253 B hB hF
  have h3016 : mixedVector B (Sum.inr 3016) = Sparse.eval nodeValue3016 (mixedVector B) := by
    change mixedMoment B node3016 node3016Labels = _
    exact sound3016 B hB hF
  have h3025 : mixedVector B (Sum.inr 3025) = Sparse.eval nodeValue3025 (mixedVector B) := by
    change mixedMoment B node3025 node3025Labels = _
    exact sound3025 B hB hF
  have h3038 : mixedVector B (Sum.inr 3038) = Sparse.eval nodeValue3038 (mixedVector B) := by
    change mixedMoment B node3038 node3038Labels = _
    exact sound3038 B hB hF
  have h3086 : mixedVector B (Sum.inr 3086) = Sparse.eval nodeValue3086 (mixedVector B) := by
    change mixedMoment B node3086 node3086Labels = _
    exact sound3086 B hB hF
  have h3464 : mixedVector B (Sum.inr 3464) = Sparse.eval nodeValue3464 (mixedVector B) := by
    change mixedMoment B node3464 node3464Labels = _
    exact sound3464 B hB hF
  have h3479 : mixedVector B (Sum.inr 3479) = Sparse.eval nodeValue3479 (mixedVector B) := by
    change mixedMoment B node3479 node3479Labels = _
    exact sound3479 B hB hF
  have h3480 : mixedVector B (Sum.inr 3480) = Sparse.eval nodeValue3480 (mixedVector B) := by
    change mixedMoment B node3480 node3480Labels = _
    exact sound3480 B hB hF
  have h3541 : mixedVector B (Sum.inr 3541) = Sparse.eval nodeValue3541 (mixedVector B) := by
    change mixedMoment B node3541 node3541Labels = _
    exact sound3541 B hB hF
  have h3762 : mixedVector B (Sum.inr 3762) = Sparse.eval nodeValue3762 (mixedVector B) := by
    change mixedMoment B node3762 node3762Labels = _
    exact sound3762 B hB hF
  have h3771 : mixedVector B (Sum.inr 3771) = Sparse.eval nodeValue3771 (mixedVector B) := by
    change mixedMoment B node3771 node3771Labels = _
    exact sound3771 B hB hF
  have h3772 : mixedVector B (Sum.inr 3772) = Sparse.eval nodeValue3772 (mixedVector B) := by
    change mixedMoment B node3772 node3772Labels = _
    exact sound3772 B hB hF
  have h3796 : mixedVector B (Sum.inr 3796) = Sparse.eval nodeValue3796 (mixedVector B) := by
    change mixedMoment B node3796 node3796Labels = _
    exact sound3796 B hB hF
  have h3801 : mixedVector B (Sum.inr 3801) = Sparse.eval nodeValue3801 (mixedVector B) := by
    change mixedMoment B node3801 node3801Labels = _
    exact sound3801 B hB hF
  have h3803 : mixedVector B (Sum.inr 3803) = Sparse.eval nodeValue3803 (mixedVector B) := by
    change mixedMoment B node3803 node3803Labels = _
    exact sound3803 B hB hF
  have h3808 : mixedVector B (Sum.inr 3808) = Sparse.eval nodeValue3808 (mixedVector B) := by
    change mixedMoment B node3808 node3808Labels = _
    exact sound3808 B hB hF
  have h3809 : mixedVector B (Sum.inr 3809) = Sparse.eval nodeValue3809 (mixedVector B) := by
    change mixedMoment B node3809 node3809Labels = _
    exact sound3809 B hB hF
  have h3813 : mixedVector B (Sum.inr 3813) = Sparse.eval nodeValue3813 (mixedVector B) := by
    change mixedMoment B node3813 node3813Labels = _
    exact sound3813 B hB hF
  have h3841 : mixedVector B (Sum.inr 3841) = Sparse.eval nodeValue3841 (mixedVector B) := by
    change mixedMoment B node3841 node3841Labels = _
    exact sound3841 B hB hF
  have h3853 : mixedVector B (Sum.inr 3853) = Sparse.eval nodeValue3853 (mixedVector B) := by
    change mixedMoment B node3853 node3853Labels = _
    exact sound3853 B hB hF
  have h3856 : mixedVector B (Sum.inr 3856) = Sparse.eval nodeValue3856 (mixedVector B) := by
    change mixedMoment B node3856 node3856Labels = _
    exact sound3856 B hB hF
  have h3872 : mixedVector B (Sum.inr 3872) = Sparse.eval nodeValue3872 (mixedVector B) := by
    change mixedMoment B node3872 node3872Labels = _
    exact sound3872 B hB hF
  have h3877 : mixedVector B (Sum.inr 3877) = Sparse.eval nodeValue3877 (mixedVector B) := by
    change mixedMoment B node3877 node3877Labels = _
    exact sound3877 B hB hF
  have h3883 : mixedVector B (Sum.inr 3883) = Sparse.eval nodeValue3883 (mixedVector B) := by
    change mixedMoment B node3883 node3883Labels = _
    exact sound3883 B hB hF
  have h3982 : mixedVector B (Sum.inr 3982) = Sparse.eval nodeValue3982 (mixedVector B) := by
    change mixedMoment B node3982 node3982Labels = _
    exact sound3982 B hB hF
  simpa only [sourceForm934, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2196, h2197, h2207, h2217, h2253, h3016, h3025, h3038, h3086, h3464, h3479, h3480, h3541, h3762, h3771, h3772, h3796, h3801, h3803, h3808, h3809, h3813, h3841, h3853, h3856, h3872, h3877, h3883, h3982, reducedSource815] using sourceEq934 B hB

theorem rowSound815 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row815 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck815, numericCheck815, reducedZero815 B hB hF, mul_zero]

theorem sourceRowsAt800 : MixedData.sourceRows (800 : Fin 2425) =
    MixedData.row800 := by decide +kernel

theorem sourceRowsAt801 : MixedData.sourceRows (801 : Fin 2425) =
    MixedData.row801 := by decide +kernel

theorem sourceRowsAt802 : MixedData.sourceRows (802 : Fin 2425) =
    MixedData.row802 := by decide +kernel

theorem sourceRowsAt803 : MixedData.sourceRows (803 : Fin 2425) =
    MixedData.row803 := by decide +kernel

theorem sourceRowsAt804 : MixedData.sourceRows (804 : Fin 2425) =
    MixedData.row804 := by decide +kernel

theorem sourceRowsAt805 : MixedData.sourceRows (805 : Fin 2425) =
    MixedData.row805 := by decide +kernel

theorem sourceRowsAt806 : MixedData.sourceRows (806 : Fin 2425) =
    MixedData.row806 := by decide +kernel

theorem sourceRowsAt807 : MixedData.sourceRows (807 : Fin 2425) =
    MixedData.row807 := by decide +kernel

theorem sourceRowsAt808 : MixedData.sourceRows (808 : Fin 2425) =
    MixedData.row808 := by decide +kernel

theorem sourceRowsAt809 : MixedData.sourceRows (809 : Fin 2425) =
    MixedData.row809 := by decide +kernel

theorem sourceRowsAt810 : MixedData.sourceRows (810 : Fin 2425) =
    MixedData.row810 := by decide +kernel

theorem sourceRowsAt811 : MixedData.sourceRows (811 : Fin 2425) =
    MixedData.row811 := by decide +kernel

theorem sourceRowsAt812 : MixedData.sourceRows (812 : Fin 2425) =
    MixedData.row812 := by decide +kernel

theorem sourceRowsAt813 : MixedData.sourceRows (813 : Fin 2425) =
    MixedData.row813 := by decide +kernel

theorem sourceRowsAt814 : MixedData.sourceRows (814 : Fin 2425) =
    MixedData.row814 := by decide +kernel

theorem sourceRowsAt815 : MixedData.sourceRows (815 : Fin 2425) =
    MixedData.row815 := by decide +kernel

theorem chunkSound50 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 50) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 800 ∨ k.val = 801 ∨ k.val = 802 ∨ k.val = 803 ∨ k.val = 804 ∨ k.val = 805 ∨ k.val = 806 ∨ k.val = 807 ∨ k.val = 808 ∨ k.val = 809 ∨ k.val = 810 ∨ k.val = 811 ∨ k.val = 812 ∨ k.val = 813 ∨ k.val = 814 ∨ k.val = 815 := by omega
  rcases heq with h800 | h801 | h802 | h803 | h804 | h805 | h806 | h807 | h808 | h809 | h810 | h811 | h812 | h813 | h814 | h815
  · have he : k = (800 : Fin 2425) := Fin.ext h800
    subst k
    rw [sourceRowsAt800]
    exact rowSound800 B hB hF
  · have he : k = (801 : Fin 2425) := Fin.ext h801
    subst k
    rw [sourceRowsAt801]
    exact rowSound801 B hB hF
  · have he : k = (802 : Fin 2425) := Fin.ext h802
    subst k
    rw [sourceRowsAt802]
    exact rowSound802 B hB hF
  · have he : k = (803 : Fin 2425) := Fin.ext h803
    subst k
    rw [sourceRowsAt803]
    exact rowSound803 B hB hF
  · have he : k = (804 : Fin 2425) := Fin.ext h804
    subst k
    rw [sourceRowsAt804]
    exact rowSound804 B hB hF
  · have he : k = (805 : Fin 2425) := Fin.ext h805
    subst k
    rw [sourceRowsAt805]
    exact rowSound805 B hB hF
  · have he : k = (806 : Fin 2425) := Fin.ext h806
    subst k
    rw [sourceRowsAt806]
    exact rowSound806 B hB hF
  · have he : k = (807 : Fin 2425) := Fin.ext h807
    subst k
    rw [sourceRowsAt807]
    exact rowSound807 B hB hF
  · have he : k = (808 : Fin 2425) := Fin.ext h808
    subst k
    rw [sourceRowsAt808]
    exact rowSound808 B hB hF
  · have he : k = (809 : Fin 2425) := Fin.ext h809
    subst k
    rw [sourceRowsAt809]
    exact rowSound809 B hB hF
  · have he : k = (810 : Fin 2425) := Fin.ext h810
    subst k
    rw [sourceRowsAt810]
    exact rowSound810 B hB hF
  · have he : k = (811 : Fin 2425) := Fin.ext h811
    subst k
    rw [sourceRowsAt811]
    exact rowSound811 B hB hF
  · have he : k = (812 : Fin 2425) := Fin.ext h812
    subst k
    rw [sourceRowsAt812]
    exact rowSound812 B hB hF
  · have he : k = (813 : Fin 2425) := Fin.ext h813
    subst k
    rw [sourceRowsAt813]
    exact rowSound813 B hB hF
  · have he : k = (814 : Fin 2425) := Fin.ext h814
    subst k
    rw [sourceRowsAt814]
    exact rowSound814 B hB hF
  · have he : k = (815 : Fin 2425) := Fin.ext h815
    subst k
    rw [sourceRowsAt815]
    exact rowSound815 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
