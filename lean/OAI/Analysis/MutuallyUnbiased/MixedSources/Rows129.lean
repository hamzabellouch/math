import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic129
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound72
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources81

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2064 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2064 (mixedVector B) = 0 := by
  have h4680 : mixedVector B (Sum.inr 4680) = Sparse.eval nodeValue4680 (mixedVector B) := by
    change mixedMoment B node4680 node4680Labels = _
    exact sound4680 B hB hF
  have h4682 : mixedVector B (Sum.inr 4682) = Sparse.eval nodeValue4682 (mixedVector B) := by
    change mixedMoment B node4682 node4682Labels = _
    exact sound4682 B hB hF
  have h4683 : mixedVector B (Sum.inr 4683) = Sparse.eval nodeValue4683 (mixedVector B) := by
    change mixedMoment B node4683 node4683Labels = _
    exact sound4683 B hB hF
  have h4690 : mixedVector B (Sum.inr 4690) = Sparse.eval nodeValue4690 (mixedVector B) := by
    change mixedMoment B node4690 node4690Labels = _
    exact sound4690 B hB hF
  have h4867 : mixedVector B (Sum.inr 4867) = Sparse.eval nodeValue4867 (mixedVector B) := by
    change mixedMoment B node4867 node4867Labels = _
    exact sound4867 B hB hF
  have h4963 : mixedVector B (Sum.inr 4963) = Sparse.eval nodeValue4963 (mixedVector B) := by
    change mixedMoment B node4963 node4963Labels = _
    exact sound4963 B hB hF
  have h4965 : mixedVector B (Sum.inr 4965) = Sparse.eval nodeValue4965 (mixedVector B) := by
    change mixedMoment B node4965 node4965Labels = _
    exact sound4965 B hB hF
  have h4966 : mixedVector B (Sum.inr 4966) = Sparse.eval nodeValue4966 (mixedVector B) := by
    change mixedMoment B node4966 node4966Labels = _
    exact sound4966 B hB hF
  have h4976 : mixedVector B (Sum.inr 4976) = Sparse.eval nodeValue4976 (mixedVector B) := by
    change mixedMoment B node4976 node4976Labels = _
    exact sound4976 B hB hF
  have h5042 : mixedVector B (Sum.inr 5042) = Sparse.eval nodeValue5042 (mixedVector B) := by
    change mixedMoment B node5042 node5042Labels = _
    exact sound5042 B hB hF
  have h5080 : mixedVector B (Sum.inr 5080) = Sparse.eval nodeValue5080 (mixedVector B) := by
    change mixedMoment B node5080 node5080Labels = _
    exact sound5080 B hB hF
  have h5163 : mixedVector B (Sum.inr 5163) = Sparse.eval nodeValue5163 (mixedVector B) := by
    change mixedMoment B node5163 node5163Labels = _
    exact sound5163 B hB hF
  have h5188 : mixedVector B (Sum.inr 5188) = Sparse.eval nodeValue5188 (mixedVector B) := by
    change mixedMoment B node5188 node5188Labels = _
    exact sound5188 B hB hF
  have h5216 : mixedVector B (Sum.inr 5216) = Sparse.eval nodeValue5216 (mixedVector B) := by
    change mixedMoment B node5216 node5216Labels = _
    exact sound5216 B hB hF
  have h5232 : mixedVector B (Sum.inr 5232) = Sparse.eval nodeValue5232 (mixedVector B) := by
    change mixedMoment B node5232 node5232Labels = _
    exact sound5232 B hB hF
  have h5264 : mixedVector B (Sum.inr 5264) = Sparse.eval nodeValue5264 (mixedVector B) := by
    change mixedMoment B node5264 node5264Labels = _
    exact sound5264 B hB hF
  have h5339 : mixedVector B (Sum.inr 5339) = Sparse.eval nodeValue5339 (mixedVector B) := by
    change mixedMoment B node5339 node5339Labels = _
    exact sound5339 B hB hF
  have h5355 : mixedVector B (Sum.inr 5355) = Sparse.eval nodeValue5355 (mixedVector B) := by
    change mixedMoment B node5355 node5355Labels = _
    exact sound5355 B hB hF
  have h5378 : mixedVector B (Sum.inr 5378) = Sparse.eval nodeValue5378 (mixedVector B) := by
    change mixedMoment B node5378 node5378Labels = _
    exact sound5378 B hB hF
  have h5381 : mixedVector B (Sum.inr 5381) = Sparse.eval nodeValue5381 (mixedVector B) := by
    change mixedMoment B node5381 node5381Labels = _
    exact sound5381 B hB hF
  have h5382 : mixedVector B (Sum.inr 5382) = Sparse.eval nodeValue5382 (mixedVector B) := by
    change mixedMoment B node5382 node5382Labels = _
    exact sound5382 B hB hF
  have h5385 : mixedVector B (Sum.inr 5385) = Sparse.eval nodeValue5385 (mixedVector B) := by
    change mixedMoment B node5385 node5385Labels = _
    exact sound5385 B hB hF
  have h5400 : mixedVector B (Sum.inr 5400) = Sparse.eval nodeValue5400 (mixedVector B) := by
    change mixedMoment B node5400 node5400Labels = _
    exact sound5400 B hB hF
  have h5402 : mixedVector B (Sum.inr 5402) = Sparse.eval nodeValue5402 (mixedVector B) := by
    change mixedMoment B node5402 node5402Labels = _
    exact sound5402 B hB hF
  have h5409 : mixedVector B (Sum.inr 5409) = Sparse.eval nodeValue5409 (mixedVector B) := by
    change mixedMoment B node5409 node5409Labels = _
    exact sound5409 B hB hF
  have h5411 : mixedVector B (Sum.inr 5411) = Sparse.eval nodeValue5411 (mixedVector B) := by
    change mixedMoment B node5411 node5411Labels = _
    exact sound5411 B hB hF
  have h5432 : mixedVector B (Sum.inr 5432) = Sparse.eval nodeValue5432 (mixedVector B) := by
    change mixedMoment B node5432 node5432Labels = _
    exact sound5432 B hB hF
  have h5436 : mixedVector B (Sum.inr 5436) = Sparse.eval nodeValue5436 (mixedVector B) := by
    change mixedMoment B node5436 node5436Labels = _
    exact sound5436 B hB hF
  have h5438 : mixedVector B (Sum.inr 5438) = Sparse.eval nodeValue5438 (mixedVector B) := by
    change mixedMoment B node5438 node5438Labels = _
    exact sound5438 B hB hF
  have h5446 : mixedVector B (Sum.inr 5446) = Sparse.eval nodeValue5446 (mixedVector B) := by
    change mixedMoment B node5446 node5446Labels = _
    exact sound5446 B hB hF
  simpa only [sourceForm2579, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4680, h4682, h4683, h4690, h4867, h4963, h4965, h4966, h4976, h5042, h5080, h5163, h5188, h5216, h5232, h5264, h5339, h5355, h5378, h5381, h5382, h5385, h5400, h5402, h5409, h5411, h5432, h5436, h5438, h5446, reducedSource2064] using sourceEq2579 B hB

theorem rowSound2064 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2064 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2064, numericCheck2064, reducedZero2064 B hB hF, mul_zero]

theorem reducedZero2065 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2065 (mixedVector B) = 0 := by
  have h2145 : mixedVector B (Sum.inr 2145) = Sparse.eval nodeValue2145 (mixedVector B) := by
    change mixedMoment B node2145 node2145Labels = _
    exact sound2145 B hB hF
  have h2146 : mixedVector B (Sum.inr 2146) = Sparse.eval nodeValue2146 (mixedVector B) := by
    change mixedMoment B node2146 node2146Labels = _
    exact sound2146 B hB hF
  have h2153 : mixedVector B (Sum.inr 2153) = Sparse.eval nodeValue2153 (mixedVector B) := by
    change mixedMoment B node2153 node2153Labels = _
    exact sound2153 B hB hF
  have h2158 : mixedVector B (Sum.inr 2158) = Sparse.eval nodeValue2158 (mixedVector B) := by
    change mixedMoment B node2158 node2158Labels = _
    exact sound2158 B hB hF
  have h2251 : mixedVector B (Sum.inr 2251) = Sparse.eval nodeValue2251 (mixedVector B) := by
    change mixedMoment B node2251 node2251Labels = _
    exact sound2251 B hB hF
  have h2654 : mixedVector B (Sum.inr 2654) = Sparse.eval nodeValue2654 (mixedVector B) := by
    change mixedMoment B node2654 node2654Labels = _
    exact sound2654 B hB hF
  have h2659 : mixedVector B (Sum.inr 2659) = Sparse.eval nodeValue2659 (mixedVector B) := by
    change mixedMoment B node2659 node2659Labels = _
    exact sound2659 B hB hF
  have h2677 : mixedVector B (Sum.inr 2677) = Sparse.eval nodeValue2677 (mixedVector B) := by
    change mixedMoment B node2677 node2677Labels = _
    exact sound2677 B hB hF
  have h2729 : mixedVector B (Sum.inr 2729) = Sparse.eval nodeValue2729 (mixedVector B) := by
    change mixedMoment B node2729 node2729Labels = _
    exact sound2729 B hB hF
  have h3462 : mixedVector B (Sum.inr 3462) = Sparse.eval nodeValue3462 (mixedVector B) := by
    change mixedMoment B node3462 node3462Labels = _
    exact sound3462 B hB hF
  have h3475 : mixedVector B (Sum.inr 3475) = Sparse.eval nodeValue3475 (mixedVector B) := by
    change mixedMoment B node3475 node3475Labels = _
    exact sound3475 B hB hF
  have h3478 : mixedVector B (Sum.inr 3478) = Sparse.eval nodeValue3478 (mixedVector B) := by
    change mixedMoment B node3478 node3478Labels = _
    exact sound3478 B hB hF
  have h3538 : mixedVector B (Sum.inr 3538) = Sparse.eval nodeValue3538 (mixedVector B) := by
    change mixedMoment B node3538 node3538Labels = _
    exact sound3538 B hB hF
  have h3553 : mixedVector B (Sum.inr 3553) = Sparse.eval nodeValue3553 (mixedVector B) := by
    change mixedMoment B node3553 node3553Labels = _
    exact sound3553 B hB hF
  have h3555 : mixedVector B (Sum.inr 3555) = Sparse.eval nodeValue3555 (mixedVector B) := by
    change mixedMoment B node3555 node3555Labels = _
    exact sound3555 B hB hF
  have h3564 : mixedVector B (Sum.inr 3564) = Sparse.eval nodeValue3564 (mixedVector B) := by
    change mixedMoment B node3564 node3564Labels = _
    exact sound3564 B hB hF
  have h3760 : mixedVector B (Sum.inr 3760) = Sparse.eval nodeValue3760 (mixedVector B) := by
    change mixedMoment B node3760 node3760Labels = _
    exact sound3760 B hB hF
  have h3770 : mixedVector B (Sum.inr 3770) = Sparse.eval nodeValue3770 (mixedVector B) := by
    change mixedMoment B node3770 node3770Labels = _
    exact sound3770 B hB hF
  have h3795 : mixedVector B (Sum.inr 3795) = Sparse.eval nodeValue3795 (mixedVector B) := by
    change mixedMoment B node3795 node3795Labels = _
    exact sound3795 B hB hF
  have h3799 : mixedVector B (Sum.inr 3799) = Sparse.eval nodeValue3799 (mixedVector B) := by
    change mixedMoment B node3799 node3799Labels = _
    exact sound3799 B hB hF
  have h3802 : mixedVector B (Sum.inr 3802) = Sparse.eval nodeValue3802 (mixedVector B) := by
    change mixedMoment B node3802 node3802Labels = _
    exact sound3802 B hB hF
  have h3807 : mixedVector B (Sum.inr 3807) = Sparse.eval nodeValue3807 (mixedVector B) := by
    change mixedMoment B node3807 node3807Labels = _
    exact sound3807 B hB hF
  have h3813 : mixedVector B (Sum.inr 3813) = Sparse.eval nodeValue3813 (mixedVector B) := by
    change mixedMoment B node3813 node3813Labels = _
    exact sound3813 B hB hF
  have h3834 : mixedVector B (Sum.inr 3834) = Sparse.eval nodeValue3834 (mixedVector B) := by
    change mixedMoment B node3834 node3834Labels = _
    exact sound3834 B hB hF
  have h3850 : mixedVector B (Sum.inr 3850) = Sparse.eval nodeValue3850 (mixedVector B) := by
    change mixedMoment B node3850 node3850Labels = _
    exact sound3850 B hB hF
  have h3854 : mixedVector B (Sum.inr 3854) = Sparse.eval nodeValue3854 (mixedVector B) := by
    change mixedMoment B node3854 node3854Labels = _
    exact sound3854 B hB hF
  have h3866 : mixedVector B (Sum.inr 3866) = Sparse.eval nodeValue3866 (mixedVector B) := by
    change mixedMoment B node3866 node3866Labels = _
    exact sound3866 B hB hF
  have h3868 : mixedVector B (Sum.inr 3868) = Sparse.eval nodeValue3868 (mixedVector B) := by
    change mixedMoment B node3868 node3868Labels = _
    exact sound3868 B hB hF
  have h3876 : mixedVector B (Sum.inr 3876) = Sparse.eval nodeValue3876 (mixedVector B) := by
    change mixedMoment B node3876 node3876Labels = _
    exact sound3876 B hB hF
  have h3881 : mixedVector B (Sum.inr 3881) = Sparse.eval nodeValue3881 (mixedVector B) := by
    change mixedMoment B node3881 node3881Labels = _
    exact sound3881 B hB hF
  simpa only [sourceForm2580, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2145, h2146, h2153, h2158, h2251, h2654, h2659, h2677, h2729, h3462, h3475, h3478, h3538, h3553, h3555, h3564, h3760, h3770, h3795, h3799, h3802, h3807, h3813, h3834, h3850, h3854, h3866, h3868, h3876, h3881, reducedSource2065] using sourceEq2580 B hB

theorem rowSound2065 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2065 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2065, numericCheck2065, reducedZero2065 B hB hF, mul_zero]

theorem reducedZero2066 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2066 (mixedVector B) = 0 := by
  have h4660 : mixedVector B (Sum.inr 4660) = Sparse.eval nodeValue4660 (mixedVector B) := by
    change mixedMoment B node4660 node4660Labels = _
    exact sound4660 B hB hF
  have h4661 : mixedVector B (Sum.inr 4661) = Sparse.eval nodeValue4661 (mixedVector B) := by
    change mixedMoment B node4661 node4661Labels = _
    exact sound4661 B hB hF
  have h4679 : mixedVector B (Sum.inr 4679) = Sparse.eval nodeValue4679 (mixedVector B) := by
    change mixedMoment B node4679 node4679Labels = _
    exact sound4679 B hB hF
  have h4826 : mixedVector B (Sum.inr 4826) = Sparse.eval nodeValue4826 (mixedVector B) := by
    change mixedMoment B node4826 node4826Labels = _
    exact sound4826 B hB hF
  have h4960 : mixedVector B (Sum.inr 4960) = Sparse.eval nodeValue4960 (mixedVector B) := by
    change mixedMoment B node4960 node4960Labels = _
    exact sound4960 B hB hF
  have h4961 : mixedVector B (Sum.inr 4961) = Sparse.eval nodeValue4961 (mixedVector B) := by
    change mixedMoment B node4961 node4961Labels = _
    exact sound4961 B hB hF
  have h4968 : mixedVector B (Sum.inr 4968) = Sparse.eval nodeValue4968 (mixedVector B) := by
    change mixedMoment B node4968 node4968Labels = _
    exact sound4968 B hB hF
  have h5030 : mixedVector B (Sum.inr 5030) = Sparse.eval nodeValue5030 (mixedVector B) := by
    change mixedMoment B node5030 node5030Labels = _
    exact sound5030 B hB hF
  have h5080 : mixedVector B (Sum.inr 5080) = Sparse.eval nodeValue5080 (mixedVector B) := by
    change mixedMoment B node5080 node5080Labels = _
    exact sound5080 B hB hF
  have h5148 : mixedVector B (Sum.inr 5148) = Sparse.eval nodeValue5148 (mixedVector B) := by
    change mixedMoment B node5148 node5148Labels = _
    exact sound5148 B hB hF
  have h5333 : mixedVector B (Sum.inr 5333) = Sparse.eval nodeValue5333 (mixedVector B) := by
    change mixedMoment B node5333 node5333Labels = _
    exact sound5333 B hB hF
  have h5355 : mixedVector B (Sum.inr 5355) = Sparse.eval nodeValue5355 (mixedVector B) := by
    change mixedMoment B node5355 node5355Labels = _
    exact sound5355 B hB hF
  have h5363 : mixedVector B (Sum.inr 5363) = Sparse.eval nodeValue5363 (mixedVector B) := by
    change mixedMoment B node5363 node5363Labels = _
    exact sound5363 B hB hF
  have h5378 : mixedVector B (Sum.inr 5378) = Sparse.eval nodeValue5378 (mixedVector B) := by
    change mixedMoment B node5378 node5378Labels = _
    exact sound5378 B hB hF
  have h5386 : mixedVector B (Sum.inr 5386) = Sparse.eval nodeValue5386 (mixedVector B) := by
    change mixedMoment B node5386 node5386Labels = _
    exact sound5386 B hB hF
  have h5388 : mixedVector B (Sum.inr 5388) = Sparse.eval nodeValue5388 (mixedVector B) := by
    change mixedMoment B node5388 node5388Labels = _
    exact sound5388 B hB hF
  have h5422 : mixedVector B (Sum.inr 5422) = Sparse.eval nodeValue5422 (mixedVector B) := by
    change mixedMoment B node5422 node5422Labels = _
    exact sound5422 B hB hF
  have h5431 : mixedVector B (Sum.inr 5431) = Sparse.eval nodeValue5431 (mixedVector B) := by
    change mixedMoment B node5431 node5431Labels = _
    exact sound5431 B hB hF
  have h5433 : mixedVector B (Sum.inr 5433) = Sparse.eval nodeValue5433 (mixedVector B) := by
    change mixedMoment B node5433 node5433Labels = _
    exact sound5433 B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434 B hB hF
  have h5438 : mixedVector B (Sum.inr 5438) = Sparse.eval nodeValue5438 (mixedVector B) := by
    change mixedMoment B node5438 node5438Labels = _
    exact sound5438 B hB hF
  simpa only [sourceForm2582, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4660, h4661, h4679, h4826, h4960, h4961, h4968, h5030, h5080, h5148, h5333, h5355, h5363, h5378, h5386, h5388, h5422, h5431, h5433, h5434, h5438, reducedSource2066] using sourceEq2582 B hB

theorem rowSound2066 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2066 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2066, numericCheck2066, reducedZero2066 B hB hF, mul_zero]

theorem reducedZero2067 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2067 (mixedVector B) = 0 := by
  have h4663 : mixedVector B (Sum.inr 4663) = Sparse.eval nodeValue4663 (mixedVector B) := by
    change mixedMoment B node4663 node4663Labels = _
    exact sound4663 B hB hF
  have h4666 : mixedVector B (Sum.inr 4666) = Sparse.eval nodeValue4666 (mixedVector B) := by
    change mixedMoment B node4666 node4666Labels = _
    exact sound4666 B hB hF
  have h4677 : mixedVector B (Sum.inr 4677) = Sparse.eval nodeValue4677 (mixedVector B) := by
    change mixedMoment B node4677 node4677Labels = _
    exact sound4677 B hB hF
  have h4851 : mixedVector B (Sum.inr 4851) = Sparse.eval nodeValue4851 (mixedVector B) := by
    change mixedMoment B node4851 node4851Labels = _
    exact sound4851 B hB hF
  have h4956 : mixedVector B (Sum.inr 4956) = Sparse.eval nodeValue4956 (mixedVector B) := by
    change mixedMoment B node4956 node4956Labels = _
    exact sound4956 B hB hF
  have h4958 : mixedVector B (Sum.inr 4958) = Sparse.eval nodeValue4958 (mixedVector B) := by
    change mixedMoment B node4958 node4958Labels = _
    exact sound4958 B hB hF
  have h4964 : mixedVector B (Sum.inr 4964) = Sparse.eval nodeValue4964 (mixedVector B) := by
    change mixedMoment B node4964 node4964Labels = _
    exact sound4964 B hB hF
  have h5114 : mixedVector B (Sum.inr 5114) = Sparse.eval nodeValue5114 (mixedVector B) := by
    change mixedMoment B node5114 node5114Labels = _
    exact sound5114 B hB hF
  have h5129 : mixedVector B (Sum.inr 5129) = Sparse.eval nodeValue5129 (mixedVector B) := by
    change mixedMoment B node5129 node5129Labels = _
    exact sound5129 B hB hF
  have h5137 : mixedVector B (Sum.inr 5137) = Sparse.eval nodeValue5137 (mixedVector B) := by
    change mixedMoment B node5137 node5137Labels = _
    exact sound5137 B hB hF
  have h5373 : mixedVector B (Sum.inr 5373) = Sparse.eval nodeValue5373 (mixedVector B) := by
    change mixedMoment B node5373 node5373Labels = _
    exact sound5373 B hB hF
  have h5377 : mixedVector B (Sum.inr 5377) = Sparse.eval nodeValue5377 (mixedVector B) := by
    change mixedMoment B node5377 node5377Labels = _
    exact sound5377 B hB hF
  have h5379 : mixedVector B (Sum.inr 5379) = Sparse.eval nodeValue5379 (mixedVector B) := by
    change mixedMoment B node5379 node5379Labels = _
    exact sound5379 B hB hF
  have h5380 : mixedVector B (Sum.inr 5380) = Sparse.eval nodeValue5380 (mixedVector B) := by
    change mixedMoment B node5380 node5380Labels = _
    exact sound5380 B hB hF
  have h5383 : mixedVector B (Sum.inr 5383) = Sparse.eval nodeValue5383 (mixedVector B) := by
    change mixedMoment B node5383 node5383Labels = _
    exact sound5383 B hB hF
  have h5396 : mixedVector B (Sum.inr 5396) = Sparse.eval nodeValue5396 (mixedVector B) := by
    change mixedMoment B node5396 node5396Labels = _
    exact sound5396 B hB hF
  have h5422 : mixedVector B (Sum.inr 5422) = Sparse.eval nodeValue5422 (mixedVector B) := by
    change mixedMoment B node5422 node5422Labels = _
    exact sound5422 B hB hF
  have h5424 : mixedVector B (Sum.inr 5424) = Sparse.eval nodeValue5424 (mixedVector B) := by
    change mixedMoment B node5424 node5424Labels = _
    exact sound5424 B hB hF
  have h5427 : mixedVector B (Sum.inr 5427) = Sparse.eval nodeValue5427 (mixedVector B) := by
    change mixedMoment B node5427 node5427Labels = _
    exact sound5427 B hB hF
  have h5430 : mixedVector B (Sum.inr 5430) = Sparse.eval nodeValue5430 (mixedVector B) := by
    change mixedMoment B node5430 node5430Labels = _
    exact sound5430 B hB hF
  have h5447 : mixedVector B (Sum.inr 5447) = Sparse.eval nodeValue5447 (mixedVector B) := by
    change mixedMoment B node5447 node5447Labels = _
    exact sound5447 B hB hF
  simpa only [sourceForm2583, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4663, h4666, h4677, h4851, h4956, h4958, h4964, h5114, h5129, h5137, h5373, h5377, h5379, h5380, h5383, h5396, h5422, h5424, h5427, h5430, h5447, reducedSource2067] using sourceEq2583 B hB

theorem rowSound2067 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2067 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2067, numericCheck2067, reducedZero2067 B hB hF, mul_zero]

theorem reducedZero2068 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2068 (mixedVector B) = 0 := by
  have h2140 : mixedVector B (Sum.inr 2140) = Sparse.eval nodeValue2140 (mixedVector B) := by
    change mixedMoment B node2140 node2140Labels = _
    exact sound2140 B hB hF
  have h2142 : mixedVector B (Sum.inr 2142) = Sparse.eval nodeValue2142 (mixedVector B) := by
    change mixedMoment B node2142 node2142Labels = _
    exact sound2142 B hB hF
  have h2148 : mixedVector B (Sum.inr 2148) = Sparse.eval nodeValue2148 (mixedVector B) := by
    change mixedMoment B node2148 node2148Labels = _
    exact sound2148 B hB hF
  have h2240 : mixedVector B (Sum.inr 2240) = Sparse.eval nodeValue2240 (mixedVector B) := by
    change mixedMoment B node2240 node2240Labels = _
    exact sound2240 B hB hF
  have h3510 : mixedVector B (Sum.inr 3510) = Sparse.eval nodeValue3510 (mixedVector B) := by
    change mixedMoment B node3510 node3510Labels = _
    exact sound3510 B hB hF
  have h3511 : mixedVector B (Sum.inr 3511) = Sparse.eval nodeValue3511 (mixedVector B) := by
    change mixedMoment B node3511 node3511Labels = _
    exact sound3511 B hB hF
  have h3516 : mixedVector B (Sum.inr 3516) = Sparse.eval nodeValue3516 (mixedVector B) := by
    change mixedMoment B node3516 node3516Labels = _
    exact sound3516 B hB hF
  have h3521 : mixedVector B (Sum.inr 3521) = Sparse.eval nodeValue3521 (mixedVector B) := by
    change mixedMoment B node3521 node3521Labels = _
    exact sound3521 B hB hF
  have h3554 : mixedVector B (Sum.inr 3554) = Sparse.eval nodeValue3554 (mixedVector B) := by
    change mixedMoment B node3554 node3554Labels = _
    exact sound3554 B hB hF
  have h3597 : mixedVector B (Sum.inr 3597) = Sparse.eval nodeValue3597 (mixedVector B) := by
    change mixedMoment B node3597 node3597Labels = _
    exact sound3597 B hB hF
  have h3792 : mixedVector B (Sum.inr 3792) = Sparse.eval nodeValue3792 (mixedVector B) := by
    change mixedMoment B node3792 node3792Labels = _
    exact sound3792 B hB hF
  have h3798 : mixedVector B (Sum.inr 3798) = Sparse.eval nodeValue3798 (mixedVector B) := by
    change mixedMoment B node3798 node3798Labels = _
    exact sound3798 B hB hF
  have h3832 : mixedVector B (Sum.inr 3832) = Sparse.eval nodeValue3832 (mixedVector B) := by
    change mixedMoment B node3832 node3832Labels = _
    exact sound3832 B hB hF
  have h3835 : mixedVector B (Sum.inr 3835) = Sparse.eval nodeValue3835 (mixedVector B) := by
    change mixedMoment B node3835 node3835Labels = _
    exact sound3835 B hB hF
  have h3836 : mixedVector B (Sum.inr 3836) = Sparse.eval nodeValue3836 (mixedVector B) := by
    change mixedMoment B node3836 node3836Labels = _
    exact sound3836 B hB hF
  have h3843 : mixedVector B (Sum.inr 3843) = Sparse.eval nodeValue3843 (mixedVector B) := by
    change mixedMoment B node3843 node3843Labels = _
    exact sound3843 B hB hF
  have h3844 : mixedVector B (Sum.inr 3844) = Sparse.eval nodeValue3844 (mixedVector B) := by
    change mixedMoment B node3844 node3844Labels = _
    exact sound3844 B hB hF
  have h3848 : mixedVector B (Sum.inr 3848) = Sparse.eval nodeValue3848 (mixedVector B) := by
    change mixedMoment B node3848 node3848Labels = _
    exact sound3848 B hB hF
  have h3867 : mixedVector B (Sum.inr 3867) = Sparse.eval nodeValue3867 (mixedVector B) := by
    change mixedMoment B node3867 node3867Labels = _
    exact sound3867 B hB hF
  have h3900 : mixedVector B (Sum.inr 3900) = Sparse.eval nodeValue3900 (mixedVector B) := by
    change mixedMoment B node3900 node3900Labels = _
    exact sound3900 B hB hF
  have h3909 : mixedVector B (Sum.inr 3909) = Sparse.eval nodeValue3909 (mixedVector B) := by
    change mixedMoment B node3909 node3909Labels = _
    exact sound3909 B hB hF
  simpa only [sourceForm2584, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2140, h2142, h2148, h2240, h3510, h3511, h3516, h3521, h3554, h3597, h3792, h3798, h3832, h3835, h3836, h3843, h3844, h3848, h3867, h3900, h3909, reducedSource2068] using sourceEq2584 B hB

theorem rowSound2068 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2068 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2068, numericCheck2068, reducedZero2068 B hB hF, mul_zero]

theorem reducedZero2069 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2069 (mixedVector B) = 0 := by
  have h4664 : mixedVector B (Sum.inr 4664) = Sparse.eval nodeValue4664 (mixedVector B) := by
    change mixedMoment B node4664 node4664Labels = _
    exact sound4664 B hB hF
  have h4665 : mixedVector B (Sum.inr 4665) = Sparse.eval nodeValue4665 (mixedVector B) := by
    change mixedMoment B node4665 node4665Labels = _
    exact sound4665 B hB hF
  have h4668 : mixedVector B (Sum.inr 4668) = Sparse.eval nodeValue4668 (mixedVector B) := by
    change mixedMoment B node4668 node4668Labels = _
    exact sound4668 B hB hF
  have h4680 : mixedVector B (Sum.inr 4680) = Sparse.eval nodeValue4680 (mixedVector B) := by
    change mixedMoment B node4680 node4680Labels = _
    exact sound4680 B hB hF
  have h4852 : mixedVector B (Sum.inr 4852) = Sparse.eval nodeValue4852 (mixedVector B) := by
    change mixedMoment B node4852 node4852Labels = _
    exact sound4852 B hB hF
  have h4954 : mixedVector B (Sum.inr 4954) = Sparse.eval nodeValue4954 (mixedVector B) := by
    change mixedMoment B node4954 node4954Labels = _
    exact sound4954 B hB hF
  have h4955 : mixedVector B (Sum.inr 4955) = Sparse.eval nodeValue4955 (mixedVector B) := by
    change mixedMoment B node4955 node4955Labels = _
    exact sound4955 B hB hF
  have h4957 : mixedVector B (Sum.inr 4957) = Sparse.eval nodeValue4957 (mixedVector B) := by
    change mixedMoment B node4957 node4957Labels = _
    exact sound4957 B hB hF
  have h4963 : mixedVector B (Sum.inr 4963) = Sparse.eval nodeValue4963 (mixedVector B) := by
    change mixedMoment B node4963 node4963Labels = _
    exact sound4963 B hB hF
  have h5038 : mixedVector B (Sum.inr 5038) = Sparse.eval nodeValue5038 (mixedVector B) := by
    change mixedMoment B node5038 node5038Labels = _
    exact sound5038 B hB hF
  have h5080 : mixedVector B (Sum.inr 5080) = Sparse.eval nodeValue5080 (mixedVector B) := by
    change mixedMoment B node5080 node5080Labels = _
    exact sound5080 B hB hF
  have h5129 : mixedVector B (Sum.inr 5129) = Sparse.eval nodeValue5129 (mixedVector B) := by
    change mixedMoment B node5129 node5129Labels = _
    exact sound5129 B hB hF
  have h5134 : mixedVector B (Sum.inr 5134) = Sparse.eval nodeValue5134 (mixedVector B) := by
    change mixedMoment B node5134 node5134Labels = _
    exact sound5134 B hB hF
  have h5336 : mixedVector B (Sum.inr 5336) = Sparse.eval nodeValue5336 (mixedVector B) := by
    change mixedMoment B node5336 node5336Labels = _
    exact sound5336 B hB hF
  have h5355 : mixedVector B (Sum.inr 5355) = Sparse.eval nodeValue5355 (mixedVector B) := by
    change mixedMoment B node5355 node5355Labels = _
    exact sound5355 B hB hF
  have h5372 : mixedVector B (Sum.inr 5372) = Sparse.eval nodeValue5372 (mixedVector B) := by
    change mixedMoment B node5372 node5372Labels = _
    exact sound5372 B hB hF
  have h5376 : mixedVector B (Sum.inr 5376) = Sparse.eval nodeValue5376 (mixedVector B) := by
    change mixedMoment B node5376 node5376Labels = _
    exact sound5376 B hB hF
  have h5379 : mixedVector B (Sum.inr 5379) = Sparse.eval nodeValue5379 (mixedVector B) := by
    change mixedMoment B node5379 node5379Labels = _
    exact sound5379 B hB hF
  have h5381 : mixedVector B (Sum.inr 5381) = Sparse.eval nodeValue5381 (mixedVector B) := by
    change mixedMoment B node5381 node5381Labels = _
    exact sound5381 B hB hF
  have h5382 : mixedVector B (Sum.inr 5382) = Sparse.eval nodeValue5382 (mixedVector B) := by
    change mixedMoment B node5382 node5382Labels = _
    exact sound5382 B hB hF
  have h5384 : mixedVector B (Sum.inr 5384) = Sparse.eval nodeValue5384 (mixedVector B) := by
    change mixedMoment B node5384 node5384Labels = _
    exact sound5384 B hB hF
  have h5394 : mixedVector B (Sum.inr 5394) = Sparse.eval nodeValue5394 (mixedVector B) := by
    change mixedMoment B node5394 node5394Labels = _
    exact sound5394 B hB hF
  have h5397 : mixedVector B (Sum.inr 5397) = Sparse.eval nodeValue5397 (mixedVector B) := by
    change mixedMoment B node5397 node5397Labels = _
    exact sound5397 B hB hF
  have h5409 : mixedVector B (Sum.inr 5409) = Sparse.eval nodeValue5409 (mixedVector B) := by
    change mixedMoment B node5409 node5409Labels = _
    exact sound5409 B hB hF
  have h5411 : mixedVector B (Sum.inr 5411) = Sparse.eval nodeValue5411 (mixedVector B) := by
    change mixedMoment B node5411 node5411Labels = _
    exact sound5411 B hB hF
  have h5423 : mixedVector B (Sum.inr 5423) = Sparse.eval nodeValue5423 (mixedVector B) := by
    change mixedMoment B node5423 node5423Labels = _
    exact sound5423 B hB hF
  have h5424 : mixedVector B (Sum.inr 5424) = Sparse.eval nodeValue5424 (mixedVector B) := by
    change mixedMoment B node5424 node5424Labels = _
    exact sound5424 B hB hF
  have h5425 : mixedVector B (Sum.inr 5425) = Sparse.eval nodeValue5425 (mixedVector B) := by
    change mixedMoment B node5425 node5425Labels = _
    exact sound5425 B hB hF
  have h5445 : mixedVector B (Sum.inr 5445) = Sparse.eval nodeValue5445 (mixedVector B) := by
    change mixedMoment B node5445 node5445Labels = _
    exact sound5445 B hB hF
  simpa only [sourceForm2587, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4664, h4665, h4668, h4680, h4852, h4954, h4955, h4957, h4963, h5038, h5080, h5129, h5134, h5336, h5355, h5372, h5376, h5379, h5381, h5382, h5384, h5394, h5397, h5409, h5411, h5423, h5424, h5425, h5445, reducedSource2069] using sourceEq2587 B hB

theorem rowSound2069 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2069 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2069, numericCheck2069, reducedZero2069 B hB hF, mul_zero]

theorem reducedZero2070 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2070 (mixedVector B) = 0 := by
  have h2144 : mixedVector B (Sum.inr 2144) = Sparse.eval nodeValue2144 (mixedVector B) := by
    change mixedMoment B node2144 node2144Labels = _
    exact sound2144 B hB hF
  have h2145 : mixedVector B (Sum.inr 2145) = Sparse.eval nodeValue2145 (mixedVector B) := by
    change mixedMoment B node2145 node2145Labels = _
    exact sound2145 B hB hF
  have h2147 : mixedVector B (Sum.inr 2147) = Sparse.eval nodeValue2147 (mixedVector B) := by
    change mixedMoment B node2147 node2147Labels = _
    exact sound2147 B hB hF
  have h2154 : mixedVector B (Sum.inr 2154) = Sparse.eval nodeValue2154 (mixedVector B) := by
    change mixedMoment B node2154 node2154Labels = _
    exact sound2154 B hB hF
  have h2250 : mixedVector B (Sum.inr 2250) = Sparse.eval nodeValue2250 (mixedVector B) := by
    change mixedMoment B node2250 node2250Labels = _
    exact sound2250 B hB hF
  have h3452 : mixedVector B (Sum.inr 3452) = Sparse.eval nodeValue3452 (mixedVector B) := by
    change mixedMoment B node3452 node3452Labels = _
    exact sound3452 B hB hF
  have h3453 : mixedVector B (Sum.inr 3453) = Sparse.eval nodeValue3453 (mixedVector B) := by
    change mixedMoment B node3453 node3453Labels = _
    exact sound3453 B hB hF
  have h3478 : mixedVector B (Sum.inr 3478) = Sparse.eval nodeValue3478 (mixedVector B) := by
    change mixedMoment B node3478 node3478Labels = _
    exact sound3478 B hB hF
  have h3508 : mixedVector B (Sum.inr 3508) = Sparse.eval nodeValue3508 (mixedVector B) := by
    change mixedMoment B node3508 node3508Labels = _
    exact sound3508 B hB hF
  have h3509 : mixedVector B (Sum.inr 3509) = Sparse.eval nodeValue3509 (mixedVector B) := by
    change mixedMoment B node3509 node3509Labels = _
    exact sound3509 B hB hF
  have h3514 : mixedVector B (Sum.inr 3514) = Sparse.eval nodeValue3514 (mixedVector B) := by
    change mixedMoment B node3514 node3514Labels = _
    exact sound3514 B hB hF
  have h3516 : mixedVector B (Sum.inr 3516) = Sparse.eval nodeValue3516 (mixedVector B) := by
    change mixedMoment B node3516 node3516Labels = _
    exact sound3516 B hB hF
  have h3553 : mixedVector B (Sum.inr 3553) = Sparse.eval nodeValue3553 (mixedVector B) := by
    change mixedMoment B node3553 node3553Labels = _
    exact sound3553 B hB hF
  have h3754 : mixedVector B (Sum.inr 3754) = Sparse.eval nodeValue3754 (mixedVector B) := by
    change mixedMoment B node3754 node3754Labels = _
    exact sound3754 B hB hF
  have h3770 : mixedVector B (Sum.inr 3770) = Sparse.eval nodeValue3770 (mixedVector B) := by
    change mixedMoment B node3770 node3770Labels = _
    exact sound3770 B hB hF
  have h3791 : mixedVector B (Sum.inr 3791) = Sparse.eval nodeValue3791 (mixedVector B) := by
    change mixedMoment B node3791 node3791Labels = _
    exact sound3791 B hB hF
  have h3793 : mixedVector B (Sum.inr 3793) = Sparse.eval nodeValue3793 (mixedVector B) := by
    change mixedMoment B node3793 node3793Labels = _
    exact sound3793 B hB hF
  have h3796 : mixedVector B (Sum.inr 3796) = Sparse.eval nodeValue3796 (mixedVector B) := by
    change mixedMoment B node3796 node3796Labels = _
    exact sound3796 B hB hF
  have h3807 : mixedVector B (Sum.inr 3807) = Sparse.eval nodeValue3807 (mixedVector B) := by
    change mixedMoment B node3807 node3807Labels = _
    exact sound3807 B hB hF
  have h3811 : mixedVector B (Sum.inr 3811) = Sparse.eval nodeValue3811 (mixedVector B) := by
    change mixedMoment B node3811 node3811Labels = _
    exact sound3811 B hB hF
  have h3813 : mixedVector B (Sum.inr 3813) = Sparse.eval nodeValue3813 (mixedVector B) := by
    change mixedMoment B node3813 node3813Labels = _
    exact sound3813 B hB hF
  have h3832 : mixedVector B (Sum.inr 3832) = Sparse.eval nodeValue3832 (mixedVector B) := by
    change mixedMoment B node3832 node3832Labels = _
    exact sound3832 B hB hF
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
  have h3840 : mixedVector B (Sum.inr 3840) = Sparse.eval nodeValue3840 (mixedVector B) := by
    change mixedMoment B node3840 node3840Labels = _
    exact sound3840 B hB hF
  have h3866 : mixedVector B (Sum.inr 3866) = Sparse.eval nodeValue3866 (mixedVector B) := by
    change mixedMoment B node3866 node3866Labels = _
    exact sound3866 B hB hF
  have h3880 : mixedVector B (Sum.inr 3880) = Sparse.eval nodeValue3880 (mixedVector B) := by
    change mixedMoment B node3880 node3880Labels = _
    exact sound3880 B hB hF
  simpa only [sourceForm2588, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2144, h2145, h2147, h2154, h2250, h3452, h3453, h3478, h3508, h3509, h3514, h3516, h3553, h3754, h3770, h3791, h3793, h3796, h3807, h3811, h3813, h3832, h3833, h3834, h3837, h3838, h3840, h3866, h3880, reducedSource2070] using sourceEq2588 B hB

theorem rowSound2070 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2070 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2070, numericCheck2070, reducedZero2070 B hB hF, mul_zero]

theorem reducedZero2071 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2071 (mixedVector B) = 0 := by
  have h4679 : mixedVector B (Sum.inr 4679) = Sparse.eval nodeValue4679 (mixedVector B) := by
    change mixedMoment B node4679 node4679Labels = _
    exact sound4679 B hB hF
  have h4686 : mixedVector B (Sum.inr 4686) = Sparse.eval nodeValue4686 (mixedVector B) := by
    change mixedMoment B node4686 node4686Labels = _
    exact sound4686 B hB hF
  have h4689 : mixedVector B (Sum.inr 4689) = Sparse.eval nodeValue4689 (mixedVector B) := by
    change mixedMoment B node4689 node4689Labels = _
    exact sound4689 B hB hF
  have h4696 : mixedVector B (Sum.inr 4696) = Sparse.eval nodeValue4696 (mixedVector B) := by
    change mixedMoment B node4696 node4696Labels = _
    exact sound4696 B hB hF
  have h4697 : mixedVector B (Sum.inr 4697) = Sparse.eval nodeValue4697 (mixedVector B) := by
    change mixedMoment B node4697 node4697Labels = _
    exact sound4697 B hB hF
  have h4701 : mixedVector B (Sum.inr 4701) = Sparse.eval nodeValue4701 (mixedVector B) := by
    change mixedMoment B node4701 node4701Labels = _
    exact sound4701 B hB hF
  have h4838 : mixedVector B (Sum.inr 4838) = Sparse.eval nodeValue4838 (mixedVector B) := by
    change mixedMoment B node4838 node4838Labels = _
    exact sound4838 B hB hF
  have h4879 : mixedVector B (Sum.inr 4879) = Sparse.eval nodeValue4879 (mixedVector B) := by
    change mixedMoment B node4879 node4879Labels = _
    exact sound4879 B hB hF
  have h5116 : mixedVector B (Sum.inr 5116) = Sparse.eval nodeValue5116 (mixedVector B) := by
    change mixedMoment B node5116 node5116Labels = _
    exact sound5116 B hB hF
  have h5151 : mixedVector B (Sum.inr 5151) = Sparse.eval nodeValue5151 (mixedVector B) := by
    change mixedMoment B node5151 node5151Labels = _
    exact sound5151 B hB hF
  have h5217 : mixedVector B (Sum.inr 5217) = Sparse.eval nodeValue5217 (mixedVector B) := by
    change mixedMoment B node5217 node5217Labels = _
    exact sound5217 B hB hF
  have h5226 : mixedVector B (Sum.inr 5226) = Sparse.eval nodeValue5226 (mixedVector B) := by
    change mixedMoment B node5226 node5226Labels = _
    exact sound5226 B hB hF
  have h5227 : mixedVector B (Sum.inr 5227) = Sparse.eval nodeValue5227 (mixedVector B) := by
    change mixedMoment B node5227 node5227Labels = _
    exact sound5227 B hB hF
  have h5236 : mixedVector B (Sum.inr 5236) = Sparse.eval nodeValue5236 (mixedVector B) := by
    change mixedMoment B node5236 node5236Labels = _
    exact sound5236 B hB hF
  have h5237 : mixedVector B (Sum.inr 5237) = Sparse.eval nodeValue5237 (mixedVector B) := by
    change mixedMoment B node5237 node5237Labels = _
    exact sound5237 B hB hF
  have h5247 : mixedVector B (Sum.inr 5247) = Sparse.eval nodeValue5247 (mixedVector B) := by
    change mixedMoment B node5247 node5247Labels = _
    exact sound5247 B hB hF
  have h5271 : mixedVector B (Sum.inr 5271) = Sparse.eval nodeValue5271 (mixedVector B) := by
    change mixedMoment B node5271 node5271Labels = _
    exact sound5271 B hB hF
  have h5273 : mixedVector B (Sum.inr 5273) = Sparse.eval nodeValue5273 (mixedVector B) := by
    change mixedMoment B node5273 node5273Labels = _
    exact sound5273 B hB hF
  have h5286 : mixedVector B (Sum.inr 5286) = Sparse.eval nodeValue5286 (mixedVector B) := by
    change mixedMoment B node5286 node5286Labels = _
    exact sound5286 B hB hF
  have h5299 : mixedVector B (Sum.inr 5299) = Sparse.eval nodeValue5299 (mixedVector B) := by
    change mixedMoment B node5299 node5299Labels = _
    exact sound5299 B hB hF
  have h5301 : mixedVector B (Sum.inr 5301) = Sparse.eval nodeValue5301 (mixedVector B) := by
    change mixedMoment B node5301 node5301Labels = _
    exact sound5301 B hB hF
  simpa only [sourceForm2591, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4679, h4686, h4689, h4696, h4697, h4701, h4838, h4879, h5116, h5151, h5217, h5226, h5227, h5236, h5237, h5247, h5271, h5273, h5286, h5299, h5301, reducedSource2071] using sourceEq2591 B hB

theorem rowSound2071 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2071 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2071, numericCheck2071, reducedZero2071 B hB hF, mul_zero]

theorem reducedZero2072 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2072 (mixedVector B) = 0 := by
  have h2150 : mixedVector B (Sum.inr 2150) = Sparse.eval nodeValue2150 (mixedVector B) := by
    change mixedMoment B node2150 node2150Labels = _
    exact sound2150 B hB hF
  have h2165 : mixedVector B (Sum.inr 2165) = Sparse.eval nodeValue2165 (mixedVector B) := by
    change mixedMoment B node2165 node2165Labels = _
    exact sound2165 B hB hF
  have h2166 : mixedVector B (Sum.inr 2166) = Sparse.eval nodeValue2166 (mixedVector B) := by
    change mixedMoment B node2166 node2166Labels = _
    exact sound2166 B hB hF
  have h2227 : mixedVector B (Sum.inr 2227) = Sparse.eval nodeValue2227 (mixedVector B) := by
    change mixedMoment B node2227 node2227Labels = _
    exact sound2227 B hB hF
  have h2238 : mixedVector B (Sum.inr 2238) = Sparse.eval nodeValue2238 (mixedVector B) := by
    change mixedMoment B node2238 node2238Labels = _
    exact sound2238 B hB hF
  have h2239 : mixedVector B (Sum.inr 2239) = Sparse.eval nodeValue2239 (mixedVector B) := by
    change mixedMoment B node2239 node2239Labels = _
    exact sound2239 B hB hF
  have h2246 : mixedVector B (Sum.inr 2246) = Sparse.eval nodeValue2246 (mixedVector B) := by
    change mixedMoment B node2246 node2246Labels = _
    exact sound2246 B hB hF
  have h2257 : mixedVector B (Sum.inr 2257) = Sparse.eval nodeValue2257 (mixedVector B) := by
    change mixedMoment B node2257 node2257Labels = _
    exact sound2257 B hB hF
  have h2655 : mixedVector B (Sum.inr 2655) = Sparse.eval nodeValue2655 (mixedVector B) := by
    change mixedMoment B node2655 node2655Labels = _
    exact sound2655 B hB hF
  have h2656 : mixedVector B (Sum.inr 2656) = Sparse.eval nodeValue2656 (mixedVector B) := by
    change mixedMoment B node2656 node2656Labels = _
    exact sound2656 B hB hF
  have h2669 : mixedVector B (Sum.inr 2669) = Sparse.eval nodeValue2669 (mixedVector B) := by
    change mixedMoment B node2669 node2669Labels = _
    exact sound2669 B hB hF
  have h2671 : mixedVector B (Sum.inr 2671) = Sparse.eval nodeValue2671 (mixedVector B) := by
    change mixedMoment B node2671 node2671Labels = _
    exact sound2671 B hB hF
  have h2681 : mixedVector B (Sum.inr 2681) = Sparse.eval nodeValue2681 (mixedVector B) := by
    change mixedMoment B node2681 node2681Labels = _
    exact sound2681 B hB hF
  have h2682 : mixedVector B (Sum.inr 2682) = Sparse.eval nodeValue2682 (mixedVector B) := by
    change mixedMoment B node2682 node2682Labels = _
    exact sound2682 B hB hF
  have h2684 : mixedVector B (Sum.inr 2684) = Sparse.eval nodeValue2684 (mixedVector B) := by
    change mixedMoment B node2684 node2684Labels = _
    exact sound2684 B hB hF
  have h2703 : mixedVector B (Sum.inr 2703) = Sparse.eval nodeValue2703 (mixedVector B) := by
    change mixedMoment B node2703 node2703Labels = _
    exact sound2703 B hB hF
  have h2739 : mixedVector B (Sum.inr 2739) = Sparse.eval nodeValue2739 (mixedVector B) := by
    change mixedMoment B node2739 node2739Labels = _
    exact sound2739 B hB hF
  have h2741 : mixedVector B (Sum.inr 2741) = Sparse.eval nodeValue2741 (mixedVector B) := by
    change mixedMoment B node2741 node2741Labels = _
    exact sound2741 B hB hF
  have h3023 : mixedVector B (Sum.inr 3023) = Sparse.eval nodeValue3023 (mixedVector B) := by
    change mixedMoment B node3023 node3023Labels = _
    exact sound3023 B hB hF
  have h3051 : mixedVector B (Sum.inr 3051) = Sparse.eval nodeValue3051 (mixedVector B) := by
    change mixedMoment B node3051 node3051Labels = _
    exact sound3051 B hB hF
  have h3053 : mixedVector B (Sum.inr 3053) = Sparse.eval nodeValue3053 (mixedVector B) := by
    change mixedMoment B node3053 node3053Labels = _
    exact sound3053 B hB hF
  simpa only [sourceForm2592, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2150, h2165, h2166, h2227, h2238, h2239, h2246, h2257, h2655, h2656, h2669, h2671, h2681, h2682, h2684, h2703, h2739, h2741, h3023, h3051, h3053, reducedSource2072] using sourceEq2592 B hB

theorem rowSound2072 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2072 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2072, numericCheck2072, reducedZero2072 B hB hF, mul_zero]

theorem reducedZero2073 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2073 (mixedVector B) = 0 := by
  have h4676 : mixedVector B (Sum.inr 4676) = Sparse.eval nodeValue4676 (mixedVector B) := by
    change mixedMoment B node4676 node4676Labels = _
    exact sound4676 B hB hF
  have h4681 : mixedVector B (Sum.inr 4681) = Sparse.eval nodeValue4681 (mixedVector B) := by
    change mixedMoment B node4681 node4681Labels = _
    exact sound4681 B hB hF
  have h4684 : mixedVector B (Sum.inr 4684) = Sparse.eval nodeValue4684 (mixedVector B) := by
    change mixedMoment B node4684 node4684Labels = _
    exact sound4684 B hB hF
  have h4688 : mixedVector B (Sum.inr 4688) = Sparse.eval nodeValue4688 (mixedVector B) := by
    change mixedMoment B node4688 node4688Labels = _
    exact sound4688 B hB hF
  have h4698 : mixedVector B (Sum.inr 4698) = Sparse.eval nodeValue4698 (mixedVector B) := by
    change mixedMoment B node4698 node4698Labels = _
    exact sound4698 B hB hF
  have h4699 : mixedVector B (Sum.inr 4699) = Sparse.eval nodeValue4699 (mixedVector B) := by
    change mixedMoment B node4699 node4699Labels = _
    exact sound4699 B hB hF
  have h4700 : mixedVector B (Sum.inr 4700) = Sparse.eval nodeValue4700 (mixedVector B) := by
    change mixedMoment B node4700 node4700Labels = _
    exact sound4700 B hB hF
  have h4703 : mixedVector B (Sum.inr 4703) = Sparse.eval nodeValue4703 (mixedVector B) := by
    change mixedMoment B node4703 node4703Labels = _
    exact sound4703 B hB hF
  have h4834 : mixedVector B (Sum.inr 4834) = Sparse.eval nodeValue4834 (mixedVector B) := by
    change mixedMoment B node4834 node4834Labels = _
    exact sound4834 B hB hF
  have h4880 : mixedVector B (Sum.inr 4880) = Sparse.eval nodeValue4880 (mixedVector B) := by
    change mixedMoment B node4880 node4880Labels = _
    exact sound4880 B hB hF
  have h5035 : mixedVector B (Sum.inr 5035) = Sparse.eval nodeValue5035 (mixedVector B) := by
    change mixedMoment B node5035 node5035Labels = _
    exact sound5035 B hB hF
  have h5110 : mixedVector B (Sum.inr 5110) = Sparse.eval nodeValue5110 (mixedVector B) := by
    change mixedMoment B node5110 node5110Labels = _
    exact sound5110 B hB hF
  have h5140 : mixedVector B (Sum.inr 5140) = Sparse.eval nodeValue5140 (mixedVector B) := by
    change mixedMoment B node5140 node5140Labels = _
    exact sound5140 B hB hF
  have h5215 : mixedVector B (Sum.inr 5215) = Sparse.eval nodeValue5215 (mixedVector B) := by
    change mixedMoment B node5215 node5215Labels = _
    exact sound5215 B hB hF
  have h5216 : mixedVector B (Sum.inr 5216) = Sparse.eval nodeValue5216 (mixedVector B) := by
    change mixedMoment B node5216 node5216Labels = _
    exact sound5216 B hB hF
  have h5219 : mixedVector B (Sum.inr 5219) = Sparse.eval nodeValue5219 (mixedVector B) := by
    change mixedMoment B node5219 node5219Labels = _
    exact sound5219 B hB hF
  have h5220 : mixedVector B (Sum.inr 5220) = Sparse.eval nodeValue5220 (mixedVector B) := by
    change mixedMoment B node5220 node5220Labels = _
    exact sound5220 B hB hF
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
  have h5238 : mixedVector B (Sum.inr 5238) = Sparse.eval nodeValue5238 (mixedVector B) := by
    change mixedMoment B node5238 node5238Labels = _
    exact sound5238 B hB hF
  have h5241 : mixedVector B (Sum.inr 5241) = Sparse.eval nodeValue5241 (mixedVector B) := by
    change mixedMoment B node5241 node5241Labels = _
    exact sound5241 B hB hF
  have h5254 : mixedVector B (Sum.inr 5254) = Sparse.eval nodeValue5254 (mixedVector B) := by
    change mixedMoment B node5254 node5254Labels = _
    exact sound5254 B hB hF
  have h5258 : mixedVector B (Sum.inr 5258) = Sparse.eval nodeValue5258 (mixedVector B) := by
    change mixedMoment B node5258 node5258Labels = _
    exact sound5258 B hB hF
  have h5259 : mixedVector B (Sum.inr 5259) = Sparse.eval nodeValue5259 (mixedVector B) := by
    change mixedMoment B node5259 node5259Labels = _
    exact sound5259 B hB hF
  have h5266 : mixedVector B (Sum.inr 5266) = Sparse.eval nodeValue5266 (mixedVector B) := by
    change mixedMoment B node5266 node5266Labels = _
    exact sound5266 B hB hF
  have h5267 : mixedVector B (Sum.inr 5267) = Sparse.eval nodeValue5267 (mixedVector B) := by
    change mixedMoment B node5267 node5267Labels = _
    exact sound5267 B hB hF
  have h5274 : mixedVector B (Sum.inr 5274) = Sparse.eval nodeValue5274 (mixedVector B) := by
    change mixedMoment B node5274 node5274Labels = _
    exact sound5274 B hB hF
  have h5302 : mixedVector B (Sum.inr 5302) = Sparse.eval nodeValue5302 (mixedVector B) := by
    change mixedMoment B node5302 node5302Labels = _
    exact sound5302 B hB hF
  simpa only [sourceForm2595, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4676, h4681, h4684, h4688, h4698, h4699, h4700, h4703, h4834, h4880, h5035, h5110, h5140, h5215, h5216, h5219, h5220, h5228, h5229, h5232, h5233, h5238, h5241, h5254, h5258, h5259, h5266, h5267, h5274, h5302, reducedSource2073] using sourceEq2595 B hB

theorem rowSound2073 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2073 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2073, numericCheck2073, reducedZero2073 B hB hF, mul_zero]

theorem reducedZero2074 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2074 (mixedVector B) = 0 := by
  have h2141 : mixedVector B (Sum.inr 2141) = Sparse.eval nodeValue2141 (mixedVector B) := by
    change mixedMoment B node2141 node2141Labels = _
    exact sound2141 B hB hF
  have h2151 : mixedVector B (Sum.inr 2151) = Sparse.eval nodeValue2151 (mixedVector B) := by
    change mixedMoment B node2151 node2151Labels = _
    exact sound2151 B hB hF
  have h2152 : mixedVector B (Sum.inr 2152) = Sparse.eval nodeValue2152 (mixedVector B) := by
    change mixedMoment B node2152 node2152Labels = _
    exact sound2152 B hB hF
  have h2157 : mixedVector B (Sum.inr 2157) = Sparse.eval nodeValue2157 (mixedVector B) := by
    change mixedMoment B node2157 node2157Labels = _
    exact sound2157 B hB hF
  have h2205 : mixedVector B (Sum.inr 2205) = Sparse.eval nodeValue2205 (mixedVector B) := by
    change mixedMoment B node2205 node2205Labels = _
    exact sound2205 B hB hF
  have h2248 : mixedVector B (Sum.inr 2248) = Sparse.eval nodeValue2248 (mixedVector B) := by
    change mixedMoment B node2248 node2248Labels = _
    exact sound2248 B hB hF
  have h2249 : mixedVector B (Sum.inr 2249) = Sparse.eval nodeValue2249 (mixedVector B) := by
    change mixedMoment B node2249 node2249Labels = _
    exact sound2249 B hB hF
  have h2254 : mixedVector B (Sum.inr 2254) = Sparse.eval nodeValue2254 (mixedVector B) := by
    change mixedMoment B node2254 node2254Labels = _
    exact sound2254 B hB hF
  have h2256 : mixedVector B (Sum.inr 2256) = Sparse.eval nodeValue2256 (mixedVector B) := by
    change mixedMoment B node2256 node2256Labels = _
    exact sound2256 B hB hF
  have h2272 : mixedVector B (Sum.inr 2272) = Sparse.eval nodeValue2272 (mixedVector B) := by
    change mixedMoment B node2272 node2272Labels = _
    exact sound2272 B hB hF
  have h2652 : mixedVector B (Sum.inr 2652) = Sparse.eval nodeValue2652 (mixedVector B) := by
    change mixedMoment B node2652 node2652Labels = _
    exact sound2652 B hB hF
  have h2653 : mixedVector B (Sum.inr 2653) = Sparse.eval nodeValue2653 (mixedVector B) := by
    change mixedMoment B node2653 node2653Labels = _
    exact sound2653 B hB hF
  have h2654 : mixedVector B (Sum.inr 2654) = Sparse.eval nodeValue2654 (mixedVector B) := by
    change mixedMoment B node2654 node2654Labels = _
    exact sound2654 B hB hF
  have h2661 : mixedVector B (Sum.inr 2661) = Sparse.eval nodeValue2661 (mixedVector B) := by
    change mixedMoment B node2661 node2661Labels = _
    exact sound2661 B hB hF
  have h2662 : mixedVector B (Sum.inr 2662) = Sparse.eval nodeValue2662 (mixedVector B) := by
    change mixedMoment B node2662 node2662Labels = _
    exact sound2662 B hB hF
  have h2670 : mixedVector B (Sum.inr 2670) = Sparse.eval nodeValue2670 (mixedVector B) := by
    change mixedMoment B node2670 node2670Labels = _
    exact sound2670 B hB hF
  have h2672 : mixedVector B (Sum.inr 2672) = Sparse.eval nodeValue2672 (mixedVector B) := by
    change mixedMoment B node2672 node2672Labels = _
    exact sound2672 B hB hF
  have h2673 : mixedVector B (Sum.inr 2673) = Sparse.eval nodeValue2673 (mixedVector B) := by
    change mixedMoment B node2673 node2673Labels = _
    exact sound2673 B hB hF
  have h2677 : mixedVector B (Sum.inr 2677) = Sparse.eval nodeValue2677 (mixedVector B) := by
    change mixedMoment B node2677 node2677Labels = _
    exact sound2677 B hB hF
  have h2678 : mixedVector B (Sum.inr 2678) = Sparse.eval nodeValue2678 (mixedVector B) := by
    change mixedMoment B node2678 node2678Labels = _
    exact sound2678 B hB hF
  have h2685 : mixedVector B (Sum.inr 2685) = Sparse.eval nodeValue2685 (mixedVector B) := by
    change mixedMoment B node2685 node2685Labels = _
    exact sound2685 B hB hF
  have h2686 : mixedVector B (Sum.inr 2686) = Sparse.eval nodeValue2686 (mixedVector B) := by
    change mixedMoment B node2686 node2686Labels = _
    exact sound2686 B hB hF
  have h2694 : mixedVector B (Sum.inr 2694) = Sparse.eval nodeValue2694 (mixedVector B) := by
    change mixedMoment B node2694 node2694Labels = _
    exact sound2694 B hB hF
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  have h2723 : mixedVector B (Sum.inr 2723) = Sparse.eval nodeValue2723 (mixedVector B) := by
    change mixedMoment B node2723 node2723Labels = _
    exact sound2723 B hB hF
  have h2742 : mixedVector B (Sum.inr 2742) = Sparse.eval nodeValue2742 (mixedVector B) := by
    change mixedMoment B node2742 node2742Labels = _
    exact sound2742 B hB hF
  have h3016 : mixedVector B (Sum.inr 3016) = Sparse.eval nodeValue3016 (mixedVector B) := by
    change mixedMoment B node3016 node3016Labels = _
    exact sound3016 B hB hF
  have h3038 : mixedVector B (Sum.inr 3038) = Sparse.eval nodeValue3038 (mixedVector B) := by
    change mixedMoment B node3038 node3038Labels = _
    exact sound3038 B hB hF
  have h3039 : mixedVector B (Sum.inr 3039) = Sparse.eval nodeValue3039 (mixedVector B) := by
    change mixedMoment B node3039 node3039Labels = _
    exact sound3039 B hB hF
  have h3054 : mixedVector B (Sum.inr 3054) = Sparse.eval nodeValue3054 (mixedVector B) := by
    change mixedMoment B node3054 node3054Labels = _
    exact sound3054 B hB hF
  simpa only [sourceForm2596, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2141, h2151, h2152, h2157, h2205, h2248, h2249, h2254, h2256, h2272, h2652, h2653, h2654, h2661, h2662, h2670, h2672, h2673, h2677, h2678, h2685, h2686, h2694, h2722, h2723, h2742, h3016, h3038, h3039, h3054, reducedSource2074] using sourceEq2596 B hB

theorem rowSound2074 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2074 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2074, numericCheck2074, reducedZero2074 B hB hF, mul_zero]

theorem reducedZero2075 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2075 (mixedVector B) = 0 := by
  have h4947 : mixedVector B (Sum.inr 4947) = Sparse.eval nodeValue4947 (mixedVector B) := by
    change mixedMoment B node4947 node4947Labels = _
    exact sound4947 B hB hF
  have h4948 : mixedVector B (Sum.inr 4948) = Sparse.eval nodeValue4948 (mixedVector B) := by
    change mixedMoment B node4948 node4948Labels = _
    exact sound4948 B hB hF
  have h4949 : mixedVector B (Sum.inr 4949) = Sparse.eval nodeValue4949 (mixedVector B) := by
    change mixedMoment B node4949 node4949Labels = _
    exact sound4949 B hB hF
  have h5115 : mixedVector B (Sum.inr 5115) = Sparse.eval nodeValue5115 (mixedVector B) := by
    change mixedMoment B node5115 node5115Labels = _
    exact sound5115 B hB hF
  have h5172 : mixedVector B (Sum.inr 5172) = Sparse.eval nodeValue5172 (mixedVector B) := by
    change mixedMoment B node5172 node5172Labels = _
    exact sound5172 B hB hF
  have h5177 : mixedVector B (Sum.inr 5177) = Sparse.eval nodeValue5177 (mixedVector B) := by
    change mixedMoment B node5177 node5177Labels = _
    exact sound5177 B hB hF
  have h5373 : mixedVector B (Sum.inr 5373) = Sparse.eval nodeValue5373 (mixedVector B) := by
    change mixedMoment B node5373 node5373Labels = _
    exact sound5373 B hB hF
  have h5390 : mixedVector B (Sum.inr 5390) = Sparse.eval nodeValue5390 (mixedVector B) := by
    change mixedMoment B node5390 node5390Labels = _
    exact sound5390 B hB hF
  have h5404 : mixedVector B (Sum.inr 5404) = Sparse.eval nodeValue5404 (mixedVector B) := by
    change mixedMoment B node5404 node5404Labels = _
    exact sound5404 B hB hF
  have h5416 : mixedVector B (Sum.inr 5416) = Sparse.eval nodeValue5416 (mixedVector B) := by
    change mixedMoment B node5416 node5416Labels = _
    exact sound5416 B hB hF
  have h5418 : mixedVector B (Sum.inr 5418) = Sparse.eval nodeValue5418 (mixedVector B) := by
    change mixedMoment B node5418 node5418Labels = _
    exact sound5418 B hB hF
  have h5442 : mixedVector B (Sum.inr 5442) = Sparse.eval nodeValue5442 (mixedVector B) := by
    change mixedMoment B node5442 node5442Labels = _
    exact sound5442 B hB hF
  have h5462 : mixedVector B (Sum.inr 5462) = Sparse.eval nodeValue5462 (mixedVector B) := by
    change mixedMoment B node5462 node5462Labels = _
    exact sound5462 B hB hF
  have h5485 : mixedVector B (Sum.inr 5485) = Sparse.eval nodeValue5485 (mixedVector B) := by
    change mixedMoment B node5485 node5485Labels = _
    exact sound5485 B hB hF
  simpa only [sourceForm2597, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4947, h4948, h4949, h5115, h5172, h5177, h5373, h5390, h5404, h5416, h5418, h5442, h5462, h5485, reducedSource2075] using sourceEq2597 B hB

theorem rowSound2075 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2075 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2075, numericCheck2075, reducedZero2075 B hB hF, mul_zero]

theorem reducedZero2076 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2076 (mixedVector B) = 0 := by
  have h4767 : mixedVector B (Sum.inr 4767) = Sparse.eval nodeValue4767 (mixedVector B) := by
    change mixedMoment B node4767 node4767Labels = _
    exact sound4767 B hB hF
  have h4769 : mixedVector B (Sum.inr 4769) = Sparse.eval nodeValue4769 (mixedVector B) := by
    change mixedMoment B node4769 node4769Labels = _
    exact sound4769 B hB hF
  have h4811 : mixedVector B (Sum.inr 4811) = Sparse.eval nodeValue4811 (mixedVector B) := by
    change mixedMoment B node4811 node4811Labels = _
    exact sound4811 B hB hF
  have h4939 : mixedVector B (Sum.inr 4939) = Sparse.eval nodeValue4939 (mixedVector B) := by
    change mixedMoment B node4939 node4939Labels = _
    exact sound4939 B hB hF
  have h4946 : mixedVector B (Sum.inr 4946) = Sparse.eval nodeValue4946 (mixedVector B) := by
    change mixedMoment B node4946 node4946Labels = _
    exact sound4946 B hB hF
  have h5168 : mixedVector B (Sum.inr 5168) = Sparse.eval nodeValue5168 (mixedVector B) := by
    change mixedMoment B node5168 node5168Labels = _
    exact sound5168 B hB hF
  have h5337 : mixedVector B (Sum.inr 5337) = Sparse.eval nodeValue5337 (mixedVector B) := by
    change mixedMoment B node5337 node5337Labels = _
    exact sound5337 B hB hF
  have h5356 : mixedVector B (Sum.inr 5356) = Sparse.eval nodeValue5356 (mixedVector B) := by
    change mixedMoment B node5356 node5356Labels = _
    exact sound5356 B hB hF
  have h5393 : mixedVector B (Sum.inr 5393) = Sparse.eval nodeValue5393 (mixedVector B) := by
    change mixedMoment B node5393 node5393Labels = _
    exact sound5393 B hB hF
  have h5416 : mixedVector B (Sum.inr 5416) = Sparse.eval nodeValue5416 (mixedVector B) := by
    change mixedMoment B node5416 node5416Labels = _
    exact sound5416 B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434 B hB hF
  have h5464 : mixedVector B (Sum.inr 5464) = Sparse.eval nodeValue5464 (mixedVector B) := by
    change mixedMoment B node5464 node5464Labels = _
    exact sound5464 B hB hF
  have h5465 : mixedVector B (Sum.inr 5465) = Sparse.eval nodeValue5465 (mixedVector B) := by
    change mixedMoment B node5465 node5465Labels = _
    exact sound5465 B hB hF
  have h5486 : mixedVector B (Sum.inr 5486) = Sparse.eval nodeValue5486 (mixedVector B) := by
    change mixedMoment B node5486 node5486Labels = _
    exact sound5486 B hB hF
  simpa only [sourceForm2598, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4767, h4769, h4811, h4939, h4946, h5168, h5337, h5356, h5393, h5416, h5434, h5464, h5465, h5486, reducedSource2076] using sourceEq2598 B hB

theorem rowSound2076 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2076 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2076, numericCheck2076, reducedZero2076 B hB hF, mul_zero]

theorem reducedZero2077 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2077 (mixedVector B) = 0 := by
  have h4941 : mixedVector B (Sum.inr 4941) = Sparse.eval nodeValue4941 (mixedVector B) := by
    change mixedMoment B node4941 node4941Labels = _
    exact sound4941 B hB hF
  have h4943 : mixedVector B (Sum.inr 4943) = Sparse.eval nodeValue4943 (mixedVector B) := by
    change mixedMoment B node4943 node4943Labels = _
    exact sound4943 B hB hF
  have h4946 : mixedVector B (Sum.inr 4946) = Sparse.eval nodeValue4946 (mixedVector B) := by
    change mixedMoment B node4946 node4946Labels = _
    exact sound4946 B hB hF
  have h4950 : mixedVector B (Sum.inr 4950) = Sparse.eval nodeValue4950 (mixedVector B) := by
    change mixedMoment B node4950 node4950Labels = _
    exact sound4950 B hB hF
  have h5039 : mixedVector B (Sum.inr 5039) = Sparse.eval nodeValue5039 (mixedVector B) := by
    change mixedMoment B node5039 node5039Labels = _
    exact sound5039 B hB hF
  have h5081 : mixedVector B (Sum.inr 5081) = Sparse.eval nodeValue5081 (mixedVector B) := by
    change mixedMoment B node5081 node5081Labels = _
    exact sound5081 B hB hF
  have h5169 : mixedVector B (Sum.inr 5169) = Sparse.eval nodeValue5169 (mixedVector B) := by
    change mixedMoment B node5169 node5169Labels = _
    exact sound5169 B hB hF
  have h5177 : mixedVector B (Sum.inr 5177) = Sparse.eval nodeValue5177 (mixedVector B) := by
    change mixedMoment B node5177 node5177Labels = _
    exact sound5177 B hB hF
  have h5337 : mixedVector B (Sum.inr 5337) = Sparse.eval nodeValue5337 (mixedVector B) := by
    change mixedMoment B node5337 node5337Labels = _
    exact sound5337 B hB hF
  have h5356 : mixedVector B (Sum.inr 5356) = Sparse.eval nodeValue5356 (mixedVector B) := by
    change mixedMoment B node5356 node5356Labels = _
    exact sound5356 B hB hF
  have h5418 : mixedVector B (Sum.inr 5418) = Sparse.eval nodeValue5418 (mixedVector B) := by
    change mixedMoment B node5418 node5418Labels = _
    exact sound5418 B hB hF
  have h5457 : mixedVector B (Sum.inr 5457) = Sparse.eval nodeValue5457 (mixedVector B) := by
    change mixedMoment B node5457 node5457Labels = _
    exact sound5457 B hB hF
  have h5460 : mixedVector B (Sum.inr 5460) = Sparse.eval nodeValue5460 (mixedVector B) := by
    change mixedMoment B node5460 node5460Labels = _
    exact sound5460 B hB hF
  have h5464 : mixedVector B (Sum.inr 5464) = Sparse.eval nodeValue5464 (mixedVector B) := by
    change mixedMoment B node5464 node5464Labels = _
    exact sound5464 B hB hF
  have h5465 : mixedVector B (Sum.inr 5465) = Sparse.eval nodeValue5465 (mixedVector B) := by
    change mixedMoment B node5465 node5465Labels = _
    exact sound5465 B hB hF
  have h5466 : mixedVector B (Sum.inr 5466) = Sparse.eval nodeValue5466 (mixedVector B) := by
    change mixedMoment B node5466 node5466Labels = _
    exact sound5466 B hB hF
  have h5476 : mixedVector B (Sum.inr 5476) = Sparse.eval nodeValue5476 (mixedVector B) := by
    change mixedMoment B node5476 node5476Labels = _
    exact sound5476 B hB hF
  have h5483 : mixedVector B (Sum.inr 5483) = Sparse.eval nodeValue5483 (mixedVector B) := by
    change mixedMoment B node5483 node5483Labels = _
    exact sound5483 B hB hF
  have h5486 : mixedVector B (Sum.inr 5486) = Sparse.eval nodeValue5486 (mixedVector B) := by
    change mixedMoment B node5486 node5486Labels = _
    exact sound5486 B hB hF
  have h5487 : mixedVector B (Sum.inr 5487) = Sparse.eval nodeValue5487 (mixedVector B) := by
    change mixedMoment B node5487 node5487Labels = _
    exact sound5487 B hB hF
  simpa only [sourceForm2599, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4941, h4943, h4946, h4950, h5039, h5081, h5169, h5177, h5337, h5356, h5418, h5457, h5460, h5464, h5465, h5466, h5476, h5483, h5486, h5487, reducedSource2077] using sourceEq2599 B hB

theorem rowSound2077 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2077 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2077, numericCheck2077, reducedZero2077 B hB hF, mul_zero]

theorem reducedZero2078 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2078 (mixedVector B) = 0 := by
  have h4942 : mixedVector B (Sum.inr 4942) = Sparse.eval nodeValue4942 (mixedVector B) := by
    change mixedMoment B node4942 node4942Labels = _
    exact sound4942 B hB hF
  have h4944 : mixedVector B (Sum.inr 4944) = Sparse.eval nodeValue4944 (mixedVector B) := by
    change mixedMoment B node4944 node4944Labels = _
    exact sound4944 B hB hF
  have h4945 : mixedVector B (Sum.inr 4945) = Sparse.eval nodeValue4945 (mixedVector B) := by
    change mixedMoment B node4945 node4945Labels = _
    exact sound4945 B hB hF
  have h4951 : mixedVector B (Sum.inr 4951) = Sparse.eval nodeValue4951 (mixedVector B) := by
    change mixedMoment B node4951 node4951Labels = _
    exact sound4951 B hB hF
  have h5043 : mixedVector B (Sum.inr 5043) = Sparse.eval nodeValue5043 (mixedVector B) := by
    change mixedMoment B node5043 node5043Labels = _
    exact sound5043 B hB hF
  have h5081 : mixedVector B (Sum.inr 5081) = Sparse.eval nodeValue5081 (mixedVector B) := by
    change mixedMoment B node5081 node5081Labels = _
    exact sound5081 B hB hF
  have h5170 : mixedVector B (Sum.inr 5170) = Sparse.eval nodeValue5170 (mixedVector B) := by
    change mixedMoment B node5170 node5170Labels = _
    exact sound5170 B hB hF
  have h5189 : mixedVector B (Sum.inr 5189) = Sparse.eval nodeValue5189 (mixedVector B) := by
    change mixedMoment B node5189 node5189Labels = _
    exact sound5189 B hB hF
  have h5217 : mixedVector B (Sum.inr 5217) = Sparse.eval nodeValue5217 (mixedVector B) := by
    change mixedMoment B node5217 node5217Labels = _
    exact sound5217 B hB hF
  have h5236 : mixedVector B (Sum.inr 5236) = Sparse.eval nodeValue5236 (mixedVector B) := by
    change mixedMoment B node5236 node5236Labels = _
    exact sound5236 B hB hF
  have h5269 : mixedVector B (Sum.inr 5269) = Sparse.eval nodeValue5269 (mixedVector B) := by
    change mixedMoment B node5269 node5269Labels = _
    exact sound5269 B hB hF
  have h5340 : mixedVector B (Sum.inr 5340) = Sparse.eval nodeValue5340 (mixedVector B) := by
    change mixedMoment B node5340 node5340Labels = _
    exact sound5340 B hB hF
  have h5356 : mixedVector B (Sum.inr 5356) = Sparse.eval nodeValue5356 (mixedVector B) := by
    change mixedMoment B node5356 node5356Labels = _
    exact sound5356 B hB hF
  have h5393 : mixedVector B (Sum.inr 5393) = Sparse.eval nodeValue5393 (mixedVector B) := by
    change mixedMoment B node5393 node5393Labels = _
    exact sound5393 B hB hF
  have h5401 : mixedVector B (Sum.inr 5401) = Sparse.eval nodeValue5401 (mixedVector B) := by
    change mixedMoment B node5401 node5401Labels = _
    exact sound5401 B hB hF
  have h5410 : mixedVector B (Sum.inr 5410) = Sparse.eval nodeValue5410 (mixedVector B) := by
    change mixedMoment B node5410 node5410Labels = _
    exact sound5410 B hB hF
  have h5419 : mixedVector B (Sum.inr 5419) = Sparse.eval nodeValue5419 (mixedVector B) := by
    change mixedMoment B node5419 node5419Labels = _
    exact sound5419 B hB hF
  have h5438 : mixedVector B (Sum.inr 5438) = Sparse.eval nodeValue5438 (mixedVector B) := by
    change mixedMoment B node5438 node5438Labels = _
    exact sound5438 B hB hF
  have h5461 : mixedVector B (Sum.inr 5461) = Sparse.eval nodeValue5461 (mixedVector B) := by
    change mixedMoment B node5461 node5461Labels = _
    exact sound5461 B hB hF
  have h5463 : mixedVector B (Sum.inr 5463) = Sparse.eval nodeValue5463 (mixedVector B) := by
    change mixedMoment B node5463 node5463Labels = _
    exact sound5463 B hB hF
  have h5484 : mixedVector B (Sum.inr 5484) = Sparse.eval nodeValue5484 (mixedVector B) := by
    change mixedMoment B node5484 node5484Labels = _
    exact sound5484 B hB hF
  simpa only [sourceForm2602, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4942, h4944, h4945, h4951, h5043, h5081, h5170, h5189, h5217, h5236, h5269, h5340, h5356, h5393, h5401, h5410, h5419, h5438, h5461, h5463, h5484, reducedSource2078] using sourceEq2602 B hB

theorem rowSound2078 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2078 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2078, numericCheck2078, reducedZero2078 B hB hF, mul_zero]

theorem reducedZero2079 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2079 (mixedVector B) = 0 := by
  have h2656 : mixedVector B (Sum.inr 2656) = Sparse.eval nodeValue2656 (mixedVector B) := by
    change mixedMoment B node2656 node2656Labels = _
    exact sound2656 B hB hF
  have h2658 : mixedVector B (Sum.inr 2658) = Sparse.eval nodeValue2658 (mixedVector B) := by
    change mixedMoment B node2658 node2658Labels = _
    exact sound2658 B hB hF
  have h2682 : mixedVector B (Sum.inr 2682) = Sparse.eval nodeValue2682 (mixedVector B) := by
    change mixedMoment B node2682 node2682Labels = _
    exact sound2682 B hB hF
  have h2736 : mixedVector B (Sum.inr 2736) = Sparse.eval nodeValue2736 (mixedVector B) := by
    change mixedMoment B node2736 node2736Labels = _
    exact sound2736 B hB hF
  have h3407 : mixedVector B (Sum.inr 3407) = Sparse.eval nodeValue3407 (mixedVector B) := by
    change mixedMoment B node3407 node3407Labels = _
    exact sound3407 B hB hF
  have h3413 : mixedVector B (Sum.inr 3413) = Sparse.eval nodeValue3413 (mixedVector B) := by
    change mixedMoment B node3413 node3413Labels = _
    exact sound3413 B hB hF
  have h3418 : mixedVector B (Sum.inr 3418) = Sparse.eval nodeValue3418 (mixedVector B) := by
    change mixedMoment B node3418 node3418Labels = _
    exact sound3418 B hB hF
  have h3465 : mixedVector B (Sum.inr 3465) = Sparse.eval nodeValue3465 (mixedVector B) := by
    change mixedMoment B node3465 node3465Labels = _
    exact sound3465 B hB hF
  have h3482 : mixedVector B (Sum.inr 3482) = Sparse.eval nodeValue3482 (mixedVector B) := by
    change mixedMoment B node3482 node3482Labels = _
    exact sound3482 B hB hF
  have h3542 : mixedVector B (Sum.inr 3542) = Sparse.eval nodeValue3542 (mixedVector B) := by
    change mixedMoment B node3542 node3542Labels = _
    exact sound3542 B hB hF
  have h3606 : mixedVector B (Sum.inr 3606) = Sparse.eval nodeValue3606 (mixedVector B) := by
    change mixedMoment B node3606 node3606Labels = _
    exact sound3606 B hB hF
  have h3763 : mixedVector B (Sum.inr 3763) = Sparse.eval nodeValue3763 (mixedVector B) := by
    change mixedMoment B node3763 node3763Labels = _
    exact sound3763 B hB hF
  have h3773 : mixedVector B (Sum.inr 3773) = Sparse.eval nodeValue3773 (mixedVector B) := by
    change mixedMoment B node3773 node3773Labels = _
    exact sound3773 B hB hF
  have h3797 : mixedVector B (Sum.inr 3797) = Sparse.eval nodeValue3797 (mixedVector B) := by
    change mixedMoment B node3797 node3797Labels = _
    exact sound3797 B hB hF
  have h3804 : mixedVector B (Sum.inr 3804) = Sparse.eval nodeValue3804 (mixedVector B) := by
    change mixedMoment B node3804 node3804Labels = _
    exact sound3804 B hB hF
  have h3816 : mixedVector B (Sum.inr 3816) = Sparse.eval nodeValue3816 (mixedVector B) := by
    change mixedMoment B node3816 node3816Labels = _
    exact sound3816 B hB hF
  have h3842 : mixedVector B (Sum.inr 3842) = Sparse.eval nodeValue3842 (mixedVector B) := by
    change mixedMoment B node3842 node3842Labels = _
    exact sound3842 B hB hF
  have h3857 : mixedVector B (Sum.inr 3857) = Sparse.eval nodeValue3857 (mixedVector B) := by
    change mixedMoment B node3857 node3857Labels = _
    exact sound3857 B hB hF
  have h3960 : mixedVector B (Sum.inr 3960) = Sparse.eval nodeValue3960 (mixedVector B) := by
    change mixedMoment B node3960 node3960Labels = _
    exact sound3960 B hB hF
  have h3973 : mixedVector B (Sum.inr 3973) = Sparse.eval nodeValue3973 (mixedVector B) := by
    change mixedMoment B node3973 node3973Labels = _
    exact sound3973 B hB hF
  have h3983 : mixedVector B (Sum.inr 3983) = Sparse.eval nodeValue3983 (mixedVector B) := by
    change mixedMoment B node3983 node3983Labels = _
    exact sound3983 B hB hF
  simpa only [sourceForm2603, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2656, h2658, h2682, h2736, h3407, h3413, h3418, h3465, h3482, h3542, h3606, h3763, h3773, h3797, h3804, h3816, h3842, h3857, h3960, h3973, h3983, reducedSource2079] using sourceEq2603 B hB

theorem rowSound2079 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2079 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2079, numericCheck2079, reducedZero2079 B hB hF, mul_zero]

theorem sourceRowsAt2064 : MixedData.sourceRows (2064 : Fin 2425) =
    MixedData.row2064 := by decide +kernel

theorem sourceRowsAt2065 : MixedData.sourceRows (2065 : Fin 2425) =
    MixedData.row2065 := by decide +kernel

theorem sourceRowsAt2066 : MixedData.sourceRows (2066 : Fin 2425) =
    MixedData.row2066 := by decide +kernel

theorem sourceRowsAt2067 : MixedData.sourceRows (2067 : Fin 2425) =
    MixedData.row2067 := by decide +kernel

theorem sourceRowsAt2068 : MixedData.sourceRows (2068 : Fin 2425) =
    MixedData.row2068 := by decide +kernel

theorem sourceRowsAt2069 : MixedData.sourceRows (2069 : Fin 2425) =
    MixedData.row2069 := by decide +kernel

theorem sourceRowsAt2070 : MixedData.sourceRows (2070 : Fin 2425) =
    MixedData.row2070 := by decide +kernel

theorem sourceRowsAt2071 : MixedData.sourceRows (2071 : Fin 2425) =
    MixedData.row2071 := by decide +kernel

theorem sourceRowsAt2072 : MixedData.sourceRows (2072 : Fin 2425) =
    MixedData.row2072 := by decide +kernel

theorem sourceRowsAt2073 : MixedData.sourceRows (2073 : Fin 2425) =
    MixedData.row2073 := by decide +kernel

theorem sourceRowsAt2074 : MixedData.sourceRows (2074 : Fin 2425) =
    MixedData.row2074 := by decide +kernel

theorem sourceRowsAt2075 : MixedData.sourceRows (2075 : Fin 2425) =
    MixedData.row2075 := by decide +kernel

theorem sourceRowsAt2076 : MixedData.sourceRows (2076 : Fin 2425) =
    MixedData.row2076 := by decide +kernel

theorem sourceRowsAt2077 : MixedData.sourceRows (2077 : Fin 2425) =
    MixedData.row2077 := by decide +kernel

theorem sourceRowsAt2078 : MixedData.sourceRows (2078 : Fin 2425) =
    MixedData.row2078 := by decide +kernel

theorem sourceRowsAt2079 : MixedData.sourceRows (2079 : Fin 2425) =
    MixedData.row2079 := by decide +kernel

theorem chunkSound129 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 129) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 2064 ∨ k.val = 2065 ∨ k.val = 2066 ∨ k.val = 2067 ∨ k.val = 2068 ∨ k.val = 2069 ∨ k.val = 2070 ∨ k.val = 2071 ∨ k.val = 2072 ∨ k.val = 2073 ∨ k.val = 2074 ∨ k.val = 2075 ∨ k.val = 2076 ∨ k.val = 2077 ∨ k.val = 2078 ∨ k.val = 2079 := by omega
  rcases heq with h2064 | h2065 | h2066 | h2067 | h2068 | h2069 | h2070 | h2071 | h2072 | h2073 | h2074 | h2075 | h2076 | h2077 | h2078 | h2079
  · have he : k = (2064 : Fin 2425) := Fin.ext h2064
    subst k
    rw [sourceRowsAt2064]
    exact rowSound2064 B hB hF
  · have he : k = (2065 : Fin 2425) := Fin.ext h2065
    subst k
    rw [sourceRowsAt2065]
    exact rowSound2065 B hB hF
  · have he : k = (2066 : Fin 2425) := Fin.ext h2066
    subst k
    rw [sourceRowsAt2066]
    exact rowSound2066 B hB hF
  · have he : k = (2067 : Fin 2425) := Fin.ext h2067
    subst k
    rw [sourceRowsAt2067]
    exact rowSound2067 B hB hF
  · have he : k = (2068 : Fin 2425) := Fin.ext h2068
    subst k
    rw [sourceRowsAt2068]
    exact rowSound2068 B hB hF
  · have he : k = (2069 : Fin 2425) := Fin.ext h2069
    subst k
    rw [sourceRowsAt2069]
    exact rowSound2069 B hB hF
  · have he : k = (2070 : Fin 2425) := Fin.ext h2070
    subst k
    rw [sourceRowsAt2070]
    exact rowSound2070 B hB hF
  · have he : k = (2071 : Fin 2425) := Fin.ext h2071
    subst k
    rw [sourceRowsAt2071]
    exact rowSound2071 B hB hF
  · have he : k = (2072 : Fin 2425) := Fin.ext h2072
    subst k
    rw [sourceRowsAt2072]
    exact rowSound2072 B hB hF
  · have he : k = (2073 : Fin 2425) := Fin.ext h2073
    subst k
    rw [sourceRowsAt2073]
    exact rowSound2073 B hB hF
  · have he : k = (2074 : Fin 2425) := Fin.ext h2074
    subst k
    rw [sourceRowsAt2074]
    exact rowSound2074 B hB hF
  · have he : k = (2075 : Fin 2425) := Fin.ext h2075
    subst k
    rw [sourceRowsAt2075]
    exact rowSound2075 B hB hF
  · have he : k = (2076 : Fin 2425) := Fin.ext h2076
    subst k
    rw [sourceRowsAt2076]
    exact rowSound2076 B hB hF
  · have he : k = (2077 : Fin 2425) := Fin.ext h2077
    subst k
    rw [sourceRowsAt2077]
    exact rowSound2077 B hB hF
  · have he : k = (2078 : Fin 2425) := Fin.ext h2078
    subst k
    rw [sourceRowsAt2078]
    exact rowSound2078 B hB hF
  · have he : k = (2079 : Fin 2425) := Fin.ext h2079
    subst k
    rw [sourceRowsAt2079]
    exact rowSound2079 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
