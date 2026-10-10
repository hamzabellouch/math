import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound52
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources30

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero832 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource832 (mixedVector B) = 0 := by
  have h2858 : mixedVector B (Sum.inr 2858) = Sparse.eval nodeValue2858 (mixedVector B) := by
    change mixedMoment B node2858 node2858Labels = _
    exact sound2858 B hB hF
  have h2859 : mixedVector B (Sum.inr 2859) = Sparse.eval nodeValue2859 (mixedVector B) := by
    change mixedMoment B node2859 node2859Labels = _
    exact sound2859 B hB hF
  have h2864 : mixedVector B (Sum.inr 2864) = Sparse.eval nodeValue2864 (mixedVector B) := by
    change mixedMoment B node2864 node2864Labels = _
    exact sound2864 B hB hF
  have h3030 : mixedVector B (Sum.inr 3030) = Sparse.eval nodeValue3030 (mixedVector B) := by
    change mixedMoment B node3030 node3030Labels = _
    exact sound3030 B hB hF
  have h3954 : mixedVector B (Sum.inr 3954) = Sparse.eval nodeValue3954 (mixedVector B) := by
    change mixedMoment B node3954 node3954Labels = _
    exact sound3954 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm952, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2858, h2859, h2864, h3030, h3954, h4091, reducedSource832] using sourceEq952 B hB

theorem rowSound832 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row832 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck832, numericCheck832, reducedZero832 B hB hF, mul_zero]

theorem reducedZero833 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource833 (mixedVector B) = 0 := by
  have h2606 : mixedVector B (Sum.inr 2606) = Sparse.eval nodeValue2606 (mixedVector B) := by
    change mixedMoment B node2606 node2606Labels = _
    exact sound2606 B hB hF
  have h2607 : mixedVector B (Sum.inr 2607) = Sparse.eval nodeValue2607 (mixedVector B) := by
    change mixedMoment B node2607 node2607Labels = _
    exact sound2607 B hB hF
  have h2631 : mixedVector B (Sum.inr 2631) = Sparse.eval nodeValue2631 (mixedVector B) := by
    change mixedMoment B node2631 node2631Labels = _
    exact sound2631 B hB hF
  have h2676 : mixedVector B (Sum.inr 2676) = Sparse.eval nodeValue2676 (mixedVector B) := by
    change mixedMoment B node2676 node2676Labels = _
    exact sound2676 B hB hF
  have h3524 : mixedVector B (Sum.inr 3524) = Sparse.eval nodeValue3524 (mixedVector B) := by
    change mixedMoment B node3524 node3524Labels = _
    exact sound3524 B hB hF
  have h3525 : mixedVector B (Sum.inr 3525) = Sparse.eval nodeValue3525 (mixedVector B) := by
    change mixedMoment B node3525 node3525Labels = _
    exact sound3525 B hB hF
  have h3527 : mixedVector B (Sum.inr 3527) = Sparse.eval nodeValue3527 (mixedVector B) := by
    change mixedMoment B node3527 node3527Labels = _
    exact sound3527 B hB hF
  have h3566 : mixedVector B (Sum.inr 3566) = Sparse.eval nodeValue3566 (mixedVector B) := by
    change mixedMoment B node3566 node3566Labels = _
    exact sound3566 B hB hF
  have h3780 : mixedVector B (Sum.inr 3780) = Sparse.eval nodeValue3780 (mixedVector B) := by
    change mixedMoment B node3780 node3780Labels = _
    exact sound3780 B hB hF
  have h3799 : mixedVector B (Sum.inr 3799) = Sparse.eval nodeValue3799 (mixedVector B) := by
    change mixedMoment B node3799 node3799Labels = _
    exact sound3799 B hB hF
  have h3800 : mixedVector B (Sum.inr 3800) = Sparse.eval nodeValue3800 (mixedVector B) := by
    change mixedMoment B node3800 node3800Labels = _
    exact sound3800 B hB hF
  have h3802 : mixedVector B (Sum.inr 3802) = Sparse.eval nodeValue3802 (mixedVector B) := by
    change mixedMoment B node3802 node3802Labels = _
    exact sound3802 B hB hF
  have h3847 : mixedVector B (Sum.inr 3847) = Sparse.eval nodeValue3847 (mixedVector B) := by
    change mixedMoment B node3847 node3847Labels = _
    exact sound3847 B hB hF
  have h3850 : mixedVector B (Sum.inr 3850) = Sparse.eval nodeValue3850 (mixedVector B) := by
    change mixedMoment B node3850 node3850Labels = _
    exact sound3850 B hB hF
  have h3852 : mixedVector B (Sum.inr 3852) = Sparse.eval nodeValue3852 (mixedVector B) := by
    change mixedMoment B node3852 node3852Labels = _
    exact sound3852 B hB hF
  have h3854 : mixedVector B (Sum.inr 3854) = Sparse.eval nodeValue3854 (mixedVector B) := by
    change mixedMoment B node3854 node3854Labels = _
    exact sound3854 B hB hF
  have h3878 : mixedVector B (Sum.inr 3878) = Sparse.eval nodeValue3878 (mixedVector B) := by
    change mixedMoment B node3878 node3878Labels = _
    exact sound3878 B hB hF
  have h3881 : mixedVector B (Sum.inr 3881) = Sparse.eval nodeValue3881 (mixedVector B) := by
    change mixedMoment B node3881 node3881Labels = _
    exact sound3881 B hB hF
  have h3938 : mixedVector B (Sum.inr 3938) = Sparse.eval nodeValue3938 (mixedVector B) := by
    change mixedMoment B node3938 node3938Labels = _
    exact sound3938 B hB hF
  have h3976 : mixedVector B (Sum.inr 3976) = Sparse.eval nodeValue3976 (mixedVector B) := by
    change mixedMoment B node3976 node3976Labels = _
    exact sound3976 B hB hF
  have h3995 : mixedVector B (Sum.inr 3995) = Sparse.eval nodeValue3995 (mixedVector B) := by
    change mixedMoment B node3995 node3995Labels = _
    exact sound3995 B hB hF
  simpa only [sourceForm954, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2606, h2607, h2631, h2676, h3524, h3525, h3527, h3566, h3780, h3799, h3800, h3802, h3847, h3850, h3852, h3854, h3878, h3881, h3938, h3976, h3995, reducedSource833] using sourceEq954 B hB

theorem rowSound833 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row833 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck833, numericCheck833, reducedZero833 B hB hF, mul_zero]

theorem reducedZero834 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource834 (mixedVector B) = 0 := by
  have h2860 : mixedVector B (Sum.inr 2860) = Sparse.eval nodeValue2860 (mixedVector B) := by
    change mixedMoment B node2860 node2860Labels = _
    exact sound2860 B hB hF
  have h2864 : mixedVector B (Sum.inr 2864) = Sparse.eval nodeValue2864 (mixedVector B) := by
    change mixedMoment B node2864 node2864Labels = _
    exact sound2864 B hB hF
  have h2874 : mixedVector B (Sum.inr 2874) = Sparse.eval nodeValue2874 (mixedVector B) := by
    change mixedMoment B node2874 node2874Labels = _
    exact sound2874 B hB hF
  have h3085 : mixedVector B (Sum.inr 3085) = Sparse.eval nodeValue3085 (mixedVector B) := by
    change mixedMoment B node3085 node3085Labels = _
    exact sound3085 B hB hF
  have h3374 : mixedVector B (Sum.inr 3374) = Sparse.eval nodeValue3374 (mixedVector B) := by
    change mixedMoment B node3374 node3374Labels = _
    exact sound3374 B hB hF
  have h3378 : mixedVector B (Sum.inr 3378) = Sparse.eval nodeValue3378 (mixedVector B) := by
    change mixedMoment B node3378 node3378Labels = _
    exact sound3378 B hB hF
  have h3384 : mixedVector B (Sum.inr 3384) = Sparse.eval nodeValue3384 (mixedVector B) := by
    change mixedMoment B node3384 node3384Labels = _
    exact sound3384 B hB hF
  have h3569 : mixedVector B (Sum.inr 3569) = Sparse.eval nodeValue3569 (mixedVector B) := by
    change mixedMoment B node3569 node3569Labels = _
    exact sound3569 B hB hF
  have h3758 : mixedVector B (Sum.inr 3758) = Sparse.eval nodeValue3758 (mixedVector B) := by
    change mixedMoment B node3758 node3758Labels = _
    exact sound3758 B hB hF
  have h3759 : mixedVector B (Sum.inr 3759) = Sparse.eval nodeValue3759 (mixedVector B) := by
    change mixedMoment B node3759 node3759Labels = _
    exact sound3759 B hB hF
  have h3762 : mixedVector B (Sum.inr 3762) = Sparse.eval nodeValue3762 (mixedVector B) := by
    change mixedMoment B node3762 node3762Labels = _
    exact sound3762 B hB hF
  have h3788 : mixedVector B (Sum.inr 3788) = Sparse.eval nodeValue3788 (mixedVector B) := by
    change mixedMoment B node3788 node3788Labels = _
    exact sound3788 B hB hF
  have h3801 : mixedVector B (Sum.inr 3801) = Sparse.eval nodeValue3801 (mixedVector B) := by
    change mixedMoment B node3801 node3801Labels = _
    exact sound3801 B hB hF
  have h3877 : mixedVector B (Sum.inr 3877) = Sparse.eval nodeValue3877 (mixedVector B) := by
    change mixedMoment B node3877 node3877Labels = _
    exact sound3877 B hB hF
  have h3953 : mixedVector B (Sum.inr 3953) = Sparse.eval nodeValue3953 (mixedVector B) := by
    change mixedMoment B node3953 node3953Labels = _
    exact sound3953 B hB hF
  have h3958 : mixedVector B (Sum.inr 3958) = Sparse.eval nodeValue3958 (mixedVector B) := by
    change mixedMoment B node3958 node3958Labels = _
    exact sound3958 B hB hF
  have h3959 : mixedVector B (Sum.inr 3959) = Sparse.eval nodeValue3959 (mixedVector B) := by
    change mixedMoment B node3959 node3959Labels = _
    exact sound3959 B hB hF
  have h3977 : mixedVector B (Sum.inr 3977) = Sparse.eval nodeValue3977 (mixedVector B) := by
    change mixedMoment B node3977 node3977Labels = _
    exact sound3977 B hB hF
  have h3982 : mixedVector B (Sum.inr 3982) = Sparse.eval nodeValue3982 (mixedVector B) := by
    change mixedMoment B node3982 node3982Labels = _
    exact sound3982 B hB hF
  have h4023 : mixedVector B (Sum.inr 4023) = Sparse.eval nodeValue4023 (mixedVector B) := by
    change mixedMoment B node4023 node4023Labels = _
    exact sound4023 B hB hF
  have h4027 : mixedVector B (Sum.inr 4027) = Sparse.eval nodeValue4027 (mixedVector B) := by
    change mixedMoment B node4027 node4027Labels = _
    exact sound4027 B hB hF
  simpa only [sourceForm955, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2860, h2864, h2874, h3085, h3374, h3378, h3384, h3569, h3758, h3759, h3762, h3788, h3801, h3877, h3953, h3958, h3959, h3977, h3982, h4023, h4027, reducedSource834] using sourceEq955 B hB

theorem rowSound834 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row834 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck834, numericCheck834, reducedZero834 B hB hF, mul_zero]

theorem reducedZero835 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource835 (mixedVector B) = 0 := by
  have h2878 : mixedVector B (Sum.inr 2878) = Sparse.eval nodeValue2878 (mixedVector B) := by
    change mixedMoment B node2878 node2878Labels = _
    exact sound2878 B hB hF
  have h3703 : mixedVector B (Sum.inr 3703) = Sparse.eval nodeValue3703 (mixedVector B) := by
    change mixedMoment B node3703 node3703Labels = _
    exact sound3703 B hB hF
  have h3874 : mixedVector B (Sum.inr 3874) = Sparse.eval nodeValue3874 (mixedVector B) := by
    change mixedMoment B node3874 node3874Labels = _
    exact sound3874 B hB hF
  have h3956 : mixedVector B (Sum.inr 3956) = Sparse.eval nodeValue3956 (mixedVector B) := by
    change mixedMoment B node3956 node3956Labels = _
    exact sound3956 B hB hF
  have h3961 : mixedVector B (Sum.inr 3961) = Sparse.eval nodeValue3961 (mixedVector B) := by
    change mixedMoment B node3961 node3961Labels = _
    exact sound3961 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm956, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2878, h3703, h3874, h3956, h3961, h4092, reducedSource835] using sourceEq956 B hB

theorem rowSound835 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row835 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck835, numericCheck835, reducedZero835 B hB hF, mul_zero]

theorem reducedZero836 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource836 (mixedVector B) = 0 := by
  have h2630 : mixedVector B (Sum.inr 2630) = Sparse.eval nodeValue2630 (mixedVector B) := by
    change mixedMoment B node2630 node2630Labels = _
    exact sound2630 B hB hF
  have h2869 : mixedVector B (Sum.inr 2869) = Sparse.eval nodeValue2869 (mixedVector B) := by
    change mixedMoment B node2869 node2869Labels = _
    exact sound2869 B hB hF
  have h3697 : mixedVector B (Sum.inr 3697) = Sparse.eval nodeValue3697 (mixedVector B) := by
    change mixedMoment B node3697 node3697Labels = _
    exact sound3697 B hB hF
  have h3874 : mixedVector B (Sum.inr 3874) = Sparse.eval nodeValue3874 (mixedVector B) := by
    change mixedMoment B node3874 node3874Labels = _
    exact sound3874 B hB hF
  have h3884 : mixedVector B (Sum.inr 3884) = Sparse.eval nodeValue3884 (mixedVector B) := by
    change mixedMoment B node3884 node3884Labels = _
    exact sound3884 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm957, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2630, h2869, h3697, h3874, h3884, h4092, reducedSource836] using sourceEq957 B hB

theorem rowSound836 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row836 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck836, numericCheck836, reducedZero836 B hB hF, mul_zero]

theorem reducedZero837 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource837 (mixedVector B) = 0 := by
  have h3786 : mixedVector B (Sum.inr 3786) = Sparse.eval nodeValue3786 (mixedVector B) := by
    change mixedMoment B node3786 node3786Labels = _
    exact sound3786 B hB hF
  have h3788 : mixedVector B (Sum.inr 3788) = Sparse.eval nodeValue3788 (mixedVector B) := by
    change mixedMoment B node3788 node3788Labels = _
    exact sound3788 B hB hF
  have h3805 : mixedVector B (Sum.inr 3805) = Sparse.eval nodeValue3805 (mixedVector B) := by
    change mixedMoment B node3805 node3805Labels = _
    exact sound3805 B hB hF
  have h3874 : mixedVector B (Sum.inr 3874) = Sparse.eval nodeValue3874 (mixedVector B) := by
    change mixedMoment B node3874 node3874Labels = _
    exact sound3874 B hB hF
  have h3956 : mixedVector B (Sum.inr 3956) = Sparse.eval nodeValue3956 (mixedVector B) := by
    change mixedMoment B node3956 node3956Labels = _
    exact sound3956 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm958, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3786, h3788, h3805, h3874, h3956, h4092, reducedSource837] using sourceEq958 B hB

theorem rowSound837 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row837 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck837, numericCheck837, reducedZero837 B hB hF, mul_zero]

theorem reducedZero838 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource838 (mixedVector B) = 0 := by
  have h2869 : mixedVector B (Sum.inr 2869) = Sparse.eval nodeValue2869 (mixedVector B) := by
    change mixedMoment B node2869 node2869Labels = _
    exact sound2869 B hB hF
  have h2870 : mixedVector B (Sum.inr 2870) = Sparse.eval nodeValue2870 (mixedVector B) := by
    change mixedMoment B node2870 node2870Labels = _
    exact sound2870 B hB hF
  have h2878 : mixedVector B (Sum.inr 2878) = Sparse.eval nodeValue2878 (mixedVector B) := by
    change mixedMoment B node2878 node2878Labels = _
    exact sound2878 B hB hF
  have h3043 : mixedVector B (Sum.inr 3043) = Sparse.eval nodeValue3043 (mixedVector B) := by
    change mixedMoment B node3043 node3043Labels = _
    exact sound3043 B hB hF
  have h3874 : mixedVector B (Sum.inr 3874) = Sparse.eval nodeValue3874 (mixedVector B) := by
    change mixedMoment B node3874 node3874Labels = _
    exact sound3874 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm959, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2869, h2870, h2878, h3043, h3874, h4092, reducedSource838] using sourceEq959 B hB

theorem rowSound838 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row838 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck838, numericCheck838, reducedZero838 B hB hF, mul_zero]

theorem reducedZero839 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource839 (mixedVector B) = 0 := by
  have h2614 : mixedVector B (Sum.inr 2614) = Sparse.eval nodeValue2614 (mixedVector B) := by
    change mixedMoment B node2614 node2614Labels = _
    exact sound2614 B hB hF
  have h3043 : mixedVector B (Sum.inr 3043) = Sparse.eval nodeValue3043 (mixedVector B) := by
    change mixedMoment B node3043 node3043Labels = _
    exact sound3043 B hB hF
  have h3786 : mixedVector B (Sum.inr 3786) = Sparse.eval nodeValue3786 (mixedVector B) := by
    change mixedMoment B node3786 node3786Labels = _
    exact sound3786 B hB hF
  have h3850 : mixedVector B (Sum.inr 3850) = Sparse.eval nodeValue3850 (mixedVector B) := by
    change mixedMoment B node3850 node3850Labels = _
    exact sound3850 B hB hF
  have h3874 : mixedVector B (Sum.inr 3874) = Sparse.eval nodeValue3874 (mixedVector B) := by
    change mixedMoment B node3874 node3874Labels = _
    exact sound3874 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm960, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2614, h3043, h3786, h3850, h3874, h4092, reducedSource839] using sourceEq960 B hB

theorem rowSound839 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row839 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck839, numericCheck839, reducedZero839 B hB hF, mul_zero]

theorem reducedZero840 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource840 (mixedVector B) = 0 := by
  have h4792 : mixedVector B (Sum.inr 4792) = Sparse.eval nodeValue4792 (mixedVector B) := by
    change mixedMoment B node4792 node4792Labels = _
    exact sound4792 B hB hF
  have h4795 : mixedVector B (Sum.inr 4795) = Sparse.eval nodeValue4795 (mixedVector B) := by
    change mixedMoment B node4795 node4795Labels = _
    exact sound4795 B hB hF
  have h4803 : mixedVector B (Sum.inr 4803) = Sparse.eval nodeValue4803 (mixedVector B) := by
    change mixedMoment B node4803 node4803Labels = _
    exact sound4803 B hB hF
  have h4885 : mixedVector B (Sum.inr 4885) = Sparse.eval nodeValue4885 (mixedVector B) := by
    change mixedMoment B node4885 node4885Labels = _
    exact sound4885 B hB hF
  have h5067 : mixedVector B (Sum.inr 5067) = Sparse.eval nodeValue5067 (mixedVector B) := by
    change mixedMoment B node5067 node5067Labels = _
    exact sound5067 B hB hF
  have h5076 : mixedVector B (Sum.inr 5076) = Sparse.eval nodeValue5076 (mixedVector B) := by
    change mixedMoment B node5076 node5076Labels = _
    exact sound5076 B hB hF
  have h5251 : mixedVector B (Sum.inr 5251) = Sparse.eval nodeValue5251 (mixedVector B) := by
    change mixedMoment B node5251 node5251Labels = _
    exact sound5251 B hB hF
  have h5348 : mixedVector B (Sum.inr 5348) = Sparse.eval nodeValue5348 (mixedVector B) := by
    change mixedMoment B node5348 node5348Labels = _
    exact sound5348 B hB hF
  have h5353 : mixedVector B (Sum.inr 5353) = Sparse.eval nodeValue5353 (mixedVector B) := by
    change mixedMoment B node5353 node5353Labels = _
    exact sound5353 B hB hF
  have h5354 : mixedVector B (Sum.inr 5354) = Sparse.eval nodeValue5354 (mixedVector B) := by
    change mixedMoment B node5354 node5354Labels = _
    exact sound5354 B hB hF
  have h5403 : mixedVector B (Sum.inr 5403) = Sparse.eval nodeValue5403 (mixedVector B) := by
    change mixedMoment B node5403 node5403Labels = _
    exact sound5403 B hB hF
  have h5405 : mixedVector B (Sum.inr 5405) = Sparse.eval nodeValue5405 (mixedVector B) := by
    change mixedMoment B node5405 node5405Labels = _
    exact sound5405 B hB hF
  have h5406 : mixedVector B (Sum.inr 5406) = Sparse.eval nodeValue5406 (mixedVector B) := by
    change mixedMoment B node5406 node5406Labels = _
    exact sound5406 B hB hF
  have h5408 : mixedVector B (Sum.inr 5408) = Sparse.eval nodeValue5408 (mixedVector B) := by
    change mixedMoment B node5408 node5408Labels = _
    exact sound5408 B hB hF
  have h5425 : mixedVector B (Sum.inr 5425) = Sparse.eval nodeValue5425 (mixedVector B) := by
    change mixedMoment B node5425 node5425Labels = _
    exact sound5425 B hB hF
  have h5429 : mixedVector B (Sum.inr 5429) = Sparse.eval nodeValue5429 (mixedVector B) := by
    change mixedMoment B node5429 node5429Labels = _
    exact sound5429 B hB hF
  have h5430 : mixedVector B (Sum.inr 5430) = Sparse.eval nodeValue5430 (mixedVector B) := by
    change mixedMoment B node5430 node5430Labels = _
    exact sound5430 B hB hF
  have h5433 : mixedVector B (Sum.inr 5433) = Sparse.eval nodeValue5433 (mixedVector B) := by
    change mixedMoment B node5433 node5433Labels = _
    exact sound5433 B hB hF
  have h5437 : mixedVector B (Sum.inr 5437) = Sparse.eval nodeValue5437 (mixedVector B) := by
    change mixedMoment B node5437 node5437Labels = _
    exact sound5437 B hB hF
  have h5447 : mixedVector B (Sum.inr 5447) = Sparse.eval nodeValue5447 (mixedVector B) := by
    change mixedMoment B node5447 node5447Labels = _
    exact sound5447 B hB hF
  have h5482 : mixedVector B (Sum.inr 5482) = Sparse.eval nodeValue5482 (mixedVector B) := by
    change mixedMoment B node5482 node5482Labels = _
    exact sound5482 B hB hF
  simpa only [sourceForm963, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4792, h4795, h4803, h4885, h5067, h5076, h5251, h5348, h5353, h5354, h5403, h5405, h5406, h5408, h5425, h5429, h5430, h5433, h5437, h5447, h5482, reducedSource840] using sourceEq963 B hB

theorem rowSound840 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row840 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck840, numericCheck840, reducedZero840 B hB hF, mul_zero]

theorem reducedZero841 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource841 (mixedVector B) = 0 := by
  have h2009 : mixedVector B (Sum.inr 2009) = Sparse.eval nodeValue2009 (mixedVector B) := by
    change mixedMoment B node2009 node2009Labels = _
    exact sound2009 B hB hF
  have h2012 : mixedVector B (Sum.inr 2012) = Sparse.eval nodeValue2012 (mixedVector B) := by
    change mixedMoment B node2012 node2012Labels = _
    exact sound2012 B hB hF
  have h2021 : mixedVector B (Sum.inr 2021) = Sparse.eval nodeValue2021 (mixedVector B) := by
    change mixedMoment B node2021 node2021Labels = _
    exact sound2021 B hB hF
  have h2233 : mixedVector B (Sum.inr 2233) = Sparse.eval nodeValue2233 (mixedVector B) := by
    change mixedMoment B node2233 node2233Labels = _
    exact sound2233 B hB hF
  have h2981 : mixedVector B (Sum.inr 2981) = Sparse.eval nodeValue2981 (mixedVector B) := by
    change mixedMoment B node2981 node2981Labels = _
    exact sound2981 B hB hF
  have h2986 : mixedVector B (Sum.inr 2986) = Sparse.eval nodeValue2986 (mixedVector B) := by
    change mixedMoment B node2986 node2986Labels = _
    exact sound2986 B hB hF
  have h3064 : mixedVector B (Sum.inr 3064) = Sparse.eval nodeValue3064 (mixedVector B) := by
    change mixedMoment B node3064 node3064Labels = _
    exact sound3064 B hB hF
  have h3685 : mixedVector B (Sum.inr 3685) = Sparse.eval nodeValue3685 (mixedVector B) := by
    change mixedMoment B node3685 node3685Labels = _
    exact sound3685 B hB hF
  have h3691 : mixedVector B (Sum.inr 3691) = Sparse.eval nodeValue3691 (mixedVector B) := by
    change mixedMoment B node3691 node3691Labels = _
    exact sound3691 B hB hF
  have h3818 : mixedVector B (Sum.inr 3818) = Sparse.eval nodeValue3818 (mixedVector B) := by
    change mixedMoment B node3818 node3818Labels = _
    exact sound3818 B hB hF
  have h3822 : mixedVector B (Sum.inr 3822) = Sparse.eval nodeValue3822 (mixedVector B) := by
    change mixedMoment B node3822 node3822Labels = _
    exact sound3822 B hB hF
  have h3839 : mixedVector B (Sum.inr 3839) = Sparse.eval nodeValue3839 (mixedVector B) := by
    change mixedMoment B node3839 node3839Labels = _
    exact sound3839 B hB hF
  have h3846 : mixedVector B (Sum.inr 3846) = Sparse.eval nodeValue3846 (mixedVector B) := by
    change mixedMoment B node3846 node3846Labels = _
    exact sound3846 B hB hF
  have h3847 : mixedVector B (Sum.inr 3847) = Sparse.eval nodeValue3847 (mixedVector B) := by
    change mixedMoment B node3847 node3847Labels = _
    exact sound3847 B hB hF
  have h3848 : mixedVector B (Sum.inr 3848) = Sparse.eval nodeValue3848 (mixedVector B) := by
    change mixedMoment B node3848 node3848Labels = _
    exact sound3848 B hB hF
  have h3899 : mixedVector B (Sum.inr 3899) = Sparse.eval nodeValue3899 (mixedVector B) := by
    change mixedMoment B node3899 node3899Labels = _
    exact sound3899 B hB hF
  have h3909 : mixedVector B (Sum.inr 3909) = Sparse.eval nodeValue3909 (mixedVector B) := by
    change mixedMoment B node3909 node3909Labels = _
    exact sound3909 B hB hF
  have h3977 : mixedVector B (Sum.inr 3977) = Sparse.eval nodeValue3977 (mixedVector B) := by
    change mixedMoment B node3977 node3977Labels = _
    exact sound3977 B hB hF
  have h3992 : mixedVector B (Sum.inr 3992) = Sparse.eval nodeValue3992 (mixedVector B) := by
    change mixedMoment B node3992 node3992Labels = _
    exact sound3992 B hB hF
  have h4033 : mixedVector B (Sum.inr 4033) = Sparse.eval nodeValue4033 (mixedVector B) := by
    change mixedMoment B node4033 node4033Labels = _
    exact sound4033 B hB hF
  have h4038 : mixedVector B (Sum.inr 4038) = Sparse.eval nodeValue4038 (mixedVector B) := by
    change mixedMoment B node4038 node4038Labels = _
    exact sound4038 B hB hF
  simpa only [sourceForm964, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2009, h2012, h2021, h2233, h2981, h2986, h3064, h3685, h3691, h3818, h3822, h3839, h3846, h3847, h3848, h3899, h3909, h3977, h3992, h4033, h4038, reducedSource841] using sourceEq964 B hB

theorem rowSound841 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row841 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck841, numericCheck841, reducedZero841 B hB hF, mul_zero]

theorem reducedZero842 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource842 (mixedVector B) = 0 := by
  have h2195 : mixedVector B (Sum.inr 2195) = Sparse.eval nodeValue2195 (mixedVector B) := by
    change mixedMoment B node2195 node2195Labels = _
    exact sound2195 B hB hF
  have h2201 : mixedVector B (Sum.inr 2201) = Sparse.eval nodeValue2201 (mixedVector B) := by
    change mixedMoment B node2201 node2201Labels = _
    exact sound2201 B hB hF
  have h2213 : mixedVector B (Sum.inr 2213) = Sparse.eval nodeValue2213 (mixedVector B) := by
    change mixedMoment B node2213 node2213Labels = _
    exact sound2213 B hB hF
  have h2252 : mixedVector B (Sum.inr 2252) = Sparse.eval nodeValue2252 (mixedVector B) := by
    change mixedMoment B node2252 node2252Labels = _
    exact sound2252 B hB hF
  have h3476 : mixedVector B (Sum.inr 3476) = Sparse.eval nodeValue3476 (mixedVector B) := by
    change mixedMoment B node3476 node3476Labels = _
    exact sound3476 B hB hF
  have h3477 : mixedVector B (Sum.inr 3477) = Sparse.eval nodeValue3477 (mixedVector B) := by
    change mixedMoment B node3477 node3477Labels = _
    exact sound3477 B hB hF
  have h3539 : mixedVector B (Sum.inr 3539) = Sparse.eval nodeValue3539 (mixedVector B) := by
    change mixedMoment B node3539 node3539Labels = _
    exact sound3539 B hB hF
  have h3761 : mixedVector B (Sum.inr 3761) = Sparse.eval nodeValue3761 (mixedVector B) := by
    change mixedMoment B node3761 node3761Labels = _
    exact sound3761 B hB hF
  have h3768 : mixedVector B (Sum.inr 3768) = Sparse.eval nodeValue3768 (mixedVector B) := by
    change mixedMoment B node3768 node3768Labels = _
    exact sound3768 B hB hF
  have h3769 : mixedVector B (Sum.inr 3769) = Sparse.eval nodeValue3769 (mixedVector B) := by
    change mixedMoment B node3769 node3769Labels = _
    exact sound3769 B hB hF
  have h3805 : mixedVector B (Sum.inr 3805) = Sparse.eval nodeValue3805 (mixedVector B) := by
    change mixedMoment B node3805 node3805Labels = _
    exact sound3805 B hB hF
  have h3806 : mixedVector B (Sum.inr 3806) = Sparse.eval nodeValue3806 (mixedVector B) := by
    change mixedMoment B node3806 node3806Labels = _
    exact sound3806 B hB hF
  have h3810 : mixedVector B (Sum.inr 3810) = Sparse.eval nodeValue3810 (mixedVector B) := by
    change mixedMoment B node3810 node3810Labels = _
    exact sound3810 B hB hF
  have h3812 : mixedVector B (Sum.inr 3812) = Sparse.eval nodeValue3812 (mixedVector B) := by
    change mixedMoment B node3812 node3812Labels = _
    exact sound3812 B hB hF
  have h3840 : mixedVector B (Sum.inr 3840) = Sparse.eval nodeValue3840 (mixedVector B) := by
    change mixedMoment B node3840 node3840Labels = _
    exact sound3840 B hB hF
  have h3851 : mixedVector B (Sum.inr 3851) = Sparse.eval nodeValue3851 (mixedVector B) := by
    change mixedMoment B node3851 node3851Labels = _
    exact sound3851 B hB hF
  have h3855 : mixedVector B (Sum.inr 3855) = Sparse.eval nodeValue3855 (mixedVector B) := by
    change mixedMoment B node3855 node3855Labels = _
    exact sound3855 B hB hF
  have h3871 : mixedVector B (Sum.inr 3871) = Sparse.eval nodeValue3871 (mixedVector B) := by
    change mixedMoment B node3871 node3871Labels = _
    exact sound3871 B hB hF
  have h3874 : mixedVector B (Sum.inr 3874) = Sparse.eval nodeValue3874 (mixedVector B) := by
    change mixedMoment B node3874 node3874Labels = _
    exact sound3874 B hB hF
  have h3882 : mixedVector B (Sum.inr 3882) = Sparse.eval nodeValue3882 (mixedVector B) := by
    change mixedMoment B node3882 node3882Labels = _
    exact sound3882 B hB hF
  have h3980 : mixedVector B (Sum.inr 3980) = Sparse.eval nodeValue3980 (mixedVector B) := by
    change mixedMoment B node3980 node3980Labels = _
    exact sound3980 B hB hF
  simpa only [sourceForm965, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2195, h2201, h2213, h2252, h3476, h3477, h3539, h3761, h3768, h3769, h3805, h3806, h3810, h3812, h3840, h3851, h3855, h3871, h3874, h3882, h3980, reducedSource842] using sourceEq965 B hB

theorem rowSound842 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row842 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck842, numericCheck842, reducedZero842 B hB hF, mul_zero]

theorem reducedZero843 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource843 (mixedVector B) = 0 := by
  have h5085 : mixedVector B (Sum.inr 5085) = Sparse.eval nodeValue5085 (mixedVector B) := by
    change mixedMoment B node5085 node5085Labels = _
    exact sound5085 B hB hF
  have h5086 : mixedVector B (Sum.inr 5086) = Sparse.eval nodeValue5086 (mixedVector B) := by
    change mixedMoment B node5086 node5086Labels = _
    exact sound5086 B hB hF
  have h5098 : mixedVector B (Sum.inr 5098) = Sparse.eval nodeValue5098 (mixedVector B) := by
    change mixedMoment B node5098 node5098Labels = _
    exact sound5098 B hB hF
  have h5254 : mixedVector B (Sum.inr 5254) = Sparse.eval nodeValue5254 (mixedVector B) := by
    change mixedMoment B node5254 node5254Labels = _
    exact sound5254 B hB hF
  have h5256 : mixedVector B (Sum.inr 5256) = Sparse.eval nodeValue5256 (mixedVector B) := by
    change mixedMoment B node5256 node5256Labels = _
    exact sound5256 B hB hF
  have h5265 : mixedVector B (Sum.inr 5265) = Sparse.eval nodeValue5265 (mixedVector B) := by
    change mixedMoment B node5265 node5265Labels = _
    exact sound5265 B hB hF
  have h5286 : mixedVector B (Sum.inr 5286) = Sparse.eval nodeValue5286 (mixedVector B) := by
    change mixedMoment B node5286 node5286Labels = _
    exact sound5286 B hB hF
  have h5359 : mixedVector B (Sum.inr 5359) = Sparse.eval nodeValue5359 (mixedVector B) := by
    change mixedMoment B node5359 node5359Labels = _
    exact sound5359 B hB hF
  have h5360 : mixedVector B (Sum.inr 5360) = Sparse.eval nodeValue5360 (mixedVector B) := by
    change mixedMoment B node5360 node5360Labels = _
    exact sound5360 B hB hF
  have h5365 : mixedVector B (Sum.inr 5365) = Sparse.eval nodeValue5365 (mixedVector B) := by
    change mixedMoment B node5365 node5365Labels = _
    exact sound5365 B hB hF
  have h5405 : mixedVector B (Sum.inr 5405) = Sparse.eval nodeValue5405 (mixedVector B) := by
    change mixedMoment B node5405 node5405Labels = _
    exact sound5405 B hB hF
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
  have h5429 : mixedVector B (Sum.inr 5429) = Sparse.eval nodeValue5429 (mixedVector B) := by
    change mixedMoment B node5429 node5429Labels = _
    exact sound5429 B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434 B hB hF
  have h5435 : mixedVector B (Sum.inr 5435) = Sparse.eval nodeValue5435 (mixedVector B) := by
    change mixedMoment B node5435 node5435Labels = _
    exact sound5435 B hB hF
  simpa only [sourceForm966, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5085, h5086, h5098, h5254, h5256, h5265, h5286, h5359, h5360, h5365, h5405, h5406, h5407, h5410, h5411, h5412, h5429, h5434, h5435, reducedSource843] using sourceEq966 B hB

theorem rowSound843 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row843 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck843, numericCheck843, reducedZero843 B hB hF, mul_zero]

theorem reducedZero844 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource844 (mixedVector B) = 0 := by
  have h2974 : mixedVector B (Sum.inr 2974) = Sparse.eval nodeValue2974 (mixedVector B) := by
    change mixedMoment B node2974 node2974Labels = _
    exact sound2974 B hB hF
  have h2976 : mixedVector B (Sum.inr 2976) = Sparse.eval nodeValue2976 (mixedVector B) := by
    change mixedMoment B node2976 node2976Labels = _
    exact sound2976 B hB hF
  have h2996 : mixedVector B (Sum.inr 2996) = Sparse.eval nodeValue2996 (mixedVector B) := by
    change mixedMoment B node2996 node2996Labels = _
    exact sound2996 B hB hF
  have h3037 : mixedVector B (Sum.inr 3037) = Sparse.eval nodeValue3037 (mixedVector B) := by
    change mixedMoment B node3037 node3037Labels = _
    exact sound3037 B hB hF
  have h3525 : mixedVector B (Sum.inr 3525) = Sparse.eval nodeValue3525 (mixedVector B) := by
    change mixedMoment B node3525 node3525Labels = _
    exact sound3525 B hB hF
  have h3526 : mixedVector B (Sum.inr 3526) = Sparse.eval nodeValue3526 (mixedVector B) := by
    change mixedMoment B node3526 node3526Labels = _
    exact sound3526 B hB hF
  have h3528 : mixedVector B (Sum.inr 3528) = Sparse.eval nodeValue3528 (mixedVector B) := by
    change mixedMoment B node3528 node3528Labels = _
    exact sound3528 B hB hF
  have h3567 : mixedVector B (Sum.inr 3567) = Sparse.eval nodeValue3567 (mixedVector B) := by
    change mixedMoment B node3567 node3567Labels = _
    exact sound3567 B hB hF
  have h3780 : mixedVector B (Sum.inr 3780) = Sparse.eval nodeValue3780 (mixedVector B) := by
    change mixedMoment B node3780 node3780Labels = _
    exact sound3780 B hB hF
  have h3800 : mixedVector B (Sum.inr 3800) = Sparse.eval nodeValue3800 (mixedVector B) := by
    change mixedMoment B node3800 node3800Labels = _
    exact sound3800 B hB hF
  have h3801 : mixedVector B (Sum.inr 3801) = Sparse.eval nodeValue3801 (mixedVector B) := by
    change mixedMoment B node3801 node3801Labels = _
    exact sound3801 B hB hF
  have h3803 : mixedVector B (Sum.inr 3803) = Sparse.eval nodeValue3803 (mixedVector B) := by
    change mixedMoment B node3803 node3803Labels = _
    exact sound3803 B hB hF
  have h3846 : mixedVector B (Sum.inr 3846) = Sparse.eval nodeValue3846 (mixedVector B) := by
    change mixedMoment B node3846 node3846Labels = _
    exact sound3846 B hB hF
  have h3852 : mixedVector B (Sum.inr 3852) = Sparse.eval nodeValue3852 (mixedVector B) := by
    change mixedMoment B node3852 node3852Labels = _
    exact sound3852 B hB hF
  have h3853 : mixedVector B (Sum.inr 3853) = Sparse.eval nodeValue3853 (mixedVector B) := by
    change mixedMoment B node3853 node3853Labels = _
    exact sound3853 B hB hF
  have h3856 : mixedVector B (Sum.inr 3856) = Sparse.eval nodeValue3856 (mixedVector B) := by
    change mixedMoment B node3856 node3856Labels = _
    exact sound3856 B hB hF
  have h3878 : mixedVector B (Sum.inr 3878) = Sparse.eval nodeValue3878 (mixedVector B) := by
    change mixedMoment B node3878 node3878Labels = _
    exact sound3878 B hB hF
  have h3883 : mixedVector B (Sum.inr 3883) = Sparse.eval nodeValue3883 (mixedVector B) := by
    change mixedMoment B node3883 node3883Labels = _
    exact sound3883 B hB hF
  have h3938 : mixedVector B (Sum.inr 3938) = Sparse.eval nodeValue3938 (mixedVector B) := by
    change mixedMoment B node3938 node3938Labels = _
    exact sound3938 B hB hF
  have h3977 : mixedVector B (Sum.inr 3977) = Sparse.eval nodeValue3977 (mixedVector B) := by
    change mixedMoment B node3977 node3977Labels = _
    exact sound3977 B hB hF
  have h3996 : mixedVector B (Sum.inr 3996) = Sparse.eval nodeValue3996 (mixedVector B) := by
    change mixedMoment B node3996 node3996Labels = _
    exact sound3996 B hB hF
  simpa only [sourceForm967, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2974, h2976, h2996, h3037, h3525, h3526, h3528, h3567, h3780, h3800, h3801, h3803, h3846, h3852, h3853, h3856, h3878, h3883, h3938, h3977, h3996, reducedSource844] using sourceEq967 B hB

theorem rowSound844 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row844 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck844, numericCheck844, reducedZero844 B hB hF, mul_zero]

theorem reducedZero845 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource845 (mixedVector B) = 0 := by
  have h3016 : mixedVector B (Sum.inr 3016) = Sparse.eval nodeValue3016 (mixedVector B) := by
    change mixedMoment B node3016 node3016Labels = _
    exact sound3016 B hB hF
  have h3023 : mixedVector B (Sum.inr 3023) = Sparse.eval nodeValue3023 (mixedVector B) := by
    change mixedMoment B node3023 node3023Labels = _
    exact sound3023 B hB hF
  have h3037 : mixedVector B (Sum.inr 3037) = Sparse.eval nodeValue3037 (mixedVector B) := by
    change mixedMoment B node3037 node3037Labels = _
    exact sound3037 B hB hF
  have h3085 : mixedVector B (Sum.inr 3085) = Sparse.eval nodeValue3085 (mixedVector B) := by
    change mixedMoment B node3085 node3085Labels = _
    exact sound3085 B hB hF
  have h3460 : mixedVector B (Sum.inr 3460) = Sparse.eval nodeValue3460 (mixedVector B) := by
    change mixedMoment B node3460 node3460Labels = _
    exact sound3460 B hB hF
  have h3461 : mixedVector B (Sum.inr 3461) = Sparse.eval nodeValue3461 (mixedVector B) := by
    change mixedMoment B node3461 node3461Labels = _
    exact sound3461 B hB hF
  have h3464 : mixedVector B (Sum.inr 3464) = Sparse.eval nodeValue3464 (mixedVector B) := by
    change mixedMoment B node3464 node3464Labels = _
    exact sound3464 B hB hF
  have h3526 : mixedVector B (Sum.inr 3526) = Sparse.eval nodeValue3526 (mixedVector B) := by
    change mixedMoment B node3526 node3526Labels = _
    exact sound3526 B hB hF
  have h3758 : mixedVector B (Sum.inr 3758) = Sparse.eval nodeValue3758 (mixedVector B) := by
    change mixedMoment B node3758 node3758Labels = _
    exact sound3758 B hB hF
  have h3759 : mixedVector B (Sum.inr 3759) = Sparse.eval nodeValue3759 (mixedVector B) := by
    change mixedMoment B node3759 node3759Labels = _
    exact sound3759 B hB hF
  have h3762 : mixedVector B (Sum.inr 3762) = Sparse.eval nodeValue3762 (mixedVector B) := by
    change mixedMoment B node3762 node3762Labels = _
    exact sound3762 B hB hF
  have h3800 : mixedVector B (Sum.inr 3800) = Sparse.eval nodeValue3800 (mixedVector B) := by
    change mixedMoment B node3800 node3800Labels = _
    exact sound3800 B hB hF
  have h3803 : mixedVector B (Sum.inr 3803) = Sparse.eval nodeValue3803 (mixedVector B) := by
    change mixedMoment B node3803 node3803Labels = _
    exact sound3803 B hB hF
  have h3808 : mixedVector B (Sum.inr 3808) = Sparse.eval nodeValue3808 (mixedVector B) := by
    change mixedMoment B node3808 node3808Labels = _
    exact sound3808 B hB hF
  have h3809 : mixedVector B (Sum.inr 3809) = Sparse.eval nodeValue3809 (mixedVector B) := by
    change mixedMoment B node3809 node3809Labels = _
    exact sound3809 B hB hF
  have h3814 : mixedVector B (Sum.inr 3814) = Sparse.eval nodeValue3814 (mixedVector B) := by
    change mixedMoment B node3814 node3814Labels = _
    exact sound3814 B hB hF
  have h3847 : mixedVector B (Sum.inr 3847) = Sparse.eval nodeValue3847 (mixedVector B) := by
    change mixedMoment B node3847 node3847Labels = _
    exact sound3847 B hB hF
  have h3853 : mixedVector B (Sum.inr 3853) = Sparse.eval nodeValue3853 (mixedVector B) := by
    change mixedMoment B node3853 node3853Labels = _
    exact sound3853 B hB hF
  have h3954 : mixedVector B (Sum.inr 3954) = Sparse.eval nodeValue3954 (mixedVector B) := by
    change mixedMoment B node3954 node3954Labels = _
    exact sound3954 B hB hF
  have h3977 : mixedVector B (Sum.inr 3977) = Sparse.eval nodeValue3977 (mixedVector B) := by
    change mixedMoment B node3977 node3977Labels = _
    exact sound3977 B hB hF
  have h3982 : mixedVector B (Sum.inr 3982) = Sparse.eval nodeValue3982 (mixedVector B) := by
    change mixedMoment B node3982 node3982Labels = _
    exact sound3982 B hB hF
  simpa only [sourceForm968, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3016, h3023, h3037, h3085, h3460, h3461, h3464, h3526, h3758, h3759, h3762, h3800, h3803, h3808, h3809, h3814, h3847, h3853, h3954, h3977, h3982, reducedSource845] using sourceEq968 B hB

theorem rowSound845 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row845 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck845, numericCheck845, reducedZero845 B hB hF, mul_zero]

theorem reducedZero846 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource846 (mixedVector B) = 0 := by
  have h2508 : mixedVector B (Sum.inr 2508) = Sparse.eval nodeValue2508 (mixedVector B) := by
    change mixedMoment B node2508 node2508Labels = _
    exact sound2508 B hB hF
  have h3703 : mixedVector B (Sum.inr 3703) = Sparse.eval nodeValue3703 (mixedVector B) := by
    change mixedMoment B node3703 node3703Labels = _
    exact sound3703 B hB hF
  have h3805 : mixedVector B (Sum.inr 3805) = Sparse.eval nodeValue3805 (mixedVector B) := by
    change mixedMoment B node3805 node3805Labels = _
    exact sound3805 B hB hF
  have h3812 : mixedVector B (Sum.inr 3812) = Sparse.eval nodeValue3812 (mixedVector B) := by
    change mixedMoment B node3812 node3812Labels = _
    exact sound3812 B hB hF
  have h3816 : mixedVector B (Sum.inr 3816) = Sparse.eval nodeValue3816 (mixedVector B) := by
    change mixedMoment B node3816 node3816Labels = _
    exact sound3816 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm969, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2508, h3703, h3805, h3812, h3816, h4092, reducedSource846] using sourceEq969 B hB

theorem rowSound846 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row846 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck846, numericCheck846, reducedZero846 B hB hF, mul_zero]

theorem reducedZero847 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource847 (mixedVector B) = 0 := by
  have h2534 : mixedVector B (Sum.inr 2534) = Sparse.eval nodeValue2534 (mixedVector B) := by
    change mixedMoment B node2534 node2534Labels = _
    exact sound2534 B hB hF
  have h2535 : mixedVector B (Sum.inr 2535) = Sparse.eval nodeValue2535 (mixedVector B) := by
    change mixedMoment B node2535 node2535Labels = _
    exact sound2535 B hB hF
  have h2537 : mixedVector B (Sum.inr 2537) = Sparse.eval nodeValue2537 (mixedVector B) := by
    change mixedMoment B node2537 node2537Labels = _
    exact sound2537 B hB hF
  have h2587 : mixedVector B (Sum.inr 2587) = Sparse.eval nodeValue2587 (mixedVector B) := by
    change mixedMoment B node2587 node2587Labels = _
    exact sound2587 B hB hF
  have h2669 : mixedVector B (Sum.inr 2669) = Sparse.eval nodeValue2669 (mixedVector B) := by
    change mixedMoment B node2669 node2669Labels = _
    exact sound2669 B hB hF
  have h3431 : mixedVector B (Sum.inr 3431) = Sparse.eval nodeValue3431 (mixedVector B) := by
    change mixedMoment B node3431 node3431Labels = _
    exact sound3431 B hB hF
  have h3434 : mixedVector B (Sum.inr 3434) = Sparse.eval nodeValue3434 (mixedVector B) := by
    change mixedMoment B node3434 node3434Labels = _
    exact sound3434 B hB hF
  have h3463 : mixedVector B (Sum.inr 3463) = Sparse.eval nodeValue3463 (mixedVector B) := by
    change mixedMoment B node3463 node3463Labels = _
    exact sound3463 B hB hF
  have h3529 : mixedVector B (Sum.inr 3529) = Sparse.eval nodeValue3529 (mixedVector B) := by
    change mixedMoment B node3529 node3529Labels = _
    exact sound3529 B hB hF
  have h3531 : mixedVector B (Sum.inr 3531) = Sparse.eval nodeValue3531 (mixedVector B) := by
    change mixedMoment B node3531 node3531Labels = _
    exact sound3531 B hB hF
  have h3536 : mixedVector B (Sum.inr 3536) = Sparse.eval nodeValue3536 (mixedVector B) := by
    change mixedMoment B node3536 node3536Labels = _
    exact sound3536 B hB hF
  have h3540 : mixedVector B (Sum.inr 3540) = Sparse.eval nodeValue3540 (mixedVector B) := by
    change mixedMoment B node3540 node3540Labels = _
    exact sound3540 B hB hF
  have h3568 : mixedVector B (Sum.inr 3568) = Sparse.eval nodeValue3568 (mixedVector B) := by
    change mixedMoment B node3568 node3568Labels = _
    exact sound3568 B hB hF
  have h3743 : mixedVector B (Sum.inr 3743) = Sparse.eval nodeValue3743 (mixedVector B) := by
    change mixedMoment B node3743 node3743Labels = _
    exact sound3743 B hB hF
  have h3761 : mixedVector B (Sum.inr 3761) = Sparse.eval nodeValue3761 (mixedVector B) := by
    change mixedMoment B node3761 node3761Labels = _
    exact sound3761 B hB hF
  have h3804 : mixedVector B (Sum.inr 3804) = Sparse.eval nodeValue3804 (mixedVector B) := by
    change mixedMoment B node3804 node3804Labels = _
    exact sound3804 B hB hF
  have h3805 : mixedVector B (Sum.inr 3805) = Sparse.eval nodeValue3805 (mixedVector B) := by
    change mixedMoment B node3805 node3805Labels = _
    exact sound3805 B hB hF
  have h3840 : mixedVector B (Sum.inr 3840) = Sparse.eval nodeValue3840 (mixedVector B) := by
    change mixedMoment B node3840 node3840Labels = _
    exact sound3840 B hB hF
  have h3848 : mixedVector B (Sum.inr 3848) = Sparse.eval nodeValue3848 (mixedVector B) := by
    change mixedMoment B node3848 node3848Labels = _
    exact sound3848 B hB hF
  have h3849 : mixedVector B (Sum.inr 3849) = Sparse.eval nodeValue3849 (mixedVector B) := by
    change mixedMoment B node3849 node3849Labels = _
    exact sound3849 B hB hF
  have h3851 : mixedVector B (Sum.inr 3851) = Sparse.eval nodeValue3851 (mixedVector B) := by
    change mixedMoment B node3851 node3851Labels = _
    exact sound3851 B hB hF
  have h3857 : mixedVector B (Sum.inr 3857) = Sparse.eval nodeValue3857 (mixedVector B) := by
    change mixedMoment B node3857 node3857Labels = _
    exact sound3857 B hB hF
  have h3858 : mixedVector B (Sum.inr 3858) = Sparse.eval nodeValue3858 (mixedVector B) := by
    change mixedMoment B node3858 node3858Labels = _
    exact sound3858 B hB hF
  have h3879 : mixedVector B (Sum.inr 3879) = Sparse.eval nodeValue3879 (mixedVector B) := by
    change mixedMoment B node3879 node3879Labels = _
    exact sound3879 B hB hF
  have h3880 : mixedVector B (Sum.inr 3880) = Sparse.eval nodeValue3880 (mixedVector B) := by
    change mixedMoment B node3880 node3880Labels = _
    exact sound3880 B hB hF
  have h3884 : mixedVector B (Sum.inr 3884) = Sparse.eval nodeValue3884 (mixedVector B) := by
    change mixedMoment B node3884 node3884Labels = _
    exact sound3884 B hB hF
  have h3927 : mixedVector B (Sum.inr 3927) = Sparse.eval nodeValue3927 (mixedVector B) := by
    change mixedMoment B node3927 node3927Labels = _
    exact sound3927 B hB hF
  have h3978 : mixedVector B (Sum.inr 3978) = Sparse.eval nodeValue3978 (mixedVector B) := by
    change mixedMoment B node3978 node3978Labels = _
    exact sound3978 B hB hF
  have h3994 : mixedVector B (Sum.inr 3994) = Sparse.eval nodeValue3994 (mixedVector B) := by
    change mixedMoment B node3994 node3994Labels = _
    exact sound3994 B hB hF
  have h3997 : mixedVector B (Sum.inr 3997) = Sparse.eval nodeValue3997 (mixedVector B) := by
    change mixedMoment B node3997 node3997Labels = _
    exact sound3997 B hB hF
  simpa only [sourceForm972, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2534, h2535, h2537, h2587, h2669, h3431, h3434, h3463, h3529, h3531, h3536, h3540, h3568, h3743, h3761, h3804, h3805, h3840, h3848, h3849, h3851, h3857, h3858, h3879, h3880, h3884, h3927, h3978, h3994, h3997, reducedSource847] using sourceEq972 B hB

theorem rowSound847 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row847 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck847, numericCheck847, reducedZero847 B hB hF, mul_zero]

theorem sourceRowsAt832 : MixedData.sourceRows (832 : Fin 2425) =
    MixedData.row832 := by decide +kernel

theorem sourceRowsAt833 : MixedData.sourceRows (833 : Fin 2425) =
    MixedData.row833 := by decide +kernel

theorem sourceRowsAt834 : MixedData.sourceRows (834 : Fin 2425) =
    MixedData.row834 := by decide +kernel

theorem sourceRowsAt835 : MixedData.sourceRows (835 : Fin 2425) =
    MixedData.row835 := by decide +kernel

theorem sourceRowsAt836 : MixedData.sourceRows (836 : Fin 2425) =
    MixedData.row836 := by decide +kernel

theorem sourceRowsAt837 : MixedData.sourceRows (837 : Fin 2425) =
    MixedData.row837 := by decide +kernel

theorem sourceRowsAt838 : MixedData.sourceRows (838 : Fin 2425) =
    MixedData.row838 := by decide +kernel

theorem sourceRowsAt839 : MixedData.sourceRows (839 : Fin 2425) =
    MixedData.row839 := by decide +kernel

theorem sourceRowsAt840 : MixedData.sourceRows (840 : Fin 2425) =
    MixedData.row840 := by decide +kernel

theorem sourceRowsAt841 : MixedData.sourceRows (841 : Fin 2425) =
    MixedData.row841 := by decide +kernel

theorem sourceRowsAt842 : MixedData.sourceRows (842 : Fin 2425) =
    MixedData.row842 := by decide +kernel

theorem sourceRowsAt843 : MixedData.sourceRows (843 : Fin 2425) =
    MixedData.row843 := by decide +kernel

theorem sourceRowsAt844 : MixedData.sourceRows (844 : Fin 2425) =
    MixedData.row844 := by decide +kernel

theorem sourceRowsAt845 : MixedData.sourceRows (845 : Fin 2425) =
    MixedData.row845 := by decide +kernel

theorem sourceRowsAt846 : MixedData.sourceRows (846 : Fin 2425) =
    MixedData.row846 := by decide +kernel

theorem sourceRowsAt847 : MixedData.sourceRows (847 : Fin 2425) =
    MixedData.row847 := by decide +kernel

theorem chunkSound52 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 52) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 832 ∨ k.val = 833 ∨ k.val = 834 ∨ k.val = 835 ∨ k.val = 836 ∨ k.val = 837 ∨ k.val = 838 ∨ k.val = 839 ∨ k.val = 840 ∨ k.val = 841 ∨ k.val = 842 ∨ k.val = 843 ∨ k.val = 844 ∨ k.val = 845 ∨ k.val = 846 ∨ k.val = 847 := by omega
  rcases heq with h832 | h833 | h834 | h835 | h836 | h837 | h838 | h839 | h840 | h841 | h842 | h843 | h844 | h845 | h846 | h847
  · have he : k = (832 : Fin 2425) := Fin.ext h832
    subst k
    rw [sourceRowsAt832]
    exact rowSound832 B hB hF
  · have he : k = (833 : Fin 2425) := Fin.ext h833
    subst k
    rw [sourceRowsAt833]
    exact rowSound833 B hB hF
  · have he : k = (834 : Fin 2425) := Fin.ext h834
    subst k
    rw [sourceRowsAt834]
    exact rowSound834 B hB hF
  · have he : k = (835 : Fin 2425) := Fin.ext h835
    subst k
    rw [sourceRowsAt835]
    exact rowSound835 B hB hF
  · have he : k = (836 : Fin 2425) := Fin.ext h836
    subst k
    rw [sourceRowsAt836]
    exact rowSound836 B hB hF
  · have he : k = (837 : Fin 2425) := Fin.ext h837
    subst k
    rw [sourceRowsAt837]
    exact rowSound837 B hB hF
  · have he : k = (838 : Fin 2425) := Fin.ext h838
    subst k
    rw [sourceRowsAt838]
    exact rowSound838 B hB hF
  · have he : k = (839 : Fin 2425) := Fin.ext h839
    subst k
    rw [sourceRowsAt839]
    exact rowSound839 B hB hF
  · have he : k = (840 : Fin 2425) := Fin.ext h840
    subst k
    rw [sourceRowsAt840]
    exact rowSound840 B hB hF
  · have he : k = (841 : Fin 2425) := Fin.ext h841
    subst k
    rw [sourceRowsAt841]
    exact rowSound841 B hB hF
  · have he : k = (842 : Fin 2425) := Fin.ext h842
    subst k
    rw [sourceRowsAt842]
    exact rowSound842 B hB hF
  · have he : k = (843 : Fin 2425) := Fin.ext h843
    subst k
    rw [sourceRowsAt843]
    exact rowSound843 B hB hF
  · have he : k = (844 : Fin 2425) := Fin.ext h844
    subst k
    rw [sourceRowsAt844]
    exact rowSound844 B hB hF
  · have he : k = (845 : Fin 2425) := Fin.ext h845
    subst k
    rw [sourceRowsAt845]
    exact rowSound845 B hB hF
  · have he : k = (846 : Fin 2425) := Fin.ext h846
    subst k
    rw [sourceRowsAt846]
    exact rowSound846 B hB hF
  · have he : k = (847 : Fin 2425) := Fin.ext h847
    subst k
    rw [sourceRowsAt847]
    exact rowSound847 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
