import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources28

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero768 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource768 (mixedVector B) = 0 := by
  have h2544 : mixedVector B (Sum.inr 2544) = Sparse.eval nodeValue2544 (mixedVector B) := by
    change mixedMoment B node2544 node2544Labels = _
    exact sound2544 B hB hF
  have h3168 : mixedVector B (Sum.inr 3168) = Sparse.eval nodeValue3168 (mixedVector B) := by
    change mixedMoment B node3168 node3168Labels = _
    exact sound3168 B hB hF
  have h3170 : mixedVector B (Sum.inr 3170) = Sparse.eval nodeValue3170 (mixedVector B) := by
    change mixedMoment B node3170 node3170Labels = _
    exact sound3170 B hB hF
  have h3175 : mixedVector B (Sum.inr 3175) = Sparse.eval nodeValue3175 (mixedVector B) := by
    change mixedMoment B node3175 node3175Labels = _
    exact sound3175 B hB hF
  have h3196 : mixedVector B (Sum.inr 3196) = Sparse.eval nodeValue3196 (mixedVector B) := by
    change mixedMoment B node3196 node3196Labels = _
    exact sound3196 B hB hF
  have h3839 : mixedVector B (Sum.inr 3839) = Sparse.eval nodeValue3839 (mixedVector B) := by
    change mixedMoment B node3839 node3839Labels = _
    exact sound3839 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm879, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2544, h3168, h3170, h3175, h3196, h3839, h4092, reducedSource768] using sourceEq879 B hB

theorem rowSound768 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row768 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck768, numericCheck768, reducedZero768 B hB hF, mul_zero]

theorem reducedZero769 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource769 (mixedVector B) = 0 := by
  have h1991 : mixedVector B (Sum.inr 1991) = Sparse.eval nodeValue1991 (mixedVector B) := by
    change mixedMoment B node1991 node1991Labels = _
    exact sound1991 B hB hF
  have h1994 : mixedVector B (Sum.inr 1994) = Sparse.eval nodeValue1994 (mixedVector B) := by
    change mixedMoment B node1994 node1994Labels = _
    exact sound1994 B hB hF
  have h1998 : mixedVector B (Sum.inr 1998) = Sparse.eval nodeValue1998 (mixedVector B) := by
    change mixedMoment B node1998 node1998Labels = _
    exact sound1998 B hB hF
  have h2033 : mixedVector B (Sum.inr 2033) = Sparse.eval nodeValue2033 (mixedVector B) := by
    change mixedMoment B node2033 node2033Labels = _
    exact sound2033 B hB hF
  have h2195 : mixedVector B (Sum.inr 2195) = Sparse.eval nodeValue2195 (mixedVector B) := by
    change mixedMoment B node2195 node2195Labels = _
    exact sound2195 B hB hF
  have h2533 : mixedVector B (Sum.inr 2533) = Sparse.eval nodeValue2533 (mixedVector B) := by
    change mixedMoment B node2533 node2533Labels = _
    exact sound2533 B hB hF
  have h2535 : mixedVector B (Sum.inr 2535) = Sparse.eval nodeValue2535 (mixedVector B) := by
    change mixedMoment B node2535 node2535Labels = _
    exact sound2535 B hB hF
  have h2566 : mixedVector B (Sum.inr 2566) = Sparse.eval nodeValue2566 (mixedVector B) := by
    change mixedMoment B node2566 node2566Labels = _
    exact sound2566 B hB hF
  have h2661 : mixedVector B (Sum.inr 2661) = Sparse.eval nodeValue2661 (mixedVector B) := by
    change mixedMoment B node2661 node2661Labels = _
    exact sound2661 B hB hF
  have h3536 : mixedVector B (Sum.inr 3536) = Sparse.eval nodeValue3536 (mixedVector B) := by
    change mixedMoment B node3536 node3536Labels = _
    exact sound3536 B hB hF
  have h3537 : mixedVector B (Sum.inr 3537) = Sparse.eval nodeValue3537 (mixedVector B) := by
    change mixedMoment B node3537 node3537Labels = _
    exact sound3537 B hB hF
  have h3539 : mixedVector B (Sum.inr 3539) = Sparse.eval nodeValue3539 (mixedVector B) := by
    change mixedMoment B node3539 node3539Labels = _
    exact sound3539 B hB hF
  have h3574 : mixedVector B (Sum.inr 3574) = Sparse.eval nodeValue3574 (mixedVector B) := by
    change mixedMoment B node3574 node3574Labels = _
    exact sound3574 B hB hF
  have h3680 : mixedVector B (Sum.inr 3680) = Sparse.eval nodeValue3680 (mixedVector B) := by
    change mixedMoment B node3680 node3680Labels = _
    exact sound3680 B hB hF
  have h3697 : mixedVector B (Sum.inr 3697) = Sparse.eval nodeValue3697 (mixedVector B) := by
    change mixedMoment B node3697 node3697Labels = _
    exact sound3697 B hB hF
  have h3743 : mixedVector B (Sum.inr 3743) = Sparse.eval nodeValue3743 (mixedVector B) := by
    change mixedMoment B node3743 node3743Labels = _
    exact sound3743 B hB hF
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
  have h3848 : mixedVector B (Sum.inr 3848) = Sparse.eval nodeValue3848 (mixedVector B) := by
    change mixedMoment B node3848 node3848Labels = _
    exact sound3848 B hB hF
  have h3849 : mixedVector B (Sum.inr 3849) = Sparse.eval nodeValue3849 (mixedVector B) := by
    change mixedMoment B node3849 node3849Labels = _
    exact sound3849 B hB hF
  have h3851 : mixedVector B (Sum.inr 3851) = Sparse.eval nodeValue3851 (mixedVector B) := by
    change mixedMoment B node3851 node3851Labels = _
    exact sound3851 B hB hF
  have h3855 : mixedVector B (Sum.inr 3855) = Sparse.eval nodeValue3855 (mixedVector B) := by
    change mixedMoment B node3855 node3855Labels = _
    exact sound3855 B hB hF
  have h3871 : mixedVector B (Sum.inr 3871) = Sparse.eval nodeValue3871 (mixedVector B) := by
    change mixedMoment B node3871 node3871Labels = _
    exact sound3871 B hB hF
  have h3880 : mixedVector B (Sum.inr 3880) = Sparse.eval nodeValue3880 (mixedVector B) := by
    change mixedMoment B node3880 node3880Labels = _
    exact sound3880 B hB hF
  have h3994 : mixedVector B (Sum.inr 3994) = Sparse.eval nodeValue3994 (mixedVector B) := by
    change mixedMoment B node3994 node3994Labels = _
    exact sound3994 B hB hF
  simpa only [sourceForm882, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1991, h1994, h1998, h2033, h2195, h2533, h2535, h2566, h2661, h3536, h3537, h3539, h3574, h3680, h3697, h3743, h3761, h3810, h3812, h3825, h3829, h3840, h3848, h3849, h3851, h3855, h3871, h3880, h3994, reducedSource769] using sourceEq882 B hB

theorem rowSound769 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row769 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck769, numericCheck769, reducedZero769 B hB hF, mul_zero]

theorem reducedZero770 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource770 (mixedVector B) = 0 := by
  have h3871 : mixedVector B (Sum.inr 3871) = Sparse.eval nodeValue3871 (mixedVector B) := by
    change mixedMoment B node3871 node3871Labels = _
    exact sound3871 B hB hF
  have h3872 : mixedVector B (Sum.inr 3872) = Sparse.eval nodeValue3872 (mixedVector B) := by
    change mixedMoment B node3872 node3872Labels = _
    exact sound3872 B hB hF
  have h3875 : mixedVector B (Sum.inr 3875) = Sparse.eval nodeValue3875 (mixedVector B) := by
    change mixedMoment B node3875 node3875Labels = _
    exact sound3875 B hB hF
  have h3880 : mixedVector B (Sum.inr 3880) = Sparse.eval nodeValue3880 (mixedVector B) := by
    change mixedMoment B node3880 node3880Labels = _
    exact sound3880 B hB hF
  have h3901 : mixedVector B (Sum.inr 3901) = Sparse.eval nodeValue3901 (mixedVector B) := by
    change mixedMoment B node3901 node3901Labels = _
    exact sound3901 B hB hF
  have h3974 : mixedVector B (Sum.inr 3974) = Sparse.eval nodeValue3974 (mixedVector B) := by
    change mixedMoment B node3974 node3974Labels = _
    exact sound3974 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm883, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3871, h3872, h3875, h3880, h3901, h3974, h4091, reducedSource770] using sourceEq883 B hB

theorem rowSound770 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row770 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck770, numericCheck770, reducedZero770 B hB hF, mul_zero]

theorem reducedZero771 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource771 (mixedVector B) = 0 := by
  have h2611 : mixedVector B (Sum.inr 2611) = Sparse.eval nodeValue2611 (mixedVector B) := by
    change mixedMoment B node2611 node2611Labels = _
    exact sound2611 B hB hF
  have h2919 : mixedVector B (Sum.inr 2919) = Sparse.eval nodeValue2919 (mixedVector B) := by
    change mixedMoment B node2919 node2919Labels = _
    exact sound2919 B hB hF
  have h3195 : mixedVector B (Sum.inr 3195) = Sparse.eval nodeValue3195 (mixedVector B) := by
    change mixedMoment B node3195 node3195Labels = _
    exact sound3195 B hB hF
  have h3197 : mixedVector B (Sum.inr 3197) = Sparse.eval nodeValue3197 (mixedVector B) := by
    change mixedMoment B node3197 node3197Labels = _
    exact sound3197 B hB hF
  have h3202 : mixedVector B (Sum.inr 3202) = Sparse.eval nodeValue3202 (mixedVector B) := by
    change mixedMoment B node3202 node3202Labels = _
    exact sound3202 B hB hF
  have h3872 : mixedVector B (Sum.inr 3872) = Sparse.eval nodeValue3872 (mixedVector B) := by
    change mixedMoment B node3872 node3872Labels = _
    exact sound3872 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm884, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2611, h2919, h3195, h3197, h3202, h3872, h4091, reducedSource771] using sourceEq884 B hB

theorem rowSound771 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row771 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck771, numericCheck771, reducedZero771 B hB hF, mul_zero]

theorem reducedZero772 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource772 (mixedVector B) = 0 := by
  have h3197 : mixedVector B (Sum.inr 3197) = Sparse.eval nodeValue3197 (mixedVector B) := by
    change mixedMoment B node3197 node3197Labels = _
    exact sound3197 B hB hF
  have h3872 : mixedVector B (Sum.inr 3872) = Sparse.eval nodeValue3872 (mixedVector B) := by
    change mixedMoment B node3872 node3872Labels = _
    exact sound3872 B hB hF
  have h3878 : mixedVector B (Sum.inr 3878) = Sparse.eval nodeValue3878 (mixedVector B) := by
    change mixedMoment B node3878 node3878Labels = _
    exact sound3878 B hB hF
  have h3899 : mixedVector B (Sum.inr 3899) = Sparse.eval nodeValue3899 (mixedVector B) := by
    change mixedMoment B node3899 node3899Labels = _
    exact sound3899 B hB hF
  have h3964 : mixedVector B (Sum.inr 3964) = Sparse.eval nodeValue3964 (mixedVector B) := by
    change mixedMoment B node3964 node3964Labels = _
    exact sound3964 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm885, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3197, h3872, h3878, h3899, h3964, h4091, reducedSource772] using sourceEq885 B hB

theorem rowSound772 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row772 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck772, numericCheck772, reducedZero772 B hB hF, mul_zero]

theorem reducedZero773 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource773 (mixedVector B) = 0 := by
  have h2612 : mixedVector B (Sum.inr 2612) = Sparse.eval nodeValue2612 (mixedVector B) := by
    change mixedMoment B node2612 node2612Labels = _
    exact sound2612 B hB hF
  have h2945 : mixedVector B (Sum.inr 2945) = Sparse.eval nodeValue2945 (mixedVector B) := by
    change mixedMoment B node2945 node2945Labels = _
    exact sound2945 B hB hF
  have h3783 : mixedVector B (Sum.inr 3783) = Sparse.eval nodeValue3783 (mixedVector B) := by
    change mixedMoment B node3783 node3783Labels = _
    exact sound3783 B hB hF
  have h3863 : mixedVector B (Sum.inr 3863) = Sparse.eval nodeValue3863 (mixedVector B) := by
    change mixedMoment B node3863 node3863Labels = _
    exact sound3863 B hB hF
  have h3871 : mixedVector B (Sum.inr 3871) = Sparse.eval nodeValue3871 (mixedVector B) := by
    change mixedMoment B node3871 node3871Labels = _
    exact sound3871 B hB hF
  have h3872 : mixedVector B (Sum.inr 3872) = Sparse.eval nodeValue3872 (mixedVector B) := by
    change mixedMoment B node3872 node3872Labels = _
    exact sound3872 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm886, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2612, h2945, h3783, h3863, h3871, h3872, h4091, reducedSource773] using sourceEq886 B hB

theorem rowSound773 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row773 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck773, numericCheck773, reducedZero773 B hB hF, mul_zero]

theorem reducedZero774 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource774 (mixedVector B) = 0 := by
  have h3202 : mixedVector B (Sum.inr 3202) = Sparse.eval nodeValue3202 (mixedVector B) := by
    change mixedMoment B node3202 node3202Labels = _
    exact sound3202 B hB hF
  have h3783 : mixedVector B (Sum.inr 3783) = Sparse.eval nodeValue3783 (mixedVector B) := by
    change mixedMoment B node3783 node3783Labels = _
    exact sound3783 B hB hF
  have h3789 : mixedVector B (Sum.inr 3789) = Sparse.eval nodeValue3789 (mixedVector B) := by
    change mixedMoment B node3789 node3789Labels = _
    exact sound3789 B hB hF
  have h3801 : mixedVector B (Sum.inr 3801) = Sparse.eval nodeValue3801 (mixedVector B) := by
    change mixedMoment B node3801 node3801Labels = _
    exact sound3801 B hB hF
  have h3872 : mixedVector B (Sum.inr 3872) = Sparse.eval nodeValue3872 (mixedVector B) := by
    change mixedMoment B node3872 node3872Labels = _
    exact sound3872 B hB hF
  have h3972 : mixedVector B (Sum.inr 3972) = Sparse.eval nodeValue3972 (mixedVector B) := by
    change mixedMoment B node3972 node3972Labels = _
    exact sound3972 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm887, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3202, h3783, h3789, h3801, h3872, h3972, h4091, reducedSource774] using sourceEq887 B hB

theorem rowSound774 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row774 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck774, numericCheck774, reducedZero774 B hB hF, mul_zero]

theorem reducedZero775 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource775 (mixedVector B) = 0 := by
  have h2623 : mixedVector B (Sum.inr 2623) = Sparse.eval nodeValue2623 (mixedVector B) := by
    change mixedMoment B node2623 node2623Labels = _
    exact sound2623 B hB hF
  have h2920 : mixedVector B (Sum.inr 2920) = Sparse.eval nodeValue2920 (mixedVector B) := by
    change mixedMoment B node2920 node2920Labels = _
    exact sound2920 B hB hF
  have h3865 : mixedVector B (Sum.inr 3865) = Sparse.eval nodeValue3865 (mixedVector B) := by
    change mixedMoment B node3865 node3865Labels = _
    exact sound3865 B hB hF
  have h3872 : mixedVector B (Sum.inr 3872) = Sparse.eval nodeValue3872 (mixedVector B) := by
    change mixedMoment B node3872 node3872Labels = _
    exact sound3872 B hB hF
  have h3878 : mixedVector B (Sum.inr 3878) = Sparse.eval nodeValue3878 (mixedVector B) := by
    change mixedMoment B node3878 node3878Labels = _
    exact sound3878 B hB hF
  have h3880 : mixedVector B (Sum.inr 3880) = Sparse.eval nodeValue3880 (mixedVector B) := by
    change mixedMoment B node3880 node3880Labels = _
    exact sound3880 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm888, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2623, h2920, h3865, h3872, h3878, h3880, h4091, reducedSource775] using sourceEq888 B hB

theorem rowSound775 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row775 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck775, numericCheck775, reducedZero775 B hB hF, mul_zero]

theorem reducedZero776 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource776 (mixedVector B) = 0 := by
  have h3195 : mixedVector B (Sum.inr 3195) = Sparse.eval nodeValue3195 (mixedVector B) := by
    change mixedMoment B node3195 node3195Labels = _
    exact sound3195 B hB hF
  have h3863 : mixedVector B (Sum.inr 3863) = Sparse.eval nodeValue3863 (mixedVector B) := by
    change mixedMoment B node3863 node3863Labels = _
    exact sound3863 B hB hF
  have h3865 : mixedVector B (Sum.inr 3865) = Sparse.eval nodeValue3865 (mixedVector B) := by
    change mixedMoment B node3865 node3865Labels = _
    exact sound3865 B hB hF
  have h3872 : mixedVector B (Sum.inr 3872) = Sparse.eval nodeValue3872 (mixedVector B) := by
    change mixedMoment B node3872 node3872Labels = _
    exact sound3872 B hB hF
  have h3922 : mixedVector B (Sum.inr 3922) = Sparse.eval nodeValue3922 (mixedVector B) := by
    change mixedMoment B node3922 node3922Labels = _
    exact sound3922 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm889, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3195, h3863, h3865, h3872, h3922, h4091, reducedSource776] using sourceEq889 B hB

theorem rowSound776 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row776 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck776, numericCheck776, reducedZero776 B hB hF, mul_zero]

theorem reducedZero777 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource777 (mixedVector B) = 0 := by
  have h2617 : mixedVector B (Sum.inr 2617) = Sparse.eval nodeValue2617 (mixedVector B) := by
    change mixedMoment B node2617 node2617Labels = _
    exact sound2617 B hB hF
  have h3069 : mixedVector B (Sum.inr 3069) = Sparse.eval nodeValue3069 (mixedVector B) := by
    change mixedMoment B node3069 node3069Labels = _
    exact sound3069 B hB hF
  have h3789 : mixedVector B (Sum.inr 3789) = Sparse.eval nodeValue3789 (mixedVector B) := by
    change mixedMoment B node3789 node3789Labels = _
    exact sound3789 B hB hF
  have h3872 : mixedVector B (Sum.inr 3872) = Sparse.eval nodeValue3872 (mixedVector B) := by
    change mixedMoment B node3872 node3872Labels = _
    exact sound3872 B hB hF
  have h3875 : mixedVector B (Sum.inr 3875) = Sparse.eval nodeValue3875 (mixedVector B) := by
    change mixedMoment B node3875 node3875Labels = _
    exact sound3875 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm890, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2617, h3069, h3789, h3872, h3875, h4091, reducedSource777] using sourceEq890 B hB

theorem rowSound777 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row777 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck777, numericCheck777, reducedZero777 B hB hF, mul_zero]

theorem reducedZero778 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource778 (mixedVector B) = 0 := by
  have h2919 : mixedVector B (Sum.inr 2919) = Sparse.eval nodeValue2919 (mixedVector B) := by
    change mixedMoment B node2919 node2919Labels = _
    exact sound2919 B hB hF
  have h2920 : mixedVector B (Sum.inr 2920) = Sparse.eval nodeValue2920 (mixedVector B) := by
    change mixedMoment B node2920 node2920Labels = _
    exact sound2920 B hB hF
  have h2928 : mixedVector B (Sum.inr 2928) = Sparse.eval nodeValue2928 (mixedVector B) := by
    change mixedMoment B node2928 node2928Labels = _
    exact sound2928 B hB hF
  have h2945 : mixedVector B (Sum.inr 2945) = Sparse.eval nodeValue2945 (mixedVector B) := by
    change mixedMoment B node2945 node2945Labels = _
    exact sound2945 B hB hF
  have h3069 : mixedVector B (Sum.inr 3069) = Sparse.eval nodeValue3069 (mixedVector B) := by
    change mixedMoment B node3069 node3069Labels = _
    exact sound3069 B hB hF
  have h3872 : mixedVector B (Sum.inr 3872) = Sparse.eval nodeValue3872 (mixedVector B) := by
    change mixedMoment B node3872 node3872Labels = _
    exact sound3872 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm891, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2919, h2920, h2928, h2945, h3069, h3872, h4091, reducedSource778] using sourceEq891 B hB

theorem rowSound778 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row778 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck778, numericCheck778, reducedZero778 B hB hF, mul_zero]

theorem reducedZero779 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource779 (mixedVector B) = 0 := by
  have h2906 : mixedVector B (Sum.inr 2906) = Sparse.eval nodeValue2906 (mixedVector B) := by
    change mixedMoment B node2906 node2906Labels = _
    exact sound2906 B hB hF
  have h2907 : mixedVector B (Sum.inr 2907) = Sparse.eval nodeValue2907 (mixedVector B) := by
    change mixedMoment B node2907 node2907Labels = _
    exact sound2907 B hB hF
  have h2909 : mixedVector B (Sum.inr 2909) = Sparse.eval nodeValue2909 (mixedVector B) := by
    change mixedMoment B node2909 node2909Labels = _
    exact sound2909 B hB hF
  have h2951 : mixedVector B (Sum.inr 2951) = Sparse.eval nodeValue2951 (mixedVector B) := by
    change mixedMoment B node2951 node2951Labels = _
    exact sound2951 B hB hF
  have h3051 : mixedVector B (Sum.inr 3051) = Sparse.eval nodeValue3051 (mixedVector B) := by
    change mixedMoment B node3051 node3051Labels = _
    exact sound3051 B hB hF
  have h3430 : mixedVector B (Sum.inr 3430) = Sparse.eval nodeValue3430 (mixedVector B) := by
    change mixedMoment B node3430 node3430Labels = _
    exact sound3430 B hB hF
  have h3437 : mixedVector B (Sum.inr 3437) = Sparse.eval nodeValue3437 (mixedVector B) := by
    change mixedMoment B node3437 node3437Labels = _
    exact sound3437 B hB hF
  have h3464 : mixedVector B (Sum.inr 3464) = Sparse.eval nodeValue3464 (mixedVector B) := by
    change mixedMoment B node3464 node3464Labels = _
    exact sound3464 B hB hF
  have h3515 : mixedVector B (Sum.inr 3515) = Sparse.eval nodeValue3515 (mixedVector B) := by
    change mixedMoment B node3515 node3515Labels = _
    exact sound3515 B hB hF
  have h3518 : mixedVector B (Sum.inr 3518) = Sparse.eval nodeValue3518 (mixedVector B) := by
    change mixedMoment B node3518 node3518Labels = _
    exact sound3518 B hB hF
  have h3535 : mixedVector B (Sum.inr 3535) = Sparse.eval nodeValue3535 (mixedVector B) := by
    change mixedMoment B node3535 node3535Labels = _
    exact sound3535 B hB hF
  have h3541 : mixedVector B (Sum.inr 3541) = Sparse.eval nodeValue3541 (mixedVector B) := by
    change mixedMoment B node3541 node3541Labels = _
    exact sound3541 B hB hF
  have h3559 : mixedVector B (Sum.inr 3559) = Sparse.eval nodeValue3559 (mixedVector B) := by
    change mixedMoment B node3559 node3559Labels = _
    exact sound3559 B hB hF
  have h3712 : mixedVector B (Sum.inr 3712) = Sparse.eval nodeValue3712 (mixedVector B) := by
    change mixedMoment B node3712 node3712Labels = _
    exact sound3712 B hB hF
  have h3714 : mixedVector B (Sum.inr 3714) = Sparse.eval nodeValue3714 (mixedVector B) := by
    change mixedMoment B node3714 node3714Labels = _
    exact sound3714 B hB hF
  have h3730 : mixedVector B (Sum.inr 3730) = Sparse.eval nodeValue3730 (mixedVector B) := by
    change mixedMoment B node3730 node3730Labels = _
    exact sound3730 B hB hF
  have h3762 : mixedVector B (Sum.inr 3762) = Sparse.eval nodeValue3762 (mixedVector B) := by
    change mixedMoment B node3762 node3762Labels = _
    exact sound3762 B hB hF
  have h3794 : mixedVector B (Sum.inr 3794) = Sparse.eval nodeValue3794 (mixedVector B) := by
    change mixedMoment B node3794 node3794Labels = _
    exact sound3794 B hB hF
  have h3809 : mixedVector B (Sum.inr 3809) = Sparse.eval nodeValue3809 (mixedVector B) := by
    change mixedMoment B node3809 node3809Labels = _
    exact sound3809 B hB hF
  have h3832 : mixedVector B (Sum.inr 3832) = Sparse.eval nodeValue3832 (mixedVector B) := by
    change mixedMoment B node3832 node3832Labels = _
    exact sound3832 B hB hF
  have h3838 : mixedVector B (Sum.inr 3838) = Sparse.eval nodeValue3838 (mixedVector B) := by
    change mixedMoment B node3838 node3838Labels = _
    exact sound3838 B hB hF
  have h3841 : mixedVector B (Sum.inr 3841) = Sparse.eval nodeValue3841 (mixedVector B) := by
    change mixedMoment B node3841 node3841Labels = _
    exact sound3841 B hB hF
  have h3845 : mixedVector B (Sum.inr 3845) = Sparse.eval nodeValue3845 (mixedVector B) := by
    change mixedMoment B node3845 node3845Labels = _
    exact sound3845 B hB hF
  have h3853 : mixedVector B (Sum.inr 3853) = Sparse.eval nodeValue3853 (mixedVector B) := by
    change mixedMoment B node3853 node3853Labels = _
    exact sound3853 B hB hF
  have h3862 : mixedVector B (Sum.inr 3862) = Sparse.eval nodeValue3862 (mixedVector B) := by
    change mixedMoment B node3862 node3862Labels = _
    exact sound3862 B hB hF
  have h3872 : mixedVector B (Sum.inr 3872) = Sparse.eval nodeValue3872 (mixedVector B) := by
    change mixedMoment B node3872 node3872Labels = _
    exact sound3872 B hB hF
  have h3877 : mixedVector B (Sum.inr 3877) = Sparse.eval nodeValue3877 (mixedVector B) := by
    change mixedMoment B node3877 node3877Labels = _
    exact sound3877 B hB hF
  have h3972 : mixedVector B (Sum.inr 3972) = Sparse.eval nodeValue3972 (mixedVector B) := by
    change mixedMoment B node3972 node3972Labels = _
    exact sound3972 B hB hF
  have h3990 : mixedVector B (Sum.inr 3990) = Sparse.eval nodeValue3990 (mixedVector B) := by
    change mixedMoment B node3990 node3990Labels = _
    exact sound3990 B hB hF
  have h3993 : mixedVector B (Sum.inr 3993) = Sparse.eval nodeValue3993 (mixedVector B) := by
    change mixedMoment B node3993 node3993Labels = _
    exact sound3993 B hB hF
  simpa only [sourceForm893, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2906, h2907, h2909, h2951, h3051, h3430, h3437, h3464, h3515, h3518, h3535, h3541, h3559, h3712, h3714, h3730, h3762, h3794, h3809, h3832, h3838, h3841, h3845, h3853, h3862, h3872, h3877, h3972, h3990, h3993, reducedSource779] using sourceEq893 B hB

theorem rowSound779 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row779 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck779, numericCheck779, reducedZero779 B hB hF, mul_zero]

theorem reducedZero780 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource780 (mixedVector B) = 0 := by
  have h2454 : mixedVector B (Sum.inr 2454) = Sparse.eval nodeValue2454 (mixedVector B) := by
    change mixedMoment B node2454 node2454Labels = _
    exact sound2454 B hB hF
  have h2455 : mixedVector B (Sum.inr 2455) = Sparse.eval nodeValue2455 (mixedVector B) := by
    change mixedMoment B node2455 node2455Labels = _
    exact sound2455 B hB hF
  have h2463 : mixedVector B (Sum.inr 2463) = Sparse.eval nodeValue2463 (mixedVector B) := by
    change mixedMoment B node2463 node2463Labels = _
    exact sound2463 B hB hF
  have h2494 : mixedVector B (Sum.inr 2494) = Sparse.eval nodeValue2494 (mixedVector B) := by
    change mixedMoment B node2494 node2494Labels = _
    exact sound2494 B hB hF
  have h2732 : mixedVector B (Sum.inr 2732) = Sparse.eval nodeValue2732 (mixedVector B) := by
    change mixedMoment B node2732 node2732Labels = _
    exact sound2732 B hB hF
  have h2905 : mixedVector B (Sum.inr 2905) = Sparse.eval nodeValue2905 (mixedVector B) := by
    change mixedMoment B node2905 node2905Labels = _
    exact sound2905 B hB hF
  have h2909 : mixedVector B (Sum.inr 2909) = Sparse.eval nodeValue2909 (mixedVector B) := by
    change mixedMoment B node2909 node2909Labels = _
    exact sound2909 B hB hF
  have h2934 : mixedVector B (Sum.inr 2934) = Sparse.eval nodeValue2934 (mixedVector B) := by
    change mixedMoment B node2934 node2934Labels = _
    exact sound2934 B hB hF
  have h3039 : mixedVector B (Sum.inr 3039) = Sparse.eval nodeValue3039 (mixedVector B) := by
    change mixedMoment B node3039 node3039Labels = _
    exact sound3039 B hB hF
  have h3558 : mixedVector B (Sum.inr 3558) = Sparse.eval nodeValue3558 (mixedVector B) := by
    change mixedMoment B node3558 node3558Labels = _
    exact sound3558 B hB hF
  have h3559 : mixedVector B (Sum.inr 3559) = Sparse.eval nodeValue3559 (mixedVector B) := by
    change mixedMoment B node3559 node3559Labels = _
    exact sound3559 B hB hF
  have h3561 : mixedVector B (Sum.inr 3561) = Sparse.eval nodeValue3561 (mixedVector B) := by
    change mixedMoment B node3561 node3561Labels = _
    exact sound3561 B hB hF
  have h3573 : mixedVector B (Sum.inr 3573) = Sparse.eval nodeValue3573 (mixedVector B) := by
    change mixedMoment B node3573 node3573Labels = _
    exact sound3573 B hB hF
  have h3679 : mixedVector B (Sum.inr 3679) = Sparse.eval nodeValue3679 (mixedVector B) := by
    change mixedMoment B node3679 node3679Labels = _
    exact sound3679 B hB hF
  have h3698 : mixedVector B (Sum.inr 3698) = Sparse.eval nodeValue3698 (mixedVector B) := by
    change mixedMoment B node3698 node3698Labels = _
    exact sound3698 B hB hF
  have h3714 : mixedVector B (Sum.inr 3714) = Sparse.eval nodeValue3714 (mixedVector B) := by
    change mixedMoment B node3714 node3714Labels = _
    exact sound3714 B hB hF
  have h3724 : mixedVector B (Sum.inr 3724) = Sparse.eval nodeValue3724 (mixedVector B) := by
    change mixedMoment B node3724 node3724Labels = _
    exact sound3724 B hB hF
  have h3838 : mixedVector B (Sum.inr 3838) = Sparse.eval nodeValue3838 (mixedVector B) := by
    change mixedMoment B node3838 node3838Labels = _
    exact sound3838 B hB hF
  have h3839 : mixedVector B (Sum.inr 3839) = Sparse.eval nodeValue3839 (mixedVector B) := by
    change mixedMoment B node3839 node3839Labels = _
    exact sound3839 B hB hF
  have h3841 : mixedVector B (Sum.inr 3841) = Sparse.eval nodeValue3841 (mixedVector B) := by
    change mixedMoment B node3841 node3841Labels = _
    exact sound3841 B hB hF
  have h3853 : mixedVector B (Sum.inr 3853) = Sparse.eval nodeValue3853 (mixedVector B) := by
    change mixedMoment B node3853 node3853Labels = _
    exact sound3853 B hB hF
  have h3866 : mixedVector B (Sum.inr 3866) = Sparse.eval nodeValue3866 (mixedVector B) := by
    change mixedMoment B node3866 node3866Labels = _
    exact sound3866 B hB hF
  have h3871 : mixedVector B (Sum.inr 3871) = Sparse.eval nodeValue3871 (mixedVector B) := by
    change mixedMoment B node3871 node3871Labels = _
    exact sound3871 B hB hF
  have h3876 : mixedVector B (Sum.inr 3876) = Sparse.eval nodeValue3876 (mixedVector B) := by
    change mixedMoment B node3876 node3876Labels = _
    exact sound3876 B hB hF
  have h3877 : mixedVector B (Sum.inr 3877) = Sparse.eval nodeValue3877 (mixedVector B) := by
    change mixedMoment B node3877 node3877Labels = _
    exact sound3877 B hB hF
  have h3883 : mixedVector B (Sum.inr 3883) = Sparse.eval nodeValue3883 (mixedVector B) := by
    change mixedMoment B node3883 node3883Labels = _
    exact sound3883 B hB hF
  have h3889 : mixedVector B (Sum.inr 3889) = Sparse.eval nodeValue3889 (mixedVector B) := by
    change mixedMoment B node3889 node3889Labels = _
    exact sound3889 B hB hF
  have h3970 : mixedVector B (Sum.inr 3970) = Sparse.eval nodeValue3970 (mixedVector B) := by
    change mixedMoment B node3970 node3970Labels = _
    exact sound3970 B hB hF
  have h3990 : mixedVector B (Sum.inr 3990) = Sparse.eval nodeValue3990 (mixedVector B) := by
    change mixedMoment B node3990 node3990Labels = _
    exact sound3990 B hB hF
  have h4003 : mixedVector B (Sum.inr 4003) = Sparse.eval nodeValue4003 (mixedVector B) := by
    change mixedMoment B node4003 node4003Labels = _
    exact sound4003 B hB hF
  simpa only [sourceForm894, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2454, h2455, h2463, h2494, h2732, h2905, h2909, h2934, h3039, h3558, h3559, h3561, h3573, h3679, h3698, h3714, h3724, h3838, h3839, h3841, h3853, h3866, h3871, h3876, h3877, h3883, h3889, h3970, h3990, h4003, reducedSource780] using sourceEq894 B hB

theorem rowSound780 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row780 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck780, numericCheck780, reducedZero780 B hB hF, mul_zero]

theorem reducedZero781 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource781 (mixedVector B) = 0 := by
  have h2587 : mixedVector B (Sum.inr 2587) = Sparse.eval nodeValue2587 (mixedVector B) := by
    change mixedMoment B node2587 node2587Labels = _
    exact sound2587 B hB hF
  have h3730 : mixedVector B (Sum.inr 3730) = Sparse.eval nodeValue3730 (mixedVector B) := by
    change mixedMoment B node3730 node3730Labels = _
    exact sound3730 B hB hF
  have h3840 : mixedVector B (Sum.inr 3840) = Sparse.eval nodeValue3840 (mixedVector B) := by
    change mixedMoment B node3840 node3840Labels = _
    exact sound3840 B hB hF
  have h3843 : mixedVector B (Sum.inr 3843) = Sparse.eval nodeValue3843 (mixedVector B) := by
    change mixedMoment B node3843 node3843Labels = _
    exact sound3843 B hB hF
  have h3848 : mixedVector B (Sum.inr 3848) = Sparse.eval nodeValue3848 (mixedVector B) := by
    change mixedMoment B node3848 node3848Labels = _
    exact sound3848 B hB hF
  have h3857 : mixedVector B (Sum.inr 3857) = Sparse.eval nodeValue3857 (mixedVector B) := by
    change mixedMoment B node3857 node3857Labels = _
    exact sound3857 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm895, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2587, h3730, h3840, h3843, h3848, h3857, h4092, reducedSource781] using sourceEq895 B hB

theorem rowSound781 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row781 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck781, numericCheck781, reducedZero781 B hB hF, mul_zero]

theorem reducedZero782 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource782 (mixedVector B) = 0 := by
  have h2577 : mixedVector B (Sum.inr 2577) = Sparse.eval nodeValue2577 (mixedVector B) := by
    change mixedMoment B node2577 node2577Labels = _
    exact sound2577 B hB hF
  have h3729 : mixedVector B (Sum.inr 3729) = Sparse.eval nodeValue3729 (mixedVector B) := by
    change mixedMoment B node3729 node3729Labels = _
    exact sound3729 B hB hF
  have h3840 : mixedVector B (Sum.inr 3840) = Sparse.eval nodeValue3840 (mixedVector B) := by
    change mixedMoment B node3840 node3840Labels = _
    exact sound3840 B hB hF
  have h3854 : mixedVector B (Sum.inr 3854) = Sparse.eval nodeValue3854 (mixedVector B) := by
    change mixedMoment B node3854 node3854Labels = _
    exact sound3854 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm896, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2577, h3729, h3840, h3854, h4092, reducedSource782] using sourceEq896 B hB

theorem rowSound782 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row782 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck782, numericCheck782, reducedZero782 B hB hF, mul_zero]

theorem reducedZero783 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource783 (mixedVector B) = 0 := by
  have h2974 : mixedVector B (Sum.inr 2974) = Sparse.eval nodeValue2974 (mixedVector B) := by
    change mixedMoment B node2974 node2974Labels = _
    exact sound2974 B hB hF
  have h3780 : mixedVector B (Sum.inr 3780) = Sparse.eval nodeValue3780 (mixedVector B) := by
    change mixedMoment B node3780 node3780Labels = _
    exact sound3780 B hB hF
  have h3781 : mixedVector B (Sum.inr 3781) = Sparse.eval nodeValue3781 (mixedVector B) := by
    change mixedMoment B node3781 node3781Labels = _
    exact sound3781 B hB hF
  have h3813 : mixedVector B (Sum.inr 3813) = Sparse.eval nodeValue3813 (mixedVector B) := by
    change mixedMoment B node3813 node3813Labels = _
    exact sound3813 B hB hF
  have h3840 : mixedVector B (Sum.inr 3840) = Sparse.eval nodeValue3840 (mixedVector B) := by
    change mixedMoment B node3840 node3840Labels = _
    exact sound3840 B hB hF
  have h3848 : mixedVector B (Sum.inr 3848) = Sparse.eval nodeValue3848 (mixedVector B) := by
    change mixedMoment B node3848 node3848Labels = _
    exact sound3848 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm897, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2974, h3780, h3781, h3813, h3840, h3848, h4092, reducedSource783] using sourceEq897 B hB

theorem rowSound783 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row783 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck783, numericCheck783, reducedZero783 B hB hF, mul_zero]

theorem sourceRowsAt768 : MixedData.sourceRows (768 : Fin 2425) =
    MixedData.row768 := by decide +kernel

theorem sourceRowsAt769 : MixedData.sourceRows (769 : Fin 2425) =
    MixedData.row769 := by decide +kernel

theorem sourceRowsAt770 : MixedData.sourceRows (770 : Fin 2425) =
    MixedData.row770 := by decide +kernel

theorem sourceRowsAt771 : MixedData.sourceRows (771 : Fin 2425) =
    MixedData.row771 := by decide +kernel

theorem sourceRowsAt772 : MixedData.sourceRows (772 : Fin 2425) =
    MixedData.row772 := by decide +kernel

theorem sourceRowsAt773 : MixedData.sourceRows (773 : Fin 2425) =
    MixedData.row773 := by decide +kernel

theorem sourceRowsAt774 : MixedData.sourceRows (774 : Fin 2425) =
    MixedData.row774 := by decide +kernel

theorem sourceRowsAt775 : MixedData.sourceRows (775 : Fin 2425) =
    MixedData.row775 := by decide +kernel

theorem sourceRowsAt776 : MixedData.sourceRows (776 : Fin 2425) =
    MixedData.row776 := by decide +kernel

theorem sourceRowsAt777 : MixedData.sourceRows (777 : Fin 2425) =
    MixedData.row777 := by decide +kernel

theorem sourceRowsAt778 : MixedData.sourceRows (778 : Fin 2425) =
    MixedData.row778 := by decide +kernel

theorem sourceRowsAt779 : MixedData.sourceRows (779 : Fin 2425) =
    MixedData.row779 := by decide +kernel

theorem sourceRowsAt780 : MixedData.sourceRows (780 : Fin 2425) =
    MixedData.row780 := by decide +kernel

theorem sourceRowsAt781 : MixedData.sourceRows (781 : Fin 2425) =
    MixedData.row781 := by decide +kernel

theorem sourceRowsAt782 : MixedData.sourceRows (782 : Fin 2425) =
    MixedData.row782 := by decide +kernel

theorem sourceRowsAt783 : MixedData.sourceRows (783 : Fin 2425) =
    MixedData.row783 := by decide +kernel

theorem chunkSound48 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 48) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 768 ∨ k.val = 769 ∨ k.val = 770 ∨ k.val = 771 ∨ k.val = 772 ∨ k.val = 773 ∨ k.val = 774 ∨ k.val = 775 ∨ k.val = 776 ∨ k.val = 777 ∨ k.val = 778 ∨ k.val = 779 ∨ k.val = 780 ∨ k.val = 781 ∨ k.val = 782 ∨ k.val = 783 := by omega
  rcases heq with h768 | h769 | h770 | h771 | h772 | h773 | h774 | h775 | h776 | h777 | h778 | h779 | h780 | h781 | h782 | h783
  · have he : k = (768 : Fin 2425) := Fin.ext h768
    subst k
    rw [sourceRowsAt768]
    exact rowSound768 B hB hF
  · have he : k = (769 : Fin 2425) := Fin.ext h769
    subst k
    rw [sourceRowsAt769]
    exact rowSound769 B hB hF
  · have he : k = (770 : Fin 2425) := Fin.ext h770
    subst k
    rw [sourceRowsAt770]
    exact rowSound770 B hB hF
  · have he : k = (771 : Fin 2425) := Fin.ext h771
    subst k
    rw [sourceRowsAt771]
    exact rowSound771 B hB hF
  · have he : k = (772 : Fin 2425) := Fin.ext h772
    subst k
    rw [sourceRowsAt772]
    exact rowSound772 B hB hF
  · have he : k = (773 : Fin 2425) := Fin.ext h773
    subst k
    rw [sourceRowsAt773]
    exact rowSound773 B hB hF
  · have he : k = (774 : Fin 2425) := Fin.ext h774
    subst k
    rw [sourceRowsAt774]
    exact rowSound774 B hB hF
  · have he : k = (775 : Fin 2425) := Fin.ext h775
    subst k
    rw [sourceRowsAt775]
    exact rowSound775 B hB hF
  · have he : k = (776 : Fin 2425) := Fin.ext h776
    subst k
    rw [sourceRowsAt776]
    exact rowSound776 B hB hF
  · have he : k = (777 : Fin 2425) := Fin.ext h777
    subst k
    rw [sourceRowsAt777]
    exact rowSound777 B hB hF
  · have he : k = (778 : Fin 2425) := Fin.ext h778
    subst k
    rw [sourceRowsAt778]
    exact rowSound778 B hB hF
  · have he : k = (779 : Fin 2425) := Fin.ext h779
    subst k
    rw [sourceRowsAt779]
    exact rowSound779 B hB hF
  · have he : k = (780 : Fin 2425) := Fin.ext h780
    subst k
    rw [sourceRowsAt780]
    exact rowSound780 B hB hF
  · have he : k = (781 : Fin 2425) := Fin.ext h781
    subst k
    rw [sourceRowsAt781]
    exact rowSound781 B hB hF
  · have he : k = (782 : Fin 2425) := Fin.ext h782
    subst k
    rw [sourceRowsAt782]
    exact rowSound782 B hB hF
  · have he : k = (783 : Fin 2425) := Fin.ext h783
    subst k
    rw [sourceRowsAt783]
    exact rowSound783 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
