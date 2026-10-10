import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic130
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources82

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2080 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2080 (mixedVector B) = 0 := by
  have h4930 : mixedVector B (Sum.inr 4930) = Sparse.eval nodeValue4930 (mixedVector B) := by
    change mixedMoment B node4930 node4930Labels = _
    exact sound4930 B hB hF
  have h4931 : mixedVector B (Sum.inr 4931) = Sparse.eval nodeValue4931 (mixedVector B) := by
    change mixedMoment B node4931 node4931Labels = _
    exact sound4931 B hB hF
  have h4933 : mixedVector B (Sum.inr 4933) = Sparse.eval nodeValue4933 (mixedVector B) := by
    change mixedMoment B node4933 node4933Labels = _
    exact sound4933 B hB hF
  have h4942 : mixedVector B (Sum.inr 4942) = Sparse.eval nodeValue4942 (mixedVector B) := by
    change mixedMoment B node4942 node4942Labels = _
    exact sound4942 B hB hF
  have h5039 : mixedVector B (Sum.inr 5039) = Sparse.eval nodeValue5039 (mixedVector B) := by
    change mixedMoment B node5039 node5039Labels = _
    exact sound5039 B hB hF
  have h5081 : mixedVector B (Sum.inr 5081) = Sparse.eval nodeValue5081 (mixedVector B) := by
    change mixedMoment B node5081 node5081Labels = _
    exact sound5081 B hB hF
  have h5130 : mixedVector B (Sum.inr 5130) = Sparse.eval nodeValue5130 (mixedVector B) := by
    change mixedMoment B node5130 node5130Labels = _
    exact sound5130 B hB hF
  have h5149 : mixedVector B (Sum.inr 5149) = Sparse.eval nodeValue5149 (mixedVector B) := by
    change mixedMoment B node5149 node5149Labels = _
    exact sound5149 B hB hF
  have h5337 : mixedVector B (Sum.inr 5337) = Sparse.eval nodeValue5337 (mixedVector B) := by
    change mixedMoment B node5337 node5337Labels = _
    exact sound5337 B hB hF
  have h5356 : mixedVector B (Sum.inr 5356) = Sparse.eval nodeValue5356 (mixedVector B) := by
    change mixedMoment B node5356 node5356Labels = _
    exact sound5356 B hB hF
  have h5373 : mixedVector B (Sum.inr 5373) = Sparse.eval nodeValue5373 (mixedVector B) := by
    change mixedMoment B node5373 node5373Labels = _
    exact sound5373 B hB hF
  have h5377 : mixedVector B (Sum.inr 5377) = Sparse.eval nodeValue5377 (mixedVector B) := by
    change mixedMoment B node5377 node5377Labels = _
    exact sound5377 B hB hF
  have h5396 : mixedVector B (Sum.inr 5396) = Sparse.eval nodeValue5396 (mixedVector B) := by
    change mixedMoment B node5396 node5396Labels = _
    exact sound5396 B hB hF
  have h5404 : mixedVector B (Sum.inr 5404) = Sparse.eval nodeValue5404 (mixedVector B) := by
    change mixedMoment B node5404 node5404Labels = _
    exact sound5404 B hB hF
  have h5410 : mixedVector B (Sum.inr 5410) = Sparse.eval nodeValue5410 (mixedVector B) := by
    change mixedMoment B node5410 node5410Labels = _
    exact sound5410 B hB hF
  have h5419 : mixedVector B (Sum.inr 5419) = Sparse.eval nodeValue5419 (mixedVector B) := by
    change mixedMoment B node5419 node5419Labels = _
    exact sound5419 B hB hF
  have h5424 : mixedVector B (Sum.inr 5424) = Sparse.eval nodeValue5424 (mixedVector B) := by
    change mixedMoment B node5424 node5424Labels = _
    exact sound5424 B hB hF
  have h5459 : mixedVector B (Sum.inr 5459) = Sparse.eval nodeValue5459 (mixedVector B) := by
    change mixedMoment B node5459 node5459Labels = _
    exact sound5459 B hB hF
  have h5461 : mixedVector B (Sum.inr 5461) = Sparse.eval nodeValue5461 (mixedVector B) := by
    change mixedMoment B node5461 node5461Labels = _
    exact sound5461 B hB hF
  have h5478 : mixedVector B (Sum.inr 5478) = Sparse.eval nodeValue5478 (mixedVector B) := by
    change mixedMoment B node5478 node5478Labels = _
    exact sound5478 B hB hF
  simpa only [sourceForm2607, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4930, h4931, h4933, h4942, h5039, h5081, h5130, h5149, h5337, h5356, h5373, h5377, h5396, h5404, h5410, h5419, h5424, h5459, h5461, h5478, reducedSource2080] using sourceEq2607 B hB

theorem rowSound2080 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2080 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2080, numericCheck2080, reducedZero2080 B hB hF, mul_zero]

theorem reducedZero2081 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2081 (mixedVector B) = 0 := by
  have h3406 : mixedVector B (Sum.inr 3406) = Sparse.eval nodeValue3406 (mixedVector B) := by
    change mixedMoment B node3406 node3406Labels = _
    exact sound3406 B hB hF
  have h3407 : mixedVector B (Sum.inr 3407) = Sparse.eval nodeValue3407 (mixedVector B) := by
    change mixedMoment B node3407 node3407Labels = _
    exact sound3407 B hB hF
  have h3408 : mixedVector B (Sum.inr 3408) = Sparse.eval nodeValue3408 (mixedVector B) := by
    change mixedMoment B node3408 node3408Labels = _
    exact sound3408 B hB hF
  have h3414 : mixedVector B (Sum.inr 3414) = Sparse.eval nodeValue3414 (mixedVector B) := by
    change mixedMoment B node3414 node3414Labels = _
    exact sound3414 B hB hF
  have h3456 : mixedVector B (Sum.inr 3456) = Sparse.eval nodeValue3456 (mixedVector B) := by
    change mixedMoment B node3456 node3456Labels = _
    exact sound3456 B hB hF
  have h3482 : mixedVector B (Sum.inr 3482) = Sparse.eval nodeValue3482 (mixedVector B) := by
    change mixedMoment B node3482 node3482Labels = _
    exact sound3482 B hB hF
  have h3520 : mixedVector B (Sum.inr 3520) = Sparse.eval nodeValue3520 (mixedVector B) := by
    change mixedMoment B node3520 node3520Labels = _
    exact sound3520 B hB hF
  have h3605 : mixedVector B (Sum.inr 3605) = Sparse.eval nodeValue3605 (mixedVector B) := by
    change mixedMoment B node3605 node3605Labels = _
    exact sound3605 B hB hF
  have h3756 : mixedVector B (Sum.inr 3756) = Sparse.eval nodeValue3756 (mixedVector B) := by
    change mixedMoment B node3756 node3756Labels = _
    exact sound3756 B hB hF
  have h3773 : mixedVector B (Sum.inr 3773) = Sparse.eval nodeValue3773 (mixedVector B) := by
    change mixedMoment B node3773 node3773Labels = _
    exact sound3773 B hB hF
  have h3792 : mixedVector B (Sum.inr 3792) = Sparse.eval nodeValue3792 (mixedVector B) := by
    change mixedMoment B node3792 node3792Labels = _
    exact sound3792 B hB hF
  have h3798 : mixedVector B (Sum.inr 3798) = Sparse.eval nodeValue3798 (mixedVector B) := by
    change mixedMoment B node3798 node3798Labels = _
    exact sound3798 B hB hF
  have h3815 : mixedVector B (Sum.inr 3815) = Sparse.eval nodeValue3815 (mixedVector B) := by
    change mixedMoment B node3815 node3815Labels = _
    exact sound3815 B hB hF
  have h3816 : mixedVector B (Sum.inr 3816) = Sparse.eval nodeValue3816 (mixedVector B) := by
    change mixedMoment B node3816 node3816Labels = _
    exact sound3816 B hB hF
  have h3835 : mixedVector B (Sum.inr 3835) = Sparse.eval nodeValue3835 (mixedVector B) := by
    change mixedMoment B node3835 node3835Labels = _
    exact sound3835 B hB hF
  have h3842 : mixedVector B (Sum.inr 3842) = Sparse.eval nodeValue3842 (mixedVector B) := by
    change mixedMoment B node3842 node3842Labels = _
    exact sound3842 B hB hF
  have h3843 : mixedVector B (Sum.inr 3843) = Sparse.eval nodeValue3843 (mixedVector B) := by
    change mixedMoment B node3843 node3843Labels = _
    exact sound3843 B hB hF
  have h3951 : mixedVector B (Sum.inr 3951) = Sparse.eval nodeValue3951 (mixedVector B) := by
    change mixedMoment B node3951 node3951Labels = _
    exact sound3951 B hB hF
  have h3973 : mixedVector B (Sum.inr 3973) = Sparse.eval nodeValue3973 (mixedVector B) := by
    change mixedMoment B node3973 node3973Labels = _
    exact sound3973 B hB hF
  have h3974 : mixedVector B (Sum.inr 3974) = Sparse.eval nodeValue3974 (mixedVector B) := by
    change mixedMoment B node3974 node3974Labels = _
    exact sound3974 B hB hF
  simpa only [sourceForm2608, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3406, h3407, h3408, h3414, h3456, h3482, h3520, h3605, h3756, h3773, h3792, h3798, h3815, h3816, h3835, h3842, h3843, h3951, h3973, h3974, reducedSource2081] using sourceEq2608 B hB

theorem rowSound2081 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2081 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2081, numericCheck2081, reducedZero2081 B hB hF, mul_zero]

theorem reducedZero2082 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2082 (mixedVector B) = 0 := by
  have h4756 : mixedVector B (Sum.inr 4756) = Sparse.eval nodeValue4756 (mixedVector B) := by
    change mixedMoment B node4756 node4756Labels = _
    exact sound4756 B hB hF
  have h4757 : mixedVector B (Sum.inr 4757) = Sparse.eval nodeValue4757 (mixedVector B) := by
    change mixedMoment B node4757 node4757Labels = _
    exact sound4757 B hB hF
  have h4768 : mixedVector B (Sum.inr 4768) = Sparse.eval nodeValue4768 (mixedVector B) := by
    change mixedMoment B node4768 node4768Labels = _
    exact sound4768 B hB hF
  have h4795 : mixedVector B (Sum.inr 4795) = Sparse.eval nodeValue4795 (mixedVector B) := by
    change mixedMoment B node4795 node4795Labels = _
    exact sound4795 B hB hF
  have h4933 : mixedVector B (Sum.inr 4933) = Sparse.eval nodeValue4933 (mixedVector B) := by
    change mixedMoment B node4933 node4933Labels = _
    exact sound4933 B hB hF
  have h4947 : mixedVector B (Sum.inr 4947) = Sparse.eval nodeValue4947 (mixedVector B) := by
    change mixedMoment B node4947 node4947Labels = _
    exact sound4947 B hB hF
  have h4955 : mixedVector B (Sum.inr 4955) = Sparse.eval nodeValue4955 (mixedVector B) := by
    change mixedMoment B node4955 node4955Labels = _
    exact sound4955 B hB hF
  have h4967 : mixedVector B (Sum.inr 4967) = Sparse.eval nodeValue4967 (mixedVector B) := by
    change mixedMoment B node4967 node4967Labels = _
    exact sound4967 B hB hF
  have h5076 : mixedVector B (Sum.inr 5076) = Sparse.eval nodeValue5076 (mixedVector B) := by
    change mixedMoment B node5076 node5076Labels = _
    exact sound5076 B hB hF
  have h5184 : mixedVector B (Sum.inr 5184) = Sparse.eval nodeValue5184 (mixedVector B) := by
    change mixedMoment B node5184 node5184Labels = _
    exact sound5184 B hB hF
  have h5338 : mixedVector B (Sum.inr 5338) = Sparse.eval nodeValue5338 (mixedVector B) := by
    change mixedMoment B node5338 node5338Labels = _
    exact sound5338 B hB hF
  have h5348 : mixedVector B (Sum.inr 5348) = Sparse.eval nodeValue5348 (mixedVector B) := by
    change mixedMoment B node5348 node5348Labels = _
    exact sound5348 B hB hF
  have h5352 : mixedVector B (Sum.inr 5352) = Sparse.eval nodeValue5352 (mixedVector B) := by
    change mixedMoment B node5352 node5352Labels = _
    exact sound5352 B hB hF
  have h5354 : mixedVector B (Sum.inr 5354) = Sparse.eval nodeValue5354 (mixedVector B) := by
    change mixedMoment B node5354 node5354Labels = _
    exact sound5354 B hB hF
  have h5366 : mixedVector B (Sum.inr 5366) = Sparse.eval nodeValue5366 (mixedVector B) := by
    change mixedMoment B node5366 node5366Labels = _
    exact sound5366 B hB hF
  have h5403 : mixedVector B (Sum.inr 5403) = Sparse.eval nodeValue5403 (mixedVector B) := by
    change mixedMoment B node5403 node5403Labels = _
    exact sound5403 B hB hF
  have h5406 : mixedVector B (Sum.inr 5406) = Sparse.eval nodeValue5406 (mixedVector B) := by
    change mixedMoment B node5406 node5406Labels = _
    exact sound5406 B hB hF
  have h5408 : mixedVector B (Sum.inr 5408) = Sparse.eval nodeValue5408 (mixedVector B) := by
    change mixedMoment B node5408 node5408Labels = _
    exact sound5408 B hB hF
  have h5414 : mixedVector B (Sum.inr 5414) = Sparse.eval nodeValue5414 (mixedVector B) := by
    change mixedMoment B node5414 node5414Labels = _
    exact sound5414 B hB hF
  have h5429 : mixedVector B (Sum.inr 5429) = Sparse.eval nodeValue5429 (mixedVector B) := by
    change mixedMoment B node5429 node5429Labels = _
    exact sound5429 B hB hF
  have h5472 : mixedVector B (Sum.inr 5472) = Sparse.eval nodeValue5472 (mixedVector B) := by
    change mixedMoment B node5472 node5472Labels = _
    exact sound5472 B hB hF
  simpa only [sourceForm2611, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4756, h4757, h4768, h4795, h4933, h4947, h4955, h4967, h5076, h5184, h5338, h5348, h5352, h5354, h5366, h5403, h5406, h5408, h5414, h5429, h5472, reducedSource2082] using sourceEq2611 B hB

theorem rowSound2082 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2082 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2082, numericCheck2082, reducedZero2082 B hB hF, mul_zero]

theorem reducedZero2083 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2083 (mixedVector B) = 0 := by
  have h2176 : mixedVector B (Sum.inr 2176) = Sparse.eval nodeValue2176 (mixedVector B) := by
    change mixedMoment B node2176 node2176Labels = _
    exact sound2176 B hB hF
  have h2178 : mixedVector B (Sum.inr 2178) = Sparse.eval nodeValue2178 (mixedVector B) := by
    change mixedMoment B node2178 node2178Labels = _
    exact sound2178 B hB hF
  have h2181 : mixedVector B (Sum.inr 2181) = Sparse.eval nodeValue2181 (mixedVector B) := by
    change mixedMoment B node2181 node2181Labels = _
    exact sound2181 B hB hF
  have h2213 : mixedVector B (Sum.inr 2213) = Sparse.eval nodeValue2213 (mixedVector B) := by
    change mixedMoment B node2213 node2213Labels = _
    exact sound2213 B hB hF
  have h3414 : mixedVector B (Sum.inr 3414) = Sparse.eval nodeValue3414 (mixedVector B) := by
    change mixedMoment B node3414 node3414Labels = _
    exact sound3414 B hB hF
  have h3416 : mixedVector B (Sum.inr 3416) = Sparse.eval nodeValue3416 (mixedVector B) := by
    change mixedMoment B node3416 node3416Labels = _
    exact sound3416 B hB hF
  have h3477 : mixedVector B (Sum.inr 3477) = Sparse.eval nodeValue3477 (mixedVector B) := by
    change mixedMoment B node3477 node3477Labels = _
    exact sound3477 B hB hF
  have h3508 : mixedVector B (Sum.inr 3508) = Sparse.eval nodeValue3508 (mixedVector B) := by
    change mixedMoment B node3508 node3508Labels = _
    exact sound3508 B hB hF
  have h3524 : mixedVector B (Sum.inr 3524) = Sparse.eval nodeValue3524 (mixedVector B) := by
    change mixedMoment B node3524 node3524Labels = _
    exact sound3524 B hB hF
  have h3585 : mixedVector B (Sum.inr 3585) = Sparse.eval nodeValue3585 (mixedVector B) := by
    change mixedMoment B node3585 node3585Labels = _
    exact sound3585 B hB hF
  have h3755 : mixedVector B (Sum.inr 3755) = Sparse.eval nodeValue3755 (mixedVector B) := by
    change mixedMoment B node3755 node3755Labels = _
    exact sound3755 B hB hF
  have h3764 : mixedVector B (Sum.inr 3764) = Sparse.eval nodeValue3764 (mixedVector B) := by
    change mixedMoment B node3764 node3764Labels = _
    exact sound3764 B hB hF
  have h3765 : mixedVector B (Sum.inr 3765) = Sparse.eval nodeValue3765 (mixedVector B) := by
    change mixedMoment B node3765 node3765Labels = _
    exact sound3765 B hB hF
  have h3768 : mixedVector B (Sum.inr 3768) = Sparse.eval nodeValue3768 (mixedVector B) := by
    change mixedMoment B node3768 node3768Labels = _
    exact sound3768 B hB hF
  have h3769 : mixedVector B (Sum.inr 3769) = Sparse.eval nodeValue3769 (mixedVector B) := by
    change mixedMoment B node3769 node3769Labels = _
    exact sound3769 B hB hF
  have h3806 : mixedVector B (Sum.inr 3806) = Sparse.eval nodeValue3806 (mixedVector B) := by
    change mixedMoment B node3806 node3806Labels = _
    exact sound3806 B hB hF
  have h3810 : mixedVector B (Sum.inr 3810) = Sparse.eval nodeValue3810 (mixedVector B) := by
    change mixedMoment B node3810 node3810Labels = _
    exact sound3810 B hB hF
  have h3812 : mixedVector B (Sum.inr 3812) = Sparse.eval nodeValue3812 (mixedVector B) := by
    change mixedMoment B node3812 node3812Labels = _
    exact sound3812 B hB hF
  have h3869 : mixedVector B (Sum.inr 3869) = Sparse.eval nodeValue3869 (mixedVector B) := by
    change mixedMoment B node3869 node3869Labels = _
    exact sound3869 B hB hF
  have h3874 : mixedVector B (Sum.inr 3874) = Sparse.eval nodeValue3874 (mixedVector B) := by
    change mixedMoment B node3874 node3874Labels = _
    exact sound3874 B hB hF
  have h3957 : mixedVector B (Sum.inr 3957) = Sparse.eval nodeValue3957 (mixedVector B) := by
    change mixedMoment B node3957 node3957Labels = _
    exact sound3957 B hB hF
  simpa only [sourceForm2612, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2176, h2178, h2181, h2213, h3414, h3416, h3477, h3508, h3524, h3585, h3755, h3764, h3765, h3768, h3769, h3806, h3810, h3812, h3869, h3874, h3957, reducedSource2083] using sourceEq2612 B hB

theorem rowSound2083 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2083 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2083, numericCheck2083, reducedZero2083 B hB hF, mul_zero]

theorem reducedZero2084 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2084 (mixedVector B) = 0 := by
  have h4930 : mixedVector B (Sum.inr 4930) = Sparse.eval nodeValue4930 (mixedVector B) := by
    change mixedMoment B node4930 node4930Labels = _
    exact sound4930 B hB hF
  have h4932 : mixedVector B (Sum.inr 4932) = Sparse.eval nodeValue4932 (mixedVector B) := by
    change mixedMoment B node4932 node4932Labels = _
    exact sound4932 B hB hF
  have h4933 : mixedVector B (Sum.inr 4933) = Sparse.eval nodeValue4933 (mixedVector B) := by
    change mixedMoment B node4933 node4933Labels = _
    exact sound4933 B hB hF
  have h4941 : mixedVector B (Sum.inr 4941) = Sparse.eval nodeValue4941 (mixedVector B) := by
    change mixedMoment B node4941 node4941Labels = _
    exact sound4941 B hB hF
  have h4954 : mixedVector B (Sum.inr 4954) = Sparse.eval nodeValue4954 (mixedVector B) := by
    change mixedMoment B node4954 node4954Labels = _
    exact sound4954 B hB hF
  have h4955 : mixedVector B (Sum.inr 4955) = Sparse.eval nodeValue4955 (mixedVector B) := by
    change mixedMoment B node4955 node4955Labels = _
    exact sound4955 B hB hF
  have h4958 : mixedVector B (Sum.inr 4958) = Sparse.eval nodeValue4958 (mixedVector B) := by
    change mixedMoment B node4958 node4958Labels = _
    exact sound4958 B hB hF
  have h4968 : mixedVector B (Sum.inr 4968) = Sparse.eval nodeValue4968 (mixedVector B) := by
    change mixedMoment B node4968 node4968Labels = _
    exact sound4968 B hB hF
  have h5040 : mixedVector B (Sum.inr 5040) = Sparse.eval nodeValue5040 (mixedVector B) := by
    change mixedMoment B node5040 node5040Labels = _
    exact sound5040 B hB hF
  have h5067 : mixedVector B (Sum.inr 5067) = Sparse.eval nodeValue5067 (mixedVector B) := by
    change mixedMoment B node5067 node5067Labels = _
    exact sound5067 B hB hF
  have h5073 : mixedVector B (Sum.inr 5073) = Sparse.eval nodeValue5073 (mixedVector B) := by
    change mixedMoment B node5073 node5073Labels = _
    exact sound5073 B hB hF
  have h5152 : mixedVector B (Sum.inr 5152) = Sparse.eval nodeValue5152 (mixedVector B) := by
    change mixedMoment B node5152 node5152Labels = _
    exact sound5152 B hB hF
  have h5185 : mixedVector B (Sum.inr 5185) = Sparse.eval nodeValue5185 (mixedVector B) := by
    change mixedMoment B node5185 node5185Labels = _
    exact sound5185 B hB hF
  have h5338 : mixedVector B (Sum.inr 5338) = Sparse.eval nodeValue5338 (mixedVector B) := by
    change mixedMoment B node5338 node5338Labels = _
    exact sound5338 B hB hF
  have h5340 : mixedVector B (Sum.inr 5340) = Sparse.eval nodeValue5340 (mixedVector B) := by
    change mixedMoment B node5340 node5340Labels = _
    exact sound5340 B hB hF
  have h5348 : mixedVector B (Sum.inr 5348) = Sparse.eval nodeValue5348 (mixedVector B) := by
    change mixedMoment B node5348 node5348Labels = _
    exact sound5348 B hB hF
  have h5352 : mixedVector B (Sum.inr 5352) = Sparse.eval nodeValue5352 (mixedVector B) := by
    change mixedMoment B node5352 node5352Labels = _
    exact sound5352 B hB hF
  have h5354 : mixedVector B (Sum.inr 5354) = Sparse.eval nodeValue5354 (mixedVector B) := by
    change mixedMoment B node5354 node5354Labels = _
    exact sound5354 B hB hF
  have h5356 : mixedVector B (Sum.inr 5356) = Sparse.eval nodeValue5356 (mixedVector B) := by
    change mixedMoment B node5356 node5356Labels = _
    exact sound5356 B hB hF
  have h5366 : mixedVector B (Sum.inr 5366) = Sparse.eval nodeValue5366 (mixedVector B) := by
    change mixedMoment B node5366 node5366Labels = _
    exact sound5366 B hB hF
  have h5369 : mixedVector B (Sum.inr 5369) = Sparse.eval nodeValue5369 (mixedVector B) := by
    change mixedMoment B node5369 node5369Labels = _
    exact sound5369 B hB hF
  have h5401 : mixedVector B (Sum.inr 5401) = Sparse.eval nodeValue5401 (mixedVector B) := by
    change mixedMoment B node5401 node5401Labels = _
    exact sound5401 B hB hF
  have h5405 : mixedVector B (Sum.inr 5405) = Sparse.eval nodeValue5405 (mixedVector B) := by
    change mixedMoment B node5405 node5405Labels = _
    exact sound5405 B hB hF
  have h5408 : mixedVector B (Sum.inr 5408) = Sparse.eval nodeValue5408 (mixedVector B) := by
    change mixedMoment B node5408 node5408Labels = _
    exact sound5408 B hB hF
  have h5410 : mixedVector B (Sum.inr 5410) = Sparse.eval nodeValue5410 (mixedVector B) := by
    change mixedMoment B node5410 node5410Labels = _
    exact sound5410 B hB hF
  have h5470 : mixedVector B (Sum.inr 5470) = Sparse.eval nodeValue5470 (mixedVector B) := by
    change mixedMoment B node5470 node5470Labels = _
    exact sound5470 B hB hF
  have h5471 : mixedVector B (Sum.inr 5471) = Sparse.eval nodeValue5471 (mixedVector B) := by
    change mixedMoment B node5471 node5471Labels = _
    exact sound5471 B hB hF
  have h5472 : mixedVector B (Sum.inr 5472) = Sparse.eval nodeValue5472 (mixedVector B) := by
    change mixedMoment B node5472 node5472Labels = _
    exact sound5472 B hB hF
  have h5473 : mixedVector B (Sum.inr 5473) = Sparse.eval nodeValue5473 (mixedVector B) := by
    change mixedMoment B node5473 node5473Labels = _
    exact sound5473 B hB hF
  simpa only [sourceForm2614, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4930, h4932, h4933, h4941, h4954, h4955, h4958, h4968, h5040, h5067, h5073, h5152, h5185, h5338, h5340, h5348, h5352, h5354, h5356, h5366, h5369, h5401, h5405, h5408, h5410, h5470, h5471, h5472, h5473, reducedSource2084] using sourceEq2614 B hB

theorem rowSound2084 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2084 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2084, numericCheck2084, reducedZero2084 B hB hF, mul_zero]

theorem reducedZero2085 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2085 (mixedVector B) = 0 := by
  have h3408 : mixedVector B (Sum.inr 3408) = Sparse.eval nodeValue3408 (mixedVector B) := by
    change mixedMoment B node3408 node3408Labels = _
    exact sound3408 B hB hF
  have h3409 : mixedVector B (Sum.inr 3409) = Sparse.eval nodeValue3409 (mixedVector B) := by
    change mixedMoment B node3409 node3409Labels = _
    exact sound3409 B hB hF
  have h3410 : mixedVector B (Sum.inr 3410) = Sparse.eval nodeValue3410 (mixedVector B) := by
    change mixedMoment B node3410 node3410Labels = _
    exact sound3410 B hB hF
  have h3414 : mixedVector B (Sum.inr 3414) = Sparse.eval nodeValue3414 (mixedVector B) := by
    change mixedMoment B node3414 node3414Labels = _
    exact sound3414 B hB hF
  have h3452 : mixedVector B (Sum.inr 3452) = Sparse.eval nodeValue3452 (mixedVector B) := by
    change mixedMoment B node3452 node3452Labels = _
    exact sound3452 B hB hF
  have h3454 : mixedVector B (Sum.inr 3454) = Sparse.eval nodeValue3454 (mixedVector B) := by
    change mixedMoment B node3454 node3454Labels = _
    exact sound3454 B hB hF
  have h3467 : mixedVector B (Sum.inr 3467) = Sparse.eval nodeValue3467 (mixedVector B) := by
    change mixedMoment B node3467 node3467Labels = _
    exact sound3467 B hB hF
  have h3476 : mixedVector B (Sum.inr 3476) = Sparse.eval nodeValue3476 (mixedVector B) := by
    change mixedMoment B node3476 node3476Labels = _
    exact sound3476 B hB hF
  have h3508 : mixedVector B (Sum.inr 3508) = Sparse.eval nodeValue3508 (mixedVector B) := by
    change mixedMoment B node3508 node3508Labels = _
    exact sound3508 B hB hF
  have h3511 : mixedVector B (Sum.inr 3511) = Sparse.eval nodeValue3511 (mixedVector B) := by
    change mixedMoment B node3511 node3511Labels = _
    exact sound3511 B hB hF
  have h3529 : mixedVector B (Sum.inr 3529) = Sparse.eval nodeValue3529 (mixedVector B) := by
    change mixedMoment B node3529 node3529Labels = _
    exact sound3529 B hB hF
  have h3587 : mixedVector B (Sum.inr 3587) = Sparse.eval nodeValue3587 (mixedVector B) := by
    change mixedMoment B node3587 node3587Labels = _
    exact sound3587 B hB hF
  have h3612 : mixedVector B (Sum.inr 3612) = Sparse.eval nodeValue3612 (mixedVector B) := by
    change mixedMoment B node3612 node3612Labels = _
    exact sound3612 B hB hF
  have h3755 : mixedVector B (Sum.inr 3755) = Sparse.eval nodeValue3755 (mixedVector B) := by
    change mixedMoment B node3755 node3755Labels = _
    exact sound3755 B hB hF
  have h3763 : mixedVector B (Sum.inr 3763) = Sparse.eval nodeValue3763 (mixedVector B) := by
    change mixedMoment B node3763 node3763Labels = _
    exact sound3763 B hB hF
  have h3764 : mixedVector B (Sum.inr 3764) = Sparse.eval nodeValue3764 (mixedVector B) := by
    change mixedMoment B node3764 node3764Labels = _
    exact sound3764 B hB hF
  have h3765 : mixedVector B (Sum.inr 3765) = Sparse.eval nodeValue3765 (mixedVector B) := by
    change mixedMoment B node3765 node3765Labels = _
    exact sound3765 B hB hF
  have h3768 : mixedVector B (Sum.inr 3768) = Sparse.eval nodeValue3768 (mixedVector B) := by
    change mixedMoment B node3768 node3768Labels = _
    exact sound3768 B hB hF
  have h3769 : mixedVector B (Sum.inr 3769) = Sparse.eval nodeValue3769 (mixedVector B) := by
    change mixedMoment B node3769 node3769Labels = _
    exact sound3769 B hB hF
  have h3773 : mixedVector B (Sum.inr 3773) = Sparse.eval nodeValue3773 (mixedVector B) := by
    change mixedMoment B node3773 node3773Labels = _
    exact sound3773 B hB hF
  have h3774 : mixedVector B (Sum.inr 3774) = Sparse.eval nodeValue3774 (mixedVector B) := by
    change mixedMoment B node3774 node3774Labels = _
    exact sound3774 B hB hF
  have h3804 : mixedVector B (Sum.inr 3804) = Sparse.eval nodeValue3804 (mixedVector B) := by
    change mixedMoment B node3804 node3804Labels = _
    exact sound3804 B hB hF
  have h3805 : mixedVector B (Sum.inr 3805) = Sparse.eval nodeValue3805 (mixedVector B) := by
    change mixedMoment B node3805 node3805Labels = _
    exact sound3805 B hB hF
  have h3806 : mixedVector B (Sum.inr 3806) = Sparse.eval nodeValue3806 (mixedVector B) := by
    change mixedMoment B node3806 node3806Labels = _
    exact sound3806 B hB hF
  have h3816 : mixedVector B (Sum.inr 3816) = Sparse.eval nodeValue3816 (mixedVector B) := by
    change mixedMoment B node3816 node3816Labels = _
    exact sound3816 B hB hF
  have h3955 : mixedVector B (Sum.inr 3955) = Sparse.eval nodeValue3955 (mixedVector B) := by
    change mixedMoment B node3955 node3955Labels = _
    exact sound3955 B hB hF
  have h3956 : mixedVector B (Sum.inr 3956) = Sparse.eval nodeValue3956 (mixedVector B) := by
    change mixedMoment B node3956 node3956Labels = _
    exact sound3956 B hB hF
  have h3957 : mixedVector B (Sum.inr 3957) = Sparse.eval nodeValue3957 (mixedVector B) := by
    change mixedMoment B node3957 node3957Labels = _
    exact sound3957 B hB hF
  have h3961 : mixedVector B (Sum.inr 3961) = Sparse.eval nodeValue3961 (mixedVector B) := by
    change mixedMoment B node3961 node3961Labels = _
    exact sound3961 B hB hF
  simpa only [sourceForm2615, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3408, h3409, h3410, h3414, h3452, h3454, h3467, h3476, h3508, h3511, h3529, h3587, h3612, h3755, h3763, h3764, h3765, h3768, h3769, h3773, h3774, h3804, h3805, h3806, h3816, h3955, h3956, h3957, h3961, reducedSource2085] using sourceEq2615 B hB

theorem rowSound2085 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2085 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2085, numericCheck2085, reducedZero2085 B hB hF, mul_zero]

theorem reducedZero2086 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2086 (mixedVector B) = 0 := by
  have h4929 : mixedVector B (Sum.inr 4929) = Sparse.eval nodeValue4929 (mixedVector B) := by
    change mixedMoment B node4929 node4929Labels = _
    exact sound4929 B hB hF
  have h4931 : mixedVector B (Sum.inr 4931) = Sparse.eval nodeValue4931 (mixedVector B) := by
    change mixedMoment B node4931 node4931Labels = _
    exact sound4931 B hB hF
  have h4939 : mixedVector B (Sum.inr 4939) = Sparse.eval nodeValue4939 (mixedVector B) := by
    change mixedMoment B node4939 node4939Labels = _
    exact sound4939 B hB hF
  have h4956 : mixedVector B (Sum.inr 4956) = Sparse.eval nodeValue4956 (mixedVector B) := by
    change mixedMoment B node4956 node4956Labels = _
    exact sound4956 B hB hF
  have h4957 : mixedVector B (Sum.inr 4957) = Sparse.eval nodeValue4957 (mixedVector B) := by
    change mixedMoment B node4957 node4957Labels = _
    exact sound4957 B hB hF
  have h4971 : mixedVector B (Sum.inr 4971) = Sparse.eval nodeValue4971 (mixedVector B) := by
    change mixedMoment B node4971 node4971Labels = _
    exact sound4971 B hB hF
  have h5072 : mixedVector B (Sum.inr 5072) = Sparse.eval nodeValue5072 (mixedVector B) := by
    change mixedMoment B node5072 node5072Labels = _
    exact sound5072 B hB hF
  have h5112 : mixedVector B (Sum.inr 5112) = Sparse.eval nodeValue5112 (mixedVector B) := by
    change mixedMoment B node5112 node5112Labels = _
    exact sound5112 B hB hF
  have h5141 : mixedVector B (Sum.inr 5141) = Sparse.eval nodeValue5141 (mixedVector B) := by
    change mixedMoment B node5141 node5141Labels = _
    exact sound5141 B hB hF
  have h5187 : mixedVector B (Sum.inr 5187) = Sparse.eval nodeValue5187 (mixedVector B) := by
    change mixedMoment B node5187 node5187Labels = _
    exact sound5187 B hB hF
  have h5339 : mixedVector B (Sum.inr 5339) = Sparse.eval nodeValue5339 (mixedVector B) := by
    change mixedMoment B node5339 node5339Labels = _
    exact sound5339 B hB hF
  have h5353 : mixedVector B (Sum.inr 5353) = Sparse.eval nodeValue5353 (mixedVector B) := by
    change mixedMoment B node5353 node5353Labels = _
    exact sound5353 B hB hF
  have h5355 : mixedVector B (Sum.inr 5355) = Sparse.eval nodeValue5355 (mixedVector B) := by
    change mixedMoment B node5355 node5355Labels = _
    exact sound5355 B hB hF
  have h5365 : mixedVector B (Sum.inr 5365) = Sparse.eval nodeValue5365 (mixedVector B) := by
    change mixedMoment B node5365 node5365Labels = _
    exact sound5365 B hB hF
  have h5367 : mixedVector B (Sum.inr 5367) = Sparse.eval nodeValue5367 (mixedVector B) := by
    change mixedMoment B node5367 node5367Labels = _
    exact sound5367 B hB hF
  have h5400 : mixedVector B (Sum.inr 5400) = Sparse.eval nodeValue5400 (mixedVector B) := by
    change mixedMoment B node5400 node5400Labels = _
    exact sound5400 B hB hF
  have h5405 : mixedVector B (Sum.inr 5405) = Sparse.eval nodeValue5405 (mixedVector B) := by
    change mixedMoment B node5405 node5405Labels = _
    exact sound5405 B hB hF
  have h5409 : mixedVector B (Sum.inr 5409) = Sparse.eval nodeValue5409 (mixedVector B) := by
    change mixedMoment B node5409 node5409Labels = _
    exact sound5409 B hB hF
  have h5414 : mixedVector B (Sum.inr 5414) = Sparse.eval nodeValue5414 (mixedVector B) := by
    change mixedMoment B node5414 node5414Labels = _
    exact sound5414 B hB hF
  have h5428 : mixedVector B (Sum.inr 5428) = Sparse.eval nodeValue5428 (mixedVector B) := by
    change mixedMoment B node5428 node5428Labels = _
    exact sound5428 B hB hF
  have h5471 : mixedVector B (Sum.inr 5471) = Sparse.eval nodeValue5471 (mixedVector B) := by
    change mixedMoment B node5471 node5471Labels = _
    exact sound5471 B hB hF
  simpa only [sourceForm2618, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4929, h4931, h4939, h4956, h4957, h4971, h5072, h5112, h5141, h5187, h5339, h5353, h5355, h5365, h5367, h5400, h5405, h5409, h5414, h5428, h5471, reducedSource2086] using sourceEq2618 B hB

theorem rowSound2086 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2086 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2086, numericCheck2086, reducedZero2086 B hB hF, mul_zero]

theorem reducedZero2087 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2087 (mixedVector B) = 0 := by
  have h3403 : mixedVector B (Sum.inr 3403) = Sparse.eval nodeValue3403 (mixedVector B) := by
    change mixedMoment B node3403 node3403Labels = _
    exact sound3403 B hB hF
  have h3404 : mixedVector B (Sum.inr 3404) = Sparse.eval nodeValue3404 (mixedVector B) := by
    change mixedMoment B node3404 node3404Labels = _
    exact sound3404 B hB hF
  have h3406 : mixedVector B (Sum.inr 3406) = Sparse.eval nodeValue3406 (mixedVector B) := by
    change mixedMoment B node3406 node3406Labels = _
    exact sound3406 B hB hF
  have h3459 : mixedVector B (Sum.inr 3459) = Sparse.eval nodeValue3459 (mixedVector B) := by
    change mixedMoment B node3459 node3459Labels = _
    exact sound3459 B hB hF
  have h3509 : mixedVector B (Sum.inr 3509) = Sparse.eval nodeValue3509 (mixedVector B) := by
    change mixedMoment B node3509 node3509Labels = _
    exact sound3509 B hB hF
  have h3510 : mixedVector B (Sum.inr 3510) = Sparse.eval nodeValue3510 (mixedVector B) := by
    change mixedMoment B node3510 node3510Labels = _
    exact sound3510 B hB hF
  have h3522 : mixedVector B (Sum.inr 3522) = Sparse.eval nodeValue3522 (mixedVector B) := by
    change mixedMoment B node3522 node3522Labels = _
    exact sound3522 B hB hF
  have h3537 : mixedVector B (Sum.inr 3537) = Sparse.eval nodeValue3537 (mixedVector B) := by
    change mixedMoment B node3537 node3537Labels = _
    exact sound3537 B hB hF
  have h3556 : mixedVector B (Sum.inr 3556) = Sparse.eval nodeValue3556 (mixedVector B) := by
    change mixedMoment B node3556 node3556Labels = _
    exact sound3556 B hB hF
  have h3590 : mixedVector B (Sum.inr 3590) = Sparse.eval nodeValue3590 (mixedVector B) := by
    change mixedMoment B node3590 node3590Labels = _
    exact sound3590 B hB hF
  have h3758 : mixedVector B (Sum.inr 3758) = Sparse.eval nodeValue3758 (mixedVector B) := by
    change mixedMoment B node3758 node3758Labels = _
    exact sound3758 B hB hF
  have h3760 : mixedVector B (Sum.inr 3760) = Sparse.eval nodeValue3760 (mixedVector B) := by
    change mixedMoment B node3760 node3760Labels = _
    exact sound3760 B hB hF
  have h3761 : mixedVector B (Sum.inr 3761) = Sparse.eval nodeValue3761 (mixedVector B) := by
    change mixedMoment B node3761 node3761Labels = _
    exact sound3761 B hB hF
  have h3766 : mixedVector B (Sum.inr 3766) = Sparse.eval nodeValue3766 (mixedVector B) := by
    change mixedMoment B node3766 node3766Labels = _
    exact sound3766 B hB hF
  have h3770 : mixedVector B (Sum.inr 3770) = Sparse.eval nodeValue3770 (mixedVector B) := by
    change mixedMoment B node3770 node3770Labels = _
    exact sound3770 B hB hF
  have h3799 : mixedVector B (Sum.inr 3799) = Sparse.eval nodeValue3799 (mixedVector B) := by
    change mixedMoment B node3799 node3799Labels = _
    exact sound3799 B hB hF
  have h3800 : mixedVector B (Sum.inr 3800) = Sparse.eval nodeValue3800 (mixedVector B) := by
    change mixedMoment B node3800 node3800Labels = _
    exact sound3800 B hB hF
  have h3807 : mixedVector B (Sum.inr 3807) = Sparse.eval nodeValue3807 (mixedVector B) := by
    change mixedMoment B node3807 node3807Labels = _
    exact sound3807 B hB hF
  have h3845 : mixedVector B (Sum.inr 3845) = Sparse.eval nodeValue3845 (mixedVector B) := by
    change mixedMoment B node3845 node3845Labels = _
    exact sound3845 B hB hF
  have h3869 : mixedVector B (Sum.inr 3869) = Sparse.eval nodeValue3869 (mixedVector B) := by
    change mixedMoment B node3869 node3869Labels = _
    exact sound3869 B hB hF
  have h3953 : mixedVector B (Sum.inr 3953) = Sparse.eval nodeValue3953 (mixedVector B) := by
    change mixedMoment B node3953 node3953Labels = _
    exact sound3953 B hB hF
  simpa only [sourceForm2619, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3403, h3404, h3406, h3459, h3509, h3510, h3522, h3537, h3556, h3590, h3758, h3760, h3761, h3766, h3770, h3799, h3800, h3807, h3845, h3869, h3953, reducedSource2087] using sourceEq2619 B hB

theorem rowSound2087 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2087 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2087, numericCheck2087, reducedZero2087 B hB hF, mul_zero]

theorem reducedZero2088 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2088 (mixedVector B) = 0 := by
  have h4775 : mixedVector B (Sum.inr 4775) = Sparse.eval nodeValue4775 (mixedVector B) := by
    change mixedMoment B node4775 node4775Labels = _
    exact sound4775 B hB hF
  have h4776 : mixedVector B (Sum.inr 4776) = Sparse.eval nodeValue4776 (mixedVector B) := by
    change mixedMoment B node4776 node4776Labels = _
    exact sound4776 B hB hF
  have h4777 : mixedVector B (Sum.inr 4777) = Sparse.eval nodeValue4777 (mixedVector B) := by
    change mixedMoment B node4777 node4777Labels = _
    exact sound4777 B hB hF
  have h4821 : mixedVector B (Sum.inr 4821) = Sparse.eval nodeValue4821 (mixedVector B) := by
    change mixedMoment B node4821 node4821Labels = _
    exact sound4821 B hB hF
  have h4856 : mixedVector B (Sum.inr 4856) = Sparse.eval nodeValue4856 (mixedVector B) := by
    change mixedMoment B node4856 node4856Labels = _
    exact sound4856 B hB hF
  have h4942 : mixedVector B (Sum.inr 4942) = Sparse.eval nodeValue4942 (mixedVector B) := by
    change mixedMoment B node4942 node4942Labels = _
    exact sound4942 B hB hF
  have h4949 : mixedVector B (Sum.inr 4949) = Sparse.eval nodeValue4949 (mixedVector B) := by
    change mixedMoment B node4949 node4949Labels = _
    exact sound4949 B hB hF
  have h4951 : mixedVector B (Sum.inr 4951) = Sparse.eval nodeValue4951 (mixedVector B) := by
    change mixedMoment B node4951 node4951Labels = _
    exact sound4951 B hB hF
  have h4963 : mixedVector B (Sum.inr 4963) = Sparse.eval nodeValue4963 (mixedVector B) := by
    change mixedMoment B node4963 node4963Labels = _
    exact sound4963 B hB hF
  have h4966 : mixedVector B (Sum.inr 4966) = Sparse.eval nodeValue4966 (mixedVector B) := by
    change mixedMoment B node4966 node4966Labels = _
    exact sound4966 B hB hF
  have h4973 : mixedVector B (Sum.inr 4973) = Sparse.eval nodeValue4973 (mixedVector B) := by
    change mixedMoment B node4973 node4973Labels = _
    exact sound4973 B hB hF
  have h5105 : mixedVector B (Sum.inr 5105) = Sparse.eval nodeValue5105 (mixedVector B) := by
    change mixedMoment B node5105 node5105Labels = _
    exact sound5105 B hB hF
  have h5198 : mixedVector B (Sum.inr 5198) = Sparse.eval nodeValue5198 (mixedVector B) := by
    change mixedMoment B node5198 node5198Labels = _
    exact sound5198 B hB hF
  have h5336 : mixedVector B (Sum.inr 5336) = Sparse.eval nodeValue5336 (mixedVector B) := by
    change mixedMoment B node5336 node5336Labels = _
    exact sound5336 B hB hF
  have h5338 : mixedVector B (Sum.inr 5338) = Sparse.eval nodeValue5338 (mixedVector B) := by
    change mixedMoment B node5338 node5338Labels = _
    exact sound5338 B hB hF
  have h5353 : mixedVector B (Sum.inr 5353) = Sparse.eval nodeValue5353 (mixedVector B) := by
    change mixedMoment B node5353 node5353Labels = _
    exact sound5353 B hB hF
  have h5355 : mixedVector B (Sum.inr 5355) = Sparse.eval nodeValue5355 (mixedVector B) := by
    change mixedMoment B node5355 node5355Labels = _
    exact sound5355 B hB hF
  have h5360 : mixedVector B (Sum.inr 5360) = Sparse.eval nodeValue5360 (mixedVector B) := by
    change mixedMoment B node5360 node5360Labels = _
    exact sound5360 B hB hF
  have h5361 : mixedVector B (Sum.inr 5361) = Sparse.eval nodeValue5361 (mixedVector B) := by
    change mixedMoment B node5361 node5361Labels = _
    exact sound5361 B hB hF
  have h5365 : mixedVector B (Sum.inr 5365) = Sparse.eval nodeValue5365 (mixedVector B) := by
    change mixedMoment B node5365 node5365Labels = _
    exact sound5365 B hB hF
  have h5367 : mixedVector B (Sum.inr 5367) = Sparse.eval nodeValue5367 (mixedVector B) := by
    change mixedMoment B node5367 node5367Labels = _
    exact sound5367 B hB hF
  have h5368 : mixedVector B (Sum.inr 5368) = Sparse.eval nodeValue5368 (mixedVector B) := by
    change mixedMoment B node5368 node5368Labels = _
    exact sound5368 B hB hF
  have h5397 : mixedVector B (Sum.inr 5397) = Sparse.eval nodeValue5397 (mixedVector B) := by
    change mixedMoment B node5397 node5397Labels = _
    exact sound5397 B hB hF
  have h5410 : mixedVector B (Sum.inr 5410) = Sparse.eval nodeValue5410 (mixedVector B) := by
    change mixedMoment B node5410 node5410Labels = _
    exact sound5410 B hB hF
  have h5411 : mixedVector B (Sum.inr 5411) = Sparse.eval nodeValue5411 (mixedVector B) := by
    change mixedMoment B node5411 node5411Labels = _
    exact sound5411 B hB hF
  have h5412 : mixedVector B (Sum.inr 5412) = Sparse.eval nodeValue5412 (mixedVector B) := by
    change mixedMoment B node5412 node5412Labels = _
    exact sound5412 B hB hF
  have h5421 : mixedVector B (Sum.inr 5421) = Sparse.eval nodeValue5421 (mixedVector B) := by
    change mixedMoment B node5421 node5421Labels = _
    exact sound5421 B hB hF
  have h5436 : mixedVector B (Sum.inr 5436) = Sparse.eval nodeValue5436 (mixedVector B) := by
    change mixedMoment B node5436 node5436Labels = _
    exact sound5436 B hB hF
  have h5446 : mixedVector B (Sum.inr 5446) = Sparse.eval nodeValue5446 (mixedVector B) := by
    change mixedMoment B node5446 node5446Labels = _
    exact sound5446 B hB hF
  have h5473 : mixedVector B (Sum.inr 5473) = Sparse.eval nodeValue5473 (mixedVector B) := by
    change mixedMoment B node5473 node5473Labels = _
    exact sound5473 B hB hF
  simpa only [sourceForm2621, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4775, h4776, h4777, h4821, h4856, h4942, h4949, h4951, h4963, h4966, h4973, h5105, h5198, h5336, h5338, h5353, h5355, h5360, h5361, h5365, h5367, h5368, h5397, h5410, h5411, h5412, h5421, h5436, h5446, h5473, reducedSource2088] using sourceEq2621 B hB

theorem rowSound2088 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2088 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2088, numericCheck2088, reducedZero2088 B hB hF, mul_zero]

theorem reducedZero2089 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2089 (mixedVector B) = 0 := by
  have h2211 : mixedVector B (Sum.inr 2211) = Sparse.eval nodeValue2211 (mixedVector B) := by
    change mixedMoment B node2211 node2211Labels = _
    exact sound2211 B hB hF
  have h2212 : mixedVector B (Sum.inr 2212) = Sparse.eval nodeValue2212 (mixedVector B) := by
    change mixedMoment B node2212 node2212Labels = _
    exact sound2212 B hB hF
  have h2217 : mixedVector B (Sum.inr 2217) = Sparse.eval nodeValue2217 (mixedVector B) := by
    change mixedMoment B node2217 node2217Labels = _
    exact sound2217 B hB hF
  have h2223 : mixedVector B (Sum.inr 2223) = Sparse.eval nodeValue2223 (mixedVector B) := by
    change mixedMoment B node2223 node2223Labels = _
    exact sound2223 B hB hF
  have h2274 : mixedVector B (Sum.inr 2274) = Sparse.eval nodeValue2274 (mixedVector B) := by
    change mixedMoment B node2274 node2274Labels = _
    exact sound2274 B hB hF
  have h3407 : mixedVector B (Sum.inr 3407) = Sparse.eval nodeValue3407 (mixedVector B) := by
    change mixedMoment B node3407 node3407Labels = _
    exact sound3407 B hB hF
  have h3417 : mixedVector B (Sum.inr 3417) = Sparse.eval nodeValue3417 (mixedVector B) := by
    change mixedMoment B node3417 node3417Labels = _
    exact sound3417 B hB hF
  have h3418 : mixedVector B (Sum.inr 3418) = Sparse.eval nodeValue3418 (mixedVector B) := by
    change mixedMoment B node3418 node3418Labels = _
    exact sound3418 B hB hF
  have h3479 : mixedVector B (Sum.inr 3479) = Sparse.eval nodeValue3479 (mixedVector B) := by
    change mixedMoment B node3479 node3479Labels = _
    exact sound3479 B hB hF
  have h3553 : mixedVector B (Sum.inr 3553) = Sparse.eval nodeValue3553 (mixedVector B) := by
    change mixedMoment B node3553 node3553Labels = _
    exact sound3553 B hB hF
  have h3555 : mixedVector B (Sum.inr 3555) = Sparse.eval nodeValue3555 (mixedVector B) := by
    change mixedMoment B node3555 node3555Labels = _
    exact sound3555 B hB hF
  have h3570 : mixedVector B (Sum.inr 3570) = Sparse.eval nodeValue3570 (mixedVector B) := by
    change mixedMoment B node3570 node3570Labels = _
    exact sound3570 B hB hF
  have h3591 : mixedVector B (Sum.inr 3591) = Sparse.eval nodeValue3591 (mixedVector B) := by
    change mixedMoment B node3591 node3591Labels = _
    exact sound3591 B hB hF
  have h3754 : mixedVector B (Sum.inr 3754) = Sparse.eval nodeValue3754 (mixedVector B) := by
    change mixedMoment B node3754 node3754Labels = _
    exact sound3754 B hB hF
  have h3755 : mixedVector B (Sum.inr 3755) = Sparse.eval nodeValue3755 (mixedVector B) := by
    change mixedMoment B node3755 node3755Labels = _
    exact sound3755 B hB hF
  have h3758 : mixedVector B (Sum.inr 3758) = Sparse.eval nodeValue3758 (mixedVector B) := by
    change mixedMoment B node3758 node3758Labels = _
    exact sound3758 B hB hF
  have h3761 : mixedVector B (Sum.inr 3761) = Sparse.eval nodeValue3761 (mixedVector B) := by
    change mixedMoment B node3761 node3761Labels = _
    exact sound3761 B hB hF
  have h3762 : mixedVector B (Sum.inr 3762) = Sparse.eval nodeValue3762 (mixedVector B) := by
    change mixedMoment B node3762 node3762Labels = _
    exact sound3762 B hB hF
  have h3766 : mixedVector B (Sum.inr 3766) = Sparse.eval nodeValue3766 (mixedVector B) := by
    change mixedMoment B node3766 node3766Labels = _
    exact sound3766 B hB hF
  have h3767 : mixedVector B (Sum.inr 3767) = Sparse.eval nodeValue3767 (mixedVector B) := by
    change mixedMoment B node3767 node3767Labels = _
    exact sound3767 B hB hF
  have h3770 : mixedVector B (Sum.inr 3770) = Sparse.eval nodeValue3770 (mixedVector B) := by
    change mixedMoment B node3770 node3770Labels = _
    exact sound3770 B hB hF
  have h3772 : mixedVector B (Sum.inr 3772) = Sparse.eval nodeValue3772 (mixedVector B) := by
    change mixedMoment B node3772 node3772Labels = _
    exact sound3772 B hB hF
  have h3796 : mixedVector B (Sum.inr 3796) = Sparse.eval nodeValue3796 (mixedVector B) := by
    change mixedMoment B node3796 node3796Labels = _
    exact sound3796 B hB hF
  have h3808 : mixedVector B (Sum.inr 3808) = Sparse.eval nodeValue3808 (mixedVector B) := by
    change mixedMoment B node3808 node3808Labels = _
    exact sound3808 B hB hF
  have h3813 : mixedVector B (Sum.inr 3813) = Sparse.eval nodeValue3813 (mixedVector B) := by
    change mixedMoment B node3813 node3813Labels = _
    exact sound3813 B hB hF
  have h3814 : mixedVector B (Sum.inr 3814) = Sparse.eval nodeValue3814 (mixedVector B) := by
    change mixedMoment B node3814 node3814Labels = _
    exact sound3814 B hB hF
  have h3873 : mixedVector B (Sum.inr 3873) = Sparse.eval nodeValue3873 (mixedVector B) := by
    change mixedMoment B node3873 node3873Labels = _
    exact sound3873 B hB hF
  have h3877 : mixedVector B (Sum.inr 3877) = Sparse.eval nodeValue3877 (mixedVector B) := by
    change mixedMoment B node3877 node3877Labels = _
    exact sound3877 B hB hF
  have h3884 : mixedVector B (Sum.inr 3884) = Sparse.eval nodeValue3884 (mixedVector B) := by
    change mixedMoment B node3884 node3884Labels = _
    exact sound3884 B hB hF
  have h3958 : mixedVector B (Sum.inr 3958) = Sparse.eval nodeValue3958 (mixedVector B) := by
    change mixedMoment B node3958 node3958Labels = _
    exact sound3958 B hB hF
  simpa only [sourceForm2622, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2211, h2212, h2217, h2223, h2274, h3407, h3417, h3418, h3479, h3553, h3555, h3570, h3591, h3754, h3755, h3758, h3761, h3762, h3766, h3767, h3770, h3772, h3796, h3808, h3813, h3814, h3873, h3877, h3884, h3958, reducedSource2089] using sourceEq2622 B hB

theorem rowSound2089 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2089 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2089, numericCheck2089, reducedZero2089 B hB hF, mul_zero]

theorem reducedZero2090 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2090 (mixedVector B) = 0 := by
  have h4940 : mixedVector B (Sum.inr 4940) = Sparse.eval nodeValue4940 (mixedVector B) := by
    change mixedMoment B node4940 node4940Labels = _
    exact sound4940 B hB hF
  have h4944 : mixedVector B (Sum.inr 4944) = Sparse.eval nodeValue4944 (mixedVector B) := by
    change mixedMoment B node4944 node4944Labels = _
    exact sound4944 B hB hF
  have h4946 : mixedVector B (Sum.inr 4946) = Sparse.eval nodeValue4946 (mixedVector B) := by
    change mixedMoment B node4946 node4946Labels = _
    exact sound4946 B hB hF
  have h4951 : mixedVector B (Sum.inr 4951) = Sparse.eval nodeValue4951 (mixedVector B) := by
    change mixedMoment B node4951 node4951Labels = _
    exact sound4951 B hB hF
  have h4964 : mixedVector B (Sum.inr 4964) = Sparse.eval nodeValue4964 (mixedVector B) := by
    change mixedMoment B node4964 node4964Labels = _
    exact sound4964 B hB hF
  have h4965 : mixedVector B (Sum.inr 4965) = Sparse.eval nodeValue4965 (mixedVector B) := by
    change mixedMoment B node4965 node4965Labels = _
    exact sound4965 B hB hF
  have h4966 : mixedVector B (Sum.inr 4966) = Sparse.eval nodeValue4966 (mixedVector B) := by
    change mixedMoment B node4966 node4966Labels = _
    exact sound4966 B hB hF
  have h4977 : mixedVector B (Sum.inr 4977) = Sparse.eval nodeValue4977 (mixedVector B) := by
    change mixedMoment B node4977 node4977Labels = _
    exact sound4977 B hB hF
  have h5044 : mixedVector B (Sum.inr 5044) = Sparse.eval nodeValue5044 (mixedVector B) := by
    change mixedMoment B node5044 node5044Labels = _
    exact sound5044 B hB hF
  have h5090 : mixedVector B (Sum.inr 5090) = Sparse.eval nodeValue5090 (mixedVector B) := by
    change mixedMoment B node5090 node5090Labels = _
    exact sound5090 B hB hF
  have h5102 : mixedVector B (Sum.inr 5102) = Sparse.eval nodeValue5102 (mixedVector B) := by
    change mixedMoment B node5102 node5102Labels = _
    exact sound5102 B hB hF
  have h5199 : mixedVector B (Sum.inr 5199) = Sparse.eval nodeValue5199 (mixedVector B) := by
    change mixedMoment B node5199 node5199Labels = _
    exact sound5199 B hB hF
  have h5207 : mixedVector B (Sum.inr 5207) = Sparse.eval nodeValue5207 (mixedVector B) := by
    change mixedMoment B node5207 node5207Labels = _
    exact sound5207 B hB hF
  have h5335 : mixedVector B (Sum.inr 5335) = Sparse.eval nodeValue5335 (mixedVector B) := by
    change mixedMoment B node5335 node5335Labels = _
    exact sound5335 B hB hF
  have h5338 : mixedVector B (Sum.inr 5338) = Sparse.eval nodeValue5338 (mixedVector B) := by
    change mixedMoment B node5338 node5338Labels = _
    exact sound5338 B hB hF
  have h5359 : mixedVector B (Sum.inr 5359) = Sparse.eval nodeValue5359 (mixedVector B) := by
    change mixedMoment B node5359 node5359Labels = _
    exact sound5359 B hB hF
  have h5361 : mixedVector B (Sum.inr 5361) = Sparse.eval nodeValue5361 (mixedVector B) := by
    change mixedMoment B node5361 node5361Labels = _
    exact sound5361 B hB hF
  have h5365 : mixedVector B (Sum.inr 5365) = Sparse.eval nodeValue5365 (mixedVector B) := by
    change mixedMoment B node5365 node5365Labels = _
    exact sound5365 B hB hF
  have h5367 : mixedVector B (Sum.inr 5367) = Sparse.eval nodeValue5367 (mixedVector B) := by
    change mixedMoment B node5367 node5367Labels = _
    exact sound5367 B hB hF
  have h5368 : mixedVector B (Sum.inr 5368) = Sparse.eval nodeValue5368 (mixedVector B) := by
    change mixedMoment B node5368 node5368Labels = _
    exact sound5368 B hB hF
  have h5370 : mixedVector B (Sum.inr 5370) = Sparse.eval nodeValue5370 (mixedVector B) := by
    change mixedMoment B node5370 node5370Labels = _
    exact sound5370 B hB hF
  have h5371 : mixedVector B (Sum.inr 5371) = Sparse.eval nodeValue5371 (mixedVector B) := by
    change mixedMoment B node5371 node5371Labels = _
    exact sound5371 B hB hF
  have h5395 : mixedVector B (Sum.inr 5395) = Sparse.eval nodeValue5395 (mixedVector B) := by
    change mixedMoment B node5395 node5395Labels = _
    exact sound5395 B hB hF
  have h5410 : mixedVector B (Sum.inr 5410) = Sparse.eval nodeValue5410 (mixedVector B) := by
    change mixedMoment B node5410 node5410Labels = _
    exact sound5410 B hB hF
  have h5411 : mixedVector B (Sum.inr 5411) = Sparse.eval nodeValue5411 (mixedVector B) := by
    change mixedMoment B node5411 node5411Labels = _
    exact sound5411 B hB hF
  have h5413 : mixedVector B (Sum.inr 5413) = Sparse.eval nodeValue5413 (mixedVector B) := by
    change mixedMoment B node5413 node5413Labels = _
    exact sound5413 B hB hF
  have h5446 : mixedVector B (Sum.inr 5446) = Sparse.eval nodeValue5446 (mixedVector B) := by
    change mixedMoment B node5446 node5446Labels = _
    exact sound5446 B hB hF
  have h5468 : mixedVector B (Sum.inr 5468) = Sparse.eval nodeValue5468 (mixedVector B) := by
    change mixedMoment B node5468 node5468Labels = _
    exact sound5468 B hB hF
  have h5473 : mixedVector B (Sum.inr 5473) = Sparse.eval nodeValue5473 (mixedVector B) := by
    change mixedMoment B node5473 node5473Labels = _
    exact sound5473 B hB hF
  have h5475 : mixedVector B (Sum.inr 5475) = Sparse.eval nodeValue5475 (mixedVector B) := by
    change mixedMoment B node5475 node5475Labels = _
    exact sound5475 B hB hF
  simpa only [sourceForm2624, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4940, h4944, h4946, h4951, h4964, h4965, h4966, h4977, h5044, h5090, h5102, h5199, h5207, h5335, h5338, h5359, h5361, h5365, h5367, h5368, h5370, h5371, h5395, h5410, h5411, h5413, h5446, h5468, h5473, h5475, reducedSource2090] using sourceEq2624 B hB

theorem rowSound2090 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2090 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2090, numericCheck2090, reducedZero2090 B hB hF, mul_zero]

theorem reducedZero2091 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2091 (mixedVector B) = 0 := by
  have h3405 : mixedVector B (Sum.inr 3405) = Sparse.eval nodeValue3405 (mixedVector B) := by
    change mixedMoment B node3405 node3405Labels = _
    exact sound3405 B hB hF
  have h3412 : mixedVector B (Sum.inr 3412) = Sparse.eval nodeValue3412 (mixedVector B) := by
    change mixedMoment B node3412 node3412Labels = _
    exact sound3412 B hB hF
  have h3413 : mixedVector B (Sum.inr 3413) = Sparse.eval nodeValue3413 (mixedVector B) := by
    change mixedMoment B node3413 node3413Labels = _
    exact sound3413 B hB hF
  have h3418 : mixedVector B (Sum.inr 3418) = Sparse.eval nodeValue3418 (mixedVector B) := by
    change mixedMoment B node3418 node3418Labels = _
    exact sound3418 B hB hF
  have h3471 : mixedVector B (Sum.inr 3471) = Sparse.eval nodeValue3471 (mixedVector B) := by
    change mixedMoment B node3471 node3471Labels = _
    exact sound3471 B hB hF
  have h3474 : mixedVector B (Sum.inr 3474) = Sparse.eval nodeValue3474 (mixedVector B) := by
    change mixedMoment B node3474 node3474Labels = _
    exact sound3474 B hB hF
  have h3475 : mixedVector B (Sum.inr 3475) = Sparse.eval nodeValue3475 (mixedVector B) := by
    change mixedMoment B node3475 node3475Labels = _
    exact sound3475 B hB hF
  have h3480 : mixedVector B (Sum.inr 3480) = Sparse.eval nodeValue3480 (mixedVector B) := by
    change mixedMoment B node3480 node3480Labels = _
    exact sound3480 B hB hF
  have h3554 : mixedVector B (Sum.inr 3554) = Sparse.eval nodeValue3554 (mixedVector B) := by
    change mixedMoment B node3554 node3554Labels = _
    exact sound3554 B hB hF
  have h3555 : mixedVector B (Sum.inr 3555) = Sparse.eval nodeValue3555 (mixedVector B) := by
    change mixedMoment B node3555 node3555Labels = _
    exact sound3555 B hB hF
  have h3578 : mixedVector B (Sum.inr 3578) = Sparse.eval nodeValue3578 (mixedVector B) := by
    change mixedMoment B node3578 node3578Labels = _
    exact sound3578 B hB hF
  have h3595 : mixedVector B (Sum.inr 3595) = Sparse.eval nodeValue3595 (mixedVector B) := by
    change mixedMoment B node3595 node3595Labels = _
    exact sound3595 B hB hF
  have h3631 : mixedVector B (Sum.inr 3631) = Sparse.eval nodeValue3631 (mixedVector B) := by
    change mixedMoment B node3631 node3631Labels = _
    exact sound3631 B hB hF
  have h3753 : mixedVector B (Sum.inr 3753) = Sparse.eval nodeValue3753 (mixedVector B) := by
    change mixedMoment B node3753 node3753Labels = _
    exact sound3753 B hB hF
  have h3755 : mixedVector B (Sum.inr 3755) = Sparse.eval nodeValue3755 (mixedVector B) := by
    change mixedMoment B node3755 node3755Labels = _
    exact sound3755 B hB hF
  have h3758 : mixedVector B (Sum.inr 3758) = Sparse.eval nodeValue3758 (mixedVector B) := by
    change mixedMoment B node3758 node3758Labels = _
    exact sound3758 B hB hF
  have h3759 : mixedVector B (Sum.inr 3759) = Sparse.eval nodeValue3759 (mixedVector B) := by
    change mixedMoment B node3759 node3759Labels = _
    exact sound3759 B hB hF
  have h3766 : mixedVector B (Sum.inr 3766) = Sparse.eval nodeValue3766 (mixedVector B) := by
    change mixedMoment B node3766 node3766Labels = _
    exact sound3766 B hB hF
  have h3767 : mixedVector B (Sum.inr 3767) = Sparse.eval nodeValue3767 (mixedVector B) := by
    change mixedMoment B node3767 node3767Labels = _
    exact sound3767 B hB hF
  have h3771 : mixedVector B (Sum.inr 3771) = Sparse.eval nodeValue3771 (mixedVector B) := by
    change mixedMoment B node3771 node3771Labels = _
    exact sound3771 B hB hF
  have h3772 : mixedVector B (Sum.inr 3772) = Sparse.eval nodeValue3772 (mixedVector B) := by
    change mixedMoment B node3772 node3772Labels = _
    exact sound3772 B hB hF
  have h3775 : mixedVector B (Sum.inr 3775) = Sparse.eval nodeValue3775 (mixedVector B) := by
    change mixedMoment B node3775 node3775Labels = _
    exact sound3775 B hB hF
  have h3794 : mixedVector B (Sum.inr 3794) = Sparse.eval nodeValue3794 (mixedVector B) := by
    change mixedMoment B node3794 node3794Labels = _
    exact sound3794 B hB hF
  have h3808 : mixedVector B (Sum.inr 3808) = Sparse.eval nodeValue3808 (mixedVector B) := by
    change mixedMoment B node3808 node3808Labels = _
    exact sound3808 B hB hF
  have h3809 : mixedVector B (Sum.inr 3809) = Sparse.eval nodeValue3809 (mixedVector B) := by
    change mixedMoment B node3809 node3809Labels = _
    exact sound3809 B hB hF
  have h3817 : mixedVector B (Sum.inr 3817) = Sparse.eval nodeValue3817 (mixedVector B) := by
    change mixedMoment B node3817 node3817Labels = _
    exact sound3817 B hB hF
  have h3950 : mixedVector B (Sum.inr 3950) = Sparse.eval nodeValue3950 (mixedVector B) := by
    change mixedMoment B node3950 node3950Labels = _
    exact sound3950 B hB hF
  have h3958 : mixedVector B (Sum.inr 3958) = Sparse.eval nodeValue3958 (mixedVector B) := by
    change mixedMoment B node3958 node3958Labels = _
    exact sound3958 B hB hF
  have h3959 : mixedVector B (Sum.inr 3959) = Sparse.eval nodeValue3959 (mixedVector B) := by
    change mixedMoment B node3959 node3959Labels = _
    exact sound3959 B hB hF
  have h3963 : mixedVector B (Sum.inr 3963) = Sparse.eval nodeValue3963 (mixedVector B) := by
    change mixedMoment B node3963 node3963Labels = _
    exact sound3963 B hB hF
  simpa only [sourceForm2625, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3405, h3412, h3413, h3418, h3471, h3474, h3475, h3480, h3554, h3555, h3578, h3595, h3631, h3753, h3755, h3758, h3759, h3766, h3767, h3771, h3772, h3775, h3794, h3808, h3809, h3817, h3950, h3958, h3959, h3963, reducedSource2091] using sourceEq2625 B hB

theorem rowSound2091 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2091 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2091, numericCheck2091, reducedZero2091 B hB hF, mul_zero]

theorem reducedZero2092 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2092 (mixedVector B) = 0 := by
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  have h4941 : mixedVector B (Sum.inr 4941) = Sparse.eval nodeValue4941 (mixedVector B) := by
    change mixedMoment B node4941 node4941Labels = _
    exact sound4941 B hB hF
  have h4948 : mixedVector B (Sum.inr 4948) = Sparse.eval nodeValue4948 (mixedVector B) := by
    change mixedMoment B node4948 node4948Labels = _
    exact sound4948 B hB hF
  have h4950 : mixedVector B (Sum.inr 4950) = Sparse.eval nodeValue4950 (mixedVector B) := by
    change mixedMoment B node4950 node4950Labels = _
    exact sound4950 B hB hF
  have h4968 : mixedVector B (Sum.inr 4968) = Sparse.eval nodeValue4968 (mixedVector B) := by
    change mixedMoment B node4968 node4968Labels = _
    exact sound4968 B hB hF
  have h4970 : mixedVector B (Sum.inr 4970) = Sparse.eval nodeValue4970 (mixedVector B) := by
    change mixedMoment B node4970 node4970Labels = _
    exact sound4970 B hB hF
  have h4974 : mixedVector B (Sum.inr 4974) = Sparse.eval nodeValue4974 (mixedVector B) := by
    change mixedMoment B node4974 node4974Labels = _
    exact sound4974 B hB hF
  have h5104 : mixedVector B (Sum.inr 5104) = Sparse.eval nodeValue5104 (mixedVector B) := by
    change mixedMoment B node5104 node5104Labels = _
    exact sound5104 B hB hF
  have h5117 : mixedVector B (Sum.inr 5117) = Sparse.eval nodeValue5117 (mixedVector B) := by
    change mixedMoment B node5117 node5117Labels = _
    exact sound5117 B hB hF
  have h5152 : mixedVector B (Sum.inr 5152) = Sparse.eval nodeValue5152 (mixedVector B) := by
    change mixedMoment B node5152 node5152Labels = _
    exact sound5152 B hB hF
  have h5203 : mixedVector B (Sum.inr 5203) = Sparse.eval nodeValue5203 (mixedVector B) := by
    change mixedMoment B node5203 node5203Labels = _
    exact sound5203 B hB hF
  have h5337 : mixedVector B (Sum.inr 5337) = Sparse.eval nodeValue5337 (mixedVector B) := by
    change mixedMoment B node5337 node5337Labels = _
    exact sound5337 B hB hF
  have h5352 : mixedVector B (Sum.inr 5352) = Sparse.eval nodeValue5352 (mixedVector B) := by
    change mixedMoment B node5352 node5352Labels = _
    exact sound5352 B hB hF
  have h5356 : mixedVector B (Sum.inr 5356) = Sparse.eval nodeValue5356 (mixedVector B) := by
    change mixedMoment B node5356 node5356Labels = _
    exact sound5356 B hB hF
  have h5366 : mixedVector B (Sum.inr 5366) = Sparse.eval nodeValue5366 (mixedVector B) := by
    change mixedMoment B node5366 node5366Labels = _
    exact sound5366 B hB hF
  have h5369 : mixedVector B (Sum.inr 5369) = Sparse.eval nodeValue5369 (mixedVector B) := by
    change mixedMoment B node5369 node5369Labels = _
    exact sound5369 B hB hF
  have h5396 : mixedVector B (Sum.inr 5396) = Sparse.eval nodeValue5396 (mixedVector B) := by
    change mixedMoment B node5396 node5396Labels = _
    exact sound5396 B hB hF
  have h5410 : mixedVector B (Sum.inr 5410) = Sparse.eval nodeValue5410 (mixedVector B) := by
    change mixedMoment B node5410 node5410Labels = _
    exact sound5410 B hB hF
  have h5469 : mixedVector B (Sum.inr 5469) = Sparse.eval nodeValue5469 (mixedVector B) := by
    change mixedMoment B node5469 node5469Labels = _
    exact sound5469 B hB hF
  have h5473 : mixedVector B (Sum.inr 5473) = Sparse.eval nodeValue5473 (mixedVector B) := by
    change mixedMoment B node5473 node5473Labels = _
    exact sound5473 B hB hF
  have h5474 : mixedVector B (Sum.inr 5474) = Sparse.eval nodeValue5474 (mixedVector B) := by
    change mixedMoment B node5474 node5474Labels = _
    exact sound5474 B hB hF
  simpa only [sourceForm2627, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4091, h4941, h4948, h4950, h4968, h4970, h4974, h5104, h5117, h5152, h5203, h5337, h5352, h5356, h5366, h5369, h5396, h5410, h5469, h5473, h5474, reducedSource2092] using sourceEq2627 B hB

theorem rowSound2092 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2092 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2092, numericCheck2092, reducedZero2092 B hB hF, mul_zero]

theorem reducedZero2093 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2093 (mixedVector B) = 0 := by
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  have h4939 : mixedVector B (Sum.inr 4939) = Sparse.eval nodeValue4939 (mixedVector B) := by
    change mixedMoment B node4939 node4939Labels = _
    exact sound4939 B hB hF
  have h4943 : mixedVector B (Sum.inr 4943) = Sparse.eval nodeValue4943 (mixedVector B) := by
    change mixedMoment B node4943 node4943Labels = _
    exact sound4943 B hB hF
  have h4946 : mixedVector B (Sum.inr 4946) = Sparse.eval nodeValue4946 (mixedVector B) := by
    change mixedMoment B node4946 node4946Labels = _
    exact sound4946 B hB hF
  have h4949 : mixedVector B (Sum.inr 4949) = Sparse.eval nodeValue4949 (mixedVector B) := by
    change mixedMoment B node4949 node4949Labels = _
    exact sound4949 B hB hF
  have h4971 : mixedVector B (Sum.inr 4971) = Sparse.eval nodeValue4971 (mixedVector B) := by
    change mixedMoment B node4971 node4971Labels = _
    exact sound4971 B hB hF
  have h4972 : mixedVector B (Sum.inr 4972) = Sparse.eval nodeValue4972 (mixedVector B) := by
    change mixedMoment B node4972 node4972Labels = _
    exact sound4972 B hB hF
  have h4973 : mixedVector B (Sum.inr 4973) = Sparse.eval nodeValue4973 (mixedVector B) := by
    change mixedMoment B node4973 node4973Labels = _
    exact sound4973 B hB hF
  have h4977 : mixedVector B (Sum.inr 4977) = Sparse.eval nodeValue4977 (mixedVector B) := by
    change mixedMoment B node4977 node4977Labels = _
    exact sound4977 B hB hF
  have h5036 : mixedVector B (Sum.inr 5036) = Sparse.eval nodeValue5036 (mixedVector B) := by
    change mixedMoment B node5036 node5036Labels = _
    exact sound5036 B hB hF
  have h5101 : mixedVector B (Sum.inr 5101) = Sparse.eval nodeValue5101 (mixedVector B) := by
    change mixedMoment B node5101 node5101Labels = _
    exact sound5101 B hB hF
  have h5111 : mixedVector B (Sum.inr 5111) = Sparse.eval nodeValue5111 (mixedVector B) := by
    change mixedMoment B node5111 node5111Labels = _
    exact sound5111 B hB hF
  have h5141 : mixedVector B (Sum.inr 5141) = Sparse.eval nodeValue5141 (mixedVector B) := by
    change mixedMoment B node5141 node5141Labels = _
    exact sound5141 B hB hF
  have h5204 : mixedVector B (Sum.inr 5204) = Sparse.eval nodeValue5204 (mixedVector B) := by
    change mixedMoment B node5204 node5204Labels = _
    exact sound5204 B hB hF
  have h5335 : mixedVector B (Sum.inr 5335) = Sparse.eval nodeValue5335 (mixedVector B) := by
    change mixedMoment B node5335 node5335Labels = _
    exact sound5335 B hB hF
  have h5336 : mixedVector B (Sum.inr 5336) = Sparse.eval nodeValue5336 (mixedVector B) := by
    change mixedMoment B node5336 node5336Labels = _
    exact sound5336 B hB hF
  have h5351 : mixedVector B (Sum.inr 5351) = Sparse.eval nodeValue5351 (mixedVector B) := by
    change mixedMoment B node5351 node5351Labels = _
    exact sound5351 B hB hF
  have h5355 : mixedVector B (Sum.inr 5355) = Sparse.eval nodeValue5355 (mixedVector B) := by
    change mixedMoment B node5355 node5355Labels = _
    exact sound5355 B hB hF
  have h5365 : mixedVector B (Sum.inr 5365) = Sparse.eval nodeValue5365 (mixedVector B) := by
    change mixedMoment B node5365 node5365Labels = _
    exact sound5365 B hB hF
  have h5367 : mixedVector B (Sum.inr 5367) = Sparse.eval nodeValue5367 (mixedVector B) := by
    change mixedMoment B node5367 node5367Labels = _
    exact sound5367 B hB hF
  have h5368 : mixedVector B (Sum.inr 5368) = Sparse.eval nodeValue5368 (mixedVector B) := by
    change mixedMoment B node5368 node5368Labels = _
    exact sound5368 B hB hF
  have h5370 : mixedVector B (Sum.inr 5370) = Sparse.eval nodeValue5370 (mixedVector B) := by
    change mixedMoment B node5370 node5370Labels = _
    exact sound5370 B hB hF
  have h5371 : mixedVector B (Sum.inr 5371) = Sparse.eval nodeValue5371 (mixedVector B) := by
    change mixedMoment B node5371 node5371Labels = _
    exact sound5371 B hB hF
  have h5394 : mixedVector B (Sum.inr 5394) = Sparse.eval nodeValue5394 (mixedVector B) := by
    change mixedMoment B node5394 node5394Labels = _
    exact sound5394 B hB hF
  have h5395 : mixedVector B (Sum.inr 5395) = Sparse.eval nodeValue5395 (mixedVector B) := by
    change mixedMoment B node5395 node5395Labels = _
    exact sound5395 B hB hF
  have h5409 : mixedVector B (Sum.inr 5409) = Sparse.eval nodeValue5409 (mixedVector B) := by
    change mixedMoment B node5409 node5409Labels = _
    exact sound5409 B hB hF
  have h5410 : mixedVector B (Sum.inr 5410) = Sparse.eval nodeValue5410 (mixedVector B) := by
    change mixedMoment B node5410 node5410Labels = _
    exact sound5410 B hB hF
  have h5413 : mixedVector B (Sum.inr 5413) = Sparse.eval nodeValue5413 (mixedVector B) := by
    change mixedMoment B node5413 node5413Labels = _
    exact sound5413 B hB hF
  have h5428 : mixedVector B (Sum.inr 5428) = Sparse.eval nodeValue5428 (mixedVector B) := by
    change mixedMoment B node5428 node5428Labels = _
    exact sound5428 B hB hF
  have h5473 : mixedVector B (Sum.inr 5473) = Sparse.eval nodeValue5473 (mixedVector B) := by
    change mixedMoment B node5473 node5473Labels = _
    exact sound5473 B hB hF
  simpa only [sourceForm2628, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4092, h4939, h4943, h4946, h4949, h4971, h4972, h4973, h4977, h5036, h5101, h5111, h5141, h5204, h5335, h5336, h5351, h5355, h5365, h5367, h5368, h5370, h5371, h5394, h5395, h5409, h5410, h5413, h5428, h5473, reducedSource2093] using sourceEq2628 B hB

theorem rowSound2093 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2093 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2093, numericCheck2093, reducedZero2093 B hB hF, mul_zero]

theorem reducedZero2094 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2094 (mixedVector B) = 0 := by
  have h4763 : mixedVector B (Sum.inr 4763) = Sparse.eval nodeValue4763 (mixedVector B) := by
    change mixedMoment B node4763 node4763Labels = _
    exact sound4763 B hB hF
  have h4769 : mixedVector B (Sum.inr 4769) = Sparse.eval nodeValue4769 (mixedVector B) := by
    change mixedMoment B node4769 node4769Labels = _
    exact sound4769 B hB hF
  have h4770 : mixedVector B (Sum.inr 4770) = Sparse.eval nodeValue4770 (mixedVector B) := by
    change mixedMoment B node4770 node4770Labels = _
    exact sound4770 B hB hF
  have h4846 : mixedVector B (Sum.inr 4846) = Sparse.eval nodeValue4846 (mixedVector B) := by
    change mixedMoment B node4846 node4846Labels = _
    exact sound4846 B hB hF
  have h4938 : mixedVector B (Sum.inr 4938) = Sparse.eval nodeValue4938 (mixedVector B) := by
    change mixedMoment B node4938 node4938Labels = _
    exact sound4938 B hB hF
  have h4945 : mixedVector B (Sum.inr 4945) = Sparse.eval nodeValue4945 (mixedVector B) := by
    change mixedMoment B node4945 node4945Labels = _
    exact sound4945 B hB hF
  have h4975 : mixedVector B (Sum.inr 4975) = Sparse.eval nodeValue4975 (mixedVector B) := by
    change mixedMoment B node4975 node4975Labels = _
    exact sound4975 B hB hF
  have h4976 : mixedVector B (Sum.inr 4976) = Sparse.eval nodeValue4976 (mixedVector B) := by
    change mixedMoment B node4976 node4976Labels = _
    exact sound4976 B hB hF
  have h5099 : mixedVector B (Sum.inr 5099) = Sparse.eval nodeValue5099 (mixedVector B) := by
    change mixedMoment B node5099 node5099Labels = _
    exact sound5099 B hB hF
  have h5205 : mixedVector B (Sum.inr 5205) = Sparse.eval nodeValue5205 (mixedVector B) := by
    change mixedMoment B node5205 node5205Labels = _
    exact sound5205 B hB hF
  have h5215 : mixedVector B (Sum.inr 5215) = Sparse.eval nodeValue5215 (mixedVector B) := by
    change mixedMoment B node5215 node5215Labels = _
    exact sound5215 B hB hF
  have h5238 : mixedVector B (Sum.inr 5238) = Sparse.eval nodeValue5238 (mixedVector B) := by
    change mixedMoment B node5238 node5238Labels = _
    exact sound5238 B hB hF
  have h5241 : mixedVector B (Sum.inr 5241) = Sparse.eval nodeValue5241 (mixedVector B) := by
    change mixedMoment B node5241 node5241Labels = _
    exact sound5241 B hB hF
  have h5242 : mixedVector B (Sum.inr 5242) = Sparse.eval nodeValue5242 (mixedVector B) := by
    change mixedMoment B node5242 node5242Labels = _
    exact sound5242 B hB hF
  have h5248 : mixedVector B (Sum.inr 5248) = Sparse.eval nodeValue5248 (mixedVector B) := by
    change mixedMoment B node5248 node5248Labels = _
    exact sound5248 B hB hF
  have h5274 : mixedVector B (Sum.inr 5274) = Sparse.eval nodeValue5274 (mixedVector B) := by
    change mixedMoment B node5274 node5274Labels = _
    exact sound5274 B hB hF
  have h5275 : mixedVector B (Sum.inr 5275) = Sparse.eval nodeValue5275 (mixedVector B) := by
    change mixedMoment B node5275 node5275Labels = _
    exact sound5275 B hB hF
  have h5277 : mixedVector B (Sum.inr 5277) = Sparse.eval nodeValue5277 (mixedVector B) := by
    change mixedMoment B node5277 node5277Labels = _
    exact sound5277 B hB hF
  have h5282 : mixedVector B (Sum.inr 5282) = Sparse.eval nodeValue5282 (mixedVector B) := by
    change mixedMoment B node5282 node5282Labels = _
    exact sound5282 B hB hF
  have h5284 : mixedVector B (Sum.inr 5284) = Sparse.eval nodeValue5284 (mixedVector B) := by
    change mixedMoment B node5284 node5284Labels = _
    exact sound5284 B hB hF
  have h5287 : mixedVector B (Sum.inr 5287) = Sparse.eval nodeValue5287 (mixedVector B) := by
    change mixedMoment B node5287 node5287Labels = _
    exact sound5287 B hB hF
  simpa only [sourceForm2629, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4763, h4769, h4770, h4846, h4938, h4945, h4975, h4976, h5099, h5205, h5215, h5238, h5241, h5242, h5248, h5274, h5275, h5277, h5282, h5284, h5287, reducedSource2094] using sourceEq2629 B hB

theorem rowSound2094 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2094 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2094, numericCheck2094, reducedZero2094 B hB hF, mul_zero]

theorem reducedZero2095 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2095 (mixedVector B) = 0 := by
  have h2174 : mixedVector B (Sum.inr 2174) = Sparse.eval nodeValue2174 (mixedVector B) := by
    change mixedMoment B node2174 node2174Labels = _
    exact sound2174 B hB hF
  have h2185 : mixedVector B (Sum.inr 2185) = Sparse.eval nodeValue2185 (mixedVector B) := by
    change mixedMoment B node2185 node2185Labels = _
    exact sound2185 B hB hF
  have h2186 : mixedVector B (Sum.inr 2186) = Sparse.eval nodeValue2186 (mixedVector B) := by
    change mixedMoment B node2186 node2186Labels = _
    exact sound2186 B hB hF
  have h2229 : mixedVector B (Sum.inr 2229) = Sparse.eval nodeValue2229 (mixedVector B) := by
    change mixedMoment B node2229 node2229Labels = _
    exact sound2229 B hB hF
  have h2653 : mixedVector B (Sum.inr 2653) = Sparse.eval nodeValue2653 (mixedVector B) := by
    change mixedMoment B node2653 node2653Labels = _
    exact sound2653 B hB hF
  have h2658 : mixedVector B (Sum.inr 2658) = Sparse.eval nodeValue2658 (mixedVector B) := by
    change mixedMoment B node2658 node2658Labels = _
    exact sound2658 B hB hF
  have h2659 : mixedVector B (Sum.inr 2659) = Sparse.eval nodeValue2659 (mixedVector B) := by
    change mixedMoment B node2659 node2659Labels = _
    exact sound2659 B hB hF
  have h2686 : mixedVector B (Sum.inr 2686) = Sparse.eval nodeValue2686 (mixedVector B) := by
    change mixedMoment B node2686 node2686Labels = _
    exact sound2686 B hB hF
  have h2689 : mixedVector B (Sum.inr 2689) = Sparse.eval nodeValue2689 (mixedVector B) := by
    change mixedMoment B node2689 node2689Labels = _
    exact sound2689 B hB hF
  have h2690 : mixedVector B (Sum.inr 2690) = Sparse.eval nodeValue2690 (mixedVector B) := by
    change mixedMoment B node2690 node2690Labels = _
    exact sound2690 B hB hF
  have h2694 : mixedVector B (Sum.inr 2694) = Sparse.eval nodeValue2694 (mixedVector B) := by
    change mixedMoment B node2694 node2694Labels = _
    exact sound2694 B hB hF
  have h2695 : mixedVector B (Sum.inr 2695) = Sparse.eval nodeValue2695 (mixedVector B) := by
    change mixedMoment B node2695 node2695Labels = _
    exact sound2695 B hB hF
  have h2704 : mixedVector B (Sum.inr 2704) = Sparse.eval nodeValue2704 (mixedVector B) := by
    change mixedMoment B node2704 node2704Labels = _
    exact sound2704 B hB hF
  have h2705 : mixedVector B (Sum.inr 2705) = Sparse.eval nodeValue2705 (mixedVector B) := by
    change mixedMoment B node2705 node2705Labels = _
    exact sound2705 B hB hF
  have h2706 : mixedVector B (Sum.inr 2706) = Sparse.eval nodeValue2706 (mixedVector B) := by
    change mixedMoment B node2706 node2706Labels = _
    exact sound2706 B hB hF
  have h2742 : mixedVector B (Sum.inr 2742) = Sparse.eval nodeValue2742 (mixedVector B) := by
    change mixedMoment B node2742 node2742Labels = _
    exact sound2742 B hB hF
  have h2743 : mixedVector B (Sum.inr 2743) = Sparse.eval nodeValue2743 (mixedVector B) := by
    change mixedMoment B node2743 node2743Labels = _
    exact sound2743 B hB hF
  have h3025 : mixedVector B (Sum.inr 3025) = Sparse.eval nodeValue3025 (mixedVector B) := by
    change mixedMoment B node3025 node3025Labels = _
    exact sound3025 B hB hF
  have h3059 : mixedVector B (Sum.inr 3059) = Sparse.eval nodeValue3059 (mixedVector B) := by
    change mixedMoment B node3059 node3059Labels = _
    exact sound3059 B hB hF
  have h3077 : mixedVector B (Sum.inr 3077) = Sparse.eval nodeValue3077 (mixedVector B) := by
    change mixedMoment B node3077 node3077Labels = _
    exact sound3077 B hB hF
  have h3078 : mixedVector B (Sum.inr 3078) = Sparse.eval nodeValue3078 (mixedVector B) := by
    change mixedMoment B node3078 node3078Labels = _
    exact sound3078 B hB hF
  simpa only [sourceForm2630, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2174, h2185, h2186, h2229, h2653, h2658, h2659, h2686, h2689, h2690, h2694, h2695, h2704, h2705, h2706, h2742, h2743, h3025, h3059, h3077, h3078, reducedSource2095] using sourceEq2630 B hB

theorem rowSound2095 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2095 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2095, numericCheck2095, reducedZero2095 B hB hF, mul_zero]

theorem sourceRowsAt2080 : MixedData.sourceRows (2080 : Fin 2425) =
    MixedData.row2080 := by decide +kernel

theorem sourceRowsAt2081 : MixedData.sourceRows (2081 : Fin 2425) =
    MixedData.row2081 := by decide +kernel

theorem sourceRowsAt2082 : MixedData.sourceRows (2082 : Fin 2425) =
    MixedData.row2082 := by decide +kernel

theorem sourceRowsAt2083 : MixedData.sourceRows (2083 : Fin 2425) =
    MixedData.row2083 := by decide +kernel

theorem sourceRowsAt2084 : MixedData.sourceRows (2084 : Fin 2425) =
    MixedData.row2084 := by decide +kernel

theorem sourceRowsAt2085 : MixedData.sourceRows (2085 : Fin 2425) =
    MixedData.row2085 := by decide +kernel

theorem sourceRowsAt2086 : MixedData.sourceRows (2086 : Fin 2425) =
    MixedData.row2086 := by decide +kernel

theorem sourceRowsAt2087 : MixedData.sourceRows (2087 : Fin 2425) =
    MixedData.row2087 := by decide +kernel

theorem sourceRowsAt2088 : MixedData.sourceRows (2088 : Fin 2425) =
    MixedData.row2088 := by decide +kernel

theorem sourceRowsAt2089 : MixedData.sourceRows (2089 : Fin 2425) =
    MixedData.row2089 := by decide +kernel

theorem sourceRowsAt2090 : MixedData.sourceRows (2090 : Fin 2425) =
    MixedData.row2090 := by decide +kernel

theorem sourceRowsAt2091 : MixedData.sourceRows (2091 : Fin 2425) =
    MixedData.row2091 := by decide +kernel

theorem sourceRowsAt2092 : MixedData.sourceRows (2092 : Fin 2425) =
    MixedData.row2092 := by decide +kernel

theorem sourceRowsAt2093 : MixedData.sourceRows (2093 : Fin 2425) =
    MixedData.row2093 := by decide +kernel

theorem sourceRowsAt2094 : MixedData.sourceRows (2094 : Fin 2425) =
    MixedData.row2094 := by decide +kernel

theorem sourceRowsAt2095 : MixedData.sourceRows (2095 : Fin 2425) =
    MixedData.row2095 := by decide +kernel

theorem chunkSound130 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 130) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 2080 ∨ k.val = 2081 ∨ k.val = 2082 ∨ k.val = 2083 ∨ k.val = 2084 ∨ k.val = 2085 ∨ k.val = 2086 ∨ k.val = 2087 ∨ k.val = 2088 ∨ k.val = 2089 ∨ k.val = 2090 ∨ k.val = 2091 ∨ k.val = 2092 ∨ k.val = 2093 ∨ k.val = 2094 ∨ k.val = 2095 := by omega
  rcases heq with h2080 | h2081 | h2082 | h2083 | h2084 | h2085 | h2086 | h2087 | h2088 | h2089 | h2090 | h2091 | h2092 | h2093 | h2094 | h2095
  · have he : k = (2080 : Fin 2425) := Fin.ext h2080
    subst k
    rw [sourceRowsAt2080]
    exact rowSound2080 B hB hF
  · have he : k = (2081 : Fin 2425) := Fin.ext h2081
    subst k
    rw [sourceRowsAt2081]
    exact rowSound2081 B hB hF
  · have he : k = (2082 : Fin 2425) := Fin.ext h2082
    subst k
    rw [sourceRowsAt2082]
    exact rowSound2082 B hB hF
  · have he : k = (2083 : Fin 2425) := Fin.ext h2083
    subst k
    rw [sourceRowsAt2083]
    exact rowSound2083 B hB hF
  · have he : k = (2084 : Fin 2425) := Fin.ext h2084
    subst k
    rw [sourceRowsAt2084]
    exact rowSound2084 B hB hF
  · have he : k = (2085 : Fin 2425) := Fin.ext h2085
    subst k
    rw [sourceRowsAt2085]
    exact rowSound2085 B hB hF
  · have he : k = (2086 : Fin 2425) := Fin.ext h2086
    subst k
    rw [sourceRowsAt2086]
    exact rowSound2086 B hB hF
  · have he : k = (2087 : Fin 2425) := Fin.ext h2087
    subst k
    rw [sourceRowsAt2087]
    exact rowSound2087 B hB hF
  · have he : k = (2088 : Fin 2425) := Fin.ext h2088
    subst k
    rw [sourceRowsAt2088]
    exact rowSound2088 B hB hF
  · have he : k = (2089 : Fin 2425) := Fin.ext h2089
    subst k
    rw [sourceRowsAt2089]
    exact rowSound2089 B hB hF
  · have he : k = (2090 : Fin 2425) := Fin.ext h2090
    subst k
    rw [sourceRowsAt2090]
    exact rowSound2090 B hB hF
  · have he : k = (2091 : Fin 2425) := Fin.ext h2091
    subst k
    rw [sourceRowsAt2091]
    exact rowSound2091 B hB hF
  · have he : k = (2092 : Fin 2425) := Fin.ext h2092
    subst k
    rw [sourceRowsAt2092]
    exact rowSound2092 B hB hF
  · have he : k = (2093 : Fin 2425) := Fin.ext h2093
    subst k
    rw [sourceRowsAt2093]
    exact rowSound2093 B hB hF
  · have he : k = (2094 : Fin 2425) := Fin.ext h2094
    subst k
    rw [sourceRowsAt2094]
    exact rowSound2094 B hB hF
  · have he : k = (2095 : Fin 2425) := Fin.ext h2095
    subst k
    rw [sourceRowsAt2095]
    exact rowSound2095 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
