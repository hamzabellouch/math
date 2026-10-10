import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic104
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources61

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1664 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1664 (mixedVector B) = 0 := by
  have h1320 : mixedVector B (Sum.inr 1320) = Sparse.eval nodeValue1320 (mixedVector B) := by
    change mixedMoment B node1320 node1320Labels = _
    exact sound1320 B hB hF
  have h2815 : mixedVector B (Sum.inr 2815) = Sparse.eval nodeValue2815 (mixedVector B) := by
    change mixedMoment B node2815 node2815Labels = _
    exact sound2815 B hB hF
  have h2847 : mixedVector B (Sum.inr 2847) = Sparse.eval nodeValue2847 (mixedVector B) := by
    change mixedMoment B node2847 node2847Labels = _
    exact sound2847 B hB hF
  have h2865 : mixedVector B (Sum.inr 2865) = Sparse.eval nodeValue2865 (mixedVector B) := by
    change mixedMoment B node2865 node2865Labels = _
    exact sound2865 B hB hF
  have h2884 : mixedVector B (Sum.inr 2884) = Sparse.eval nodeValue2884 (mixedVector B) := by
    change mixedMoment B node2884 node2884Labels = _
    exact sound2884 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1959, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1320, h2815, h2847, h2865, h2884, h4091, reducedSource1664] using sourceEq1959 B hB

theorem rowSound1664 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1664 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1664, numericCheck1664, reducedZero1664 B hB hF, mul_zero]

theorem reducedZero1665 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1665 (mixedVector B) = 0 := by
  have h1334 : mixedVector B (Sum.inr 1334) = Sparse.eval nodeValue1334 (mixedVector B) := by
    change mixedMoment B node1334 node1334Labels = _
    exact sound1334 B hB hF
  have h2797 : mixedVector B (Sum.inr 2797) = Sparse.eval nodeValue2797 (mixedVector B) := by
    change mixedMoment B node2797 node2797Labels = _
    exact sound2797 B hB hF
  have h2802 : mixedVector B (Sum.inr 2802) = Sparse.eval nodeValue2802 (mixedVector B) := by
    change mixedMoment B node2802 node2802Labels = _
    exact sound2802 B hB hF
  have h2815 : mixedVector B (Sum.inr 2815) = Sparse.eval nodeValue2815 (mixedVector B) := by
    change mixedMoment B node2815 node2815Labels = _
    exact sound2815 B hB hF
  have h2865 : mixedVector B (Sum.inr 2865) = Sparse.eval nodeValue2865 (mixedVector B) := by
    change mixedMoment B node2865 node2865Labels = _
    exact sound2865 B hB hF
  have h2931 : mixedVector B (Sum.inr 2931) = Sparse.eval nodeValue2931 (mixedVector B) := by
    change mixedMoment B node2931 node2931Labels = _
    exact sound2931 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1960, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1334, h2797, h2802, h2815, h2865, h2931, h4091, reducedSource1665] using sourceEq1960 B hB

theorem rowSound1665 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1665 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1665, numericCheck1665, reducedZero1665 B hB hF, mul_zero]

theorem reducedZero1666 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1666 (mixedVector B) = 0 := by
  have h2018 : mixedVector B (Sum.inr 2018) = Sparse.eval nodeValue2018 (mixedVector B) := by
    change mixedMoment B node2018 node2018Labels = _
    exact sound2018 B hB hF
  have h2074 : mixedVector B (Sum.inr 2074) = Sparse.eval nodeValue2074 (mixedVector B) := by
    change mixedMoment B node2074 node2074Labels = _
    exact sound2074 B hB hF
  have h2081 : mixedVector B (Sum.inr 2081) = Sparse.eval nodeValue2081 (mixedVector B) := by
    change mixedMoment B node2081 node2081Labels = _
    exact sound2081 B hB hF
  have h2099 : mixedVector B (Sum.inr 2099) = Sparse.eval nodeValue2099 (mixedVector B) := by
    change mixedMoment B node2099 node2099Labels = _
    exact sound2099 B hB hF
  have h2203 : mixedVector B (Sum.inr 2203) = Sparse.eval nodeValue2203 (mixedVector B) := by
    change mixedMoment B node2203 node2203Labels = _
    exact sound2203 B hB hF
  have h3530 : mixedVector B (Sum.inr 3530) = Sparse.eval nodeValue3530 (mixedVector B) := by
    change mixedMoment B node3530 node3530Labels = _
    exact sound3530 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1961, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2018, h2074, h2081, h2099, h2203, h3530, h4081, reducedSource1666] using sourceEq1961 B hB

theorem rowSound1666 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1666 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1666, numericCheck1666, reducedZero1666 B hB hF, mul_zero]

theorem reducedZero1667 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1667 (mixedVector B) = 0 := by
  have h2015 : mixedVector B (Sum.inr 2015) = Sparse.eval nodeValue2015 (mixedVector B) := by
    change mixedMoment B node2015 node2015Labels = _
    exact sound2015 B hB hF
  have h2018 : mixedVector B (Sum.inr 2018) = Sparse.eval nodeValue2018 (mixedVector B) := by
    change mixedMoment B node2018 node2018Labels = _
    exact sound2018 B hB hF
  have h2027 : mixedVector B (Sum.inr 2027) = Sparse.eval nodeValue2027 (mixedVector B) := by
    change mixedMoment B node2027 node2027Labels = _
    exact sound2027 B hB hF
  have h2047 : mixedVector B (Sum.inr 2047) = Sparse.eval nodeValue2047 (mixedVector B) := by
    change mixedMoment B node2047 node2047Labels = _
    exact sound2047 B hB hF
  have h2261 : mixedVector B (Sum.inr 2261) = Sparse.eval nodeValue2261 (mixedVector B) := by
    change mixedMoment B node2261 node2261Labels = _
    exact sound2261 B hB hF
  have h3530 : mixedVector B (Sum.inr 3530) = Sparse.eval nodeValue3530 (mixedVector B) := by
    change mixedMoment B node3530 node3530Labels = _
    exact sound3530 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1962, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2015, h2018, h2027, h2047, h2261, h3530, h4081, reducedSource1667] using sourceEq1962 B hB

theorem rowSound1667 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1667 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1667, numericCheck1667, reducedZero1667 B hB hF, mul_zero]

theorem reducedZero1668 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1668 (mixedVector B) = 0 := by
  have h4327 : mixedVector B (Sum.inr 4327) = Sparse.eval nodeValue4327 (mixedVector B) := by
    change mixedMoment B node4327 node4327Labels = _
    exact sound4327 B hB hF
  have h4330 : mixedVector B (Sum.inr 4330) = Sparse.eval nodeValue4330 (mixedVector B) := by
    change mixedMoment B node4330 node4330Labels = _
    exact sound4330 B hB hF
  have h4335 : mixedVector B (Sum.inr 4335) = Sparse.eval nodeValue4335 (mixedVector B) := by
    change mixedMoment B node4335 node4335Labels = _
    exact sound4335 B hB hF
  have h4347 : mixedVector B (Sum.inr 4347) = Sparse.eval nodeValue4347 (mixedVector B) := by
    change mixedMoment B node4347 node4347Labels = _
    exact sound4347 B hB hF
  have h4440 : mixedVector B (Sum.inr 4440) = Sparse.eval nodeValue4440 (mixedVector B) := by
    change mixedMoment B node4440 node4440Labels = _
    exact sound4440 B hB hF
  have h4528 : mixedVector B (Sum.inr 4528) = Sparse.eval nodeValue4528 (mixedVector B) := by
    change mixedMoment B node4528 node4528Labels = _
    exact sound4528 B hB hF
  have h4535 : mixedVector B (Sum.inr 4535) = Sparse.eval nodeValue4535 (mixedVector B) := by
    change mixedMoment B node4535 node4535Labels = _
    exact sound4535 B hB hF
  have h4551 : mixedVector B (Sum.inr 4551) = Sparse.eval nodeValue4551 (mixedVector B) := by
    change mixedMoment B node4551 node4551Labels = _
    exact sound4551 B hB hF
  have h4591 : mixedVector B (Sum.inr 4591) = Sparse.eval nodeValue4591 (mixedVector B) := by
    change mixedMoment B node4591 node4591Labels = _
    exact sound4591 B hB hF
  have h4930 : mixedVector B (Sum.inr 4930) = Sparse.eval nodeValue4930 (mixedVector B) := by
    change mixedMoment B node4930 node4930Labels = _
    exact sound4930 B hB hF
  have h4935 : mixedVector B (Sum.inr 4935) = Sparse.eval nodeValue4935 (mixedVector B) := by
    change mixedMoment B node4935 node4935Labels = _
    exact sound4935 B hB hF
  have h4944 : mixedVector B (Sum.inr 4944) = Sparse.eval nodeValue4944 (mixedVector B) := by
    change mixedMoment B node4944 node4944Labels = _
    exact sound4944 B hB hF
  have h4948 : mixedVector B (Sum.inr 4948) = Sparse.eval nodeValue4948 (mixedVector B) := by
    change mixedMoment B node4948 node4948Labels = _
    exact sound4948 B hB hF
  have h5034 : mixedVector B (Sum.inr 5034) = Sparse.eval nodeValue5034 (mixedVector B) := by
    change mixedMoment B node5034 node5034Labels = _
    exact sound5034 B hB hF
  have h5037 : mixedVector B (Sum.inr 5037) = Sparse.eval nodeValue5037 (mixedVector B) := by
    change mixedMoment B node5037 node5037Labels = _
    exact sound5037 B hB hF
  have h5065 : mixedVector B (Sum.inr 5065) = Sparse.eval nodeValue5065 (mixedVector B) := by
    change mixedMoment B node5065 node5065Labels = _
    exact sound5065 B hB hF
  have h5073 : mixedVector B (Sum.inr 5073) = Sparse.eval nodeValue5073 (mixedVector B) := by
    change mixedMoment B node5073 node5073Labels = _
    exact sound5073 B hB hF
  have h5078 : mixedVector B (Sum.inr 5078) = Sparse.eval nodeValue5078 (mixedVector B) := by
    change mixedMoment B node5078 node5078Labels = _
    exact sound5078 B hB hF
  have h5081 : mixedVector B (Sum.inr 5081) = Sparse.eval nodeValue5081 (mixedVector B) := by
    change mixedMoment B node5081 node5081Labels = _
    exact sound5081 B hB hF
  have h5104 : mixedVector B (Sum.inr 5104) = Sparse.eval nodeValue5104 (mixedVector B) := by
    change mixedMoment B node5104 node5104Labels = _
    exact sound5104 B hB hF
  have h5128 : mixedVector B (Sum.inr 5128) = Sparse.eval nodeValue5128 (mixedVector B) := by
    change mixedMoment B node5128 node5128Labels = _
    exact sound5128 B hB hF
  have h5139 : mixedVector B (Sum.inr 5139) = Sparse.eval nodeValue5139 (mixedVector B) := by
    change mixedMoment B node5139 node5139Labels = _
    exact sound5139 B hB hF
  have h5149 : mixedVector B (Sum.inr 5149) = Sparse.eval nodeValue5149 (mixedVector B) := by
    change mixedMoment B node5149 node5149Labels = _
    exact sound5149 B hB hF
  have h5152 : mixedVector B (Sum.inr 5152) = Sparse.eval nodeValue5152 (mixedVector B) := by
    change mixedMoment B node5152 node5152Labels = _
    exact sound5152 B hB hF
  have h5170 : mixedVector B (Sum.inr 5170) = Sparse.eval nodeValue5170 (mixedVector B) := by
    change mixedMoment B node5170 node5170Labels = _
    exact sound5170 B hB hF
  have h5252 : mixedVector B (Sum.inr 5252) = Sparse.eval nodeValue5252 (mixedVector B) := by
    change mixedMoment B node5252 node5252Labels = _
    exact sound5252 B hB hF
  have h5259 : mixedVector B (Sum.inr 5259) = Sparse.eval nodeValue5259 (mixedVector B) := by
    change mixedMoment B node5259 node5259Labels = _
    exact sound5259 B hB hF
  have h5284 : mixedVector B (Sum.inr 5284) = Sparse.eval nodeValue5284 (mixedVector B) := by
    change mixedMoment B node5284 node5284Labels = _
    exact sound5284 B hB hF
  have h5410 : mixedVector B (Sum.inr 5410) = Sparse.eval nodeValue5410 (mixedVector B) := by
    change mixedMoment B node5410 node5410Labels = _
    exact sound5410 B hB hF
  simpa only [sourceForm1965, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4327, h4330, h4335, h4347, h4440, h4528, h4535, h4551, h4591, h4930, h4935, h4944, h4948, h5034, h5037, h5065, h5073, h5078, h5081, h5104, h5128, h5139, h5149, h5152, h5170, h5252, h5259, h5284, h5410, reducedSource1668] using sourceEq1965 B hB

theorem rowSound1668 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1668 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1668, numericCheck1668, reducedZero1668 B hB hF, mul_zero]

theorem reducedZero1669 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1669 (mixedVector B) = 0 := by
  have h905 : mixedVector B (Sum.inr 905) = Sparse.eval nodeValue905 (mixedVector B) := by
    change mixedMoment B node905 node905Labels = _
    exact sound905 B hB hF
  have h908 : mixedVector B (Sum.inr 908) = Sparse.eval nodeValue908 (mixedVector B) := by
    change mixedMoment B node908 node908Labels = _
    exact sound908 B hB hF
  have h913 : mixedVector B (Sum.inr 913) = Sparse.eval nodeValue913 (mixedVector B) := by
    change mixedMoment B node913 node913Labels = _
    exact sound913 B hB hF
  have h925 : mixedVector B (Sum.inr 925) = Sparse.eval nodeValue925 (mixedVector B) := by
    change mixedMoment B node925 node925Labels = _
    exact sound925 B hB hF
  have h1022 : mixedVector B (Sum.inr 1022) = Sparse.eval nodeValue1022 (mixedVector B) := by
    change mixedMoment B node1022 node1022Labels = _
    exact sound1022 B hB hF
  have h1148 : mixedVector B (Sum.inr 1148) = Sparse.eval nodeValue1148 (mixedVector B) := by
    change mixedMoment B node1148 node1148Labels = _
    exact sound1148 B hB hF
  have h1154 : mixedVector B (Sum.inr 1154) = Sparse.eval nodeValue1154 (mixedVector B) := by
    change mixedMoment B node1154 node1154Labels = _
    exact sound1154 B hB hF
  have h1163 : mixedVector B (Sum.inr 1163) = Sparse.eval nodeValue1163 (mixedVector B) := by
    change mixedMoment B node1163 node1163Labels = _
    exact sound1163 B hB hF
  have h1215 : mixedVector B (Sum.inr 1215) = Sparse.eval nodeValue1215 (mixedVector B) := by
    change mixedMoment B node1215 node1215Labels = _
    exact sound1215 B hB hF
  have h2320 : mixedVector B (Sum.inr 2320) = Sparse.eval nodeValue2320 (mixedVector B) := by
    change mixedMoment B node2320 node2320Labels = _
    exact sound2320 B hB hF
  have h2326 : mixedVector B (Sum.inr 2326) = Sparse.eval nodeValue2326 (mixedVector B) := by
    change mixedMoment B node2326 node2326Labels = _
    exact sound2326 B hB hF
  have h2335 : mixedVector B (Sum.inr 2335) = Sparse.eval nodeValue2335 (mixedVector B) := by
    change mixedMoment B node2335 node2335Labels = _
    exact sound2335 B hB hF
  have h2422 : mixedVector B (Sum.inr 2422) = Sparse.eval nodeValue2422 (mixedVector B) := by
    change mixedMoment B node2422 node2422Labels = _
    exact sound2422 B hB hF
  have h2426 : mixedVector B (Sum.inr 2426) = Sparse.eval nodeValue2426 (mixedVector B) := by
    change mixedMoment B node2426 node2426Labels = _
    exact sound2426 B hB hF
  have h2470 : mixedVector B (Sum.inr 2470) = Sparse.eval nodeValue2470 (mixedVector B) := by
    change mixedMoment B node2470 node2470Labels = _
    exact sound2470 B hB hF
  have h2526 : mixedVector B (Sum.inr 2526) = Sparse.eval nodeValue2526 (mixedVector B) := by
    change mixedMoment B node2526 node2526Labels = _
    exact sound2526 B hB hF
  have h2531 : mixedVector B (Sum.inr 2531) = Sparse.eval nodeValue2531 (mixedVector B) := by
    change mixedMoment B node2531 node2531Labels = _
    exact sound2531 B hB hF
  have h2543 : mixedVector B (Sum.inr 2543) = Sparse.eval nodeValue2543 (mixedVector B) := by
    change mixedMoment B node2543 node2543Labels = _
    exact sound2543 B hB hF
  have h2558 : mixedVector B (Sum.inr 2558) = Sparse.eval nodeValue2558 (mixedVector B) := by
    change mixedMoment B node2558 node2558Labels = _
    exact sound2558 B hB hF
  have h2570 : mixedVector B (Sum.inr 2570) = Sparse.eval nodeValue2570 (mixedVector B) := by
    change mixedMoment B node2570 node2570Labels = _
    exact sound2570 B hB hF
  have h2572 : mixedVector B (Sum.inr 2572) = Sparse.eval nodeValue2572 (mixedVector B) := by
    change mixedMoment B node2572 node2572Labels = _
    exact sound2572 B hB hF
  have h2576 : mixedVector B (Sum.inr 2576) = Sparse.eval nodeValue2576 (mixedVector B) := by
    change mixedMoment B node2576 node2576Labels = _
    exact sound2576 B hB hF
  have h2596 : mixedVector B (Sum.inr 2596) = Sparse.eval nodeValue2596 (mixedVector B) := by
    change mixedMoment B node2596 node2596Labels = _
    exact sound2596 B hB hF
  have h2712 : mixedVector B (Sum.inr 2712) = Sparse.eval nodeValue2712 (mixedVector B) := by
    change mixedMoment B node2712 node2712Labels = _
    exact sound2712 B hB hF
  have h2753 : mixedVector B (Sum.inr 2753) = Sparse.eval nodeValue2753 (mixedVector B) := by
    change mixedMoment B node2753 node2753Labels = _
    exact sound2753 B hB hF
  have h2987 : mixedVector B (Sum.inr 2987) = Sparse.eval nodeValue2987 (mixedVector B) := by
    change mixedMoment B node2987 node2987Labels = _
    exact sound2987 B hB hF
  have h2991 : mixedVector B (Sum.inr 2991) = Sparse.eval nodeValue2991 (mixedVector B) := by
    change mixedMoment B node2991 node2991Labels = _
    exact sound2991 B hB hF
  have h3000 : mixedVector B (Sum.inr 3000) = Sparse.eval nodeValue3000 (mixedVector B) := by
    change mixedMoment B node3000 node3000Labels = _
    exact sound3000 B hB hF
  have h3088 : mixedVector B (Sum.inr 3088) = Sparse.eval nodeValue3088 (mixedVector B) := by
    change mixedMoment B node3088 node3088Labels = _
    exact sound3088 B hB hF
  have h3996 : mixedVector B (Sum.inr 3996) = Sparse.eval nodeValue3996 (mixedVector B) := by
    change mixedMoment B node3996 node3996Labels = _
    exact sound3996 B hB hF
  simpa only [sourceForm1966, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h905, h908, h913, h925, h1022, h1148, h1154, h1163, h1215, h2320, h2326, h2335, h2422, h2426, h2470, h2526, h2531, h2543, h2558, h2570, h2572, h2576, h2596, h2712, h2753, h2987, h2991, h3000, h3088, h3996, reducedSource1669] using sourceEq1966 B hB

theorem rowSound1669 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1669 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1669, numericCheck1669, reducedZero1669 B hB hF, mul_zero]

theorem reducedZero1670 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1670 (mixedVector B) = 0 := by
  have h1670 : mixedVector B (Sum.inr 1670) = Sparse.eval nodeValue1670 (mixedVector B) := by
    change mixedMoment B node1670 node1670Labels = _
    exact sound1670 B hB hF
  have h1672 : mixedVector B (Sum.inr 1672) = Sparse.eval nodeValue1672 (mixedVector B) := by
    change mixedMoment B node1672 node1672Labels = _
    exact sound1672 B hB hF
  have h1676 : mixedVector B (Sum.inr 1676) = Sparse.eval nodeValue1676 (mixedVector B) := by
    change mixedMoment B node1676 node1676Labels = _
    exact sound1676 B hB hF
  have h1689 : mixedVector B (Sum.inr 1689) = Sparse.eval nodeValue1689 (mixedVector B) := by
    change mixedMoment B node1689 node1689Labels = _
    exact sound1689 B hB hF
  have h1723 : mixedVector B (Sum.inr 1723) = Sparse.eval nodeValue1723 (mixedVector B) := by
    change mixedMoment B node1723 node1723Labels = _
    exact sound1723 B hB hF
  have h3260 : mixedVector B (Sum.inr 3260) = Sparse.eval nodeValue3260 (mixedVector B) := by
    change mixedMoment B node3260 node3260Labels = _
    exact sound3260 B hB hF
  have h3272 : mixedVector B (Sum.inr 3272) = Sparse.eval nodeValue3272 (mixedVector B) := by
    change mixedMoment B node3272 node3272Labels = _
    exact sound3272 B hB hF
  have h3273 : mixedVector B (Sum.inr 3273) = Sparse.eval nodeValue3273 (mixedVector B) := by
    change mixedMoment B node3273 node3273Labels = _
    exact sound3273 B hB hF
  have h3291 : mixedVector B (Sum.inr 3291) = Sparse.eval nodeValue3291 (mixedVector B) := by
    change mixedMoment B node3291 node3291Labels = _
    exact sound3291 B hB hF
  have h3408 : mixedVector B (Sum.inr 3408) = Sparse.eval nodeValue3408 (mixedVector B) := by
    change mixedMoment B node3408 node3408Labels = _
    exact sound3408 B hB hF
  have h3413 : mixedVector B (Sum.inr 3413) = Sparse.eval nodeValue3413 (mixedVector B) := by
    change mixedMoment B node3413 node3413Labels = _
    exact sound3413 B hB hF
  have h3419 : mixedVector B (Sum.inr 3419) = Sparse.eval nodeValue3419 (mixedVector B) := by
    change mixedMoment B node3419 node3419Labels = _
    exact sound3419 B hB hF
  have h3420 : mixedVector B (Sum.inr 3420) = Sparse.eval nodeValue3420 (mixedVector B) := by
    change mixedMoment B node3420 node3420Labels = _
    exact sound3420 B hB hF
  have h3451 : mixedVector B (Sum.inr 3451) = Sparse.eval nodeValue3451 (mixedVector B) := by
    change mixedMoment B node3451 node3451Labels = _
    exact sound3451 B hB hF
  have h3455 : mixedVector B (Sum.inr 3455) = Sparse.eval nodeValue3455 (mixedVector B) := by
    change mixedMoment B node3455 node3455Labels = _
    exact sound3455 B hB hF
  have h3466 : mixedVector B (Sum.inr 3466) = Sparse.eval nodeValue3466 (mixedVector B) := by
    change mixedMoment B node3466 node3466Labels = _
    exact sound3466 B hB hF
  have h3467 : mixedVector B (Sum.inr 3467) = Sparse.eval nodeValue3467 (mixedVector B) := by
    change mixedMoment B node3467 node3467Labels = _
    exact sound3467 B hB hF
  have h3481 : mixedVector B (Sum.inr 3481) = Sparse.eval nodeValue3481 (mixedVector B) := by
    change mixedMoment B node3481 node3481Labels = _
    exact sound3481 B hB hF
  have h3482 : mixedVector B (Sum.inr 3482) = Sparse.eval nodeValue3482 (mixedVector B) := by
    change mixedMoment B node3482 node3482Labels = _
    exact sound3482 B hB hF
  have h3483 : mixedVector B (Sum.inr 3483) = Sparse.eval nodeValue3483 (mixedVector B) := by
    change mixedMoment B node3483 node3483Labels = _
    exact sound3483 B hB hF
  have h3519 : mixedVector B (Sum.inr 3519) = Sparse.eval nodeValue3519 (mixedVector B) := by
    change mixedMoment B node3519 node3519Labels = _
    exact sound3519 B hB hF
  have h3523 : mixedVector B (Sum.inr 3523) = Sparse.eval nodeValue3523 (mixedVector B) := by
    change mixedMoment B node3523 node3523Labels = _
    exact sound3523 B hB hF
  have h3543 : mixedVector B (Sum.inr 3543) = Sparse.eval nodeValue3543 (mixedVector B) := by
    change mixedMoment B node3543 node3543Labels = _
    exact sound3543 B hB hF
  have h3544 : mixedVector B (Sum.inr 3544) = Sparse.eval nodeValue3544 (mixedVector B) := by
    change mixedMoment B node3544 node3544Labels = _
    exact sound3544 B hB hF
  have h3605 : mixedVector B (Sum.inr 3605) = Sparse.eval nodeValue3605 (mixedVector B) := by
    change mixedMoment B node3605 node3605Labels = _
    exact sound3605 B hB hF
  have h3606 : mixedVector B (Sum.inr 3606) = Sparse.eval nodeValue3606 (mixedVector B) := by
    change mixedMoment B node3606 node3606Labels = _
    exact sound3606 B hB hF
  have h3612 : mixedVector B (Sum.inr 3612) = Sparse.eval nodeValue3612 (mixedVector B) := by
    change mixedMoment B node3612 node3612Labels = _
    exact sound3612 B hB hF
  have h3625 : mixedVector B (Sum.inr 3625) = Sparse.eval nodeValue3625 (mixedVector B) := by
    change mixedMoment B node3625 node3625Labels = _
    exact sound3625 B hB hF
  have h3816 : mixedVector B (Sum.inr 3816) = Sparse.eval nodeValue3816 (mixedVector B) := by
    change mixedMoment B node3816 node3816Labels = _
    exact sound3816 B hB hF
  simpa only [sourceForm1967, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1670, h1672, h1676, h1689, h1723, h3260, h3272, h3273, h3291, h3408, h3413, h3419, h3420, h3451, h3455, h3466, h3467, h3481, h3482, h3483, h3519, h3523, h3543, h3544, h3605, h3606, h3612, h3625, h3816, reducedSource1670] using sourceEq1967 B hB

theorem rowSound1670 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1670 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1670, numericCheck1670, reducedZero1670 B hB hF, mul_zero]

theorem reducedZero1671 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1671 (mixedVector B) = 0 := by
  have h1136 : mixedVector B (Sum.inr 1136) = Sparse.eval nodeValue1136 (mixedVector B) := by
    change mixedMoment B node1136 node1136Labels = _
    exact sound1136 B hB hF
  have h2339 : mixedVector B (Sum.inr 2339) = Sparse.eval nodeValue2339 (mixedVector B) := by
    change mixedMoment B node2339 node2339Labels = _
    exact sound2339 B hB hF
  have h2429 : mixedVector B (Sum.inr 2429) = Sparse.eval nodeValue2429 (mixedVector B) := by
    change mixedMoment B node2429 node2429Labels = _
    exact sound2429 B hB hF
  have h2485 : mixedVector B (Sum.inr 2485) = Sparse.eval nodeValue2485 (mixedVector B) := by
    change mixedMoment B node2485 node2485Labels = _
    exact sound2485 B hB hF
  have h2514 : mixedVector B (Sum.inr 2514) = Sparse.eval nodeValue2514 (mixedVector B) := by
    change mixedMoment B node2514 node2514Labels = _
    exact sound2514 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1968, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1136, h2339, h2429, h2485, h2514, h4091, reducedSource1671] using sourceEq1968 B hB

theorem rowSound1671 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1671 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1671, numericCheck1671, reducedZero1671 B hB hF, mul_zero]

theorem reducedZero1672 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1672 (mixedVector B) = 0 := by
  have h4199 : mixedVector B (Sum.inr 4199) = Sparse.eval nodeValue4199 (mixedVector B) := by
    change mixedMoment B node4199 node4199Labels = _
    exact sound4199 B hB hF
  have h4202 : mixedVector B (Sum.inr 4202) = Sparse.eval nodeValue4202 (mixedVector B) := by
    change mixedMoment B node4202 node4202Labels = _
    exact sound4202 B hB hF
  have h4205 : mixedVector B (Sum.inr 4205) = Sparse.eval nodeValue4205 (mixedVector B) := by
    change mixedMoment B node4205 node4205Labels = _
    exact sound4205 B hB hF
  have h4219 : mixedVector B (Sum.inr 4219) = Sparse.eval nodeValue4219 (mixedVector B) := by
    change mixedMoment B node4219 node4219Labels = _
    exact sound4219 B hB hF
  have h4253 : mixedVector B (Sum.inr 4253) = Sparse.eval nodeValue4253 (mixedVector B) := by
    change mixedMoment B node4253 node4253Labels = _
    exact sound4253 B hB hF
  have h4521 : mixedVector B (Sum.inr 4521) = Sparse.eval nodeValue4521 (mixedVector B) := by
    change mixedMoment B node4521 node4521Labels = _
    exact sound4521 B hB hF
  have h4525 : mixedVector B (Sum.inr 4525) = Sparse.eval nodeValue4525 (mixedVector B) := by
    change mixedMoment B node4525 node4525Labels = _
    exact sound4525 B hB hF
  have h4543 : mixedVector B (Sum.inr 4543) = Sparse.eval nodeValue4543 (mixedVector B) := by
    change mixedMoment B node4543 node4543Labels = _
    exact sound4543 B hB hF
  have h4605 : mixedVector B (Sum.inr 4605) = Sparse.eval nodeValue4605 (mixedVector B) := by
    change mixedMoment B node4605 node4605Labels = _
    exact sound4605 B hB hF
  have h4633 : mixedVector B (Sum.inr 4633) = Sparse.eval nodeValue4633 (mixedVector B) := by
    change mixedMoment B node4633 node4633Labels = _
    exact sound4633 B hB hF
  have h4638 : mixedVector B (Sum.inr 4638) = Sparse.eval nodeValue4638 (mixedVector B) := by
    change mixedMoment B node4638 node4638Labels = _
    exact sound4638 B hB hF
  have h4650 : mixedVector B (Sum.inr 4650) = Sparse.eval nodeValue4650 (mixedVector B) := by
    change mixedMoment B node4650 node4650Labels = _
    exact sound4650 B hB hF
  have h4707 : mixedVector B (Sum.inr 4707) = Sparse.eval nodeValue4707 (mixedVector B) := by
    change mixedMoment B node4707 node4707Labels = _
    exact sound4707 B hB hF
  have h4713 : mixedVector B (Sum.inr 4713) = Sparse.eval nodeValue4713 (mixedVector B) := by
    change mixedMoment B node4713 node4713Labels = _
    exact sound4713 B hB hF
  have h4729 : mixedVector B (Sum.inr 4729) = Sparse.eval nodeValue4729 (mixedVector B) := by
    change mixedMoment B node4729 node4729Labels = _
    exact sound4729 B hB hF
  have h4764 : mixedVector B (Sum.inr 4764) = Sparse.eval nodeValue4764 (mixedVector B) := by
    change mixedMoment B node4764 node4764Labels = _
    exact sound4764 B hB hF
  have h4770 : mixedVector B (Sum.inr 4770) = Sparse.eval nodeValue4770 (mixedVector B) := by
    change mixedMoment B node4770 node4770Labels = _
    exact sound4770 B hB hF
  have h4805 : mixedVector B (Sum.inr 4805) = Sparse.eval nodeValue4805 (mixedVector B) := by
    change mixedMoment B node4805 node4805Labels = _
    exact sound4805 B hB hF
  have h4807 : mixedVector B (Sum.inr 4807) = Sparse.eval nodeValue4807 (mixedVector B) := by
    change mixedMoment B node4807 node4807Labels = _
    exact sound4807 B hB hF
  have h4810 : mixedVector B (Sum.inr 4810) = Sparse.eval nodeValue4810 (mixedVector B) := by
    change mixedMoment B node4810 node4810Labels = _
    exact sound4810 B hB hF
  have h4839 : mixedVector B (Sum.inr 4839) = Sparse.eval nodeValue4839 (mixedVector B) := by
    change mixedMoment B node4839 node4839Labels = _
    exact sound4839 B hB hF
  have h4843 : mixedVector B (Sum.inr 4843) = Sparse.eval nodeValue4843 (mixedVector B) := by
    change mixedMoment B node4843 node4843Labels = _
    exact sound4843 B hB hF
  have h4889 : mixedVector B (Sum.inr 4889) = Sparse.eval nodeValue4889 (mixedVector B) := by
    change mixedMoment B node4889 node4889Labels = _
    exact sound4889 B hB hF
  have h4890 : mixedVector B (Sum.inr 4890) = Sparse.eval nodeValue4890 (mixedVector B) := by
    change mixedMoment B node4890 node4890Labels = _
    exact sound4890 B hB hF
  have h5149 : mixedVector B (Sum.inr 5149) = Sparse.eval nodeValue5149 (mixedVector B) := by
    change mixedMoment B node5149 node5149Labels = _
    exact sound5149 B hB hF
  have h5152 : mixedVector B (Sum.inr 5152) = Sparse.eval nodeValue5152 (mixedVector B) := by
    change mixedMoment B node5152 node5152Labels = _
    exact sound5152 B hB hF
  have h5172 : mixedVector B (Sum.inr 5172) = Sparse.eval nodeValue5172 (mixedVector B) := by
    change mixedMoment B node5172 node5172Labels = _
    exact sound5172 B hB hF
  have h5294 : mixedVector B (Sum.inr 5294) = Sparse.eval nodeValue5294 (mixedVector B) := by
    change mixedMoment B node5294 node5294Labels = _
    exact sound5294 B hB hF
  have h5435 : mixedVector B (Sum.inr 5435) = Sparse.eval nodeValue5435 (mixedVector B) := by
    change mixedMoment B node5435 node5435Labels = _
    exact sound5435 B hB hF
  simpa only [sourceForm1971, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4199, h4202, h4205, h4219, h4253, h4521, h4525, h4543, h4605, h4633, h4638, h4650, h4707, h4713, h4729, h4764, h4770, h4805, h4807, h4810, h4839, h4843, h4889, h4890, h5149, h5152, h5172, h5294, h5435, reducedSource1672] using sourceEq1971 B hB

theorem rowSound1672 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1672 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1672, numericCheck1672, reducedZero1672 B hB hF, mul_zero]

theorem reducedZero1673 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1673 (mixedVector B) = 0 := by
  have h4327 : mixedVector B (Sum.inr 4327) = Sparse.eval nodeValue4327 (mixedVector B) := by
    change mixedMoment B node4327 node4327Labels = _
    exact sound4327 B hB hF
  have h4331 : mixedVector B (Sum.inr 4331) = Sparse.eval nodeValue4331 (mixedVector B) := by
    change mixedMoment B node4331 node4331Labels = _
    exact sound4331 B hB hF
  have h4333 : mixedVector B (Sum.inr 4333) = Sparse.eval nodeValue4333 (mixedVector B) := by
    change mixedMoment B node4333 node4333Labels = _
    exact sound4333 B hB hF
  have h4335 : mixedVector B (Sum.inr 4335) = Sparse.eval nodeValue4335 (mixedVector B) := by
    change mixedMoment B node4335 node4335Labels = _
    exact sound4335 B hB hF
  have h4336 : mixedVector B (Sum.inr 4336) = Sparse.eval nodeValue4336 (mixedVector B) := by
    change mixedMoment B node4336 node4336Labels = _
    exact sound4336 B hB hF
  have h4352 : mixedVector B (Sum.inr 4352) = Sparse.eval nodeValue4352 (mixedVector B) := by
    change mixedMoment B node4352 node4352Labels = _
    exact sound4352 B hB hF
  have h4353 : mixedVector B (Sum.inr 4353) = Sparse.eval nodeValue4353 (mixedVector B) := by
    change mixedMoment B node4353 node4353Labels = _
    exact sound4353 B hB hF
  have h4442 : mixedVector B (Sum.inr 4442) = Sparse.eval nodeValue4442 (mixedVector B) := by
    change mixedMoment B node4442 node4442Labels = _
    exact sound4442 B hB hF
  have h4463 : mixedVector B (Sum.inr 4463) = Sparse.eval nodeValue4463 (mixedVector B) := by
    change mixedMoment B node4463 node4463Labels = _
    exact sound4463 B hB hF
  have h4664 : mixedVector B (Sum.inr 4664) = Sparse.eval nodeValue4664 (mixedVector B) := by
    change mixedMoment B node4664 node4664Labels = _
    exact sound4664 B hB hF
  have h4670 : mixedVector B (Sum.inr 4670) = Sparse.eval nodeValue4670 (mixedVector B) := by
    change mixedMoment B node4670 node4670Labels = _
    exact sound4670 B hB hF
  have h4686 : mixedVector B (Sum.inr 4686) = Sparse.eval nodeValue4686 (mixedVector B) := by
    change mixedMoment B node4686 node4686Labels = _
    exact sound4686 B hB hF
  have h4757 : mixedVector B (Sum.inr 4757) = Sparse.eval nodeValue4757 (mixedVector B) := by
    change mixedMoment B node4757 node4757Labels = _
    exact sound4757 B hB hF
  have h4764 : mixedVector B (Sum.inr 4764) = Sparse.eval nodeValue4764 (mixedVector B) := by
    change mixedMoment B node4764 node4764Labels = _
    exact sound4764 B hB hF
  have h4772 : mixedVector B (Sum.inr 4772) = Sparse.eval nodeValue4772 (mixedVector B) := by
    change mixedMoment B node4772 node4772Labels = _
    exact sound4772 B hB hF
  have h4777 : mixedVector B (Sum.inr 4777) = Sparse.eval nodeValue4777 (mixedVector B) := by
    change mixedMoment B node4777 node4777Labels = _
    exact sound4777 B hB hF
  have h4792 : mixedVector B (Sum.inr 4792) = Sparse.eval nodeValue4792 (mixedVector B) := by
    change mixedMoment B node4792 node4792Labels = _
    exact sound4792 B hB hF
  have h4802 : mixedVector B (Sum.inr 4802) = Sparse.eval nodeValue4802 (mixedVector B) := by
    change mixedMoment B node4802 node4802Labels = _
    exact sound4802 B hB hF
  have h4807 : mixedVector B (Sum.inr 4807) = Sparse.eval nodeValue4807 (mixedVector B) := by
    change mixedMoment B node4807 node4807Labels = _
    exact sound4807 B hB hF
  have h4811 : mixedVector B (Sum.inr 4811) = Sparse.eval nodeValue4811 (mixedVector B) := by
    change mixedMoment B node4811 node4811Labels = _
    exact sound4811 B hB hF
  have h4838 : mixedVector B (Sum.inr 4838) = Sparse.eval nodeValue4838 (mixedVector B) := by
    change mixedMoment B node4838 node4838Labels = _
    exact sound4838 B hB hF
  have h4871 : mixedVector B (Sum.inr 4871) = Sparse.eval nodeValue4871 (mixedVector B) := by
    change mixedMoment B node4871 node4871Labels = _
    exact sound4871 B hB hF
  have h4890 : mixedVector B (Sum.inr 4890) = Sparse.eval nodeValue4890 (mixedVector B) := by
    change mixedMoment B node4890 node4890Labels = _
    exact sound4890 B hB hF
  have h4895 : mixedVector B (Sum.inr 4895) = Sparse.eval nodeValue4895 (mixedVector B) := by
    change mixedMoment B node4895 node4895Labels = _
    exact sound4895 B hB hF
  have h5150 : mixedVector B (Sum.inr 5150) = Sparse.eval nodeValue5150 (mixedVector B) := by
    change mixedMoment B node5150 node5150Labels = _
    exact sound5150 B hB hF
  have h5151 : mixedVector B (Sum.inr 5151) = Sparse.eval nodeValue5151 (mixedVector B) := by
    change mixedMoment B node5151 node5151Labels = _
    exact sound5151 B hB hF
  have h5173 : mixedVector B (Sum.inr 5173) = Sparse.eval nodeValue5173 (mixedVector B) := by
    change mixedMoment B node5173 node5173Labels = _
    exact sound5173 B hB hF
  have h5270 : mixedVector B (Sum.inr 5270) = Sparse.eval nodeValue5270 (mixedVector B) := by
    change mixedMoment B node5270 node5270Labels = _
    exact sound5270 B hB hF
  have h5271 : mixedVector B (Sum.inr 5271) = Sparse.eval nodeValue5271 (mixedVector B) := by
    change mixedMoment B node5271 node5271Labels = _
    exact sound5271 B hB hF
  simpa only [sourceForm1973, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4327, h4331, h4333, h4335, h4336, h4352, h4353, h4442, h4463, h4664, h4670, h4686, h4757, h4764, h4772, h4777, h4792, h4802, h4807, h4811, h4838, h4871, h4890, h4895, h5150, h5151, h5173, h5270, h5271, reducedSource1673] using sourceEq1973 B hB

theorem rowSound1673 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1673 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1673, numericCheck1673, reducedZero1673 B hB hF, mul_zero]

theorem reducedZero1674 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1674 (mixedVector B) = 0 := by
  have h909 : mixedVector B (Sum.inr 909) = Sparse.eval nodeValue909 (mixedVector B) := by
    change mixedMoment B node909 node909Labels = _
    exact sound909 B hB hF
  have h911 : mixedVector B (Sum.inr 911) = Sparse.eval nodeValue911 (mixedVector B) := by
    change mixedMoment B node911 node911Labels = _
    exact sound911 B hB hF
  have h914 : mixedVector B (Sum.inr 914) = Sparse.eval nodeValue914 (mixedVector B) := by
    change mixedMoment B node914 node914Labels = _
    exact sound914 B hB hF
  have h931 : mixedVector B (Sum.inr 931) = Sparse.eval nodeValue931 (mixedVector B) := by
    change mixedMoment B node931 node931Labels = _
    exact sound931 B hB hF
  have h1024 : mixedVector B (Sum.inr 1024) = Sparse.eval nodeValue1024 (mixedVector B) := by
    change mixedMoment B node1024 node1024Labels = _
    exact sound1024 B hB hF
  have h1327 : mixedVector B (Sum.inr 1327) = Sparse.eval nodeValue1327 (mixedVector B) := by
    change mixedMoment B node1327 node1327Labels = _
    exact sound1327 B hB hF
  have h1333 : mixedVector B (Sum.inr 1333) = Sparse.eval nodeValue1333 (mixedVector B) := by
    change mixedMoment B node1333 node1333Labels = _
    exact sound1333 B hB hF
  have h1340 : mixedVector B (Sum.inr 1340) = Sparse.eval nodeValue1340 (mixedVector B) := by
    change mixedMoment B node1340 node1340Labels = _
    exact sound1340 B hB hF
  have h1413 : mixedVector B (Sum.inr 1413) = Sparse.eval nodeValue1413 (mixedVector B) := by
    change mixedMoment B node1413 node1413Labels = _
    exact sound1413 B hB hF
  have h2323 : mixedVector B (Sum.inr 2323) = Sparse.eval nodeValue2323 (mixedVector B) := by
    change mixedMoment B node2323 node2323Labels = _
    exact sound2323 B hB hF
  have h2327 : mixedVector B (Sum.inr 2327) = Sparse.eval nodeValue2327 (mixedVector B) := by
    change mixedMoment B node2327 node2327Labels = _
    exact sound2327 B hB hF
  have h2340 : mixedVector B (Sum.inr 2340) = Sparse.eval nodeValue2340 (mixedVector B) := by
    change mixedMoment B node2340 node2340Labels = _
    exact sound2340 B hB hF
  have h2423 : mixedVector B (Sum.inr 2423) = Sparse.eval nodeValue2423 (mixedVector B) := by
    change mixedMoment B node2423 node2423Labels = _
    exact sound2423 B hB hF
  have h2430 : mixedVector B (Sum.inr 2430) = Sparse.eval nodeValue2430 (mixedVector B) := by
    change mixedMoment B node2430 node2430Labels = _
    exact sound2430 B hB hF
  have h2471 : mixedVector B (Sum.inr 2471) = Sparse.eval nodeValue2471 (mixedVector B) := by
    change mixedMoment B node2471 node2471Labels = _
    exact sound2471 B hB hF
  have h2528 : mixedVector B (Sum.inr 2528) = Sparse.eval nodeValue2528 (mixedVector B) := by
    change mixedMoment B node2528 node2528Labels = _
    exact sound2528 B hB hF
  have h2532 : mixedVector B (Sum.inr 2532) = Sparse.eval nodeValue2532 (mixedVector B) := by
    change mixedMoment B node2532 node2532Labels = _
    exact sound2532 B hB hF
  have h2573 : mixedVector B (Sum.inr 2573) = Sparse.eval nodeValue2573 (mixedVector B) := by
    change mixedMoment B node2573 node2573Labels = _
    exact sound2573 B hB hF
  have h2574 : mixedVector B (Sum.inr 2574) = Sparse.eval nodeValue2574 (mixedVector B) := by
    change mixedMoment B node2574 node2574Labels = _
    exact sound2574 B hB hF
  have h2575 : mixedVector B (Sum.inr 2575) = Sparse.eval nodeValue2575 (mixedVector B) := by
    change mixedMoment B node2575 node2575Labels = _
    exact sound2575 B hB hF
  have h2600 : mixedVector B (Sum.inr 2600) = Sparse.eval nodeValue2600 (mixedVector B) := by
    change mixedMoment B node2600 node2600Labels = _
    exact sound2600 B hB hF
  have h2602 : mixedVector B (Sum.inr 2602) = Sparse.eval nodeValue2602 (mixedVector B) := by
    change mixedMoment B node2602 node2602Labels = _
    exact sound2602 B hB hF
  have h2754 : mixedVector B (Sum.inr 2754) = Sparse.eval nodeValue2754 (mixedVector B) := by
    change mixedMoment B node2754 node2754Labels = _
    exact sound2754 B hB hF
  have h2755 : mixedVector B (Sum.inr 2755) = Sparse.eval nodeValue2755 (mixedVector B) := by
    change mixedMoment B node2755 node2755Labels = _
    exact sound2755 B hB hF
  have h3109 : mixedVector B (Sum.inr 3109) = Sparse.eval nodeValue3109 (mixedVector B) := by
    change mixedMoment B node3109 node3109Labels = _
    exact sound3109 B hB hF
  have h3204 : mixedVector B (Sum.inr 3204) = Sparse.eval nodeValue3204 (mixedVector B) := by
    change mixedMoment B node3204 node3204Labels = _
    exact sound3204 B hB hF
  have h3207 : mixedVector B (Sum.inr 3207) = Sparse.eval nodeValue3207 (mixedVector B) := by
    change mixedMoment B node3207 node3207Labels = _
    exact sound3207 B hB hF
  have h3213 : mixedVector B (Sum.inr 3213) = Sparse.eval nodeValue3213 (mixedVector B) := by
    change mixedMoment B node3213 node3213Labels = _
    exact sound3213 B hB hF
  have h3229 : mixedVector B (Sum.inr 3229) = Sparse.eval nodeValue3229 (mixedVector B) := by
    change mixedMoment B node3229 node3229Labels = _
    exact sound3229 B hB hF
  simpa only [sourceForm1974, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h909, h911, h914, h931, h1024, h1327, h1333, h1340, h1413, h2323, h2327, h2340, h2423, h2430, h2471, h2528, h2532, h2573, h2574, h2575, h2600, h2602, h2754, h2755, h3109, h3204, h3207, h3213, h3229, reducedSource1674] using sourceEq1974 B hB

theorem rowSound1674 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1674 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1674, numericCheck1674, reducedZero1674 B hB hF, mul_zero]

theorem reducedZero1675 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1675 (mixedVector B) = 0 := by
  have h1670 : mixedVector B (Sum.inr 1670) = Sparse.eval nodeValue1670 (mixedVector B) := by
    change mixedMoment B node1670 node1670Labels = _
    exact sound1670 B hB hF
  have h1684 : mixedVector B (Sum.inr 1684) = Sparse.eval nodeValue1684 (mixedVector B) := by
    change mixedMoment B node1684 node1684Labels = _
    exact sound1684 B hB hF
  have h1685 : mixedVector B (Sum.inr 1685) = Sparse.eval nodeValue1685 (mixedVector B) := by
    change mixedMoment B node1685 node1685Labels = _
    exact sound1685 B hB hF
  have h1686 : mixedVector B (Sum.inr 1686) = Sparse.eval nodeValue1686 (mixedVector B) := by
    change mixedMoment B node1686 node1686Labels = _
    exact sound1686 B hB hF
  have h1688 : mixedVector B (Sum.inr 1688) = Sparse.eval nodeValue1688 (mixedVector B) := by
    change mixedMoment B node1688 node1688Labels = _
    exact sound1688 B hB hF
  have h1689 : mixedVector B (Sum.inr 1689) = Sparse.eval nodeValue1689 (mixedVector B) := by
    change mixedMoment B node1689 node1689Labels = _
    exact sound1689 B hB hF
  have h1690 : mixedVector B (Sum.inr 1690) = Sparse.eval nodeValue1690 (mixedVector B) := by
    change mixedMoment B node1690 node1690Labels = _
    exact sound1690 B hB hF
  have h1744 : mixedVector B (Sum.inr 1744) = Sparse.eval nodeValue1744 (mixedVector B) := by
    change mixedMoment B node1744 node1744Labels = _
    exact sound1744 B hB hF
  have h1750 : mixedVector B (Sum.inr 1750) = Sparse.eval nodeValue1750 (mixedVector B) := by
    change mixedMoment B node1750 node1750Labels = _
    exact sound1750 B hB hF
  have h2147 : mixedVector B (Sum.inr 2147) = Sparse.eval nodeValue2147 (mixedVector B) := by
    change mixedMoment B node2147 node2147Labels = _
    exact sound2147 B hB hF
  have h2164 : mixedVector B (Sum.inr 2164) = Sparse.eval nodeValue2164 (mixedVector B) := by
    change mixedMoment B node2164 node2164Labels = _
    exact sound2164 B hB hF
  have h2165 : mixedVector B (Sum.inr 2165) = Sparse.eval nodeValue2165 (mixedVector B) := by
    change mixedMoment B node2165 node2165Labels = _
    exact sound2165 B hB hF
  have h2181 : mixedVector B (Sum.inr 2181) = Sparse.eval nodeValue2181 (mixedVector B) := by
    change mixedMoment B node2181 node2181Labels = _
    exact sound2181 B hB hF
  have h2182 : mixedVector B (Sum.inr 2182) = Sparse.eval nodeValue2182 (mixedVector B) := by
    change mixedMoment B node2182 node2182Labels = _
    exact sound2182 B hB hF
  have h2198 : mixedVector B (Sum.inr 2198) = Sparse.eval nodeValue2198 (mixedVector B) := by
    change mixedMoment B node2198 node2198Labels = _
    exact sound2198 B hB hF
  have h2201 : mixedVector B (Sum.inr 2201) = Sparse.eval nodeValue2201 (mixedVector B) := by
    change mixedMoment B node2201 node2201Labels = _
    exact sound2201 B hB hF
  have h2202 : mixedVector B (Sum.inr 2202) = Sparse.eval nodeValue2202 (mixedVector B) := by
    change mixedMoment B node2202 node2202Labels = _
    exact sound2202 B hB hF
  have h2223 : mixedVector B (Sum.inr 2223) = Sparse.eval nodeValue2223 (mixedVector B) := by
    change mixedMoment B node2223 node2223Labels = _
    exact sound2223 B hB hF
  have h2224 : mixedVector B (Sum.inr 2224) = Sparse.eval nodeValue2224 (mixedVector B) := by
    change mixedMoment B node2224 node2224Labels = _
    exact sound2224 B hB hF
  have h2225 : mixedVector B (Sum.inr 2225) = Sparse.eval nodeValue2225 (mixedVector B) := by
    change mixedMoment B node2225 node2225Labels = _
    exact sound2225 B hB hF
  have h2227 : mixedVector B (Sum.inr 2227) = Sparse.eval nodeValue2227 (mixedVector B) := by
    change mixedMoment B node2227 node2227Labels = _
    exact sound2227 B hB hF
  have h2287 : mixedVector B (Sum.inr 2287) = Sparse.eval nodeValue2287 (mixedVector B) := by
    change mixedMoment B node2287 node2287Labels = _
    exact sound2287 B hB hF
  have h2290 : mixedVector B (Sum.inr 2290) = Sparse.eval nodeValue2290 (mixedVector B) := by
    change mixedMoment B node2290 node2290Labels = _
    exact sound2290 B hB hF
  have h2291 : mixedVector B (Sum.inr 2291) = Sparse.eval nodeValue2291 (mixedVector B) := by
    change mixedMoment B node2291 node2291Labels = _
    exact sound2291 B hB hF
  have h2681 : mixedVector B (Sum.inr 2681) = Sparse.eval nodeValue2681 (mixedVector B) := by
    change mixedMoment B node2681 node2681Labels = _
    exact sound2681 B hB hF
  have h2700 : mixedVector B (Sum.inr 2700) = Sparse.eval nodeValue2700 (mixedVector B) := by
    change mixedMoment B node2700 node2700Labels = _
    exact sound2700 B hB hF
  have h2735 : mixedVector B (Sum.inr 2735) = Sparse.eval nodeValue2735 (mixedVector B) := by
    change mixedMoment B node2735 node2735Labels = _
    exact sound2735 B hB hF
  have h2738 : mixedVector B (Sum.inr 2738) = Sparse.eval nodeValue2738 (mixedVector B) := by
    change mixedMoment B node2738 node2738Labels = _
    exact sound2738 B hB hF
  have h2739 : mixedVector B (Sum.inr 2739) = Sparse.eval nodeValue2739 (mixedVector B) := by
    change mixedMoment B node2739 node2739Labels = _
    exact sound2739 B hB hF
  simpa only [sourceForm1975, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1670, h1684, h1685, h1686, h1688, h1689, h1690, h1744, h1750, h2147, h2164, h2165, h2181, h2182, h2198, h2201, h2202, h2223, h2224, h2225, h2227, h2287, h2290, h2291, h2681, h2700, h2735, h2738, h2739, reducedSource1675] using sourceEq1975 B hB

theorem rowSound1675 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1675 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1675, numericCheck1675, reducedZero1675 B hB hF, mul_zero]

theorem reducedZero1676 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1676 (mixedVector B) = 0 := by
  have h913 : mixedVector B (Sum.inr 913) = Sparse.eval nodeValue913 (mixedVector B) := by
    change mixedMoment B node913 node913Labels = _
    exact sound913 B hB hF
  have h1796 : mixedVector B (Sum.inr 1796) = Sparse.eval nodeValue1796 (mixedVector B) := by
    change mixedMoment B node1796 node1796Labels = _
    exact sound1796 B hB hF
  have h1956 : mixedVector B (Sum.inr 1956) = Sparse.eval nodeValue1956 (mixedVector B) := by
    change mixedMoment B node1956 node1956Labels = _
    exact sound1956 B hB hF
  have h1979 : mixedVector B (Sum.inr 1979) = Sparse.eval nodeValue1979 (mixedVector B) := by
    change mixedMoment B node1979 node1979Labels = _
    exact sound1979 B hB hF
  have h2025 : mixedVector B (Sum.inr 2025) = Sparse.eval nodeValue2025 (mixedVector B) := by
    change mixedMoment B node2025 node2025Labels = _
    exact sound2025 B hB hF
  have h2029 : mixedVector B (Sum.inr 2029) = Sparse.eval nodeValue2029 (mixedVector B) := by
    change mixedMoment B node2029 node2029Labels = _
    exact sound2029 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1976, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h913, h1796, h1956, h1979, h2025, h2029, h4083, reducedSource1676] using sourceEq1976 B hB

theorem rowSound1676 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1676 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1676, numericCheck1676, reducedZero1676 B hB hF, mul_zero]

theorem reducedZero1677 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1677 (mixedVector B) = 0 := by
  have h1326 : mixedVector B (Sum.inr 1326) = Sparse.eval nodeValue1326 (mixedVector B) := by
    change mixedMoment B node1326 node1326Labels = _
    exact sound1326 B hB hF
  have h1956 : mixedVector B (Sum.inr 1956) = Sparse.eval nodeValue1956 (mixedVector B) := by
    change mixedMoment B node1956 node1956Labels = _
    exact sound1956 B hB hF
  have h1964 : mixedVector B (Sum.inr 1964) = Sparse.eval nodeValue1964 (mixedVector B) := by
    change mixedMoment B node1964 node1964Labels = _
    exact sound1964 B hB hF
  have h2025 : mixedVector B (Sum.inr 2025) = Sparse.eval nodeValue2025 (mixedVector B) := by
    change mixedMoment B node2025 node2025Labels = _
    exact sound2025 B hB hF
  have h2923 : mixedVector B (Sum.inr 2923) = Sparse.eval nodeValue2923 (mixedVector B) := by
    change mixedMoment B node2923 node2923Labels = _
    exact sound2923 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1977, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1326, h1956, h1964, h2025, h2923, h4083, reducedSource1677] using sourceEq1977 B hB

theorem rowSound1677 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1677 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1677, numericCheck1677, reducedZero1677 B hB hF, mul_zero]

theorem reducedZero1678 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1678 (mixedVector B) = 0 := by
  have h930 : mixedVector B (Sum.inr 930) = Sparse.eval nodeValue930 (mixedVector B) := by
    change mixedMoment B node930 node930Labels = _
    exact sound930 B hB hF
  have h1812 : mixedVector B (Sum.inr 1812) = Sparse.eval nodeValue1812 (mixedVector B) := by
    change mixedMoment B node1812 node1812Labels = _
    exact sound1812 B hB hF
  have h1964 : mixedVector B (Sum.inr 1964) = Sparse.eval nodeValue1964 (mixedVector B) := by
    change mixedMoment B node1964 node1964Labels = _
    exact sound1964 B hB hF
  have h2025 : mixedVector B (Sum.inr 2025) = Sparse.eval nodeValue2025 (mixedVector B) := by
    change mixedMoment B node2025 node2025Labels = _
    exact sound2025 B hB hF
  have h2057 : mixedVector B (Sum.inr 2057) = Sparse.eval nodeValue2057 (mixedVector B) := by
    change mixedMoment B node2057 node2057Labels = _
    exact sound2057 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1978, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h930, h1812, h1964, h2025, h2057, h4083, reducedSource1678] using sourceEq1978 B hB

theorem rowSound1678 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1678 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1678, numericCheck1678, reducedZero1678 B hB hF, mul_zero]

theorem reducedZero1679 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1679 (mixedVector B) = 0 := by
  have h4414 : mixedVector B (Sum.inr 4414) = Sparse.eval nodeValue4414 (mixedVector B) := by
    change mixedMoment B node4414 node4414Labels = _
    exact sound4414 B hB hF
  have h4418 : mixedVector B (Sum.inr 4418) = Sparse.eval nodeValue4418 (mixedVector B) := by
    change mixedMoment B node4418 node4418Labels = _
    exact sound4418 B hB hF
  have h4420 : mixedVector B (Sum.inr 4420) = Sparse.eval nodeValue4420 (mixedVector B) := by
    change mixedMoment B node4420 node4420Labels = _
    exact sound4420 B hB hF
  have h4425 : mixedVector B (Sum.inr 4425) = Sparse.eval nodeValue4425 (mixedVector B) := by
    change mixedMoment B node4425 node4425Labels = _
    exact sound4425 B hB hF
  have h4486 : mixedVector B (Sum.inr 4486) = Sparse.eval nodeValue4486 (mixedVector B) := by
    change mixedMoment B node4486 node4486Labels = _
    exact sound4486 B hB hF
  have h4729 : mixedVector B (Sum.inr 4729) = Sparse.eval nodeValue4729 (mixedVector B) := by
    change mixedMoment B node4729 node4729Labels = _
    exact sound4729 B hB hF
  have h4741 : mixedVector B (Sum.inr 4741) = Sparse.eval nodeValue4741 (mixedVector B) := by
    change mixedMoment B node4741 node4741Labels = _
    exact sound4741 B hB hF
  have h4742 : mixedVector B (Sum.inr 4742) = Sparse.eval nodeValue4742 (mixedVector B) := by
    change mixedMoment B node4742 node4742Labels = _
    exact sound4742 B hB hF
  have h4747 : mixedVector B (Sum.inr 4747) = Sparse.eval nodeValue4747 (mixedVector B) := by
    change mixedMoment B node4747 node4747Labels = _
    exact sound4747 B hB hF
  have h4779 : mixedVector B (Sum.inr 4779) = Sparse.eval nodeValue4779 (mixedVector B) := by
    change mixedMoment B node4779 node4779Labels = _
    exact sound4779 B hB hF
  have h4780 : mixedVector B (Sum.inr 4780) = Sparse.eval nodeValue4780 (mixedVector B) := by
    change mixedMoment B node4780 node4780Labels = _
    exact sound4780 B hB hF
  have h4783 : mixedVector B (Sum.inr 4783) = Sparse.eval nodeValue4783 (mixedVector B) := by
    change mixedMoment B node4783 node4783Labels = _
    exact sound4783 B hB hF
  have h4792 : mixedVector B (Sum.inr 4792) = Sparse.eval nodeValue4792 (mixedVector B) := by
    change mixedMoment B node4792 node4792Labels = _
    exact sound4792 B hB hF
  have h4793 : mixedVector B (Sum.inr 4793) = Sparse.eval nodeValue4793 (mixedVector B) := by
    change mixedMoment B node4793 node4793Labels = _
    exact sound4793 B hB hF
  have h4804 : mixedVector B (Sum.inr 4804) = Sparse.eval nodeValue4804 (mixedVector B) := by
    change mixedMoment B node4804 node4804Labels = _
    exact sound4804 B hB hF
  have h4807 : mixedVector B (Sum.inr 4807) = Sparse.eval nodeValue4807 (mixedVector B) := by
    change mixedMoment B node4807 node4807Labels = _
    exact sound4807 B hB hF
  have h4808 : mixedVector B (Sum.inr 4808) = Sparse.eval nodeValue4808 (mixedVector B) := by
    change mixedMoment B node4808 node4808Labels = _
    exact sound4808 B hB hF
  have h4817 : mixedVector B (Sum.inr 4817) = Sparse.eval nodeValue4817 (mixedVector B) := by
    change mixedMoment B node4817 node4817Labels = _
    exact sound4817 B hB hF
  have h4819 : mixedVector B (Sum.inr 4819) = Sparse.eval nodeValue4819 (mixedVector B) := by
    change mixedMoment B node4819 node4819Labels = _
    exact sound4819 B hB hF
  have h4824 : mixedVector B (Sum.inr 4824) = Sparse.eval nodeValue4824 (mixedVector B) := by
    change mixedMoment B node4824 node4824Labels = _
    exact sound4824 B hB hF
  have h4841 : mixedVector B (Sum.inr 4841) = Sparse.eval nodeValue4841 (mixedVector B) := by
    change mixedMoment B node4841 node4841Labels = _
    exact sound4841 B hB hF
  have h4843 : mixedVector B (Sum.inr 4843) = Sparse.eval nodeValue4843 (mixedVector B) := by
    change mixedMoment B node4843 node4843Labels = _
    exact sound4843 B hB hF
  have h4853 : mixedVector B (Sum.inr 4853) = Sparse.eval nodeValue4853 (mixedVector B) := by
    change mixedMoment B node4853 node4853Labels = _
    exact sound4853 B hB hF
  have h4871 : mixedVector B (Sum.inr 4871) = Sparse.eval nodeValue4871 (mixedVector B) := by
    change mixedMoment B node4871 node4871Labels = _
    exact sound4871 B hB hF
  have h5078 : mixedVector B (Sum.inr 5078) = Sparse.eval nodeValue5078 (mixedVector B) := by
    change mixedMoment B node5078 node5078Labels = _
    exact sound5078 B hB hF
  have h5128 : mixedVector B (Sum.inr 5128) = Sparse.eval nodeValue5128 (mixedVector B) := by
    change mixedMoment B node5128 node5128Labels = _
    exact sound5128 B hB hF
  have h5174 : mixedVector B (Sum.inr 5174) = Sparse.eval nodeValue5174 (mixedVector B) := by
    change mixedMoment B node5174 node5174Labels = _
    exact sound5174 B hB hF
  simpa only [sourceForm1979, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4414, h4418, h4420, h4425, h4486, h4729, h4741, h4742, h4747, h4779, h4780, h4783, h4792, h4793, h4804, h4807, h4808, h4817, h4819, h4824, h4841, h4843, h4853, h4871, h5078, h5128, h5174, reducedSource1679] using sourceEq1979 B hB

theorem rowSound1679 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1679 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1679, numericCheck1679, reducedZero1679 B hB hF, mul_zero]

theorem sourceRowsAt1664 : MixedData.sourceRows (1664 : Fin 2425) =
    MixedData.row1664 := by decide +kernel

theorem sourceRowsAt1665 : MixedData.sourceRows (1665 : Fin 2425) =
    MixedData.row1665 := by decide +kernel

theorem sourceRowsAt1666 : MixedData.sourceRows (1666 : Fin 2425) =
    MixedData.row1666 := by decide +kernel

theorem sourceRowsAt1667 : MixedData.sourceRows (1667 : Fin 2425) =
    MixedData.row1667 := by decide +kernel

theorem sourceRowsAt1668 : MixedData.sourceRows (1668 : Fin 2425) =
    MixedData.row1668 := by decide +kernel

theorem sourceRowsAt1669 : MixedData.sourceRows (1669 : Fin 2425) =
    MixedData.row1669 := by decide +kernel

theorem sourceRowsAt1670 : MixedData.sourceRows (1670 : Fin 2425) =
    MixedData.row1670 := by decide +kernel

theorem sourceRowsAt1671 : MixedData.sourceRows (1671 : Fin 2425) =
    MixedData.row1671 := by decide +kernel

theorem sourceRowsAt1672 : MixedData.sourceRows (1672 : Fin 2425) =
    MixedData.row1672 := by decide +kernel

theorem sourceRowsAt1673 : MixedData.sourceRows (1673 : Fin 2425) =
    MixedData.row1673 := by decide +kernel

theorem sourceRowsAt1674 : MixedData.sourceRows (1674 : Fin 2425) =
    MixedData.row1674 := by decide +kernel

theorem sourceRowsAt1675 : MixedData.sourceRows (1675 : Fin 2425) =
    MixedData.row1675 := by decide +kernel

theorem sourceRowsAt1676 : MixedData.sourceRows (1676 : Fin 2425) =
    MixedData.row1676 := by decide +kernel

theorem sourceRowsAt1677 : MixedData.sourceRows (1677 : Fin 2425) =
    MixedData.row1677 := by decide +kernel

theorem sourceRowsAt1678 : MixedData.sourceRows (1678 : Fin 2425) =
    MixedData.row1678 := by decide +kernel

theorem sourceRowsAt1679 : MixedData.sourceRows (1679 : Fin 2425) =
    MixedData.row1679 := by decide +kernel

theorem chunkSound104 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 104) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1664 ∨ k.val = 1665 ∨ k.val = 1666 ∨ k.val = 1667 ∨ k.val = 1668 ∨ k.val = 1669 ∨ k.val = 1670 ∨ k.val = 1671 ∨ k.val = 1672 ∨ k.val = 1673 ∨ k.val = 1674 ∨ k.val = 1675 ∨ k.val = 1676 ∨ k.val = 1677 ∨ k.val = 1678 ∨ k.val = 1679 := by omega
  rcases heq with h1664 | h1665 | h1666 | h1667 | h1668 | h1669 | h1670 | h1671 | h1672 | h1673 | h1674 | h1675 | h1676 | h1677 | h1678 | h1679
  · have he : k = (1664 : Fin 2425) := Fin.ext h1664
    subst k
    rw [sourceRowsAt1664]
    exact rowSound1664 B hB hF
  · have he : k = (1665 : Fin 2425) := Fin.ext h1665
    subst k
    rw [sourceRowsAt1665]
    exact rowSound1665 B hB hF
  · have he : k = (1666 : Fin 2425) := Fin.ext h1666
    subst k
    rw [sourceRowsAt1666]
    exact rowSound1666 B hB hF
  · have he : k = (1667 : Fin 2425) := Fin.ext h1667
    subst k
    rw [sourceRowsAt1667]
    exact rowSound1667 B hB hF
  · have he : k = (1668 : Fin 2425) := Fin.ext h1668
    subst k
    rw [sourceRowsAt1668]
    exact rowSound1668 B hB hF
  · have he : k = (1669 : Fin 2425) := Fin.ext h1669
    subst k
    rw [sourceRowsAt1669]
    exact rowSound1669 B hB hF
  · have he : k = (1670 : Fin 2425) := Fin.ext h1670
    subst k
    rw [sourceRowsAt1670]
    exact rowSound1670 B hB hF
  · have he : k = (1671 : Fin 2425) := Fin.ext h1671
    subst k
    rw [sourceRowsAt1671]
    exact rowSound1671 B hB hF
  · have he : k = (1672 : Fin 2425) := Fin.ext h1672
    subst k
    rw [sourceRowsAt1672]
    exact rowSound1672 B hB hF
  · have he : k = (1673 : Fin 2425) := Fin.ext h1673
    subst k
    rw [sourceRowsAt1673]
    exact rowSound1673 B hB hF
  · have he : k = (1674 : Fin 2425) := Fin.ext h1674
    subst k
    rw [sourceRowsAt1674]
    exact rowSound1674 B hB hF
  · have he : k = (1675 : Fin 2425) := Fin.ext h1675
    subst k
    rw [sourceRowsAt1675]
    exact rowSound1675 B hB hF
  · have he : k = (1676 : Fin 2425) := Fin.ext h1676
    subst k
    rw [sourceRowsAt1676]
    exact rowSound1676 B hB hF
  · have he : k = (1677 : Fin 2425) := Fin.ext h1677
    subst k
    rw [sourceRowsAt1677]
    exact rowSound1677 B hB hF
  · have he : k = (1678 : Fin 2425) := Fin.ext h1678
    subst k
    rw [sourceRowsAt1678]
    exact rowSound1678 B hB hF
  · have he : k = (1679 : Fin 2425) := Fin.ext h1679
    subst k
    rw [sourceRowsAt1679]
    exact rowSound1679 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
