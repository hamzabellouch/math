import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources12

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero320 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource320 (mixedVector B) = 0 := by
  have h2710 : mixedVector B (Sum.inr 2710) = Sparse.eval nodeValue2710 (mixedVector B) := by
    change mixedMoment B node2710 node2710Labels = _
    exact sound2710 B hB hF
  have h3801 : mixedVector B (Sum.inr 3801) = Sparse.eval nodeValue3801 (mixedVector B) := by
    change mixedMoment B node3801 node3801Labels = _
    exact sound3801 B hB hF
  have h3872 : mixedVector B (Sum.inr 3872) = Sparse.eval nodeValue3872 (mixedVector B) := by
    change mixedMoment B node3872 node3872Labels = _
    exact sound3872 B hB hF
  have h3899 : mixedVector B (Sum.inr 3899) = Sparse.eval nodeValue3899 (mixedVector B) := by
    change mixedMoment B node3899 node3899Labels = _
    exact sound3899 B hB hF
  have h3901 : mixedVector B (Sum.inr 3901) = Sparse.eval nodeValue3901 (mixedVector B) := by
    change mixedMoment B node3901 node3901Labels = _
    exact sound3901 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm382, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2710, h3801, h3872, h3899, h3901, h4091, reducedSource320] using sourceEq382 B hB

theorem rowSound320 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row320 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck320, numericCheck320, reducedZero320 B hB hF, mul_zero]

theorem reducedZero321 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource321 (mixedVector B) = 0 := by
  have h1248 : mixedVector B (Sum.inr 1248) = Sparse.eval nodeValue1248 (mixedVector B) := by
    change mixedMoment B node1248 node1248Labels = _
    exact sound1248 B hB hF
  have h2623 : mixedVector B (Sum.inr 2623) = Sparse.eval nodeValue2623 (mixedVector B) := by
    change mixedMoment B node2623 node2623Labels = _
    exact sound2623 B hB hF
  have h2710 : mixedVector B (Sum.inr 2710) = Sparse.eval nodeValue2710 (mixedVector B) := by
    change mixedMoment B node2710 node2710Labels = _
    exact sound2710 B hB hF
  have h2745 : mixedVector B (Sum.inr 2745) = Sparse.eval nodeValue2745 (mixedVector B) := by
    change mixedMoment B node2745 node2745Labels = _
    exact sound2745 B hB hF
  have h2750 : mixedVector B (Sum.inr 2750) = Sparse.eval nodeValue2750 (mixedVector B) := by
    change mixedMoment B node2750 node2750Labels = _
    exact sound2750 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm384, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1248, h2623, h2710, h2745, h2750, h4091, reducedSource321] using sourceEq384 B hB

theorem rowSound321 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row321 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck321, numericCheck321, reducedZero321 B hB hF, mul_zero]

theorem reducedZero322 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource322 (mixedVector B) = 0 := by
  have h2471 : mixedVector B (Sum.inr 2471) = Sparse.eval nodeValue2471 (mixedVector B) := by
    change mixedMoment B node2471 node2471Labels = _
    exact sound2471 B hB hF
  have h2473 : mixedVector B (Sum.inr 2473) = Sparse.eval nodeValue2473 (mixedVector B) := by
    change mixedMoment B node2473 node2473Labels = _
    exact sound2473 B hB hF
  have h2483 : mixedVector B (Sum.inr 2483) = Sparse.eval nodeValue2483 (mixedVector B) := by
    change mixedMoment B node2483 node2483Labels = _
    exact sound2483 B hB hF
  have h2710 : mixedVector B (Sum.inr 2710) = Sparse.eval nodeValue2710 (mixedVector B) := by
    change mixedMoment B node2710 node2710Labels = _
    exact sound2710 B hB hF
  have h3801 : mixedVector B (Sum.inr 3801) = Sparse.eval nodeValue3801 (mixedVector B) := by
    change mixedMoment B node3801 node3801Labels = _
    exact sound3801 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm385, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2471, h2473, h2483, h2710, h3801, h4091, reducedSource322] using sourceEq385 B hB

theorem rowSound322 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row322 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck322, numericCheck322, reducedZero322 B hB hF, mul_zero]

theorem reducedZero323 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource323 (mixedVector B) = 0 := by
  have h1216 : mixedVector B (Sum.inr 1216) = Sparse.eval nodeValue1216 (mixedVector B) := by
    change mixedMoment B node1216 node1216Labels = _
    exact sound1216 B hB hF
  have h2483 : mixedVector B (Sum.inr 2483) = Sparse.eval nodeValue2483 (mixedVector B) := by
    change mixedMoment B node2483 node2483Labels = _
    exact sound2483 B hB hF
  have h2617 : mixedVector B (Sum.inr 2617) = Sparse.eval nodeValue2617 (mixedVector B) := by
    change mixedMoment B node2617 node2617Labels = _
    exact sound2617 B hB hF
  have h2710 : mixedVector B (Sum.inr 2710) = Sparse.eval nodeValue2710 (mixedVector B) := by
    change mixedMoment B node2710 node2710Labels = _
    exact sound2710 B hB hF
  have h2721 : mixedVector B (Sum.inr 2721) = Sparse.eval nodeValue2721 (mixedVector B) := by
    change mixedMoment B node2721 node2721Labels = _
    exact sound2721 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm386, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1216, h2483, h2617, h2710, h2721, h4091, reducedSource323] using sourceEq386 B hB

theorem rowSound323 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row323 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck323, numericCheck323, reducedZero323 B hB hF, mul_zero]

theorem reducedZero324 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource324 (mixedVector B) = 0 := by
  have h2611 : mixedVector B (Sum.inr 2611) = Sparse.eval nodeValue2611 (mixedVector B) := by
    change mixedMoment B node2611 node2611Labels = _
    exact sound2611 B hB hF
  have h2612 : mixedVector B (Sum.inr 2612) = Sparse.eval nodeValue2612 (mixedVector B) := by
    change mixedMoment B node2612 node2612Labels = _
    exact sound2612 B hB hF
  have h2617 : mixedVector B (Sum.inr 2617) = Sparse.eval nodeValue2617 (mixedVector B) := by
    change mixedMoment B node2617 node2617Labels = _
    exact sound2617 B hB hF
  have h2623 : mixedVector B (Sum.inr 2623) = Sparse.eval nodeValue2623 (mixedVector B) := by
    change mixedMoment B node2623 node2623Labels = _
    exact sound2623 B hB hF
  have h2710 : mixedVector B (Sum.inr 2710) = Sparse.eval nodeValue2710 (mixedVector B) := by
    change mixedMoment B node2710 node2710Labels = _
    exact sound2710 B hB hF
  have h3872 : mixedVector B (Sum.inr 3872) = Sparse.eval nodeValue3872 (mixedVector B) := by
    change mixedMoment B node3872 node3872Labels = _
    exact sound3872 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm387, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2611, h2612, h2617, h2623, h2710, h3872, h4091, reducedSource324] using sourceEq387 B hB

theorem rowSound324 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row324 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck324, numericCheck324, reducedZero324 B hB hF, mul_zero]

theorem reducedZero325 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource325 (mixedVector B) = 0 := by
  have h2707 : mixedVector B (Sum.inr 2707) = Sparse.eval nodeValue2707 (mixedVector B) := by
    change mixedMoment B node2707 node2707Labels = _
    exact sound2707 B hB hF
  have h2710 : mixedVector B (Sum.inr 2710) = Sparse.eval nodeValue2710 (mixedVector B) := by
    change mixedMoment B node2710 node2710Labels = _
    exact sound2710 B hB hF
  have h2745 : mixedVector B (Sum.inr 2745) = Sparse.eval nodeValue2745 (mixedVector B) := by
    change mixedMoment B node2745 node2745Labels = _
    exact sound2745 B hB hF
  have h3899 : mixedVector B (Sum.inr 3899) = Sparse.eval nodeValue3899 (mixedVector B) := by
    change mixedMoment B node3899 node3899Labels = _
    exact sound3899 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm388, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2707, h2710, h2745, h3899, h4091, reducedSource325] using sourceEq388 B hB

theorem rowSound325 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row325 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck325, numericCheck325, reducedZero325 B hB hF, mul_zero]

theorem reducedZero326 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource326 (mixedVector B) = 0 := by
  have h4391 : mixedVector B (Sum.inr 4391) = Sparse.eval nodeValue4391 (mixedVector B) := by
    change mixedMoment B node4391 node4391Labels = _
    exact sound4391 B hB hF
  have h4392 : mixedVector B (Sum.inr 4392) = Sparse.eval nodeValue4392 (mixedVector B) := by
    change mixedMoment B node4392 node4392Labels = _
    exact sound4392 B hB hF
  have h4400 : mixedVector B (Sum.inr 4400) = Sparse.eval nodeValue4400 (mixedVector B) := by
    change mixedMoment B node4400 node4400Labels = _
    exact sound4400 B hB hF
  have h4439 : mixedVector B (Sum.inr 4439) = Sparse.eval nodeValue4439 (mixedVector B) := by
    change mixedMoment B node4439 node4439Labels = _
    exact sound4439 B hB hF
  have h4992 : mixedVector B (Sum.inr 4992) = Sparse.eval nodeValue4992 (mixedVector B) := by
    change mixedMoment B node4992 node4992Labels = _
    exact sound4992 B hB hF
  have h4993 : mixedVector B (Sum.inr 4993) = Sparse.eval nodeValue4993 (mixedVector B) := by
    change mixedMoment B node4993 node4993Labels = _
    exact sound4993 B hB hF
  have h4999 : mixedVector B (Sum.inr 4999) = Sparse.eval nodeValue4999 (mixedVector B) := by
    change mixedMoment B node4999 node4999Labels = _
    exact sound4999 B hB hF
  have h5128 : mixedVector B (Sum.inr 5128) = Sparse.eval nodeValue5128 (mixedVector B) := by
    change mixedMoment B node5128 node5128Labels = _
    exact sound5128 B hB hF
  have h5129 : mixedVector B (Sum.inr 5129) = Sparse.eval nodeValue5129 (mixedVector B) := by
    change mixedMoment B node5129 node5129Labels = _
    exact sound5129 B hB hF
  have h5138 : mixedVector B (Sum.inr 5138) = Sparse.eval nodeValue5138 (mixedVector B) := by
    change mixedMoment B node5138 node5138Labels = _
    exact sound5138 B hB hF
  have h5149 : mixedVector B (Sum.inr 5149) = Sparse.eval nodeValue5149 (mixedVector B) := by
    change mixedMoment B node5149 node5149Labels = _
    exact sound5149 B hB hF
  have h5249 : mixedVector B (Sum.inr 5249) = Sparse.eval nodeValue5249 (mixedVector B) := by
    change mixedMoment B node5249 node5249Labels = _
    exact sound5249 B hB hF
  have h5252 : mixedVector B (Sum.inr 5252) = Sparse.eval nodeValue5252 (mixedVector B) := by
    change mixedMoment B node5252 node5252Labels = _
    exact sound5252 B hB hF
  have h5255 : mixedVector B (Sum.inr 5255) = Sparse.eval nodeValue5255 (mixedVector B) := by
    change mixedMoment B node5255 node5255Labels = _
    exact sound5255 B hB hF
  have h5260 : mixedVector B (Sum.inr 5260) = Sparse.eval nodeValue5260 (mixedVector B) := by
    change mixedMoment B node5260 node5260Labels = _
    exact sound5260 B hB hF
  have h5281 : mixedVector B (Sum.inr 5281) = Sparse.eval nodeValue5281 (mixedVector B) := by
    change mixedMoment B node5281 node5281Labels = _
    exact sound5281 B hB hF
  have h5284 : mixedVector B (Sum.inr 5284) = Sparse.eval nodeValue5284 (mixedVector B) := by
    change mixedMoment B node5284 node5284Labels = _
    exact sound5284 B hB hF
  have h5424 : mixedVector B (Sum.inr 5424) = Sparse.eval nodeValue5424 (mixedVector B) := by
    change mixedMoment B node5424 node5424Labels = _
    exact sound5424 B hB hF
  have h5429 : mixedVector B (Sum.inr 5429) = Sparse.eval nodeValue5429 (mixedVector B) := by
    change mixedMoment B node5429 node5429Labels = _
    exact sound5429 B hB hF
  have h5439 : mixedVector B (Sum.inr 5439) = Sparse.eval nodeValue5439 (mixedVector B) := by
    change mixedMoment B node5439 node5439Labels = _
    exact sound5439 B hB hF
  have h5481 : mixedVector B (Sum.inr 5481) = Sparse.eval nodeValue5481 (mixedVector B) := by
    change mixedMoment B node5481 node5481Labels = _
    exact sound5481 B hB hF
  simpa only [sourceForm389, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4391, h4392, h4400, h4439, h4992, h4993, h4999, h5128, h5129, h5138, h5149, h5249, h5252, h5255, h5260, h5281, h5284, h5424, h5429, h5439, h5481, reducedSource326] using sourceEq389 B hB

theorem rowSound326 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row326 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck326, numericCheck326, reducedZero326 B hB hF, mul_zero]

theorem reducedZero327 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource327 (mixedVector B) = 0 := by
  have h972 : mixedVector B (Sum.inr 972) = Sparse.eval nodeValue972 (mixedVector B) := by
    change mixedMoment B node972 node972Labels = _
    exact sound972 B hB hF
  have h973 : mixedVector B (Sum.inr 973) = Sparse.eval nodeValue973 (mixedVector B) := by
    change mixedMoment B node973 node973Labels = _
    exact sound973 B hB hF
  have h981 : mixedVector B (Sum.inr 981) = Sparse.eval nodeValue981 (mixedVector B) := by
    change mixedMoment B node981 node981Labels = _
    exact sound981 B hB hF
  have h1021 : mixedVector B (Sum.inr 1021) = Sparse.eval nodeValue1021 (mixedVector B) := by
    change mixedMoment B node1021 node1021Labels = _
    exact sound1021 B hB hF
  have h2378 : mixedVector B (Sum.inr 2378) = Sparse.eval nodeValue2378 (mixedVector B) := by
    change mixedMoment B node2378 node2378Labels = _
    exact sound2378 B hB hF
  have h2379 : mixedVector B (Sum.inr 2379) = Sparse.eval nodeValue2379 (mixedVector B) := by
    change mixedMoment B node2379 node2379Labels = _
    exact sound2379 B hB hF
  have h2384 : mixedVector B (Sum.inr 2384) = Sparse.eval nodeValue2384 (mixedVector B) := by
    change mixedMoment B node2384 node2384Labels = _
    exact sound2384 B hB hF
  have h2543 : mixedVector B (Sum.inr 2543) = Sparse.eval nodeValue2543 (mixedVector B) := by
    change mixedMoment B node2543 node2543Labels = _
    exact sound2543 B hB hF
  have h2545 : mixedVector B (Sum.inr 2545) = Sparse.eval nodeValue2545 (mixedVector B) := by
    change mixedMoment B node2545 node2545Labels = _
    exact sound2545 B hB hF
  have h2557 : mixedVector B (Sum.inr 2557) = Sparse.eval nodeValue2557 (mixedVector B) := by
    change mixedMoment B node2557 node2557Labels = _
    exact sound2557 B hB hF
  have h2570 : mixedVector B (Sum.inr 2570) = Sparse.eval nodeValue2570 (mixedVector B) := by
    change mixedMoment B node2570 node2570Labels = _
    exact sound2570 B hB hF
  have h2708 : mixedVector B (Sum.inr 2708) = Sparse.eval nodeValue2708 (mixedVector B) := by
    change mixedMoment B node2708 node2708Labels = _
    exact sound2708 B hB hF
  have h2712 : mixedVector B (Sum.inr 2712) = Sparse.eval nodeValue2712 (mixedVector B) := by
    change mixedMoment B node2712 node2712Labels = _
    exact sound2712 B hB hF
  have h2718 : mixedVector B (Sum.inr 2718) = Sparse.eval nodeValue2718 (mixedVector B) := by
    change mixedMoment B node2718 node2718Labels = _
    exact sound2718 B hB hF
  have h2724 : mixedVector B (Sum.inr 2724) = Sparse.eval nodeValue2724 (mixedVector B) := by
    change mixedMoment B node2724 node2724Labels = _
    exact sound2724 B hB hF
  have h2750 : mixedVector B (Sum.inr 2750) = Sparse.eval nodeValue2750 (mixedVector B) := by
    change mixedMoment B node2750 node2750Labels = _
    exact sound2750 B hB hF
  have h2753 : mixedVector B (Sum.inr 2753) = Sparse.eval nodeValue2753 (mixedVector B) := by
    change mixedMoment B node2753 node2753Labels = _
    exact sound2753 B hB hF
  have h3954 : mixedVector B (Sum.inr 3954) = Sparse.eval nodeValue3954 (mixedVector B) := by
    change mixedMoment B node3954 node3954Labels = _
    exact sound3954 B hB hF
  have h3979 : mixedVector B (Sum.inr 3979) = Sparse.eval nodeValue3979 (mixedVector B) := by
    change mixedMoment B node3979 node3979Labels = _
    exact sound3979 B hB hF
  have h3990 : mixedVector B (Sum.inr 3990) = Sparse.eval nodeValue3990 (mixedVector B) := by
    change mixedMoment B node3990 node3990Labels = _
    exact sound3990 B hB hF
  have h4012 : mixedVector B (Sum.inr 4012) = Sparse.eval nodeValue4012 (mixedVector B) := by
    change mixedMoment B node4012 node4012Labels = _
    exact sound4012 B hB hF
  simpa only [sourceForm390, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h972, h973, h981, h1021, h2378, h2379, h2384, h2543, h2545, h2557, h2570, h2708, h2712, h2718, h2724, h2750, h2753, h3954, h3979, h3990, h4012, reducedSource327] using sourceEq390 B hB

theorem rowSound327 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row327 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck327, numericCheck327, reducedZero327 B hB hF, mul_zero]

theorem reducedZero328 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource328 (mixedVector B) = 0 := by
  have h1606 : mixedVector B (Sum.inr 1606) = Sparse.eval nodeValue1606 (mixedVector B) := by
    change mixedMoment B node1606 node1606Labels = _
    exact sound1606 B hB hF
  have h1607 : mixedVector B (Sum.inr 1607) = Sparse.eval nodeValue1607 (mixedVector B) := by
    change mixedMoment B node1607 node1607Labels = _
    exact sound1607 B hB hF
  have h1613 : mixedVector B (Sum.inr 1613) = Sparse.eval nodeValue1613 (mixedVector B) := by
    change mixedMoment B node1613 node1613Labels = _
    exact sound1613 B hB hF
  have h1713 : mixedVector B (Sum.inr 1713) = Sparse.eval nodeValue1713 (mixedVector B) := by
    change mixedMoment B node1713 node1713Labels = _
    exact sound1713 B hB hF
  have h3345 : mixedVector B (Sum.inr 3345) = Sparse.eval nodeValue3345 (mixedVector B) := by
    change mixedMoment B node3345 node3345Labels = _
    exact sound3345 B hB hF
  have h3346 : mixedVector B (Sum.inr 3346) = Sparse.eval nodeValue3346 (mixedVector B) := by
    change mixedMoment B node3346 node3346Labels = _
    exact sound3346 B hB hF
  have h3350 : mixedVector B (Sum.inr 3350) = Sparse.eval nodeValue3350 (mixedVector B) := by
    change mixedMoment B node3350 node3350Labels = _
    exact sound3350 B hB hF
  have h3502 : mixedVector B (Sum.inr 3502) = Sparse.eval nodeValue3502 (mixedVector B) := by
    change mixedMoment B node3502 node3502Labels = _
    exact sound3502 B hB hF
  have h3503 : mixedVector B (Sum.inr 3503) = Sparse.eval nodeValue3503 (mixedVector B) := by
    change mixedMoment B node3503 node3503Labels = _
    exact sound3503 B hB hF
  have h3516 : mixedVector B (Sum.inr 3516) = Sparse.eval nodeValue3516 (mixedVector B) := by
    change mixedMoment B node3516 node3516Labels = _
    exact sound3516 B hB hF
  have h3517 : mixedVector B (Sum.inr 3517) = Sparse.eval nodeValue3517 (mixedVector B) := by
    change mixedMoment B node3517 node3517Labels = _
    exact sound3517 B hB hF
  have h3519 : mixedVector B (Sum.inr 3519) = Sparse.eval nodeValue3519 (mixedVector B) := by
    change mixedMoment B node3519 node3519Labels = _
    exact sound3519 B hB hF
  have h3540 : mixedVector B (Sum.inr 3540) = Sparse.eval nodeValue3540 (mixedVector B) := by
    change mixedMoment B node3540 node3540Labels = _
    exact sound3540 B hB hF
  have h3543 : mixedVector B (Sum.inr 3543) = Sparse.eval nodeValue3543 (mixedVector B) := by
    change mixedMoment B node3543 node3543Labels = _
    exact sound3543 B hB hF
  have h3571 : mixedVector B (Sum.inr 3571) = Sparse.eval nodeValue3571 (mixedVector B) := by
    change mixedMoment B node3571 node3571Labels = _
    exact sound3571 B hB hF
  have h3605 : mixedVector B (Sum.inr 3605) = Sparse.eval nodeValue3605 (mixedVector B) := by
    change mixedMoment B node3605 node3605Labels = _
    exact sound3605 B hB hF
  have h3625 : mixedVector B (Sum.inr 3625) = Sparse.eval nodeValue3625 (mixedVector B) := by
    change mixedMoment B node3625 node3625Labels = _
    exact sound3625 B hB hF
  have h3843 : mixedVector B (Sum.inr 3843) = Sparse.eval nodeValue3843 (mixedVector B) := by
    change mixedMoment B node3843 node3843Labels = _
    exact sound3843 B hB hF
  have h3858 : mixedVector B (Sum.inr 3858) = Sparse.eval nodeValue3858 (mixedVector B) := by
    change mixedMoment B node3858 node3858Labels = _
    exact sound3858 B hB hF
  have h3874 : mixedVector B (Sum.inr 3874) = Sparse.eval nodeValue3874 (mixedVector B) := by
    change mixedMoment B node3874 node3874Labels = _
    exact sound3874 B hB hF
  have h3991 : mixedVector B (Sum.inr 3991) = Sparse.eval nodeValue3991 (mixedVector B) := by
    change mixedMoment B node3991 node3991Labels = _
    exact sound3991 B hB hF
  simpa only [sourceForm391, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1606, h1607, h1613, h1713, h3345, h3346, h3350, h3502, h3503, h3516, h3517, h3519, h3540, h3543, h3571, h3605, h3625, h3843, h3858, h3874, h3991, reducedSource328] using sourceEq391 B hB

theorem rowSound328 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row328 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck328, numericCheck328, reducedZero328 B hB hF, mul_zero]

theorem reducedZero329 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource329 (mixedVector B) = 0 := by
  have h3064 : mixedVector B (Sum.inr 3064) = Sparse.eval nodeValue3064 (mixedVector B) := by
    change mixedMoment B node3064 node3064Labels = _
    exact sound3064 B hB hF
  have h3838 : mixedVector B (Sum.inr 3838) = Sparse.eval nodeValue3838 (mixedVector B) := by
    change mixedMoment B node3838 node3838Labels = _
    exact sound3838 B hB hF
  have h3846 : mixedVector B (Sum.inr 3846) = Sparse.eval nodeValue3846 (mixedVector B) := by
    change mixedMoment B node3846 node3846Labels = _
    exact sound3846 B hB hF
  have h3902 : mixedVector B (Sum.inr 3902) = Sparse.eval nodeValue3902 (mixedVector B) := by
    change mixedMoment B node3902 node3902Labels = _
    exact sound3902 B hB hF
  have h4008 : mixedVector B (Sum.inr 4008) = Sparse.eval nodeValue4008 (mixedVector B) := by
    change mixedMoment B node4008 node4008Labels = _
    exact sound4008 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm392, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3064, h3838, h3846, h3902, h4008, h4091, reducedSource329] using sourceEq392 B hB

theorem rowSound329 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row329 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck329, numericCheck329, reducedZero329 B hB hF, mul_zero]

theorem reducedZero330 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource330 (mixedVector B) = 0 := by
  have h1378 : mixedVector B (Sum.inr 1378) = Sparse.eval nodeValue1378 (mixedVector B) := by
    change mixedMoment B node1378 node1378Labels = _
    exact sound1378 B hB hF
  have h1380 : mixedVector B (Sum.inr 1380) = Sparse.eval nodeValue1380 (mixedVector B) := by
    change mixedMoment B node1380 node1380Labels = _
    exact sound1380 B hB hF
  have h1383 : mixedVector B (Sum.inr 1383) = Sparse.eval nodeValue1383 (mixedVector B) := by
    change mixedMoment B node1383 node1383Labels = _
    exact sound1383 B hB hF
  have h1392 : mixedVector B (Sum.inr 1392) = Sparse.eval nodeValue1392 (mixedVector B) := by
    change mixedMoment B node1392 node1392Labels = _
    exact sound1392 B hB hF
  have h3064 : mixedVector B (Sum.inr 3064) = Sparse.eval nodeValue3064 (mixedVector B) := by
    change mixedMoment B node3064 node3064Labels = _
    exact sound3064 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm393, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1378, h1380, h1383, h1392, h3064, h4091, reducedSource330] using sourceEq393 B hB

theorem rowSound330 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row330 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck330, numericCheck330, reducedZero330 B hB hF, mul_zero]

theorem reducedZero331 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource331 (mixedVector B) = 0 := by
  have h1383 : mixedVector B (Sum.inr 1383) = Sparse.eval nodeValue1383 (mixedVector B) := by
    change mixedMoment B node1383 node1383Labels = _
    exact sound1383 B hB hF
  have h2924 : mixedVector B (Sum.inr 2924) = Sparse.eval nodeValue2924 (mixedVector B) := by
    change mixedMoment B node2924 node2924Labels = _
    exact sound2924 B hB hF
  have h3064 : mixedVector B (Sum.inr 3064) = Sparse.eval nodeValue3064 (mixedVector B) := by
    change mixedMoment B node3064 node3064Labels = _
    exact sound3064 B hB hF
  have h3074 : mixedVector B (Sum.inr 3074) = Sparse.eval nodeValue3074 (mixedVector B) := by
    change mixedMoment B node3074 node3074Labels = _
    exact sound3074 B hB hF
  have h3077 : mixedVector B (Sum.inr 3077) = Sparse.eval nodeValue3077 (mixedVector B) := by
    change mixedMoment B node3077 node3077Labels = _
    exact sound3077 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm394, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1383, h2924, h3064, h3074, h3077, h4091, reducedSource331] using sourceEq394 B hB

theorem rowSound331 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row331 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck331, numericCheck331, reducedZero331 B hB hF, mul_zero]

theorem reducedZero332 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource332 (mixedVector B) = 0 := by
  have h2562 : mixedVector B (Sum.inr 2562) = Sparse.eval nodeValue2562 (mixedVector B) := by
    change mixedMoment B node2562 node2562Labels = _
    exact sound2562 B hB hF
  have h3012 : mixedVector B (Sum.inr 3012) = Sparse.eval nodeValue3012 (mixedVector B) := by
    change mixedMoment B node3012 node3012Labels = _
    exact sound3012 B hB hF
  have h3013 : mixedVector B (Sum.inr 3013) = Sparse.eval nodeValue3013 (mixedVector B) := by
    change mixedMoment B node3013 node3013Labels = _
    exact sound3013 B hB hF
  have h3064 : mixedVector B (Sum.inr 3064) = Sparse.eval nodeValue3064 (mixedVector B) := by
    change mixedMoment B node3064 node3064Labels = _
    exact sound3064 B hB hF
  have h3846 : mixedVector B (Sum.inr 3846) = Sparse.eval nodeValue3846 (mixedVector B) := by
    change mixedMoment B node3846 node3846Labels = _
    exact sound3846 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm395, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2562, h3012, h3013, h3064, h3846, h4091, reducedSource332] using sourceEq395 B hB

theorem rowSound332 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row332 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck332, numericCheck332, reducedZero332 B hB hF, mul_zero]

theorem reducedZero333 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource333 (mixedVector B) = 0 := by
  have h2543 : mixedVector B (Sum.inr 2543) = Sparse.eval nodeValue2543 (mixedVector B) := by
    change mixedMoment B node2543 node2543Labels = _
    exact sound2543 B hB hF
  have h2916 : mixedVector B (Sum.inr 2916) = Sparse.eval nodeValue2916 (mixedVector B) := by
    change mixedMoment B node2916 node2916Labels = _
    exact sound2916 B hB hF
  have h2924 : mixedVector B (Sum.inr 2924) = Sparse.eval nodeValue2924 (mixedVector B) := by
    change mixedMoment B node2924 node2924Labels = _
    exact sound2924 B hB hF
  have h2933 : mixedVector B (Sum.inr 2933) = Sparse.eval nodeValue2933 (mixedVector B) := by
    change mixedMoment B node2933 node2933Labels = _
    exact sound2933 B hB hF
  have h3064 : mixedVector B (Sum.inr 3064) = Sparse.eval nodeValue3064 (mixedVector B) := by
    change mixedMoment B node3064 node3064Labels = _
    exact sound3064 B hB hF
  have h3838 : mixedVector B (Sum.inr 3838) = Sparse.eval nodeValue3838 (mixedVector B) := by
    change mixedMoment B node3838 node3838Labels = _
    exact sound3838 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm396, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2543, h2916, h2924, h2933, h3064, h3838, h4091, reducedSource333] using sourceEq396 B hB

theorem rowSound333 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row333 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck333, numericCheck333, reducedZero333 B hB hF, mul_zero]

theorem reducedZero334 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource334 (mixedVector B) = 0 := by
  have h1380 : mixedVector B (Sum.inr 1380) = Sparse.eval nodeValue1380 (mixedVector B) := by
    change mixedMoment B node1380 node1380Labels = _
    exact sound1380 B hB hF
  have h2916 : mixedVector B (Sum.inr 2916) = Sparse.eval nodeValue2916 (mixedVector B) := by
    change mixedMoment B node2916 node2916Labels = _
    exact sound2916 B hB hF
  have h3012 : mixedVector B (Sum.inr 3012) = Sparse.eval nodeValue3012 (mixedVector B) := by
    change mixedMoment B node3012 node3012Labels = _
    exact sound3012 B hB hF
  have h3064 : mixedVector B (Sum.inr 3064) = Sparse.eval nodeValue3064 (mixedVector B) := by
    change mixedMoment B node3064 node3064Labels = _
    exact sound3064 B hB hF
  have h3066 : mixedVector B (Sum.inr 3066) = Sparse.eval nodeValue3066 (mixedVector B) := by
    change mixedMoment B node3066 node3066Labels = _
    exact sound3066 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm397, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1380, h2916, h3012, h3064, h3066, h4091, reducedSource334] using sourceEq397 B hB

theorem rowSound334 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row334 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck334, numericCheck334, reducedZero334 B hB hF, mul_zero]

theorem reducedZero335 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource335 (mixedVector B) = 0 := by
  have h2693 : mixedVector B (Sum.inr 2693) = Sparse.eval nodeValue2693 (mixedVector B) := by
    change mixedMoment B node2693 node2693Labels = _
    exact sound2693 B hB hF
  have h2694 : mixedVector B (Sum.inr 2694) = Sparse.eval nodeValue2694 (mixedVector B) := by
    change mixedMoment B node2694 node2694Labels = _
    exact sound2694 B hB hF
  have h2697 : mixedVector B (Sum.inr 2697) = Sparse.eval nodeValue2697 (mixedVector B) := by
    change mixedMoment B node2697 node2697Labels = _
    exact sound2697 B hB hF
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  have h3015 : mixedVector B (Sum.inr 3015) = Sparse.eval nodeValue3015 (mixedVector B) := by
    change mixedMoment B node3015 node3015Labels = _
    exact sound3015 B hB hF
  have h3016 : mixedVector B (Sum.inr 3016) = Sparse.eval nodeValue3016 (mixedVector B) := by
    change mixedMoment B node3016 node3016Labels = _
    exact sound3016 B hB hF
  have h3018 : mixedVector B (Sum.inr 3018) = Sparse.eval nodeValue3018 (mixedVector B) := by
    change mixedMoment B node3018 node3018Labels = _
    exact sound3018 B hB hF
  have h3038 : mixedVector B (Sum.inr 3038) = Sparse.eval nodeValue3038 (mixedVector B) := by
    change mixedMoment B node3038 node3038Labels = _
    exact sound3038 B hB hF
  have h3063 : mixedVector B (Sum.inr 3063) = Sparse.eval nodeValue3063 (mixedVector B) := by
    change mixedMoment B node3063 node3063Labels = _
    exact sound3063 B hB hF
  have h3065 : mixedVector B (Sum.inr 3065) = Sparse.eval nodeValue3065 (mixedVector B) := by
    change mixedMoment B node3065 node3065Labels = _
    exact sound3065 B hB hF
  have h3067 : mixedVector B (Sum.inr 3067) = Sparse.eval nodeValue3067 (mixedVector B) := by
    change mixedMoment B node3067 node3067Labels = _
    exact sound3067 B hB hF
  have h3068 : mixedVector B (Sum.inr 3068) = Sparse.eval nodeValue3068 (mixedVector B) := by
    change mixedMoment B node3068 node3068Labels = _
    exact sound3068 B hB hF
  have h3075 : mixedVector B (Sum.inr 3075) = Sparse.eval nodeValue3075 (mixedVector B) := by
    change mixedMoment B node3075 node3075Labels = _
    exact sound3075 B hB hF
  have h3077 : mixedVector B (Sum.inr 3077) = Sparse.eval nodeValue3077 (mixedVector B) := by
    change mixedMoment B node3077 node3077Labels = _
    exact sound3077 B hB hF
  have h3086 : mixedVector B (Sum.inr 3086) = Sparse.eval nodeValue3086 (mixedVector B) := by
    change mixedMoment B node3086 node3086Labels = _
    exact sound3086 B hB hF
  have h3088 : mixedVector B (Sum.inr 3088) = Sparse.eval nodeValue3088 (mixedVector B) := by
    change mixedMoment B node3088 node3088Labels = _
    exact sound3088 B hB hF
  have h3101 : mixedVector B (Sum.inr 3101) = Sparse.eval nodeValue3101 (mixedVector B) := by
    change mixedMoment B node3101 node3101Labels = _
    exact sound3101 B hB hF
  have h3196 : mixedVector B (Sum.inr 3196) = Sparse.eval nodeValue3196 (mixedVector B) := by
    change mixedMoment B node3196 node3196Labels = _
    exact sound3196 B hB hF
  have h3197 : mixedVector B (Sum.inr 3197) = Sparse.eval nodeValue3197 (mixedVector B) := by
    change mixedMoment B node3197 node3197Labels = _
    exact sound3197 B hB hF
  have h3209 : mixedVector B (Sum.inr 3209) = Sparse.eval nodeValue3209 (mixedVector B) := by
    change mixedMoment B node3209 node3209Labels = _
    exact sound3209 B hB hF
  have h3223 : mixedVector B (Sum.inr 3223) = Sparse.eval nodeValue3223 (mixedVector B) := by
    change mixedMoment B node3223 node3223Labels = _
    exact sound3223 B hB hF
  simpa only [sourceForm400, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2693, h2694, h2697, h2722, h3015, h3016, h3018, h3038, h3063, h3065, h3067, h3068, h3075, h3077, h3086, h3088, h3101, h3196, h3197, h3209, h3223, reducedSource335] using sourceEq400 B hB

theorem rowSound335 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row335 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck335, numericCheck335, reducedZero335 B hB hF, mul_zero]

theorem sourceRowsAt320 : MixedData.sourceRows (320 : Fin 2425) =
    MixedData.row320 := by decide +kernel

theorem sourceRowsAt321 : MixedData.sourceRows (321 : Fin 2425) =
    MixedData.row321 := by decide +kernel

theorem sourceRowsAt322 : MixedData.sourceRows (322 : Fin 2425) =
    MixedData.row322 := by decide +kernel

theorem sourceRowsAt323 : MixedData.sourceRows (323 : Fin 2425) =
    MixedData.row323 := by decide +kernel

theorem sourceRowsAt324 : MixedData.sourceRows (324 : Fin 2425) =
    MixedData.row324 := by decide +kernel

theorem sourceRowsAt325 : MixedData.sourceRows (325 : Fin 2425) =
    MixedData.row325 := by decide +kernel

theorem sourceRowsAt326 : MixedData.sourceRows (326 : Fin 2425) =
    MixedData.row326 := by decide +kernel

theorem sourceRowsAt327 : MixedData.sourceRows (327 : Fin 2425) =
    MixedData.row327 := by decide +kernel

theorem sourceRowsAt328 : MixedData.sourceRows (328 : Fin 2425) =
    MixedData.row328 := by decide +kernel

theorem sourceRowsAt329 : MixedData.sourceRows (329 : Fin 2425) =
    MixedData.row329 := by decide +kernel

theorem sourceRowsAt330 : MixedData.sourceRows (330 : Fin 2425) =
    MixedData.row330 := by decide +kernel

theorem sourceRowsAt331 : MixedData.sourceRows (331 : Fin 2425) =
    MixedData.row331 := by decide +kernel

theorem sourceRowsAt332 : MixedData.sourceRows (332 : Fin 2425) =
    MixedData.row332 := by decide +kernel

theorem sourceRowsAt333 : MixedData.sourceRows (333 : Fin 2425) =
    MixedData.row333 := by decide +kernel

theorem sourceRowsAt334 : MixedData.sourceRows (334 : Fin 2425) =
    MixedData.row334 := by decide +kernel

theorem sourceRowsAt335 : MixedData.sourceRows (335 : Fin 2425) =
    MixedData.row335 := by decide +kernel

theorem chunkSound20 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 20) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 320 ∨ k.val = 321 ∨ k.val = 322 ∨ k.val = 323 ∨ k.val = 324 ∨ k.val = 325 ∨ k.val = 326 ∨ k.val = 327 ∨ k.val = 328 ∨ k.val = 329 ∨ k.val = 330 ∨ k.val = 331 ∨ k.val = 332 ∨ k.val = 333 ∨ k.val = 334 ∨ k.val = 335 := by omega
  rcases heq with h320 | h321 | h322 | h323 | h324 | h325 | h326 | h327 | h328 | h329 | h330 | h331 | h332 | h333 | h334 | h335
  · have he : k = (320 : Fin 2425) := Fin.ext h320
    subst k
    rw [sourceRowsAt320]
    exact rowSound320 B hB hF
  · have he : k = (321 : Fin 2425) := Fin.ext h321
    subst k
    rw [sourceRowsAt321]
    exact rowSound321 B hB hF
  · have he : k = (322 : Fin 2425) := Fin.ext h322
    subst k
    rw [sourceRowsAt322]
    exact rowSound322 B hB hF
  · have he : k = (323 : Fin 2425) := Fin.ext h323
    subst k
    rw [sourceRowsAt323]
    exact rowSound323 B hB hF
  · have he : k = (324 : Fin 2425) := Fin.ext h324
    subst k
    rw [sourceRowsAt324]
    exact rowSound324 B hB hF
  · have he : k = (325 : Fin 2425) := Fin.ext h325
    subst k
    rw [sourceRowsAt325]
    exact rowSound325 B hB hF
  · have he : k = (326 : Fin 2425) := Fin.ext h326
    subst k
    rw [sourceRowsAt326]
    exact rowSound326 B hB hF
  · have he : k = (327 : Fin 2425) := Fin.ext h327
    subst k
    rw [sourceRowsAt327]
    exact rowSound327 B hB hF
  · have he : k = (328 : Fin 2425) := Fin.ext h328
    subst k
    rw [sourceRowsAt328]
    exact rowSound328 B hB hF
  · have he : k = (329 : Fin 2425) := Fin.ext h329
    subst k
    rw [sourceRowsAt329]
    exact rowSound329 B hB hF
  · have he : k = (330 : Fin 2425) := Fin.ext h330
    subst k
    rw [sourceRowsAt330]
    exact rowSound330 B hB hF
  · have he : k = (331 : Fin 2425) := Fin.ext h331
    subst k
    rw [sourceRowsAt331]
    exact rowSound331 B hB hF
  · have he : k = (332 : Fin 2425) := Fin.ext h332
    subst k
    rw [sourceRowsAt332]
    exact rowSound332 B hB hF
  · have he : k = (333 : Fin 2425) := Fin.ext h333
    subst k
    rw [sourceRowsAt333]
    exact rowSound333 B hB hF
  · have he : k = (334 : Fin 2425) := Fin.ext h334
    subst k
    rw [sourceRowsAt334]
    exact rowSound334 B hB hF
  · have he : k = (335 : Fin 2425) := Fin.ext h335
    subst k
    rw [sourceRowsAt335]
    exact rowSound335 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
