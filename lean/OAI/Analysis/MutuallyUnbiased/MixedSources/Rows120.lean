import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic120
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound53
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources74

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1920 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1920 (mixedVector B) = 0 := by
  have h2895 : mixedVector B (Sum.inr 2895) = Sparse.eval nodeValue2895 (mixedVector B) := by
    change mixedMoment B node2895 node2895Labels = _
    exact sound2895 B hB hF
  have h2896 : mixedVector B (Sum.inr 2896) = Sparse.eval nodeValue2896 (mixedVector B) := by
    change mixedMoment B node2896 node2896Labels = _
    exact sound2896 B hB hF
  have h2898 : mixedVector B (Sum.inr 2898) = Sparse.eval nodeValue2898 (mixedVector B) := by
    change mixedMoment B node2898 node2898Labels = _
    exact sound2898 B hB hF
  have h2928 : mixedVector B (Sum.inr 2928) = Sparse.eval nodeValue2928 (mixedVector B) := by
    change mixedMoment B node2928 node2928Labels = _
    exact sound2928 B hB hF
  have h3964 : mixedVector B (Sum.inr 3964) = Sparse.eval nodeValue3964 (mixedVector B) := by
    change mixedMoment B node3964 node3964Labels = _
    exact sound3964 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2356, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2895, h2896, h2898, h2928, h3964, h4091, reducedSource1920] using sourceEq2356 B hB

theorem rowSound1920 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1920 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1920, numericCheck1920, reducedZero1920 B hB hF, mul_zero]

theorem reducedZero1921 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1921 (mixedVector B) = 0 := by
  have h1158 : mixedVector B (Sum.inr 1158) = Sparse.eval nodeValue1158 (mixedVector B) := by
    change mixedMoment B node1158 node1158Labels = _
    exact sound1158 B hB hF
  have h2354 : mixedVector B (Sum.inr 2354) = Sparse.eval nodeValue2354 (mixedVector B) := by
    change mixedMoment B node2354 node2354Labels = _
    exact sound2354 B hB hF
  have h2556 : mixedVector B (Sum.inr 2556) = Sparse.eval nodeValue2556 (mixedVector B) := by
    change mixedMoment B node2556 node2556Labels = _
    exact sound2556 B hB hF
  have h2567 : mixedVector B (Sum.inr 2567) = Sparse.eval nodeValue2567 (mixedVector B) := by
    change mixedMoment B node2567 node2567Labels = _
    exact sound2567 B hB hF
  have h2589 : mixedVector B (Sum.inr 2589) = Sparse.eval nodeValue2589 (mixedVector B) := by
    change mixedMoment B node2589 node2589Labels = _
    exact sound2589 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2357, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1158, h2354, h2556, h2567, h2589, h4091, reducedSource1921] using sourceEq2357 B hB

theorem rowSound1921 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1921 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1921, numericCheck1921, reducedZero1921 B hB hF, mul_zero]

theorem reducedZero1922 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1922 (mixedVector B) = 0 := by
  have h2847 : mixedVector B (Sum.inr 2847) = Sparse.eval nodeValue2847 (mixedVector B) := by
    change mixedMoment B node2847 node2847Labels = _
    exact sound2847 B hB hF
  have h2893 : mixedVector B (Sum.inr 2893) = Sparse.eval nodeValue2893 (mixedVector B) := by
    change mixedMoment B node2893 node2893Labels = _
    exact sound2893 B hB hF
  have h2898 : mixedVector B (Sum.inr 2898) = Sparse.eval nodeValue2898 (mixedVector B) := by
    change mixedMoment B node2898 node2898Labels = _
    exact sound2898 B hB hF
  have h2925 : mixedVector B (Sum.inr 2925) = Sparse.eval nodeValue2925 (mixedVector B) := by
    change mixedMoment B node2925 node2925Labels = _
    exact sound2925 B hB hF
  have h3945 : mixedVector B (Sum.inr 3945) = Sparse.eval nodeValue3945 (mixedVector B) := by
    change mixedMoment B node3945 node3945Labels = _
    exact sound3945 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2358, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2847, h2893, h2898, h2925, h3945, h4091, reducedSource1922] using sourceEq2358 B hB

theorem rowSound1922 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1922 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1922, numericCheck1922, reducedZero1922 B hB hF, mul_zero]

theorem reducedZero1923 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1923 (mixedVector B) = 0 := by
  have h2922 : mixedVector B (Sum.inr 2922) = Sparse.eval nodeValue2922 (mixedVector B) := by
    change mixedMoment B node2922 node2922Labels = _
    exact sound2922 B hB hF
  have h3748 : mixedVector B (Sum.inr 3748) = Sparse.eval nodeValue3748 (mixedVector B) := by
    change mixedMoment B node3748 node3748Labels = _
    exact sound3748 B hB hF
  have h3751 : mixedVector B (Sum.inr 3751) = Sparse.eval nodeValue3751 (mixedVector B) := by
    change mixedMoment B node3751 node3751Labels = _
    exact sound3751 B hB hF
  have h3758 : mixedVector B (Sum.inr 3758) = Sparse.eval nodeValue3758 (mixedVector B) := by
    change mixedMoment B node3758 node3758Labels = _
    exact sound3758 B hB hF
  have h3866 : mixedVector B (Sum.inr 3866) = Sparse.eval nodeValue3866 (mixedVector B) := by
    change mixedMoment B node3866 node3866Labels = _
    exact sound3866 B hB hF
  have h3973 : mixedVector B (Sum.inr 3973) = Sparse.eval nodeValue3973 (mixedVector B) := by
    change mixedMoment B node3973 node3973Labels = _
    exact sound3973 B hB hF
  have h4087 : mixedVector B (Sum.inr 4087) = Sparse.eval nodeValue4087 (mixedVector B) := by
    change mixedMoment B node4087 node4087Labels = _
    exact sound4087 B hB hF
  simpa only [sourceForm2359, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2922, h3748, h3751, h3758, h3866, h3973, h4087, reducedSource1923] using sourceEq2359 B hB

theorem rowSound1923 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1923 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1923, numericCheck1923, reducedZero1923 B hB hF, mul_zero]

theorem reducedZero1924 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1924 (mixedVector B) = 0 := by
  have h4327 : mixedVector B (Sum.inr 4327) = Sparse.eval nodeValue4327 (mixedVector B) := by
    change mixedMoment B node4327 node4327Labels = _
    exact sound4327 B hB hF
  have h4328 : mixedVector B (Sum.inr 4328) = Sparse.eval nodeValue4328 (mixedVector B) := by
    change mixedMoment B node4328 node4328Labels = _
    exact sound4328 B hB hF
  have h4332 : mixedVector B (Sum.inr 4332) = Sparse.eval nodeValue4332 (mixedVector B) := by
    change mixedMoment B node4332 node4332Labels = _
    exact sound4332 B hB hF
  have h4345 : mixedVector B (Sum.inr 4345) = Sparse.eval nodeValue4345 (mixedVector B) := by
    change mixedMoment B node4345 node4345Labels = _
    exact sound4345 B hB hF
  have h4439 : mixedVector B (Sum.inr 4439) = Sparse.eval nodeValue4439 (mixedVector B) := by
    change mixedMoment B node4439 node4439Labels = _
    exact sound4439 B hB hF
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
  have h5037 : mixedVector B (Sum.inr 5037) = Sparse.eval nodeValue5037 (mixedVector B) := by
    change mixedMoment B node5037 node5037Labels = _
    exact sound5037 B hB hF
  have h5078 : mixedVector B (Sum.inr 5078) = Sparse.eval nodeValue5078 (mixedVector B) := by
    change mixedMoment B node5078 node5078Labels = _
    exact sound5078 B hB hF
  have h5114 : mixedVector B (Sum.inr 5114) = Sparse.eval nodeValue5114 (mixedVector B) := by
    change mixedMoment B node5114 node5114Labels = _
    exact sound5114 B hB hF
  have h5117 : mixedVector B (Sum.inr 5117) = Sparse.eval nodeValue5117 (mixedVector B) := by
    change mixedMoment B node5117 node5117Labels = _
    exact sound5117 B hB hF
  have h5128 : mixedVector B (Sum.inr 5128) = Sparse.eval nodeValue5128 (mixedVector B) := by
    change mixedMoment B node5128 node5128Labels = _
    exact sound5128 B hB hF
  have h5129 : mixedVector B (Sum.inr 5129) = Sparse.eval nodeValue5129 (mixedVector B) := by
    change mixedMoment B node5129 node5129Labels = _
    exact sound5129 B hB hF
  have h5138 : mixedVector B (Sum.inr 5138) = Sparse.eval nodeValue5138 (mixedVector B) := by
    change mixedMoment B node5138 node5138Labels = _
    exact sound5138 B hB hF
  have h5144 : mixedVector B (Sum.inr 5144) = Sparse.eval nodeValue5144 (mixedVector B) := by
    change mixedMoment B node5144 node5144Labels = _
    exact sound5144 B hB hF
  have h5145 : mixedVector B (Sum.inr 5145) = Sparse.eval nodeValue5145 (mixedVector B) := by
    change mixedMoment B node5145 node5145Labels = _
    exact sound5145 B hB hF
  have h5149 : mixedVector B (Sum.inr 5149) = Sparse.eval nodeValue5149 (mixedVector B) := by
    change mixedMoment B node5149 node5149Labels = _
    exact sound5149 B hB hF
  have h5152 : mixedVector B (Sum.inr 5152) = Sparse.eval nodeValue5152 (mixedVector B) := by
    change mixedMoment B node5152 node5152Labels = _
    exact sound5152 B hB hF
  have h5160 : mixedVector B (Sum.inr 5160) = Sparse.eval nodeValue5160 (mixedVector B) := by
    change mixedMoment B node5160 node5160Labels = _
    exact sound5160 B hB hF
  have h5170 : mixedVector B (Sum.inr 5170) = Sparse.eval nodeValue5170 (mixedVector B) := by
    change mixedMoment B node5170 node5170Labels = _
    exact sound5170 B hB hF
  have h5251 : mixedVector B (Sum.inr 5251) = Sparse.eval nodeValue5251 (mixedVector B) := by
    change mixedMoment B node5251 node5251Labels = _
    exact sound5251 B hB hF
  have h5281 : mixedVector B (Sum.inr 5281) = Sparse.eval nodeValue5281 (mixedVector B) := by
    change mixedMoment B node5281 node5281Labels = _
    exact sound5281 B hB hF
  have h5284 : mixedVector B (Sum.inr 5284) = Sparse.eval nodeValue5284 (mixedVector B) := by
    change mixedMoment B node5284 node5284Labels = _
    exact sound5284 B hB hF
  have h5393 : mixedVector B (Sum.inr 5393) = Sparse.eval nodeValue5393 (mixedVector B) := by
    change mixedMoment B node5393 node5393Labels = _
    exact sound5393 B hB hF
  have h5396 : mixedVector B (Sum.inr 5396) = Sparse.eval nodeValue5396 (mixedVector B) := by
    change mixedMoment B node5396 node5396Labels = _
    exact sound5396 B hB hF
  have h5410 : mixedVector B (Sum.inr 5410) = Sparse.eval nodeValue5410 (mixedVector B) := by
    change mixedMoment B node5410 node5410Labels = _
    exact sound5410 B hB hF
  have h5424 : mixedVector B (Sum.inr 5424) = Sparse.eval nodeValue5424 (mixedVector B) := by
    change mixedMoment B node5424 node5424Labels = _
    exact sound5424 B hB hF
  have h5478 : mixedVector B (Sum.inr 5478) = Sparse.eval nodeValue5478 (mixedVector B) := by
    change mixedMoment B node5478 node5478Labels = _
    exact sound5478 B hB hF
  simpa only [sourceForm2365, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4327, h4328, h4332, h4345, h4439, h4930, h4931, h4933, h4942, h5037, h5078, h5114, h5117, h5128, h5129, h5138, h5144, h5145, h5149, h5152, h5160, h5170, h5251, h5281, h5284, h5393, h5396, h5410, h5424, h5478, reducedSource1924] using sourceEq2365 B hB

theorem rowSound1924 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1924 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1924, numericCheck1924, reducedZero1924 B hB hF, mul_zero]

theorem reducedZero1925 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1925 (mixedVector B) = 0 := by
  have h905 : mixedVector B (Sum.inr 905) = Sparse.eval nodeValue905 (mixedVector B) := by
    change mixedMoment B node905 node905Labels = _
    exact sound905 B hB hF
  have h906 : mixedVector B (Sum.inr 906) = Sparse.eval nodeValue906 (mixedVector B) := by
    change mixedMoment B node906 node906Labels = _
    exact sound906 B hB hF
  have h910 : mixedVector B (Sum.inr 910) = Sparse.eval nodeValue910 (mixedVector B) := by
    change mixedMoment B node910 node910Labels = _
    exact sound910 B hB hF
  have h923 : mixedVector B (Sum.inr 923) = Sparse.eval nodeValue923 (mixedVector B) := by
    change mixedMoment B node923 node923Labels = _
    exact sound923 B hB hF
  have h1021 : mixedVector B (Sum.inr 1021) = Sparse.eval nodeValue1021 (mixedVector B) := by
    change mixedMoment B node1021 node1021Labels = _
    exact sound1021 B hB hF
  have h2320 : mixedVector B (Sum.inr 2320) = Sparse.eval nodeValue2320 (mixedVector B) := by
    change mixedMoment B node2320 node2320Labels = _
    exact sound2320 B hB hF
  have h2321 : mixedVector B (Sum.inr 2321) = Sparse.eval nodeValue2321 (mixedVector B) := by
    change mixedMoment B node2321 node2321Labels = _
    exact sound2321 B hB hF
  have h2324 : mixedVector B (Sum.inr 2324) = Sparse.eval nodeValue2324 (mixedVector B) := by
    change mixedMoment B node2324 node2324Labels = _
    exact sound2324 B hB hF
  have h2333 : mixedVector B (Sum.inr 2333) = Sparse.eval nodeValue2333 (mixedVector B) := by
    change mixedMoment B node2333 node2333Labels = _
    exact sound2333 B hB hF
  have h2526 : mixedVector B (Sum.inr 2526) = Sparse.eval nodeValue2526 (mixedVector B) := by
    change mixedMoment B node2526 node2526Labels = _
    exact sound2526 B hB hF
  have h2527 : mixedVector B (Sum.inr 2527) = Sparse.eval nodeValue2527 (mixedVector B) := by
    change mixedMoment B node2527 node2527Labels = _
    exact sound2527 B hB hF
  have h2530 : mixedVector B (Sum.inr 2530) = Sparse.eval nodeValue2530 (mixedVector B) := by
    change mixedMoment B node2530 node2530Labels = _
    exact sound2530 B hB hF
  have h2543 : mixedVector B (Sum.inr 2543) = Sparse.eval nodeValue2543 (mixedVector B) := by
    change mixedMoment B node2543 node2543Labels = _
    exact sound2543 B hB hF
  have h2545 : mixedVector B (Sum.inr 2545) = Sparse.eval nodeValue2545 (mixedVector B) := by
    change mixedMoment B node2545 node2545Labels = _
    exact sound2545 B hB hF
  have h2557 : mixedVector B (Sum.inr 2557) = Sparse.eval nodeValue2557 (mixedVector B) := by
    change mixedMoment B node2557 node2557Labels = _
    exact sound2557 B hB hF
  have h2566 : mixedVector B (Sum.inr 2566) = Sparse.eval nodeValue2566 (mixedVector B) := by
    change mixedMoment B node2566 node2566Labels = _
    exact sound2566 B hB hF
  have h2567 : mixedVector B (Sum.inr 2567) = Sparse.eval nodeValue2567 (mixedVector B) := by
    change mixedMoment B node2567 node2567Labels = _
    exact sound2567 B hB hF
  have h2570 : mixedVector B (Sum.inr 2570) = Sparse.eval nodeValue2570 (mixedVector B) := by
    change mixedMoment B node2570 node2570Labels = _
    exact sound2570 B hB hF
  have h2572 : mixedVector B (Sum.inr 2572) = Sparse.eval nodeValue2572 (mixedVector B) := by
    change mixedMoment B node2572 node2572Labels = _
    exact sound2572 B hB hF
  have h2576 : mixedVector B (Sum.inr 2576) = Sparse.eval nodeValue2576 (mixedVector B) := by
    change mixedMoment B node2576 node2576Labels = _
    exact sound2576 B hB hF
  have h2587 : mixedVector B (Sum.inr 2587) = Sparse.eval nodeValue2587 (mixedVector B) := by
    change mixedMoment B node2587 node2587Labels = _
    exact sound2587 B hB hF
  have h2596 : mixedVector B (Sum.inr 2596) = Sparse.eval nodeValue2596 (mixedVector B) := by
    change mixedMoment B node2596 node2596Labels = _
    exact sound2596 B hB hF
  have h2710 : mixedVector B (Sum.inr 2710) = Sparse.eval nodeValue2710 (mixedVector B) := by
    change mixedMoment B node2710 node2710Labels = _
    exact sound2710 B hB hF
  have h2750 : mixedVector B (Sum.inr 2750) = Sparse.eval nodeValue2750 (mixedVector B) := by
    change mixedMoment B node2750 node2750Labels = _
    exact sound2750 B hB hF
  have h2753 : mixedVector B (Sum.inr 2753) = Sparse.eval nodeValue2753 (mixedVector B) := by
    change mixedMoment B node2753 node2753Labels = _
    exact sound2753 B hB hF
  have h3925 : mixedVector B (Sum.inr 3925) = Sparse.eval nodeValue3925 (mixedVector B) := by
    change mixedMoment B node3925 node3925Labels = _
    exact sound3925 B hB hF
  have h3988 : mixedVector B (Sum.inr 3988) = Sparse.eval nodeValue3988 (mixedVector B) := by
    change mixedMoment B node3988 node3988Labels = _
    exact sound3988 B hB hF
  have h3990 : mixedVector B (Sum.inr 3990) = Sparse.eval nodeValue3990 (mixedVector B) := by
    change mixedMoment B node3990 node3990Labels = _
    exact sound3990 B hB hF
  have h3994 : mixedVector B (Sum.inr 3994) = Sparse.eval nodeValue3994 (mixedVector B) := by
    change mixedMoment B node3994 node3994Labels = _
    exact sound3994 B hB hF
  have h3996 : mixedVector B (Sum.inr 3996) = Sparse.eval nodeValue3996 (mixedVector B) := by
    change mixedMoment B node3996 node3996Labels = _
    exact sound3996 B hB hF
  simpa only [sourceForm2366, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h905, h906, h910, h923, h1021, h2320, h2321, h2324, h2333, h2526, h2527, h2530, h2543, h2545, h2557, h2566, h2567, h2570, h2572, h2576, h2587, h2596, h2710, h2750, h2753, h3925, h3988, h3990, h3994, h3996, reducedSource1925] using sourceEq2366 B hB

theorem rowSound1925 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1925 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1925, numericCheck1925, reducedZero1925 B hB hF, mul_zero]

theorem reducedZero1926 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1926 (mixedVector B) = 0 := by
  have h1667 : mixedVector B (Sum.inr 1667) = Sparse.eval nodeValue1667 (mixedVector B) := by
    change mixedMoment B node1667 node1667Labels = _
    exact sound1667 B hB hF
  have h1668 : mixedVector B (Sum.inr 1668) = Sparse.eval nodeValue1668 (mixedVector B) := by
    change mixedMoment B node1668 node1668Labels = _
    exact sound1668 B hB hF
  have h1670 : mixedVector B (Sum.inr 1670) = Sparse.eval nodeValue1670 (mixedVector B) := by
    change mixedMoment B node1670 node1670Labels = _
    exact sound1670 B hB hF
  have h1678 : mixedVector B (Sum.inr 1678) = Sparse.eval nodeValue1678 (mixedVector B) := by
    change mixedMoment B node1678 node1678Labels = _
    exact sound1678 B hB hF
  have h1713 : mixedVector B (Sum.inr 1713) = Sparse.eval nodeValue1713 (mixedVector B) := by
    change mixedMoment B node1713 node1713Labels = _
    exact sound1713 B hB hF
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
  have h3455 : mixedVector B (Sum.inr 3455) = Sparse.eval nodeValue3455 (mixedVector B) := by
    change mixedMoment B node3455 node3455Labels = _
    exact sound3455 B hB hF
  have h3481 : mixedVector B (Sum.inr 3481) = Sparse.eval nodeValue3481 (mixedVector B) := by
    change mixedMoment B node3481 node3481Labels = _
    exact sound3481 B hB hF
  have h3516 : mixedVector B (Sum.inr 3516) = Sparse.eval nodeValue3516 (mixedVector B) := by
    change mixedMoment B node3516 node3516Labels = _
    exact sound3516 B hB hF
  have h3517 : mixedVector B (Sum.inr 3517) = Sparse.eval nodeValue3517 (mixedVector B) := by
    change mixedMoment B node3517 node3517Labels = _
    exact sound3517 B hB hF
  have h3519 : mixedVector B (Sum.inr 3519) = Sparse.eval nodeValue3519 (mixedVector B) := by
    change mixedMoment B node3519 node3519Labels = _
    exact sound3519 B hB hF
  have h3539 : mixedVector B (Sum.inr 3539) = Sparse.eval nodeValue3539 (mixedVector B) := by
    change mixedMoment B node3539 node3539Labels = _
    exact sound3539 B hB hF
  have h3557 : mixedVector B (Sum.inr 3557) = Sparse.eval nodeValue3557 (mixedVector B) := by
    change mixedMoment B node3557 node3557Labels = _
    exact sound3557 B hB hF
  have h3558 : mixedVector B (Sum.inr 3558) = Sparse.eval nodeValue3558 (mixedVector B) := by
    change mixedMoment B node3558 node3558Labels = _
    exact sound3558 B hB hF
  have h3562 : mixedVector B (Sum.inr 3562) = Sparse.eval nodeValue3562 (mixedVector B) := by
    change mixedMoment B node3562 node3562Labels = _
    exact sound3562 B hB hF
  have h3571 : mixedVector B (Sum.inr 3571) = Sparse.eval nodeValue3571 (mixedVector B) := by
    change mixedMoment B node3571 node3571Labels = _
    exact sound3571 B hB hF
  have h3597 : mixedVector B (Sum.inr 3597) = Sparse.eval nodeValue3597 (mixedVector B) := by
    change mixedMoment B node3597 node3597Labels = _
    exact sound3597 B hB hF
  have h3599 : mixedVector B (Sum.inr 3599) = Sparse.eval nodeValue3599 (mixedVector B) := by
    change mixedMoment B node3599 node3599Labels = _
    exact sound3599 B hB hF
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
  have h3797 : mixedVector B (Sum.inr 3797) = Sparse.eval nodeValue3797 (mixedVector B) := by
    change mixedMoment B node3797 node3797Labels = _
    exact sound3797 B hB hF
  have h3798 : mixedVector B (Sum.inr 3798) = Sparse.eval nodeValue3798 (mixedVector B) := by
    change mixedMoment B node3798 node3798Labels = _
    exact sound3798 B hB hF
  have h3816 : mixedVector B (Sum.inr 3816) = Sparse.eval nodeValue3816 (mixedVector B) := by
    change mixedMoment B node3816 node3816Labels = _
    exact sound3816 B hB hF
  have h3843 : mixedVector B (Sum.inr 3843) = Sparse.eval nodeValue3843 (mixedVector B) := by
    change mixedMoment B node3843 node3843Labels = _
    exact sound3843 B hB hF
  have h3974 : mixedVector B (Sum.inr 3974) = Sparse.eval nodeValue3974 (mixedVector B) := by
    change mixedMoment B node3974 node3974Labels = _
    exact sound3974 B hB hF
  simpa only [sourceForm2367, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1667, h1668, h1670, h1678, h1713, h3406, h3407, h3408, h3414, h3455, h3481, h3516, h3517, h3519, h3539, h3557, h3558, h3562, h3571, h3597, h3599, h3605, h3606, h3612, h3625, h3797, h3798, h3816, h3843, h3974, reducedSource1926] using sourceEq2367 B hB

theorem rowSound1926 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1926 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1926, numericCheck1926, reducedZero1926 B hB hF, mul_zero]

theorem reducedZero1927 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1927 (mixedVector B) = 0 := by
  have h2422 : mixedVector B (Sum.inr 2422) = Sparse.eval nodeValue2422 (mixedVector B) := by
    change mixedMoment B node2422 node2422Labels = _
    exact sound2422 B hB hF
  have h2822 : mixedVector B (Sum.inr 2822) = Sparse.eval nodeValue2822 (mixedVector B) := by
    change mixedMoment B node2822 node2822Labels = _
    exact sound2822 B hB hF
  have h2824 : mixedVector B (Sum.inr 2824) = Sparse.eval nodeValue2824 (mixedVector B) := by
    change mixedMoment B node2824 node2824Labels = _
    exact sound2824 B hB hF
  have h2826 : mixedVector B (Sum.inr 2826) = Sparse.eval nodeValue2826 (mixedVector B) := by
    change mixedMoment B node2826 node2826Labels = _
    exact sound2826 B hB hF
  have h2924 : mixedVector B (Sum.inr 2924) = Sparse.eval nodeValue2924 (mixedVector B) := by
    change mixedMoment B node2924 node2924Labels = _
    exact sound2924 B hB hF
  have h3779 : mixedVector B (Sum.inr 3779) = Sparse.eval nodeValue3779 (mixedVector B) := by
    change mixedMoment B node3779 node3779Labels = _
    exact sound3779 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2368, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2422, h2822, h2824, h2826, h2924, h3779, h4091, reducedSource1927] using sourceEq2368 B hB

theorem rowSound1927 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1927 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1927, numericCheck1927, reducedZero1927 B hB hF, mul_zero]

theorem reducedZero1928 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1928 (mixedVector B) = 0 := by
  have h1169 : mixedVector B (Sum.inr 1169) = Sparse.eval nodeValue1169 (mixedVector B) := by
    change mixedMoment B node1169 node1169Labels = _
    exact sound1169 B hB hF
  have h2361 : mixedVector B (Sum.inr 2361) = Sparse.eval nodeValue2361 (mixedVector B) := by
    change mixedMoment B node2361 node2361Labels = _
    exact sound2361 B hB hF
  have h2573 : mixedVector B (Sum.inr 2573) = Sparse.eval nodeValue2573 (mixedVector B) := by
    change mixedMoment B node2573 node2573Labels = _
    exact sound2573 B hB hF
  have h2589 : mixedVector B (Sum.inr 2589) = Sparse.eval nodeValue2589 (mixedVector B) := by
    change mixedMoment B node2589 node2589Labels = _
    exact sound2589 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2370, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1169, h2361, h2573, h2589, h4091, reducedSource1928] using sourceEq2370 B hB

theorem rowSound1928 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1928 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1928, numericCheck1928, reducedZero1928 B hB hF, mul_zero]

theorem reducedZero1929 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1929 (mixedVector B) = 0 := by
  have h1964 : mixedVector B (Sum.inr 1964) = Sparse.eval nodeValue1964 (mixedVector B) := by
    change mixedMoment B node1964 node1964Labels = _
    exact sound1964 B hB hF
  have h2892 : mixedVector B (Sum.inr 2892) = Sparse.eval nodeValue2892 (mixedVector B) := by
    change mixedMoment B node2892 node2892Labels = _
    exact sound2892 B hB hF
  have h2923 : mixedVector B (Sum.inr 2923) = Sparse.eval nodeValue2923 (mixedVector B) := by
    change mixedMoment B node2923 node2923Labels = _
    exact sound2923 B hB hF
  have h3496 : mixedVector B (Sum.inr 3496) = Sparse.eval nodeValue3496 (mixedVector B) := by
    change mixedMoment B node3496 node3496Labels = _
    exact sound3496 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm2371, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1964, h2892, h2923, h3496, h4083, reducedSource1929] using sourceEq2371 B hB

theorem rowSound1929 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1929 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1929, numericCheck1929, reducedZero1929 B hB hF, mul_zero]

theorem reducedZero1930 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1930 (mixedVector B) = 0 := by
  have h2800 : mixedVector B (Sum.inr 2800) = Sparse.eval nodeValue2800 (mixedVector B) := by
    change mixedMoment B node2800 node2800Labels = _
    exact sound2800 B hB hF
  have h2801 : mixedVector B (Sum.inr 2801) = Sparse.eval nodeValue2801 (mixedVector B) := by
    change mixedMoment B node2801 node2801Labels = _
    exact sound2801 B hB hF
  have h2814 : mixedVector B (Sum.inr 2814) = Sparse.eval nodeValue2814 (mixedVector B) := by
    change mixedMoment B node2814 node2814Labels = _
    exact sound2814 B hB hF
  have h2864 : mixedVector B (Sum.inr 2864) = Sparse.eval nodeValue2864 (mixedVector B) := by
    change mixedMoment B node2864 node2864Labels = _
    exact sound2864 B hB hF
  have h3692 : mixedVector B (Sum.inr 3692) = Sparse.eval nodeValue3692 (mixedVector B) := by
    change mixedMoment B node3692 node3692Labels = _
    exact sound3692 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2374, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2800, h2801, h2814, h2864, h3692, h4091, reducedSource1930] using sourceEq2374 B hB

theorem rowSound1930 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1930 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1930, numericCheck1930, reducedZero1930 B hB hF, mul_zero]

theorem reducedZero1931 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1931 (mixedVector B) = 0 := by
  have h2797 : mixedVector B (Sum.inr 2797) = Sparse.eval nodeValue2797 (mixedVector B) := by
    change mixedMoment B node2797 node2797Labels = _
    exact sound2797 B hB hF
  have h2799 : mixedVector B (Sum.inr 2799) = Sparse.eval nodeValue2799 (mixedVector B) := by
    change mixedMoment B node2799 node2799Labels = _
    exact sound2799 B hB hF
  have h2801 : mixedVector B (Sum.inr 2801) = Sparse.eval nodeValue2801 (mixedVector B) := by
    change mixedMoment B node2801 node2801Labels = _
    exact sound2801 B hB hF
  have h2809 : mixedVector B (Sum.inr 2809) = Sparse.eval nodeValue2809 (mixedVector B) := by
    change mixedMoment B node2809 node2809Labels = _
    exact sound2809 B hB hF
  have h2862 : mixedVector B (Sum.inr 2862) = Sparse.eval nodeValue2862 (mixedVector B) := by
    change mixedMoment B node2862 node2862Labels = _
    exact sound2862 B hB hF
  have h3690 : mixedVector B (Sum.inr 3690) = Sparse.eval nodeValue3690 (mixedVector B) := by
    change mixedMoment B node3690 node3690Labels = _
    exact sound3690 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2375, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2797, h2799, h2801, h2809, h2862, h3690, h4091, reducedSource1931] using sourceEq2375 B hB

theorem rowSound1931 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1931 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1931, numericCheck1931, reducedZero1931 B hB hF, mul_zero]

theorem reducedZero1932 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1932 (mixedVector B) = 0 := by
  have h2524 : mixedVector B (Sum.inr 2524) = Sparse.eval nodeValue2524 (mixedVector B) := by
    change mixedMoment B node2524 node2524Labels = _
    exact sound2524 B hB hF
  have h2798 : mixedVector B (Sum.inr 2798) = Sparse.eval nodeValue2798 (mixedVector B) := by
    change mixedMoment B node2798 node2798Labels = _
    exact sound2798 B hB hF
  have h2807 : mixedVector B (Sum.inr 2807) = Sparse.eval nodeValue2807 (mixedVector B) := by
    change mixedMoment B node2807 node2807Labels = _
    exact sound2807 B hB hF
  have h2861 : mixedVector B (Sum.inr 2861) = Sparse.eval nodeValue2861 (mixedVector B) := by
    change mixedMoment B node2861 node2861Labels = _
    exact sound2861 B hB hF
  have h3689 : mixedVector B (Sum.inr 3689) = Sparse.eval nodeValue3689 (mixedVector B) := by
    change mixedMoment B node3689 node3689Labels = _
    exact sound3689 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2376, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2524, h2798, h2807, h2861, h3689, h4092, reducedSource1932] using sourceEq2376 B hB

theorem rowSound1932 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1932 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1932, numericCheck1932, reducedZero1932 B hB hF, mul_zero]

theorem reducedZero1933 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1933 (mixedVector B) = 0 := by
  have h2031 : mixedVector B (Sum.inr 2031) = Sparse.eval nodeValue2031 (mixedVector B) := by
    change mixedMoment B node2031 node2031Labels = _
    exact sound2031 B hB hF
  have h2036 : mixedVector B (Sum.inr 2036) = Sparse.eval nodeValue2036 (mixedVector B) := by
    change mixedMoment B node2036 node2036Labels = _
    exact sound2036 B hB hF
  have h2046 : mixedVector B (Sum.inr 2046) = Sparse.eval nodeValue2046 (mixedVector B) := by
    change mixedMoment B node2046 node2046Labels = _
    exact sound2046 B hB hF
  have h2275 : mixedVector B (Sum.inr 2275) = Sparse.eval nodeValue2275 (mixedVector B) := by
    change mixedMoment B node2275 node2275Labels = _
    exact sound2275 B hB hF
  have h3537 : mixedVector B (Sum.inr 3537) = Sparse.eval nodeValue3537 (mixedVector B) := by
    change mixedMoment B node3537 node3537Labels = _
    exact sound3537 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm2377, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2031, h2036, h2046, h2275, h3537, h4080, reducedSource1933] using sourceEq2377 B hB

theorem rowSound1933 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1933 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1933, numericCheck1933, reducedZero1933 B hB hF, mul_zero]

theorem reducedZero1934 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1934 (mixedVector B) = 0 := by
  have h2810 : mixedVector B (Sum.inr 2810) = Sparse.eval nodeValue2810 (mixedVector B) := by
    change mixedMoment B node2810 node2810Labels = _
    exact sound2810 B hB hF
  have h2816 : mixedVector B (Sum.inr 2816) = Sparse.eval nodeValue2816 (mixedVector B) := by
    change mixedMoment B node2816 node2816Labels = _
    exact sound2816 B hB hF
  have h2817 : mixedVector B (Sum.inr 2817) = Sparse.eval nodeValue2817 (mixedVector B) := by
    change mixedMoment B node2817 node2817Labels = _
    exact sound2817 B hB hF
  have h2819 : mixedVector B (Sum.inr 2819) = Sparse.eval nodeValue2819 (mixedVector B) := by
    change mixedMoment B node2819 node2819Labels = _
    exact sound2819 B hB hF
  have h2885 : mixedVector B (Sum.inr 2885) = Sparse.eval nodeValue2885 (mixedVector B) := by
    change mixedMoment B node2885 node2885Labels = _
    exact sound2885 B hB hF
  have h3706 : mixedVector B (Sum.inr 3706) = Sparse.eval nodeValue3706 (mixedVector B) := by
    change mixedMoment B node3706 node3706Labels = _
    exact sound3706 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2378, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2810, h2816, h2817, h2819, h2885, h3706, h4092, reducedSource1934] using sourceEq2378 B hB

theorem rowSound1934 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1934 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1934, numericCheck1934, reducedZero1934 B hB hF, mul_zero]

theorem reducedZero1935 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1935 (mixedVector B) = 0 := by
  have h4364 : mixedVector B (Sum.inr 4364) = Sparse.eval nodeValue4364 (mixedVector B) := by
    change mixedMoment B node4364 node4364Labels = _
    exact sound4364 B hB hF
  have h4365 : mixedVector B (Sum.inr 4365) = Sparse.eval nodeValue4365 (mixedVector B) := by
    change mixedMoment B node4365 node4365Labels = _
    exact sound4365 B hB hF
  have h4369 : mixedVector B (Sum.inr 4369) = Sparse.eval nodeValue4369 (mixedVector B) := by
    change mixedMoment B node4369 node4369Labels = _
    exact sound4369 B hB hF
  have h4474 : mixedVector B (Sum.inr 4474) = Sparse.eval nodeValue4474 (mixedVector B) := by
    change mixedMoment B node4474 node4474Labels = _
    exact sound4474 B hB hF
  have h4968 : mixedVector B (Sum.inr 4968) = Sparse.eval nodeValue4968 (mixedVector B) := by
    change mixedMoment B node4968 node4968Labels = _
    exact sound4968 B hB hF
  have h4970 : mixedVector B (Sum.inr 4970) = Sparse.eval nodeValue4970 (mixedVector B) := by
    change mixedMoment B node4970 node4970Labels = _
    exact sound4970 B hB hF
  have h4974 : mixedVector B (Sum.inr 4974) = Sparse.eval nodeValue4974 (mixedVector B) := by
    change mixedMoment B node4974 node4974Labels = _
    exact sound4974 B hB hF
  have h5041 : mixedVector B (Sum.inr 5041) = Sparse.eval nodeValue5041 (mixedVector B) := by
    change mixedMoment B node5041 node5041Labels = _
    exact sound5041 B hB hF
  have h5043 : mixedVector B (Sum.inr 5043) = Sparse.eval nodeValue5043 (mixedVector B) := by
    change mixedMoment B node5043 node5043Labels = _
    exact sound5043 B hB hF
  have h5085 : mixedVector B (Sum.inr 5085) = Sparse.eval nodeValue5085 (mixedVector B) := by
    change mixedMoment B node5085 node5085Labels = _
    exact sound5085 B hB hF
  have h5147 : mixedVector B (Sum.inr 5147) = Sparse.eval nodeValue5147 (mixedVector B) := by
    change mixedMoment B node5147 node5147Labels = _
    exact sound5147 B hB hF
  have h5185 : mixedVector B (Sum.inr 5185) = Sparse.eval nodeValue5185 (mixedVector B) := by
    change mixedMoment B node5185 node5185Labels = _
    exact sound5185 B hB hF
  have h5189 : mixedVector B (Sum.inr 5189) = Sparse.eval nodeValue5189 (mixedVector B) := by
    change mixedMoment B node5189 node5189Labels = _
    exact sound5189 B hB hF
  have h5202 : mixedVector B (Sum.inr 5202) = Sparse.eval nodeValue5202 (mixedVector B) := by
    change mixedMoment B node5202 node5202Labels = _
    exact sound5202 B hB hF
  have h5203 : mixedVector B (Sum.inr 5203) = Sparse.eval nodeValue5203 (mixedVector B) := by
    change mixedMoment B node5203 node5203Labels = _
    exact sound5203 B hB hF
  have h5266 : mixedVector B (Sum.inr 5266) = Sparse.eval nodeValue5266 (mixedVector B) := by
    change mixedMoment B node5266 node5266Labels = _
    exact sound5266 B hB hF
  have h5301 : mixedVector B (Sum.inr 5301) = Sparse.eval nodeValue5301 (mixedVector B) := by
    change mixedMoment B node5301 node5301Labels = _
    exact sound5301 B hB hF
  have h5369 : mixedVector B (Sum.inr 5369) = Sparse.eval nodeValue5369 (mixedVector B) := by
    change mixedMoment B node5369 node5369Labels = _
    exact sound5369 B hB hF
  have h5469 : mixedVector B (Sum.inr 5469) = Sparse.eval nodeValue5469 (mixedVector B) := by
    change mixedMoment B node5469 node5469Labels = _
    exact sound5469 B hB hF
  have h5473 : mixedVector B (Sum.inr 5473) = Sparse.eval nodeValue5473 (mixedVector B) := by
    change mixedMoment B node5473 node5473Labels = _
    exact sound5473 B hB hF
  have h5474 : mixedVector B (Sum.inr 5474) = Sparse.eval nodeValue5474 (mixedVector B) := by
    change mixedMoment B node5474 node5474Labels = _
    exact sound5474 B hB hF
  simpa only [sourceForm2382, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4364, h4365, h4369, h4474, h4968, h4970, h4974, h5041, h5043, h5085, h5147, h5185, h5189, h5202, h5203, h5266, h5301, h5369, h5469, h5473, h5474, reducedSource1935] using sourceEq2382 B hB

theorem rowSound1935 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1935 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1935, numericCheck1935, reducedZero1935 B hB hF, mul_zero]

theorem sourceRowsAt1920 : MixedData.sourceRows (1920 : Fin 2425) =
    MixedData.row1920 := by decide +kernel

theorem sourceRowsAt1921 : MixedData.sourceRows (1921 : Fin 2425) =
    MixedData.row1921 := by decide +kernel

theorem sourceRowsAt1922 : MixedData.sourceRows (1922 : Fin 2425) =
    MixedData.row1922 := by decide +kernel

theorem sourceRowsAt1923 : MixedData.sourceRows (1923 : Fin 2425) =
    MixedData.row1923 := by decide +kernel

theorem sourceRowsAt1924 : MixedData.sourceRows (1924 : Fin 2425) =
    MixedData.row1924 := by decide +kernel

theorem sourceRowsAt1925 : MixedData.sourceRows (1925 : Fin 2425) =
    MixedData.row1925 := by decide +kernel

theorem sourceRowsAt1926 : MixedData.sourceRows (1926 : Fin 2425) =
    MixedData.row1926 := by decide +kernel

theorem sourceRowsAt1927 : MixedData.sourceRows (1927 : Fin 2425) =
    MixedData.row1927 := by decide +kernel

theorem sourceRowsAt1928 : MixedData.sourceRows (1928 : Fin 2425) =
    MixedData.row1928 := by decide +kernel

theorem sourceRowsAt1929 : MixedData.sourceRows (1929 : Fin 2425) =
    MixedData.row1929 := by decide +kernel

theorem sourceRowsAt1930 : MixedData.sourceRows (1930 : Fin 2425) =
    MixedData.row1930 := by decide +kernel

theorem sourceRowsAt1931 : MixedData.sourceRows (1931 : Fin 2425) =
    MixedData.row1931 := by decide +kernel

theorem sourceRowsAt1932 : MixedData.sourceRows (1932 : Fin 2425) =
    MixedData.row1932 := by decide +kernel

theorem sourceRowsAt1933 : MixedData.sourceRows (1933 : Fin 2425) =
    MixedData.row1933 := by decide +kernel

theorem sourceRowsAt1934 : MixedData.sourceRows (1934 : Fin 2425) =
    MixedData.row1934 := by decide +kernel

theorem sourceRowsAt1935 : MixedData.sourceRows (1935 : Fin 2425) =
    MixedData.row1935 := by decide +kernel

theorem chunkSound120 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 120) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1920 ∨ k.val = 1921 ∨ k.val = 1922 ∨ k.val = 1923 ∨ k.val = 1924 ∨ k.val = 1925 ∨ k.val = 1926 ∨ k.val = 1927 ∨ k.val = 1928 ∨ k.val = 1929 ∨ k.val = 1930 ∨ k.val = 1931 ∨ k.val = 1932 ∨ k.val = 1933 ∨ k.val = 1934 ∨ k.val = 1935 := by omega
  rcases heq with h1920 | h1921 | h1922 | h1923 | h1924 | h1925 | h1926 | h1927 | h1928 | h1929 | h1930 | h1931 | h1932 | h1933 | h1934 | h1935
  · have he : k = (1920 : Fin 2425) := Fin.ext h1920
    subst k
    rw [sourceRowsAt1920]
    exact rowSound1920 B hB hF
  · have he : k = (1921 : Fin 2425) := Fin.ext h1921
    subst k
    rw [sourceRowsAt1921]
    exact rowSound1921 B hB hF
  · have he : k = (1922 : Fin 2425) := Fin.ext h1922
    subst k
    rw [sourceRowsAt1922]
    exact rowSound1922 B hB hF
  · have he : k = (1923 : Fin 2425) := Fin.ext h1923
    subst k
    rw [sourceRowsAt1923]
    exact rowSound1923 B hB hF
  · have he : k = (1924 : Fin 2425) := Fin.ext h1924
    subst k
    rw [sourceRowsAt1924]
    exact rowSound1924 B hB hF
  · have he : k = (1925 : Fin 2425) := Fin.ext h1925
    subst k
    rw [sourceRowsAt1925]
    exact rowSound1925 B hB hF
  · have he : k = (1926 : Fin 2425) := Fin.ext h1926
    subst k
    rw [sourceRowsAt1926]
    exact rowSound1926 B hB hF
  · have he : k = (1927 : Fin 2425) := Fin.ext h1927
    subst k
    rw [sourceRowsAt1927]
    exact rowSound1927 B hB hF
  · have he : k = (1928 : Fin 2425) := Fin.ext h1928
    subst k
    rw [sourceRowsAt1928]
    exact rowSound1928 B hB hF
  · have he : k = (1929 : Fin 2425) := Fin.ext h1929
    subst k
    rw [sourceRowsAt1929]
    exact rowSound1929 B hB hF
  · have he : k = (1930 : Fin 2425) := Fin.ext h1930
    subst k
    rw [sourceRowsAt1930]
    exact rowSound1930 B hB hF
  · have he : k = (1931 : Fin 2425) := Fin.ext h1931
    subst k
    rw [sourceRowsAt1931]
    exact rowSound1931 B hB hF
  · have he : k = (1932 : Fin 2425) := Fin.ext h1932
    subst k
    rw [sourceRowsAt1932]
    exact rowSound1932 B hB hF
  · have he : k = (1933 : Fin 2425) := Fin.ext h1933
    subst k
    rw [sourceRowsAt1933]
    exact rowSound1933 B hB hF
  · have he : k = (1934 : Fin 2425) := Fin.ext h1934
    subst k
    rw [sourceRowsAt1934]
    exact rowSound1934 B hB hF
  · have he : k = (1935 : Fin 2425) := Fin.ext h1935
    subst k
    rw [sourceRowsAt1935]
    exact rowSound1935 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
