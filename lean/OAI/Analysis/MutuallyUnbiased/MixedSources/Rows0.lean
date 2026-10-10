import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound5
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound7
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources0

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero0 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource0 (mixedVector B) = 0 := by
  have h4898 : mixedVector B (Sum.inr 4898) = Sparse.eval nodeValue4898 (mixedVector B) := by
    change mixedMoment B node4898 node4898Labels = _
    exact sound4898 B hB hF
  have h4899 : mixedVector B (Sum.inr 4899) = Sparse.eval nodeValue4899 (mixedVector B) := by
    change mixedMoment B node4899 node4899Labels = _
    exact sound4899 B hB hF
  have h5302 : mixedVector B (Sum.inr 5302) = Sparse.eval nodeValue5302 (mixedVector B) := by
    change mixedMoment B node5302 node5302Labels = _
    exact sound5302 B hB hF
  have h5310 : mixedVector B (Sum.inr 5310) = Sparse.eval nodeValue5310 (mixedVector B) := by
    change mixedMoment B node5310 node5310Labels = _
    exact sound5310 B hB hF
  have h5412 : mixedVector B (Sum.inr 5412) = Sparse.eval nodeValue5412 (mixedVector B) := by
    change mixedMoment B node5412 node5412Labels = _
    exact sound5412 B hB hF
  have h5443 : mixedVector B (Sum.inr 5443) = Sparse.eval nodeValue5443 (mixedVector B) := by
    change mixedMoment B node5443 node5443Labels = _
    exact sound5443 B hB hF
  have h5453 : mixedVector B (Sum.inr 5453) = Sparse.eval nodeValue5453 (mixedVector B) := by
    change mixedMoment B node5453 node5453Labels = _
    exact sound5453 B hB hF
  have h5455 : mixedVector B (Sum.inr 5455) = Sparse.eval nodeValue5455 (mixedVector B) := by
    change mixedMoment B node5455 node5455Labels = _
    exact sound5455 B hB hF
  simpa only [sourceForm0, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4898, h4899, h5302, h5310, h5412, h5443, h5453, h5455, reducedSource0] using sourceEq0 B hB

theorem rowSound0 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row0 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck0, numericCheck0, reducedZero0 B hB hF, mul_zero]

theorem reducedZero1 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1 (mixedVector B) = 0 := by
  have h4889 : mixedVector B (Sum.inr 4889) = Sparse.eval nodeValue4889 (mixedVector B) := by
    change mixedMoment B node4889 node4889Labels = _
    exact sound4889 B hB hF
  have h4890 : mixedVector B (Sum.inr 4890) = Sparse.eval nodeValue4890 (mixedVector B) := by
    change mixedMoment B node4890 node4890Labels = _
    exact sound4890 B hB hF
  have h4896 : mixedVector B (Sum.inr 4896) = Sparse.eval nodeValue4896 (mixedVector B) := by
    change mixedMoment B node4896 node4896Labels = _
    exact sound4896 B hB hF
  have h5284 : mixedVector B (Sum.inr 5284) = Sparse.eval nodeValue5284 (mixedVector B) := by
    change mixedMoment B node5284 node5284Labels = _
    exact sound5284 B hB hF
  have h5294 : mixedVector B (Sum.inr 5294) = Sparse.eval nodeValue5294 (mixedVector B) := by
    change mixedMoment B node5294 node5294Labels = _
    exact sound5294 B hB hF
  have h5406 : mixedVector B (Sum.inr 5406) = Sparse.eval nodeValue5406 (mixedVector B) := by
    change mixedMoment B node5406 node5406Labels = _
    exact sound5406 B hB hF
  have h5411 : mixedVector B (Sum.inr 5411) = Sparse.eval nodeValue5411 (mixedVector B) := by
    change mixedMoment B node5411 node5411Labels = _
    exact sound5411 B hB hF
  have h5435 : mixedVector B (Sum.inr 5435) = Sparse.eval nodeValue5435 (mixedVector B) := by
    change mixedMoment B node5435 node5435Labels = _
    exact sound5435 B hB hF
  have h5443 : mixedVector B (Sum.inr 5443) = Sparse.eval nodeValue5443 (mixedVector B) := by
    change mixedMoment B node5443 node5443Labels = _
    exact sound5443 B hB hF
  have h5450 : mixedVector B (Sum.inr 5450) = Sparse.eval nodeValue5450 (mixedVector B) := by
    change mixedMoment B node5450 node5450Labels = _
    exact sound5450 B hB hF
  have h5451 : mixedVector B (Sum.inr 5451) = Sparse.eval nodeValue5451 (mixedVector B) := by
    change mixedMoment B node5451 node5451Labels = _
    exact sound5451 B hB hF
  have h5452 : mixedVector B (Sum.inr 5452) = Sparse.eval nodeValue5452 (mixedVector B) := by
    change mixedMoment B node5452 node5452Labels = _
    exact sound5452 B hB hF
  have h5454 : mixedVector B (Sum.inr 5454) = Sparse.eval nodeValue5454 (mixedVector B) := by
    change mixedMoment B node5454 node5454Labels = _
    exact sound5454 B hB hF
  have h5493 : mixedVector B (Sum.inr 5493) = Sparse.eval nodeValue5493 (mixedVector B) := by
    change mixedMoment B node5493 node5493Labels = _
    exact sound5493 B hB hF
  simpa only [sourceForm1, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4889, h4890, h4896, h5284, h5294, h5406, h5411, h5435, h5443, h5450, h5451, h5452, h5454, h5493, reducedSource1] using sourceEq1 B hB

theorem rowSound1 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1, numericCheck1, reducedZero1 B hB hF, mul_zero]

theorem reducedZero2 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2 (mixedVector B) = 0 := by
  have h2245 : mixedVector B (Sum.inr 2245) = Sparse.eval nodeValue2245 (mixedVector B) := by
    change mixedMoment B node2245 node2245Labels = _
    exact sound2245 B hB hF
  have h2247 : mixedVector B (Sum.inr 2247) = Sparse.eval nodeValue2247 (mixedVector B) := by
    change mixedMoment B node2247 node2247Labels = _
    exact sound2247 B hB hF
  have h2266 : mixedVector B (Sum.inr 2266) = Sparse.eval nodeValue2266 (mixedVector B) := by
    change mixedMoment B node2266 node2266Labels = _
    exact sound2266 B hB hF
  have h3077 : mixedVector B (Sum.inr 3077) = Sparse.eval nodeValue3077 (mixedVector B) := by
    change mixedMoment B node3077 node3077Labels = _
    exact sound3077 B hB hF
  have h3101 : mixedVector B (Sum.inr 3101) = Sparse.eval nodeValue3101 (mixedVector B) := by
    change mixedMoment B node3101 node3101Labels = _
    exact sound3101 B hB hF
  have h3801 : mixedVector B (Sum.inr 3801) = Sparse.eval nodeValue3801 (mixedVector B) := by
    change mixedMoment B node3801 node3801Labels = _
    exact sound3801 B hB hF
  have h3809 : mixedVector B (Sum.inr 3809) = Sparse.eval nodeValue3809 (mixedVector B) := by
    change mixedMoment B node3809 node3809Labels = _
    exact sound3809 B hB hF
  have h3853 : mixedVector B (Sum.inr 3853) = Sparse.eval nodeValue3853 (mixedVector B) := by
    change mixedMoment B node3853 node3853Labels = _
    exact sound3853 B hB hF
  have h3862 : mixedVector B (Sum.inr 3862) = Sparse.eval nodeValue3862 (mixedVector B) := by
    change mixedMoment B node3862 node3862Labels = _
    exact sound3862 B hB hF
  have h3910 : mixedVector B (Sum.inr 3910) = Sparse.eval nodeValue3910 (mixedVector B) := by
    change mixedMoment B node3910 node3910Labels = _
    exact sound3910 B hB hF
  have h3913 : mixedVector B (Sum.inr 3913) = Sparse.eval nodeValue3913 (mixedVector B) := by
    change mixedMoment B node3913 node3913Labels = _
    exact sound3913 B hB hF
  have h4016 : mixedVector B (Sum.inr 4016) = Sparse.eval nodeValue4016 (mixedVector B) := by
    change mixedMoment B node4016 node4016Labels = _
    exact sound4016 B hB hF
  have h4039 : mixedVector B (Sum.inr 4039) = Sparse.eval nodeValue4039 (mixedVector B) := by
    change mixedMoment B node4039 node4039Labels = _
    exact sound4039 B hB hF
  have h4040 : mixedVector B (Sum.inr 4040) = Sparse.eval nodeValue4040 (mixedVector B) := by
    change mixedMoment B node4040 node4040Labels = _
    exact sound4040 B hB hF
  simpa only [sourceForm2, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2245, h2247, h2266, h3077, h3101, h3801, h3809, h3853, h3862, h3910, h3913, h4016, h4039, h4040, reducedSource2] using sourceEq2 B hB

theorem rowSound2 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2, numericCheck2, reducedZero2 B hB hF, mul_zero]

theorem reducedZero3 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource3 (mixedVector B) = 0 := by
  have h5301 : mixedVector B (Sum.inr 5301) = Sparse.eval nodeValue5301 (mixedVector B) := by
    change mixedMoment B node5301 node5301Labels = _
    exact sound5301 B hB hF
  have h5302 : mixedVector B (Sum.inr 5302) = Sparse.eval nodeValue5302 (mixedVector B) := by
    change mixedMoment B node5302 node5302Labels = _
    exact sound5302 B hB hF
  have h5306 : mixedVector B (Sum.inr 5306) = Sparse.eval nodeValue5306 (mixedVector B) := by
    change mixedMoment B node5306 node5306Labels = _
    exact sound5306 B hB hF
  have h5412 : mixedVector B (Sum.inr 5412) = Sparse.eval nodeValue5412 (mixedVector B) := by
    change mixedMoment B node5412 node5412Labels = _
    exact sound5412 B hB hF
  have h5437 : mixedVector B (Sum.inr 5437) = Sparse.eval nodeValue5437 (mixedVector B) := by
    change mixedMoment B node5437 node5437Labels = _
    exact sound5437 B hB hF
  have h5439 : mixedVector B (Sum.inr 5439) = Sparse.eval nodeValue5439 (mixedVector B) := by
    change mixedMoment B node5439 node5439Labels = _
    exact sound5439 B hB hF
  have h5453 : mixedVector B (Sum.inr 5453) = Sparse.eval nodeValue5453 (mixedVector B) := by
    change mixedMoment B node5453 node5453Labels = _
    exact sound5453 B hB hF
  have h5455 : mixedVector B (Sum.inr 5455) = Sparse.eval nodeValue5455 (mixedVector B) := by
    change mixedMoment B node5455 node5455Labels = _
    exact sound5455 B hB hF
  have h5456 : mixedVector B (Sum.inr 5456) = Sparse.eval nodeValue5456 (mixedVector B) := by
    change mixedMoment B node5456 node5456Labels = _
    exact sound5456 B hB hF
  simpa only [sourceForm3, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5301, h5302, h5306, h5412, h5437, h5439, h5453, h5455, h5456, reducedSource3] using sourceEq3 B hB

theorem rowSound3 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row3 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck3, numericCheck3, reducedZero3 B hB hF, mul_zero]

theorem reducedZero4 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource4 (mixedVector B) = 0 := by
  have h5259 : mixedVector B (Sum.inr 5259) = Sparse.eval nodeValue5259 (mixedVector B) := by
    change mixedMoment B node5259 node5259Labels = _
    exact sound5259 B hB hF
  have h5261 : mixedVector B (Sum.inr 5261) = Sparse.eval nodeValue5261 (mixedVector B) := by
    change mixedMoment B node5261 node5261Labels = _
    exact sound5261 B hB hF
  have h5275 : mixedVector B (Sum.inr 5275) = Sparse.eval nodeValue5275 (mixedVector B) := by
    change mixedMoment B node5275 node5275Labels = _
    exact sound5275 B hB hF
  have h5293 : mixedVector B (Sum.inr 5293) = Sparse.eval nodeValue5293 (mixedVector B) := by
    change mixedMoment B node5293 node5293Labels = _
    exact sound5293 B hB hF
  have h5473 : mixedVector B (Sum.inr 5473) = Sparse.eval nodeValue5473 (mixedVector B) := by
    change mixedMoment B node5473 node5473Labels = _
    exact sound5473 B hB hF
  have h5475 : mixedVector B (Sum.inr 5475) = Sparse.eval nodeValue5475 (mixedVector B) := by
    change mixedMoment B node5475 node5475Labels = _
    exact sound5475 B hB hF
  have h5477 : mixedVector B (Sum.inr 5477) = Sparse.eval nodeValue5477 (mixedVector B) := by
    change mixedMoment B node5477 node5477Labels = _
    exact sound5477 B hB hF
  have h5483 : mixedVector B (Sum.inr 5483) = Sparse.eval nodeValue5483 (mixedVector B) := by
    change mixedMoment B node5483 node5483Labels = _
    exact sound5483 B hB hF
  have h5487 : mixedVector B (Sum.inr 5487) = Sparse.eval nodeValue5487 (mixedVector B) := by
    change mixedMoment B node5487 node5487Labels = _
    exact sound5487 B hB hF
  have h5490 : mixedVector B (Sum.inr 5490) = Sparse.eval nodeValue5490 (mixedVector B) := by
    change mixedMoment B node5490 node5490Labels = _
    exact sound5490 B hB hF
  have h5492 : mixedVector B (Sum.inr 5492) = Sparse.eval nodeValue5492 (mixedVector B) := by
    change mixedMoment B node5492 node5492Labels = _
    exact sound5492 B hB hF
  have h5493 : mixedVector B (Sum.inr 5493) = Sparse.eval nodeValue5493 (mixedVector B) := by
    change mixedMoment B node5493 node5493Labels = _
    exact sound5493 B hB hF
  have h5501 : mixedVector B (Sum.inr 5501) = Sparse.eval nodeValue5501 (mixedVector B) := by
    change mixedMoment B node5501 node5501Labels = _
    exact sound5501 B hB hF
  simpa only [sourceForm4, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5259, h5261, h5275, h5293, h5473, h5475, h5477, h5483, h5487, h5490, h5492, h5493, h5501, reducedSource4] using sourceEq4 B hB

theorem rowSound4 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row4 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck4, numericCheck4, reducedZero4 B hB hF, mul_zero]

theorem reducedZero5 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource5 (mixedVector B) = 0 := by
  have h2723 : mixedVector B (Sum.inr 2723) = Sparse.eval nodeValue2723 (mixedVector B) := by
    change mixedMoment B node2723 node2723Labels = _
    exact sound2723 B hB hF
  have h2726 : mixedVector B (Sum.inr 2726) = Sparse.eval nodeValue2726 (mixedVector B) := by
    change mixedMoment B node2726 node2726Labels = _
    exact sound2726 B hB hF
  have h2743 : mixedVector B (Sum.inr 2743) = Sparse.eval nodeValue2743 (mixedVector B) := by
    change mixedMoment B node2743 node2743Labels = _
    exact sound2743 B hB hF
  have h2767 : mixedVector B (Sum.inr 2767) = Sparse.eval nodeValue2767 (mixedVector B) := by
    change mixedMoment B node2767 node2767Labels = _
    exact sound2767 B hB hF
  have h3958 : mixedVector B (Sum.inr 3958) = Sparse.eval nodeValue3958 (mixedVector B) := by
    change mixedMoment B node3958 node3958Labels = _
    exact sound3958 B hB hF
  have h3963 : mixedVector B (Sum.inr 3963) = Sparse.eval nodeValue3963 (mixedVector B) := by
    change mixedMoment B node3963 node3963Labels = _
    exact sound3963 B hB hF
  have h3971 : mixedVector B (Sum.inr 3971) = Sparse.eval nodeValue3971 (mixedVector B) := by
    change mixedMoment B node3971 node3971Labels = _
    exact sound3971 B hB hF
  have h3981 : mixedVector B (Sum.inr 3981) = Sparse.eval nodeValue3981 (mixedVector B) := by
    change mixedMoment B node3981 node3981Labels = _
    exact sound3981 B hB hF
  have h4000 : mixedVector B (Sum.inr 4000) = Sparse.eval nodeValue4000 (mixedVector B) := by
    change mixedMoment B node4000 node4000Labels = _
    exact sound4000 B hB hF
  have h4013 : mixedVector B (Sum.inr 4013) = Sparse.eval nodeValue4013 (mixedVector B) := by
    change mixedMoment B node4013 node4013Labels = _
    exact sound4013 B hB hF
  have h4015 : mixedVector B (Sum.inr 4015) = Sparse.eval nodeValue4015 (mixedVector B) := by
    change mixedMoment B node4015 node4015Labels = _
    exact sound4015 B hB hF
  have h4018 : mixedVector B (Sum.inr 4018) = Sparse.eval nodeValue4018 (mixedVector B) := by
    change mixedMoment B node4018 node4018Labels = _
    exact sound4018 B hB hF
  have h4055 : mixedVector B (Sum.inr 4055) = Sparse.eval nodeValue4055 (mixedVector B) := by
    change mixedMoment B node4055 node4055Labels = _
    exact sound4055 B hB hF
  simpa only [sourceForm5, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2723, h2726, h2743, h2767, h3958, h3963, h3971, h3981, h4000, h4013, h4015, h4018, h4055, reducedSource5] using sourceEq5 B hB

theorem rowSound5 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row5 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck5, numericCheck5, reducedZero5 B hB hF, mul_zero]

theorem reducedZero6 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource6 (mixedVector B) = 0 := by
  have h7 : mixedVector B (Sum.inr 7) = Sparse.eval nodeValue7 (mixedVector B) := by
    change mixedMoment B node7 node7Labels = _
    exact sound7 B hB hF
  have h378 : mixedVector B (Sum.inr 378) = Sparse.eval nodeValue378 (mixedVector B) := by
    change mixedMoment B node378 node378Labels = _
    exact sound378 B hB hF
  have h514 : mixedVector B (Sum.inr 514) = Sparse.eval nodeValue514 (mixedVector B) := by
    change mixedMoment B node514 node514Labels = _
    exact sound514 B hB hF
  have h518 : mixedVector B (Sum.inr 518) = Sparse.eval nodeValue518 (mixedVector B) := by
    change mixedMoment B node518 node518Labels = _
    exact sound518 B hB hF
  have h521 : mixedVector B (Sum.inr 521) = Sparse.eval nodeValue521 (mixedVector B) := by
    change mixedMoment B node521 node521Labels = _
    exact sound521 B hB hF
  have h526 : mixedVector B (Sum.inr 526) = Sparse.eval nodeValue526 (mixedVector B) := by
    change mixedMoment B node526 node526Labels = _
    exact sound526 B hB hF
  have h527 : mixedVector B (Sum.inr 527) = Sparse.eval nodeValue527 (mixedVector B) := by
    change mixedMoment B node527 node527Labels = _
    exact sound527 B hB hF
  simpa only [sourceForm6, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h7, h378, h514, h518, h521, h526, h527, reducedSource6] using sourceEq6 B hB

theorem rowSound6 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row6 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck6, numericCheck6, reducedZero6 B hB hF, mul_zero]

theorem reducedZero7 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource7 (mixedVector B) = 0 := by
  have h5439 : mixedVector B (Sum.inr 5439) = Sparse.eval nodeValue5439 (mixedVector B) := by
    change mixedMoment B node5439 node5439Labels = _
    exact sound5439 B hB hF
  have h5441 : mixedVector B (Sum.inr 5441) = Sparse.eval nodeValue5441 (mixedVector B) := by
    change mixedMoment B node5441 node5441Labels = _
    exact sound5441 B hB hF
  have h5443 : mixedVector B (Sum.inr 5443) = Sparse.eval nodeValue5443 (mixedVector B) := by
    change mixedMoment B node5443 node5443Labels = _
    exact sound5443 B hB hF
  have h5448 : mixedVector B (Sum.inr 5448) = Sparse.eval nodeValue5448 (mixedVector B) := by
    change mixedMoment B node5448 node5448Labels = _
    exact sound5448 B hB hF
  have h5449 : mixedVector B (Sum.inr 5449) = Sparse.eval nodeValue5449 (mixedVector B) := by
    change mixedMoment B node5449 node5449Labels = _
    exact sound5449 B hB hF
  have h5455 : mixedVector B (Sum.inr 5455) = Sparse.eval nodeValue5455 (mixedVector B) := by
    change mixedMoment B node5455 node5455Labels = _
    exact sound5455 B hB hF
  have h5488 : mixedVector B (Sum.inr 5488) = Sparse.eval nodeValue5488 (mixedVector B) := by
    change mixedMoment B node5488 node5488Labels = _
    exact sound5488 B hB hF
  have h5491 : mixedVector B (Sum.inr 5491) = Sparse.eval nodeValue5491 (mixedVector B) := by
    change mixedMoment B node5491 node5491Labels = _
    exact sound5491 B hB hF
  have h5496 : mixedVector B (Sum.inr 5496) = Sparse.eval nodeValue5496 (mixedVector B) := by
    change mixedMoment B node5496 node5496Labels = _
    exact sound5496 B hB hF
  simpa only [sourceForm7, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5439, h5441, h5443, h5448, h5449, h5455, h5488, h5491, h5496, reducedSource7] using sourceEq7 B hB

theorem rowSound7 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row7 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck7, numericCheck7, reducedZero7 B hB hF, mul_zero]

theorem reducedZero8 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource8 (mixedVector B) = 0 := by
  have h6 : mixedVector B (Sum.inr 6) = Sparse.eval nodeValue6 (mixedVector B) := by
    change mixedMoment B node6 node6Labels = _
    exact sound6 B hB hF
  have h494 : mixedVector B (Sum.inr 494) = Sparse.eval nodeValue494 (mixedVector B) := by
    change mixedMoment B node494 node494Labels = _
    exact sound494 B hB hF
  have h500 : mixedVector B (Sum.inr 500) = Sparse.eval nodeValue500 (mixedVector B) := by
    change mixedMoment B node500 node500Labels = _
    exact sound500 B hB hF
  have h524 : mixedVector B (Sum.inr 524) = Sparse.eval nodeValue524 (mixedVector B) := by
    change mixedMoment B node524 node524Labels = _
    exact sound524 B hB hF
  have h527 : mixedVector B (Sum.inr 527) = Sparse.eval nodeValue527 (mixedVector B) := by
    change mixedMoment B node527 node527Labels = _
    exact sound527 B hB hF
  simpa only [sourceForm8, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h6, h494, h500, h524, h527, reducedSource8] using sourceEq8 B hB

theorem rowSound8 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row8 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck8, numericCheck8, reducedZero8 B hB hF, mul_zero]

theorem reducedZero9 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource9 (mixedVector B) = 0 := by
  have h4093 : mixedVector B (Sum.inr 4093) = Sparse.eval nodeValue4093 (mixedVector B) := by
    change mixedMoment B node4093 node4093Labels = _
    exact sound4093 B hB hF
  have h5293 : mixedVector B (Sum.inr 5293) = Sparse.eval nodeValue5293 (mixedVector B) := by
    change mixedMoment B node5293 node5293Labels = _
    exact sound5293 B hB hF
  have h5294 : mixedVector B (Sum.inr 5294) = Sparse.eval nodeValue5294 (mixedVector B) := by
    change mixedMoment B node5294 node5294Labels = _
    exact sound5294 B hB hF
  have h5296 : mixedVector B (Sum.inr 5296) = Sparse.eval nodeValue5296 (mixedVector B) := by
    change mixedMoment B node5296 node5296Labels = _
    exact sound5296 B hB hF
  have h5309 : mixedVector B (Sum.inr 5309) = Sparse.eval nodeValue5309 (mixedVector B) := by
    change mixedMoment B node5309 node5309Labels = _
    exact sound5309 B hB hF
  have h5310 : mixedVector B (Sum.inr 5310) = Sparse.eval nodeValue5310 (mixedVector B) := by
    change mixedMoment B node5310 node5310Labels = _
    exact sound5310 B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434 B hB hF
  have h5442 : mixedVector B (Sum.inr 5442) = Sparse.eval nodeValue5442 (mixedVector B) := by
    change mixedMoment B node5442 node5442Labels = _
    exact sound5442 B hB hF
  have h5451 : mixedVector B (Sum.inr 5451) = Sparse.eval nodeValue5451 (mixedVector B) := by
    change mixedMoment B node5451 node5451Labels = _
    exact sound5451 B hB hF
  have h5454 : mixedVector B (Sum.inr 5454) = Sparse.eval nodeValue5454 (mixedVector B) := by
    change mixedMoment B node5454 node5454Labels = _
    exact sound5454 B hB hF
  have h5492 : mixedVector B (Sum.inr 5492) = Sparse.eval nodeValue5492 (mixedVector B) := by
    change mixedMoment B node5492 node5492Labels = _
    exact sound5492 B hB hF
  have h5494 : mixedVector B (Sum.inr 5494) = Sparse.eval nodeValue5494 (mixedVector B) := by
    change mixedMoment B node5494 node5494Labels = _
    exact sound5494 B hB hF
  have h5495 : mixedVector B (Sum.inr 5495) = Sparse.eval nodeValue5495 (mixedVector B) := by
    change mixedMoment B node5495 node5495Labels = _
    exact sound5495 B hB hF
  simpa only [sourceForm9, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4093, h5293, h5294, h5296, h5309, h5310, h5434, h5442, h5451, h5454, h5492, h5494, h5495, reducedSource9] using sourceEq9 B hB

theorem rowSound9 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row9 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck9, numericCheck9, reducedZero9 B hB hF, mul_zero]

theorem reducedZero10 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource10 (mixedVector B) = 0 := by
  have h4094 : mixedVector B (Sum.inr 4094) = Sparse.eval nodeValue4094 (mixedVector B) := by
    change mixedMoment B node4094 node4094Labels = _
    exact sound4094 B hB hF
  have h5306 : mixedVector B (Sum.inr 5306) = Sparse.eval nodeValue5306 (mixedVector B) := by
    change mixedMoment B node5306 node5306Labels = _
    exact sound5306 B hB hF
  have h5308 : mixedVector B (Sum.inr 5308) = Sparse.eval nodeValue5308 (mixedVector B) := by
    change mixedMoment B node5308 node5308Labels = _
    exact sound5308 B hB hF
  have h5310 : mixedVector B (Sum.inr 5310) = Sparse.eval nodeValue5310 (mixedVector B) := by
    change mixedMoment B node5310 node5310Labels = _
    exact sound5310 B hB hF
  have h5439 : mixedVector B (Sum.inr 5439) = Sparse.eval nodeValue5439 (mixedVector B) := by
    change mixedMoment B node5439 node5439Labels = _
    exact sound5439 B hB hF
  have h5441 : mixedVector B (Sum.inr 5441) = Sparse.eval nodeValue5441 (mixedVector B) := by
    change mixedMoment B node5441 node5441Labels = _
    exact sound5441 B hB hF
  have h5443 : mixedVector B (Sum.inr 5443) = Sparse.eval nodeValue5443 (mixedVector B) := by
    change mixedMoment B node5443 node5443Labels = _
    exact sound5443 B hB hF
  have h5453 : mixedVector B (Sum.inr 5453) = Sparse.eval nodeValue5453 (mixedVector B) := by
    change mixedMoment B node5453 node5453Labels = _
    exact sound5453 B hB hF
  have h5455 : mixedVector B (Sum.inr 5455) = Sparse.eval nodeValue5455 (mixedVector B) := by
    change mixedMoment B node5455 node5455Labels = _
    exact sound5455 B hB hF
  have h5456 : mixedVector B (Sum.inr 5456) = Sparse.eval nodeValue5456 (mixedVector B) := by
    change mixedMoment B node5456 node5456Labels = _
    exact sound5456 B hB hF
  have h5491 : mixedVector B (Sum.inr 5491) = Sparse.eval nodeValue5491 (mixedVector B) := by
    change mixedMoment B node5491 node5491Labels = _
    exact sound5491 B hB hF
  have h5496 : mixedVector B (Sum.inr 5496) = Sparse.eval nodeValue5496 (mixedVector B) := by
    change mixedMoment B node5496 node5496Labels = _
    exact sound5496 B hB hF
  simpa only [sourceForm10, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4094, h5306, h5308, h5310, h5439, h5441, h5443, h5453, h5455, h5456, h5491, h5496, reducedSource10] using sourceEq10 B hB

theorem rowSound10 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row10 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck10, numericCheck10, reducedZero10 B hB hF, mul_zero]

theorem reducedZero11 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource11 (mixedVector B) = 0 := by
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  have h4093 : mixedVector B (Sum.inr 4093) = Sparse.eval nodeValue4093 (mixedVector B) := by
    change mixedMoment B node4093 node4093Labels = _
    exact sound4093 B hB hF
  have h4097 : mixedVector B (Sum.inr 4097) = Sparse.eval nodeValue4097 (mixedVector B) := by
    change mixedMoment B node4097 node4097Labels = _
    exact sound4097 B hB hF
  simpa only [sourceForm11, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4084, h4085, h4092, h4093, h4097, reducedSource11] using sourceEq11 B hB

theorem rowSound11 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row11 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck11, numericCheck11, reducedZero11 B hB hF, mul_zero]

theorem reducedZero12 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource12 (mixedVector B) = 0 := by
  have h5283 : mixedVector B (Sum.inr 5283) = Sparse.eval nodeValue5283 (mixedVector B) := by
    change mixedMoment B node5283 node5283Labels = _
    exact sound5283 B hB hF
  have h5284 : mixedVector B (Sum.inr 5284) = Sparse.eval nodeValue5284 (mixedVector B) := by
    change mixedMoment B node5284 node5284Labels = _
    exact sound5284 B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292 B hB hF
  have h5406 : mixedVector B (Sum.inr 5406) = Sparse.eval nodeValue5406 (mixedVector B) := by
    change mixedMoment B node5406 node5406Labels = _
    exact sound5406 B hB hF
  have h5411 : mixedVector B (Sum.inr 5411) = Sparse.eval nodeValue5411 (mixedVector B) := by
    change mixedMoment B node5411 node5411Labels = _
    exact sound5411 B hB hF
  have h5433 : mixedVector B (Sum.inr 5433) = Sparse.eval nodeValue5433 (mixedVector B) := by
    change mixedMoment B node5433 node5433Labels = _
    exact sound5433 B hB hF
  have h5447 : mixedVector B (Sum.inr 5447) = Sparse.eval nodeValue5447 (mixedVector B) := by
    change mixedMoment B node5447 node5447Labels = _
    exact sound5447 B hB hF
  have h5450 : mixedVector B (Sum.inr 5450) = Sparse.eval nodeValue5450 (mixedVector B) := by
    change mixedMoment B node5450 node5450Labels = _
    exact sound5450 B hB hF
  have h5452 : mixedVector B (Sum.inr 5452) = Sparse.eval nodeValue5452 (mixedVector B) := by
    change mixedMoment B node5452 node5452Labels = _
    exact sound5452 B hB hF
  have h5453 : mixedVector B (Sum.inr 5453) = Sparse.eval nodeValue5453 (mixedVector B) := by
    change mixedMoment B node5453 node5453Labels = _
    exact sound5453 B hB hF
  have h5454 : mixedVector B (Sum.inr 5454) = Sparse.eval nodeValue5454 (mixedVector B) := by
    change mixedMoment B node5454 node5454Labels = _
    exact sound5454 B hB hF
  have h5485 : mixedVector B (Sum.inr 5485) = Sparse.eval nodeValue5485 (mixedVector B) := by
    change mixedMoment B node5485 node5485Labels = _
    exact sound5485 B hB hF
  have h5489 : mixedVector B (Sum.inr 5489) = Sparse.eval nodeValue5489 (mixedVector B) := by
    change mixedMoment B node5489 node5489Labels = _
    exact sound5489 B hB hF
  have h5493 : mixedVector B (Sum.inr 5493) = Sparse.eval nodeValue5493 (mixedVector B) := by
    change mixedMoment B node5493 node5493Labels = _
    exact sound5493 B hB hF
  simpa only [sourceForm12, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5283, h5284, h5292, h5406, h5411, h5433, h5447, h5450, h5452, h5453, h5454, h5485, h5489, h5493, reducedSource12] using sourceEq12 B hB

theorem rowSound12 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row12 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck12, numericCheck12, reducedZero12 B hB hF, mul_zero]

theorem reducedZero13 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource13 (mixedVector B) = 0 := by
  have h3076 : mixedVector B (Sum.inr 3076) = Sparse.eval nodeValue3076 (mixedVector B) := by
    change mixedMoment B node3076 node3076Labels = _
    exact sound3076 B hB hF
  have h3077 : mixedVector B (Sum.inr 3077) = Sparse.eval nodeValue3077 (mixedVector B) := by
    change mixedMoment B node3077 node3077Labels = _
    exact sound3077 B hB hF
  have h3100 : mixedVector B (Sum.inr 3100) = Sparse.eval nodeValue3100 (mixedVector B) := by
    change mixedMoment B node3100 node3100Labels = _
    exact sound3100 B hB hF
  have h3801 : mixedVector B (Sum.inr 3801) = Sparse.eval nodeValue3801 (mixedVector B) := by
    change mixedMoment B node3801 node3801Labels = _
    exact sound3801 B hB hF
  have h3809 : mixedVector B (Sum.inr 3809) = Sparse.eval nodeValue3809 (mixedVector B) := by
    change mixedMoment B node3809 node3809Labels = _
    exact sound3809 B hB hF
  have h3912 : mixedVector B (Sum.inr 3912) = Sparse.eval nodeValue3912 (mixedVector B) := by
    change mixedMoment B node3912 node3912Labels = _
    exact sound3912 B hB hF
  have h4009 : mixedVector B (Sum.inr 4009) = Sparse.eval nodeValue4009 (mixedVector B) := by
    change mixedMoment B node4009 node4009Labels = _
    exact sound4009 B hB hF
  have h4010 : mixedVector B (Sum.inr 4010) = Sparse.eval nodeValue4010 (mixedVector B) := by
    change mixedMoment B node4010 node4010Labels = _
    exact sound4010 B hB hF
  have h4016 : mixedVector B (Sum.inr 4016) = Sparse.eval nodeValue4016 (mixedVector B) := by
    change mixedMoment B node4016 node4016Labels = _
    exact sound4016 B hB hF
  have h4025 : mixedVector B (Sum.inr 4025) = Sparse.eval nodeValue4025 (mixedVector B) := by
    change mixedMoment B node4025 node4025Labels = _
    exact sound4025 B hB hF
  have h4029 : mixedVector B (Sum.inr 4029) = Sparse.eval nodeValue4029 (mixedVector B) := by
    change mixedMoment B node4029 node4029Labels = _
    exact sound4029 B hB hF
  have h4033 : mixedVector B (Sum.inr 4033) = Sparse.eval nodeValue4033 (mixedVector B) := by
    change mixedMoment B node4033 node4033Labels = _
    exact sound4033 B hB hF
  have h4039 : mixedVector B (Sum.inr 4039) = Sparse.eval nodeValue4039 (mixedVector B) := by
    change mixedMoment B node4039 node4039Labels = _
    exact sound4039 B hB hF
  have h4040 : mixedVector B (Sum.inr 4040) = Sparse.eval nodeValue4040 (mixedVector B) := by
    change mixedMoment B node4040 node4040Labels = _
    exact sound4040 B hB hF
  simpa only [sourceForm13, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3076, h3077, h3100, h3801, h3809, h3912, h4009, h4010, h4016, h4025, h4029, h4033, h4039, h4040, reducedSource13] using sourceEq13 B hB

theorem rowSound13 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row13 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck13, numericCheck13, reducedZero13 B hB hF, mul_zero]

theorem reducedZero14 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource14 (mixedVector B) = 0 := by
  have h4887 : mixedVector B (Sum.inr 4887) = Sparse.eval nodeValue4887 (mixedVector B) := by
    change mixedMoment B node4887 node4887Labels = _
    exact sound4887 B hB hF
  have h4888 : mixedVector B (Sum.inr 4888) = Sparse.eval nodeValue4888 (mixedVector B) := by
    change mixedMoment B node4888 node4888Labels = _
    exact sound4888 B hB hF
  have h5405 : mixedVector B (Sum.inr 5405) = Sparse.eval nodeValue5405 (mixedVector B) := by
    change mixedMoment B node5405 node5405Labels = _
    exact sound5405 B hB hF
  have h5433 : mixedVector B (Sum.inr 5433) = Sparse.eval nodeValue5433 (mixedVector B) := by
    change mixedMoment B node5433 node5433Labels = _
    exact sound5433 B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434 B hB hF
  have h5439 : mixedVector B (Sum.inr 5439) = Sparse.eval nodeValue5439 (mixedVector B) := by
    change mixedMoment B node5439 node5439Labels = _
    exact sound5439 B hB hF
  have h5498 : mixedVector B (Sum.inr 5498) = Sparse.eval nodeValue5498 (mixedVector B) := by
    change mixedMoment B node5498 node5498Labels = _
    exact sound5498 B hB hF
  have h5499 : mixedVector B (Sum.inr 5499) = Sparse.eval nodeValue5499 (mixedVector B) := by
    change mixedMoment B node5499 node5499Labels = _
    exact sound5499 B hB hF
  simpa only [sourceForm14, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4887, h4888, h5405, h5433, h5434, h5439, h5498, h5499, reducedSource14] using sourceEq14 B hB

theorem rowSound14 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row14 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck14, numericCheck14, reducedZero14 B hB hF, mul_zero]

theorem reducedZero15 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource15 (mixedVector B) = 0 := by
  have h5290 : mixedVector B (Sum.inr 5290) = Sparse.eval nodeValue5290 (mixedVector B) := by
    change mixedMoment B node5290 node5290Labels = _
    exact sound5290 B hB hF
  have h5291 : mixedVector B (Sum.inr 5291) = Sparse.eval nodeValue5291 (mixedVector B) := by
    change mixedMoment B node5291 node5291Labels = _
    exact sound5291 B hB hF
  have h5294 : mixedVector B (Sum.inr 5294) = Sparse.eval nodeValue5294 (mixedVector B) := by
    change mixedMoment B node5294 node5294Labels = _
    exact sound5294 B hB hF
  have h5304 : mixedVector B (Sum.inr 5304) = Sparse.eval nodeValue5304 (mixedVector B) := by
    change mixedMoment B node5304 node5304Labels = _
    exact sound5304 B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434 B hB hF
  have h5438 : mixedVector B (Sum.inr 5438) = Sparse.eval nodeValue5438 (mixedVector B) := by
    change mixedMoment B node5438 node5438Labels = _
    exact sound5438 B hB hF
  have h5442 : mixedVector B (Sum.inr 5442) = Sparse.eval nodeValue5442 (mixedVector B) := by
    change mixedMoment B node5442 node5442Labels = _
    exact sound5442 B hB hF
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
  have h5481 : mixedVector B (Sum.inr 5481) = Sparse.eval nodeValue5481 (mixedVector B) := by
    change mixedMoment B node5481 node5481Labels = _
    exact sound5481 B hB hF
  have h5484 : mixedVector B (Sum.inr 5484) = Sparse.eval nodeValue5484 (mixedVector B) := by
    change mixedMoment B node5484 node5484Labels = _
    exact sound5484 B hB hF
  have h5485 : mixedVector B (Sum.inr 5485) = Sparse.eval nodeValue5485 (mixedVector B) := by
    change mixedMoment B node5485 node5485Labels = _
    exact sound5485 B hB hF
  have h5490 : mixedVector B (Sum.inr 5490) = Sparse.eval nodeValue5490 (mixedVector B) := by
    change mixedMoment B node5490 node5490Labels = _
    exact sound5490 B hB hF
  have h5492 : mixedVector B (Sum.inr 5492) = Sparse.eval nodeValue5492 (mixedVector B) := by
    change mixedMoment B node5492 node5492Labels = _
    exact sound5492 B hB hF
  have h5493 : mixedVector B (Sum.inr 5493) = Sparse.eval nodeValue5493 (mixedVector B) := by
    change mixedMoment B node5493 node5493Labels = _
    exact sound5493 B hB hF
  have h5494 : mixedVector B (Sum.inr 5494) = Sparse.eval nodeValue5494 (mixedVector B) := by
    change mixedMoment B node5494 node5494Labels = _
    exact sound5494 B hB hF
  have h5495 : mixedVector B (Sum.inr 5495) = Sparse.eval nodeValue5495 (mixedVector B) := by
    change mixedMoment B node5495 node5495Labels = _
    exact sound5495 B hB hF
  simpa only [sourceForm15, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5290, h5291, h5294, h5304, h5434, h5438, h5442, h5443, h5450, h5451, h5454, h5455, h5481, h5484, h5485, h5490, h5492, h5493, h5494, h5495, reducedSource15] using sourceEq15 B hB

theorem rowSound15 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row15 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck15, numericCheck15, reducedZero15 B hB hF, mul_zero]

theorem sourceRowsAt0 : MixedData.sourceRows (0 : Fin 2425) =
    MixedData.row0 := by decide +kernel

theorem sourceRowsAt1 : MixedData.sourceRows (1 : Fin 2425) =
    MixedData.row1 := by decide +kernel

theorem sourceRowsAt2 : MixedData.sourceRows (2 : Fin 2425) =
    MixedData.row2 := by decide +kernel

theorem sourceRowsAt3 : MixedData.sourceRows (3 : Fin 2425) =
    MixedData.row3 := by decide +kernel

theorem sourceRowsAt4 : MixedData.sourceRows (4 : Fin 2425) =
    MixedData.row4 := by decide +kernel

theorem sourceRowsAt5 : MixedData.sourceRows (5 : Fin 2425) =
    MixedData.row5 := by decide +kernel

theorem sourceRowsAt6 : MixedData.sourceRows (6 : Fin 2425) =
    MixedData.row6 := by decide +kernel

theorem sourceRowsAt7 : MixedData.sourceRows (7 : Fin 2425) =
    MixedData.row7 := by decide +kernel

theorem sourceRowsAt8 : MixedData.sourceRows (8 : Fin 2425) =
    MixedData.row8 := by decide +kernel

theorem sourceRowsAt9 : MixedData.sourceRows (9 : Fin 2425) =
    MixedData.row9 := by decide +kernel

theorem sourceRowsAt10 : MixedData.sourceRows (10 : Fin 2425) =
    MixedData.row10 := by decide +kernel

theorem sourceRowsAt11 : MixedData.sourceRows (11 : Fin 2425) =
    MixedData.row11 := by decide +kernel

theorem sourceRowsAt12 : MixedData.sourceRows (12 : Fin 2425) =
    MixedData.row12 := by decide +kernel

theorem sourceRowsAt13 : MixedData.sourceRows (13 : Fin 2425) =
    MixedData.row13 := by decide +kernel

theorem sourceRowsAt14 : MixedData.sourceRows (14 : Fin 2425) =
    MixedData.row14 := by decide +kernel

theorem sourceRowsAt15 : MixedData.sourceRows (15 : Fin 2425) =
    MixedData.row15 := by decide +kernel

theorem chunkSound0 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 0) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ k.val = 3 ∨ k.val = 4 ∨ k.val = 5 ∨ k.val = 6 ∨ k.val = 7 ∨ k.val = 8 ∨ k.val = 9 ∨ k.val = 10 ∨ k.val = 11 ∨ k.val = 12 ∨ k.val = 13 ∨ k.val = 14 ∨ k.val = 15 := by omega
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15
  · have he : k = (0 : Fin 2425) := Fin.ext h0
    subst k
    rw [sourceRowsAt0]
    exact rowSound0 B hB hF
  · have he : k = (1 : Fin 2425) := Fin.ext h1
    subst k
    rw [sourceRowsAt1]
    exact rowSound1 B hB hF
  · have he : k = (2 : Fin 2425) := Fin.ext h2
    subst k
    rw [sourceRowsAt2]
    exact rowSound2 B hB hF
  · have he : k = (3 : Fin 2425) := Fin.ext h3
    subst k
    rw [sourceRowsAt3]
    exact rowSound3 B hB hF
  · have he : k = (4 : Fin 2425) := Fin.ext h4
    subst k
    rw [sourceRowsAt4]
    exact rowSound4 B hB hF
  · have he : k = (5 : Fin 2425) := Fin.ext h5
    subst k
    rw [sourceRowsAt5]
    exact rowSound5 B hB hF
  · have he : k = (6 : Fin 2425) := Fin.ext h6
    subst k
    rw [sourceRowsAt6]
    exact rowSound6 B hB hF
  · have he : k = (7 : Fin 2425) := Fin.ext h7
    subst k
    rw [sourceRowsAt7]
    exact rowSound7 B hB hF
  · have he : k = (8 : Fin 2425) := Fin.ext h8
    subst k
    rw [sourceRowsAt8]
    exact rowSound8 B hB hF
  · have he : k = (9 : Fin 2425) := Fin.ext h9
    subst k
    rw [sourceRowsAt9]
    exact rowSound9 B hB hF
  · have he : k = (10 : Fin 2425) := Fin.ext h10
    subst k
    rw [sourceRowsAt10]
    exact rowSound10 B hB hF
  · have he : k = (11 : Fin 2425) := Fin.ext h11
    subst k
    rw [sourceRowsAt11]
    exact rowSound11 B hB hF
  · have he : k = (12 : Fin 2425) := Fin.ext h12
    subst k
    rw [sourceRowsAt12]
    exact rowSound12 B hB hF
  · have he : k = (13 : Fin 2425) := Fin.ext h13
    subst k
    rw [sourceRowsAt13]
    exact rowSound13 B hB hF
  · have he : k = (14 : Fin 2425) := Fin.ext h14
    subst k
    rw [sourceRowsAt14]
    exact rowSound14 B hB hF
  · have he : k = (15 : Fin 2425) := Fin.ext h15
    subst k
    rw [sourceRowsAt15]
    exact rowSound15 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
