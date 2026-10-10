import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic1
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources1

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero16 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource16 (mixedVector B) = 0 := by
  have h2764 : mixedVector B (Sum.inr 2764) = Sparse.eval nodeValue2764 (mixedVector B) := by
    change mixedMoment B node2764 node2764Labels = _
    exact sound2764 B hB hF
  have h2765 : mixedVector B (Sum.inr 2765) = Sparse.eval nodeValue2765 (mixedVector B) := by
    change mixedMoment B node2765 node2765Labels = _
    exact sound2765 B hB hF
  have h2768 : mixedVector B (Sum.inr 2768) = Sparse.eval nodeValue2768 (mixedVector B) := by
    change mixedMoment B node2768 node2768Labels = _
    exact sound2768 B hB hF
  have h2782 : mixedVector B (Sum.inr 2782) = Sparse.eval nodeValue2782 (mixedVector B) := by
    change mixedMoment B node2782 node2782Labels = _
    exact sound2782 B hB hF
  have h3876 : mixedVector B (Sum.inr 3876) = Sparse.eval nodeValue3876 (mixedVector B) := by
    change mixedMoment B node3876 node3876Labels = _
    exact sound3876 B hB hF
  have h3888 : mixedVector B (Sum.inr 3888) = Sparse.eval nodeValue3888 (mixedVector B) := by
    change mixedMoment B node3888 node3888Labels = _
    exact sound3888 B hB hF
  have h3907 : mixedVector B (Sum.inr 3907) = Sparse.eval nodeValue3907 (mixedVector B) := by
    change mixedMoment B node3907 node3907Labels = _
    exact sound3907 B hB hF
  have h3910 : mixedVector B (Sum.inr 3910) = Sparse.eval nodeValue3910 (mixedVector B) := by
    change mixedMoment B node3910 node3910Labels = _
    exact sound3910 B hB hF
  have h3913 : mixedVector B (Sum.inr 3913) = Sparse.eval nodeValue3913 (mixedVector B) := by
    change mixedMoment B node3913 node3913Labels = _
    exact sound3913 B hB hF
  have h3914 : mixedVector B (Sum.inr 3914) = Sparse.eval nodeValue3914 (mixedVector B) := by
    change mixedMoment B node3914 node3914Labels = _
    exact sound3914 B hB hF
  have h3979 : mixedVector B (Sum.inr 3979) = Sparse.eval nodeValue3979 (mixedVector B) := by
    change mixedMoment B node3979 node3979Labels = _
    exact sound3979 B hB hF
  have h3982 : mixedVector B (Sum.inr 3982) = Sparse.eval nodeValue3982 (mixedVector B) := by
    change mixedMoment B node3982 node3982Labels = _
    exact sound3982 B hB hF
  have h3983 : mixedVector B (Sum.inr 3983) = Sparse.eval nodeValue3983 (mixedVector B) := by
    change mixedMoment B node3983 node3983Labels = _
    exact sound3983 B hB hF
  have h3998 : mixedVector B (Sum.inr 3998) = Sparse.eval nodeValue3998 (mixedVector B) := by
    change mixedMoment B node3998 node3998Labels = _
    exact sound3998 B hB hF
  have h4001 : mixedVector B (Sum.inr 4001) = Sparse.eval nodeValue4001 (mixedVector B) := by
    change mixedMoment B node4001 node4001Labels = _
    exact sound4001 B hB hF
  have h4013 : mixedVector B (Sum.inr 4013) = Sparse.eval nodeValue4013 (mixedVector B) := by
    change mixedMoment B node4013 node4013Labels = _
    exact sound4013 B hB hF
  have h4017 : mixedVector B (Sum.inr 4017) = Sparse.eval nodeValue4017 (mixedVector B) := by
    change mixedMoment B node4017 node4017Labels = _
    exact sound4017 B hB hF
  have h4018 : mixedVector B (Sum.inr 4018) = Sparse.eval nodeValue4018 (mixedVector B) := by
    change mixedMoment B node4018 node4018Labels = _
    exact sound4018 B hB hF
  have h4019 : mixedVector B (Sum.inr 4019) = Sparse.eval nodeValue4019 (mixedVector B) := by
    change mixedMoment B node4019 node4019Labels = _
    exact sound4019 B hB hF
  have h4020 : mixedVector B (Sum.inr 4020) = Sparse.eval nodeValue4020 (mixedVector B) := by
    change mixedMoment B node4020 node4020Labels = _
    exact sound4020 B hB hF
  have h4021 : mixedVector B (Sum.inr 4021) = Sparse.eval nodeValue4021 (mixedVector B) := by
    change mixedMoment B node4021 node4021Labels = _
    exact sound4021 B hB hF
  simpa only [sourceForm16, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2764, h2765, h2768, h2782, h3876, h3888, h3907, h3910, h3913, h3914, h3979, h3982, h3983, h3998, h4001, h4013, h4017, h4018, h4019, h4020, h4021, reducedSource16] using sourceEq16 B hB

theorem rowSound16 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row16 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck16, numericCheck16, reducedZero16 B hB hF, mul_zero]

theorem reducedZero17 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource17 (mixedVector B) = 0 := by
  have h5271 : mixedVector B (Sum.inr 5271) = Sparse.eval nodeValue5271 (mixedVector B) := by
    change mixedMoment B node5271 node5271Labels = _
    exact sound5271 B hB hF
  have h5272 : mixedVector B (Sum.inr 5272) = Sparse.eval nodeValue5272 (mixedVector B) := by
    change mixedMoment B node5272 node5272Labels = _
    exact sound5272 B hB hF
  have h5275 : mixedVector B (Sum.inr 5275) = Sparse.eval nodeValue5275 (mixedVector B) := by
    change mixedMoment B node5275 node5275Labels = _
    exact sound5275 B hB hF
  have h5306 : mixedVector B (Sum.inr 5306) = Sparse.eval nodeValue5306 (mixedVector B) := by
    change mixedMoment B node5306 node5306Labels = _
    exact sound5306 B hB hF
  have h5473 : mixedVector B (Sum.inr 5473) = Sparse.eval nodeValue5473 (mixedVector B) := by
    change mixedMoment B node5473 node5473Labels = _
    exact sound5473 B hB hF
  have h5475 : mixedVector B (Sum.inr 5475) = Sparse.eval nodeValue5475 (mixedVector B) := by
    change mixedMoment B node5475 node5475Labels = _
    exact sound5475 B hB hF
  have h5478 : mixedVector B (Sum.inr 5478) = Sparse.eval nodeValue5478 (mixedVector B) := by
    change mixedMoment B node5478 node5478Labels = _
    exact sound5478 B hB hF
  have h5485 : mixedVector B (Sum.inr 5485) = Sparse.eval nodeValue5485 (mixedVector B) := by
    change mixedMoment B node5485 node5485Labels = _
    exact sound5485 B hB hF
  have h5490 : mixedVector B (Sum.inr 5490) = Sparse.eval nodeValue5490 (mixedVector B) := by
    change mixedMoment B node5490 node5490Labels = _
    exact sound5490 B hB hF
  have h5491 : mixedVector B (Sum.inr 5491) = Sparse.eval nodeValue5491 (mixedVector B) := by
    change mixedMoment B node5491 node5491Labels = _
    exact sound5491 B hB hF
  have h5492 : mixedVector B (Sum.inr 5492) = Sparse.eval nodeValue5492 (mixedVector B) := by
    change mixedMoment B node5492 node5492Labels = _
    exact sound5492 B hB hF
  have h5493 : mixedVector B (Sum.inr 5493) = Sparse.eval nodeValue5493 (mixedVector B) := by
    change mixedMoment B node5493 node5493Labels = _
    exact sound5493 B hB hF
  have h5501 : mixedVector B (Sum.inr 5501) = Sparse.eval nodeValue5501 (mixedVector B) := by
    change mixedMoment B node5501 node5501Labels = _
    exact sound5501 B hB hF
  simpa only [sourceForm17, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5271, h5272, h5275, h5306, h5473, h5475, h5478, h5485, h5490, h5491, h5492, h5493, h5501, reducedSource17] using sourceEq17 B hB

theorem rowSound17 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row17 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck17, numericCheck17, reducedZero17 B hB hF, mul_zero]

theorem reducedZero18 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource18 (mixedVector B) = 0 := by
  have h5257 : mixedVector B (Sum.inr 5257) = Sparse.eval nodeValue5257 (mixedVector B) := by
    change mixedMoment B node5257 node5257Labels = _
    exact sound5257 B hB hF
  have h5258 : mixedVector B (Sum.inr 5258) = Sparse.eval nodeValue5258 (mixedVector B) := by
    change mixedMoment B node5258 node5258Labels = _
    exact sound5258 B hB hF
  have h5259 : mixedVector B (Sum.inr 5259) = Sparse.eval nodeValue5259 (mixedVector B) := by
    change mixedMoment B node5259 node5259Labels = _
    exact sound5259 B hB hF
  have h5271 : mixedVector B (Sum.inr 5271) = Sparse.eval nodeValue5271 (mixedVector B) := by
    change mixedMoment B node5271 node5271Labels = _
    exact sound5271 B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292 B hB hF
  have h5424 : mixedVector B (Sum.inr 5424) = Sparse.eval nodeValue5424 (mixedVector B) := by
    change mixedMoment B node5424 node5424Labels = _
    exact sound5424 B hB hF
  have h5428 : mixedVector B (Sum.inr 5428) = Sparse.eval nodeValue5428 (mixedVector B) := by
    change mixedMoment B node5428 node5428Labels = _
    exact sound5428 B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434 B hB hF
  have h5439 : mixedVector B (Sum.inr 5439) = Sparse.eval nodeValue5439 (mixedVector B) := by
    change mixedMoment B node5439 node5439Labels = _
    exact sound5439 B hB hF
  have h5472 : mixedVector B (Sum.inr 5472) = Sparse.eval nodeValue5472 (mixedVector B) := by
    change mixedMoment B node5472 node5472Labels = _
    exact sound5472 B hB hF
  have h5473 : mixedVector B (Sum.inr 5473) = Sparse.eval nodeValue5473 (mixedVector B) := by
    change mixedMoment B node5473 node5473Labels = _
    exact sound5473 B hB hF
  have h5477 : mixedVector B (Sum.inr 5477) = Sparse.eval nodeValue5477 (mixedVector B) := by
    change mixedMoment B node5477 node5477Labels = _
    exact sound5477 B hB hF
  have h5478 : mixedVector B (Sum.inr 5478) = Sparse.eval nodeValue5478 (mixedVector B) := by
    change mixedMoment B node5478 node5478Labels = _
    exact sound5478 B hB hF
  have h5482 : mixedVector B (Sum.inr 5482) = Sparse.eval nodeValue5482 (mixedVector B) := by
    change mixedMoment B node5482 node5482Labels = _
    exact sound5482 B hB hF
  have h5483 : mixedVector B (Sum.inr 5483) = Sparse.eval nodeValue5483 (mixedVector B) := by
    change mixedMoment B node5483 node5483Labels = _
    exact sound5483 B hB hF
  have h5485 : mixedVector B (Sum.inr 5485) = Sparse.eval nodeValue5485 (mixedVector B) := by
    change mixedMoment B node5485 node5485Labels = _
    exact sound5485 B hB hF
  have h5486 : mixedVector B (Sum.inr 5486) = Sparse.eval nodeValue5486 (mixedVector B) := by
    change mixedMoment B node5486 node5486Labels = _
    exact sound5486 B hB hF
  have h5489 : mixedVector B (Sum.inr 5489) = Sparse.eval nodeValue5489 (mixedVector B) := by
    change mixedMoment B node5489 node5489Labels = _
    exact sound5489 B hB hF
  have h5490 : mixedVector B (Sum.inr 5490) = Sparse.eval nodeValue5490 (mixedVector B) := by
    change mixedMoment B node5490 node5490Labels = _
    exact sound5490 B hB hF
  have h5491 : mixedVector B (Sum.inr 5491) = Sparse.eval nodeValue5491 (mixedVector B) := by
    change mixedMoment B node5491 node5491Labels = _
    exact sound5491 B hB hF
  have h5492 : mixedVector B (Sum.inr 5492) = Sparse.eval nodeValue5492 (mixedVector B) := by
    change mixedMoment B node5492 node5492Labels = _
    exact sound5492 B hB hF
  have h5493 : mixedVector B (Sum.inr 5493) = Sparse.eval nodeValue5493 (mixedVector B) := by
    change mixedMoment B node5493 node5493Labels = _
    exact sound5493 B hB hF
  have h5499 : mixedVector B (Sum.inr 5499) = Sparse.eval nodeValue5499 (mixedVector B) := by
    change mixedMoment B node5499 node5499Labels = _
    exact sound5499 B hB hF
  have h5500 : mixedVector B (Sum.inr 5500) = Sparse.eval nodeValue5500 (mixedVector B) := by
    change mixedMoment B node5500 node5500Labels = _
    exact sound5500 B hB hF
  have h5501 : mixedVector B (Sum.inr 5501) = Sparse.eval nodeValue5501 (mixedVector B) := by
    change mixedMoment B node5501 node5501Labels = _
    exact sound5501 B hB hF
  simpa only [sourceForm18, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5257, h5258, h5259, h5271, h5292, h5424, h5428, h5434, h5439, h5472, h5473, h5477, h5478, h5482, h5483, h5485, h5486, h5489, h5490, h5491, h5492, h5493, h5499, h5500, h5501, reducedSource18] using sourceEq18 B hB

theorem rowSound18 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row18 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck18, numericCheck18, reducedZero18 B hB hF, mul_zero]

theorem reducedZero19 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource19 (mixedVector B) = 0 := by
  have h2721 : mixedVector B (Sum.inr 2721) = Sparse.eval nodeValue2721 (mixedVector B) := by
    change mixedMoment B node2721 node2721Labels = _
    exact sound2721 B hB hF
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  have h2723 : mixedVector B (Sum.inr 2723) = Sparse.eval nodeValue2723 (mixedVector B) := by
    change mixedMoment B node2723 node2723Labels = _
    exact sound2723 B hB hF
  have h2739 : mixedVector B (Sum.inr 2739) = Sparse.eval nodeValue2739 (mixedVector B) := by
    change mixedMoment B node2739 node2739Labels = _
    exact sound2739 B hB hF
  have h2766 : mixedVector B (Sum.inr 2766) = Sparse.eval nodeValue2766 (mixedVector B) := by
    change mixedMoment B node2766 node2766Labels = _
    exact sound2766 B hB hF
  have h3838 : mixedVector B (Sum.inr 3838) = Sparse.eval nodeValue3838 (mixedVector B) := by
    change mixedMoment B node3838 node3838Labels = _
    exact sound3838 B hB hF
  have h3845 : mixedVector B (Sum.inr 3845) = Sparse.eval nodeValue3845 (mixedVector B) := by
    change mixedMoment B node3845 node3845Labels = _
    exact sound3845 B hB hF
  have h3852 : mixedVector B (Sum.inr 3852) = Sparse.eval nodeValue3852 (mixedVector B) := by
    change mixedMoment B node3852 node3852Labels = _
    exact sound3852 B hB hF
  have h3902 : mixedVector B (Sum.inr 3902) = Sparse.eval nodeValue3902 (mixedVector B) := by
    change mixedMoment B node3902 node3902Labels = _
    exact sound3902 B hB hF
  have h3957 : mixedVector B (Sum.inr 3957) = Sparse.eval nodeValue3957 (mixedVector B) := by
    change mixedMoment B node3957 node3957Labels = _
    exact sound3957 B hB hF
  have h3958 : mixedVector B (Sum.inr 3958) = Sparse.eval nodeValue3958 (mixedVector B) := by
    change mixedMoment B node3958 node3958Labels = _
    exact sound3958 B hB hF
  have h3961 : mixedVector B (Sum.inr 3961) = Sparse.eval nodeValue3961 (mixedVector B) := by
    change mixedMoment B node3961 node3961Labels = _
    exact sound3961 B hB hF
  have h3971 : mixedVector B (Sum.inr 3971) = Sparse.eval nodeValue3971 (mixedVector B) := by
    change mixedMoment B node3971 node3971Labels = _
    exact sound3971 B hB hF
  have h3974 : mixedVector B (Sum.inr 3974) = Sparse.eval nodeValue3974 (mixedVector B) := by
    change mixedMoment B node3974 node3974Labels = _
    exact sound3974 B hB hF
  have h3980 : mixedVector B (Sum.inr 3980) = Sparse.eval nodeValue3980 (mixedVector B) := by
    change mixedMoment B node3980 node3980Labels = _
    exact sound3980 B hB hF
  have h3981 : mixedVector B (Sum.inr 3981) = Sparse.eval nodeValue3981 (mixedVector B) := by
    change mixedMoment B node3981 node3981Labels = _
    exact sound3981 B hB hF
  have h3992 : mixedVector B (Sum.inr 3992) = Sparse.eval nodeValue3992 (mixedVector B) := by
    change mixedMoment B node3992 node3992Labels = _
    exact sound3992 B hB hF
  have h3999 : mixedVector B (Sum.inr 3999) = Sparse.eval nodeValue3999 (mixedVector B) := by
    change mixedMoment B node3999 node3999Labels = _
    exact sound3999 B hB hF
  have h4009 : mixedVector B (Sum.inr 4009) = Sparse.eval nodeValue4009 (mixedVector B) := by
    change mixedMoment B node4009 node4009Labels = _
    exact sound4009 B hB hF
  have h4010 : mixedVector B (Sum.inr 4010) = Sparse.eval nodeValue4010 (mixedVector B) := by
    change mixedMoment B node4010 node4010Labels = _
    exact sound4010 B hB hF
  have h4013 : mixedVector B (Sum.inr 4013) = Sparse.eval nodeValue4013 (mixedVector B) := by
    change mixedMoment B node4013 node4013Labels = _
    exact sound4013 B hB hF
  have h4014 : mixedVector B (Sum.inr 4014) = Sparse.eval nodeValue4014 (mixedVector B) := by
    change mixedMoment B node4014 node4014Labels = _
    exact sound4014 B hB hF
  have h4015 : mixedVector B (Sum.inr 4015) = Sparse.eval nodeValue4015 (mixedVector B) := by
    change mixedMoment B node4015 node4015Labels = _
    exact sound4015 B hB hF
  have h4018 : mixedVector B (Sum.inr 4018) = Sparse.eval nodeValue4018 (mixedVector B) := by
    change mixedMoment B node4018 node4018Labels = _
    exact sound4018 B hB hF
  have h4050 : mixedVector B (Sum.inr 4050) = Sparse.eval nodeValue4050 (mixedVector B) := by
    change mixedMoment B node4050 node4050Labels = _
    exact sound4050 B hB hF
  have h4052 : mixedVector B (Sum.inr 4052) = Sparse.eval nodeValue4052 (mixedVector B) := by
    change mixedMoment B node4052 node4052Labels = _
    exact sound4052 B hB hF
  have h4053 : mixedVector B (Sum.inr 4053) = Sparse.eval nodeValue4053 (mixedVector B) := by
    change mixedMoment B node4053 node4053Labels = _
    exact sound4053 B hB hF
  have h4054 : mixedVector B (Sum.inr 4054) = Sparse.eval nodeValue4054 (mixedVector B) := by
    change mixedMoment B node4054 node4054Labels = _
    exact sound4054 B hB hF
  have h4055 : mixedVector B (Sum.inr 4055) = Sparse.eval nodeValue4055 (mixedVector B) := by
    change mixedMoment B node4055 node4055Labels = _
    exact sound4055 B hB hF
  simpa only [sourceForm19, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2721, h2722, h2723, h2739, h2766, h3838, h3845, h3852, h3902, h3957, h3958, h3961, h3971, h3974, h3980, h3981, h3992, h3999, h4009, h4010, h4013, h4014, h4015, h4018, h4050, h4052, h4053, h4054, h4055, reducedSource19] using sourceEq19 B hB

theorem rowSound19 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row19 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck19, numericCheck19, reducedZero19 B hB hF, mul_zero]

theorem reducedZero20 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource20 (mixedVector B) = 0 := by
  have h5431 : mixedVector B (Sum.inr 5431) = Sparse.eval nodeValue5431 (mixedVector B) := by
    change mixedMoment B node5431 node5431Labels = _
    exact sound5431 B hB hF
  have h5432 : mixedVector B (Sum.inr 5432) = Sparse.eval nodeValue5432 (mixedVector B) := by
    change mixedMoment B node5432 node5432Labels = _
    exact sound5432 B hB hF
  have h5433 : mixedVector B (Sum.inr 5433) = Sparse.eval nodeValue5433 (mixedVector B) := by
    change mixedMoment B node5433 node5433Labels = _
    exact sound5433 B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434 B hB hF
  have h5435 : mixedVector B (Sum.inr 5435) = Sparse.eval nodeValue5435 (mixedVector B) := by
    change mixedMoment B node5435 node5435Labels = _
    exact sound5435 B hB hF
  have h5438 : mixedVector B (Sum.inr 5438) = Sparse.eval nodeValue5438 (mixedVector B) := by
    change mixedMoment B node5438 node5438Labels = _
    exact sound5438 B hB hF
  have h5440 : mixedVector B (Sum.inr 5440) = Sparse.eval nodeValue5440 (mixedVector B) := by
    change mixedMoment B node5440 node5440Labels = _
    exact sound5440 B hB hF
  have h5450 : mixedVector B (Sum.inr 5450) = Sparse.eval nodeValue5450 (mixedVector B) := by
    change mixedMoment B node5450 node5450Labels = _
    exact sound5450 B hB hF
  have h5454 : mixedVector B (Sum.inr 5454) = Sparse.eval nodeValue5454 (mixedVector B) := by
    change mixedMoment B node5454 node5454Labels = _
    exact sound5454 B hB hF
  have h5481 : mixedVector B (Sum.inr 5481) = Sparse.eval nodeValue5481 (mixedVector B) := by
    change mixedMoment B node5481 node5481Labels = _
    exact sound5481 B hB hF
  have h5484 : mixedVector B (Sum.inr 5484) = Sparse.eval nodeValue5484 (mixedVector B) := by
    change mixedMoment B node5484 node5484Labels = _
    exact sound5484 B hB hF
  have h5489 : mixedVector B (Sum.inr 5489) = Sparse.eval nodeValue5489 (mixedVector B) := by
    change mixedMoment B node5489 node5489Labels = _
    exact sound5489 B hB hF
  have h5490 : mixedVector B (Sum.inr 5490) = Sparse.eval nodeValue5490 (mixedVector B) := by
    change mixedMoment B node5490 node5490Labels = _
    exact sound5490 B hB hF
  have h5492 : mixedVector B (Sum.inr 5492) = Sparse.eval nodeValue5492 (mixedVector B) := by
    change mixedMoment B node5492 node5492Labels = _
    exact sound5492 B hB hF
  have h5493 : mixedVector B (Sum.inr 5493) = Sparse.eval nodeValue5493 (mixedVector B) := by
    change mixedMoment B node5493 node5493Labels = _
    exact sound5493 B hB hF
  have h5495 : mixedVector B (Sum.inr 5495) = Sparse.eval nodeValue5495 (mixedVector B) := by
    change mixedMoment B node5495 node5495Labels = _
    exact sound5495 B hB hF
  simpa only [sourceForm20, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5431, h5432, h5433, h5434, h5435, h5438, h5440, h5450, h5454, h5481, h5484, h5489, h5490, h5492, h5493, h5495, reducedSource20] using sourceEq20 B hB

theorem rowSound20 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row20 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck20, numericCheck20, reducedZero20 B hB hF, mul_zero]

theorem reducedZero21 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource21 (mixedVector B) = 0 := by
  have h5304 : mixedVector B (Sum.inr 5304) = Sparse.eval nodeValue5304 (mixedVector B) := by
    change mixedMoment B node5304 node5304Labels = _
    exact sound5304 B hB hF
  have h5305 : mixedVector B (Sum.inr 5305) = Sparse.eval nodeValue5305 (mixedVector B) := by
    change mixedMoment B node5305 node5305Labels = _
    exact sound5305 B hB hF
  have h5310 : mixedVector B (Sum.inr 5310) = Sparse.eval nodeValue5310 (mixedVector B) := by
    change mixedMoment B node5310 node5310Labels = _
    exact sound5310 B hB hF
  have h5451 : mixedVector B (Sum.inr 5451) = Sparse.eval nodeValue5451 (mixedVector B) := by
    change mixedMoment B node5451 node5451Labels = _
    exact sound5451 B hB hF
  have h5455 : mixedVector B (Sum.inr 5455) = Sparse.eval nodeValue5455 (mixedVector B) := by
    change mixedMoment B node5455 node5455Labels = _
    exact sound5455 B hB hF
  have h5484 : mixedVector B (Sum.inr 5484) = Sparse.eval nodeValue5484 (mixedVector B) := by
    change mixedMoment B node5484 node5484Labels = _
    exact sound5484 B hB hF
  have h5492 : mixedVector B (Sum.inr 5492) = Sparse.eval nodeValue5492 (mixedVector B) := by
    change mixedMoment B node5492 node5492Labels = _
    exact sound5492 B hB hF
  have h5495 : mixedVector B (Sum.inr 5495) = Sparse.eval nodeValue5495 (mixedVector B) := by
    change mixedMoment B node5495 node5495Labels = _
    exact sound5495 B hB hF
  simpa only [sourceForm21, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5304, h5305, h5310, h5451, h5455, h5484, h5492, h5495, reducedSource21] using sourceEq21 B hB

theorem rowSound21 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row21 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck21, numericCheck21, reducedZero21 B hB hF, mul_zero]

theorem reducedZero22 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource22 (mixedVector B) = 0 := by
  have h4096 : mixedVector B (Sum.inr 4096) = Sparse.eval nodeValue4096 (mixedVector B) := by
    change mixedMoment B node4096 node4096Labels = _
    exact sound4096 B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292 B hB hF
  have h5293 : mixedVector B (Sum.inr 5293) = Sparse.eval nodeValue5293 (mixedVector B) := by
    change mixedMoment B node5293 node5293Labels = _
    exact sound5293 B hB hF
  have h5306 : mixedVector B (Sum.inr 5306) = Sparse.eval nodeValue5306 (mixedVector B) := by
    change mixedMoment B node5306 node5306Labels = _
    exact sound5306 B hB hF
  have h5482 : mixedVector B (Sum.inr 5482) = Sparse.eval nodeValue5482 (mixedVector B) := by
    change mixedMoment B node5482 node5482Labels = _
    exact sound5482 B hB hF
  have h5483 : mixedVector B (Sum.inr 5483) = Sparse.eval nodeValue5483 (mixedVector B) := by
    change mixedMoment B node5483 node5483Labels = _
    exact sound5483 B hB hF
  have h5485 : mixedVector B (Sum.inr 5485) = Sparse.eval nodeValue5485 (mixedVector B) := by
    change mixedMoment B node5485 node5485Labels = _
    exact sound5485 B hB hF
  have h5486 : mixedVector B (Sum.inr 5486) = Sparse.eval nodeValue5486 (mixedVector B) := by
    change mixedMoment B node5486 node5486Labels = _
    exact sound5486 B hB hF
  have h5487 : mixedVector B (Sum.inr 5487) = Sparse.eval nodeValue5487 (mixedVector B) := by
    change mixedMoment B node5487 node5487Labels = _
    exact sound5487 B hB hF
  have h5490 : mixedVector B (Sum.inr 5490) = Sparse.eval nodeValue5490 (mixedVector B) := by
    change mixedMoment B node5490 node5490Labels = _
    exact sound5490 B hB hF
  have h5491 : mixedVector B (Sum.inr 5491) = Sparse.eval nodeValue5491 (mixedVector B) := by
    change mixedMoment B node5491 node5491Labels = _
    exact sound5491 B hB hF
  have h5492 : mixedVector B (Sum.inr 5492) = Sparse.eval nodeValue5492 (mixedVector B) := by
    change mixedMoment B node5492 node5492Labels = _
    exact sound5492 B hB hF
  have h5499 : mixedVector B (Sum.inr 5499) = Sparse.eval nodeValue5499 (mixedVector B) := by
    change mixedMoment B node5499 node5499Labels = _
    exact sound5499 B hB hF
  have h5501 : mixedVector B (Sum.inr 5501) = Sparse.eval nodeValue5501 (mixedVector B) := by
    change mixedMoment B node5501 node5501Labels = _
    exact sound5501 B hB hF
  simpa only [sourceForm22, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4096, h5292, h5293, h5306, h5482, h5483, h5485, h5486, h5487, h5490, h5491, h5492, h5499, h5501, reducedSource22] using sourceEq22 B hB

theorem rowSound22 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row22 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck22, numericCheck22, reducedZero22 B hB hF, mul_zero]

theorem reducedZero23 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource23 (mixedVector B) = 0 := by
  have h4093 : mixedVector B (Sum.inr 4093) = Sparse.eval nodeValue4093 (mixedVector B) := by
    change mixedMoment B node4093 node4093Labels = _
    exact sound4093 B hB hF
  have h5440 : mixedVector B (Sum.inr 5440) = Sparse.eval nodeValue5440 (mixedVector B) := by
    change mixedMoment B node5440 node5440Labels = _
    exact sound5440 B hB hF
  have h5442 : mixedVector B (Sum.inr 5442) = Sparse.eval nodeValue5442 (mixedVector B) := by
    change mixedMoment B node5442 node5442Labels = _
    exact sound5442 B hB hF
  have h5450 : mixedVector B (Sum.inr 5450) = Sparse.eval nodeValue5450 (mixedVector B) := by
    change mixedMoment B node5450 node5450Labels = _
    exact sound5450 B hB hF
  have h5451 : mixedVector B (Sum.inr 5451) = Sparse.eval nodeValue5451 (mixedVector B) := by
    change mixedMoment B node5451 node5451Labels = _
    exact sound5451 B hB hF
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
  have h5490 : mixedVector B (Sum.inr 5490) = Sparse.eval nodeValue5490 (mixedVector B) := by
    change mixedMoment B node5490 node5490Labels = _
    exact sound5490 B hB hF
  have h5492 : mixedVector B (Sum.inr 5492) = Sparse.eval nodeValue5492 (mixedVector B) := by
    change mixedMoment B node5492 node5492Labels = _
    exact sound5492 B hB hF
  have h5493 : mixedVector B (Sum.inr 5493) = Sparse.eval nodeValue5493 (mixedVector B) := by
    change mixedMoment B node5493 node5493Labels = _
    exact sound5493 B hB hF
  have h5495 : mixedVector B (Sum.inr 5495) = Sparse.eval nodeValue5495 (mixedVector B) := by
    change mixedMoment B node5495 node5495Labels = _
    exact sound5495 B hB hF
  simpa only [sourceForm23, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4093, h5440, h5442, h5450, h5451, h5452, h5453, h5454, h5485, h5489, h5490, h5492, h5493, h5495, reducedSource23] using sourceEq23 B hB

theorem rowSound23 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row23 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck23, numericCheck23, reducedZero23 B hB hF, mul_zero]

theorem reducedZero24 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource24 (mixedVector B) = 0 := by
  have h4093 : mixedVector B (Sum.inr 4093) = Sparse.eval nodeValue4093 (mixedVector B) := by
    change mixedMoment B node4093 node4093Labels = _
    exact sound4093 B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292 B hB hF
  have h5293 : mixedVector B (Sum.inr 5293) = Sparse.eval nodeValue5293 (mixedVector B) := by
    change mixedMoment B node5293 node5293Labels = _
    exact sound5293 B hB hF
  have h5294 : mixedVector B (Sum.inr 5294) = Sparse.eval nodeValue5294 (mixedVector B) := by
    change mixedMoment B node5294 node5294Labels = _
    exact sound5294 B hB hF
  have h5307 : mixedVector B (Sum.inr 5307) = Sparse.eval nodeValue5307 (mixedVector B) := by
    change mixedMoment B node5307 node5307Labels = _
    exact sound5307 B hB hF
  have h5433 : mixedVector B (Sum.inr 5433) = Sparse.eval nodeValue5433 (mixedVector B) := by
    change mixedMoment B node5433 node5433Labels = _
    exact sound5433 B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434 B hB hF
  have h5435 : mixedVector B (Sum.inr 5435) = Sparse.eval nodeValue5435 (mixedVector B) := by
    change mixedMoment B node5435 node5435Labels = _
    exact sound5435 B hB hF
  have h5440 : mixedVector B (Sum.inr 5440) = Sparse.eval nodeValue5440 (mixedVector B) := by
    change mixedMoment B node5440 node5440Labels = _
    exact sound5440 B hB hF
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
  have h5453 : mixedVector B (Sum.inr 5453) = Sparse.eval nodeValue5453 (mixedVector B) := by
    change mixedMoment B node5453 node5453Labels = _
    exact sound5453 B hB hF
  have h5454 : mixedVector B (Sum.inr 5454) = Sparse.eval nodeValue5454 (mixedVector B) := by
    change mixedMoment B node5454 node5454Labels = _
    exact sound5454 B hB hF
  have h5455 : mixedVector B (Sum.inr 5455) = Sparse.eval nodeValue5455 (mixedVector B) := by
    change mixedMoment B node5455 node5455Labels = _
    exact sound5455 B hB hF
  have h5490 : mixedVector B (Sum.inr 5490) = Sparse.eval nodeValue5490 (mixedVector B) := by
    change mixedMoment B node5490 node5490Labels = _
    exact sound5490 B hB hF
  have h5492 : mixedVector B (Sum.inr 5492) = Sparse.eval nodeValue5492 (mixedVector B) := by
    change mixedMoment B node5492 node5492Labels = _
    exact sound5492 B hB hF
  have h5493 : mixedVector B (Sum.inr 5493) = Sparse.eval nodeValue5493 (mixedVector B) := by
    change mixedMoment B node5493 node5493Labels = _
    exact sound5493 B hB hF
  have h5495 : mixedVector B (Sum.inr 5495) = Sparse.eval nodeValue5495 (mixedVector B) := by
    change mixedMoment B node5495 node5495Labels = _
    exact sound5495 B hB hF
  simpa only [sourceForm24, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4093, h5292, h5293, h5294, h5307, h5433, h5434, h5435, h5440, h5443, h5450, h5451, h5452, h5453, h5454, h5455, h5490, h5492, h5493, h5495, reducedSource24] using sourceEq24 B hB

theorem rowSound24 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row24 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck24, numericCheck24, reducedZero24 B hB hF, mul_zero]

theorem reducedZero25 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource25 (mixedVector B) = 0 := by
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  have h4093 : mixedVector B (Sum.inr 4093) = Sparse.eval nodeValue4093 (mixedVector B) := by
    change mixedMoment B node4093 node4093Labels = _
    exact sound4093 B hB hF
  have h4094 : mixedVector B (Sum.inr 4094) = Sparse.eval nodeValue4094 (mixedVector B) := by
    change mixedMoment B node4094 node4094Labels = _
    exact sound4094 B hB hF
  have h4096 : mixedVector B (Sum.inr 4096) = Sparse.eval nodeValue4096 (mixedVector B) := by
    change mixedMoment B node4096 node4096Labels = _
    exact sound4096 B hB hF
  have h4097 : mixedVector B (Sum.inr 4097) = Sparse.eval nodeValue4097 (mixedVector B) := by
    change mixedMoment B node4097 node4097Labels = _
    exact sound4097 B hB hF
  simpa only [sourceForm25, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4083, h4084, h4091, h4092, h4093, h4094, h4096, h4097, reducedSource25] using sourceEq25 B hB

theorem rowSound25 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row25 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck25, numericCheck25, reducedZero25 B hB hF, mul_zero]

theorem reducedZero26 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource26 (mixedVector B) = 0 := by
  have h5405 : mixedVector B (Sum.inr 5405) = Sparse.eval nodeValue5405 (mixedVector B) := by
    change mixedMoment B node5405 node5405Labels = _
    exact sound5405 B hB hF
  have h5452 : mixedVector B (Sum.inr 5452) = Sparse.eval nodeValue5452 (mixedVector B) := by
    change mixedMoment B node5452 node5452Labels = _
    exact sound5452 B hB hF
  have h5482 : mixedVector B (Sum.inr 5482) = Sparse.eval nodeValue5482 (mixedVector B) := by
    change mixedMoment B node5482 node5482Labels = _
    exact sound5482 B hB hF
  have h5489 : mixedVector B (Sum.inr 5489) = Sparse.eval nodeValue5489 (mixedVector B) := by
    change mixedMoment B node5489 node5489Labels = _
    exact sound5489 B hB hF
  have h5499 : mixedVector B (Sum.inr 5499) = Sparse.eval nodeValue5499 (mixedVector B) := by
    change mixedMoment B node5499 node5499Labels = _
    exact sound5499 B hB hF
  simpa only [sourceForm26, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5405, h5452, h5482, h5489, h5499, reducedSource26] using sourceEq26 B hB

theorem rowSound26 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row26 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck26, numericCheck26, reducedZero26 B hB hF, mul_zero]

theorem reducedZero27 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource27 (mixedVector B) = 0 := by
  have h5423 : mixedVector B (Sum.inr 5423) = Sparse.eval nodeValue5423 (mixedVector B) := by
    change mixedMoment B node5423 node5423Labels = _
    exact sound5423 B hB hF
  have h5424 : mixedVector B (Sum.inr 5424) = Sparse.eval nodeValue5424 (mixedVector B) := by
    change mixedMoment B node5424 node5424Labels = _
    exact sound5424 B hB hF
  have h5433 : mixedVector B (Sum.inr 5433) = Sparse.eval nodeValue5433 (mixedVector B) := by
    change mixedMoment B node5433 node5433Labels = _
    exact sound5433 B hB hF
  have h5477 : mixedVector B (Sum.inr 5477) = Sparse.eval nodeValue5477 (mixedVector B) := by
    change mixedMoment B node5477 node5477Labels = _
    exact sound5477 B hB hF
  have h5478 : mixedVector B (Sum.inr 5478) = Sparse.eval nodeValue5478 (mixedVector B) := by
    change mixedMoment B node5478 node5478Labels = _
    exact sound5478 B hB hF
  have h5482 : mixedVector B (Sum.inr 5482) = Sparse.eval nodeValue5482 (mixedVector B) := by
    change mixedMoment B node5482 node5482Labels = _
    exact sound5482 B hB hF
  have h5490 : mixedVector B (Sum.inr 5490) = Sparse.eval nodeValue5490 (mixedVector B) := by
    change mixedMoment B node5490 node5490Labels = _
    exact sound5490 B hB hF
  have h5497 : mixedVector B (Sum.inr 5497) = Sparse.eval nodeValue5497 (mixedVector B) := by
    change mixedMoment B node5497 node5497Labels = _
    exact sound5497 B hB hF
  have h5499 : mixedVector B (Sum.inr 5499) = Sparse.eval nodeValue5499 (mixedVector B) := by
    change mixedMoment B node5499 node5499Labels = _
    exact sound5499 B hB hF
  have h5500 : mixedVector B (Sum.inr 5500) = Sparse.eval nodeValue5500 (mixedVector B) := by
    change mixedMoment B node5500 node5500Labels = _
    exact sound5500 B hB hF
  have h5501 : mixedVector B (Sum.inr 5501) = Sparse.eval nodeValue5501 (mixedVector B) := by
    change mixedMoment B node5501 node5501Labels = _
    exact sound5501 B hB hF
  simpa only [sourceForm27, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5423, h5424, h5433, h5477, h5478, h5482, h5490, h5497, h5499, h5500, h5501, reducedSource27] using sourceEq27 B hB

theorem rowSound27 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row27 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck27, numericCheck27, reducedZero27 B hB hF, mul_zero]

theorem reducedZero28 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource28 (mixedVector B) = 0 := by
  have h4096 : mixedVector B (Sum.inr 4096) = Sparse.eval nodeValue4096 (mixedVector B) := by
    change mixedMoment B node4096 node4096Labels = _
    exact sound4096 B hB hF
  have h5433 : mixedVector B (Sum.inr 5433) = Sparse.eval nodeValue5433 (mixedVector B) := by
    change mixedMoment B node5433 node5433Labels = _
    exact sound5433 B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434 B hB hF
  have h5439 : mixedVector B (Sum.inr 5439) = Sparse.eval nodeValue5439 (mixedVector B) := by
    change mixedMoment B node5439 node5439Labels = _
    exact sound5439 B hB hF
  have h5452 : mixedVector B (Sum.inr 5452) = Sparse.eval nodeValue5452 (mixedVector B) := by
    change mixedMoment B node5452 node5452Labels = _
    exact sound5452 B hB hF
  have h5482 : mixedVector B (Sum.inr 5482) = Sparse.eval nodeValue5482 (mixedVector B) := by
    change mixedMoment B node5482 node5482Labels = _
    exact sound5482 B hB hF
  have h5483 : mixedVector B (Sum.inr 5483) = Sparse.eval nodeValue5483 (mixedVector B) := by
    change mixedMoment B node5483 node5483Labels = _
    exact sound5483 B hB hF
  have h5485 : mixedVector B (Sum.inr 5485) = Sparse.eval nodeValue5485 (mixedVector B) := by
    change mixedMoment B node5485 node5485Labels = _
    exact sound5485 B hB hF
  have h5486 : mixedVector B (Sum.inr 5486) = Sparse.eval nodeValue5486 (mixedVector B) := by
    change mixedMoment B node5486 node5486Labels = _
    exact sound5486 B hB hF
  have h5489 : mixedVector B (Sum.inr 5489) = Sparse.eval nodeValue5489 (mixedVector B) := by
    change mixedMoment B node5489 node5489Labels = _
    exact sound5489 B hB hF
  have h5490 : mixedVector B (Sum.inr 5490) = Sparse.eval nodeValue5490 (mixedVector B) := by
    change mixedMoment B node5490 node5490Labels = _
    exact sound5490 B hB hF
  have h5493 : mixedVector B (Sum.inr 5493) = Sparse.eval nodeValue5493 (mixedVector B) := by
    change mixedMoment B node5493 node5493Labels = _
    exact sound5493 B hB hF
  have h5497 : mixedVector B (Sum.inr 5497) = Sparse.eval nodeValue5497 (mixedVector B) := by
    change mixedMoment B node5497 node5497Labels = _
    exact sound5497 B hB hF
  have h5498 : mixedVector B (Sum.inr 5498) = Sparse.eval nodeValue5498 (mixedVector B) := by
    change mixedMoment B node5498 node5498Labels = _
    exact sound5498 B hB hF
  have h5499 : mixedVector B (Sum.inr 5499) = Sparse.eval nodeValue5499 (mixedVector B) := by
    change mixedMoment B node5499 node5499Labels = _
    exact sound5499 B hB hF
  have h5500 : mixedVector B (Sum.inr 5500) = Sparse.eval nodeValue5500 (mixedVector B) := by
    change mixedMoment B node5500 node5500Labels = _
    exact sound5500 B hB hF
  have h5501 : mixedVector B (Sum.inr 5501) = Sparse.eval nodeValue5501 (mixedVector B) := by
    change mixedMoment B node5501 node5501Labels = _
    exact sound5501 B hB hF
  simpa only [sourceForm28, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4096, h5433, h5434, h5439, h5452, h5482, h5483, h5485, h5486, h5489, h5490, h5493, h5497, h5498, h5499, h5500, h5501, reducedSource28] using sourceEq28 B hB

theorem rowSound28 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row28 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck28, numericCheck28, reducedZero28 B hB hF, mul_zero]

theorem reducedZero29 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource29 (mixedVector B) = 0 := by
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  have h4093 : mixedVector B (Sum.inr 4093) = Sparse.eval nodeValue4093 (mixedVector B) := by
    change mixedMoment B node4093 node4093Labels = _
    exact sound4093 B hB hF
  have h4095 : mixedVector B (Sum.inr 4095) = Sparse.eval nodeValue4095 (mixedVector B) := by
    change mixedMoment B node4095 node4095Labels = _
    exact sound4095 B hB hF
  have h4096 : mixedVector B (Sum.inr 4096) = Sparse.eval nodeValue4096 (mixedVector B) := by
    change mixedMoment B node4096 node4096Labels = _
    exact sound4096 B hB hF
  have h4097 : mixedVector B (Sum.inr 4097) = Sparse.eval nodeValue4097 (mixedVector B) := by
    change mixedMoment B node4097 node4097Labels = _
    exact sound4097 B hB hF
  simpa only [sourceForm29, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4091, h4092, h4093, h4095, h4096, h4097, reducedSource29] using sourceEq29 B hB

theorem rowSound29 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row29 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck29, numericCheck29, reducedZero29 B hB hF, mul_zero]

theorem reducedZero30 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource30 (mixedVector B) = 0 := by
  have h1092 : mixedVector B (Sum.inr 1092) = Sparse.eval nodeValue1092 (mixedVector B) := by
    change mixedMoment B node1092 node1092Labels = _
    exact sound1092 B hB hF
  have h2063 : mixedVector B (Sum.inr 2063) = Sparse.eval nodeValue2063 (mixedVector B) := by
    change mixedMoment B node2063 node2063Labels = _
    exact sound2063 B hB hF
  have h2285 : mixedVector B (Sum.inr 2285) = Sparse.eval nodeValue2285 (mixedVector B) := by
    change mixedMoment B node2285 node2285Labels = _
    exact sound2285 B hB hF
  have h2294 : mixedVector B (Sum.inr 2294) = Sparse.eval nodeValue2294 (mixedVector B) := by
    change mixedMoment B node2294 node2294Labels = _
    exact sound2294 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm32, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1092, h2063, h2285, h2294, h4085, reducedSource30] using sourceEq32 B hB

theorem rowSound30 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row30 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck30, numericCheck30, reducedZero30 B hB hF, mul_zero]

theorem reducedZero31 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource31 (mixedVector B) = 0 := by
  have h1067 : mixedVector B (Sum.inr 1067) = Sparse.eval nodeValue1067 (mixedVector B) := by
    change mixedMoment B node1067 node1067Labels = _
    exact sound1067 B hB hF
  have h1069 : mixedVector B (Sum.inr 1069) = Sparse.eval nodeValue1069 (mixedVector B) := by
    change mixedMoment B node1069 node1069Labels = _
    exact sound1069 B hB hF
  have h1092 : mixedVector B (Sum.inr 1092) = Sparse.eval nodeValue1092 (mixedVector B) := by
    change mixedMoment B node1092 node1092Labels = _
    exact sound1092 B hB hF
  have h2285 : mixedVector B (Sum.inr 2285) = Sparse.eval nodeValue2285 (mixedVector B) := by
    change mixedMoment B node2285 node2285Labels = _
    exact sound2285 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm33, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1067, h1069, h1092, h2285, h4085, reducedSource31] using sourceEq33 B hB

theorem rowSound31 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row31 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck31, numericCheck31, reducedZero31 B hB hF, mul_zero]

theorem sourceRowsAt16 : MixedData.sourceRows (16 : Fin 2425) =
    MixedData.row16 := by decide +kernel

theorem sourceRowsAt17 : MixedData.sourceRows (17 : Fin 2425) =
    MixedData.row17 := by decide +kernel

theorem sourceRowsAt18 : MixedData.sourceRows (18 : Fin 2425) =
    MixedData.row18 := by decide +kernel

theorem sourceRowsAt19 : MixedData.sourceRows (19 : Fin 2425) =
    MixedData.row19 := by decide +kernel

theorem sourceRowsAt20 : MixedData.sourceRows (20 : Fin 2425) =
    MixedData.row20 := by decide +kernel

theorem sourceRowsAt21 : MixedData.sourceRows (21 : Fin 2425) =
    MixedData.row21 := by decide +kernel

theorem sourceRowsAt22 : MixedData.sourceRows (22 : Fin 2425) =
    MixedData.row22 := by decide +kernel

theorem sourceRowsAt23 : MixedData.sourceRows (23 : Fin 2425) =
    MixedData.row23 := by decide +kernel

theorem sourceRowsAt24 : MixedData.sourceRows (24 : Fin 2425) =
    MixedData.row24 := by decide +kernel

theorem sourceRowsAt25 : MixedData.sourceRows (25 : Fin 2425) =
    MixedData.row25 := by decide +kernel

theorem sourceRowsAt26 : MixedData.sourceRows (26 : Fin 2425) =
    MixedData.row26 := by decide +kernel

theorem sourceRowsAt27 : MixedData.sourceRows (27 : Fin 2425) =
    MixedData.row27 := by decide +kernel

theorem sourceRowsAt28 : MixedData.sourceRows (28 : Fin 2425) =
    MixedData.row28 := by decide +kernel

theorem sourceRowsAt29 : MixedData.sourceRows (29 : Fin 2425) =
    MixedData.row29 := by decide +kernel

theorem sourceRowsAt30 : MixedData.sourceRows (30 : Fin 2425) =
    MixedData.row30 := by decide +kernel

theorem sourceRowsAt31 : MixedData.sourceRows (31 : Fin 2425) =
    MixedData.row31 := by decide +kernel

theorem chunkSound1 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 1) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 16 ∨ k.val = 17 ∨ k.val = 18 ∨ k.val = 19 ∨ k.val = 20 ∨ k.val = 21 ∨ k.val = 22 ∨ k.val = 23 ∨ k.val = 24 ∨ k.val = 25 ∨ k.val = 26 ∨ k.val = 27 ∨ k.val = 28 ∨ k.val = 29 ∨ k.val = 30 ∨ k.val = 31 := by omega
  rcases heq with h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31
  · have he : k = (16 : Fin 2425) := Fin.ext h16
    subst k
    rw [sourceRowsAt16]
    exact rowSound16 B hB hF
  · have he : k = (17 : Fin 2425) := Fin.ext h17
    subst k
    rw [sourceRowsAt17]
    exact rowSound17 B hB hF
  · have he : k = (18 : Fin 2425) := Fin.ext h18
    subst k
    rw [sourceRowsAt18]
    exact rowSound18 B hB hF
  · have he : k = (19 : Fin 2425) := Fin.ext h19
    subst k
    rw [sourceRowsAt19]
    exact rowSound19 B hB hF
  · have he : k = (20 : Fin 2425) := Fin.ext h20
    subst k
    rw [sourceRowsAt20]
    exact rowSound20 B hB hF
  · have he : k = (21 : Fin 2425) := Fin.ext h21
    subst k
    rw [sourceRowsAt21]
    exact rowSound21 B hB hF
  · have he : k = (22 : Fin 2425) := Fin.ext h22
    subst k
    rw [sourceRowsAt22]
    exact rowSound22 B hB hF
  · have he : k = (23 : Fin 2425) := Fin.ext h23
    subst k
    rw [sourceRowsAt23]
    exact rowSound23 B hB hF
  · have he : k = (24 : Fin 2425) := Fin.ext h24
    subst k
    rw [sourceRowsAt24]
    exact rowSound24 B hB hF
  · have he : k = (25 : Fin 2425) := Fin.ext h25
    subst k
    rw [sourceRowsAt25]
    exact rowSound25 B hB hF
  · have he : k = (26 : Fin 2425) := Fin.ext h26
    subst k
    rw [sourceRowsAt26]
    exact rowSound26 B hB hF
  · have he : k = (27 : Fin 2425) := Fin.ext h27
    subst k
    rw [sourceRowsAt27]
    exact rowSound27 B hB hF
  · have he : k = (28 : Fin 2425) := Fin.ext h28
    subst k
    rw [sourceRowsAt28]
    exact rowSound28 B hB hF
  · have he : k = (29 : Fin 2425) := Fin.ext h29
    subst k
    rw [sourceRowsAt29]
    exact rowSound29 B hB hF
  · have he : k = (30 : Fin 2425) := Fin.ext h30
    subst k
    rw [sourceRowsAt30]
    exact rowSound30 B hB hF
  · have he : k = (31 : Fin 2425) := Fin.ext h31
    subst k
    rw [sourceRowsAt31]
    exact rowSound31 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
