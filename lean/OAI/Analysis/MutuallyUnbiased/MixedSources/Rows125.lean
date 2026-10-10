import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic125
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound53
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources78

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2000 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2000 (mixedVector B) = 0 := by
  have h1665 : mixedVector B (Sum.inr 1665) = Sparse.eval nodeValue1665 (mixedVector B) := by
    change mixedMoment B node1665 node1665Labels = _
    exact sound1665 B hB hF
  have h1675 : mixedVector B (Sum.inr 1675) = Sparse.eval nodeValue1675 (mixedVector B) := by
    change mixedMoment B node1675 node1675Labels = _
    exact sound1675 B hB hF
  have h1676 : mixedVector B (Sum.inr 1676) = Sparse.eval nodeValue1676 (mixedVector B) := by
    change mixedMoment B node1676 node1676Labels = _
    exact sound1676 B hB hF
  have h1682 : mixedVector B (Sum.inr 1682) = Sparse.eval nodeValue1682 (mixedVector B) := by
    change mixedMoment B node1682 node1682Labels = _
    exact sound1682 B hB hF
  have h1728 : mixedVector B (Sum.inr 1728) = Sparse.eval nodeValue1728 (mixedVector B) := by
    change mixedMoment B node1728 node1728Labels = _
    exact sound1728 B hB hF
  have h2142 : mixedVector B (Sum.inr 2142) = Sparse.eval nodeValue2142 (mixedVector B) := by
    change mixedMoment B node2142 node2142Labels = _
    exact sound2142 B hB hF
  have h2152 : mixedVector B (Sum.inr 2152) = Sparse.eval nodeValue2152 (mixedVector B) := by
    change mixedMoment B node2152 node2152Labels = _
    exact sound2152 B hB hF
  have h2153 : mixedVector B (Sum.inr 2153) = Sparse.eval nodeValue2153 (mixedVector B) := by
    change mixedMoment B node2153 node2153Labels = _
    exact sound2153 B hB hF
  have h2158 : mixedVector B (Sum.inr 2158) = Sparse.eval nodeValue2158 (mixedVector B) := by
    change mixedMoment B node2158 node2158Labels = _
    exact sound2158 B hB hF
  have h2174 : mixedVector B (Sum.inr 2174) = Sparse.eval nodeValue2174 (mixedVector B) := by
    change mixedMoment B node2174 node2174Labels = _
    exact sound2174 B hB hF
  have h2175 : mixedVector B (Sum.inr 2175) = Sparse.eval nodeValue2175 (mixedVector B) := by
    change mixedMoment B node2175 node2175Labels = _
    exact sound2175 B hB hF
  have h2178 : mixedVector B (Sum.inr 2178) = Sparse.eval nodeValue2178 (mixedVector B) := by
    change mixedMoment B node2178 node2178Labels = _
    exact sound2178 B hB hF
  have h2191 : mixedVector B (Sum.inr 2191) = Sparse.eval nodeValue2191 (mixedVector B) := by
    change mixedMoment B node2191 node2191Labels = _
    exact sound2191 B hB hF
  have h2192 : mixedVector B (Sum.inr 2192) = Sparse.eval nodeValue2192 (mixedVector B) := by
    change mixedMoment B node2192 node2192Labels = _
    exact sound2192 B hB hF
  have h2205 : mixedVector B (Sum.inr 2205) = Sparse.eval nodeValue2205 (mixedVector B) := by
    change mixedMoment B node2205 node2205Labels = _
    exact sound2205 B hB hF
  have h2206 : mixedVector B (Sum.inr 2206) = Sparse.eval nodeValue2206 (mixedVector B) := by
    change mixedMoment B node2206 node2206Labels = _
    exact sound2206 B hB hF
  have h2207 : mixedVector B (Sum.inr 2207) = Sparse.eval nodeValue2207 (mixedVector B) := by
    change mixedMoment B node2207 node2207Labels = _
    exact sound2207 B hB hF
  have h2216 : mixedVector B (Sum.inr 2216) = Sparse.eval nodeValue2216 (mixedVector B) := by
    change mixedMoment B node2216 node2216Labels = _
    exact sound2216 B hB hF
  have h2217 : mixedVector B (Sum.inr 2217) = Sparse.eval nodeValue2217 (mixedVector B) := by
    change mixedMoment B node2217 node2217Labels = _
    exact sound2217 B hB hF
  have h2229 : mixedVector B (Sum.inr 2229) = Sparse.eval nodeValue2229 (mixedVector B) := by
    change mixedMoment B node2229 node2229Labels = _
    exact sound2229 B hB hF
  have h2230 : mixedVector B (Sum.inr 2230) = Sparse.eval nodeValue2230 (mixedVector B) := by
    change mixedMoment B node2230 node2230Labels = _
    exact sound2230 B hB hF
  have h2265 : mixedVector B (Sum.inr 2265) = Sparse.eval nodeValue2265 (mixedVector B) := by
    change mixedMoment B node2265 node2265Labels = _
    exact sound2265 B hB hF
  have h2266 : mixedVector B (Sum.inr 2266) = Sparse.eval nodeValue2266 (mixedVector B) := by
    change mixedMoment B node2266 node2266Labels = _
    exact sound2266 B hB hF
  have h2293 : mixedVector B (Sum.inr 2293) = Sparse.eval nodeValue2293 (mixedVector B) := by
    change mixedMoment B node2293 node2293Labels = _
    exact sound2293 B hB hF
  have h2673 : mixedVector B (Sum.inr 2673) = Sparse.eval nodeValue2673 (mixedVector B) := by
    change mixedMoment B node2673 node2673Labels = _
    exact sound2673 B hB hF
  have h2695 : mixedVector B (Sum.inr 2695) = Sparse.eval nodeValue2695 (mixedVector B) := by
    change mixedMoment B node2695 node2695Labels = _
    exact sound2695 B hB hF
  have h2723 : mixedVector B (Sum.inr 2723) = Sparse.eval nodeValue2723 (mixedVector B) := by
    change mixedMoment B node2723 node2723Labels = _
    exact sound2723 B hB hF
  have h2724 : mixedVector B (Sum.inr 2724) = Sparse.eval nodeValue2724 (mixedVector B) := by
    change mixedMoment B node2724 node2724Labels = _
    exact sound2724 B hB hF
  have h2743 : mixedVector B (Sum.inr 2743) = Sparse.eval nodeValue2743 (mixedVector B) := by
    change mixedMoment B node2743 node2743Labels = _
    exact sound2743 B hB hF
  simpa only [sourceForm2483, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1665, h1675, h1676, h1682, h1728, h2142, h2152, h2153, h2158, h2174, h2175, h2178, h2191, h2192, h2205, h2206, h2207, h2216, h2217, h2229, h2230, h2265, h2266, h2293, h2673, h2695, h2723, h2724, h2743, reducedSource2000] using sourceEq2483 B hB

theorem rowSound2000 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2000 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2000, numericCheck2000, reducedZero2000 B hB hF, mul_zero]

theorem reducedZero2001 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2001 (mixedVector B) = 0 := by
  have h1803 : mixedVector B (Sum.inr 1803) = Sparse.eval nodeValue1803 (mixedVector B) := by
    change mixedMoment B node1803 node1803Labels = _
    exact sound1803 B hB hF
  have h1808 : mixedVector B (Sum.inr 1808) = Sparse.eval nodeValue1808 (mixedVector B) := by
    change mixedMoment B node1808 node1808Labels = _
    exact sound1808 B hB hF
  have h1810 : mixedVector B (Sum.inr 1810) = Sparse.eval nodeValue1810 (mixedVector B) := by
    change mixedMoment B node1810 node1810Labels = _
    exact sound1810 B hB hF
  have h1816 : mixedVector B (Sum.inr 1816) = Sparse.eval nodeValue1816 (mixedVector B) := by
    change mixedMoment B node1816 node1816Labels = _
    exact sound1816 B hB hF
  have h2054 : mixedVector B (Sum.inr 2054) = Sparse.eval nodeValue2054 (mixedVector B) := by
    change mixedMoment B node2054 node2054Labels = _
    exact sound2054 B hB hF
  have h3392 : mixedVector B (Sum.inr 3392) = Sparse.eval nodeValue3392 (mixedVector B) := by
    change mixedMoment B node3392 node3392Labels = _
    exact sound3392 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2484, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1803, h1808, h1810, h1816, h2054, h3392, h4084, reducedSource2001] using sourceEq2484 B hB

theorem rowSound2001 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2001 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2001, numericCheck2001, reducedZero2001 B hB hF, mul_zero]

theorem reducedZero2002 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2002 (mixedVector B) = 0 := by
  have h4210 : mixedVector B (Sum.inr 4210) = Sparse.eval nodeValue4210 (mixedVector B) := by
    change mixedMoment B node4210 node4210Labels = _
    exact sound4210 B hB hF
  have h4212 : mixedVector B (Sum.inr 4212) = Sparse.eval nodeValue4212 (mixedVector B) := by
    change mixedMoment B node4212 node4212Labels = _
    exact sound4212 B hB hF
  have h4213 : mixedVector B (Sum.inr 4213) = Sparse.eval nodeValue4213 (mixedVector B) := by
    change mixedMoment B node4213 node4213Labels = _
    exact sound4213 B hB hF
  have h4224 : mixedVector B (Sum.inr 4224) = Sparse.eval nodeValue4224 (mixedVector B) := by
    change mixedMoment B node4224 node4224Labels = _
    exact sound4224 B hB hF
  have h4265 : mixedVector B (Sum.inr 4265) = Sparse.eval nodeValue4265 (mixedVector B) := by
    change mixedMoment B node4265 node4265Labels = _
    exact sound4265 B hB hF
  have h4642 : mixedVector B (Sum.inr 4642) = Sparse.eval nodeValue4642 (mixedVector B) := by
    change mixedMoment B node4642 node4642Labels = _
    exact sound4642 B hB hF
  have h4644 : mixedVector B (Sum.inr 4644) = Sparse.eval nodeValue4644 (mixedVector B) := by
    change mixedMoment B node4644 node4644Labels = _
    exact sound4644 B hB hF
  have h4645 : mixedVector B (Sum.inr 4645) = Sparse.eval nodeValue4645 (mixedVector B) := by
    change mixedMoment B node4645 node4645Labels = _
    exact sound4645 B hB hF
  have h4654 : mixedVector B (Sum.inr 4654) = Sparse.eval nodeValue4654 (mixedVector B) := by
    change mixedMoment B node4654 node4654Labels = _
    exact sound4654 B hB hF
  have h4709 : mixedVector B (Sum.inr 4709) = Sparse.eval nodeValue4709 (mixedVector B) := by
    change mixedMoment B node4709 node4709Labels = _
    exact sound4709 B hB hF
  have h4710 : mixedVector B (Sum.inr 4710) = Sparse.eval nodeValue4710 (mixedVector B) := by
    change mixedMoment B node4710 node4710Labels = _
    exact sound4710 B hB hF
  have h4717 : mixedVector B (Sum.inr 4717) = Sparse.eval nodeValue4717 (mixedVector B) := by
    change mixedMoment B node4717 node4717Labels = _
    exact sound4717 B hB hF
  have h4737 : mixedVector B (Sum.inr 4737) = Sparse.eval nodeValue4737 (mixedVector B) := by
    change mixedMoment B node4737 node4737Labels = _
    exact sound4737 B hB hF
  have h4787 : mixedVector B (Sum.inr 4787) = Sparse.eval nodeValue4787 (mixedVector B) := by
    change mixedMoment B node4787 node4787Labels = _
    exact sound4787 B hB hF
  have h4788 : mixedVector B (Sum.inr 4788) = Sparse.eval nodeValue4788 (mixedVector B) := by
    change mixedMoment B node4788 node4788Labels = _
    exact sound4788 B hB hF
  have h4802 : mixedVector B (Sum.inr 4802) = Sparse.eval nodeValue4802 (mixedVector B) := by
    change mixedMoment B node4802 node4802Labels = _
    exact sound4802 B hB hF
  have h4804 : mixedVector B (Sum.inr 4804) = Sparse.eval nodeValue4804 (mixedVector B) := by
    change mixedMoment B node4804 node4804Labels = _
    exact sound4804 B hB hF
  have h4811 : mixedVector B (Sum.inr 4811) = Sparse.eval nodeValue4811 (mixedVector B) := by
    change mixedMoment B node4811 node4811Labels = _
    exact sound4811 B hB hF
  have h4831 : mixedVector B (Sum.inr 4831) = Sparse.eval nodeValue4831 (mixedVector B) := by
    change mixedMoment B node4831 node4831Labels = _
    exact sound4831 B hB hF
  have h4832 : mixedVector B (Sum.inr 4832) = Sparse.eval nodeValue4832 (mixedVector B) := by
    change mixedMoment B node4832 node4832Labels = _
    exact sound4832 B hB hF
  have h4835 : mixedVector B (Sum.inr 4835) = Sparse.eval nodeValue4835 (mixedVector B) := by
    change mixedMoment B node4835 node4835Labels = _
    exact sound4835 B hB hF
  have h4888 : mixedVector B (Sum.inr 4888) = Sparse.eval nodeValue4888 (mixedVector B) := by
    change mixedMoment B node4888 node4888Labels = _
    exact sound4888 B hB hF
  have h5368 : mixedVector B (Sum.inr 5368) = Sparse.eval nodeValue5368 (mixedVector B) := by
    change mixedMoment B node5368 node5368Labels = _
    exact sound5368 B hB hF
  have h5395 : mixedVector B (Sum.inr 5395) = Sparse.eval nodeValue5395 (mixedVector B) := by
    change mixedMoment B node5395 node5395Labels = _
    exact sound5395 B hB hF
  have h5428 : mixedVector B (Sum.inr 5428) = Sparse.eval nodeValue5428 (mixedVector B) := by
    change mixedMoment B node5428 node5428Labels = _
    exact sound5428 B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434 B hB hF
  have h5439 : mixedVector B (Sum.inr 5439) = Sparse.eval nodeValue5439 (mixedVector B) := by
    change mixedMoment B node5439 node5439Labels = _
    exact sound5439 B hB hF
  simpa only [sourceForm2485, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4210, h4212, h4213, h4224, h4265, h4642, h4644, h4645, h4654, h4709, h4710, h4717, h4737, h4787, h4788, h4802, h4804, h4811, h4831, h4832, h4835, h4888, h5368, h5395, h5428, h5434, h5439, reducedSource2002] using sourceEq2485 B hB

theorem rowSound2002 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2002 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2002, numericCheck2002, reducedZero2002 B hB hF, mul_zero]

theorem reducedZero2003 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2003 (mixedVector B) = 0 := by
  have h4397 : mixedVector B (Sum.inr 4397) = Sparse.eval nodeValue4397 (mixedVector B) := by
    change mixedMoment B node4397 node4397Labels = _
    exact sound4397 B hB hF
  have h4402 : mixedVector B (Sum.inr 4402) = Sparse.eval nodeValue4402 (mixedVector B) := by
    change mixedMoment B node4402 node4402Labels = _
    exact sound4402 B hB hF
  have h4404 : mixedVector B (Sum.inr 4404) = Sparse.eval nodeValue4404 (mixedVector B) := by
    change mixedMoment B node4404 node4404Labels = _
    exact sound4404 B hB hF
  have h4424 : mixedVector B (Sum.inr 4424) = Sparse.eval nodeValue4424 (mixedVector B) := by
    change mixedMoment B node4424 node4424Labels = _
    exact sound4424 B hB hF
  have h4453 : mixedVector B (Sum.inr 4453) = Sparse.eval nodeValue4453 (mixedVector B) := by
    change mixedMoment B node4453 node4453Labels = _
    exact sound4453 B hB hF
  have h4737 : mixedVector B (Sum.inr 4737) = Sparse.eval nodeValue4737 (mixedVector B) := by
    change mixedMoment B node4737 node4737Labels = _
    exact sound4737 B hB hF
  have h4742 : mixedVector B (Sum.inr 4742) = Sparse.eval nodeValue4742 (mixedVector B) := by
    change mixedMoment B node4742 node4742Labels = _
    exact sound4742 B hB hF
  have h4745 : mixedVector B (Sum.inr 4745) = Sparse.eval nodeValue4745 (mixedVector B) := by
    change mixedMoment B node4745 node4745Labels = _
    exact sound4745 B hB hF
  have h4752 : mixedVector B (Sum.inr 4752) = Sparse.eval nodeValue4752 (mixedVector B) := by
    change mixedMoment B node4752 node4752Labels = _
    exact sound4752 B hB hF
  have h4780 : mixedVector B (Sum.inr 4780) = Sparse.eval nodeValue4780 (mixedVector B) := by
    change mixedMoment B node4780 node4780Labels = _
    exact sound4780 B hB hF
  have h4782 : mixedVector B (Sum.inr 4782) = Sparse.eval nodeValue4782 (mixedVector B) := by
    change mixedMoment B node4782 node4782Labels = _
    exact sound4782 B hB hF
  have h4787 : mixedVector B (Sum.inr 4787) = Sparse.eval nodeValue4787 (mixedVector B) := by
    change mixedMoment B node4787 node4787Labels = _
    exact sound4787 B hB hF
  have h4799 : mixedVector B (Sum.inr 4799) = Sparse.eval nodeValue4799 (mixedVector B) := by
    change mixedMoment B node4799 node4799Labels = _
    exact sound4799 B hB hF
  have h4802 : mixedVector B (Sum.inr 4802) = Sparse.eval nodeValue4802 (mixedVector B) := by
    change mixedMoment B node4802 node4802Labels = _
    exact sound4802 B hB hF
  have h4803 : mixedVector B (Sum.inr 4803) = Sparse.eval nodeValue4803 (mixedVector B) := by
    change mixedMoment B node4803 node4803Labels = _
    exact sound4803 B hB hF
  have h4828 : mixedVector B (Sum.inr 4828) = Sparse.eval nodeValue4828 (mixedVector B) := by
    change mixedMoment B node4828 node4828Labels = _
    exact sound4828 B hB hF
  have h4829 : mixedVector B (Sum.inr 4829) = Sparse.eval nodeValue4829 (mixedVector B) := by
    change mixedMoment B node4829 node4829Labels = _
    exact sound4829 B hB hF
  have h4834 : mixedVector B (Sum.inr 4834) = Sparse.eval nodeValue4834 (mixedVector B) := by
    change mixedMoment B node4834 node4834Labels = _
    exact sound4834 B hB hF
  have h4836 : mixedVector B (Sum.inr 4836) = Sparse.eval nodeValue4836 (mixedVector B) := by
    change mixedMoment B node4836 node4836Labels = _
    exact sound4836 B hB hF
  have h4838 : mixedVector B (Sum.inr 4838) = Sparse.eval nodeValue4838 (mixedVector B) := by
    change mixedMoment B node4838 node4838Labels = _
    exact sound4838 B hB hF
  have h4839 : mixedVector B (Sum.inr 4839) = Sparse.eval nodeValue4839 (mixedVector B) := by
    change mixedMoment B node4839 node4839Labels = _
    exact sound4839 B hB hF
  have h4861 : mixedVector B (Sum.inr 4861) = Sparse.eval nodeValue4861 (mixedVector B) := by
    change mixedMoment B node4861 node4861Labels = _
    exact sound4861 B hB hF
  have h4866 : mixedVector B (Sum.inr 4866) = Sparse.eval nodeValue4866 (mixedVector B) := by
    change mixedMoment B node4866 node4866Labels = _
    exact sound4866 B hB hF
  have h4867 : mixedVector B (Sum.inr 4867) = Sparse.eval nodeValue4867 (mixedVector B) := by
    change mixedMoment B node4867 node4867Labels = _
    exact sound4867 B hB hF
  have h5102 : mixedVector B (Sum.inr 5102) = Sparse.eval nodeValue5102 (mixedVector B) := by
    change mixedMoment B node5102 node5102Labels = _
    exact sound5102 B hB hF
  have h5135 : mixedVector B (Sum.inr 5135) = Sparse.eval nodeValue5135 (mixedVector B) := by
    change mixedMoment B node5135 node5135Labels = _
    exact sound5135 B hB hF
  have h5164 : mixedVector B (Sum.inr 5164) = Sparse.eval nodeValue5164 (mixedVector B) := by
    change mixedMoment B node5164 node5164Labels = _
    exact sound5164 B hB hF
  have h5169 : mixedVector B (Sum.inr 5169) = Sparse.eval nodeValue5169 (mixedVector B) := by
    change mixedMoment B node5169 node5169Labels = _
    exact sound5169 B hB hF
  have h5170 : mixedVector B (Sum.inr 5170) = Sparse.eval nodeValue5170 (mixedVector B) := by
    change mixedMoment B node5170 node5170Labels = _
    exact sound5170 B hB hF
  simpa only [sourceForm2486, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4397, h4402, h4404, h4424, h4453, h4737, h4742, h4745, h4752, h4780, h4782, h4787, h4799, h4802, h4803, h4828, h4829, h4834, h4836, h4838, h4839, h4861, h4866, h4867, h5102, h5135, h5164, h5169, h5170, reducedSource2003] using sourceEq2486 B hB

theorem rowSound2003 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2003 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2003, numericCheck2003, reducedZero2003 B hB hF, mul_zero]

theorem reducedZero2004 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2004 (mixedVector B) = 0 := by
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  have h4344 : mixedVector B (Sum.inr 4344) = Sparse.eval nodeValue4344 (mixedVector B) := by
    change mixedMoment B node4344 node4344Labels = _
    exact sound4344 B hB hF
  have h4352 : mixedVector B (Sum.inr 4352) = Sparse.eval nodeValue4352 (mixedVector B) := by
    change mixedMoment B node4352 node4352Labels = _
    exact sound4352 B hB hF
  have h4355 : mixedVector B (Sum.inr 4355) = Sparse.eval nodeValue4355 (mixedVector B) := by
    change mixedMoment B node4355 node4355Labels = _
    exact sound4355 B hB hF
  have h4502 : mixedVector B (Sum.inr 4502) = Sparse.eval nodeValue4502 (mixedVector B) := by
    change mixedMoment B node4502 node4502Labels = _
    exact sound4502 B hB hF
  have h4679 : mixedVector B (Sum.inr 4679) = Sparse.eval nodeValue4679 (mixedVector B) := by
    change mixedMoment B node4679 node4679Labels = _
    exact sound4679 B hB hF
  have h4686 : mixedVector B (Sum.inr 4686) = Sparse.eval nodeValue4686 (mixedVector B) := by
    change mixedMoment B node4686 node4686Labels = _
    exact sound4686 B hB hF
  have h4689 : mixedVector B (Sum.inr 4689) = Sparse.eval nodeValue4689 (mixedVector B) := by
    change mixedMoment B node4689 node4689Labels = _
    exact sound4689 B hB hF
  have h4764 : mixedVector B (Sum.inr 4764) = Sparse.eval nodeValue4764 (mixedVector B) := by
    change mixedMoment B node4764 node4764Labels = _
    exact sound4764 B hB hF
  have h4767 : mixedVector B (Sum.inr 4767) = Sparse.eval nodeValue4767 (mixedVector B) := by
    change mixedMoment B node4767 node4767Labels = _
    exact sound4767 B hB hF
  have h4802 : mixedVector B (Sum.inr 4802) = Sparse.eval nodeValue4802 (mixedVector B) := by
    change mixedMoment B node4802 node4802Labels = _
    exact sound4802 B hB hF
  have h4807 : mixedVector B (Sum.inr 4807) = Sparse.eval nodeValue4807 (mixedVector B) := by
    change mixedMoment B node4807 node4807Labels = _
    exact sound4807 B hB hF
  have h4811 : mixedVector B (Sum.inr 4811) = Sparse.eval nodeValue4811 (mixedVector B) := by
    change mixedMoment B node4811 node4811Labels = _
    exact sound4811 B hB hF
  have h4833 : mixedVector B (Sum.inr 4833) = Sparse.eval nodeValue4833 (mixedVector B) := by
    change mixedMoment B node4833 node4833Labels = _
    exact sound4833 B hB hF
  have h4838 : mixedVector B (Sum.inr 4838) = Sparse.eval nodeValue4838 (mixedVector B) := by
    change mixedMoment B node4838 node4838Labels = _
    exact sound4838 B hB hF
  have h4895 : mixedVector B (Sum.inr 4895) = Sparse.eval nodeValue4895 (mixedVector B) := by
    change mixedMoment B node4895 node4895Labels = _
    exact sound4895 B hB hF
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
  simpa only [sourceForm2487, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4083, h4344, h4352, h4355, h4502, h4679, h4686, h4689, h4764, h4767, h4802, h4807, h4811, h4833, h4838, h4895, h5237, h5247, h5271, h5273, reducedSource2004] using sourceEq2487 B hB

theorem rowSound2004 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2004 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2004, numericCheck2004, reducedZero2004 B hB hF, mul_zero]

theorem reducedZero2005 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2005 (mixedVector B) = 0 := by
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  have h4341 : mixedVector B (Sum.inr 4341) = Sparse.eval nodeValue4341 (mixedVector B) := by
    change mixedMoment B node4341 node4341Labels = _
    exact sound4341 B hB hF
  have h4346 : mixedVector B (Sum.inr 4346) = Sparse.eval nodeValue4346 (mixedVector B) := by
    change mixedMoment B node4346 node4346Labels = _
    exact sound4346 B hB hF
  have h4349 : mixedVector B (Sum.inr 4349) = Sparse.eval nodeValue4349 (mixedVector B) := by
    change mixedMoment B node4349 node4349Labels = _
    exact sound4349 B hB hF
  have h4354 : mixedVector B (Sum.inr 4354) = Sparse.eval nodeValue4354 (mixedVector B) := by
    change mixedMoment B node4354 node4354Labels = _
    exact sound4354 B hB hF
  have h4498 : mixedVector B (Sum.inr 4498) = Sparse.eval nodeValue4498 (mixedVector B) := by
    change mixedMoment B node4498 node4498Labels = _
    exact sound4498 B hB hF
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
  have h4760 : mixedVector B (Sum.inr 4760) = Sparse.eval nodeValue4760 (mixedVector B) := by
    change mixedMoment B node4760 node4760Labels = _
    exact sound4760 B hB hF
  have h4763 : mixedVector B (Sum.inr 4763) = Sparse.eval nodeValue4763 (mixedVector B) := by
    change mixedMoment B node4763 node4763Labels = _
    exact sound4763 B hB hF
  have h4766 : mixedVector B (Sum.inr 4766) = Sparse.eval nodeValue4766 (mixedVector B) := by
    change mixedMoment B node4766 node4766Labels = _
    exact sound4766 B hB hF
  have h4801 : mixedVector B (Sum.inr 4801) = Sparse.eval nodeValue4801 (mixedVector B) := by
    change mixedMoment B node4801 node4801Labels = _
    exact sound4801 B hB hF
  have h4804 : mixedVector B (Sum.inr 4804) = Sparse.eval nodeValue4804 (mixedVector B) := by
    change mixedMoment B node4804 node4804Labels = _
    exact sound4804 B hB hF
  have h4810 : mixedVector B (Sum.inr 4810) = Sparse.eval nodeValue4810 (mixedVector B) := by
    change mixedMoment B node4810 node4810Labels = _
    exact sound4810 B hB hF
  have h4831 : mixedVector B (Sum.inr 4831) = Sparse.eval nodeValue4831 (mixedVector B) := by
    change mixedMoment B node4831 node4831Labels = _
    exact sound4831 B hB hF
  have h4834 : mixedVector B (Sum.inr 4834) = Sparse.eval nodeValue4834 (mixedVector B) := by
    change mixedMoment B node4834 node4834Labels = _
    exact sound4834 B hB hF
  have h4835 : mixedVector B (Sum.inr 4835) = Sparse.eval nodeValue4835 (mixedVector B) := by
    change mixedMoment B node4835 node4835Labels = _
    exact sound4835 B hB hF
  have h4839 : mixedVector B (Sum.inr 4839) = Sparse.eval nodeValue4839 (mixedVector B) := by
    change mixedMoment B node4839 node4839Labels = _
    exact sound4839 B hB hF
  have h4841 : mixedVector B (Sum.inr 4841) = Sparse.eval nodeValue4841 (mixedVector B) := by
    change mixedMoment B node4841 node4841Labels = _
    exact sound4841 B hB hF
  have h4846 : mixedVector B (Sum.inr 4846) = Sparse.eval nodeValue4846 (mixedVector B) := by
    change mixedMoment B node4846 node4846Labels = _
    exact sound4846 B hB hF
  have h4894 : mixedVector B (Sum.inr 4894) = Sparse.eval nodeValue4894 (mixedVector B) := by
    change mixedMoment B node4894 node4894Labels = _
    exact sound4894 B hB hF
  have h4895 : mixedVector B (Sum.inr 4895) = Sparse.eval nodeValue4895 (mixedVector B) := by
    change mixedMoment B node4895 node4895Labels = _
    exact sound4895 B hB hF
  have h5228 : mixedVector B (Sum.inr 5228) = Sparse.eval nodeValue5228 (mixedVector B) := by
    change mixedMoment B node5228 node5228Labels = _
    exact sound5228 B hB hF
  have h5241 : mixedVector B (Sum.inr 5241) = Sparse.eval nodeValue5241 (mixedVector B) := by
    change mixedMoment B node5241 node5241Labels = _
    exact sound5241 B hB hF
  have h5258 : mixedVector B (Sum.inr 5258) = Sparse.eval nodeValue5258 (mixedVector B) := by
    change mixedMoment B node5258 node5258Labels = _
    exact sound5258 B hB hF
  have h5259 : mixedVector B (Sum.inr 5259) = Sparse.eval nodeValue5259 (mixedVector B) := by
    change mixedMoment B node5259 node5259Labels = _
    exact sound5259 B hB hF
  have h5274 : mixedVector B (Sum.inr 5274) = Sparse.eval nodeValue5274 (mixedVector B) := by
    change mixedMoment B node5274 node5274Labels = _
    exact sound5274 B hB hF
  simpa only [sourceForm2488, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4084, h4341, h4346, h4349, h4354, h4498, h4676, h4681, h4684, h4688, h4760, h4763, h4766, h4801, h4804, h4810, h4831, h4834, h4835, h4839, h4841, h4846, h4894, h4895, h5228, h5241, h5258, h5259, h5274, reducedSource2005] using sourceEq2488 B hB

theorem rowSound2005 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2005 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2005, numericCheck2005, reducedZero2005 B hB hF, mul_zero]

theorem reducedZero2006 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2006 (mixedVector B) = 0 := by
  have h4340 : mixedVector B (Sum.inr 4340) = Sparse.eval nodeValue4340 (mixedVector B) := by
    change mixedMoment B node4340 node4340Labels = _
    exact sound4340 B hB hF
  have h4343 : mixedVector B (Sum.inr 4343) = Sparse.eval nodeValue4343 (mixedVector B) := by
    change mixedMoment B node4343 node4343Labels = _
    exact sound4343 B hB hF
  have h4348 : mixedVector B (Sum.inr 4348) = Sparse.eval nodeValue4348 (mixedVector B) := by
    change mixedMoment B node4348 node4348Labels = _
    exact sound4348 B hB hF
  have h4496 : mixedVector B (Sum.inr 4496) = Sparse.eval nodeValue4496 (mixedVector B) := by
    change mixedMoment B node4496 node4496Labels = _
    exact sound4496 B hB hF
  have h4675 : mixedVector B (Sum.inr 4675) = Sparse.eval nodeValue4675 (mixedVector B) := by
    change mixedMoment B node4675 node4675Labels = _
    exact sound4675 B hB hF
  have h4678 : mixedVector B (Sum.inr 4678) = Sparse.eval nodeValue4678 (mixedVector B) := by
    change mixedMoment B node4678 node4678Labels = _
    exact sound4678 B hB hF
  have h4683 : mixedVector B (Sum.inr 4683) = Sparse.eval nodeValue4683 (mixedVector B) := by
    change mixedMoment B node4683 node4683Labels = _
    exact sound4683 B hB hF
  have h4759 : mixedVector B (Sum.inr 4759) = Sparse.eval nodeValue4759 (mixedVector B) := by
    change mixedMoment B node4759 node4759Labels = _
    exact sound4759 B hB hF
  have h4762 : mixedVector B (Sum.inr 4762) = Sparse.eval nodeValue4762 (mixedVector B) := by
    change mixedMoment B node4762 node4762Labels = _
    exact sound4762 B hB hF
  have h4830 : mixedVector B (Sum.inr 4830) = Sparse.eval nodeValue4830 (mixedVector B) := by
    change mixedMoment B node4830 node4830Labels = _
    exact sound4830 B hB hF
  have h4832 : mixedVector B (Sum.inr 4832) = Sparse.eval nodeValue4832 (mixedVector B) := by
    change mixedMoment B node4832 node4832Labels = _
    exact sound4832 B hB hF
  have h4836 : mixedVector B (Sum.inr 4836) = Sparse.eval nodeValue4836 (mixedVector B) := by
    change mixedMoment B node4836 node4836Labels = _
    exact sound4836 B hB hF
  have h4837 : mixedVector B (Sum.inr 4837) = Sparse.eval nodeValue4837 (mixedVector B) := by
    change mixedMoment B node4837 node4837Labels = _
    exact sound4837 B hB hF
  have h4845 : mixedVector B (Sum.inr 4845) = Sparse.eval nodeValue4845 (mixedVector B) := by
    change mixedMoment B node4845 node4845Labels = _
    exact sound4845 B hB hF
  have h4890 : mixedVector B (Sum.inr 4890) = Sparse.eval nodeValue4890 (mixedVector B) := by
    change mixedMoment B node4890 node4890Labels = _
    exact sound4890 B hB hF
  have h4897 : mixedVector B (Sum.inr 4897) = Sparse.eval nodeValue4897 (mixedVector B) := by
    change mixedMoment B node4897 node4897Labels = _
    exact sound4897 B hB hF
  have h5222 : mixedVector B (Sum.inr 5222) = Sparse.eval nodeValue5222 (mixedVector B) := by
    change mixedMoment B node5222 node5222Labels = _
    exact sound5222 B hB hF
  have h5239 : mixedVector B (Sum.inr 5239) = Sparse.eval nodeValue5239 (mixedVector B) := by
    change mixedMoment B node5239 node5239Labels = _
    exact sound5239 B hB hF
  have h5252 : mixedVector B (Sum.inr 5252) = Sparse.eval nodeValue5252 (mixedVector B) := by
    change mixedMoment B node5252 node5252Labels = _
    exact sound5252 B hB hF
  have h5261 : mixedVector B (Sum.inr 5261) = Sparse.eval nodeValue5261 (mixedVector B) := by
    change mixedMoment B node5261 node5261Labels = _
    exact sound5261 B hB hF
  simpa only [sourceForm2489, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4340, h4343, h4348, h4496, h4675, h4678, h4683, h4759, h4762, h4830, h4832, h4836, h4837, h4845, h4890, h4897, h5222, h5239, h5252, h5261, reducedSource2006] using sourceEq2489 B hB

theorem rowSound2006 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2006 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2006, numericCheck2006, reducedZero2006 B hB hF, mul_zero]

theorem reducedZero2007 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2007 (mixedVector B) = 0 := by
  have h1662 : mixedVector B (Sum.inr 1662) = Sparse.eval nodeValue1662 (mixedVector B) := by
    change mixedMoment B node1662 node1662Labels = _
    exact sound1662 B hB hF
  have h1666 : mixedVector B (Sum.inr 1666) = Sparse.eval nodeValue1666 (mixedVector B) := by
    change mixedMoment B node1666 node1666Labels = _
    exact sound1666 B hB hF
  have h1669 : mixedVector B (Sum.inr 1669) = Sparse.eval nodeValue1669 (mixedVector B) := by
    change mixedMoment B node1669 node1669Labels = _
    exact sound1669 B hB hF
  have h1710 : mixedVector B (Sum.inr 1710) = Sparse.eval nodeValue1710 (mixedVector B) := by
    change mixedMoment B node1710 node1710Labels = _
    exact sound1710 B hB hF
  have h2139 : mixedVector B (Sum.inr 2139) = Sparse.eval nodeValue2139 (mixedVector B) := by
    change mixedMoment B node2139 node2139Labels = _
    exact sound2139 B hB hF
  have h2143 : mixedVector B (Sum.inr 2143) = Sparse.eval nodeValue2143 (mixedVector B) := by
    change mixedMoment B node2143 node2143Labels = _
    exact sound2143 B hB hF
  have h2146 : mixedVector B (Sum.inr 2146) = Sparse.eval nodeValue2146 (mixedVector B) := by
    change mixedMoment B node2146 node2146Labels = _
    exact sound2146 B hB hF
  have h2170 : mixedVector B (Sum.inr 2170) = Sparse.eval nodeValue2170 (mixedVector B) := by
    change mixedMoment B node2170 node2170Labels = _
    exact sound2170 B hB hF
  have h2171 : mixedVector B (Sum.inr 2171) = Sparse.eval nodeValue2171 (mixedVector B) := by
    change mixedMoment B node2171 node2171Labels = _
    exact sound2171 B hB hF
  have h2187 : mixedVector B (Sum.inr 2187) = Sparse.eval nodeValue2187 (mixedVector B) := by
    change mixedMoment B node2187 node2187Labels = _
    exact sound2187 B hB hF
  have h2193 : mixedVector B (Sum.inr 2193) = Sparse.eval nodeValue2193 (mixedVector B) := by
    change mixedMoment B node2193 node2193Labels = _
    exact sound2193 B hB hF
  have h2197 : mixedVector B (Sum.inr 2197) = Sparse.eval nodeValue2197 (mixedVector B) := by
    change mixedMoment B node2197 node2197Labels = _
    exact sound2197 B hB hF
  have h2208 : mixedVector B (Sum.inr 2208) = Sparse.eval nodeValue2208 (mixedVector B) := by
    change mixedMoment B node2208 node2208Labels = _
    exact sound2208 B hB hF
  have h2218 : mixedVector B (Sum.inr 2218) = Sparse.eval nodeValue2218 (mixedVector B) := by
    change mixedMoment B node2218 node2218Labels = _
    exact sound2218 B hB hF
  have h2247 : mixedVector B (Sum.inr 2247) = Sparse.eval nodeValue2247 (mixedVector B) := by
    change mixedMoment B node2247 node2247Labels = _
    exact sound2247 B hB hF
  have h2268 : mixedVector B (Sum.inr 2268) = Sparse.eval nodeValue2268 (mixedVector B) := by
    change mixedMoment B node2268 node2268Labels = _
    exact sound2268 B hB hF
  have h2664 : mixedVector B (Sum.inr 2664) = Sparse.eval nodeValue2664 (mixedVector B) := by
    change mixedMoment B node2664 node2664Labels = _
    exact sound2664 B hB hF
  have h2691 : mixedVector B (Sum.inr 2691) = Sparse.eval nodeValue2691 (mixedVector B) := by
    change mixedMoment B node2691 node2691Labels = _
    exact sound2691 B hB hF
  have h2712 : mixedVector B (Sum.inr 2712) = Sparse.eval nodeValue2712 (mixedVector B) := by
    change mixedMoment B node2712 node2712Labels = _
    exact sound2712 B hB hF
  have h2726 : mixedVector B (Sum.inr 2726) = Sparse.eval nodeValue2726 (mixedVector B) := by
    change mixedMoment B node2726 node2726Labels = _
    exact sound2726 B hB hF
  simpa only [sourceForm2491, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1662, h1666, h1669, h1710, h2139, h2143, h2146, h2170, h2171, h2187, h2193, h2197, h2208, h2218, h2247, h2268, h2664, h2691, h2712, h2726, reducedSource2007] using sourceEq2491 B hB

theorem rowSound2007 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2007 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2007, numericCheck2007, reducedZero2007 B hB hF, mul_zero]

theorem reducedZero2008 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2008 (mixedVector B) = 0 := by
  have h1801 : mixedVector B (Sum.inr 1801) = Sparse.eval nodeValue1801 (mixedVector B) := by
    change mixedMoment B node1801 node1801Labels = _
    exact sound1801 B hB hF
  have h1804 : mixedVector B (Sum.inr 1804) = Sparse.eval nodeValue1804 (mixedVector B) := by
    change mixedMoment B node1804 node1804Labels = _
    exact sound1804 B hB hF
  have h1809 : mixedVector B (Sum.inr 1809) = Sparse.eval nodeValue1809 (mixedVector B) := by
    change mixedMoment B node1809 node1809Labels = _
    exact sound1809 B hB hF
  have h2052 : mixedVector B (Sum.inr 2052) = Sparse.eval nodeValue2052 (mixedVector B) := by
    change mixedMoment B node2052 node2052Labels = _
    exact sound2052 B hB hF
  have h3389 : mixedVector B (Sum.inr 3389) = Sparse.eval nodeValue3389 (mixedVector B) := by
    change mixedMoment B node3389 node3389Labels = _
    exact sound3389 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm2492, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1801, h1804, h1809, h2052, h3389, h4085, reducedSource2008] using sourceEq2492 B hB

theorem rowSound2008 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2008 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2008, numericCheck2008, reducedZero2008 B hB hF, mul_zero]

theorem reducedZero2009 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2009 (mixedVector B) = 0 := by
  have h918 : mixedVector B (Sum.inr 918) = Sparse.eval nodeValue918 (mixedVector B) := by
    change mixedMoment B node918 node918Labels = _
    exact sound918 B hB hF
  have h1801 : mixedVector B (Sum.inr 1801) = Sparse.eval nodeValue1801 (mixedVector B) := by
    change mixedMoment B node1801 node1801Labels = _
    exact sound1801 B hB hF
  have h2050 : mixedVector B (Sum.inr 2050) = Sparse.eval nodeValue2050 (mixedVector B) := by
    change mixedMoment B node2050 node2050Labels = _
    exact sound2050 B hB hF
  have h2052 : mixedVector B (Sum.inr 2052) = Sparse.eval nodeValue2052 (mixedVector B) := by
    change mixedMoment B node2052 node2052Labels = _
    exact sound2052 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm2493, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h918, h1801, h2050, h2052, h4085, reducedSource2009] using sourceEq2493 B hB

theorem rowSound2009 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2009 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2009, numericCheck2009, reducedZero2009 B hB hF, mul_zero]

theorem reducedZero2010 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2010 (mixedVector B) = 0 := by
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  have h4322 : mixedVector B (Sum.inr 4322) = Sparse.eval nodeValue4322 (mixedVector B) := by
    change mixedMoment B node4322 node4322Labels = _
    exact sound4322 B hB hF
  have h4323 : mixedVector B (Sum.inr 4323) = Sparse.eval nodeValue4323 (mixedVector B) := by
    change mixedMoment B node4323 node4323Labels = _
    exact sound4323 B hB hF
  have h4337 : mixedVector B (Sum.inr 4337) = Sparse.eval nodeValue4337 (mixedVector B) := by
    change mixedMoment B node4337 node4337Labels = _
    exact sound4337 B hB hF
  have h4423 : mixedVector B (Sum.inr 4423) = Sparse.eval nodeValue4423 (mixedVector B) := by
    change mixedMoment B node4423 node4423Labels = _
    exact sound4423 B hB hF
  have h4660 : mixedVector B (Sum.inr 4660) = Sparse.eval nodeValue4660 (mixedVector B) := by
    change mixedMoment B node4660 node4660Labels = _
    exact sound4660 B hB hF
  have h4661 : mixedVector B (Sum.inr 4661) = Sparse.eval nodeValue4661 (mixedVector B) := by
    change mixedMoment B node4661 node4661Labels = _
    exact sound4661 B hB hF
  have h4672 : mixedVector B (Sum.inr 4672) = Sparse.eval nodeValue4672 (mixedVector B) := by
    change mixedMoment B node4672 node4672Labels = _
    exact sound4672 B hB hF
  have h4712 : mixedVector B (Sum.inr 4712) = Sparse.eval nodeValue4712 (mixedVector B) := by
    change mixedMoment B node4712 node4712Labels = _
    exact sound4712 B hB hF
  have h4715 : mixedVector B (Sum.inr 4715) = Sparse.eval nodeValue4715 (mixedVector B) := by
    change mixedMoment B node4715 node4715Labels = _
    exact sound4715 B hB hF
  have h4779 : mixedVector B (Sum.inr 4779) = Sparse.eval nodeValue4779 (mixedVector B) := by
    change mixedMoment B node4779 node4779Labels = _
    exact sound4779 B hB hF
  have h4782 : mixedVector B (Sum.inr 4782) = Sparse.eval nodeValue4782 (mixedVector B) := by
    change mixedMoment B node4782 node4782Labels = _
    exact sound4782 B hB hF
  have h4787 : mixedVector B (Sum.inr 4787) = Sparse.eval nodeValue4787 (mixedVector B) := by
    change mixedMoment B node4787 node4787Labels = _
    exact sound4787 B hB hF
  have h4798 : mixedVector B (Sum.inr 4798) = Sparse.eval nodeValue4798 (mixedVector B) := by
    change mixedMoment B node4798 node4798Labels = _
    exact sound4798 B hB hF
  have h4826 : mixedVector B (Sum.inr 4826) = Sparse.eval nodeValue4826 (mixedVector B) := by
    change mixedMoment B node4826 node4826Labels = _
    exact sound4826 B hB hF
  have h4834 : mixedVector B (Sum.inr 4834) = Sparse.eval nodeValue4834 (mixedVector B) := by
    change mixedMoment B node4834 node4834Labels = _
    exact sound4834 B hB hF
  have h4838 : mixedVector B (Sum.inr 4838) = Sparse.eval nodeValue4838 (mixedVector B) := by
    change mixedMoment B node4838 node4838Labels = _
    exact sound4838 B hB hF
  have h5058 : mixedVector B (Sum.inr 5058) = Sparse.eval nodeValue5058 (mixedVector B) := by
    change mixedMoment B node5058 node5058Labels = _
    exact sound5058 B hB hF
  have h5123 : mixedVector B (Sum.inr 5123) = Sparse.eval nodeValue5123 (mixedVector B) := by
    change mixedMoment B node5123 node5123Labels = _
    exact sound5123 B hB hF
  have h5134 : mixedVector B (Sum.inr 5134) = Sparse.eval nodeValue5134 (mixedVector B) := by
    change mixedMoment B node5134 node5134Labels = _
    exact sound5134 B hB hF
  have h5137 : mixedVector B (Sum.inr 5137) = Sparse.eval nodeValue5137 (mixedVector B) := by
    change mixedMoment B node5137 node5137Labels = _
    exact sound5137 B hB hF
  simpa only [sourceForm2494, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4080, h4322, h4323, h4337, h4423, h4660, h4661, h4672, h4712, h4715, h4779, h4782, h4787, h4798, h4826, h4834, h4838, h5058, h5123, h5134, h5137, reducedSource2010] using sourceEq2494 B hB

theorem rowSound2010 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2010 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2010, numericCheck2010, reducedZero2010 B hB hF, mul_zero]

theorem reducedZero2011 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2011 (mixedVector B) = 0 := by
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  have h4300 : mixedVector B (Sum.inr 4300) = Sparse.eval nodeValue4300 (mixedVector B) := by
    change mixedMoment B node4300 node4300Labels = _
    exact sound4300 B hB hF
  have h4301 : mixedVector B (Sum.inr 4301) = Sparse.eval nodeValue4301 (mixedVector B) := by
    change mixedMoment B node4301 node4301Labels = _
    exact sound4301 B hB hF
  have h4307 : mixedVector B (Sum.inr 4307) = Sparse.eval nodeValue4307 (mixedVector B) := by
    change mixedMoment B node4307 node4307Labels = _
    exact sound4307 B hB hF
  have h4417 : mixedVector B (Sum.inr 4417) = Sparse.eval nodeValue4417 (mixedVector B) := by
    change mixedMoment B node4417 node4417Labels = _
    exact sound4417 B hB hF
  have h4641 : mixedVector B (Sum.inr 4641) = Sparse.eval nodeValue4641 (mixedVector B) := by
    change mixedMoment B node4641 node4641Labels = _
    exact sound4641 B hB hF
  have h4642 : mixedVector B (Sum.inr 4642) = Sparse.eval nodeValue4642 (mixedVector B) := by
    change mixedMoment B node4642 node4642Labels = _
    exact sound4642 B hB hF
  have h4648 : mixedVector B (Sum.inr 4648) = Sparse.eval nodeValue4648 (mixedVector B) := by
    change mixedMoment B node4648 node4648Labels = _
    exact sound4648 B hB hF
  have h4736 : mixedVector B (Sum.inr 4736) = Sparse.eval nodeValue4736 (mixedVector B) := by
    change mixedMoment B node4736 node4736Labels = _
    exact sound4736 B hB hF
  have h4737 : mixedVector B (Sum.inr 4737) = Sparse.eval nodeValue4737 (mixedVector B) := by
    change mixedMoment B node4737 node4737Labels = _
    exact sound4737 B hB hF
  have h4740 : mixedVector B (Sum.inr 4740) = Sparse.eval nodeValue4740 (mixedVector B) := by
    change mixedMoment B node4740 node4740Labels = _
    exact sound4740 B hB hF
  have h4746 : mixedVector B (Sum.inr 4746) = Sparse.eval nodeValue4746 (mixedVector B) := by
    change mixedMoment B node4746 node4746Labels = _
    exact sound4746 B hB hF
  have h4752 : mixedVector B (Sum.inr 4752) = Sparse.eval nodeValue4752 (mixedVector B) := by
    change mixedMoment B node4752 node4752Labels = _
    exact sound4752 B hB hF
  have h4802 : mixedVector B (Sum.inr 4802) = Sparse.eval nodeValue4802 (mixedVector B) := by
    change mixedMoment B node4802 node4802Labels = _
    exact sound4802 B hB hF
  have h4805 : mixedVector B (Sum.inr 4805) = Sparse.eval nodeValue4805 (mixedVector B) := by
    change mixedMoment B node4805 node4805Labels = _
    exact sound4805 B hB hF
  have h4838 : mixedVector B (Sum.inr 4838) = Sparse.eval nodeValue4838 (mixedVector B) := by
    change mixedMoment B node4838 node4838Labels = _
    exact sound4838 B hB hF
  have h4998 : mixedVector B (Sum.inr 4998) = Sparse.eval nodeValue4998 (mixedVector B) := by
    change mixedMoment B node4998 node4998Labels = _
    exact sound4998 B hB hF
  have h5073 : mixedVector B (Sum.inr 5073) = Sparse.eval nodeValue5073 (mixedVector B) := by
    change mixedMoment B node5073 node5073Labels = _
    exact sound5073 B hB hF
  have h5076 : mixedVector B (Sum.inr 5076) = Sparse.eval nodeValue5076 (mixedVector B) := by
    change mixedMoment B node5076 node5076Labels = _
    exact sound5076 B hB hF
  have h5104 : mixedVector B (Sum.inr 5104) = Sparse.eval nodeValue5104 (mixedVector B) := by
    change mixedMoment B node5104 node5104Labels = _
    exact sound5104 B hB hF
  simpa only [sourceForm2495, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4080, h4300, h4301, h4307, h4417, h4641, h4642, h4648, h4736, h4737, h4740, h4746, h4752, h4802, h4805, h4838, h4998, h5073, h5076, h5104, reducedSource2011] using sourceEq2495 B hB

theorem rowSound2011 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2011 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2011, numericCheck2011, reducedZero2011 B hB hF, mul_zero]

theorem reducedZero2012 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2012 (mixedVector B) = 0 := by
  have h4063 : mixedVector B (Sum.inr 4063) = Sparse.eval nodeValue4063 (mixedVector B) := by
    change mixedMoment B node4063 node4063Labels = _
    exact sound4063 B hB hF
  have h4064 : mixedVector B (Sum.inr 4064) = Sparse.eval nodeValue4064 (mixedVector B) := by
    change mixedMoment B node4064 node4064Labels = _
    exact sound4064 B hB hF
  have h4065 : mixedVector B (Sum.inr 4065) = Sparse.eval nodeValue4065 (mixedVector B) := by
    change mixedMoment B node4065 node4065Labels = _
    exact sound4065 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  have h4073 : mixedVector B (Sum.inr 4073) = Sparse.eval nodeValue4073 (mixedVector B) := by
    change mixedMoment B node4073 node4073Labels = _
    exact sound4073 B hB hF
  have h4074 : mixedVector B (Sum.inr 4074) = Sparse.eval nodeValue4074 (mixedVector B) := by
    change mixedMoment B node4074 node4074Labels = _
    exact sound4074 B hB hF
  have h4075 : mixedVector B (Sum.inr 4075) = Sparse.eval nodeValue4075 (mixedVector B) := by
    change mixedMoment B node4075 node4075Labels = _
    exact sound4075 B hB hF
  have h4077 : mixedVector B (Sum.inr 4077) = Sparse.eval nodeValue4077 (mixedVector B) := by
    change mixedMoment B node4077 node4077Labels = _
    exact sound4077 B hB hF
  have h4078 : mixedVector B (Sum.inr 4078) = Sparse.eval nodeValue4078 (mixedVector B) := by
    change mixedMoment B node4078 node4078Labels = _
    exact sound4078 B hB hF
  have h4079 : mixedVector B (Sum.inr 4079) = Sparse.eval nodeValue4079 (mixedVector B) := by
    change mixedMoment B node4079 node4079Labels = _
    exact sound4079 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  have h4090 : mixedVector B (Sum.inr 4090) = Sparse.eval nodeValue4090 (mixedVector B) := by
    change mixedMoment B node4090 node4090Labels = _
    exact sound4090 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2496, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4063, h4064, h4065, h4069, h4073, h4074, h4075, h4077, h4078, h4079, h4080, h4081, h4082, h4083, h4084, h4088, h4090, h4091, h4092, reducedSource2012] using sourceEq2496 B hB

theorem rowSound2012 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2012 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2012, numericCheck2012, reducedZero2012 B hB hF, mul_zero]

theorem reducedZero2013 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2013 (mixedVector B) = 0 := by
  have h3128 : mixedVector B (Sum.inr 3128) = Sparse.eval nodeValue3128 (mixedVector B) := by
    change mixedMoment B node3128 node3128Labels = _
    exact sound3128 B hB hF
  have h3130 : mixedVector B (Sum.inr 3130) = Sparse.eval nodeValue3130 (mixedVector B) := by
    change mixedMoment B node3130 node3130Labels = _
    exact sound3130 B hB hF
  have h3155 : mixedVector B (Sum.inr 3155) = Sparse.eval nodeValue3155 (mixedVector B) := by
    change mixedMoment B node3155 node3155Labels = _
    exact sound3155 B hB hF
  have h3390 : mixedVector B (Sum.inr 3390) = Sparse.eval nodeValue3390 (mixedVector B) := by
    change mixedMoment B node3390 node3390Labels = _
    exact sound3390 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm2497, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3128, h3130, h3155, h3390, h4083, reducedSource2013] using sourceEq2497 B hB

theorem rowSound2013 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2013 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2013, numericCheck2013, reducedZero2013 B hB hF, mul_zero]

theorem reducedZero2014 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2014 (mixedVector B) = 0 := by
  have h4541 : mixedVector B (Sum.inr 4541) = Sparse.eval nodeValue4541 (mixedVector B) := by
    change mixedMoment B node4541 node4541Labels = _
    exact sound4541 B hB hF
  have h4544 : mixedVector B (Sum.inr 4544) = Sparse.eval nodeValue4544 (mixedVector B) := by
    change mixedMoment B node4544 node4544Labels = _
    exact sound4544 B hB hF
  have h4622 : mixedVector B (Sum.inr 4622) = Sparse.eval nodeValue4622 (mixedVector B) := by
    change mixedMoment B node4622 node4622Labels = _
    exact sound4622 B hB hF
  have h4968 : mixedVector B (Sum.inr 4968) = Sparse.eval nodeValue4968 (mixedVector B) := by
    change mixedMoment B node4968 node4968Labels = _
    exact sound4968 B hB hF
  have h4971 : mixedVector B (Sum.inr 4971) = Sparse.eval nodeValue4971 (mixedVector B) := by
    change mixedMoment B node4971 node4971Labels = _
    exact sound4971 B hB hF
  have h5148 : mixedVector B (Sum.inr 5148) = Sparse.eval nodeValue5148 (mixedVector B) := by
    change mixedMoment B node5148 node5148Labels = _
    exact sound5148 B hB hF
  have h5149 : mixedVector B (Sum.inr 5149) = Sparse.eval nodeValue5149 (mixedVector B) := by
    change mixedMoment B node5149 node5149Labels = _
    exact sound5149 B hB hF
  have h5169 : mixedVector B (Sum.inr 5169) = Sparse.eval nodeValue5169 (mixedVector B) := by
    change mixedMoment B node5169 node5169Labels = _
    exact sound5169 B hB hF
  have h5172 : mixedVector B (Sum.inr 5172) = Sparse.eval nodeValue5172 (mixedVector B) := by
    change mixedMoment B node5172 node5172Labels = _
    exact sound5172 B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292 B hB hF
  have h5307 : mixedVector B (Sum.inr 5307) = Sparse.eval nodeValue5307 (mixedVector B) := by
    change mixedMoment B node5307 node5307Labels = _
    exact sound5307 B hB hF
  have h5386 : mixedVector B (Sum.inr 5386) = Sparse.eval nodeValue5386 (mixedVector B) := by
    change mixedMoment B node5386 node5386Labels = _
    exact sound5386 B hB hF
  have h5433 : mixedVector B (Sum.inr 5433) = Sparse.eval nodeValue5433 (mixedVector B) := by
    change mixedMoment B node5433 node5433Labels = _
    exact sound5433 B hB hF
  have h5440 : mixedVector B (Sum.inr 5440) = Sparse.eval nodeValue5440 (mixedVector B) := by
    change mixedMoment B node5440 node5440Labels = _
    exact sound5440 B hB hF
  simpa only [sourceForm2499, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4541, h4544, h4622, h4968, h4971, h5148, h5149, h5169, h5172, h5292, h5307, h5386, h5433, h5440, reducedSource2014] using sourceEq2499 B hB

theorem rowSound2014 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2014 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2014, numericCheck2014, reducedZero2014 B hB hF, mul_zero]

theorem reducedZero2015 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2015 (mixedVector B) = 0 := by
  have h4341 : mixedVector B (Sum.inr 4341) = Sparse.eval nodeValue4341 (mixedVector B) := by
    change mixedMoment B node4341 node4341Labels = _
    exact sound4341 B hB hF
  have h4344 : mixedVector B (Sum.inr 4344) = Sparse.eval nodeValue4344 (mixedVector B) := by
    change mixedMoment B node4344 node4344Labels = _
    exact sound4344 B hB hF
  have h4456 : mixedVector B (Sum.inr 4456) = Sparse.eval nodeValue4456 (mixedVector B) := by
    change mixedMoment B node4456 node4456Labels = _
    exact sound4456 B hB hF
  have h4939 : mixedVector B (Sum.inr 4939) = Sparse.eval nodeValue4939 (mixedVector B) := by
    change mixedMoment B node4939 node4939Labels = _
    exact sound4939 B hB hF
  have h4941 : mixedVector B (Sum.inr 4941) = Sparse.eval nodeValue4941 (mixedVector B) := by
    change mixedMoment B node4941 node4941Labels = _
    exact sound4941 B hB hF
  have h5134 : mixedVector B (Sum.inr 5134) = Sparse.eval nodeValue5134 (mixedVector B) := by
    change mixedMoment B node5134 node5134Labels = _
    exact sound5134 B hB hF
  have h5137 : mixedVector B (Sum.inr 5137) = Sparse.eval nodeValue5137 (mixedVector B) := by
    change mixedMoment B node5137 node5137Labels = _
    exact sound5137 B hB hF
  have h5168 : mixedVector B (Sum.inr 5168) = Sparse.eval nodeValue5168 (mixedVector B) := by
    change mixedMoment B node5168 node5168Labels = _
    exact sound5168 B hB hF
  have h5169 : mixedVector B (Sum.inr 5169) = Sparse.eval nodeValue5169 (mixedVector B) := by
    change mixedMoment B node5169 node5169Labels = _
    exact sound5169 B hB hF
  have h5257 : mixedVector B (Sum.inr 5257) = Sparse.eval nodeValue5257 (mixedVector B) := by
    change mixedMoment B node5257 node5257Labels = _
    exact sound5257 B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292 B hB hF
  have h5464 : mixedVector B (Sum.inr 5464) = Sparse.eval nodeValue5464 (mixedVector B) := by
    change mixedMoment B node5464 node5464Labels = _
    exact sound5464 B hB hF
  have h5482 : mixedVector B (Sum.inr 5482) = Sparse.eval nodeValue5482 (mixedVector B) := by
    change mixedMoment B node5482 node5482Labels = _
    exact sound5482 B hB hF
  have h5486 : mixedVector B (Sum.inr 5486) = Sparse.eval nodeValue5486 (mixedVector B) := by
    change mixedMoment B node5486 node5486Labels = _
    exact sound5486 B hB hF
  simpa only [sourceForm2500, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4341, h4344, h4456, h4939, h4941, h5134, h5137, h5168, h5169, h5257, h5292, h5464, h5482, h5486, reducedSource2015] using sourceEq2500 B hB

theorem rowSound2015 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2015 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2015, numericCheck2015, reducedZero2015 B hB hF, mul_zero]

theorem sourceRowsAt2000 : MixedData.sourceRows (2000 : Fin 2425) =
    MixedData.row2000 := by decide +kernel

theorem sourceRowsAt2001 : MixedData.sourceRows (2001 : Fin 2425) =
    MixedData.row2001 := by decide +kernel

theorem sourceRowsAt2002 : MixedData.sourceRows (2002 : Fin 2425) =
    MixedData.row2002 := by decide +kernel

theorem sourceRowsAt2003 : MixedData.sourceRows (2003 : Fin 2425) =
    MixedData.row2003 := by decide +kernel

theorem sourceRowsAt2004 : MixedData.sourceRows (2004 : Fin 2425) =
    MixedData.row2004 := by decide +kernel

theorem sourceRowsAt2005 : MixedData.sourceRows (2005 : Fin 2425) =
    MixedData.row2005 := by decide +kernel

theorem sourceRowsAt2006 : MixedData.sourceRows (2006 : Fin 2425) =
    MixedData.row2006 := by decide +kernel

theorem sourceRowsAt2007 : MixedData.sourceRows (2007 : Fin 2425) =
    MixedData.row2007 := by decide +kernel

theorem sourceRowsAt2008 : MixedData.sourceRows (2008 : Fin 2425) =
    MixedData.row2008 := by decide +kernel

theorem sourceRowsAt2009 : MixedData.sourceRows (2009 : Fin 2425) =
    MixedData.row2009 := by decide +kernel

theorem sourceRowsAt2010 : MixedData.sourceRows (2010 : Fin 2425) =
    MixedData.row2010 := by decide +kernel

theorem sourceRowsAt2011 : MixedData.sourceRows (2011 : Fin 2425) =
    MixedData.row2011 := by decide +kernel

theorem sourceRowsAt2012 : MixedData.sourceRows (2012 : Fin 2425) =
    MixedData.row2012 := by decide +kernel

theorem sourceRowsAt2013 : MixedData.sourceRows (2013 : Fin 2425) =
    MixedData.row2013 := by decide +kernel

theorem sourceRowsAt2014 : MixedData.sourceRows (2014 : Fin 2425) =
    MixedData.row2014 := by decide +kernel

theorem sourceRowsAt2015 : MixedData.sourceRows (2015 : Fin 2425) =
    MixedData.row2015 := by decide +kernel

theorem chunkSound125 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 125) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 2000 ∨ k.val = 2001 ∨ k.val = 2002 ∨ k.val = 2003 ∨ k.val = 2004 ∨ k.val = 2005 ∨ k.val = 2006 ∨ k.val = 2007 ∨ k.val = 2008 ∨ k.val = 2009 ∨ k.val = 2010 ∨ k.val = 2011 ∨ k.val = 2012 ∨ k.val = 2013 ∨ k.val = 2014 ∨ k.val = 2015 := by omega
  rcases heq with h2000 | h2001 | h2002 | h2003 | h2004 | h2005 | h2006 | h2007 | h2008 | h2009 | h2010 | h2011 | h2012 | h2013 | h2014 | h2015
  · have he : k = (2000 : Fin 2425) := Fin.ext h2000
    subst k
    rw [sourceRowsAt2000]
    exact rowSound2000 B hB hF
  · have he : k = (2001 : Fin 2425) := Fin.ext h2001
    subst k
    rw [sourceRowsAt2001]
    exact rowSound2001 B hB hF
  · have he : k = (2002 : Fin 2425) := Fin.ext h2002
    subst k
    rw [sourceRowsAt2002]
    exact rowSound2002 B hB hF
  · have he : k = (2003 : Fin 2425) := Fin.ext h2003
    subst k
    rw [sourceRowsAt2003]
    exact rowSound2003 B hB hF
  · have he : k = (2004 : Fin 2425) := Fin.ext h2004
    subst k
    rw [sourceRowsAt2004]
    exact rowSound2004 B hB hF
  · have he : k = (2005 : Fin 2425) := Fin.ext h2005
    subst k
    rw [sourceRowsAt2005]
    exact rowSound2005 B hB hF
  · have he : k = (2006 : Fin 2425) := Fin.ext h2006
    subst k
    rw [sourceRowsAt2006]
    exact rowSound2006 B hB hF
  · have he : k = (2007 : Fin 2425) := Fin.ext h2007
    subst k
    rw [sourceRowsAt2007]
    exact rowSound2007 B hB hF
  · have he : k = (2008 : Fin 2425) := Fin.ext h2008
    subst k
    rw [sourceRowsAt2008]
    exact rowSound2008 B hB hF
  · have he : k = (2009 : Fin 2425) := Fin.ext h2009
    subst k
    rw [sourceRowsAt2009]
    exact rowSound2009 B hB hF
  · have he : k = (2010 : Fin 2425) := Fin.ext h2010
    subst k
    rw [sourceRowsAt2010]
    exact rowSound2010 B hB hF
  · have he : k = (2011 : Fin 2425) := Fin.ext h2011
    subst k
    rw [sourceRowsAt2011]
    exact rowSound2011 B hB hF
  · have he : k = (2012 : Fin 2425) := Fin.ext h2012
    subst k
    rw [sourceRowsAt2012]
    exact rowSound2012 B hB hF
  · have he : k = (2013 : Fin 2425) := Fin.ext h2013
    subst k
    rw [sourceRowsAt2013]
    exact rowSound2013 B hB hF
  · have he : k = (2014 : Fin 2425) := Fin.ext h2014
    subst k
    rw [sourceRowsAt2014]
    exact rowSound2014 B hB hF
  · have he : k = (2015 : Fin 2425) := Fin.ext h2015
    subst k
    rw [sourceRowsAt2015]
    exact rowSound2015 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
