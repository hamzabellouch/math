import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic117
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources72

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1872 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1872 (mixedVector B) = 0 := by
  have h4415 : mixedVector B (Sum.inr 4415) = Sparse.eval nodeValue4415 (mixedVector B) := by
    change mixedMoment B node4415 node4415Labels = _
    exact sound4415 B hB hF
  have h4419 : mixedVector B (Sum.inr 4419) = Sparse.eval nodeValue4419 (mixedVector B) := by
    change mixedMoment B node4419 node4419Labels = _
    exact sound4419 B hB hF
  have h4427 : mixedVector B (Sum.inr 4427) = Sparse.eval nodeValue4427 (mixedVector B) := by
    change mixedMoment B node4427 node4427Labels = _
    exact sound4427 B hB hF
  have h4487 : mixedVector B (Sum.inr 4487) = Sparse.eval nodeValue4487 (mixedVector B) := by
    change mixedMoment B node4487 node4487Labels = _
    exact sound4487 B hB hF
  have h4732 : mixedVector B (Sum.inr 4732) = Sparse.eval nodeValue4732 (mixedVector B) := by
    change mixedMoment B node4732 node4732Labels = _
    exact sound4732 B hB hF
  have h4745 : mixedVector B (Sum.inr 4745) = Sparse.eval nodeValue4745 (mixedVector B) := by
    change mixedMoment B node4745 node4745Labels = _
    exact sound4745 B hB hF
  have h4750 : mixedVector B (Sum.inr 4750) = Sparse.eval nodeValue4750 (mixedVector B) := by
    change mixedMoment B node4750 node4750Labels = _
    exact sound4750 B hB hF
  have h4782 : mixedVector B (Sum.inr 4782) = Sparse.eval nodeValue4782 (mixedVector B) := by
    change mixedMoment B node4782 node4782Labels = _
    exact sound4782 B hB hF
  have h4785 : mixedVector B (Sum.inr 4785) = Sparse.eval nodeValue4785 (mixedVector B) := by
    change mixedMoment B node4785 node4785Labels = _
    exact sound4785 B hB hF
  have h4795 : mixedVector B (Sum.inr 4795) = Sparse.eval nodeValue4795 (mixedVector B) := by
    change mixedMoment B node4795 node4795Labels = _
    exact sound4795 B hB hF
  have h4810 : mixedVector B (Sum.inr 4810) = Sparse.eval nodeValue4810 (mixedVector B) := by
    change mixedMoment B node4810 node4810Labels = _
    exact sound4810 B hB hF
  have h4811 : mixedVector B (Sum.inr 4811) = Sparse.eval nodeValue4811 (mixedVector B) := by
    change mixedMoment B node4811 node4811Labels = _
    exact sound4811 B hB hF
  have h4821 : mixedVector B (Sum.inr 4821) = Sparse.eval nodeValue4821 (mixedVector B) := by
    change mixedMoment B node4821 node4821Labels = _
    exact sound4821 B hB hF
  have h4825 : mixedVector B (Sum.inr 4825) = Sparse.eval nodeValue4825 (mixedVector B) := by
    change mixedMoment B node4825 node4825Labels = _
    exact sound4825 B hB hF
  have h4846 : mixedVector B (Sum.inr 4846) = Sparse.eval nodeValue4846 (mixedVector B) := by
    change mixedMoment B node4846 node4846Labels = _
    exact sound4846 B hB hF
  have h4856 : mixedVector B (Sum.inr 4856) = Sparse.eval nodeValue4856 (mixedVector B) := by
    change mixedMoment B node4856 node4856Labels = _
    exact sound4856 B hB hF
  have h4875 : mixedVector B (Sum.inr 4875) = Sparse.eval nodeValue4875 (mixedVector B) := by
    change mixedMoment B node4875 node4875Labels = _
    exact sound4875 B hB hF
  have h5081 : mixedVector B (Sum.inr 5081) = Sparse.eval nodeValue5081 (mixedVector B) := by
    change mixedMoment B node5081 node5081Labels = _
    exact sound5081 B hB hF
  have h5130 : mixedVector B (Sum.inr 5130) = Sparse.eval nodeValue5130 (mixedVector B) := by
    change mixedMoment B node5130 node5130Labels = _
    exact sound5130 B hB hF
  have h5152 : mixedVector B (Sum.inr 5152) = Sparse.eval nodeValue5152 (mixedVector B) := by
    change mixedMoment B node5152 node5152Labels = _
    exact sound5152 B hB hF
  have h5177 : mixedVector B (Sum.inr 5177) = Sparse.eval nodeValue5177 (mixedVector B) := by
    change mixedMoment B node5177 node5177Labels = _
    exact sound5177 B hB hF
  simpa only [sourceForm2291, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4415, h4419, h4427, h4487, h4732, h4745, h4750, h4782, h4785, h4795, h4810, h4811, h4821, h4825, h4846, h4856, h4875, h5081, h5130, h5152, h5177, reducedSource1872] using sourceEq2291 B hB

theorem rowSound1872 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1872 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1872, numericCheck1872, reducedZero1872 B hB hF, mul_zero]

theorem reducedZero1873 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1873 (mixedVector B) = 0 := by
  have h4348 : mixedVector B (Sum.inr 4348) = Sparse.eval nodeValue4348 (mixedVector B) := by
    change mixedMoment B node4348 node4348Labels = _
    exact sound4348 B hB hF
  have h4359 : mixedVector B (Sum.inr 4359) = Sparse.eval nodeValue4359 (mixedVector B) := by
    change mixedMoment B node4359 node4359Labels = _
    exact sound4359 B hB hF
  have h4362 : mixedVector B (Sum.inr 4362) = Sparse.eval nodeValue4362 (mixedVector B) := by
    change mixedMoment B node4362 node4362Labels = _
    exact sound4362 B hB hF
  have h4510 : mixedVector B (Sum.inr 4510) = Sparse.eval nodeValue4510 (mixedVector B) := by
    change mixedMoment B node4510 node4510Labels = _
    exact sound4510 B hB hF
  have h4678 : mixedVector B (Sum.inr 4678) = Sparse.eval nodeValue4678 (mixedVector B) := by
    change mixedMoment B node4678 node4678Labels = _
    exact sound4678 B hB hF
  have h4683 : mixedVector B (Sum.inr 4683) = Sparse.eval nodeValue4683 (mixedVector B) := by
    change mixedMoment B node4683 node4683Labels = _
    exact sound4683 B hB hF
  have h4691 : mixedVector B (Sum.inr 4691) = Sparse.eval nodeValue4691 (mixedVector B) := by
    change mixedMoment B node4691 node4691Labels = _
    exact sound4691 B hB hF
  have h4694 : mixedVector B (Sum.inr 4694) = Sparse.eval nodeValue4694 (mixedVector B) := by
    change mixedMoment B node4694 node4694Labels = _
    exact sound4694 B hB hF
  have h4702 : mixedVector B (Sum.inr 4702) = Sparse.eval nodeValue4702 (mixedVector B) := by
    change mixedMoment B node4702 node4702Labels = _
    exact sound4702 B hB hF
  have h4762 : mixedVector B (Sum.inr 4762) = Sparse.eval nodeValue4762 (mixedVector B) := by
    change mixedMoment B node4762 node4762Labels = _
    exact sound4762 B hB hF
  have h4832 : mixedVector B (Sum.inr 4832) = Sparse.eval nodeValue4832 (mixedVector B) := by
    change mixedMoment B node4832 node4832Labels = _
    exact sound4832 B hB hF
  have h4836 : mixedVector B (Sum.inr 4836) = Sparse.eval nodeValue4836 (mixedVector B) := by
    change mixedMoment B node4836 node4836Labels = _
    exact sound4836 B hB hF
  have h4837 : mixedVector B (Sum.inr 4837) = Sparse.eval nodeValue4837 (mixedVector B) := by
    change mixedMoment B node4837 node4837Labels = _
    exact sound4837 B hB hF
  have h4844 : mixedVector B (Sum.inr 4844) = Sparse.eval nodeValue4844 (mixedVector B) := by
    change mixedMoment B node4844 node4844Labels = _
    exact sound4844 B hB hF
  have h4845 : mixedVector B (Sum.inr 4845) = Sparse.eval nodeValue4845 (mixedVector B) := by
    change mixedMoment B node4845 node4845Labels = _
    exact sound4845 B hB hF
  have h4897 : mixedVector B (Sum.inr 4897) = Sparse.eval nodeValue4897 (mixedVector B) := by
    change mixedMoment B node4897 node4897Labels = _
    exact sound4897 B hB hF
  have h4899 : mixedVector B (Sum.inr 4899) = Sparse.eval nodeValue4899 (mixedVector B) := by
    change mixedMoment B node4899 node4899Labels = _
    exact sound4899 B hB hF
  have h5222 : mixedVector B (Sum.inr 5222) = Sparse.eval nodeValue5222 (mixedVector B) := by
    change mixedMoment B node5222 node5222Labels = _
    exact sound5222 B hB hF
  have h5235 : mixedVector B (Sum.inr 5235) = Sparse.eval nodeValue5235 (mixedVector B) := by
    change mixedMoment B node5235 node5235Labels = _
    exact sound5235 B hB hF
  have h5261 : mixedVector B (Sum.inr 5261) = Sparse.eval nodeValue5261 (mixedVector B) := by
    change mixedMoment B node5261 node5261Labels = _
    exact sound5261 B hB hF
  have h5268 : mixedVector B (Sum.inr 5268) = Sparse.eval nodeValue5268 (mixedVector B) := by
    change mixedMoment B node5268 node5268Labels = _
    exact sound5268 B hB hF
  simpa only [sourceForm2295, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4348, h4359, h4362, h4510, h4678, h4683, h4691, h4694, h4702, h4762, h4832, h4836, h4837, h4844, h4845, h4897, h4899, h5222, h5235, h5261, h5268, reducedSource1873] using sourceEq2295 B hB

theorem rowSound1873 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1873 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1873, numericCheck1873, reducedZero1873 B hB hF, mul_zero]

theorem reducedZero1874 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1874 (mixedVector B) = 0 := by
  have h1347 : mixedVector B (Sum.inr 1347) = Sparse.eval nodeValue1347 (mixedVector B) := by
    change mixedMoment B node1347 node1347Labels = _
    exact sound1347 B hB hF
  have h1348 : mixedVector B (Sum.inr 1348) = Sparse.eval nodeValue1348 (mixedVector B) := by
    change mixedMoment B node1348 node1348Labels = _
    exact sound1348 B hB hF
  have h1349 : mixedVector B (Sum.inr 1349) = Sparse.eval nodeValue1349 (mixedVector B) := by
    change mixedMoment B node1349 node1349Labels = _
    exact sound1349 B hB hF
  have h1454 : mixedVector B (Sum.inr 1454) = Sparse.eval nodeValue1454 (mixedVector B) := by
    change mixedMoment B node1454 node1454Labels = _
    exact sound1454 B hB hF
  have h1828 : mixedVector B (Sum.inr 1828) = Sparse.eval nodeValue1828 (mixedVector B) := by
    change mixedMoment B node1828 node1828Labels = _
    exact sound1828 B hB hF
  have h1832 : mixedVector B (Sum.inr 1832) = Sparse.eval nodeValue1832 (mixedVector B) := by
    change mixedMoment B node1832 node1832Labels = _
    exact sound1832 B hB hF
  have h2136 : mixedVector B (Sum.inr 2136) = Sparse.eval nodeValue2136 (mixedVector B) := by
    change mixedMoment B node2136 node2136Labels = _
    exact sound2136 B hB hF
  have h2716 : mixedVector B (Sum.inr 2716) = Sparse.eval nodeValue2716 (mixedVector B) := by
    change mixedMoment B node2716 node2716Labels = _
    exact sound2716 B hB hF
  have h2734 : mixedVector B (Sum.inr 2734) = Sparse.eval nodeValue2734 (mixedVector B) := by
    change mixedMoment B node2734 node2734Labels = _
    exact sound2734 B hB hF
  have h2778 : mixedVector B (Sum.inr 2778) = Sparse.eval nodeValue2778 (mixedVector B) := by
    change mixedMoment B node2778 node2778Labels = _
    exact sound2778 B hB hF
  have h3031 : mixedVector B (Sum.inr 3031) = Sparse.eval nodeValue3031 (mixedVector B) := by
    change mixedMoment B node3031 node3031Labels = _
    exact sound3031 B hB hF
  have h3033 : mixedVector B (Sum.inr 3033) = Sparse.eval nodeValue3033 (mixedVector B) := by
    change mixedMoment B node3033 node3033Labels = _
    exact sound3033 B hB hF
  have h3046 : mixedVector B (Sum.inr 3046) = Sparse.eval nodeValue3046 (mixedVector B) := by
    change mixedMoment B node3046 node3046Labels = _
    exact sound3046 B hB hF
  have h3062 : mixedVector B (Sum.inr 3062) = Sparse.eval nodeValue3062 (mixedVector B) := by
    change mixedMoment B node3062 node3062Labels = _
    exact sound3062 B hB hF
  have h3082 : mixedVector B (Sum.inr 3082) = Sparse.eval nodeValue3082 (mixedVector B) := by
    change mixedMoment B node3082 node3082Labels = _
    exact sound3082 B hB hF
  have h3090 : mixedVector B (Sum.inr 3090) = Sparse.eval nodeValue3090 (mixedVector B) := by
    change mixedMoment B node3090 node3090Labels = _
    exact sound3090 B hB hF
  have h3095 : mixedVector B (Sum.inr 3095) = Sparse.eval nodeValue3095 (mixedVector B) := by
    change mixedMoment B node3095 node3095Labels = _
    exact sound3095 B hB hF
  have h3114 : mixedVector B (Sum.inr 3114) = Sparse.eval nodeValue3114 (mixedVector B) := by
    change mixedMoment B node3114 node3114Labels = _
    exact sound3114 B hB hF
  have h3143 : mixedVector B (Sum.inr 3143) = Sparse.eval nodeValue3143 (mixedVector B) := by
    change mixedMoment B node3143 node3143Labels = _
    exact sound3143 B hB hF
  have h3145 : mixedVector B (Sum.inr 3145) = Sparse.eval nodeValue3145 (mixedVector B) := by
    change mixedMoment B node3145 node3145Labels = _
    exact sound3145 B hB hF
  have h3215 : mixedVector B (Sum.inr 3215) = Sparse.eval nodeValue3215 (mixedVector B) := by
    change mixedMoment B node3215 node3215Labels = _
    exact sound3215 B hB hF
  simpa only [sourceForm2296, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1347, h1348, h1349, h1454, h1828, h1832, h2136, h2716, h2734, h2778, h3031, h3033, h3046, h3062, h3082, h3090, h3095, h3114, h3143, h3145, h3215, reducedSource1874] using sourceEq2296 B hB

theorem rowSound1874 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1874 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1874, numericCheck1874, reducedZero1874 B hB hF, mul_zero]

theorem reducedZero1875 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1875 (mixedVector B) = 0 := by
  have h1669 : mixedVector B (Sum.inr 1669) = Sparse.eval nodeValue1669 (mixedVector B) := by
    change mixedMoment B node1669 node1669Labels = _
    exact sound1669 B hB hF
  have h1683 : mixedVector B (Sum.inr 1683) = Sparse.eval nodeValue1683 (mixedVector B) := by
    change mixedMoment B node1683 node1683Labels = _
    exact sound1683 B hB hF
  have h1687 : mixedVector B (Sum.inr 1687) = Sparse.eval nodeValue1687 (mixedVector B) := by
    change mixedMoment B node1687 node1687Labels = _
    exact sound1687 B hB hF
  have h1741 : mixedVector B (Sum.inr 1741) = Sparse.eval nodeValue1741 (mixedVector B) := by
    change mixedMoment B node1741 node1741Labels = _
    exact sound1741 B hB hF
  have h2143 : mixedVector B (Sum.inr 2143) = Sparse.eval nodeValue2143 (mixedVector B) := by
    change mixedMoment B node2143 node2143Labels = _
    exact sound2143 B hB hF
  have h2146 : mixedVector B (Sum.inr 2146) = Sparse.eval nodeValue2146 (mixedVector B) := by
    change mixedMoment B node2146 node2146Labels = _
    exact sound2146 B hB hF
  have h2159 : mixedVector B (Sum.inr 2159) = Sparse.eval nodeValue2159 (mixedVector B) := by
    change mixedMoment B node2159 node2159Labels = _
    exact sound2159 B hB hF
  have h2163 : mixedVector B (Sum.inr 2163) = Sparse.eval nodeValue2163 (mixedVector B) := by
    change mixedMoment B node2163 node2163Labels = _
    exact sound2163 B hB hF
  have h2171 : mixedVector B (Sum.inr 2171) = Sparse.eval nodeValue2171 (mixedVector B) := by
    change mixedMoment B node2171 node2171Labels = _
    exact sound2171 B hB hF
  have h2180 : mixedVector B (Sum.inr 2180) = Sparse.eval nodeValue2180 (mixedVector B) := by
    change mixedMoment B node2180 node2180Labels = _
    exact sound2180 B hB hF
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
  have h2222 : mixedVector B (Sum.inr 2222) = Sparse.eval nodeValue2222 (mixedVector B) := by
    change mixedMoment B node2222 node2222Labels = _
    exact sound2222 B hB hF
  have h2268 : mixedVector B (Sum.inr 2268) = Sparse.eval nodeValue2268 (mixedVector B) := by
    change mixedMoment B node2268 node2268Labels = _
    exact sound2268 B hB hF
  have h2281 : mixedVector B (Sum.inr 2281) = Sparse.eval nodeValue2281 (mixedVector B) := by
    change mixedMoment B node2281 node2281Labels = _
    exact sound2281 B hB hF
  have h2664 : mixedVector B (Sum.inr 2664) = Sparse.eval nodeValue2664 (mixedVector B) := by
    change mixedMoment B node2664 node2664Labels = _
    exact sound2664 B hB hF
  have h2680 : mixedVector B (Sum.inr 2680) = Sparse.eval nodeValue2680 (mixedVector B) := by
    change mixedMoment B node2680 node2680Labels = _
    exact sound2680 B hB hF
  have h2726 : mixedVector B (Sum.inr 2726) = Sparse.eval nodeValue2726 (mixedVector B) := by
    change mixedMoment B node2726 node2726Labels = _
    exact sound2726 B hB hF
  have h2734 : mixedVector B (Sum.inr 2734) = Sparse.eval nodeValue2734 (mixedVector B) := by
    change mixedMoment B node2734 node2734Labels = _
    exact sound2734 B hB hF
  simpa only [sourceForm2297, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1669, h1683, h1687, h1741, h2143, h2146, h2159, h2163, h2171, h2180, h2193, h2197, h2208, h2218, h2222, h2268, h2281, h2664, h2680, h2726, h2734, reducedSource1875] using sourceEq2297 B hB

theorem rowSound1875 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1875 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1875, numericCheck1875, reducedZero1875 B hB hF, mul_zero]

theorem reducedZero1876 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1876 (mixedVector B) = 0 := by
  have h1809 : mixedVector B (Sum.inr 1809) = Sparse.eval nodeValue1809 (mixedVector B) := by
    change mixedMoment B node1809 node1809Labels = _
    exact sound1809 B hB hF
  have h1817 : mixedVector B (Sum.inr 1817) = Sparse.eval nodeValue1817 (mixedVector B) := by
    change mixedMoment B node1817 node1817Labels = _
    exact sound1817 B hB hF
  have h1820 : mixedVector B (Sum.inr 1820) = Sparse.eval nodeValue1820 (mixedVector B) := by
    change mixedMoment B node1820 node1820Labels = _
    exact sound1820 B hB hF
  have h2065 : mixedVector B (Sum.inr 2065) = Sparse.eval nodeValue2065 (mixedVector B) := by
    change mixedMoment B node2065 node2065Labels = _
    exact sound2065 B hB hF
  have h3396 : mixedVector B (Sum.inr 3396) = Sparse.eval nodeValue3396 (mixedVector B) := by
    change mixedMoment B node3396 node3396Labels = _
    exact sound3396 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm2298, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1809, h1817, h1820, h2065, h3396, h4085, reducedSource1876] using sourceEq2298 B hB

theorem rowSound1876 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1876 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1876, numericCheck1876, reducedZero1876 B hB hF, mul_zero]

theorem reducedZero1877 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1877 (mixedVector B) = 0 := by
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  have h4349 : mixedVector B (Sum.inr 4349) = Sparse.eval nodeValue4349 (mixedVector B) := by
    change mixedMoment B node4349 node4349Labels = _
    exact sound4349 B hB hF
  have h4360 : mixedVector B (Sum.inr 4360) = Sparse.eval nodeValue4360 (mixedVector B) := by
    change mixedMoment B node4360 node4360Labels = _
    exact sound4360 B hB hF
  have h4361 : mixedVector B (Sum.inr 4361) = Sparse.eval nodeValue4361 (mixedVector B) := by
    change mixedMoment B node4361 node4361Labels = _
    exact sound4361 B hB hF
  have h4511 : mixedVector B (Sum.inr 4511) = Sparse.eval nodeValue4511 (mixedVector B) := by
    change mixedMoment B node4511 node4511Labels = _
    exact sound4511 B hB hF
  have h4684 : mixedVector B (Sum.inr 4684) = Sparse.eval nodeValue4684 (mixedVector B) := by
    change mixedMoment B node4684 node4684Labels = _
    exact sound4684 B hB hF
  have h4692 : mixedVector B (Sum.inr 4692) = Sparse.eval nodeValue4692 (mixedVector B) := by
    change mixedMoment B node4692 node4692Labels = _
    exact sound4692 B hB hF
  have h4693 : mixedVector B (Sum.inr 4693) = Sparse.eval nodeValue4693 (mixedVector B) := by
    change mixedMoment B node4693 node4693Labels = _
    exact sound4693 B hB hF
  have h4763 : mixedVector B (Sum.inr 4763) = Sparse.eval nodeValue4763 (mixedVector B) := by
    change mixedMoment B node4763 node4763Labels = _
    exact sound4763 B hB hF
  have h4769 : mixedVector B (Sum.inr 4769) = Sparse.eval nodeValue4769 (mixedVector B) := by
    change mixedMoment B node4769 node4769Labels = _
    exact sound4769 B hB hF
  have h4770 : mixedVector B (Sum.inr 4770) = Sparse.eval nodeValue4770 (mixedVector B) := by
    change mixedMoment B node4770 node4770Labels = _
    exact sound4770 B hB hF
  have h4834 : mixedVector B (Sum.inr 4834) = Sparse.eval nodeValue4834 (mixedVector B) := by
    change mixedMoment B node4834 node4834Labels = _
    exact sound4834 B hB hF
  have h4835 : mixedVector B (Sum.inr 4835) = Sparse.eval nodeValue4835 (mixedVector B) := by
    change mixedMoment B node4835 node4835Labels = _
    exact sound4835 B hB hF
  have h4841 : mixedVector B (Sum.inr 4841) = Sparse.eval nodeValue4841 (mixedVector B) := by
    change mixedMoment B node4841 node4841Labels = _
    exact sound4841 B hB hF
  have h4843 : mixedVector B (Sum.inr 4843) = Sparse.eval nodeValue4843 (mixedVector B) := by
    change mixedMoment B node4843 node4843Labels = _
    exact sound4843 B hB hF
  have h4846 : mixedVector B (Sum.inr 4846) = Sparse.eval nodeValue4846 (mixedVector B) := by
    change mixedMoment B node4846 node4846Labels = _
    exact sound4846 B hB hF
  have h4901 : mixedVector B (Sum.inr 4901) = Sparse.eval nodeValue4901 (mixedVector B) := by
    change mixedMoment B node4901 node4901Labels = _
    exact sound4901 B hB hF
  have h5238 : mixedVector B (Sum.inr 5238) = Sparse.eval nodeValue5238 (mixedVector B) := by
    change mixedMoment B node5238 node5238Labels = _
    exact sound5238 B hB hF
  have h5248 : mixedVector B (Sum.inr 5248) = Sparse.eval nodeValue5248 (mixedVector B) := by
    change mixedMoment B node5248 node5248Labels = _
    exact sound5248 B hB hF
  have h5274 : mixedVector B (Sum.inr 5274) = Sparse.eval nodeValue5274 (mixedVector B) := by
    change mixedMoment B node5274 node5274Labels = _
    exact sound5274 B hB hF
  have h5275 : mixedVector B (Sum.inr 5275) = Sparse.eval nodeValue5275 (mixedVector B) := by
    change mixedMoment B node5275 node5275Labels = _
    exact sound5275 B hB hF
  simpa only [sourceForm2302, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4084, h4349, h4360, h4361, h4511, h4684, h4692, h4693, h4763, h4769, h4770, h4834, h4835, h4841, h4843, h4846, h4901, h5238, h5248, h5274, h5275, reducedSource1877] using sourceEq2302 B hB

theorem rowSound1877 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1877 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1877, numericCheck1877, reducedZero1877 B hB hF, mul_zero]

theorem reducedZero1878 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1878 (mixedVector B) = 0 := by
  have h1675 : mixedVector B (Sum.inr 1675) = Sparse.eval nodeValue1675 (mixedVector B) := by
    change mixedMoment B node1675 node1675Labels = _
    exact sound1675 B hB hF
  have h1693 : mixedVector B (Sum.inr 1693) = Sparse.eval nodeValue1693 (mixedVector B) := by
    change mixedMoment B node1693 node1693Labels = _
    exact sound1693 B hB hF
  have h1694 : mixedVector B (Sum.inr 1694) = Sparse.eval nodeValue1694 (mixedVector B) := by
    change mixedMoment B node1694 node1694Labels = _
    exact sound1694 B hB hF
  have h1755 : mixedVector B (Sum.inr 1755) = Sparse.eval nodeValue1755 (mixedVector B) := by
    change mixedMoment B node1755 node1755Labels = _
    exact sound1755 B hB hF
  have h2152 : mixedVector B (Sum.inr 2152) = Sparse.eval nodeValue2152 (mixedVector B) := by
    change mixedMoment B node2152 node2152Labels = _
    exact sound2152 B hB hF
  have h2168 : mixedVector B (Sum.inr 2168) = Sparse.eval nodeValue2168 (mixedVector B) := by
    change mixedMoment B node2168 node2168Labels = _
    exact sound2168 B hB hF
  have h2169 : mixedVector B (Sum.inr 2169) = Sparse.eval nodeValue2169 (mixedVector B) := by
    change mixedMoment B node2169 node2169Labels = _
    exact sound2169 B hB hF
  have h2174 : mixedVector B (Sum.inr 2174) = Sparse.eval nodeValue2174 (mixedVector B) := by
    change mixedMoment B node2174 node2174Labels = _
    exact sound2174 B hB hF
  have h2185 : mixedVector B (Sum.inr 2185) = Sparse.eval nodeValue2185 (mixedVector B) := by
    change mixedMoment B node2185 node2185Labels = _
    exact sound2185 B hB hF
  have h2186 : mixedVector B (Sum.inr 2186) = Sparse.eval nodeValue2186 (mixedVector B) := by
    change mixedMoment B node2186 node2186Labels = _
    exact sound2186 B hB hF
  have h2205 : mixedVector B (Sum.inr 2205) = Sparse.eval nodeValue2205 (mixedVector B) := by
    change mixedMoment B node2205 node2205Labels = _
    exact sound2205 B hB hF
  have h2206 : mixedVector B (Sum.inr 2206) = Sparse.eval nodeValue2206 (mixedVector B) := by
    change mixedMoment B node2206 node2206Labels = _
    exact sound2206 B hB hF
  have h2228 : mixedVector B (Sum.inr 2228) = Sparse.eval nodeValue2228 (mixedVector B) := by
    change mixedMoment B node2228 node2228Labels = _
    exact sound2228 B hB hF
  have h2229 : mixedVector B (Sum.inr 2229) = Sparse.eval nodeValue2229 (mixedVector B) := by
    change mixedMoment B node2229 node2229Labels = _
    exact sound2229 B hB hF
  have h2230 : mixedVector B (Sum.inr 2230) = Sparse.eval nodeValue2230 (mixedVector B) := by
    change mixedMoment B node2230 node2230Labels = _
    exact sound2230 B hB hF
  have h2293 : mixedVector B (Sum.inr 2293) = Sparse.eval nodeValue2293 (mixedVector B) := by
    change mixedMoment B node2293 node2293Labels = _
    exact sound2293 B hB hF
  have h2686 : mixedVector B (Sum.inr 2686) = Sparse.eval nodeValue2686 (mixedVector B) := by
    change mixedMoment B node2686 node2686Labels = _
    exact sound2686 B hB hF
  have h2705 : mixedVector B (Sum.inr 2705) = Sparse.eval nodeValue2705 (mixedVector B) := by
    change mixedMoment B node2705 node2705Labels = _
    exact sound2705 B hB hF
  have h2742 : mixedVector B (Sum.inr 2742) = Sparse.eval nodeValue2742 (mixedVector B) := by
    change mixedMoment B node2742 node2742Labels = _
    exact sound2742 B hB hF
  have h2743 : mixedVector B (Sum.inr 2743) = Sparse.eval nodeValue2743 (mixedVector B) := by
    change mixedMoment B node2743 node2743Labels = _
    exact sound2743 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2303, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1675, h1693, h1694, h1755, h2152, h2168, h2169, h2174, h2185, h2186, h2205, h2206, h2228, h2229, h2230, h2293, h2686, h2705, h2742, h2743, h4084, reducedSource1878] using sourceEq2303 B hB

theorem rowSound1878 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1878 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1878, numericCheck1878, reducedZero1878 B hB hF, mul_zero]

theorem reducedZero1879 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1879 (mixedVector B) = 0 := by
  have h1810 : mixedVector B (Sum.inr 1810) = Sparse.eval nodeValue1810 (mixedVector B) := by
    change mixedMoment B node1810 node1810Labels = _
    exact sound1810 B hB hF
  have h1818 : mixedVector B (Sum.inr 1818) = Sparse.eval nodeValue1818 (mixedVector B) := by
    change mixedMoment B node1818 node1818Labels = _
    exact sound1818 B hB hF
  have h1819 : mixedVector B (Sum.inr 1819) = Sparse.eval nodeValue1819 (mixedVector B) := by
    change mixedMoment B node1819 node1819Labels = _
    exact sound1819 B hB hF
  have h2066 : mixedVector B (Sum.inr 2066) = Sparse.eval nodeValue2066 (mixedVector B) := by
    change mixedMoment B node2066 node2066Labels = _
    exact sound2066 B hB hF
  have h3397 : mixedVector B (Sum.inr 3397) = Sparse.eval nodeValue3397 (mixedVector B) := by
    change mixedMoment B node3397 node3397Labels = _
    exact sound3397 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2304, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1810, h1818, h1819, h2066, h3397, h4084, reducedSource1879] using sourceEq2304 B hB

theorem rowSound1879 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1879 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1879, numericCheck1879, reducedZero1879 B hB hF, mul_zero]

theorem reducedZero1880 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1880 (mixedVector B) = 0 := by
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  have h4288 : mixedVector B (Sum.inr 4288) = Sparse.eval nodeValue4288 (mixedVector B) := by
    change mixedMoment B node4288 node4288Labels = _
    exact sound4288 B hB hF
  have h4295 : mixedVector B (Sum.inr 4295) = Sparse.eval nodeValue4295 (mixedVector B) := by
    change mixedMoment B node4295 node4295Labels = _
    exact sound4295 B hB hF
  have h4296 : mixedVector B (Sum.inr 4296) = Sparse.eval nodeValue4296 (mixedVector B) := by
    change mixedMoment B node4296 node4296Labels = _
    exact sound4296 B hB hF
  have h4311 : mixedVector B (Sum.inr 4311) = Sparse.eval nodeValue4311 (mixedVector B) := by
    change mixedMoment B node4311 node4311Labels = _
    exact sound4311 B hB hF
  have h4404 : mixedVector B (Sum.inr 4404) = Sparse.eval nodeValue4404 (mixedVector B) := by
    change mixedMoment B node4404 node4404Labels = _
    exact sound4404 B hB hF
  have h4632 : mixedVector B (Sum.inr 4632) = Sparse.eval nodeValue4632 (mixedVector B) := by
    change mixedMoment B node4632 node4632Labels = _
    exact sound4632 B hB hF
  have h4637 : mixedVector B (Sum.inr 4637) = Sparse.eval nodeValue4637 (mixedVector B) := by
    change mixedMoment B node4637 node4637Labels = _
    exact sound4637 B hB hF
  have h4638 : mixedVector B (Sum.inr 4638) = Sparse.eval nodeValue4638 (mixedVector B) := by
    change mixedMoment B node4638 node4638Labels = _
    exact sound4638 B hB hF
  have h4652 : mixedVector B (Sum.inr 4652) = Sparse.eval nodeValue4652 (mixedVector B) := by
    change mixedMoment B node4652 node4652Labels = _
    exact sound4652 B hB hF
  have h4706 : mixedVector B (Sum.inr 4706) = Sparse.eval nodeValue4706 (mixedVector B) := by
    change mixedMoment B node4706 node4706Labels = _
    exact sound4706 B hB hF
  have h4707 : mixedVector B (Sum.inr 4707) = Sparse.eval nodeValue4707 (mixedVector B) := by
    change mixedMoment B node4707 node4707Labels = _
    exact sound4707 B hB hF
  have h4715 : mixedVector B (Sum.inr 4715) = Sparse.eval nodeValue4715 (mixedVector B) := by
    change mixedMoment B node4715 node4715Labels = _
    exact sound4715 B hB hF
  have h4722 : mixedVector B (Sum.inr 4722) = Sparse.eval nodeValue4722 (mixedVector B) := by
    change mixedMoment B node4722 node4722Labels = _
    exact sound4722 B hB hF
  have h4726 : mixedVector B (Sum.inr 4726) = Sparse.eval nodeValue4726 (mixedVector B) := by
    change mixedMoment B node4726 node4726Labels = _
    exact sound4726 B hB hF
  have h4727 : mixedVector B (Sum.inr 4727) = Sparse.eval nodeValue4727 (mixedVector B) := by
    change mixedMoment B node4727 node4727Labels = _
    exact sound4727 B hB hF
  have h4736 : mixedVector B (Sum.inr 4736) = Sparse.eval nodeValue4736 (mixedVector B) := by
    change mixedMoment B node4736 node4736Labels = _
    exact sound4736 B hB hF
  have h4737 : mixedVector B (Sum.inr 4737) = Sparse.eval nodeValue4737 (mixedVector B) := by
    change mixedMoment B node4737 node4737Labels = _
    exact sound4737 B hB hF
  have h4741 : mixedVector B (Sum.inr 4741) = Sparse.eval nodeValue4741 (mixedVector B) := by
    change mixedMoment B node4741 node4741Labels = _
    exact sound4741 B hB hF
  have h4742 : mixedVector B (Sum.inr 4742) = Sparse.eval nodeValue4742 (mixedVector B) := by
    change mixedMoment B node4742 node4742Labels = _
    exact sound4742 B hB hF
  have h4752 : mixedVector B (Sum.inr 4752) = Sparse.eval nodeValue4752 (mixedVector B) := by
    change mixedMoment B node4752 node4752Labels = _
    exact sound4752 B hB hF
  have h4782 : mixedVector B (Sum.inr 4782) = Sparse.eval nodeValue4782 (mixedVector B) := by
    change mixedMoment B node4782 node4782Labels = _
    exact sound4782 B hB hF
  have h4828 : mixedVector B (Sum.inr 4828) = Sparse.eval nodeValue4828 (mixedVector B) := by
    change mixedMoment B node4828 node4828Labels = _
    exact sound4828 B hB hF
  have h4834 : mixedVector B (Sum.inr 4834) = Sparse.eval nodeValue4834 (mixedVector B) := by
    change mixedMoment B node4834 node4834Labels = _
    exact sound4834 B hB hF
  have h4835 : mixedVector B (Sum.inr 4835) = Sparse.eval nodeValue4835 (mixedVector B) := by
    change mixedMoment B node4835 node4835Labels = _
    exact sound4835 B hB hF
  have h5015 : mixedVector B (Sum.inr 5015) = Sparse.eval nodeValue5015 (mixedVector B) := by
    change mixedMoment B node5015 node5015Labels = _
    exact sound5015 B hB hF
  have h5056 : mixedVector B (Sum.inr 5056) = Sparse.eval nodeValue5056 (mixedVector B) := by
    change mixedMoment B node5056 node5056Labels = _
    exact sound5056 B hB hF
  have h5095 : mixedVector B (Sum.inr 5095) = Sparse.eval nodeValue5095 (mixedVector B) := by
    change mixedMoment B node5095 node5095Labels = _
    exact sound5095 B hB hF
  have h5101 : mixedVector B (Sum.inr 5101) = Sparse.eval nodeValue5101 (mixedVector B) := by
    change mixedMoment B node5101 node5101Labels = _
    exact sound5101 B hB hF
  have h5102 : mixedVector B (Sum.inr 5102) = Sparse.eval nodeValue5102 (mixedVector B) := by
    change mixedMoment B node5102 node5102Labels = _
    exact sound5102 B hB hF
  simpa only [sourceForm2308, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4080, h4288, h4295, h4296, h4311, h4404, h4632, h4637, h4638, h4652, h4706, h4707, h4715, h4722, h4726, h4727, h4736, h4737, h4741, h4742, h4752, h4782, h4828, h4834, h4835, h5015, h5056, h5095, h5101, h5102, reducedSource1880] using sourceEq2308 B hB

theorem rowSound1880 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1880 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1880, numericCheck1880, reducedZero1880 B hB hF, mul_zero]

theorem reducedZero1881 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1881 (mixedVector B) = 0 := by
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  have h4298 : mixedVector B (Sum.inr 4298) = Sparse.eval nodeValue4298 (mixedVector B) := by
    change mixedMoment B node4298 node4298Labels = _
    exact sound4298 B hB hF
  have h4303 : mixedVector B (Sum.inr 4303) = Sparse.eval nodeValue4303 (mixedVector B) := by
    change mixedMoment B node4303 node4303Labels = _
    exact sound4303 B hB hF
  have h4305 : mixedVector B (Sum.inr 4305) = Sparse.eval nodeValue4305 (mixedVector B) := by
    change mixedMoment B node4305 node4305Labels = _
    exact sound4305 B hB hF
  have h4313 : mixedVector B (Sum.inr 4313) = Sparse.eval nodeValue4313 (mixedVector B) := by
    change mixedMoment B node4313 node4313Labels = _
    exact sound4313 B hB hF
  have h4419 : mixedVector B (Sum.inr 4419) = Sparse.eval nodeValue4419 (mixedVector B) := by
    change mixedMoment B node4419 node4419Labels = _
    exact sound4419 B hB hF
  have h4640 : mixedVector B (Sum.inr 4640) = Sparse.eval nodeValue4640 (mixedVector B) := by
    change mixedMoment B node4640 node4640Labels = _
    exact sound4640 B hB hF
  have h4644 : mixedVector B (Sum.inr 4644) = Sparse.eval nodeValue4644 (mixedVector B) := by
    change mixedMoment B node4644 node4644Labels = _
    exact sound4644 B hB hF
  have h4646 : mixedVector B (Sum.inr 4646) = Sparse.eval nodeValue4646 (mixedVector B) := by
    change mixedMoment B node4646 node4646Labels = _
    exact sound4646 B hB hF
  have h4653 : mixedVector B (Sum.inr 4653) = Sparse.eval nodeValue4653 (mixedVector B) := by
    change mixedMoment B node4653 node4653Labels = _
    exact sound4653 B hB hF
  have h4709 : mixedVector B (Sum.inr 4709) = Sparse.eval nodeValue4709 (mixedVector B) := by
    change mixedMoment B node4709 node4709Labels = _
    exact sound4709 B hB hF
  have h4711 : mixedVector B (Sum.inr 4711) = Sparse.eval nodeValue4711 (mixedVector B) := by
    change mixedMoment B node4711 node4711Labels = _
    exact sound4711 B hB hF
  have h4716 : mixedVector B (Sum.inr 4716) = Sparse.eval nodeValue4716 (mixedVector B) := by
    change mixedMoment B node4716 node4716Labels = _
    exact sound4716 B hB hF
  have h4731 : mixedVector B (Sum.inr 4731) = Sparse.eval nodeValue4731 (mixedVector B) := by
    change mixedMoment B node4731 node4731Labels = _
    exact sound4731 B hB hF
  have h4732 : mixedVector B (Sum.inr 4732) = Sparse.eval nodeValue4732 (mixedVector B) := by
    change mixedMoment B node4732 node4732Labels = _
    exact sound4732 B hB hF
  have h4744 : mixedVector B (Sum.inr 4744) = Sparse.eval nodeValue4744 (mixedVector B) := by
    change mixedMoment B node4744 node4744Labels = _
    exact sound4744 B hB hF
  have h4745 : mixedVector B (Sum.inr 4745) = Sparse.eval nodeValue4745 (mixedVector B) := by
    change mixedMoment B node4745 node4745Labels = _
    exact sound4745 B hB hF
  have h4749 : mixedVector B (Sum.inr 4749) = Sparse.eval nodeValue4749 (mixedVector B) := by
    change mixedMoment B node4749 node4749Labels = _
    exact sound4749 B hB hF
  have h4750 : mixedVector B (Sum.inr 4750) = Sparse.eval nodeValue4750 (mixedVector B) := by
    change mixedMoment B node4750 node4750Labels = _
    exact sound4750 B hB hF
  have h4753 : mixedVector B (Sum.inr 4753) = Sparse.eval nodeValue4753 (mixedVector B) := by
    change mixedMoment B node4753 node4753Labels = _
    exact sound4753 B hB hF
  have h4782 : mixedVector B (Sum.inr 4782) = Sparse.eval nodeValue4782 (mixedVector B) := by
    change mixedMoment B node4782 node4782Labels = _
    exact sound4782 B hB hF
  have h4810 : mixedVector B (Sum.inr 4810) = Sparse.eval nodeValue4810 (mixedVector B) := by
    change mixedMoment B node4810 node4810Labels = _
    exact sound4810 B hB hF
  have h4811 : mixedVector B (Sum.inr 4811) = Sparse.eval nodeValue4811 (mixedVector B) := by
    change mixedMoment B node4811 node4811Labels = _
    exact sound4811 B hB hF
  have h4846 : mixedVector B (Sum.inr 4846) = Sparse.eval nodeValue4846 (mixedVector B) := by
    change mixedMoment B node4846 node4846Labels = _
    exact sound4846 B hB hF
  have h5003 : mixedVector B (Sum.inr 5003) = Sparse.eval nodeValue5003 (mixedVector B) := by
    change mixedMoment B node5003 node5003Labels = _
    exact sound5003 B hB hF
  have h5050 : mixedVector B (Sum.inr 5050) = Sparse.eval nodeValue5050 (mixedVector B) := by
    change mixedMoment B node5050 node5050Labels = _
    exact sound5050 B hB hF
  have h5080 : mixedVector B (Sum.inr 5080) = Sparse.eval nodeValue5080 (mixedVector B) := by
    change mixedMoment B node5080 node5080Labels = _
    exact sound5080 B hB hF
  have h5081 : mixedVector B (Sum.inr 5081) = Sparse.eval nodeValue5081 (mixedVector B) := by
    change mixedMoment B node5081 node5081Labels = _
    exact sound5081 B hB hF
  have h5111 : mixedVector B (Sum.inr 5111) = Sparse.eval nodeValue5111 (mixedVector B) := by
    change mixedMoment B node5111 node5111Labels = _
    exact sound5111 B hB hF
  simpa only [sourceForm2310, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4082, h4298, h4303, h4305, h4313, h4419, h4640, h4644, h4646, h4653, h4709, h4711, h4716, h4731, h4732, h4744, h4745, h4749, h4750, h4753, h4782, h4810, h4811, h4846, h5003, h5050, h5080, h5081, h5111, reducedSource1881] using sourceEq2310 B hB

theorem rowSound1881 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1881 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1881, numericCheck1881, reducedZero1881 B hB hF, mul_zero]

theorem reducedZero1882 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1882 (mixedVector B) = 0 := by
  have h4065 : mixedVector B (Sum.inr 4065) = Sparse.eval nodeValue4065 (mixedVector B) := by
    change mixedMoment B node4065 node4065Labels = _
    exact sound4065 B hB hF
  have h4067 : mixedVector B (Sum.inr 4067) = Sparse.eval nodeValue4067 (mixedVector B) := by
    change mixedMoment B node4067 node4067Labels = _
    exact sound4067 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  have h4074 : mixedVector B (Sum.inr 4074) = Sparse.eval nodeValue4074 (mixedVector B) := by
    change mixedMoment B node4074 node4074Labels = _
    exact sound4074 B hB hF
  have h4075 : mixedVector B (Sum.inr 4075) = Sparse.eval nodeValue4075 (mixedVector B) := by
    change mixedMoment B node4075 node4075Labels = _
    exact sound4075 B hB hF
  have h4076 : mixedVector B (Sum.inr 4076) = Sparse.eval nodeValue4076 (mixedVector B) := by
    change mixedMoment B node4076 node4076Labels = _
    exact sound4076 B hB hF
  have h4078 : mixedVector B (Sum.inr 4078) = Sparse.eval nodeValue4078 (mixedVector B) := by
    change mixedMoment B node4078 node4078Labels = _
    exact sound4078 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  have h4089 : mixedVector B (Sum.inr 4089) = Sparse.eval nodeValue4089 (mixedVector B) := by
    change mixedMoment B node4089 node4089Labels = _
    exact sound4089 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2311, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4065, h4067, h4071, h4074, h4075, h4076, h4078, h4080, h4081, h4082, h4084, h4088, h4089, h4092, reducedSource1882] using sourceEq2311 B hB

theorem rowSound1882 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1882 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1882, numericCheck1882, reducedZero1882 B hB hF, mul_zero]

theorem reducedZero1883 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1883 (mixedVector B) = 0 := by
  have h923 : mixedVector B (Sum.inr 923) = Sparse.eval nodeValue923 (mixedVector B) := by
    change mixedMoment B node923 node923Labels = _
    exact sound923 B hB hF
  have h1806 : mixedVector B (Sum.inr 1806) = Sparse.eval nodeValue1806 (mixedVector B) := by
    change mixedMoment B node1806 node1806Labels = _
    exact sound1806 B hB hF
  have h2021 : mixedVector B (Sum.inr 2021) = Sparse.eval nodeValue2021 (mixedVector B) := by
    change mixedMoment B node2021 node2021Labels = _
    exact sound2021 B hB hF
  have h2034 : mixedVector B (Sum.inr 2034) = Sparse.eval nodeValue2034 (mixedVector B) := by
    change mixedMoment B node2034 node2034Labels = _
    exact sound2034 B hB hF
  have h2051 : mixedVector B (Sum.inr 2051) = Sparse.eval nodeValue2051 (mixedVector B) := by
    change mixedMoment B node2051 node2051Labels = _
    exact sound2051 B hB hF
  have h2058 : mixedVector B (Sum.inr 2058) = Sparse.eval nodeValue2058 (mixedVector B) := by
    change mixedMoment B node2058 node2058Labels = _
    exact sound2058 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2312, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h923, h1806, h2021, h2034, h2051, h2058, h4084, reducedSource1883] using sourceEq2312 B hB

theorem rowSound1883 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1883 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1883, numericCheck1883, reducedZero1883 B hB hF, mul_zero]

theorem reducedZero1884 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1884 (mixedVector B) = 0 := by
  have h2440 : mixedVector B (Sum.inr 2440) = Sparse.eval nodeValue2440 (mixedVector B) := by
    change mixedMoment B node2440 node2440Labels = _
    exact sound2440 B hB hF
  have h3062 : mixedVector B (Sum.inr 3062) = Sparse.eval nodeValue3062 (mixedVector B) := by
    change mixedMoment B node3062 node3062Labels = _
    exact sound3062 B hB hF
  have h3189 : mixedVector B (Sum.inr 3189) = Sparse.eval nodeValue3189 (mixedVector B) := by
    change mixedMoment B node3189 node3189Labels = _
    exact sound3189 B hB hF
  have h3202 : mixedVector B (Sum.inr 3202) = Sparse.eval nodeValue3202 (mixedVector B) := by
    change mixedMoment B node3202 node3202Labels = _
    exact sound3202 B hB hF
  have h3789 : mixedVector B (Sum.inr 3789) = Sparse.eval nodeValue3789 (mixedVector B) := by
    change mixedMoment B node3789 node3789Labels = _
    exact sound3789 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2313, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2440, h3062, h3189, h3202, h3789, h4091, reducedSource1884] using sourceEq2313 B hB

theorem rowSound1884 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1884 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1884, numericCheck1884, reducedZero1884 B hB hF, mul_zero]

theorem reducedZero1885 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1885 (mixedVector B) = 0 := by
  have h920 : mixedVector B (Sum.inr 920) = Sparse.eval nodeValue920 (mixedVector B) := by
    change mixedMoment B node920 node920Labels = _
    exact sound920 B hB hF
  have h1803 : mixedVector B (Sum.inr 1803) = Sparse.eval nodeValue1803 (mixedVector B) := by
    change mixedMoment B node1803 node1803Labels = _
    exact sound1803 B hB hF
  have h2033 : mixedVector B (Sum.inr 2033) = Sparse.eval nodeValue2033 (mixedVector B) := by
    change mixedMoment B node2033 node2033Labels = _
    exact sound2033 B hB hF
  have h2051 : mixedVector B (Sum.inr 2051) = Sparse.eval nodeValue2051 (mixedVector B) := by
    change mixedMoment B node2051 node2051Labels = _
    exact sound2051 B hB hF
  have h2054 : mixedVector B (Sum.inr 2054) = Sparse.eval nodeValue2054 (mixedVector B) := by
    change mixedMoment B node2054 node2054Labels = _
    exact sound2054 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2315, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h920, h1803, h2033, h2051, h2054, h4084, reducedSource1885] using sourceEq2315 B hB

theorem rowSound1885 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1885 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1885, numericCheck1885, reducedZero1885 B hB hF, mul_zero]

theorem reducedZero1886 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1886 (mixedVector B) = 0 := by
  have h2895 : mixedVector B (Sum.inr 2895) = Sparse.eval nodeValue2895 (mixedVector B) := by
    change mixedMoment B node2895 node2895Labels = _
    exact sound2895 B hB hF
  have h3164 : mixedVector B (Sum.inr 3164) = Sparse.eval nodeValue3164 (mixedVector B) := by
    change mixedMoment B node3164 node3164Labels = _
    exact sound3164 B hB hF
  have h3172 : mixedVector B (Sum.inr 3172) = Sparse.eval nodeValue3172 (mixedVector B) := by
    change mixedMoment B node3172 node3172Labels = _
    exact sound3172 B hB hF
  have h3197 : mixedVector B (Sum.inr 3197) = Sparse.eval nodeValue3197 (mixedVector B) := by
    change mixedMoment B node3197 node3197Labels = _
    exact sound3197 B hB hF
  have h3964 : mixedVector B (Sum.inr 3964) = Sparse.eval nodeValue3964 (mixedVector B) := by
    change mixedMoment B node3964 node3964Labels = _
    exact sound3964 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2316, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2895, h3164, h3172, h3197, h3964, h4091, reducedSource1886] using sourceEq2316 B hB

theorem rowSound1886 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1886 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1886, numericCheck1886, reducedZero1886 B hB hF, mul_zero]

theorem reducedZero1887 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1887 (mixedVector B) = 0 := by
  have h2430 : mixedVector B (Sum.inr 2430) = Sparse.eval nodeValue2430 (mixedVector B) := by
    change mixedMoment B node2430 node2430Labels = _
    exact sound2430 B hB hF
  have h3162 : mixedVector B (Sum.inr 3162) = Sparse.eval nodeValue3162 (mixedVector B) := by
    change mixedMoment B node3162 node3162Labels = _
    exact sound3162 B hB hF
  have h3163 : mixedVector B (Sum.inr 3163) = Sparse.eval nodeValue3163 (mixedVector B) := by
    change mixedMoment B node3163 node3163Labels = _
    exact sound3163 B hB hF
  have h3170 : mixedVector B (Sum.inr 3170) = Sparse.eval nodeValue3170 (mixedVector B) := by
    change mixedMoment B node3170 node3170Labels = _
    exact sound3170 B hB hF
  have h3196 : mixedVector B (Sum.inr 3196) = Sparse.eval nodeValue3196 (mixedVector B) := by
    change mixedMoment B node3196 node3196Labels = _
    exact sound3196 B hB hF
  have h3782 : mixedVector B (Sum.inr 3782) = Sparse.eval nodeValue3782 (mixedVector B) := by
    change mixedMoment B node3782 node3782Labels = _
    exact sound3782 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2318, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2430, h3162, h3163, h3170, h3196, h3782, h4092, reducedSource1887] using sourceEq2318 B hB

theorem rowSound1887 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1887 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1887, numericCheck1887, reducedZero1887 B hB hF, mul_zero]

theorem sourceRowsAt1872 : MixedData.sourceRows (1872 : Fin 2425) =
    MixedData.row1872 := by decide +kernel

theorem sourceRowsAt1873 : MixedData.sourceRows (1873 : Fin 2425) =
    MixedData.row1873 := by decide +kernel

theorem sourceRowsAt1874 : MixedData.sourceRows (1874 : Fin 2425) =
    MixedData.row1874 := by decide +kernel

theorem sourceRowsAt1875 : MixedData.sourceRows (1875 : Fin 2425) =
    MixedData.row1875 := by decide +kernel

theorem sourceRowsAt1876 : MixedData.sourceRows (1876 : Fin 2425) =
    MixedData.row1876 := by decide +kernel

theorem sourceRowsAt1877 : MixedData.sourceRows (1877 : Fin 2425) =
    MixedData.row1877 := by decide +kernel

theorem sourceRowsAt1878 : MixedData.sourceRows (1878 : Fin 2425) =
    MixedData.row1878 := by decide +kernel

theorem sourceRowsAt1879 : MixedData.sourceRows (1879 : Fin 2425) =
    MixedData.row1879 := by decide +kernel

theorem sourceRowsAt1880 : MixedData.sourceRows (1880 : Fin 2425) =
    MixedData.row1880 := by decide +kernel

theorem sourceRowsAt1881 : MixedData.sourceRows (1881 : Fin 2425) =
    MixedData.row1881 := by decide +kernel

theorem sourceRowsAt1882 : MixedData.sourceRows (1882 : Fin 2425) =
    MixedData.row1882 := by decide +kernel

theorem sourceRowsAt1883 : MixedData.sourceRows (1883 : Fin 2425) =
    MixedData.row1883 := by decide +kernel

theorem sourceRowsAt1884 : MixedData.sourceRows (1884 : Fin 2425) =
    MixedData.row1884 := by decide +kernel

theorem sourceRowsAt1885 : MixedData.sourceRows (1885 : Fin 2425) =
    MixedData.row1885 := by decide +kernel

theorem sourceRowsAt1886 : MixedData.sourceRows (1886 : Fin 2425) =
    MixedData.row1886 := by decide +kernel

theorem sourceRowsAt1887 : MixedData.sourceRows (1887 : Fin 2425) =
    MixedData.row1887 := by decide +kernel

theorem chunkSound117 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 117) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1872 ∨ k.val = 1873 ∨ k.val = 1874 ∨ k.val = 1875 ∨ k.val = 1876 ∨ k.val = 1877 ∨ k.val = 1878 ∨ k.val = 1879 ∨ k.val = 1880 ∨ k.val = 1881 ∨ k.val = 1882 ∨ k.val = 1883 ∨ k.val = 1884 ∨ k.val = 1885 ∨ k.val = 1886 ∨ k.val = 1887 := by omega
  rcases heq with h1872 | h1873 | h1874 | h1875 | h1876 | h1877 | h1878 | h1879 | h1880 | h1881 | h1882 | h1883 | h1884 | h1885 | h1886 | h1887
  · have he : k = (1872 : Fin 2425) := Fin.ext h1872
    subst k
    rw [sourceRowsAt1872]
    exact rowSound1872 B hB hF
  · have he : k = (1873 : Fin 2425) := Fin.ext h1873
    subst k
    rw [sourceRowsAt1873]
    exact rowSound1873 B hB hF
  · have he : k = (1874 : Fin 2425) := Fin.ext h1874
    subst k
    rw [sourceRowsAt1874]
    exact rowSound1874 B hB hF
  · have he : k = (1875 : Fin 2425) := Fin.ext h1875
    subst k
    rw [sourceRowsAt1875]
    exact rowSound1875 B hB hF
  · have he : k = (1876 : Fin 2425) := Fin.ext h1876
    subst k
    rw [sourceRowsAt1876]
    exact rowSound1876 B hB hF
  · have he : k = (1877 : Fin 2425) := Fin.ext h1877
    subst k
    rw [sourceRowsAt1877]
    exact rowSound1877 B hB hF
  · have he : k = (1878 : Fin 2425) := Fin.ext h1878
    subst k
    rw [sourceRowsAt1878]
    exact rowSound1878 B hB hF
  · have he : k = (1879 : Fin 2425) := Fin.ext h1879
    subst k
    rw [sourceRowsAt1879]
    exact rowSound1879 B hB hF
  · have he : k = (1880 : Fin 2425) := Fin.ext h1880
    subst k
    rw [sourceRowsAt1880]
    exact rowSound1880 B hB hF
  · have he : k = (1881 : Fin 2425) := Fin.ext h1881
    subst k
    rw [sourceRowsAt1881]
    exact rowSound1881 B hB hF
  · have he : k = (1882 : Fin 2425) := Fin.ext h1882
    subst k
    rw [sourceRowsAt1882]
    exact rowSound1882 B hB hF
  · have he : k = (1883 : Fin 2425) := Fin.ext h1883
    subst k
    rw [sourceRowsAt1883]
    exact rowSound1883 B hB hF
  · have he : k = (1884 : Fin 2425) := Fin.ext h1884
    subst k
    rw [sourceRowsAt1884]
    exact rowSound1884 B hB hF
  · have he : k = (1885 : Fin 2425) := Fin.ext h1885
    subst k
    rw [sourceRowsAt1885]
    exact rowSound1885 B hB hF
  · have he : k = (1886 : Fin 2425) := Fin.ext h1886
    subst k
    rw [sourceRowsAt1886]
    exact rowSound1886 B hB hF
  · have he : k = (1887 : Fin 2425) := Fin.ext h1887
    subst k
    rw [sourceRowsAt1887]
    exact rowSound1887 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
