import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic123
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources77

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1968 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1968 (mixedVector B) = 0 := by
  have h4232 : mixedVector B (Sum.inr 4232) = Sparse.eval nodeValue4232 (mixedVector B) := by
    change mixedMoment B node4232 node4232Labels = _
    exact sound4232 B hB hF
  have h4233 : mixedVector B (Sum.inr 4233) = Sparse.eval nodeValue4233 (mixedVector B) := by
    change mixedMoment B node4233 node4233Labels = _
    exact sound4233 B hB hF
  have h4234 : mixedVector B (Sum.inr 4234) = Sparse.eval nodeValue4234 (mixedVector B) := by
    change mixedMoment B node4234 node4234Labels = _
    exact sound4234 B hB hF
  have h4239 : mixedVector B (Sum.inr 4239) = Sparse.eval nodeValue4239 (mixedVector B) := by
    change mixedMoment B node4239 node4239Labels = _
    exact sound4239 B hB hF
  have h4268 : mixedVector B (Sum.inr 4268) = Sparse.eval nodeValue4268 (mixedVector B) := by
    change mixedMoment B node4268 node4268Labels = _
    exact sound4268 B hB hF
  have h4679 : mixedVector B (Sum.inr 4679) = Sparse.eval nodeValue4679 (mixedVector B) := by
    change mixedMoment B node4679 node4679Labels = _
    exact sound4679 B hB hF
  have h4681 : mixedVector B (Sum.inr 4681) = Sparse.eval nodeValue4681 (mixedVector B) := by
    change mixedMoment B node4681 node4681Labels = _
    exact sound4681 B hB hF
  have h4684 : mixedVector B (Sum.inr 4684) = Sparse.eval nodeValue4684 (mixedVector B) := by
    change mixedMoment B node4684 node4684Labels = _
    exact sound4684 B hB hF
  have h4689 : mixedVector B (Sum.inr 4689) = Sparse.eval nodeValue4689 (mixedVector B) := by
    change mixedMoment B node4689 node4689Labels = _
    exact sound4689 B hB hF
  have h4721 : mixedVector B (Sum.inr 4721) = Sparse.eval nodeValue4721 (mixedVector B) := by
    change mixedMoment B node4721 node4721Labels = _
    exact sound4721 B hB hF
  have h4722 : mixedVector B (Sum.inr 4722) = Sparse.eval nodeValue4722 (mixedVector B) := by
    change mixedMoment B node4722 node4722Labels = _
    exact sound4722 B hB hF
  have h4725 : mixedVector B (Sum.inr 4725) = Sparse.eval nodeValue4725 (mixedVector B) := by
    change mixedMoment B node4725 node4725Labels = _
    exact sound4725 B hB hF
  have h4740 : mixedVector B (Sum.inr 4740) = Sparse.eval nodeValue4740 (mixedVector B) := by
    change mixedMoment B node4740 node4740Labels = _
    exact sound4740 B hB hF
  have h4826 : mixedVector B (Sum.inr 4826) = Sparse.eval nodeValue4826 (mixedVector B) := by
    change mixedMoment B node4826 node4826Labels = _
    exact sound4826 B hB hF
  have h4827 : mixedVector B (Sum.inr 4827) = Sparse.eval nodeValue4827 (mixedVector B) := by
    change mixedMoment B node4827 node4827Labels = _
    exact sound4827 B hB hF
  have h4828 : mixedVector B (Sum.inr 4828) = Sparse.eval nodeValue4828 (mixedVector B) := by
    change mixedMoment B node4828 node4828Labels = _
    exact sound4828 B hB hF
  have h4839 : mixedVector B (Sum.inr 4839) = Sparse.eval nodeValue4839 (mixedVector B) := by
    change mixedMoment B node4839 node4839Labels = _
    exact sound4839 B hB hF
  have h4864 : mixedVector B (Sum.inr 4864) = Sparse.eval nodeValue4864 (mixedVector B) := by
    change mixedMoment B node4864 node4864Labels = _
    exact sound4864 B hB hF
  have h4865 : mixedVector B (Sum.inr 4865) = Sparse.eval nodeValue4865 (mixedVector B) := by
    change mixedMoment B node4865 node4865Labels = _
    exact sound4865 B hB hF
  have h4866 : mixedVector B (Sum.inr 4866) = Sparse.eval nodeValue4866 (mixedVector B) := by
    change mixedMoment B node4866 node4866Labels = _
    exact sound4866 B hB hF
  have h4868 : mixedVector B (Sum.inr 4868) = Sparse.eval nodeValue4868 (mixedVector B) := by
    change mixedMoment B node4868 node4868Labels = _
    exact sound4868 B hB hF
  have h4875 : mixedVector B (Sum.inr 4875) = Sparse.eval nodeValue4875 (mixedVector B) := by
    change mixedMoment B node4875 node4875Labels = _
    exact sound4875 B hB hF
  have h4889 : mixedVector B (Sum.inr 4889) = Sparse.eval nodeValue4889 (mixedVector B) := by
    change mixedMoment B node4889 node4889Labels = _
    exact sound4889 B hB hF
  have h4896 : mixedVector B (Sum.inr 4896) = Sparse.eval nodeValue4896 (mixedVector B) := by
    change mixedMoment B node4896 node4896Labels = _
    exact sound4896 B hB hF
  have h5388 : mixedVector B (Sum.inr 5388) = Sparse.eval nodeValue5388 (mixedVector B) := by
    change mixedMoment B node5388 node5388Labels = _
    exact sound5388 B hB hF
  have h5401 : mixedVector B (Sum.inr 5401) = Sparse.eval nodeValue5401 (mixedVector B) := by
    change mixedMoment B node5401 node5401Labels = _
    exact sound5401 B hB hF
  have h5438 : mixedVector B (Sum.inr 5438) = Sparse.eval nodeValue5438 (mixedVector B) := by
    change mixedMoment B node5438 node5438Labels = _
    exact sound5438 B hB hF
  have h5450 : mixedVector B (Sum.inr 5450) = Sparse.eval nodeValue5450 (mixedVector B) := by
    change mixedMoment B node5450 node5450Labels = _
    exact sound5450 B hB hF
  have h5451 : mixedVector B (Sum.inr 5451) = Sparse.eval nodeValue5451 (mixedVector B) := by
    change mixedMoment B node5451 node5451Labels = _
    exact sound5451 B hB hF
  simpa only [sourceForm2448, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4232, h4233, h4234, h4239, h4268, h4679, h4681, h4684, h4689, h4721, h4722, h4725, h4740, h4826, h4827, h4828, h4839, h4864, h4865, h4866, h4868, h4875, h4889, h4896, h5388, h5401, h5438, h5450, h5451, reducedSource1968] using sourceEq2448 B hB

theorem rowSound1968 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1968 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1968, numericCheck1968, reducedZero1968 B hB hF, mul_zero]

theorem reducedZero1969 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1969 (mixedVector B) = 0 := by
  have h732 : mixedVector B (Sum.inr 732) = Sparse.eval nodeValue732 (mixedVector B) := by
    change mixedMoment B node732 node732Labels = _
    exact sound732 B hB hF
  have h733 : mixedVector B (Sum.inr 733) = Sparse.eval nodeValue733 (mixedVector B) := by
    change mixedMoment B node733 node733Labels = _
    exact sound733 B hB hF
  have h734 : mixedVector B (Sum.inr 734) = Sparse.eval nodeValue734 (mixedVector B) := by
    change mixedMoment B node734 node734Labels = _
    exact sound734 B hB hF
  have h739 : mixedVector B (Sum.inr 739) = Sparse.eval nodeValue739 (mixedVector B) := by
    change mixedMoment B node739 node739Labels = _
    exact sound739 B hB hF
  have h824 : mixedVector B (Sum.inr 824) = Sparse.eval nodeValue824 (mixedVector B) := by
    change mixedMoment B node824 node824Labels = _
    exact sound824 B hB hF
  have h1805 : mixedVector B (Sum.inr 1805) = Sparse.eval nodeValue1805 (mixedVector B) := by
    change mixedMoment B node1805 node1805Labels = _
    exact sound1805 B hB hF
  have h1807 : mixedVector B (Sum.inr 1807) = Sparse.eval nodeValue1807 (mixedVector B) := by
    change mixedMoment B node1807 node1807Labels = _
    exact sound1807 B hB hF
  have h1810 : mixedVector B (Sum.inr 1810) = Sparse.eval nodeValue1810 (mixedVector B) := by
    change mixedMoment B node1810 node1810Labels = _
    exact sound1810 B hB hF
  have h1815 : mixedVector B (Sum.inr 1815) = Sparse.eval nodeValue1815 (mixedVector B) := by
    change mixedMoment B node1815 node1815Labels = _
    exact sound1815 B hB hF
  have h1875 : mixedVector B (Sum.inr 1875) = Sparse.eval nodeValue1875 (mixedVector B) := by
    change mixedMoment B node1875 node1875Labels = _
    exact sound1875 B hB hF
  have h1876 : mixedVector B (Sum.inr 1876) = Sparse.eval nodeValue1876 (mixedVector B) := by
    change mixedMoment B node1876 node1876Labels = _
    exact sound1876 B hB hF
  have h1879 : mixedVector B (Sum.inr 1879) = Sparse.eval nodeValue1879 (mixedVector B) := by
    change mixedMoment B node1879 node1879Labels = _
    exact sound1879 B hB hF
  have h1922 : mixedVector B (Sum.inr 1922) = Sparse.eval nodeValue1922 (mixedVector B) := by
    change mixedMoment B node1922 node1922Labels = _
    exact sound1922 B hB hF
  have h2077 : mixedVector B (Sum.inr 2077) = Sparse.eval nodeValue2077 (mixedVector B) := by
    change mixedMoment B node2077 node2077Labels = _
    exact sound2077 B hB hF
  have h2079 : mixedVector B (Sum.inr 2079) = Sparse.eval nodeValue2079 (mixedVector B) := by
    change mixedMoment B node2079 node2079Labels = _
    exact sound2079 B hB hF
  have h2082 : mixedVector B (Sum.inr 2082) = Sparse.eval nodeValue2082 (mixedVector B) := by
    change mixedMoment B node2082 node2082Labels = _
    exact sound2082 B hB hF
  have h2105 : mixedVector B (Sum.inr 2105) = Sparse.eval nodeValue2105 (mixedVector B) := by
    change mixedMoment B node2105 node2105Labels = _
    exact sound2105 B hB hF
  have h2106 : mixedVector B (Sum.inr 2106) = Sparse.eval nodeValue2106 (mixedVector B) := by
    change mixedMoment B node2106 node2106Labels = _
    exact sound2106 B hB hF
  have h2107 : mixedVector B (Sum.inr 2107) = Sparse.eval nodeValue2107 (mixedVector B) := by
    change mixedMoment B node2107 node2107Labels = _
    exact sound2107 B hB hF
  have h2109 : mixedVector B (Sum.inr 2109) = Sparse.eval nodeValue2109 (mixedVector B) := by
    change mixedMoment B node2109 node2109Labels = _
    exact sound2109 B hB hF
  have h2116 : mixedVector B (Sum.inr 2116) = Sparse.eval nodeValue2116 (mixedVector B) := by
    change mixedMoment B node2116 node2116Labels = _
    exact sound2116 B hB hF
  have h2216 : mixedVector B (Sum.inr 2216) = Sparse.eval nodeValue2216 (mixedVector B) := by
    change mixedMoment B node2216 node2216Labels = _
    exact sound2216 B hB hF
  have h2277 : mixedVector B (Sum.inr 2277) = Sparse.eval nodeValue2277 (mixedVector B) := by
    change mixedMoment B node2277 node2277Labels = _
    exact sound2277 B hB hF
  have h2278 : mixedVector B (Sum.inr 2278) = Sparse.eval nodeValue2278 (mixedVector B) := by
    change mixedMoment B node2278 node2278Labels = _
    exact sound2278 B hB hF
  have h3737 : mixedVector B (Sum.inr 3737) = Sparse.eval nodeValue3737 (mixedVector B) := by
    change mixedMoment B node3737 node3737Labels = _
    exact sound3737 B hB hF
  have h3787 : mixedVector B (Sum.inr 3787) = Sparse.eval nodeValue3787 (mixedVector B) := by
    change mixedMoment B node3787 node3787Labels = _
    exact sound3787 B hB hF
  have h3876 : mixedVector B (Sum.inr 3876) = Sparse.eval nodeValue3876 (mixedVector B) := by
    change mixedMoment B node3876 node3876Labels = _
    exact sound3876 B hB hF
  have h3887 : mixedVector B (Sum.inr 3887) = Sparse.eval nodeValue3887 (mixedVector B) := by
    change mixedMoment B node3887 node3887Labels = _
    exact sound3887 B hB hF
  have h3888 : mixedVector B (Sum.inr 3888) = Sparse.eval nodeValue3888 (mixedVector B) := by
    change mixedMoment B node3888 node3888Labels = _
    exact sound3888 B hB hF
  simpa only [sourceForm2449, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h732, h733, h734, h739, h824, h1805, h1807, h1810, h1815, h1875, h1876, h1879, h1922, h2077, h2079, h2082, h2105, h2106, h2107, h2109, h2116, h2216, h2277, h2278, h3737, h3787, h3876, h3887, h3888, reducedSource1969] using sourceEq2449 B hB

theorem rowSound1969 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1969 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1969, numericCheck1969, reducedZero1969 B hB hF, mul_zero]

theorem reducedZero1970 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1970 (mixedVector B) = 0 := by
  have h4449 : mixedVector B (Sum.inr 4449) = Sparse.eval nodeValue4449 (mixedVector B) := by
    change mixedMoment B node4449 node4449Labels = _
    exact sound4449 B hB hF
  have h4452 : mixedVector B (Sum.inr 4452) = Sparse.eval nodeValue4452 (mixedVector B) := by
    change mixedMoment B node4452 node4452Labels = _
    exact sound4452 B hB hF
  have h4453 : mixedVector B (Sum.inr 4453) = Sparse.eval nodeValue4453 (mixedVector B) := by
    change mixedMoment B node4453 node4453Labels = _
    exact sound4453 B hB hF
  have h4462 : mixedVector B (Sum.inr 4462) = Sparse.eval nodeValue4462 (mixedVector B) := by
    change mixedMoment B node4462 node4462Labels = _
    exact sound4462 B hB hF
  have h4489 : mixedVector B (Sum.inr 4489) = Sparse.eval nodeValue4489 (mixedVector B) := by
    change mixedMoment B node4489 node4489Labels = _
    exact sound4489 B hB hF
  have h4798 : mixedVector B (Sum.inr 4798) = Sparse.eval nodeValue4798 (mixedVector B) := by
    change mixedMoment B node4798 node4798Labels = _
    exact sound4798 B hB hF
  have h4799 : mixedVector B (Sum.inr 4799) = Sparse.eval nodeValue4799 (mixedVector B) := by
    change mixedMoment B node4799 node4799Labels = _
    exact sound4799 B hB hF
  have h4802 : mixedVector B (Sum.inr 4802) = Sparse.eval nodeValue4802 (mixedVector B) := by
    change mixedMoment B node4802 node4802Labels = _
    exact sound4802 B hB hF
  have h4806 : mixedVector B (Sum.inr 4806) = Sparse.eval nodeValue4806 (mixedVector B) := by
    change mixedMoment B node4806 node4806Labels = _
    exact sound4806 B hB hF
  have h4826 : mixedVector B (Sum.inr 4826) = Sparse.eval nodeValue4826 (mixedVector B) := by
    change mixedMoment B node4826 node4826Labels = _
    exact sound4826 B hB hF
  have h4834 : mixedVector B (Sum.inr 4834) = Sparse.eval nodeValue4834 (mixedVector B) := by
    change mixedMoment B node4834 node4834Labels = _
    exact sound4834 B hB hF
  have h4835 : mixedVector B (Sum.inr 4835) = Sparse.eval nodeValue4835 (mixedVector B) := by
    change mixedMoment B node4835 node4835Labels = _
    exact sound4835 B hB hF
  have h4838 : mixedVector B (Sum.inr 4838) = Sparse.eval nodeValue4838 (mixedVector B) := by
    change mixedMoment B node4838 node4838Labels = _
    exact sound4838 B hB hF
  have h4849 : mixedVector B (Sum.inr 4849) = Sparse.eval nodeValue4849 (mixedVector B) := by
    change mixedMoment B node4849 node4849Labels = _
    exact sound4849 B hB hF
  have h4851 : mixedVector B (Sum.inr 4851) = Sparse.eval nodeValue4851 (mixedVector B) := by
    change mixedMoment B node4851 node4851Labels = _
    exact sound4851 B hB hF
  have h4852 : mixedVector B (Sum.inr 4852) = Sparse.eval nodeValue4852 (mixedVector B) := by
    change mixedMoment B node4852 node4852Labels = _
    exact sound4852 B hB hF
  have h4860 : mixedVector B (Sum.inr 4860) = Sparse.eval nodeValue4860 (mixedVector B) := by
    change mixedMoment B node4860 node4860Labels = _
    exact sound4860 B hB hF
  have h4861 : mixedVector B (Sum.inr 4861) = Sparse.eval nodeValue4861 (mixedVector B) := by
    change mixedMoment B node4861 node4861Labels = _
    exact sound4861 B hB hF
  have h4865 : mixedVector B (Sum.inr 4865) = Sparse.eval nodeValue4865 (mixedVector B) := by
    change mixedMoment B node4865 node4865Labels = _
    exact sound4865 B hB hF
  have h4866 : mixedVector B (Sum.inr 4866) = Sparse.eval nodeValue4866 (mixedVector B) := by
    change mixedMoment B node4866 node4866Labels = _
    exact sound4866 B hB hF
  have h4867 : mixedVector B (Sum.inr 4867) = Sparse.eval nodeValue4867 (mixedVector B) := by
    change mixedMoment B node4867 node4867Labels = _
    exact sound4867 B hB hF
  have h4869 : mixedVector B (Sum.inr 4869) = Sparse.eval nodeValue4869 (mixedVector B) := by
    change mixedMoment B node4869 node4869Labels = _
    exact sound4869 B hB hF
  have h4870 : mixedVector B (Sum.inr 4870) = Sparse.eval nodeValue4870 (mixedVector B) := by
    change mixedMoment B node4870 node4870Labels = _
    exact sound4870 B hB hF
  have h4879 : mixedVector B (Sum.inr 4879) = Sparse.eval nodeValue4879 (mixedVector B) := by
    change mixedMoment B node4879 node4879Labels = _
    exact sound4879 B hB hF
  have h4880 : mixedVector B (Sum.inr 4880) = Sparse.eval nodeValue4880 (mixedVector B) := by
    change mixedMoment B node4880 node4880Labels = _
    exact sound4880 B hB hF
  have h5169 : mixedVector B (Sum.inr 5169) = Sparse.eval nodeValue5169 (mixedVector B) := by
    change mixedMoment B node5169 node5169Labels = _
    exact sound5169 B hB hF
  have h5185 : mixedVector B (Sum.inr 5185) = Sparse.eval nodeValue5185 (mixedVector B) := by
    change mixedMoment B node5185 node5185Labels = _
    exact sound5185 B hB hF
  have h5199 : mixedVector B (Sum.inr 5199) = Sparse.eval nodeValue5199 (mixedVector B) := by
    change mixedMoment B node5199 node5199Labels = _
    exact sound5199 B hB hF
  have h5203 : mixedVector B (Sum.inr 5203) = Sparse.eval nodeValue5203 (mixedVector B) := by
    change mixedMoment B node5203 node5203Labels = _
    exact sound5203 B hB hF
  have h5204 : mixedVector B (Sum.inr 5204) = Sparse.eval nodeValue5204 (mixedVector B) := by
    change mixedMoment B node5204 node5204Labels = _
    exact sound5204 B hB hF
  simpa only [sourceForm2450, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4449, h4452, h4453, h4462, h4489, h4798, h4799, h4802, h4806, h4826, h4834, h4835, h4838, h4849, h4851, h4852, h4860, h4861, h4865, h4866, h4867, h4869, h4870, h4879, h4880, h5169, h5185, h5199, h5203, h5204, reducedSource1970] using sourceEq2450 B hB

theorem rowSound1970 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1970 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1970, numericCheck1970, reducedZero1970 B hB hF, mul_zero]

theorem reducedZero1971 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1971 (mixedVector B) = 0 := by
  have h4363 : mixedVector B (Sum.inr 4363) = Sparse.eval nodeValue4363 (mixedVector B) := by
    change mixedMoment B node4363 node4363Labels = _
    exact sound4363 B hB hF
  have h4365 : mixedVector B (Sum.inr 4365) = Sparse.eval nodeValue4365 (mixedVector B) := by
    change mixedMoment B node4365 node4365Labels = _
    exact sound4365 B hB hF
  have h4368 : mixedVector B (Sum.inr 4368) = Sparse.eval nodeValue4368 (mixedVector B) := by
    change mixedMoment B node4368 node4368Labels = _
    exact sound4368 B hB hF
  have h4457 : mixedVector B (Sum.inr 4457) = Sparse.eval nodeValue4457 (mixedVector B) := by
    change mixedMoment B node4457 node4457Labels = _
    exact sound4457 B hB hF
  have h4695 : mixedVector B (Sum.inr 4695) = Sparse.eval nodeValue4695 (mixedVector B) := by
    change mixedMoment B node4695 node4695Labels = _
    exact sound4695 B hB hF
  have h4697 : mixedVector B (Sum.inr 4697) = Sparse.eval nodeValue4697 (mixedVector B) := by
    change mixedMoment B node4697 node4697Labels = _
    exact sound4697 B hB hF
  have h4700 : mixedVector B (Sum.inr 4700) = Sparse.eval nodeValue4700 (mixedVector B) := by
    change mixedMoment B node4700 node4700Labels = _
    exact sound4700 B hB hF
  have h4771 : mixedVector B (Sum.inr 4771) = Sparse.eval nodeValue4771 (mixedVector B) := by
    change mixedMoment B node4771 node4771Labels = _
    exact sound4771 B hB hF
  have h4773 : mixedVector B (Sum.inr 4773) = Sparse.eval nodeValue4773 (mixedVector B) := by
    change mixedMoment B node4773 node4773Labels = _
    exact sound4773 B hB hF
  have h4801 : mixedVector B (Sum.inr 4801) = Sparse.eval nodeValue4801 (mixedVector B) := by
    change mixedMoment B node4801 node4801Labels = _
    exact sound4801 B hB hF
  have h4863 : mixedVector B (Sum.inr 4863) = Sparse.eval nodeValue4863 (mixedVector B) := by
    change mixedMoment B node4863 node4863Labels = _
    exact sound4863 B hB hF
  have h4865 : mixedVector B (Sum.inr 4865) = Sparse.eval nodeValue4865 (mixedVector B) := by
    change mixedMoment B node4865 node4865Labels = _
    exact sound4865 B hB hF
  have h4867 : mixedVector B (Sum.inr 4867) = Sparse.eval nodeValue4867 (mixedVector B) := by
    change mixedMoment B node4867 node4867Labels = _
    exact sound4867 B hB hF
  have h4868 : mixedVector B (Sum.inr 4868) = Sparse.eval nodeValue4868 (mixedVector B) := by
    change mixedMoment B node4868 node4868Labels = _
    exact sound4868 B hB hF
  have h4874 : mixedVector B (Sum.inr 4874) = Sparse.eval nodeValue4874 (mixedVector B) := by
    change mixedMoment B node4874 node4874Labels = _
    exact sound4874 B hB hF
  have h4888 : mixedVector B (Sum.inr 4888) = Sparse.eval nodeValue4888 (mixedVector B) := by
    change mixedMoment B node4888 node4888Labels = _
    exact sound4888 B hB hF
  have h4894 : mixedVector B (Sum.inr 4894) = Sparse.eval nodeValue4894 (mixedVector B) := by
    change mixedMoment B node4894 node4894Labels = _
    exact sound4894 B hB hF
  have h5249 : mixedVector B (Sum.inr 5249) = Sparse.eval nodeValue5249 (mixedVector B) := by
    change mixedMoment B node5249 node5249Labels = _
    exact sound5249 B hB hF
  have h5279 : mixedVector B (Sum.inr 5279) = Sparse.eval nodeValue5279 (mixedVector B) := by
    change mixedMoment B node5279 node5279Labels = _
    exact sound5279 B hB hF
  have h5282 : mixedVector B (Sum.inr 5282) = Sparse.eval nodeValue5282 (mixedVector B) := by
    change mixedMoment B node5282 node5282Labels = _
    exact sound5282 B hB hF
  have h5291 : mixedVector B (Sum.inr 5291) = Sparse.eval nodeValue5291 (mixedVector B) := by
    change mixedMoment B node5291 node5291Labels = _
    exact sound5291 B hB hF
  simpa only [sourceForm2451, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4363, h4365, h4368, h4457, h4695, h4697, h4700, h4771, h4773, h4801, h4863, h4865, h4867, h4868, h4874, h4888, h4894, h5249, h5279, h5282, h5291, reducedSource1971] using sourceEq2451 B hB

theorem rowSound1971 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1971 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1971, numericCheck1971, reducedZero1971 B hB hF, mul_zero]

theorem reducedZero1972 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1972 (mixedVector B) = 0 := by
  have h1319 : mixedVector B (Sum.inr 1319) = Sparse.eval nodeValue1319 (mixedVector B) := by
    change mixedMoment B node1319 node1319Labels = _
    exact sound1319 B hB hF
  have h1320 : mixedVector B (Sum.inr 1320) = Sparse.eval nodeValue1320 (mixedVector B) := by
    change mixedMoment B node1320 node1320Labels = _
    exact sound1320 B hB hF
  have h1321 : mixedVector B (Sum.inr 1321) = Sparse.eval nodeValue1321 (mixedVector B) := by
    change mixedMoment B node1321 node1321Labels = _
    exact sound1321 B hB hF
  have h1414 : mixedVector B (Sum.inr 1414) = Sparse.eval nodeValue1414 (mixedVector B) := by
    change mixedMoment B node1414 node1414Labels = _
    exact sound1414 B hB hF
  have h2895 : mixedVector B (Sum.inr 2895) = Sparse.eval nodeValue2895 (mixedVector B) := by
    change mixedMoment B node2895 node2895Labels = _
    exact sound2895 B hB hF
  have h2899 : mixedVector B (Sum.inr 2899) = Sparse.eval nodeValue2899 (mixedVector B) := by
    change mixedMoment B node2899 node2899Labels = _
    exact sound2899 B hB hF
  have h2966 : mixedVector B (Sum.inr 2966) = Sparse.eval nodeValue2966 (mixedVector B) := by
    change mixedMoment B node2966 node2966Labels = _
    exact sound2966 B hB hF
  have h3066 : mixedVector B (Sum.inr 3066) = Sparse.eval nodeValue3066 (mixedVector B) := by
    change mixedMoment B node3066 node3066Labels = _
    exact sound3066 B hB hF
  have h3078 : mixedVector B (Sum.inr 3078) = Sparse.eval nodeValue3078 (mixedVector B) := by
    change mixedMoment B node3078 node3078Labels = _
    exact sound3078 B hB hF
  have h3079 : mixedVector B (Sum.inr 3079) = Sparse.eval nodeValue3079 (mixedVector B) := by
    change mixedMoment B node3079 node3079Labels = _
    exact sound3079 B hB hF
  have h3103 : mixedVector B (Sum.inr 3103) = Sparse.eval nodeValue3103 (mixedVector B) := by
    change mixedMoment B node3103 node3103Labels = _
    exact sound3103 B hB hF
  have h3130 : mixedVector B (Sum.inr 3130) = Sparse.eval nodeValue3130 (mixedVector B) := by
    change mixedMoment B node3130 node3130Labels = _
    exact sound3130 B hB hF
  have h3131 : mixedVector B (Sum.inr 3131) = Sparse.eval nodeValue3131 (mixedVector B) := by
    change mixedMoment B node3131 node3131Labels = _
    exact sound3131 B hB hF
  have h3163 : mixedVector B (Sum.inr 3163) = Sparse.eval nodeValue3163 (mixedVector B) := by
    change mixedMoment B node3163 node3163Labels = _
    exact sound3163 B hB hF
  have h3179 : mixedVector B (Sum.inr 3179) = Sparse.eval nodeValue3179 (mixedVector B) := by
    change mixedMoment B node3179 node3179Labels = _
    exact sound3179 B hB hF
  have h3180 : mixedVector B (Sum.inr 3180) = Sparse.eval nodeValue3180 (mixedVector B) := by
    change mixedMoment B node3180 node3180Labels = _
    exact sound3180 B hB hF
  have h3185 : mixedVector B (Sum.inr 3185) = Sparse.eval nodeValue3185 (mixedVector B) := by
    change mixedMoment B node3185 node3185Labels = _
    exact sound3185 B hB hF
  have h3187 : mixedVector B (Sum.inr 3187) = Sparse.eval nodeValue3187 (mixedVector B) := by
    change mixedMoment B node3187 node3187Labels = _
    exact sound3187 B hB hF
  have h3205 : mixedVector B (Sum.inr 3205) = Sparse.eval nodeValue3205 (mixedVector B) := by
    change mixedMoment B node3205 node3205Labels = _
    exact sound3205 B hB hF
  have h3227 : mixedVector B (Sum.inr 3227) = Sparse.eval nodeValue3227 (mixedVector B) := by
    change mixedMoment B node3227 node3227Labels = _
    exact sound3227 B hB hF
  have h3230 : mixedVector B (Sum.inr 3230) = Sparse.eval nodeValue3230 (mixedVector B) := by
    change mixedMoment B node3230 node3230Labels = _
    exact sound3230 B hB hF
  simpa only [sourceForm2452, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1319, h1320, h1321, h1414, h2895, h2899, h2966, h3066, h3078, h3079, h3103, h3130, h3131, h3163, h3179, h3180, h3185, h3187, h3205, h3227, h3230, reducedSource1972] using sourceEq2452 B hB

theorem rowSound1972 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1972 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1972, numericCheck1972, reducedZero1972 B hB hF, mul_zero]

theorem reducedZero1973 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1973 (mixedVector B) = 0 := by
  have h1697 : mixedVector B (Sum.inr 1697) = Sparse.eval nodeValue1697 (mixedVector B) := by
    change mixedMoment B node1697 node1697Labels = _
    exact sound1697 B hB hF
  have h1704 : mixedVector B (Sum.inr 1704) = Sparse.eval nodeValue1704 (mixedVector B) := by
    change mixedMoment B node1704 node1704Labels = _
    exact sound1704 B hB hF
  have h1707 : mixedVector B (Sum.inr 1707) = Sparse.eval nodeValue1707 (mixedVector B) := by
    change mixedMoment B node1707 node1707Labels = _
    exact sound1707 B hB hF
  have h1712 : mixedVector B (Sum.inr 1712) = Sparse.eval nodeValue1712 (mixedVector B) := by
    change mixedMoment B node1712 node1712Labels = _
    exact sound1712 B hB hF
  have h2189 : mixedVector B (Sum.inr 2189) = Sparse.eval nodeValue2189 (mixedVector B) := by
    change mixedMoment B node2189 node2189Labels = _
    exact sound2189 B hB hF
  have h2190 : mixedVector B (Sum.inr 2190) = Sparse.eval nodeValue2190 (mixedVector B) := by
    change mixedMoment B node2190 node2190Labels = _
    exact sound2190 B hB hF
  have h2194 : mixedVector B (Sum.inr 2194) = Sparse.eval nodeValue2194 (mixedVector B) := by
    change mixedMoment B node2194 node2194Labels = _
    exact sound2194 B hB hF
  have h2231 : mixedVector B (Sum.inr 2231) = Sparse.eval nodeValue2231 (mixedVector B) := by
    change mixedMoment B node2231 node2231Labels = _
    exact sound2231 B hB hF
  have h2232 : mixedVector B (Sum.inr 2232) = Sparse.eval nodeValue2232 (mixedVector B) := by
    change mixedMoment B node2232 node2232Labels = _
    exact sound2232 B hB hF
  have h2239 : mixedVector B (Sum.inr 2239) = Sparse.eval nodeValue2239 (mixedVector B) := by
    change mixedMoment B node2239 node2239Labels = _
    exact sound2239 B hB hF
  have h2242 : mixedVector B (Sum.inr 2242) = Sparse.eval nodeValue2242 (mixedVector B) := by
    change mixedMoment B node2242 node2242Labels = _
    exact sound2242 B hB hF
  have h2244 : mixedVector B (Sum.inr 2244) = Sparse.eval nodeValue2244 (mixedVector B) := by
    change mixedMoment B node2244 node2244Labels = _
    exact sound2244 B hB hF
  have h2249 : mixedVector B (Sum.inr 2249) = Sparse.eval nodeValue2249 (mixedVector B) := by
    change mixedMoment B node2249 node2249Labels = _
    exact sound2249 B hB hF
  have h2251 : mixedVector B (Sum.inr 2251) = Sparse.eval nodeValue2251 (mixedVector B) := by
    change mixedMoment B node2251 node2251Labels = _
    exact sound2251 B hB hF
  have h2261 : mixedVector B (Sum.inr 2261) = Sparse.eval nodeValue2261 (mixedVector B) := by
    change mixedMoment B node2261 node2261Labels = _
    exact sound2261 B hB hF
  have h2264 : mixedVector B (Sum.inr 2264) = Sparse.eval nodeValue2264 (mixedVector B) := by
    change mixedMoment B node2264 node2264Labels = _
    exact sound2264 B hB hF
  have h2276 : mixedVector B (Sum.inr 2276) = Sparse.eval nodeValue2276 (mixedVector B) := by
    change mixedMoment B node2276 node2276Labels = _
    exact sound2276 B hB hF
  have h2708 : mixedVector B (Sum.inr 2708) = Sparse.eval nodeValue2708 (mixedVector B) := by
    change mixedMoment B node2708 node2708Labels = _
    exact sound2708 B hB hF
  have h2748 : mixedVector B (Sum.inr 2748) = Sparse.eval nodeValue2748 (mixedVector B) := by
    change mixedMoment B node2748 node2748Labels = _
    exact sound2748 B hB hF
  have h2751 : mixedVector B (Sum.inr 2751) = Sparse.eval nodeValue2751 (mixedVector B) := by
    change mixedMoment B node2751 node2751Labels = _
    exact sound2751 B hB hF
  have h2765 : mixedVector B (Sum.inr 2765) = Sparse.eval nodeValue2765 (mixedVector B) := by
    change mixedMoment B node2765 node2765Labels = _
    exact sound2765 B hB hF
  simpa only [sourceForm2453, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1697, h1704, h1707, h1712, h2189, h2190, h2194, h2231, h2232, h2239, h2242, h2244, h2249, h2251, h2261, h2264, h2276, h2708, h2748, h2751, h2765, reducedSource1973] using sourceEq2453 B hB

theorem rowSound1973 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1973 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1973, numericCheck1973, reducedZero1973 B hB hF, mul_zero]

theorem reducedZero1974 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1974 (mixedVector B) = 0 := by
  have h1821 : mixedVector B (Sum.inr 1821) = Sparse.eval nodeValue1821 (mixedVector B) := by
    change mixedMoment B node1821 node1821Labels = _
    exact sound1821 B hB hF
  have h1823 : mixedVector B (Sum.inr 1823) = Sparse.eval nodeValue1823 (mixedVector B) := by
    change mixedMoment B node1823 node1823Labels = _
    exact sound1823 B hB hF
  have h1826 : mixedVector B (Sum.inr 1826) = Sparse.eval nodeValue1826 (mixedVector B) := by
    change mixedMoment B node1826 node1826Labels = _
    exact sound1826 B hB hF
  have h2106 : mixedVector B (Sum.inr 2106) = Sparse.eval nodeValue2106 (mixedVector B) := by
    change mixedMoment B node2106 node2106Labels = _
    exact sound2106 B hB hF
  have h3050 : mixedVector B (Sum.inr 3050) = Sparse.eval nodeValue3050 (mixedVector B) := by
    change mixedMoment B node3050 node3050Labels = _
    exact sound3050 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2454, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1821, h1823, h1826, h2106, h3050, h4084, reducedSource1974] using sourceEq2454 B hB

theorem rowSound1974 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1974 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1974, numericCheck1974, reducedZero1974 B hB hF, mul_zero]

theorem reducedZero1975 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1975 (mixedVector B) = 0 := by
  have h941 : mixedVector B (Sum.inr 941) = Sparse.eval nodeValue941 (mixedVector B) := by
    change mixedMoment B node941 node941Labels = _
    exact sound941 B hB hF
  have h1821 : mixedVector B (Sum.inr 1821) = Sparse.eval nodeValue1821 (mixedVector B) := by
    change mixedMoment B node1821 node1821Labels = _
    exact sound1821 B hB hF
  have h2104 : mixedVector B (Sum.inr 2104) = Sparse.eval nodeValue2104 (mixedVector B) := by
    change mixedMoment B node2104 node2104Labels = _
    exact sound2104 B hB hF
  have h2106 : mixedVector B (Sum.inr 2106) = Sparse.eval nodeValue2106 (mixedVector B) := by
    change mixedMoment B node2106 node2106Labels = _
    exact sound2106 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2455, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h941, h1821, h2104, h2106, h4084, reducedSource1975] using sourceEq2455 B hB

theorem rowSound1975 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1975 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1975, numericCheck1975, reducedZero1975 B hB hF, mul_zero]

theorem reducedZero1976 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1976 (mixedVector B) = 0 := by
  have h4230 : mixedVector B (Sum.inr 4230) = Sparse.eval nodeValue4230 (mixedVector B) := by
    change mixedMoment B node4230 node4230Labels = _
    exact sound4230 B hB hF
  have h4231 : mixedVector B (Sum.inr 4231) = Sparse.eval nodeValue4231 (mixedVector B) := by
    change mixedMoment B node4231 node4231Labels = _
    exact sound4231 B hB hF
  have h4234 : mixedVector B (Sum.inr 4234) = Sparse.eval nodeValue4234 (mixedVector B) := by
    change mixedMoment B node4234 node4234Labels = _
    exact sound4234 B hB hF
  have h4255 : mixedVector B (Sum.inr 4255) = Sparse.eval nodeValue4255 (mixedVector B) := by
    change mixedMoment B node4255 node4255Labels = _
    exact sound4255 B hB hF
  have h4676 : mixedVector B (Sum.inr 4676) = Sparse.eval nodeValue4676 (mixedVector B) := by
    change mixedMoment B node4676 node4676Labels = _
    exact sound4676 B hB hF
  have h4678 : mixedVector B (Sum.inr 4678) = Sparse.eval nodeValue4678 (mixedVector B) := by
    change mixedMoment B node4678 node4678Labels = _
    exact sound4678 B hB hF
  have h4684 : mixedVector B (Sum.inr 4684) = Sparse.eval nodeValue4684 (mixedVector B) := by
    change mixedMoment B node4684 node4684Labels = _
    exact sound4684 B hB hF
  have h4720 : mixedVector B (Sum.inr 4720) = Sparse.eval nodeValue4720 (mixedVector B) := by
    change mixedMoment B node4720 node4720Labels = _
    exact sound4720 B hB hF
  have h4722 : mixedVector B (Sum.inr 4722) = Sparse.eval nodeValue4722 (mixedVector B) := by
    change mixedMoment B node4722 node4722Labels = _
    exact sound4722 B hB hF
  have h4731 : mixedVector B (Sum.inr 4731) = Sparse.eval nodeValue4731 (mixedVector B) := by
    change mixedMoment B node4731 node4731Labels = _
    exact sound4731 B hB hF
  have h4798 : mixedVector B (Sum.inr 4798) = Sparse.eval nodeValue4798 (mixedVector B) := by
    change mixedMoment B node4798 node4798Labels = _
    exact sound4798 B hB hF
  have h4800 : mixedVector B (Sum.inr 4800) = Sparse.eval nodeValue4800 (mixedVector B) := by
    change mixedMoment B node4800 node4800Labels = _
    exact sound4800 B hB hF
  have h4810 : mixedVector B (Sum.inr 4810) = Sparse.eval nodeValue4810 (mixedVector B) := by
    change mixedMoment B node4810 node4810Labels = _
    exact sound4810 B hB hF
  have h4828 : mixedVector B (Sum.inr 4828) = Sparse.eval nodeValue4828 (mixedVector B) := by
    change mixedMoment B node4828 node4828Labels = _
    exact sound4828 B hB hF
  have h4864 : mixedVector B (Sum.inr 4864) = Sparse.eval nodeValue4864 (mixedVector B) := by
    change mixedMoment B node4864 node4864Labels = _
    exact sound4864 B hB hF
  have h4866 : mixedVector B (Sum.inr 4866) = Sparse.eval nodeValue4866 (mixedVector B) := by
    change mixedMoment B node4866 node4866Labels = _
    exact sound4866 B hB hF
  have h4889 : mixedVector B (Sum.inr 4889) = Sparse.eval nodeValue4889 (mixedVector B) := by
    change mixedMoment B node4889 node4889Labels = _
    exact sound4889 B hB hF
  have h5387 : mixedVector B (Sum.inr 5387) = Sparse.eval nodeValue5387 (mixedVector B) := by
    change mixedMoment B node5387 node5387Labels = _
    exact sound5387 B hB hF
  have h5400 : mixedVector B (Sum.inr 5400) = Sparse.eval nodeValue5400 (mixedVector B) := by
    change mixedMoment B node5400 node5400Labels = _
    exact sound5400 B hB hF
  have h5432 : mixedVector B (Sum.inr 5432) = Sparse.eval nodeValue5432 (mixedVector B) := by
    change mixedMoment B node5432 node5432Labels = _
    exact sound5432 B hB hF
  have h5450 : mixedVector B (Sum.inr 5450) = Sparse.eval nodeValue5450 (mixedVector B) := by
    change mixedMoment B node5450 node5450Labels = _
    exact sound5450 B hB hF
  simpa only [sourceForm2456, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4230, h4231, h4234, h4255, h4676, h4678, h4684, h4720, h4722, h4731, h4798, h4800, h4810, h4828, h4864, h4866, h4889, h5387, h5400, h5432, h5450, reducedSource1976] using sourceEq2456 B hB

theorem rowSound1976 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1976 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1976, numericCheck1976, reducedZero1976 B hB hF, mul_zero]

theorem reducedZero1977 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1977 (mixedVector B) = 0 := by
  have h730 : mixedVector B (Sum.inr 730) = Sparse.eval nodeValue730 (mixedVector B) := by
    change mixedMoment B node730 node730Labels = _
    exact sound730 B hB hF
  have h731 : mixedVector B (Sum.inr 731) = Sparse.eval nodeValue731 (mixedVector B) := by
    change mixedMoment B node731 node731Labels = _
    exact sound731 B hB hF
  have h734 : mixedVector B (Sum.inr 734) = Sparse.eval nodeValue734 (mixedVector B) := by
    change mixedMoment B node734 node734Labels = _
    exact sound734 B hB hF
  have h823 : mixedVector B (Sum.inr 823) = Sparse.eval nodeValue823 (mixedVector B) := by
    change mixedMoment B node823 node823Labels = _
    exact sound823 B hB hF
  have h1802 : mixedVector B (Sum.inr 1802) = Sparse.eval nodeValue1802 (mixedVector B) := by
    change mixedMoment B node1802 node1802Labels = _
    exact sound1802 B hB hF
  have h1804 : mixedVector B (Sum.inr 1804) = Sparse.eval nodeValue1804 (mixedVector B) := by
    change mixedMoment B node1804 node1804Labels = _
    exact sound1804 B hB hF
  have h1810 : mixedVector B (Sum.inr 1810) = Sparse.eval nodeValue1810 (mixedVector B) := by
    change mixedMoment B node1810 node1810Labels = _
    exact sound1810 B hB hF
  have h1874 : mixedVector B (Sum.inr 1874) = Sparse.eval nodeValue1874 (mixedVector B) := by
    change mixedMoment B node1874 node1874Labels = _
    exact sound1874 B hB hF
  have h1876 : mixedVector B (Sum.inr 1876) = Sparse.eval nodeValue1876 (mixedVector B) := by
    change mixedMoment B node1876 node1876Labels = _
    exact sound1876 B hB hF
  have h1921 : mixedVector B (Sum.inr 1921) = Sparse.eval nodeValue1921 (mixedVector B) := by
    change mixedMoment B node1921 node1921Labels = _
    exact sound1921 B hB hF
  have h2018 : mixedVector B (Sum.inr 2018) = Sparse.eval nodeValue2018 (mixedVector B) := by
    change mixedMoment B node2018 node2018Labels = _
    exact sound2018 B hB hF
  have h2075 : mixedVector B (Sum.inr 2075) = Sparse.eval nodeValue2075 (mixedVector B) := by
    change mixedMoment B node2075 node2075Labels = _
    exact sound2075 B hB hF
  have h2082 : mixedVector B (Sum.inr 2082) = Sparse.eval nodeValue2082 (mixedVector B) := by
    change mixedMoment B node2082 node2082Labels = _
    exact sound2082 B hB hF
  have h2105 : mixedVector B (Sum.inr 2105) = Sparse.eval nodeValue2105 (mixedVector B) := by
    change mixedMoment B node2105 node2105Labels = _
    exact sound2105 B hB hF
  have h2107 : mixedVector B (Sum.inr 2107) = Sparse.eval nodeValue2107 (mixedVector B) := by
    change mixedMoment B node2107 node2107Labels = _
    exact sound2107 B hB hF
  have h2215 : mixedVector B (Sum.inr 2215) = Sparse.eval nodeValue2215 (mixedVector B) := by
    change mixedMoment B node2215 node2215Labels = _
    exact sound2215 B hB hF
  have h2277 : mixedVector B (Sum.inr 2277) = Sparse.eval nodeValue2277 (mixedVector B) := by
    change mixedMoment B node2277 node2277Labels = _
    exact sound2277 B hB hF
  have h3736 : mixedVector B (Sum.inr 3736) = Sparse.eval nodeValue3736 (mixedVector B) := by
    change mixedMoment B node3736 node3736Labels = _
    exact sound3736 B hB hF
  have h3786 : mixedVector B (Sum.inr 3786) = Sparse.eval nodeValue3786 (mixedVector B) := by
    change mixedMoment B node3786 node3786Labels = _
    exact sound3786 B hB hF
  have h3850 : mixedVector B (Sum.inr 3850) = Sparse.eval nodeValue3850 (mixedVector B) := by
    change mixedMoment B node3850 node3850Labels = _
    exact sound3850 B hB hF
  have h3887 : mixedVector B (Sum.inr 3887) = Sparse.eval nodeValue3887 (mixedVector B) := by
    change mixedMoment B node3887 node3887Labels = _
    exact sound3887 B hB hF
  simpa only [sourceForm2457, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h730, h731, h734, h823, h1802, h1804, h1810, h1874, h1876, h1921, h2018, h2075, h2082, h2105, h2107, h2215, h2277, h3736, h3786, h3850, h3887, reducedSource1977] using sourceEq2457 B hB

theorem rowSound1977 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1977 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1977, numericCheck1977, reducedZero1977 B hB hF, mul_zero]

theorem reducedZero1978 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1978 (mixedVector B) = 0 := by
  have h4435 : mixedVector B (Sum.inr 4435) = Sparse.eval nodeValue4435 (mixedVector B) := by
    change mixedMoment B node4435 node4435Labels = _
    exact sound4435 B hB hF
  have h4437 : mixedVector B (Sum.inr 4437) = Sparse.eval nodeValue4437 (mixedVector B) := by
    change mixedMoment B node4437 node4437Labels = _
    exact sound4437 B hB hF
  have h4443 : mixedVector B (Sum.inr 4443) = Sparse.eval nodeValue4443 (mixedVector B) := by
    change mixedMoment B node4443 node4443Labels = _
    exact sound4443 B hB hF
  have h4452 : mixedVector B (Sum.inr 4452) = Sparse.eval nodeValue4452 (mixedVector B) := by
    change mixedMoment B node4452 node4452Labels = _
    exact sound4452 B hB hF
  have h4791 : mixedVector B (Sum.inr 4791) = Sparse.eval nodeValue4791 (mixedVector B) := by
    change mixedMoment B node4791 node4791Labels = _
    exact sound4791 B hB hF
  have h4794 : mixedVector B (Sum.inr 4794) = Sparse.eval nodeValue4794 (mixedVector B) := by
    change mixedMoment B node4794 node4794Labels = _
    exact sound4794 B hB hF
  have h4798 : mixedVector B (Sum.inr 4798) = Sparse.eval nodeValue4798 (mixedVector B) := by
    change mixedMoment B node4798 node4798Labels = _
    exact sound4798 B hB hF
  have h4801 : mixedVector B (Sum.inr 4801) = Sparse.eval nodeValue4801 (mixedVector B) := by
    change mixedMoment B node4801 node4801Labels = _
    exact sound4801 B hB hF
  have h4832 : mixedVector B (Sum.inr 4832) = Sparse.eval nodeValue4832 (mixedVector B) := by
    change mixedMoment B node4832 node4832Labels = _
    exact sound4832 B hB hF
  have h4834 : mixedVector B (Sum.inr 4834) = Sparse.eval nodeValue4834 (mixedVector B) := by
    change mixedMoment B node4834 node4834Labels = _
    exact sound4834 B hB hF
  have h4848 : mixedVector B (Sum.inr 4848) = Sparse.eval nodeValue4848 (mixedVector B) := by
    change mixedMoment B node4848 node4848Labels = _
    exact sound4848 B hB hF
  have h4850 : mixedVector B (Sum.inr 4850) = Sparse.eval nodeValue4850 (mixedVector B) := by
    change mixedMoment B node4850 node4850Labels = _
    exact sound4850 B hB hF
  have h4851 : mixedVector B (Sum.inr 4851) = Sparse.eval nodeValue4851 (mixedVector B) := by
    change mixedMoment B node4851 node4851Labels = _
    exact sound4851 B hB hF
  have h4855 : mixedVector B (Sum.inr 4855) = Sparse.eval nodeValue4855 (mixedVector B) := by
    change mixedMoment B node4855 node4855Labels = _
    exact sound4855 B hB hF
  have h4860 : mixedVector B (Sum.inr 4860) = Sparse.eval nodeValue4860 (mixedVector B) := by
    change mixedMoment B node4860 node4860Labels = _
    exact sound4860 B hB hF
  have h4866 : mixedVector B (Sum.inr 4866) = Sparse.eval nodeValue4866 (mixedVector B) := by
    change mixedMoment B node4866 node4866Labels = _
    exact sound4866 B hB hF
  have h4879 : mixedVector B (Sum.inr 4879) = Sparse.eval nodeValue4879 (mixedVector B) := by
    change mixedMoment B node4879 node4879Labels = _
    exact sound4879 B hB hF
  have h5168 : mixedVector B (Sum.inr 5168) = Sparse.eval nodeValue5168 (mixedVector B) := by
    change mixedMoment B node5168 node5168Labels = _
    exact sound5168 B hB hF
  have h5184 : mixedVector B (Sum.inr 5184) = Sparse.eval nodeValue5184 (mixedVector B) := by
    change mixedMoment B node5184 node5184Labels = _
    exact sound5184 B hB hF
  have h5198 : mixedVector B (Sum.inr 5198) = Sparse.eval nodeValue5198 (mixedVector B) := by
    change mixedMoment B node5198 node5198Labels = _
    exact sound5198 B hB hF
  have h5203 : mixedVector B (Sum.inr 5203) = Sparse.eval nodeValue5203 (mixedVector B) := by
    change mixedMoment B node5203 node5203Labels = _
    exact sound5203 B hB hF
  simpa only [sourceForm2458, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4435, h4437, h4443, h4452, h4791, h4794, h4798, h4801, h4832, h4834, h4848, h4850, h4851, h4855, h4860, h4866, h4879, h5168, h5184, h5198, h5203, reducedSource1978] using sourceEq2458 B hB

theorem rowSound1978 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1978 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1978, numericCheck1978, reducedZero1978 B hB hF, mul_zero]

theorem reducedZero1979 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1979 (mixedVector B) = 0 := by
  have h1877 : mixedVector B (Sum.inr 1877) = Sparse.eval nodeValue1877 (mixedVector B) := by
    change mixedMoment B node1877 node1877Labels = _
    exact sound1877 B hB hF
  have h1879 : mixedVector B (Sum.inr 1879) = Sparse.eval nodeValue1879 (mixedVector B) := by
    change mixedMoment B node1879 node1879Labels = _
    exact sound1879 B hB hF
  have h1912 : mixedVector B (Sum.inr 1912) = Sparse.eval nodeValue1912 (mixedVector B) := by
    change mixedMoment B node1912 node1912Labels = _
    exact sound1912 B hB hF
  have h2077 : mixedVector B (Sum.inr 2077) = Sparse.eval nodeValue2077 (mixedVector B) := by
    change mixedMoment B node2077 node2077Labels = _
    exact sound2077 B hB hF
  have h3446 : mixedVector B (Sum.inr 3446) = Sparse.eval nodeValue3446 (mixedVector B) := by
    change mixedMoment B node3446 node3446Labels = _
    exact sound3446 B hB hF
  have h4079 : mixedVector B (Sum.inr 4079) = Sparse.eval nodeValue4079 (mixedVector B) := by
    change mixedMoment B node4079 node4079Labels = _
    exact sound4079 B hB hF
  simpa only [sourceForm2460, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1877, h1879, h1912, h2077, h3446, h4079, reducedSource1979] using sourceEq2460 B hB

theorem rowSound1979 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1979 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1979, numericCheck1979, reducedZero1979 B hB hF, mul_zero]

theorem reducedZero1980 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1980 (mixedVector B) = 0 := by
  have h4331 : mixedVector B (Sum.inr 4331) = Sparse.eval nodeValue4331 (mixedVector B) := by
    change mixedMoment B node4331 node4331Labels = _
    exact sound4331 B hB hF
  have h4332 : mixedVector B (Sum.inr 4332) = Sparse.eval nodeValue4332 (mixedVector B) := by
    change mixedMoment B node4332 node4332Labels = _
    exact sound4332 B hB hF
  have h4351 : mixedVector B (Sum.inr 4351) = Sparse.eval nodeValue4351 (mixedVector B) := by
    change mixedMoment B node4351 node4351Labels = _
    exact sound4351 B hB hF
  have h4461 : mixedVector B (Sum.inr 4461) = Sparse.eval nodeValue4461 (mixedVector B) := by
    change mixedMoment B node4461 node4461Labels = _
    exact sound4461 B hB hF
  have h4667 : mixedVector B (Sum.inr 4667) = Sparse.eval nodeValue4667 (mixedVector B) := by
    change mixedMoment B node4667 node4667Labels = _
    exact sound4667 B hB hF
  have h4668 : mixedVector B (Sum.inr 4668) = Sparse.eval nodeValue4668 (mixedVector B) := by
    change mixedMoment B node4668 node4668Labels = _
    exact sound4668 B hB hF
  have h4685 : mixedVector B (Sum.inr 4685) = Sparse.eval nodeValue4685 (mixedVector B) := by
    change mixedMoment B node4685 node4685Labels = _
    exact sound4685 B hB hF
  have h4765 : mixedVector B (Sum.inr 4765) = Sparse.eval nodeValue4765 (mixedVector B) := by
    change mixedMoment B node4765 node4765Labels = _
    exact sound4765 B hB hF
  have h4775 : mixedVector B (Sum.inr 4775) = Sparse.eval nodeValue4775 (mixedVector B) := by
    change mixedMoment B node4775 node4775Labels = _
    exact sound4775 B hB hF
  have h4793 : mixedVector B (Sum.inr 4793) = Sparse.eval nodeValue4793 (mixedVector B) := by
    change mixedMoment B node4793 node4793Labels = _
    exact sound4793 B hB hF
  have h4795 : mixedVector B (Sum.inr 4795) = Sparse.eval nodeValue4795 (mixedVector B) := by
    change mixedMoment B node4795 node4795Labels = _
    exact sound4795 B hB hF
  have h4802 : mixedVector B (Sum.inr 4802) = Sparse.eval nodeValue4802 (mixedVector B) := by
    change mixedMoment B node4802 node4802Labels = _
    exact sound4802 B hB hF
  have h4805 : mixedVector B (Sum.inr 4805) = Sparse.eval nodeValue4805 (mixedVector B) := by
    change mixedMoment B node4805 node4805Labels = _
    exact sound4805 B hB hF
  have h4833 : mixedVector B (Sum.inr 4833) = Sparse.eval nodeValue4833 (mixedVector B) := by
    change mixedMoment B node4833 node4833Labels = _
    exact sound4833 B hB hF
  have h4869 : mixedVector B (Sum.inr 4869) = Sparse.eval nodeValue4869 (mixedVector B) := by
    change mixedMoment B node4869 node4869Labels = _
    exact sound4869 B hB hF
  have h4889 : mixedVector B (Sum.inr 4889) = Sparse.eval nodeValue4889 (mixedVector B) := by
    change mixedMoment B node4889 node4889Labels = _
    exact sound4889 B hB hF
  have h4893 : mixedVector B (Sum.inr 4893) = Sparse.eval nodeValue4893 (mixedVector B) := by
    change mixedMoment B node4893 node4893Labels = _
    exact sound4893 B hB hF
  have h5231 : mixedVector B (Sum.inr 5231) = Sparse.eval nodeValue5231 (mixedVector B) := by
    change mixedMoment B node5231 node5231Labels = _
    exact sound5231 B hB hF
  have h5257 : mixedVector B (Sum.inr 5257) = Sparse.eval nodeValue5257 (mixedVector B) := by
    change mixedMoment B node5257 node5257Labels = _
    exact sound5257 B hB hF
  have h5263 : mixedVector B (Sum.inr 5263) = Sparse.eval nodeValue5263 (mixedVector B) := by
    change mixedMoment B node5263 node5263Labels = _
    exact sound5263 B hB hF
  have h5265 : mixedVector B (Sum.inr 5265) = Sparse.eval nodeValue5265 (mixedVector B) := by
    change mixedMoment B node5265 node5265Labels = _
    exact sound5265 B hB hF
  simpa only [sourceForm2461, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4331, h4332, h4351, h4461, h4667, h4668, h4685, h4765, h4775, h4793, h4795, h4802, h4805, h4833, h4869, h4889, h4893, h5231, h5257, h5263, h5265, reducedSource1980] using sourceEq2461 B hB

theorem rowSound1980 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1980 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1980, numericCheck1980, reducedZero1980 B hB hF, mul_zero]

theorem reducedZero1981 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1981 (mixedVector B) = 0 := by
  have h1678 : mixedVector B (Sum.inr 1678) = Sparse.eval nodeValue1678 (mixedVector B) := by
    change mixedMoment B node1678 node1678Labels = _
    exact sound1678 B hB hF
  have h1680 : mixedVector B (Sum.inr 1680) = Sparse.eval nodeValue1680 (mixedVector B) := by
    change mixedMoment B node1680 node1680Labels = _
    exact sound1680 B hB hF
  have h1684 : mixedVector B (Sum.inr 1684) = Sparse.eval nodeValue1684 (mixedVector B) := by
    change mixedMoment B node1684 node1684Labels = _
    exact sound1684 B hB hF
  have h1737 : mixedVector B (Sum.inr 1737) = Sparse.eval nodeValue1737 (mixedVector B) := by
    change mixedMoment B node1737 node1737Labels = _
    exact sound1737 B hB hF
  have h2154 : mixedVector B (Sum.inr 2154) = Sparse.eval nodeValue2154 (mixedVector B) := by
    change mixedMoment B node2154 node2154Labels = _
    exact sound2154 B hB hF
  have h2156 : mixedVector B (Sum.inr 2156) = Sparse.eval nodeValue2156 (mixedVector B) := by
    change mixedMoment B node2156 node2156Labels = _
    exact sound2156 B hB hF
  have h2160 : mixedVector B (Sum.inr 2160) = Sparse.eval nodeValue2160 (mixedVector B) := by
    change mixedMoment B node2160 node2160Labels = _
    exact sound2160 B hB hF
  have h2179 : mixedVector B (Sum.inr 2179) = Sparse.eval nodeValue2179 (mixedVector B) := by
    change mixedMoment B node2179 node2179Labels = _
    exact sound2179 B hB hF
  have h2202 : mixedVector B (Sum.inr 2202) = Sparse.eval nodeValue2202 (mixedVector B) := by
    change mixedMoment B node2202 node2202Labels = _
    exact sound2202 B hB hF
  have h2204 : mixedVector B (Sum.inr 2204) = Sparse.eval nodeValue2204 (mixedVector B) := by
    change mixedMoment B node2204 node2204Labels = _
    exact sound2204 B hB hF
  have h2211 : mixedVector B (Sum.inr 2211) = Sparse.eval nodeValue2211 (mixedVector B) := by
    change mixedMoment B node2211 node2211Labels = _
    exact sound2211 B hB hF
  have h2213 : mixedVector B (Sum.inr 2213) = Sparse.eval nodeValue2213 (mixedVector B) := by
    change mixedMoment B node2213 node2213Labels = _
    exact sound2213 B hB hF
  have h2214 : mixedVector B (Sum.inr 2214) = Sparse.eval nodeValue2214 (mixedVector B) := by
    change mixedMoment B node2214 node2214Labels = _
    exact sound2214 B hB hF
  have h2219 : mixedVector B (Sum.inr 2219) = Sparse.eval nodeValue2219 (mixedVector B) := by
    change mixedMoment B node2219 node2219Labels = _
    exact sound2219 B hB hF
  have h2263 : mixedVector B (Sum.inr 2263) = Sparse.eval nodeValue2263 (mixedVector B) := by
    change mixedMoment B node2263 node2263Labels = _
    exact sound2263 B hB hF
  have h2275 : mixedVector B (Sum.inr 2275) = Sparse.eval nodeValue2275 (mixedVector B) := by
    change mixedMoment B node2275 node2275Labels = _
    exact sound2275 B hB hF
  have h2277 : mixedVector B (Sum.inr 2277) = Sparse.eval nodeValue2277 (mixedVector B) := by
    change mixedMoment B node2277 node2277Labels = _
    exact sound2277 B hB hF
  have h2676 : mixedVector B (Sum.inr 2676) = Sparse.eval nodeValue2676 (mixedVector B) := by
    change mixedMoment B node2676 node2676Labels = _
    exact sound2676 B hB hF
  have h2721 : mixedVector B (Sum.inr 2721) = Sparse.eval nodeValue2721 (mixedVector B) := by
    change mixedMoment B node2721 node2721Labels = _
    exact sound2721 B hB hF
  have h2728 : mixedVector B (Sum.inr 2728) = Sparse.eval nodeValue2728 (mixedVector B) := by
    change mixedMoment B node2728 node2728Labels = _
    exact sound2728 B hB hF
  have h2730 : mixedVector B (Sum.inr 2730) = Sparse.eval nodeValue2730 (mixedVector B) := by
    change mixedMoment B node2730 node2730Labels = _
    exact sound2730 B hB hF
  simpa only [sourceForm2462, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1678, h1680, h1684, h1737, h2154, h2156, h2160, h2179, h2202, h2204, h2211, h2213, h2214, h2219, h2263, h2275, h2277, h2676, h2721, h2728, h2730, reducedSource1981] using sourceEq2462 B hB

theorem rowSound1981 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1981 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1981, numericCheck1981, reducedZero1981 B hB hF, mul_zero]

theorem reducedZero1982 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1982 (mixedVector B) = 0 := by
  have h1793 : mixedVector B (Sum.inr 1793) = Sparse.eval nodeValue1793 (mixedVector B) := by
    change mixedMoment B node1793 node1793Labels = _
    exact sound1793 B hB hF
  have h1794 : mixedVector B (Sum.inr 1794) = Sparse.eval nodeValue1794 (mixedVector B) := by
    change mixedMoment B node1794 node1794Labels = _
    exact sound1794 B hB hF
  have h1811 : mixedVector B (Sum.inr 1811) = Sparse.eval nodeValue1811 (mixedVector B) := by
    change mixedMoment B node1811 node1811Labels = _
    exact sound1811 B hB hF
  have h2023 : mixedVector B (Sum.inr 2023) = Sparse.eval nodeValue2023 (mixedVector B) := by
    change mixedMoment B node2023 node2023Labels = _
    exact sound2023 B hB hF
  have h3378 : mixedVector B (Sum.inr 3378) = Sparse.eval nodeValue3378 (mixedVector B) := by
    change mixedMoment B node3378 node3378Labels = _
    exact sound3378 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm2463, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1793, h1794, h1811, h2023, h3378, h4083, reducedSource1982] using sourceEq2463 B hB

theorem rowSound1982 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1982 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1982, numericCheck1982, reducedZero1982 B hB hF, mul_zero]

theorem reducedZero1983 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1983 (mixedVector B) = 0 := by
  have h4199 : mixedVector B (Sum.inr 4199) = Sparse.eval nodeValue4199 (mixedVector B) := by
    change mixedMoment B node4199 node4199Labels = _
    exact sound4199 B hB hF
  have h4200 : mixedVector B (Sum.inr 4200) = Sparse.eval nodeValue4200 (mixedVector B) := by
    change mixedMoment B node4200 node4200Labels = _
    exact sound4200 B hB hF
  have h4217 : mixedVector B (Sum.inr 4217) = Sparse.eval nodeValue4217 (mixedVector B) := by
    change mixedMoment B node4217 node4217Labels = _
    exact sound4217 B hB hF
  have h4252 : mixedVector B (Sum.inr 4252) = Sparse.eval nodeValue4252 (mixedVector B) := by
    change mixedMoment B node4252 node4252Labels = _
    exact sound4252 B hB hF
  have h4633 : mixedVector B (Sum.inr 4633) = Sparse.eval nodeValue4633 (mixedVector B) := by
    change mixedMoment B node4633 node4633Labels = _
    exact sound4633 B hB hF
  have h4634 : mixedVector B (Sum.inr 4634) = Sparse.eval nodeValue4634 (mixedVector B) := by
    change mixedMoment B node4634 node4634Labels = _
    exact sound4634 B hB hF
  have h4648 : mixedVector B (Sum.inr 4648) = Sparse.eval nodeValue4648 (mixedVector B) := by
    change mixedMoment B node4648 node4648Labels = _
    exact sound4648 B hB hF
  have h4764 : mixedVector B (Sum.inr 4764) = Sparse.eval nodeValue4764 (mixedVector B) := by
    change mixedMoment B node4764 node4764Labels = _
    exact sound4764 B hB hF
  have h4766 : mixedVector B (Sum.inr 4766) = Sparse.eval nodeValue4766 (mixedVector B) := by
    change mixedMoment B node4766 node4766Labels = _
    exact sound4766 B hB hF
  have h4798 : mixedVector B (Sum.inr 4798) = Sparse.eval nodeValue4798 (mixedVector B) := by
    change mixedMoment B node4798 node4798Labels = _
    exact sound4798 B hB hF
  have h4805 : mixedVector B (Sum.inr 4805) = Sparse.eval nodeValue4805 (mixedVector B) := by
    change mixedMoment B node4805 node4805Labels = _
    exact sound4805 B hB hF
  have h4807 : mixedVector B (Sum.inr 4807) = Sparse.eval nodeValue4807 (mixedVector B) := by
    change mixedMoment B node4807 node4807Labels = _
    exact sound4807 B hB hF
  have h4810 : mixedVector B (Sum.inr 4810) = Sparse.eval nodeValue4810 (mixedVector B) := by
    change mixedMoment B node4810 node4810Labels = _
    exact sound4810 B hB hF
  have h4826 : mixedVector B (Sum.inr 4826) = Sparse.eval nodeValue4826 (mixedVector B) := by
    change mixedMoment B node4826 node4826Labels = _
    exact sound4826 B hB hF
  have h4839 : mixedVector B (Sum.inr 4839) = Sparse.eval nodeValue4839 (mixedVector B) := by
    change mixedMoment B node4839 node4839Labels = _
    exact sound4839 B hB hF
  have h4864 : mixedVector B (Sum.inr 4864) = Sparse.eval nodeValue4864 (mixedVector B) := by
    change mixedMoment B node4864 node4864Labels = _
    exact sound4864 B hB hF
  have h4889 : mixedVector B (Sum.inr 4889) = Sparse.eval nodeValue4889 (mixedVector B) := by
    change mixedMoment B node4889 node4889Labels = _
    exact sound4889 B hB hF
  have h5354 : mixedVector B (Sum.inr 5354) = Sparse.eval nodeValue5354 (mixedVector B) := by
    change mixedMoment B node5354 node5354Labels = _
    exact sound5354 B hB hF
  have h5417 : mixedVector B (Sum.inr 5417) = Sparse.eval nodeValue5417 (mixedVector B) := by
    change mixedMoment B node5417 node5417Labels = _
    exact sound5417 B hB hF
  have h5431 : mixedVector B (Sum.inr 5431) = Sparse.eval nodeValue5431 (mixedVector B) := by
    change mixedMoment B node5431 node5431Labels = _
    exact sound5431 B hB hF
  have h5435 : mixedVector B (Sum.inr 5435) = Sparse.eval nodeValue5435 (mixedVector B) := by
    change mixedMoment B node5435 node5435Labels = _
    exact sound5435 B hB hF
  simpa only [sourceForm2464, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4199, h4200, h4217, h4252, h4633, h4634, h4648, h4764, h4766, h4798, h4805, h4807, h4810, h4826, h4839, h4864, h4889, h5354, h5417, h5431, h5435, reducedSource1983] using sourceEq2464 B hB

theorem rowSound1983 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1983 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1983, numericCheck1983, reducedZero1983 B hB hF, mul_zero]

theorem sourceRowsAt1968 : MixedData.sourceRows (1968 : Fin 2425) =
    MixedData.row1968 := by decide +kernel

theorem sourceRowsAt1969 : MixedData.sourceRows (1969 : Fin 2425) =
    MixedData.row1969 := by decide +kernel

theorem sourceRowsAt1970 : MixedData.sourceRows (1970 : Fin 2425) =
    MixedData.row1970 := by decide +kernel

theorem sourceRowsAt1971 : MixedData.sourceRows (1971 : Fin 2425) =
    MixedData.row1971 := by decide +kernel

theorem sourceRowsAt1972 : MixedData.sourceRows (1972 : Fin 2425) =
    MixedData.row1972 := by decide +kernel

theorem sourceRowsAt1973 : MixedData.sourceRows (1973 : Fin 2425) =
    MixedData.row1973 := by decide +kernel

theorem sourceRowsAt1974 : MixedData.sourceRows (1974 : Fin 2425) =
    MixedData.row1974 := by decide +kernel

theorem sourceRowsAt1975 : MixedData.sourceRows (1975 : Fin 2425) =
    MixedData.row1975 := by decide +kernel

theorem sourceRowsAt1976 : MixedData.sourceRows (1976 : Fin 2425) =
    MixedData.row1976 := by decide +kernel

theorem sourceRowsAt1977 : MixedData.sourceRows (1977 : Fin 2425) =
    MixedData.row1977 := by decide +kernel

theorem sourceRowsAt1978 : MixedData.sourceRows (1978 : Fin 2425) =
    MixedData.row1978 := by decide +kernel

theorem sourceRowsAt1979 : MixedData.sourceRows (1979 : Fin 2425) =
    MixedData.row1979 := by decide +kernel

theorem sourceRowsAt1980 : MixedData.sourceRows (1980 : Fin 2425) =
    MixedData.row1980 := by decide +kernel

theorem sourceRowsAt1981 : MixedData.sourceRows (1981 : Fin 2425) =
    MixedData.row1981 := by decide +kernel

theorem sourceRowsAt1982 : MixedData.sourceRows (1982 : Fin 2425) =
    MixedData.row1982 := by decide +kernel

theorem sourceRowsAt1983 : MixedData.sourceRows (1983 : Fin 2425) =
    MixedData.row1983 := by decide +kernel

theorem chunkSound123 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 123) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1968 ∨ k.val = 1969 ∨ k.val = 1970 ∨ k.val = 1971 ∨ k.val = 1972 ∨ k.val = 1973 ∨ k.val = 1974 ∨ k.val = 1975 ∨ k.val = 1976 ∨ k.val = 1977 ∨ k.val = 1978 ∨ k.val = 1979 ∨ k.val = 1980 ∨ k.val = 1981 ∨ k.val = 1982 ∨ k.val = 1983 := by omega
  rcases heq with h1968 | h1969 | h1970 | h1971 | h1972 | h1973 | h1974 | h1975 | h1976 | h1977 | h1978 | h1979 | h1980 | h1981 | h1982 | h1983
  · have he : k = (1968 : Fin 2425) := Fin.ext h1968
    subst k
    rw [sourceRowsAt1968]
    exact rowSound1968 B hB hF
  · have he : k = (1969 : Fin 2425) := Fin.ext h1969
    subst k
    rw [sourceRowsAt1969]
    exact rowSound1969 B hB hF
  · have he : k = (1970 : Fin 2425) := Fin.ext h1970
    subst k
    rw [sourceRowsAt1970]
    exact rowSound1970 B hB hF
  · have he : k = (1971 : Fin 2425) := Fin.ext h1971
    subst k
    rw [sourceRowsAt1971]
    exact rowSound1971 B hB hF
  · have he : k = (1972 : Fin 2425) := Fin.ext h1972
    subst k
    rw [sourceRowsAt1972]
    exact rowSound1972 B hB hF
  · have he : k = (1973 : Fin 2425) := Fin.ext h1973
    subst k
    rw [sourceRowsAt1973]
    exact rowSound1973 B hB hF
  · have he : k = (1974 : Fin 2425) := Fin.ext h1974
    subst k
    rw [sourceRowsAt1974]
    exact rowSound1974 B hB hF
  · have he : k = (1975 : Fin 2425) := Fin.ext h1975
    subst k
    rw [sourceRowsAt1975]
    exact rowSound1975 B hB hF
  · have he : k = (1976 : Fin 2425) := Fin.ext h1976
    subst k
    rw [sourceRowsAt1976]
    exact rowSound1976 B hB hF
  · have he : k = (1977 : Fin 2425) := Fin.ext h1977
    subst k
    rw [sourceRowsAt1977]
    exact rowSound1977 B hB hF
  · have he : k = (1978 : Fin 2425) := Fin.ext h1978
    subst k
    rw [sourceRowsAt1978]
    exact rowSound1978 B hB hF
  · have he : k = (1979 : Fin 2425) := Fin.ext h1979
    subst k
    rw [sourceRowsAt1979]
    exact rowSound1979 B hB hF
  · have he : k = (1980 : Fin 2425) := Fin.ext h1980
    subst k
    rw [sourceRowsAt1980]
    exact rowSound1980 B hB hF
  · have he : k = (1981 : Fin 2425) := Fin.ext h1981
    subst k
    rw [sourceRowsAt1981]
    exact rowSound1981 B hB hF
  · have he : k = (1982 : Fin 2425) := Fin.ext h1982
    subst k
    rw [sourceRowsAt1982]
    exact rowSound1982 B hB hF
  · have he : k = (1983 : Fin 2425) := Fin.ext h1983
    subst k
    rw [sourceRowsAt1983]
    exact rowSound1983 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
