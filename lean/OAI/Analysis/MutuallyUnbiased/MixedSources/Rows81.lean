import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources47

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1296 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1296 (mixedVector B) = 0 := by
  have h582 : mixedVector B (Sum.inr 582) = Sparse.eval nodeValue582 (mixedVector B) := by
    change mixedMoment B node582 node582Labels = _
    exact sound582 B hB hF
  have h588 : mixedVector B (Sum.inr 588) = Sparse.eval nodeValue588 (mixedVector B) := by
    change mixedMoment B node588 node588Labels = _
    exact sound588 B hB hF
  have h590 : mixedVector B (Sum.inr 590) = Sparse.eval nodeValue590 (mixedVector B) := by
    change mixedMoment B node590 node590Labels = _
    exact sound590 B hB hF
  have h613 : mixedVector B (Sum.inr 613) = Sparse.eval nodeValue613 (mixedVector B) := by
    change mixedMoment B node613 node613Labels = _
    exact sound613 B hB hF
  have h1049 : mixedVector B (Sum.inr 1049) = Sparse.eval nodeValue1049 (mixedVector B) := by
    change mixedMoment B node1049 node1049Labels = _
    exact sound1049 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1513, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h582, h588, h590, h613, h1049, h4084, reducedSource1296] using sourceEq1513 B hB

theorem rowSound1296 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1296 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1296, numericCheck1296, reducedZero1296 B hB hF, mul_zero]

theorem reducedZero1297 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1297 (mixedVector B) = 0 := by
  have h613 : mixedVector B (Sum.inr 613) = Sparse.eval nodeValue613 (mixedVector B) := by
    change mixedMoment B node613 node613Labels = _
    exact sound613 B hB hF
  have h932 : mixedVector B (Sum.inr 932) = Sparse.eval nodeValue932 (mixedVector B) := by
    change mixedMoment B node932 node932Labels = _
    exact sound932 B hB hF
  have h1049 : mixedVector B (Sum.inr 1049) = Sparse.eval nodeValue1049 (mixedVector B) := by
    change mixedMoment B node1049 node1049Labels = _
    exact sound1049 B hB hF
  have h1082 : mixedVector B (Sum.inr 1082) = Sparse.eval nodeValue1082 (mixedVector B) := by
    change mixedMoment B node1082 node1082Labels = _
    exact sound1082 B hB hF
  have h1087 : mixedVector B (Sum.inr 1087) = Sparse.eval nodeValue1087 (mixedVector B) := by
    change mixedMoment B node1087 node1087Labels = _
    exact sound1087 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1514, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h613, h932, h1049, h1082, h1087, h4084, reducedSource1297] using sourceEq1514 B hB

theorem rowSound1297 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1297 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1297, numericCheck1297, reducedZero1297 B hB hF, mul_zero]

theorem reducedZero1298 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1298 (mixedVector B) = 0 := by
  have h946 : mixedVector B (Sum.inr 946) = Sparse.eval nodeValue946 (mixedVector B) := by
    change mixedMoment B node946 node946Labels = _
    exact sound946 B hB hF
  have h952 : mixedVector B (Sum.inr 952) = Sparse.eval nodeValue952 (mixedVector B) := by
    change mixedMoment B node952 node952Labels = _
    exact sound952 B hB hF
  have h954 : mixedVector B (Sum.inr 954) = Sparse.eval nodeValue954 (mixedVector B) := by
    change mixedMoment B node954 node954Labels = _
    exact sound954 B hB hF
  have h1049 : mixedVector B (Sum.inr 1049) = Sparse.eval nodeValue1049 (mixedVector B) := by
    change mixedMoment B node1049 node1049Labels = _
    exact sound1049 B hB hF
  have h2115 : mixedVector B (Sum.inr 2115) = Sparse.eval nodeValue2115 (mixedVector B) := by
    change mixedMoment B node2115 node2115Labels = _
    exact sound2115 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1515, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h946, h952, h954, h1049, h2115, h4084, reducedSource1298] using sourceEq1515 B hB

theorem rowSound1298 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1298 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1298, numericCheck1298, reducedZero1298 B hB hF, mul_zero]

theorem reducedZero1299 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1299 (mixedVector B) = 0 := by
  have h582 : mixedVector B (Sum.inr 582) = Sparse.eval nodeValue582 (mixedVector B) := by
    change mixedMoment B node582 node582Labels = _
    exact sound582 B hB hF
  have h906 : mixedVector B (Sum.inr 906) = Sparse.eval nodeValue906 (mixedVector B) := by
    change mixedMoment B node906 node906Labels = _
    exact sound906 B hB hF
  have h946 : mixedVector B (Sum.inr 946) = Sparse.eval nodeValue946 (mixedVector B) := by
    change mixedMoment B node946 node946Labels = _
    exact sound946 B hB hF
  have h1040 : mixedVector B (Sum.inr 1040) = Sparse.eval nodeValue1040 (mixedVector B) := by
    change mixedMoment B node1040 node1040Labels = _
    exact sound1040 B hB hF
  have h1042 : mixedVector B (Sum.inr 1042) = Sparse.eval nodeValue1042 (mixedVector B) := by
    change mixedMoment B node1042 node1042Labels = _
    exact sound1042 B hB hF
  have h1049 : mixedVector B (Sum.inr 1049) = Sparse.eval nodeValue1049 (mixedVector B) := by
    change mixedMoment B node1049 node1049Labels = _
    exact sound1049 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1516, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h582, h906, h946, h1040, h1042, h1049, h4084, reducedSource1299] using sourceEq1516 B hB

theorem rowSound1299 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1299 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1299, numericCheck1299, reducedZero1299 B hB hF, mul_zero]

theorem reducedZero1300 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1300 (mixedVector B) = 0 := by
  have h4106 : mixedVector B (Sum.inr 4106) = Sparse.eval nodeValue4106 (mixedVector B) := by
    change mixedMoment B node4106 node4106Labels = _
    exact sound4106 B hB hF
  have h4109 : mixedVector B (Sum.inr 4109) = Sparse.eval nodeValue4109 (mixedVector B) := by
    change mixedMoment B node4109 node4109Labels = _
    exact sound4109 B hB hF
  have h4111 : mixedVector B (Sum.inr 4111) = Sparse.eval nodeValue4111 (mixedVector B) := by
    change mixedMoment B node4111 node4111Labels = _
    exact sound4111 B hB hF
  have h4132 : mixedVector B (Sum.inr 4132) = Sparse.eval nodeValue4132 (mixedVector B) := by
    change mixedMoment B node4132 node4132Labels = _
    exact sound4132 B hB hF
  have h4291 : mixedVector B (Sum.inr 4291) = Sparse.eval nodeValue4291 (mixedVector B) := by
    change mixedMoment B node4291 node4291Labels = _
    exact sound4291 B hB hF
  have h4294 : mixedVector B (Sum.inr 4294) = Sparse.eval nodeValue4294 (mixedVector B) := by
    change mixedMoment B node4294 node4294Labels = _
    exact sound4294 B hB hF
  have h4296 : mixedVector B (Sum.inr 4296) = Sparse.eval nodeValue4296 (mixedVector B) := by
    change mixedMoment B node4296 node4296Labels = _
    exact sound4296 B hB hF
  have h4313 : mixedVector B (Sum.inr 4313) = Sparse.eval nodeValue4313 (mixedVector B) := by
    change mixedMoment B node4313 node4313Labels = _
    exact sound4313 B hB hF
  have h4354 : mixedVector B (Sum.inr 4354) = Sparse.eval nodeValue4354 (mixedVector B) := by
    change mixedMoment B node4354 node4354Labels = _
    exact sound4354 B hB hF
  have h4359 : mixedVector B (Sum.inr 4359) = Sparse.eval nodeValue4359 (mixedVector B) := by
    change mixedMoment B node4359 node4359Labels = _
    exact sound4359 B hB hF
  have h4361 : mixedVector B (Sum.inr 4361) = Sparse.eval nodeValue4361 (mixedVector B) := by
    change mixedMoment B node4361 node4361Labels = _
    exact sound4361 B hB hF
  have h4452 : mixedVector B (Sum.inr 4452) = Sparse.eval nodeValue4452 (mixedVector B) := by
    change mixedMoment B node4452 node4452Labels = _
    exact sound4452 B hB hF
  have h4454 : mixedVector B (Sum.inr 4454) = Sparse.eval nodeValue4454 (mixedVector B) := by
    change mixedMoment B node4454 node4454Labels = _
    exact sound4454 B hB hF
  have h4461 : mixedVector B (Sum.inr 4461) = Sparse.eval nodeValue4461 (mixedVector B) := by
    change mixedMoment B node4461 node4461Labels = _
    exact sound4461 B hB hF
  have h4463 : mixedVector B (Sum.inr 4463) = Sparse.eval nodeValue4463 (mixedVector B) := by
    change mixedMoment B node4463 node4463Labels = _
    exact sound4463 B hB hF
  have h4491 : mixedVector B (Sum.inr 4491) = Sparse.eval nodeValue4491 (mixedVector B) := by
    change mixedMoment B node4491 node4491Labels = _
    exact sound4491 B hB hF
  have h4503 : mixedVector B (Sum.inr 4503) = Sparse.eval nodeValue4503 (mixedVector B) := by
    change mixedMoment B node4503 node4503Labels = _
    exact sound4503 B hB hF
  have h5080 : mixedVector B (Sum.inr 5080) = Sparse.eval nodeValue5080 (mixedVector B) := by
    change mixedMoment B node5080 node5080Labels = _
    exact sound5080 B hB hF
  have h5176 : mixedVector B (Sum.inr 5176) = Sparse.eval nodeValue5176 (mixedVector B) := by
    change mixedMoment B node5176 node5176Labels = _
    exact sound5176 B hB hF
  have h5291 : mixedVector B (Sum.inr 5291) = Sparse.eval nodeValue5291 (mixedVector B) := by
    change mixedMoment B node5291 node5291Labels = _
    exact sound5291 B hB hF
  have h5294 : mixedVector B (Sum.inr 5294) = Sparse.eval nodeValue5294 (mixedVector B) := by
    change mixedMoment B node5294 node5294Labels = _
    exact sound5294 B hB hF
  simpa only [sourceForm1517, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4106, h4109, h4111, h4132, h4291, h4294, h4296, h4313, h4354, h4359, h4361, h4452, h4454, h4461, h4463, h4491, h4503, h5080, h5176, h5291, h5294, reducedSource1300] using sourceEq1517 B hB

theorem rowSound1300 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1300 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1300, numericCheck1300, reducedZero1300 B hB hF, mul_zero]

theorem reducedZero1301 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1301 (mixedVector B) = 0 := by
  have h543 : mixedVector B (Sum.inr 543) = Sparse.eval nodeValue543 (mixedVector B) := by
    change mixedMoment B node543 node543Labels = _
    exact sound543 B hB hF
  have h546 : mixedVector B (Sum.inr 546) = Sparse.eval nodeValue546 (mixedVector B) := by
    change mixedMoment B node546 node546Labels = _
    exact sound546 B hB hF
  have h548 : mixedVector B (Sum.inr 548) = Sparse.eval nodeValue548 (mixedVector B) := by
    change mixedMoment B node548 node548Labels = _
    exact sound548 B hB hF
  have h562 : mixedVector B (Sum.inr 562) = Sparse.eval nodeValue562 (mixedVector B) := by
    change mixedMoment B node562 node562Labels = _
    exact sound562 B hB hF
  have h869 : mixedVector B (Sum.inr 869) = Sparse.eval nodeValue869 (mixedVector B) := by
    change mixedMoment B node869 node869Labels = _
    exact sound869 B hB hF
  have h872 : mixedVector B (Sum.inr 872) = Sparse.eval nodeValue872 (mixedVector B) := by
    change mixedMoment B node872 node872Labels = _
    exact sound872 B hB hF
  have h874 : mixedVector B (Sum.inr 874) = Sparse.eval nodeValue874 (mixedVector B) := by
    change mixedMoment B node874 node874Labels = _
    exact sound874 B hB hF
  have h891 : mixedVector B (Sum.inr 891) = Sparse.eval nodeValue891 (mixedVector B) := by
    change mixedMoment B node891 node891Labels = _
    exact sound891 B hB hF
  have h932 : mixedVector B (Sum.inr 932) = Sparse.eval nodeValue932 (mixedVector B) := by
    change mixedMoment B node932 node932Labels = _
    exact sound932 B hB hF
  have h937 : mixedVector B (Sum.inr 937) = Sparse.eval nodeValue937 (mixedVector B) := by
    change mixedMoment B node937 node937Labels = _
    exact sound937 B hB hF
  have h939 : mixedVector B (Sum.inr 939) = Sparse.eval nodeValue939 (mixedVector B) := by
    change mixedMoment B node939 node939Labels = _
    exact sound939 B hB hF
  have h1035 : mixedVector B (Sum.inr 1035) = Sparse.eval nodeValue1035 (mixedVector B) := by
    change mixedMoment B node1035 node1035Labels = _
    exact sound1035 B hB hF
  have h1037 : mixedVector B (Sum.inr 1037) = Sparse.eval nodeValue1037 (mixedVector B) := by
    change mixedMoment B node1037 node1037Labels = _
    exact sound1037 B hB hF
  have h1044 : mixedVector B (Sum.inr 1044) = Sparse.eval nodeValue1044 (mixedVector B) := by
    change mixedMoment B node1044 node1044Labels = _
    exact sound1044 B hB hF
  have h1046 : mixedVector B (Sum.inr 1046) = Sparse.eval nodeValue1046 (mixedVector B) := by
    change mixedMoment B node1046 node1046Labels = _
    exact sound1046 B hB hF
  have h1075 : mixedVector B (Sum.inr 1075) = Sparse.eval nodeValue1075 (mixedVector B) := by
    change mixedMoment B node1075 node1075Labels = _
    exact sound1075 B hB hF
  have h1087 : mixedVector B (Sum.inr 1087) = Sparse.eval nodeValue1087 (mixedVector B) := by
    change mixedMoment B node1087 node1087Labels = _
    exact sound1087 B hB hF
  have h2488 : mixedVector B (Sum.inr 2488) = Sparse.eval nodeValue2488 (mixedVector B) := by
    change mixedMoment B node2488 node2488Labels = _
    exact sound2488 B hB hF
  have h2604 : mixedVector B (Sum.inr 2604) = Sparse.eval nodeValue2604 (mixedVector B) := by
    change mixedMoment B node2604 node2604Labels = _
    exact sound2604 B hB hF
  have h2765 : mixedVector B (Sum.inr 2765) = Sparse.eval nodeValue2765 (mixedVector B) := by
    change mixedMoment B node2765 node2765Labels = _
    exact sound2765 B hB hF
  have h2768 : mixedVector B (Sum.inr 2768) = Sparse.eval nodeValue2768 (mixedVector B) := by
    change mixedMoment B node2768 node2768Labels = _
    exact sound2768 B hB hF
  simpa only [sourceForm1518, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h543, h546, h548, h562, h869, h872, h874, h891, h932, h937, h939, h1035, h1037, h1044, h1046, h1075, h1087, h2488, h2604, h2765, h2768, reducedSource1301] using sourceEq1518 B hB

theorem rowSound1301 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1301 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1301, numericCheck1301, reducedZero1301 B hB hF, mul_zero]

theorem reducedZero1302 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1302 (mixedVector B) = 0 := by
  have h4155 : mixedVector B (Sum.inr 4155) = Sparse.eval nodeValue4155 (mixedVector B) := by
    change mixedMoment B node4155 node4155Labels = _
    exact sound4155 B hB hF
  have h4161 : mixedVector B (Sum.inr 4161) = Sparse.eval nodeValue4161 (mixedVector B) := by
    change mixedMoment B node4161 node4161Labels = _
    exact sound4161 B hB hF
  have h4186 : mixedVector B (Sum.inr 4186) = Sparse.eval nodeValue4186 (mixedVector B) := by
    change mixedMoment B node4186 node4186Labels = _
    exact sound4186 B hB hF
  have h4329 : mixedVector B (Sum.inr 4329) = Sparse.eval nodeValue4329 (mixedVector B) := by
    change mixedMoment B node4329 node4329Labels = _
    exact sound4329 B hB hF
  have h4335 : mixedVector B (Sum.inr 4335) = Sparse.eval nodeValue4335 (mixedVector B) := by
    change mixedMoment B node4335 node4335Labels = _
    exact sound4335 B hB hF
  have h4355 : mixedVector B (Sum.inr 4355) = Sparse.eval nodeValue4355 (mixedVector B) := by
    change mixedMoment B node4355 node4355Labels = _
    exact sound4355 B hB hF
  have h4369 : mixedVector B (Sum.inr 4369) = Sparse.eval nodeValue4369 (mixedVector B) := by
    change mixedMoment B node4369 node4369Labels = _
    exact sound4369 B hB hF
  have h4374 : mixedVector B (Sum.inr 4374) = Sparse.eval nodeValue4374 (mixedVector B) := by
    change mixedMoment B node4374 node4374Labels = _
    exact sound4374 B hB hF
  have h4458 : mixedVector B (Sum.inr 4458) = Sparse.eval nodeValue4458 (mixedVector B) := by
    change mixedMoment B node4458 node4458Labels = _
    exact sound4458 B hB hF
  have h4463 : mixedVector B (Sum.inr 4463) = Sparse.eval nodeValue4463 (mixedVector B) := by
    change mixedMoment B node4463 node4463Labels = _
    exact sound4463 B hB hF
  have h4502 : mixedVector B (Sum.inr 4502) = Sparse.eval nodeValue4502 (mixedVector B) := by
    change mixedMoment B node4502 node4502Labels = _
    exact sound4502 B hB hF
  have h4811 : mixedVector B (Sum.inr 4811) = Sparse.eval nodeValue4811 (mixedVector B) := by
    change mixedMoment B node4811 node4811Labels = _
    exact sound4811 B hB hF
  have h4875 : mixedVector B (Sum.inr 4875) = Sparse.eval nodeValue4875 (mixedVector B) := by
    change mixedMoment B node4875 node4875Labels = _
    exact sound4875 B hB hF
  have h4895 : mixedVector B (Sum.inr 4895) = Sparse.eval nodeValue4895 (mixedVector B) := by
    change mixedMoment B node4895 node4895Labels = _
    exact sound4895 B hB hF
  simpa only [sourceForm1522, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4155, h4161, h4186, h4329, h4335, h4355, h4369, h4374, h4458, h4463, h4502, h4811, h4875, h4895, reducedSource1302] using sourceEq1522 B hB

theorem rowSound1302 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1302 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1302, numericCheck1302, reducedZero1302 B hB hF, mul_zero]

theorem reducedZero1303 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1303 (mixedVector B) = 0 := by
  have h632 : mixedVector B (Sum.inr 632) = Sparse.eval nodeValue632 (mixedVector B) := by
    change mixedMoment B node632 node632Labels = _
    exact sound632 B hB hF
  have h635 : mixedVector B (Sum.inr 635) = Sparse.eval nodeValue635 (mixedVector B) := by
    change mixedMoment B node635 node635Labels = _
    exact sound635 B hB hF
  have h649 : mixedVector B (Sum.inr 649) = Sparse.eval nodeValue649 (mixedVector B) := by
    change mixedMoment B node649 node649Labels = _
    exact sound649 B hB hF
  have h1322 : mixedVector B (Sum.inr 1322) = Sparse.eval nodeValue1322 (mixedVector B) := by
    change mixedMoment B node1322 node1322Labels = _
    exact sound1322 B hB hF
  have h1324 : mixedVector B (Sum.inr 1324) = Sparse.eval nodeValue1324 (mixedVector B) := by
    change mixedMoment B node1324 node1324Labels = _
    exact sound1324 B hB hF
  have h1331 : mixedVector B (Sum.inr 1331) = Sparse.eval nodeValue1331 (mixedVector B) := by
    change mixedMoment B node1331 node1331Labels = _
    exact sound1331 B hB hF
  have h1333 : mixedVector B (Sum.inr 1333) = Sparse.eval nodeValue1333 (mixedVector B) := by
    change mixedMoment B node1333 node1333Labels = _
    exact sound1333 B hB hF
  have h1344 : mixedVector B (Sum.inr 1344) = Sparse.eval nodeValue1344 (mixedVector B) := by
    change mixedMoment B node1344 node1344Labels = _
    exact sound1344 B hB hF
  have h1411 : mixedVector B (Sum.inr 1411) = Sparse.eval nodeValue1411 (mixedVector B) := by
    change mixedMoment B node1411 node1411Labels = _
    exact sound1411 B hB hF
  have h1413 : mixedVector B (Sum.inr 1413) = Sparse.eval nodeValue1413 (mixedVector B) := by
    change mixedMoment B node1413 node1413Labels = _
    exact sound1413 B hB hF
  have h1447 : mixedVector B (Sum.inr 1447) = Sparse.eval nodeValue1447 (mixedVector B) := by
    change mixedMoment B node1447 node1447Labels = _
    exact sound1447 B hB hF
  have h3188 : mixedVector B (Sum.inr 3188) = Sparse.eval nodeValue3188 (mixedVector B) := by
    change mixedMoment B node3188 node3188Labels = _
    exact sound3188 B hB hF
  have h3207 : mixedVector B (Sum.inr 3207) = Sparse.eval nodeValue3207 (mixedVector B) := by
    change mixedMoment B node3207 node3207Labels = _
    exact sound3207 B hB hF
  have h3229 : mixedVector B (Sum.inr 3229) = Sparse.eval nodeValue3229 (mixedVector B) := by
    change mixedMoment B node3229 node3229Labels = _
    exact sound3229 B hB hF
  simpa only [sourceForm1523, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h632, h635, h649, h1322, h1324, h1331, h1333, h1344, h1411, h1413, h1447, h3188, h3207, h3229, reducedSource1303] using sourceEq1523 B hB

theorem rowSound1303 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1303 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1303, numericCheck1303, reducedZero1303 B hB hF, mul_zero]

theorem reducedZero1304 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1304 (mixedVector B) = 0 := by
  have h1515 : mixedVector B (Sum.inr 1515) = Sparse.eval nodeValue1515 (mixedVector B) := by
    change mixedMoment B node1515 node1515Labels = _
    exact sound1515 B hB hF
  have h1533 : mixedVector B (Sum.inr 1533) = Sparse.eval nodeValue1533 (mixedVector B) := by
    change mixedMoment B node1533 node1533Labels = _
    exact sound1533 B hB hF
  have h1536 : mixedVector B (Sum.inr 1536) = Sparse.eval nodeValue1536 (mixedVector B) := by
    change mixedMoment B node1536 node1536Labels = _
    exact sound1536 B hB hF
  have h1671 : mixedVector B (Sum.inr 1671) = Sparse.eval nodeValue1671 (mixedVector B) := by
    change mixedMoment B node1671 node1671Labels = _
    exact sound1671 B hB hF
  have h1689 : mixedVector B (Sum.inr 1689) = Sparse.eval nodeValue1689 (mixedVector B) := by
    change mixedMoment B node1689 node1689Labels = _
    exact sound1689 B hB hF
  have h1691 : mixedVector B (Sum.inr 1691) = Sparse.eval nodeValue1691 (mixedVector B) := by
    change mixedMoment B node1691 node1691Labels = _
    exact sound1691 B hB hF
  have h1721 : mixedVector B (Sum.inr 1721) = Sparse.eval nodeValue1721 (mixedVector B) := by
    change mixedMoment B node1721 node1721Labels = _
    exact sound1721 B hB hF
  have h1724 : mixedVector B (Sum.inr 1724) = Sparse.eval nodeValue1724 (mixedVector B) := by
    change mixedMoment B node1724 node1724Labels = _
    exact sound1724 B hB hF
  have h1748 : mixedVector B (Sum.inr 1748) = Sparse.eval nodeValue1748 (mixedVector B) := by
    change mixedMoment B node1748 node1748Labels = _
    exact sound1748 B hB hF
  have h1750 : mixedVector B (Sum.inr 1750) = Sparse.eval nodeValue1750 (mixedVector B) := by
    change mixedMoment B node1750 node1750Labels = _
    exact sound1750 B hB hF
  have h1753 : mixedVector B (Sum.inr 1753) = Sparse.eval nodeValue1753 (mixedVector B) := by
    change mixedMoment B node1753 node1753Labels = _
    exact sound1753 B hB hF
  have h2225 : mixedVector B (Sum.inr 2225) = Sparse.eval nodeValue2225 (mixedVector B) := by
    change mixedMoment B node2225 node2225Labels = _
    exact sound2225 B hB hF
  have h2288 : mixedVector B (Sum.inr 2288) = Sparse.eval nodeValue2288 (mixedVector B) := by
    change mixedMoment B node2288 node2288Labels = _
    exact sound2288 B hB hF
  have h2291 : mixedVector B (Sum.inr 2291) = Sparse.eval nodeValue2291 (mixedVector B) := by
    change mixedMoment B node2291 node2291Labels = _
    exact sound2291 B hB hF
  simpa only [sourceForm1524, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1515, h1533, h1536, h1671, h1689, h1691, h1721, h1724, h1748, h1750, h1753, h2225, h2288, h2291, reducedSource1304] using sourceEq1524 B hB

theorem rowSound1304 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1304 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1304, numericCheck1304, reducedZero1304 B hB hF, mul_zero]

theorem reducedZero1305 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1305 (mixedVector B) = 0 := by
  have h583 : mixedVector B (Sum.inr 583) = Sparse.eval nodeValue583 (mixedVector B) := by
    change mixedMoment B node583 node583Labels = _
    exact sound583 B hB hF
  have h589 : mixedVector B (Sum.inr 589) = Sparse.eval nodeValue589 (mixedVector B) := by
    change mixedMoment B node589 node589Labels = _
    exact sound589 B hB hF
  have h614 : mixedVector B (Sum.inr 614) = Sparse.eval nodeValue614 (mixedVector B) := by
    change mixedMoment B node614 node614Labels = _
    exact sound614 B hB hF
  have h1050 : mixedVector B (Sum.inr 1050) = Sparse.eval nodeValue1050 (mixedVector B) := by
    change mixedMoment B node1050 node1050Labels = _
    exact sound1050 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1525, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h583, h589, h614, h1050, h4083, reducedSource1305] using sourceEq1525 B hB

theorem rowSound1305 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1305 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1305, numericCheck1305, reducedZero1305 B hB hF, mul_zero]

theorem reducedZero1306 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1306 (mixedVector B) = 0 := by
  have h614 : mixedVector B (Sum.inr 614) = Sparse.eval nodeValue614 (mixedVector B) := by
    change mixedMoment B node614 node614Labels = _
    exact sound614 B hB hF
  have h933 : mixedVector B (Sum.inr 933) = Sparse.eval nodeValue933 (mixedVector B) := by
    change mixedMoment B node933 node933Labels = _
    exact sound933 B hB hF
  have h1050 : mixedVector B (Sum.inr 1050) = Sparse.eval nodeValue1050 (mixedVector B) := by
    change mixedMoment B node1050 node1050Labels = _
    exact sound1050 B hB hF
  have h1086 : mixedVector B (Sum.inr 1086) = Sparse.eval nodeValue1086 (mixedVector B) := by
    change mixedMoment B node1086 node1086Labels = _
    exact sound1086 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1526, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h614, h933, h1050, h1086, h4083, reducedSource1306] using sourceEq1526 B hB

theorem rowSound1306 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1306 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1306, numericCheck1306, reducedZero1306 B hB hF, mul_zero]

theorem reducedZero1307 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1307 (mixedVector B) = 0 := by
  have h947 : mixedVector B (Sum.inr 947) = Sparse.eval nodeValue947 (mixedVector B) := by
    change mixedMoment B node947 node947Labels = _
    exact sound947 B hB hF
  have h953 : mixedVector B (Sum.inr 953) = Sparse.eval nodeValue953 (mixedVector B) := by
    change mixedMoment B node953 node953Labels = _
    exact sound953 B hB hF
  have h1050 : mixedVector B (Sum.inr 1050) = Sparse.eval nodeValue1050 (mixedVector B) := by
    change mixedMoment B node1050 node1050Labels = _
    exact sound1050 B hB hF
  have h2116 : mixedVector B (Sum.inr 2116) = Sparse.eval nodeValue2116 (mixedVector B) := by
    change mixedMoment B node2116 node2116Labels = _
    exact sound2116 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1527, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h947, h953, h1050, h2116, h4083, reducedSource1307] using sourceEq1527 B hB

theorem rowSound1307 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1307 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1307, numericCheck1307, reducedZero1307 B hB hF, mul_zero]

theorem reducedZero1308 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1308 (mixedVector B) = 0 := by
  have h583 : mixedVector B (Sum.inr 583) = Sparse.eval nodeValue583 (mixedVector B) := by
    change mixedMoment B node583 node583Labels = _
    exact sound583 B hB hF
  have h907 : mixedVector B (Sum.inr 907) = Sparse.eval nodeValue907 (mixedVector B) := by
    change mixedMoment B node907 node907Labels = _
    exact sound907 B hB hF
  have h947 : mixedVector B (Sum.inr 947) = Sparse.eval nodeValue947 (mixedVector B) := by
    change mixedMoment B node947 node947Labels = _
    exact sound947 B hB hF
  have h1041 : mixedVector B (Sum.inr 1041) = Sparse.eval nodeValue1041 (mixedVector B) := by
    change mixedMoment B node1041 node1041Labels = _
    exact sound1041 B hB hF
  have h1050 : mixedVector B (Sum.inr 1050) = Sparse.eval nodeValue1050 (mixedVector B) := by
    change mixedMoment B node1050 node1050Labels = _
    exact sound1050 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1528, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h583, h907, h947, h1041, h1050, h4083, reducedSource1308] using sourceEq1528 B hB

theorem rowSound1308 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1308 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1308, numericCheck1308, reducedZero1308 B hB hF, mul_zero]

theorem reducedZero1309 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1309 (mixedVector B) = 0 := by
  have h4107 : mixedVector B (Sum.inr 4107) = Sparse.eval nodeValue4107 (mixedVector B) := by
    change mixedMoment B node4107 node4107Labels = _
    exact sound4107 B hB hF
  have h4110 : mixedVector B (Sum.inr 4110) = Sparse.eval nodeValue4110 (mixedVector B) := by
    change mixedMoment B node4110 node4110Labels = _
    exact sound4110 B hB hF
  have h4133 : mixedVector B (Sum.inr 4133) = Sparse.eval nodeValue4133 (mixedVector B) := by
    change mixedMoment B node4133 node4133Labels = _
    exact sound4133 B hB hF
  have h4292 : mixedVector B (Sum.inr 4292) = Sparse.eval nodeValue4292 (mixedVector B) := by
    change mixedMoment B node4292 node4292Labels = _
    exact sound4292 B hB hF
  have h4295 : mixedVector B (Sum.inr 4295) = Sparse.eval nodeValue4295 (mixedVector B) := by
    change mixedMoment B node4295 node4295Labels = _
    exact sound4295 B hB hF
  have h4314 : mixedVector B (Sum.inr 4314) = Sparse.eval nodeValue4314 (mixedVector B) := by
    change mixedMoment B node4314 node4314Labels = _
    exact sound4314 B hB hF
  have h4355 : mixedVector B (Sum.inr 4355) = Sparse.eval nodeValue4355 (mixedVector B) := by
    change mixedMoment B node4355 node4355Labels = _
    exact sound4355 B hB hF
  have h4360 : mixedVector B (Sum.inr 4360) = Sparse.eval nodeValue4360 (mixedVector B) := by
    change mixedMoment B node4360 node4360Labels = _
    exact sound4360 B hB hF
  have h4458 : mixedVector B (Sum.inr 4458) = Sparse.eval nodeValue4458 (mixedVector B) := by
    change mixedMoment B node4458 node4458Labels = _
    exact sound4458 B hB hF
  have h4460 : mixedVector B (Sum.inr 4460) = Sparse.eval nodeValue4460 (mixedVector B) := by
    change mixedMoment B node4460 node4460Labels = _
    exact sound4460 B hB hF
  have h4499 : mixedVector B (Sum.inr 4499) = Sparse.eval nodeValue4499 (mixedVector B) := by
    change mixedMoment B node4499 node4499Labels = _
    exact sound4499 B hB hF
  have h5081 : mixedVector B (Sum.inr 5081) = Sparse.eval nodeValue5081 (mixedVector B) := by
    change mixedMoment B node5081 node5081Labels = _
    exact sound5081 B hB hF
  have h5177 : mixedVector B (Sum.inr 5177) = Sparse.eval nodeValue5177 (mixedVector B) := by
    change mixedMoment B node5177 node5177Labels = _
    exact sound5177 B hB hF
  have h5293 : mixedVector B (Sum.inr 5293) = Sparse.eval nodeValue5293 (mixedVector B) := by
    change mixedMoment B node5293 node5293Labels = _
    exact sound5293 B hB hF
  simpa only [sourceForm1529, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4107, h4110, h4133, h4292, h4295, h4314, h4355, h4360, h4458, h4460, h4499, h5081, h5177, h5293, reducedSource1309] using sourceEq1529 B hB

theorem rowSound1309 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1309 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1309, numericCheck1309, reducedZero1309 B hB hF, mul_zero]

theorem reducedZero1310 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1310 (mixedVector B) = 0 := by
  have h4256 : mixedVector B (Sum.inr 4256) = Sparse.eval nodeValue4256 (mixedVector B) := by
    change mixedMoment B node4256 node4256Labels = _
    exact sound4256 B hB hF
  have h4273 : mixedVector B (Sum.inr 4273) = Sparse.eval nodeValue4273 (mixedVector B) := by
    change mixedMoment B node4273 node4273Labels = _
    exact sound4273 B hB hF
  have h4279 : mixedVector B (Sum.inr 4279) = Sparse.eval nodeValue4279 (mixedVector B) := by
    change mixedMoment B node4279 node4279Labels = _
    exact sound4279 B hB hF
  have h4393 : mixedVector B (Sum.inr 4393) = Sparse.eval nodeValue4393 (mixedVector B) := by
    change mixedMoment B node4393 node4393Labels = _
    exact sound4393 B hB hF
  have h4404 : mixedVector B (Sum.inr 4404) = Sparse.eval nodeValue4404 (mixedVector B) := by
    change mixedMoment B node4404 node4404Labels = _
    exact sound4404 B hB hF
  have h4412 : mixedVector B (Sum.inr 4412) = Sparse.eval nodeValue4412 (mixedVector B) := by
    change mixedMoment B node4412 node4412Labels = _
    exact sound4412 B hB hF
  have h4444 : mixedVector B (Sum.inr 4444) = Sparse.eval nodeValue4444 (mixedVector B) := by
    change mixedMoment B node4444 node4444Labels = _
    exact sound4444 B hB hF
  have h4466 : mixedVector B (Sum.inr 4466) = Sparse.eval nodeValue4466 (mixedVector B) := by
    change mixedMoment B node4466 node4466Labels = _
    exact sound4466 B hB hF
  have h4467 : mixedVector B (Sum.inr 4467) = Sparse.eval nodeValue4467 (mixedVector B) := by
    change mixedMoment B node4467 node4467Labels = _
    exact sound4467 B hB hF
  have h4480 : mixedVector B (Sum.inr 4480) = Sparse.eval nodeValue4480 (mixedVector B) := by
    change mixedMoment B node4480 node4480Labels = _
    exact sound4480 B hB hF
  have h4511 : mixedVector B (Sum.inr 4511) = Sparse.eval nodeValue4511 (mixedVector B) := by
    change mixedMoment B node4511 node4511Labels = _
    exact sound4511 B hB hF
  have h4593 : mixedVector B (Sum.inr 4593) = Sparse.eval nodeValue4593 (mixedVector B) := by
    change mixedMoment B node4593 node4593Labels = _
    exact sound4593 B hB hF
  have h4612 : mixedVector B (Sum.inr 4612) = Sparse.eval nodeValue4612 (mixedVector B) := by
    change mixedMoment B node4612 node4612Labels = _
    exact sound4612 B hB hF
  have h4628 : mixedVector B (Sum.inr 4628) = Sparse.eval nodeValue4628 (mixedVector B) := by
    change mixedMoment B node4628 node4628Labels = _
    exact sound4628 B hB hF
  simpa only [sourceForm1531, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4256, h4273, h4279, h4393, h4404, h4412, h4444, h4466, h4467, h4480, h4511, h4593, h4612, h4628, reducedSource1310] using sourceEq1531 B hB

theorem rowSound1310 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1310 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1310, numericCheck1310, reducedZero1310 B hB hF, mul_zero]

theorem reducedZero1311 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1311 (mixedVector B) = 0 := by
  have h790 : mixedVector B (Sum.inr 790) = Sparse.eval nodeValue790 (mixedVector B) := by
    change mixedMoment B node790 node790Labels = _
    exact sound790 B hB hF
  have h816 : mixedVector B (Sum.inr 816) = Sparse.eval nodeValue816 (mixedVector B) := by
    change mixedMoment B node816 node816Labels = _
    exact sound816 B hB hF
  have h831 : mixedVector B (Sum.inr 831) = Sparse.eval nodeValue831 (mixedVector B) := by
    change mixedMoment B node831 node831Labels = _
    exact sound831 B hB hF
  have h974 : mixedVector B (Sum.inr 974) = Sparse.eval nodeValue974 (mixedVector B) := by
    change mixedMoment B node974 node974Labels = _
    exact sound974 B hB hF
  have h985 : mixedVector B (Sum.inr 985) = Sparse.eval nodeValue985 (mixedVector B) := by
    change mixedMoment B node985 node985Labels = _
    exact sound985 B hB hF
  have h993 : mixedVector B (Sum.inr 993) = Sparse.eval nodeValue993 (mixedVector B) := by
    change mixedMoment B node993 node993Labels = _
    exact sound993 B hB hF
  have h1026 : mixedVector B (Sum.inr 1026) = Sparse.eval nodeValue1026 (mixedVector B) := by
    change mixedMoment B node1026 node1026Labels = _
    exact sound1026 B hB hF
  have h1049 : mixedVector B (Sum.inr 1049) = Sparse.eval nodeValue1049 (mixedVector B) := by
    change mixedMoment B node1049 node1049Labels = _
    exact sound1049 B hB hF
  have h1050 : mixedVector B (Sum.inr 1050) = Sparse.eval nodeValue1050 (mixedVector B) := by
    change mixedMoment B node1050 node1050Labels = _
    exact sound1050 B hB hF
  have h1063 : mixedVector B (Sum.inr 1063) = Sparse.eval nodeValue1063 (mixedVector B) := by
    change mixedMoment B node1063 node1063Labels = _
    exact sound1063 B hB hF
  have h1095 : mixedVector B (Sum.inr 1095) = Sparse.eval nodeValue1095 (mixedVector B) := by
    change mixedMoment B node1095 node1095Labels = _
    exact sound1095 B hB hF
  have h1220 : mixedVector B (Sum.inr 1220) = Sparse.eval nodeValue1220 (mixedVector B) := by
    change mixedMoment B node1220 node1220Labels = _
    exact sound1220 B hB hF
  have h1274 : mixedVector B (Sum.inr 1274) = Sparse.eval nodeValue1274 (mixedVector B) := by
    change mixedMoment B node1274 node1274Labels = _
    exact sound1274 B hB hF
  have h1312 : mixedVector B (Sum.inr 1312) = Sparse.eval nodeValue1312 (mixedVector B) := by
    change mixedMoment B node1312 node1312Labels = _
    exact sound1312 B hB hF
  simpa only [sourceForm1532, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h790, h816, h831, h974, h985, h993, h1026, h1049, h1050, h1063, h1095, h1220, h1274, h1312, reducedSource1311] using sourceEq1532 B hB

theorem rowSound1311 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1311 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1311, numericCheck1311, reducedZero1311 B hB hF, mul_zero]

theorem sourceRowsAt1296 : MixedData.sourceRows (1296 : Fin 2425) =
    MixedData.row1296 := by decide +kernel

theorem sourceRowsAt1297 : MixedData.sourceRows (1297 : Fin 2425) =
    MixedData.row1297 := by decide +kernel

theorem sourceRowsAt1298 : MixedData.sourceRows (1298 : Fin 2425) =
    MixedData.row1298 := by decide +kernel

theorem sourceRowsAt1299 : MixedData.sourceRows (1299 : Fin 2425) =
    MixedData.row1299 := by decide +kernel

theorem sourceRowsAt1300 : MixedData.sourceRows (1300 : Fin 2425) =
    MixedData.row1300 := by decide +kernel

theorem sourceRowsAt1301 : MixedData.sourceRows (1301 : Fin 2425) =
    MixedData.row1301 := by decide +kernel

theorem sourceRowsAt1302 : MixedData.sourceRows (1302 : Fin 2425) =
    MixedData.row1302 := by decide +kernel

theorem sourceRowsAt1303 : MixedData.sourceRows (1303 : Fin 2425) =
    MixedData.row1303 := by decide +kernel

theorem sourceRowsAt1304 : MixedData.sourceRows (1304 : Fin 2425) =
    MixedData.row1304 := by decide +kernel

theorem sourceRowsAt1305 : MixedData.sourceRows (1305 : Fin 2425) =
    MixedData.row1305 := by decide +kernel

theorem sourceRowsAt1306 : MixedData.sourceRows (1306 : Fin 2425) =
    MixedData.row1306 := by decide +kernel

theorem sourceRowsAt1307 : MixedData.sourceRows (1307 : Fin 2425) =
    MixedData.row1307 := by decide +kernel

theorem sourceRowsAt1308 : MixedData.sourceRows (1308 : Fin 2425) =
    MixedData.row1308 := by decide +kernel

theorem sourceRowsAt1309 : MixedData.sourceRows (1309 : Fin 2425) =
    MixedData.row1309 := by decide +kernel

theorem sourceRowsAt1310 : MixedData.sourceRows (1310 : Fin 2425) =
    MixedData.row1310 := by decide +kernel

theorem sourceRowsAt1311 : MixedData.sourceRows (1311 : Fin 2425) =
    MixedData.row1311 := by decide +kernel

theorem chunkSound81 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 81) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1296 ∨ k.val = 1297 ∨ k.val = 1298 ∨ k.val = 1299 ∨ k.val = 1300 ∨ k.val = 1301 ∨ k.val = 1302 ∨ k.val = 1303 ∨ k.val = 1304 ∨ k.val = 1305 ∨ k.val = 1306 ∨ k.val = 1307 ∨ k.val = 1308 ∨ k.val = 1309 ∨ k.val = 1310 ∨ k.val = 1311 := by omega
  rcases heq with h1296 | h1297 | h1298 | h1299 | h1300 | h1301 | h1302 | h1303 | h1304 | h1305 | h1306 | h1307 | h1308 | h1309 | h1310 | h1311
  · have he : k = (1296 : Fin 2425) := Fin.ext h1296
    subst k
    rw [sourceRowsAt1296]
    exact rowSound1296 B hB hF
  · have he : k = (1297 : Fin 2425) := Fin.ext h1297
    subst k
    rw [sourceRowsAt1297]
    exact rowSound1297 B hB hF
  · have he : k = (1298 : Fin 2425) := Fin.ext h1298
    subst k
    rw [sourceRowsAt1298]
    exact rowSound1298 B hB hF
  · have he : k = (1299 : Fin 2425) := Fin.ext h1299
    subst k
    rw [sourceRowsAt1299]
    exact rowSound1299 B hB hF
  · have he : k = (1300 : Fin 2425) := Fin.ext h1300
    subst k
    rw [sourceRowsAt1300]
    exact rowSound1300 B hB hF
  · have he : k = (1301 : Fin 2425) := Fin.ext h1301
    subst k
    rw [sourceRowsAt1301]
    exact rowSound1301 B hB hF
  · have he : k = (1302 : Fin 2425) := Fin.ext h1302
    subst k
    rw [sourceRowsAt1302]
    exact rowSound1302 B hB hF
  · have he : k = (1303 : Fin 2425) := Fin.ext h1303
    subst k
    rw [sourceRowsAt1303]
    exact rowSound1303 B hB hF
  · have he : k = (1304 : Fin 2425) := Fin.ext h1304
    subst k
    rw [sourceRowsAt1304]
    exact rowSound1304 B hB hF
  · have he : k = (1305 : Fin 2425) := Fin.ext h1305
    subst k
    rw [sourceRowsAt1305]
    exact rowSound1305 B hB hF
  · have he : k = (1306 : Fin 2425) := Fin.ext h1306
    subst k
    rw [sourceRowsAt1306]
    exact rowSound1306 B hB hF
  · have he : k = (1307 : Fin 2425) := Fin.ext h1307
    subst k
    rw [sourceRowsAt1307]
    exact rowSound1307 B hB hF
  · have he : k = (1308 : Fin 2425) := Fin.ext h1308
    subst k
    rw [sourceRowsAt1308]
    exact rowSound1308 B hB hF
  · have he : k = (1309 : Fin 2425) := Fin.ext h1309
    subst k
    rw [sourceRowsAt1309]
    exact rowSound1309 B hB hF
  · have he : k = (1310 : Fin 2425) := Fin.ext h1310
    subst k
    rw [sourceRowsAt1310]
    exact rowSound1310 B hB hF
  · have he : k = (1311 : Fin 2425) := Fin.ext h1311
    subst k
    rw [sourceRowsAt1311]
    exact rowSound1311 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
