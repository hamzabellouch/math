import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources38

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1040 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1040 (mixedVector B) = 0 := by
  have h621 : mixedVector B (Sum.inr 621) = Sparse.eval nodeValue621 (mixedVector B) := by
    change mixedMoment B node621 node621Labels = _
    exact sound621 B hB hF
  have h940 : mixedVector B (Sum.inr 940) = Sparse.eval nodeValue940 (mixedVector B) := by
    change mixedMoment B node940 node940Labels = _
    exact sound940 B hB hF
  have h1092 : mixedVector B (Sum.inr 1092) = Sparse.eval nodeValue1092 (mixedVector B) := by
    change mixedMoment B node1092 node1092Labels = _
    exact sound1092 B hB hF
  have h1094 : mixedVector B (Sum.inr 1094) = Sparse.eval nodeValue1094 (mixedVector B) := by
    change mixedMoment B node1094 node1094Labels = _
    exact sound1094 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm1201, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h621, h940, h1092, h1094, h4085, reducedSource1040] using sourceEq1201 B hB

theorem rowSound1040 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1040 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1040, numericCheck1040, reducedZero1040 B hB hF, mul_zero]

theorem reducedZero1041 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1041 (mixedVector B) = 0 := by
  have h1093 : mixedVector B (Sum.inr 1093) = Sparse.eval nodeValue1093 (mixedVector B) := by
    change mixedMoment B node1093 node1093Labels = _
    exact sound1093 B hB hF
  have h1747 : mixedVector B (Sum.inr 1747) = Sparse.eval nodeValue1747 (mixedVector B) := by
    change mixedMoment B node1747 node1747Labels = _
    exact sound1747 B hB hF
  have h2064 : mixedVector B (Sum.inr 2064) = Sparse.eval nodeValue2064 (mixedVector B) := by
    change mixedMoment B node2064 node2064Labels = _
    exact sound2064 B hB hF
  have h2289 : mixedVector B (Sum.inr 2289) = Sparse.eval nodeValue2289 (mixedVector B) := by
    change mixedMoment B node2289 node2289Labels = _
    exact sound2289 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1202, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1093, h1747, h2064, h2289, h4070, reducedSource1041] using sourceEq1202 B hB

theorem rowSound1041 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1041 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1041, numericCheck1041, reducedZero1041 B hB hF, mul_zero]

theorem reducedZero1042 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1042 (mixedVector B) = 0 := by
  have h1745 : mixedVector B (Sum.inr 1745) = Sparse.eval nodeValue1745 (mixedVector B) := by
    change mixedMoment B node1745 node1745Labels = _
    exact sound1745 B hB hF
  have h1747 : mixedVector B (Sum.inr 1747) = Sparse.eval nodeValue1747 (mixedVector B) := by
    change mixedMoment B node1747 node1747Labels = _
    exact sound1747 B hB hF
  have h1756 : mixedVector B (Sum.inr 1756) = Sparse.eval nodeValue1756 (mixedVector B) := by
    change mixedMoment B node1756 node1756Labels = _
    exact sound1756 B hB hF
  have h2289 : mixedVector B (Sum.inr 2289) = Sparse.eval nodeValue2289 (mixedVector B) := by
    change mixedMoment B node2289 node2289Labels = _
    exact sound2289 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1203, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1745, h1747, h1756, h2289, h4070, reducedSource1042] using sourceEq1203 B hB

theorem rowSound1042 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1042 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1042, numericCheck1042, reducedZero1042 B hB hF, mul_zero]

theorem reducedZero1043 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1043 (mixedVector B) = 0 := by
  have h860 : mixedVector B (Sum.inr 860) = Sparse.eval nodeValue860 (mixedVector B) := by
    change mixedMoment B node860 node860Labels = _
    exact sound860 B hB hF
  have h1628 : mixedVector B (Sum.inr 1628) = Sparse.eval nodeValue1628 (mixedVector B) := by
    change mixedMoment B node1628 node1628Labels = _
    exact sound1628 B hB hF
  have h1747 : mixedVector B (Sum.inr 1747) = Sparse.eval nodeValue1747 (mixedVector B) := by
    change mixedMoment B node1747 node1747Labels = _
    exact sound1747 B hB hF
  have h1756 : mixedVector B (Sum.inr 1756) = Sparse.eval nodeValue1756 (mixedVector B) := by
    change mixedMoment B node1756 node1756Labels = _
    exact sound1756 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1204, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h860, h1628, h1747, h1756, h4070, reducedSource1043] using sourceEq1204 B hB

theorem rowSound1043 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1043 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1043, numericCheck1043, reducedZero1043 B hB hF, mul_zero]

theorem reducedZero1044 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1044 (mixedVector B) = 0 := by
  have h612 : mixedVector B (Sum.inr 612) = Sparse.eval nodeValue612 (mixedVector B) := by
    change mixedMoment B node612 node612Labels = _
    exact sound612 B hB hF
  have h931 : mixedVector B (Sum.inr 931) = Sparse.eval nodeValue931 (mixedVector B) := by
    change mixedMoment B node931 node931Labels = _
    exact sound931 B hB hF
  have h1047 : mixedVector B (Sum.inr 1047) = Sparse.eval nodeValue1047 (mixedVector B) := by
    change mixedMoment B node1047 node1047Labels = _
    exact sound1047 B hB hF
  have h1061 : mixedVector B (Sum.inr 1061) = Sparse.eval nodeValue1061 (mixedVector B) := by
    change mixedMoment B node1061 node1061Labels = _
    exact sound1061 B hB hF
  have h1087 : mixedVector B (Sum.inr 1087) = Sparse.eval nodeValue1087 (mixedVector B) := by
    change mixedMoment B node1087 node1087Labels = _
    exact sound1087 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1205, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h612, h931, h1047, h1061, h1087, h4084, reducedSource1044] using sourceEq1205 B hB

theorem rowSound1044 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1044 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1044, numericCheck1044, reducedZero1044 B hB hF, mul_zero]

theorem reducedZero1045 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1045 (mixedVector B) = 0 := by
  have h590 : mixedVector B (Sum.inr 590) = Sparse.eval nodeValue590 (mixedVector B) := by
    change mixedMoment B node590 node590Labels = _
    exact sound590 B hB hF
  have h914 : mixedVector B (Sum.inr 914) = Sparse.eval nodeValue914 (mixedVector B) := by
    change mixedMoment B node914 node914Labels = _
    exact sound914 B hB hF
  have h954 : mixedVector B (Sum.inr 954) = Sparse.eval nodeValue954 (mixedVector B) := by
    change mixedMoment B node954 node954Labels = _
    exact sound954 B hB hF
  have h1047 : mixedVector B (Sum.inr 1047) = Sparse.eval nodeValue1047 (mixedVector B) := by
    change mixedMoment B node1047 node1047Labels = _
    exact sound1047 B hB hF
  have h1049 : mixedVector B (Sum.inr 1049) = Sparse.eval nodeValue1049 (mixedVector B) := by
    change mixedMoment B node1049 node1049Labels = _
    exact sound1049 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1206, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h590, h914, h954, h1047, h1049, h4084, reducedSource1045] using sourceEq1206 B hB

theorem rowSound1045 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1045 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1045, numericCheck1045, reducedZero1045 B hB hF, mul_zero]

theorem reducedZero1046 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1046 (mixedVector B) = 0 := by
  have h951 : mixedVector B (Sum.inr 951) = Sparse.eval nodeValue951 (mixedVector B) := by
    change mixedMoment B node951 node951Labels = _
    exact sound951 B hB hF
  have h1336 : mixedVector B (Sum.inr 1336) = Sparse.eval nodeValue1336 (mixedVector B) := by
    change mixedMoment B node1336 node1336Labels = _
    exact sound1336 B hB hF
  have h1348 : mixedVector B (Sum.inr 1348) = Sparse.eval nodeValue1348 (mixedVector B) := by
    change mixedMoment B node1348 node1348Labels = _
    exact sound1348 B hB hF
  have h1408 : mixedVector B (Sum.inr 1408) = Sparse.eval nodeValue1408 (mixedVector B) := by
    change mixedMoment B node1408 node1408Labels = _
    exact sound1408 B hB hF
  have h2112 : mixedVector B (Sum.inr 2112) = Sparse.eval nodeValue2112 (mixedVector B) := by
    change mixedMoment B node2112 node2112Labels = _
    exact sound2112 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1207, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h951, h1336, h1348, h1408, h2112, h4083, reducedSource1046] using sourceEq1207 B hB

theorem rowSound1046 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1046 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1046, numericCheck1046, reducedZero1046 B hB hF, mul_zero]

theorem reducedZero1047 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1047 (mixedVector B) = 0 := by
  have h1072 : mixedVector B (Sum.inr 1072) = Sparse.eval nodeValue1072 (mixedVector B) := by
    change mixedMoment B node1072 node1072Labels = _
    exact sound1072 B hB hF
  have h1745 : mixedVector B (Sum.inr 1745) = Sparse.eval nodeValue1745 (mixedVector B) := by
    change mixedMoment B node1745 node1745Labels = _
    exact sound1745 B hB hF
  have h2045 : mixedVector B (Sum.inr 2045) = Sparse.eval nodeValue2045 (mixedVector B) := by
    change mixedMoment B node2045 node2045Labels = _
    exact sound2045 B hB hF
  have h2226 : mixedVector B (Sum.inr 2226) = Sparse.eval nodeValue2226 (mixedVector B) := by
    change mixedMoment B node2226 node2226Labels = _
    exact sound2226 B hB hF
  have h2289 : mixedVector B (Sum.inr 2289) = Sparse.eval nodeValue2289 (mixedVector B) := by
    change mixedMoment B node2289 node2289Labels = _
    exact sound2289 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1208, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1072, h1745, h2045, h2226, h2289, h4070, reducedSource1047] using sourceEq1208 B hB

theorem rowSound1047 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1047 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1047, numericCheck1047, reducedZero1047 B hB hF, mul_zero]

theorem reducedZero1048 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1048 (mixedVector B) = 0 := by
  have h1744 : mixedVector B (Sum.inr 1744) = Sparse.eval nodeValue1744 (mixedVector B) := by
    change mixedMoment B node1744 node1744Labels = _
    exact sound1744 B hB hF
  have h1745 : mixedVector B (Sum.inr 1745) = Sparse.eval nodeValue1745 (mixedVector B) := by
    change mixedMoment B node1745 node1745Labels = _
    exact sound1745 B hB hF
  have h1746 : mixedVector B (Sum.inr 1746) = Sparse.eval nodeValue1746 (mixedVector B) := by
    change mixedMoment B node1746 node1746Labels = _
    exact sound1746 B hB hF
  have h1750 : mixedVector B (Sum.inr 1750) = Sparse.eval nodeValue1750 (mixedVector B) := by
    change mixedMoment B node1750 node1750Labels = _
    exact sound1750 B hB hF
  have h2226 : mixedVector B (Sum.inr 2226) = Sparse.eval nodeValue2226 (mixedVector B) := by
    change mixedMoment B node2226 node2226Labels = _
    exact sound2226 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1210, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1744, h1745, h1746, h1750, h2226, h4070, reducedSource1048] using sourceEq1210 B hB

theorem rowSound1048 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1048 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1048, numericCheck1048, reducedZero1048 B hB hF, mul_zero]

theorem reducedZero1049 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1049 (mixedVector B) = 0 := by
  have h853 : mixedVector B (Sum.inr 853) = Sparse.eval nodeValue853 (mixedVector B) := by
    change mixedMoment B node853 node853Labels = _
    exact sound853 B hB hF
  have h1619 : mixedVector B (Sum.inr 1619) = Sparse.eval nodeValue1619 (mixedVector B) := by
    change mixedMoment B node1619 node1619Labels = _
    exact sound1619 B hB hF
  have h1745 : mixedVector B (Sum.inr 1745) = Sparse.eval nodeValue1745 (mixedVector B) := by
    change mixedMoment B node1745 node1745Labels = _
    exact sound1745 B hB hF
  have h1750 : mixedVector B (Sum.inr 1750) = Sparse.eval nodeValue1750 (mixedVector B) := by
    change mixedMoment B node1750 node1750Labels = _
    exact sound1750 B hB hF
  have h1756 : mixedVector B (Sum.inr 1756) = Sparse.eval nodeValue1756 (mixedVector B) := by
    change mixedMoment B node1756 node1756Labels = _
    exact sound1756 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1211, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h853, h1619, h1745, h1750, h1756, h4070, reducedSource1049] using sourceEq1211 B hB

theorem rowSound1049 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1049 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1049, numericCheck1049, reducedZero1049 B hB hF, mul_zero]

theorem reducedZero1050 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1050 (mixedVector B) = 0 := by
  have h606 : mixedVector B (Sum.inr 606) = Sparse.eval nodeValue606 (mixedVector B) := by
    change mixedMoment B node606 node606Labels = _
    exact sound606 B hB hF
  have h925 : mixedVector B (Sum.inr 925) = Sparse.eval nodeValue925 (mixedVector B) := by
    change mixedMoment B node925 node925Labels = _
    exact sound925 B hB hF
  have h1059 : mixedVector B (Sum.inr 1059) = Sparse.eval nodeValue1059 (mixedVector B) := by
    change mixedMoment B node1059 node1059Labels = _
    exact sound1059 B hB hF
  have h1083 : mixedVector B (Sum.inr 1083) = Sparse.eval nodeValue1083 (mixedVector B) := by
    change mixedMoment B node1083 node1083Labels = _
    exact sound1083 B hB hF
  have h1091 : mixedVector B (Sum.inr 1091) = Sparse.eval nodeValue1091 (mixedVector B) := by
    change mixedMoment B node1091 node1091Labels = _
    exact sound1091 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1212, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h606, h925, h1059, h1083, h1091, h4084, reducedSource1050] using sourceEq1212 B hB

theorem rowSound1050 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1050 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1050, numericCheck1050, reducedZero1050 B hB hF, mul_zero]

theorem reducedZero1051 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1051 (mixedVector B) = 0 := by
  have h1142 : mixedVector B (Sum.inr 1142) = Sparse.eval nodeValue1142 (mixedVector B) := by
    change mixedMoment B node1142 node1142Labels = _
    exact sound1142 B hB hF
  have h1317 : mixedVector B (Sum.inr 1317) = Sparse.eval nodeValue1317 (mixedVector B) := by
    change mixedMoment B node1317 node1317Labels = _
    exact sound1317 B hB hF
  have h1324 : mixedVector B (Sum.inr 1324) = Sparse.eval nodeValue1324 (mixedVector B) := by
    change mixedMoment B node1324 node1324Labels = _
    exact sound1324 B hB hF
  have h1372 : mixedVector B (Sum.inr 1372) = Sparse.eval nodeValue1372 (mixedVector B) := by
    change mixedMoment B node1372 node1372Labels = _
    exact sound1372 B hB hF
  have h2519 : mixedVector B (Sum.inr 2519) = Sparse.eval nodeValue2519 (mixedVector B) := by
    change mixedMoment B node2519 node2519Labels = _
    exact sound2519 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1213, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1142, h1317, h1324, h1372, h2519, h4092, reducedSource1051] using sourceEq1213 B hB

theorem rowSound1051 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1051 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1051, numericCheck1051, reducedZero1051 B hB hF, mul_zero]

theorem reducedZero1052 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1052 (mixedVector B) = 0 := by
  have h1729 : mixedVector B (Sum.inr 1729) = Sparse.eval nodeValue1729 (mixedVector B) := by
    change mixedMoment B node1729 node1729Labels = _
    exact sound1729 B hB hF
  have h1952 : mixedVector B (Sum.inr 1952) = Sparse.eval nodeValue1952 (mixedVector B) := by
    change mixedMoment B node1952 node1952Labels = _
    exact sound1952 B hB hF
  have h3242 : mixedVector B (Sum.inr 3242) = Sparse.eval nodeValue3242 (mixedVector B) := by
    change mixedMoment B node3242 node3242Labels = _
    exact sound3242 B hB hF
  have h3247 : mixedVector B (Sum.inr 3247) = Sparse.eval nodeValue3247 (mixedVector B) := by
    change mixedMoment B node3247 node3247Labels = _
    exact sound3247 B hB hF
  have h3300 : mixedVector B (Sum.inr 3300) = Sparse.eval nodeValue3300 (mixedVector B) := by
    change mixedMoment B node3300 node3300Labels = _
    exact sound3300 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1214, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1729, h1952, h3242, h3247, h3300, h4070, reducedSource1052] using sourceEq1214 B hB

theorem rowSound1052 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1052 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1052, numericCheck1052, reducedZero1052 B hB hF, mul_zero]

theorem reducedZero1053 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1053 (mixedVector B) = 0 := by
  have h808 : mixedVector B (Sum.inr 808) = Sparse.eval nodeValue808 (mixedVector B) := by
    change mixedMoment B node808 node808Labels = _
    exact sound808 B hB hF
  have h814 : mixedVector B (Sum.inr 814) = Sparse.eval nodeValue814 (mixedVector B) := by
    change mixedMoment B node814 node814Labels = _
    exact sound814 B hB hF
  have h815 : mixedVector B (Sum.inr 815) = Sparse.eval nodeValue815 (mixedVector B) := by
    change mixedMoment B node815 node815Labels = _
    exact sound815 B hB hF
  have h857 : mixedVector B (Sum.inr 857) = Sparse.eval nodeValue857 (mixedVector B) := by
    change mixedMoment B node857 node857Labels = _
    exact sound857 B hB hF
  have h1729 : mixedVector B (Sum.inr 1729) = Sparse.eval nodeValue1729 (mixedVector B) := by
    change mixedMoment B node1729 node1729Labels = _
    exact sound1729 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1215, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h808, h814, h815, h857, h1729, h4070, reducedSource1053] using sourceEq1215 B hB

theorem rowSound1053 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1053 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1053, numericCheck1053, reducedZero1053 B hB hF, mul_zero]

theorem reducedZero1054 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1054 (mixedVector B) = 0 := by
  have h1723 : mixedVector B (Sum.inr 1723) = Sparse.eval nodeValue1723 (mixedVector B) := by
    change mixedMoment B node1723 node1723Labels = _
    exact sound1723 B hB hF
  have h1725 : mixedVector B (Sum.inr 1725) = Sparse.eval nodeValue1725 (mixedVector B) := by
    change mixedMoment B node1725 node1725Labels = _
    exact sound1725 B hB hF
  have h1729 : mixedVector B (Sum.inr 1729) = Sparse.eval nodeValue1729 (mixedVector B) := by
    change mixedMoment B node1729 node1729Labels = _
    exact sound1729 B hB hF
  have h1750 : mixedVector B (Sum.inr 1750) = Sparse.eval nodeValue1750 (mixedVector B) := by
    change mixedMoment B node1750 node1750Labels = _
    exact sound1750 B hB hF
  have h3300 : mixedVector B (Sum.inr 3300) = Sparse.eval nodeValue3300 (mixedVector B) := by
    change mixedMoment B node3300 node3300Labels = _
    exact sound3300 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1216, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1723, h1725, h1729, h1750, h3300, h4070, reducedSource1054] using sourceEq1216 B hB

theorem rowSound1054 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1054 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1054, numericCheck1054, reducedZero1054 B hB hF, mul_zero]

theorem reducedZero1055 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1055 (mixedVector B) = 0 := by
  have h857 : mixedVector B (Sum.inr 857) = Sparse.eval nodeValue857 (mixedVector B) := by
    change mixedMoment B node857 node857Labels = _
    exact sound857 B hB hF
  have h1624 : mixedVector B (Sum.inr 1624) = Sparse.eval nodeValue1624 (mixedVector B) := by
    change mixedMoment B node1624 node1624Labels = _
    exact sound1624 B hB hF
  have h1729 : mixedVector B (Sum.inr 1729) = Sparse.eval nodeValue1729 (mixedVector B) := by
    change mixedMoment B node1729 node1729Labels = _
    exact sound1729 B hB hF
  have h1746 : mixedVector B (Sum.inr 1746) = Sparse.eval nodeValue1746 (mixedVector B) := by
    change mixedMoment B node1746 node1746Labels = _
    exact sound1746 B hB hF
  have h1750 : mixedVector B (Sum.inr 1750) = Sparse.eval nodeValue1750 (mixedVector B) := by
    change mixedMoment B node1750 node1750Labels = _
    exact sound1750 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1217, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h857, h1624, h1729, h1746, h1750, h4070, reducedSource1055] using sourceEq1217 B hB

theorem rowSound1055 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1055 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1055, numericCheck1055, reducedZero1055 B hB hF, mul_zero]

theorem sourceRowsAt1040 : MixedData.sourceRows (1040 : Fin 2425) =
    MixedData.row1040 := by decide +kernel

theorem sourceRowsAt1041 : MixedData.sourceRows (1041 : Fin 2425) =
    MixedData.row1041 := by decide +kernel

theorem sourceRowsAt1042 : MixedData.sourceRows (1042 : Fin 2425) =
    MixedData.row1042 := by decide +kernel

theorem sourceRowsAt1043 : MixedData.sourceRows (1043 : Fin 2425) =
    MixedData.row1043 := by decide +kernel

theorem sourceRowsAt1044 : MixedData.sourceRows (1044 : Fin 2425) =
    MixedData.row1044 := by decide +kernel

theorem sourceRowsAt1045 : MixedData.sourceRows (1045 : Fin 2425) =
    MixedData.row1045 := by decide +kernel

theorem sourceRowsAt1046 : MixedData.sourceRows (1046 : Fin 2425) =
    MixedData.row1046 := by decide +kernel

theorem sourceRowsAt1047 : MixedData.sourceRows (1047 : Fin 2425) =
    MixedData.row1047 := by decide +kernel

theorem sourceRowsAt1048 : MixedData.sourceRows (1048 : Fin 2425) =
    MixedData.row1048 := by decide +kernel

theorem sourceRowsAt1049 : MixedData.sourceRows (1049 : Fin 2425) =
    MixedData.row1049 := by decide +kernel

theorem sourceRowsAt1050 : MixedData.sourceRows (1050 : Fin 2425) =
    MixedData.row1050 := by decide +kernel

theorem sourceRowsAt1051 : MixedData.sourceRows (1051 : Fin 2425) =
    MixedData.row1051 := by decide +kernel

theorem sourceRowsAt1052 : MixedData.sourceRows (1052 : Fin 2425) =
    MixedData.row1052 := by decide +kernel

theorem sourceRowsAt1053 : MixedData.sourceRows (1053 : Fin 2425) =
    MixedData.row1053 := by decide +kernel

theorem sourceRowsAt1054 : MixedData.sourceRows (1054 : Fin 2425) =
    MixedData.row1054 := by decide +kernel

theorem sourceRowsAt1055 : MixedData.sourceRows (1055 : Fin 2425) =
    MixedData.row1055 := by decide +kernel

theorem chunkSound65 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 65) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1040 ∨ k.val = 1041 ∨ k.val = 1042 ∨ k.val = 1043 ∨ k.val = 1044 ∨ k.val = 1045 ∨ k.val = 1046 ∨ k.val = 1047 ∨ k.val = 1048 ∨ k.val = 1049 ∨ k.val = 1050 ∨ k.val = 1051 ∨ k.val = 1052 ∨ k.val = 1053 ∨ k.val = 1054 ∨ k.val = 1055 := by omega
  rcases heq with h1040 | h1041 | h1042 | h1043 | h1044 | h1045 | h1046 | h1047 | h1048 | h1049 | h1050 | h1051 | h1052 | h1053 | h1054 | h1055
  · have he : k = (1040 : Fin 2425) := Fin.ext h1040
    subst k
    rw [sourceRowsAt1040]
    exact rowSound1040 B hB hF
  · have he : k = (1041 : Fin 2425) := Fin.ext h1041
    subst k
    rw [sourceRowsAt1041]
    exact rowSound1041 B hB hF
  · have he : k = (1042 : Fin 2425) := Fin.ext h1042
    subst k
    rw [sourceRowsAt1042]
    exact rowSound1042 B hB hF
  · have he : k = (1043 : Fin 2425) := Fin.ext h1043
    subst k
    rw [sourceRowsAt1043]
    exact rowSound1043 B hB hF
  · have he : k = (1044 : Fin 2425) := Fin.ext h1044
    subst k
    rw [sourceRowsAt1044]
    exact rowSound1044 B hB hF
  · have he : k = (1045 : Fin 2425) := Fin.ext h1045
    subst k
    rw [sourceRowsAt1045]
    exact rowSound1045 B hB hF
  · have he : k = (1046 : Fin 2425) := Fin.ext h1046
    subst k
    rw [sourceRowsAt1046]
    exact rowSound1046 B hB hF
  · have he : k = (1047 : Fin 2425) := Fin.ext h1047
    subst k
    rw [sourceRowsAt1047]
    exact rowSound1047 B hB hF
  · have he : k = (1048 : Fin 2425) := Fin.ext h1048
    subst k
    rw [sourceRowsAt1048]
    exact rowSound1048 B hB hF
  · have he : k = (1049 : Fin 2425) := Fin.ext h1049
    subst k
    rw [sourceRowsAt1049]
    exact rowSound1049 B hB hF
  · have he : k = (1050 : Fin 2425) := Fin.ext h1050
    subst k
    rw [sourceRowsAt1050]
    exact rowSound1050 B hB hF
  · have he : k = (1051 : Fin 2425) := Fin.ext h1051
    subst k
    rw [sourceRowsAt1051]
    exact rowSound1051 B hB hF
  · have he : k = (1052 : Fin 2425) := Fin.ext h1052
    subst k
    rw [sourceRowsAt1052]
    exact rowSound1052 B hB hF
  · have he : k = (1053 : Fin 2425) := Fin.ext h1053
    subst k
    rw [sourceRowsAt1053]
    exact rowSound1053 B hB hF
  · have he : k = (1054 : Fin 2425) := Fin.ext h1054
    subst k
    rw [sourceRowsAt1054]
    exact rowSound1054 B hB hF
  · have he : k = (1055 : Fin 2425) := Fin.ext h1055
    subst k
    rw [sourceRowsAt1055]
    exact rowSound1055 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
