import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources38

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1056 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1056 (mixedVector B) = 0 := by
  have h815 : mixedVector B (Sum.inr 815) = Sparse.eval nodeValue815 (mixedVector B) := by
    change mixedMoment B node815 node815Labels = _
    exact sound815 B hB hF
  have h1604 : mixedVector B (Sum.inr 1604) = Sparse.eval nodeValue1604 (mixedVector B) := by
    change mixedMoment B node1604 node1604Labels = _
    exact sound1604 B hB hF
  have h1652 : mixedVector B (Sum.inr 1652) = Sparse.eval nodeValue1652 (mixedVector B) := by
    change mixedMoment B node1652 node1652Labels = _
    exact sound1652 B hB hF
  have h1725 : mixedVector B (Sum.inr 1725) = Sparse.eval nodeValue1725 (mixedVector B) := by
    change mixedMoment B node1725 node1725Labels = _
    exact sound1725 B hB hF
  have h1729 : mixedVector B (Sum.inr 1729) = Sparse.eval nodeValue1729 (mixedVector B) := by
    change mixedMoment B node1729 node1729Labels = _
    exact sound1729 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1218, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h815, h1604, h1652, h1725, h1729, h4070, reducedSource1056] using sourceEq1218 B hB

theorem rowSound1056 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1056 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1056, numericCheck1056, reducedZero1056 B hB hF, mul_zero]

theorem reducedZero1057 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1057 (mixedVector B) = 0 := by
  have h936 : mixedVector B (Sum.inr 936) = Sparse.eval nodeValue936 (mixedVector B) := by
    change mixedMoment B node936 node936Labels = _
    exact sound936 B hB hF
  have h1315 : mixedVector B (Sum.inr 1315) = Sparse.eval nodeValue1315 (mixedVector B) := by
    change mixedMoment B node1315 node1315Labels = _
    exact sound1315 B hB hF
  have h1323 : mixedVector B (Sum.inr 1323) = Sparse.eval nodeValue1323 (mixedVector B) := by
    change mixedMoment B node1323 node1323Labels = _
    exact sound1323 B hB hF
  have h1369 : mixedVector B (Sum.inr 1369) = Sparse.eval nodeValue1369 (mixedVector B) := by
    change mixedMoment B node1369 node1369Labels = _
    exact sound1369 B hB hF
  have h2062 : mixedVector B (Sum.inr 2062) = Sparse.eval nodeValue2062 (mixedVector B) := by
    change mixedMoment B node2062 node2062Labels = _
    exact sound2062 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1220, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h936, h1315, h1323, h1369, h2062, h4084, reducedSource1057] using sourceEq1220 B hB

theorem rowSound1057 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1057 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1057, numericCheck1057, reducedZero1057 B hB hF, mul_zero]

theorem reducedZero1058 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1058 (mixedVector B) = 0 := by
  have h1011 : mixedVector B (Sum.inr 1011) = Sparse.eval nodeValue1011 (mixedVector B) := by
    change mixedMoment B node1011 node1011Labels = _
    exact sound1011 B hB hF
  have h1746 : mixedVector B (Sum.inr 1746) = Sparse.eval nodeValue1746 (mixedVector B) := by
    change mixedMoment B node1746 node1746Labels = _
    exact sound1746 B hB hF
  have h1952 : mixedVector B (Sum.inr 1952) = Sparse.eval nodeValue1952 (mixedVector B) := by
    change mixedMoment B node1952 node1952Labels = _
    exact sound1952 B hB hF
  have h2005 : mixedVector B (Sum.inr 2005) = Sparse.eval nodeValue2005 (mixedVector B) := by
    change mixedMoment B node2005 node2005Labels = _
    exact sound2005 B hB hF
  have h2226 : mixedVector B (Sum.inr 2226) = Sparse.eval nodeValue2226 (mixedVector B) := by
    change mixedMoment B node2226 node2226Labels = _
    exact sound2226 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1221, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1011, h1746, h1952, h2005, h2226, h4070, reducedSource1058] using sourceEq1221 B hB

theorem rowSound1058 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1058 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1058, numericCheck1058, reducedZero1058 B hB hF, mul_zero]

theorem reducedZero1059 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1059 (mixedVector B) = 0 := by
  have h581 : mixedVector B (Sum.inr 581) = Sparse.eval nodeValue581 (mixedVector B) := by
    change mixedMoment B node581 node581Labels = _
    exact sound581 B hB hF
  have h905 : mixedVector B (Sum.inr 905) = Sparse.eval nodeValue905 (mixedVector B) := by
    change mixedMoment B node905 node905Labels = _
    exact sound905 B hB hF
  have h945 : mixedVector B (Sum.inr 945) = Sparse.eval nodeValue945 (mixedVector B) := by
    change mixedMoment B node945 node945Labels = _
    exact sound945 B hB hF
  have h1022 : mixedVector B (Sum.inr 1022) = Sparse.eval nodeValue1022 (mixedVector B) := by
    change mixedMoment B node1022 node1022Labels = _
    exact sound1022 B hB hF
  have h1041 : mixedVector B (Sum.inr 1041) = Sparse.eval nodeValue1041 (mixedVector B) := by
    change mixedMoment B node1041 node1041Labels = _
    exact sound1041 B hB hF
  have h1046 : mixedVector B (Sum.inr 1046) = Sparse.eval nodeValue1046 (mixedVector B) := by
    change mixedMoment B node1046 node1046Labels = _
    exact sound1046 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1224, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h581, h905, h945, h1022, h1041, h1046, h4083, reducedSource1059] using sourceEq1224 B hB

theorem rowSound1059 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1059 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1059, numericCheck1059, reducedZero1059 B hB hF, mul_zero]

theorem reducedZero1060 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1060 (mixedVector B) = 0 := by
  have h1118 : mixedVector B (Sum.inr 1118) = Sparse.eval nodeValue1118 (mixedVector B) := by
    change mixedMoment B node1118 node1118Labels = _
    exact sound1118 B hB hF
  have h1327 : mixedVector B (Sum.inr 1327) = Sparse.eval nodeValue1327 (mixedVector B) := by
    change mixedMoment B node1327 node1327Labels = _
    exact sound1327 B hB hF
  have h1333 : mixedVector B (Sum.inr 1333) = Sparse.eval nodeValue1333 (mixedVector B) := by
    change mixedMoment B node1333 node1333Labels = _
    exact sound1333 B hB hF
  have h1337 : mixedVector B (Sum.inr 1337) = Sparse.eval nodeValue1337 (mixedVector B) := by
    change mixedMoment B node1337 node1337Labels = _
    exact sound1337 B hB hF
  have h1388 : mixedVector B (Sum.inr 1388) = Sparse.eval nodeValue1388 (mixedVector B) := by
    change mixedMoment B node1388 node1388Labels = _
    exact sound1388 B hB hF
  have h2485 : mixedVector B (Sum.inr 2485) = Sparse.eval nodeValue2485 (mixedVector B) := by
    change mixedMoment B node2485 node2485Labels = _
    exact sound2485 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1225, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1118, h1327, h1333, h1337, h1388, h2485, h4091, reducedSource1060] using sourceEq1225 B hB

theorem rowSound1060 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1060 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1060, numericCheck1060, reducedZero1060 B hB hF, mul_zero]

theorem reducedZero1061 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1061 (mixedVector B) = 0 := by
  have h1723 : mixedVector B (Sum.inr 1723) = Sparse.eval nodeValue1723 (mixedVector B) := by
    change mixedMoment B node1723 node1723Labels = _
    exact sound1723 B hB hF
  have h1942 : mixedVector B (Sum.inr 1942) = Sparse.eval nodeValue1942 (mixedVector B) := by
    change mixedMoment B node1942 node1942Labels = _
    exact sound1942 B hB hF
  have h3279 : mixedVector B (Sum.inr 3279) = Sparse.eval nodeValue3279 (mixedVector B) := by
    change mixedMoment B node3279 node3279Labels = _
    exact sound3279 B hB hF
  have h3283 : mixedVector B (Sum.inr 3283) = Sparse.eval nodeValue3283 (mixedVector B) := by
    change mixedMoment B node3283 node3283Labels = _
    exact sound3283 B hB hF
  have h3300 : mixedVector B (Sum.inr 3300) = Sparse.eval nodeValue3300 (mixedVector B) := by
    change mixedMoment B node3300 node3300Labels = _
    exact sound3300 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1226, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1723, h1942, h3279, h3283, h3300, h4070, reducedSource1061] using sourceEq1226 B hB

theorem rowSound1061 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1061 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1061, numericCheck1061, reducedZero1061 B hB hF, mul_zero]

theorem reducedZero1062 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1062 (mixedVector B) = 0 := by
  have h847 : mixedVector B (Sum.inr 847) = Sparse.eval nodeValue847 (mixedVector B) := by
    change mixedMoment B node847 node847Labels = _
    exact sound847 B hB hF
  have h1613 : mixedVector B (Sum.inr 1613) = Sparse.eval nodeValue1613 (mixedVector B) := by
    change mixedMoment B node1613 node1613Labels = _
    exact sound1613 B hB hF
  have h1723 : mixedVector B (Sum.inr 1723) = Sparse.eval nodeValue1723 (mixedVector B) := by
    change mixedMoment B node1723 node1723Labels = _
    exact sound1723 B hB hF
  have h1744 : mixedVector B (Sum.inr 1744) = Sparse.eval nodeValue1744 (mixedVector B) := by
    change mixedMoment B node1744 node1744Labels = _
    exact sound1744 B hB hF
  have h1750 : mixedVector B (Sum.inr 1750) = Sparse.eval nodeValue1750 (mixedVector B) := by
    change mixedMoment B node1750 node1750Labels = _
    exact sound1750 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1228, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h847, h1613, h1723, h1744, h1750, h4070, reducedSource1062] using sourceEq1228 B hB

theorem rowSound1062 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1062 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1062, numericCheck1062, reducedZero1062 B hB hF, mul_zero]

theorem reducedZero1063 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1063 (mixedVector B) = 0 := by
  have h804 : mixedVector B (Sum.inr 804) = Sparse.eval nodeValue804 (mixedVector B) := by
    change mixedMoment B node804 node804Labels = _
    exact sound804 B hB hF
  have h1596 : mixedVector B (Sum.inr 1596) = Sparse.eval nodeValue1596 (mixedVector B) := by
    change mixedMoment B node1596 node1596Labels = _
    exact sound1596 B hB hF
  have h1643 : mixedVector B (Sum.inr 1643) = Sparse.eval nodeValue1643 (mixedVector B) := by
    change mixedMoment B node1643 node1643Labels = _
    exact sound1643 B hB hF
  have h1723 : mixedVector B (Sum.inr 1723) = Sparse.eval nodeValue1723 (mixedVector B) := by
    change mixedMoment B node1723 node1723Labels = _
    exact sound1723 B hB hF
  have h1725 : mixedVector B (Sum.inr 1725) = Sparse.eval nodeValue1725 (mixedVector B) := by
    change mixedMoment B node1725 node1725Labels = _
    exact sound1725 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1229, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h804, h1596, h1643, h1723, h1725, h4070, reducedSource1063] using sourceEq1229 B hB

theorem rowSound1063 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1063 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1063, numericCheck1063, reducedZero1063 B hB hF, mul_zero]

theorem reducedZero1064 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1064 (mixedVector B) = 0 := by
  have h585 : mixedVector B (Sum.inr 585) = Sparse.eval nodeValue585 (mixedVector B) := by
    change mixedMoment B node585 node585Labels = _
    exact sound585 B hB hF
  have h909 : mixedVector B (Sum.inr 909) = Sparse.eval nodeValue909 (mixedVector B) := by
    change mixedMoment B node909 node909Labels = _
    exact sound909 B hB hF
  have h949 : mixedVector B (Sum.inr 949) = Sparse.eval nodeValue949 (mixedVector B) := by
    change mixedMoment B node949 node949Labels = _
    exact sound949 B hB hF
  have h1024 : mixedVector B (Sum.inr 1024) = Sparse.eval nodeValue1024 (mixedVector B) := by
    change mixedMoment B node1024 node1024Labels = _
    exact sound1024 B hB hF
  have h1044 : mixedVector B (Sum.inr 1044) = Sparse.eval nodeValue1044 (mixedVector B) := by
    change mixedMoment B node1044 node1044Labels = _
    exact sound1044 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1231, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h585, h909, h949, h1024, h1044, h4083, reducedSource1064] using sourceEq1231 B hB

theorem rowSound1064 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1064 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1064, numericCheck1064, reducedZero1064 B hB hF, mul_zero]

theorem reducedZero1065 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1065 (mixedVector B) = 0 := by
  have h911 : mixedVector B (Sum.inr 911) = Sparse.eval nodeValue911 (mixedVector B) := by
    change mixedMoment B node911 node911Labels = _
    exact sound911 B hB hF
  have h1326 : mixedVector B (Sum.inr 1326) = Sparse.eval nodeValue1326 (mixedVector B) := by
    change mixedMoment B node1326 node1326Labels = _
    exact sound1326 B hB hF
  have h1332 : mixedVector B (Sum.inr 1332) = Sparse.eval nodeValue1332 (mixedVector B) := by
    change mixedMoment B node1332 node1332Labels = _
    exact sound1332 B hB hF
  have h1336 : mixedVector B (Sum.inr 1336) = Sparse.eval nodeValue1336 (mixedVector B) := by
    change mixedMoment B node1336 node1336Labels = _
    exact sound1336 B hB hF
  have h1385 : mixedVector B (Sum.inr 1385) = Sparse.eval nodeValue1385 (mixedVector B) := by
    change mixedMoment B node1385 node1385Labels = _
    exact sound1385 B hB hF
  have h2025 : mixedVector B (Sum.inr 2025) = Sparse.eval nodeValue2025 (mixedVector B) := by
    change mixedMoment B node2025 node2025Labels = _
    exact sound2025 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1232, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h911, h1326, h1332, h1336, h1385, h2025, h4083, reducedSource1065] using sourceEq1232 B hB

theorem rowSound1065 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1065 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1065, numericCheck1065, reducedZero1065 B hB hF, mul_zero]

theorem reducedZero1066 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1066 (mixedVector B) = 0 := by
  have h997 : mixedVector B (Sum.inr 997) = Sparse.eval nodeValue997 (mixedVector B) := by
    change mixedMoment B node997 node997Labels = _
    exact sound997 B hB hF
  have h1744 : mixedVector B (Sum.inr 1744) = Sparse.eval nodeValue1744 (mixedVector B) := by
    change mixedMoment B node1744 node1744Labels = _
    exact sound1744 B hB hF
  have h1942 : mixedVector B (Sum.inr 1942) = Sparse.eval nodeValue1942 (mixedVector B) := by
    change mixedMoment B node1942 node1942Labels = _
    exact sound1942 B hB hF
  have h1995 : mixedVector B (Sum.inr 1995) = Sparse.eval nodeValue1995 (mixedVector B) := by
    change mixedMoment B node1995 node1995Labels = _
    exact sound1995 B hB hF
  have h2226 : mixedVector B (Sum.inr 2226) = Sparse.eval nodeValue2226 (mixedVector B) := by
    change mixedMoment B node2226 node2226Labels = _
    exact sound2226 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1233, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h997, h1744, h1942, h1995, h2226, h4070, reducedSource1066] using sourceEq1233 B hB

theorem rowSound1066 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1066 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1066, numericCheck1066, reducedZero1066 B hB hF, mul_zero]

theorem reducedZero1067 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1067 (mixedVector B) = 0 := by
  have h1355 : mixedVector B (Sum.inr 1355) = Sparse.eval nodeValue1355 (mixedVector B) := by
    change mixedMoment B node1355 node1355Labels = _
    exact sound1355 B hB hF
  have h1902 : mixedVector B (Sum.inr 1902) = Sparse.eval nodeValue1902 (mixedVector B) := by
    change mixedMoment B node1902 node1902Labels = _
    exact sound1902 B hB hF
  have h1915 : mixedVector B (Sum.inr 1915) = Sparse.eval nodeValue1915 (mixedVector B) := by
    change mixedMoment B node1915 node1915Labels = _
    exact sound1915 B hB hF
  have h1926 : mixedVector B (Sum.inr 1926) = Sparse.eval nodeValue1926 (mixedVector B) := by
    change mixedMoment B node1926 node1926Labels = _
    exact sound1926 B hB hF
  have h2197 : mixedVector B (Sum.inr 2197) = Sparse.eval nodeValue2197 (mixedVector B) := by
    change mixedMoment B node2197 node2197Labels = _
    exact sound2197 B hB hF
  have h3024 : mixedVector B (Sum.inr 3024) = Sparse.eval nodeValue3024 (mixedVector B) := by
    change mixedMoment B node3024 node3024Labels = _
    exact sound3024 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1235, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1355, h1902, h1915, h1926, h2197, h3024, h4080, reducedSource1067] using sourceEq1235 B hB

theorem rowSound1067 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1067 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1067, numericCheck1067, reducedZero1067 B hB hF, mul_zero]

theorem reducedZero1068 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1068 (mixedVector B) = 0 := by
  have h1132 : mixedVector B (Sum.inr 1132) = Sparse.eval nodeValue1132 (mixedVector B) := by
    change mixedMoment B node1132 node1132Labels = _
    exact sound1132 B hB hF
  have h1142 : mixedVector B (Sum.inr 1142) = Sparse.eval nodeValue1142 (mixedVector B) := by
    change mixedMoment B node1142 node1142Labels = _
    exact sound1142 B hB hF
  have h1145 : mixedVector B (Sum.inr 1145) = Sparse.eval nodeValue1145 (mixedVector B) := by
    change mixedMoment B node1145 node1145Labels = _
    exact sound1145 B hB hF
  have h1243 : mixedVector B (Sum.inr 1243) = Sparse.eval nodeValue1243 (mixedVector B) := by
    change mixedMoment B node1243 node1243Labels = _
    exact sound1243 B hB hF
  have h2519 : mixedVector B (Sum.inr 2519) = Sparse.eval nodeValue2519 (mixedVector B) := by
    change mixedMoment B node2519 node2519Labels = _
    exact sound2519 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1237, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1132, h1142, h1145, h1243, h2519, h4092, reducedSource1068] using sourceEq1237 B hB

theorem rowSound1068 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1068 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1068, numericCheck1068, reducedZero1068 B hB hF, mul_zero]

theorem reducedZero1069 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1069 (mixedVector B) = 0 := by
  have h636 : mixedVector B (Sum.inr 636) = Sparse.eval nodeValue636 (mixedVector B) := by
    change mixedMoment B node636 node636Labels = _
    exact sound636 B hB hF
  have h1145 : mixedVector B (Sum.inr 1145) = Sparse.eval nodeValue1145 (mixedVector B) := by
    change mixedMoment B node1145 node1145Labels = _
    exact sound1145 B hB hF
  have h1155 : mixedVector B (Sum.inr 1155) = Sparse.eval nodeValue1155 (mixedVector B) := by
    change mixedMoment B node1155 node1155Labels = _
    exact sound1155 B hB hF
  have h1243 : mixedVector B (Sum.inr 1243) = Sparse.eval nodeValue1243 (mixedVector B) := by
    change mixedMoment B node1243 node1243Labels = _
    exact sound1243 B hB hF
  have h1246 : mixedVector B (Sum.inr 1246) = Sparse.eval nodeValue1246 (mixedVector B) := by
    change mixedMoment B node1246 node1246Labels = _
    exact sound1246 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1238, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h636, h1145, h1155, h1243, h1246, h4092, reducedSource1069] using sourceEq1238 B hB

theorem rowSound1069 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1069 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1069, numericCheck1069, reducedZero1069 B hB hF, mul_zero]

theorem reducedZero1070 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1070 (mixedVector B) = 0 := by
  have h641 : mixedVector B (Sum.inr 641) = Sparse.eval nodeValue641 (mixedVector B) := by
    change mixedMoment B node641 node641Labels = _
    exact sound641 B hB hF
  have h1159 : mixedVector B (Sum.inr 1159) = Sparse.eval nodeValue1159 (mixedVector B) := by
    change mixedMoment B node1159 node1159Labels = _
    exact sound1159 B hB hF
  have h1242 : mixedVector B (Sum.inr 1242) = Sparse.eval nodeValue1242 (mixedVector B) := by
    change mixedMoment B node1242 node1242Labels = _
    exact sound1242 B hB hF
  have h1264 : mixedVector B (Sum.inr 1264) = Sparse.eval nodeValue1264 (mixedVector B) := by
    change mixedMoment B node1264 node1264Labels = _
    exact sound1264 B hB hF
  have h1294 : mixedVector B (Sum.inr 1294) = Sparse.eval nodeValue1294 (mixedVector B) := by
    change mixedMoment B node1294 node1294Labels = _
    exact sound1294 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1239, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h641, h1159, h1242, h1264, h1294, h4092, reducedSource1070] using sourceEq1239 B hB

theorem rowSound1070 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1070 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1070, numericCheck1070, reducedZero1070 B hB hF, mul_zero]

theorem reducedZero1071 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1071 (mixedVector B) = 0 := by
  have h1643 : mixedVector B (Sum.inr 1643) = Sparse.eval nodeValue1643 (mixedVector B) := by
    change mixedMoment B node1643 node1643Labels = _
    exact sound1643 B hB hF
  have h1647 : mixedVector B (Sum.inr 1647) = Sparse.eval nodeValue1647 (mixedVector B) := by
    change mixedMoment B node1647 node1647Labels = _
    exact sound1647 B hB hF
  have h1652 : mixedVector B (Sum.inr 1652) = Sparse.eval nodeValue1652 (mixedVector B) := by
    change mixedMoment B node1652 node1652Labels = _
    exact sound1652 B hB hF
  have h1725 : mixedVector B (Sum.inr 1725) = Sparse.eval nodeValue1725 (mixedVector B) := by
    change mixedMoment B node1725 node1725Labels = _
    exact sound1725 B hB hF
  have h3302 : mixedVector B (Sum.inr 3302) = Sparse.eval nodeValue3302 (mixedVector B) := by
    change mixedMoment B node3302 node3302Labels = _
    exact sound3302 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1240, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1643, h1647, h1652, h1725, h3302, h4070, reducedSource1071] using sourceEq1240 B hB

theorem rowSound1071 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1071 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1071, numericCheck1071, reducedZero1071 B hB hF, mul_zero]

theorem sourceRowsAt1056 : MixedData.sourceRows (1056 : Fin 2425) =
    MixedData.row1056 := by decide +kernel

theorem sourceRowsAt1057 : MixedData.sourceRows (1057 : Fin 2425) =
    MixedData.row1057 := by decide +kernel

theorem sourceRowsAt1058 : MixedData.sourceRows (1058 : Fin 2425) =
    MixedData.row1058 := by decide +kernel

theorem sourceRowsAt1059 : MixedData.sourceRows (1059 : Fin 2425) =
    MixedData.row1059 := by decide +kernel

theorem sourceRowsAt1060 : MixedData.sourceRows (1060 : Fin 2425) =
    MixedData.row1060 := by decide +kernel

theorem sourceRowsAt1061 : MixedData.sourceRows (1061 : Fin 2425) =
    MixedData.row1061 := by decide +kernel

theorem sourceRowsAt1062 : MixedData.sourceRows (1062 : Fin 2425) =
    MixedData.row1062 := by decide +kernel

theorem sourceRowsAt1063 : MixedData.sourceRows (1063 : Fin 2425) =
    MixedData.row1063 := by decide +kernel

theorem sourceRowsAt1064 : MixedData.sourceRows (1064 : Fin 2425) =
    MixedData.row1064 := by decide +kernel

theorem sourceRowsAt1065 : MixedData.sourceRows (1065 : Fin 2425) =
    MixedData.row1065 := by decide +kernel

theorem sourceRowsAt1066 : MixedData.sourceRows (1066 : Fin 2425) =
    MixedData.row1066 := by decide +kernel

theorem sourceRowsAt1067 : MixedData.sourceRows (1067 : Fin 2425) =
    MixedData.row1067 := by decide +kernel

theorem sourceRowsAt1068 : MixedData.sourceRows (1068 : Fin 2425) =
    MixedData.row1068 := by decide +kernel

theorem sourceRowsAt1069 : MixedData.sourceRows (1069 : Fin 2425) =
    MixedData.row1069 := by decide +kernel

theorem sourceRowsAt1070 : MixedData.sourceRows (1070 : Fin 2425) =
    MixedData.row1070 := by decide +kernel

theorem sourceRowsAt1071 : MixedData.sourceRows (1071 : Fin 2425) =
    MixedData.row1071 := by decide +kernel

theorem chunkSound66 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 66) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1056 ∨ k.val = 1057 ∨ k.val = 1058 ∨ k.val = 1059 ∨ k.val = 1060 ∨ k.val = 1061 ∨ k.val = 1062 ∨ k.val = 1063 ∨ k.val = 1064 ∨ k.val = 1065 ∨ k.val = 1066 ∨ k.val = 1067 ∨ k.val = 1068 ∨ k.val = 1069 ∨ k.val = 1070 ∨ k.val = 1071 := by omega
  rcases heq with h1056 | h1057 | h1058 | h1059 | h1060 | h1061 | h1062 | h1063 | h1064 | h1065 | h1066 | h1067 | h1068 | h1069 | h1070 | h1071
  · have he : k = (1056 : Fin 2425) := Fin.ext h1056
    subst k
    rw [sourceRowsAt1056]
    exact rowSound1056 B hB hF
  · have he : k = (1057 : Fin 2425) := Fin.ext h1057
    subst k
    rw [sourceRowsAt1057]
    exact rowSound1057 B hB hF
  · have he : k = (1058 : Fin 2425) := Fin.ext h1058
    subst k
    rw [sourceRowsAt1058]
    exact rowSound1058 B hB hF
  · have he : k = (1059 : Fin 2425) := Fin.ext h1059
    subst k
    rw [sourceRowsAt1059]
    exact rowSound1059 B hB hF
  · have he : k = (1060 : Fin 2425) := Fin.ext h1060
    subst k
    rw [sourceRowsAt1060]
    exact rowSound1060 B hB hF
  · have he : k = (1061 : Fin 2425) := Fin.ext h1061
    subst k
    rw [sourceRowsAt1061]
    exact rowSound1061 B hB hF
  · have he : k = (1062 : Fin 2425) := Fin.ext h1062
    subst k
    rw [sourceRowsAt1062]
    exact rowSound1062 B hB hF
  · have he : k = (1063 : Fin 2425) := Fin.ext h1063
    subst k
    rw [sourceRowsAt1063]
    exact rowSound1063 B hB hF
  · have he : k = (1064 : Fin 2425) := Fin.ext h1064
    subst k
    rw [sourceRowsAt1064]
    exact rowSound1064 B hB hF
  · have he : k = (1065 : Fin 2425) := Fin.ext h1065
    subst k
    rw [sourceRowsAt1065]
    exact rowSound1065 B hB hF
  · have he : k = (1066 : Fin 2425) := Fin.ext h1066
    subst k
    rw [sourceRowsAt1066]
    exact rowSound1066 B hB hF
  · have he : k = (1067 : Fin 2425) := Fin.ext h1067
    subst k
    rw [sourceRowsAt1067]
    exact rowSound1067 B hB hF
  · have he : k = (1068 : Fin 2425) := Fin.ext h1068
    subst k
    rw [sourceRowsAt1068]
    exact rowSound1068 B hB hF
  · have he : k = (1069 : Fin 2425) := Fin.ext h1069
    subst k
    rw [sourceRowsAt1069]
    exact rowSound1069 B hB hF
  · have he : k = (1070 : Fin 2425) := Fin.ext h1070
    subst k
    rw [sourceRowsAt1070]
    exact rowSound1070 B hB hF
  · have he : k = (1071 : Fin 2425) := Fin.ext h1071
    subst k
    rw [sourceRowsAt1071]
    exact rowSound1071 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
