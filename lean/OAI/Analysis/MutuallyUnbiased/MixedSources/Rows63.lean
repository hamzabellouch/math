import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources36

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1008 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1008 (mixedVector B) = 0 := by
  have h615 : mixedVector B (Sum.inr 615) = Sparse.eval nodeValue615 (mixedVector B) := by
    change mixedMoment B node615 node615Labels = _
    exact sound615 B hB hF
  have h622 : mixedVector B (Sum.inr 622) = Sparse.eval nodeValue622 (mixedVector B) := by
    change mixedMoment B node622 node622Labels = _
    exact sound622 B hB hF
  have h1140 : mixedVector B (Sum.inr 1140) = Sparse.eval nodeValue1140 (mixedVector B) := by
    change mixedMoment B node1140 node1140Labels = _
    exact sound1140 B hB hF
  have h1307 : mixedVector B (Sum.inr 1307) = Sparse.eval nodeValue1307 (mixedVector B) := by
    change mixedMoment B node1307 node1307Labels = _
    exact sound1307 B hB hF
  have h3126 : mixedVector B (Sum.inr 3126) = Sparse.eval nodeValue3126 (mixedVector B) := by
    change mixedMoment B node3126 node3126Labels = _
    exact sound3126 B hB hF
  simpa only [sourceForm1160, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h615, h622, h1140, h1307, h3126, reducedSource1008] using sourceEq1160 B hB

theorem rowSound1008 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1008 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1008, numericCheck1008, reducedZero1008 B hB hF, mul_zero]

theorem reducedZero1009 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1009 (mixedVector B) = 0 := by
  have h4468 : mixedVector B (Sum.inr 4468) = Sparse.eval nodeValue4468 (mixedVector B) := by
    change mixedMoment B node4468 node4468Labels = _
    exact sound4468 B hB hF
  have h4512 : mixedVector B (Sum.inr 4512) = Sparse.eval nodeValue4512 (mixedVector B) := by
    change mixedMoment B node4512 node4512Labels = _
    exact sound4512 B hB hF
  have h4594 : mixedVector B (Sum.inr 4594) = Sparse.eval nodeValue4594 (mixedVector B) := by
    change mixedMoment B node4594 node4594Labels = _
    exact sound4594 B hB hF
  simpa only [sourceForm1161, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4468, h4512, h4594, reducedSource1009] using sourceEq1161 B hB

theorem rowSound1009 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1009 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1009, numericCheck1009, reducedZero1009 B hB hF, mul_zero]

theorem reducedZero1010 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1010 (mixedVector B) = 0 := by
  have h1051 : mixedVector B (Sum.inr 1051) = Sparse.eval nodeValue1051 (mixedVector B) := by
    change mixedMoment B node1051 node1051Labels = _
    exact sound1051 B hB hF
  have h1096 : mixedVector B (Sum.inr 1096) = Sparse.eval nodeValue1096 (mixedVector B) := by
    change mixedMoment B node1096 node1096Labels = _
    exact sound1096 B hB hF
  have h1221 : mixedVector B (Sum.inr 1221) = Sparse.eval nodeValue1221 (mixedVector B) := by
    change mixedMoment B node1221 node1221Labels = _
    exact sound1221 B hB hF
  have h1275 : mixedVector B (Sum.inr 1275) = Sparse.eval nodeValue1275 (mixedVector B) := by
    change mixedMoment B node1275 node1275Labels = _
    exact sound1275 B hB hF
  have h1456 : mixedVector B (Sum.inr 1456) = Sparse.eval nodeValue1456 (mixedVector B) := by
    change mixedMoment B node1456 node1456Labels = _
    exact sound1456 B hB hF
  simpa only [sourceForm1162, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1051, h1096, h1221, h1275, h1456, reducedSource1010] using sourceEq1162 B hB

theorem rowSound1010 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1010 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1010, numericCheck1010, reducedZero1010 B hB hF, mul_zero]

theorem reducedZero1011 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1011 (mixedVector B) = 0 := by
  have h1752 : mixedVector B (Sum.inr 1752) = Sparse.eval nodeValue1752 (mixedVector B) := by
    change mixedMoment B node1752 node1752Labels = _
    exact sound1752 B hB hF
  have h1758 : mixedVector B (Sum.inr 1758) = Sparse.eval nodeValue1758 (mixedVector B) := by
    change mixedMoment B node1758 node1758Labels = _
    exact sound1758 B hB hF
  have h3313 : mixedVector B (Sum.inr 3313) = Sparse.eval nodeValue3313 (mixedVector B) := by
    change mixedMoment B node3313 node3313Labels = _
    exact sound3313 B hB hF
  have h4072 : mixedVector B (Sum.inr 4072) = Sparse.eval nodeValue4072 (mixedVector B) := by
    change mixedMoment B node4072 node4072Labels = _
    exact sound4072 B hB hF
  simpa only [sourceForm1163, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1752, h1758, h3313, h4072, reducedSource1011] using sourceEq1163 B hB

theorem rowSound1011 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1011 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1011, numericCheck1011, reducedZero1011 B hB hF, mul_zero]

theorem reducedZero1012 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1012 (mixedVector B) = 0 := by
  have h4156 : mixedVector B (Sum.inr 4156) = Sparse.eval nodeValue4156 (mixedVector B) := by
    change mixedMoment B node4156 node4156Labels = _
    exact sound4156 B hB hF
  have h4159 : mixedVector B (Sum.inr 4159) = Sparse.eval nodeValue4159 (mixedVector B) := by
    change mixedMoment B node4159 node4159Labels = _
    exact sound4159 B hB hF
  have h4163 : mixedVector B (Sum.inr 4163) = Sparse.eval nodeValue4163 (mixedVector B) := by
    change mixedMoment B node4163 node4163Labels = _
    exact sound4163 B hB hF
  have h4187 : mixedVector B (Sum.inr 4187) = Sparse.eval nodeValue4187 (mixedVector B) := by
    change mixedMoment B node4187 node4187Labels = _
    exact sound4187 B hB hF
  have h4189 : mixedVector B (Sum.inr 4189) = Sparse.eval nodeValue4189 (mixedVector B) := by
    change mixedMoment B node4189 node4189Labels = _
    exact sound4189 B hB hF
  have h4330 : mixedVector B (Sum.inr 4330) = Sparse.eval nodeValue4330 (mixedVector B) := by
    change mixedMoment B node4330 node4330Labels = _
    exact sound4330 B hB hF
  have h4356 : mixedVector B (Sum.inr 4356) = Sparse.eval nodeValue4356 (mixedVector B) := by
    change mixedMoment B node4356 node4356Labels = _
    exact sound4356 B hB hF
  have h4370 : mixedVector B (Sum.inr 4370) = Sparse.eval nodeValue4370 (mixedVector B) := by
    change mixedMoment B node4370 node4370Labels = _
    exact sound4370 B hB hF
  have h4460 : mixedVector B (Sum.inr 4460) = Sparse.eval nodeValue4460 (mixedVector B) := by
    change mixedMoment B node4460 node4460Labels = _
    exact sound4460 B hB hF
  have h4505 : mixedVector B (Sum.inr 4505) = Sparse.eval nodeValue4505 (mixedVector B) := by
    change mixedMoment B node4505 node4505Labels = _
    exact sound4505 B hB hF
  have h4605 : mixedVector B (Sum.inr 4605) = Sparse.eval nodeValue4605 (mixedVector B) := by
    change mixedMoment B node4605 node4605Labels = _
    exact sound4605 B hB hF
  have h4621 : mixedVector B (Sum.inr 4621) = Sparse.eval nodeValue4621 (mixedVector B) := by
    change mixedMoment B node4621 node4621Labels = _
    exact sound4621 B hB hF
  have h4897 : mixedVector B (Sum.inr 4897) = Sparse.eval nodeValue4897 (mixedVector B) := by
    change mixedMoment B node4897 node4897Labels = _
    exact sound4897 B hB hF
  simpa only [sourceForm1164, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4156, h4159, h4163, h4187, h4189, h4330, h4356, h4370, h4460, h4505, h4605, h4621, h4897, reducedSource1012] using sourceEq1164 B hB

theorem rowSound1012 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1012 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1012, numericCheck1012, reducedZero1012 B hB hF, mul_zero]

theorem reducedZero1013 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1013 (mixedVector B) = 0 := by
  have h587 : mixedVector B (Sum.inr 587) = Sparse.eval nodeValue587 (mixedVector B) := by
    change mixedMoment B node587 node587Labels = _
    exact sound587 B hB hF
  have h591 : mixedVector B (Sum.inr 591) = Sparse.eval nodeValue591 (mixedVector B) := by
    change mixedMoment B node591 node591Labels = _
    exact sound591 B hB hF
  have h617 : mixedVector B (Sum.inr 617) = Sparse.eval nodeValue617 (mixedVector B) := by
    change mixedMoment B node617 node617Labels = _
    exact sound617 B hB hF
  have h633 : mixedVector B (Sum.inr 633) = Sparse.eval nodeValue633 (mixedVector B) := by
    change mixedMoment B node633 node633Labels = _
    exact sound633 B hB hF
  have h650 : mixedVector B (Sum.inr 650) = Sparse.eval nodeValue650 (mixedVector B) := by
    change mixedMoment B node650 node650Labels = _
    exact sound650 B hB hF
  have h1118 : mixedVector B (Sum.inr 1118) = Sparse.eval nodeValue1118 (mixedVector B) := by
    change mixedMoment B node1118 node1118Labels = _
    exact sound1118 B hB hF
  have h1142 : mixedVector B (Sum.inr 1142) = Sparse.eval nodeValue1142 (mixedVector B) := by
    change mixedMoment B node1142 node1142Labels = _
    exact sound1142 B hB hF
  have h1173 : mixedVector B (Sum.inr 1173) = Sparse.eval nodeValue1173 (mixedVector B) := by
    change mixedMoment B node1173 node1173Labels = _
    exact sound1173 B hB hF
  have h1271 : mixedVector B (Sum.inr 1271) = Sparse.eval nodeValue1271 (mixedVector B) := by
    change mixedMoment B node1271 node1271Labels = _
    exact sound1271 B hB hF
  have h1308 : mixedVector B (Sum.inr 1308) = Sparse.eval nodeValue1308 (mixedVector B) := by
    change mixedMoment B node1308 node1308Labels = _
    exact sound1308 B hB hF
  have h1416 : mixedVector B (Sum.inr 1416) = Sparse.eval nodeValue1416 (mixedVector B) := by
    change mixedMoment B node1416 node1416Labels = _
    exact sound1416 B hB hF
  have h1450 : mixedVector B (Sum.inr 1450) = Sparse.eval nodeValue1450 (mixedVector B) := by
    change mixedMoment B node1450 node1450Labels = _
    exact sound1450 B hB hF
  have h3114 : mixedVector B (Sum.inr 3114) = Sparse.eval nodeValue3114 (mixedVector B) := by
    change mixedMoment B node3114 node3114Labels = _
    exact sound3114 B hB hF
  simpa only [sourceForm1165, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h587, h591, h617, h633, h650, h1118, h1142, h1173, h1271, h1308, h1416, h1450, h3114, reducedSource1013] using sourceEq1165 B hB

theorem rowSound1013 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1013 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1013, numericCheck1013, reducedZero1013 B hB hF, mul_zero]

theorem reducedZero1014 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1014 (mixedVector B) = 0 := by
  have h1516 : mixedVector B (Sum.inr 1516) = Sparse.eval nodeValue1516 (mixedVector B) := by
    change mixedMoment B node1516 node1516Labels = _
    exact sound1516 B hB hF
  have h1532 : mixedVector B (Sum.inr 1532) = Sparse.eval nodeValue1532 (mixedVector B) := by
    change mixedMoment B node1532 node1532Labels = _
    exact sound1532 B hB hF
  have h1534 : mixedVector B (Sum.inr 1534) = Sparse.eval nodeValue1534 (mixedVector B) := by
    change mixedMoment B node1534 node1534Labels = _
    exact sound1534 B hB hF
  have h1537 : mixedVector B (Sum.inr 1537) = Sparse.eval nodeValue1537 (mixedVector B) := by
    change mixedMoment B node1537 node1537Labels = _
    exact sound1537 B hB hF
  have h1540 : mixedVector B (Sum.inr 1540) = Sparse.eval nodeValue1540 (mixedVector B) := by
    change mixedMoment B node1540 node1540Labels = _
    exact sound1540 B hB hF
  have h1672 : mixedVector B (Sum.inr 1672) = Sparse.eval nodeValue1672 (mixedVector B) := by
    change mixedMoment B node1672 node1672Labels = _
    exact sound1672 B hB hF
  have h1692 : mixedVector B (Sum.inr 1692) = Sparse.eval nodeValue1692 (mixedVector B) := by
    change mixedMoment B node1692 node1692Labels = _
    exact sound1692 B hB hF
  have h1722 : mixedVector B (Sum.inr 1722) = Sparse.eval nodeValue1722 (mixedVector B) := by
    change mixedMoment B node1722 node1722Labels = _
    exact sound1722 B hB hF
  have h1725 : mixedVector B (Sum.inr 1725) = Sparse.eval nodeValue1725 (mixedVector B) := by
    change mixedMoment B node1725 node1725Labels = _
    exact sound1725 B hB hF
  have h1754 : mixedVector B (Sum.inr 1754) = Sparse.eval nodeValue1754 (mixedVector B) := by
    change mixedMoment B node1754 node1754Labels = _
    exact sound1754 B hB hF
  have h2226 : mixedVector B (Sum.inr 2226) = Sparse.eval nodeValue2226 (mixedVector B) := by
    change mixedMoment B node2226 node2226Labels = _
    exact sound2226 B hB hF
  have h2289 : mixedVector B (Sum.inr 2289) = Sparse.eval nodeValue2289 (mixedVector B) := by
    change mixedMoment B node2289 node2289Labels = _
    exact sound2289 B hB hF
  have h2292 : mixedVector B (Sum.inr 2292) = Sparse.eval nodeValue2292 (mixedVector B) := by
    change mixedMoment B node2292 node2292Labels = _
    exact sound2292 B hB hF
  simpa only [sourceForm1166, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1516, h1532, h1534, h1537, h1540, h1672, h1692, h1722, h1725, h1754, h2226, h2289, h2292, reducedSource1014] using sourceEq1166 B hB

theorem rowSound1014 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1014 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1014, numericCheck1014, reducedZero1014 B hB hF, mul_zero]

theorem reducedZero1015 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1015 (mixedVector B) = 0 := by
  have h591 : mixedVector B (Sum.inr 591) = Sparse.eval nodeValue591 (mixedVector B) := by
    change mixedMoment B node591 node591Labels = _
    exact sound591 B hB hF
  have h628 : mixedVector B (Sum.inr 628) = Sparse.eval nodeValue628 (mixedVector B) := by
    change mixedMoment B node628 node628Labels = _
    exact sound628 B hB hF
  have h643 : mixedVector B (Sum.inr 643) = Sparse.eval nodeValue643 (mixedVector B) := by
    change mixedMoment B node643 node643Labels = _
    exact sound643 B hB hF
  have h1051 : mixedVector B (Sum.inr 1051) = Sparse.eval nodeValue1051 (mixedVector B) := by
    change mixedMoment B node1051 node1051Labels = _
    exact sound1051 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1167, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h591, h628, h643, h1051, h4084, reducedSource1015] using sourceEq1167 B hB

theorem rowSound1015 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1015 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1015, numericCheck1015, reducedZero1015 B hB hF, mul_zero]

theorem reducedZero1016 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1016 (mixedVector B) = 0 := by
  have h628 : mixedVector B (Sum.inr 628) = Sparse.eval nodeValue628 (mixedVector B) := by
    change mixedMoment B node628 node628Labels = _
    exact sound628 B hB hF
  have h908 : mixedVector B (Sum.inr 908) = Sparse.eval nodeValue908 (mixedVector B) := by
    change mixedMoment B node908 node908Labels = _
    exact sound908 B hB hF
  have h934 : mixedVector B (Sum.inr 934) = Sparse.eval nodeValue934 (mixedVector B) := by
    change mixedMoment B node934 node934Labels = _
    exact sound934 B hB hF
  have h1051 : mixedVector B (Sum.inr 1051) = Sparse.eval nodeValue1051 (mixedVector B) := by
    change mixedMoment B node1051 node1051Labels = _
    exact sound1051 B hB hF
  have h1239 : mixedVector B (Sum.inr 1239) = Sparse.eval nodeValue1239 (mixedVector B) := by
    change mixedMoment B node1239 node1239Labels = _
    exact sound1239 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1168, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h628, h908, h934, h1051, h1239, h4084, reducedSource1016] using sourceEq1168 B hB

theorem rowSound1016 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1016 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1016, numericCheck1016, reducedZero1016 B hB hF, mul_zero]

theorem reducedZero1017 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1017 (mixedVector B) = 0 := by
  have h584 : mixedVector B (Sum.inr 584) = Sparse.eval nodeValue584 (mixedVector B) := by
    change mixedMoment B node584 node584Labels = _
    exact sound584 B hB hF
  have h908 : mixedVector B (Sum.inr 908) = Sparse.eval nodeValue908 (mixedVector B) := by
    change mixedMoment B node908 node908Labels = _
    exact sound908 B hB hF
  have h948 : mixedVector B (Sum.inr 948) = Sparse.eval nodeValue948 (mixedVector B) := by
    change mixedMoment B node948 node948Labels = _
    exact sound948 B hB hF
  have h1043 : mixedVector B (Sum.inr 1043) = Sparse.eval nodeValue1043 (mixedVector B) := by
    change mixedMoment B node1043 node1043Labels = _
    exact sound1043 B hB hF
  have h1051 : mixedVector B (Sum.inr 1051) = Sparse.eval nodeValue1051 (mixedVector B) := by
    change mixedMoment B node1051 node1051Labels = _
    exact sound1051 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1169, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h584, h908, h948, h1043, h1051, h4084, reducedSource1017] using sourceEq1169 B hB

theorem rowSound1017 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1017 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1017, numericCheck1017, reducedZero1017 B hB hF, mul_zero]

theorem reducedZero1018 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1018 (mixedVector B) = 0 := by
  have h643 : mixedVector B (Sum.inr 643) = Sparse.eval nodeValue643 (mixedVector B) := by
    change mixedMoment B node643 node643Labels = _
    exact sound643 B hB hF
  have h948 : mixedVector B (Sum.inr 948) = Sparse.eval nodeValue948 (mixedVector B) := by
    change mixedMoment B node948 node948Labels = _
    exact sound948 B hB hF
  have h1051 : mixedVector B (Sum.inr 1051) = Sparse.eval nodeValue1051 (mixedVector B) := by
    change mixedMoment B node1051 node1051Labels = _
    exact sound1051 B hB hF
  have h1297 : mixedVector B (Sum.inr 1297) = Sparse.eval nodeValue1297 (mixedVector B) := by
    change mixedMoment B node1297 node1297Labels = _
    exact sound1297 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1170, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h643, h948, h1051, h1297, h4084, reducedSource1018] using sourceEq1170 B hB

theorem rowSound1018 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1018 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1018, numericCheck1018, reducedZero1018 B hB hF, mul_zero]

theorem reducedZero1019 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1019 (mixedVector B) = 0 := by
  have h615 : mixedVector B (Sum.inr 615) = Sparse.eval nodeValue615 (mixedVector B) := by
    change mixedMoment B node615 node615Labels = _
    exact sound615 B hB hF
  have h934 : mixedVector B (Sum.inr 934) = Sparse.eval nodeValue934 (mixedVector B) := by
    change mixedMoment B node934 node934Labels = _
    exact sound934 B hB hF
  have h1051 : mixedVector B (Sum.inr 1051) = Sparse.eval nodeValue1051 (mixedVector B) := by
    change mixedMoment B node1051 node1051Labels = _
    exact sound1051 B hB hF
  have h1089 : mixedVector B (Sum.inr 1089) = Sparse.eval nodeValue1089 (mixedVector B) := by
    change mixedMoment B node1089 node1089Labels = _
    exact sound1089 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1171, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h615, h934, h1051, h1089, h4084, reducedSource1019] using sourceEq1171 B hB

theorem rowSound1019 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1019 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1019, numericCheck1019, reducedZero1019 B hB hF, mul_zero]

theorem reducedZero1020 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1020 (mixedVector B) = 0 := by
  have h4108 : mixedVector B (Sum.inr 4108) = Sparse.eval nodeValue4108 (mixedVector B) := by
    change mixedMoment B node4108 node4108Labels = _
    exact sound4108 B hB hF
  have h4112 : mixedVector B (Sum.inr 4112) = Sparse.eval nodeValue4112 (mixedVector B) := by
    change mixedMoment B node4112 node4112Labels = _
    exact sound4112 B hB hF
  have h4134 : mixedVector B (Sum.inr 4134) = Sparse.eval nodeValue4134 (mixedVector B) := by
    change mixedMoment B node4134 node4134Labels = _
    exact sound4134 B hB hF
  have h4146 : mixedVector B (Sum.inr 4146) = Sparse.eval nodeValue4146 (mixedVector B) := by
    change mixedMoment B node4146 node4146Labels = _
    exact sound4146 B hB hF
  have h4181 : mixedVector B (Sum.inr 4181) = Sparse.eval nodeValue4181 (mixedVector B) := by
    change mixedMoment B node4181 node4181Labels = _
    exact sound4181 B hB hF
  have h4293 : mixedVector B (Sum.inr 4293) = Sparse.eval nodeValue4293 (mixedVector B) := by
    change mixedMoment B node4293 node4293Labels = _
    exact sound4293 B hB hF
  have h4315 : mixedVector B (Sum.inr 4315) = Sparse.eval nodeValue4315 (mixedVector B) := by
    change mixedMoment B node4315 node4315Labels = _
    exact sound4315 B hB hF
  have h4356 : mixedVector B (Sum.inr 4356) = Sparse.eval nodeValue4356 (mixedVector B) := by
    change mixedMoment B node4356 node4356Labels = _
    exact sound4356 B hB hF
  have h4463 : mixedVector B (Sum.inr 4463) = Sparse.eval nodeValue4463 (mixedVector B) := by
    change mixedMoment B node4463 node4463Labels = _
    exact sound4463 B hB hF
  have h4507 : mixedVector B (Sum.inr 4507) = Sparse.eval nodeValue4507 (mixedVector B) := by
    change mixedMoment B node4507 node4507Labels = _
    exact sound4507 B hB hF
  have h4608 : mixedVector B (Sum.inr 4608) = Sparse.eval nodeValue4608 (mixedVector B) := by
    change mixedMoment B node4608 node4608Labels = _
    exact sound4608 B hB hF
  have h4625 : mixedVector B (Sum.inr 4625) = Sparse.eval nodeValue4625 (mixedVector B) := by
    change mixedMoment B node4625 node4625Labels = _
    exact sound4625 B hB hF
  have h5296 : mixedVector B (Sum.inr 5296) = Sparse.eval nodeValue5296 (mixedVector B) := by
    change mixedMoment B node5296 node5296Labels = _
    exact sound5296 B hB hF
  simpa only [sourceForm1172, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4108, h4112, h4134, h4146, h4181, h4293, h4315, h4356, h4463, h4507, h4608, h4625, h5296, reducedSource1020] using sourceEq1172 B hB

theorem rowSound1020 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1020 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1020, numericCheck1020, reducedZero1020 B hB hF, mul_zero]

theorem reducedZero1021 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1021 (mixedVector B) = 0 := by
  have h545 : mixedVector B (Sum.inr 545) = Sparse.eval nodeValue545 (mixedVector B) := by
    change mixedMoment B node545 node545Labels = _
    exact sound545 B hB hF
  have h549 : mixedVector B (Sum.inr 549) = Sparse.eval nodeValue549 (mixedVector B) := by
    change mixedMoment B node549 node549Labels = _
    exact sound549 B hB hF
  have h564 : mixedVector B (Sum.inr 564) = Sparse.eval nodeValue564 (mixedVector B) := by
    change mixedMoment B node564 node564Labels = _
    exact sound564 B hB hF
  have h574 : mixedVector B (Sum.inr 574) = Sparse.eval nodeValue574 (mixedVector B) := by
    change mixedMoment B node574 node574Labels = _
    exact sound574 B hB hF
  have h609 : mixedVector B (Sum.inr 609) = Sparse.eval nodeValue609 (mixedVector B) := by
    change mixedMoment B node609 node609Labels = _
    exact sound609 B hB hF
  have h871 : mixedVector B (Sum.inr 871) = Sparse.eval nodeValue871 (mixedVector B) := by
    change mixedMoment B node871 node871Labels = _
    exact sound871 B hB hF
  have h893 : mixedVector B (Sum.inr 893) = Sparse.eval nodeValue893 (mixedVector B) := by
    change mixedMoment B node893 node893Labels = _
    exact sound893 B hB hF
  have h934 : mixedVector B (Sum.inr 934) = Sparse.eval nodeValue934 (mixedVector B) := by
    change mixedMoment B node934 node934Labels = _
    exact sound934 B hB hF
  have h1046 : mixedVector B (Sum.inr 1046) = Sparse.eval nodeValue1046 (mixedVector B) := by
    change mixedMoment B node1046 node1046Labels = _
    exact sound1046 B hB hF
  have h1091 : mixedVector B (Sum.inr 1091) = Sparse.eval nodeValue1091 (mixedVector B) := by
    change mixedMoment B node1091 node1091Labels = _
    exact sound1091 B hB hF
  have h1242 : mixedVector B (Sum.inr 1242) = Sparse.eval nodeValue1242 (mixedVector B) := by
    change mixedMoment B node1242 node1242Labels = _
    exact sound1242 B hB hF
  have h1304 : mixedVector B (Sum.inr 1304) = Sparse.eval nodeValue1304 (mixedVector B) := by
    change mixedMoment B node1304 node1304Labels = _
    exact sound1304 B hB hF
  have h2770 : mixedVector B (Sum.inr 2770) = Sparse.eval nodeValue2770 (mixedVector B) := by
    change mixedMoment B node2770 node2770Labels = _
    exact sound2770 B hB hF
  simpa only [sourceForm1173, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h545, h549, h564, h574, h609, h871, h893, h934, h1046, h1091, h1242, h1304, h2770, reducedSource1021] using sourceEq1173 B hB

theorem rowSound1021 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1021 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1021, numericCheck1021, reducedZero1021 B hB hF, mul_zero]

theorem reducedZero1022 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1022 (mixedVector B) = 0 := by
  have h855 : mixedVector B (Sum.inr 855) = Sparse.eval nodeValue855 (mixedVector B) := by
    change mixedMoment B node855 node855Labels = _
    exact sound855 B hB hF
  have h1620 : mixedVector B (Sum.inr 1620) = Sparse.eval nodeValue1620 (mixedVector B) := by
    change mixedMoment B node1620 node1620Labels = _
    exact sound1620 B hB hF
  have h1752 : mixedVector B (Sum.inr 1752) = Sparse.eval nodeValue1752 (mixedVector B) := by
    change mixedMoment B node1752 node1752Labels = _
    exact sound1752 B hB hF
  have h1758 : mixedVector B (Sum.inr 1758) = Sparse.eval nodeValue1758 (mixedVector B) := by
    change mixedMoment B node1758 node1758Labels = _
    exact sound1758 B hB hF
  have h4072 : mixedVector B (Sum.inr 4072) = Sparse.eval nodeValue4072 (mixedVector B) := by
    change mixedMoment B node4072 node4072Labels = _
    exact sound4072 B hB hF
  simpa only [sourceForm1177, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h855, h1620, h1752, h1758, h4072, reducedSource1022] using sourceEq1177 B hB

theorem rowSound1022 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1022 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1022, numericCheck1022, reducedZero1022 B hB hF, mul_zero]

theorem reducedZero1023 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1023 (mixedVector B) = 0 := by
  have h826 : mixedVector B (Sum.inr 826) = Sparse.eval nodeValue826 (mixedVector B) := by
    change mixedMoment B node826 node826Labels = _
    exact sound826 B hB hF
  have h832 : mixedVector B (Sum.inr 832) = Sparse.eval nodeValue832 (mixedVector B) := by
    change mixedMoment B node832 node832Labels = _
    exact sound832 B hB hF
  have h859 : mixedVector B (Sum.inr 859) = Sparse.eval nodeValue859 (mixedVector B) := by
    change mixedMoment B node859 node859Labels = _
    exact sound859 B hB hF
  have h1741 : mixedVector B (Sum.inr 1741) = Sparse.eval nodeValue1741 (mixedVector B) := by
    change mixedMoment B node1741 node1741Labels = _
    exact sound1741 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1178, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h826, h832, h859, h1741, h4071, reducedSource1023] using sourceEq1178 B hB

theorem rowSound1023 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1023 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1023, numericCheck1023, reducedZero1023 B hB hF, mul_zero]

theorem sourceRowsAt1008 : MixedData.sourceRows (1008 : Fin 2425) =
    MixedData.row1008 := by decide +kernel

theorem sourceRowsAt1009 : MixedData.sourceRows (1009 : Fin 2425) =
    MixedData.row1009 := by decide +kernel

theorem sourceRowsAt1010 : MixedData.sourceRows (1010 : Fin 2425) =
    MixedData.row1010 := by decide +kernel

theorem sourceRowsAt1011 : MixedData.sourceRows (1011 : Fin 2425) =
    MixedData.row1011 := by decide +kernel

theorem sourceRowsAt1012 : MixedData.sourceRows (1012 : Fin 2425) =
    MixedData.row1012 := by decide +kernel

theorem sourceRowsAt1013 : MixedData.sourceRows (1013 : Fin 2425) =
    MixedData.row1013 := by decide +kernel

theorem sourceRowsAt1014 : MixedData.sourceRows (1014 : Fin 2425) =
    MixedData.row1014 := by decide +kernel

theorem sourceRowsAt1015 : MixedData.sourceRows (1015 : Fin 2425) =
    MixedData.row1015 := by decide +kernel

theorem sourceRowsAt1016 : MixedData.sourceRows (1016 : Fin 2425) =
    MixedData.row1016 := by decide +kernel

theorem sourceRowsAt1017 : MixedData.sourceRows (1017 : Fin 2425) =
    MixedData.row1017 := by decide +kernel

theorem sourceRowsAt1018 : MixedData.sourceRows (1018 : Fin 2425) =
    MixedData.row1018 := by decide +kernel

theorem sourceRowsAt1019 : MixedData.sourceRows (1019 : Fin 2425) =
    MixedData.row1019 := by decide +kernel

theorem sourceRowsAt1020 : MixedData.sourceRows (1020 : Fin 2425) =
    MixedData.row1020 := by decide +kernel

theorem sourceRowsAt1021 : MixedData.sourceRows (1021 : Fin 2425) =
    MixedData.row1021 := by decide +kernel

theorem sourceRowsAt1022 : MixedData.sourceRows (1022 : Fin 2425) =
    MixedData.row1022 := by decide +kernel

theorem sourceRowsAt1023 : MixedData.sourceRows (1023 : Fin 2425) =
    MixedData.row1023 := by decide +kernel

theorem chunkSound63 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 63) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1008 ∨ k.val = 1009 ∨ k.val = 1010 ∨ k.val = 1011 ∨ k.val = 1012 ∨ k.val = 1013 ∨ k.val = 1014 ∨ k.val = 1015 ∨ k.val = 1016 ∨ k.val = 1017 ∨ k.val = 1018 ∨ k.val = 1019 ∨ k.val = 1020 ∨ k.val = 1021 ∨ k.val = 1022 ∨ k.val = 1023 := by omega
  rcases heq with h1008 | h1009 | h1010 | h1011 | h1012 | h1013 | h1014 | h1015 | h1016 | h1017 | h1018 | h1019 | h1020 | h1021 | h1022 | h1023
  · have he : k = (1008 : Fin 2425) := Fin.ext h1008
    subst k
    rw [sourceRowsAt1008]
    exact rowSound1008 B hB hF
  · have he : k = (1009 : Fin 2425) := Fin.ext h1009
    subst k
    rw [sourceRowsAt1009]
    exact rowSound1009 B hB hF
  · have he : k = (1010 : Fin 2425) := Fin.ext h1010
    subst k
    rw [sourceRowsAt1010]
    exact rowSound1010 B hB hF
  · have he : k = (1011 : Fin 2425) := Fin.ext h1011
    subst k
    rw [sourceRowsAt1011]
    exact rowSound1011 B hB hF
  · have he : k = (1012 : Fin 2425) := Fin.ext h1012
    subst k
    rw [sourceRowsAt1012]
    exact rowSound1012 B hB hF
  · have he : k = (1013 : Fin 2425) := Fin.ext h1013
    subst k
    rw [sourceRowsAt1013]
    exact rowSound1013 B hB hF
  · have he : k = (1014 : Fin 2425) := Fin.ext h1014
    subst k
    rw [sourceRowsAt1014]
    exact rowSound1014 B hB hF
  · have he : k = (1015 : Fin 2425) := Fin.ext h1015
    subst k
    rw [sourceRowsAt1015]
    exact rowSound1015 B hB hF
  · have he : k = (1016 : Fin 2425) := Fin.ext h1016
    subst k
    rw [sourceRowsAt1016]
    exact rowSound1016 B hB hF
  · have he : k = (1017 : Fin 2425) := Fin.ext h1017
    subst k
    rw [sourceRowsAt1017]
    exact rowSound1017 B hB hF
  · have he : k = (1018 : Fin 2425) := Fin.ext h1018
    subst k
    rw [sourceRowsAt1018]
    exact rowSound1018 B hB hF
  · have he : k = (1019 : Fin 2425) := Fin.ext h1019
    subst k
    rw [sourceRowsAt1019]
    exact rowSound1019 B hB hF
  · have he : k = (1020 : Fin 2425) := Fin.ext h1020
    subst k
    rw [sourceRowsAt1020]
    exact rowSound1020 B hB hF
  · have he : k = (1021 : Fin 2425) := Fin.ext h1021
    subst k
    rw [sourceRowsAt1021]
    exact rowSound1021 B hB hF
  · have he : k = (1022 : Fin 2425) := Fin.ext h1022
    subst k
    rw [sourceRowsAt1022]
    exact rowSound1022 B hB hF
  · have he : k = (1023 : Fin 2425) := Fin.ext h1023
    subst k
    rw [sourceRowsAt1023]
    exact rowSound1023 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
