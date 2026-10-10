import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic98
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources58

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1568 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1568 (mixedVector B) = 0 := by
  have h599 : mixedVector B (Sum.inr 599) = Sparse.eval nodeValue599 (mixedVector B) := by
    change mixedMoment B node599 node599Labels = _
    exact sound599 B hB hF
  have h600 : mixedVector B (Sum.inr 600) = Sparse.eval nodeValue600 (mixedVector B) := by
    change mixedMoment B node600 node600Labels = _
    exact sound600 B hB hF
  have h603 : mixedVector B (Sum.inr 603) = Sparse.eval nodeValue603 (mixedVector B) := by
    change mixedMoment B node603 node603Labels = _
    exact sound603 B hB hF
  have h1126 : mixedVector B (Sum.inr 1126) = Sparse.eval nodeValue1126 (mixedVector B) := by
    change mixedMoment B node1126 node1126Labels = _
    exact sound1126 B hB hF
  have h1129 : mixedVector B (Sum.inr 1129) = Sparse.eval nodeValue1129 (mixedVector B) := by
    change mixedMoment B node1129 node1129Labels = _
    exact sound1129 B hB hF
  have h1235 : mixedVector B (Sum.inr 1235) = Sparse.eval nodeValue1235 (mixedVector B) := by
    change mixedMoment B node1235 node1235Labels = _
    exact sound1235 B hB hF
  have h1236 : mixedVector B (Sum.inr 1236) = Sparse.eval nodeValue1236 (mixedVector B) := by
    change mixedMoment B node1236 node1236Labels = _
    exact sound1236 B hB hF
  have h1240 : mixedVector B (Sum.inr 1240) = Sparse.eval nodeValue1240 (mixedVector B) := by
    change mixedMoment B node1240 node1240Labels = _
    exact sound1240 B hB hF
  have h1299 : mixedVector B (Sum.inr 1299) = Sparse.eval nodeValue1299 (mixedVector B) := by
    change mixedMoment B node1299 node1299Labels = _
    exact sound1299 B hB hF
  have h1300 : mixedVector B (Sum.inr 1300) = Sparse.eval nodeValue1300 (mixedVector B) := by
    change mixedMoment B node1300 node1300Labels = _
    exact sound1300 B hB hF
  have h1301 : mixedVector B (Sum.inr 1301) = Sparse.eval nodeValue1301 (mixedVector B) := by
    change mixedMoment B node1301 node1301Labels = _
    exact sound1301 B hB hF
  have h2958 : mixedVector B (Sum.inr 2958) = Sparse.eval nodeValue2958 (mixedVector B) := by
    change mixedMoment B node2958 node2958Labels = _
    exact sound2958 B hB hF
  have h3100 : mixedVector B (Sum.inr 3100) = Sparse.eval nodeValue3100 (mixedVector B) := by
    change mixedMoment B node3100 node3100Labels = _
    exact sound3100 B hB hF
  have h3122 : mixedVector B (Sum.inr 3122) = Sparse.eval nodeValue3122 (mixedVector B) := by
    change mixedMoment B node3122 node3122Labels = _
    exact sound3122 B hB hF
  simpa only [sourceForm1853, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h599, h600, h603, h1126, h1129, h1235, h1236, h1240, h1299, h1300, h1301, h2958, h3100, h3122, reducedSource1568] using sourceEq1853 B hB

theorem rowSound1568 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1568 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1568, numericCheck1568, reducedZero1568 B hB hF, mul_zero]

theorem reducedZero1569 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1569 (mixedVector B) = 0 := by
  have h4456 : mixedVector B (Sum.inr 4456) = Sparse.eval nodeValue4456 (mixedVector B) := by
    change mixedMoment B node4456 node4456Labels = _
    exact sound4456 B hB hF
  have h4495 : mixedVector B (Sum.inr 4495) = Sparse.eval nodeValue4495 (mixedVector B) := by
    change mixedMoment B node4495 node4495Labels = _
    exact sound4495 B hB hF
  have h4497 : mixedVector B (Sum.inr 4497) = Sparse.eval nodeValue4497 (mixedVector B) := by
    change mixedMoment B node4497 node4497Labels = _
    exact sound4497 B hB hF
  have h4599 : mixedVector B (Sum.inr 4599) = Sparse.eval nodeValue4599 (mixedVector B) := by
    change mixedMoment B node4599 node4599Labels = _
    exact sound4599 B hB hF
  have h4601 : mixedVector B (Sum.inr 4601) = Sparse.eval nodeValue4601 (mixedVector B) := by
    change mixedMoment B node4601 node4601Labels = _
    exact sound4601 B hB hF
  have h4616 : mixedVector B (Sum.inr 4616) = Sparse.eval nodeValue4616 (mixedVector B) := by
    change mixedMoment B node4616 node4616Labels = _
    exact sound4616 B hB hF
  have h4618 : mixedVector B (Sum.inr 4618) = Sparse.eval nodeValue4618 (mixedVector B) := by
    change mixedMoment B node4618 node4618Labels = _
    exact sound4618 B hB hF
  have h4622 : mixedVector B (Sum.inr 4622) = Sparse.eval nodeValue4622 (mixedVector B) := by
    change mixedMoment B node4622 node4622Labels = _
    exact sound4622 B hB hF
  simpa only [sourceForm1854, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4456, h4495, h4497, h4599, h4601, h4616, h4618, h4622, reducedSource1569] using sourceEq1854 B hB

theorem rowSound1569 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1569 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1569, numericCheck1569, reducedZero1569 B hB hF, mul_zero]

theorem reducedZero1570 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1570 (mixedVector B) = 0 := by
  have h1228 : mixedVector B (Sum.inr 1228) = Sparse.eval nodeValue1228 (mixedVector B) := by
    change mixedMoment B node1228 node1228Labels = _
    exact sound1228 B hB hF
  have h2503 : mixedVector B (Sum.inr 2503) = Sparse.eval nodeValue2503 (mixedVector B) := by
    change mixedMoment B node2503 node2503Labels = _
    exact sound2503 B hB hF
  have h2703 : mixedVector B (Sum.inr 2703) = Sparse.eval nodeValue2703 (mixedVector B) := by
    change mixedMoment B node2703 node2703Labels = _
    exact sound2703 B hB hF
  have h2718 : mixedVector B (Sum.inr 2718) = Sparse.eval nodeValue2718 (mixedVector B) := by
    change mixedMoment B node2718 node2718Labels = _
    exact sound2718 B hB hF
  have h2728 : mixedVector B (Sum.inr 2728) = Sparse.eval nodeValue2728 (mixedVector B) := by
    change mixedMoment B node2728 node2728Labels = _
    exact sound2728 B hB hF
  have h4090 : mixedVector B (Sum.inr 4090) = Sparse.eval nodeValue4090 (mixedVector B) := by
    change mixedMoment B node4090 node4090Labels = _
    exact sound4090 B hB hF
  simpa only [sourceForm1855, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1228, h2503, h2703, h2718, h2728, h4090, reducedSource1570] using sourceEq1855 B hB

theorem rowSound1570 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1570 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1570, numericCheck1570, reducedZero1570 B hB hF, mul_zero]

theorem reducedZero1571 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1571 (mixedVector B) = 0 := by
  have h4149 : mixedVector B (Sum.inr 4149) = Sparse.eval nodeValue4149 (mixedVector B) := by
    change mixedMoment B node4149 node4149Labels = _
    exact sound4149 B hB hF
  have h4150 : mixedVector B (Sum.inr 4150) = Sparse.eval nodeValue4150 (mixedVector B) := by
    change mixedMoment B node4150 node4150Labels = _
    exact sound4150 B hB hF
  have h4169 : mixedVector B (Sum.inr 4169) = Sparse.eval nodeValue4169 (mixedVector B) := by
    change mixedMoment B node4169 node4169Labels = _
    exact sound4169 B hB hF
  have h4544 : mixedVector B (Sum.inr 4544) = Sparse.eval nodeValue4544 (mixedVector B) := by
    change mixedMoment B node4544 node4544Labels = _
    exact sound4544 B hB hF
  have h4550 : mixedVector B (Sum.inr 4550) = Sparse.eval nodeValue4550 (mixedVector B) := by
    change mixedMoment B node4550 node4550Labels = _
    exact sound4550 B hB hF
  have h4589 : mixedVector B (Sum.inr 4589) = Sparse.eval nodeValue4589 (mixedVector B) := by
    change mixedMoment B node4589 node4589Labels = _
    exact sound4589 B hB hF
  have h4590 : mixedVector B (Sum.inr 4590) = Sparse.eval nodeValue4590 (mixedVector B) := by
    change mixedMoment B node4590 node4590Labels = _
    exact sound4590 B hB hF
  have h4599 : mixedVector B (Sum.inr 4599) = Sparse.eval nodeValue4599 (mixedVector B) := by
    change mixedMoment B node4599 node4599Labels = _
    exact sound4599 B hB hF
  have h4606 : mixedVector B (Sum.inr 4606) = Sparse.eval nodeValue4606 (mixedVector B) := by
    change mixedMoment B node4606 node4606Labels = _
    exact sound4606 B hB hF
  have h4618 : mixedVector B (Sum.inr 4618) = Sparse.eval nodeValue4618 (mixedVector B) := by
    change mixedMoment B node4618 node4618Labels = _
    exact sound4618 B hB hF
  have h5100 : mixedVector B (Sum.inr 5100) = Sparse.eval nodeValue5100 (mixedVector B) := by
    change mixedMoment B node5100 node5100Labels = _
    exact sound5100 B hB hF
  have h5257 : mixedVector B (Sum.inr 5257) = Sparse.eval nodeValue5257 (mixedVector B) := by
    change mixedMoment B node5257 node5257Labels = _
    exact sound5257 B hB hF
  have h5273 : mixedVector B (Sum.inr 5273) = Sparse.eval nodeValue5273 (mixedVector B) := by
    change mixedMoment B node5273 node5273Labels = _
    exact sound5273 B hB hF
  simpa only [sourceForm1856, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4149, h4150, h4169, h4544, h4550, h4589, h4590, h4599, h4606, h4618, h5100, h5257, h5273, reducedSource1571] using sourceEq1856 B hB

theorem rowSound1571 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1571 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1571, numericCheck1571, reducedZero1571 B hB hF, mul_zero]

theorem reducedZero1572 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1572 (mixedVector B) = 0 := by
  have h577 : mixedVector B (Sum.inr 577) = Sparse.eval nodeValue577 (mixedVector B) := by
    change mixedMoment B node577 node577Labels = _
    exact sound577 B hB hF
  have h578 : mixedVector B (Sum.inr 578) = Sparse.eval nodeValue578 (mixedVector B) := by
    change mixedMoment B node578 node578Labels = _
    exact sound578 B hB hF
  have h597 : mixedVector B (Sum.inr 597) = Sparse.eval nodeValue597 (mixedVector B) := by
    change mixedMoment B node597 node597Labels = _
    exact sound597 B hB hF
  have h1161 : mixedVector B (Sum.inr 1161) = Sparse.eval nodeValue1161 (mixedVector B) := by
    change mixedMoment B node1161 node1161Labels = _
    exact sound1161 B hB hF
  have h1162 : mixedVector B (Sum.inr 1162) = Sparse.eval nodeValue1162 (mixedVector B) := by
    change mixedMoment B node1162 node1162Labels = _
    exact sound1162 B hB hF
  have h1212 : mixedVector B (Sum.inr 1212) = Sparse.eval nodeValue1212 (mixedVector B) := by
    change mixedMoment B node1212 node1212Labels = _
    exact sound1212 B hB hF
  have h1213 : mixedVector B (Sum.inr 1213) = Sparse.eval nodeValue1213 (mixedVector B) := by
    change mixedMoment B node1213 node1213Labels = _
    exact sound1213 B hB hF
  have h1233 : mixedVector B (Sum.inr 1233) = Sparse.eval nodeValue1233 (mixedVector B) := by
    change mixedMoment B node1233 node1233Labels = _
    exact sound1233 B hB hF
  have h1266 : mixedVector B (Sum.inr 1266) = Sparse.eval nodeValue1266 (mixedVector B) := by
    change mixedMoment B node1266 node1266Labels = _
    exact sound1266 B hB hF
  have h1298 : mixedVector B (Sum.inr 1298) = Sparse.eval nodeValue1298 (mixedVector B) := by
    change mixedMoment B node1298 node1298Labels = _
    exact sound1298 B hB hF
  have h2999 : mixedVector B (Sum.inr 2999) = Sparse.eval nodeValue2999 (mixedVector B) := by
    change mixedMoment B node2999 node2999Labels = _
    exact sound2999 B hB hF
  have h3087 : mixedVector B (Sum.inr 3087) = Sparse.eval nodeValue3087 (mixedVector B) := by
    change mixedMoment B node3087 node3087Labels = _
    exact sound3087 B hB hF
  have h3111 : mixedVector B (Sum.inr 3111) = Sparse.eval nodeValue3111 (mixedVector B) := by
    change mixedMoment B node3111 node3111Labels = _
    exact sound3111 B hB hF
  simpa only [sourceForm1857, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h577, h578, h597, h1161, h1162, h1212, h1213, h1233, h1266, h1298, h2999, h3087, h3111, reducedSource1572] using sourceEq1857 B hB

theorem rowSound1572 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1572 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1572, numericCheck1572, reducedZero1572 B hB hF, mul_zero]

theorem reducedZero1573 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1573 (mixedVector B) = 0 := by
  have h1501 : mixedVector B (Sum.inr 1501) = Sparse.eval nodeValue1501 (mixedVector B) := by
    change mixedMoment B node1501 node1501Labels = _
    exact sound1501 B hB hF
  have h1502 : mixedVector B (Sum.inr 1502) = Sparse.eval nodeValue1502 (mixedVector B) := by
    change mixedMoment B node1502 node1502Labels = _
    exact sound1502 B hB hF
  have h1504 : mixedVector B (Sum.inr 1504) = Sparse.eval nodeValue1504 (mixedVector B) := by
    change mixedMoment B node1504 node1504Labels = _
    exact sound1504 B hB hF
  have h3263 : mixedVector B (Sum.inr 3263) = Sparse.eval nodeValue3263 (mixedVector B) := by
    change mixedMoment B node3263 node3263Labels = _
    exact sound3263 B hB hF
  have h3269 : mixedVector B (Sum.inr 3269) = Sparse.eval nodeValue3269 (mixedVector B) := by
    change mixedMoment B node3269 node3269Labels = _
    exact sound3269 B hB hF
  have h3288 : mixedVector B (Sum.inr 3288) = Sparse.eval nodeValue3288 (mixedVector B) := by
    change mixedMoment B node3288 node3288Labels = _
    exact sound3288 B hB hF
  have h3289 : mixedVector B (Sum.inr 3289) = Sparse.eval nodeValue3289 (mixedVector B) := by
    change mixedMoment B node3289 node3289Labels = _
    exact sound3289 B hB hF
  have h3290 : mixedVector B (Sum.inr 3290) = Sparse.eval nodeValue3290 (mixedVector B) := by
    change mixedMoment B node3290 node3290Labels = _
    exact sound3290 B hB hF
  have h3299 : mixedVector B (Sum.inr 3299) = Sparse.eval nodeValue3299 (mixedVector B) := by
    change mixedMoment B node3299 node3299Labels = _
    exact sound3299 B hB hF
  have h3304 : mixedVector B (Sum.inr 3304) = Sparse.eval nodeValue3304 (mixedVector B) := by
    change mixedMoment B node3304 node3304Labels = _
    exact sound3304 B hB hF
  have h3469 : mixedVector B (Sum.inr 3469) = Sparse.eval nodeValue3469 (mixedVector B) := by
    change mixedMoment B node3469 node3469Labels = _
    exact sound3469 B hB hF
  have h3532 : mixedVector B (Sum.inr 3532) = Sparse.eval nodeValue3532 (mixedVector B) := by
    change mixedMoment B node3532 node3532Labels = _
    exact sound3532 B hB hF
  have h3546 : mixedVector B (Sum.inr 3546) = Sparse.eval nodeValue3546 (mixedVector B) := by
    change mixedMoment B node3546 node3546Labels = _
    exact sound3546 B hB hF
  simpa only [sourceForm1858, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1501, h1502, h1504, h3263, h3269, h3288, h3289, h3290, h3299, h3304, h3469, h3532, h3546, reducedSource1573] using sourceEq1858 B hB

theorem rowSound1573 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1573 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1573, numericCheck1573, reducedZero1573 B hB hF, mul_zero]

theorem reducedZero1574 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1574 (mixedVector B) = 0 := by
  have h625 : mixedVector B (Sum.inr 625) = Sparse.eval nodeValue625 (mixedVector B) := by
    change mixedMoment B node625 node625Labels = _
    exact sound625 B hB hF
  have h629 : mixedVector B (Sum.inr 629) = Sparse.eval nodeValue629 (mixedVector B) := by
    change mixedMoment B node629 node629Labels = _
    exact sound629 B hB hF
  have h637 : mixedVector B (Sum.inr 637) = Sparse.eval nodeValue637 (mixedVector B) := by
    change mixedMoment B node637 node637Labels = _
    exact sound637 B hB hF
  have h1235 : mixedVector B (Sum.inr 1235) = Sparse.eval nodeValue1235 (mixedVector B) := by
    change mixedMoment B node1235 node1235Labels = _
    exact sound1235 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1859, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h625, h629, h637, h1235, h4091, reducedSource1574] using sourceEq1859 B hB

theorem rowSound1574 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1574 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1574, numericCheck1574, reducedZero1574 B hB hF, mul_zero]

theorem reducedZero1575 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1575 (mixedVector B) = 0 := by
  have h4139 : mixedVector B (Sum.inr 4139) = Sparse.eval nodeValue4139 (mixedVector B) := by
    change mixedMoment B node4139 node4139Labels = _
    exact sound4139 B hB hF
  have h4143 : mixedVector B (Sum.inr 4143) = Sparse.eval nodeValue4143 (mixedVector B) := by
    change mixedMoment B node4143 node4143Labels = _
    exact sound4143 B hB hF
  have h4171 : mixedVector B (Sum.inr 4171) = Sparse.eval nodeValue4171 (mixedVector B) := by
    change mixedMoment B node4171 node4171Labels = _
    exact sound4171 B hB hF
  have h4513 : mixedVector B (Sum.inr 4513) = Sparse.eval nodeValue4513 (mixedVector B) := by
    change mixedMoment B node4513 node4513Labels = _
    exact sound4513 B hB hF
  have h4516 : mixedVector B (Sum.inr 4516) = Sparse.eval nodeValue4516 (mixedVector B) := by
    change mixedMoment B node4516 node4516Labels = _
    exact sound4516 B hB hF
  have h4581 : mixedVector B (Sum.inr 4581) = Sparse.eval nodeValue4581 (mixedVector B) := by
    change mixedMoment B node4581 node4581Labels = _
    exact sound4581 B hB hF
  have h4601 : mixedVector B (Sum.inr 4601) = Sparse.eval nodeValue4601 (mixedVector B) := by
    change mixedMoment B node4601 node4601Labels = _
    exact sound4601 B hB hF
  have h4602 : mixedVector B (Sum.inr 4602) = Sparse.eval nodeValue4602 (mixedVector B) := by
    change mixedMoment B node4602 node4602Labels = _
    exact sound4602 B hB hF
  have h4606 : mixedVector B (Sum.inr 4606) = Sparse.eval nodeValue4606 (mixedVector B) := by
    change mixedMoment B node4606 node4606Labels = _
    exact sound4606 B hB hF
  have h4622 : mixedVector B (Sum.inr 4622) = Sparse.eval nodeValue4622 (mixedVector B) := by
    change mixedMoment B node4622 node4622Labels = _
    exact sound4622 B hB hF
  have h5202 : mixedVector B (Sum.inr 5202) = Sparse.eval nodeValue5202 (mixedVector B) := by
    change mixedMoment B node5202 node5202Labels = _
    exact sound5202 B hB hF
  have h5283 : mixedVector B (Sum.inr 5283) = Sparse.eval nodeValue5283 (mixedVector B) := by
    change mixedMoment B node5283 node5283Labels = _
    exact sound5283 B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292 B hB hF
  simpa only [sourceForm1860, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4139, h4143, h4171, h4513, h4516, h4581, h4601, h4602, h4606, h4622, h5202, h5283, h5292, reducedSource1575] using sourceEq1860 B hB

theorem rowSound1575 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1575 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1575, numericCheck1575, reducedZero1575 B hB hF, mul_zero]

theorem reducedZero1576 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1576 (mixedVector B) = 0 := by
  have h567 : mixedVector B (Sum.inr 567) = Sparse.eval nodeValue567 (mixedVector B) := by
    change mixedMoment B node567 node567Labels = _
    exact sound567 B hB hF
  have h571 : mixedVector B (Sum.inr 571) = Sparse.eval nodeValue571 (mixedVector B) := by
    change mixedMoment B node571 node571Labels = _
    exact sound571 B hB hF
  have h599 : mixedVector B (Sum.inr 599) = Sparse.eval nodeValue599 (mixedVector B) := by
    change mixedMoment B node599 node599Labels = _
    exact sound599 B hB hF
  have h1097 : mixedVector B (Sum.inr 1097) = Sparse.eval nodeValue1097 (mixedVector B) := by
    change mixedMoment B node1097 node1097Labels = _
    exact sound1097 B hB hF
  have h1100 : mixedVector B (Sum.inr 1100) = Sparse.eval nodeValue1100 (mixedVector B) := by
    change mixedMoment B node1100 node1100Labels = _
    exact sound1100 B hB hF
  have h1200 : mixedVector B (Sum.inr 1200) = Sparse.eval nodeValue1200 (mixedVector B) := by
    change mixedMoment B node1200 node1200Labels = _
    exact sound1200 B hB hF
  have h1235 : mixedVector B (Sum.inr 1235) = Sparse.eval nodeValue1235 (mixedVector B) := by
    change mixedMoment B node1235 node1235Labels = _
    exact sound1235 B hB hF
  have h1236 : mixedVector B (Sum.inr 1236) = Sparse.eval nodeValue1236 (mixedVector B) := by
    change mixedMoment B node1236 node1236Labels = _
    exact sound1236 B hB hF
  have h1240 : mixedVector B (Sum.inr 1240) = Sparse.eval nodeValue1240 (mixedVector B) := by
    change mixedMoment B node1240 node1240Labels = _
    exact sound1240 B hB hF
  have h1299 : mixedVector B (Sum.inr 1299) = Sparse.eval nodeValue1299 (mixedVector B) := by
    change mixedMoment B node1299 node1299Labels = _
    exact sound1299 B hB hF
  have h2880 : mixedVector B (Sum.inr 2880) = Sparse.eval nodeValue2880 (mixedVector B) := by
    change mixedMoment B node2880 node2880Labels = _
    exact sound2880 B hB hF
  have h3076 : mixedVector B (Sum.inr 3076) = Sparse.eval nodeValue3076 (mixedVector B) := by
    change mixedMoment B node3076 node3076Labels = _
    exact sound3076 B hB hF
  have h3100 : mixedVector B (Sum.inr 3100) = Sparse.eval nodeValue3100 (mixedVector B) := by
    change mixedMoment B node3100 node3100Labels = _
    exact sound3100 B hB hF
  simpa only [sourceForm1861, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h567, h571, h599, h1097, h1100, h1200, h1235, h1236, h1240, h1299, h2880, h3076, h3100, reducedSource1576] using sourceEq1861 B hB

theorem rowSound1576 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1576 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1576, numericCheck1576, reducedZero1576 B hB hF, mul_zero]

theorem reducedZero1577 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1577 (mixedVector B) = 0 := by
  have h1183 : mixedVector B (Sum.inr 1183) = Sparse.eval nodeValue1183 (mixedVector B) := by
    change mixedMoment B node1183 node1183Labels = _
    exact sound1183 B hB hF
  have h2398 : mixedVector B (Sum.inr 2398) = Sparse.eval nodeValue2398 (mixedVector B) := by
    change mixedMoment B node2398 node2398Labels = _
    exact sound2398 B hB hF
  have h2669 : mixedVector B (Sum.inr 2669) = Sparse.eval nodeValue2669 (mixedVector B) := by
    change mixedMoment B node2669 node2669Labels = _
    exact sound2669 B hB hF
  have h2676 : mixedVector B (Sum.inr 2676) = Sparse.eval nodeValue2676 (mixedVector B) := by
    change mixedMoment B node2676 node2676Labels = _
    exact sound2676 B hB hF
  have h2684 : mixedVector B (Sum.inr 2684) = Sparse.eval nodeValue2684 (mixedVector B) := by
    change mixedMoment B node2684 node2684Labels = _
    exact sound2684 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm1863, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1183, h2398, h2669, h2676, h2684, h4088, reducedSource1577] using sourceEq1863 B hB

theorem rowSound1577 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1577 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1577, numericCheck1577, reducedZero1577 B hB hF, mul_zero]

theorem reducedZero1578 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1578 (mixedVector B) = 0 := by
  have h1187 : mixedVector B (Sum.inr 1187) = Sparse.eval nodeValue1187 (mixedVector B) := by
    change mixedMoment B node1187 node1187Labels = _
    exact sound1187 B hB hF
  have h2402 : mixedVector B (Sum.inr 2402) = Sparse.eval nodeValue2402 (mixedVector B) := by
    change mixedMoment B node2402 node2402Labels = _
    exact sound2402 B hB hF
  have h2671 : mixedVector B (Sum.inr 2671) = Sparse.eval nodeValue2671 (mixedVector B) := by
    change mixedMoment B node2671 node2671Labels = _
    exact sound2671 B hB hF
  have h4087 : mixedVector B (Sum.inr 4087) = Sparse.eval nodeValue4087 (mixedVector B) := by
    change mixedMoment B node4087 node4087Labels = _
    exact sound4087 B hB hF
  simpa only [sourceForm1864, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1187, h2402, h2671, h4087, reducedSource1578] using sourceEq1864 B hB

theorem rowSound1578 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1578 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1578, numericCheck1578, reducedZero1578 B hB hF, mul_zero]

theorem reducedZero1579 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1579 (mixedVector B) = 0 := by
  have h1100 : mixedVector B (Sum.inr 1100) = Sparse.eval nodeValue1100 (mixedVector B) := by
    change mixedMoment B node1100 node1100Labels = _
    exact sound1100 B hB hF
  have h1187 : mixedVector B (Sum.inr 1187) = Sparse.eval nodeValue1187 (mixedVector B) := by
    change mixedMoment B node1187 node1187Labels = _
    exact sound1187 B hB hF
  have h2402 : mixedVector B (Sum.inr 2402) = Sparse.eval nodeValue2402 (mixedVector B) := by
    change mixedMoment B node2402 node2402Labels = _
    exact sound2402 B hB hF
  have h4087 : mixedVector B (Sum.inr 4087) = Sparse.eval nodeValue4087 (mixedVector B) := by
    change mixedMoment B node4087 node4087Labels = _
    exact sound4087 B hB hF
  simpa only [sourceForm1865, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1100, h1187, h2402, h4087, reducedSource1579] using sourceEq1865 B hB

theorem rowSound1579 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1579 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1579, numericCheck1579, reducedZero1579 B hB hF, mul_zero]

theorem reducedZero1580 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1580 (mixedVector B) = 0 := by
  have h1052 : mixedVector B (Sum.inr 1052) = Sparse.eval nodeValue1052 (mixedVector B) := by
    change mixedMoment B node1052 node1052Labels = _
    exact sound1052 B hB hF
  have h2127 : mixedVector B (Sum.inr 2127) = Sparse.eval nodeValue2127 (mixedVector B) := by
    change mixedMoment B node2127 node2127Labels = _
    exact sound2127 B hB hF
  have h2214 : mixedVector B (Sum.inr 2214) = Sparse.eval nodeValue2214 (mixedVector B) := by
    change mixedMoment B node2214 node2214Labels = _
    exact sound2214 B hB hF
  have h2250 : mixedVector B (Sum.inr 2250) = Sparse.eval nodeValue2250 (mixedVector B) := by
    change mixedMoment B node2250 node2250Labels = _
    exact sound2250 B hB hF
  have h2275 : mixedVector B (Sum.inr 2275) = Sparse.eval nodeValue2275 (mixedVector B) := by
    change mixedMoment B node2275 node2275Labels = _
    exact sound2275 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1867, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1052, h2127, h2214, h2250, h2275, h4080, reducedSource1580] using sourceEq1867 B hB

theorem rowSound1580 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1580 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1580, numericCheck1580, reducedZero1580 B hB hF, mul_zero]

theorem reducedZero1581 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1581 (mixedVector B) = 0 := by
  have h1032 : mixedVector B (Sum.inr 1032) = Sparse.eval nodeValue1032 (mixedVector B) := by
    change mixedMoment B node1032 node1032Labels = _
    exact sound1032 B hB hF
  have h2098 : mixedVector B (Sum.inr 2098) = Sparse.eval nodeValue2098 (mixedVector B) := by
    change mixedMoment B node2098 node2098Labels = _
    exact sound2098 B hB hF
  have h2202 : mixedVector B (Sum.inr 2202) = Sparse.eval nodeValue2202 (mixedVector B) := by
    change mixedMoment B node2202 node2202Labels = _
    exact sound2202 B hB hF
  have h2240 : mixedVector B (Sum.inr 2240) = Sparse.eval nodeValue2240 (mixedVector B) := by
    change mixedMoment B node2240 node2240Labels = _
    exact sound2240 B hB hF
  have h2250 : mixedVector B (Sum.inr 2250) = Sparse.eval nodeValue2250 (mixedVector B) := by
    change mixedMoment B node2250 node2250Labels = _
    exact sound2250 B hB hF
  have h2260 : mixedVector B (Sum.inr 2260) = Sparse.eval nodeValue2260 (mixedVector B) := by
    change mixedMoment B node2260 node2260Labels = _
    exact sound2260 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1868, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1032, h2098, h2202, h2240, h2250, h2260, h4080, reducedSource1581] using sourceEq1868 B hB

theorem rowSound1581 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1581 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1581, numericCheck1581, reducedZero1581 B hB hF, mul_zero]

theorem reducedZero1582 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1582 (mixedVector B) = 0 := by
  have h1034 : mixedVector B (Sum.inr 1034) = Sparse.eval nodeValue1034 (mixedVector B) := by
    change mixedMoment B node1034 node1034Labels = _
    exact sound1034 B hB hF
  have h2100 : mixedVector B (Sum.inr 2100) = Sparse.eval nodeValue2100 (mixedVector B) := by
    change mixedMoment B node2100 node2100Labels = _
    exact sound2100 B hB hF
  have h2204 : mixedVector B (Sum.inr 2204) = Sparse.eval nodeValue2204 (mixedVector B) := by
    change mixedMoment B node2204 node2204Labels = _
    exact sound2204 B hB hF
  have h2241 : mixedVector B (Sum.inr 2241) = Sparse.eval nodeValue2241 (mixedVector B) := by
    change mixedMoment B node2241 node2241Labels = _
    exact sound2241 B hB hF
  have h4079 : mixedVector B (Sum.inr 4079) = Sparse.eval nodeValue4079 (mixedVector B) := by
    change mixedMoment B node4079 node4079Labels = _
    exact sound4079 B hB hF
  simpa only [sourceForm1869, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1034, h2100, h2204, h2241, h4079, reducedSource1582] using sourceEq1869 B hB

theorem rowSound1582 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1582 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1582, numericCheck1582, reducedZero1582 B hB hF, mul_zero]

theorem reducedZero1583 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1583 (mixedVector B) = 0 := by
  have h732 : mixedVector B (Sum.inr 732) = Sparse.eval nodeValue732 (mixedVector B) := by
    change mixedMoment B node732 node732Labels = _
    exact sound732 B hB hF
  have h736 : mixedVector B (Sum.inr 736) = Sparse.eval nodeValue736 (mixedVector B) := by
    change mixedMoment B node736 node736Labels = _
    exact sound736 B hB hF
  have h805 : mixedVector B (Sum.inr 805) = Sparse.eval nodeValue805 (mixedVector B) := by
    change mixedMoment B node805 node805Labels = _
    exact sound805 B hB hF
  have h1644 : mixedVector B (Sum.inr 1644) = Sparse.eval nodeValue1644 (mixedVector B) := by
    change mixedMoment B node1644 node1644Labels = _
    exact sound1644 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1870, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h732, h736, h805, h1644, h4068, reducedSource1583] using sourceEq1870 B hB

theorem rowSound1583 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1583 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1583, numericCheck1583, reducedZero1583 B hB hF, mul_zero]

theorem sourceRowsAt1568 : MixedData.sourceRows (1568 : Fin 2425) =
    MixedData.row1568 := by decide +kernel

theorem sourceRowsAt1569 : MixedData.sourceRows (1569 : Fin 2425) =
    MixedData.row1569 := by decide +kernel

theorem sourceRowsAt1570 : MixedData.sourceRows (1570 : Fin 2425) =
    MixedData.row1570 := by decide +kernel

theorem sourceRowsAt1571 : MixedData.sourceRows (1571 : Fin 2425) =
    MixedData.row1571 := by decide +kernel

theorem sourceRowsAt1572 : MixedData.sourceRows (1572 : Fin 2425) =
    MixedData.row1572 := by decide +kernel

theorem sourceRowsAt1573 : MixedData.sourceRows (1573 : Fin 2425) =
    MixedData.row1573 := by decide +kernel

theorem sourceRowsAt1574 : MixedData.sourceRows (1574 : Fin 2425) =
    MixedData.row1574 := by decide +kernel

theorem sourceRowsAt1575 : MixedData.sourceRows (1575 : Fin 2425) =
    MixedData.row1575 := by decide +kernel

theorem sourceRowsAt1576 : MixedData.sourceRows (1576 : Fin 2425) =
    MixedData.row1576 := by decide +kernel

theorem sourceRowsAt1577 : MixedData.sourceRows (1577 : Fin 2425) =
    MixedData.row1577 := by decide +kernel

theorem sourceRowsAt1578 : MixedData.sourceRows (1578 : Fin 2425) =
    MixedData.row1578 := by decide +kernel

theorem sourceRowsAt1579 : MixedData.sourceRows (1579 : Fin 2425) =
    MixedData.row1579 := by decide +kernel

theorem sourceRowsAt1580 : MixedData.sourceRows (1580 : Fin 2425) =
    MixedData.row1580 := by decide +kernel

theorem sourceRowsAt1581 : MixedData.sourceRows (1581 : Fin 2425) =
    MixedData.row1581 := by decide +kernel

theorem sourceRowsAt1582 : MixedData.sourceRows (1582 : Fin 2425) =
    MixedData.row1582 := by decide +kernel

theorem sourceRowsAt1583 : MixedData.sourceRows (1583 : Fin 2425) =
    MixedData.row1583 := by decide +kernel

theorem chunkSound98 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 98) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1568 ∨ k.val = 1569 ∨ k.val = 1570 ∨ k.val = 1571 ∨ k.val = 1572 ∨ k.val = 1573 ∨ k.val = 1574 ∨ k.val = 1575 ∨ k.val = 1576 ∨ k.val = 1577 ∨ k.val = 1578 ∨ k.val = 1579 ∨ k.val = 1580 ∨ k.val = 1581 ∨ k.val = 1582 ∨ k.val = 1583 := by omega
  rcases heq with h1568 | h1569 | h1570 | h1571 | h1572 | h1573 | h1574 | h1575 | h1576 | h1577 | h1578 | h1579 | h1580 | h1581 | h1582 | h1583
  · have he : k = (1568 : Fin 2425) := Fin.ext h1568
    subst k
    rw [sourceRowsAt1568]
    exact rowSound1568 B hB hF
  · have he : k = (1569 : Fin 2425) := Fin.ext h1569
    subst k
    rw [sourceRowsAt1569]
    exact rowSound1569 B hB hF
  · have he : k = (1570 : Fin 2425) := Fin.ext h1570
    subst k
    rw [sourceRowsAt1570]
    exact rowSound1570 B hB hF
  · have he : k = (1571 : Fin 2425) := Fin.ext h1571
    subst k
    rw [sourceRowsAt1571]
    exact rowSound1571 B hB hF
  · have he : k = (1572 : Fin 2425) := Fin.ext h1572
    subst k
    rw [sourceRowsAt1572]
    exact rowSound1572 B hB hF
  · have he : k = (1573 : Fin 2425) := Fin.ext h1573
    subst k
    rw [sourceRowsAt1573]
    exact rowSound1573 B hB hF
  · have he : k = (1574 : Fin 2425) := Fin.ext h1574
    subst k
    rw [sourceRowsAt1574]
    exact rowSound1574 B hB hF
  · have he : k = (1575 : Fin 2425) := Fin.ext h1575
    subst k
    rw [sourceRowsAt1575]
    exact rowSound1575 B hB hF
  · have he : k = (1576 : Fin 2425) := Fin.ext h1576
    subst k
    rw [sourceRowsAt1576]
    exact rowSound1576 B hB hF
  · have he : k = (1577 : Fin 2425) := Fin.ext h1577
    subst k
    rw [sourceRowsAt1577]
    exact rowSound1577 B hB hF
  · have he : k = (1578 : Fin 2425) := Fin.ext h1578
    subst k
    rw [sourceRowsAt1578]
    exact rowSound1578 B hB hF
  · have he : k = (1579 : Fin 2425) := Fin.ext h1579
    subst k
    rw [sourceRowsAt1579]
    exact rowSound1579 B hB hF
  · have he : k = (1580 : Fin 2425) := Fin.ext h1580
    subst k
    rw [sourceRowsAt1580]
    exact rowSound1580 B hB hF
  · have he : k = (1581 : Fin 2425) := Fin.ext h1581
    subst k
    rw [sourceRowsAt1581]
    exact rowSound1581 B hB hF
  · have he : k = (1582 : Fin 2425) := Fin.ext h1582
    subst k
    rw [sourceRowsAt1582]
    exact rowSound1582 B hB hF
  · have he : k = (1583 : Fin 2425) := Fin.ext h1583
    subst k
    rw [sourceRowsAt1583]
    exact rowSound1583 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
