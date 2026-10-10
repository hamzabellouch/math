import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources36

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero992 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource992 (mixedVector B) = 0 := by
  have h5398 : mixedVector B (Sum.inr 5398) = Sparse.eval nodeValue5398 (mixedVector B) := by
    change mixedMoment B node5398 node5398Labels = _
    exact sound5398 B hB hF
  have h5403 : mixedVector B (Sum.inr 5403) = Sparse.eval nodeValue5403 (mixedVector B) := by
    change mixedMoment B node5403 node5403Labels = _
    exact sound5403 B hB hF
  have h5415 : mixedVector B (Sum.inr 5415) = Sparse.eval nodeValue5415 (mixedVector B) := by
    change mixedMoment B node5415 node5415Labels = _
    exact sound5415 B hB hF
  have h5439 : mixedVector B (Sum.inr 5439) = Sparse.eval nodeValue5439 (mixedVector B) := by
    change mixedMoment B node5439 node5439Labels = _
    exact sound5439 B hB hF
  have h5448 : mixedVector B (Sum.inr 5448) = Sparse.eval nodeValue5448 (mixedVector B) := by
    change mixedMoment B node5448 node5448Labels = _
    exact sound5448 B hB hF
  have h5491 : mixedVector B (Sum.inr 5491) = Sparse.eval nodeValue5491 (mixedVector B) := by
    change mixedMoment B node5491 node5491Labels = _
    exact sound5491 B hB hF
  simpa only [sourceForm1140, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5398, h5403, h5415, h5439, h5448, h5491, reducedSource992] using sourceEq1140 B hB

theorem rowSound992 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row992 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck992, numericCheck992, reducedZero992 B hB hF, mul_zero]

theorem reducedZero993 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource993 (mixedVector B) = 0 := by
  have h4090 : mixedVector B (Sum.inr 4090) = Sparse.eval nodeValue4090 (mixedVector B) := by
    change mixedMoment B node4090 node4090Labels = _
    exact sound4090 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  have h4096 : mixedVector B (Sum.inr 4096) = Sparse.eval nodeValue4096 (mixedVector B) := by
    change mixedMoment B node4096 node4096Labels = _
    exact sound4096 B hB hF
  simpa only [sourceForm1141, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4090, h4091, h4096, reducedSource993] using sourceEq1141 B hB

theorem rowSound993 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row993 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck993, numericCheck993, reducedZero993 B hB hF, mul_zero]

theorem reducedZero994 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource994 (mixedVector B) = 0 := by
  have h617 : mixedVector B (Sum.inr 617) = Sparse.eval nodeValue617 (mixedVector B) := by
    change mixedMoment B node617 node617Labels = _
    exact sound617 B hB hF
  have h936 : mixedVector B (Sum.inr 936) = Sparse.eval nodeValue936 (mixedVector B) := by
    change mixedMoment B node936 node936Labels = _
    exact sound936 B hB hF
  have h1064 : mixedVector B (Sum.inr 1064) = Sparse.eval nodeValue1064 (mixedVector B) := by
    change mixedMoment B node1064 node1064Labels = _
    exact sound1064 B hB hF
  have h1091 : mixedVector B (Sum.inr 1091) = Sparse.eval nodeValue1091 (mixedVector B) := by
    change mixedMoment B node1091 node1091Labels = _
    exact sound1091 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1142, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h617, h936, h1064, h1091, h4084, reducedSource994] using sourceEq1142 B hB

theorem rowSound994 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row994 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck994, numericCheck994, reducedZero994 B hB hF, mul_zero]

theorem reducedZero995 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource995 (mixedVector B) = 0 := by
  have h862 : mixedVector B (Sum.inr 862) = Sparse.eval nodeValue862 (mixedVector B) := by
    change mixedMoment B node862 node862Labels = _
    exact sound862 B hB hF
  have h1629 : mixedVector B (Sum.inr 1629) = Sparse.eval nodeValue1629 (mixedVector B) := by
    change mixedMoment B node1629 node1629Labels = _
    exact sound1629 B hB hF
  have h1752 : mixedVector B (Sum.inr 1752) = Sparse.eval nodeValue1752 (mixedVector B) := by
    change mixedMoment B node1752 node1752Labels = _
    exact sound1752 B hB hF
  have h1757 : mixedVector B (Sum.inr 1757) = Sparse.eval nodeValue1757 (mixedVector B) := by
    change mixedMoment B node1757 node1757Labels = _
    exact sound1757 B hB hF
  have h4072 : mixedVector B (Sum.inr 4072) = Sparse.eval nodeValue4072 (mixedVector B) := by
    change mixedMoment B node4072 node4072Labels = _
    exact sound4072 B hB hF
  simpa only [sourceForm1143, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h862, h1629, h1752, h1757, h4072, reducedSource995] using sourceEq1143 B hB

theorem rowSound995 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row995 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck995, numericCheck995, reducedZero995 B hB hF, mul_zero]

theorem reducedZero996 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource996 (mixedVector B) = 0 := by
  have h1749 : mixedVector B (Sum.inr 1749) = Sparse.eval nodeValue1749 (mixedVector B) := by
    change mixedMoment B node1749 node1749Labels = _
    exact sound1749 B hB hF
  have h1752 : mixedVector B (Sum.inr 1752) = Sparse.eval nodeValue1752 (mixedVector B) := by
    change mixedMoment B node1752 node1752Labels = _
    exact sound1752 B hB hF
  have h1757 : mixedVector B (Sum.inr 1757) = Sparse.eval nodeValue1757 (mixedVector B) := by
    change mixedMoment B node1757 node1757Labels = _
    exact sound1757 B hB hF
  have h4072 : mixedVector B (Sum.inr 4072) = Sparse.eval nodeValue4072 (mixedVector B) := by
    change mixedMoment B node4072 node4072Labels = _
    exact sound4072 B hB hF
  simpa only [sourceForm1145, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1749, h1752, h1757, h4072, reducedSource996] using sourceEq1145 B hB

theorem rowSound996 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row996 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck996, numericCheck996, reducedZero996 B hB hF, mul_zero]

theorem reducedZero997 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource997 (mixedVector B) = 0 := by
  have h587 : mixedVector B (Sum.inr 587) = Sparse.eval nodeValue587 (mixedVector B) := by
    change mixedMoment B node587 node587Labels = _
    exact sound587 B hB hF
  have h911 : mixedVector B (Sum.inr 911) = Sparse.eval nodeValue911 (mixedVector B) := by
    change mixedMoment B node911 node911Labels = _
    exact sound911 B hB hF
  have h951 : mixedVector B (Sum.inr 951) = Sparse.eval nodeValue951 (mixedVector B) := by
    change mixedMoment B node951 node951Labels = _
    exact sound951 B hB hF
  have h1027 : mixedVector B (Sum.inr 1027) = Sparse.eval nodeValue1027 (mixedVector B) := by
    change mixedMoment B node1027 node1027Labels = _
    exact sound1027 B hB hF
  have h1046 : mixedVector B (Sum.inr 1046) = Sparse.eval nodeValue1046 (mixedVector B) := by
    change mixedMoment B node1046 node1046Labels = _
    exact sound1046 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1147, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h587, h911, h951, h1027, h1046, h4083, reducedSource997] using sourceEq1147 B hB

theorem rowSound997 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row997 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck997, numericCheck997, reducedZero997 B hB hF, mul_zero]

theorem reducedZero998 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource998 (mixedVector B) = 0 := by
  have h849 : mixedVector B (Sum.inr 849) = Sparse.eval nodeValue849 (mixedVector B) := by
    change mixedMoment B node849 node849Labels = _
    exact sound849 B hB hF
  have h1615 : mixedVector B (Sum.inr 1615) = Sparse.eval nodeValue1615 (mixedVector B) := by
    change mixedMoment B node1615 node1615Labels = _
    exact sound1615 B hB hF
  have h1749 : mixedVector B (Sum.inr 1749) = Sparse.eval nodeValue1749 (mixedVector B) := by
    change mixedMoment B node1749 node1749Labels = _
    exact sound1749 B hB hF
  have h1752 : mixedVector B (Sum.inr 1752) = Sparse.eval nodeValue1752 (mixedVector B) := by
    change mixedMoment B node1752 node1752Labels = _
    exact sound1752 B hB hF
  have h4072 : mixedVector B (Sum.inr 4072) = Sparse.eval nodeValue4072 (mixedVector B) := by
    change mixedMoment B node4072 node4072Labels = _
    exact sound4072 B hB hF
  simpa only [sourceForm1148, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h849, h1615, h1749, h1752, h4072, reducedSource998] using sourceEq1148 B hB

theorem rowSound998 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row998 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck998, numericCheck998, reducedZero998 B hB hF, mul_zero]

theorem reducedZero999 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource999 (mixedVector B) = 0 := by
  have h794 : mixedVector B (Sum.inr 794) = Sparse.eval nodeValue794 (mixedVector B) := by
    change mixedMoment B node794 node794Labels = _
    exact sound794 B hB hF
  have h797 : mixedVector B (Sum.inr 797) = Sparse.eval nodeValue797 (mixedVector B) := by
    change mixedMoment B node797 node797Labels = _
    exact sound797 B hB hF
  have h813 : mixedVector B (Sum.inr 813) = Sparse.eval nodeValue813 (mixedVector B) := by
    change mixedMoment B node813 node813Labels = _
    exact sound813 B hB hF
  have h828 : mixedVector B (Sum.inr 828) = Sparse.eval nodeValue828 (mixedVector B) := by
    change mixedMoment B node828 node828Labels = _
    exact sound828 B hB hF
  have h1716 : mixedVector B (Sum.inr 1716) = Sparse.eval nodeValue1716 (mixedVector B) := by
    change mixedMoment B node1716 node1716Labels = _
    exact sound1716 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1150, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h794, h797, h813, h828, h1716, h4069, reducedSource999] using sourceEq1150 B hB

theorem rowSound999 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row999 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck999, numericCheck999, reducedZero999 B hB hF, mul_zero]

theorem reducedZero1000 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1000 (mixedVector B) = 0 := by
  have h633 : mixedVector B (Sum.inr 633) = Sparse.eval nodeValue633 (mixedVector B) := by
    change mixedMoment B node633 node633Labels = _
    exact sound633 B hB hF
  have h1115 : mixedVector B (Sum.inr 1115) = Sparse.eval nodeValue1115 (mixedVector B) := by
    change mixedMoment B node1115 node1115Labels = _
    exact sound1115 B hB hF
  have h1140 : mixedVector B (Sum.inr 1140) = Sparse.eval nodeValue1140 (mixedVector B) := by
    change mixedMoment B node1140 node1140Labels = _
    exact sound1140 B hB hF
  have h1221 : mixedVector B (Sum.inr 1221) = Sparse.eval nodeValue1221 (mixedVector B) := by
    change mixedMoment B node1221 node1221Labels = _
    exact sound1221 B hB hF
  have h1242 : mixedVector B (Sum.inr 1242) = Sparse.eval nodeValue1242 (mixedVector B) := by
    change mixedMoment B node1242 node1242Labels = _
    exact sound1242 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1152, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h633, h1115, h1140, h1221, h1242, h4092, reducedSource1000] using sourceEq1152 B hB

theorem rowSound1000 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1000 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1000, numericCheck1000, reducedZero1000 B hB hF, mul_zero]

theorem reducedZero1001 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1001 (mixedVector B) = 0 := by
  have h1615 : mixedVector B (Sum.inr 1615) = Sparse.eval nodeValue1615 (mixedVector B) := by
    change mixedMoment B node1615 node1615Labels = _
    exact sound1615 B hB hF
  have h1620 : mixedVector B (Sum.inr 1620) = Sparse.eval nodeValue1620 (mixedVector B) := by
    change mixedMoment B node1620 node1620Labels = _
    exact sound1620 B hB hF
  have h1629 : mixedVector B (Sum.inr 1629) = Sparse.eval nodeValue1629 (mixedVector B) := by
    change mixedMoment B node1629 node1629Labels = _
    exact sound1629 B hB hF
  have h1752 : mixedVector B (Sum.inr 1752) = Sparse.eval nodeValue1752 (mixedVector B) := by
    change mixedMoment B node1752 node1752Labels = _
    exact sound1752 B hB hF
  have h3298 : mixedVector B (Sum.inr 3298) = Sparse.eval nodeValue3298 (mixedVector B) := by
    change mixedMoment B node3298 node3298Labels = _
    exact sound3298 B hB hF
  have h4072 : mixedVector B (Sum.inr 4072) = Sparse.eval nodeValue4072 (mixedVector B) := by
    change mixedMoment B node4072 node4072Labels = _
    exact sound4072 B hB hF
  simpa only [sourceForm1153, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1615, h1620, h1629, h1752, h3298, h4072, reducedSource1001] using sourceEq1153 B hB

theorem rowSound1001 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1001 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1001, numericCheck1001, reducedZero1001 B hB hF, mul_zero]

theorem reducedZero1002 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1002 (mixedVector B) = 0 := by
  have h1752 : mixedVector B (Sum.inr 1752) = Sparse.eval nodeValue1752 (mixedVector B) := by
    change mixedMoment B node1752 node1752Labels = _
    exact sound1752 B hB hF
  have h3298 : mixedVector B (Sum.inr 3298) = Sparse.eval nodeValue3298 (mixedVector B) := by
    change mixedMoment B node3298 node3298Labels = _
    exact sound3298 B hB hF
  have h3313 : mixedVector B (Sum.inr 3313) = Sparse.eval nodeValue3313 (mixedVector B) := by
    change mixedMoment B node3313 node3313Labels = _
    exact sound3313 B hB hF
  have h4072 : mixedVector B (Sum.inr 4072) = Sparse.eval nodeValue4072 (mixedVector B) := by
    change mixedMoment B node4072 node4072Labels = _
    exact sound4072 B hB hF
  simpa only [sourceForm1154, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1752, h3298, h3313, h4072, reducedSource1002] using sourceEq1154 B hB

theorem rowSound1002 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1002 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1002, numericCheck1002, reducedZero1002 B hB hF, mul_zero]

theorem reducedZero1003 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1003 (mixedVector B) = 0 := by
  have h989 : mixedVector B (Sum.inr 989) = Sparse.eval nodeValue989 (mixedVector B) := by
    change mixedMoment B node989 node989Labels = _
    exact sound989 B hB hF
  have h994 : mixedVector B (Sum.inr 994) = Sparse.eval nodeValue994 (mixedVector B) := by
    change mixedMoment B node994 node994Labels = _
    exact sound994 B hB hF
  have h1009 : mixedVector B (Sum.inr 1009) = Sparse.eval nodeValue1009 (mixedVector B) := by
    change mixedMoment B node1009 node1009Labels = _
    exact sound1009 B hB hF
  have h1055 : mixedVector B (Sum.inr 1055) = Sparse.eval nodeValue1055 (mixedVector B) := by
    change mixedMoment B node1055 node1055Labels = _
    exact sound1055 B hB hF
  have h2218 : mixedVector B (Sum.inr 2218) = Sparse.eval nodeValue2218 (mixedVector B) := by
    change mixedMoment B node2218 node2218Labels = _
    exact sound2218 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1155, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h989, h994, h1009, h1055, h2218, h4082, reducedSource1003] using sourceEq1155 B hB

theorem rowSound1003 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1003 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1003, numericCheck1003, reducedZero1003 B hB hF, mul_zero]

theorem reducedZero1004 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1004 (mixedVector B) = 0 := by
  have h994 : mixedVector B (Sum.inr 994) = Sparse.eval nodeValue994 (mixedVector B) := by
    change mixedMoment B node994 node994Labels = _
    exact sound994 B hB hF
  have h1179 : mixedVector B (Sum.inr 1179) = Sparse.eval nodeValue1179 (mixedVector B) := by
    change mixedMoment B node1179 node1179Labels = _
    exact sound1179 B hB hF
  have h1190 : mixedVector B (Sum.inr 1190) = Sparse.eval nodeValue1190 (mixedVector B) := by
    change mixedMoment B node1190 node1190Labels = _
    exact sound1190 B hB hF
  have h1258 : mixedVector B (Sum.inr 1258) = Sparse.eval nodeValue1258 (mixedVector B) := by
    change mixedMoment B node1258 node1258Labels = _
    exact sound1258 B hB hF
  have h2218 : mixedVector B (Sum.inr 2218) = Sparse.eval nodeValue2218 (mixedVector B) := by
    change mixedMoment B node2218 node2218Labels = _
    exact sound2218 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1156, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h994, h1179, h1190, h1258, h2218, h4082, reducedSource1004] using sourceEq1156 B hB

theorem rowSound1004 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1004 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1004, numericCheck1004, reducedZero1004 B hB hF, mul_zero]

theorem reducedZero1005 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1005 (mixedVector B) = 0 := by
  have h971 : mixedVector B (Sum.inr 971) = Sparse.eval nodeValue971 (mixedVector B) := by
    change mixedMoment B node971 node971Labels = _
    exact sound971 B hB hF
  have h975 : mixedVector B (Sum.inr 975) = Sparse.eval nodeValue975 (mixedVector B) := by
    change mixedMoment B node975 node975Labels = _
    exact sound975 B hB hF
  have h982 : mixedVector B (Sum.inr 982) = Sparse.eval nodeValue982 (mixedVector B) := by
    change mixedMoment B node982 node982Labels = _
    exact sound982 B hB hF
  have h1019 : mixedVector B (Sum.inr 1019) = Sparse.eval nodeValue1019 (mixedVector B) := by
    change mixedMoment B node1019 node1019Labels = _
    exact sound1019 B hB hF
  have h2193 : mixedVector B (Sum.inr 2193) = Sparse.eval nodeValue2193 (mixedVector B) := by
    change mixedMoment B node2193 node2193Labels = _
    exact sound2193 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1157, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h971, h975, h982, h1019, h2193, h4080, reducedSource1005] using sourceEq1157 B hB

theorem rowSound1005 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1005 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1005, numericCheck1005, reducedZero1005 B hB hF, mul_zero]

theorem reducedZero1006 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1006 (mixedVector B) = 0 := by
  have h975 : mixedVector B (Sum.inr 975) = Sparse.eval nodeValue975 (mixedVector B) := by
    change mixedMoment B node975 node975Labels = _
    exact sound975 B hB hF
  have h1194 : mixedVector B (Sum.inr 1194) = Sparse.eval nodeValue1194 (mixedVector B) := by
    change mixedMoment B node1194 node1194Labels = _
    exact sound1194 B hB hF
  have h1202 : mixedVector B (Sum.inr 1202) = Sparse.eval nodeValue1202 (mixedVector B) := by
    change mixedMoment B node1202 node1202Labels = _
    exact sound1202 B hB hF
  have h1211 : mixedVector B (Sum.inr 1211) = Sparse.eval nodeValue1211 (mixedVector B) := by
    change mixedMoment B node1211 node1211Labels = _
    exact sound1211 B hB hF
  have h2193 : mixedVector B (Sum.inr 2193) = Sparse.eval nodeValue2193 (mixedVector B) := by
    change mixedMoment B node2193 node2193Labels = _
    exact sound2193 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1158, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h975, h1194, h1202, h1211, h2193, h4080, reducedSource1006] using sourceEq1158 B hB

theorem rowSound1006 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1006 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1006, numericCheck1006, reducedZero1006 B hB hF, mul_zero]

theorem reducedZero1007 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1007 (mixedVector B) = 0 := by
  have h4187 : mixedVector B (Sum.inr 4187) = Sparse.eval nodeValue4187 (mixedVector B) := by
    change mixedMoment B node4187 node4187Labels = _
    exact sound4187 B hB hF
  have h4194 : mixedVector B (Sum.inr 4194) = Sparse.eval nodeValue4194 (mixedVector B) := by
    change mixedMoment B node4194 node4194Labels = _
    exact sound4194 B hB hF
  have h4555 : mixedVector B (Sum.inr 4555) = Sparse.eval nodeValue4555 (mixedVector B) := by
    change mixedMoment B node4555 node4555Labels = _
    exact sound4555 B hB hF
  have h4625 : mixedVector B (Sum.inr 4625) = Sparse.eval nodeValue4625 (mixedVector B) := by
    change mixedMoment B node4625 node4625Labels = _
    exact sound4625 B hB hF
  have h5312 : mixedVector B (Sum.inr 5312) = Sparse.eval nodeValue5312 (mixedVector B) := by
    change mixedMoment B node5312 node5312Labels = _
    exact sound5312 B hB hF
  simpa only [sourceForm1159, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4187, h4194, h4555, h4625, h5312, reducedSource1007] using sourceEq1159 B hB

theorem rowSound1007 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1007 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1007, numericCheck1007, reducedZero1007 B hB hF, mul_zero]

theorem sourceRowsAt992 : MixedData.sourceRows (992 : Fin 2425) =
    MixedData.row992 := by decide +kernel

theorem sourceRowsAt993 : MixedData.sourceRows (993 : Fin 2425) =
    MixedData.row993 := by decide +kernel

theorem sourceRowsAt994 : MixedData.sourceRows (994 : Fin 2425) =
    MixedData.row994 := by decide +kernel

theorem sourceRowsAt995 : MixedData.sourceRows (995 : Fin 2425) =
    MixedData.row995 := by decide +kernel

theorem sourceRowsAt996 : MixedData.sourceRows (996 : Fin 2425) =
    MixedData.row996 := by decide +kernel

theorem sourceRowsAt997 : MixedData.sourceRows (997 : Fin 2425) =
    MixedData.row997 := by decide +kernel

theorem sourceRowsAt998 : MixedData.sourceRows (998 : Fin 2425) =
    MixedData.row998 := by decide +kernel

theorem sourceRowsAt999 : MixedData.sourceRows (999 : Fin 2425) =
    MixedData.row999 := by decide +kernel

theorem sourceRowsAt1000 : MixedData.sourceRows (1000 : Fin 2425) =
    MixedData.row1000 := by decide +kernel

theorem sourceRowsAt1001 : MixedData.sourceRows (1001 : Fin 2425) =
    MixedData.row1001 := by decide +kernel

theorem sourceRowsAt1002 : MixedData.sourceRows (1002 : Fin 2425) =
    MixedData.row1002 := by decide +kernel

theorem sourceRowsAt1003 : MixedData.sourceRows (1003 : Fin 2425) =
    MixedData.row1003 := by decide +kernel

theorem sourceRowsAt1004 : MixedData.sourceRows (1004 : Fin 2425) =
    MixedData.row1004 := by decide +kernel

theorem sourceRowsAt1005 : MixedData.sourceRows (1005 : Fin 2425) =
    MixedData.row1005 := by decide +kernel

theorem sourceRowsAt1006 : MixedData.sourceRows (1006 : Fin 2425) =
    MixedData.row1006 := by decide +kernel

theorem sourceRowsAt1007 : MixedData.sourceRows (1007 : Fin 2425) =
    MixedData.row1007 := by decide +kernel

theorem chunkSound62 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 62) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 992 ∨ k.val = 993 ∨ k.val = 994 ∨ k.val = 995 ∨ k.val = 996 ∨ k.val = 997 ∨ k.val = 998 ∨ k.val = 999 ∨ k.val = 1000 ∨ k.val = 1001 ∨ k.val = 1002 ∨ k.val = 1003 ∨ k.val = 1004 ∨ k.val = 1005 ∨ k.val = 1006 ∨ k.val = 1007 := by omega
  rcases heq with h992 | h993 | h994 | h995 | h996 | h997 | h998 | h999 | h1000 | h1001 | h1002 | h1003 | h1004 | h1005 | h1006 | h1007
  · have he : k = (992 : Fin 2425) := Fin.ext h992
    subst k
    rw [sourceRowsAt992]
    exact rowSound992 B hB hF
  · have he : k = (993 : Fin 2425) := Fin.ext h993
    subst k
    rw [sourceRowsAt993]
    exact rowSound993 B hB hF
  · have he : k = (994 : Fin 2425) := Fin.ext h994
    subst k
    rw [sourceRowsAt994]
    exact rowSound994 B hB hF
  · have he : k = (995 : Fin 2425) := Fin.ext h995
    subst k
    rw [sourceRowsAt995]
    exact rowSound995 B hB hF
  · have he : k = (996 : Fin 2425) := Fin.ext h996
    subst k
    rw [sourceRowsAt996]
    exact rowSound996 B hB hF
  · have he : k = (997 : Fin 2425) := Fin.ext h997
    subst k
    rw [sourceRowsAt997]
    exact rowSound997 B hB hF
  · have he : k = (998 : Fin 2425) := Fin.ext h998
    subst k
    rw [sourceRowsAt998]
    exact rowSound998 B hB hF
  · have he : k = (999 : Fin 2425) := Fin.ext h999
    subst k
    rw [sourceRowsAt999]
    exact rowSound999 B hB hF
  · have he : k = (1000 : Fin 2425) := Fin.ext h1000
    subst k
    rw [sourceRowsAt1000]
    exact rowSound1000 B hB hF
  · have he : k = (1001 : Fin 2425) := Fin.ext h1001
    subst k
    rw [sourceRowsAt1001]
    exact rowSound1001 B hB hF
  · have he : k = (1002 : Fin 2425) := Fin.ext h1002
    subst k
    rw [sourceRowsAt1002]
    exact rowSound1002 B hB hF
  · have he : k = (1003 : Fin 2425) := Fin.ext h1003
    subst k
    rw [sourceRowsAt1003]
    exact rowSound1003 B hB hF
  · have he : k = (1004 : Fin 2425) := Fin.ext h1004
    subst k
    rw [sourceRowsAt1004]
    exact rowSound1004 B hB hF
  · have he : k = (1005 : Fin 2425) := Fin.ext h1005
    subst k
    rw [sourceRowsAt1005]
    exact rowSound1005 B hB hF
  · have he : k = (1006 : Fin 2425) := Fin.ext h1006
    subst k
    rw [sourceRowsAt1006]
    exact rowSound1006 B hB hF
  · have he : k = (1007 : Fin 2425) := Fin.ext h1007
    subst k
    rw [sourceRowsAt1007]
    exact rowSound1007 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
