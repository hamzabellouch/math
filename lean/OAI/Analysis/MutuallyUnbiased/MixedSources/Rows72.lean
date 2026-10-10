import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources42

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1152 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1152 (mixedVector B) = 0 := by
  have h1019 : mixedVector B (Sum.inr 1019) = Sparse.eval nodeValue1019 (mixedVector B) := by
    change mixedMoment B node1019 node1019Labels = _
    exact sound1019 B hB hF
  have h2008 : mixedVector B (Sum.inr 2008) = Sparse.eval nodeValue2008 (mixedVector B) := by
    change mixedMoment B node2008 node2008Labels = _
    exact sound2008 B hB hF
  have h2087 : mixedVector B (Sum.inr 2087) = Sparse.eval nodeValue2087 (mixedVector B) := by
    change mixedMoment B node2087 node2087Labels = _
    exact sound2087 B hB hF
  have h2193 : mixedVector B (Sum.inr 2193) = Sparse.eval nodeValue2193 (mixedVector B) := by
    change mixedMoment B node2193 node2193Labels = _
    exact sound2193 B hB hF
  have h2242 : mixedVector B (Sum.inr 2242) = Sparse.eval nodeValue2242 (mixedVector B) := by
    change mixedMoment B node2242 node2242Labels = _
    exact sound2242 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1329, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1019, h2008, h2087, h2193, h2242, h4080, reducedSource1152] using sourceEq1329 B hB

theorem rowSound1152 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1152 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1152, numericCheck1152, reducedZero1152 B hB hF, mul_zero]

theorem reducedZero1153 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1153 (mixedVector B) = 0 := by
  have h1017 : mixedVector B (Sum.inr 1017) = Sparse.eval nodeValue1017 (mixedVector B) := by
    change mixedMoment B node1017 node1017Labels = _
    exact sound1017 B hB hF
  have h1019 : mixedVector B (Sum.inr 1019) = Sparse.eval nodeValue1019 (mixedVector B) := by
    change mixedMoment B node1019 node1019Labels = _
    exact sound1019 B hB hF
  have h1025 : mixedVector B (Sum.inr 1025) = Sparse.eval nodeValue1025 (mixedVector B) := by
    change mixedMoment B node1025 node1025Labels = _
    exact sound1025 B hB hF
  have h1035 : mixedVector B (Sum.inr 1035) = Sparse.eval nodeValue1035 (mixedVector B) := by
    change mixedMoment B node1035 node1035Labels = _
    exact sound1035 B hB hF
  have h2242 : mixedVector B (Sum.inr 2242) = Sparse.eval nodeValue2242 (mixedVector B) := by
    change mixedMoment B node2242 node2242Labels = _
    exact sound2242 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1330, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1017, h1019, h1025, h1035, h2242, h4080, reducedSource1153] using sourceEq1330 B hB

theorem rowSound1153 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1153 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1153, numericCheck1153, reducedZero1153 B hB hF, mul_zero]

theorem reducedZero1154 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1154 (mixedVector B) = 0 := by
  have h972 : mixedVector B (Sum.inr 972) = Sparse.eval nodeValue972 (mixedVector B) := by
    change mixedMoment B node972 node972Labels = _
    exact sound972 B hB hF
  have h1898 : mixedVector B (Sum.inr 1898) = Sparse.eval nodeValue1898 (mixedVector B) := by
    change mixedMoment B node1898 node1898Labels = _
    exact sound1898 B hB hF
  have h2071 : mixedVector B (Sum.inr 2071) = Sparse.eval nodeValue2071 (mixedVector B) := by
    change mixedMoment B node2071 node2071Labels = _
    exact sound2071 B hB hF
  have h2187 : mixedVector B (Sum.inr 2187) = Sparse.eval nodeValue2187 (mixedVector B) := by
    change mixedMoment B node2187 node2187Labels = _
    exact sound2187 B hB hF
  have h2191 : mixedVector B (Sum.inr 2191) = Sparse.eval nodeValue2191 (mixedVector B) := by
    change mixedMoment B node2191 node2191Labels = _
    exact sound2191 B hB hF
  have h4079 : mixedVector B (Sum.inr 4079) = Sparse.eval nodeValue4079 (mixedVector B) := by
    change mixedMoment B node4079 node4079Labels = _
    exact sound4079 B hB hF
  simpa only [sourceForm1331, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h972, h1898, h2071, h2187, h2191, h4079, reducedSource1154] using sourceEq1331 B hB

theorem rowSound1154 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1154 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1154, numericCheck1154, reducedZero1154 B hB hF, mul_zero]

theorem reducedZero1155 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1155 (mixedVector B) = 0 := by
  have h972 : mixedVector B (Sum.inr 972) = Sparse.eval nodeValue972 (mixedVector B) := by
    change mixedMoment B node972 node972Labels = _
    exact sound972 B hB hF
  have h974 : mixedVector B (Sum.inr 974) = Sparse.eval nodeValue974 (mixedVector B) := by
    change mixedMoment B node974 node974Labels = _
    exact sound974 B hB hF
  have h980 : mixedVector B (Sum.inr 980) = Sparse.eval nodeValue980 (mixedVector B) := by
    change mixedMoment B node980 node980Labels = _
    exact sound980 B hB hF
  have h1018 : mixedVector B (Sum.inr 1018) = Sparse.eval nodeValue1018 (mixedVector B) := by
    change mixedMoment B node1018 node1018Labels = _
    exact sound1018 B hB hF
  have h2191 : mixedVector B (Sum.inr 2191) = Sparse.eval nodeValue2191 (mixedVector B) := by
    change mixedMoment B node2191 node2191Labels = _
    exact sound2191 B hB hF
  have h4079 : mixedVector B (Sum.inr 4079) = Sparse.eval nodeValue4079 (mixedVector B) := by
    change mixedMoment B node4079 node4079Labels = _
    exact sound4079 B hB hF
  simpa only [sourceForm1332, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h972, h974, h980, h1018, h2191, h4079, reducedSource1155] using sourceEq1332 B hB

theorem rowSound1155 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1155 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1155, numericCheck1155, reducedZero1155 B hB hF, mul_zero]

theorem reducedZero1156 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1156 (mixedVector B) = 0 := by
  have h971 : mixedVector B (Sum.inr 971) = Sparse.eval nodeValue971 (mixedVector B) := by
    change mixedMoment B node971 node971Labels = _
    exact sound971 B hB hF
  have h1897 : mixedVector B (Sum.inr 1897) = Sparse.eval nodeValue1897 (mixedVector B) := by
    change mixedMoment B node1897 node1897Labels = _
    exact sound1897 B hB hF
  have h2070 : mixedVector B (Sum.inr 2070) = Sparse.eval nodeValue2070 (mixedVector B) := by
    change mixedMoment B node2070 node2070Labels = _
    exact sound2070 B hB hF
  have h2190 : mixedVector B (Sum.inr 2190) = Sparse.eval nodeValue2190 (mixedVector B) := by
    change mixedMoment B node2190 node2190Labels = _
    exact sound2190 B hB hF
  have h2193 : mixedVector B (Sum.inr 2193) = Sparse.eval nodeValue2193 (mixedVector B) := by
    change mixedMoment B node2193 node2193Labels = _
    exact sound2193 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1333, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h971, h1897, h2070, h2190, h2193, h4080, reducedSource1156] using sourceEq1333 B hB

theorem rowSound1156 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1156 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1156, numericCheck1156, reducedZero1156 B hB hF, mul_zero]

theorem reducedZero1157 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1157 (mixedVector B) = 0 := by
  have h971 : mixedVector B (Sum.inr 971) = Sparse.eval nodeValue971 (mixedVector B) := by
    change mixedMoment B node971 node971Labels = _
    exact sound971 B hB hF
  have h973 : mixedVector B (Sum.inr 973) = Sparse.eval nodeValue973 (mixedVector B) := by
    change mixedMoment B node973 node973Labels = _
    exact sound973 B hB hF
  have h977 : mixedVector B (Sum.inr 977) = Sparse.eval nodeValue977 (mixedVector B) := by
    change mixedMoment B node977 node977Labels = _
    exact sound977 B hB hF
  have h1017 : mixedVector B (Sum.inr 1017) = Sparse.eval nodeValue1017 (mixedVector B) := by
    change mixedMoment B node1017 node1017Labels = _
    exact sound1017 B hB hF
  have h2190 : mixedVector B (Sum.inr 2190) = Sparse.eval nodeValue2190 (mixedVector B) := by
    change mixedMoment B node2190 node2190Labels = _
    exact sound2190 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1334, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h971, h973, h977, h1017, h2190, h4080, reducedSource1157] using sourceEq1334 B hB

theorem rowSound1157 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1157 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1157, numericCheck1157, reducedZero1157 B hB hF, mul_zero]

theorem reducedZero1158 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1158 (mixedVector B) = 0 := by
  have h4153 : mixedVector B (Sum.inr 4153) = Sparse.eval nodeValue4153 (mixedVector B) := by
    change mixedMoment B node4153 node4153Labels = _
    exact sound4153 B hB hF
  have h4159 : mixedVector B (Sum.inr 4159) = Sparse.eval nodeValue4159 (mixedVector B) := by
    change mixedMoment B node4159 node4159Labels = _
    exact sound4159 B hB hF
  have h4161 : mixedVector B (Sum.inr 4161) = Sparse.eval nodeValue4161 (mixedVector B) := by
    change mixedMoment B node4161 node4161Labels = _
    exact sound4161 B hB hF
  have h4183 : mixedVector B (Sum.inr 4183) = Sparse.eval nodeValue4183 (mixedVector B) := by
    change mixedMoment B node4183 node4183Labels = _
    exact sound4183 B hB hF
  have h4327 : mixedVector B (Sum.inr 4327) = Sparse.eval nodeValue4327 (mixedVector B) := by
    change mixedMoment B node4327 node4327Labels = _
    exact sound4327 B hB hF
  have h4333 : mixedVector B (Sum.inr 4333) = Sparse.eval nodeValue4333 (mixedVector B) := by
    change mixedMoment B node4333 node4333Labels = _
    exact sound4333 B hB hF
  have h4335 : mixedVector B (Sum.inr 4335) = Sparse.eval nodeValue4335 (mixedVector B) := by
    change mixedMoment B node4335 node4335Labels = _
    exact sound4335 B hB hF
  have h4352 : mixedVector B (Sum.inr 4352) = Sparse.eval nodeValue4352 (mixedVector B) := by
    change mixedMoment B node4352 node4352Labels = _
    exact sound4352 B hB hF
  have h4358 : mixedVector B (Sum.inr 4358) = Sparse.eval nodeValue4358 (mixedVector B) := by
    change mixedMoment B node4358 node4358Labels = _
    exact sound4358 B hB hF
  have h4367 : mixedVector B (Sum.inr 4367) = Sparse.eval nodeValue4367 (mixedVector B) := by
    change mixedMoment B node4367 node4367Labels = _
    exact sound4367 B hB hF
  have h4374 : mixedVector B (Sum.inr 4374) = Sparse.eval nodeValue4374 (mixedVector B) := by
    change mixedMoment B node4374 node4374Labels = _
    exact sound4374 B hB hF
  have h4440 : mixedVector B (Sum.inr 4440) = Sparse.eval nodeValue4440 (mixedVector B) := by
    change mixedMoment B node4440 node4440Labels = _
    exact sound4440 B hB hF
  have h4445 : mixedVector B (Sum.inr 4445) = Sparse.eval nodeValue4445 (mixedVector B) := by
    change mixedMoment B node4445 node4445Labels = _
    exact sound4445 B hB hF
  have h4458 : mixedVector B (Sum.inr 4458) = Sparse.eval nodeValue4458 (mixedVector B) := by
    change mixedMoment B node4458 node4458Labels = _
    exact sound4458 B hB hF
  have h4463 : mixedVector B (Sum.inr 4463) = Sparse.eval nodeValue4463 (mixedVector B) := by
    change mixedMoment B node4463 node4463Labels = _
    exact sound4463 B hB hF
  have h4467 : mixedVector B (Sum.inr 4467) = Sparse.eval nodeValue4467 (mixedVector B) := by
    change mixedMoment B node4467 node4467Labels = _
    exact sound4467 B hB hF
  have h4502 : mixedVector B (Sum.inr 4502) = Sparse.eval nodeValue4502 (mixedVector B) := by
    change mixedMoment B node4502 node4502Labels = _
    exact sound4502 B hB hF
  have h4807 : mixedVector B (Sum.inr 4807) = Sparse.eval nodeValue4807 (mixedVector B) := by
    change mixedMoment B node4807 node4807Labels = _
    exact sound4807 B hB hF
  have h4871 : mixedVector B (Sum.inr 4871) = Sparse.eval nodeValue4871 (mixedVector B) := by
    change mixedMoment B node4871 node4871Labels = _
    exact sound4871 B hB hF
  have h4890 : mixedVector B (Sum.inr 4890) = Sparse.eval nodeValue4890 (mixedVector B) := by
    change mixedMoment B node4890 node4890Labels = _
    exact sound4890 B hB hF
  have h4895 : mixedVector B (Sum.inr 4895) = Sparse.eval nodeValue4895 (mixedVector B) := by
    change mixedMoment B node4895 node4895Labels = _
    exact sound4895 B hB hF
  simpa only [sourceForm1335, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4153, h4159, h4161, h4183, h4327, h4333, h4335, h4352, h4358, h4367, h4374, h4440, h4445, h4458, h4463, h4467, h4502, h4807, h4871, h4890, h4895, reducedSource1158] using sourceEq1335 B hB

theorem rowSound1158 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1158 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1158, numericCheck1158, reducedZero1158 B hB hF, mul_zero]

theorem reducedZero1159 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1159 (mixedVector B) = 0 := by
  have h626 : mixedVector B (Sum.inr 626) = Sparse.eval nodeValue626 (mixedVector B) := by
    change mixedMoment B node626 node626Labels = _
    exact sound626 B hB hF
  have h628 : mixedVector B (Sum.inr 628) = Sparse.eval nodeValue628 (mixedVector B) := by
    change mixedMoment B node628 node628Labels = _
    exact sound628 B hB hF
  have h635 : mixedVector B (Sum.inr 635) = Sparse.eval nodeValue635 (mixedVector B) := by
    change mixedMoment B node635 node635Labels = _
    exact sound635 B hB hF
  have h645 : mixedVector B (Sum.inr 645) = Sparse.eval nodeValue645 (mixedVector B) := by
    change mixedMoment B node645 node645Labels = _
    exact sound645 B hB hF
  have h911 : mixedVector B (Sum.inr 911) = Sparse.eval nodeValue911 (mixedVector B) := by
    change mixedMoment B node911 node911Labels = _
    exact sound911 B hB hF
  have h936 : mixedVector B (Sum.inr 936) = Sparse.eval nodeValue936 (mixedVector B) := by
    change mixedMoment B node936 node936Labels = _
    exact sound936 B hB hF
  have h1027 : mixedVector B (Sum.inr 1027) = Sparse.eval nodeValue1027 (mixedVector B) := by
    change mixedMoment B node1027 node1027Labels = _
    exact sound1027 B hB hF
  have h1317 : mixedVector B (Sum.inr 1317) = Sparse.eval nodeValue1317 (mixedVector B) := by
    change mixedMoment B node1317 node1317Labels = _
    exact sound1317 B hB hF
  have h1324 : mixedVector B (Sum.inr 1324) = Sparse.eval nodeValue1324 (mixedVector B) := by
    change mixedMoment B node1324 node1324Labels = _
    exact sound1324 B hB hF
  have h1327 : mixedVector B (Sum.inr 1327) = Sparse.eval nodeValue1327 (mixedVector B) := by
    change mixedMoment B node1327 node1327Labels = _
    exact sound1327 B hB hF
  have h1333 : mixedVector B (Sum.inr 1333) = Sparse.eval nodeValue1333 (mixedVector B) := by
    change mixedMoment B node1333 node1333Labels = _
    exact sound1333 B hB hF
  have h1340 : mixedVector B (Sum.inr 1340) = Sparse.eval nodeValue1340 (mixedVector B) := by
    change mixedMoment B node1340 node1340Labels = _
    exact sound1340 B hB hF
  have h1388 : mixedVector B (Sum.inr 1388) = Sparse.eval nodeValue1388 (mixedVector B) := by
    change mixedMoment B node1388 node1388Labels = _
    exact sound1388 B hB hF
  have h1411 : mixedVector B (Sum.inr 1411) = Sparse.eval nodeValue1411 (mixedVector B) := by
    change mixedMoment B node1411 node1411Labels = _
    exact sound1411 B hB hF
  have h1413 : mixedVector B (Sum.inr 1413) = Sparse.eval nodeValue1413 (mixedVector B) := by
    change mixedMoment B node1413 node1413Labels = _
    exact sound1413 B hB hF
  have h1420 : mixedVector B (Sum.inr 1420) = Sparse.eval nodeValue1420 (mixedVector B) := by
    change mixedMoment B node1420 node1420Labels = _
    exact sound1420 B hB hF
  have h1447 : mixedVector B (Sum.inr 1447) = Sparse.eval nodeValue1447 (mixedVector B) := by
    change mixedMoment B node1447 node1447Labels = _
    exact sound1447 B hB hF
  have h2574 : mixedVector B (Sum.inr 2574) = Sparse.eval nodeValue2574 (mixedVector B) := by
    change mixedMoment B node2574 node2574Labels = _
    exact sound2574 B hB hF
  have h2602 : mixedVector B (Sum.inr 2602) = Sparse.eval nodeValue2602 (mixedVector B) := by
    change mixedMoment B node2602 node2602Labels = _
    exact sound2602 B hB hF
  have h2755 : mixedVector B (Sum.inr 2755) = Sparse.eval nodeValue2755 (mixedVector B) := by
    change mixedMoment B node2755 node2755Labels = _
    exact sound2755 B hB hF
  have h3229 : mixedVector B (Sum.inr 3229) = Sparse.eval nodeValue3229 (mixedVector B) := by
    change mixedMoment B node3229 node3229Labels = _
    exact sound3229 B hB hF
  simpa only [sourceForm1336, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h626, h628, h635, h645, h911, h936, h1027, h1317, h1324, h1327, h1333, h1340, h1388, h1411, h1413, h1420, h1447, h2574, h2602, h2755, h3229, reducedSource1159] using sourceEq1336 B hB

theorem rowSound1159 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1159 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1159, numericCheck1159, reducedZero1159 B hB hF, mul_zero]

theorem reducedZero1160 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1160 (mixedVector B) = 0 := by
  have h1514 : mixedVector B (Sum.inr 1514) = Sparse.eval nodeValue1514 (mixedVector B) := by
    change mixedMoment B node1514 node1514Labels = _
    exact sound1514 B hB hF
  have h1532 : mixedVector B (Sum.inr 1532) = Sparse.eval nodeValue1532 (mixedVector B) := by
    change mixedMoment B node1532 node1532Labels = _
    exact sound1532 B hB hF
  have h1533 : mixedVector B (Sum.inr 1533) = Sparse.eval nodeValue1533 (mixedVector B) := by
    change mixedMoment B node1533 node1533Labels = _
    exact sound1533 B hB hF
  have h1535 : mixedVector B (Sum.inr 1535) = Sparse.eval nodeValue1535 (mixedVector B) := by
    change mixedMoment B node1535 node1535Labels = _
    exact sound1535 B hB hF
  have h1670 : mixedVector B (Sum.inr 1670) = Sparse.eval nodeValue1670 (mixedVector B) := by
    change mixedMoment B node1670 node1670Labels = _
    exact sound1670 B hB hF
  have h1688 : mixedVector B (Sum.inr 1688) = Sparse.eval nodeValue1688 (mixedVector B) := by
    change mixedMoment B node1688 node1688Labels = _
    exact sound1688 B hB hF
  have h1689 : mixedVector B (Sum.inr 1689) = Sparse.eval nodeValue1689 (mixedVector B) := by
    change mixedMoment B node1689 node1689Labels = _
    exact sound1689 B hB hF
  have h1690 : mixedVector B (Sum.inr 1690) = Sparse.eval nodeValue1690 (mixedVector B) := by
    change mixedMoment B node1690 node1690Labels = _
    exact sound1690 B hB hF
  have h1695 : mixedVector B (Sum.inr 1695) = Sparse.eval nodeValue1695 (mixedVector B) := by
    change mixedMoment B node1695 node1695Labels = _
    exact sound1695 B hB hF
  have h1720 : mixedVector B (Sum.inr 1720) = Sparse.eval nodeValue1720 (mixedVector B) := by
    change mixedMoment B node1720 node1720Labels = _
    exact sound1720 B hB hF
  have h1723 : mixedVector B (Sum.inr 1723) = Sparse.eval nodeValue1723 (mixedVector B) := by
    change mixedMoment B node1723 node1723Labels = _
    exact sound1723 B hB hF
  have h1724 : mixedVector B (Sum.inr 1724) = Sparse.eval nodeValue1724 (mixedVector B) := by
    change mixedMoment B node1724 node1724Labels = _
    exact sound1724 B hB hF
  have h1748 : mixedVector B (Sum.inr 1748) = Sparse.eval nodeValue1748 (mixedVector B) := by
    change mixedMoment B node1748 node1748Labels = _
    exact sound1748 B hB hF
  have h1749 : mixedVector B (Sum.inr 1749) = Sparse.eval nodeValue1749 (mixedVector B) := by
    change mixedMoment B node1749 node1749Labels = _
    exact sound1749 B hB hF
  have h1750 : mixedVector B (Sum.inr 1750) = Sparse.eval nodeValue1750 (mixedVector B) := by
    change mixedMoment B node1750 node1750Labels = _
    exact sound1750 B hB hF
  have h1751 : mixedVector B (Sum.inr 1751) = Sparse.eval nodeValue1751 (mixedVector B) := by
    change mixedMoment B node1751 node1751Labels = _
    exact sound1751 B hB hF
  have h1753 : mixedVector B (Sum.inr 1753) = Sparse.eval nodeValue1753 (mixedVector B) := by
    change mixedMoment B node1753 node1753Labels = _
    exact sound1753 B hB hF
  have h2224 : mixedVector B (Sum.inr 2224) = Sparse.eval nodeValue2224 (mixedVector B) := by
    change mixedMoment B node2224 node2224Labels = _
    exact sound2224 B hB hF
  have h2287 : mixedVector B (Sum.inr 2287) = Sparse.eval nodeValue2287 (mixedVector B) := by
    change mixedMoment B node2287 node2287Labels = _
    exact sound2287 B hB hF
  have h2290 : mixedVector B (Sum.inr 2290) = Sparse.eval nodeValue2290 (mixedVector B) := by
    change mixedMoment B node2290 node2290Labels = _
    exact sound2290 B hB hF
  have h2291 : mixedVector B (Sum.inr 2291) = Sparse.eval nodeValue2291 (mixedVector B) := by
    change mixedMoment B node2291 node2291Labels = _
    exact sound2291 B hB hF
  simpa only [sourceForm1337, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1514, h1532, h1533, h1535, h1670, h1688, h1689, h1690, h1695, h1720, h1723, h1724, h1748, h1749, h1750, h1751, h1753, h2224, h2287, h2290, h2291, reducedSource1160] using sourceEq1337 B hB

theorem rowSound1160 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1160 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1160, numericCheck1160, reducedZero1160 B hB hF, mul_zero]

theorem reducedZero1161 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1161 (mixedVector B) = 0 := by
  have h581 : mixedVector B (Sum.inr 581) = Sparse.eval nodeValue581 (mixedVector B) := by
    change mixedMoment B node581 node581Labels = _
    exact sound581 B hB hF
  have h587 : mixedVector B (Sum.inr 587) = Sparse.eval nodeValue587 (mixedVector B) := by
    change mixedMoment B node587 node587Labels = _
    exact sound587 B hB hF
  have h589 : mixedVector B (Sum.inr 589) = Sparse.eval nodeValue589 (mixedVector B) := by
    change mixedMoment B node589 node589Labels = _
    exact sound589 B hB hF
  have h611 : mixedVector B (Sum.inr 611) = Sparse.eval nodeValue611 (mixedVector B) := by
    change mixedMoment B node611 node611Labels = _
    exact sound611 B hB hF
  have h1046 : mixedVector B (Sum.inr 1046) = Sparse.eval nodeValue1046 (mixedVector B) := by
    change mixedMoment B node1046 node1046Labels = _
    exact sound1046 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1338, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h581, h587, h589, h611, h1046, h4083, reducedSource1161] using sourceEq1338 B hB

theorem rowSound1161 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1161 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1161, numericCheck1161, reducedZero1161 B hB hF, mul_zero]

theorem reducedZero1162 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1162 (mixedVector B) = 0 := by
  have h611 : mixedVector B (Sum.inr 611) = Sparse.eval nodeValue611 (mixedVector B) := by
    change mixedMoment B node611 node611Labels = _
    exact sound611 B hB hF
  have h930 : mixedVector B (Sum.inr 930) = Sparse.eval nodeValue930 (mixedVector B) := by
    change mixedMoment B node930 node930Labels = _
    exact sound930 B hB hF
  have h1046 : mixedVector B (Sum.inr 1046) = Sparse.eval nodeValue1046 (mixedVector B) := by
    change mixedMoment B node1046 node1046Labels = _
    exact sound1046 B hB hF
  have h1086 : mixedVector B (Sum.inr 1086) = Sparse.eval nodeValue1086 (mixedVector B) := by
    change mixedMoment B node1086 node1086Labels = _
    exact sound1086 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1339, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h611, h930, h1046, h1086, h4083, reducedSource1162] using sourceEq1339 B hB

theorem rowSound1162 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1162 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1162, numericCheck1162, reducedZero1162 B hB hF, mul_zero]

theorem reducedZero1163 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1163 (mixedVector B) = 0 := by
  have h945 : mixedVector B (Sum.inr 945) = Sparse.eval nodeValue945 (mixedVector B) := by
    change mixedMoment B node945 node945Labels = _
    exact sound945 B hB hF
  have h951 : mixedVector B (Sum.inr 951) = Sparse.eval nodeValue951 (mixedVector B) := by
    change mixedMoment B node951 node951Labels = _
    exact sound951 B hB hF
  have h953 : mixedVector B (Sum.inr 953) = Sparse.eval nodeValue953 (mixedVector B) := by
    change mixedMoment B node953 node953Labels = _
    exact sound953 B hB hF
  have h1046 : mixedVector B (Sum.inr 1046) = Sparse.eval nodeValue1046 (mixedVector B) := by
    change mixedMoment B node1046 node1046Labels = _
    exact sound1046 B hB hF
  have h2112 : mixedVector B (Sum.inr 2112) = Sparse.eval nodeValue2112 (mixedVector B) := by
    change mixedMoment B node2112 node2112Labels = _
    exact sound2112 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1340, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h945, h951, h953, h1046, h2112, h4083, reducedSource1163] using sourceEq1340 B hB

theorem rowSound1163 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1163 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1163, numericCheck1163, reducedZero1163 B hB hF, mul_zero]

theorem reducedZero1164 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1164 (mixedVector B) = 0 := by
  have h905 : mixedVector B (Sum.inr 905) = Sparse.eval nodeValue905 (mixedVector B) := by
    change mixedMoment B node905 node905Labels = _
    exact sound905 B hB hF
  have h911 : mixedVector B (Sum.inr 911) = Sparse.eval nodeValue911 (mixedVector B) := by
    change mixedMoment B node911 node911Labels = _
    exact sound911 B hB hF
  have h913 : mixedVector B (Sum.inr 913) = Sparse.eval nodeValue913 (mixedVector B) := by
    change mixedMoment B node913 node913Labels = _
    exact sound913 B hB hF
  have h930 : mixedVector B (Sum.inr 930) = Sparse.eval nodeValue930 (mixedVector B) := by
    change mixedMoment B node930 node930Labels = _
    exact sound930 B hB hF
  have h1046 : mixedVector B (Sum.inr 1046) = Sparse.eval nodeValue1046 (mixedVector B) := by
    change mixedMoment B node1046 node1046Labels = _
    exact sound1046 B hB hF
  have h2025 : mixedVector B (Sum.inr 2025) = Sparse.eval nodeValue2025 (mixedVector B) := by
    change mixedMoment B node2025 node2025Labels = _
    exact sound2025 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1341, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h905, h911, h913, h930, h1046, h2025, h4083, reducedSource1164] using sourceEq1341 B hB

theorem rowSound1164 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1164 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1164, numericCheck1164, reducedZero1164 B hB hF, mul_zero]

theorem reducedZero1165 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1165 (mixedVector B) = 0 := by
  have h4105 : mixedVector B (Sum.inr 4105) = Sparse.eval nodeValue4105 (mixedVector B) := by
    change mixedMoment B node4105 node4105Labels = _
    exact sound4105 B hB hF
  have h4108 : mixedVector B (Sum.inr 4108) = Sparse.eval nodeValue4108 (mixedVector B) := by
    change mixedMoment B node4108 node4108Labels = _
    exact sound4108 B hB hF
  have h4111 : mixedVector B (Sum.inr 4111) = Sparse.eval nodeValue4111 (mixedVector B) := by
    change mixedMoment B node4111 node4111Labels = _
    exact sound4111 B hB hF
  have h4128 : mixedVector B (Sum.inr 4128) = Sparse.eval nodeValue4128 (mixedVector B) := by
    change mixedMoment B node4128 node4128Labels = _
    exact sound4128 B hB hF
  have h4290 : mixedVector B (Sum.inr 4290) = Sparse.eval nodeValue4290 (mixedVector B) := by
    change mixedMoment B node4290 node4290Labels = _
    exact sound4290 B hB hF
  have h4293 : mixedVector B (Sum.inr 4293) = Sparse.eval nodeValue4293 (mixedVector B) := by
    change mixedMoment B node4293 node4293Labels = _
    exact sound4293 B hB hF
  have h4296 : mixedVector B (Sum.inr 4296) = Sparse.eval nodeValue4296 (mixedVector B) := by
    change mixedMoment B node4296 node4296Labels = _
    exact sound4296 B hB hF
  have h4309 : mixedVector B (Sum.inr 4309) = Sparse.eval nodeValue4309 (mixedVector B) := by
    change mixedMoment B node4309 node4309Labels = _
    exact sound4309 B hB hF
  have h4352 : mixedVector B (Sum.inr 4352) = Sparse.eval nodeValue4352 (mixedVector B) := by
    change mixedMoment B node4352 node4352Labels = _
    exact sound4352 B hB hF
  have h4356 : mixedVector B (Sum.inr 4356) = Sparse.eval nodeValue4356 (mixedVector B) := by
    change mixedMoment B node4356 node4356Labels = _
    exact sound4356 B hB hF
  have h4361 : mixedVector B (Sum.inr 4361) = Sparse.eval nodeValue4361 (mixedVector B) := by
    change mixedMoment B node4361 node4361Labels = _
    exact sound4361 B hB hF
  have h4461 : mixedVector B (Sum.inr 4461) = Sparse.eval nodeValue4461 (mixedVector B) := by
    change mixedMoment B node4461 node4461Labels = _
    exact sound4461 B hB hF
  have h4463 : mixedVector B (Sum.inr 4463) = Sparse.eval nodeValue4463 (mixedVector B) := by
    change mixedMoment B node4463 node4463Labels = _
    exact sound4463 B hB hF
  have h4466 : mixedVector B (Sum.inr 4466) = Sparse.eval nodeValue4466 (mixedVector B) := by
    change mixedMoment B node4466 node4466Labels = _
    exact sound4466 B hB hF
  have h4468 : mixedVector B (Sum.inr 4468) = Sparse.eval nodeValue4468 (mixedVector B) := by
    change mixedMoment B node4468 node4468Labels = _
    exact sound4468 B hB hF
  have h4503 : mixedVector B (Sum.inr 4503) = Sparse.eval nodeValue4503 (mixedVector B) := by
    change mixedMoment B node4503 node4503Labels = _
    exact sound4503 B hB hF
  have h4507 : mixedVector B (Sum.inr 4507) = Sparse.eval nodeValue4507 (mixedVector B) := by
    change mixedMoment B node4507 node4507Labels = _
    exact sound4507 B hB hF
  have h5078 : mixedVector B (Sum.inr 5078) = Sparse.eval nodeValue5078 (mixedVector B) := by
    change mixedMoment B node5078 node5078Labels = _
    exact sound5078 B hB hF
  have h5174 : mixedVector B (Sum.inr 5174) = Sparse.eval nodeValue5174 (mixedVector B) := by
    change mixedMoment B node5174 node5174Labels = _
    exact sound5174 B hB hF
  have h5294 : mixedVector B (Sum.inr 5294) = Sparse.eval nodeValue5294 (mixedVector B) := by
    change mixedMoment B node5294 node5294Labels = _
    exact sound5294 B hB hF
  have h5296 : mixedVector B (Sum.inr 5296) = Sparse.eval nodeValue5296 (mixedVector B) := by
    change mixedMoment B node5296 node5296Labels = _
    exact sound5296 B hB hF
  simpa only [sourceForm1342, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4105, h4108, h4111, h4128, h4290, h4293, h4296, h4309, h4352, h4356, h4361, h4461, h4463, h4466, h4468, h4503, h4507, h5078, h5174, h5294, h5296, reducedSource1165] using sourceEq1342 B hB

theorem rowSound1165 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1165 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1165, numericCheck1165, reducedZero1165 B hB hF, mul_zero]

theorem reducedZero1166 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1166 (mixedVector B) = 0 := by
  have h4253 : mixedVector B (Sum.inr 4253) = Sparse.eval nodeValue4253 (mixedVector B) := by
    change mixedMoment B node4253 node4253Labels = _
    exact sound4253 B hB hF
  have h4269 : mixedVector B (Sum.inr 4269) = Sparse.eval nodeValue4269 (mixedVector B) := by
    change mixedMoment B node4269 node4269Labels = _
    exact sound4269 B hB hF
  have h4270 : mixedVector B (Sum.inr 4270) = Sparse.eval nodeValue4270 (mixedVector B) := by
    change mixedMoment B node4270 node4270Labels = _
    exact sound4270 B hB hF
  have h4276 : mixedVector B (Sum.inr 4276) = Sparse.eval nodeValue4276 (mixedVector B) := by
    change mixedMoment B node4276 node4276Labels = _
    exact sound4276 B hB hF
  have h4391 : mixedVector B (Sum.inr 4391) = Sparse.eval nodeValue4391 (mixedVector B) := by
    change mixedMoment B node4391 node4391Labels = _
    exact sound4391 B hB hF
  have h4401 : mixedVector B (Sum.inr 4401) = Sparse.eval nodeValue4401 (mixedVector B) := by
    change mixedMoment B node4401 node4401Labels = _
    exact sound4401 B hB hF
  have h4402 : mixedVector B (Sum.inr 4402) = Sparse.eval nodeValue4402 (mixedVector B) := by
    change mixedMoment B node4402 node4402Labels = _
    exact sound4402 B hB hF
  have h4410 : mixedVector B (Sum.inr 4410) = Sparse.eval nodeValue4410 (mixedVector B) := by
    change mixedMoment B node4410 node4410Labels = _
    exact sound4410 B hB hF
  have h4440 : mixedVector B (Sum.inr 4440) = Sparse.eval nodeValue4440 (mixedVector B) := by
    change mixedMoment B node4440 node4440Labels = _
    exact sound4440 B hB hF
  have h4442 : mixedVector B (Sum.inr 4442) = Sparse.eval nodeValue4442 (mixedVector B) := by
    change mixedMoment B node4442 node4442Labels = _
    exact sound4442 B hB hF
  have h4460 : mixedVector B (Sum.inr 4460) = Sparse.eval nodeValue4460 (mixedVector B) := by
    change mixedMoment B node4460 node4460Labels = _
    exact sound4460 B hB hF
  have h4463 : mixedVector B (Sum.inr 4463) = Sparse.eval nodeValue4463 (mixedVector B) := by
    change mixedMoment B node4463 node4463Labels = _
    exact sound4463 B hB hF
  have h4464 : mixedVector B (Sum.inr 4464) = Sparse.eval nodeValue4464 (mixedVector B) := by
    change mixedMoment B node4464 node4464Labels = _
    exact sound4464 B hB hF
  have h4476 : mixedVector B (Sum.inr 4476) = Sparse.eval nodeValue4476 (mixedVector B) := by
    change mixedMoment B node4476 node4476Labels = _
    exact sound4476 B hB hF
  have h4478 : mixedVector B (Sum.inr 4478) = Sparse.eval nodeValue4478 (mixedVector B) := by
    change mixedMoment B node4478 node4478Labels = _
    exact sound4478 B hB hF
  have h4505 : mixedVector B (Sum.inr 4505) = Sparse.eval nodeValue4505 (mixedVector B) := by
    change mixedMoment B node4505 node4505Labels = _
    exact sound4505 B hB hF
  have h4507 : mixedVector B (Sum.inr 4507) = Sparse.eval nodeValue4507 (mixedVector B) := by
    change mixedMoment B node4507 node4507Labels = _
    exact sound4507 B hB hF
  have h4591 : mixedVector B (Sum.inr 4591) = Sparse.eval nodeValue4591 (mixedVector B) := by
    change mixedMoment B node4591 node4591Labels = _
    exact sound4591 B hB hF
  have h4605 : mixedVector B (Sum.inr 4605) = Sparse.eval nodeValue4605 (mixedVector B) := by
    change mixedMoment B node4605 node4605Labels = _
    exact sound4605 B hB hF
  have h4608 : mixedVector B (Sum.inr 4608) = Sparse.eval nodeValue4608 (mixedVector B) := by
    change mixedMoment B node4608 node4608Labels = _
    exact sound4608 B hB hF
  have h4625 : mixedVector B (Sum.inr 4625) = Sparse.eval nodeValue4625 (mixedVector B) := by
    change mixedMoment B node4625 node4625Labels = _
    exact sound4625 B hB hF
  simpa only [sourceForm1344, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4253, h4269, h4270, h4276, h4391, h4401, h4402, h4410, h4440, h4442, h4460, h4463, h4464, h4476, h4478, h4505, h4507, h4591, h4605, h4608, h4625, reducedSource1166] using sourceEq1344 B hB

theorem rowSound1166 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1166 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1166, numericCheck1166, reducedZero1166 B hB hF, mul_zero]

theorem reducedZero1167 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1167 (mixedVector B) = 0 := by
  have h787 : mixedVector B (Sum.inr 787) = Sparse.eval nodeValue787 (mixedVector B) := by
    change mixedMoment B node787 node787Labels = _
    exact sound787 B hB hF
  have h812 : mixedVector B (Sum.inr 812) = Sparse.eval nodeValue812 (mixedVector B) := by
    change mixedMoment B node812 node812Labels = _
    exact sound812 B hB hF
  have h813 : mixedVector B (Sum.inr 813) = Sparse.eval nodeValue813 (mixedVector B) := by
    change mixedMoment B node813 node813Labels = _
    exact sound813 B hB hF
  have h828 : mixedVector B (Sum.inr 828) = Sparse.eval nodeValue828 (mixedVector B) := by
    change mixedMoment B node828 node828Labels = _
    exact sound828 B hB hF
  have h972 : mixedVector B (Sum.inr 972) = Sparse.eval nodeValue972 (mixedVector B) := by
    change mixedMoment B node972 node972Labels = _
    exact sound972 B hB hF
  have h982 : mixedVector B (Sum.inr 982) = Sparse.eval nodeValue982 (mixedVector B) := by
    change mixedMoment B node982 node982Labels = _
    exact sound982 B hB hF
  have h983 : mixedVector B (Sum.inr 983) = Sparse.eval nodeValue983 (mixedVector B) := by
    change mixedMoment B node983 node983Labels = _
    exact sound983 B hB hF
  have h991 : mixedVector B (Sum.inr 991) = Sparse.eval nodeValue991 (mixedVector B) := by
    change mixedMoment B node991 node991Labels = _
    exact sound991 B hB hF
  have h1022 : mixedVector B (Sum.inr 1022) = Sparse.eval nodeValue1022 (mixedVector B) := by
    change mixedMoment B node1022 node1022Labels = _
    exact sound1022 B hB hF
  have h1024 : mixedVector B (Sum.inr 1024) = Sparse.eval nodeValue1024 (mixedVector B) := by
    change mixedMoment B node1024 node1024Labels = _
    exact sound1024 B hB hF
  have h1043 : mixedVector B (Sum.inr 1043) = Sparse.eval nodeValue1043 (mixedVector B) := by
    change mixedMoment B node1043 node1043Labels = _
    exact sound1043 B hB hF
  have h1046 : mixedVector B (Sum.inr 1046) = Sparse.eval nodeValue1046 (mixedVector B) := by
    change mixedMoment B node1046 node1046Labels = _
    exact sound1046 B hB hF
  have h1047 : mixedVector B (Sum.inr 1047) = Sparse.eval nodeValue1047 (mixedVector B) := by
    change mixedMoment B node1047 node1047Labels = _
    exact sound1047 B hB hF
  have h1059 : mixedVector B (Sum.inr 1059) = Sparse.eval nodeValue1059 (mixedVector B) := by
    change mixedMoment B node1059 node1059Labels = _
    exact sound1059 B hB hF
  have h1061 : mixedVector B (Sum.inr 1061) = Sparse.eval nodeValue1061 (mixedVector B) := by
    change mixedMoment B node1061 node1061Labels = _
    exact sound1061 B hB hF
  have h1089 : mixedVector B (Sum.inr 1089) = Sparse.eval nodeValue1089 (mixedVector B) := by
    change mixedMoment B node1089 node1089Labels = _
    exact sound1089 B hB hF
  have h1091 : mixedVector B (Sum.inr 1091) = Sparse.eval nodeValue1091 (mixedVector B) := by
    change mixedMoment B node1091 node1091Labels = _
    exact sound1091 B hB hF
  have h1217 : mixedVector B (Sum.inr 1217) = Sparse.eval nodeValue1217 (mixedVector B) := by
    change mixedMoment B node1217 node1217Labels = _
    exact sound1217 B hB hF
  have h1269 : mixedVector B (Sum.inr 1269) = Sparse.eval nodeValue1269 (mixedVector B) := by
    change mixedMoment B node1269 node1269Labels = _
    exact sound1269 B hB hF
  have h1271 : mixedVector B (Sum.inr 1271) = Sparse.eval nodeValue1271 (mixedVector B) := by
    change mixedMoment B node1271 node1271Labels = _
    exact sound1271 B hB hF
  have h1307 : mixedVector B (Sum.inr 1307) = Sparse.eval nodeValue1307 (mixedVector B) := by
    change mixedMoment B node1307 node1307Labels = _
    exact sound1307 B hB hF
  simpa only [sourceForm1345, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h787, h812, h813, h828, h972, h982, h983, h991, h1022, h1024, h1043, h1046, h1047, h1059, h1061, h1089, h1091, h1217, h1269, h1271, h1307, reducedSource1167] using sourceEq1345 B hB

theorem rowSound1167 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1167 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1167, numericCheck1167, reducedZero1167 B hB hF, mul_zero]

theorem sourceRowsAt1152 : MixedData.sourceRows (1152 : Fin 2425) =
    MixedData.row1152 := by decide +kernel

theorem sourceRowsAt1153 : MixedData.sourceRows (1153 : Fin 2425) =
    MixedData.row1153 := by decide +kernel

theorem sourceRowsAt1154 : MixedData.sourceRows (1154 : Fin 2425) =
    MixedData.row1154 := by decide +kernel

theorem sourceRowsAt1155 : MixedData.sourceRows (1155 : Fin 2425) =
    MixedData.row1155 := by decide +kernel

theorem sourceRowsAt1156 : MixedData.sourceRows (1156 : Fin 2425) =
    MixedData.row1156 := by decide +kernel

theorem sourceRowsAt1157 : MixedData.sourceRows (1157 : Fin 2425) =
    MixedData.row1157 := by decide +kernel

theorem sourceRowsAt1158 : MixedData.sourceRows (1158 : Fin 2425) =
    MixedData.row1158 := by decide +kernel

theorem sourceRowsAt1159 : MixedData.sourceRows (1159 : Fin 2425) =
    MixedData.row1159 := by decide +kernel

theorem sourceRowsAt1160 : MixedData.sourceRows (1160 : Fin 2425) =
    MixedData.row1160 := by decide +kernel

theorem sourceRowsAt1161 : MixedData.sourceRows (1161 : Fin 2425) =
    MixedData.row1161 := by decide +kernel

theorem sourceRowsAt1162 : MixedData.sourceRows (1162 : Fin 2425) =
    MixedData.row1162 := by decide +kernel

theorem sourceRowsAt1163 : MixedData.sourceRows (1163 : Fin 2425) =
    MixedData.row1163 := by decide +kernel

theorem sourceRowsAt1164 : MixedData.sourceRows (1164 : Fin 2425) =
    MixedData.row1164 := by decide +kernel

theorem sourceRowsAt1165 : MixedData.sourceRows (1165 : Fin 2425) =
    MixedData.row1165 := by decide +kernel

theorem sourceRowsAt1166 : MixedData.sourceRows (1166 : Fin 2425) =
    MixedData.row1166 := by decide +kernel

theorem sourceRowsAt1167 : MixedData.sourceRows (1167 : Fin 2425) =
    MixedData.row1167 := by decide +kernel

theorem chunkSound72 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 72) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1152 ∨ k.val = 1153 ∨ k.val = 1154 ∨ k.val = 1155 ∨ k.val = 1156 ∨ k.val = 1157 ∨ k.val = 1158 ∨ k.val = 1159 ∨ k.val = 1160 ∨ k.val = 1161 ∨ k.val = 1162 ∨ k.val = 1163 ∨ k.val = 1164 ∨ k.val = 1165 ∨ k.val = 1166 ∨ k.val = 1167 := by omega
  rcases heq with h1152 | h1153 | h1154 | h1155 | h1156 | h1157 | h1158 | h1159 | h1160 | h1161 | h1162 | h1163 | h1164 | h1165 | h1166 | h1167
  · have he : k = (1152 : Fin 2425) := Fin.ext h1152
    subst k
    rw [sourceRowsAt1152]
    exact rowSound1152 B hB hF
  · have he : k = (1153 : Fin 2425) := Fin.ext h1153
    subst k
    rw [sourceRowsAt1153]
    exact rowSound1153 B hB hF
  · have he : k = (1154 : Fin 2425) := Fin.ext h1154
    subst k
    rw [sourceRowsAt1154]
    exact rowSound1154 B hB hF
  · have he : k = (1155 : Fin 2425) := Fin.ext h1155
    subst k
    rw [sourceRowsAt1155]
    exact rowSound1155 B hB hF
  · have he : k = (1156 : Fin 2425) := Fin.ext h1156
    subst k
    rw [sourceRowsAt1156]
    exact rowSound1156 B hB hF
  · have he : k = (1157 : Fin 2425) := Fin.ext h1157
    subst k
    rw [sourceRowsAt1157]
    exact rowSound1157 B hB hF
  · have he : k = (1158 : Fin 2425) := Fin.ext h1158
    subst k
    rw [sourceRowsAt1158]
    exact rowSound1158 B hB hF
  · have he : k = (1159 : Fin 2425) := Fin.ext h1159
    subst k
    rw [sourceRowsAt1159]
    exact rowSound1159 B hB hF
  · have he : k = (1160 : Fin 2425) := Fin.ext h1160
    subst k
    rw [sourceRowsAt1160]
    exact rowSound1160 B hB hF
  · have he : k = (1161 : Fin 2425) := Fin.ext h1161
    subst k
    rw [sourceRowsAt1161]
    exact rowSound1161 B hB hF
  · have he : k = (1162 : Fin 2425) := Fin.ext h1162
    subst k
    rw [sourceRowsAt1162]
    exact rowSound1162 B hB hF
  · have he : k = (1163 : Fin 2425) := Fin.ext h1163
    subst k
    rw [sourceRowsAt1163]
    exact rowSound1163 B hB hF
  · have he : k = (1164 : Fin 2425) := Fin.ext h1164
    subst k
    rw [sourceRowsAt1164]
    exact rowSound1164 B hB hF
  · have he : k = (1165 : Fin 2425) := Fin.ext h1165
    subst k
    rw [sourceRowsAt1165]
    exact rowSound1165 B hB hF
  · have he : k = (1166 : Fin 2425) := Fin.ext h1166
    subst k
    rw [sourceRowsAt1166]
    exact rowSound1166 B hB hF
  · have he : k = (1167 : Fin 2425) := Fin.ext h1167
    subst k
    rw [sourceRowsAt1167]
    exact rowSound1167 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
