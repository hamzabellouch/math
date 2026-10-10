import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources37

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1024 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1024 (mixedVector B) = 0 := by
  have h564 : mixedVector B (Sum.inr 564) = Sparse.eval nodeValue564 (mixedVector B) := by
    change mixedMoment B node564 node564Labels = _
    exact sound564 B hB hF
  have h726 : mixedVector B (Sum.inr 726) = Sparse.eval nodeValue726 (mixedVector B) := by
    change mixedMoment B node726 node726Labels = _
    exact sound726 B hB hF
  have h832 : mixedVector B (Sum.inr 832) = Sparse.eval nodeValue832 (mixedVector B) := by
    change mixedMoment B node832 node832Labels = _
    exact sound832 B hB hF
  have h859 : mixedVector B (Sum.inr 859) = Sparse.eval nodeValue859 (mixedVector B) := by
    change mixedMoment B node859 node859Labels = _
    exact sound859 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1179, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h564, h726, h832, h859, h4071, reducedSource1024] using sourceEq1179 B hB

theorem rowSound1024 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1024 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1024, numericCheck1024, reducedZero1024 B hB hF, mul_zero]

theorem reducedZero1025 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1025 (mixedVector B) = 0 := by
  have h832 : mixedVector B (Sum.inr 832) = Sparse.eval nodeValue832 (mixedVector B) := by
    change mixedMoment B node832 node832Labels = _
    exact sound832 B hB hF
  have h1186 : mixedVector B (Sum.inr 1186) = Sparse.eval nodeValue1186 (mixedVector B) := by
    change mixedMoment B node1186 node1186Labels = _
    exact sound1186 B hB hF
  have h1289 : mixedVector B (Sum.inr 1289) = Sparse.eval nodeValue1289 (mixedVector B) := by
    change mixedMoment B node1289 node1289Labels = _
    exact sound1289 B hB hF
  have h1741 : mixedVector B (Sum.inr 1741) = Sparse.eval nodeValue1741 (mixedVector B) := by
    change mixedMoment B node1741 node1741Labels = _
    exact sound1741 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1180, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h832, h1186, h1289, h1741, h4071, reducedSource1025] using sourceEq1180 B hB

theorem rowSound1025 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1025 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1025, numericCheck1025, reducedZero1025 B hB hF, mul_zero]

theorem reducedZero1026 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1026 (mixedVector B) = 0 := by
  have h785 : mixedVector B (Sum.inr 785) = Sparse.eval nodeValue785 (mixedVector B) := by
    change mixedMoment B node785 node785Labels = _
    exact sound785 B hB hF
  have h791 : mixedVector B (Sum.inr 791) = Sparse.eval nodeValue791 (mixedVector B) := by
    change mixedMoment B node791 node791Labels = _
    exact sound791 B hB hF
  have h812 : mixedVector B (Sum.inr 812) = Sparse.eval nodeValue812 (mixedVector B) := by
    change mixedMoment B node812 node812Labels = _
    exact sound812 B hB hF
  have h1710 : mixedVector B (Sum.inr 1710) = Sparse.eval nodeValue1710 (mixedVector B) := by
    change mixedMoment B node1710 node1710Labels = _
    exact sound1710 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1182, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h785, h791, h812, h1710, h4069, reducedSource1026] using sourceEq1182 B hB

theorem rowSound1026 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1026 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1026, numericCheck1026, reducedZero1026 B hB hF, mul_zero]

theorem reducedZero1027 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1027 (mixedVector B) = 0 := by
  have h545 : mixedVector B (Sum.inr 545) = Sparse.eval nodeValue545 (mixedVector B) := by
    change mixedMoment B node545 node545Labels = _
    exact sound545 B hB hF
  have h705 : mixedVector B (Sum.inr 705) = Sparse.eval nodeValue705 (mixedVector B) := by
    change mixedMoment B node705 node705Labels = _
    exact sound705 B hB hF
  have h740 : mixedVector B (Sum.inr 740) = Sparse.eval nodeValue740 (mixedVector B) := by
    change mixedMoment B node740 node740Labels = _
    exact sound740 B hB hF
  have h791 : mixedVector B (Sum.inr 791) = Sparse.eval nodeValue791 (mixedVector B) := by
    change mixedMoment B node791 node791Labels = _
    exact sound791 B hB hF
  have h812 : mixedVector B (Sum.inr 812) = Sparse.eval nodeValue812 (mixedVector B) := by
    change mixedMoment B node812 node812Labels = _
    exact sound812 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1183, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h545, h705, h740, h791, h812, h4069, reducedSource1027] using sourceEq1183 B hB

theorem rowSound1027 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1027 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1027, numericCheck1027, reducedZero1027 B hB hF, mul_zero]

theorem reducedZero1028 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1028 (mixedVector B) = 0 := by
  have h791 : mixedVector B (Sum.inr 791) = Sparse.eval nodeValue791 (mixedVector B) := by
    change mixedMoment B node791 node791Labels = _
    exact sound791 B hB hF
  have h1199 : mixedVector B (Sum.inr 1199) = Sparse.eval nodeValue1199 (mixedVector B) := by
    change mixedMoment B node1199 node1199Labels = _
    exact sound1199 B hB hF
  have h1231 : mixedVector B (Sum.inr 1231) = Sparse.eval nodeValue1231 (mixedVector B) := by
    change mixedMoment B node1231 node1231Labels = _
    exact sound1231 B hB hF
  have h1710 : mixedVector B (Sum.inr 1710) = Sparse.eval nodeValue1710 (mixedVector B) := by
    change mixedMoment B node1710 node1710Labels = _
    exact sound1710 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1184, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h791, h1199, h1231, h1710, h4069, reducedSource1028] using sourceEq1184 B hB

theorem rowSound1028 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1028 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1028, numericCheck1028, reducedZero1028 B hB hF, mul_zero]

theorem reducedZero1029 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1029 (mixedVector B) = 0 := by
  have h979 : mixedVector B (Sum.inr 979) = Sparse.eval nodeValue979 (mixedVector B) := by
    change mixedMoment B node979 node979Labels = _
    exact sound979 B hB hF
  have h986 : mixedVector B (Sum.inr 986) = Sparse.eval nodeValue986 (mixedVector B) := by
    change mixedMoment B node986 node986Labels = _
    exact sound986 B hB hF
  have h1007 : mixedVector B (Sum.inr 1007) = Sparse.eval nodeValue1007 (mixedVector B) := by
    change mixedMoment B node1007 node1007Labels = _
    exact sound1007 B hB hF
  have h1037 : mixedVector B (Sum.inr 1037) = Sparse.eval nodeValue1037 (mixedVector B) := by
    change mixedMoment B node1037 node1037Labels = _
    exact sound1037 B hB hF
  have h2208 : mixedVector B (Sum.inr 2208) = Sparse.eval nodeValue2208 (mixedVector B) := by
    change mixedMoment B node2208 node2208Labels = _
    exact sound2208 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1186, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h979, h986, h1007, h1037, h2208, h4081, reducedSource1029] using sourceEq1186 B hB

theorem rowSound1029 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1029 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1029, numericCheck1029, reducedZero1029 B hB hF, mul_zero]

theorem reducedZero1030 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1030 (mixedVector B) = 0 := by
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  have h4181 : mixedVector B (Sum.inr 4181) = Sparse.eval nodeValue4181 (mixedVector B) := by
    change mixedMoment B node4181 node4181Labels = _
    exact sound4181 B hB hF
  have h4194 : mixedVector B (Sum.inr 4194) = Sparse.eval nodeValue4194 (mixedVector B) := by
    change mixedMoment B node4194 node4194Labels = _
    exact sound4194 B hB hF
  have h4350 : mixedVector B (Sum.inr 4350) = Sparse.eval nodeValue4350 (mixedVector B) := by
    change mixedMoment B node4350 node4350Labels = _
    exact sound4350 B hB hF
  have h4501 : mixedVector B (Sum.inr 4501) = Sparse.eval nodeValue4501 (mixedVector B) := by
    change mixedMoment B node4501 node4501Labels = _
    exact sound4501 B hB hF
  simpa only [sourceForm1189, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4085, h4181, h4194, h4350, h4501, reducedSource1030] using sourceEq1189 B hB

theorem rowSound1030 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1030 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1030, numericCheck1030, reducedZero1030 B hB hF, mul_zero]

theorem reducedZero1031 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1031 (mixedVector B) = 0 := by
  have h1521 : mixedVector B (Sum.inr 1521) = Sparse.eval nodeValue1521 (mixedVector B) := by
    change mixedMoment B node1521 node1521Labels = _
    exact sound1521 B hB hF
  have h1541 : mixedVector B (Sum.inr 1541) = Sparse.eval nodeValue1541 (mixedVector B) := by
    change mixedMoment B node1541 node1541Labels = _
    exact sound1541 B hB hF
  have h1677 : mixedVector B (Sum.inr 1677) = Sparse.eval nodeValue1677 (mixedVector B) := by
    change mixedMoment B node1677 node1677Labels = _
    exact sound1677 B hB hF
  have h1730 : mixedVector B (Sum.inr 1730) = Sparse.eval nodeValue1730 (mixedVector B) := by
    change mixedMoment B node1730 node1730Labels = _
    exact sound1730 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm1190, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1521, h1541, h1677, h1730, h4085, reducedSource1031] using sourceEq1190 B hB

theorem rowSound1031 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1031 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1031, numericCheck1031, reducedZero1031 B hB hF, mul_zero]

theorem reducedZero1032 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1032 (mixedVector B) = 0 := by
  have h609 : mixedVector B (Sum.inr 609) = Sparse.eval nodeValue609 (mixedVector B) := by
    change mixedMoment B node609 node609Labels = _
    exact sound609 B hB hF
  have h622 : mixedVector B (Sum.inr 622) = Sparse.eval nodeValue622 (mixedVector B) := by
    change mixedMoment B node622 node622Labels = _
    exact sound622 B hB hF
  have h1096 : mixedVector B (Sum.inr 1096) = Sparse.eval nodeValue1096 (mixedVector B) := by
    change mixedMoment B node1096 node1096Labels = _
    exact sound1096 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm1191, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h609, h622, h1096, h4085, reducedSource1032] using sourceEq1191 B hB

theorem rowSound1032 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1032 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1032, numericCheck1032, reducedZero1032 B hB hF, mul_zero]

theorem reducedZero1033 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1033 (mixedVector B) = 0 := by
  have h4072 : mixedVector B (Sum.inr 4072) = Sparse.eval nodeValue4072 (mixedVector B) := by
    change mixedMoment B node4072 node4072Labels = _
    exact sound4072 B hB hF
  have h4274 : mixedVector B (Sum.inr 4274) = Sparse.eval nodeValue4274 (mixedVector B) := by
    change mixedMoment B node4274 node4274Labels = _
    exact sound4274 B hB hF
  have h4405 : mixedVector B (Sum.inr 4405) = Sparse.eval nodeValue4405 (mixedVector B) := by
    change mixedMoment B node4405 node4405Labels = _
    exact sound4405 B hB hF
  have h4468 : mixedVector B (Sum.inr 4468) = Sparse.eval nodeValue4468 (mixedVector B) := by
    change mixedMoment B node4468 node4468Labels = _
    exact sound4468 B hB hF
  have h4629 : mixedVector B (Sum.inr 4629) = Sparse.eval nodeValue4629 (mixedVector B) := by
    change mixedMoment B node4629 node4629Labels = _
    exact sound4629 B hB hF
  simpa only [sourceForm1192, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4072, h4274, h4405, h4468, h4629, reducedSource1033] using sourceEq1192 B hB

theorem rowSound1033 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1033 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1033, numericCheck1033, reducedZero1033 B hB hF, mul_zero]

theorem reducedZero1034 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1034 (mixedVector B) = 0 := by
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  have h4103 : mixedVector B (Sum.inr 4103) = Sparse.eval nodeValue4103 (mixedVector B) := by
    change mixedMoment B node4103 node4103Labels = _
    exact sound4103 B hB hF
  have h4112 : mixedVector B (Sum.inr 4112) = Sparse.eval nodeValue4112 (mixedVector B) := by
    change mixedMoment B node4112 node4112Labels = _
    exact sound4112 B hB hF
  have h4131 : mixedVector B (Sum.inr 4131) = Sparse.eval nodeValue4131 (mixedVector B) := by
    change mixedMoment B node4131 node4131Labels = _
    exact sound4131 B hB hF
  have h4142 : mixedVector B (Sum.inr 4142) = Sparse.eval nodeValue4142 (mixedVector B) := by
    change mixedMoment B node4142 node4142Labels = _
    exact sound4142 B hB hF
  have h4168 : mixedVector B (Sum.inr 4168) = Sparse.eval nodeValue4168 (mixedVector B) := by
    change mixedMoment B node4168 node4168Labels = _
    exact sound4168 B hB hF
  have h4198 : mixedVector B (Sum.inr 4198) = Sparse.eval nodeValue4198 (mixedVector B) := by
    change mixedMoment B node4198 node4198Labels = _
    exact sound4198 B hB hF
  have h4222 : mixedVector B (Sum.inr 4222) = Sparse.eval nodeValue4222 (mixedVector B) := by
    change mixedMoment B node4222 node4222Labels = _
    exact sound4222 B hB hF
  have h4235 : mixedVector B (Sum.inr 4235) = Sparse.eval nodeValue4235 (mixedVector B) := by
    change mixedMoment B node4235 node4235Labels = _
    exact sound4235 B hB hF
  have h4266 : mixedVector B (Sum.inr 4266) = Sparse.eval nodeValue4266 (mixedVector B) := by
    change mixedMoment B node4266 node4266Labels = _
    exact sound4266 B hB hF
  have h4421 : mixedVector B (Sum.inr 4421) = Sparse.eval nodeValue4421 (mixedVector B) := by
    change mixedMoment B node4421 node4421Labels = _
    exact sound4421 B hB hF
  have h4493 : mixedVector B (Sum.inr 4493) = Sparse.eval nodeValue4493 (mixedVector B) := by
    change mixedMoment B node4493 node4493Labels = _
    exact sound4493 B hB hF
  have h4501 : mixedVector B (Sum.inr 4501) = Sparse.eval nodeValue4501 (mixedVector B) := by
    change mixedMoment B node4501 node4501Labels = _
    exact sound4501 B hB hF
  simpa only [sourceForm1193, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4070, h4103, h4112, h4131, h4142, h4168, h4198, h4222, h4235, h4266, h4421, h4493, h4501, reducedSource1034] using sourceEq1193 B hB

theorem rowSound1034 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1034 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1034, numericCheck1034, reducedZero1034 B hB hF, mul_zero]

theorem reducedZero1035 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1035 (mixedVector B) = 0 := by
  have h665 : mixedVector B (Sum.inr 665) = Sparse.eval nodeValue665 (mixedVector B) := by
    change mixedMoment B node665 node665Labels = _
    exact sound665 B hB hF
  have h686 : mixedVector B (Sum.inr 686) = Sparse.eval nodeValue686 (mixedVector B) := by
    change mixedMoment B node686 node686Labels = _
    exact sound686 B hB hF
  have h691 : mixedVector B (Sum.inr 691) = Sparse.eval nodeValue691 (mixedVector B) := by
    change mixedMoment B node691 node691Labels = _
    exact sound691 B hB hF
  have h750 : mixedVector B (Sum.inr 750) = Sparse.eval nodeValue750 (mixedVector B) := by
    change mixedMoment B node750 node750Labels = _
    exact sound750 B hB hF
  have h765 : mixedVector B (Sum.inr 765) = Sparse.eval nodeValue765 (mixedVector B) := by
    change mixedMoment B node765 node765Labels = _
    exact sound765 B hB hF
  have h770 : mixedVector B (Sum.inr 770) = Sparse.eval nodeValue770 (mixedVector B) := by
    change mixedMoment B node770 node770Labels = _
    exact sound770 B hB hF
  have h801 : mixedVector B (Sum.inr 801) = Sparse.eval nodeValue801 (mixedVector B) := by
    change mixedMoment B node801 node801Labels = _
    exact sound801 B hB hF
  have h809 : mixedVector B (Sum.inr 809) = Sparse.eval nodeValue809 (mixedVector B) := by
    change mixedMoment B node809 node809Labels = _
    exact sound809 B hB hF
  have h845 : mixedVector B (Sum.inr 845) = Sparse.eval nodeValue845 (mixedVector B) := by
    change mixedMoment B node845 node845Labels = _
    exact sound845 B hB hF
  have h1002 : mixedVector B (Sum.inr 1002) = Sparse.eval nodeValue1002 (mixedVector B) := by
    change mixedMoment B node1002 node1002Labels = _
    exact sound1002 B hB hF
  have h1077 : mixedVector B (Sum.inr 1077) = Sparse.eval nodeValue1077 (mixedVector B) := by
    change mixedMoment B node1077 node1077Labels = _
    exact sound1077 B hB hF
  have h1085 : mixedVector B (Sum.inr 1085) = Sparse.eval nodeValue1085 (mixedVector B) := by
    change mixedMoment B node1085 node1085Labels = _
    exact sound1085 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1194, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h665, h686, h691, h750, h765, h770, h801, h809, h845, h1002, h1077, h1085, h4070, reducedSource1035] using sourceEq1194 B hB

theorem rowSound1035 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1035 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1035, numericCheck1035, reducedZero1035 B hB hF, mul_zero]

theorem reducedZero1036 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1036 (mixedVector B) = 0 := by
  have h549 : mixedVector B (Sum.inr 549) = Sparse.eval nodeValue549 (mixedVector B) := by
    change mixedMoment B node549 node549Labels = _
    exact sound549 B hB hF
  have h570 : mixedVector B (Sum.inr 570) = Sparse.eval nodeValue570 (mixedVector B) := by
    change mixedMoment B node570 node570Labels = _
    exact sound570 B hB hF
  have h596 : mixedVector B (Sum.inr 596) = Sparse.eval nodeValue596 (mixedVector B) := by
    change mixedMoment B node596 node596Labels = _
    exact sound596 B hB hF
  have h817 : mixedVector B (Sum.inr 817) = Sparse.eval nodeValue817 (mixedVector B) := by
    change mixedMoment B node817 node817Labels = _
    exact sound817 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1195, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h549, h570, h596, h817, h4070, reducedSource1036] using sourceEq1195 B hB

theorem rowSound1036 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1036 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1036, numericCheck1036, reducedZero1036 B hB hF, mul_zero]

theorem reducedZero1037 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1037 (mixedVector B) = 0 := by
  have h540 : mixedVector B (Sum.inr 540) = Sparse.eval nodeValue540 (mixedVector B) := by
    change mixedMoment B node540 node540Labels = _
    exact sound540 B hB hF
  have h701 : mixedVector B (Sum.inr 701) = Sparse.eval nodeValue701 (mixedVector B) := by
    change mixedMoment B node701 node701Labels = _
    exact sound701 B hB hF
  have h735 : mixedVector B (Sum.inr 735) = Sparse.eval nodeValue735 (mixedVector B) := by
    change mixedMoment B node735 node735Labels = _
    exact sound735 B hB hF
  have h809 : mixedVector B (Sum.inr 809) = Sparse.eval nodeValue809 (mixedVector B) := by
    change mixedMoment B node809 node809Labels = _
    exact sound809 B hB hF
  have h817 : mixedVector B (Sum.inr 817) = Sparse.eval nodeValue817 (mixedVector B) := by
    change mixedMoment B node817 node817Labels = _
    exact sound817 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1197, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h540, h701, h735, h809, h817, h4070, reducedSource1037] using sourceEq1197 B hB

theorem rowSound1037 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1037 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1037, numericCheck1037, reducedZero1037 B hB hF, mul_zero]

theorem reducedZero1038 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1038 (mixedVector B) = 0 := by
  have h596 : mixedVector B (Sum.inr 596) = Sparse.eval nodeValue596 (mixedVector B) := by
    change mixedMoment B node596 node596Labels = _
    exact sound596 B hB hF
  have h735 : mixedVector B (Sum.inr 735) = Sparse.eval nodeValue735 (mixedVector B) := by
    change mixedMoment B node735 node735Labels = _
    exact sound735 B hB hF
  have h817 : mixedVector B (Sum.inr 817) = Sparse.eval nodeValue817 (mixedVector B) := by
    change mixedMoment B node817 node817Labels = _
    exact sound817 B hB hF
  have h1077 : mixedVector B (Sum.inr 1077) = Sparse.eval nodeValue1077 (mixedVector B) := by
    change mixedMoment B node1077 node1077Labels = _
    exact sound1077 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1198, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h596, h735, h817, h1077, h4070, reducedSource1038] using sourceEq1198 B hB

theorem rowSound1038 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1038 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1038, numericCheck1038, reducedZero1038 B hB hF, mul_zero]

theorem reducedZero1039 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1039 (mixedVector B) = 0 := by
  have h4060 : mixedVector B (Sum.inr 4060) = Sparse.eval nodeValue4060 (mixedVector B) := by
    change mixedMoment B node4060 node4060Labels = _
    exact sound4060 B hB hF
  have h4062 : mixedVector B (Sum.inr 4062) = Sparse.eval nodeValue4062 (mixedVector B) := by
    change mixedMoment B node4062 node4062Labels = _
    exact sound4062 B hB hF
  have h4066 : mixedVector B (Sum.inr 4066) = Sparse.eval nodeValue4066 (mixedVector B) := by
    change mixedMoment B node4066 node4066Labels = _
    exact sound4066 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm1200, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4060, h4062, h4066, h4070, h4085, reducedSource1039] using sourceEq1200 B hB

theorem rowSound1039 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1039 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1039, numericCheck1039, reducedZero1039 B hB hF, mul_zero]

theorem sourceRowsAt1024 : MixedData.sourceRows (1024 : Fin 2425) =
    MixedData.row1024 := by decide +kernel

theorem sourceRowsAt1025 : MixedData.sourceRows (1025 : Fin 2425) =
    MixedData.row1025 := by decide +kernel

theorem sourceRowsAt1026 : MixedData.sourceRows (1026 : Fin 2425) =
    MixedData.row1026 := by decide +kernel

theorem sourceRowsAt1027 : MixedData.sourceRows (1027 : Fin 2425) =
    MixedData.row1027 := by decide +kernel

theorem sourceRowsAt1028 : MixedData.sourceRows (1028 : Fin 2425) =
    MixedData.row1028 := by decide +kernel

theorem sourceRowsAt1029 : MixedData.sourceRows (1029 : Fin 2425) =
    MixedData.row1029 := by decide +kernel

theorem sourceRowsAt1030 : MixedData.sourceRows (1030 : Fin 2425) =
    MixedData.row1030 := by decide +kernel

theorem sourceRowsAt1031 : MixedData.sourceRows (1031 : Fin 2425) =
    MixedData.row1031 := by decide +kernel

theorem sourceRowsAt1032 : MixedData.sourceRows (1032 : Fin 2425) =
    MixedData.row1032 := by decide +kernel

theorem sourceRowsAt1033 : MixedData.sourceRows (1033 : Fin 2425) =
    MixedData.row1033 := by decide +kernel

theorem sourceRowsAt1034 : MixedData.sourceRows (1034 : Fin 2425) =
    MixedData.row1034 := by decide +kernel

theorem sourceRowsAt1035 : MixedData.sourceRows (1035 : Fin 2425) =
    MixedData.row1035 := by decide +kernel

theorem sourceRowsAt1036 : MixedData.sourceRows (1036 : Fin 2425) =
    MixedData.row1036 := by decide +kernel

theorem sourceRowsAt1037 : MixedData.sourceRows (1037 : Fin 2425) =
    MixedData.row1037 := by decide +kernel

theorem sourceRowsAt1038 : MixedData.sourceRows (1038 : Fin 2425) =
    MixedData.row1038 := by decide +kernel

theorem sourceRowsAt1039 : MixedData.sourceRows (1039 : Fin 2425) =
    MixedData.row1039 := by decide +kernel

theorem chunkSound64 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 64) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1024 ∨ k.val = 1025 ∨ k.val = 1026 ∨ k.val = 1027 ∨ k.val = 1028 ∨ k.val = 1029 ∨ k.val = 1030 ∨ k.val = 1031 ∨ k.val = 1032 ∨ k.val = 1033 ∨ k.val = 1034 ∨ k.val = 1035 ∨ k.val = 1036 ∨ k.val = 1037 ∨ k.val = 1038 ∨ k.val = 1039 := by omega
  rcases heq with h1024 | h1025 | h1026 | h1027 | h1028 | h1029 | h1030 | h1031 | h1032 | h1033 | h1034 | h1035 | h1036 | h1037 | h1038 | h1039
  · have he : k = (1024 : Fin 2425) := Fin.ext h1024
    subst k
    rw [sourceRowsAt1024]
    exact rowSound1024 B hB hF
  · have he : k = (1025 : Fin 2425) := Fin.ext h1025
    subst k
    rw [sourceRowsAt1025]
    exact rowSound1025 B hB hF
  · have he : k = (1026 : Fin 2425) := Fin.ext h1026
    subst k
    rw [sourceRowsAt1026]
    exact rowSound1026 B hB hF
  · have he : k = (1027 : Fin 2425) := Fin.ext h1027
    subst k
    rw [sourceRowsAt1027]
    exact rowSound1027 B hB hF
  · have he : k = (1028 : Fin 2425) := Fin.ext h1028
    subst k
    rw [sourceRowsAt1028]
    exact rowSound1028 B hB hF
  · have he : k = (1029 : Fin 2425) := Fin.ext h1029
    subst k
    rw [sourceRowsAt1029]
    exact rowSound1029 B hB hF
  · have he : k = (1030 : Fin 2425) := Fin.ext h1030
    subst k
    rw [sourceRowsAt1030]
    exact rowSound1030 B hB hF
  · have he : k = (1031 : Fin 2425) := Fin.ext h1031
    subst k
    rw [sourceRowsAt1031]
    exact rowSound1031 B hB hF
  · have he : k = (1032 : Fin 2425) := Fin.ext h1032
    subst k
    rw [sourceRowsAt1032]
    exact rowSound1032 B hB hF
  · have he : k = (1033 : Fin 2425) := Fin.ext h1033
    subst k
    rw [sourceRowsAt1033]
    exact rowSound1033 B hB hF
  · have he : k = (1034 : Fin 2425) := Fin.ext h1034
    subst k
    rw [sourceRowsAt1034]
    exact rowSound1034 B hB hF
  · have he : k = (1035 : Fin 2425) := Fin.ext h1035
    subst k
    rw [sourceRowsAt1035]
    exact rowSound1035 B hB hF
  · have he : k = (1036 : Fin 2425) := Fin.ext h1036
    subst k
    rw [sourceRowsAt1036]
    exact rowSound1036 B hB hF
  · have he : k = (1037 : Fin 2425) := Fin.ext h1037
    subst k
    rw [sourceRowsAt1037]
    exact rowSound1037 B hB hF
  · have he : k = (1038 : Fin 2425) := Fin.ext h1038
    subst k
    rw [sourceRowsAt1038]
    exact rowSound1038 B hB hF
  · have he : k = (1039 : Fin 2425) := Fin.ext h1039
    subst k
    rw [sourceRowsAt1039]
    exact rowSound1039 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
