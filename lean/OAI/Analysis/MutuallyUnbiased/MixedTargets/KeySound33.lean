import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical316

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1056 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1056) =
      Integer.Sparse.eval keyMomentRow1056 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1056).leftCharge (GramAssembly.key 1056).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1321) := by
    have ha : gramCharges (GramAssembly.key 1056).leftCharge (GramAssembly.key 1056).rightCharge = raw40495 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40495Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40495 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1056).leftCharge (GramAssembly.key 1056).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1056, Integer.Sparse.eval]

theorem keyMoment1057 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1057) =
      Integer.Sparse.eval keyMomentRow1057 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1057).leftCharge (GramAssembly.key 1057).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1335) := by
    have ha : gramCharges (GramAssembly.key 1057).leftCharge (GramAssembly.key 1057).rightCharge = raw40496 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40496Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40496 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1057).leftCharge (GramAssembly.key 1057).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1057, Integer.Sparse.eval]

theorem keyMoment1058 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1058) =
      Integer.Sparse.eval keyMomentRow1058 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1058).leftCharge (GramAssembly.key 1058).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1330) := by
    have ha : gramCharges (GramAssembly.key 1058).leftCharge (GramAssembly.key 1058).rightCharge = raw40497 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40497Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40497 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1058).leftCharge (GramAssembly.key 1058).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1058, Integer.Sparse.eval]

theorem keyMoment1059 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1059) =
      Integer.Sparse.eval keyMomentRow1059 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1059).leftCharge (GramAssembly.key 1059).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1314) := by
    have ha : gramCharges (GramAssembly.key 1059).leftCharge (GramAssembly.key 1059).rightCharge = raw40498 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40498Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40498 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1059).leftCharge (GramAssembly.key 1059).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1059, Integer.Sparse.eval]

theorem keyMoment1060 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1060) =
      Integer.Sparse.eval keyMomentRow1060 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1060).leftCharge (GramAssembly.key 1060).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1383) := by
    have ha : gramCharges (GramAssembly.key 1060).leftCharge (GramAssembly.key 1060).rightCharge = raw40499 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40499Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40499 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1060).leftCharge (GramAssembly.key 1060).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1060, Integer.Sparse.eval]

theorem keyMoment1061 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1061) =
      Integer.Sparse.eval keyMomentRow1061 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1061).leftCharge (GramAssembly.key 1061).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1375) := by
    have ha : gramCharges (GramAssembly.key 1061).leftCharge (GramAssembly.key 1061).rightCharge = raw40500 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40500Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40500 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1061).leftCharge (GramAssembly.key 1061).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1061, Integer.Sparse.eval]

theorem keyMoment1062 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1062) =
      Integer.Sparse.eval keyMomentRow1062 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1062).leftCharge (GramAssembly.key 1062).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1325) := by
    have ha : gramCharges (GramAssembly.key 1062).leftCharge (GramAssembly.key 1062).rightCharge = raw40501 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40501Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40501 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1062).leftCharge (GramAssembly.key 1062).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1062, Integer.Sparse.eval]

theorem keyMoment1063 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1063) =
      Integer.Sparse.eval keyMomentRow1063 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1063).leftCharge (GramAssembly.key 1063).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1338) := by
    have ha : gramCharges (GramAssembly.key 1063).leftCharge (GramAssembly.key 1063).rightCharge = raw40502 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40502Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40502 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1063).leftCharge (GramAssembly.key 1063).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1063, Integer.Sparse.eval]

theorem keyMoment1064 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1064) =
      Integer.Sparse.eval keyMomentRow1064 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1064).leftCharge (GramAssembly.key 1064).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1334) := by
    have ha : gramCharges (GramAssembly.key 1064).leftCharge (GramAssembly.key 1064).rightCharge = raw40503 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40503Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40503 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1064).leftCharge (GramAssembly.key 1064).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1064, Integer.Sparse.eval]

theorem keyMoment1065 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1065) =
      Integer.Sparse.eval keyMomentRow1065 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1065).leftCharge (GramAssembly.key 1065).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1318) := by
    have ha : gramCharges (GramAssembly.key 1065).leftCharge (GramAssembly.key 1065).rightCharge = raw40504 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40504Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40504 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1065).leftCharge (GramAssembly.key 1065).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1065, Integer.Sparse.eval]

theorem keyMoment1066 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1066) =
      Integer.Sparse.eval keyMomentRow1066 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1066).leftCharge (GramAssembly.key 1066).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1391) := by
    have ha : gramCharges (GramAssembly.key 1066).leftCharge (GramAssembly.key 1066).rightCharge = raw40505 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40505Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40505 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1066).leftCharge (GramAssembly.key 1066).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1066, Integer.Sparse.eval]

theorem keyMoment1067 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1067) =
      Integer.Sparse.eval keyMomentRow1067 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1067).leftCharge (GramAssembly.key 1067).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1328) := by
    have ha : gramCharges (GramAssembly.key 1067).leftCharge (GramAssembly.key 1067).rightCharge = raw40506 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40506Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40506 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1067).leftCharge (GramAssembly.key 1067).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1067, Integer.Sparse.eval]

theorem keyMoment1068 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1068) =
      Integer.Sparse.eval keyMomentRow1068 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1068).leftCharge (GramAssembly.key 1068).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1435) := by
    have ha : gramCharges (GramAssembly.key 1068).leftCharge (GramAssembly.key 1068).rightCharge = raw40507 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40507Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40507 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1068).leftCharge (GramAssembly.key 1068).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1068, Integer.Sparse.eval]

theorem keyMoment1069 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1069) =
      Integer.Sparse.eval keyMomentRow1069 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1069).leftCharge (GramAssembly.key 1069).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1366) := by
    have ha : gramCharges (GramAssembly.key 1069).leftCharge (GramAssembly.key 1069).rightCharge = raw40508 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40508Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40508 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1069).leftCharge (GramAssembly.key 1069).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1069, Integer.Sparse.eval]

theorem keyMoment1070 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1070) =
      Integer.Sparse.eval keyMomentRow1070 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1070).leftCharge (GramAssembly.key 1070).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1319) := by
    have ha : gramCharges (GramAssembly.key 1070).leftCharge (GramAssembly.key 1070).rightCharge = raw40509 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40509Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40509 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1070).leftCharge (GramAssembly.key 1070).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1070, Integer.Sparse.eval]

theorem keyMoment1071 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1071) =
      Integer.Sparse.eval keyMomentRow1071 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1071).leftCharge (GramAssembly.key 1071).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1370) := by
    have ha : gramCharges (GramAssembly.key 1071).leftCharge (GramAssembly.key 1071).rightCharge = raw40510 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40510Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40510 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1071).leftCharge (GramAssembly.key 1071).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1071, Integer.Sparse.eval]

theorem keyMoment1072 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1072) =
      Integer.Sparse.eval keyMomentRow1072 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1072).leftCharge (GramAssembly.key 1072).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1320) := by
    have ha : gramCharges (GramAssembly.key 1072).leftCharge (GramAssembly.key 1072).rightCharge = raw40511 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40511Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40511 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1072).leftCharge (GramAssembly.key 1072).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1072, Integer.Sparse.eval]

theorem keyMoment1073 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1073) =
      Integer.Sparse.eval keyMomentRow1073 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1073).leftCharge (GramAssembly.key 1073).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1316) := by
    have ha : gramCharges (GramAssembly.key 1073).leftCharge (GramAssembly.key 1073).rightCharge = raw40512 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40512Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40512 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1073).leftCharge (GramAssembly.key 1073).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1073, Integer.Sparse.eval]

theorem keyMoment1074 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1074) =
      Integer.Sparse.eval keyMomentRow1074 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1074).leftCharge (GramAssembly.key 1074).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1372) := by
    have ha : gramCharges (GramAssembly.key 1074).leftCharge (GramAssembly.key 1074).rightCharge = raw40513 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40513Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40513 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1074).leftCharge (GramAssembly.key 1074).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1074, Integer.Sparse.eval]

theorem keyMoment1075 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1075) =
      Integer.Sparse.eval keyMomentRow1075 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1075).leftCharge (GramAssembly.key 1075).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1142) := by
    have ha : gramCharges (GramAssembly.key 1075).leftCharge (GramAssembly.key 1075).rightCharge = raw40514 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40514Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40514 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1075).leftCharge (GramAssembly.key 1075).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1075, Integer.Sparse.eval]

theorem keyMoment1076 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1076) =
      Integer.Sparse.eval keyMomentRow1076 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1076).leftCharge (GramAssembly.key 1076).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1337) := by
    have ha : gramCharges (GramAssembly.key 1076).leftCharge (GramAssembly.key 1076).rightCharge = raw40515 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40515Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40515 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1076).leftCharge (GramAssembly.key 1076).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1076, Integer.Sparse.eval]

theorem keyMoment1077 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1077) =
      Integer.Sparse.eval keyMomentRow1077 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1077).leftCharge (GramAssembly.key 1077).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1118) := by
    have ha : gramCharges (GramAssembly.key 1077).leftCharge (GramAssembly.key 1077).rightCharge = raw40516 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40516Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40516 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1077).leftCharge (GramAssembly.key 1077).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1077, Integer.Sparse.eval]

theorem keyMoment1078 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1078) =
      Integer.Sparse.eval keyMomentRow1078 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1078).leftCharge (GramAssembly.key 1078).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1317) := by
    have ha : gramCharges (GramAssembly.key 1078).leftCharge (GramAssembly.key 1078).rightCharge = raw40517 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40517Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40517 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1078).leftCharge (GramAssembly.key 1078).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1078, Integer.Sparse.eval]

theorem keyMoment1079 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1079) =
      Integer.Sparse.eval keyMomentRow1079 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1079).leftCharge (GramAssembly.key 1079).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1388) := by
    have ha : gramCharges (GramAssembly.key 1079).leftCharge (GramAssembly.key 1079).rightCharge = raw40518 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40518Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40518 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1079).leftCharge (GramAssembly.key 1079).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1079, Integer.Sparse.eval]

theorem keyMoment1080 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1080) =
      Integer.Sparse.eval keyMomentRow1080 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1080).leftCharge (GramAssembly.key 1080).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1322) := by
    have ha : gramCharges (GramAssembly.key 1080).leftCharge (GramAssembly.key 1080).rightCharge = raw40519 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40519Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40519 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1080).leftCharge (GramAssembly.key 1080).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1080, Integer.Sparse.eval]

theorem keyMoment1081 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1081) =
      Integer.Sparse.eval keyMomentRow1081 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1081).leftCharge (GramAssembly.key 1081).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1327) := by
    have ha : gramCharges (GramAssembly.key 1081).leftCharge (GramAssembly.key 1081).rightCharge = raw40520 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40520Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40520 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1081).leftCharge (GramAssembly.key 1081).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1081, Integer.Sparse.eval]

theorem keyMoment1082 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1082) =
      Integer.Sparse.eval keyMomentRow1082 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1082).leftCharge (GramAssembly.key 1082).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1064) := by
    have ha : gramCharges (GramAssembly.key 1082).leftCharge (GramAssembly.key 1082).rightCharge = raw40521 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40521Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40521 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1082).leftCharge (GramAssembly.key 1082).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1082, Integer.Sparse.eval]

theorem keyMoment1083 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1083) =
      Integer.Sparse.eval keyMomentRow1083 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1083).leftCharge (GramAssembly.key 1083).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 617) := by
    have ha : gramCharges (GramAssembly.key 1083).leftCharge (GramAssembly.key 1083).rightCharge = raw40522 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40522Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40522 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1083).leftCharge (GramAssembly.key 1083).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1083, Integer.Sparse.eval]

theorem keyMoment1084 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1084) =
      Integer.Sparse.eval keyMomentRow1084 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1084).leftCharge (GramAssembly.key 1084).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 951) := by
    have ha : gramCharges (GramAssembly.key 1084).leftCharge (GramAssembly.key 1084).rightCharge = raw40523 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40523Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40523 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1084).leftCharge (GramAssembly.key 1084).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1084, Integer.Sparse.eval]

theorem keyMoment1085 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1085) =
      Integer.Sparse.eval keyMomentRow1085 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1085).leftCharge (GramAssembly.key 1085).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 587) := by
    have ha : gramCharges (GramAssembly.key 1085).leftCharge (GramAssembly.key 1085).rightCharge = raw40524 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40524Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40524 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1085).leftCharge (GramAssembly.key 1085).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1085, Integer.Sparse.eval]

theorem keyMoment1086 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1086) =
      Integer.Sparse.eval keyMomentRow1086 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1086).leftCharge (GramAssembly.key 1086).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 936) := by
    have ha : gramCharges (GramAssembly.key 1086).leftCharge (GramAssembly.key 1086).rightCharge = raw40525 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40525Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40525 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1086).leftCharge (GramAssembly.key 1086).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1086, Integer.Sparse.eval]

theorem keyMoment1087 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1087) =
      Integer.Sparse.eval keyMomentRow1087 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1087).leftCharge (GramAssembly.key 1087).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1027) := by
    have ha : gramCharges (GramAssembly.key 1087).leftCharge (GramAssembly.key 1087).rightCharge = raw40526 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40526Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40526 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1087).leftCharge (GramAssembly.key 1087).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1087, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
