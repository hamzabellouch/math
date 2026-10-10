import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical316

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1088 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1088) =
      Integer.Sparse.eval keyMomentRow1088 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1088).leftCharge (GramAssembly.key 1088).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1324) := by
    have ha : gramCharges (GramAssembly.key 1088).leftCharge (GramAssembly.key 1088).rightCharge = raw40527 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40527Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40527 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1088).leftCharge (GramAssembly.key 1088).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1088, Integer.Sparse.eval]

theorem keyMoment1089 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1089) =
      Integer.Sparse.eval keyMomentRow1089 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1089).leftCharge (GramAssembly.key 1089).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 911) := by
    have ha : gramCharges (GramAssembly.key 1089).leftCharge (GramAssembly.key 1089).rightCharge = raw40528 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40528Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40528 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1089).leftCharge (GramAssembly.key 1089).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1089, Integer.Sparse.eval]

theorem keyMoment1090 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1090) =
      Integer.Sparse.eval keyMomentRow1090 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1090).leftCharge (GramAssembly.key 1090).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1333) := by
    have ha : gramCharges (GramAssembly.key 1090).leftCharge (GramAssembly.key 1090).rightCharge = raw40529 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40529Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40529 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1090).leftCharge (GramAssembly.key 1090).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1090, Integer.Sparse.eval]

theorem keyMoment1091 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1091) =
      Integer.Sparse.eval keyMomentRow1091 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1091).leftCharge (GramAssembly.key 1091).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 654) := by
    have ha : gramCharges (GramAssembly.key 1091).leftCharge (GramAssembly.key 1091).rightCharge = raw40530 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40530Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40530 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1091).leftCharge (GramAssembly.key 1091).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1091, Integer.Sparse.eval]

theorem keyMoment1092 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1092) =
      Integer.Sparse.eval keyMomentRow1092 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1092).leftCharge (GramAssembly.key 1092).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 639) := by
    have ha : gramCharges (GramAssembly.key 1092).leftCharge (GramAssembly.key 1092).rightCharge = raw40531 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40531Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40531 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1092).leftCharge (GramAssembly.key 1092).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1092, Integer.Sparse.eval]

theorem keyMoment1093 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1093) =
      Integer.Sparse.eval keyMomentRow1093 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1093).leftCharge (GramAssembly.key 1093).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 634) := by
    have ha : gramCharges (GramAssembly.key 1093).leftCharge (GramAssembly.key 1093).rightCharge = raw40532 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40532Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40532 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1093).leftCharge (GramAssembly.key 1093).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1093, Integer.Sparse.eval]

theorem keyMoment1094 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1094) =
      Integer.Sparse.eval keyMomentRow1094 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1094).leftCharge (GramAssembly.key 1094).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 624) := by
    have ha : gramCharges (GramAssembly.key 1094).leftCharge (GramAssembly.key 1094).rightCharge = raw40533 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40533Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40533 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1094).leftCharge (GramAssembly.key 1094).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1094, Integer.Sparse.eval]

theorem keyMoment1095 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1095) =
      Integer.Sparse.eval keyMomentRow1095 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1095).leftCharge (GramAssembly.key 1095).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 653) := by
    have ha : gramCharges (GramAssembly.key 1095).leftCharge (GramAssembly.key 1095).rightCharge = raw40534 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40534Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40534 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1095).leftCharge (GramAssembly.key 1095).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1095, Integer.Sparse.eval]

theorem keyMoment1096 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1096) =
      Integer.Sparse.eval keyMomentRow1096 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1096).leftCharge (GramAssembly.key 1096).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 638) := by
    have ha : gramCharges (GramAssembly.key 1096).leftCharge (GramAssembly.key 1096).rightCharge = raw40535 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40535Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40535 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1096).leftCharge (GramAssembly.key 1096).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1096, Integer.Sparse.eval]

theorem keyMoment1097 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1097) =
      Integer.Sparse.eval keyMomentRow1097 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1097).leftCharge (GramAssembly.key 1097).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 631) := by
    have ha : gramCharges (GramAssembly.key 1097).leftCharge (GramAssembly.key 1097).rightCharge = raw40536 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40536Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40536 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1097).leftCharge (GramAssembly.key 1097).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1097, Integer.Sparse.eval]

theorem keyMoment1098 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1098) =
      Integer.Sparse.eval keyMomentRow1098 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1098).leftCharge (GramAssembly.key 1098).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 623) := by
    have ha : gramCharges (GramAssembly.key 1098).leftCharge (GramAssembly.key 1098).rightCharge = raw40537 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40537Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40537 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1098).leftCharge (GramAssembly.key 1098).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1098, Integer.Sparse.eval]

theorem keyMoment1099 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1099) =
      Integer.Sparse.eval keyMomentRow1099 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1099).leftCharge (GramAssembly.key 1099).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 642) := by
    have ha : gramCharges (GramAssembly.key 1099).leftCharge (GramAssembly.key 1099).rightCharge = raw40538 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40538Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40538 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1099).leftCharge (GramAssembly.key 1099).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1099, Integer.Sparse.eval]

theorem keyMoment1100 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1100) =
      Integer.Sparse.eval keyMomentRow1100 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1100).leftCharge (GramAssembly.key 1100).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 636) := by
    have ha : gramCharges (GramAssembly.key 1100).leftCharge (GramAssembly.key 1100).rightCharge = raw40539 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40539Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40539 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1100).leftCharge (GramAssembly.key 1100).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1100, Integer.Sparse.eval]

theorem keyMoment1101 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1101) =
      Integer.Sparse.eval keyMomentRow1101 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1101).leftCharge (GramAssembly.key 1101).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 627) := by
    have ha : gramCharges (GramAssembly.key 1101).leftCharge (GramAssembly.key 1101).rightCharge = raw40540 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40540Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40540 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1101).leftCharge (GramAssembly.key 1101).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1101, Integer.Sparse.eval]

theorem keyMoment1102 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1102) =
      Integer.Sparse.eval keyMomentRow1102 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1102).leftCharge (GramAssembly.key 1102).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 637) := by
    have ha : gramCharges (GramAssembly.key 1102).leftCharge (GramAssembly.key 1102).rightCharge = raw40541 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40541Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40541 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1102).leftCharge (GramAssembly.key 1102).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1102, Integer.Sparse.eval]

theorem keyMoment1103 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1103) =
      Integer.Sparse.eval keyMomentRow1103 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1103).leftCharge (GramAssembly.key 1103).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 629) := by
    have ha : gramCharges (GramAssembly.key 1103).leftCharge (GramAssembly.key 1103).rightCharge = raw40542 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40542Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40542 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1103).leftCharge (GramAssembly.key 1103).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1103, Integer.Sparse.eval]

theorem keyMoment1104 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1104) =
      Integer.Sparse.eval keyMomentRow1104 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1104).leftCharge (GramAssembly.key 1104).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 640) := by
    have ha : gramCharges (GramAssembly.key 1104).leftCharge (GramAssembly.key 1104).rightCharge = raw40543 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40543Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40543 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1104).leftCharge (GramAssembly.key 1104).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1104, Integer.Sparse.eval]

theorem keyMoment1105 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1105) =
      Integer.Sparse.eval keyMomentRow1105 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1105).leftCharge (GramAssembly.key 1105).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 630) := by
    have ha : gramCharges (GramAssembly.key 1105).leftCharge (GramAssembly.key 1105).rightCharge = raw40544 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40544Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40544 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1105).leftCharge (GramAssembly.key 1105).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1105, Integer.Sparse.eval]

theorem keyMoment1106 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1106) =
      Integer.Sparse.eval keyMomentRow1106 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1106).leftCharge (GramAssembly.key 1106).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 641) := by
    have ha : gramCharges (GramAssembly.key 1106).leftCharge (GramAssembly.key 1106).rightCharge = raw40545 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40545Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40545 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1106).leftCharge (GramAssembly.key 1106).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1106, Integer.Sparse.eval]

theorem keyMoment1107 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1107) =
      Integer.Sparse.eval keyMomentRow1107 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1107).leftCharge (GramAssembly.key 1107).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 633) := by
    have ha : gramCharges (GramAssembly.key 1107).leftCharge (GramAssembly.key 1107).rightCharge = raw40546 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40546Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40546 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1107).leftCharge (GramAssembly.key 1107).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1107, Integer.Sparse.eval]

theorem keyMoment1108 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1108) =
      Integer.Sparse.eval keyMomentRow1108 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1108).leftCharge (GramAssembly.key 1108).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 626) := by
    have ha : gramCharges (GramAssembly.key 1108).leftCharge (GramAssembly.key 1108).rightCharge = raw40547 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40547Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40547 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1108).leftCharge (GramAssembly.key 1108).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1108, Integer.Sparse.eval]

theorem keyMoment1109 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1109) =
      Integer.Sparse.eval keyMomentRow1109 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1109).leftCharge (GramAssembly.key 1109).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 643) := by
    have ha : gramCharges (GramAssembly.key 1109).leftCharge (GramAssembly.key 1109).rightCharge = raw40548 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40548Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40548 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1109).leftCharge (GramAssembly.key 1109).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1109, Integer.Sparse.eval]

theorem keyMoment1110 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1110) =
      Integer.Sparse.eval keyMomentRow1110 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1110).leftCharge (GramAssembly.key 1110).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 591) := by
    have ha : gramCharges (GramAssembly.key 1110).leftCharge (GramAssembly.key 1110).rightCharge = raw40549 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40549Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40549 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1110).leftCharge (GramAssembly.key 1110).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1110, Integer.Sparse.eval]

theorem keyMoment1111 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1111) =
      Integer.Sparse.eval keyMomentRow1111 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1111).leftCharge (GramAssembly.key 1111).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 628) := by
    have ha : gramCharges (GramAssembly.key 1111).leftCharge (GramAssembly.key 1111).rightCharge = raw40550 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40550Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40550 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1111).leftCharge (GramAssembly.key 1111).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1111, Integer.Sparse.eval]

theorem keyMoment1112 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1112) =
      Integer.Sparse.eval keyMomentRow1112 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1112).leftCharge (GramAssembly.key 1112).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 635) := by
    have ha : gramCharges (GramAssembly.key 1112).leftCharge (GramAssembly.key 1112).rightCharge = raw40551 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40551Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40551 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1112).leftCharge (GramAssembly.key 1112).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1112, Integer.Sparse.eval]

theorem keyMoment1113 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1113) =
      Integer.Sparse.eval keyMomentRow1113 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1113).leftCharge (GramAssembly.key 1113).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2740) := by
    have ha : gramCharges (GramAssembly.key 1113).leftCharge (GramAssembly.key 1113).rightCharge = raw40552 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40552Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40552 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1113).leftCharge (GramAssembly.key 1113).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1113, Integer.Sparse.eval]

theorem keyMoment1114 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1114) =
      Integer.Sparse.eval keyMomentRow1114 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1114).leftCharge (GramAssembly.key 1114).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3052) := by
    have ha : gramCharges (GramAssembly.key 1114).leftCharge (GramAssembly.key 1114).rightCharge = raw40553 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40553Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40553 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1114).leftCharge (GramAssembly.key 1114).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1114, Integer.Sparse.eval]

theorem keyMoment1115 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1115) =
      Integer.Sparse.eval keyMomentRow1115 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1115).leftCharge (GramAssembly.key 1115).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3547) := by
    have ha : gramCharges (GramAssembly.key 1115).leftCharge (GramAssembly.key 1115).rightCharge = raw40554 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40554Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40554 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1115).leftCharge (GramAssembly.key 1115).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1115, Integer.Sparse.eval]

theorem keyMoment1116 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1116) =
      Integer.Sparse.eval keyMomentRow1116 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1116).leftCharge (GramAssembly.key 1116).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3548) := by
    have ha : gramCharges (GramAssembly.key 1116).leftCharge (GramAssembly.key 1116).rightCharge = raw40555 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40555Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40555 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1116).leftCharge (GramAssembly.key 1116).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1116, Integer.Sparse.eval]

theorem keyMoment1117 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1117) =
      Integer.Sparse.eval keyMomentRow1117 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1117).leftCharge (GramAssembly.key 1117).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3549) := by
    have ha : gramCharges (GramAssembly.key 1117).leftCharge (GramAssembly.key 1117).rightCharge = raw40556 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40556Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40556 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1117).leftCharge (GramAssembly.key 1117).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1117, Integer.Sparse.eval]

theorem keyMoment1118 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1118) =
      Integer.Sparse.eval keyMomentRow1118 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1118).leftCharge (GramAssembly.key 1118).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3075) := by
    have ha : gramCharges (GramAssembly.key 1118).leftCharge (GramAssembly.key 1118).rightCharge = raw40557 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40557Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40557 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1118).leftCharge (GramAssembly.key 1118).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1118, Integer.Sparse.eval]

theorem keyMoment1119 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1119) =
      Integer.Sparse.eval keyMomentRow1119 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1119).leftCharge (GramAssembly.key 1119).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3534) := by
    have ha : gramCharges (GramAssembly.key 1119).leftCharge (GramAssembly.key 1119).rightCharge = raw40558 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40558Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40558 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1119).leftCharge (GramAssembly.key 1119).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1119, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
