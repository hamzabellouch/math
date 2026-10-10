import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical114
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical317

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1152 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1152) =
      Integer.Sparse.eval keyMomentRow1152 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1152).leftCharge (GramAssembly.key 1152).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3077) := by
    have ha : gramCharges (GramAssembly.key 1152).leftCharge (GramAssembly.key 1152).rightCharge = raw40589 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40589Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40589 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1152).leftCharge (GramAssembly.key 1152).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1152, Integer.Sparse.eval]

theorem keyMoment1153 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1153) =
      Integer.Sparse.eval keyMomentRow1153 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1153).leftCharge (GramAssembly.key 1153).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3807) := by
    have ha : gramCharges (GramAssembly.key 1153).leftCharge (GramAssembly.key 1153).rightCharge = raw40590 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40590Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40590 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1153).leftCharge (GramAssembly.key 1153).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1153, Integer.Sparse.eval]

theorem keyMoment1154 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1154) =
      Integer.Sparse.eval keyMomentRow1154 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1154).leftCharge (GramAssembly.key 1154).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3808) := by
    have ha : gramCharges (GramAssembly.key 1154).leftCharge (GramAssembly.key 1154).rightCharge = raw40591 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40591Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40591 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1154).leftCharge (GramAssembly.key 1154).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1154, Integer.Sparse.eval]

theorem keyMoment1155 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1155) =
      Integer.Sparse.eval keyMomentRow1155 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1155).leftCharge (GramAssembly.key 1155).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3809) := by
    have ha : gramCharges (GramAssembly.key 1155).leftCharge (GramAssembly.key 1155).rightCharge = raw40592 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40592Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40592 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1155).leftCharge (GramAssembly.key 1155).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1155, Integer.Sparse.eval]

theorem keyMoment1156 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1156) =
      Integer.Sparse.eval keyMomentRow1156 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1156).leftCharge (GramAssembly.key 1156).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3813) := by
    have ha : gramCharges (GramAssembly.key 1156).leftCharge (GramAssembly.key 1156).rightCharge = raw40593 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40593Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40593 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1156).leftCharge (GramAssembly.key 1156).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1156, Integer.Sparse.eval]

theorem keyMoment1157 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1157) =
      Integer.Sparse.eval keyMomentRow1157 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1157).leftCharge (GramAssembly.key 1157).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3814) := by
    have ha : gramCharges (GramAssembly.key 1157).leftCharge (GramAssembly.key 1157).rightCharge = raw40594 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40594Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40594 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1157).leftCharge (GramAssembly.key 1157).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1157, Integer.Sparse.eval]

theorem keyMoment1158 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1158) =
      Integer.Sparse.eval keyMomentRow1158 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1158).leftCharge (GramAssembly.key 1158).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3816) := by
    have ha : gramCharges (GramAssembly.key 1158).leftCharge (GramAssembly.key 1158).rightCharge = raw40595 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40595Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40595 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1158).leftCharge (GramAssembly.key 1158).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1158, Integer.Sparse.eval]

theorem keyMoment1159 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1159) =
      Integer.Sparse.eval keyMomentRow1159 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1159).leftCharge (GramAssembly.key 1159).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4091) := by
    have ha : gramCharges (GramAssembly.key 1159).leftCharge (GramAssembly.key 1159).rightCharge = raw3332 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw3332Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical3332 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1159).leftCharge (GramAssembly.key 1159).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1159, Integer.Sparse.eval]

theorem keyMoment1160 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1160) =
      Integer.Sparse.eval keyMomentRow1160 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1160).leftCharge (GramAssembly.key 1160).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3800) := by
    have ha : gramCharges (GramAssembly.key 1160).leftCharge (GramAssembly.key 1160).rightCharge = raw40596 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40596Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40596 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1160).leftCharge (GramAssembly.key 1160).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1160, Integer.Sparse.eval]

theorem keyMoment1161 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1161) =
      Integer.Sparse.eval keyMomentRow1161 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1161).leftCharge (GramAssembly.key 1161).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3801) := by
    have ha : gramCharges (GramAssembly.key 1161).leftCharge (GramAssembly.key 1161).rightCharge = raw40597 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40597Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40597 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1161).leftCharge (GramAssembly.key 1161).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1161, Integer.Sparse.eval]

theorem keyMoment1162 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1162) =
      Integer.Sparse.eval keyMomentRow1162 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1162).leftCharge (GramAssembly.key 1162).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3805) := by
    have ha : gramCharges (GramAssembly.key 1162).leftCharge (GramAssembly.key 1162).rightCharge = raw40598 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40598Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40598 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1162).leftCharge (GramAssembly.key 1162).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1162, Integer.Sparse.eval]

theorem keyMoment1163 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1163) =
      Integer.Sparse.eval keyMomentRow1163 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1163).leftCharge (GramAssembly.key 1163).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3806) := by
    have ha : gramCharges (GramAssembly.key 1163).leftCharge (GramAssembly.key 1163).rightCharge = raw40599 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40599Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40599 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1163).leftCharge (GramAssembly.key 1163).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1163, Integer.Sparse.eval]

theorem keyMoment1164 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1164) =
      Integer.Sparse.eval keyMomentRow1164 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1164).leftCharge (GramAssembly.key 1164).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3812) := by
    have ha : gramCharges (GramAssembly.key 1164).leftCharge (GramAssembly.key 1164).rightCharge = raw40600 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40600Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40600 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1164).leftCharge (GramAssembly.key 1164).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1164, Integer.Sparse.eval]

theorem keyMoment1165 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1165) =
      Integer.Sparse.eval keyMomentRow1165 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1165).leftCharge (GramAssembly.key 1165).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2264) := by
    have ha : gramCharges (GramAssembly.key 1165).leftCharge (GramAssembly.key 1165).rightCharge = raw40601 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40601Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40601 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1165).leftCharge (GramAssembly.key 1165).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1165, Integer.Sparse.eval]

theorem keyMoment1166 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1166) =
      Integer.Sparse.eval keyMomentRow1166 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1166).leftCharge (GramAssembly.key 1166).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2722) := by
    have ha : gramCharges (GramAssembly.key 1166).leftCharge (GramAssembly.key 1166).rightCharge = raw40602 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40602Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40602 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1166).leftCharge (GramAssembly.key 1166).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1166, Integer.Sparse.eval]

theorem keyMoment1167 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1167) =
      Integer.Sparse.eval keyMomentRow1167 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1167).leftCharge (GramAssembly.key 1167).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3038) := by
    have ha : gramCharges (GramAssembly.key 1167).leftCharge (GramAssembly.key 1167).rightCharge = raw40603 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40603Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40603 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1167).leftCharge (GramAssembly.key 1167).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1167, Integer.Sparse.eval]

theorem keyMoment1168 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1168) =
      Integer.Sparse.eval keyMomentRow1168 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1168).leftCharge (GramAssembly.key 1168).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3807) := by
    have ha : gramCharges (GramAssembly.key 1168).leftCharge (GramAssembly.key 1168).rightCharge = raw40604 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40604Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40604 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1168).leftCharge (GramAssembly.key 1168).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1168, Integer.Sparse.eval]

theorem keyMoment1169 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1169) =
      Integer.Sparse.eval keyMomentRow1169 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1169).leftCharge (GramAssembly.key 1169).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3845) := by
    have ha : gramCharges (GramAssembly.key 1169).leftCharge (GramAssembly.key 1169).rightCharge = raw40605 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40605Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40605 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1169).leftCharge (GramAssembly.key 1169).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1169, Integer.Sparse.eval]

theorem keyMoment1170 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1170) =
      Integer.Sparse.eval keyMomentRow1170 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1170).leftCharge (GramAssembly.key 1170).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3541) := by
    have ha : gramCharges (GramAssembly.key 1170).leftCharge (GramAssembly.key 1170).rightCharge = raw40606 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40606Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40606 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1170).leftCharge (GramAssembly.key 1170).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1170, Integer.Sparse.eval]

theorem keyMoment1171 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1171) =
      Integer.Sparse.eval keyMomentRow1171 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1171).leftCharge (GramAssembly.key 1171).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3064) := by
    have ha : gramCharges (GramAssembly.key 1171).leftCharge (GramAssembly.key 1171).rightCharge = raw14639 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw14639Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical14639 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1171).leftCharge (GramAssembly.key 1171).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1171, Integer.Sparse.eval]

theorem keyMoment1172 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1172) =
      Integer.Sparse.eval keyMomentRow1172 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1172).leftCharge (GramAssembly.key 1172).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3837) := by
    have ha : gramCharges (GramAssembly.key 1172).leftCharge (GramAssembly.key 1172).rightCharge = raw40607 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40607Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40607 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1172).leftCharge (GramAssembly.key 1172).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1172, Integer.Sparse.eval]

theorem keyMoment1173 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1173) =
      Integer.Sparse.eval keyMomentRow1173 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1173).leftCharge (GramAssembly.key 1173).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3838) := by
    have ha : gramCharges (GramAssembly.key 1173).leftCharge (GramAssembly.key 1173).rightCharge = raw40608 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40608Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40608 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1173).leftCharge (GramAssembly.key 1173).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1173, Integer.Sparse.eval]

theorem keyMoment1174 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1174) =
      Integer.Sparse.eval keyMomentRow1174 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1174).leftCharge (GramAssembly.key 1174).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3839) := by
    have ha : gramCharges (GramAssembly.key 1174).leftCharge (GramAssembly.key 1174).rightCharge = raw40609 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40609Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40609 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1174).leftCharge (GramAssembly.key 1174).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1174, Integer.Sparse.eval]

theorem keyMoment1175 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1175) =
      Integer.Sparse.eval keyMomentRow1175 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1175).leftCharge (GramAssembly.key 1175).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3840) := by
    have ha : gramCharges (GramAssembly.key 1175).leftCharge (GramAssembly.key 1175).rightCharge = raw40610 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40610Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40610 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1175).leftCharge (GramAssembly.key 1175).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1175, Integer.Sparse.eval]

theorem keyMoment1176 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1176) =
      Integer.Sparse.eval keyMomentRow1176 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1176).leftCharge (GramAssembly.key 1176).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3841) := by
    have ha : gramCharges (GramAssembly.key 1176).leftCharge (GramAssembly.key 1176).rightCharge = raw40611 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40611Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40611 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1176).leftCharge (GramAssembly.key 1176).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1176, Integer.Sparse.eval]

theorem keyMoment1177 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1177) =
      Integer.Sparse.eval keyMomentRow1177 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1177).leftCharge (GramAssembly.key 1177).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3843) := by
    have ha : gramCharges (GramAssembly.key 1177).leftCharge (GramAssembly.key 1177).rightCharge = raw40612 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40612Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40612 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1177).leftCharge (GramAssembly.key 1177).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1177, Integer.Sparse.eval]

theorem keyMoment1178 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1178) =
      Integer.Sparse.eval keyMomentRow1178 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1178).leftCharge (GramAssembly.key 1178).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3844) := by
    have ha : gramCharges (GramAssembly.key 1178).leftCharge (GramAssembly.key 1178).rightCharge = raw40613 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40613Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40613 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1178).leftCharge (GramAssembly.key 1178).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1178, Integer.Sparse.eval]

theorem keyMoment1179 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1179) =
      Integer.Sparse.eval keyMomentRow1179 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1179).leftCharge (GramAssembly.key 1179).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3052) := by
    have ha : gramCharges (GramAssembly.key 1179).leftCharge (GramAssembly.key 1179).rightCharge = raw40614 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40614Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40614 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1179).leftCharge (GramAssembly.key 1179).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1179, Integer.Sparse.eval]

theorem keyMoment1180 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1180) =
      Integer.Sparse.eval keyMomentRow1180 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1180).leftCharge (GramAssembly.key 1180).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3850) := by
    have ha : gramCharges (GramAssembly.key 1180).leftCharge (GramAssembly.key 1180).rightCharge = raw40615 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40615Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40615 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1180).leftCharge (GramAssembly.key 1180).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1180, Integer.Sparse.eval]

theorem keyMoment1181 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1181) =
      Integer.Sparse.eval keyMomentRow1181 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1181).leftCharge (GramAssembly.key 1181).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3051) := by
    have ha : gramCharges (GramAssembly.key 1181).leftCharge (GramAssembly.key 1181).rightCharge = raw40616 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40616Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40616 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1181).leftCharge (GramAssembly.key 1181).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1181, Integer.Sparse.eval]

theorem keyMoment1182 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1182) =
      Integer.Sparse.eval keyMomentRow1182 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1182).leftCharge (GramAssembly.key 1182).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3854) := by
    have ha : gramCharges (GramAssembly.key 1182).leftCharge (GramAssembly.key 1182).rightCharge = raw40617 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40617Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40617 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1182).leftCharge (GramAssembly.key 1182).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1182, Integer.Sparse.eval]

theorem keyMoment1183 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1183) =
      Integer.Sparse.eval keyMomentRow1183 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1183).leftCharge (GramAssembly.key 1183).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3038) := by
    have ha : gramCharges (GramAssembly.key 1183).leftCharge (GramAssembly.key 1183).rightCharge = raw40618 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40618Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40618 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1183).leftCharge (GramAssembly.key 1183).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1183, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
