import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical316
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical317

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1120 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1120) =
      Integer.Sparse.eval keyMomentRow1120 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1120).leftCharge (GramAssembly.key 1120).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3535) := by
    have ha : gramCharges (GramAssembly.key 1120).leftCharge (GramAssembly.key 1120).rightCharge = raw40559 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40559Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40559 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1120).leftCharge (GramAssembly.key 1120).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1120, Integer.Sparse.eval]

theorem keyMoment1121 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1121) =
      Integer.Sparse.eval keyMomentRow1121 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1121).leftCharge (GramAssembly.key 1121).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3541) := by
    have ha : gramCharges (GramAssembly.key 1121).leftCharge (GramAssembly.key 1121).rightCharge = raw40560 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40560Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40560 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1121).leftCharge (GramAssembly.key 1121).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1121, Integer.Sparse.eval]

theorem keyMoment1122 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1122) =
      Integer.Sparse.eval keyMomentRow1122 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1122).leftCharge (GramAssembly.key 1122).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3525) := by
    have ha : gramCharges (GramAssembly.key 1122).leftCharge (GramAssembly.key 1122).rightCharge = raw40561 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40561Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40561 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1122).leftCharge (GramAssembly.key 1122).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1122, Integer.Sparse.eval]

theorem keyMoment1123 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1123) =
      Integer.Sparse.eval keyMomentRow1123 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1123).leftCharge (GramAssembly.key 1123).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3526) := by
    have ha : gramCharges (GramAssembly.key 1123).leftCharge (GramAssembly.key 1123).rightCharge = raw40562 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40562Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40562 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1123).leftCharge (GramAssembly.key 1123).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1123, Integer.Sparse.eval]

theorem keyMoment1124 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1124) =
      Integer.Sparse.eval keyMomentRow1124 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1124).leftCharge (GramAssembly.key 1124).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2783) := by
    have ha : gramCharges (GramAssembly.key 1124).leftCharge (GramAssembly.key 1124).rightCharge = raw40563 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40563Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40563 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1124).leftCharge (GramAssembly.key 1124).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1124, Integer.Sparse.eval]

theorem keyMoment1125 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1125) =
      Integer.Sparse.eval keyMomentRow1125 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1125).leftCharge (GramAssembly.key 1125).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3098) := by
    have ha : gramCharges (GramAssembly.key 1125).leftCharge (GramAssembly.key 1125).rightCharge = raw40564 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40564Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40564 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1125).leftCharge (GramAssembly.key 1125).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1125, Integer.Sparse.eval]

theorem keyMoment1126 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1126) =
      Integer.Sparse.eval keyMomentRow1126 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1126).leftCharge (GramAssembly.key 1126).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3583) := by
    have ha : gramCharges (GramAssembly.key 1126).leftCharge (GramAssembly.key 1126).rightCharge = raw40565 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40565Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40565 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1126).leftCharge (GramAssembly.key 1126).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1126, Integer.Sparse.eval]

theorem keyMoment1127 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1127) =
      Integer.Sparse.eval keyMomentRow1127 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1127).leftCharge (GramAssembly.key 1127).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3584) := by
    have ha : gramCharges (GramAssembly.key 1127).leftCharge (GramAssembly.key 1127).rightCharge = raw40566 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40566Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40566 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1127).leftCharge (GramAssembly.key 1127).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1127, Integer.Sparse.eval]

theorem keyMoment1128 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1128) =
      Integer.Sparse.eval keyMomentRow1128 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1128).leftCharge (GramAssembly.key 1128).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3572) := by
    have ha : gramCharges (GramAssembly.key 1128).leftCharge (GramAssembly.key 1128).rightCharge = raw40567 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40567Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40567 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1128).leftCharge (GramAssembly.key 1128).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1128, Integer.Sparse.eval]

theorem keyMoment1129 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1129) =
      Integer.Sparse.eval keyMomentRow1129 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1129).leftCharge (GramAssembly.key 1129).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3573) := by
    have ha : gramCharges (GramAssembly.key 1129).leftCharge (GramAssembly.key 1129).rightCharge = raw40568 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40568Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40568 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1129).leftCharge (GramAssembly.key 1129).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1129, Integer.Sparse.eval]

theorem keyMoment1130 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1130) =
      Integer.Sparse.eval keyMomentRow1130 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1130).leftCharge (GramAssembly.key 1130).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2789) := by
    have ha : gramCharges (GramAssembly.key 1130).leftCharge (GramAssembly.key 1130).rightCharge = raw40569 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40569Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40569 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1130).leftCharge (GramAssembly.key 1130).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1130, Integer.Sparse.eval]

theorem keyMoment1131 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1131) =
      Integer.Sparse.eval keyMomentRow1131 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1131).leftCharge (GramAssembly.key 1131).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2744) := by
    have ha : gramCharges (GramAssembly.key 1131).leftCharge (GramAssembly.key 1131).rightCharge = raw40570 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40570Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40570 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1131).leftCharge (GramAssembly.key 1131).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1131, Integer.Sparse.eval]

theorem keyMoment1132 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1132) =
      Integer.Sparse.eval keyMomentRow1132 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1132).leftCharge (GramAssembly.key 1132).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3636) := by
    have ha : gramCharges (GramAssembly.key 1132).leftCharge (GramAssembly.key 1132).rightCharge = raw40571 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40571Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40571 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1132).leftCharge (GramAssembly.key 1132).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1132, Integer.Sparse.eval]

theorem keyMoment1133 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1133) =
      Integer.Sparse.eval keyMomentRow1133 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1133).leftCharge (GramAssembly.key 1133).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3629) := by
    have ha : gramCharges (GramAssembly.key 1133).leftCharge (GramAssembly.key 1133).rightCharge = raw40572 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40572Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40572 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1133).leftCharge (GramAssembly.key 1133).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1133, Integer.Sparse.eval]

theorem keyMoment1134 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1134) =
      Integer.Sparse.eval keyMomentRow1134 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1134).leftCharge (GramAssembly.key 1134).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3633) := by
    have ha : gramCharges (GramAssembly.key 1134).leftCharge (GramAssembly.key 1134).rightCharge = raw40573 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40573Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40573 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1134).leftCharge (GramAssembly.key 1134).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1134, Integer.Sparse.eval]

theorem keyMoment1135 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1135) =
      Integer.Sparse.eval keyMomentRow1135 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1135).leftCharge (GramAssembly.key 1135).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2294) := by
    have ha : gramCharges (GramAssembly.key 1135).leftCharge (GramAssembly.key 1135).rightCharge = raw40574 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40574Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40574 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1135).leftCharge (GramAssembly.key 1135).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1135, Integer.Sparse.eval]

theorem keyMoment1136 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1136) =
      Integer.Sparse.eval keyMomentRow1136 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1136).leftCharge (GramAssembly.key 1136).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3635) := by
    have ha : gramCharges (GramAssembly.key 1136).leftCharge (GramAssembly.key 1136).rightCharge = raw40575 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40575Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40575 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1136).leftCharge (GramAssembly.key 1136).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1136, Integer.Sparse.eval]

theorem keyMoment1137 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1137) =
      Integer.Sparse.eval keyMomentRow1137 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1137).leftCharge (GramAssembly.key 1137).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3623) := by
    have ha : gramCharges (GramAssembly.key 1137).leftCharge (GramAssembly.key 1137).rightCharge = raw40576 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40576Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40576 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1137).leftCharge (GramAssembly.key 1137).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1137, Integer.Sparse.eval]

theorem keyMoment1138 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1138) =
      Integer.Sparse.eval keyMomentRow1138 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1138).leftCharge (GramAssembly.key 1138).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3626) := by
    have ha : gramCharges (GramAssembly.key 1138).leftCharge (GramAssembly.key 1138).rightCharge = raw40577 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40577Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40577 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1138).leftCharge (GramAssembly.key 1138).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1138, Integer.Sparse.eval]

theorem keyMoment1139 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1139) =
      Integer.Sparse.eval keyMomentRow1139 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1139).leftCharge (GramAssembly.key 1139).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3627) := by
    have ha : gramCharges (GramAssembly.key 1139).leftCharge (GramAssembly.key 1139).rightCharge = raw40578 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40578Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40578 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1139).leftCharge (GramAssembly.key 1139).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1139, Integer.Sparse.eval]

theorem keyMoment1140 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1140) =
      Integer.Sparse.eval keyMomentRow1140 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1140).leftCharge (GramAssembly.key 1140).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3628) := by
    have ha : gramCharges (GramAssembly.key 1140).leftCharge (GramAssembly.key 1140).rightCharge = raw40579 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40579Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40579 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1140).leftCharge (GramAssembly.key 1140).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1140, Integer.Sparse.eval]

theorem keyMoment1141 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1141) =
      Integer.Sparse.eval keyMomentRow1141 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1141).leftCharge (GramAssembly.key 1141).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3632) := by
    have ha : gramCharges (GramAssembly.key 1141).leftCharge (GramAssembly.key 1141).rightCharge = raw40580 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40580Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40580 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1141).leftCharge (GramAssembly.key 1141).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1141, Integer.Sparse.eval]

theorem keyMoment1142 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1142) =
      Integer.Sparse.eval keyMomentRow1142 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1142).leftCharge (GramAssembly.key 1142).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3619) := by
    have ha : gramCharges (GramAssembly.key 1142).leftCharge (GramAssembly.key 1142).rightCharge = raw40581 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40581Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40581 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1142).leftCharge (GramAssembly.key 1142).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1142, Integer.Sparse.eval]

theorem keyMoment1143 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1143) =
      Integer.Sparse.eval keyMomentRow1143 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1143).leftCharge (GramAssembly.key 1143).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3622) := by
    have ha : gramCharges (GramAssembly.key 1143).leftCharge (GramAssembly.key 1143).rightCharge = raw40582 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40582Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40582 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1143).leftCharge (GramAssembly.key 1143).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1143, Integer.Sparse.eval]

theorem keyMoment1144 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1144) =
      Integer.Sparse.eval keyMomentRow1144 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1144).leftCharge (GramAssembly.key 1144).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3625) := by
    have ha : gramCharges (GramAssembly.key 1144).leftCharge (GramAssembly.key 1144).rightCharge = raw40583 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40583Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40583 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1144).leftCharge (GramAssembly.key 1144).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1144, Integer.Sparse.eval]

theorem keyMoment1145 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1145) =
      Integer.Sparse.eval keyMomentRow1145 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1145).leftCharge (GramAssembly.key 1145).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3618) := by
    have ha : gramCharges (GramAssembly.key 1145).leftCharge (GramAssembly.key 1145).rightCharge = raw40584 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40584Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40584 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1145).leftCharge (GramAssembly.key 1145).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1145, Integer.Sparse.eval]

theorem keyMoment1146 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1146) =
      Integer.Sparse.eval keyMomentRow1146 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1146).leftCharge (GramAssembly.key 1146).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4084) := by
    have ha : gramCharges (GramAssembly.key 1146).leftCharge (GramAssembly.key 1146).rightCharge = raw2935 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw2935Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical2935 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1146).leftCharge (GramAssembly.key 1146).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1146, Integer.Sparse.eval]

theorem keyMoment1147 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1147) =
      Integer.Sparse.eval keyMomentRow1147 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1147).leftCharge (GramAssembly.key 1147).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2742) := by
    have ha : gramCharges (GramAssembly.key 1147).leftCharge (GramAssembly.key 1147).rightCharge = raw40585 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40585Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40585 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1147).leftCharge (GramAssembly.key 1147).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1147, Integer.Sparse.eval]

theorem keyMoment1148 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1148) =
      Integer.Sparse.eval keyMomentRow1148 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1148).leftCharge (GramAssembly.key 1148).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3054) := by
    have ha : gramCharges (GramAssembly.key 1148).leftCharge (GramAssembly.key 1148).rightCharge = raw40586 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40586Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40586 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1148).leftCharge (GramAssembly.key 1148).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1148, Integer.Sparse.eval]

theorem keyMoment1149 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1149) =
      Integer.Sparse.eval keyMomentRow1149 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1149).leftCharge (GramAssembly.key 1149).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4092) := by
    have ha : gramCharges (GramAssembly.key 1149).leftCharge (GramAssembly.key 1149).rightCharge = raw2930 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw2930Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical2930 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1149).leftCharge (GramAssembly.key 1149).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1149, Integer.Sparse.eval]

theorem keyMoment1150 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1150) =
      Integer.Sparse.eval keyMomentRow1150 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1150).leftCharge (GramAssembly.key 1150).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3817) := by
    have ha : gramCharges (GramAssembly.key 1150).leftCharge (GramAssembly.key 1150).rightCharge = raw40587 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40587Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40587 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1150).leftCharge (GramAssembly.key 1150).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1150, Integer.Sparse.eval]

theorem keyMoment1151 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1151) =
      Integer.Sparse.eval keyMomentRow1151 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1151).leftCharge (GramAssembly.key 1151).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3626) := by
    have ha : gramCharges (GramAssembly.key 1151).leftCharge (GramAssembly.key 1151).rightCharge = raw40588 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40588Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40588 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1151).leftCharge (GramAssembly.key 1151).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1151, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
