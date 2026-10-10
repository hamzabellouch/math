import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical150
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical273
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical274
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical317

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1184 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1184) =
      Integer.Sparse.eval keyMomentRow1184 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1184).leftCharge (GramAssembly.key 1184).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3846) := by
    have ha : gramCharges (GramAssembly.key 1184).leftCharge (GramAssembly.key 1184).rightCharge = raw40619 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40619Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40619 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1184).leftCharge (GramAssembly.key 1184).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1184, Integer.Sparse.eval]

theorem keyMoment1185 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1185) =
      Integer.Sparse.eval keyMomentRow1185 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1185).leftCharge (GramAssembly.key 1185).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3037) := by
    have ha : gramCharges (GramAssembly.key 1185).leftCharge (GramAssembly.key 1185).rightCharge = raw40620 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40620Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40620 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1185).leftCharge (GramAssembly.key 1185).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1185, Integer.Sparse.eval]

theorem keyMoment1186 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1186) =
      Integer.Sparse.eval keyMomentRow1186 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1186).leftCharge (GramAssembly.key 1186).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3848) := by
    have ha : gramCharges (GramAssembly.key 1186).leftCharge (GramAssembly.key 1186).rightCharge = raw40621 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40621Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40621 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1186).leftCharge (GramAssembly.key 1186).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1186, Integer.Sparse.eval]

theorem keyMoment1187 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1187) =
      Integer.Sparse.eval keyMomentRow1187 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1187).leftCharge (GramAssembly.key 1187).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3849) := by
    have ha : gramCharges (GramAssembly.key 1187).leftCharge (GramAssembly.key 1187).rightCharge = raw40622 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40622Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40622 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1187).leftCharge (GramAssembly.key 1187).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1187, Integer.Sparse.eval]

theorem keyMoment1188 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1188) =
      Integer.Sparse.eval keyMomentRow1188 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1188).leftCharge (GramAssembly.key 1188).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3840) := by
    have ha : gramCharges (GramAssembly.key 1188).leftCharge (GramAssembly.key 1188).rightCharge = raw40623 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40623Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40623 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1188).leftCharge (GramAssembly.key 1188).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1188, Integer.Sparse.eval]

theorem keyMoment1189 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1189) =
      Integer.Sparse.eval keyMomentRow1189 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1189).leftCharge (GramAssembly.key 1189).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2765) := by
    have ha : gramCharges (GramAssembly.key 1189).leftCharge (GramAssembly.key 1189).rightCharge = raw40624 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40624Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40624 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1189).leftCharge (GramAssembly.key 1189).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1189, Integer.Sparse.eval]

theorem keyMoment1190 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1190) =
      Integer.Sparse.eval keyMomentRow1190 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1190).leftCharge (GramAssembly.key 1190).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3086) := by
    have ha : gramCharges (GramAssembly.key 1190).leftCharge (GramAssembly.key 1190).rightCharge = raw40625 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40625Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40625 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1190).leftCharge (GramAssembly.key 1190).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1190, Integer.Sparse.eval]

theorem keyMoment1191 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1191) =
      Integer.Sparse.eval keyMomentRow1191 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1191).leftCharge (GramAssembly.key 1191).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3850) := by
    have ha : gramCharges (GramAssembly.key 1191).leftCharge (GramAssembly.key 1191).rightCharge = raw40626 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40626Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40626 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1191).leftCharge (GramAssembly.key 1191).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1191, Integer.Sparse.eval]

theorem keyMoment1192 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1192) =
      Integer.Sparse.eval keyMomentRow1192 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1192).leftCharge (GramAssembly.key 1192).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3876) := by
    have ha : gramCharges (GramAssembly.key 1192).leftCharge (GramAssembly.key 1192).rightCharge = raw19298 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw19298Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical19298 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1192).leftCharge (GramAssembly.key 1192).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1192, Integer.Sparse.eval]

theorem keyMoment1193 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1193) =
      Integer.Sparse.eval keyMomentRow1193 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1193).leftCharge (GramAssembly.key 1193).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3877) := by
    have ha : gramCharges (GramAssembly.key 1193).leftCharge (GramAssembly.key 1193).rightCharge = raw40627 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40627Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40627 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1193).leftCharge (GramAssembly.key 1193).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1193, Integer.Sparse.eval]

theorem keyMoment1194 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1194) =
      Integer.Sparse.eval keyMomentRow1194 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1194).leftCharge (GramAssembly.key 1194).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3871) := by
    have ha : gramCharges (GramAssembly.key 1194).leftCharge (GramAssembly.key 1194).rightCharge = raw40628 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40628Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40628 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1194).leftCharge (GramAssembly.key 1194).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1194, Integer.Sparse.eval]

theorem keyMoment1195 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1195) =
      Integer.Sparse.eval keyMomentRow1195 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1195).leftCharge (GramAssembly.key 1195).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3872) := by
    have ha : gramCharges (GramAssembly.key 1195).leftCharge (GramAssembly.key 1195).rightCharge = raw40629 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40629Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40629 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1195).leftCharge (GramAssembly.key 1195).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1195, Integer.Sparse.eval]

theorem keyMoment1196 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1196) =
      Integer.Sparse.eval keyMomentRow1196 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1196).leftCharge (GramAssembly.key 1196).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3874) := by
    have ha : gramCharges (GramAssembly.key 1196).leftCharge (GramAssembly.key 1196).rightCharge = raw40630 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40630Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40630 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1196).leftCharge (GramAssembly.key 1196).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1196, Integer.Sparse.eval]

theorem keyMoment1197 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1197) =
      Integer.Sparse.eval keyMomentRow1197 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1197).leftCharge (GramAssembly.key 1197).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3875) := by
    have ha : gramCharges (GramAssembly.key 1197).leftCharge (GramAssembly.key 1197).rightCharge = raw40631 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40631Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40631 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1197).leftCharge (GramAssembly.key 1197).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1197, Integer.Sparse.eval]

theorem keyMoment1198 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1198) =
      Integer.Sparse.eval keyMomentRow1198 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1198).leftCharge (GramAssembly.key 1198).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3886) := by
    have ha : gramCharges (GramAssembly.key 1198).leftCharge (GramAssembly.key 1198).rightCharge = raw40632 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40632Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40632 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1198).leftCharge (GramAssembly.key 1198).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1198, Integer.Sparse.eval]

theorem keyMoment1199 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1199) =
      Integer.Sparse.eval keyMomentRow1199 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1199).leftCharge (GramAssembly.key 1199).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3055) := by
    have ha : gramCharges (GramAssembly.key 1199).leftCharge (GramAssembly.key 1199).rightCharge = raw40633 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40633Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40633 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1199).leftCharge (GramAssembly.key 1199).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1199, Integer.Sparse.eval]

theorem keyMoment1200 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1200) =
      Integer.Sparse.eval keyMomentRow1200 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1200).leftCharge (GramAssembly.key 1200).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3881) := by
    have ha : gramCharges (GramAssembly.key 1200).leftCharge (GramAssembly.key 1200).rightCharge = raw34967 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw34967Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical34967 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1200).leftCharge (GramAssembly.key 1200).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1200, Integer.Sparse.eval]

theorem keyMoment1201 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1201) =
      Integer.Sparse.eval keyMomentRow1201 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1201).leftCharge (GramAssembly.key 1201).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3039) := by
    have ha : gramCharges (GramAssembly.key 1201).leftCharge (GramAssembly.key 1201).rightCharge = raw40634 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40634Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40634 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1201).leftCharge (GramAssembly.key 1201).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1201, Integer.Sparse.eval]

theorem keyMoment1202 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1202) =
      Integer.Sparse.eval keyMomentRow1202 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1202).leftCharge (GramAssembly.key 1202).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3884) := by
    have ha : gramCharges (GramAssembly.key 1202).leftCharge (GramAssembly.key 1202).rightCharge = raw40635 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40635Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40635 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1202).leftCharge (GramAssembly.key 1202).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1202, Integer.Sparse.eval]

theorem keyMoment1203 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1203) =
      Integer.Sparse.eval keyMomentRow1203 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1203).leftCharge (GramAssembly.key 1203).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3885) := by
    have ha : gramCharges (GramAssembly.key 1203).leftCharge (GramAssembly.key 1203).rightCharge = raw40636 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40636Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40636 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1203).leftCharge (GramAssembly.key 1203).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1203, Integer.Sparse.eval]

theorem keyMoment1204 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1204) =
      Integer.Sparse.eval keyMomentRow1204 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1204).leftCharge (GramAssembly.key 1204).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2777) := by
    have ha : gramCharges (GramAssembly.key 1204).leftCharge (GramAssembly.key 1204).rightCharge = raw40637 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40637Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40637 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1204).leftCharge (GramAssembly.key 1204).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1204, Integer.Sparse.eval]

theorem keyMoment1205 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1205) =
      Integer.Sparse.eval keyMomentRow1205 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1205).leftCharge (GramAssembly.key 1205).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2773) := by
    have ha : gramCharges (GramAssembly.key 1205).leftCharge (GramAssembly.key 1205).rightCharge = raw40638 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40638Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40638 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1205).leftCharge (GramAssembly.key 1205).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1205, Integer.Sparse.eval]

theorem keyMoment1206 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1206) =
      Integer.Sparse.eval keyMomentRow1206 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1206).leftCharge (GramAssembly.key 1206).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2732) := by
    have ha : gramCharges (GramAssembly.key 1206).leftCharge (GramAssembly.key 1206).rightCharge = raw40639 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40639Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40639 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1206).leftCharge (GramAssembly.key 1206).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1206, Integer.Sparse.eval]

theorem keyMoment1207 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1207) =
      Integer.Sparse.eval keyMomentRow1207 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1207).leftCharge (GramAssembly.key 1207).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2730) := by
    have ha : gramCharges (GramAssembly.key 1207).leftCharge (GramAssembly.key 1207).rightCharge = raw40640 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40640Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40640 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1207).leftCharge (GramAssembly.key 1207).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1207, Integer.Sparse.eval]

theorem keyMoment1208 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1208) =
      Integer.Sparse.eval keyMomentRow1208 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1208).leftCharge (GramAssembly.key 1208).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2774) := by
    have ha : gramCharges (GramAssembly.key 1208).leftCharge (GramAssembly.key 1208).rightCharge = raw35153 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw35153Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical35153 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1208).leftCharge (GramAssembly.key 1208).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1208, Integer.Sparse.eval]

theorem keyMoment1209 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1209) =
      Integer.Sparse.eval keyMomentRow1209 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1209).leftCharge (GramAssembly.key 1209).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2734) := by
    have ha : gramCharges (GramAssembly.key 1209).leftCharge (GramAssembly.key 1209).rightCharge = raw40641 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40641Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40641 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1209).leftCharge (GramAssembly.key 1209).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1209, Integer.Sparse.eval]

theorem keyMoment1210 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1210) =
      Integer.Sparse.eval keyMomentRow1210 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1210).leftCharge (GramAssembly.key 1210).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2731) := by
    have ha : gramCharges (GramAssembly.key 1210).leftCharge (GramAssembly.key 1210).rightCharge = raw40642 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40642Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40642 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1210).leftCharge (GramAssembly.key 1210).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1210, Integer.Sparse.eval]

theorem keyMoment1211 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1211) =
      Integer.Sparse.eval keyMomentRow1211 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1211).leftCharge (GramAssembly.key 1211).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3629) := by
    have ha : gramCharges (GramAssembly.key 1211).leftCharge (GramAssembly.key 1211).rightCharge = raw40643 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40643Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40643 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1211).leftCharge (GramAssembly.key 1211).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1211, Integer.Sparse.eval]

theorem keyMoment1212 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1212) =
      Integer.Sparse.eval keyMomentRow1212 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1212).leftCharge (GramAssembly.key 1212).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3905) := by
    have ha : gramCharges (GramAssembly.key 1212).leftCharge (GramAssembly.key 1212).rightCharge = raw40644 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40644Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40644 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1212).leftCharge (GramAssembly.key 1212).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1212, Integer.Sparse.eval]

theorem keyMoment1213 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1213) =
      Integer.Sparse.eval keyMomentRow1213 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1213).leftCharge (GramAssembly.key 1213).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3907) := by
    have ha : gramCharges (GramAssembly.key 1213).leftCharge (GramAssembly.key 1213).rightCharge = raw40645 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40645Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40645 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1213).leftCharge (GramAssembly.key 1213).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1213, Integer.Sparse.eval]

theorem keyMoment1214 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1214) =
      Integer.Sparse.eval keyMomentRow1214 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1214).leftCharge (GramAssembly.key 1214).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2279) := by
    have ha : gramCharges (GramAssembly.key 1214).leftCharge (GramAssembly.key 1214).rightCharge = raw40646 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40646Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40646 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1214).leftCharge (GramAssembly.key 1214).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1214, Integer.Sparse.eval]

theorem keyMoment1215 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1215) =
      Integer.Sparse.eval keyMomentRow1215 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1215).leftCharge (GramAssembly.key 1215).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3632) := by
    have ha : gramCharges (GramAssembly.key 1215).leftCharge (GramAssembly.key 1215).rightCharge = raw40647 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40647Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40647 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1215).leftCharge (GramAssembly.key 1215).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1215, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
