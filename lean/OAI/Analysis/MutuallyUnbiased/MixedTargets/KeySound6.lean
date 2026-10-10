import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys6
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical309

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment192 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 192) =
      Integer.Sparse.eval keyMomentRow192 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 192).leftCharge (GramAssembly.key 192).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 422) := by
    have ha : gramCharges (GramAssembly.key 192).leftCharge (GramAssembly.key 192).rightCharge = raw39642 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39642Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39642 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 192).leftCharge (GramAssembly.key 192).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow192, Integer.Sparse.eval]

theorem keyMoment193 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 193) =
      Integer.Sparse.eval keyMomentRow193 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 193).leftCharge (GramAssembly.key 193).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 418) := by
    have ha : gramCharges (GramAssembly.key 193).leftCharge (GramAssembly.key 193).rightCharge = raw39643 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39643Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39643 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 193).leftCharge (GramAssembly.key 193).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow193, Integer.Sparse.eval]

theorem keyMoment194 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 194) =
      Integer.Sparse.eval keyMomentRow194 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 194).leftCharge (GramAssembly.key 194).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 420) := by
    have ha : gramCharges (GramAssembly.key 194).leftCharge (GramAssembly.key 194).rightCharge = raw39644 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39644Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39644 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 194).leftCharge (GramAssembly.key 194).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow194, Integer.Sparse.eval]

theorem keyMoment195 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 195) =
      Integer.Sparse.eval keyMomentRow195 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 195).leftCharge (GramAssembly.key 195).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 270) := by
    have ha : gramCharges (GramAssembly.key 195).leftCharge (GramAssembly.key 195).rightCharge = raw39645 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39645Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39645 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 195).leftCharge (GramAssembly.key 195).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow195, Integer.Sparse.eval]

theorem keyMoment196 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 196) =
      Integer.Sparse.eval keyMomentRow196 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 196).leftCharge (GramAssembly.key 196).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 419) := by
    have ha : gramCharges (GramAssembly.key 196).leftCharge (GramAssembly.key 196).rightCharge = raw39646 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39646Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39646 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 196).leftCharge (GramAssembly.key 196).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow196, Integer.Sparse.eval]

theorem keyMoment197 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 197) =
      Integer.Sparse.eval keyMomentRow197 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 197).leftCharge (GramAssembly.key 197).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 412) := by
    have ha : gramCharges (GramAssembly.key 197).leftCharge (GramAssembly.key 197).rightCharge = raw39647 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39647Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39647 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 197).leftCharge (GramAssembly.key 197).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow197, Integer.Sparse.eval]

theorem keyMoment198 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 198) =
      Integer.Sparse.eval keyMomentRow198 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 198).leftCharge (GramAssembly.key 198).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 404) := by
    have ha : gramCharges (GramAssembly.key 198).leftCharge (GramAssembly.key 198).rightCharge = raw39648 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39648Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39648 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 198).leftCharge (GramAssembly.key 198).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow198, Integer.Sparse.eval]

theorem keyMoment199 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 199) =
      Integer.Sparse.eval keyMomentRow199 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 199).leftCharge (GramAssembly.key 199).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 417) := by
    have ha : gramCharges (GramAssembly.key 199).leftCharge (GramAssembly.key 199).rightCharge = raw39649 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39649Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39649 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 199).leftCharge (GramAssembly.key 199).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow199, Integer.Sparse.eval]

theorem keyMoment200 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 200) =
      Integer.Sparse.eval keyMomentRow200 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 200).leftCharge (GramAssembly.key 200).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 405) := by
    have ha : gramCharges (GramAssembly.key 200).leftCharge (GramAssembly.key 200).rightCharge = raw39650 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39650Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39650 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 200).leftCharge (GramAssembly.key 200).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow200, Integer.Sparse.eval]

theorem keyMoment201 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 201) =
      Integer.Sparse.eval keyMomentRow201 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 201).leftCharge (GramAssembly.key 201).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 397) := by
    have ha : gramCharges (GramAssembly.key 201).leftCharge (GramAssembly.key 201).rightCharge = raw39651 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39651Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39651 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 201).leftCharge (GramAssembly.key 201).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow201, Integer.Sparse.eval]

theorem keyMoment202 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 202) =
      Integer.Sparse.eval keyMomentRow202 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 202).leftCharge (GramAssembly.key 202).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 396) := by
    have ha : gramCharges (GramAssembly.key 202).leftCharge (GramAssembly.key 202).rightCharge = raw39652 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39652Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39652 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 202).leftCharge (GramAssembly.key 202).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow202, Integer.Sparse.eval]

theorem keyMoment203 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 203) =
      Integer.Sparse.eval keyMomentRow203 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 203).leftCharge (GramAssembly.key 203).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 1) := by
    have ha : gramCharges (GramAssembly.key 203).leftCharge (GramAssembly.key 203).rightCharge = raw39653 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39653Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39653 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 203).leftCharge (GramAssembly.key 203).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow203, Integer.Sparse.eval]

theorem keyMoment204 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 204) =
      Integer.Sparse.eval keyMomentRow204 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 204).leftCharge (GramAssembly.key 204).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 4) := by
    have ha : gramCharges (GramAssembly.key 204).leftCharge (GramAssembly.key 204).rightCharge = raw39654 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39654Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39654 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 204).leftCharge (GramAssembly.key 204).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow204, Integer.Sparse.eval]

theorem keyMoment205 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 205) =
      Integer.Sparse.eval keyMomentRow205 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 205).leftCharge (GramAssembly.key 205).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 469) := by
    have ha : gramCharges (GramAssembly.key 205).leftCharge (GramAssembly.key 205).rightCharge = raw39655 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39655Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39655 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 205).leftCharge (GramAssembly.key 205).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow205, Integer.Sparse.eval]

theorem keyMoment206 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 206) =
      Integer.Sparse.eval keyMomentRow206 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 206).leftCharge (GramAssembly.key 206).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 412) := by
    have ha : gramCharges (GramAssembly.key 206).leftCharge (GramAssembly.key 206).rightCharge = raw39656 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39656Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39656 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 206).leftCharge (GramAssembly.key 206).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow206, Integer.Sparse.eval]

theorem keyMoment207 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 207) =
      Integer.Sparse.eval keyMomentRow207 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 207).leftCharge (GramAssembly.key 207).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 465) := by
    have ha : gramCharges (GramAssembly.key 207).leftCharge (GramAssembly.key 207).rightCharge = raw39657 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39657Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39657 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 207).leftCharge (GramAssembly.key 207).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow207, Integer.Sparse.eval]

theorem keyMoment208 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 208) =
      Integer.Sparse.eval keyMomentRow208 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 208).leftCharge (GramAssembly.key 208).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 467) := by
    have ha : gramCharges (GramAssembly.key 208).leftCharge (GramAssembly.key 208).rightCharge = raw39658 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39658Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39658 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 208).leftCharge (GramAssembly.key 208).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow208, Integer.Sparse.eval]

theorem keyMoment209 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 209) =
      Integer.Sparse.eval keyMomentRow209 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 209).leftCharge (GramAssembly.key 209).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 468) := by
    have ha : gramCharges (GramAssembly.key 209).leftCharge (GramAssembly.key 209).rightCharge = raw39659 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39659Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39659 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 209).leftCharge (GramAssembly.key 209).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow209, Integer.Sparse.eval]

theorem keyMoment210 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 210) =
      Integer.Sparse.eval keyMomentRow210 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 210).leftCharge (GramAssembly.key 210).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 466) := by
    have ha : gramCharges (GramAssembly.key 210).leftCharge (GramAssembly.key 210).rightCharge = raw39660 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39660Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39660 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 210).leftCharge (GramAssembly.key 210).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow210, Integer.Sparse.eval]

theorem keyMoment211 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 211) =
      Integer.Sparse.eval keyMomentRow211 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 211).leftCharge (GramAssembly.key 211).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 3) := by
    have ha : gramCharges (GramAssembly.key 211).leftCharge (GramAssembly.key 211).rightCharge = raw39661 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39661Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39661 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 211).leftCharge (GramAssembly.key 211).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow211, Integer.Sparse.eval]

theorem keyMoment212 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 212) =
      Integer.Sparse.eval keyMomentRow212 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 212).leftCharge (GramAssembly.key 212).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 461) := by
    have ha : gramCharges (GramAssembly.key 212).leftCharge (GramAssembly.key 212).rightCharge = raw39662 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39662Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39662 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 212).leftCharge (GramAssembly.key 212).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow212, Integer.Sparse.eval]

theorem keyMoment213 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 213) =
      Integer.Sparse.eval keyMomentRow213 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 213).leftCharge (GramAssembly.key 213).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 464) := by
    have ha : gramCharges (GramAssembly.key 213).leftCharge (GramAssembly.key 213).rightCharge = raw39663 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39663Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39663 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 213).leftCharge (GramAssembly.key 213).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow213, Integer.Sparse.eval]

theorem keyMoment214 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 214) =
      Integer.Sparse.eval keyMomentRow214 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 214).leftCharge (GramAssembly.key 214).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 266) := by
    have ha : gramCharges (GramAssembly.key 214).leftCharge (GramAssembly.key 214).rightCharge = raw39664 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39664Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39664 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 214).leftCharge (GramAssembly.key 214).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow214, Integer.Sparse.eval]

theorem keyMoment215 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 215) =
      Integer.Sparse.eval keyMomentRow215 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 215).leftCharge (GramAssembly.key 215).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 465) := by
    have ha : gramCharges (GramAssembly.key 215).leftCharge (GramAssembly.key 215).rightCharge = raw39665 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39665Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39665 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 215).leftCharge (GramAssembly.key 215).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow215, Integer.Sparse.eval]

theorem keyMoment216 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 216) =
      Integer.Sparse.eval keyMomentRow216 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 216).leftCharge (GramAssembly.key 216).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 483) := by
    have ha : gramCharges (GramAssembly.key 216).leftCharge (GramAssembly.key 216).rightCharge = raw39666 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39666Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39666 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 216).leftCharge (GramAssembly.key 216).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow216, Integer.Sparse.eval]

theorem keyMoment217 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 217) =
      Integer.Sparse.eval keyMomentRow217 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 217).leftCharge (GramAssembly.key 217).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 384) := by
    have ha : gramCharges (GramAssembly.key 217).leftCharge (GramAssembly.key 217).rightCharge = raw39667 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39667Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39667 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 217).leftCharge (GramAssembly.key 217).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow217, Integer.Sparse.eval]

theorem keyMoment218 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 218) =
      Integer.Sparse.eval keyMomentRow218 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 218).leftCharge (GramAssembly.key 218).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 478) := by
    have ha : gramCharges (GramAssembly.key 218).leftCharge (GramAssembly.key 218).rightCharge = raw39668 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39668Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39668 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 218).leftCharge (GramAssembly.key 218).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow218, Integer.Sparse.eval]

theorem keyMoment219 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 219) =
      Integer.Sparse.eval keyMomentRow219 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 219).leftCharge (GramAssembly.key 219).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 480) := by
    have ha : gramCharges (GramAssembly.key 219).leftCharge (GramAssembly.key 219).rightCharge = raw39669 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39669Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39669 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 219).leftCharge (GramAssembly.key 219).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow219, Integer.Sparse.eval]

theorem keyMoment220 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 220) =
      Integer.Sparse.eval keyMomentRow220 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 220).leftCharge (GramAssembly.key 220).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 481) := by
    have ha : gramCharges (GramAssembly.key 220).leftCharge (GramAssembly.key 220).rightCharge = raw39670 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39670Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39670 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 220).leftCharge (GramAssembly.key 220).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow220, Integer.Sparse.eval]

theorem keyMoment221 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 221) =
      Integer.Sparse.eval keyMomentRow221 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 221).leftCharge (GramAssembly.key 221).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 479) := by
    have ha : gramCharges (GramAssembly.key 221).leftCharge (GramAssembly.key 221).rightCharge = raw39671 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39671Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39671 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 221).leftCharge (GramAssembly.key 221).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow221, Integer.Sparse.eval]

theorem keyMoment222 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 222) =
      Integer.Sparse.eval keyMomentRow222 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 222).leftCharge (GramAssembly.key 222).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 482) := by
    have ha : gramCharges (GramAssembly.key 222).leftCharge (GramAssembly.key 222).rightCharge = raw39672 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39672Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39672 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 222).leftCharge (GramAssembly.key 222).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow222, Integer.Sparse.eval]

theorem keyMoment223 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 223) =
      Integer.Sparse.eval keyMomentRow223 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 223).leftCharge (GramAssembly.key 223).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inr 3) := by
    have ha : gramCharges (GramAssembly.key 223).leftCharge (GramAssembly.key 223).rightCharge = raw39673 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39673Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39673 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 223).leftCharge (GramAssembly.key 223).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow223, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
