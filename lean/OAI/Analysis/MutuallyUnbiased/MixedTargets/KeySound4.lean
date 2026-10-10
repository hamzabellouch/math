import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys4
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical309

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment128 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 128) =
      Integer.Sparse.eval keyMomentRow128 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 128).leftCharge (GramAssembly.key 128).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 154) := by
    have ha : gramCharges (GramAssembly.key 128).leftCharge (GramAssembly.key 128).rightCharge = raw39578 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39578Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39578 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 128).leftCharge (GramAssembly.key 128).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow128, Integer.Sparse.eval]

theorem keyMoment129 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 129) =
      Integer.Sparse.eval keyMomentRow129 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 129).leftCharge (GramAssembly.key 129).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 41) := by
    have ha : gramCharges (GramAssembly.key 129).leftCharge (GramAssembly.key 129).rightCharge = raw39579 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39579Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39579 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 129).leftCharge (GramAssembly.key 129).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow129, Integer.Sparse.eval]

theorem keyMoment130 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 130) =
      Integer.Sparse.eval keyMomentRow130 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 130).leftCharge (GramAssembly.key 130).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 102) := by
    have ha : gramCharges (GramAssembly.key 130).leftCharge (GramAssembly.key 130).rightCharge = raw39580 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39580Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39580 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 130).leftCharge (GramAssembly.key 130).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow130, Integer.Sparse.eval]

theorem keyMoment131 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 131) =
      Integer.Sparse.eval keyMomentRow131 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 131).leftCharge (GramAssembly.key 131).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 143) := by
    have ha : gramCharges (GramAssembly.key 131).leftCharge (GramAssembly.key 131).rightCharge = raw39581 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39581Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39581 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 131).leftCharge (GramAssembly.key 131).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow131, Integer.Sparse.eval]

theorem keyMoment132 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 132) =
      Integer.Sparse.eval keyMomentRow132 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 132).leftCharge (GramAssembly.key 132).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 32) := by
    have ha : gramCharges (GramAssembly.key 132).leftCharge (GramAssembly.key 132).rightCharge = raw39582 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39582Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39582 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 132).leftCharge (GramAssembly.key 132).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow132, Integer.Sparse.eval]

theorem keyMoment133 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 133) =
      Integer.Sparse.eval keyMomentRow133 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 133).leftCharge (GramAssembly.key 133).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 19) := by
    have ha : gramCharges (GramAssembly.key 133).leftCharge (GramAssembly.key 133).rightCharge = raw39583 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39583Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39583 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 133).leftCharge (GramAssembly.key 133).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow133, Integer.Sparse.eval]

theorem keyMoment134 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 134) =
      Integer.Sparse.eval keyMomentRow134 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 134).leftCharge (GramAssembly.key 134).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 73) := by
    have ha : gramCharges (GramAssembly.key 134).leftCharge (GramAssembly.key 134).rightCharge = raw39584 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39584Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39584 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 134).leftCharge (GramAssembly.key 134).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow134, Integer.Sparse.eval]

theorem keyMoment135 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 135) =
      Integer.Sparse.eval keyMomentRow135 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 135).leftCharge (GramAssembly.key 135).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 97) := by
    have ha : gramCharges (GramAssembly.key 135).leftCharge (GramAssembly.key 135).rightCharge = raw39585 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39585Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39585 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 135).leftCharge (GramAssembly.key 135).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow135, Integer.Sparse.eval]

theorem keyMoment136 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 136) =
      Integer.Sparse.eval keyMomentRow136 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 136).leftCharge (GramAssembly.key 136).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 197) := by
    have ha : gramCharges (GramAssembly.key 136).leftCharge (GramAssembly.key 136).rightCharge = raw39586 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39586Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39586 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 136).leftCharge (GramAssembly.key 136).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow136, Integer.Sparse.eval]

theorem keyMoment137 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 137) =
      Integer.Sparse.eval keyMomentRow137 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 137).leftCharge (GramAssembly.key 137).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 249) := by
    have ha : gramCharges (GramAssembly.key 137).leftCharge (GramAssembly.key 137).rightCharge = raw39587 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39587Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39587 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 137).leftCharge (GramAssembly.key 137).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow137, Integer.Sparse.eval]

theorem keyMoment138 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 138) =
      Integer.Sparse.eval keyMomentRow138 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 138).leftCharge (GramAssembly.key 138).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 14) := by
    have ha : gramCharges (GramAssembly.key 138).leftCharge (GramAssembly.key 138).rightCharge = raw39588 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39588Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39588 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 138).leftCharge (GramAssembly.key 138).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow138, Integer.Sparse.eval]

theorem keyMoment139 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 139) =
      Integer.Sparse.eval keyMomentRow139 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 139).leftCharge (GramAssembly.key 139).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 67) := by
    have ha : gramCharges (GramAssembly.key 139).leftCharge (GramAssembly.key 139).rightCharge = raw39589 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39589Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39589 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 139).leftCharge (GramAssembly.key 139).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow139, Integer.Sparse.eval]

theorem keyMoment140 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 140) =
      Integer.Sparse.eval keyMomentRow140 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 140).leftCharge (GramAssembly.key 140).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 87) := by
    have ha : gramCharges (GramAssembly.key 140).leftCharge (GramAssembly.key 140).rightCharge = raw39590 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39590Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39590 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 140).leftCharge (GramAssembly.key 140).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow140, Integer.Sparse.eval]

theorem keyMoment141 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 141) =
      Integer.Sparse.eval keyMomentRow141 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 141).leftCharge (GramAssembly.key 141).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 227) := by
    have ha : gramCharges (GramAssembly.key 141).leftCharge (GramAssembly.key 141).rightCharge = raw39591 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39591Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39591 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 141).leftCharge (GramAssembly.key 141).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow141, Integer.Sparse.eval]

theorem keyMoment142 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 142) =
      Integer.Sparse.eval keyMomentRow142 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 142).leftCharge (GramAssembly.key 142).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 60) := by
    have ha : gramCharges (GramAssembly.key 142).leftCharge (GramAssembly.key 142).rightCharge = raw39592 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39592Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39592 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 142).leftCharge (GramAssembly.key 142).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow142, Integer.Sparse.eval]

theorem keyMoment143 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 143) =
      Integer.Sparse.eval keyMomentRow143 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 143).leftCharge (GramAssembly.key 143).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 169) := by
    have ha : gramCharges (GramAssembly.key 143).leftCharge (GramAssembly.key 143).rightCharge = raw39593 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39593Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39593 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 143).leftCharge (GramAssembly.key 143).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow143, Integer.Sparse.eval]

theorem keyMoment144 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 144) =
      Integer.Sparse.eval keyMomentRow144 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 144).leftCharge (GramAssembly.key 144).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 58) := by
    have ha : gramCharges (GramAssembly.key 144).leftCharge (GramAssembly.key 144).rightCharge = raw39594 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39594Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39594 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 144).leftCharge (GramAssembly.key 144).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow144, Integer.Sparse.eval]

theorem keyMoment145 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 145) =
      Integer.Sparse.eval keyMomentRow145 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 145).leftCharge (GramAssembly.key 145).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 102) := by
    have ha : gramCharges (GramAssembly.key 145).leftCharge (GramAssembly.key 145).rightCharge = raw39595 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39595Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39595 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 145).leftCharge (GramAssembly.key 145).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow145, Integer.Sparse.eval]

theorem keyMoment146 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 146) =
      Integer.Sparse.eval keyMomentRow146 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 146).leftCharge (GramAssembly.key 146).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 97) := by
    have ha : gramCharges (GramAssembly.key 146).leftCharge (GramAssembly.key 146).rightCharge = raw39596 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39596Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39596 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 146).leftCharge (GramAssembly.key 146).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow146, Integer.Sparse.eval]

theorem keyMoment147 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 147) =
      Integer.Sparse.eval keyMomentRow147 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 147).leftCharge (GramAssembly.key 147).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 76) := by
    have ha : gramCharges (GramAssembly.key 147).leftCharge (GramAssembly.key 147).rightCharge = raw39597 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39597Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39597 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 147).leftCharge (GramAssembly.key 147).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow147, Integer.Sparse.eval]

theorem keyMoment148 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 148) =
      Integer.Sparse.eval keyMomentRow148 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 148).leftCharge (GramAssembly.key 148).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 60) := by
    have ha : gramCharges (GramAssembly.key 148).leftCharge (GramAssembly.key 148).rightCharge = raw39598 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39598Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39598 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 148).leftCharge (GramAssembly.key 148).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow148, Integer.Sparse.eval]

theorem keyMoment149 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 149) =
      Integer.Sparse.eval keyMomentRow149 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 149).leftCharge (GramAssembly.key 149).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 87) := by
    have ha : gramCharges (GramAssembly.key 149).leftCharge (GramAssembly.key 149).rightCharge = raw39599 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39599Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39599 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 149).leftCharge (GramAssembly.key 149).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow149, Integer.Sparse.eval]

theorem keyMoment150 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 150) =
      Integer.Sparse.eval keyMomentRow150 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 150).leftCharge (GramAssembly.key 150).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 58) := by
    have ha : gramCharges (GramAssembly.key 150).leftCharge (GramAssembly.key 150).rightCharge = raw39600 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39600Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39600 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 150).leftCharge (GramAssembly.key 150).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow150, Integer.Sparse.eval]

theorem keyMoment151 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 151) =
      Integer.Sparse.eval keyMomentRow151 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 151).leftCharge (GramAssembly.key 151).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 101) := by
    have ha : gramCharges (GramAssembly.key 151).leftCharge (GramAssembly.key 151).rightCharge = raw39601 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39601Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39601 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 151).leftCharge (GramAssembly.key 151).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow151, Integer.Sparse.eval]

theorem keyMoment152 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 152) =
      Integer.Sparse.eval keyMomentRow152 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 152).leftCharge (GramAssembly.key 152).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 74) := by
    have ha : gramCharges (GramAssembly.key 152).leftCharge (GramAssembly.key 152).rightCharge = raw39602 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39602Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39602 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 152).leftCharge (GramAssembly.key 152).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow152, Integer.Sparse.eval]

theorem keyMoment153 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 153) =
      Integer.Sparse.eval keyMomentRow153 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 153).leftCharge (GramAssembly.key 153).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 103) := by
    have ha : gramCharges (GramAssembly.key 153).leftCharge (GramAssembly.key 153).rightCharge = raw39603 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39603Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39603 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 153).leftCharge (GramAssembly.key 153).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow153, Integer.Sparse.eval]

theorem keyMoment154 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 154) =
      Integer.Sparse.eval keyMomentRow154 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 154).leftCharge (GramAssembly.key 154).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 98) := by
    have ha : gramCharges (GramAssembly.key 154).leftCharge (GramAssembly.key 154).rightCharge = raw39604 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39604Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39604 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 154).leftCharge (GramAssembly.key 154).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow154, Integer.Sparse.eval]

theorem keyMoment155 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 155) =
      Integer.Sparse.eval keyMomentRow155 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 155).leftCharge (GramAssembly.key 155).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 75) := by
    have ha : gramCharges (GramAssembly.key 155).leftCharge (GramAssembly.key 155).rightCharge = raw39605 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39605Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39605 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 155).leftCharge (GramAssembly.key 155).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow155, Integer.Sparse.eval]

theorem keyMoment156 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 156) =
      Integer.Sparse.eval keyMomentRow156 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 156).leftCharge (GramAssembly.key 156).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 91) := by
    have ha : gramCharges (GramAssembly.key 156).leftCharge (GramAssembly.key 156).rightCharge = raw39606 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39606Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39606 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 156).leftCharge (GramAssembly.key 156).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow156, Integer.Sparse.eval]

theorem keyMoment157 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 157) =
      Integer.Sparse.eval keyMomentRow157 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 157).leftCharge (GramAssembly.key 157).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inr 2) := by
    have ha : gramCharges (GramAssembly.key 157).leftCharge (GramAssembly.key 157).rightCharge = raw39607 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39607Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39607 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 157).leftCharge (GramAssembly.key 157).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow157, Integer.Sparse.eval]

theorem keyMoment158 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 158) =
      Integer.Sparse.eval keyMomentRow158 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 158).leftCharge (GramAssembly.key 158).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 94) := by
    have ha : gramCharges (GramAssembly.key 158).leftCharge (GramAssembly.key 158).rightCharge = raw39608 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39608Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39608 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 158).leftCharge (GramAssembly.key 158).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow158, Integer.Sparse.eval]

theorem keyMoment159 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 159) =
      Integer.Sparse.eval keyMomentRow159 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 159).leftCharge (GramAssembly.key 159).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 93) := by
    have ha : gramCharges (GramAssembly.key 159).leftCharge (GramAssembly.key 159).rightCharge = raw39609 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39609Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39609 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 159).leftCharge (GramAssembly.key 159).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow159, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
