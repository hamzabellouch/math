import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys5
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical309

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment160 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 160) =
      Integer.Sparse.eval keyMomentRow160 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 160).leftCharge (GramAssembly.key 160).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 104) := by
    have ha : gramCharges (GramAssembly.key 160).leftCharge (GramAssembly.key 160).rightCharge = raw39610 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39610Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39610 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 160).leftCharge (GramAssembly.key 160).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow160, Integer.Sparse.eval]

theorem keyMoment161 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 161) =
      Integer.Sparse.eval keyMomentRow161 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 161).leftCharge (GramAssembly.key 161).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 100) := by
    have ha : gramCharges (GramAssembly.key 161).leftCharge (GramAssembly.key 161).rightCharge = raw39611 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39611Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39611 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 161).leftCharge (GramAssembly.key 161).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow161, Integer.Sparse.eval]

theorem keyMoment162 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 162) =
      Integer.Sparse.eval keyMomentRow162 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 162).leftCharge (GramAssembly.key 162).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 37) := by
    have ha : gramCharges (GramAssembly.key 162).leftCharge (GramAssembly.key 162).rightCharge = raw39612 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39612Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39612 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 162).leftCharge (GramAssembly.key 162).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow162, Integer.Sparse.eval]

theorem keyMoment163 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 163) =
      Integer.Sparse.eval keyMomentRow163 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 163).leftCharge (GramAssembly.key 163).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 16) := by
    have ha : gramCharges (GramAssembly.key 163).leftCharge (GramAssembly.key 163).rightCharge = raw39613 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39613Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39613 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 163).leftCharge (GramAssembly.key 163).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow163, Integer.Sparse.eval]

theorem keyMoment164 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 164) =
      Integer.Sparse.eval keyMomentRow164 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 164).leftCharge (GramAssembly.key 164).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 88) := by
    have ha : gramCharges (GramAssembly.key 164).leftCharge (GramAssembly.key 164).rightCharge = raw39614 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39614Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39614 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 164).leftCharge (GramAssembly.key 164).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow164, Integer.Sparse.eval]

theorem keyMoment165 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 165) =
      Integer.Sparse.eval keyMomentRow165 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 165).leftCharge (GramAssembly.key 165).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 99) := by
    have ha : gramCharges (GramAssembly.key 165).leftCharge (GramAssembly.key 165).rightCharge = raw39615 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39615Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39615 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 165).leftCharge (GramAssembly.key 165).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow165, Integer.Sparse.eval]

theorem keyMoment166 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 166) =
      Integer.Sparse.eval keyMomentRow166 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 166).leftCharge (GramAssembly.key 166).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 59) := by
    have ha : gramCharges (GramAssembly.key 166).leftCharge (GramAssembly.key 166).rightCharge = raw39616 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39616Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39616 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 166).leftCharge (GramAssembly.key 166).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow166, Integer.Sparse.eval]

theorem keyMoment167 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 167) =
      Integer.Sparse.eval keyMomentRow167 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 167).leftCharge (GramAssembly.key 167).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 19) := by
    have ha : gramCharges (GramAssembly.key 167).leftCharge (GramAssembly.key 167).rightCharge = raw39617 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39617Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39617 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 167).leftCharge (GramAssembly.key 167).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow167, Integer.Sparse.eval]

theorem keyMoment168 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 168) =
      Integer.Sparse.eval keyMomentRow168 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 168).leftCharge (GramAssembly.key 168).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 14) := by
    have ha : gramCharges (GramAssembly.key 168).leftCharge (GramAssembly.key 168).rightCharge = raw39618 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39618Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39618 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 168).leftCharge (GramAssembly.key 168).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow168, Integer.Sparse.eval]

theorem keyMoment169 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 169) =
      Integer.Sparse.eval keyMomentRow169 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 169).leftCharge (GramAssembly.key 169).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 12) := by
    have ha : gramCharges (GramAssembly.key 169).leftCharge (GramAssembly.key 169).rightCharge = raw39619 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39619Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39619 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 169).leftCharge (GramAssembly.key 169).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow169, Integer.Sparse.eval]

theorem keyMoment170 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 170) =
      Integer.Sparse.eval keyMomentRow170 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 170).leftCharge (GramAssembly.key 170).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 17) := by
    have ha : gramCharges (GramAssembly.key 170).leftCharge (GramAssembly.key 170).rightCharge = raw39620 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39620Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39620 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 170).leftCharge (GramAssembly.key 170).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow170, Integer.Sparse.eval]

theorem keyMoment171 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 171) =
      Integer.Sparse.eval keyMomentRow171 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 171).leftCharge (GramAssembly.key 171).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 15) := by
    have ha : gramCharges (GramAssembly.key 171).leftCharge (GramAssembly.key 171).rightCharge = raw39621 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39621Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39621 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 171).leftCharge (GramAssembly.key 171).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow171, Integer.Sparse.eval]

theorem keyMoment172 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 172) =
      Integer.Sparse.eval keyMomentRow172 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 172).leftCharge (GramAssembly.key 172).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 8) := by
    have ha : gramCharges (GramAssembly.key 172).leftCharge (GramAssembly.key 172).rightCharge = raw39622 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39622Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39622 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 172).leftCharge (GramAssembly.key 172).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow172, Integer.Sparse.eval]

theorem keyMoment173 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 173) =
      Integer.Sparse.eval keyMomentRow173 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 173).leftCharge (GramAssembly.key 173).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 9) := by
    have ha : gramCharges (GramAssembly.key 173).leftCharge (GramAssembly.key 173).rightCharge = raw39623 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39623Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39623 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 173).leftCharge (GramAssembly.key 173).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow173, Integer.Sparse.eval]

theorem keyMoment174 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 174) =
      Integer.Sparse.eval keyMomentRow174 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 174).leftCharge (GramAssembly.key 174).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 13) := by
    have ha : gramCharges (GramAssembly.key 174).leftCharge (GramAssembly.key 174).rightCharge = raw39624 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39624Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39624 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 174).leftCharge (GramAssembly.key 174).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow174, Integer.Sparse.eval]

theorem keyMoment175 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 175) =
      Integer.Sparse.eval keyMomentRow175 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 175).leftCharge (GramAssembly.key 175).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 11) := by
    have ha : gramCharges (GramAssembly.key 175).leftCharge (GramAssembly.key 175).rightCharge = raw39625 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39625Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39625 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 175).leftCharge (GramAssembly.key 175).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow175, Integer.Sparse.eval]

theorem keyMoment176 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 176) =
      Integer.Sparse.eval keyMomentRow176 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 176).leftCharge (GramAssembly.key 176).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 20) := by
    have ha : gramCharges (GramAssembly.key 176).leftCharge (GramAssembly.key 176).rightCharge = raw39626 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39626Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39626 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 176).leftCharge (GramAssembly.key 176).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow176, Integer.Sparse.eval]

theorem keyMoment177 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 177) =
      Integer.Sparse.eval keyMomentRow177 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 177).leftCharge (GramAssembly.key 177).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 16) := by
    have ha : gramCharges (GramAssembly.key 177).leftCharge (GramAssembly.key 177).rightCharge = raw39627 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39627Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39627 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 177).leftCharge (GramAssembly.key 177).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow177, Integer.Sparse.eval]

theorem keyMoment178 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 178) =
      Integer.Sparse.eval keyMomentRow178 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 178).leftCharge (GramAssembly.key 178).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 18) := by
    have ha : gramCharges (GramAssembly.key 178).leftCharge (GramAssembly.key 178).rightCharge = raw39628 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39628Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39628 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 178).leftCharge (GramAssembly.key 178).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow178, Integer.Sparse.eval]

theorem keyMoment179 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 179) =
      Integer.Sparse.eval keyMomentRow179 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 179).leftCharge (GramAssembly.key 179).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inr 0) := by
    have ha : gramCharges (GramAssembly.key 179).leftCharge (GramAssembly.key 179).rightCharge = raw39629 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39629Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39629 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 179).leftCharge (GramAssembly.key 179).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow179, Integer.Sparse.eval]

theorem keyMoment180 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 180) =
      Integer.Sparse.eval keyMomentRow180 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 180).leftCharge (GramAssembly.key 180).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 389) := by
    have ha : gramCharges (GramAssembly.key 180).leftCharge (GramAssembly.key 180).rightCharge = raw39630 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39630Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39630 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 180).leftCharge (GramAssembly.key 180).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow180, Integer.Sparse.eval]

theorem keyMoment181 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 181) =
      Integer.Sparse.eval keyMomentRow181 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 181).leftCharge (GramAssembly.key 181).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 385) := by
    have ha : gramCharges (GramAssembly.key 181).leftCharge (GramAssembly.key 181).rightCharge = raw39631 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39631Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39631 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 181).leftCharge (GramAssembly.key 181).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow181, Integer.Sparse.eval]

theorem keyMoment182 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 182) =
      Integer.Sparse.eval keyMomentRow182 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 182).leftCharge (GramAssembly.key 182).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 377) := by
    have ha : gramCharges (GramAssembly.key 182).leftCharge (GramAssembly.key 182).rightCharge = raw39632 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39632Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39632 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 182).leftCharge (GramAssembly.key 182).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow182, Integer.Sparse.eval]

theorem keyMoment183 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 183) =
      Integer.Sparse.eval keyMomentRow183 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 183).leftCharge (GramAssembly.key 183).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 387) := by
    have ha : gramCharges (GramAssembly.key 183).leftCharge (GramAssembly.key 183).rightCharge = raw39633 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39633Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39633 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 183).leftCharge (GramAssembly.key 183).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow183, Integer.Sparse.eval]

theorem keyMoment184 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 184) =
      Integer.Sparse.eval keyMomentRow184 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 184).leftCharge (GramAssembly.key 184).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 383) := by
    have ha : gramCharges (GramAssembly.key 184).leftCharge (GramAssembly.key 184).rightCharge = raw39634 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39634Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39634 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 184).leftCharge (GramAssembly.key 184).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow184, Integer.Sparse.eval]

theorem keyMoment185 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 185) =
      Integer.Sparse.eval keyMomentRow185 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 185).leftCharge (GramAssembly.key 185).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 384) := by
    have ha : gramCharges (GramAssembly.key 185).leftCharge (GramAssembly.key 185).rightCharge = raw39635 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39635Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39635 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 185).leftCharge (GramAssembly.key 185).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow185, Integer.Sparse.eval]

theorem keyMoment186 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 186) =
      Integer.Sparse.eval keyMomentRow186 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 186).leftCharge (GramAssembly.key 186).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 382) := by
    have ha : gramCharges (GramAssembly.key 186).leftCharge (GramAssembly.key 186).rightCharge = raw39636 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39636Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39636 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 186).leftCharge (GramAssembly.key 186).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow186, Integer.Sparse.eval]

theorem keyMoment187 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 187) =
      Integer.Sparse.eval keyMomentRow187 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 187).leftCharge (GramAssembly.key 187).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 402) := by
    have ha : gramCharges (GramAssembly.key 187).leftCharge (GramAssembly.key 187).rightCharge = raw39637 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39637Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39637 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 187).leftCharge (GramAssembly.key 187).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow187, Integer.Sparse.eval]

theorem keyMoment188 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 188) =
      Integer.Sparse.eval keyMomentRow188 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 188).leftCharge (GramAssembly.key 188).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 414) := by
    have ha : gramCharges (GramAssembly.key 188).leftCharge (GramAssembly.key 188).rightCharge = raw39638 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39638Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39638 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 188).leftCharge (GramAssembly.key 188).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow188, Integer.Sparse.eval]

theorem keyMoment189 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 189) =
      Integer.Sparse.eval keyMomentRow189 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 189).leftCharge (GramAssembly.key 189).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 410) := by
    have ha : gramCharges (GramAssembly.key 189).leftCharge (GramAssembly.key 189).rightCharge = raw39639 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39639Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39639 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 189).leftCharge (GramAssembly.key 189).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow189, Integer.Sparse.eval]

theorem keyMoment190 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 190) =
      Integer.Sparse.eval keyMomentRow190 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 190).leftCharge (GramAssembly.key 190).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 409) := by
    have ha : gramCharges (GramAssembly.key 190).leftCharge (GramAssembly.key 190).rightCharge = raw39640 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39640Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39640 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 190).leftCharge (GramAssembly.key 190).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow190, Integer.Sparse.eval]

theorem keyMoment191 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 191) =
      Integer.Sparse.eval keyMomentRow191 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 191).leftCharge (GramAssembly.key 191).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 391) := by
    have ha : gramCharges (GramAssembly.key 191).leftCharge (GramAssembly.key 191).rightCharge = raw39641 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39641Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39641 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 191).leftCharge (GramAssembly.key 191).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow191, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
