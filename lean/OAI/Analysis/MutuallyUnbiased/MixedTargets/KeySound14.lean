import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical311

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment448 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 448) =
      Integer.Sparse.eval keyMomentRow448 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 448).leftCharge (GramAssembly.key 448).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 496) := by
    have ha : gramCharges (GramAssembly.key 448).leftCharge (GramAssembly.key 448).rightCharge = raw39896 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39896Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39896 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 448).leftCharge (GramAssembly.key 448).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow448, Integer.Sparse.eval]

theorem keyMoment449 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 449) =
      Integer.Sparse.eval keyMomentRow449 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 449).leftCharge (GramAssembly.key 449).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 451) := by
    have ha : gramCharges (GramAssembly.key 449).leftCharge (GramAssembly.key 449).rightCharge = raw39897 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39897Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39897 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 449).leftCharge (GramAssembly.key 449).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow449, Integer.Sparse.eval]

theorem keyMoment450 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 450) =
      Integer.Sparse.eval keyMomentRow450 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 450).leftCharge (GramAssembly.key 450).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 369) := by
    have ha : gramCharges (GramAssembly.key 450).leftCharge (GramAssembly.key 450).rightCharge = raw39898 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39898Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39898 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 450).leftCharge (GramAssembly.key 450).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow450, Integer.Sparse.eval]

theorem keyMoment451 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 451) =
      Integer.Sparse.eval keyMomentRow451 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 451).leftCharge (GramAssembly.key 451).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 496) := by
    have ha : gramCharges (GramAssembly.key 451).leftCharge (GramAssembly.key 451).rightCharge = raw39899 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39899Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39899 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 451).leftCharge (GramAssembly.key 451).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow451, Integer.Sparse.eval]

theorem keyMoment452 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 452) =
      Integer.Sparse.eval keyMomentRow452 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 452).leftCharge (GramAssembly.key 452).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 505) := by
    have ha : gramCharges (GramAssembly.key 452).leftCharge (GramAssembly.key 452).rightCharge = raw39900 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39900Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39900 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 452).leftCharge (GramAssembly.key 452).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow452, Integer.Sparse.eval]

theorem keyMoment453 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 453) =
      Integer.Sparse.eval keyMomentRow453 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 453).leftCharge (GramAssembly.key 453).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 449) := by
    have ha : gramCharges (GramAssembly.key 453).leftCharge (GramAssembly.key 453).rightCharge = raw39901 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39901Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39901 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 453).leftCharge (GramAssembly.key 453).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow453, Integer.Sparse.eval]

theorem keyMoment454 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 454) =
      Integer.Sparse.eval keyMomentRow454 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 454).leftCharge (GramAssembly.key 454).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 286) := by
    have ha : gramCharges (GramAssembly.key 454).leftCharge (GramAssembly.key 454).rightCharge = raw39902 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39902Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39902 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 454).leftCharge (GramAssembly.key 454).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow454, Integer.Sparse.eval]

theorem keyMoment455 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 455) =
      Integer.Sparse.eval keyMomentRow455 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 455).leftCharge (GramAssembly.key 455).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 438) := by
    have ha : gramCharges (GramAssembly.key 455).leftCharge (GramAssembly.key 455).rightCharge = raw39903 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39903Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39903 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 455).leftCharge (GramAssembly.key 455).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow455, Integer.Sparse.eval]

theorem keyMoment456 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 456) =
      Integer.Sparse.eval keyMomentRow456 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 456).leftCharge (GramAssembly.key 456).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 490) := by
    have ha : gramCharges (GramAssembly.key 456).leftCharge (GramAssembly.key 456).rightCharge = raw39904 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39904Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39904 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 456).leftCharge (GramAssembly.key 456).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow456, Integer.Sparse.eval]

theorem keyMoment457 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 457) =
      Integer.Sparse.eval keyMomentRow457 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 457).leftCharge (GramAssembly.key 457).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 432) := by
    have ha : gramCharges (GramAssembly.key 457).leftCharge (GramAssembly.key 457).rightCharge = raw39905 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39905Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39905 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 457).leftCharge (GramAssembly.key 457).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow457, Integer.Sparse.eval]

theorem keyMoment458 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 458) =
      Integer.Sparse.eval keyMomentRow458 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 458).leftCharge (GramAssembly.key 458).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 449) := by
    have ha : gramCharges (GramAssembly.key 458).leftCharge (GramAssembly.key 458).rightCharge = raw39906 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39906Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39906 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 458).leftCharge (GramAssembly.key 458).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow458, Integer.Sparse.eval]

theorem keyMoment459 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 459) =
      Integer.Sparse.eval keyMomentRow459 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 459).leftCharge (GramAssembly.key 459).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 178) := by
    have ha : gramCharges (GramAssembly.key 459).leftCharge (GramAssembly.key 459).rightCharge = raw39907 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39907Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39907 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 459).leftCharge (GramAssembly.key 459).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow459, Integer.Sparse.eval]

theorem keyMoment460 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 460) =
      Integer.Sparse.eval keyMomentRow460 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 460).leftCharge (GramAssembly.key 460).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 424) := by
    have ha : gramCharges (GramAssembly.key 460).leftCharge (GramAssembly.key 460).rightCharge = raw39908 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39908Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39908 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 460).leftCharge (GramAssembly.key 460).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow460, Integer.Sparse.eval]

theorem keyMoment461 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 461) =
      Integer.Sparse.eval keyMomentRow461 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 461).leftCharge (GramAssembly.key 461).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 492) := by
    have ha : gramCharges (GramAssembly.key 461).leftCharge (GramAssembly.key 461).rightCharge = raw39909 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39909Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39909 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 461).leftCharge (GramAssembly.key 461).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow461, Integer.Sparse.eval]

theorem keyMoment462 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 462) =
      Integer.Sparse.eval keyMomentRow462 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 462).leftCharge (GramAssembly.key 462).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 179) := by
    have ha : gramCharges (GramAssembly.key 462).leftCharge (GramAssembly.key 462).rightCharge = raw39910 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39910Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39910 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 462).leftCharge (GramAssembly.key 462).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow462, Integer.Sparse.eval]

theorem keyMoment463 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 463) =
      Integer.Sparse.eval keyMomentRow463 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 463).leftCharge (GramAssembly.key 463).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 505) := by
    have ha : gramCharges (GramAssembly.key 463).leftCharge (GramAssembly.key 463).rightCharge = raw39911 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39911Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39911 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 463).leftCharge (GramAssembly.key 463).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow463, Integer.Sparse.eval]

theorem keyMoment464 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 464) =
      Integer.Sparse.eval keyMomentRow464 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 464).leftCharge (GramAssembly.key 464).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 449) := by
    have ha : gramCharges (GramAssembly.key 464).leftCharge (GramAssembly.key 464).rightCharge = raw39912 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39912Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39912 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 464).leftCharge (GramAssembly.key 464).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow464, Integer.Sparse.eval]

theorem keyMoment465 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 465) =
      Integer.Sparse.eval keyMomentRow465 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 465).leftCharge (GramAssembly.key 465).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 180) := by
    have ha : gramCharges (GramAssembly.key 465).leftCharge (GramAssembly.key 465).rightCharge = raw39913 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39913Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39913 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 465).leftCharge (GramAssembly.key 465).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow465, Integer.Sparse.eval]

theorem keyMoment466 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 466) =
      Integer.Sparse.eval keyMomentRow466 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 466).leftCharge (GramAssembly.key 466).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 471) := by
    have ha : gramCharges (GramAssembly.key 466).leftCharge (GramAssembly.key 466).rightCharge = raw39914 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39914Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39914 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 466).leftCharge (GramAssembly.key 466).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow466, Integer.Sparse.eval]

theorem keyMoment467 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 467) =
      Integer.Sparse.eval keyMomentRow467 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 467).leftCharge (GramAssembly.key 467).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 317) := by
    have ha : gramCharges (GramAssembly.key 467).leftCharge (GramAssembly.key 467).rightCharge = raw39915 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39915Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39915 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 467).leftCharge (GramAssembly.key 467).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow467, Integer.Sparse.eval]

theorem keyMoment468 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 468) =
      Integer.Sparse.eval keyMomentRow468 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 468).leftCharge (GramAssembly.key 468).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 448) := by
    have ha : gramCharges (GramAssembly.key 468).leftCharge (GramAssembly.key 468).rightCharge = raw39916 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39916Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39916 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 468).leftCharge (GramAssembly.key 468).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow468, Integer.Sparse.eval]

theorem keyMoment469 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 469) =
      Integer.Sparse.eval keyMomentRow469 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 469).leftCharge (GramAssembly.key 469).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 343) := by
    have ha : gramCharges (GramAssembly.key 469).leftCharge (GramAssembly.key 469).rightCharge = raw39917 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39917Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39917 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 469).leftCharge (GramAssembly.key 469).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow469, Integer.Sparse.eval]

theorem keyMoment470 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 470) =
      Integer.Sparse.eval keyMomentRow470 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 470).leftCharge (GramAssembly.key 470).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 316) := by
    have ha : gramCharges (GramAssembly.key 470).leftCharge (GramAssembly.key 470).rightCharge = raw39918 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39918Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39918 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 470).leftCharge (GramAssembly.key 470).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow470, Integer.Sparse.eval]

theorem keyMoment471 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 471) =
      Integer.Sparse.eval keyMomentRow471 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 471).leftCharge (GramAssembly.key 471).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 335) := by
    have ha : gramCharges (GramAssembly.key 471).leftCharge (GramAssembly.key 471).rightCharge = raw39919 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39919Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39919 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 471).leftCharge (GramAssembly.key 471).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow471, Integer.Sparse.eval]

theorem keyMoment472 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 472) =
      Integer.Sparse.eval keyMomentRow472 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 472).leftCharge (GramAssembly.key 472).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 127) := by
    have ha : gramCharges (GramAssembly.key 472).leftCharge (GramAssembly.key 472).rightCharge = raw39920 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39920Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39920 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 472).leftCharge (GramAssembly.key 472).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow472, Integer.Sparse.eval]

theorem keyMoment473 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 473) =
      Integer.Sparse.eval keyMomentRow473 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 473).leftCharge (GramAssembly.key 473).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 314) := by
    have ha : gramCharges (GramAssembly.key 473).leftCharge (GramAssembly.key 473).rightCharge = raw39921 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39921Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39921 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 473).leftCharge (GramAssembly.key 473).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow473, Integer.Sparse.eval]

theorem keyMoment474 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 474) =
      Integer.Sparse.eval keyMomentRow474 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 474).leftCharge (GramAssembly.key 474).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 306) := by
    have ha : gramCharges (GramAssembly.key 474).leftCharge (GramAssembly.key 474).rightCharge = raw39922 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39922Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39922 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 474).leftCharge (GramAssembly.key 474).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow474, Integer.Sparse.eval]

theorem keyMoment475 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 475) =
      Integer.Sparse.eval keyMomentRow475 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 475).leftCharge (GramAssembly.key 475).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 450) := by
    have ha : gramCharges (GramAssembly.key 475).leftCharge (GramAssembly.key 475).rightCharge = raw39923 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39923Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39923 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 475).leftCharge (GramAssembly.key 475).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow475, Integer.Sparse.eval]

theorem keyMoment476 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 476) =
      Integer.Sparse.eval keyMomentRow476 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 476).leftCharge (GramAssembly.key 476).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 175) := by
    have ha : gramCharges (GramAssembly.key 476).leftCharge (GramAssembly.key 476).rightCharge = raw39924 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39924Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39924 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 476).leftCharge (GramAssembly.key 476).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow476, Integer.Sparse.eval]

theorem keyMoment477 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 477) =
      Integer.Sparse.eval keyMomentRow477 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 477).leftCharge (GramAssembly.key 477).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 295) := by
    have ha : gramCharges (GramAssembly.key 477).leftCharge (GramAssembly.key 477).rightCharge = raw39925 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39925Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39925 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 477).leftCharge (GramAssembly.key 477).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow477, Integer.Sparse.eval]

theorem keyMoment478 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 478) =
      Integer.Sparse.eval keyMomentRow478 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 478).leftCharge (GramAssembly.key 478).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 160) := by
    have ha : gramCharges (GramAssembly.key 478).leftCharge (GramAssembly.key 478).rightCharge = raw39926 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39926Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39926 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 478).leftCharge (GramAssembly.key 478).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow478, Integer.Sparse.eval]

theorem keyMoment479 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 479) =
      Integer.Sparse.eval keyMomentRow479 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 479).leftCharge (GramAssembly.key 479).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 38) := by
    have ha : gramCharges (GramAssembly.key 479).leftCharge (GramAssembly.key 479).rightCharge = raw39927 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39927Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39927 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 479).leftCharge (GramAssembly.key 479).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow479, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
