import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical297
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical310

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment320 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 320) =
      Integer.Sparse.eval keyMomentRow320 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 320).leftCharge (GramAssembly.key 320).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 415) := by
    have ha : gramCharges (GramAssembly.key 320).leftCharge (GramAssembly.key 320).rightCharge = raw39770 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39770Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39770 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 320).leftCharge (GramAssembly.key 320).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow320, Integer.Sparse.eval]

theorem keyMoment321 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 321) =
      Integer.Sparse.eval keyMomentRow321 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 321).leftCharge (GramAssembly.key 321).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 416) := by
    have ha : gramCharges (GramAssembly.key 321).leftCharge (GramAssembly.key 321).rightCharge = raw39771 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39771Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39771 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 321).leftCharge (GramAssembly.key 321).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow321, Integer.Sparse.eval]

theorem keyMoment322 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 322) =
      Integer.Sparse.eval keyMomentRow322 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 322).leftCharge (GramAssembly.key 322).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 152) := by
    have ha : gramCharges (GramAssembly.key 322).leftCharge (GramAssembly.key 322).rightCharge = raw39772 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39772Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39772 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 322).leftCharge (GramAssembly.key 322).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow322, Integer.Sparse.eval]

theorem keyMoment323 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 323) =
      Integer.Sparse.eval keyMomentRow323 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 323).leftCharge (GramAssembly.key 323).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 414) := by
    have ha : gramCharges (GramAssembly.key 323).leftCharge (GramAssembly.key 323).rightCharge = raw39773 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39773Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39773 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 323).leftCharge (GramAssembly.key 323).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow323, Integer.Sparse.eval]

theorem keyMoment324 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 324) =
      Integer.Sparse.eval keyMomentRow324 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 324).leftCharge (GramAssembly.key 324).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 402) := by
    have ha : gramCharges (GramAssembly.key 324).leftCharge (GramAssembly.key 324).rightCharge = raw39774 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39774Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39774 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 324).leftCharge (GramAssembly.key 324).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow324, Integer.Sparse.eval]

theorem keyMoment325 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 325) =
      Integer.Sparse.eval keyMomentRow325 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 325).leftCharge (GramAssembly.key 325).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 247) := by
    have ha : gramCharges (GramAssembly.key 325).leftCharge (GramAssembly.key 325).rightCharge = raw39775 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39775Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39775 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 325).leftCharge (GramAssembly.key 325).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow325, Integer.Sparse.eval]

theorem keyMoment326 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 326) =
      Integer.Sparse.eval keyMomentRow326 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 326).leftCharge (GramAssembly.key 326).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 270) := by
    have ha : gramCharges (GramAssembly.key 326).leftCharge (GramAssembly.key 326).rightCharge = raw39776 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39776Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39776 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 326).leftCharge (GramAssembly.key 326).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow326, Integer.Sparse.eval]

theorem keyMoment327 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 327) =
      Integer.Sparse.eval keyMomentRow327 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 327).leftCharge (GramAssembly.key 327).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 412) := by
    have ha : gramCharges (GramAssembly.key 327).leftCharge (GramAssembly.key 327).rightCharge = raw39777 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39777Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39777 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 327).leftCharge (GramAssembly.key 327).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow327, Integer.Sparse.eval]

theorem keyMoment328 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 328) =
      Integer.Sparse.eval keyMomentRow328 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 328).leftCharge (GramAssembly.key 328).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 410) := by
    have ha : gramCharges (GramAssembly.key 328).leftCharge (GramAssembly.key 328).rightCharge = raw39778 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39778Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39778 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 328).leftCharge (GramAssembly.key 328).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow328, Integer.Sparse.eval]

theorem keyMoment329 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 329) =
      Integer.Sparse.eval keyMomentRow329 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 329).leftCharge (GramAssembly.key 329).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 366) := by
    have ha : gramCharges (GramAssembly.key 329).leftCharge (GramAssembly.key 329).rightCharge = raw39779 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39779Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39779 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 329).leftCharge (GramAssembly.key 329).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow329, Integer.Sparse.eval]

theorem keyMoment330 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 330) =
      Integer.Sparse.eval keyMomentRow330 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 330).leftCharge (GramAssembly.key 330).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 384) := by
    have ha : gramCharges (GramAssembly.key 330).leftCharge (GramAssembly.key 330).rightCharge = raw39780 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39780Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39780 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 330).leftCharge (GramAssembly.key 330).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow330, Integer.Sparse.eval]

theorem keyMoment331 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 331) =
      Integer.Sparse.eval keyMomentRow331 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 331).leftCharge (GramAssembly.key 331).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 409) := by
    have ha : gramCharges (GramAssembly.key 331).leftCharge (GramAssembly.key 331).rightCharge = raw39781 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39781Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39781 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 331).leftCharge (GramAssembly.key 331).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow331, Integer.Sparse.eval]

theorem keyMoment332 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 332) =
      Integer.Sparse.eval keyMomentRow332 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 332).leftCharge (GramAssembly.key 332).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 365) := by
    have ha : gramCharges (GramAssembly.key 332).leftCharge (GramAssembly.key 332).rightCharge = raw39782 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39782Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39782 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 332).leftCharge (GramAssembly.key 332).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow332, Integer.Sparse.eval]

theorem keyMoment333 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 333) =
      Integer.Sparse.eval keyMomentRow333 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 333).leftCharge (GramAssembly.key 333).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 364) := by
    have ha : gramCharges (GramAssembly.key 333).leftCharge (GramAssembly.key 333).rightCharge = raw39783 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39783Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39783 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 333).leftCharge (GramAssembly.key 333).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow333, Integer.Sparse.eval]

theorem keyMoment334 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 334) =
      Integer.Sparse.eval keyMomentRow334 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 334).leftCharge (GramAssembly.key 334).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 363) := by
    have ha : gramCharges (GramAssembly.key 334).leftCharge (GramAssembly.key 334).rightCharge = raw39784 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39784Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39784 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 334).leftCharge (GramAssembly.key 334).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow334, Integer.Sparse.eval]

theorem keyMoment335 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 335) =
      Integer.Sparse.eval keyMomentRow335 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 335).leftCharge (GramAssembly.key 335).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 268) := by
    have ha : gramCharges (GramAssembly.key 335).leftCharge (GramAssembly.key 335).rightCharge = raw39785 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39785Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39785 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 335).leftCharge (GramAssembly.key 335).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow335, Integer.Sparse.eval]

theorem keyMoment336 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 336) =
      Integer.Sparse.eval keyMomentRow336 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 336).leftCharge (GramAssembly.key 336).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 383) := by
    have ha : gramCharges (GramAssembly.key 336).leftCharge (GramAssembly.key 336).rightCharge = raw39786 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39786Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39786 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 336).leftCharge (GramAssembly.key 336).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow336, Integer.Sparse.eval]

theorem keyMoment337 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 337) =
      Integer.Sparse.eval keyMomentRow337 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 337).leftCharge (GramAssembly.key 337).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 467) := by
    have ha : gramCharges (GramAssembly.key 337).leftCharge (GramAssembly.key 337).rightCharge = raw39787 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39787Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39787 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 337).leftCharge (GramAssembly.key 337).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow337, Integer.Sparse.eval]

theorem keyMoment338 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 338) =
      Integer.Sparse.eval keyMomentRow338 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 338).leftCharge (GramAssembly.key 338).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 498) := by
    have ha : gramCharges (GramAssembly.key 338).leftCharge (GramAssembly.key 338).rightCharge = raw39788 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39788Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39788 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 338).leftCharge (GramAssembly.key 338).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow338, Integer.Sparse.eval]

theorem keyMoment339 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 339) =
      Integer.Sparse.eval keyMomentRow339 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 339).leftCharge (GramAssembly.key 339).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 365) := by
    have ha : gramCharges (GramAssembly.key 339).leftCharge (GramAssembly.key 339).rightCharge = raw39789 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39789Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39789 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 339).leftCharge (GramAssembly.key 339).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow339, Integer.Sparse.eval]

theorem keyMoment340 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 340) =
      Integer.Sparse.eval keyMomentRow340 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 340).leftCharge (GramAssembly.key 340).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 480) := by
    have ha : gramCharges (GramAssembly.key 340).leftCharge (GramAssembly.key 340).rightCharge = raw39790 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39790Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39790 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 340).leftCharge (GramAssembly.key 340).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow340, Integer.Sparse.eval]

theorem keyMoment341 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 341) =
      Integer.Sparse.eval keyMomentRow341 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 341).leftCharge (GramAssembly.key 341).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 475) := by
    have ha : gramCharges (GramAssembly.key 341).leftCharge (GramAssembly.key 341).rightCharge = raw39791 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39791Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39791 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 341).leftCharge (GramAssembly.key 341).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow341, Integer.Sparse.eval]

theorem keyMoment342 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 342) =
      Integer.Sparse.eval keyMomentRow342 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 342).leftCharge (GramAssembly.key 342).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 443) := by
    have ha : gramCharges (GramAssembly.key 342).leftCharge (GramAssembly.key 342).rightCharge = raw39792 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39792Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39792 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 342).leftCharge (GramAssembly.key 342).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow342, Integer.Sparse.eval]

theorem keyMoment343 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 343) =
      Integer.Sparse.eval keyMomentRow343 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 343).leftCharge (GramAssembly.key 343).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 497) := by
    have ha : gramCharges (GramAssembly.key 343).leftCharge (GramAssembly.key 343).rightCharge = raw39793 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39793Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39793 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 343).leftCharge (GramAssembly.key 343).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow343, Integer.Sparse.eval]

theorem keyMoment344 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 344) =
      Integer.Sparse.eval keyMomentRow344 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 344).leftCharge (GramAssembly.key 344).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 499) := by
    have ha : gramCharges (GramAssembly.key 344).leftCharge (GramAssembly.key 344).rightCharge = raw38095 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw38095Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical38095 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 344).leftCharge (GramAssembly.key 344).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow344, Integer.Sparse.eval]

theorem keyMoment345 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 345) =
      Integer.Sparse.eval keyMomentRow345 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 345).leftCharge (GramAssembly.key 345).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 410) := by
    have ha : gramCharges (GramAssembly.key 345).leftCharge (GramAssembly.key 345).rightCharge = raw39794 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39794Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39794 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 345).leftCharge (GramAssembly.key 345).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow345, Integer.Sparse.eval]

theorem keyMoment346 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 346) =
      Integer.Sparse.eval keyMomentRow346 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 346).leftCharge (GramAssembly.key 346).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 503) := by
    have ha : gramCharges (GramAssembly.key 346).leftCharge (GramAssembly.key 346).rightCharge = raw39795 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39795Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39795 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 346).leftCharge (GramAssembly.key 346).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow346, Integer.Sparse.eval]

theorem keyMoment347 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 347) =
      Integer.Sparse.eval keyMomentRow347 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 347).leftCharge (GramAssembly.key 347).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 501) := by
    have ha : gramCharges (GramAssembly.key 347).leftCharge (GramAssembly.key 347).rightCharge = raw39796 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39796Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39796 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 347).leftCharge (GramAssembly.key 347).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow347, Integer.Sparse.eval]

theorem keyMoment348 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 348) =
      Integer.Sparse.eval keyMomentRow348 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 348).leftCharge (GramAssembly.key 348).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 354) := by
    have ha : gramCharges (GramAssembly.key 348).leftCharge (GramAssembly.key 348).rightCharge = raw39797 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39797Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39797 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 348).leftCharge (GramAssembly.key 348).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow348, Integer.Sparse.eval]

theorem keyMoment349 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 349) =
      Integer.Sparse.eval keyMomentRow349 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 349).leftCharge (GramAssembly.key 349).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 491) := by
    have ha : gramCharges (GramAssembly.key 349).leftCharge (GramAssembly.key 349).rightCharge = raw39798 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39798Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39798 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 349).leftCharge (GramAssembly.key 349).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow349, Integer.Sparse.eval]

theorem keyMoment350 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 350) =
      Integer.Sparse.eval keyMomentRow350 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 350).leftCharge (GramAssembly.key 350).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 487) := by
    have ha : gramCharges (GramAssembly.key 350).leftCharge (GramAssembly.key 350).rightCharge = raw39799 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39799Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39799 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 350).leftCharge (GramAssembly.key 350).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow350, Integer.Sparse.eval]

theorem keyMoment351 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 351) =
      Integer.Sparse.eval keyMomentRow351 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 351).leftCharge (GramAssembly.key 351).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 348) := by
    have ha : gramCharges (GramAssembly.key 351).leftCharge (GramAssembly.key 351).rightCharge = raw39800 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39800Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39800 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 351).leftCharge (GramAssembly.key 351).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow351, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
