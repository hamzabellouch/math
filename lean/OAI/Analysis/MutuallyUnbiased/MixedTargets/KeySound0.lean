import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical308

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 0) =
      Integer.Sparse.eval keyMomentRow0 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 0).leftCharge (GramAssembly.key 0).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 2) := by
    have ha : gramCharges (GramAssembly.key 0).leftCharge (GramAssembly.key 0).rightCharge = raw39450 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39450Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39450 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 0).leftCharge (GramAssembly.key 0).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow0, Integer.Sparse.eval]

theorem keyMoment1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1) =
      Integer.Sparse.eval keyMomentRow1 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1).leftCharge (GramAssembly.key 1).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 1) := by
    have ha : gramCharges (GramAssembly.key 1).leftCharge (GramAssembly.key 1).rightCharge = raw39451 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39451Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39451 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1).leftCharge (GramAssembly.key 1).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow1, Integer.Sparse.eval]

theorem keyMoment2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2) =
      Integer.Sparse.eval keyMomentRow2 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2).leftCharge (GramAssembly.key 2).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 272) := by
    have ha : gramCharges (GramAssembly.key 2).leftCharge (GramAssembly.key 2).rightCharge = raw39452 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39452Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39452 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2).leftCharge (GramAssembly.key 2).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow2, Integer.Sparse.eval]

theorem keyMoment3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 3) =
      Integer.Sparse.eval keyMomentRow3 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 3).leftCharge (GramAssembly.key 3).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 270) := by
    have ha : gramCharges (GramAssembly.key 3).leftCharge (GramAssembly.key 3).rightCharge = raw39453 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39453Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39453 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 3).leftCharge (GramAssembly.key 3).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow3, Integer.Sparse.eval]

theorem keyMoment4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 4) =
      Integer.Sparse.eval keyMomentRow4 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 4).leftCharge (GramAssembly.key 4).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 266) := by
    have ha : gramCharges (GramAssembly.key 4).leftCharge (GramAssembly.key 4).rightCharge = raw39454 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39454Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39454 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 4).leftCharge (GramAssembly.key 4).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow4, Integer.Sparse.eval]

theorem keyMoment5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 5) =
      Integer.Sparse.eval keyMomentRow5 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 5).leftCharge (GramAssembly.key 5).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 267) := by
    have ha : gramCharges (GramAssembly.key 5).leftCharge (GramAssembly.key 5).rightCharge = raw39455 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39455Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39455 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 5).leftCharge (GramAssembly.key 5).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow5, Integer.Sparse.eval]

theorem keyMoment6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 6) =
      Integer.Sparse.eval keyMomentRow6 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 6).leftCharge (GramAssembly.key 6).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 268) := by
    have ha : gramCharges (GramAssembly.key 6).leftCharge (GramAssembly.key 6).rightCharge = raw39456 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39456Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39456 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 6).leftCharge (GramAssembly.key 6).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow6, Integer.Sparse.eval]

theorem keyMoment7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 7) =
      Integer.Sparse.eval keyMomentRow7 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 7).leftCharge (GramAssembly.key 7).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 269) := by
    have ha : gramCharges (GramAssembly.key 7).leftCharge (GramAssembly.key 7).rightCharge = raw39457 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39457Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39457 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 7).leftCharge (GramAssembly.key 7).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow7, Integer.Sparse.eval]

theorem keyMoment8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 8) =
      Integer.Sparse.eval keyMomentRow8 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 8).leftCharge (GramAssembly.key 8).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 267) := by
    have ha : gramCharges (GramAssembly.key 8).leftCharge (GramAssembly.key 8).rightCharge = raw39458 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39458Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39458 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 8).leftCharge (GramAssembly.key 8).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow8, Integer.Sparse.eval]

theorem keyMoment9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 9) =
      Integer.Sparse.eval keyMomentRow9 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 9).leftCharge (GramAssembly.key 9).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 0) := by
    have ha : gramCharges (GramAssembly.key 9).leftCharge (GramAssembly.key 9).rightCharge = raw39459 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39459Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39459 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 9).leftCharge (GramAssembly.key 9).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow9, Integer.Sparse.eval]

theorem keyMoment10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 10) =
      Integer.Sparse.eval keyMomentRow10 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 10).leftCharge (GramAssembly.key 10).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 261) := by
    have ha : gramCharges (GramAssembly.key 10).leftCharge (GramAssembly.key 10).rightCharge = raw39460 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39460Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39460 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 10).leftCharge (GramAssembly.key 10).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow10, Integer.Sparse.eval]

theorem keyMoment11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 11) =
      Integer.Sparse.eval keyMomentRow11 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 11).leftCharge (GramAssembly.key 11).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 265) := by
    have ha : gramCharges (GramAssembly.key 11).leftCharge (GramAssembly.key 11).rightCharge = raw39461 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39461Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39461 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 11).leftCharge (GramAssembly.key 11).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow11, Integer.Sparse.eval]

theorem keyMoment12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 12) =
      Integer.Sparse.eval keyMomentRow12 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 12).leftCharge (GramAssembly.key 12).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 261) := by
    have ha : gramCharges (GramAssembly.key 12).leftCharge (GramAssembly.key 12).rightCharge = raw39462 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39462Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39462 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 12).leftCharge (GramAssembly.key 12).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow12, Integer.Sparse.eval]

theorem keyMoment13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 13) =
      Integer.Sparse.eval keyMomentRow13 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 13).leftCharge (GramAssembly.key 13).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 259) := by
    have ha : gramCharges (GramAssembly.key 13).leftCharge (GramAssembly.key 13).rightCharge = raw39463 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39463Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39463 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 13).leftCharge (GramAssembly.key 13).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow13, Integer.Sparse.eval]

theorem keyMoment14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 14) =
      Integer.Sparse.eval keyMomentRow14 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 14).leftCharge (GramAssembly.key 14).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inr 0) := by
    have ha : gramCharges (GramAssembly.key 14).leftCharge (GramAssembly.key 14).rightCharge = raw39464 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39464Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39464 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 14).leftCharge (GramAssembly.key 14).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow14, Integer.Sparse.eval]

theorem keyMoment15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 15) =
      Integer.Sparse.eval keyMomentRow15 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 15).leftCharge (GramAssembly.key 15).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 388) := by
    have ha : gramCharges (GramAssembly.key 15).leftCharge (GramAssembly.key 15).rightCharge = raw39465 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39465Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39465 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 15).leftCharge (GramAssembly.key 15).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow15, Integer.Sparse.eval]

theorem keyMoment16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 16) =
      Integer.Sparse.eval keyMomentRow16 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 16).leftCharge (GramAssembly.key 16).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 389) := by
    have ha : gramCharges (GramAssembly.key 16).leftCharge (GramAssembly.key 16).rightCharge = raw39466 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39466Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39466 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 16).leftCharge (GramAssembly.key 16).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow16, Integer.Sparse.eval]

theorem keyMoment17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 17) =
      Integer.Sparse.eval keyMomentRow17 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 17).leftCharge (GramAssembly.key 17).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 391) := by
    have ha : gramCharges (GramAssembly.key 17).leftCharge (GramAssembly.key 17).rightCharge = raw39467 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39467Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39467 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 17).leftCharge (GramAssembly.key 17).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow17, Integer.Sparse.eval]

theorem keyMoment18 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 18) =
      Integer.Sparse.eval keyMomentRow18 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 18).leftCharge (GramAssembly.key 18).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 377) := by
    have ha : gramCharges (GramAssembly.key 18).leftCharge (GramAssembly.key 18).rightCharge = raw39468 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39468Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39468 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 18).leftCharge (GramAssembly.key 18).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow18, Integer.Sparse.eval]

theorem keyMoment19 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 19) =
      Integer.Sparse.eval keyMomentRow19 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 19).leftCharge (GramAssembly.key 19).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 384) := by
    have ha : gramCharges (GramAssembly.key 19).leftCharge (GramAssembly.key 19).rightCharge = raw39469 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39469Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39469 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 19).leftCharge (GramAssembly.key 19).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow19, Integer.Sparse.eval]

theorem keyMoment20 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 20) =
      Integer.Sparse.eval keyMomentRow20 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 20).leftCharge (GramAssembly.key 20).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 386) := by
    have ha : gramCharges (GramAssembly.key 20).leftCharge (GramAssembly.key 20).rightCharge = raw39470 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39470Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39470 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 20).leftCharge (GramAssembly.key 20).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow20, Integer.Sparse.eval]

theorem keyMoment21 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 21) =
      Integer.Sparse.eval keyMomentRow21 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 21).leftCharge (GramAssembly.key 21).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 387) := by
    have ha : gramCharges (GramAssembly.key 21).leftCharge (GramAssembly.key 21).rightCharge = raw39471 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39471Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39471 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 21).leftCharge (GramAssembly.key 21).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow21, Integer.Sparse.eval]

theorem keyMoment22 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 22) =
      Integer.Sparse.eval keyMomentRow22 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 22).leftCharge (GramAssembly.key 22).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 375) := by
    have ha : gramCharges (GramAssembly.key 22).leftCharge (GramAssembly.key 22).rightCharge = raw39472 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39472Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39472 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 22).leftCharge (GramAssembly.key 22).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow22, Integer.Sparse.eval]

theorem keyMoment23 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 23) =
      Integer.Sparse.eval keyMomentRow23 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 23).leftCharge (GramAssembly.key 23).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 382) := by
    have ha : gramCharges (GramAssembly.key 23).leftCharge (GramAssembly.key 23).rightCharge = raw39473 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39473Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39473 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 23).leftCharge (GramAssembly.key 23).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow23, Integer.Sparse.eval]

theorem keyMoment24 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 24) =
      Integer.Sparse.eval keyMomentRow24 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 24).leftCharge (GramAssembly.key 24).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 415) := by
    have ha : gramCharges (GramAssembly.key 24).leftCharge (GramAssembly.key 24).rightCharge = raw39474 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39474Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39474 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 24).leftCharge (GramAssembly.key 24).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow24, Integer.Sparse.eval]

theorem keyMoment25 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 25) =
      Integer.Sparse.eval keyMomentRow25 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 25).leftCharge (GramAssembly.key 25).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 419) := by
    have ha : gramCharges (GramAssembly.key 25).leftCharge (GramAssembly.key 25).rightCharge = raw39475 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39475Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39475 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 25).leftCharge (GramAssembly.key 25).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow25, Integer.Sparse.eval]

theorem keyMoment26 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 26) =
      Integer.Sparse.eval keyMomentRow26 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 26).leftCharge (GramAssembly.key 26).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 420) := by
    have ha : gramCharges (GramAssembly.key 26).leftCharge (GramAssembly.key 26).rightCharge = raw39476 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39476Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39476 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 26).leftCharge (GramAssembly.key 26).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow26, Integer.Sparse.eval]

theorem keyMoment27 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 27) =
      Integer.Sparse.eval keyMomentRow27 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 27).leftCharge (GramAssembly.key 27).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 421) := by
    have ha : gramCharges (GramAssembly.key 27).leftCharge (GramAssembly.key 27).rightCharge = raw39477 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39477Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39477 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 27).leftCharge (GramAssembly.key 27).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow27, Integer.Sparse.eval]

theorem keyMoment28 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 28) =
      Integer.Sparse.eval keyMomentRow28 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 28).leftCharge (GramAssembly.key 28).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 402) := by
    have ha : gramCharges (GramAssembly.key 28).leftCharge (GramAssembly.key 28).rightCharge = raw39478 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39478Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39478 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 28).leftCharge (GramAssembly.key 28).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow28, Integer.Sparse.eval]

theorem keyMoment29 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 29) =
      Integer.Sparse.eval keyMomentRow29 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 29).leftCharge (GramAssembly.key 29).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 405) := by
    have ha : gramCharges (GramAssembly.key 29).leftCharge (GramAssembly.key 29).rightCharge = raw39479 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39479Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39479 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 29).leftCharge (GramAssembly.key 29).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow29, Integer.Sparse.eval]

theorem keyMoment30 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 30) =
      Integer.Sparse.eval keyMomentRow30 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 30).leftCharge (GramAssembly.key 30).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 391) := by
    have ha : gramCharges (GramAssembly.key 30).leftCharge (GramAssembly.key 30).rightCharge = raw39480 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39480Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39480 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 30).leftCharge (GramAssembly.key 30).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow30, Integer.Sparse.eval]

theorem keyMoment31 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 31) =
      Integer.Sparse.eval keyMomentRow31 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 31).leftCharge (GramAssembly.key 31).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 406) := by
    have ha : gramCharges (GramAssembly.key 31).leftCharge (GramAssembly.key 31).rightCharge = raw39481 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39481Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39481 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 31).leftCharge (GramAssembly.key 31).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow31, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
