import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys1
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical308

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment32 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 32) =
      Integer.Sparse.eval keyMomentRow32 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 32).leftCharge (GramAssembly.key 32).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 414) := by
    have ha : gramCharges (GramAssembly.key 32).leftCharge (GramAssembly.key 32).rightCharge = raw39482 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39482Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39482 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 32).leftCharge (GramAssembly.key 32).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow32, Integer.Sparse.eval]

theorem keyMoment33 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 33) =
      Integer.Sparse.eval keyMomentRow33 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 33).leftCharge (GramAssembly.key 33).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 400) := by
    have ha : gramCharges (GramAssembly.key 33).leftCharge (GramAssembly.key 33).rightCharge = raw39483 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39483Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39483 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 33).leftCharge (GramAssembly.key 33).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow33, Integer.Sparse.eval]

theorem keyMoment34 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 34) =
      Integer.Sparse.eval keyMomentRow34 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 34).leftCharge (GramAssembly.key 34).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 409) := by
    have ha : gramCharges (GramAssembly.key 34).leftCharge (GramAssembly.key 34).rightCharge = raw39484 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39484Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39484 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 34).leftCharge (GramAssembly.key 34).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow34, Integer.Sparse.eval]

theorem keyMoment35 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 35) =
      Integer.Sparse.eval keyMomentRow35 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 35).leftCharge (GramAssembly.key 35).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 270) := by
    have ha : gramCharges (GramAssembly.key 35).leftCharge (GramAssembly.key 35).rightCharge = raw39485 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39485Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39485 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 35).leftCharge (GramAssembly.key 35).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow35, Integer.Sparse.eval]

theorem keyMoment36 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 36) =
      Integer.Sparse.eval keyMomentRow36 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 36).leftCharge (GramAssembly.key 36).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 391) := by
    have ha : gramCharges (GramAssembly.key 36).leftCharge (GramAssembly.key 36).rightCharge = raw39486 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39486Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39486 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 36).leftCharge (GramAssembly.key 36).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow36, Integer.Sparse.eval]

theorem keyMoment37 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 37) =
      Integer.Sparse.eval keyMomentRow37 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 37).leftCharge (GramAssembly.key 37).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 412) := by
    have ha : gramCharges (GramAssembly.key 37).leftCharge (GramAssembly.key 37).rightCharge = raw39487 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39487Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39487 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 37).leftCharge (GramAssembly.key 37).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow37, Integer.Sparse.eval]

theorem keyMoment38 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 38) =
      Integer.Sparse.eval keyMomentRow38 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 38).leftCharge (GramAssembly.key 38).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 410) := by
    have ha : gramCharges (GramAssembly.key 38).leftCharge (GramAssembly.key 38).rightCharge = raw39488 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39488Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39488 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 38).leftCharge (GramAssembly.key 38).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow38, Integer.Sparse.eval]

theorem keyMoment39 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 39) =
      Integer.Sparse.eval keyMomentRow39 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 39).leftCharge (GramAssembly.key 39).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 408) := by
    have ha : gramCharges (GramAssembly.key 39).leftCharge (GramAssembly.key 39).rightCharge = raw39489 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39489Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39489 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 39).leftCharge (GramAssembly.key 39).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow39, Integer.Sparse.eval]

theorem keyMoment40 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 40) =
      Integer.Sparse.eval keyMomentRow40 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 40).leftCharge (GramAssembly.key 40).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 384) := by
    have ha : gramCharges (GramAssembly.key 40).leftCharge (GramAssembly.key 40).rightCharge = raw39490 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39490Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39490 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 40).leftCharge (GramAssembly.key 40).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow40, Integer.Sparse.eval]

theorem keyMoment41 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 41) =
      Integer.Sparse.eval keyMomentRow41 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 41).leftCharge (GramAssembly.key 41).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 381) := by
    have ha : gramCharges (GramAssembly.key 41).leftCharge (GramAssembly.key 41).rightCharge = raw39491 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39491Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39491 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 41).leftCharge (GramAssembly.key 41).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow41, Integer.Sparse.eval]

theorem keyMoment42 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 42) =
      Integer.Sparse.eval keyMomentRow42 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 42).leftCharge (GramAssembly.key 42).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 364) := by
    have ha : gramCharges (GramAssembly.key 42).leftCharge (GramAssembly.key 42).rightCharge = raw39492 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39492Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39492 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 42).leftCharge (GramAssembly.key 42).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow42, Integer.Sparse.eval]

theorem keyMoment43 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 43) =
      Integer.Sparse.eval keyMomentRow43 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 43).leftCharge (GramAssembly.key 43).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 393) := by
    have ha : gramCharges (GramAssembly.key 43).leftCharge (GramAssembly.key 43).rightCharge = raw39493 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39493Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39493 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 43).leftCharge (GramAssembly.key 43).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow43, Integer.Sparse.eval]

theorem keyMoment44 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 44) =
      Integer.Sparse.eval keyMomentRow44 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 44).leftCharge (GramAssembly.key 44).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 409) := by
    have ha : gramCharges (GramAssembly.key 44).leftCharge (GramAssembly.key 44).rightCharge = raw39494 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39494Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39494 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 44).leftCharge (GramAssembly.key 44).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow44, Integer.Sparse.eval]

theorem keyMoment45 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 45) =
      Integer.Sparse.eval keyMomentRow45 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 45).leftCharge (GramAssembly.key 45).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 380) := by
    have ha : gramCharges (GramAssembly.key 45).leftCharge (GramAssembly.key 45).rightCharge = raw39495 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39495Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39495 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 45).leftCharge (GramAssembly.key 45).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow45, Integer.Sparse.eval]

theorem keyMoment46 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 46) =
      Integer.Sparse.eval keyMomentRow46 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 46).leftCharge (GramAssembly.key 46).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 363) := by
    have ha : gramCharges (GramAssembly.key 46).leftCharge (GramAssembly.key 46).rightCharge = raw39496 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39496Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39496 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 46).leftCharge (GramAssembly.key 46).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow46, Integer.Sparse.eval]

theorem keyMoment47 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 47) =
      Integer.Sparse.eval keyMomentRow47 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 47).leftCharge (GramAssembly.key 47).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 386) := by
    have ha : gramCharges (GramAssembly.key 47).leftCharge (GramAssembly.key 47).rightCharge = raw39497 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39497Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39497 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 47).leftCharge (GramAssembly.key 47).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow47, Integer.Sparse.eval]

theorem keyMoment48 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 48) =
      Integer.Sparse.eval keyMomentRow48 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 48).leftCharge (GramAssembly.key 48).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 397) := by
    have ha : gramCharges (GramAssembly.key 48).leftCharge (GramAssembly.key 48).rightCharge = raw39498 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39498Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39498 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 48).leftCharge (GramAssembly.key 48).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow48, Integer.Sparse.eval]

theorem keyMoment49 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 49) =
      Integer.Sparse.eval keyMomentRow49 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 49).leftCharge (GramAssembly.key 49).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 393) := by
    have ha : gramCharges (GramAssembly.key 49).leftCharge (GramAssembly.key 49).rightCharge = raw39499 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39499Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39499 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 49).leftCharge (GramAssembly.key 49).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow49, Integer.Sparse.eval]

theorem keyMoment50 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 50) =
      Integer.Sparse.eval keyMomentRow50 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 50).leftCharge (GramAssembly.key 50).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 357) := by
    have ha : gramCharges (GramAssembly.key 50).leftCharge (GramAssembly.key 50).rightCharge = raw39500 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39500Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39500 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 50).leftCharge (GramAssembly.key 50).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow50, Integer.Sparse.eval]

theorem keyMoment51 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 51) =
      Integer.Sparse.eval keyMomentRow51 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 51).leftCharge (GramAssembly.key 51).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 392) := by
    have ha : gramCharges (GramAssembly.key 51).leftCharge (GramAssembly.key 51).rightCharge = raw39501 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39501Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39501 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 51).leftCharge (GramAssembly.key 51).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow51, Integer.Sparse.eval]

theorem keyMoment52 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 52) =
      Integer.Sparse.eval keyMomentRow52 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 52).leftCharge (GramAssembly.key 52).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 394) := by
    have ha : gramCharges (GramAssembly.key 52).leftCharge (GramAssembly.key 52).rightCharge = raw39502 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39502Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39502 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 52).leftCharge (GramAssembly.key 52).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow52, Integer.Sparse.eval]

theorem keyMoment53 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 53) =
      Integer.Sparse.eval keyMomentRow53 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 53).leftCharge (GramAssembly.key 53).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 406) := by
    have ha : gramCharges (GramAssembly.key 53).leftCharge (GramAssembly.key 53).rightCharge = raw39503 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39503Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39503 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 53).leftCharge (GramAssembly.key 53).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow53, Integer.Sparse.eval]

theorem keyMoment54 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 54) =
      Integer.Sparse.eval keyMomentRow54 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 54).leftCharge (GramAssembly.key 54).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 404) := by
    have ha : gramCharges (GramAssembly.key 54).leftCharge (GramAssembly.key 54).rightCharge = raw39504 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39504Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39504 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 54).leftCharge (GramAssembly.key 54).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow54, Integer.Sparse.eval]

theorem keyMoment55 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 55) =
      Integer.Sparse.eval keyMomentRow55 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 55).leftCharge (GramAssembly.key 55).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 342) := by
    have ha : gramCharges (GramAssembly.key 55).leftCharge (GramAssembly.key 55).rightCharge = raw39505 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39505Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39505 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 55).leftCharge (GramAssembly.key 55).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow55, Integer.Sparse.eval]

theorem keyMoment56 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 56) =
      Integer.Sparse.eval keyMomentRow56 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 56).leftCharge (GramAssembly.key 56).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 377) := by
    have ha : gramCharges (GramAssembly.key 56).leftCharge (GramAssembly.key 56).rightCharge = raw39506 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39506Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39506 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 56).leftCharge (GramAssembly.key 56).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow56, Integer.Sparse.eval]

theorem keyMoment57 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 57) =
      Integer.Sparse.eval keyMomentRow57 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 57).leftCharge (GramAssembly.key 57).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 324) := by
    have ha : gramCharges (GramAssembly.key 57).leftCharge (GramAssembly.key 57).rightCharge = raw39507 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39507Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39507 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 57).leftCharge (GramAssembly.key 57).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow57, Integer.Sparse.eval]

theorem keyMoment58 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 58) =
      Integer.Sparse.eval keyMomentRow58 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 58).leftCharge (GramAssembly.key 58).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 399) := by
    have ha : gramCharges (GramAssembly.key 58).leftCharge (GramAssembly.key 58).rightCharge = raw39508 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39508Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39508 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 58).leftCharge (GramAssembly.key 58).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow58, Integer.Sparse.eval]

theorem keyMoment59 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 59) =
      Integer.Sparse.eval keyMomentRow59 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 59).leftCharge (GramAssembly.key 59).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 400) := by
    have ha : gramCharges (GramAssembly.key 59).leftCharge (GramAssembly.key 59).rightCharge = raw39509 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39509Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39509 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 59).leftCharge (GramAssembly.key 59).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow59, Integer.Sparse.eval]

theorem keyMoment60 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 60) =
      Integer.Sparse.eval keyMomentRow60 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 60).leftCharge (GramAssembly.key 60).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 403) := by
    have ha : gramCharges (GramAssembly.key 60).leftCharge (GramAssembly.key 60).rightCharge = raw39510 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39510Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39510 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 60).leftCharge (GramAssembly.key 60).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow60, Integer.Sparse.eval]

theorem keyMoment61 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 61) =
      Integer.Sparse.eval keyMomentRow61 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 61).leftCharge (GramAssembly.key 61).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 376) := by
    have ha : gramCharges (GramAssembly.key 61).leftCharge (GramAssembly.key 61).rightCharge = raw39511 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39511Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39511 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 61).leftCharge (GramAssembly.key 61).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow61, Integer.Sparse.eval]

theorem keyMoment62 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 62) =
      Integer.Sparse.eval keyMomentRow62 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 62).leftCharge (GramAssembly.key 62).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 359) := by
    have ha : gramCharges (GramAssembly.key 62).leftCharge (GramAssembly.key 62).rightCharge = raw39512 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39512Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39512 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 62).leftCharge (GramAssembly.key 62).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow62, Integer.Sparse.eval]

theorem keyMoment63 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 63) =
      Integer.Sparse.eval keyMomentRow63 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 63).leftCharge (GramAssembly.key 63).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 421) := by
    have ha : gramCharges (GramAssembly.key 63).leftCharge (GramAssembly.key 63).rightCharge = raw39513 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39513Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39513 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 63).leftCharge (GramAssembly.key 63).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow63, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
