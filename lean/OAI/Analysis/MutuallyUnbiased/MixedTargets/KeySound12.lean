import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical311

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment384 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 384) =
      Integer.Sparse.eval keyMomentRow384 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 384).leftCharge (GramAssembly.key 384).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 356) := by
    have ha : gramCharges (GramAssembly.key 384).leftCharge (GramAssembly.key 384).rightCharge = raw39832 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39832Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39832 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 384).leftCharge (GramAssembly.key 384).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow384, Integer.Sparse.eval]

theorem keyMoment385 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 385) =
      Integer.Sparse.eval keyMomentRow385 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 385).leftCharge (GramAssembly.key 385).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 398) := by
    have ha : gramCharges (GramAssembly.key 385).leftCharge (GramAssembly.key 385).rightCharge = raw39833 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39833Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39833 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 385).leftCharge (GramAssembly.key 385).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow385, Integer.Sparse.eval]

theorem keyMoment386 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 386) =
      Integer.Sparse.eval keyMomentRow386 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 386).leftCharge (GramAssembly.key 386).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 467) := by
    have ha : gramCharges (GramAssembly.key 386).leftCharge (GramAssembly.key 386).rightCharge = raw39834 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39834Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39834 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 386).leftCharge (GramAssembly.key 386).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow386, Integer.Sparse.eval]

theorem keyMoment387 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 387) =
      Integer.Sparse.eval keyMomentRow387 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 387).leftCharge (GramAssembly.key 387).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 446) := by
    have ha : gramCharges (GramAssembly.key 387).leftCharge (GramAssembly.key 387).rightCharge = raw39835 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39835Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39835 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 387).leftCharge (GramAssembly.key 387).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow387, Integer.Sparse.eval]

theorem keyMoment388 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 388) =
      Integer.Sparse.eval keyMomentRow388 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 388).leftCharge (GramAssembly.key 388).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 288) := by
    have ha : gramCharges (GramAssembly.key 388).leftCharge (GramAssembly.key 388).rightCharge = raw39836 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39836Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39836 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 388).leftCharge (GramAssembly.key 388).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow388, Integer.Sparse.eval]

theorem keyMoment389 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 389) =
      Integer.Sparse.eval keyMomentRow389 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 389).leftCharge (GramAssembly.key 389).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 434) := by
    have ha : gramCharges (GramAssembly.key 389).leftCharge (GramAssembly.key 389).rightCharge = raw39837 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39837Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39837 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 389).leftCharge (GramAssembly.key 389).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow389, Integer.Sparse.eval]

theorem keyMoment390 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 390) =
      Integer.Sparse.eval keyMomentRow390 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 390).leftCharge (GramAssembly.key 390).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 280) := by
    have ha : gramCharges (GramAssembly.key 390).leftCharge (GramAssembly.key 390).rightCharge = raw39838 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39838Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39838 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 390).leftCharge (GramAssembly.key 390).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow390, Integer.Sparse.eval]

theorem keyMoment391 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 391) =
      Integer.Sparse.eval keyMomentRow391 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 391).leftCharge (GramAssembly.key 391).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 278) := by
    have ha : gramCharges (GramAssembly.key 391).leftCharge (GramAssembly.key 391).rightCharge = raw39839 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39839Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39839 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 391).leftCharge (GramAssembly.key 391).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow391, Integer.Sparse.eval]

theorem keyMoment392 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 392) =
      Integer.Sparse.eval keyMomentRow392 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 392).leftCharge (GramAssembly.key 392).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 313) := by
    have ha : gramCharges (GramAssembly.key 392).leftCharge (GramAssembly.key 392).rightCharge = raw39840 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39840Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39840 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 392).leftCharge (GramAssembly.key 392).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow392, Integer.Sparse.eval]

theorem keyMoment393 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 393) =
      Integer.Sparse.eval keyMomentRow393 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 393).leftCharge (GramAssembly.key 393).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 123) := by
    have ha : gramCharges (GramAssembly.key 393).leftCharge (GramAssembly.key 393).rightCharge = raw39841 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39841Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39841 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 393).leftCharge (GramAssembly.key 393).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow393, Integer.Sparse.eval]

theorem keyMoment394 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 394) =
      Integer.Sparse.eval keyMomentRow394 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 394).leftCharge (GramAssembly.key 394).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inr 6) := by
    have ha : gramCharges (GramAssembly.key 394).leftCharge (GramAssembly.key 394).rightCharge = raw39842 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39842Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39842 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 394).leftCharge (GramAssembly.key 394).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow394, Integer.Sparse.eval]

theorem keyMoment395 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 395) =
      Integer.Sparse.eval keyMomentRow395 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 395).leftCharge (GramAssembly.key 395).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 114) := by
    have ha : gramCharges (GramAssembly.key 395).leftCharge (GramAssembly.key 395).rightCharge = raw39843 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39843Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39843 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 395).leftCharge (GramAssembly.key 395).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow395, Integer.Sparse.eval]

theorem keyMoment396 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 396) =
      Integer.Sparse.eval keyMomentRow396 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 396).leftCharge (GramAssembly.key 396).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 29) := by
    have ha : gramCharges (GramAssembly.key 396).leftCharge (GramAssembly.key 396).rightCharge = raw39844 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39844Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39844 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 396).leftCharge (GramAssembly.key 396).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow396, Integer.Sparse.eval]

theorem keyMoment397 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 397) =
      Integer.Sparse.eval keyMomentRow397 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 397).leftCharge (GramAssembly.key 397).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 101) := by
    have ha : gramCharges (GramAssembly.key 397).leftCharge (GramAssembly.key 397).rightCharge = raw39845 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39845Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39845 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 397).leftCharge (GramAssembly.key 397).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow397, Integer.Sparse.eval]

theorem keyMoment398 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 398) =
      Integer.Sparse.eval keyMomentRow398 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 398).leftCharge (GramAssembly.key 398).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 142) := by
    have ha : gramCharges (GramAssembly.key 398).leftCharge (GramAssembly.key 398).rightCharge = raw39846 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39846Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39846 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 398).leftCharge (GramAssembly.key 398).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow398, Integer.Sparse.eval]

theorem keyMoment399 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 399) =
      Integer.Sparse.eval keyMomentRow399 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 399).leftCharge (GramAssembly.key 399).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 27) := by
    have ha : gramCharges (GramAssembly.key 399).leftCharge (GramAssembly.key 399).rightCharge = raw39847 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39847Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39847 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 399).leftCharge (GramAssembly.key 399).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow399, Integer.Sparse.eval]

theorem keyMoment400 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 400) =
      Integer.Sparse.eval keyMomentRow400 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 400).leftCharge (GramAssembly.key 400).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 12) := by
    have ha : gramCharges (GramAssembly.key 400).leftCharge (GramAssembly.key 400).rightCharge = raw39848 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39848Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39848 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 400).leftCharge (GramAssembly.key 400).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow400, Integer.Sparse.eval]

theorem keyMoment401 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 401) =
      Integer.Sparse.eval keyMomentRow401 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 401).leftCharge (GramAssembly.key 401).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 10) := by
    have ha : gramCharges (GramAssembly.key 401).leftCharge (GramAssembly.key 401).rightCharge = raw39849 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39849Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39849 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 401).leftCharge (GramAssembly.key 401).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow401, Integer.Sparse.eval]

theorem keyMoment402 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 402) =
      Integer.Sparse.eval keyMomentRow402 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 402).leftCharge (GramAssembly.key 402).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 229) := by
    have ha : gramCharges (GramAssembly.key 402).leftCharge (GramAssembly.key 402).rightCharge = raw39850 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39850Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39850 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 402).leftCharge (GramAssembly.key 402).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow402, Integer.Sparse.eval]

theorem keyMoment403 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 403) =
      Integer.Sparse.eval keyMomentRow403 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 403).leftCharge (GramAssembly.key 403).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 240) := by
    have ha : gramCharges (GramAssembly.key 403).leftCharge (GramAssembly.key 403).rightCharge = raw39851 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39851Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39851 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 403).leftCharge (GramAssembly.key 403).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow403, Integer.Sparse.eval]

theorem keyMoment404 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 404) =
      Integer.Sparse.eval keyMomentRow404 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 404).leftCharge (GramAssembly.key 404).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 184) := by
    have ha : gramCharges (GramAssembly.key 404).leftCharge (GramAssembly.key 404).rightCharge = raw39852 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39852Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39852 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 404).leftCharge (GramAssembly.key 404).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow404, Integer.Sparse.eval]

theorem keyMoment405 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 405) =
      Integer.Sparse.eval keyMomentRow405 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 405).leftCharge (GramAssembly.key 405).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 167) := by
    have ha : gramCharges (GramAssembly.key 405).leftCharge (GramAssembly.key 405).rightCharge = raw39853 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39853Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39853 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 405).leftCharge (GramAssembly.key 405).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow405, Integer.Sparse.eval]

theorem keyMoment406 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 406) =
      Integer.Sparse.eval keyMomentRow406 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 406).leftCharge (GramAssembly.key 406).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 434) := by
    have ha : gramCharges (GramAssembly.key 406).leftCharge (GramAssembly.key 406).rightCharge = raw39854 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39854Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39854 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 406).leftCharge (GramAssembly.key 406).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow406, Integer.Sparse.eval]

theorem keyMoment407 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 407) =
      Integer.Sparse.eval keyMomentRow407 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 407).leftCharge (GramAssembly.key 407).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 427) := by
    have ha : gramCharges (GramAssembly.key 407).leftCharge (GramAssembly.key 407).rightCharge = raw39855 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39855Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39855 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 407).leftCharge (GramAssembly.key 407).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow407, Integer.Sparse.eval]

theorem keyMoment408 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 408) =
      Integer.Sparse.eval keyMomentRow408 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 408).leftCharge (GramAssembly.key 408).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 435) := by
    have ha : gramCharges (GramAssembly.key 408).leftCharge (GramAssembly.key 408).rightCharge = raw39856 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39856Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39856 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 408).leftCharge (GramAssembly.key 408).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow408, Integer.Sparse.eval]

theorem keyMoment409 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 409) =
      Integer.Sparse.eval keyMomentRow409 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 409).leftCharge (GramAssembly.key 409).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 432) := by
    have ha : gramCharges (GramAssembly.key 409).leftCharge (GramAssembly.key 409).rightCharge = raw39857 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39857Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39857 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 409).leftCharge (GramAssembly.key 409).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow409, Integer.Sparse.eval]

theorem keyMoment410 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 410) =
      Integer.Sparse.eval keyMomentRow410 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 410).leftCharge (GramAssembly.key 410).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 282) := by
    have ha : gramCharges (GramAssembly.key 410).leftCharge (GramAssembly.key 410).rightCharge = raw39858 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39858Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39858 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 410).leftCharge (GramAssembly.key 410).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow410, Integer.Sparse.eval]

theorem keyMoment411 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 411) =
      Integer.Sparse.eval keyMomentRow411 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 411).leftCharge (GramAssembly.key 411).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 426) := by
    have ha : gramCharges (GramAssembly.key 411).leftCharge (GramAssembly.key 411).rightCharge = raw39859 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39859Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39859 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 411).leftCharge (GramAssembly.key 411).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow411, Integer.Sparse.eval]

theorem keyMoment412 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 412) =
      Integer.Sparse.eval keyMomentRow412 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 412).leftCharge (GramAssembly.key 412).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 428) := by
    have ha : gramCharges (GramAssembly.key 412).leftCharge (GramAssembly.key 412).rightCharge = raw39860 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39860Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39860 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 412).leftCharge (GramAssembly.key 412).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow412, Integer.Sparse.eval]

theorem keyMoment413 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 413) =
      Integer.Sparse.eval keyMomentRow413 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 413).leftCharge (GramAssembly.key 413).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 429) := by
    have ha : gramCharges (GramAssembly.key 413).leftCharge (GramAssembly.key 413).rightCharge = raw39861 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39861Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39861 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 413).leftCharge (GramAssembly.key 413).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow413, Integer.Sparse.eval]

theorem keyMoment414 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 414) =
      Integer.Sparse.eval keyMomentRow414 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 414).leftCharge (GramAssembly.key 414).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 309) := by
    have ha : gramCharges (GramAssembly.key 414).leftCharge (GramAssembly.key 414).rightCharge = raw39862 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39862Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39862 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 414).leftCharge (GramAssembly.key 414).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow414, Integer.Sparse.eval]

theorem keyMoment415 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 415) =
      Integer.Sparse.eval keyMomentRow415 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 415).leftCharge (GramAssembly.key 415).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 325) := by
    have ha : gramCharges (GramAssembly.key 415).leftCharge (GramAssembly.key 415).rightCharge = raw39863 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39863Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39863 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 415).leftCharge (GramAssembly.key 415).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow415, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
