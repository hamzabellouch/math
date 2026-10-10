import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical312

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment576 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 576) =
      Integer.Sparse.eval keyMomentRow576 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 576).leftCharge (GramAssembly.key 576).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 116) := by
    have ha : gramCharges (GramAssembly.key 576).leftCharge (GramAssembly.key 576).rightCharge = raw40024 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40024Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40024 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 576).leftCharge (GramAssembly.key 576).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow576, Integer.Sparse.eval]

theorem keyMoment577 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 577) =
      Integer.Sparse.eval keyMomentRow577 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 577).leftCharge (GramAssembly.key 577).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 115) := by
    have ha : gramCharges (GramAssembly.key 577).leftCharge (GramAssembly.key 577).rightCharge = raw40025 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40025Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40025 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 577).leftCharge (GramAssembly.key 577).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow577, Integer.Sparse.eval]

theorem keyMoment578 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 578) =
      Integer.Sparse.eval keyMomentRow578 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 578).leftCharge (GramAssembly.key 578).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 13) := by
    have ha : gramCharges (GramAssembly.key 578).leftCharge (GramAssembly.key 578).rightCharge = raw40026 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40026Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40026 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 578).leftCharge (GramAssembly.key 578).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow578, Integer.Sparse.eval]

theorem keyMoment579 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 579) =
      Integer.Sparse.eval keyMomentRow579 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 579).leftCharge (GramAssembly.key 579).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 131) := by
    have ha : gramCharges (GramAssembly.key 579).leftCharge (GramAssembly.key 579).rightCharge = raw40027 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40027Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40027 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 579).leftCharge (GramAssembly.key 579).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow579, Integer.Sparse.eval]

theorem keyMoment580 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 580) =
      Integer.Sparse.eval keyMomentRow580 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 580).leftCharge (GramAssembly.key 580).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 143) := by
    have ha : gramCharges (GramAssembly.key 580).leftCharge (GramAssembly.key 580).rightCharge = raw40028 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40028Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40028 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 580).leftCharge (GramAssembly.key 580).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow580, Integer.Sparse.eval]

theorem keyMoment581 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 581) =
      Integer.Sparse.eval keyMomentRow581 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 581).leftCharge (GramAssembly.key 581).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 119) := by
    have ha : gramCharges (GramAssembly.key 581).leftCharge (GramAssembly.key 581).rightCharge = raw40029 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40029Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40029 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 581).leftCharge (GramAssembly.key 581).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow581, Integer.Sparse.eval]

theorem keyMoment582 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 582) =
      Integer.Sparse.eval keyMomentRow582 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 582).leftCharge (GramAssembly.key 582).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 127) := by
    have ha : gramCharges (GramAssembly.key 582).leftCharge (GramAssembly.key 582).rightCharge = raw40030 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40030Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40030 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 582).leftCharge (GramAssembly.key 582).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow582, Integer.Sparse.eval]

theorem keyMoment583 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 583) =
      Integer.Sparse.eval keyMomentRow583 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 583).leftCharge (GramAssembly.key 583).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 142) := by
    have ha : gramCharges (GramAssembly.key 583).leftCharge (GramAssembly.key 583).rightCharge = raw40031 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40031Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40031 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 583).leftCharge (GramAssembly.key 583).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow583, Integer.Sparse.eval]

theorem keyMoment584 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 584) =
      Integer.Sparse.eval keyMomentRow584 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 584).leftCharge (GramAssembly.key 584).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 118) := by
    have ha : gramCharges (GramAssembly.key 584).leftCharge (GramAssembly.key 584).rightCharge = raw40032 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40032Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40032 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 584).leftCharge (GramAssembly.key 584).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow584, Integer.Sparse.eval]

theorem keyMoment585 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 585) =
      Integer.Sparse.eval keyMomentRow585 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 585).leftCharge (GramAssembly.key 585).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 160) := by
    have ha : gramCharges (GramAssembly.key 585).leftCharge (GramAssembly.key 585).rightCharge = raw40033 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40033Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40033 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 585).leftCharge (GramAssembly.key 585).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow585, Integer.Sparse.eval]

theorem keyMoment586 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 586) =
      Integer.Sparse.eval keyMomentRow586 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 586).leftCharge (GramAssembly.key 586).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 133) := by
    have ha : gramCharges (GramAssembly.key 586).leftCharge (GramAssembly.key 586).rightCharge = raw40034 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40034Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40034 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 586).leftCharge (GramAssembly.key 586).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow586, Integer.Sparse.eval]

theorem keyMoment587 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 587) =
      Integer.Sparse.eval keyMomentRow587 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 587).leftCharge (GramAssembly.key 587).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 149) := by
    have ha : gramCharges (GramAssembly.key 587).leftCharge (GramAssembly.key 587).rightCharge = raw40035 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40035Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40035 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 587).leftCharge (GramAssembly.key 587).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow587, Integer.Sparse.eval]

theorem keyMoment588 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 588) =
      Integer.Sparse.eval keyMomentRow588 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 588).leftCharge (GramAssembly.key 588).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 124) := by
    have ha : gramCharges (GramAssembly.key 588).leftCharge (GramAssembly.key 588).rightCharge = raw40036 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40036Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40036 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 588).leftCharge (GramAssembly.key 588).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow588, Integer.Sparse.eval]

theorem keyMoment589 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 589) =
      Integer.Sparse.eval keyMomentRow589 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 589).leftCharge (GramAssembly.key 589).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 125) := by
    have ha : gramCharges (GramAssembly.key 589).leftCharge (GramAssembly.key 589).rightCharge = raw40037 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40037Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40037 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 589).leftCharge (GramAssembly.key 589).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow589, Integer.Sparse.eval]

theorem keyMoment590 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 590) =
      Integer.Sparse.eval keyMomentRow590 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 590).leftCharge (GramAssembly.key 590).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 126) := by
    have ha : gramCharges (GramAssembly.key 590).leftCharge (GramAssembly.key 590).rightCharge = raw40038 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40038Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40038 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 590).leftCharge (GramAssembly.key 590).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow590, Integer.Sparse.eval]

theorem keyMoment591 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 591) =
      Integer.Sparse.eval keyMomentRow591 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 591).leftCharge (GramAssembly.key 591).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 158) := by
    have ha : gramCharges (GramAssembly.key 591).leftCharge (GramAssembly.key 591).rightCharge = raw40039 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40039Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40039 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 591).leftCharge (GramAssembly.key 591).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow591, Integer.Sparse.eval]

theorem keyMoment592 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 592) =
      Integer.Sparse.eval keyMomentRow592 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 592).leftCharge (GramAssembly.key 592).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 129) := by
    have ha : gramCharges (GramAssembly.key 592).leftCharge (GramAssembly.key 592).rightCharge = raw40040 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40040Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40040 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 592).leftCharge (GramAssembly.key 592).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow592, Integer.Sparse.eval]

theorem keyMoment593 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 593) =
      Integer.Sparse.eval keyMomentRow593 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 593).leftCharge (GramAssembly.key 593).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 146) := by
    have ha : gramCharges (GramAssembly.key 593).leftCharge (GramAssembly.key 593).rightCharge = raw40041 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40041Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40041 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 593).leftCharge (GramAssembly.key 593).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow593, Integer.Sparse.eval]

theorem keyMoment594 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 594) =
      Integer.Sparse.eval keyMomentRow594 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 594).leftCharge (GramAssembly.key 594).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 121) := by
    have ha : gramCharges (GramAssembly.key 594).leftCharge (GramAssembly.key 594).rightCharge = raw40042 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40042Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40042 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 594).leftCharge (GramAssembly.key 594).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow594, Integer.Sparse.eval]

theorem keyMoment595 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 595) =
      Integer.Sparse.eval keyMomentRow595 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 595).leftCharge (GramAssembly.key 595).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 162) := by
    have ha : gramCharges (GramAssembly.key 595).leftCharge (GramAssembly.key 595).rightCharge = raw40043 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40043Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40043 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 595).leftCharge (GramAssembly.key 595).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow595, Integer.Sparse.eval]

theorem keyMoment596 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 596) =
      Integer.Sparse.eval keyMomentRow596 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 596).leftCharge (GramAssembly.key 596).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 35) := by
    have ha : gramCharges (GramAssembly.key 596).leftCharge (GramAssembly.key 596).rightCharge = raw40044 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40044Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40044 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 596).leftCharge (GramAssembly.key 596).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow596, Integer.Sparse.eval]

theorem keyMoment597 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 597) =
      Integer.Sparse.eval keyMomentRow597 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 597).leftCharge (GramAssembly.key 597).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 100) := by
    have ha : gramCharges (GramAssembly.key 597).leftCharge (GramAssembly.key 597).rightCharge = raw40045 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40045Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40045 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 597).leftCharge (GramAssembly.key 597).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow597, Integer.Sparse.eval]

theorem keyMoment598 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 598) =
      Integer.Sparse.eval keyMomentRow598 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 598).leftCharge (GramAssembly.key 598).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 70) := by
    have ha : gramCharges (GramAssembly.key 598).leftCharge (GramAssembly.key 598).rightCharge = raw40046 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40046Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40046 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 598).leftCharge (GramAssembly.key 598).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow598, Integer.Sparse.eval]

theorem keyMoment599 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 599) =
      Integer.Sparse.eval keyMomentRow599 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 599).leftCharge (GramAssembly.key 599).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 132) := by
    have ha : gramCharges (GramAssembly.key 599).leftCharge (GramAssembly.key 599).rightCharge = raw40047 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40047Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40047 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 599).leftCharge (GramAssembly.key 599).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow599, Integer.Sparse.eval]

theorem keyMoment600 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 600) =
      Integer.Sparse.eval keyMomentRow600 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 600).leftCharge (GramAssembly.key 600).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 38) := by
    have ha : gramCharges (GramAssembly.key 600).leftCharge (GramAssembly.key 600).rightCharge = raw40048 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40048Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40048 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 600).leftCharge (GramAssembly.key 600).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow600, Integer.Sparse.eval]

theorem keyMoment601 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 601) =
      Integer.Sparse.eval keyMomentRow601 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 601).leftCharge (GramAssembly.key 601).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 33) := by
    have ha : gramCharges (GramAssembly.key 601).leftCharge (GramAssembly.key 601).rightCharge = raw40049 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40049Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40049 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 601).leftCharge (GramAssembly.key 601).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow601, Integer.Sparse.eval]

theorem keyMoment602 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 602) =
      Integer.Sparse.eval keyMomentRow602 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 602).leftCharge (GramAssembly.key 602).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 40) := by
    have ha : gramCharges (GramAssembly.key 602).leftCharge (GramAssembly.key 602).rightCharge = raw40050 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40050Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40050 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 602).leftCharge (GramAssembly.key 602).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow602, Integer.Sparse.eval]

theorem keyMoment603 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 603) =
      Integer.Sparse.eval keyMomentRow603 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 603).leftCharge (GramAssembly.key 603).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 22) := by
    have ha : gramCharges (GramAssembly.key 603).leftCharge (GramAssembly.key 603).rightCharge = raw40051 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40051Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40051 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 603).leftCharge (GramAssembly.key 603).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow603, Integer.Sparse.eval]

theorem keyMoment604 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 604) =
      Integer.Sparse.eval keyMomentRow604 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 604).leftCharge (GramAssembly.key 604).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 26) := by
    have ha : gramCharges (GramAssembly.key 604).leftCharge (GramAssembly.key 604).rightCharge = raw40052 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40052Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40052 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 604).leftCharge (GramAssembly.key 604).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow604, Integer.Sparse.eval]

theorem keyMoment605 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 605) =
      Integer.Sparse.eval keyMomentRow605 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 605).leftCharge (GramAssembly.key 605).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 34) := by
    have ha : gramCharges (GramAssembly.key 605).leftCharge (GramAssembly.key 605).rightCharge = raw40053 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40053Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40053 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 605).leftCharge (GramAssembly.key 605).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow605, Integer.Sparse.eval]

theorem keyMoment606 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 606) =
      Integer.Sparse.eval keyMomentRow606 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 606).leftCharge (GramAssembly.key 606).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 42) := by
    have ha : gramCharges (GramAssembly.key 606).leftCharge (GramAssembly.key 606).rightCharge = raw40054 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40054Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40054 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 606).leftCharge (GramAssembly.key 606).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow606, Integer.Sparse.eval]

theorem keyMoment607 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 607) =
      Integer.Sparse.eval keyMomentRow607 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 607).leftCharge (GramAssembly.key 607).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 397) := by
    have ha : gramCharges (GramAssembly.key 607).leftCharge (GramAssembly.key 607).rightCharge = raw40055 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40055Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40055 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 607).leftCharge (GramAssembly.key 607).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow607, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
