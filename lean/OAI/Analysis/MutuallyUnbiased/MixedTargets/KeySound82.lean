import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical332

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2624 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2624) =
      Integer.Sparse.eval keyMomentRow2624 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2624).leftCharge (GramAssembly.key 2624).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1714) := by
    have ha : gramCharges (GramAssembly.key 2624).leftCharge (GramAssembly.key 2624).rightCharge = raw42560 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42560Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42560 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2624).leftCharge (GramAssembly.key 2624).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4459) := by
    have ha : gramCharges (GramAssembly.key 2624).leftCharge (GramAssembly.key 2624).rightCharge = raw42561 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42561Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42561 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2624).leftCharge (GramAssembly.key 2624).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2624).leftCharge (GramAssembly.key 2624).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2624, Integer.Sparse.eval]; ring

theorem keyMoment2625 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2625) =
      Integer.Sparse.eval keyMomentRow2625 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2625).leftCharge (GramAssembly.key 2625).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2658) := by
    have ha : gramCharges (GramAssembly.key 2625).leftCharge (GramAssembly.key 2625).rightCharge = raw42562 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42562Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42562 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2625).leftCharge (GramAssembly.key 2625).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4945) := by
    have ha : gramCharges (GramAssembly.key 2625).leftCharge (GramAssembly.key 2625).rightCharge = raw42563 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42563Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42563 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2625).leftCharge (GramAssembly.key 2625).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2625).leftCharge (GramAssembly.key 2625).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2625, Integer.Sparse.eval]; ring

theorem keyMoment2626 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2626) =
      Integer.Sparse.eval keyMomentRow2626 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2626).leftCharge (GramAssembly.key 2626).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1510) := by
    have ha : gramCharges (GramAssembly.key 2626).leftCharge (GramAssembly.key 2626).rightCharge = raw42564 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42564Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42564 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2626).leftCharge (GramAssembly.key 2626).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4152) := by
    have ha : gramCharges (GramAssembly.key 2626).leftCharge (GramAssembly.key 2626).rightCharge = raw42565 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42565Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42565 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2626).leftCharge (GramAssembly.key 2626).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2626).leftCharge (GramAssembly.key 2626).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2626, Integer.Sparse.eval]; ring

theorem keyMoment2627 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2627) =
      Integer.Sparse.eval keyMomentRow2627 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2627).leftCharge (GramAssembly.key 2627).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1668) := by
    have ha : gramCharges (GramAssembly.key 2627).leftCharge (GramAssembly.key 2627).rightCharge = raw42566 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42566Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42566 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2627).leftCharge (GramAssembly.key 2627).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4345) := by
    have ha : gramCharges (GramAssembly.key 2627).leftCharge (GramAssembly.key 2627).rightCharge = raw42567 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42567Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42567 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2627).leftCharge (GramAssembly.key 2627).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2627).leftCharge (GramAssembly.key 2627).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2627, Integer.Sparse.eval]; ring

theorem keyMoment2628 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2628) =
      Integer.Sparse.eval keyMomentRow2628 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2628).leftCharge (GramAssembly.key 2628).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1713) := by
    have ha : gramCharges (GramAssembly.key 2628).leftCharge (GramAssembly.key 2628).rightCharge = raw42568 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42568Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42568 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2628).leftCharge (GramAssembly.key 2628).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4439) := by
    have ha : gramCharges (GramAssembly.key 2628).leftCharge (GramAssembly.key 2628).rightCharge = raw42569 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42569Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42569 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2628).leftCharge (GramAssembly.key 2628).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2628).leftCharge (GramAssembly.key 2628).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2628, Integer.Sparse.eval]; ring

theorem keyMoment2629 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2629) =
      Integer.Sparse.eval keyMomentRow2629 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2629).leftCharge (GramAssembly.key 2629).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3407) := by
    have ha : gramCharges (GramAssembly.key 2629).leftCharge (GramAssembly.key 2629).rightCharge = raw42570 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42570Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42570 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2629).leftCharge (GramAssembly.key 2629).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4942) := by
    have ha : gramCharges (GramAssembly.key 2629).leftCharge (GramAssembly.key 2629).rightCharge = raw42571 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42571Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42571 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2629).leftCharge (GramAssembly.key 2629).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2629).leftCharge (GramAssembly.key 2629).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2629, Integer.Sparse.eval]; ring

theorem keyMoment2630 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2630) =
      Integer.Sparse.eval keyMomentRow2630 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2630).leftCharge (GramAssembly.key 2630).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1667) := by
    have ha : gramCharges (GramAssembly.key 2630).leftCharge (GramAssembly.key 2630).rightCharge = raw42572 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42572Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42572 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2630).leftCharge (GramAssembly.key 2630).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4328) := by
    have ha : gramCharges (GramAssembly.key 2630).leftCharge (GramAssembly.key 2630).rightCharge = raw42573 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42573Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42573 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2630).leftCharge (GramAssembly.key 2630).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2630).leftCharge (GramAssembly.key 2630).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2630, Integer.Sparse.eval]; ring

theorem keyMoment2631 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2631) =
      Integer.Sparse.eval keyMomentRow2631 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2631).leftCharge (GramAssembly.key 2631).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3406) := by
    have ha : gramCharges (GramAssembly.key 2631).leftCharge (GramAssembly.key 2631).rightCharge = raw42574 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42574Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42574 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2631).leftCharge (GramAssembly.key 2631).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4931) := by
    have ha : gramCharges (GramAssembly.key 2631).leftCharge (GramAssembly.key 2631).rightCharge = raw42575 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42575Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42575 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2631).leftCharge (GramAssembly.key 2631).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2631).leftCharge (GramAssembly.key 2631).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2631, Integer.Sparse.eval]; ring

theorem keyMoment2632 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2632) =
      Integer.Sparse.eval keyMomentRow2632 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2632).leftCharge (GramAssembly.key 2632).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2217) := by
    have ha : gramCharges (GramAssembly.key 2632).leftCharge (GramAssembly.key 2632).rightCharge = raw42576 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42576Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42576 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2632).leftCharge (GramAssembly.key 2632).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4821) := by
    have ha : gramCharges (GramAssembly.key 2632).leftCharge (GramAssembly.key 2632).rightCharge = raw42577 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42577Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42577 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2632).leftCharge (GramAssembly.key 2632).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2632).leftCharge (GramAssembly.key 2632).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2632, Integer.Sparse.eval]; ring

theorem keyMoment2633 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2633) =
      Integer.Sparse.eval keyMomentRow2633 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2633).leftCharge (GramAssembly.key 2633).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2274) := by
    have ha : gramCharges (GramAssembly.key 2633).leftCharge (GramAssembly.key 2633).rightCharge = raw42578 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42578Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42578 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2633).leftCharge (GramAssembly.key 2633).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4856) := by
    have ha : gramCharges (GramAssembly.key 2633).leftCharge (GramAssembly.key 2633).rightCharge = raw42579 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42579Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42579 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2633).leftCharge (GramAssembly.key 2633).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2633).leftCharge (GramAssembly.key 2633).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2633, Integer.Sparse.eval]; ring

theorem keyMoment2634 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2634) =
      Integer.Sparse.eval keyMomentRow2634 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2634).leftCharge (GramAssembly.key 2634).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2158) := by
    have ha : gramCharges (GramAssembly.key 2634).leftCharge (GramAssembly.key 2634).rightCharge = raw42580 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42580Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42580 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2634).leftCharge (GramAssembly.key 2634).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4690) := by
    have ha : gramCharges (GramAssembly.key 2634).leftCharge (GramAssembly.key 2634).rightCharge = raw42581 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42581Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42581 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2634).leftCharge (GramAssembly.key 2634).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2634).leftCharge (GramAssembly.key 2634).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2634, Integer.Sparse.eval]; ring

theorem keyMoment2635 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2635) =
      Integer.Sparse.eval keyMomentRow2635 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2635).leftCharge (GramAssembly.key 2635).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2154) := by
    have ha : gramCharges (GramAssembly.key 2635).leftCharge (GramAssembly.key 2635).rightCharge = raw42582 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42582Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42582 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2635).leftCharge (GramAssembly.key 2635).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4668) := by
    have ha : gramCharges (GramAssembly.key 2635).leftCharge (GramAssembly.key 2635).rightCharge = raw42583 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42583Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42583 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2635).leftCharge (GramAssembly.key 2635).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2635).leftCharge (GramAssembly.key 2635).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2635, Integer.Sparse.eval]; ring

theorem keyMoment2636 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2636) =
      Integer.Sparse.eval keyMomentRow2636 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2636).leftCharge (GramAssembly.key 2636).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2178) := by
    have ha : gramCharges (GramAssembly.key 2636).leftCharge (GramAssembly.key 2636).rightCharge = raw42584 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42584Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42584 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2636).leftCharge (GramAssembly.key 2636).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4768) := by
    have ha : gramCharges (GramAssembly.key 2636).leftCharge (GramAssembly.key 2636).rightCharge = raw42585 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42585Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42585 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2636).leftCharge (GramAssembly.key 2636).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2636).leftCharge (GramAssembly.key 2636).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2636, Integer.Sparse.eval]; ring

theorem keyMoment2637 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2637) =
      Integer.Sparse.eval keyMomentRow2637 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2637).leftCharge (GramAssembly.key 2637).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2213) := by
    have ha : gramCharges (GramAssembly.key 2637).leftCharge (GramAssembly.key 2637).rightCharge = raw42586 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42586Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42586 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2637).leftCharge (GramAssembly.key 2637).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4795) := by
    have ha : gramCharges (GramAssembly.key 2637).leftCharge (GramAssembly.key 2637).rightCharge = raw42587 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42587Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42587 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2637).leftCharge (GramAssembly.key 2637).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2637).leftCharge (GramAssembly.key 2637).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2637, Integer.Sparse.eval]; ring

theorem keyMoment2638 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2638) =
      Integer.Sparse.eval keyMomentRow2638 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2638).leftCharge (GramAssembly.key 2638).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3762) := by
    have ha : gramCharges (GramAssembly.key 2638).leftCharge (GramAssembly.key 2638).rightCharge = raw42588 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42588Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42588 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2638).leftCharge (GramAssembly.key 2638).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5360) := by
    have ha : gramCharges (GramAssembly.key 2638).leftCharge (GramAssembly.key 2638).rightCharge = raw42589 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42589Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42589 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2638).leftCharge (GramAssembly.key 2638).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2638).leftCharge (GramAssembly.key 2638).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2638, Integer.Sparse.eval]; ring

theorem keyMoment2639 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2639) =
      Integer.Sparse.eval keyMomentRow2639 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2639).leftCharge (GramAssembly.key 2639).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3761) := by
    have ha : gramCharges (GramAssembly.key 2639).leftCharge (GramAssembly.key 2639).rightCharge = raw42590 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42590Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42590 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2639).leftCharge (GramAssembly.key 2639).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5353) := by
    have ha : gramCharges (GramAssembly.key 2639).leftCharge (GramAssembly.key 2639).rightCharge = raw42591 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42591Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42591 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2639).leftCharge (GramAssembly.key 2639).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2639).leftCharge (GramAssembly.key 2639).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2639, Integer.Sparse.eval]; ring

theorem keyMoment2640 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2640) =
      Integer.Sparse.eval keyMomentRow2640 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2640).leftCharge (GramAssembly.key 2640).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3760) := by
    have ha : gramCharges (GramAssembly.key 2640).leftCharge (GramAssembly.key 2640).rightCharge = raw42592 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42592Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42592 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2640).leftCharge (GramAssembly.key 2640).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5339) := by
    have ha : gramCharges (GramAssembly.key 2640).leftCharge (GramAssembly.key 2640).rightCharge = raw42593 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42593Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42593 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2640).leftCharge (GramAssembly.key 2640).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2640).leftCharge (GramAssembly.key 2640).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2640, Integer.Sparse.eval]; ring

theorem keyMoment2641 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2641) =
      Integer.Sparse.eval keyMomentRow2641 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2641).leftCharge (GramAssembly.key 2641).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3772) := by
    have ha : gramCharges (GramAssembly.key 2641).leftCharge (GramAssembly.key 2641).rightCharge = raw42594 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42594Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42594 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2641).leftCharge (GramAssembly.key 2641).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5361) := by
    have ha : gramCharges (GramAssembly.key 2641).leftCharge (GramAssembly.key 2641).rightCharge = raw42595 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42595Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42595 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2641).leftCharge (GramAssembly.key 2641).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2641).leftCharge (GramAssembly.key 2641).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2641, Integer.Sparse.eval]; ring

theorem keyMoment2642 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2642) =
      Integer.Sparse.eval keyMomentRow2642 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2642).leftCharge (GramAssembly.key 2642).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3555) := by
    have ha : gramCharges (GramAssembly.key 2642).leftCharge (GramAssembly.key 2642).rightCharge = raw42596 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42596Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42596 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2642).leftCharge (GramAssembly.key 2642).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4966) := by
    have ha : gramCharges (GramAssembly.key 2642).leftCharge (GramAssembly.key 2642).rightCharge = raw42597 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42597Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42597 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2642).leftCharge (GramAssembly.key 2642).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2642).leftCharge (GramAssembly.key 2642).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2642, Integer.Sparse.eval]; ring

theorem keyMoment2643 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2643) =
      Integer.Sparse.eval keyMomentRow2643 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2643).leftCharge (GramAssembly.key 2643).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3508) := by
    have ha : gramCharges (GramAssembly.key 2643).leftCharge (GramAssembly.key 2643).rightCharge = raw42598 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42598Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42598 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2643).leftCharge (GramAssembly.key 2643).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4955) := by
    have ha : gramCharges (GramAssembly.key 2643).leftCharge (GramAssembly.key 2643).rightCharge = raw42599 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42599Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42599 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2643).leftCharge (GramAssembly.key 2643).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2643).leftCharge (GramAssembly.key 2643).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2643, Integer.Sparse.eval]; ring

theorem keyMoment2644 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2644) =
      Integer.Sparse.eval keyMomentRow2644 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2644).leftCharge (GramAssembly.key 2644).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3755) := by
    have ha : gramCharges (GramAssembly.key 2644).leftCharge (GramAssembly.key 2644).rightCharge = raw42600 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42600Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42600 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2644).leftCharge (GramAssembly.key 2644).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5338) := by
    have ha : gramCharges (GramAssembly.key 2644).leftCharge (GramAssembly.key 2644).rightCharge = raw42601 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42601Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42601 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2644).leftCharge (GramAssembly.key 2644).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2644).leftCharge (GramAssembly.key 2644).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2644, Integer.Sparse.eval]; ring

theorem keyMoment2645 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2645) =
      Integer.Sparse.eval keyMomentRow2645 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2645).leftCharge (GramAssembly.key 2645).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3768) := by
    have ha : gramCharges (GramAssembly.key 2645).leftCharge (GramAssembly.key 2645).rightCharge = raw42602 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42602Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42602 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2645).leftCharge (GramAssembly.key 2645).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5348) := by
    have ha : gramCharges (GramAssembly.key 2645).leftCharge (GramAssembly.key 2645).rightCharge = raw42603 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42603Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42603 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2645).leftCharge (GramAssembly.key 2645).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2645).leftCharge (GramAssembly.key 2645).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2645, Integer.Sparse.eval]; ring

theorem keyMoment2646 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2646) =
      Integer.Sparse.eval keyMomentRow2646 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2646).leftCharge (GramAssembly.key 2646).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3759) := by
    have ha : gramCharges (GramAssembly.key 2646).leftCharge (GramAssembly.key 2646).rightCharge = raw42604 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42604Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42604 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2646).leftCharge (GramAssembly.key 2646).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5359) := by
    have ha : gramCharges (GramAssembly.key 2646).leftCharge (GramAssembly.key 2646).rightCharge = raw42605 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42605Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42605 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2646).leftCharge (GramAssembly.key 2646).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2646).leftCharge (GramAssembly.key 2646).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2646, Integer.Sparse.eval]; ring

theorem keyMoment2647 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2647) =
      Integer.Sparse.eval keyMomentRow2647 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2647).leftCharge (GramAssembly.key 2647).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3556) := by
    have ha : gramCharges (GramAssembly.key 2647).leftCharge (GramAssembly.key 2647).rightCharge = raw42606 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42606Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42606 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2647).leftCharge (GramAssembly.key 2647).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5112) := by
    have ha : gramCharges (GramAssembly.key 2647).leftCharge (GramAssembly.key 2647).rightCharge = raw42607 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42607Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42607 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2647).leftCharge (GramAssembly.key 2647).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2647).leftCharge (GramAssembly.key 2647).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2647, Integer.Sparse.eval]; ring

theorem keyMoment2648 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2648) =
      Integer.Sparse.eval keyMomentRow2648 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2648).leftCharge (GramAssembly.key 2648).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3480) := by
    have ha : gramCharges (GramAssembly.key 2648).leftCharge (GramAssembly.key 2648).rightCharge = raw42608 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42608Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42608 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2648).leftCharge (GramAssembly.key 2648).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5090) := by
    have ha : gramCharges (GramAssembly.key 2648).leftCharge (GramAssembly.key 2648).rightCharge = raw42609 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42609Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42609 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2648).leftCharge (GramAssembly.key 2648).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2648).leftCharge (GramAssembly.key 2648).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2648, Integer.Sparse.eval]; ring

theorem keyMoment2649 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2649) =
      Integer.Sparse.eval keyMomentRow2649 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2649).leftCharge (GramAssembly.key 2649).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3271) := by
    have ha : gramCharges (GramAssembly.key 2649).leftCharge (GramAssembly.key 2649).rightCharge = raw42610 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42610Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42610 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2649).leftCharge (GramAssembly.key 2649).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4556) := by
    have ha : gramCharges (GramAssembly.key 2649).leftCharge (GramAssembly.key 2649).rightCharge = raw42611 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42611Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42611 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2649).leftCharge (GramAssembly.key 2649).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2649).leftCharge (GramAssembly.key 2649).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2649, Integer.Sparse.eval]; ring

theorem keyMoment2650 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2650) =
      Integer.Sparse.eval keyMomentRow2650 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2650).leftCharge (GramAssembly.key 2650).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3267) := by
    have ha : gramCharges (GramAssembly.key 2650).leftCharge (GramAssembly.key 2650).rightCharge = raw42612 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42612Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42612 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2650).leftCharge (GramAssembly.key 2650).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4533) := by
    have ha : gramCharges (GramAssembly.key 2650).leftCharge (GramAssembly.key 2650).rightCharge = raw42613 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42613Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42613 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2650).leftCharge (GramAssembly.key 2650).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2650).leftCharge (GramAssembly.key 2650).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2650, Integer.Sparse.eval]; ring

theorem keyMoment2651 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2651) =
      Integer.Sparse.eval keyMomentRow2651 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2651).leftCharge (GramAssembly.key 2651).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3454) := by
    have ha : gramCharges (GramAssembly.key 2651).leftCharge (GramAssembly.key 2651).rightCharge = raw42614 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42614Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42614 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2651).leftCharge (GramAssembly.key 2651).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5040) := by
    have ha : gramCharges (GramAssembly.key 2651).leftCharge (GramAssembly.key 2651).rightCharge = raw42615 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42615Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42615 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2651).leftCharge (GramAssembly.key 2651).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2651).leftCharge (GramAssembly.key 2651).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2651, Integer.Sparse.eval]; ring

theorem keyMoment2652 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2652) =
      Integer.Sparse.eval keyMomentRow2652 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2652).leftCharge (GramAssembly.key 2652).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3476) := by
    have ha : gramCharges (GramAssembly.key 2652).leftCharge (GramAssembly.key 2652).rightCharge = raw42616 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42616Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42616 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2652).leftCharge (GramAssembly.key 2652).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5067) := by
    have ha : gramCharges (GramAssembly.key 2652).leftCharge (GramAssembly.key 2652).rightCharge = raw42617 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42617Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42617 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2652).leftCharge (GramAssembly.key 2652).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2652).leftCharge (GramAssembly.key 2652).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2652, Integer.Sparse.eval]; ring

theorem keyMoment2653 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2653) =
      Integer.Sparse.eval keyMomentRow2653 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2653).leftCharge (GramAssembly.key 2653).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3763) := by
    have ha : gramCharges (GramAssembly.key 2653).leftCharge (GramAssembly.key 2653).rightCharge = raw42618 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42618Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42618 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2653).leftCharge (GramAssembly.key 2653).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5340) := by
    have ha : gramCharges (GramAssembly.key 2653).leftCharge (GramAssembly.key 2653).rightCharge = raw42619 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42619Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42619 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2653).leftCharge (GramAssembly.key 2653).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2653).leftCharge (GramAssembly.key 2653).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2653, Integer.Sparse.eval]; ring

theorem keyMoment2654 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2654) =
      Integer.Sparse.eval keyMomentRow2654 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2654).leftCharge (GramAssembly.key 2654).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1740) := by
    have ha : gramCharges (GramAssembly.key 2654).leftCharge (GramAssembly.key 2654).rightCharge = raw42620 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42620Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42620 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2654).leftCharge (GramAssembly.key 2654).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4480) := by
    have ha : gramCharges (GramAssembly.key 2654).leftCharge (GramAssembly.key 2654).rightCharge = raw42621 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42621Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42621 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2654).leftCharge (GramAssembly.key 2654).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2654).leftCharge (GramAssembly.key 2654).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2654, Integer.Sparse.eval]; ring

theorem keyMoment2655 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2655) =
      Integer.Sparse.eval keyMomentRow2655 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2655).leftCharge (GramAssembly.key 2655).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1526) := by
    have ha : gramCharges (GramAssembly.key 2655).leftCharge (GramAssembly.key 2655).rightCharge = raw42622 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42622Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42622 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2655).leftCharge (GramAssembly.key 2655).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4188) := by
    have ha : gramCharges (GramAssembly.key 2655).leftCharge (GramAssembly.key 2655).rightCharge = raw42623 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42623Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42623 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2655).leftCharge (GramAssembly.key 2655).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2655).leftCharge (GramAssembly.key 2655).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2655, Integer.Sparse.eval]; ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
