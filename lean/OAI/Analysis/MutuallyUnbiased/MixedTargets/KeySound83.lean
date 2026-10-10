import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical333

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2656 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2656) =
      Integer.Sparse.eval keyMomentRow2656 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2656).leftCharge (GramAssembly.key 2656).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1522) := by
    have ha : gramCharges (GramAssembly.key 2656).leftCharge (GramAssembly.key 2656).rightCharge = raw42624 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42624Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42624 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2656).leftCharge (GramAssembly.key 2656).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4158) := by
    have ha : gramCharges (GramAssembly.key 2656).leftCharge (GramAssembly.key 2656).rightCharge = raw42625 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42625Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42625 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2656).leftCharge (GramAssembly.key 2656).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2656).leftCharge (GramAssembly.key 2656).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2656, Integer.Sparse.eval]
  ring

theorem keyMoment2657 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2657) =
      Integer.Sparse.eval keyMomentRow2657 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2657).leftCharge (GramAssembly.key 2657).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1682) := by
    have ha : gramCharges (GramAssembly.key 2657).leftCharge (GramAssembly.key 2657).rightCharge = raw42626 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42626Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42626 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2657).leftCharge (GramAssembly.key 2657).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4357) := by
    have ha : gramCharges (GramAssembly.key 2657).leftCharge (GramAssembly.key 2657).rightCharge = raw42627 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42627Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42627 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2657).leftCharge (GramAssembly.key 2657).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2657).leftCharge (GramAssembly.key 2657).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2657, Integer.Sparse.eval]
  ring

theorem keyMoment2658 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2658) =
      Integer.Sparse.eval keyMomentRow2658 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2658).leftCharge (GramAssembly.key 2658).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1736) := by
    have ha : gramCharges (GramAssembly.key 2658).leftCharge (GramAssembly.key 2658).rightCharge = raw42628 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42628Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42628 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2658).leftCharge (GramAssembly.key 2658).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4444) := by
    have ha : gramCharges (GramAssembly.key 2658).leftCharge (GramAssembly.key 2658).rightCharge = raw42629 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42629Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42629 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2658).leftCharge (GramAssembly.key 2658).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2658).leftCharge (GramAssembly.key 2658).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2658, Integer.Sparse.eval]
  ring

theorem keyMoment2659 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2659) =
      Integer.Sparse.eval keyMomentRow2659 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2659).leftCharge (GramAssembly.key 2659).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3418) := by
    have ha : gramCharges (GramAssembly.key 2659).leftCharge (GramAssembly.key 2659).rightCharge = raw42630 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42630Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42630 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2659).leftCharge (GramAssembly.key 2659).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4951) := by
    have ha : gramCharges (GramAssembly.key 2659).leftCharge (GramAssembly.key 2659).rightCharge = raw42631 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42631Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42631 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2659).leftCharge (GramAssembly.key 2659).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2659).leftCharge (GramAssembly.key 2659).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2659, Integer.Sparse.eval]
  ring

theorem keyMoment2660 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2660) =
      Integer.Sparse.eval keyMomentRow2660 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2660).leftCharge (GramAssembly.key 2660).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1678) := by
    have ha : gramCharges (GramAssembly.key 2660).leftCharge (GramAssembly.key 2660).rightCharge = raw42632 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42632Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42632 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2660).leftCharge (GramAssembly.key 2660).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4332) := by
    have ha : gramCharges (GramAssembly.key 2660).leftCharge (GramAssembly.key 2660).rightCharge = raw42633 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42633Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42633 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2660).leftCharge (GramAssembly.key 2660).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2660).leftCharge (GramAssembly.key 2660).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2660, Integer.Sparse.eval]
  ring

theorem keyMoment2661 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2661) =
      Integer.Sparse.eval keyMomentRow2661 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2661).leftCharge (GramAssembly.key 2661).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3414) := by
    have ha : gramCharges (GramAssembly.key 2661).leftCharge (GramAssembly.key 2661).rightCharge = raw42634 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42634Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42634 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2661).leftCharge (GramAssembly.key 2661).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4933) := by
    have ha : gramCharges (GramAssembly.key 2661).leftCharge (GramAssembly.key 2661).rightCharge = raw42635 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42635Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42635 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2661).leftCharge (GramAssembly.key 2661).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2661).leftCharge (GramAssembly.key 2661).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2661, Integer.Sparse.eval]
  ring

theorem keyMoment2662 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2662) =
      Integer.Sparse.eval keyMomentRow2662 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2662).leftCharge (GramAssembly.key 2662).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2155) := by
    have ha : gramCharges (GramAssembly.key 2662).leftCharge (GramAssembly.key 2662).rightCharge = raw42636 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42636Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42636 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2662).leftCharge (GramAssembly.key 2662).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4669) := by
    have ha : gramCharges (GramAssembly.key 2662).leftCharge (GramAssembly.key 2662).rightCharge = raw42637 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42637Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42637 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2662).leftCharge (GramAssembly.key 2662).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2662).leftCharge (GramAssembly.key 2662).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2662, Integer.Sparse.eval]
  ring

theorem keyMoment2663 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2663) =
      Integer.Sparse.eval keyMomentRow2663 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2663).leftCharge (GramAssembly.key 2663).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2176) := by
    have ha : gramCharges (GramAssembly.key 2663).leftCharge (GramAssembly.key 2663).rightCharge = raw42638 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42638Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42638 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2663).leftCharge (GramAssembly.key 2663).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4756) := by
    have ha : gramCharges (GramAssembly.key 2663).leftCharge (GramAssembly.key 2663).rightCharge = raw42639 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42639Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42639 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2663).leftCharge (GramAssembly.key 2663).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2663).leftCharge (GramAssembly.key 2663).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2663, Integer.Sparse.eval]
  ring

theorem keyMoment2664 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2664) =
      Integer.Sparse.eval keyMomentRow2664 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2664).leftCharge (GramAssembly.key 2664).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3509) := by
    have ha : gramCharges (GramAssembly.key 2664).leftCharge (GramAssembly.key 2664).rightCharge = raw42640 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42640Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42640 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2664).leftCharge (GramAssembly.key 2664).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4957) := by
    have ha : gramCharges (GramAssembly.key 2664).leftCharge (GramAssembly.key 2664).rightCharge = raw42641 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42641Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42641 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2664).leftCharge (GramAssembly.key 2664).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2664).leftCharge (GramAssembly.key 2664).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2664, Integer.Sparse.eval]
  ring

theorem keyMoment2665 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2665) =
      Integer.Sparse.eval keyMomentRow2665 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2665).leftCharge (GramAssembly.key 2665).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3512) := by
    have ha : gramCharges (GramAssembly.key 2665).leftCharge (GramAssembly.key 2665).rightCharge = raw42642 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42642Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42642 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2665).leftCharge (GramAssembly.key 2665).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4959) := by
    have ha : gramCharges (GramAssembly.key 2665).leftCharge (GramAssembly.key 2665).rightCharge = raw42643 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42643Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42643 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2665).leftCharge (GramAssembly.key 2665).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2665).leftCharge (GramAssembly.key 2665).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2665, Integer.Sparse.eval]
  ring

theorem keyMoment2666 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2666) =
      Integer.Sparse.eval keyMomentRow2666 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2666).leftCharge (GramAssembly.key 2666).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3508) := by
    have ha : gramCharges (GramAssembly.key 2666).leftCharge (GramAssembly.key 2666).rightCharge = raw42644 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42644Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42644 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2666).leftCharge (GramAssembly.key 2666).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4955) := by
    have ha : gramCharges (GramAssembly.key 2666).leftCharge (GramAssembly.key 2666).rightCharge = raw42645 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42645Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42645 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2666).leftCharge (GramAssembly.key 2666).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2666).leftCharge (GramAssembly.key 2666).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2666, Integer.Sparse.eval]
  ring

theorem keyMoment2667 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2667) =
      Integer.Sparse.eval keyMomentRow2667 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2667).leftCharge (GramAssembly.key 2667).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3510) := by
    have ha : gramCharges (GramAssembly.key 2667).leftCharge (GramAssembly.key 2667).rightCharge = raw42646 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42646Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42646 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2667).leftCharge (GramAssembly.key 2667).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4956) := by
    have ha : gramCharges (GramAssembly.key 2667).leftCharge (GramAssembly.key 2667).rightCharge = raw42647 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42647Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42647 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2667).leftCharge (GramAssembly.key 2667).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2667).leftCharge (GramAssembly.key 2667).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2667, Integer.Sparse.eval]
  ring

theorem keyMoment2668 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2668) =
      Integer.Sparse.eval keyMomentRow2668 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2668).leftCharge (GramAssembly.key 2668).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3268) := by
    have ha : gramCharges (GramAssembly.key 2668).leftCharge (GramAssembly.key 2668).rightCharge = raw42648 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42648Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42648 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2668).leftCharge (GramAssembly.key 2668).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4534) := by
    have ha : gramCharges (GramAssembly.key 2668).leftCharge (GramAssembly.key 2668).rightCharge = raw42649 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42649Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42649 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2668).leftCharge (GramAssembly.key 2668).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2668).leftCharge (GramAssembly.key 2668).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2668, Integer.Sparse.eval]
  ring

theorem keyMoment2669 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2669) =
      Integer.Sparse.eval keyMomentRow2669 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2669).leftCharge (GramAssembly.key 2669).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3452) := by
    have ha : gramCharges (GramAssembly.key 2669).leftCharge (GramAssembly.key 2669).rightCharge = raw42650 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42650Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42650 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2669).leftCharge (GramAssembly.key 2669).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4954) := by
    have ha : gramCharges (GramAssembly.key 2669).leftCharge (GramAssembly.key 2669).rightCharge = raw42651 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42651Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42651 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2669).leftCharge (GramAssembly.key 2669).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2669).leftCharge (GramAssembly.key 2669).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2669, Integer.Sparse.eval]
  ring

theorem keyMoment2670 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2670) =
      Integer.Sparse.eval keyMomentRow2670 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2670).leftCharge (GramAssembly.key 2670).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3511) := by
    have ha : gramCharges (GramAssembly.key 2670).leftCharge (GramAssembly.key 2670).rightCharge = raw42652 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42652Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42652 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2670).leftCharge (GramAssembly.key 2670).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4958) := by
    have ha : gramCharges (GramAssembly.key 2670).leftCharge (GramAssembly.key 2670).rightCharge = raw42653 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42653Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42653 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2670).leftCharge (GramAssembly.key 2670).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2670).leftCharge (GramAssembly.key 2670).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2670, Integer.Sparse.eval]
  ring

theorem keyMoment2671 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2671) =
      Integer.Sparse.eval keyMomentRow2671 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2671).leftCharge (GramAssembly.key 2671).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1523) := by
    have ha : gramCharges (GramAssembly.key 2671).leftCharge (GramAssembly.key 2671).rightCharge = raw42654 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42654Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42654 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2671).leftCharge (GramAssembly.key 2671).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4160) := by
    have ha : gramCharges (GramAssembly.key 2671).leftCharge (GramAssembly.key 2671).rightCharge = raw42655 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42655Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42655 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2671).leftCharge (GramAssembly.key 2671).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2671).leftCharge (GramAssembly.key 2671).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2671, Integer.Sparse.eval]
  ring

theorem keyMoment2672 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2672) =
      Integer.Sparse.eval keyMomentRow2672 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2672).leftCharge (GramAssembly.key 2672).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1679) := by
    have ha : gramCharges (GramAssembly.key 2672).leftCharge (GramAssembly.key 2672).rightCharge = raw42656 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42656Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42656 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2672).leftCharge (GramAssembly.key 2672).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4334) := by
    have ha : gramCharges (GramAssembly.key 2672).leftCharge (GramAssembly.key 2672).rightCharge = raw42657 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42657Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42657 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2672).leftCharge (GramAssembly.key 2672).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2672).leftCharge (GramAssembly.key 2672).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2672, Integer.Sparse.eval]
  ring

theorem keyMoment2673 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2673) =
      Integer.Sparse.eval keyMomentRow2673 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2673).leftCharge (GramAssembly.key 2673).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3415) := by
    have ha : gramCharges (GramAssembly.key 2673).leftCharge (GramAssembly.key 2673).rightCharge = raw42658 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42658Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42658 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2673).leftCharge (GramAssembly.key 2673).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4934) := by
    have ha : gramCharges (GramAssembly.key 2673).leftCharge (GramAssembly.key 2673).rightCharge = raw42659 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42659Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42659 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2673).leftCharge (GramAssembly.key 2673).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2673).leftCharge (GramAssembly.key 2673).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2673, Integer.Sparse.eval]
  ring

theorem keyMoment2674 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2674) =
      Integer.Sparse.eval keyMomentRow2674 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2674).leftCharge (GramAssembly.key 2674).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2744) := by
    have ha : gramCharges (GramAssembly.key 2674).leftCharge (GramAssembly.key 2674).rightCharge = raw42660 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42660Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42660 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2674).leftCharge (GramAssembly.key 2674).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5276) := by
    have ha : gramCharges (GramAssembly.key 2674).leftCharge (GramAssembly.key 2674).rightCharge = raw42661 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42661Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42661 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2674).leftCharge (GramAssembly.key 2674).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2674).leftCharge (GramAssembly.key 2674).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2674, Integer.Sparse.eval]
  ring

theorem keyMoment2675 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2675) =
      Integer.Sparse.eval keyMomentRow2675 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2675).leftCharge (GramAssembly.key 2675).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2781) := by
    have ha : gramCharges (GramAssembly.key 2675).leftCharge (GramAssembly.key 2675).rightCharge = raw42662 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42662Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42662 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2675).leftCharge (GramAssembly.key 2675).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5295) := by
    have ha : gramCharges (GramAssembly.key 2675).leftCharge (GramAssembly.key 2675).rightCharge = raw42663 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42663Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42663 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2675).leftCharge (GramAssembly.key 2675).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2675).leftCharge (GramAssembly.key 2675).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2675, Integer.Sparse.eval]
  ring

theorem keyMoment2676 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2676) =
      Integer.Sparse.eval keyMomentRow2676 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2676).leftCharge (GramAssembly.key 2676).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2687) := by
    have ha : gramCharges (GramAssembly.key 2676).leftCharge (GramAssembly.key 2676).rightCharge = raw42664 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42664Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42664 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2676).leftCharge (GramAssembly.key 2676).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5206) := by
    have ha : gramCharges (GramAssembly.key 2676).leftCharge (GramAssembly.key 2676).rightCharge = raw42665 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42665Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42665 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2676).leftCharge (GramAssembly.key 2676).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2676).leftCharge (GramAssembly.key 2676).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2676, Integer.Sparse.eval]
  ring

theorem keyMoment2677 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2677) =
      Integer.Sparse.eval keyMomentRow2677 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2677).leftCharge (GramAssembly.key 2677).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2681) := by
    have ha : gramCharges (GramAssembly.key 2677).leftCharge (GramAssembly.key 2677).rightCharge = raw42666 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42666Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42666 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2677).leftCharge (GramAssembly.key 2677).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5151) := by
    have ha : gramCharges (GramAssembly.key 2677).leftCharge (GramAssembly.key 2677).rightCharge = raw42667 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42667Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42667 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2677).leftCharge (GramAssembly.key 2677).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2677).leftCharge (GramAssembly.key 2677).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2677, Integer.Sparse.eval]
  ring

theorem keyMoment2678 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2678) =
      Integer.Sparse.eval keyMomentRow2678 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2678).leftCharge (GramAssembly.key 2678).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2706) := by
    have ha : gramCharges (GramAssembly.key 2678).leftCharge (GramAssembly.key 2678).rightCharge = raw42668 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42668Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42668 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2678).leftCharge (GramAssembly.key 2678).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5205) := by
    have ha : gramCharges (GramAssembly.key 2678).leftCharge (GramAssembly.key 2678).rightCharge = raw42669 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42669Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42669 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2678).leftCharge (GramAssembly.key 2678).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2678).leftCharge (GramAssembly.key 2678).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2678, Integer.Sparse.eval]
  ring

theorem keyMoment2679 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2679) =
      Integer.Sparse.eval keyMomentRow2679 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2679).leftCharge (GramAssembly.key 2679).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2738) := by
    have ha : gramCharges (GramAssembly.key 2679).leftCharge (GramAssembly.key 2679).rightCharge = raw42670 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42670Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42670 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2679).leftCharge (GramAssembly.key 2679).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5270) := by
    have ha : gramCharges (GramAssembly.key 2679).leftCharge (GramAssembly.key 2679).rightCharge = raw42671 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42671Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42671 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2679).leftCharge (GramAssembly.key 2679).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2679).leftCharge (GramAssembly.key 2679).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2679, Integer.Sparse.eval]
  ring

theorem keyMoment2680 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2680) =
      Integer.Sparse.eval keyMomentRow2680 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2680).leftCharge (GramAssembly.key 2680).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2700) := by
    have ha : gramCharges (GramAssembly.key 2680).leftCharge (GramAssembly.key 2680).rightCharge = raw42672 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42672Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42672 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2680).leftCharge (GramAssembly.key 2680).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5150) := by
    have ha : gramCharges (GramAssembly.key 2680).leftCharge (GramAssembly.key 2680).rightCharge = raw42673 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42673Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42673 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2680).leftCharge (GramAssembly.key 2680).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2680).leftCharge (GramAssembly.key 2680).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2680, Integer.Sparse.eval]
  ring

theorem keyMoment2681 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2681) =
      Integer.Sparse.eval keyMomentRow2681 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2681).leftCharge (GramAssembly.key 2681).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3573) := by
    have ha : gramCharges (GramAssembly.key 2681).leftCharge (GramAssembly.key 2681).rightCharge = raw42674 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42674Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42674 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2681).leftCharge (GramAssembly.key 2681).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5299) := by
    have ha : gramCharges (GramAssembly.key 2681).leftCharge (GramAssembly.key 2681).rightCharge = raw42675 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42675Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42675 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2681).leftCharge (GramAssembly.key 2681).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2681).leftCharge (GramAssembly.key 2681).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2681, Integer.Sparse.eval]
  ring

theorem keyMoment2682 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2682) =
      Integer.Sparse.eval keyMomentRow2682 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2682).leftCharge (GramAssembly.key 2682).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3572) := by
    have ha : gramCharges (GramAssembly.key 2682).leftCharge (GramAssembly.key 2682).rightCharge = raw42676 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42676Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42676 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2682).leftCharge (GramAssembly.key 2682).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5289) := by
    have ha : gramCharges (GramAssembly.key 2682).leftCharge (GramAssembly.key 2682).rightCharge = raw42677 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42677Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42677 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2682).leftCharge (GramAssembly.key 2682).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2682).leftCharge (GramAssembly.key 2682).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2682, Integer.Sparse.eval]
  ring

theorem keyMoment2683 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2683) =
      Integer.Sparse.eval keyMomentRow2683 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2683).leftCharge (GramAssembly.key 2683).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3570) := by
    have ha : gramCharges (GramAssembly.key 2683).leftCharge (GramAssembly.key 2683).rightCharge = raw42678 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42678Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42678 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2683).leftCharge (GramAssembly.key 2683).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5198) := by
    have ha : gramCharges (GramAssembly.key 2683).leftCharge (GramAssembly.key 2683).rightCharge = raw42679 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42679Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42679 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2683).leftCharge (GramAssembly.key 2683).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2683).leftCharge (GramAssembly.key 2683).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2683, Integer.Sparse.eval]
  ring

theorem keyMoment2684 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2684) =
      Integer.Sparse.eval keyMomentRow2684 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2684).leftCharge (GramAssembly.key 2684).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3557) := by
    have ha : gramCharges (GramAssembly.key 2684).leftCharge (GramAssembly.key 2684).rightCharge = raw42680 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42680Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42680 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2684).leftCharge (GramAssembly.key 2684).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5144) := by
    have ha : gramCharges (GramAssembly.key 2684).leftCharge (GramAssembly.key 2684).rightCharge = raw42681 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42681Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42681 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2684).leftCharge (GramAssembly.key 2684).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2684).leftCharge (GramAssembly.key 2684).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2684, Integer.Sparse.eval]
  ring

theorem keyMoment2685 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2685) =
      Integer.Sparse.eval keyMomentRow2685 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2685).leftCharge (GramAssembly.key 2685).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3569) := by
    have ha : gramCharges (GramAssembly.key 2685).leftCharge (GramAssembly.key 2685).rightCharge = raw42682 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42682Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42682 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2685).leftCharge (GramAssembly.key 2685).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5197) := by
    have ha : gramCharges (GramAssembly.key 2685).leftCharge (GramAssembly.key 2685).rightCharge = raw42683 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42683Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42683 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2685).leftCharge (GramAssembly.key 2685).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2685).leftCharge (GramAssembly.key 2685).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2685, Integer.Sparse.eval]
  ring

theorem keyMoment2686 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2686) =
      Integer.Sparse.eval keyMomentRow2686 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2686).leftCharge (GramAssembly.key 2686).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3571) := by
    have ha : gramCharges (GramAssembly.key 2686).leftCharge (GramAssembly.key 2686).rightCharge = raw42684 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42684Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42684 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2686).leftCharge (GramAssembly.key 2686).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5281) := by
    have ha : gramCharges (GramAssembly.key 2686).leftCharge (GramAssembly.key 2686).rightCharge = raw42685 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42685Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42685 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2686).leftCharge (GramAssembly.key 2686).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2686).leftCharge (GramAssembly.key 2686).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2686, Integer.Sparse.eval]
  ring

theorem keyMoment2687 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2687) =
      Integer.Sparse.eval keyMomentRow2687 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2687).leftCharge (GramAssembly.key 2687).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3584) := by
    have ha : gramCharges (GramAssembly.key 2687).leftCharge (GramAssembly.key 2687).rightCharge = raw42686 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42686Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42686 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2687).leftCharge (GramAssembly.key 2687).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5300) := by
    have ha : gramCharges (GramAssembly.key 2687).leftCharge (GramAssembly.key 2687).rightCharge = raw42687 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42687Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42687 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2687).leftCharge (GramAssembly.key 2687).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2687).leftCharge (GramAssembly.key 2687).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2687, Integer.Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
