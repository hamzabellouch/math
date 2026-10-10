import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical333

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2688 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2688) =
      Integer.Sparse.eval keyMomentRow2688 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2688).leftCharge (GramAssembly.key 2688).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3579) := by
    have ha : gramCharges (GramAssembly.key 2688).leftCharge (GramAssembly.key 2688).rightCharge = raw42688 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42688Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42688 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2688).leftCharge (GramAssembly.key 2688).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5201) := by
    have ha : gramCharges (GramAssembly.key 2688).leftCharge (GramAssembly.key 2688).rightCharge = raw42689 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42689Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42689 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2688).leftCharge (GramAssembly.key 2688).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2688).leftCharge (GramAssembly.key 2688).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2688, Integer.Sparse.eval]
  ring

theorem keyMoment2689 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2689) =
      Integer.Sparse.eval keyMomentRow2689 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2689).leftCharge (GramAssembly.key 2689).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3530) := by
    have ha : gramCharges (GramAssembly.key 2689).leftCharge (GramAssembly.key 2689).rightCharge = raw42690 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42690Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42690 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2689).leftCharge (GramAssembly.key 2689).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5147) := by
    have ha : gramCharges (GramAssembly.key 2689).leftCharge (GramAssembly.key 2689).rightCharge = raw42691 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42691Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42691 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2689).leftCharge (GramAssembly.key 2689).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2689).leftCharge (GramAssembly.key 2689).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2689, Integer.Sparse.eval]
  ring

theorem keyMoment2690 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2690) =
      Integer.Sparse.eval keyMomentRow2690 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2690).leftCharge (GramAssembly.key 2690).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3578) := by
    have ha : gramCharges (GramAssembly.key 2690).leftCharge (GramAssembly.key 2690).rightCharge = raw42692 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42692Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42692 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2690).leftCharge (GramAssembly.key 2690).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5199) := by
    have ha : gramCharges (GramAssembly.key 2690).leftCharge (GramAssembly.key 2690).rightCharge = raw42693 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42693Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42693 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2690).leftCharge (GramAssembly.key 2690).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2690).leftCharge (GramAssembly.key 2690).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2690, Integer.Sparse.eval]
  ring

theorem keyMoment2691 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2691) =
      Integer.Sparse.eval keyMomentRow2691 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2691).leftCharge (GramAssembly.key 2691).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3580) := by
    have ha : gramCharges (GramAssembly.key 2691).leftCharge (GramAssembly.key 2691).rightCharge = raw42694 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42694Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42694 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2691).leftCharge (GramAssembly.key 2691).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5282) := by
    have ha : gramCharges (GramAssembly.key 2691).leftCharge (GramAssembly.key 2691).rightCharge = raw42695 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42695Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42695 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2691).leftCharge (GramAssembly.key 2691).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2691).leftCharge (GramAssembly.key 2691).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2691, Integer.Sparse.eval]
  ring

theorem keyMoment2692 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2692) =
      Integer.Sparse.eval keyMomentRow2692 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2692).leftCharge (GramAssembly.key 2692).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3562) := by
    have ha : gramCharges (GramAssembly.key 2692).leftCharge (GramAssembly.key 2692).rightCharge = raw42696 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42696Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42696 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2692).leftCharge (GramAssembly.key 2692).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5145) := by
    have ha : gramCharges (GramAssembly.key 2692).leftCharge (GramAssembly.key 2692).rightCharge = raw42697 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42697Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42697 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2692).leftCharge (GramAssembly.key 2692).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2692).leftCharge (GramAssembly.key 2692).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2692, Integer.Sparse.eval]
  ring

theorem keyMoment2693 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2693) =
      Integer.Sparse.eval keyMomentRow2693 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2693).leftCharge (GramAssembly.key 2693).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3541) := by
    have ha : gramCharges (GramAssembly.key 2693).leftCharge (GramAssembly.key 2693).rightCharge = raw42698 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42698Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42698 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2693).leftCharge (GramAssembly.key 2693).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5267) := by
    have ha : gramCharges (GramAssembly.key 2693).leftCharge (GramAssembly.key 2693).rightCharge = raw42699 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42699Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42699 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2693).leftCharge (GramAssembly.key 2693).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2693).leftCharge (GramAssembly.key 2693).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2693, Integer.Sparse.eval]
  ring

theorem keyMoment2694 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2694) =
      Integer.Sparse.eval keyMomentRow2694 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2694).leftCharge (GramAssembly.key 2694).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3540) := by
    have ha : gramCharges (GramAssembly.key 2694).leftCharge (GramAssembly.key 2694).rightCharge = raw42700 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42700Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42700 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2694).leftCharge (GramAssembly.key 2694).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5260) := by
    have ha : gramCharges (GramAssembly.key 2694).leftCharge (GramAssembly.key 2694).rightCharge = raw42701 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42701Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42701 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2694).leftCharge (GramAssembly.key 2694).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2694).leftCharge (GramAssembly.key 2694).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2694, Integer.Sparse.eval]
  ring

theorem keyMoment2695 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2695) =
      Integer.Sparse.eval keyMomentRow2695 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2695).leftCharge (GramAssembly.key 2695).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3538) := by
    have ha : gramCharges (GramAssembly.key 2695).leftCharge (GramAssembly.key 2695).rightCharge = raw42702 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42702Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42702 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2695).leftCharge (GramAssembly.key 2695).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5188) := by
    have ha : gramCharges (GramAssembly.key 2695).leftCharge (GramAssembly.key 2695).rightCharge = raw42703 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42703Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42703 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2695).leftCharge (GramAssembly.key 2695).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2695).leftCharge (GramAssembly.key 2695).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2695, Integer.Sparse.eval]
  ring

theorem keyMoment2696 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2696) =
      Integer.Sparse.eval keyMomentRow2696 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2696).leftCharge (GramAssembly.key 2696).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3516) := by
    have ha : gramCharges (GramAssembly.key 2696).leftCharge (GramAssembly.key 2696).rightCharge = raw42704 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42704Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42704 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2696).leftCharge (GramAssembly.key 2696).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5129) := by
    have ha : gramCharges (GramAssembly.key 2696).leftCharge (GramAssembly.key 2696).rightCharge = raw42705 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42705Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42705 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2696).leftCharge (GramAssembly.key 2696).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2696).leftCharge (GramAssembly.key 2696).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2696, Integer.Sparse.eval]
  ring

theorem keyMoment2697 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2697) =
      Integer.Sparse.eval keyMomentRow2697 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2697).leftCharge (GramAssembly.key 2697).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3537) := by
    have ha : gramCharges (GramAssembly.key 2697).leftCharge (GramAssembly.key 2697).rightCharge = raw42706 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42706Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42706 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2697).leftCharge (GramAssembly.key 2697).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5187) := by
    have ha : gramCharges (GramAssembly.key 2697).leftCharge (GramAssembly.key 2697).rightCharge = raw42707 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42707Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42707 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2697).leftCharge (GramAssembly.key 2697).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2697).leftCharge (GramAssembly.key 2697).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2697, Integer.Sparse.eval]
  ring

theorem keyMoment2698 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2698) =
      Integer.Sparse.eval keyMomentRow2698 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2698).leftCharge (GramAssembly.key 2698).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3539) := by
    have ha : gramCharges (GramAssembly.key 2698).leftCharge (GramAssembly.key 2698).rightCharge = raw42708 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42708Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42708 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2698).leftCharge (GramAssembly.key 2698).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5251) := by
    have ha : gramCharges (GramAssembly.key 2698).leftCharge (GramAssembly.key 2698).rightCharge = raw42709 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42709Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42709 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2698).leftCharge (GramAssembly.key 2698).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2698).leftCharge (GramAssembly.key 2698).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2698, Integer.Sparse.eval]
  ring

theorem keyMoment2699 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2699) =
      Integer.Sparse.eval keyMomentRow2699 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2699).leftCharge (GramAssembly.key 2699).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3526) := by
    have ha : gramCharges (GramAssembly.key 2699).leftCharge (GramAssembly.key 2699).rightCharge = raw42710 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42710Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42710 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2699).leftCharge (GramAssembly.key 2699).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5265) := by
    have ha : gramCharges (GramAssembly.key 2699).leftCharge (GramAssembly.key 2699).rightCharge = raw42711 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42711Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42711 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2699).leftCharge (GramAssembly.key 2699).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2699).leftCharge (GramAssembly.key 2699).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2699, Integer.Sparse.eval]
  ring

theorem keyMoment2700 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2700) =
      Integer.Sparse.eval keyMomentRow2700 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2700).leftCharge (GramAssembly.key 2700).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3524) := by
    have ha : gramCharges (GramAssembly.key 2700).leftCharge (GramAssembly.key 2700).rightCharge = raw42712 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42712Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42712 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2700).leftCharge (GramAssembly.key 2700).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5184) := by
    have ha : gramCharges (GramAssembly.key 2700).leftCharge (GramAssembly.key 2700).rightCharge = raw42713 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42713Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42713 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2700).leftCharge (GramAssembly.key 2700).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2700).leftCharge (GramAssembly.key 2700).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2700, Integer.Sparse.eval]
  ring

theorem keyMoment2701 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2701) =
      Integer.Sparse.eval keyMomentRow2701 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2701).leftCharge (GramAssembly.key 2701).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3535) := by
    have ha : gramCharges (GramAssembly.key 2701).leftCharge (GramAssembly.key 2701).rightCharge = raw42714 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42714Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42714 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2701).leftCharge (GramAssembly.key 2701).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5266) := by
    have ha : gramCharges (GramAssembly.key 2701).leftCharge (GramAssembly.key 2701).rightCharge = raw42715 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42715Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42715 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2701).leftCharge (GramAssembly.key 2701).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2701).leftCharge (GramAssembly.key 2701).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2701, Integer.Sparse.eval]
  ring

theorem keyMoment2702 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2702) =
      Integer.Sparse.eval keyMomentRow2702 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2702).leftCharge (GramAssembly.key 2702).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3530) := by
    have ha : gramCharges (GramAssembly.key 2702).leftCharge (GramAssembly.key 2702).rightCharge = raw42716 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42716Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42716 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2702).leftCharge (GramAssembly.key 2702).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5147) := by
    have ha : gramCharges (GramAssembly.key 2702).leftCharge (GramAssembly.key 2702).rightCharge = raw42717 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42717Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42717 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2702).leftCharge (GramAssembly.key 2702).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2702).leftCharge (GramAssembly.key 2702).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2702, Integer.Sparse.eval]
  ring

theorem keyMoment2703 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2703) =
      Integer.Sparse.eval keyMomentRow2703 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2703).leftCharge (GramAssembly.key 2703).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3549) := by
    have ha : gramCharges (GramAssembly.key 2703).leftCharge (GramAssembly.key 2703).rightCharge = raw42718 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42718Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42718 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2703).leftCharge (GramAssembly.key 2703).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5268) := by
    have ha : gramCharges (GramAssembly.key 2703).leftCharge (GramAssembly.key 2703).rightCharge = raw42719 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42719Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42719 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2703).leftCharge (GramAssembly.key 2703).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2703).leftCharge (GramAssembly.key 2703).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2703, Integer.Sparse.eval]
  ring

theorem keyMoment2704 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2704) =
      Integer.Sparse.eval keyMomentRow2704 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2704).leftCharge (GramAssembly.key 2704).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3302) := by
    have ha : gramCharges (GramAssembly.key 2704).leftCharge (GramAssembly.key 2704).rightCharge = raw42720 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42720Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42720 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2704).leftCharge (GramAssembly.key 2704).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4609) := by
    have ha : gramCharges (GramAssembly.key 2704).leftCharge (GramAssembly.key 2704).rightCharge = raw42721 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42721Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42721 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2704).leftCharge (GramAssembly.key 2704).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2704).leftCharge (GramAssembly.key 2704).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2704, Integer.Sparse.eval]
  ring

theorem keyMoment2705 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2705) =
      Integer.Sparse.eval keyMomentRow2705 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2705).leftCharge (GramAssembly.key 2705).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3291) := by
    have ha : gramCharges (GramAssembly.key 2705).leftCharge (GramAssembly.key 2705).rightCharge = raw42722 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42722Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42722 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2705).leftCharge (GramAssembly.key 2705).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4591) := by
    have ha : gramCharges (GramAssembly.key 2705).leftCharge (GramAssembly.key 2705).rightCharge = raw42723 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42723Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42723 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2705).leftCharge (GramAssembly.key 2705).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2705).leftCharge (GramAssembly.key 2705).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2705, Integer.Sparse.eval]
  ring

theorem keyMoment2706 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2706) =
      Integer.Sparse.eval keyMomentRow2706 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2706).leftCharge (GramAssembly.key 2706).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3523) := by
    have ha : gramCharges (GramAssembly.key 2706).leftCharge (GramAssembly.key 2706).rightCharge = raw42724 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42724Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42724 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2706).leftCharge (GramAssembly.key 2706).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5139) := by
    have ha : gramCharges (GramAssembly.key 2706).leftCharge (GramAssembly.key 2706).rightCharge = raw42725 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42725Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42725 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2706).leftCharge (GramAssembly.key 2706).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2706).leftCharge (GramAssembly.key 2706).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2706, Integer.Sparse.eval]
  ring

theorem keyMoment2707 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2707) =
      Integer.Sparse.eval keyMomentRow2707 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2707).leftCharge (GramAssembly.key 2707).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3543) := by
    have ha : gramCharges (GramAssembly.key 2707).leftCharge (GramAssembly.key 2707).rightCharge = raw42726 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42726Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42726 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2707).leftCharge (GramAssembly.key 2707).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5252) := by
    have ha : gramCharges (GramAssembly.key 2707).leftCharge (GramAssembly.key 2707).rightCharge = raw42727 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42727Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42727 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2707).leftCharge (GramAssembly.key 2707).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2707).leftCharge (GramAssembly.key 2707).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2707, Integer.Sparse.eval]
  ring

theorem keyMoment2708 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2708) =
      Integer.Sparse.eval keyMomentRow2708 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2708).leftCharge (GramAssembly.key 2708).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3542) := by
    have ha : gramCharges (GramAssembly.key 2708).leftCharge (GramAssembly.key 2708).rightCharge = raw42728 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42728Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42728 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2708).leftCharge (GramAssembly.key 2708).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5189) := by
    have ha : gramCharges (GramAssembly.key 2708).leftCharge (GramAssembly.key 2708).rightCharge = raw42729 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42729Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42729 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2708).leftCharge (GramAssembly.key 2708).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2708).leftCharge (GramAssembly.key 2708).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2708, Integer.Sparse.eval]
  ring

theorem keyMoment2709 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2709) =
      Integer.Sparse.eval keyMomentRow2709 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2709).leftCharge (GramAssembly.key 2709).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3519) := by
    have ha : gramCharges (GramAssembly.key 2709).leftCharge (GramAssembly.key 2709).rightCharge = raw42730 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42730Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42730 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2709).leftCharge (GramAssembly.key 2709).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5128) := by
    have ha : gramCharges (GramAssembly.key 2709).leftCharge (GramAssembly.key 2709).rightCharge = raw42731 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42731Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42731 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2709).leftCharge (GramAssembly.key 2709).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2709).leftCharge (GramAssembly.key 2709).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2709, Integer.Sparse.eval]
  ring

theorem keyMoment2710 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2710) =
      Integer.Sparse.eval keyMomentRow2710 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2710).leftCharge (GramAssembly.key 2710).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2207) := by
    have ha : gramCharges (GramAssembly.key 2710).leftCharge (GramAssembly.key 2710).rightCharge = raw42732 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42732Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42732 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2710).leftCharge (GramAssembly.key 2710).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4817) := by
    have ha : gramCharges (GramAssembly.key 2710).leftCharge (GramAssembly.key 2710).rightCharge = raw42733 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42733Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42733 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2710).leftCharge (GramAssembly.key 2710).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2710).leftCharge (GramAssembly.key 2710).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2710, Integer.Sparse.eval]
  ring

theorem keyMoment2711 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2711) =
      Integer.Sparse.eval keyMomentRow2711 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2711).leftCharge (GramAssembly.key 2711).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2259) := by
    have ha : gramCharges (GramAssembly.key 2711).leftCharge (GramAssembly.key 2711).rightCharge = raw42734 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42734Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42734 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2711).leftCharge (GramAssembly.key 2711).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4853) := by
    have ha : gramCharges (GramAssembly.key 2711).leftCharge (GramAssembly.key 2711).rightCharge = raw42735 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42735Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42735 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2711).leftCharge (GramAssembly.key 2711).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2711).leftCharge (GramAssembly.key 2711).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2711, Integer.Sparse.eval]
  ring

theorem keyMoment2712 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2712) =
      Integer.Sparse.eval keyMomentRow2712 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2712).leftCharge (GramAssembly.key 2712).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2153) := by
    have ha : gramCharges (GramAssembly.key 2712).leftCharge (GramAssembly.key 2712).rightCharge = raw42736 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42736Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42736 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2712).leftCharge (GramAssembly.key 2712).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4682) := by
    have ha : gramCharges (GramAssembly.key 2712).leftCharge (GramAssembly.key 2712).rightCharge = raw42737 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42737Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42737 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2712).leftCharge (GramAssembly.key 2712).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2712).leftCharge (GramAssembly.key 2712).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2712, Integer.Sparse.eval]
  ring

theorem keyMoment2713 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2713) =
      Integer.Sparse.eval keyMomentRow2713 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2713).leftCharge (GramAssembly.key 2713).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2147) := by
    have ha : gramCharges (GramAssembly.key 2713).leftCharge (GramAssembly.key 2713).rightCharge = raw42738 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42738Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42738 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2713).leftCharge (GramAssembly.key 2713).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4664) := by
    have ha : gramCharges (GramAssembly.key 2713).leftCharge (GramAssembly.key 2713).rightCharge = raw42739 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42739Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42739 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2713).leftCharge (GramAssembly.key 2713).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2713).leftCharge (GramAssembly.key 2713).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2713, Integer.Sparse.eval]
  ring

theorem keyMoment2714 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2714) =
      Integer.Sparse.eval keyMomentRow2714 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2714).leftCharge (GramAssembly.key 2714).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2175) := by
    have ha : gramCharges (GramAssembly.key 2714).leftCharge (GramAssembly.key 2714).rightCharge = raw42740 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42740Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42740 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2714).leftCharge (GramAssembly.key 2714).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4761) := by
    have ha : gramCharges (GramAssembly.key 2714).leftCharge (GramAssembly.key 2714).rightCharge = raw42741 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42741Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42741 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2714).leftCharge (GramAssembly.key 2714).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2714).leftCharge (GramAssembly.key 2714).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2714, Integer.Sparse.eval]
  ring

theorem keyMoment2715 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2715) =
      Integer.Sparse.eval keyMomentRow2715 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2715).leftCharge (GramAssembly.key 2715).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2201) := by
    have ha : gramCharges (GramAssembly.key 2715).leftCharge (GramAssembly.key 2715).rightCharge = raw42742 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42742Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42742 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2715).leftCharge (GramAssembly.key 2715).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4792) := by
    have ha : gramCharges (GramAssembly.key 2715).leftCharge (GramAssembly.key 2715).rightCharge = raw42743 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42743Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42743 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2715).leftCharge (GramAssembly.key 2715).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2715).leftCharge (GramAssembly.key 2715).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2715, Integer.Sparse.eval]
  ring

theorem keyMoment2716 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2716) =
      Integer.Sparse.eval keyMomentRow2716 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2716).leftCharge (GramAssembly.key 2716).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3464) := by
    have ha : gramCharges (GramAssembly.key 2716).leftCharge (GramAssembly.key 2716).rightCharge = raw42744 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42744Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42744 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2716).leftCharge (GramAssembly.key 2716).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5086) := by
    have ha : gramCharges (GramAssembly.key 2716).leftCharge (GramAssembly.key 2716).rightCharge = raw42745 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42745Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42745 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2716).leftCharge (GramAssembly.key 2716).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2716).leftCharge (GramAssembly.key 2716).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2716, Integer.Sparse.eval]
  ring

theorem keyMoment2717 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2717) =
      Integer.Sparse.eval keyMomentRow2717 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2717).leftCharge (GramAssembly.key 2717).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3463) := by
    have ha : gramCharges (GramAssembly.key 2717).leftCharge (GramAssembly.key 2717).rightCharge = raw42746 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42746Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42746 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2717).leftCharge (GramAssembly.key 2717).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5074) := by
    have ha : gramCharges (GramAssembly.key 2717).leftCharge (GramAssembly.key 2717).rightCharge = raw42747 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42747Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42747 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2717).leftCharge (GramAssembly.key 2717).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2717).leftCharge (GramAssembly.key 2717).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2717, Integer.Sparse.eval]
  ring

theorem keyMoment2718 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2718) =
      Integer.Sparse.eval keyMomentRow2718 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2718).leftCharge (GramAssembly.key 2718).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3462) := by
    have ha : gramCharges (GramAssembly.key 2718).leftCharge (GramAssembly.key 2718).rightCharge = raw42748 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42748Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42748 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2718).leftCharge (GramAssembly.key 2718).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5042) := by
    have ha : gramCharges (GramAssembly.key 2718).leftCharge (GramAssembly.key 2718).rightCharge = raw42749 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42749Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42749 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2718).leftCharge (GramAssembly.key 2718).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2718).leftCharge (GramAssembly.key 2718).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2718, Integer.Sparse.eval]
  ring

theorem keyMoment2719 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2719) =
      Integer.Sparse.eval keyMomentRow2719 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2719).leftCharge (GramAssembly.key 2719).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3480) := by
    have ha : gramCharges (GramAssembly.key 2719).leftCharge (GramAssembly.key 2719).rightCharge = raw42750 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42750Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42750 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2719).leftCharge (GramAssembly.key 2719).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5090) := by
    have ha : gramCharges (GramAssembly.key 2719).leftCharge (GramAssembly.key 2719).rightCharge = raw42751 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42751Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42751 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2719).leftCharge (GramAssembly.key 2719).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2719).leftCharge (GramAssembly.key 2719).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2719, Integer.Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
