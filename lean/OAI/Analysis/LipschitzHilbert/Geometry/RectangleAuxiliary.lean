import OAI.Analysis.LipschitzHilbert.Fourier.PlaneLineWeakL1
import OAI.Analysis.LipschitzHilbert.Estimates.SquareMaximalWeakL1
import OAI.Analysis.LipschitzHilbert.Geometry.RectangleCountingEnergy
import OAI.Analysis.LipschitzHilbert.Geometry.RectangleDilation

namespace OAI

/-! The auxiliary maximal operator for the Lacey--Li selection: square
averages and finitely many line directions. Every component is an actual
average majorant satisfying a uniform weak L1 bound. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert
open DyadicLineGrid

def chartLineSup (e : Plane ≃ᵐ (ℝ × ℝ)) (f : Plane → ℝ) (x : Plane) : ℝ≥0∞ :=
  horizontalSup (f ∘ e.symm) (e x)

theorem chartLineSup_measurable (e : Plane ≃ᵐ (ℝ × ℝ)) {f : Plane → ℝ}
    (hf : Measurable f) : Measurable (chartLineSup e f) :=
  (horizontalSup_measurable (hf.comp e.symm.measurable)).comp e.measurable

theorem chartLineSup_weak_L1 (e : Plane ≃ᵐ (ℝ × ℝ))
    (he : MeasurePreserving e volume (volume.prod volume)) {f : Plane → ℝ}
    (hfm : Measurable f) (hf : Integrable f volume) (t : ℝ) (ht : 0 < t) :
    volume {x | ENNReal.ofReal t < chartLineSup e f x} ≤
      3 * ENNReal.ofReal t⁻¹ * ∫⁻ x, ‖f x‖ₑ := by
  have hm := horizontalSup_measurable (hfm.comp e.symm.measurable)
  have hE : MeasurableSet {z : ℝ × ℝ | ENNReal.ofReal t < horizontalSup (f ∘ e.symm) z} :=
    measurableSet_lt measurable_const hm
  change volume (e ⁻¹' {z | ENNReal.ofReal t < horizontalSup (f ∘ e.symm) z}) ≤ _
  rw [he.measure_preimage hE.nullMeasurableSet]
  have h := horizontalSup_weak_L1 (hfm.comp e.symm.measurable)
    (he.symm.integrable_comp_of_integrable hf) t ht
  refine h.trans_eq ?_
  simp only [Function.comp_apply]
  rw [he.symm.lintegral_comp hfm.enorm,ENNReal.ofReal_mul (by norm_num)]
  norm_num

def planeSquareSup (f : Plane → ℝ) (x : Plane) : ℝ≥0∞ :=
  squareSup (fun z => ‖f (planeCoordinates z)‖ₑ) (planeCoordinates.symm x)

theorem planeSquareSup_measurable (f : Plane → ℝ) : Measurable (planeSquareSup f) :=
  (squareSup_measurable _).comp planeCoordinates.symm.measurable

theorem planeSquareSup_weak_L1 {f : Plane → ℝ} (hfm : Measurable f)
    (t : ℝ) (ht : 0 < t) :
    volume {x | ENNReal.ofReal t < planeSquareSup f x} ≤
      9 * ENNReal.ofReal t⁻¹ * ∫⁻ x, ‖f x‖ₑ := by
  have hE : MeasurableSet {z : ℝ × ℝ | ENNReal.ofReal t < squareSup
      (fun z => ‖f (planeCoordinates z)‖ₑ) z} :=
    measurableSet_lt measurable_const (squareSup_measurable _)
  change volume (planeCoordinates.symm ⁻¹' {z | ENNReal.ofReal t < squareSup
      (fun z => ‖f (planeCoordinates z)‖ₑ) z}) ≤ _
  rw [planeCoordinates_measurePreserving.symm.measure_preimage hE.nullMeasurableSet]
  have h := squareSup_weak_L1 (fun z => ‖f (planeCoordinates z)‖ₑ) (ENNReal.ofReal t)
    (ne_of_gt (ENNReal.ofReal_pos.mpr ht)) ENNReal.ofReal_ne_top
  refine h.trans_eq ?_
  rw [planeCoordinates_measurePreserving.lintegral_comp hfm.enorm,ENNReal.ofReal_inv_of_pos ht]

variable {ι : Type*} [Fintype ι]

def rectangleAuxiliary (e : ι → Plane ≃ᵐ (ℝ × ℝ)) (f : Plane → ℝ) (x : Plane) : ℝ≥0∞ :=
  planeSquareSup f x ⊔ Finset.univ.sup (fun i => chartLineSup (e i) f x)

theorem rectangleAuxiliary_measurable (e : ι → Plane ≃ᵐ (ℝ × ℝ))
    {f : Plane → ℝ} (hfm : Measurable f) : Measurable (rectangleAuxiliary e f) := by
  have h (s : Finset ι) : Measurable (fun x => s.sup (fun i => chartLineSup (e i) f x)) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih => simpa only [Finset.sup_insert] using (chartLineSup_measurable (e i) hfm).max ih
  exact (planeSquareSup_measurable f).max (h Finset.univ)

theorem rectangleAuxiliary_weak_L1 (e : ι → Plane ≃ᵐ (ℝ × ℝ))
    (he : ∀ i, MeasurePreserving (e i) volume (volume.prod volume))
    {f : Plane → ℝ} (hfm : Measurable f) (hf : Integrable f volume)
    (t : ℝ) (ht : 0 < t) :
    volume {x | ENNReal.ofReal t < rectangleAuxiliary e f x} ≤
      (9 + 3 * Fintype.card ι) * ENNReal.ofReal t⁻¹ * ∫⁻ x, ‖f x‖ₑ := by
  classical
  have hsub : {x | ENNReal.ofReal t < rectangleAuxiliary e f x} ⊆
      {x | ENNReal.ofReal t < planeSquareSup f x} ∪
      ⋃ i : ι, {x | ENNReal.ofReal t < chartLineSup (e i) f x} := by
    intro x hx
    change ENNReal.ofReal t < planeSquareSup f x ⊔ Finset.univ.sup (fun i => chartLineSup (e i) f x) at hx
    rcases lt_sup_iff.mp hx with hx | hx
    · exact Or.inl hx
    · obtain ⟨i,_,hi⟩ := Finset.lt_sup_iff.mp hx
      exact Or.inr (mem_iUnion.mpr ⟨i,hi⟩)
  calc
    _ ≤ volume ({x | ENNReal.ofReal t < planeSquareSup f x} ∪
        ⋃ i : ι, {x | ENNReal.ofReal t < chartLineSup (e i) f x}) := measure_mono hsub
    _ ≤ volume {x | ENNReal.ofReal t < planeSquareSup f x} +
        ∑ i : ι, volume {x | ENNReal.ofReal t < chartLineSup (e i) f x} :=
      (measure_union_le _ _).trans (add_le_add le_rfl (measure_iUnion_fintype_le _ _))
    _ ≤ 9 * ENNReal.ofReal t⁻¹ * (∫⁻ x, ‖f x‖ₑ) +
        ∑ _i : ι, 3 * ENNReal.ofReal t⁻¹ * ∫⁻ x, ‖f x‖ₑ :=
      add_le_add (planeSquareSup_weak_L1 hfm t ht)
        (Finset.sum_le_sum (fun i _ => chartLineSup_weak_L1 (e i) (he i) hfm hf t ht))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      ring

end LipschitzHilbert

end

end OAI
