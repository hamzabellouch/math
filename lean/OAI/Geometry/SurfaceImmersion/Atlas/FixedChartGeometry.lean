import OAI.Geometry.SurfaceImmersion.Atlas.NonlinearPhaseFrameMargins
import OAI.Geometry.SurfaceImmersion.Atlas.NoncriticalPhaseCover

namespace OAI

/-! Restricting a fixed phase chart preserves its derivative budgets.
Both Jacobian denominators are bounded by the original chart's first jets. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

lemma coordDet_abs_le_norm (A : Base →L[ℝ] Base) : |coordDet A| ≤ 2*‖A‖^2 := by
  have hx : ‖A dx‖ ≤ ‖A‖ := by simpa [dx] using A.le_opNorm dx
  have hy : ‖A dy‖ ≤ ‖A‖ := by simpa [dy] using A.le_opNorm dy
  have ha := (norm_fst_le (A dx)).trans hx
  have hb := (norm_snd_le (A dx)).trans hx
  have hc := (norm_fst_le (A dy)).trans hy
  have hd := (norm_snd_le (A dy)).trans hy
  simp only [Real.norm_eq_abs] at ha hb hc hd
  calc
    |coordDet A| ≤ |(A dx).1*(A dy).2|+|(A dx).2*(A dy).1| := abs_sub _ _
    _ ≤ ‖A‖*‖A‖+‖A‖*‖A‖ := by rw [abs_mul,abs_mul]; gcongr
    _ = 2*‖A‖^2 := by ring

lemma chart_jacobian_bounds (e : OpenPartialHomeomorph Base Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm) {J : ℝ}
    (_hJ : 0 ≤ J)
    (hf : ∀ x ∈ e.source, ‖fderiv ℝ e x‖ ≤ J)
    (hb : ∀ x ∈ e.target, ‖fderiv ℝ e.symm x‖ ≤ J) :
    ∀ x ∈ e.source, |coordDet (fderiv ℝ e x)| ≤ 2*J^2 ∧
      ‖(coordDet (fderiv ℝ e x))⁻¹‖ ≤ 2*J^2 := by
  intro x hx
  constructor
  · exact (coordDet_abs_le_norm _).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hf x hx) 2)
        (by norm_num))
  · have hh := inverse_chart_det_inv e.symm hi he hx
    change (coordDet (fderiv ℝ e x))⁻¹ = coordDet (fderiv ℝ e.symm (e x)) at hh
    rw [hh,Real.norm_eq_abs]
    exact (coordDet_abs_le_norm _).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
        (hb (e x) (e.map_source hx)) 2) (by norm_num))

lemma restrict_chart_forward_jets (e : OpenPartialHomeomorph Base Base)
    (U : Set Base) (hU : IsOpen U) (J : ℕ → ℝ)
    (hb : ∀ m j, j ≤ m → ∀ x ∈ e.source,
      ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ J m) :
    ∀ m j, j ≤ m → ∀ x ∈ (e.restrOpen U hU).source,
      ‖iteratedFDerivWithin ℝ j (e.restrOpen U hU)
        (e.restrOpen U hU).source x‖ ≤ J m := by
  intro m j hj x hx
  have hh := hb m j hj x hx.1
  rw [iteratedFDerivWithin_of_isOpen j e.open_source hx.1] at hh
  simpa only [OpenPartialHomeomorph.coe_restrOpen,
    iteratedFDerivWithin_of_isOpen j (e.restrOpen U hU).open_source hx] using hh

lemma restrict_chart_inverse_jets (e : OpenPartialHomeomorph Base Base)
    (U : Set Base) (hU : IsOpen U) (J : ℕ → ℝ)
    (hb : ∀ m j, j ≤ m → ∀ x ∈ e.target,
      ‖iteratedFDerivWithin ℝ j e.symm e.target x‖ ≤ J m) :
    ∀ m j, j ≤ m → ∀ x ∈ (e.restrOpen U hU).target,
      ‖iteratedFDerivWithin ℝ j (e.restrOpen U hU).symm
        (e.restrOpen U hU).target x‖ ≤ J m := by
  intro m j hj x hx
  have hh := hb m j hj x hx.1
  rw [iteratedFDerivWithin_of_isOpen j e.open_target hx.1] at hh
  simpa only [OpenPartialHomeomorph.coe_restrOpen_symm,
    iteratedFDerivWithin_of_isOpen j (e.restrOpen U hU).open_target hx] using hh

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
