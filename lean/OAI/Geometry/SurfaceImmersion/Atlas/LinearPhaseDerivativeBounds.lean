import OAI.Geometry.SurfaceImmersion.Correction.PolynomialPhaseFrame

namespace OAI

/-! Higher derivatives of the selected linear phase charts need no
compactness constants. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

lemma phaseEquiv_norm_le (ξ : Base) (hξ : ξ ≠ 0) :
    ‖(phaseEquiv ξ hξ).toContinuousLinearMap‖ ≤ 2*‖ξ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  change ‖phaseEquiv ξ hξ v‖ ≤ 2*‖ξ‖*‖v‖
  rw [phaseEquiv_apply, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_le_iff]
  have hξ1 : |ξ.1| ≤ ‖ξ‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le ξ
  have hξ2 : |ξ.2| ≤ ‖ξ‖ := by simpa only [Real.norm_eq_abs] using norm_snd_le ξ
  have hv1 : |v.1| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le v
  have hv2 : |v.2| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_snd_le v
  constructor
  · calc
      _ ≤ |ξ.1*v.1|+|ξ.2*v.2| := abs_add_le _ _
      _ ≤ ‖ξ‖*‖v‖+‖ξ‖*‖v‖ := by rw [abs_mul, abs_mul]; gcongr
      _ = _ := by ring
  · calc
      _ ≤ |(-ξ.2)*v.1|+|ξ.1*v.2| := abs_add_le _ _
      _ ≤ ‖ξ‖*‖v‖+‖ξ‖*‖v‖ := by rw [abs_mul, abs_neg, abs_mul]; gcongr
      _ = _ := by ring

lemma positive_order_linear_derivative_le (L : Base →L[ℝ] Base)
    {U : Set Base} (hU : IsOpen U) {j : ℕ} (hj : 1 ≤ j) {x : Base} (hx : x ∈ U) :
    ‖iteratedFDerivWithin ℝ j L U x‖ ≤ ‖L‖ := by
  rw [iteratedFDerivWithin_of_isOpen j hU hx]
  cases j with
  | zero => omega
  | succ j =>
    rw [← norm_iteratedFDeriv_fderiv]
    have he : fderiv ℝ L = fun _ => L := funext fun _ => L.fderiv
    rw [he]
    cases j with
    | zero => rw [norm_iteratedFDeriv_zero]
    | succ j =>
      rw [iteratedFDeriv_succ_const]
      simpa only [Pi.zero_apply, norm_zero] using norm_nonneg L

lemma linearPhaseChart_derivative_bound {ξ : Base} (hξ : ξ ≠ 0)
    {U : Set Base} (hU : IsOpen U) {j : ℕ} (hj : 1 ≤ j) {x : Base} (hx : x ∈ U) :
    ‖iteratedFDerivWithin ℝ j (linearPhaseChart ξ hξ U hU) U x‖ ≤ 2*‖ξ‖ :=
  (positive_order_linear_derivative_le (phaseEquiv ξ hξ).toContinuousLinearMap hU hj hx).trans
    (phaseEquiv_norm_le ξ hξ)

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
