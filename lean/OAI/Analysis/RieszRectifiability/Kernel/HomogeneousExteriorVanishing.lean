import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.ClosedTailBounds
import OAI.Analysis.RieszRectifiability.Kernel.PolynomialHomogeneousScaling
import OAI.Analysis.RieszRectifiability.Kernel.SchwartzPairingSeparation

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set

theorem homogeneous_polynomial_eval_zero_of_ae_exterior {d n : ℕ}
    (P : MvPolynomial (Fin d) ℂ) (hP : P.IsHomogeneous n) (hn : n ≠ 0)
    (hae : ∀ᵐ x ∂volume.restrict (closedExterior (0 : Ambient d) 1),
      MvPolynomial.eval (fun j => (x j : ℂ)) P = 0) :
    ∀ x : Ambient d, MvPolynomial.eval (fun j => (x j : ℂ)) P = 0 := by
  let U : Set (Ambient d) := {x | 1 < ‖x‖}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_norm
  have hsub : U ⊆ closedExterior 0 1 := by
    intro x hx
    change 1 ≤ dist (0 : Ambient d) x
    rw [dist_zero_left]
    exact hx.le
  have hUae : (fun x : Ambient d => MvPolynomial.eval (fun j => (x j : ℂ)) P) =ᵐ[volume.restrict U]
      (fun _ => (0 : ℂ)) := ae_restrict_of_ae_restrict_of_subset hsub hae
  have hzero := Measure.eqOn_open_of_ae_eq hUae hU
    (mvPolynomial_complex_eval_continuous P).continuousOn continuous_const.continuousOn
  intro x
  by_cases hx : x = 0
  · subst x
    have h := homogeneous_polynomial_eval_real_smul P hP (0 : ℝ) (0 : Ambient d)
    simpa only [zero_smul, Complex.ofReal_zero, zero_pow hn, zero_mul] using! h
  · have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let r : ℝ := 2 / ‖x‖
    have hr : 0 < r := div_pos (by norm_num) hnx
    have hrx : r • x ∈ U := by
      change 1 < ‖r • x‖
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      dsimp only [r]
      rw [div_mul_cancel₀ _ hnx.ne']
      norm_num
    have h := hzero hrx
    dsimp only at h
    rw [homogeneous_polynomial_eval_real_smul P hP r x] at h
    exact (mul_eq_zero.mp h).resolve_left
      (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hr.ne'))

end

end RieszRectifiability

end OAI
