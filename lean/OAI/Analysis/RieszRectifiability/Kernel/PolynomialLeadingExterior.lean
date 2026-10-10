import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.PolynomialTailDecay
import OAI.Analysis.RieszRectifiability.Kernel.ExteriorDilationIntegrability
import OAI.Analysis.RieszRectifiability.Limits.IntegralZeroLimit
import OAI.Analysis.RieszRectifiability.Kernel.SchwartzPairingSeparation

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter Topology

theorem polynomial_leading_component_ae_zero_exterior {d : ℕ}
    (P : MvPolynomial (Fin d) ℂ) (hk : 2 ≤ P.totalDegree)
    (hi : IntegrableOn (fun x : Ambient d =>
      ‖MvPolynomial.eval (fun j => (x j : ℂ)) P‖ * inverseDistancePow (d + 2) 0 x)
      (closedExterior 0 1)) :
    ∀ᵐ x ∂volume.restrict (closedExterior (0 : Ambient d) 1),
      MvPolynomial.eval (fun j => (x j : ℂ))
        (MvPolynomial.homogeneousComponent P.totalDegree P) = 0 := by
  let f : Ambient d → ℂ := fun x => MvPolynomial.eval (fun j => (x j : ℂ)) P
  let H : Ambient d → ℂ := fun x => MvPolynomial.eval (fun j => (x j : ℂ))
    (MvPolynomial.homogeneousComponent P.totalDegree P)
  let G : ℕ → Ambient d → ℝ := fun j x =>
    ‖((polynomialExpansionRadius j : ℂ) ^ P.totalDegree)⁻¹ *
      f (polynomialExpansionRadius j • x)‖ * inverseDistancePow (d + 2) 0 x
  have hGi : ∀ j, Integrable (G j) (volume.restrict (closedExterior 0 1)) := by
    intro j
    apply exterior_weighted_normalized_dilation_integrable (d + 2) P.totalDegree f
      (polynomialExpansionRadius j) (polynomialExpansionRadius_pos j)
    apply hi.mono_set
    intro x hx
    change 1 ≤ dist (0 : Ambient d) x
    change polynomialExpansionRadius j ≤ dist (0 : Ambient d) x at hx
    unfold polynomialExpansionRadius at hx
    linarith [Nat.cast_nonneg (α := ℝ) j]
  have hGn : ∀ j x, 0 ≤ G j x := fun j x =>
    mul_nonneg (norm_nonneg _) (inverseDistancePow_nonneg _ _ _)
  have hHm : Measurable (fun x => ‖H x‖ * inverseDistancePow (d + 2) 0 x) :=
    (mvPolynomial_complex_eval_continuous _).norm.measurable.mul
      (inverseDistancePow_measurable _ _)
  have hlim : ∀ᵐ x ∂volume.restrict (closedExterior (0 : Ambient d) 1),
      Tendsto (fun j => G j x) atTop (𝓝 (‖H x‖ * inverseDistancePow (d + 2) 0 x)) :=
    Eventually.of_forall (fun x =>
      (polynomial_normalized_dilation_tendsto P x).norm.mul_const (inverseDistancePow (d + 2) 0 x))
  have hint := normalized_exterior_weighted_integral_tendsto_zero P.totalDegree hk f hi
  have hz := ae_zero_of_nonnegative_integral_limit
    (volume.restrict (closedExterior (0 : Ambient d) 1)) G
    (fun x => ‖H x‖ * inverseDistancePow (d + 2) 0 x) hGi hGn hHm hlim hint
  filter_upwards [hz, ae_restrict_mem (closedExterior_measurable (0 : Ambient d) 1)] with x hx hmem
  have hd : 0 < dist (0 : Ambient d) x := lt_of_lt_of_le zero_lt_one hmem
  have hp : 0 < inverseDistancePow (d + 2) 0 x := by
    unfold inverseDistancePow
    positivity
  have hnorm : ‖H x‖ = 0 := (mul_eq_zero.mp hx).resolve_right hp.ne'
  exact norm_eq_zero.mp hnorm

end

end RieszRectifiability

end OAI
