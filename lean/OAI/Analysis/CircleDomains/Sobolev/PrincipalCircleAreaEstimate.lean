import OAI.Analysis.CircleDomains.Selection.PrincipalLeadingBounds
import OAI.Analysis.CircleDomains.Topology.InverseCircleAnalytic
import OAI.Analysis.CircleDomains.Sobolev.CurveAreaStability

namespace OAI

/-! The analytic remainder contributes vanishing signed area. All
bounds here come from its actual values and first derivatives. -/
open Set Filter Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def principalAreaErrorBudget (K B C : ℝ) : ℝ :=
    2*Real.pi*K*(3*B+C)+2*Real.pi*B*(2*B+C)

 theorem principal_area_budget_le {R K B C : ℝ} (hR : 1 ≤ R)
    (_hK : 0 ≤ K) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    (B/R^2)*(2*Real.pi*K*R)+(K*R+B/R^2)*(2*Real.pi*(2*B+C)/R^2) ≤
      principalAreaErrorBudget K B C/R := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hri : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
  have hri0 : 0 ≤ R⁻¹ := inv_nonneg.mpr hRp.le
  have hp : R⁻¹^4 ≤ R⁻¹ := by
    calc
      _ = R⁻¹*R⁻¹^3 := by ring
      _ ≤ R⁻¹*1^3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hri0 hri 3) hri0
      _ = _ := by ring
  calc
    _ = 2*Real.pi*K*(3*B+C)*R⁻¹+2*Real.pi*B*(2*B+C)*R⁻¹^4 := by
      field_simp
      ring
    _ ≤ 2*Real.pi*K*(3*B+C)*R⁻¹+2*Real.pi*B*(2*B+C)*R⁻¹ :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hp
        (show 0 ≤ 2*Real.pi*B*(2*B+C) by positivity))
    _ = _ := by unfold principalAreaErrorBudget; rw [div_eq_mul_inv]; ring

 theorem principal_circle_decomposition {F : ℂ → ℂ} {c : ℂ} {T : ℂ → ℂ}
    (hexp : ∀ z : ℂ, z ≠ 0 → F z-z = c*z⁻¹+z⁻¹^2*T z⁻¹)
    {R : ℝ} (hR : 0 < R) :
    (fun t => F (unitCircleParam 0 R t)) =
      principalLeadingCurve R c + principalCircleRemainder R T := by
  funext t
  have hn : unitCircleParam 0 R t ≠ 0 := by
    have hh : ‖unitCircleParam 0 R t‖ = R := by
      simp only [unitCircleParam, norm_circleMap_zero, abs_of_pos hR]
    intro he
    rw [he, norm_zero] at hh
    linarith
  have hh := hexp _ hn
  change F (unitCircleParam 0 R t) = unitCircleParam 0 R t+c/unitCircleParam 0 R t +
    (unitCircleParam 0 R t)⁻¹^2*T (unitCircleParam 0 R t)⁻¹
  rw [div_eq_mul_inv]
  linear_combination hh

 theorem principal_circle_area_estimate {F : ℂ → ℂ} {c : ℂ} {T : ℂ → ℂ}
    (hexp : ∀ z : ℂ, z ≠ 0 → F z-z = c*z⁻¹+z⁻¹^2*T z⁻¹)
    {R B C : ℝ} (hR : 1 ≤ R) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hT : ∀ t : ℝ, AnalyticAt ℂ T (unitCircleParam 0 R t)⁻¹)
    (hb : ∀ t : ℝ, ‖T (unitCircleParam 0 R t)⁻¹‖ ≤ B)
    (hc : ∀ t : ℝ, ‖deriv T (unitCircleParam 0 R t)⁻¹‖ ≤ C) :
    |signedCurveArea (fun t => F (unitCircleParam 0 R t)) -
      (Real.pi*R^2-Real.pi*‖c‖^2/R^2)| ≤ principalAreaErrorBudget (1+‖c‖) B C/R := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  let γ : ℝ → ℂ := fun t => F (unitCircleParam 0 R t)
  let G := principalLeadingCurve R c
  let E := principalCircleRemainder R T
  have heq : γ = G+E := principal_circle_decomposition hexp hRp
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := principalLeadingCurve_smooth hRp c
  have hE : ContDiff ℝ (⊤ : ℕ∞) E := principalCircleRemainder_smooth hRp hT
  have hγ : ContDiff ℝ (⊤ : ℕ∞) γ := by rw [heq]; exact hG.add hE
  have hval (t : ℝ) : ‖γ t-G t‖ ≤ B/R^2 := by
    rw [heq]
    simp only [Pi.add_apply, add_sub_cancel_left]
    change ‖(unitCircleParam 0 R t)⁻¹^2*T (unitCircleParam 0 R t)⁻¹‖ ≤ _
    rw [norm_mul, norm_pow, norm_inv]
    simp only [unitCircleParam, norm_circleMap_zero, abs_of_pos hRp]
    calc
      _ ≤ R⁻¹^2*B := mul_le_mul_of_nonneg_left (hb t) (sq_nonneg _)
      _ = _ := by field_simp
  have hder (t : ℝ) : ‖deriv γ t-deriv G t‖ ≤ 2*Real.pi*(2*B+C)/R^2 := by
    rw [heq, deriv_add (hG.differentiable (by simp)).differentiableAt
      (hE.differentiable (by simp)).differentiableAt, add_sub_cancel_left]
    exact principalCircleRemainder_deriv_bound hR hB hC t (hT t).differentiableAt (hb t) (hc t)
  have hs := signedCurveArea_stability (hγ.of_le (by simp)) (hG.of_le (by simp))
    (show 0 ≤ (1+‖c‖)*R by positivity)
    (show 0 ≤ 2*Real.pi*(1+‖c‖)*R by positivity)
    (show 0 ≤ B/R^2 by positivity) (show 0 ≤ 2*Real.pi*(2*B+C)/R^2 by positivity)
    (principalLeadingCurve_norm hR c) (principalLeadingCurve_deriv_norm hR c) hval hder
  dsimp only [γ, G] at hs
  rw [principal_leading_circle_area R hRp c] at hs
  exact hs.trans (principal_area_budget_le hR (by positivity) hB hC)

end CircleDomainRigidity

end

end OAI
