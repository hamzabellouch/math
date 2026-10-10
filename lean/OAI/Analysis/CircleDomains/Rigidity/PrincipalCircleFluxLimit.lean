import OAI.Analysis.CircleDomains.Rigidity.PrincipalCircleFlux
import OAI.Analysis.CircleDomains.Rigidity.CircleFluxStability
import OAI.Analysis.CircleDomains.Selection.PrincipalExteriorGerm

namespace OAI

/-! The actual analytic principal germ gives the limiting vertical
boundary flux. No boundary estimate is assumed: continuity of the
analytic remainder supplies a uniform bound on inverse circles. -/
open Set Filter Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem inverse_circle_remainder_bound {T : ℂ → ℂ} (hT : ContinuousAt T 0) :
    ∃ B R₀ : ℝ, 0 ≤ B ∧ ∀ R ≥ R₀, 0 < R ∧
      ∀ t : ℝ, ‖T (unitCircleParam 0 R t)⁻¹‖ ≤ B := by
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp hT 1 zero_lt_one
  refine ⟨‖T 0‖+1, max 1 (δ⁻¹+1), by positivity, ?_⟩
  intro R hR
  have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  refine ⟨hRp, ?_⟩
  intro t
  have hn : ‖(unitCircleParam 0 R t)⁻¹‖ < δ := by
    rw [norm_inv]
    simp only [unitCircleParam, norm_circleMap_zero, abs_of_pos hRp]
    apply (inv_lt_comm₀ hRp hδ).mpr
    have hh := (le_max_right 1 (δ⁻¹+1)).trans hR
    linarith
  have he := hd (show dist ((unitCircleParam 0 R t)⁻¹) 0 < δ by
    simpa only [dist_zero_right] using hn)
  have hl : ‖T (unitCircleParam 0 R t)⁻¹-T 0‖ < 1 := by
    simpa only [dist_eq_norm] using he
  have ht := norm_add_le (T (unitCircleParam 0 R t)⁻¹-T 0) (T 0)
  rw [sub_add_cancel] at ht
  linarith

 theorem principal_circle_flux_estimate {F : ℂ → ℂ} (hF : Continuous F)
    {c : ℂ} {T : ℂ → ℂ}
    (hexp : ∀ z : ℂ, z ≠ 0 → F z-z = c*z⁻¹+z⁻¹^2*T z⁻¹)
    {B R : ℝ} (hB : 0 ≤ B) (hR : 0 < R)
    (hT : ∀ t : ℝ, ‖T (unitCircleParam 0 R t)⁻¹‖ ≤ B) :
    |planarFormIntegral (fun z => -(F z).im) (fun _ => 0) (unitCircleParam 0 R) -
      Real.pi*R^2 + Real.pi*c.re| ≤ 2*Real.pi*B/R := by
  have hn (t : ℝ) : ‖unitCircleParam 0 R t‖ = R := by
    simp only [unitCircleParam, norm_circleMap_zero, abs_of_pos hR]
  have hne (t : ℝ) : unitCircleParam 0 R t ≠ 0 := by
    intro he
    have hh := hn t
    rw [he, norm_zero] at hh
    linarith
  have hb (t : ℝ) : ‖F (unitCircleParam 0 R t) -
      (unitCircleParam 0 R t+c/unitCircleParam 0 R t)‖ ≤ B/R^2 := by
    have he := hexp _ (hne t)
    have heq : F (unitCircleParam 0 R t) -
        (unitCircleParam 0 R t+c/unitCircleParam 0 R t) =
        (unitCircleParam 0 R t)⁻¹^2*T (unitCircleParam 0 R t)⁻¹ := by
      rw [div_eq_mul_inv]
      linear_combination he
    rw [heq, norm_mul, norm_pow, norm_inv, hn]
    calc
      _ ≤ R⁻¹^2*B := mul_le_mul_of_nonneg_left (hT t) (sq_nonneg _)
      _ = _ := by field_simp
  have hγ : Continuous (unitCircleParam 0 R) :=
    (continuous_circleMap 0 R).comp (continuous_const.mul continuous_id)
  have hfl := vertical_circle_flux_stability (G := fun z => z+c/z) hR.le (div_nonneg hB (sq_nonneg R))
    (hF.comp hγ) (hγ.add (continuous_const.div hγ hne)) hb
  rw [principal_leading_circle_flux R hR c] at hfl
  have heq : 2*Real.pi*R*(B/R^2) = 2*Real.pi*B/R := by field_simp
  rw [heq] at hfl
  convert hfl using 1
  congr 1
  ring

 theorem principal_circle_flux_limit {F : ℂ → ℂ} (hF : Continuous F)
    {c : ℂ} {T : ℂ → ℂ} (hT : ContinuousAt T 0)
    (hexp : ∀ z : ℂ, z ≠ 0 → F z-z = c*z⁻¹+z⁻¹^2*T z⁻¹) :
    Tendsto (fun R : ℝ =>
      planarFormIntegral (fun z => -(F z).im) (fun _ => 0) (unitCircleParam 0 R) -
        Real.pi*R^2) atTop (𝓝 (-Real.pi*c.re)) := by
  obtain ⟨B, R₀, hB, hb⟩ := inverse_circle_remainder_bound hT
  rw [Metric.tendsto_atTop]
  intro ε hε
  refine ⟨max R₀ (2*Real.pi*B/ε+1), ?_⟩
  intro R hR
  have hRR : R₀ ≤ R := (le_max_left _ _).trans hR
  obtain ⟨hRp, hTbound⟩ := hb R hRR
  have he := principal_circle_flux_estimate hF hexp hB hRp hTbound
  have hRlarge := (le_max_right R₀ (2*Real.pi*B/ε+1)).trans hR
  have hlt : 2*Real.pi*B/R < ε := by
    apply (div_lt_iff₀ hRp).mpr
    have hh : 2*Real.pi*B/ε < R := by linarith
    have hh' := (div_lt_iff₀ hε).mp hh
    nlinarith
  rw [dist_eq_norm, Real.norm_eq_abs]
  calc
    _ = |planarFormIntegral (fun z => -(F z).im) (fun _ => 0) (unitCircleParam 0 R) -
        Real.pi*R^2 + Real.pi*c.re| := by congr 1; ring
    _ ≤ _ := he
    _ < _ := hlt

end CircleDomainRigidity

end

end OAI
