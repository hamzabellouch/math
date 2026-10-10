import OAI.Geometry.RCD.Sobolev.HessianL1LimitUniqueness
import OAI.Geometry.RCD.Metric.RadonDensityL2Bound

namespace OAI

/-! # A full-mass Young estimate survives the canonical Hessian L¹ limit -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem integral_abs_tendsto_of_L1_error (F : ℕ → X → ℝ)
    (hF : ∀ k, Integrable (F k) μ) (J : Lp ℝ 1 μ)
    (hJ : Tendsto (fun k => ∫ x, |F k x-J x| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, |F k x| ∂μ) atTop (𝓝 (∫ x, |J x| ∂μ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun k => ?_) hJ
  have hiJ := (memLp_one_iff_integrable).mp (Lp.memLp J)
  rw [← integral_sub (hF k).abs hiJ.abs,Real.norm_eq_abs]
  calc
    |∫ x, |F k x|-|J x| ∂μ| ≤ ∫ x, |(|F k x|-|J x|)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, |F k x-J x| ∂μ := by
      apply integral_mono ((hF k).abs.sub hiJ.abs).abs ((hF k).sub hiJ).abs
      intro x
      exact abs_abs_sub_abs_le_abs_sub _ _

theorem L1_limit_radon_young_bound (σ : Measure X) [IsFiniteMeasure σ]
    {S : Set X} (hS : μ S ≠ ⊤)
    (F : ℕ → X → ℝ) (hF : ∀ k, Integrable (F k) (μ.restrict S))
    (J : Lp ℝ 1 (μ.restrict S))
    (hJ : Tendsto (fun k => ∫ x in S, |F k x-J x| ∂μ) atTop (𝓝 0))
    (B : ℝ)
    (hbound : ∀ k, ∀ᵐ x ∂μ.restrict S, (F k x)^2 ≤ B^2*(σ.rnDeriv μ x).toReal)
    {a : ℝ} (_ha : 0 < a) :
    4*a*(∫ x in S, |J x| ∂μ) ≤ 4*a^2*μ.real S+B^2*σ.real S := by
  let : IsFiniteMeasure (μ.restrict S) := ⟨by simpa only [Measure.restrict_apply_univ] using hS.lt_top⟩
  have hden := Measure.integrableOn_toReal_rnDeriv (μ := σ) (ν := μ) (measure_ne_top σ S)
  have hlim := (integral_abs_tendsto_of_L1_error (μ.restrict S) F hF J hJ).const_mul (4*a)
  apply le_of_tendsto hlim
  apply Eventually.of_forall
  intro k
  have hy : ∀ᵐ x ∂μ.restrict S,
      4*a*|F k x| ≤ 4*a^2+B^2*(σ.rnDeriv μ x).toReal := by
    filter_upwards [hbound k] with x hx
    nlinarith only [sq_nonneg (2*a-|F k x|),sq_abs (F k x),hx]
  have hh := integral_mono_ae ((hF k).abs.const_mul (4*a))
    ((integrable_const (4*a^2)).add (hden.const_mul (B^2))) hy
  simp only [Pi.add_apply] at hh
  rw [integral_const_mul,integral_add (integrable_const (4*a^2)) (hden.const_mul (B^2)),
    integral_const_mul,integral_const] at hh
  have hmass := mul_le_mul_of_nonneg_left
    (Measure.setIntegral_toReal_rnDeriv_le (μ := σ) (ν := μ) (measure_ne_top σ S)) (sq_nonneg B)
  simp only [integral_const_mul,smul_eq_mul,measureReal_restrict_apply_univ] at hh
  nlinarith only [hh,hmass]

end RegularPointCoordinates

end

end OAI
