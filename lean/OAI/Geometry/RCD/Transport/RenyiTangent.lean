import OAI.Analysis.RCDHeat.WeightedRenyi
import Mathlib.Analysis.Convex.Deriv

namespace OAI

/-! # The finite Rényi tangent inequality

This is the scalar and integral tangent inequality used to differentiate
the original curvature-dimension transport bound at a positive density.
The exponent stays strictly below one.
-/

open Set Filter MeasureTheory

noncomputable section
namespace RegularPointCoordinates

theorem rpow_tangent_upper {a b q : ℝ} (ha : 0<a) (hb : 0≤b)
    (hq0 : 0<q) (hq1 : q<1) :
    b^q≤(1-q)*a^q+q*a^(q-1)*b := by
  have hc := Real.concaveOn_rpow hq0.le hq1.le
  have hd := Real.hasDerivAt_rpow_const (p := q) (Or.inl ha.ne')
  have he : a^(q-1)*a=a^q := by
    conv_lhs => arg 2; rw [← Real.rpow_one a]
    rw [← Real.rpow_add ha]
    congr 1
    ring
  rcases lt_trichotomy a b with hab | hab | hba
  · have hs := hc.slope_le_of_hasDerivAt ha.le hb hab hd
    rw [slope_def_field] at hs
    have hh := (div_le_iff₀ (sub_pos.mpr hab)).mp hs
    nlinarith only [hh,congrArg (fun z : ℝ => q*z) he]
  · rw [← hab]
    nlinarith only [congrArg (fun z : ℝ => q*z) he]
  · have hs := hc.le_slope_of_hasDerivAt hb ha.le hba hd
    rw [slope_def_field] at hs
    have hh := (le_div_iff₀ (sub_pos.mpr hba)).mp hs
    nlinarith only [hh,congrArg (fun z : ℝ => q*z) he]

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

/-- The density tangent is integrable even when the comparison density
vanishes. Only the reference density has to be bounded below. -/
theorem integral_rpow_tangent_upper (ρ η : X → ℝ) (hρ : Measurable ρ) (hη : Measurable η)
    (hρi : Integrable ρ μ) (hηi : Integrable η μ) {ε q : ℝ} (hε : 0<ε)
    (hρ0 : ∀ᵐ x ∂μ, ε≤ρ x) (hη0 : ∀ᵐ x ∂μ, 0≤η x)
    (hq0 : 0<q) (hq1 : q<1) :
    Integrable (fun x => ρ x^(q-1)*η x) μ ∧
    (∫ x, η x^q ∂μ)≤(1-q)*(∫ x, ρ x^q ∂μ)+q*(∫ x, ρ x^(q-1)*η x ∂μ) := by
  have hρn : ∀ᵐ x ∂μ, 0≤ρ x := hρ0.mono fun _ hx => hε.le.trans hx
  have hρp := integrable_density_power μ ρ hρ hρi hρn hq0.le hq1.le
  have hηp := integrable_density_power μ η hη hηi hη0 hq0.le hq1.le
  have hb : ∀ᵐ x ∂μ, ‖ρ x^(q-1)‖≤ε^(q-1) := by
    filter_upwards [hρ0] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (hε.le.trans hx) _)]
    exact Real.rpow_le_rpow_of_nonpos hε hx (by linarith)
  have hi : Integrable (fun x => ρ x^(q-1)*η x) μ :=
    hηi.bdd_mul (hρ.pow_const (q-1)).aestronglyMeasurable hb
  refine ⟨hi,?_⟩
  have ht : (∫ x, η x^q ∂μ)≤∫ x, ((1-q)*ρ x^q+q*(ρ x^(q-1)*η x)) ∂μ := by
    apply integral_mono_ae hηp ((hρp.const_mul _).add (hi.const_mul _))
    filter_upwards [hρ0,hη0] with x hx hy
    change η x^q≤(1-q)*ρ x^q+q*(ρ x^(q-1)*η x)
    simpa only [mul_assoc] using rpow_tangent_upper (hε.trans_le hx) hy hq0 hq1
  rwa [integral_add (hρp.const_mul _) (hi.const_mul _),integral_const_mul,integral_const_mul] at ht

end RegularPointCoordinates

end

end OAI
