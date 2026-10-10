import OAI.Geometry.RCD.Sobolev.SignedLipschitzMeasure
import OAI.Geometry.RCD.Sobolev.CompactLipschitzTests

namespace OAI

/-! # Positive local distributions retain their full signed measure -/

open Set Filter MeasureTheory
open scoped NNReal ENNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SecondCountableTopology X]

theorem signedMeasure_nonneg_restrict_of_tests
    (ν : SignedMeasure X) {Ω S : Set X} (hS : MeasurableSet S)
    (χ : X →ᵇ ℝ) {L : ℝ≥0} (hχ : LipschitzWith L χ)
    (hχc : HasCompactSupport (χ : X → ℝ)) (hχΩ : tsupport χ ⊆ Ω)
    (hχ0 : 0 ≤ χ) (hχ1 : ∀ x ∈ S, χ x = 1)
    (h : ∀ f : compactLipschitzTests Ω, 0 ≤ (f : X →ᵇ ℝ) →
      0 ≤ ∫ᵛ x, (f : X →ᵇ ℝ) x ∂<•ν) :
    0 ≤ ν.restrict S := by
  let μp := ν.toJordanDecomposition.posPart
  let μn := ν.toJordanDecomposition.negPart
  let ρ (μ : Measure X) := μ.withDensity (fun x => ENNReal.ofReal (χ x))
  have hρ (μ : Measure X) [IsFiniteMeasure μ] : IsFiniteMeasure (ρ μ) :=
    isFiniteMeasure_withDensity_ofReal
      (Integrable.of_bound χ.continuous.aestronglyMeasurable ‖χ‖
        (Eventually.of_forall χ.norm_coe_le_norm)).2
  have : IsFiniteMeasure (ρ μp) := hρ μp
  have : IsFiniteMeasure (ρ μn) := hρ μn
  have hi (μ : Measure X) (f : X → ℝ) :
      (∫ x, f x ∂ρ μ) = ∫ x, χ x * f x ∂μ := by
    dsimp only [ρ]
    rw [integral_withDensity_eq_integral_toReal_smul
      χ.continuous.measurable.ennreal_ofReal (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [smul_eq_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change (ENNReal.ofReal (χ x)).toReal * f x = χ x * f x
      have hpos : 0 ≤ χ x := hχ0 x
      exact congrArg (fun a : ℝ => a * f x) (ENNReal.toReal_ofReal hpos)
  have hle : ρ μn ≤ ρ μp := by
    apply measure_le_of_bounded_lipschitz_integral
    intro f A hf h0 hB
    obtain ⟨B, hB⟩ := hB
    let g : X →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup f hf.continuous
      B (fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (h0 x)] using hB x)
    have hprod : LipschitzWith (‖χ‖₊ * A + ‖g‖₊ * L) (χ * g : X →ᵇ ℝ) :=
      lipschitzWith_mul_of_support_bound hχ hf
        (fun x => by simpa only [Real.norm_eq_abs, coe_nnnorm] using χ.norm_coe_le_norm x)
        (fun x _ => by simpa only [Real.norm_eq_abs, coe_nnnorm] using g.norm_coe_le_norm x)
    let q : compactLipschitzTests Ω := ⟨χ * g, _, hprod,
      hχc.mul_right, tsupport_mul_subset_left.trans hχΩ⟩
    have hq : 0 ≤ (q : X →ᵇ ℝ) := fun x => mul_nonneg (hχ0 x) (h0 x)
    have hh := h q hq
    rw [signed_integral_jordan] at hh
    rw [hi, hi]
    exact sub_nonneg.mp hh
  have hρS (μ : Measure X) : (ρ μ).restrict S = μ.restrict S := by
    dsimp only [ρ]
    rw [restrict_withDensity hS]
    have heq : (fun x => ENNReal.ofReal (χ x)) =ᵐ[μ.restrict S] (1 : X → ℝ≥0∞) := by
      filter_upwards [ae_restrict_mem hS] with x hx
      simp only [hχ1 x hx, ENNReal.ofReal_one, Pi.one_apply]
    rw [withDensity_congr_ae heq, withDensity_one]
  have hrest : μn.restrict S ≤ μp.restrict S := by
    rw [← hρS μn, ← hρS μp]
    exact Measure.restrict_mono le_rfl hle
  rw [← ν.toSignedMeasure_toJordanDecomposition]
  change 0 ≤ (μp.toSignedMeasure - μn.toSignedMeasure).restrict S
  rw [VectorMeasure.restrict_sub,
    Measure.toSignedMeasure_restrict_eq_restrict_toSignedMeasure μp S hS,
    Measure.toSignedMeasure_restrict_eq_restrict_toSignedMeasure μn S hS]
  exact sub_nonneg.mpr ((Measure.toSignedMeasure_le_toSignedMeasure_iff _ _).mpr hrest)

end RegularPointCoordinates

end

end OAI
