import OAI.Geometry.RCD.Heat.HeatVarianceSobolev

namespace OAI

/-! # Reverse Poincaré for arbitrary bounded L² initial data -/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Small positive heat times approximate bounded L² data while preserving
the amplitude bound, so the variance inequality holds without initial
Sobolev regularity. -/
theorem NoncollapsedRCD.heat_variance_lower_bounded
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X) (p : X) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) :=
      locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    let μ := hausdorff n X
    ∀ (f w : Lp ℝ 2 μ) (C B : ℝ≥0), (∀ᵐ x ∂μ, |f x| ≤ C) →
      0 ≤ w → (∀ᵐ x ∂μ, |w x| ≤ B) → ∀ (T : ℝ) (hT : 0 < T),
      2*T*Real.exp (-2*|K| *T)*
          (∫ x, w x*(SobolevSpace.minimalSlope μ hX.quadratic
            (heatSobolev μ hX.quadratic T hT f) x)^2 ∂μ) ≤
        (∫ x, heatAt μ hX.quadratic T w x*(f x)^2 ∂μ)-
          (∫ x, w x*(heatAt μ hX.quadratic T f x)^2 ∂μ) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let : μ.Regular := inferInstance
  dsimp only
  intro f w C B hf hw hwB T hT
  let τ : ℕ → ℝ := fun i => 1/(i+1:ℝ)
  have hτ (i : ℕ) : 0 < τ i := by dsimp [τ]; positivity
  let us := fun i => heatSobolev μ hX.quadratic (τ i) (hτ i) f
  have hi (i : ℕ) : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hX.quadratic (us i) x| ≤ C := by
    simpa only [us,heatSobolev_toLp] using heatAt_abs_le_const μ hX.quadratic (τ i) C f hf
  have hu : Tendsto (fun i => SobolevSpace.toLp μ hX.quadratic (us i)) atTop (𝓝 f) := by
    simpa only [us,τ,Function.comp_apply,heatSobolev_toLp,heatAt_zero,one_apply_eq_self] using!
      ((heatAt_continuous μ hX.quadratic f).tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
  have hbound (i : ℕ) := hX.heat_variance_lower_sobolev K n hn p (us i) w C B
    (hi i) hw hwB T hT
  have hleft := (((heat_weighted_energy_continuous μ hX.quadratic w B hwB T hT).tendsto f).comp hu).const_mul
      (2*T*Real.exp (-2*|K| *T))
  have hright := ((heat_variance_continuous μ hX.quadratic w B hwB T).tendsto f).comp hu
  exact le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall hbound)

end RegularPointCoordinates

end

end OAI
