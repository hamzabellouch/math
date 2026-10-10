import OAI.Geometry.RCD.Heat.HeatVarianceForms
import OAI.Geometry.RCD.Metric.BoundedCompactApproximation

namespace OAI

/-! # Reverse Poincaré for bounded Sobolev initial data -/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- L² continuity after positive heat time passes the compact Lipschitz
inequality to any bounded Sobolev function. -/
theorem NoncollapsedRCD.heat_variance_lower_sobolev
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X) (p : X) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) :=
      locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    let μ := hausdorff n X
    ∀ (f : SobolevSpace μ hX.quadratic) (w : Lp ℝ 2 μ) (C B : ℝ≥0),
      (∀ᵐ x ∂μ, |SobolevSpace.toLp μ hX.quadratic f x| ≤ C) →
      0 ≤ w → (∀ᵐ x ∂μ, |w x| ≤ B) → ∀ (T : ℝ) (hT : 0 < T),
      2*T*Real.exp (-2*|K| *T)*
          (∫ x, w x*(SobolevSpace.minimalSlope μ hX.quadratic
            (heatSobolev μ hX.quadratic T hT (SobolevSpace.toLp μ hX.quadratic f)) x)^2 ∂μ) ≤
        (∫ x, heatAt μ hX.quadratic T w x*(SobolevSpace.toLp μ hX.quadratic f x)^2 ∂μ)-
          (∫ x, w x*(heatAt μ hX.quadratic T (SobolevSpace.toLp μ hX.quadratic f) x)^2 ∂μ) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let : μ.Regular := inferInstance
  dsimp only
  intro f w C B hf hw hwB T hT
  obtain ⟨us,gs,hu,hl,hs,he,hb⟩ :=
    SobolevSpace.bounded_compact_L2_approximation μ hX.quadratic f C hf p
  have hi (i : ℕ) : ∀ᵐ x ∂μ, |us i x| ≤ C := (he i).mono fun x hx => by
    rw [hx]
    exact hb i x
  have hbound (i : ℕ) := hX.heat_variance_lower K n hn (hl i).choose_spec (hs i)
    p (us i) w (he i).symm C B (hi i) hw hwB T hT
  have hleft := (((heat_weighted_energy_continuous μ hX.quadratic w B hwB T hT).tendsto
    (SobolevSpace.toLp μ hX.quadratic f)).comp hu).const_mul
      (2*T*Real.exp (-2*|K| *T))
  have hright := ((heat_variance_continuous μ hX.quadratic w B hwB T).tendsto
    (SobolevSpace.toLp μ hX.quadratic f)).comp hu
  exact le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall hbound)

end RegularPointCoordinates

end

end OAI
