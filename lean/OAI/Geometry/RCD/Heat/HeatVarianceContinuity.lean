import OAI.Geometry.RCD.Heat.HeatVarianceDerivative

namespace OAI

/-! # Continuity and endpoint identities for the heat variance pairing -/

open Filter MeasureTheory
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

/-- The variance pairing is continuous, including at both heat endpoints. -/
theorem heatSquarePairing_continuous (f w : Lp ℝ 2 μ) (C : ℝ≥0)
    (hf : ∀ᵐ x ∂μ, |f x| ≤ C) (T : ℝ) :
    Continuous (heatSquarePairing μ hQ f w C hf T) := by
  have hF : Continuous (fun s : ℝ => heatAt μ hQ (T-s) f) :=
    (heatAt_continuous μ hQ f).comp (continuous_const.sub continuous_id)
  have hS : Continuous (fun s : ℝ => boundedLpSquare μ (heatAt μ hQ (T-s) f) C
      C.coe_nonneg (heatAt_abs_le_const μ hQ (T-s) C f hf)) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    exact boundedLpSquare_continuousAt μ C.coe_nonneg hF.continuousAt
      (fun r => heatAt_abs_le_const μ hQ (T-r) C f hf)
  exact (heatAt_continuous μ hQ w).inner hS

/-- Integral representation with the actual heat functions. -/
theorem heatSquarePairing_eq_integral (f w : Lp ℝ 2 μ) (C : ℝ≥0)
    (hf : ∀ᵐ x ∂μ, |f x| ≤ C) (T s : ℝ) :
    heatSquarePairing μ hQ f w C hf T s =
      ∫ x, heatAt μ hQ s w x*(heatAt μ hQ (T-s) f x)^2 ∂μ := by
  rw [heatSquarePairing,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [boundedLpSquare_coe μ (heatAt μ hQ (T-s) f) C C.coe_nonneg
    (heatAt_abs_le_const μ hQ (T-s) C f hf)] with x hx
  simp only [Real.inner_apply,hx]

/-- The heat semigroup identity holds in the actual Sobolev space. -/
theorem heatSobolev_iterate (f : Lp ℝ 2 μ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    heatSobolev μ hQ s hs (SobolevSpace.toLp μ hQ (heatSobolev μ hQ t ht f)) =
      heatSobolev μ hQ (s+t) (add_pos hs ht) f := by
  apply Subtype.ext
  change heatAt μ hQ s (SobolevSpace.toLp μ hQ (heatSobolev μ hQ t ht f)) =
    heatAt μ hQ (s+t) f
  simp only [heatSobolev_toLp]
  rw [heatAt_add μ hQ s t hs.le ht.le]
  rfl

end RegularPointCoordinates

end

end OAI
