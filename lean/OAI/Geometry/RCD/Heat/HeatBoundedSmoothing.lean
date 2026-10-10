import OAI.Geometry.RCD.Sobolev.BoundedGradientLipschitz
import OAI.Geometry.RCD.Heat.HeatReversePoincare

namespace OAI

/-! # Bounded-data Lipschitz smoothing for the actual RCD heat flow -/

open Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Reverse Poincaré bounds the weak gradient of a positive-time heat flow
using only the amplitude of its initial L² data. -/
theorem NoncollapsedRCD.heat_bounded_gradient
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X) (p : X) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) :=
      locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    let μ := hausdorff n X
    ∀ (f : Lp ℝ 2 μ) (C : ℝ≥0) (_hf : ∀ᵐ x ∂μ, |f x| ≤ C) (T : ℝ) (hT : 0 < T),
      ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hX.quadratic (heatSobolev μ hX.quadratic T hT f) x ≤
        Real.sqrt ((C:ℝ)^2/(2*T*Real.exp (-2*|K| *T))) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let : μ.Regular := inferInstance
  dsimp only
  intro f C hf T hT
  let Q := boundedLpSquare μ f C C.coe_nonneg hf
  have hQb : ∀ᵐ x ∂μ, Q x ≤ (C:ℝ)^2 := by
    filter_upwards [boundedLpSquare_coe μ f C C.coe_nonneg hf,hf] with x hx hfx
    rw [hx]
    nlinarith [sq_abs (f x),pow_le_pow_left₀ (abs_nonneg (f x)) hfx 2]
  have hqb := heatAt_le_const μ hX.quadratic T (sq_nonneg (C:ℝ)) Q hQb
  have ha : 0 < 2*T*Real.exp (-2*|K| *T) := by positivity
  have hr := hX.heat_reverse_poincare K n hn p f C hf T hT
  filter_upwards [hr,hqb] with x hx hqx
  apply Real.le_sqrt_of_sq_le
  apply (le_div_iff₀ ha).mpr
  nlinarith [sq_nonneg (heatAt μ hX.quadratic T f x)]

/-- Positive heat time turns arbitrary bounded L² data into a function
with a Lipschitz representative. -/
theorem NoncollapsedRCD.heat_bounded_lipschitz
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X) (p : X)
    (f : Lp ℝ 2 (hausdorff n X)) (C : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ C) (T : ℝ) (hT : 0 < T) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) :=
      locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    let μ := hausdorff n X
    ∃ v : X → ℝ,
      LipschitzWith ⟨Real.sqrt ((C:ℝ)^2/(2*T*Real.exp (-2*|K| *T))),Real.sqrt_nonneg _⟩ v ∧
      heatAt μ hX.quadratic T f =ᵐ[μ] v := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let u := heatSobolev μ hX.quadratic T hT f
  exact hX.lipschitz_of_bounded_gradient K n hn (SobolevSpace.minimalSlope_isRelaxed μ hX.quadratic u)
    _ (hX.heat_bounded_gradient K n hn p f C hf T hT)

end RegularPointCoordinates

end

end OAI
