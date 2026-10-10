import Mathlib
import OAI.Analysis.RCDHeat.ExistingAnalytic
import OAI.Analysis.RCDHeat.DimensionalCompactWeightedGradient

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: FiniteDimensionalBochnerTarget, FiniteDimensionalBochnerProof. -/



namespace RegularPointCoordinates

section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal

 

def FiniteDimensionalHeatBochnerObligation
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X) : Prop :=
  letI : ProperSpace X := hX.proper K n hn
  letI : SeparableSpace X := hX.separable
  letI : IsLocallyFiniteMeasure (hausdorff n X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  let μ := hausdorff n X
  ∀ (φ : X → ℝ) (L : ℝ≥0), LipschitzWith L φ → HasCompactSupport φ →
    ∀ (_ : X) (f w : Lp ℝ 2 μ), φ =ᵐ[μ] f → 0 ≤ w →
    ∀ (C : ℝ≥0), (∀ᵐ x ∂μ, |w x| ≤ C) →
    ∀ (t s : ℝ) (ht : 0 < t) (_hs : 0 < s),
      let F := heatSobolev μ hX.quadratic t ht f
      let D := heatSobolevMap μ hX.quadratic (t/2) (half_pos ht)
        (-heatGeneratorAt μ hX.quadratic (t-t/2) f)
      K*(∫ x, heatAt μ hX.quadratic s w x *
          (SobolevSpace.minimalSlope μ hX.quadratic F x)^2 ∂μ)
        + weightedGamma μ hX.quadratic (heatAt μ hX.quadratic s w) F D
        + (1/(n:ℝ))*(∫ x, heatAt μ hX.quadratic s w x *
            (SobolevSpace.toLp μ hX.quadratic D x)^2 ∂μ) ≤
      (1/2:ℝ)*(∫ x, (-heatGeneratorAt μ hX.quadratic s w) x *
          (SobolevSpace.minimalSlope μ hX.quadratic F x)^2 ∂μ)

end

 

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.dimensional_heat_compact_weak_bochner
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) (hs : HasCompactSupport φ)
    (p : X) (f w : Lp ℝ 2 (hausdorff n X)) (hf : φ =ᵐ[hausdorff n X] f)
    (N : ℝ) (hN : (n:ℝ) ≤ N)
    (hw : 0 ≤ w) (C : ℝ≥0) (hwC : ∀ᵐ x ∂hausdorff n X, |w x| ≤ C)
    (t s : ℝ) (ht : 0 < t) (hs' : 0 < s) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    let μ := hausdorff n X
    let F := heatSobolev μ hX.quadratic t ht f
    let D := heatSobolevMap μ hX.quadratic (t/2) (half_pos ht)
      (-heatGeneratorAt μ hX.quadratic (t-t/2) f)
    IsWeakLaplacian μ hX.quadratic F (SobolevSpace.toLp μ hX.quadratic D) ∧
      K*(∫ x, heatAt μ hX.quadratic s w x*(SobolevSpace.minimalSlope μ hX.quadratic F x)^2 ∂μ)
        +weightedGamma μ hX.quadratic (heatAt μ hX.quadratic s w) F D
        +(1/N)*(∫ x, heatAt μ hX.quadratic s w x * (SobolevSpace.toLp μ hX.quadratic D x)^2 ∂μ) ≤
      (1/2:ℝ)*(∫ x, (-heatGeneratorAt μ hX.quadratic s w) x*
        (SobolevSpace.minimalSlope μ hX.quadratic F x)^2 ∂μ) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let F := heatSobolev μ hX.quadratic t ht f
  let hm := hX.heat_compact_gamma_memLp K n hn hφ hs p f hf t ht
  let H := hm.toLp (fun x => (SobolevSpace.minimalSlope μ hX.quadratic F x)^2)
  have hH : (fun x => (SobolevSpace.minimalSlope μ hX.quadratic F x)^2) =ᵐ[μ] H := hm.coeFn_toLp.symm
  refine ⟨heatTail_weak_laplacian μ hX.quadratic t ht f,?_⟩
  have hh := hX.dimensional_heat_weak_bochner K n hn p f w N hN hw C hwC t s ht hs' H hH
  convert hh using 2
  apply integral_congr_ae
  filter_upwards [hH] with x hx
  rw [hx]

theorem NoncollapsedRCD.finiteDimensionalHeatBochner
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X) :
    FiniteDimensionalHeatBochnerObligation K n hn hX := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let : IsLocallyFiniteMeasure (hausdorff n X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  intro φ L hφ hφs p f w hf hw C hwC t s ht hs
  exact (hX.dimensional_heat_compact_weak_bochner K n hn hφ hφs p f w hf
    (n:ℝ) le_rfl hw C hwC t s ht hs).2


end RegularPointCoordinates

end OAI
