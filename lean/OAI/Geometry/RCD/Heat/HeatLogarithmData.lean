import OAI.Geometry.RCD.Coordinates.ShiftedLogarithmRegularData
import OAI.Geometry.RCD.Coordinates.HeatRegularSourceGram
import OAI.Geometry.RCD.Heat.BoundedHeatOrder
import OAI.Geometry.RCD.Sobolev.BoundedGlobalBochner

namespace OAI

/-! # Constructed Sobolev logarithmic heat data

The regularized logarithm of the actual bounded RCD heat evolution has a
Sobolev Laplacian and a Sobolev squared gradient. No bound on the original
heat generator is assumed.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2≤n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn p

theorem heat_logarithm_sobolev_data (f : Lp ℝ 2 (hausdorff n X))
    (hf0 : 0≤f) (A : ℝ≥0) (hf : ∀ᵐ x ∂hausdorff n X, |f x|≤A)
    {t ε : ℝ} (ht : 0<t) (hε : 0<ε) :
    let v := hX.boundedHeat hn p f ⟨A,hf⟩ t ht
    ∃ (ℓ S H : SobolevSpace (hausdorff n X) hX.quadratic) (B C : ℝ≥0),
      IsWeakLaplacian (hausdorff n X) hX.quadratic ℓ
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic S) ∧
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic H =ᵐ[hausdorff n X]
        localGamma (hausdorff n X) hX.quadratic ℓ ℓ) ∧
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic ℓ =ᵐ[hausdorff n X]
        fun x => Real.log (ε+v x)-Real.log ε) ∧
      LipschitzWith C (fun x => Real.log (ε+v x)-Real.log ε) ∧
      (∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic ℓ x|≤B) ∧
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic S =ᵐ[hausdorff n X] fun x =>
        (-heatGeneratorAt (hausdorff n X) hX.quadratic t f) x/(ε+v x)-
        localGamma (hausdorff n X) hX.quadratic
          (heatSobolev (hausdorff n X) hX.quadratic t ht f)
          (heatSobolev (hausdorff n X) hX.quadratic t ht f) x/(ε+v x)^2) := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let v := hX.boundedHeat hn p f ⟨A,hf⟩ t ht
  let U := heatSobolev μ Q t ht f
  have hv := hX.boundedHeat_lipschitz hn p f ⟨A,hf⟩ t ht A hf
  have hUr : SobolevSpace.toLp μ Q U =ᵐ[μ] v := hX.boundedHeat_represents hn p f ⟨A,hf⟩ t ht
  have hU := SobolevSpace.minimalSlope_le_lipschitz μ Q U hv hUr
  obtain ⟨D,G,hD,hG,hGb⟩ := hX.heat_regular_source_gram hn p f ht _ hU
  have hval (x : X) : v x∈Icc 0 (A:ℝ) :=
    ⟨hX.boundedHeat_nonneg hn p f ⟨A,hf⟩ t ht hf0 x,
      (le_abs_self _).trans (hX.boundedHeat_abs_le hn p f ⟨A,hf⟩ t ht A hf x)⟩
  obtain ⟨ℓ,S,H,B,C,hS,hH,hℓ,hC,hB,hsource⟩ :=
    shifted_logarithm_regular_data μ Q p U D G hD hG v hv hUr hε A hval
  have hD' : SobolevSpace.toLp μ Q D = -heatGeneratorAt μ Q t f :=
    IsWeakLaplacian.unique μ Q hD (by
      simpa only [heatGeneratorAt_of_pos μ Q t ht] using heatSobolev_weak_laplacian μ Q t ht f)
  refine ⟨ℓ,S,H,B,C,hS,hH,hℓ,hC,hB,?_⟩
  simpa only [hD'] using hsource

/-- The actual logarithmic heat state satisfies Bochner for every bounded
continuous nonnegative Sobolev test on the whole space. -/
theorem heat_logarithm_bochner_data (f : Lp ℝ 2 (hausdorff n X))
    (hf0 : 0≤f) (A : ℝ≥0) (hf : ∀ᵐ x ∂hausdorff n X, |f x|≤A)
    {t ε : ℝ} (ht : 0<t) (hε : 0<ε) :
    let v := hX.boundedHeat hn p f ⟨A,hf⟩ t ht
    ∃ (ℓ S H : SobolevSpace (hausdorff n X) hX.quadratic),
      IsWeakLaplacian (hausdorff n X) hX.quadratic ℓ
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic S) ∧
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic H =ᵐ[hausdorff n X]
        localGamma (hausdorff n X) hX.quadratic ℓ ℓ) ∧
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic ℓ =ᵐ[hausdorff n X]
        fun x => Real.log (ε+v x)-Real.log ε) ∧
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic S =ᵐ[hausdorff n X] fun x =>
        (-heatGeneratorAt (hausdorff n X) hX.quadratic t f) x/(ε+v x)-
        localGamma (hausdorff n X) hX.quadratic
          (heatSobolev (hausdorff n X) hX.quadratic t ht f)
          (heatSobolev (hausdorff n X) hX.quadratic t ht f) x/(ε+v x)^2) ∧
      (∀ (w : SobolevSpace (hausdorff n X) hX.quadratic) (q : X → ℝ),
        Continuous q → ∀ (C : ℝ≥0), (∀ x, |q x|≤C) → (∀ x, 0≤q x) →
        SobolevSpace.toLp (hausdorff n X) hX.quadratic w =ᵐ[hausdorff n X] q →
        0≤bochnerTestForm (hausdorff n X) hX.quadratic (-K) H w-
          weightedGamma (hausdorff n X) hX.quadratic
            (SobolevSpace.toLp (hausdorff n X) hX.quadratic w) ℓ S) := by
  obtain ⟨ℓ,S,H,B,L,hS,hH,hℓ,hL,hB,hsource⟩ :=
    hX.heat_logarithm_sobolev_data hn p f hf0 A hf ht hε
  refine ⟨ℓ,S,H,hS,hH,hℓ,hsource,?_⟩
  intro w q hq C hC hq0 hw
  exact hX.bounded_global_bochner hn p ℓ S H w hS _ hL hℓ B hB hH q hq C hC hq0 hw

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
