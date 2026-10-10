import OAI.GroupTheory.PolycyclicRecognition.Geometry.PairHeightCocycle
import OAI.GroupTheory.PolycyclicRecognition.Algebra.DistortedHomomorphisms

namespace OAI

/-! # Metric control of the actual stationary mean

The common Lipschitz constant of normalized pairs bounds their height
profiles, and hence bounds the homomorphism obtained by integration.
Consequently the actual averaged homomorphism kills every root flow.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory LieAlgebra LieModule
open scoped NNReal Manifold

section Mean

variable {G W : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
  {Λ K : ℝ≥0}

omit [ProperSpace G] [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedSpace ℝ W] [CompleteSpace W] in
/-- Pointwise height control uses the forward normalization at the identity. -/
theorem norm_pairHeight_le (π : G →* Multiplicative W)
    (hπ : LipschitzWith K (fun g => (π g).toAdd))
    (g : G) (p : NormalizedPair G Λ) :
    ‖pairHeight π g p‖ ≤ (K : ℝ) * Λ * dist 1 g := by
  have h₁ := hπ.dist_le_mul (p.val.1 g) (p.val.1 1)
  have h₂ := p.property.1.1.dist_le_mul g 1
  rw [p.property.2] at h₂
  rw [p.property.2, map_one] at h₁
  change dist (pairHeight π g p) 0 ≤ _ at h₁
  rw [dist_zero_right] at h₁
  exact h₁.trans (by simpa only [dist_comm, mul_assoc] using
    mul_le_mul_of_nonneg_left h₂ K.coe_nonneg)

variable [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
  [SMulInvariantMeasure G (NormalizedPair G Λ) μ]

attribute [local instance] stationaryL2Action

/-- The averaged slope of the actual evaluation cocycle. -/
def normalizedPairMeanSlope (π : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) : G →* Multiplicative W :=
  l2MeanSlope μ (pairHeightL2 μ π hπ) (isCocycle_pairHeightL2 μ π hπ)

omit [CompleteSpace W] in
theorem continuous_normalizedPairMeanSlope (π : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) :
    Continuous (fun g => (normalizedPairMeanSlope μ π hπ g).toAdd) :=
  (stationaryL2Mean μ).continuous.comp (continuous_pairHeightL2 μ π hπ)

omit [CompleteSpace W] in
/-- Integration preserves the common linear metric bound. -/
theorem norm_normalizedPairMeanSlope_le (π : G →* Multiplicative W)
    (hπ : LipschitzWith K (fun g => (π g).toAdd)) (g : G) :
    ‖(normalizedPairMeanSlope μ π hπ.continuous g).toAdd‖ ≤
      (K : ℝ) * Λ * dist 1 g := by
  change ‖∫ p, pairHeightL2 μ π hπ.continuous g p ∂μ‖ ≤ _
  have hae : (pairHeightL2 μ π hπ.continuous g : NormalizedPair G Λ → W) =ᵐ[μ]
      pairHeight π g := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ
        (pairHeightProfile π hπ.continuous g)
  calc
    _ = ‖∫ p, pairHeight π g p ∂μ‖ := congrArg norm (integral_congr_ae hae)
    _ ≤ _ := by
      simpa using norm_integral_le_of_norm_le_const (μ := μ)
        (Filter.Eventually.of_forall (norm_pairHeight_le π hπ g))

end Mean

end PolycyclicRecognition

end

end OAI
