import OAI.GroupTheory.PolycyclicRecognition.Algebra.SuccessfulBundleStates

namespace OAI

/-! # The joint volume of good bundle-end states

The successful parameter set can be correlated.  Haar preservation is
applied to its image, after the joint polynomial image estimate.
-/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Filter Set Metric
open scoped Manifold Topology

variable {L I : Type*} [LieRing L] [LieAlgebra ℝ L]
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]
  [MeasurableMul₂ G] [MeasurableInv G]

theorem good_source_bundle_image {m h : ℕ}
    (lie : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (X : I → L) (s : I → ℝ) (letters : Fin m → I)
    (scale : ℕ → ℝ) (p : ℝ)
    (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant]
    (φ : ℕ → Fin h → G ≃ₜ* G)
    (hφ : ∀ r i, MeasurePreserving (φ r i) μ μ)
    (sample : ℕ → ℕ → ℝ → G)
    (hsub : ∀ r j u v, sample r j u * (sample r j v)⁻¹ = sample r j (u - v))
    (hsample : ∀ r (i : Fin h) (j : Fin m) t,
      sample r (finProdFinEquiv (i, j)).val t = φ r i
        (Exp (lie (t • (Real.exp (scale r * s (letters j)) • X (letters j))))))
    (Good : ℕ → Set G) (x : ℕ → G) (hx : ∀ r, x r ∈ Good r)
    (C : ℕ → Set (Fin h → G)) (hC : ∀ r, IsCompact (C r))
    (hvol : HasSubexponentialLowerBoundSeq scale (fun r =>
      ((Measure.pi fun _ : Fin h => μ) (C r)).toReal / Real.exp (scale r * p)))
    (ρ : ℝ)
    (hreach : ∀ᶠ r in atTop, ∀ y ∈ C r, ∃ t : Fin (h * m + h * m) → ℝ,
      t ∈ closedBall 0 ρ ∧
      SwitchSuccessful (fun _ => Good r) 0 (h * m) (x r)
        (sampledSwitchParameters (sample r) (h * m) t) ∧
      sourceBundleProduct lie Exp X s letters (bundleParameterChart h m) (scale r) t = y) :
    let S := fun r => sourceBundleStateEquiv h (x r)
      (fun i => (φ r i).toHomeomorph.toMeasurableEquiv) '' C r
    (∀ r, IsCompact (S r)) ∧
      HasSubexponentialLowerBoundSeq scale (fun r =>
        ((Measure.pi fun _ : Fin h => μ) (S r)).toReal / Real.exp (scale r * p)) ∧
      ∀ᶠ r in atTop, ∀ v ∈ S r, (∀ i, v i ∈ Good r) ∧
        ∃ t : Fin (h * m + h * m) → ℝ, t ∈ closedBall 0 ρ ∧
          SwitchSuccessful (fun _ => Good r) 0 (h * m) (x r)
            (sampledSwitchParameters (sample r) (h * m) t) ∧
          v = sourceBundleStateEquiv h (x r)
            (fun i => (φ r i).toHomeomorph.toMeasurableEquiv)
            (sourceBundleProduct lie Exp X s letters (bundleParameterChart h m) (scale r) t) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro r
    exact (hC r).image (continuous_sourceBundleStateEquiv h (x r) _
      (fun i => (φ r i).continuous))
  · have he (r : ℕ) := sourceBundleStateEquiv_image_measure μ h (x r)
      (fun i => (φ r i).toHomeomorph.toMeasurableEquiv) (hφ r) (C r)
    simpa only [he] using hvol
  · filter_upwards [hreach] with r hr
    rintro v ⟨y, hy, rfl⟩
    obtain ⟨t, ht, hs, rfl⟩ := hr y hy
    refine ⟨?_, t, ht, hs, rfl⟩
    exact successful_sourceBundleStates_good lie Exp X s letters (scale r)
      (fun i => (φ r i).toMulEquiv) (sample r) (hsub r) (hsample r) (Good r) (x r) (hx r) t hs

end PolycyclicRecognition

end

end OAI
