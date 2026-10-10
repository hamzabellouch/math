import OAI.Geometry.SurfaceImmersion.Atlas.BundleAtlasBounds
import OAI.Geometry.SurfaceImmersion.Correction.SmoothingTailBounds

namespace OAI

/-! Boundedness, gain and finite-input tails for bundle smoothing. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle MeasureTheory
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {E : M → Type*} [∀ x, TopologicalSpace (E x)]
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContMDiffVectorBundle ∞ F E planeModel]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)
variable (e : A.centers → Trivialization F (TotalSpace.proj : TotalSpace F E → M))
  [∀ i, MemTrivializationAtlas (e i)]
variable (hdomain : ∀ i : A.centers, (chart (i : M)).source ⊆ (e i).baseSet)
include hdomain

/-- No derivative above the stated input order occurs in either bound. -/
theorem bundle_smoothing_bounds (r m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧
      (∀ (u : ∀ x, E x) (s t C : ℝ), 0 < s → 0 < t → t ≤ 1 → 0 ≤ C →
        ContMDiff planeModel (planeModel.prod 𝓘(ℝ, F)) ∞
          (fun x => TotalSpace.mk' F x (u x)) → A.BundleWeightedBound e t m C u →
        A.BundleWeightedBound e t m (D * (1 + (1 + ∫ y, ‖kernel 0 y‖) ^ r) * C)
          (A.bundleSmooth e r s u)) ∧
      (∀ (u : ∀ x, E x) (s t C : ℝ), 0 < s → s ≤ 1 → 0 ≤ C →
        ContMDiff planeModel (planeModel.prod 𝓘(ℝ, F)) ∞
          (fun x => TotalSpace.mk' F x (u x)) → A.BundleWeightedBound e t 0 C u →
        A.BundleWeightedBound e s m (D * weightedGainConstant r m * C)
          (A.bundleSmooth e r s u)) := by
  obtain ⟨D, hD, hd⟩ := A.bundle_restoration_bound e hdomain m
  refine ⟨D, hD, ?_, ?_⟩
  · intro u s t C hs ht ht1 hC hu hb
    have hnon : 0 ≤ (1 + (1 + ∫ y, ‖kernel 0 y‖) ^ r) * C := by positivity
    have h := hd (fun i => finiteSmooth r s (A.bundleLocalize e i u)) t
      ((1 + (1 + ∫ y, ‖kernel 0 y‖) ^ r) * C) ht ht1 hnon
      (fun i => finiteSmooth_smooth r hs (A.bundleLocalize_smooth e hdomain i hu))
      (fun i => finiteSmooth_weighted_bounded r m hs ht
        (A.bundleLocalize_smooth e hdomain i hu)
        (localize_compact (i : M) (A.weight_support i) _) (hb i))
    rw [show A.bundleSmooth e r s u = (fun x => ∑ i : A.centers,
      A.bundleRestore e i (finiteSmooth r s (A.bundleLocalize e i u)) x) from rfl]
    simpa only [mul_assoc] using h
  · intro u s t C hs hs1 hC hu hb
    have h := hd (fun i => finiteSmooth r s (A.bundleLocalize e i u)) s
      (weightedGainConstant r m * C) hs hs1
      (mul_nonneg (weightedGainConstant_nonneg r m) hC)
      (fun i => finiteSmooth_smooth r hs (A.bundleLocalize_smooth e hdomain i hu))
      (fun i => finiteSmooth_weighted_gain r m hs
        (A.bundleLocalize_smooth e hdomain i hu) (fun x => (hb i).norm_le (mem_univ x)))
    rw [show A.bundleSmooth e r s u = (fun x => ∑ i : A.centers,
      A.bundleRestore e i (finiteSmooth r s (A.bundleLocalize e i u)) x) from rfl]
    simpa only [mul_assoc] using h

variable [CompleteSpace F]

/-- The high input norm remains linear after all bundle transition maps. -/
theorem bundle_smoothing_tail (r m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (u : ∀ x, E x) (s t τ B C : ℝ),
      0 < τ → τ ≤ s → s ≤ t → t ≤ 1 → 0 ≤ B → 0 ≤ C →
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, F)) ∞
        (fun x => TotalSpace.mk' F x (u x)) →
      A.BundleWeightedBound e t r B u → A.BundleWeightedBound e t m C u →
      A.BundleWeightedBound e τ m
        (D * tailConstant r * (B * (s / t) ^ r + C * (τ / t) ^ r))
        (fun x => u x - A.bundleSmooth e r s u x) := by
  obtain ⟨D, hD, hd⟩ := A.bundle_restoration_bound e hdomain m
  refine ⟨D, hD, ?_⟩
  intro u s t τ B C hτ hτs hst ht1 hB hC hu hb hc
  have hs : 0 < s := hτ.trans_le hτs
  have ht : 0 < t := hs.trans_le hst
  have hτ1 : τ ≤ 1 := hτs.trans (hst.trans ht1)
  have hsize : 0 ≤ tailConstant r * (B * (s / t) ^ r + C * (τ / t) ^ r) :=
    mul_nonneg (tailConstant_nonneg r) (by positivity)
  have h := hd (fun i => residual s r (A.bundleLocalize e i u)) τ
    (tailConstant r * (B * (s / t) ^ r + C * (τ / t) ^ r)) hτ hτ1 hsize
    (fun i => residual_smooth hs r (A.bundleLocalize_smooth e hdomain i hu))
    (fun i => by
      rw [← error_finiteSmooth]
      exact weighted_smoothing_tail r m hτ hτs hst
        (A.bundleLocalize_smooth e hdomain i hu)
        (localize_compact (i : M) (A.weight_support i) _) (hb i) (hc i))
  have heq : (fun x => u x - A.bundleSmooth e r s u x) =
      fun x => ∑ i : A.centers, A.bundleRestore e i
        (residual s r (A.bundleLocalize e i u)) x :=
    funext (A.bundle_smoothing_error e hdomain r s u)
  rw [heq]
  simpa only [mul_assoc] using h

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
