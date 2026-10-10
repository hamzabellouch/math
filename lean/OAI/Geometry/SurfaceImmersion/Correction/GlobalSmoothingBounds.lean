import OAI.Geometry.SurfaceImmersion.Atlas.AtlasWeightedBounds
import OAI.Geometry.SurfaceImmersion.Correction.SmoothingTailBounds

namespace OAI

/-! Global smoothing estimates in the fixed finite atlas. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold MeasureTheory
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

/-- Global boundedness and smoothing gain use fixed chart constants and
no higher derivative of the true input. -/
theorem smoothing_bounds (r m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧
      (∀ (f : M → V) (s t C : ℝ), 0 < s → 0 < t → t ≤ 1 → 0 ≤ C →
        ContMDiff planeModel 𝓘(ℝ, V) ∞ f → A.WeightedBound t m C f →
        A.WeightedBound t m (D * (1 + (1 + ∫ y, ‖kernel 0 y‖) ^ r) * C) (A.smooth r s f)) ∧
      (∀ (f : M → V) (s t C : ℝ), 0 < s → s ≤ 1 → 0 ≤ C →
        ContMDiff planeModel 𝓘(ℝ, V) ∞ f → A.WeightedBound t 0 C f →
        A.WeightedBound s m (D * weightedGainConstant r m * C) (A.smooth r s f)) := by
  obtain ⟨D, hD, hd⟩ := A.restoration_bound (V := V) m
  refine ⟨D, hD, ?_, ?_⟩
  · intro f s t C hs ht ht1 hC hf hb
    have hnon : 0 ≤ (1 + (1 + ∫ y, ‖kernel 0 y‖) ^ r) * C := by positivity
    have h := hd (fun i => finiteSmooth r s (localize (i : M) (A.weight i) f)) t
      ((1 + (1 + ∫ y, ‖kernel 0 y‖) ^ r) * C) ht ht1 hnon
      (fun i => finiteSmooth_smooth r hs
        (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hf))
      (fun i => finiteSmooth_weighted_bounded r m hs ht
        (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hf)
        (localize_compact (i : M) (A.weight_support i) f) (hb i))
    simpa only [smooth, mul_assoc] using h
  · intro f s t C hs hs1 hC hf hb
    have h := hd (fun i => finiteSmooth r s (localize (i : M) (A.weight i) f)) s
      (weightedGainConstant r m * C) hs hs1
      (mul_nonneg (weightedGainConstant_nonneg r m) hC)
      (fun i => finiteSmooth_smooth r hs
        (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hf))
      (fun i => finiteSmooth_weighted_gain r m hs
        (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hf)
        (fun x => (hb i).norm_le (mem_univ x)))
    simpa only [smooth, mul_assoc] using h

variable [CompleteSpace V]

/-- The coordinate two-scale estimate survives finite atlas assembly. The
large higher input norm still occurs only linearly. -/
theorem smoothing_tail_bound (r m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : M → V) (s t τ B C : ℝ),
      0 < τ → τ ≤ s → s ≤ t → t ≤ 1 → 0 ≤ B → 0 ≤ C →
      ContMDiff planeModel 𝓘(ℝ, V) ∞ f →
      A.WeightedBound t r B f → A.WeightedBound t m C f →
      A.WeightedBound τ m
        (D * tailConstant r * (B * (s / t) ^ r + C * (τ / t) ^ r))
        (f - A.smooth r s f) := by
  obtain ⟨D, hD, hd⟩ := A.restoration_bound (V := V) m
  refine ⟨D, hD, ?_⟩
  intro f s t τ B C hτ hτs hst ht1 hB hC hf hb hc
  have hs : 0 < s := hτ.trans_le hτs
  have ht : 0 < t := hs.trans_le hst
  have hτ1 : τ ≤ 1 := hτs.trans (hst.trans ht1)
  have hsize : 0 ≤ tailConstant r * (B * (s / t) ^ r + C * (τ / t) ^ r) :=
    mul_nonneg (tailConstant_nonneg r) (add_nonneg
      (mul_nonneg hB (pow_nonneg (div_nonneg hs.le ht.le) _))
      (mul_nonneg hC (pow_nonneg (div_nonneg hτ.le ht.le) _)))
  have h := hd (fun i => residual s r (localize (i : M) (A.weight i) f)) τ
    (tailConstant r * (B * (s / t) ^ r + C * (τ / t) ^ r)) hτ hτ1 hsize
    (fun i => residual_smooth hs r
      (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hf))
    (fun i => by
      rw [← error_finiteSmooth]
      exact weighted_smoothing_tail r m hτ hτs hst
        (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hf)
        (localize_compact (i : M) (A.weight_support i) f) (hb i) (hc i))
  rw [A.sub_smooth_eq_error]
  simpa only [error, mul_assoc] using h

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
