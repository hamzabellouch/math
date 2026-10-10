import OAI.Geometry.SurfaceImmersion.Correction.GlobalBundleSmoothing
import OAI.Geometry.SurfaceImmersion.Correction.GlobalShiftedSmoothing

namespace OAI

/-! Every smooth input has finite bounds at each fixed atlas order. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle WeightedEstimates
open JetPolynomial (Base)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma compact_smooth_bound {f : Base → F} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ WeightedBound univ 1 m C f := by
  classical
  have hb (j : ℕ) : ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ C :=
    (hc.iteratedFDeriv j).exists_bound_of_continuous (hf.continuous_iteratedFDeriv (by simp))
  choose C hC using hb
  refine ⟨∑ j ∈ Finset.range (m + 1), |C j|, Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  intro j hj x _
  simp only [one_pow, one_mul, iteratedFDerivWithin_univ]
  exact ((hC j x).trans (le_abs_self _)).trans
    (Finset.single_le_sum (s := Finset.range (m + 1)) (a := j)
      (fun k _ => abs_nonneg (C k)) (Finset.mem_range.mpr (by omega)))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

/-- Arbitrarily high map norms are finite; no uniform high-order input bound
is required for the eventual waiting argument. -/
theorem exists_shifted_bound (q m : ℕ) {f : M → F}
    (hf : ContMDiff planeModel 𝓘(ℝ, F) ∞ f) :
    ∃ C : ℝ, 0 ≤ C ∧ A.ShiftedBound q m 1 C f := by
  classical
  choose C hC hb using fun i : A.centers => compact_smooth_bound
    (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hf)
    (localize_compact (i : M) (A.weight_support i) f) (q + m)
  refine ⟨∑ i : A.centers, C i, Finset.sum_nonneg (fun i _ => hC i), ?_⟩
  intro i j hj x
  have h := hb i j hj x (mem_univ x)
  simp only [one_pow, one_mul, iteratedFDerivWithin_univ] at h ⊢
  exact h.trans (Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ i))

variable {E : M → Type*} [∀ x, TopologicalSpace (E x)]
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContMDiffVectorBundle ∞ F E planeModel]
variable (e : A.centers → Trivialization F (TotalSpace.proj : TotalSpace F E → M))
  [∀ i, MemTrivializationAtlas (e i)]
variable (hdomain : ∀ i : A.centers, (chart (i : M)).source ⊆ (e i).baseSet)
include hdomain

/-- Smooth tensor inputs likewise have finite localized bounds at every
fixed order, even when their high derivatives are large. -/
theorem exists_bundle_bound (m : ℕ) {u : ∀ x, E x}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, F)) ∞
      (fun x => TotalSpace.mk' F x (u x))) :
    ∃ C : ℝ, 0 ≤ C ∧ A.BundleWeightedBound e 1 m C u := by
  classical
  choose C hC hb using fun i : A.centers => compact_smooth_bound
    (A.bundleLocalize_smooth e hdomain i hu)
    (localize_compact (i : M) (A.weight_support i) _) m
  refine ⟨∑ i : A.centers, C i, Finset.sum_nonneg (fun i _ => hC i), ?_⟩
  intro i
  exact (hb i).mono_const (Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ i))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
