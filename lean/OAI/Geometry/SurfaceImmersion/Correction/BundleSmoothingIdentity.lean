import OAI.Geometry.SurfaceImmersion.Correction.BundleSmoothing

namespace OAI

/-! Exact reconstruction and error identities for bundle smoothing. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {E : M → Type*} [∀ x, TopologicalSpace (E x)]
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)
variable (e : A.centers → Trivialization F (TotalSpace.proj : TotalSpace F E → M))
  [∀ i, MemTrivializationAtlas (e i)]

lemma bundleRestore_sub (i : A.centers) (f g : Base → F) (x : M) :
    A.bundleRestore e i (f - g) x = A.bundleRestore e i f x - A.bundleRestore e i g x := by
  simp only [bundleRestore, Pi.sub_apply, map_sub, smul_sub]

variable (hdomain : ∀ i : A.centers, (chart (i : M)).source ⊆ (e i).baseSet)
include hdomain

lemma bundleRestore_localize (i : A.centers) (u : ∀ x, E x) (x : M) :
    A.bundleRestore e i (A.bundleLocalize e i u) x = (A.weight i x) ^ 2 • u x := by
  by_cases hx : x ∈ (chart (i : M)).source
  · rw [bundleRestore, bundleLocalize, localize_chart _ _ _ hx, bundleComponent, map_smul,
      (e i).symmL_continuousLinearMapAt (hdomain i hx)]
    by_cases hz : A.weight i x = 0
    · simp [hz]
    · rw [A.outer_one i x (subset_tsupport _ hz), one_smul]
  · have ho : A.outer i x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hx (A.outer_support i h))
    have hw : A.weight i x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hx (A.weight_support i h))
    simp only [bundleRestore, ho, hw, zero_smul, zero_pow (by decide : 2 ≠ 0)]

lemma bundle_sum_restore_localize (u : ∀ x, E x) (x : M) :
    (∑ i : A.centers, A.bundleRestore e i (A.bundleLocalize e i u) x) = u x := by
  simp_rw [A.bundleRestore_localize e hdomain]
  rw [← Finset.sum_smul, A.partition x, one_smul]

/-- The smoothing tail is exactly the finite restoration of coordinate tails. -/
theorem bundle_smoothing_error (r : ℕ) (s : ℝ) (u : ∀ x, E x) (x : M) :
    u x - A.bundleSmooth e r s u x =
      ∑ i : A.centers, A.bundleRestore e i (residual s r (A.bundleLocalize e i u)) x := by
  rw [← A.bundle_sum_restore_localize e hdomain u x]
  unfold bundleSmooth
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← A.bundleRestore_sub, ← error_finiteSmooth]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
