import OAI.Geometry.SurfaceImmersion.Correction.SmoothingLocalization
import OAI.Geometry.SurfaceImmersion.Correction.ManifoldFreeIncrement

namespace OAI

/-! Actual smoothing maps on a closed surface, assembled from a fixed atlas. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def restore (p : M) (χ : M → ℝ) (h : Base → V) : M → V :=
  (chart p).source.indicator (fun x => χ x • h (chart p x))

lemma restore_smooth (p : M) {χ : M → ℝ}
    (hχ : ContMDiff planeModel 𝓘(ℝ) ∞ χ)
    (hs : tsupport χ ⊆ (chart p).source) {h : Base → V} (hh : ContDiff ℝ ∞ h) :
    ContMDiff planeModel 𝓘(ℝ, V) ∞ (restore p χ h) := by
  apply (contMDiff_indicator_of_support (chart p).open_source
    (isClosed_tsupport χ) hs
    (hχ.contMDiffOn.smul (hh.contMDiff.comp_contMDiffOn (chart_smooth p))) ?_).1
  intro x _ hx
  change χ x • h (chart p x) = 0
  rw [image_eq_zero_of_notMem_tsupport hx, zero_smul]

omit [IsManifold planeModel ∞ M] in
lemma restore_sub (p : M) (χ : M → ℝ) (h k : Base → V) :
    restore p χ (h - k) = restore p χ h - restore p χ k := by
  funext x
  by_cases hx : x ∈ (chart p).source <;>
    simp [restore, hx, smul_sub]

namespace SmoothingAtlas

variable (A : SmoothingAtlas M)

/-- The actual global operator; no choice in its definition depends on `f`. -/
def smooth (r : ℕ) (s : ℝ) (f : M → V) : M → V :=
  ∑ i : A.centers, restore (i : M) (A.outer i) (finiteSmooth r s (localize (i : M) (A.weight i) f))

/-- The corresponding global error, written entirely in coordinate residuals. -/
def error (r : ℕ) (s : ℝ) (f : M → V) : M → V :=
  ∑ i : A.centers, restore (i : M) (A.outer i) (residual s r (localize (i : M) (A.weight i) f))

variable [CompactSpace M]

lemma smooth_smooth (r : ℕ) {s : ℝ} (hs : 0 < s) {f : M → V}
    (hf : ContMDiff planeModel 𝓘(ℝ, V) ∞ f) :
    ContMDiff planeModel 𝓘(ℝ, V) ∞ (A.smooth r s f) := by
  have heq : A.smooth r s f = fun x => ∑ i : A.centers,
      restore (i : M) (A.outer i) (finiteSmooth r s (localize (i : M) (A.weight i) f)) x := by
    funext x
    simp only [smooth, Finset.sum_apply]
  rw [heq]
  apply ContMDiff.sum
  intro i _
  exact restore_smooth (i : M) (A.outer_smooth i) (A.outer_support i)
    (finiteSmooth_smooth r hs (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hf))

omit [CompactSpace M] in
lemma restore_localize (i : A.centers) (f : M → V) (x : M) :
    restore (i : M) (A.outer i) (localize (i : M) (A.weight i) f) x =
      (A.weight i x) ^ 2 • f x := by
  by_cases hx : x ∈ (chart (i : M)).source
  · rw [restore, indicator_of_mem hx, localize_chart _ _ _ hx]
    by_cases hzero : A.weight i x = 0
    · simp only [hzero, zero_pow (by decide : 2 ≠ 0), zero_smul, smul_zero]
    · rw [A.outer_one i x (subset_tsupport _ hzero), one_smul]
  · have hz : A.weight i x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hx (A.weight_support i h))
    simp only [restore, indicator_of_notMem hx, hz, zero_pow (by decide : 2 ≠ 0), zero_smul]

omit [CompactSpace M] in
lemma sum_restore_localize (f : M → V) :
    (∑ i : A.centers, restore (i : M) (A.outer i) (localize (i : M) (A.weight i) f)) = f := by
  funext x
  simp only [Finset.sum_apply, A.restore_localize]
  rw [← Finset.sum_smul, A.partition, one_smul]

omit [CompactSpace M] in
/-- Global smoothing error is exactly the sum of the localized residuals.
This identity is the link for transporting the coordinate tail estimates. -/
lemma sub_smooth_eq_error (r : ℕ) (s : ℝ) (f : M → V) :
    f - A.smooth r s f = A.error r s f := by
  conv_lhs => lhs; rw [← A.sum_restore_localize f]
  unfold smooth error
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← restore_sub, error_finiteSmooth]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
