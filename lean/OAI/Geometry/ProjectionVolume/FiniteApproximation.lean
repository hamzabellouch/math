import OAI.Geometry.ProjectionVolume.Basic
import OAI.Geometry.ProjectionVolume.SupportGeometry
import OAI.Geometry.ProjectionVolume.Brightness
import Mathlib.Analysis.Normed.Affine.Convex

namespace OAI

open Set Metric Filter
open scoped Pointwise Topology RealInnerProductSpace

namespace Paper092

theorem convex_smul_subset_interior {n : ℕ} {K : Set (Euclidean n)}
    (hK : Convex ℝ K) (h0 : (0 : Euclidean n) ∈ interior K)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) : r • K ⊆ interior K := by
  rintro _ ⟨x, hx, rfl⟩
  simpa only [smul_zero, add_zero] using
    hK.combo_self_interior_mem_interior hx h0 hr (sub_pos.mpr hr1) (add_sub_cancel _ _)

theorem exists_inscribed_finset_sandwich {n : ℕ} {K : Set (Euclidean n)}
    (hc : IsCompact K) (hv : Convex ℝ K) (h0 : (0 : Euclidean n) ∈ interior K)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    ∃ t : Finset (Euclidean n),
      r • K ⊆ interior (convexHull ℝ (t : Set (Euclidean n))) ∧
      convexHull ℝ (t : Set (Euclidean n)) ⊆ K ∧
      (0 : Euclidean n) ∈ interior (convexHull ℝ (t : Set (Euclidean n))) := by
  obtain ⟨t, ht, htK⟩ := (hv.smul r).exists_subset_interior_convexHull_finset_of_isCompact
    (hc.smul r) (mem_nhdsSet_iff_exists.mpr
      ⟨interior K, isOpen_interior, convex_smul_subset_interior hv h0 hr hr1, interior_subset⟩)
  refine ⟨t, ht, htK, ht ?_⟩
  exact ⟨0, interior_subset h0, smul_zero r⟩

theorem support_mono {n : ℕ} {A B : Set (Euclidean n)}
    (hne : A.Nonempty) (hc : IsCompact B) (h : A ⊆ B) (u : Euclidean n) :
    SupportGeometry.support A (innerSL ℝ u) ≤
      SupportGeometry.support B (innerSL ℝ u) :=
  SupportGeometry.support_le hne _ fun _ hx => SupportGeometry.le_support hc _ (h hx)

theorem projectionBody_support_le {n : ℕ} (K : Set (Euclidean n)) (u : Euclidean n) :
    SupportGeometry.support (projectionBody K) (innerSL ℝ u) ≤ brightness K u :=
  SupportGeometry.support_le ⟨0, zero_mem_projectionBody K⟩ _ fun _ hx => hx u

end Paper092

end OAI
