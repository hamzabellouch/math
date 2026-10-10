import OAI.Geometry.ProjectionVolume.Basic
import Mathlib.Analysis.Convex.Measure
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

namespace OAI

universe uE

noncomputable section

open Set MeasureTheory
open scoped RealInnerProductSpace Pointwise

namespace Paper092

theorem projection_finrank_le {d : ℕ} (S : Set (Euclidean d)) (u : Euclidean d) :
    Module.finrank ℝ (vectorSpan ℝ ((normalHyperplane u).orthogonalProjectionOnto '' S)) ≤
      Module.finrank ℝ (vectorSpan ℝ S) := by
  let p := (normalHyperplane u).orthogonalProjectionOnto.toLinearMap
  have h := Submodule.finrank_map_le p (vectorSpan ℝ S)
  have hmap : (vectorSpan ℝ S).map p =
      vectorSpan ℝ ((normalHyperplane u).orthogonalProjectionOnto '' S) :=
    p.toAffineMap.map_vectorSpan
  rwa [hmap] at h

theorem volume_eq_zero_of_finrank_vectorSpan_lt
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (S : Set E)
    (hS : Module.finrank ℝ (vectorSpan ℝ S) < Module.finrank ℝ E) :
    volume S = 0 := by
  have hspan : affineSpan ℝ S ≠ ⊤ := by
    intro h
    have htop := AffineSubspace.vectorSpan_eq_top_of_affineSpan_eq_top ℝ E E h
    rw [htop, finrank_top] at hS
    exact lt_irrefl _ hS
  exact measure_mono_null (subset_affineSpan ℝ S)
    (Measure.addHaar_affineSubspace volume (affineSpan ℝ S) hspan)

theorem projectionVolume_eq_zero_of_finrank_lt {d : ℕ} (S : Set (Euclidean d))
    {u : Euclidean d} (hu : u ≠ 0)
    (hS : Module.finrank ℝ (vectorSpan ℝ S) < d - 1) :
    projectionVolume S u = 0 := by
  apply volume_eq_zero_of_finrank_vectorSpan_lt
  rw [normalHyperplane_finrank u hu]
  exact lt_of_le_of_lt (projection_finrank_le S u) hS

theorem projection_finrank_le_of_parallel {d : ℕ} (S : Set (Euclidean d))
    {u ν : Euclidean d} (hu : u ≠ 0) (hν : ν ≠ 0) (hperp : ⟪u, ν⟫ = 0)
    (c : ℝ) (hS : ∀ x ∈ S, ⟪ν, x⟫ = c) :
    Module.finrank ℝ (vectorSpan ℝ ((normalHyperplane u).orthogonalProjectionOnto '' S)) ≤
      d - 2 := by
  let v : normalHyperplane u :=
    ⟨ν, Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hperp⟩
  have hv : v ≠ 0 := by
    intro h
    exact hν (congrArg Subtype.val h)
  let H := (Submodule.span ℝ ({v} : Set (normalHyperplane u)))ᗮ
  have hle : vectorSpan ℝ ((normalHyperplane u).orthogonalProjectionOnto '' S) ≤ H := by
    rw [vectorSpan_def]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    change ⟪v, (normalHyperplane u).orthogonalProjectionOnto x -
      (normalHyperplane u).orthogonalProjectionOnto y⟫ = 0
    rw [inner_sub_right,
      Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,
      Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
    exact sub_eq_zero.mpr ((hS x hx).trans (hS y hy).symm)
  have hrank := (Submodule.span ℝ ({v} : Set (normalHyperplane u))).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hv, normalHyperplane_finrank u hu] at hrank
  have hdim : Module.finrank ℝ H = d - 2 := by
    dsimp [H]
    omega
  exact hdim ▸ Submodule.finrank_mono hle

theorem projectionVolume_eq_zero_of_parallel {d : ℕ} (hd : 2 ≤ d)
    (S : Set (Euclidean d)) {u ν : Euclidean d} (hu : u ≠ 0) (hν : ν ≠ 0)
    (hperp : ⟪u, ν⟫ = 0) (c : ℝ) (hS : ∀ x ∈ S, ⟪ν, x⟫ = c) :
    projectionVolume S u = 0 := by
  apply volume_eq_zero_of_finrank_vectorSpan_lt
  rw [normalHyperplane_finrank u hu]
  exact lt_of_le_of_lt (projection_finrank_le_of_parallel S hu hν hperp c hS) (by omega)

theorem projection_boundary_volume_eq_zero {d : ℕ} (K : Set (Euclidean d))
    (hK : Convex ℝ K) (u : Euclidean d) :
    (volume : Measure (normalHyperplane u))
      (frontier ((normalHyperplane u).orthogonalProjectionOnto '' K)) = 0 := by
  exact (hK.linear_image (normalHyperplane u).orthogonalProjectionOnto.toLinearMap).addHaar_frontier
    volume

end Paper092

end

end OAI
