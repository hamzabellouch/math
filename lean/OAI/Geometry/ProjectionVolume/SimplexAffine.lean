import OAI.Geometry.ProjectionVolume.SimplexValue
import OAI.Geometry.ProjectionVolume.AffineCovariance
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

namespace OAI

open Set Module
open scoped Pointwise

namespace Paper092

theorem simplex_eq_vadd_linearEquiv_image {n : ℕ}
    (s : Affine.Simplex ℝ (Euclidean n) n) :
    ∃ (L : Euclidean n ≃ₗ[ℝ] Euclidean n) (v : Euclidean n),
      convexHull ℝ (range s.points) = v +ᵥ (L '' standardSimplex n) := by
  let b : AffineBasis (Fin (n + 1)) ℝ (Euclidean n) :=
    ⟨s.points, s.independent, s.affineSpan_eq_top (by simp)⟩
  let edgeBasis : Basis (Fin n) ℝ (Euclidean n) :=
    (b.basisOf 0).reindex (finSuccAboveEquiv 0).symm
  let L : Euclidean n ≃ₗ[ℝ] Euclidean n :=
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.equiv edgeBasis (Equiv.refl _)
  have hL (i : Fin n) : L (EuclideanSpace.single i 1) =
      s.points i.succ - s.points 0 := by
    change (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.equiv edgeBasis (Equiv.refl _)
      (EuclideanSpace.single i 1) = _
    rw [← EuclideanSpace.basisFun_apply]
    change (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.equiv edgeBasis (Equiv.refl _)
      ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis i) = _
    rw [Basis.equiv_apply]
    simp [edgeBasis, b, finSuccAboveEquiv_apply, vsub_eq_sub]
    rfl
  let f : Euclidean n ≃ᵃ[ℝ] Euclidean n :=
    AffineEquiv.ofLinearEquiv L 0 (s.points 0)
  have hf0 : f 0 = s.points 0 := by simp [f]
  have hfi (i : Fin n) : f (EuclideanSpace.single i 1) = s.points i.succ := by
    simp [f, hL, vsub_eq_sub, vadd_eq_add]
  have hf : f '' standardSimplex n = convexHull ℝ (range s.points) := by
    change f.toAffineMap '' convexHull ℝ _ = _
    rw [f.toAffineMap.image_convexHull]
    congr 1
    change f '' insert (0 : Euclidean n) (range (fun i : Fin n =>
      EuclideanSpace.single i (1 : ℝ))) = _
    rw [image_insert_eq, ← range_comp, hf0]
    have hfun : f ∘ (fun i : Fin n => EuclideanSpace.single i (1 : ℝ)) =
        Fin.tail s.points := funext hfi
    rw [hfun]
    exact (Fin.range_fin_succ s.points).symm
  refine ⟨L, s.points 0, hf.symm.trans ?_⟩
  rw [← image_vadd, image_image]
  congr 1
  funext x
  simp [f, vsub_eq_sub, vadd_eq_add, add_comm]

theorem simplex_is_convex_body {n : ℕ} (s : Affine.Simplex ℝ (Euclidean n) n) :
    IsCompact (convexHull ℝ (range s.points)) ∧
      Convex ℝ (convexHull ℝ (range s.points)) ∧
      (interior (convexHull ℝ (range s.points))).Nonempty := by
  exact ⟨(finite_range s.points).isCompact_convexHull ℝ, convex_convexHull ℝ _,
    interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr (s.affineSpan_eq_top (by simp))⟩

theorem simplex_normalizedProjectionVolume {n : ℕ} (hn : 0 < n)
    (s : Affine.Simplex ℝ (Euclidean n) n) :
    normalizedProjectionVolume (convexHull ℝ (range s.points)) = simplexConstant n := by
  obtain ⟨L, v, hs⟩ := simplex_eq_vadd_linearEquiv_image s
  rw [hs]
  exact standardSimplex_affine_image_normalizedProjectionVolume hn L v

end Paper092

end OAI
