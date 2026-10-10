import OAI.Geometry.ProjectionBody.GeometryDefinitions
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace OAI

open Set

namespace ProjectionCounterexample

noncomputable section

theorem simplex_convex (d : ℕ) : Convex ℝ (simplex d) :=
  convex_convexHull ℝ _

theorem simplex_compact (d : ℕ) : IsCompact (simplex d) :=
  ((finite_range _).insert 0).isCompact_convexHull ℝ

theorem simplex_interior_nonempty (d : ℕ) : (interior (simplex d)).Nonempty := by
  rw [(simplex_convex d).interior_nonempty_iff_affineSpan_eq_top]
  rw [simplex, affineSpan_convexHull]
  apply SetLike.coe_injective
  rw [affineSpan_insert_zero]
  have hb : (EuclideanSpace.basisFun (Fin d) ℝ : Fin d → E d) =
      (fun i : Fin d => EuclideanSpace.single i (1 : ℝ)) := by
    funext i
    simp only [EuclideanSpace.basisFun_apply]
  have hspan : Submodule.span ℝ (range fun i : Fin d => EuclideanSpace.single i (1 : ℝ)) = ⊤ := by
    simpa only [OrthonormalBasis.coe_toBasis, hb] using
      (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.span_eq
  exact congrArg (fun S : Submodule ℝ (E d) => (S : Set (E d))) hspan

theorem simplex_eq_coordinates (d : ℕ) :
    simplex d = {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1} := by
  classical
  apply Subset.antisymm
  · apply convexHull_min
    · rintro x (rfl | ⟨i, rfl⟩)
      · simp
      · constructor
        · intro j
          simp only [PiLp.single_apply]
          split_ifs
          · exact zero_le_one
          · exact le_rfl
        · simp [PiLp.single_apply]
    · intro x hx y hy a b ha hb hab
      constructor
      · intro i
        exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
      · change ∑ i, (a * x i + b * y i) ≤ 1
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        calc
          a * ∑ i, x i + b * ∑ i, y i ≤ a * 1 + b * 1 :=
            add_le_add (mul_le_mul_of_nonneg_left hx.2 ha)
              (mul_le_mul_of_nonneg_left hy.2 hb)
          _ = 1 := by simpa using hab
  · intro x hx
    let w : Option (Fin d) → ℝ := fun o =>
      match o with
      | none => 1 - ∑ i, x i
      | some i => x i
    let z : Option (Fin d) → E d := fun o =>
      match o with
      | none => 0
      | some i => EuclideanSpace.single i 1
    apply mem_convexHull_of_exists_fintype w z
    · intro o
      cases o with
      | none => exact sub_nonneg.mpr hx.2
      | some i => exact hx.1 i
    · simp [w, Fintype.sum_option]
    · intro o
      cases o with
      | none => exact mem_insert 0 _
      | some i => exact mem_insert_of_mem 0 (mem_range_self i)
    · simpa [w, z, Fintype.sum_option, EuclideanSpace.basisFun_apply] using
        (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr x

def blockEquiv : E 20 ≃L[ℝ] E 10 × E 10 :=
  EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 10) (m := 10)

theorem blockEquiv_apply (x : E 20) :
    blockEquiv x =
      (WithLp.toLp 2 fun i : Fin 10 => x (Fin.castAdd 10 i),
       WithLp.toLp 2 fun i : Fin 10 => x (Fin.natAdd 10 i)) := by
  rfl

theorem productBody_eq_preimage :
    productBody = blockEquiv ⁻¹' (simplex 10 ×ˢ simplex 10) := by
  rfl

theorem productBody_compact : IsCompact productBody := by
  rw [productBody_eq_preimage]
  exact blockEquiv.toHomeomorph.isCompact_preimage.mpr
    ((simplex_compact 10).prod (simplex_compact 10))

theorem productBody_convex : Convex ℝ productBody := by
  rw [productBody_eq_preimage]
  exact ((simplex_convex 10).prod (simplex_convex 10)).linear_preimage
    blockEquiv.toLinearMap

theorem productBody_interior_nonempty : (interior productBody).Nonempty := by
  rw [productBody_eq_preimage]
  change (interior (blockEquiv.toHomeomorph ⁻¹' (simplex 10 ×ˢ simplex 10))).Nonempty
  rw [← blockEquiv.toHomeomorph.preimage_interior, interior_prod_eq]
  obtain ⟨x, hx⟩ := simplex_interior_nonempty 10
  exact ⟨blockEquiv.symm (x, x), by simpa using And.intro hx hx⟩

theorem productBody_convexBody :
    IsCompact productBody ∧ Convex ℝ productBody ∧ (interior productBody).Nonempty :=
  ⟨productBody_compact, productBody_convex, productBody_interior_nonempty⟩

end

end ProjectionCounterexample

end OAI
