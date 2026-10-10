import OAI.Geometry.ProjectionVolume.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Convex.Topology
import Mathlib.MeasureTheory.Measure.OpenPos

namespace OAI

noncomputable section

open Set MeasureTheory

namespace Paper092

theorem standardSimplex_isCompact (n : ℕ) : IsCompact (standardSimplex n) :=
  ((Set.finite_range _).insert 0).isCompact_convexHull ℝ

theorem standardSimplex_convex (n : ℕ) : Convex ℝ (standardSimplex n) :=
  convex_convexHull ℝ _

theorem standardSimplex_interior_nonempty (n : ℕ) :
    (interior (standardSimplex n)).Nonempty := by
  apply interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr
  have hspan : Submodule.span ℝ
      (range fun i : Fin n => EuclideanSpace.single i (1 : ℝ)) = ⊤ := by
    have hfun : (fun i : Fin n => EuclideanSpace.single i (1 : ℝ)) =
        (EuclideanSpace.basisFun (Fin n) ℝ).toBasis := by
      funext i
      simp
    rw [hfun]
    exact (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.span_eq
  apply SetLike.coe_injective
  rw [affineSpan_insert_zero, hspan]
  rfl

def splitBlocks : Euclidean 20 ≃L[ℝ] Euclidean 10 × Euclidean 10 :=
  (((WithLp.linearEquiv 2 ℝ (Fin 20 → ℝ)).trans
      (LinearEquiv.piCongrLeft ℝ (fun _ : Fin 20 => ℝ)
        (finSumFinEquiv : Fin 10 ⊕ Fin 10 ≃ Fin 20)).symm).trans
      (LinearEquiv.sumArrowLequivProdArrow (Fin 10) (Fin 10) ℝ ℝ) |>.trans
      (LinearEquiv.prodCongr (WithLp.linearEquiv 2 ℝ (Fin 10 → ℝ)).symm
        (WithLp.linearEquiv 2 ℝ (Fin 10 → ℝ)).symm)).toContinuousLinearEquiv

theorem splitBlocks_apply (x : Euclidean 20) :
    splitBlocks x = (firstBlock x, secondBlock x) := rfl

theorem productWitness_eq_preimage :
    productWitness = splitBlocks ⁻¹' (standardSimplex 10 ×ˢ standardSimplex 10) := rfl

theorem productWitness_isCompact : IsCompact productWitness := by
  rw [productWitness_eq_preimage]
  exact splitBlocks.toHomeomorph.isCompact_preimage.mpr
    ((standardSimplex_isCompact 10).prod (standardSimplex_isCompact 10))

theorem productWitness_convex : Convex ℝ productWitness := by
  rw [productWitness_eq_preimage]
  exact ((standardSimplex_convex 10).prod (standardSimplex_convex 10)).linear_preimage
    splitBlocks.toLinearMap

theorem productWitness_interior_nonempty : (interior productWitness).Nonempty := by
  rw [productWitness_eq_preimage]
  change (interior (splitBlocks.toHomeomorph ⁻¹'
    (standardSimplex 10 ×ˢ standardSimplex 10))).Nonempty
  rw [← splitBlocks.toHomeomorph.preimage_interior, interior_prod_eq]
  exact ((standardSimplex_interior_nonempty 10).prod
    (standardSimplex_interior_nonempty 10)).preimage splitBlocks.surjective

theorem productWitness_is_convex_body :
    IsCompact productWitness ∧ Convex ℝ productWitness ∧ (interior productWitness).Nonempty :=
  ⟨productWitness_isCompact, productWitness_convex, productWitness_interior_nonempty⟩

theorem productWitness_volume_pos : 0 < (volume productWitness).toReal :=
  ENNReal.toReal_pos (ne_of_gt (Measure.measure_pos_of_nonempty_interior volume
    productWitness_interior_nonempty)) productWitness_isCompact.measure_lt_top.ne

end Paper092

end

end OAI
