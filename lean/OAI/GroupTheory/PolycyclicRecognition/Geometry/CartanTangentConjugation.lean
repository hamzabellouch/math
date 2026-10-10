import OAI.GroupTheory.PolycyclicRecognition.Geometry.RealPhaseExponential
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RealShadowConjugation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntrinsicAdjointExponential

namespace OAI

/-! # The corrected adjoint in the original tangent coordinates -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  {a : ℕ} (T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a)
  (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)) [H.IsCartanSubalgebra]

theorem realShadow_representation_rotated_adjoint
    {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G} (hExp : IsGroupExponential Exp)
    (j : CartanRealShadow T H →ₗ⁅ℝ⁆ A) (h : H)
    (y : GroupLieAlgebra (𝓘(ℝ,E)) G) :
    j (cartanRealShadowEquiv T H
      (realTorusOperator (GroupLieAlgebra (𝓘(ℝ,E)) G) H
        (realPhaseVector (GroupLieAlgebra (𝓘(ℝ,E)) G) H h)⁻¹
        (adjointLinearMap (E := E) (Exp h) y))) =
      NormedSpace.exp (j (cartanRealShadowEquiv T H h)) *
        j (cartanRealShadowEquiv T H y) *
          NormedSpace.exp (-j (cartanRealShadowEquiv T H h)) := by
  let L := GroupLieAlgebra (𝓘(ℝ,E)) G
  let J : E →L[ℝ] A := (show E →ₗ[ℝ] A from
    j.toLinearMap.comp (cartanRealShadowEquiv T H).toLinearMap).toContinuousLinearMap
  let B := groupAdjointOperator (E := E) (G := G) h
  let C := tangentImaginaryOperator H h
  let S := B - C
  have hinter (x : E) : J (S x) =
      adjointOperator (j (cartanRealShadowEquiv T H h)) (J x) := by
    have hb : cartanRealShadowEquiv T H (S x) =
        ⁅cartanRealShadowEquiv T H h,cartanRealShadowEquiv T H x⁆ := by
      let z : L := x
      change cartanRealShadowEquiv T H
          (⁅(h : L), z⁆ - realImaginaryOperator L H h z) =
        ⁅cartanRealShadowEquiv T H h, cartanRealShadowEquiv T H z⁆
      apply (cartanRealShadowEquiv T H).symm.injective
      rw [(cartanRealShadowEquiv T H).symm_apply_apply, cartanRealShadow_bracket,
        T.weightImaginaryAction_cartan, weightImaginaryAction_apply_cartan, add_zero]
    change j (cartanRealShadowEquiv T H (S x)) = _
    rw [hb]
    exact j.map_lie _ _
  have hc : Commute C B := by
    ext x
    have hh := LinearMap.congr_fun (realImaginaryOperator_commutes_ad (L := L) H h).eq x
    exact hh
  have hprod : NormedSpace.exp (-C) * NormedSpace.exp B = NormedSpace.exp S := by
    let : NormedAlgebra ℚ (E →L[ℝ] E) := NormedAlgebra.restrictScalars ℚ ℝ _
    rw [← NormedSpace.exp_add_of_commute hc.neg_left]
    congr 1
    dsimp only [S]
    abel
  have ha := adjointLinearMap_exponential hExp (h : L) 1
  simp only [one_smul] at ha
  have hp := tangentPhase_inv_eq_exp H h
  change j (cartanRealShadowEquiv T H
    ((tangentTorusUnitAction H (realPhaseVector L H h)⁻¹ : E →L[ℝ] E)
      (adjointLinearMap (E := E) (Exp h) y))) = _
  rw [hp, ha]
  have he := congrArg (fun D : E →L[ℝ] E => J (D y)) hprod
  exact he.trans ((exp_intertwine_apply J S _ hinter y).trans
    (exp_adjointOperator_apply _ _))

end PolycyclicRecognition

end

end OAI
