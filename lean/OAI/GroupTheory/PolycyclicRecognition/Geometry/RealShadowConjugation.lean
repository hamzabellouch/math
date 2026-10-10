import OAI.GroupTheory.PolycyclicRecognition.Geometry.RealShadowCartan
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ConjugationFlow
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RealNormedLieAlgebra

namespace OAI

/-! # The corrected Cartan action in a representation of the real shadow -/

noncomputable section
namespace PolycyclicRecognition
open LieAlgebra
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L A : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  {a : ℕ} (T : ComplexTriangularAdjoint L a)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

def cartanAdjointCLM (h : H) : L →L[ℝ] L :=
  LinearMap.toContinuousLinearMap (ad ℝ L (h : L))

def cartanImaginaryCLM (h : H) : L →L[ℝ] L :=
  (realImaginaryOperator L H h).toContinuousLinearMap

theorem cartan_correction_exp (h : H) :
    NormedSpace.exp (-cartanImaginaryCLM H h) * NormedSpace.exp (cartanAdjointCLM H h) =
      NormedSpace.exp (cartanAdjointCLM H h - cartanImaginaryCLM H h) := by
  let : NormedAlgebra ℚ (L →L[ℝ] L) := NormedAlgebra.restrictScalars ℚ ℝ _
  have hc : Commute (-cartanImaginaryCLM H h) (cartanAdjointCLM H h) := by
    apply ContinuousLinearMap.ext
    intro x
    have he := LinearMap.congr_fun (realImaginaryOperator_commutes_ad (L := L) H h).eq x
    change realImaginaryOperator L H h ⁅(h : L),x⁆ =
      ⁅(h : L),realImaginaryOperator L H h x⁆ at he
    change -(realImaginaryOperator L H h ⁅(h : L),x⁆) =
      ⁅(h : L),-realImaginaryOperator L H h x⁆
    rw [he, lie_neg]
  rw [← NormedSpace.exp_add_of_commute hc]
  congr 1
  abel

/-- The original Cartan action followed by inverse rotation becomes ordinary
matrix conjugation in every representation of the real-shadow algebra. -/
theorem realShadow_representation_corrected_action
    (j : CartanRealShadow T H →ₗ⁅ℝ⁆ A) (h : H) (y : L) :
    j (cartanRealShadowEquiv T H
      ((NormedSpace.exp (-cartanImaginaryCLM H h))
        ((NormedSpace.exp (cartanAdjointCLM H h)) y))) =
      NormedSpace.exp (j (cartanRealShadowEquiv T H h)) *
        j (cartanRealShadowEquiv T H y) *
          NormedSpace.exp (-j (cartanRealShadowEquiv T H h)) := by
  let J : L →L[ℝ] A :=
    (j.toLinearMap.comp (cartanRealShadowEquiv T H).toLinearMap).toContinuousLinearMap
  let S := cartanAdjointCLM H h - cartanImaginaryCLM H h
  have hinter (x : L) : J (S x) =
      adjointOperator (j (cartanRealShadowEquiv T H h)) (J x) := by
    have he : cartanRealShadowEquiv T H (S x) =
        ⁅cartanRealShadowEquiv T H h,cartanRealShadowEquiv T H x⁆ := by
      apply (cartanRealShadowEquiv T H).symm.injective
      rw [(cartanRealShadowEquiv T H).symm_apply_apply, cartanRealShadow_bracket,
        T.weightImaginaryAction_cartan, weightImaginaryAction_apply_cartan, add_zero]
      rfl
    change j (cartanRealShadowEquiv T H (S x)) = _
    rw [he]
    exact j.map_lie _ _
  have hh := exp_intertwine_apply J S
    (adjointOperator (j (cartanRealShadowEquiv T H h))) hinter y
  have hprod := congrArg (fun D : L →L[ℝ] L => J (D y)) (cartan_correction_exp H h)
  exact hprod.trans (hh.trans (exp_adjointOperator_apply _ _))

end PolycyclicRecognition

end

end OAI
