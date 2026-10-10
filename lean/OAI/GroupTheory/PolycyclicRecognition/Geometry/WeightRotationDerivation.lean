import OAI.GroupTheory.PolycyclicRecognition.Geometry.RealRotationDerivation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RealCartanQuotient

namespace OAI

/-! # The infinitesimal rotation factors through the complex weight quotient -/

noncomputable section
namespace PolycyclicRecognition
open LieAlgebra LieModule Module
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : ComplexTriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

namespace ComplexTriangularAdjoint

/-- No infinitesimal rotation remains on a nilpotent Cartan parameter. -/
theorem realImaginaryOperator_eq_zero (h : H) (hh : T.weightMap (h : L) = 0) (x : L) :
    realImaginaryOperator L H h x = 0 := by
  have hn := complex_ad_nilpotent (h : L) (T.ad_nilpotent h hh)
  apply complexificationLieHom_injective L
  change (1 : ℂ) ⊗ₜ[ℝ] realImaginaryOperator L H h x = 1 ⊗ₜ[ℝ] (0 : L)
  rw [realImaginaryOperator_complexify,TensorProduct.tmul_zero]
  apply ComplexCartan.root_induction (complexifiedSubalgebra L H)
    (p := fun v => ComplexCartan.imaginaryOperator (complexifiedSubalgebra L H)
      (realCartanInComplex L H h) v = 0) (x := (1 : ℂ) ⊗ₜ[ℝ] x)
  · intro χ v hv
    rw [ComplexCartan.imaginaryOperator_apply _ _ χ hv]
    have hz := χ.apply_eq_zero_of_isNilpotent (realCartanInComplex L H h) hn
    rw [hz,map_zero,zero_smul]
  · simp
  · intro v w hv hw
    simp only [map_add,hv,hw,add_zero]

theorem realImaginaryOperator_eq_of_weightMap_eq (h k : H)
    (hh : T.weightMap (h : L) = T.weightMap (k : L)) (x : L) :
    realImaginaryOperator L H h x = realImaginaryOperator L H k x := by
  have hz : T.weightMap ((h-k : H) : L) = 0 := by
    change T.weightMap ((h : L) - k) = 0
    rw [map_sub,hh,sub_self]
  have he := realImaginaryOperator_add L H (h-k) k x
  rw [sub_add_cancel,T.realImaginaryOperator_eq_zero H (h-k) hz x,zero_add] at he
  exact he

/-- The infinitesimal imaginary action depends only on the actual weight
quotient; this is the derivative used in the rotational modification. -/
def weightImaginaryAction : L →ₗ[ℝ] LieDerivation ℝ L L :=
  (realImaginaryDerivationLinear L H).comp ((T.cartanWeightSection H).comp
    T.weightMap.rangeRestrict)

@[simp] theorem weightImaginaryAction_cartan (h : H) (x : L) :
    T.weightImaginaryAction H (h : L) x = realImaginaryOperator L H h x := by
  apply T.realImaginaryOperator_eq_of_weightMap_eq H
  exact T.cartanWeightSection_weight H _

@[simp] theorem weightImaginaryAction_kernel (x : L) (hx : T.weightMap x = 0) :
    T.weightImaginaryAction H x = 0 := by
  have he : T.weightMap.rangeRestrict x = 0 := Subtype.ext hx
  change realImaginaryDerivationLinear L H (T.cartanWeightSection H
    (T.weightMap.rangeRestrict x)) = 0
  rw [he,map_zero,map_zero]

@[simp] theorem weightImaginaryAction_lie (x y : L) :
    T.weightImaginaryAction H ⁅x,y⁆ = 0 :=
  T.weightImaginaryAction_kernel H _ (T.weightMap_lie x y)

/-- The infinitesimal rotation acts trivially on the whole weight quotient. -/
theorem weightMap_realImaginaryOperator (h : H) (x : L) :
    T.weightMap (realImaginaryOperator L H h x) = 0 := by
  rw [← T.complexWeightMap_one_tmul,realImaginaryOperator_complexify]
  apply ComplexCartan.root_induction (complexifiedSubalgebra L H)
    (p := fun v => T.complexWeightMap (ComplexCartan.imaginaryOperator
      (complexifiedSubalgebra L H) (realCartanInComplex L H h) v) = 0)
    (x := (1 : ℂ) ⊗ₜ[ℝ] x)
  · intro χ v hv
    rw [ComplexCartan.imaginaryOperator_apply _ _ χ hv,map_smul]
    by_cases hχ : (χ : complexifiedSubalgebra L H → ℂ) = 0
    · have hz : χ (realCartanInComplex L H h) = 0 := congrFun hχ _
      rw [hz,map_zero,zero_smul]
    · rw [T.complexWeightMap_root_zero H hχ hv,smul_zero]
  · simp
  · intro v w hv hw
    simp only [map_add,hv,hw,add_zero]

@[simp] theorem weightImaginaryAction_annihilate (x y : L) :
    T.weightImaginaryAction H (T.weightImaginaryAction H x y) = 0 := by
  apply T.weightImaginaryAction_kernel H
  exact T.weightMap_realImaginaryOperator H _ _

/-- The quotient derivations commute. -/
theorem weightImaginaryAction_commute (x y : L) :
    ⁅T.weightImaginaryAction H x,T.weightImaginaryAction H y⁆ = 0 := by
  ext z
  change realImaginaryOperator L H _ (realImaginaryOperator L H _ z) -
    realImaginaryOperator L H _ (realImaginaryOperator L H _ z) = 0
  rw [realImaginaryOperator_commute L H,sub_self]

end ComplexTriangularAdjoint
end PolycyclicRecognition

end

end OAI
