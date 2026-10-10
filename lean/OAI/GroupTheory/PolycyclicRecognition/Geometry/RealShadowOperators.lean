import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRealDiagonal
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRealShadowSolvable

namespace OAI

/-! # The triangular operator underlying the real shadow adjoint action -/

noncomputable section
namespace PolycyclicRecognition
open LieAlgebra Module
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : ComplexTriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

namespace ComplexTriangularAdjoint

def weightCorrectedOperator (x : L) : Module.End ℝ L :=
  ad ℝ L x - (T.weightImaginaryAction H x).toLinearMap

def complexWeightCorrectedOperator (x : L) : Module.End ℂ (ℂ ⊗[ℝ] L) :=
  ad ℂ (ℂ ⊗[ℝ] L) (complexificationLieHom L x) -
    ComplexCartan.imaginaryOperator (complexifiedSubalgebra L H)
      (realCartanInComplex L H (T.cartanWeightSection H (T.weightMap.rangeRestrict x)))

theorem weightCorrectedOperator_complexify (x : L) :
    (T.weightCorrectedOperator H x).baseChange ℂ = T.complexWeightCorrectedOperator H x := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul c y =>
    change c ⊗ₜ[ℝ] (⁅x,y⁆ - realImaginaryOperator L H _ y) = _
    rw [TensorProduct.tmul_sub]
    change _ = ⁅(1 : ℂ) ⊗ₜ[ℝ] x,c ⊗ₜ[ℝ] y⁆ -
      ComplexCartan.imaginaryOperator (complexifiedSubalgebra L H) _ (c ⊗ₜ[ℝ] y)
    have he : c ⊗ₜ[ℝ] y = c • ((1 : ℂ) ⊗ₜ[ℝ] y) := by
      rw [TensorProduct.smul_tmul',smul_eq_mul,mul_one]
    rw [he,map_smul,← realImaginaryOperator_complexify,
      TensorProduct.smul_tmul',smul_eq_mul,mul_one]
    simp only [LieAlgebra.ExtendScalars.bracket_tmul,one_mul,
      TensorProduct.smul_tmul',smul_eq_mul,mul_one,LinearMap.comp_apply]
  | add z w hz hw => simp only [map_add,hz,hw]

theorem complexWeightCorrectedOperator_upper (x : L) :
    (LinearMap.toMatrix T.basis T.basis (T.complexWeightCorrectedOperator H x)).IsUpperTriangular := by
  unfold complexWeightCorrectedOperator
  rw [map_sub]
  apply (T.upper _).sub
  exact ComplexCartan.imaginaryOperator_upper (complexifiedSubalgebra L H) T.basis _
    (T.upper _)

/-- The corrected operator has real diagonal in the original complex flag. -/
theorem complexWeightCorrectedOperator_diagonal_im (x : L) (i : Fin n) :
    (LinearMap.toMatrix T.basis T.basis (T.complexWeightCorrectedOperator H x) i i).im = 0 := by
  let h := T.cartanWeightSection H (T.weightMap.rangeRestrict x)
  have he : T.weightMap (h : L) = T.weightMap x := T.cartanWeightSection_weight H _
  have hei := congrFun he i
  change LinearMap.toMatrix T.basis T.basis
      (ad ℂ (ℂ ⊗[ℝ] L) ((1 : ℂ) ⊗ₜ[ℝ] (h : L))) i i =
    LinearMap.toMatrix T.basis T.basis
      (ad ℂ (ℂ ⊗[ℝ] L) ((1 : ℂ) ⊗ₜ[ℝ] x)) i i at hei
  change (LinearMap.toMatrix T.basis T.basis
    (ad ℂ (ℂ ⊗[ℝ] L) ((1 : ℂ) ⊗ₜ[ℝ] x) -
      ComplexCartan.imaginaryOperator (complexifiedSubalgebra L H)
        (realCartanInComplex L H h)) i i).im = 0
  rw [map_sub,Matrix.sub_apply,
    ComplexCartan.imaginaryOperator_diagonal (complexifiedSubalgebra L H) T.basis _ (T.upper _)]
  change (_ - ComplexCartan.imaginaryPart
    (LinearMap.toMatrix T.basis T.basis
      (ad ℂ (ℂ ⊗[ℝ] L) ((1 : ℂ) ⊗ₜ[ℝ] (h : L))) i i)).im = 0
  rw [hei]
  simp [ComplexCartan.imaginaryPart]

end ComplexTriangularAdjoint
end PolycyclicRecognition

end

end OAI
