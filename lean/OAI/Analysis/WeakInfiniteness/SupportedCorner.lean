import Mathlib
import OAI.Analysis.WeakInfiniteness.RectangularPolar

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

variable {A : Type*} [NonUnitalCStarAlgebra A]

def supportedAlgebra (e : A) (he : IsSelfAdjoint e) : NonUnitalStarSubalgebra ℂ A where
  carrier := {z | e*z=z ∧ z*e=z}
  zero_mem' := by simp
  add_mem' hx hy := by
    change e*(_+_)=_ ∧ (_+_)*e=_
    simp only [mul_add, add_mul, hx.1, hx.2, hy.1, hy.2, and_self]
  mul_mem' hx hy := by
    constructor
    · rw [← mul_assoc, hx.1]
    · rw [mul_assoc, hy.2]
  smul_mem' c x hx := by
    change e*(c • x)=_ ∧ (c • x)*e=_
    simp only [mul_smul_comm, smul_mul_assoc, hx.1, hx.2, and_self]
  star_mem' hx := by
    constructor
    · simpa only [star_mul, he.star_eq] using congrArg star hx.2
    · simpa only [star_mul, he.star_eq] using congrArg star hx.1

lemma supportedAlgebra_closed (e : A) (he : IsSelfAdjoint e) :
    IsClosed (supportedAlgebra e he : Set A) :=
  (isClosed_eq (by fun_prop) continuous_id).inter (isClosed_eq (by fun_prop) continuous_id)

instance supportedAlgebra_complete (e : A) (he : IsSelfAdjoint e) :
    CompleteSpace (supportedAlgebra e he) := (supportedAlgebra_closed e he).completeSpace_coe

def matrixSingletonHom : CStarMatrix (Fin 1) (Fin 1) A →⋆ₙₐ[ℂ] A where
  toFun x := x 0 0
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl
  map_mul' x y := by
    change (∑ i : Fin 1, x 0 i*y i 0)=x 0 0*y 0 0
    exact Fin.sum_univ_one _

lemma matrixSingletonHom_injective : Function.Injective (matrixSingletonHom (A := A)) := by
  intro x y h
  ext i j
  have hi : i=0 := Subsingleton.elim _ _
  have hj : j=0 := Subsingleton.elim _ _
  subst i; subst j
  exact h

variable {n : Type*} [Fintype n]

lemma rectangular_mul_zero_support {m k : Type*} (M : CStarMatrix m n A) :
    M*(0 : CStarMatrix n k A)=0 := Matrix.mul_zero M

lemma rectangular_zero_mul_support {m k : Type*} (M : CStarMatrix n k A) :
    (0 : CStarMatrix m n A)*M=0 := Matrix.zero_mul M

lemma rectangular_mul_add_support {m k : Type*} (M : CStarMatrix m n A)
    (N P : CStarMatrix n k A) : M*(N+P)=M*N+M*P := Matrix.mul_add M N P

lemma rectangular_add_mul_support {m k : Type*} (M N : CStarMatrix m n A)
    (P : CStarMatrix n k A) : (M+N)*P=M*P+N*P := Matrix.add_mul M N P

lemma rectangular_mul_smul_support {m k : Type*} (M : CStarMatrix m n A)
    (c : ℂ) (N : CStarMatrix n k A) : M*(c • N)=c • (M*N) := Matrix.mul_smul M c N

lemma rectangular_smul_mul_support {m k : Type*} (M : CStarMatrix m n A)
    (c : ℂ) (N : CStarMatrix n k A) : (c • M)*N=c • (M*N) := Matrix.smul_mul c M N

variable [PartialOrder A] [StarOrderedRing A]

def supportedCompression (U : CStarMatrix (Fin 1) n A)
    (e : CStarMatrix n n A) (he : IsSelfAdjoint e) (hU : U.conjTranspose*U=e) :
    supportedAlgebra e he →⋆ₙₐ[ℂ] CStarMatrix (Fin 1) (Fin 1) A where
  toFun z := U*z.val*U.conjTranspose
  map_zero' := by change U*0*U.conjTranspose=0; rw [rectangular_mul_zero_support, rectangular_zero_mul_support]
  map_add' x y := by
    change U*(x.val+y.val)*U.conjTranspose=U*x.val*U.conjTranspose+U*y.val*U.conjTranspose
    rw [rectangular_mul_add_support, rectangular_add_mul_support]
  map_smul' c z := by
    change U*(c • z.val)*U.conjTranspose=c • (U*z.val*U.conjTranspose)
    rw [rectangular_mul_smul_support, rectangular_smul_mul_support]
  map_mul' x y := by
    change U*(x.val*y.val)*U.conjTranspose=(U*x.val*U.conjTranspose)*(U*y.val*U.conjTranspose)
    simp only [rectangular_mul_assoc]
    rw [← rectangular_mul_assoc U.conjTranspose U, hU,
      ← rectangular_mul_assoc e y.val, y.property.1]
  map_star' z := by
    change U*z.val.conjTranspose*U.conjTranspose=(U*z.val*U.conjTranspose).conjTranspose
    rw [rectangular_star_mul, rectangular_star_mul, rectangular_conjTranspose_conjTranspose,
      rectangular_mul_assoc]

lemma supportedCompression_inverse (U : CStarMatrix (Fin 1) n A)
    (e : CStarMatrix n n A) (he : IsSelfAdjoint e) (hU : U.conjTranspose*U=e)
    (z : supportedAlgebra e he) :
    U.conjTranspose*(supportedCompression U e he hU z)*U=z.val := by
  change U.conjTranspose*(U*z.val*U.conjTranspose)*U=z.val
  rw [← rectangular_mul_assoc, ← rectangular_mul_assoc, hU,
    rectangular_mul_assoc (e*z.val) U.conjTranspose U, hU, z.property.1, z.property.2]

lemma supportedCompression_injective (U : CStarMatrix (Fin 1) n A)
    (e : CStarMatrix n n A) (he : IsSelfAdjoint e) (hU : U.conjTranspose*U=e) :
    Function.Injective (supportedCompression U e he hU) := by
  intro x y h
  apply Subtype.ext
  rw [← supportedCompression_inverse U e he hU x, ← supportedCompression_inverse U e he hU y, h]

end

end WeakPureInfiniteness
end

end OAI
