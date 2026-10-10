import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.TraceCone.Weights
import OAI.Analysis.JiangSu.CStarAlgebras.FourEdgeGroupSurgery

namespace OAI


noncomputable section
namespace TensorSliceSeparation
open scoped TensorProduct

variable {A B I : Type*} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B]

def slice (f : A →ₗ[ℂ] ℂ) : A ⊗[ℂ] B →ₗ[ℂ] B :=
  (TensorProduct.lid ℂ B).toLinearMap.comp
    (TensorProduct.map f (LinearMap.id : B →ₗ[ℂ] B))
@[simp] lemma slice_tmul (f : A →ₗ[ℂ] ℂ) (a : A) (b : B) :
    slice f (a ⊗ₜ[ℂ] b)=f a • b := rfl

lemma tensor_eq_zero_of_slices (f : I → A →ₗ[ℂ] ℂ)
    (hf : ∀ a,(∀ i,f i a=0) → a=0) (z : A ⊗[ℂ] B)
    (hz : ∀ i,slice (f i) z=0) : z=0 := by
  classical
  let b := Module.Basis.ofVectorSpace ℂ B
  let e := TensorProduct.equivFinsuppOfBasisRight (M := A) b
  apply e.injective
  simp only [map_zero]
  apply Finsupp.ext
  intro k
  change e z k=0
  apply hf
  intro i
  have he : ∀ z : A ⊗[ℂ] B,f i (e z k)=b.repr (slice (f i) z) k := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul a c =>
      simp only [e,TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply,
        map_smul,slice_tmul,Finsupp.smul_apply,smul_eq_mul]
      exact mul_comm _ _
    | add v w hv hw => simp only [map_add,Finsupp.add_apply,hv,hw]
  rw [he,hz,map_zero,Finsupp.zero_apply]

variable {J : Type*}
lemma tensor_eq_zero_of_double_slices (f : I → A →ₗ[ℂ] ℂ)
    (g : J → B →ₗ[ℂ] ℂ)
    (hf : ∀ a,(∀ i,f i a=0) → a=0)
    (hg : ∀ b,(∀ j,g j b=0) → b=0) (z : A ⊗[ℂ] B)
    (hz : ∀ i j,g j (slice (f i) z)=0) : z=0 := by
  apply tensor_eq_zero_of_slices f hf z
  intro i
  exact hg _ (hz i)

end TensorSliceSeparation

end


noncomputable section
namespace MatrixTensor
open scoped Kronecker

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
abbrev Mat (I : Type*) := CStarMatrix I I ℂ

def left : Mat I →⋆ₐ[ℂ] Mat (I×J) where
  toFun x := CStarMatrix.ofMatrix (CStarMatrix.ofMatrix.symm x ⊗ₖ (1 : Matrix J J ℂ))
  map_one' := Matrix.one_kronecker_one
  map_zero' := Matrix.zero_kronecker _
  map_add' x y := Matrix.add_kronecker _ _ _
  map_mul' x y := by
    change (CStarMatrix.ofMatrix.symm x*CStarMatrix.ofMatrix.symm y) ⊗ₖ
      (1 : Matrix J J ℂ)=(CStarMatrix.ofMatrix.symm x ⊗ₖ (1 : Matrix J J ℂ))*
      (CStarMatrix.ofMatrix.symm y ⊗ₖ (1 : Matrix J J ℂ))
    simpa only [Matrix.one_mul] using Matrix.mul_kronecker_mul
      (CStarMatrix.ofMatrix.symm x) (CStarMatrix.ofMatrix.symm y) (1 : Matrix J J ℂ) 1
  commutes' z := by
    ext ⟨i,j⟩ ⟨k,l⟩
    by_cases hik : i=k <;> by_cases hjl : j=l <;>
      simp [CStarMatrix.algebraMap_apply,Matrix.kroneckerMap_apply,hik,hjl]
  map_star' x := by
    change (CStarMatrix.ofMatrix.symm x).conjTranspose ⊗ₖ (1 : Matrix J J ℂ)=
      (CStarMatrix.ofMatrix.symm x ⊗ₖ (1 : Matrix J J ℂ)).conjTranspose
    simpa only [Matrix.conjTranspose_one] using
      (Matrix.conjTranspose_kronecker (CStarMatrix.ofMatrix.symm x) (1 : Matrix J J ℂ)).symm

def right : Mat J →⋆ₐ[ℂ] Mat (I×J) where
  toFun x := CStarMatrix.ofMatrix ((1 : Matrix I I ℂ) ⊗ₖ CStarMatrix.ofMatrix.symm x)
  map_one' := Matrix.one_kronecker_one
  map_zero' := Matrix.kronecker_zero _
  map_add' x y := Matrix.kronecker_add _ _ _
  map_mul' x y := by
    change (1 : Matrix I I ℂ) ⊗ₖ (CStarMatrix.ofMatrix.symm x*CStarMatrix.ofMatrix.symm y)=
      ((1 : Matrix I I ℂ) ⊗ₖ CStarMatrix.ofMatrix.symm x)*
      ((1 : Matrix I I ℂ) ⊗ₖ CStarMatrix.ofMatrix.symm y)
    simpa only [Matrix.one_mul] using Matrix.mul_kronecker_mul
      (1 : Matrix I I ℂ) 1 (CStarMatrix.ofMatrix.symm x) (CStarMatrix.ofMatrix.symm y)
  commutes' z := by
    ext ⟨i,j⟩ ⟨k,l⟩
    by_cases hik : i=k <;> by_cases hjl : j=l <;>
      simp [CStarMatrix.algebraMap_apply,Matrix.kroneckerMap_apply,hik,hjl]
  map_star' x := by
    change (1 : Matrix I I ℂ) ⊗ₖ (CStarMatrix.ofMatrix.symm x).conjTranspose=
      ((1 : Matrix I I ℂ) ⊗ₖ CStarMatrix.ofMatrix.symm x).conjTranspose
    simpa only [Matrix.conjTranspose_one] using
      (Matrix.conjTranspose_kronecker (1 : Matrix I I ℂ) (CStarMatrix.ofMatrix.symm x)).symm

lemma left_mul_right (a : Mat I) (b : Mat J) :
    left (J := J) a*right (I := I) b=CStarMatrix.ofMatrix (CStarMatrix.ofMatrix.symm a ⊗ₖ
      CStarMatrix.ofMatrix.symm b) := by
  change ((CStarMatrix.ofMatrix.symm a) ⊗ₖ (1 : Matrix J J ℂ))*
    ((1 : Matrix I I ℂ) ⊗ₖ CStarMatrix.ofMatrix.symm b)=
    CStarMatrix.ofMatrix.symm a ⊗ₖ CStarMatrix.ofMatrix.symm b
  simpa only [Matrix.mul_one,Matrix.one_mul] using
    (Matrix.mul_kronecker_mul (CStarMatrix.ofMatrix.symm a) (1 : Matrix I I ℂ)
      (1 : Matrix J J ℂ) (CStarMatrix.ofMatrix.symm b)).symm

lemma right_mul_left (a : Mat I) (b : Mat J) :
    right (I := I) b*left (J := J) a=CStarMatrix.ofMatrix (CStarMatrix.ofMatrix.symm a ⊗ₖ
      CStarMatrix.ofMatrix.symm b) := by
  change ((1 : Matrix I I ℂ) ⊗ₖ CStarMatrix.ofMatrix.symm b)*
    (CStarMatrix.ofMatrix.symm a ⊗ₖ (1 : Matrix J J ℂ))=
    CStarMatrix.ofMatrix.symm a ⊗ₖ CStarMatrix.ofMatrix.symm b
  simpa only [Matrix.mul_one,Matrix.one_mul] using
    (Matrix.mul_kronecker_mul (1 : Matrix I I ℂ) (CStarMatrix.ofMatrix.symm a)
      (CStarMatrix.ofMatrix.symm b) (1 : Matrix J J ℂ)).symm

lemma commute (a : Mat I) (b : Mat J) : Commute (left (J := J) a) (right (I := I) b) := by
  change left (J := J) a*right (I := I) b=right (I := I) b*left (J := J) a
  rw [left_mul_right,right_mul_left]

@[simp] lemma left_mul_right_apply (a : Mat I) (b : Mat J) (i k : I) (j l : J) :
    (left (J := J) a*right (I := I) b) (i,j) (k,l)=a i k*b j l := by rw [left_mul_right]; rfl

end MatrixTensor

end


noncomputable section
namespace MatrixTensor
open Pureness
open scoped TensorProduct CStarAlgebra ComplexOrder

variable {I J X Y : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y] [CompactSpace Y]

local instance (priority := 2000) sectionSemiring : Semiring C(X,Mat I) :=
  (inferInstance : Ring C(X,Mat I)).toSemiring

instance matFiniteDimensional : FiniteDimensional ℂ (Mat I) :=
  FiniteDimensional.of_injective (CStarMatrix.ofMatrixₗ (R := ℂ)).symm.toLinearMap
    (CStarMatrix.ofMatrixₗ (R := ℂ)).symm.injective

instance closedSectionCStar (S : StarSubalgebra ℂ C(X,Mat I))
    [IsClosed (S : Set C(X,Mat I))] : CStarAlgebra S := by
  letI : SubringClass (StarSubalgebra ℂ C(X,Mat I)) C(X,Mat I) :=
    @StarSubalgebra.subringClass ℂ C(X,Mat I) _ _ _ _ _ _
  exact StarSubalgebra.cstarAlgebra S

def leftSection : C(X,Mat I) →⋆ₐ[ℂ] C(X×Y,Mat (I×J)) where
  toFun f := ⟨fun z => left (J := J) (f z.1),
    (map_continuous _).comp (f.continuous.comp continuous_fst)⟩
  map_one' := by apply ContinuousMap.ext; intro z; exact map_one left
  map_zero' := by apply ContinuousMap.ext; intro z; exact map_zero left
  map_add' f g := by apply ContinuousMap.ext; intro z; exact map_add left _ _
  map_mul' f g := by apply ContinuousMap.ext; intro z; exact map_mul left _ _
  commutes' z := by apply ContinuousMap.ext; intro x; exact left.commutes z
  map_star' f := by apply ContinuousMap.ext; intro z; exact map_star left _

def rightSection : C(Y,Mat J) →⋆ₐ[ℂ] C(X×Y,Mat (I×J)) where
  toFun f := ⟨fun z => right (I := I) (f z.2),
    (map_continuous _).comp (f.continuous.comp continuous_snd)⟩
  map_one' := by apply ContinuousMap.ext; intro z; exact map_one right
  map_zero' := by apply ContinuousMap.ext; intro z; exact map_zero right
  map_add' f g := by apply ContinuousMap.ext; intro z; exact map_add right _ _
  map_mul' f g := by apply ContinuousMap.ext; intro z; exact map_mul right _ _
  commutes' z := by apply ContinuousMap.ext; intro x; exact right.commutes z
  map_star' f := by apply ContinuousMap.ext; intro z; exact map_star right _

omit [CompactSpace X] [CompactSpace Y] in
lemma section_commute (a : C(X,Mat I)) (b : C(Y,Mat J)) :
    Commute (leftSection (Y := Y) (J := J) a) (rightSection (X := X) (I := I) b) := by
  apply ContinuousMap.ext
  intro z
  exact (commute (a z.1) (b z.2)).eq

variable (S : StarSubalgebra ℂ C(X,Mat I)) (T : StarSubalgebra ℂ C(Y,Mat J))
variable [IsClosed (S : Set C(X,Mat I))] [IsClosed (T : Set C(Y,Mat J))]

local instance (priority := 2000) closedSectionSemiring
    (S : StarSubalgebra ℂ C(X,Mat I)) [IsClosed (S : Set C(X,Mat I))] : Semiring S :=
  (inferInstance : CStarAlgebra S).toSemiring

def sectionMap : S ⊗[ℂ] T →⋆ₐ[ℂ] C(X×Y,Mat (I×J)) :=
  commutingStarTensorHom (N := C(X×Y,Mat (I×J)))
    (leftSection.comp S.subtype) (rightSection.comp T.subtype)
    (fun (a : S) (b : T) => section_commute a.val b.val)

lemma sectionMap_tmul (a : S) (b : T) (x : X) (y : Y) :
    sectionMap S T (a ⊗ₜ[ℂ] b) (x,y)=left (a.val x)*right (b.val y) := rfl

lemma sectionMap_tmul_entry (a : S) (b : T) (x : X) (y : Y) (i k : I) (j l : J) :
    sectionMap S T (a ⊗ₜ[ℂ] b) (x,y) (i,j) (k,l)=a.val x i k*b.val y j l :=
  left_mul_right_apply _ _ _ _ _ _

def entryLinear (x : X) (i k : I) : S →ₗ[ℂ] ℂ where
  toFun a := a.val x i k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma entryLinear_separates (a : S) (h : ∀ z : X×I×I,entryLinear S z.1 z.2.1 z.2.2 a=0) : a=0 := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  ext i k
  exact h (x,i,k)

lemma sectionMap_slice_entry (z : S ⊗[ℂ] T) (x : X) (y : Y) (i k : I) (j l : J) :
    entryLinear T y j l (TensorSliceSeparation.slice (entryLinear S x i k) z)=
      sectionMap S T z (x,y) (i,j) (k,l) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    rw [TensorSliceSeparation.slice_tmul,map_smul,sectionMap_tmul_entry]
    rfl
  | add z w hz hw => simp only [map_add,hz,hw]; rfl

theorem sectionMap_injective : Function.Injective (sectionMap S T) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  apply TensorSliceSeparation.tensor_eq_zero_of_double_slices
    (fun x : X×I×I => entryLinear S x.1 x.2.1 x.2.2)
    (fun y : Y×J×J => entryLinear T y.1 y.2.1 y.2.2)
    (entryLinear_separates S) (entryLinear_separates T) z
  intro x y
  rw [sectionMap_slice_entry,hz]
  rfl

end MatrixTensor

end

end OAI
