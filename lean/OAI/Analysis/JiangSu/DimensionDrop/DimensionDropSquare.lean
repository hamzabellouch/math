import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.TensorProducts.TensorSliceSeparation

namespace OAI


noncomputable section
namespace MatrixTensor
open Pureness
open scoped TensorProduct CStarAlgebra ComplexOrder

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

instance matrixSubalgebraClosed (S : StarSubalgebra ℂ (Mat I)) :
    IsClosed (S : Set (Mat I)) := S.toSubalgebra.toSubmodule.closed_of_finiteDimensional
instance matrixSubalgebraCStar (S : StarSubalgebra ℂ (Mat I)) : CStarAlgebra S :=
  by
    letI : SubringClass (StarSubalgebra ℂ (Mat I)) (Mat I) :=
      @StarSubalgebra.subringClass ℂ (Mat I) _ _ _ _ _ _
    exact StarSubalgebra.cstarAlgebra S

local instance (priority := 2000) matrixSubalgebraSemiring (S : StarSubalgebra ℂ (Mat I)) : Semiring S :=
  (inferInstance : CStarAlgebra S).toSemiring

def fiberMap (S : StarSubalgebra ℂ (Mat I)) (T : StarSubalgebra ℂ (Mat J)) :
    S ⊗[ℂ] T →⋆ₐ[ℂ] Mat (I×J) :=
  commutingStarTensorHom (N := Mat (I×J)) (left.comp S.subtype) (right.comp T.subtype)
    (fun (a : S) (b : T) => commute a.val b.val)

def fiberAlgebra (S : StarSubalgebra ℂ (Mat I)) (T : StarSubalgebra ℂ (Mat J)) :
    StarSubalgebra ℂ (Mat (I×J)) := (fiberMap S T).range

lemma mul_mem_fiber (S : StarSubalgebra ℂ (Mat I)) (T : StarSubalgebra ℂ (Mat J))
    {a : Mat I} {b : Mat J} (ha : a∈S) (hb : b∈T) :
    left (J := J) a*right (I := I) b∈fiberAlgebra S T :=
  ⟨(⟨a,ha⟩:S) ⊗ₜ[ℂ] (⟨b,hb⟩:T),rfl⟩

lemma fiber_finite_sum (S : StarSubalgebra ℂ (Mat I)) (T : StarSubalgebra ℂ (Mat J))
    {x : Mat (I×J)} (hx : x∈fiberAlgebra S T) :
    ∃ n : ℕ,∃ a : Fin n → S,∃ b : Fin n → T,
      x=∑ i,left (a i).val*right (b i).val := by
  obtain ⟨z,rfl⟩ := hx
  obtain ⟨n,a,b,rfl⟩ := TensorProduct.exists_sum_tmul_eq z
  refine ⟨n,a,b,?_⟩
  rw [map_sum]
  rfl
end MatrixTensor

namespace JiangSuConstruction
open MatrixTensor Pureness
open scoped CStarAlgebra TensorProduct ComplexOrder

variable (p q r s : ℕ)
local instance (priority := 2000) squareSectionSemiring :
    Semiring C(Interval×Interval,MatrixTensor.Mat ((Fin p×Fin q)×(Fin r×Fin s))) :=
  (inferInstance : Ring C(Interval×Interval,MatrixTensor.Mat ((Fin p×Fin q)×(Fin r×Fin s)))).toSemiring

def dropFiber (t : Interval) : StarSubalgebra ℂ (TensorMat p q) :=
  if t=leftEndpoint then (leftAmplification p q).range
  else if t=rightEndpoint then (rightAmplification p q).range else ⊤

lemma drop_mem_fiber (f : DimensionDrop p q) (t : Interval) : f.val t∈dropFiber p q t := by
  unfold dropFiber
  split_ifs with ht ht
  · subst t; exact f.property.1
  · subst t; exact f.property.2
  · trivial

def squareSections : StarSubalgebra ℂ
    C(Interval×Interval,MatrixTensor.Mat ((Fin p×Fin q)×(Fin r×Fin s))) where
  carrier := {f | ∀ x y,f (x,y)∈fiberAlgebra (dropFiber p q x) (dropFiber r s y)}
  one_mem' := by intro x y; exact one_mem _
  zero_mem' := by intro x y; exact zero_mem _
  add_mem' hf hg := by intro x y; exact add_mem (hf x y) (hg x y)
  mul_mem' hf hg := by intro x y; exact mul_mem (hf x y) (hg x y)
  algebraMap_mem' z := by intro x y; exact algebraMap_mem _ z
  star_mem' hf := by intro x y; exact star_mem (hf x y)

instance squareSections_closed : IsClosed
    (squareSections p q r s : Set C(Interval×Interval,MatrixTensor.Mat ((Fin p×Fin q)×(Fin r×Fin s)))) := by
  change IsClosed {f : C(Interval×Interval,MatrixTensor.Mat ((Fin p×Fin q)×(Fin r×Fin s))) |
    ∀ x y,f (x,y)∈fiberAlgebra (dropFiber p q x) (dropFiber r s y)}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter; intro x
  apply isClosed_iInter; intro y
  exact (matrixSubalgebraClosed _).preimage (continuous_eval_const (x,y))

abbrev Square := squareSections p q r s

lemma sectionMap_mem_square (z : DimensionDrop p q ⊗[ℂ] DimensionDrop r s) :
    sectionMap (dimensionDrop p q) (dimensionDrop r s) z∈squareSections p q r s := by
  induction z using TensorProduct.inductionOn with
  | add z w hz hw =>
    rw [map_add]
    intro x y
    exact (fiberAlgebra (dropFiber p q x) (dropFiber r s y)).add_mem (hz x y) (hw x y)
  | tmul a b =>
    intro x y
    exact mul_mem_fiber _ _ (drop_mem_fiber p q a x) (drop_mem_fiber r s b y)

def squareTensorMap : DimensionDrop p q ⊗[ℂ] DimensionDrop r s →⋆ₐ[ℂ] Square p q r s where
  toFun z := ⟨sectionMap (dimensionDrop p q) (dimensionDrop r s) z,sectionMap_mem_square p q r s z⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_zero' := by apply Subtype.ext; exact map_zero _
  map_add' z w := by apply Subtype.ext; exact map_add _ _ _
  map_mul' z w := by apply Subtype.ext; exact map_mul _ _ _
  commutes' c := by apply Subtype.ext; exact (sectionMap (dimensionDrop p q) (dimensionDrop r s)).commutes c
  map_star' z := by apply Subtype.ext; exact map_star _ _

theorem squareTensorMap_injective : Function.Injective (squareTensorMap p q r s) := by
  intro z w h
  exact sectionMap_injective _ _ (congrArg Subtype.val h)

end JiangSuConstruction

end

end OAI
