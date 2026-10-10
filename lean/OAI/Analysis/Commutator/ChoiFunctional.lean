import Mathlib
import OAI.Analysis.Commutator.CyclicMatrix
import OAI.Analysis.Commutator.OperatorSystem
import OAI.Analysis.Commutator.PositiveExtensionComplex

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder CStarAlgebra

namespace Kadison.OperatorSystem

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {ι : Type} [Fintype ι]

local instance : DecidableEq ι := Classical.decEq ι

abbrev CoordinateSpace (ι : Type) [Fintype ι] := PiLp 2 (fun _ : ι => ℂ)

def basisVector (i : ι) : CoordinateSpace ι := WithLp.toLp 2 (fun j => if j=i then 1 else 0)

@[simp] lemma basisVector_apply (i j : ι) : basisVector i j=if j=i then 1 else 0 := rfl

def choi (S : Submodule ℂ A) (f : S →ₗ[ℂ] (CoordinateSpace ι →L[ℂ] CoordinateSpace ι)) :
    matrices S ι →ₗ[ℂ] ℂ where
  toFun X := ∑ i,∑ j,⟪basisVector i,mapMatrix S f X i j (basisVector j)⟫_ℂ
  map_add' X Y := by simp only [map_add,CStarMatrix.add_apply,add_apply,inner_add_right,Finset.sum_add_distrib]
  map_smul' c X := by simp only [map_smul,CStarMatrix.smul_apply,smul_apply,inner_smul_right,Finset.mul_sum,smul_eq_mul,RingHom.id_apply]

lemma choi_nonneg (S : Submodule ℂ A)
    (f : S →ₗ[ℂ] (CoordinateSpace ι →L[ℂ] CoordinateSpace ι))
    (hf : IsCompletelyPositive S f) (X : matrices S ι) (hX : 0≤X.val) : 0≤choi S f X := by
  let v : PiLp 2 (fun _ : ι => CoordinateSpace ι) := WithLp.toLp 2 basisVector
  have hp := map_nonneg
    (CyclicColumns.matrixRepresentation (ι:=ι) (StarAlgHom.id ℂ (CoordinateSpace ι →L[ℂ] CoordinateSpace ι)))
    (hf ι X hX)
  have hh := (ContinuousLinearMap.nonneg_iff_isPositive.mp hp).inner_nonneg_right v
  simpa [CyclicColumns.matrixRepresentation,CyclicColumns.matrixAction_apply,PiLp.inner_apply,
    v,choi,inner_sum] using hh

theorem exists_choi_extension (S : Submodule ℂ A) (h1 : (1 : A)∈S)
    (hs : ∀ a∈S,star a∈S)
    (f : S →ₗ[ℂ] (CoordinateSpace ι →L[ℂ] CoordinateSpace ι))
    (hf : IsCompletelyPositive S f) :
    ∃ η : CStarMatrix ι ι A →ₚ[ℂ] ℂ,∀ X : matrices S ι,η X=choi S f X :=
  PositiveExtension.exists_positive_extension (matrices S ι) (matrices_one S h1)
    (matrices_star S hs) (choi S f) (choi_nonneg S f hf)

end Kadison.OperatorSystem

end

end
end

end OAI
