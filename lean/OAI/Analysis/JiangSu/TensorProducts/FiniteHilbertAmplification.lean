import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.TraceCone.Weights

namespace OAI

section

noncomputable section
namespace PureStateExcision
open scoped InnerProductSpace ENNReal

variable {A H I : Type*} [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype I] [DecidableEq I]

 def tupleOp (T : H →L[ℂ] H) : PiLp 2 (fun _ : I => H) →L[ℂ] PiLp 2 (fun _ : I => H) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : I => H)).symm.toContinuousLinearMap ∘L
    (ContinuousLinearMap.piMap (fun _ : I => T)) ∘L
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : I => H)).toContinuousLinearMap

omit [CompleteSpace H] [Fintype I] [DecidableEq I] in
@[simp] lemma tupleOp_apply (T : H →L[ℂ] H) (x : PiLp 2 (fun _ : I => H)) (i : I) :
    tupleOp T x i=T (x i) := rfl

omit [DecidableEq I] in
lemma tupleOp_star (T : H →L[ℂ] H) : tupleOp (I := I) (star T)=star (tupleOp T) := by
  rw [ContinuousLinearMap.star_eq_adjoint (tupleOp (I := I) T),ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [PiLp.inner_apply,tupleOp_apply,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]

 def tupleRepresentation (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    A →⋆ₐ[ℂ] (PiLp 2 (fun _ : I => H) →L[ℂ] PiLp 2 (fun _ : I => H)) where
  toFun a := tupleOp (π a)
  map_one' := by ext x i; simp
  map_mul' a b := by ext x i; simp
  map_zero' := by ext x i; simp
  map_add' a b := by ext x i; simp
  commutes' z := by
    ext x i
    change (π (algebraMap ℂ A z)) (x i)=z • x i
    rw [Algebra.algebraMap_eq_smul_one,map_smul,map_one]
    rfl
  map_star' a := by rw [map_star,tupleOp_star]

omit [DecidableEq I] in
@[simp] lemma tupleRepresentation_apply (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (a : A)
    (x : PiLp 2 (fun _ : I => H)) (i : I) : tupleRepresentation π a x i=π a (x i) := rfl

 def tupleSingle (i : I) : H →L[ℂ] PiLp 2 (fun _ : I => H) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : I => H)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.single ℂ (fun _ : I => H) i

omit [CompleteSpace H] [Fintype I] in
@[simp] lemma tupleSingle_apply (i : I) (x : H) : tupleSingle i x=PiLp.single 2 i x := rfl

 def tupleEntry (T : PiLp 2 (fun _ : I => H) →L[ℂ] PiLp 2 (fun _ : I => H)) (i j : I) :
    H →L[ℂ] H := (ContinuousLinearMap.proj i) ∘L
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : I => H)).toContinuousLinearMap ∘L T ∘L tupleSingle j

omit [CompleteSpace H] [Fintype I] in
@[simp] lemma tupleEntry_apply (T : PiLp 2 (fun _ : I => H) →L[ℂ] PiLp 2 (fun _ : I => H))
    (i j : I) (x : H) : tupleEntry T i j x=T (PiLp.single 2 j x) i := rfl

omit [CompleteSpace H] [Fintype I] in
lemma tupleOp_single (T : H →L[ℂ] H) (j : I) (x : H) :
    tupleOp T (PiLp.single 2 j x)=PiLp.single 2 j (T x) := by
  classical
  ext i
  by_cases hi : i=j <;> simp [hi]

lemma commuting_tuple_entries (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (T : PiLp 2 (fun _ : I => H) →L[ℂ] PiLp 2 (fun _ : I => H))
    (hcomm : ∀ a : A,Commute T (tupleRepresentation π a)) (i j : I) (a : A) :
    Commute (tupleEntry T i j) (π a) := by
  apply ContinuousLinearMap.ext
  intro x
  have he := congrArg (fun U : PiLp 2 (fun _ : I => H) →L[ℂ] PiLp 2 (fun _ : I => H) =>
    U (PiLp.single 2 j x) i) (hcomm a).eq
  change T (tupleOp (π a) (PiLp.single 2 j x)) i=π a (T (PiLp.single 2 j x) i) at he
  rw [tupleOp_single] at he
  exact he

omit [CompleteSpace H] in
lemma tuple_operator_expansion (T : PiLp 2 (fun _ : I => H) →L[ℂ] PiLp 2 (fun _ : I => H))
    (x : PiLp 2 (fun _ : I => H)) (i : I) : T x i=∑ j,tupleEntry T i j (x j) := by
  have hx : x=∑ j,PiLp.single 2 j (x j) := by
    classical
    ext k
    simp
  conv_lhs => rw [hx,map_sum]
  simp [tupleEntry_apply]

end PureStateExcision

end
end

end OAI
