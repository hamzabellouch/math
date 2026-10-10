import Mathlib
import OAI.Probability.SKValue.GroundState.LiteralLower
import OAI.Probability.SKValue.GroundState.GaussianTree

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma treeAux_tensor_distance (n : ℕ) (T : GaussianTree) (hT : ValidTreeGrid 0 T)
    (α β : TreeLeaves T) :
    (∑ e,(leafAuxCoeff n (treeFieldVector 0 T) α e-leafAuxCoeff n (treeFieldVector 0 T) β e)^2)=
      ∑ e,(treeAuxVector n 0 T α e-treeAuxVector n 0 T β e)^2 := by
  rw [sq_distance_sum,leafAux_sq n _ (treeField_unit T hT),
    leafAux_sq n _ (treeField_unit T hT),leafAux_inner,treeField_inner 0 T hT,
    treeAux_distance n T hT]
  ring

lemma expected_treeAux_eq_tensor (n : ℕ) (T : GaussianTree) (hT : ValidTreeGrid 0 T)
    (d : TreeLeaves T → ℝ) :
    (∫ z,finiteMaximum (fun α ↦ linearProcess (treeAuxVector n 0 T) z α+d α)
      ∂gaussianProduct (TreeEdges T))=
    ∫ z,finiteMaximum (fun α ↦ linearProcess (leafAuxCoeff n (treeFieldVector 0 T)) z α+d α)
      ∂gaussianProduct (TreeEdges T × TreeEdges T) := by
  apply le_antisymm
  · exact expected_affine_max_le _ _ d (fun α β ↦ (treeAux_tensor_distance n T hT α β).symm.le)
  · exact expected_affine_max_le _ _ d (fun α β ↦ (treeAux_tensor_distance n T hT α β).le)

theorem finite_tree_guerra_upper {n : ℕ} (hn : 0 < n)
    (T : GaussianTree) (hT : ValidTreeGrid 0 T) (d : TreeLeaves T → ℝ) :
    expectedMaximum n+
      (∫ z,finiteMaximum (fun α ↦ linearProcess (treeAuxVector n 0 T) z α+d α)
        ∂gaussianProduct (TreeEdges T))≤
      ∫ z,finiteMaximum (fun α ↦ (∑ i,|leafField (treeFieldVector 0 T) z α i|)+d α)
        ∂gaussianProduct (Fin n × TreeEdges T) := by
  rw [expected_treeAux_eq_tensor n T hT d]
  exact finite_guerra_upper hn (treeFieldVector 0 T) (treeField_unit T hT) d

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma finiteMaximum_prod_curry_left {ι κ : Type*} [Fintype ι] [Nonempty ι]
    [Fintype κ] [Nonempty κ] (f : ι×κ → ℝ) :
    finiteMaximum f=finiteMaximum (fun i ↦ finiteMaximum (fun j ↦ f (i,j))) := by
  apply le_antisymm
  · obtain ⟨p,hp⟩ := exists_finiteMaximum f
    rw [←hp]
    exact (le_finiteMaximum (fun j ↦ f (p.1,j)) p.2).trans
      (le_finiteMaximum (fun i ↦ finiteMaximum (fun j ↦ f (i,j))) p.1)
  · obtain ⟨i,hi⟩ := exists_finiteMaximum (fun i ↦ finiteMaximum (fun j ↦ f (i,j)))
    obtain ⟨j,hj⟩ := exists_finiteMaximum (fun j ↦ f (i,j))
    rw [←hi,←hj]
    exact le_finiteMaximum f (i,j)

lemma treeLinear_step (c : ℝ → TreeLevel → ℝ) (q : ℝ) (l : TreeLevel) (T : GaussianTree)
    (z : TreeEdges (l::T) → ℝ) (α : TreeLeaves (l::T)) :
    linearProcess (treePathCoeff c q (l::T)) z α=
      c q l*z (Sum.inl α.1)+linearProcess (treePathCoeff c l.endpoint T)
        (fun e ↦ z (Sum.inr (α.1,e))) α.2 := by
  classical
  change (∑ e : Fin (l.branchExcess+1) ⊕ (Fin (l.branchExcess+1) × TreeEdges T),_)=_
  rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
  simp only [treePathCoeff,ite_mul,zero_mul]
  simp [linearProcess]

noncomputable def treeCenter : GaussianTree → ℝ
  | [] => 0
  | l::T => Real.log (l.branchExcess+1 : ℝ)/l.height+treeCenter T

noncomputable def treeOffset (T : GaussianTree) (g : TreeEdges T → ℝ) (α : TreeLeaves T) : ℝ :=
  linearProcess (treePathCoeff (fun _ l ↦ 1/l.height) 0 T) g α-treeCenter T

lemma treePathCoeff_const_q (c : TreeLevel → ℝ) (q r : ℝ) (T : GaussianTree) :
    treePathCoeff (fun _ l ↦ c l) q T=treePathCoeff (fun _ l ↦ c l) r T := by
  induction T with
  | nil => rfl
  | cons l T ih => funext α e; cases e <;> rfl

lemma treeOffset_step (l : TreeLevel) (T : GaussianTree)
    (g : TreeEdges (l::T) → ℝ) (α : TreeLeaves (l::T)) :
    treeOffset (l::T) g α=(g (Sum.inl α.1)-Real.log (l.branchExcess+1 : ℝ))/l.height+
      treeOffset T (fun e ↦ g (Sum.inr (α.1,e))) α.2 := by
  rw [treeOffset,treeLinear_step,treeCenter]
  rw [treePathCoeff_const_q (fun l ↦ 1/l.height) l.endpoint 0 T]
  simp only [treeOffset]
  ring

noncomputable def scalarTreeValue (c : ℝ → TreeLevel → ℝ) (q : ℝ) (T : GaussianTree)
    (z g : TreeEdges T → ℝ) : ℝ :=
  finiteMaximum (fun α ↦ linearProcess (treePathCoeff c q T) z α+treeOffset T g α)

lemma scalarTreeValue_step (c : ℝ → TreeLevel → ℝ) (q : ℝ) (l : TreeLevel) (T : GaussianTree)
    (z g : TreeEdges (l::T) → ℝ) :
    scalarTreeValue c q (l::T) z g=finiteMaximum (fun i : Fin (l.branchExcess+1) ↦
      c q l*z (Sum.inl i)+scalarTreeValue c l.endpoint T
        (fun e ↦ z (Sum.inr (i,e))) (fun e ↦ g (Sum.inr (i,e)))+
      (g (Sum.inl i)-Real.log (l.branchExcess+1 : ℝ))/l.height) := by
  unfold scalarTreeValue
  change finiteMaximum (fun α : Fin (l.branchExcess+1) × TreeLeaves T ↦ _)=_
  rw [finiteMaximum_prod_curry_left]
  congr 1; funext i
  conv_lhs =>
    arg 1
    ext α
    rw [treeLinear_step c q l T z (i,α),treeOffset_step l T g (i,α)]
  have he (a b d e : ℝ) : a+b+(d+e)=(b+e)+(a+d) := by ring
  conv_lhs =>
    arg 1
    ext α
    rw [he]
  dsimp only
  rw [finiteMaximum_add_const]
  ring

noncomputable def fieldTreeValue (n : ℕ) (q : ℝ) (T : GaussianTree) (x : Fin n → ℝ)
    (z : Fin n × TreeEdges T → ℝ) (g : TreeEdges T → ℝ) : ℝ :=
  finiteMaximum (fun α ↦ (∑ i,|x i+leafField (treeFieldVector q T) z α i|)+treeOffset T g α)

lemma fieldTreeValue_step (n : ℕ) (q : ℝ) (l : TreeLevel) (T : GaussianTree) (x : Fin n → ℝ)
    (z : Fin n × TreeEdges (l::T) → ℝ) (g : TreeEdges (l::T) → ℝ) :
    fieldTreeValue n q (l::T) x z g=finiteMaximum (fun j : Fin (l.branchExcess+1) ↦
      fieldTreeValue n l.endpoint T (fun i ↦ x i+Real.sqrt (l.endpoint-q)*z (i,Sum.inl j))
        (fun p ↦ z (p.1,Sum.inr (j,p.2))) (fun e ↦ g (Sum.inr (j,e)))+
      (g (Sum.inl j)-Real.log (l.branchExcess+1 : ℝ))/l.height) := by
  have hh (α : TreeLeaves (l::T)) (i : Fin n) :
      leafField (treeFieldVector q (l::T)) z α i=
      Real.sqrt (l.endpoint-q)*z (i,Sum.inl α.1)+
        leafField (treeFieldVector l.endpoint T) (fun p ↦ z (p.1,Sum.inr (α.1,p.2))) α.2 i := by
    exact treeLinear_step (fun q l ↦ Real.sqrt (l.endpoint-q)) q l T (fun e ↦ z (i,e)) α
  unfold fieldTreeValue
  change finiteMaximum (fun α : Fin (l.branchExcess+1) × TreeLeaves T ↦ _)=_
  rw [finiteMaximum_prod_curry_left]
  congr 1; funext j
  conv_lhs =>
    arg 1
    ext α
    rw [treeOffset_step l T g (j,α)]
    simp only [hh (j,α),←add_assoc]
  dsimp only
  have he (a b d : ℝ) : a+b+d=(a+d)+b := by ring
  conv_lhs =>
    arg 1
    ext α
    rw [he]
  rw [finiteMaximum_add_const]

end SKValueG

end

end OAI
