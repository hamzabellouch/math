import Mathlib
import OAI.Probability.SKValue.GroundState.AffineComparison

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

structure TreeLevel where
  branchExcess : ℕ
  endpoint : ℝ
  height : ℝ

abbrev GaussianTree := List TreeLevel

abbrev TreeLeaves : GaussianTree → Type
  | [] => PUnit
  | l::T => Fin (l.branchExcess+1) × TreeLeaves T

abbrev TreeEdges : GaussianTree → Type
  | [] => PEmpty
  | l::T => Fin (l.branchExcess+1) ⊕ (Fin (l.branchExcess+1) × TreeEdges T)

instance treeLeavesFintype (T : GaussianTree) : Fintype (TreeLeaves T) := by
  induction T with
  | nil => exact inferInstanceAs (Fintype PUnit)
  | cons l T ih => exact inferInstanceAs (Fintype (Fin (l.branchExcess+1) × TreeLeaves T))
instance treeLeavesNonempty (T : GaussianTree) : Nonempty (TreeLeaves T) := by
  induction T with
  | nil => exact inferInstanceAs (Nonempty PUnit)
  | cons l T ih => exact inferInstanceAs (Nonempty (Fin (l.branchExcess+1) × TreeLeaves T))
instance treeEdgesFintype (T : GaussianTree) : Fintype (TreeEdges T) := by
  induction T with
  | nil => exact inferInstanceAs (Fintype PEmpty)
  | cons l T ih => exact inferInstanceAs (Fintype (Fin (l.branchExcess+1) ⊕ (Fin (l.branchExcess+1) × TreeEdges T)))

noncomputable def treePathCoeff (c : ℝ → TreeLevel → ℝ) (q : ℝ) :
    (T : GaussianTree) → TreeLeaves T → TreeEdges T → ℝ
  | [],_,e => PEmpty.elim e
  | l::T,α,e => match e with
    | Sum.inl i => if α.1=i then c q l else 0
    | Sum.inr (i,e) => if α.1=i then treePathCoeff c l.endpoint T α.2 e else 0

noncomputable def treeOverlap (q : ℝ) : (T : GaussianTree) → TreeLeaves T → TreeLeaves T → ℝ
  | [],_,_ => q
  | l::T,α,β => if α.1=β.1 then treeOverlap l.endpoint T α.2 β.2 else q

def ValidTreeGrid (q : ℝ) : GaussianTree → Prop
  | [] => q=1
  | l::T => q≤l.endpoint ∧ ValidTreeGrid l.endpoint T

lemma treePath_inner_node (c : ℝ → TreeLevel → ℝ) (q : ℝ) (l : TreeLevel) (T : GaussianTree)
    (α β : TreeLeaves (l::T)) :
    (∑ e,treePathCoeff c q (l::T) α e*treePathCoeff c q (l::T) β e)=
    if α.1=β.1 then (c q l)^2+∑ e,treePathCoeff c l.endpoint T α.2 e*treePathCoeff c l.endpoint T β.2 e else 0 := by
  classical
  change (∑ e : Fin (l.branchExcess+1) ⊕ (Fin (l.branchExcess+1) × TreeEdges T),_)=_
  rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
  simp only [treePathCoeff]
  by_cases h : α.1=β.1
  · simp only [h,ite_true]
    simp [←h,ite_mul,mul_ite,sq]
  · simp only [h,ite_false]
    have he (i : Fin (l.branchExcess+1)) : ¬(α.1=i ∧ β.1=i) := by
      rintro ⟨ha,hb⟩; exact h (ha.trans hb.symm)
    simp_rw [ite_mul,zero_mul]
    simp only [mul_ite,mul_zero]
    have hzero (i : Fin (l.branchExcess+1)) (r s : ℝ) :
        (if α.1=i then if β.1=i then r*s else 0 else 0)=0 := by
      split_ifs with ha hb <;> try rfl
      exact (he i ⟨ha,hb⟩).elim
    simp only [hzero,Finset.sum_const_zero,add_zero]

noncomputable def treeFieldVector (q : ℝ) (T : GaussianTree) : TreeLeaves T → TreeEdges T → ℝ :=
  treePathCoeff (fun q l ↦ Real.sqrt (l.endpoint-q)) q T

noncomputable def treeAuxVector (n : ℕ) (q : ℝ) (T : GaussianTree) : TreeLeaves T → TreeEdges T → ℝ :=
  treePathCoeff (fun q l ↦ Real.sqrt ((n : ℝ)/2)*Real.sqrt (l.endpoint^2-q^2)) q T

lemma treeField_inner (q : ℝ) (T : GaussianTree) (hT : ValidTreeGrid q T)
    (α β : TreeLeaves T) :
    (∑ e,treeFieldVector q T α e*treeFieldVector q T β e)=treeOverlap q T α β-q := by
  induction T generalizing q with
  | nil =>
    simp only [treeFieldVector,treePathCoeff,treeOverlap,sub_self]
    exact Finset.sum_eq_zero (by intro e he; exact PEmpty.elim e)
  | cons l T ih =>
    change q≤l.endpoint ∧ ValidTreeGrid l.endpoint T at hT
    rw [treeFieldVector,treePath_inner_node]
    dsimp [treeOverlap]
    split_ifs with h
    · rw [Real.sq_sqrt (sub_nonneg.mpr hT.1)]
      have hh := ih l.endpoint hT.2 α.2 β.2
      change (l.endpoint-q)+(∑ e,treeFieldVector l.endpoint T α.2 e*treeFieldVector l.endpoint T β.2 e)=_
      rw [hh]; ring
    · ring

lemma treeAux_inner (n : ℕ) (q : ℝ) (hq : 0≤q) (T : GaussianTree) (hT : ValidTreeGrid q T)
    (α β : TreeLeaves T) :
    (∑ e,treeAuxVector n q T α e*treeAuxVector n q T β e)=
      ((n : ℝ)/2)*((treeOverlap q T α β)^2-q^2) := by
  induction T generalizing q with
  | nil =>
    simp only [treeAuxVector,treePathCoeff,treeOverlap,sub_self,mul_zero]
    exact Finset.sum_eq_zero (by intro e he; exact PEmpty.elim e)
  | cons l T ih =>
    change q≤l.endpoint ∧ ValidTreeGrid l.endpoint T at hT
    rw [treeAuxVector,treePath_inner_node]
    dsimp [treeOverlap]
    split_ifs with h
    · rw [mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt (by nlinarith [hT.1])]
      have hh := ih l.endpoint (hq.trans hT.1) hT.2 α.2 β.2
      change ((n : ℝ)/2)*(l.endpoint^2-q^2)+
        (∑ e,treeAuxVector n l.endpoint T α.2 e*treeAuxVector n l.endpoint T β.2 e)=_
      rw [hh]; ring
    · ring

lemma treeOverlap_self (q : ℝ) (T : GaussianTree) (hT : ValidTreeGrid q T) (α : TreeLeaves T) :
    treeOverlap q T α α=1 := by
  induction T generalizing q with
  | nil => exact hT
  | cons l T ih => simp only [treeOverlap,ite_true]; exact ih l.endpoint hT.2 α.2

lemma treeField_unit (T : GaussianTree) (hT : ValidTreeGrid 0 T) (α : TreeLeaves T) :
    (∑ e,(treeFieldVector 0 T α e)^2)=1 := by
  simp only [sq]
  rw [treeField_inner 0 T hT,treeOverlap_self 0 T hT]
  norm_num

lemma treeAux_distance (n : ℕ) (T : GaussianTree) (hT : ValidTreeGrid 0 T)
    (α β : TreeLeaves T) :
    (∑ e,(treeAuxVector n 0 T α e-treeAuxVector n 0 T β e)^2)=
      (n : ℝ)*(1-(treeOverlap 0 T α β)^2) := by
  rw [sq_distance_sum]
  simp only [sq]
  rw [treeAux_inner n 0 (by norm_num) T hT,
    treeAux_inner n 0 (by norm_num) T hT,
    treeAux_inner n 0 (by norm_num) T hT,
    treeOverlap_self 0 T hT,treeOverlap_self 0 T hT]
  ring

end SKValueG

end

end OAI
