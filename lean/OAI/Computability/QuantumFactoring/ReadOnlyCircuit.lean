import Mathlib
import OAI.Computability.QuantumFactoring.GateSemantics

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

lemma Gate.arity_pos (g : Gate) : 0<g.arity := by
  cases g with
  | mk p inv ctrl => cases p <;> cases ctrl <;> simp [Gate.arity,Primitive.arity]

def Instruction.target {q : ℕ} (o : Instruction q) : Fin q :=
  o.wire ⟨o.gate.arity-1,by have := o.gate.arity_pos; omega⟩

lemma Primitive.nonTarget_zero (p : Primitive) (x y : Basis p.arity) (i : Fin p.arity)
    (hi : i.val+1<p.arity) (hne : x i≠y i) : p.localMatrix x y=0 := by
  cases p with
  | not => simp only [Primitive.arity] at hi; omega
  | hadamard => simp only [Primitive.arity] at hi; omega
  | phase => simp only [Primitive.arity] at hi; omega
  | cnot =>
    rw [cnot_localMatrix]
    have hc : cnotPerm y i=y i := by
      fin_cases i <;> simp_all [cnotPerm,Primitive.arity]
    have hxy : x≠cnotPerm y := fun he => hne ((congrFun he i).trans hc)
    change (if x=_ then (1 : ℂ) else 0)=0
    exact ite_eq_right hxy
  | toffoli =>
    rw [toffoli_localMatrix]
    have hc : toffoliPerm y i=y i := by
      fin_cases i <;> simp_all [toffoliPerm,Primitive.arity]
    have hxy : x≠toffoliPerm y := fun he => hne ((congrFun he i).trans hc)
    change (if x=_ then (1 : ℂ) else 0)=0
    exact ite_eq_right hxy

lemma Gate.base_nonTarget_zero (g : Gate) (x y : Basis g.primitive.arity)
    (i : Fin g.primitive.arity) (hi : i.val+1<g.primitive.arity) (hne : x i≠y i) :
    g.baseLocalMatrix x y=0 := by
  rw [g.baseLocalMatrix_eq]
  split_ifs
  · change star (g.primitive.localMatrix y x)=0
    rw [g.primitive.nonTarget_zero y x i hi (Ne.symm hne),star_zero]
  · exact g.primitive.nonTarget_zero x y i hi hne

/-- In the literal fixed alphabet, all but the final wire are controls.
The inverse and added-control variants preserve these same wires. -/
lemma Gate.nonTarget_zero (g : Gate) (x y : Basis g.arity) (i : Fin g.arity)
    (hi : i.val+1<g.arity) (hne : x i≠y i) : g.localMatrix x y=0 := by
  rcases g with ⟨p,inv,ctrl⟩
  cases ctrl
  · exact Gate.base_nonTarget_zero ⟨p,inv,false⟩ x y i hi hne
  · change Basis (p.arity+1) at x y
    change Fin (p.arity+1) at i
    rw [Gate.controlled_localMatrix]
    change controlledMatrix (Gate.mk p inv true).baseLocalMatrix
      (x 0,Fin.tail x) (y 0,Fin.tail y)=0
    by_cases ht : x 0=y 0
    · have hi0 : i.val≠0 := by
        intro hi0
        have hie : i=0 := Fin.ext hi0
        exact hne (hie ▸ ht)
      have hi' : i.val+1<p.arity+1 := hi
      let j : Fin p.arity := ⟨i.val-1,by omega⟩
      have hji : j.succ=i := Fin.ext (by simp only [Fin.val_succ,j]; omega)
      have hjn : Fin.tail x j≠Fin.tail y j := by
        simpa only [Fin.tail_def,hji] using hne
      have htail : Fin.tail x≠Fin.tail y := fun he => hjn (congrFun he j)
      dsimp only [controlledMatrix,Matrix.of_apply]
      rw [ite_eq_left ht]
      split_ifs
      · exact Gate.base_nonTarget_zero ⟨p,inv,true⟩ _ _ j (by simp only [j]; omega) hjn
      · simp
    · simp [controlledMatrix,ht]

lemma Instruction.nonzero_eq {q : ℕ} (o : Instruction q) (x y : Basis q)
    (h : o.matrix x y≠0) (i : Fin q) (hi : i≠o.target) : x i=y i := by
  classical
  have houtside : ∀ i : Fin q,(∀ j,o.wire j≠i)→x i=y i := by
    by_contra hn
    exact h (by simp only [Instruction.matrix,ite_eq_right hn])
  have hlocal : o.gate.localMatrix (x∘o.wire) (y∘o.wire)≠0 := by
    simpa only [Instruction.matrix,ite_eq_left houtside,Gate.localMatrix,Matrix.of_apply] using h
  by_cases hw : ∃ j,o.wire j=i
  · obtain ⟨j,rfl⟩ := hw
    have hj : j.val+1<o.gate.arity := by
      have hjne : j.val≠o.gate.arity-1 := by
        intro he
        apply hi
        unfold Instruction.target
        congr 1
        exact Fin.ext he
      omega
    by_contra hne
    exact hlocal (o.gate.nonTarget_zero _ _ j hj hne)
  · exact houtside i (by simpa only [not_exists] using hw)


end ExactQuantumFactoring
end

end OAI
