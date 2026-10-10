import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalAmplification
import OAI.Computability.QuantumFactoring.ReadOnlyCircuit

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

/-- One of the literal fixed alphabet gates; the extra control is the first
wire and is never modified. -/
abbrev controlledHadamardAt {q : ℕ} (c t : Fin q) (h : c≠t) : Instruction q :=
  ⟨⟨.hadamard,false,true⟩, ![c,t], by
    change Function.Injective (![c,t] : Fin 2→Fin q)
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all⟩

lemma controlledHadamardAt_matrix {q : ℕ} (c t : Fin q) (h : c≠t) (x y : Basis q) :
    (controlledHadamardAt c t h).matrix y x =
      if x c then (hadamardAt t).matrix y x else if y=x then 1 else 0 := by
  classical
  have ho : (∀ i : Fin q,(∀ j : Fin 2, (![c,t] : Fin 2→Fin q) j≠i)→y i=x i) ↔
      (∀ i : Fin q, i≠c→i≠t→y i=x i) := by
    constructor
    · intro hh i hic hit
      apply hh i
      intro j
      fin_cases j
      · exact Ne.symm hic
      · exact Ne.symm hit
    · intro hh i hi
      exact hh i (Ne.symm (hi 0)) (Ne.symm (hi 1))
  change (if ∀ i : Fin q,(∀ j : Fin 2, (![c,t] : Fin 2→Fin q) j≠i)→y i=x i then
    (Gate.mk .hadamard false true).matrix
      (List.ofFn (y∘(![c,t] : Fin 2→Fin q)))
      (List.ofFn (x∘(![c,t] : Fin 2→Fin q))) else 0)=_
  simp only [ho,List.ofFn_succ,List.ofFn_zero,Function.comp_apply,
    Matrix.cons_val_zero,Matrix.cons_val_succ]
  rw [hadamardAt_matrix]
  have hyc : (∀ i : Fin q,i≠t→y i=x i) ↔ y c=x c ∧ (∀ i : Fin q,i≠c→i≠t→y i=x i) := by
    constructor
    · exact fun hh => ⟨hh c h,fun i _ hit => hh i hit⟩
    · rintro ⟨hc,hh⟩ i hit
      by_cases hic : i=c
      · simpa [hic] using hc
      · exact hh i hic hit
  have heq : y=x ↔ y c=x c ∧ y t=x t ∧ (∀ i : Fin q,i≠c→i≠t→y i=x i) := by
    constructor
    · rintro rfl; simp
    · rintro ⟨hc,ht,hh⟩
      funext i
      by_cases hic : i=c
      · simpa [hic] using hc
      · by_cases hit : i=t
        · simpa [hit] using ht
        · exact hh i hic hit
  simp only [hyc,heq]
  cases xc : x c <;> cases yc : y c <;>
    simp only [Gate.matrix,Gate.baseMatrix,Bool.true_eq,Bool.false_eq_true,ite_true,ite_false,
      Primitive.matrix,List.cons.injEq, and_true]
  all_goals split_ifs <;> simp_all

lemma controlledHadamardAt_basis {q : ℕ} (c t : Fin q) (h : c≠t) (x : Basis q) :
    (controlledHadamardAt c t h).matrix.mulVec (basisVector x)=
      if x c then (hadamardAt t).matrix.mulVec (basisVector x) else basisVector x := by
  classical
  rw [matrix_basisVector]
  funext y
  rw [controlledHadamardAt_matrix]
  cases hx : x c <;> simp [matrix_basisVector,basisVector]

lemma controlledHadamardAt_target {q : ℕ} (c t : Fin q) (h : c≠t) :
    (controlledHadamardAt c t h).target=t := rfl

/-- On a sector with a fixed control, controlled H is H or the identity on an
arbitrary coherent state, including all old retained work. -/
lemma controlledHadamardAt_sector {q : ℕ} (c t : Fin q) (h : c≠t) (b : Bool)
    (ψ : State q) (hs : Supported (fun x => x c=b) ψ) :
    (controlledHadamardAt c t h).matrix.mulVec ψ=
      if b then (hadamardAt t).matrix.mulVec ψ else ψ := by
  classical
  funext y
  change (∑ x,(controlledHadamardAt c t h).matrix y x*ψ x)=_
  simp_rw [controlledHadamardAt_matrix]
  cases b
  · simp only [Bool.false_eq_true,ite_false]
    calc
      _ = ∑ x : Basis q,(if y=x then (1 : ℂ) else 0)*ψ x := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x c=false
        · simp [hx]
        · rw [hs x hx]; simp
      _ = ψ y := by simp
  · simp only [ite_true]
    change _=∑ x,(hadamardAt t).matrix y x*ψ x
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x c=true
    · simp [hx]
    · rw [hs x hx]; simp

end ExactQuantumFactoring


end

end OAI
