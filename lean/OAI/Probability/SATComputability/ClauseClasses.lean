import OAI.Probability.SATComputability.ClauseRestoration

namespace OAI

namespace FixedClauseThreshold.Computability

open scoped Classical

abbrev Triple (A : Type*) := A × A × A
abbrev TripleClasses (A : Type*) :=
  Triple A ⊕ (Fin 3 × Bool × A × A) ⊕ (Fin 3 × Bool × Bool × A) ⊕ Triple Bool

def splitTriple {A : Type*} : Triple (Bool ⊕ A) → TripleClasses A
  | (.inr a,.inr b,.inr c) => .inl (a,b,c)
  | (.inl a,.inr b,.inr c) => .inr (.inl (0,a,b,c))
  | (.inr a,.inl b,.inr c) => .inr (.inl (1,b,a,c))
  | (.inr a,.inr b,.inl c) => .inr (.inl (2,c,a,b))
  | (.inr a,.inl b,.inl c) => .inr (.inr (.inl (0,b,c,a)))
  | (.inl a,.inr b,.inl c) => .inr (.inr (.inl (1,a,c,b)))
  | (.inl a,.inl b,.inr c) => .inr (.inr (.inl (2,a,b,c)))
  | (.inl a,.inl b,.inl c) => .inr (.inr (.inr (a,b,c)))

def joinTriple {A : Type*} : TripleClasses A → Triple (Bool ⊕ A)
  | .inl (a,b,c) => (.inr a,.inr b,.inr c)
  | .inr (.inl (i,b,a,c)) =>
      if i = 0 then (.inl b,.inr a,.inr c)
      else if i = 1 then (.inr a,.inl b,.inr c)
      else (.inr a,.inr c,.inl b)
  | .inr (.inr (.inl (i,a,b,c))) =>
      if i = 0 then (.inr c,.inl a,.inl b)
      else if i = 1 then (.inl a,.inr c,.inl b)
      else (.inl a,.inl b,.inr c)
  | .inr (.inr (.inr (a,b,c))) => (.inl a,.inl b,.inl c)

def tripleClassesEquiv (A : Type*) : Triple (Bool ⊕ A) ≃ TripleClasses A where
  toFun := splitTriple
  invFun := joinTriple
  left_inv := by
    rintro ⟨a,b,c⟩
    cases a <;> cases b <;> cases c <;> rfl
  right_inv := by
    rintro (⟨a,b,c⟩ | (⟨i,a,b,c⟩ | (⟨i,a,b,c⟩ | ⟨a,b,c⟩)))
    · rfl
    · fin_cases i <;> rfl
    · fin_cases i <;> rfl
    · rfl

def literalSplitEquiv (n : ℕ) : SignedLiteral (n+1) ≃ Bool ⊕ SignedLiteral n where
  toFun l := Fin.cases (.inl l.2) (fun j => .inr (j,l.2)) l.1
  invFun := fun l => match l with
    | .inl b => (0,b)
    | .inr (j,b) => (j.succ,b)
  left_inv := by
    rintro ⟨i,b⟩
    refine Fin.cases rfl (fun j => ?_) i
    rfl
  right_inv := by
    rintro (b | ⟨j,b⟩) <;> rfl

def tripleVectorEquiv (A : Type*) : (Fin 3 → A) ≃ Triple A where
  toFun f := (f 0,f 1,f 2)
  invFun t := ![t.1,t.2.1,t.2.2]
  left_inv := by intro f; funext i; fin_cases i <;> rfl
  right_inv := by rintro ⟨a,b,c⟩; rfl

def clauseClassesEquiv (n : ℕ) : (Fin 3 → SignedLiteral (n+1)) ≃ TripleClasses (SignedLiteral n) :=
  (Equiv.arrowCongr (Equiv.refl _) (literalSplitEquiv n)).trans
    ((tripleVectorEquiv _).trans (tripleClassesEquiv _))

theorem clauseClasses_base_card (n : ℕ) :
    Fintype.card (Triple (SignedLiteral n)) = 8*n^3 := by
  simp [Triple, SignedLiteral, Fintype.card_prod, Fintype.card_fin]
  ring

theorem clauseClasses_single_card (n : ℕ) :
    Fintype.card (Fin 3 × Bool × SignedLiteral n × SignedLiteral n) = 24*n^2 := by
  simp [SignedLiteral, Fintype.card_prod, Fintype.card_fin]
  ring

theorem clauseClasses_double_card (n : ℕ) :
    Fintype.card (Fin 3 × Bool × Bool × SignedLiteral n) = 24*n := by
  simp [SignedLiteral, Fintype.card_prod, Fintype.card_fin]
  ring

end FixedClauseThreshold.Computability

end OAI
