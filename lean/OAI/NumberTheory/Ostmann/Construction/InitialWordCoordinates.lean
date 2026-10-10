import OAI.NumberTheory.Ostmann.Construction.SignedAtomSchedule
import OAI.NumberTheory.Ostmann.Construction.WordCopyCoordinates

namespace OAI

/-! # Explicit original word and cell coordinates for the signed atom schedule -/

namespace Ostmann
open scoped Classical BigOperators

def initialWordSize {C : Type*} (k : ℕ) (s : C → ℕ) : Option C → ℕ
  | none => k
  | some c => s c

def positiveWordConstituentEquiv {C : Type*} (k : ℕ) (s : C → ℕ) :
    (Σ a : Option C, Fin (initialWordSize k s a)) ≃ (Fin k ⊕ (Σ c, Fin (s c))) where
  toFun := fun ⟨a, i⟩ => match a with
    | none => Sum.inl i
    | some c => Sum.inr ⟨c, i⟩
  invFun := fun z => match z with
    | Sum.inl i => ⟨none, i⟩
    | Sum.inr ⟨c, i⟩ => ⟨some c, i⟩
  left_inv := by rintro ⟨a, i⟩; cases a <;> rfl
  right_inv := by rintro (i | ⟨c, i⟩) <;> rfl

def signedConstituentEquiv {I : Type*} (size : I → ℕ) :
    (Σ a : Bool × I, Fin (size a.2)) ≃
      ((Σ i, Fin (size i)) ⊕ (Σ i, Fin (size i))) where
  toFun := fun ⟨⟨b, i⟩, j⟩ => if b then Sum.inl ⟨i, j⟩ else Sum.inr ⟨i, j⟩
  invFun := fun z => match z with
    | Sum.inl ⟨i, j⟩ => ⟨⟨true, i⟩, j⟩
    | Sum.inr ⟨i, j⟩ => ⟨⟨false, i⟩, j⟩
  left_inv := by rintro ⟨⟨b, i⟩, j⟩; cases b <;> rfl
  right_inv := by rintro (⟨i, j⟩ | ⟨i, j⟩) <;> rfl

def positiveWordTupleEquiv {C : Type*} (k m : ℕ) (s : C → ℕ)
    (cell : (Σ c, Fin (s c)) ≃ Fin m) :
    (Σ a : Option C, Fin (initialWordSize k s a)) ≃ Fin (k + m) :=
  (positiveWordConstituentEquiv k s).trans
    ((Equiv.sumCongr (Equiv.refl _) cell).trans finSumFinEquiv)

def initialWordTupleEquiv {C : Type*} (k m : ℕ) (s : C → ℕ)
    (cell : (Σ c, Fin (s c)) ≃ Fin m) :
    (Σ a : Bool × Option C, Fin (initialWordSize k s a.2)) ≃
      Fin ((k + m) + (k + m)) :=
  (signedConstituentEquiv (initialWordSize k s)).trans
    ((Equiv.sumCongr (positiveWordTupleEquiv k m s cell)
      (positiveWordTupleEquiv k m s cell)).trans finSumFinEquiv)

theorem initialWordTupleEquiv_positive {C : Type*} (k m : ℕ) (s : C → ℕ)
    (cell : (Σ c, Fin (s c)) ≃ Fin m)
    (a : Option C) (i : Fin (initialWordSize k s a)) :
    initialWordTupleEquiv k m s cell ⟨⟨true, a⟩, i⟩ =
      (positiveWordTupleEquiv k m s cell ⟨a, i⟩).castAdd (k + m) := rfl

theorem initialWordTupleEquiv_negative {C : Type*} (k m : ℕ) (s : C → ℕ)
    (cell : (Σ c, Fin (s c)) ≃ Fin m)
    (a : Option C) (i : Fin (initialWordSize k s a)) :
    initialWordTupleEquiv k m s cell ⟨⟨false, a⟩, i⟩ =
      (positiveWordTupleEquiv k m s cell ⟨a, i⟩).natAdd (k + m) := rfl

theorem initialWordTupleEquiv_character {C : Type*} (k m : ℕ) (s : C → ℕ)
    (cell : (Σ c, Fin (s c)) ≃ Fin m) (χ : ∀ p : ℕ, DirichletCharacter ℂ p)
    (i : Σ a : Bool × Option C, Fin (initialWordSize k s a.2)) :
    wordCopyCharacter k m χ (initialWordTupleEquiv k m s cell i) =
      signedAtomCharacter (initialWordSize k s) χ i := by
  rcases i with ⟨⟨b, a⟩, i⟩
  cases b with
  | false =>
      rw [initialWordTupleEquiv_negative]
      simp only [wordCopyCharacter, Fin.append_right]
      rfl

  | true =>
      rw [initialWordTupleEquiv_positive]
      simp only [wordCopyCharacter, Fin.append_left]
      rfl

theorem wordCopyEquiv_positive_word {A : Type*} (k m : ℕ)
    (y : Fin ((k + m) + (k + m)) → A) (i : Fin k) :
    ((wordCopyEquiv A k m).symm y).1.1 i = y ((i.castAdd m).castAdd (k + m)) := by
  have h := congrFun ((wordCopyEquiv A k m).apply_symm_apply y)
    ((i.castAdd m).castAdd (k + m))
  change Fin.append (Fin.append _ _) (Fin.append _ _) _ = _ at h
  simp only [Fin.append_left] at h
  exact h

theorem wordCopyEquiv_negative_word {A : Type*} (k m : ℕ)
    (y : Fin ((k + m) + (k + m)) → A) (i : Fin k) :
    ((wordCopyEquiv A k m).symm y).2.1 i = y ((i.castAdd m).natAdd (k + m)) := by
  have h := congrFun ((wordCopyEquiv A k m).apply_symm_apply y)
    ((i.castAdd m).natAdd (k + m))
  change Fin.append (Fin.append _ _) (Fin.append _ _) _ = _ at h
  simp only [Fin.append_left, Fin.append_right] at h
  exact h

theorem initialWordTuple_positive_word {A C : Type*} (k m : ℕ) (s : C → ℕ)
    (cell : (Σ c, Fin (s c)) ≃ Fin m) (y : Fin ((k + m) + (k + m)) → A)
    (i : Fin k) :
    ((wordCopyEquiv A k m).symm y).1.1 i =
      y (initialWordTupleEquiv k m s cell ⟨(true, none), i⟩) :=
  wordCopyEquiv_positive_word k m y i

theorem initialWordTuple_negative_word {A C : Type*} (k m : ℕ) (s : C → ℕ)
    (cell : (Σ c, Fin (s c)) ≃ Fin m) (y : Fin ((k + m) + (k + m)) → A)
    (i : Fin k) :
    ((wordCopyEquiv A k m).symm y).2.1 i =
      y (initialWordTupleEquiv k m s cell ⟨(false, none), i⟩) :=
  wordCopyEquiv_negative_word k m y i

end Ostmann

end OAI
