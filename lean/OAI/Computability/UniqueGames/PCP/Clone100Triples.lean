import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace OAI

section

/-! The concrete clone sample space. Global distinctness is a stronger
conditioning rule than distinctness only at repeated original variables.
It retains the same 3/100 bound and makes the number of copies uniform. -/

namespace UniqueGamesTheorem.Outer.Clone100Triples

abbrev Index := Fin 100
abbrev Triple := Index × Index × Index

def good (t : Triple) : Prop :=
  t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2

instance : DecidablePred good := fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

abbrev GoodTriple := {t : Triple // good t}

def toEmbedding (t : GoodTriple) : Fin 3 ↪ Index where
  toFun := ![t.val.1, t.val.2.1, t.val.2.2]
  inj' := by
    have h01 := t.property.1
    have h02 := t.property.2.1
    have h12 := t.property.2.2
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

def fromEmbedding (f : Fin 3 ↪ Index) : GoodTriple :=
  ⟨(f 0, f 1, f 2), by
    constructor
    · exact fun h => (by decide : (0 : Fin 3) ≠ 1) (f.injective h)
    constructor
    · exact fun h => (by decide : (0 : Fin 3) ≠ 2) (f.injective h)
    · exact fun h => (by decide : (1 : Fin 3) ≠ 2) (f.injective h)⟩

def embeddingEquiv : GoodTriple ≃ (Fin 3 ↪ Index) where
  toFun := toEmbedding
  invFun := fromEmbedding
  left_inv t := by
    apply Subtype.ext
    rfl
  right_inv f := by
    ext i
    fin_cases i <;> rfl

theorem card_goodTriple : Fintype.card GoodTriple = 970200 := by
  rw [Fintype.card_congr embeddingEquiv, Fintype.card_embedding_eq]
  norm_num [Nat.descFactorial_succ]

theorem card_triple : Fintype.card Triple = 1000000 := by
  norm_num [Fintype.card_prod, Fintype.card_fin]

instance : Nonempty GoodTriple :=
  ⟨⟨(0, 1, 2), by decide⟩⟩

end UniqueGamesTheorem.Outer.Clone100Triples

end

end OAI
