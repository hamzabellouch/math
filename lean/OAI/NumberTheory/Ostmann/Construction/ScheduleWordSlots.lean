import Mathlib.Data.Fintype.EquivFin
import OAI.NumberTheory.Ostmann.Construction.CopyScheduleSupport

namespace OAI

/-! # The surviving word slots are precisely the full binary copy paths -/

namespace Ostmann

noncomputable instance copyScheduleVertexFintype {I : Type*} [Fintype I] (n : ℕ) :
    Fintype (CopyScheduleVertex I n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype I)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype ((Bool × CopyScheduleVertex I n) ⊕ CopyScheduleVertex I n))

theorem copySchedulePath_injective {I : Type*} (n : ℕ) :
    Function.Injective (fun x : (Fin n → Bool) × I => copySchedulePath n x.1 x.2) := by
  induction n with
  | zero =>
    intro x y h
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · exact h
  | succ n ih =>
    rintro ⟨t, i⟩ ⟨u, j⟩ h
    change Sum.inl (t (Fin.last n), copySchedulePath n (fun k => t k.castSucc) i) =
      Sum.inl (u (Fin.last n), copySchedulePath n (fun k => u k.castSucc) j) at h
    have he := Prod.mk.inj (Sum.inl.inj h)
    have hp : ((fun k : Fin n => t k.castSucc), i) = ((fun k : Fin n => u k.castSucc), j) := ih he.2
    apply Prod.ext
    · funext k
      refine Fin.lastCases he.1 (fun a => ?_) k
      exact congrFun (congrArg Prod.fst hp) a
    · exact congrArg (fun z : (Fin n → Bool) × I => z.2) hp

theorem surviving_word_is_path {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (v : CopyScheduleVertex I n)
    (hv : CopyScheduleSurvives role n v) (hw : copyScheduleRole role n v = .word) :
    ∃ (t : Fin n → Bool) (i : I), role i = .word ∧ v = copySchedulePath n t i := by
  induction n with
  | zero => exact ⟨fun j => Fin.elim0 j, v, hw, rfl⟩
  | succ n ih =>
    cases v with
    | inl q =>
      rcases q with ⟨b, v⟩
      change CopyScheduleSurvives role n v ∧ _ at hv
      change (copyScheduleRole role n v).afterCopy b = .word at hw
      have hrole : copyScheduleRole role n v = .word := by
        cases hr : copyScheduleRole role n v <;>
          cases b <;> simp_all [CopyScheduleRole.afterCopy]
      obtain ⟨t, i, hi, rfl⟩ := ih v hv.1 hrole
      exact ⟨Fin.snoc t b, i, hi, (copySchedulePath_snoc t b i).symm⟩
    | inr v =>
      change CopyScheduleSurvives role n v ∧ _ ∧ _ at hv
      change copyScheduleRole role n v = .word at hw
      have hc := hv.2.1
      rw [hw] at hc
      cases hc

abbrev SurvivingWordSlot {I : Type*} (role : I → CopyScheduleRole) (n : ℕ) :=
  {v : CopyScheduleVertex I n // CopyScheduleSurvives role n v ∧ copyScheduleRole role n v = .word}

noncomputable def survivingWordEquiv {I : Type*} (role : I → CopyScheduleRole) (n : ℕ) :
    ((Fin n → Bool) × {i : I // role i = .word}) ≃ SurvivingWordSlot role n :=
  Equiv.ofBijective (fun x => ⟨copySchedulePath n x.1 x.2.val,
    copyScheduleSurvives_path role x.2.val x.2.property n x.1,
    copyScheduleRole_path role x.2.val x.2.property n x.1⟩) (by
      constructor
      · intro x y h
        have he : (x.1, x.2.val) = (y.1, y.2.val) :=
          copySchedulePath_injective n (congrArg Subtype.val h)
        refine Prod.ext ?_ ?_
        · exact congrArg (fun z : (Fin n → Bool) × I => z.1) he
        · exact Subtype.ext (congrArg (fun z : (Fin n → Bool) × I => z.2) he)
      · intro v
        obtain ⟨t, i, hi, he⟩ := surviving_word_is_path role n v.val v.property.1 v.property.2
        exact ⟨(t, ⟨i, hi⟩), Subtype.ext he.symm⟩)

/-- The schedule has exactly 2^n independently sampled copies of each initial
word slot. No outside or discarded pivot label contributes to this count. -/
theorem surviving_word_card {I : Type*} [Fintype I] (role : I → CopyScheduleRole)
    (n : ℕ) :
    Nat.card (SurvivingWordSlot role n) =
      2 ^ n * Nat.card {i : I // role i = .word} := by
  classical
  calc
    _ = Nat.card ((Fin n → Bool) × {i : I // role i = .word}) :=
      (Nat.card_congr (survivingWordEquiv role n)).symm
    _ = _ := by simp only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

end Ostmann

end OAI
