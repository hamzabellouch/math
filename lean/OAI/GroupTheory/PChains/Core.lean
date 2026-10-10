import Mathlib.GroupTheory.PGroup
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Data.Finset.Lattice.Fold

namespace OAI

/-! The p-core of a subgroup, represented inside the ambient group. -/

namespace PCoreCancellation

variable {X : Type*} [Group X]

/-- A p-subgroup of `J` normalized by every element of `J`. -/
def NormalPIn (p : ℕ) (J P : Subgroup X) : Prop :=
  P ≤ J ∧ J ≤ Subgroup.normalizer (P : Set X) ∧ IsPGroup p P

/-- The ambient image of the p-core of `J`. -/
noncomputable def pCore (p : ℕ) (J : Subgroup X) : Subgroup X :=
  sSup {P | NormalPIn p J P}

theorem exists_normal_p_subgroup {p : ℕ} {J : Subgroup X}
    (hc : pCore p J ≠ ⊥) : ∃ P : Subgroup X, NormalPIn p J P ∧ P ≠ ⊥ := by
  classical
  by_contra hn
  have hall : ∀ P : Subgroup X, NormalPIn p J P → P = ⊥ := by
    intro P hp
    by_contra hP
    exact hn ⟨P, hp, hP⟩
  apply hc
  apply le_bot_iff.mp
  apply sSup_le
  intro P hp
  rw [hall P hp]

lemma normalPIn_bot (p : ℕ) (J : Subgroup X) : NormalPIn p J ⊥ := by
  refine ⟨bot_le, ?_, ?_⟩
  · calc
      J ≤ (⊤ : Subgroup X) := le_top
      _ = Subgroup.normalizer ((⊥ : Subgroup X) : Set X) :=
        (Subgroup.normalizer_eq_top (⊥ : Subgroup X)).symm
  · intro g
    exact ⟨0, Subsingleton.elim _ _⟩

lemma normalPIn_sup {p : ℕ} [Fact p.Prime] {J H K : Subgroup X}
    (hH : NormalPIn p J H) (hK : NormalPIn p J K) : NormalPIn p J (H ⊔ K) := by
  refine ⟨sup_le hH.1 hK.1, ?_, ?_⟩
  · exact (le_inf hH.2.1 hK.2.1).trans
      (Subgroup.inf_normalizer_le_normalizer_sup H K)
  · exact hH.2.2.to_sup_of_normal_left' hK.2.2 (hK.1.trans hH.2.1)

section Finite

variable [Fintype X]

noncomputable local instance : Fintype (Subgroup X) :=
  Fintype.ofInjective (fun H : Subgroup X => (H : Set X)) SetLike.coe_injective

/-- The p-core is a normal p-subgroup of `J`. -/
theorem pCore_normalPIn (p : ℕ) [Fact p.Prime] (J : Subgroup X) :
    NormalPIn p J (pCore p J) := by
  classical
  let s : Finset (Subgroup X) := Finset.univ.filter (NormalPIn p J)
  have heq : pCore p J = s.sup id := by
    apply le_antisymm
    · apply sSup_le
      intro Q hQ
      exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hQ⟩)
    · apply Finset.sup_le_iff.mpr
      intro Q hQ
      exact le_sSup (Finset.mem_filter.mp hQ).2
  rw [heq]
  have hfold : ∀ t : Finset (Subgroup X), (∀ Q ∈ t, NormalPIn p J Q) →
      NormalPIn p J (t.sup id) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa using normalPIn_bot p J
    | @insert Q t hQt ih =>
      intro h
      rw [Finset.sup_insert]
      exact normalPIn_sup (h Q (Finset.mem_insert_self _ _))
        (ih (fun R hR => h R (Finset.mem_insert_of_mem hR)))
  exact hfold s (fun Q hQ => (Finset.mem_filter.mp hQ).2)

/-- The p-core is the greatest normal p-subgroup of `J`. -/
theorem pCore_greatest (p : ℕ) [Fact p.Prime] (J : Subgroup X) :
    NormalPIn p J (pCore p J) ∧
      ∀ Q : Subgroup X, NormalPIn p J Q → Q ≤ pCore p J :=
  ⟨pCore_normalPIn p J, fun _ hQ => le_sSup hQ⟩

theorem pCore_eq_of_greatest (p : ℕ) [Fact p.Prime] (J P : Subgroup X)
    (hP : NormalPIn p J P) (hmax : ∀ Q, NormalPIn p J Q → Q ≤ P) :
    pCore p J = P :=
  le_antisymm (hmax _ (pCore_normalPIn p J)) (le_sSup hP)

end Finite

end PCoreCancellation

end OAI
