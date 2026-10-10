import Mathlib

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

noncomputable def localChoiceRank {α : Type*} (C : Finset α) (a : α) : ℕ := by
  classical
  exact if h : a ∈ C then ((Fintype.equivFin {a // a ∈ C}) ⟨a,h⟩).val else 0

lemma localChoiceRank_lt {α : Type*} (C : Finset α) (a : α) (ha : a ∈ C) :
    localChoiceRank C a < C.card := by
  classical
  simp only [localChoiceRank,dite_eq_left ha]
  simpa only [Fintype.card_coe] using (Fintype.equivFin {a // a ∈ C} ⟨a,ha⟩).isLt

lemma localChoiceRank_injective {α : Type*} (C : Finset α) {a b : α}
    (ha : a ∈ C) (hb : b ∈ C) (he : localChoiceRank C a = localChoiceRank C b) : a = b := by
  classical
  simp only [localChoiceRank,dite_eq_left ha,dite_eq_left hb] at he
  have he' := (Fintype.equivFin {a // a ∈ C}).injective (Fin.ext he)
  exact congrArg Subtype.val he'

noncomputable def prefixChoiceValues {n : ℕ} {α : Type*}
    (S : Finset (Fin n → α)) (f : Fin n → α) (i : Fin n) : Finset α := by
  classical
  exact (S.filter (fun g => ∀ j, j < i → g j = f j)).image (fun g => g i)

lemma prefixChoiceValues_self {n : ℕ} {α : Type*}
    (S : Finset (Fin n → α)) (f : Fin n → α) (hf : f ∈ S) (i : Fin n) :
    f i ∈ prefixChoiceValues S f i := by
  classical
  exact Finset.mem_image.mpr ⟨f,Finset.mem_filter.mpr ⟨hf,fun _ _ => rfl⟩,rfl⟩

lemma prefixChoiceValues_eq {n : ℕ} {α : Type*}
    (S : Finset (Fin n → α)) (f g : Fin n → α) (i : Fin n)
    (he : ∀ j, j < i → f j = g j) : prefixChoiceValues S f i = prefixChoiceValues S g i := by
  classical
  unfold prefixChoiceValues
  congr 1
  apply Finset.filter_congr
  intro q _
  constructor <;> intro h j hj
  · exact (h j hj).trans (he j hj)
  · exact (h j hj).trans (he j hj).symm

theorem finite_branching_family_bound {n : ℕ} {α : Type*}
    (S : Finset (Fin n → α)) (b : ℕ)
    (hb : ∀ f ∈ S, ∀ i, (prefixChoiceValues S f i).card ≤ b) : S.card ≤ b^n := by
  classical
  let code : {f // f ∈ S} → (Fin n → Fin b) := fun f i =>
    ⟨localChoiceRank (prefixChoiceValues S f.val i) (f.val i),
      (localChoiceRank_lt _ _ (prefixChoiceValues_self S f.val f.property i)).trans_le
        (hb f.val f.property i)⟩
  have hinj : Function.Injective code := by
    intro f g hcode
    apply Subtype.ext
    funext i
    have hrec : ∀ k, ∀ hk : k < n, f.val ⟨k,hk⟩ = g.val ⟨k,hk⟩ := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
        intro hk
        let i : Fin n := ⟨k,hk⟩
        have hprev : ∀ j, j < i → f.val j = g.val j := by
          intro j hj
          exact ih j.val hj j.isLt
        have heC := prefixChoiceValues_eq S f.val g.val i hprev
        have hval := congrArg Fin.val (congrFun hcode i)
        change localChoiceRank (prefixChoiceValues S f.val i) (f.val i) =
          localChoiceRank (prefixChoiceValues S g.val i) (g.val i) at hval
        rw [← heC] at hval
        apply localChoiceRank_injective _ (prefixChoiceValues_self S f.val f.property i) _ hval
        rw [heC]
        exact prefixChoiceValues_self S g.val g.property i
    exact hrec i.val i.isLt
  have h := Fintype.card_le_of_injective code hinj
  simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_fin] using h

end SharpTerminalLeave

end

end OAI
