import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.ArithmeticSaving
open Finset Classical
noncomputable section
variable {α : Type*} [DecidableEq α]

theorem independent_tests (R : α → α → Prop) (d : ℕ) (A : Finset α)
    (hout : ∀ a ∈ A,(A.filter (R a)).card ≤ d) :
    ∃ I ⊆ A,A.card ≤ (2*d+1)*I.card ∧
      ∀ a ∈ I,∀ b ∈ I,a≠b → ¬R a b := by
  induction A using Finset.strongInductionOn with
  | _ A ih =>
    by_cases hA : A.Nonempty
    · let degree (a : α) := (A.filter (fun b => R a b ∨ R b a)).card
      have hsum : ∑ a ∈ A,degree a ≤ ∑ _a ∈ A,2*d := by
        have hin : (∑ a ∈ A,(A.filter (fun b => R b a)).card) =
            ∑ a ∈ A,(A.filter (R a)).card := by
          simp only [card_eq_sum_ones,sum_filter]
          rw [sum_comm]
        calc
          _ ≤ ∑ a ∈ A,((A.filter (R a)).card+(A.filter (fun b => R b a)).card) := by
            apply sum_le_sum
            intro a ha
            have he : A.filter (fun b => R a b ∨ R b a)=A.filter (R a) ∪ A.filter (fun b => R b a) := by
              ext b; simp; tauto
            change (A.filter (fun b => R a b ∨ R b a)).card ≤ _
            rw [he]
            exact card_union_le _ _
          _ = (∑ a ∈ A,(A.filter (R a)).card)+(∑ a ∈ A,(A.filter (R a)).card) := by
            rw [sum_add_distrib,hin]
          _ ≤ (∑ _a ∈ A,d)+(∑ _a ∈ A,d) := Nat.add_le_add (sum_le_sum hout) (sum_le_sum hout)
          _ = _ := by simp; ring
      obtain ⟨v,hv,hdeg⟩ := exists_le_of_sum_le hA hsum
      let C := A.filter (fun a => a≠v ∧ ¬R v a ∧ ¬R a v)
      have hC : C ⊂ A := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨filter_subset _ _,?_⟩
        intro heq
        have : v ∈ C := heq.symm ▸ hv
        simp [C] at this
      have hcout : ∀ a ∈ C,(C.filter (R a)).card ≤ d := by
        intro a ha
        exact (card_le_card (filter_subset_filter _ (filter_subset _ _))).trans (hout a ((filter_subset _ _) ha))
      obtain ⟨I,hI,hcard,hind⟩ := ih C hC hcout
      have hvI : v ∉ I := by
        intro hin
        exact (mem_filter.mp (hI hin)).2.1 rfl
      have hremoved : A.card ≤ C.card+(2*d+1) := by
        have hsub : A ⊆ C ∪ insert v (A.filter (fun b => R v b ∨ R b v)) := by
          intro a ha
          by_cases hav : a=v
          · exact mem_union_right C (mem_insert.mpr (Or.inl hav))
          · by_cases hr : R v a ∨ R a v
            · exact mem_union_right C (mem_insert_of_mem (mem_filter.mpr ⟨ha,hr⟩))
            · exact mem_union_left _ (mem_filter.mpr ⟨ha,hav,not_or.mp hr⟩)
        have := (card_le_card hsub).trans (card_union_le _ _)
        have hi := card_insert_le v (A.filter (fun b => R v b ∨ R b v))
        dsimp only [degree] at hdeg
        omega
      refine ⟨insert v I,insert_subset hv (hI.trans (filter_subset _ _)),?_,?_⟩
      · rw [card_insert_of_notMem hvI]
        nlinarith
      · intro a ha b hb hab
        rcases mem_insert.mp ha with hav | ha
        · subst a
          rcases mem_insert.mp hb with hbv | hb
          · exact (hab hbv.symm).elim
          · exact (mem_filter.mp (hI hb)).2.2.1
        · rcases mem_insert.mp hb with hbv | hb
          · subst b
            exact (mem_filter.mp (hI ha)).2.2.2
          · exact hind a ha b hb hab
    · refine ⟨∅,empty_subset _,?_,by simp⟩
      rw [not_nonempty_iff_eq_empty.mp hA]
      simp

end
end OrdinaryCorrelations.ArithmeticSaving

end

end OAI
