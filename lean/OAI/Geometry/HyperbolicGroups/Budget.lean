import Mathlib

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction
namespace SparsePattern
open scoped BigOperators

/-- Independent table entry types, with their coordinate supports and critical costs.
The table model of Sections 2 and 4 is a concrete instance. -/
structure Pattern (F R : Type*) [Fintype F] [Fintype R] where
  support : R → Finset F
  cost : R → ℤ
  nonneg : ∀ r, 0 ≤ cost r

variable {F R : Type*} [Fintype F] [Fintype R] [DecidableEq F]

namespace Pattern

def exponent (P : Pattern F R) (W : Finset F) : ℤ :=
  W.card - ∑ r, if P.support r ⊆ W then P.cost r else 0

lemma exponent_submodular (P : Pattern F R) (S T : Finset F) :
    P.exponent (S ∪ T) + P.exponent (S ∩ T) ≤ P.exponent S + P.exponent T := by
  classical
  have hcost : (∑ r, if P.support r ⊆ S then P.cost r else 0) +
      (∑ r, if P.support r ⊆ T then P.cost r else 0) ≤
      (∑ r, if P.support r ⊆ S ∪ T then P.cost r else 0) +
      (∑ r, if P.support r ⊆ S ∩ T then P.cost r else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro r _
    by_cases hS : P.support r ⊆ S <;> by_cases hT : P.support r ⊆ T
    · simp [hS, hT, Finset.subset_union_left.trans' hS, Finset.subset_inter hS hT]
    · have hu : P.support r ⊆ S ∪ T := hS.trans Finset.subset_union_left
      have hi : ¬P.support r ⊆ S ∩ T := fun h => hT (h.trans Finset.inter_subset_right)
      simp [hS, hT, hu, hi]
    · have hu : P.support r ⊆ S ∪ T := hT.trans Finset.subset_union_right
      have hi : ¬P.support r ⊆ S ∩ T := fun h => hS (h.trans Finset.inter_subset_left)
      simp [hS, hT, hu, hi]
    · have hi : ¬P.support r ⊆ S ∩ T := fun h => hS (h.trans Finset.inter_subset_left)
      simp only [hS, hT, hi, ite_false, add_zero]
      split_ifs <;> simp [P.nonneg]
  have hc : ((S ∪ T).card : ℤ) + (S ∩ T).card = S.card + T.card := by
    exact_mod_cast Finset.card_union_add_card_inter S T
  unfold exponent
  linarith

lemma exponent_eq_card (P : Pattern F R) (I : Finset F)
    (hI : ∀ r, ¬P.support r ⊆ I) : P.exponent I = I.card := by
  simp [exponent, hI]

/-- The maximal critical closure in Section 4. The conclusions retain a full
unit integer margin, not merely strictness. -/
theorem critical_closure (P : Pattern F R) (I : Finset F) (e : F)
    (he : e ∉ I) (hI : P.exponent I = I.card)
    (hbudget : ∀ W, I ⊆ W → (I.card : ℤ) ≤ P.exponent W)
    (htest : ∀ W, insert e I ⊆ W → ((insert e I).card : ℤ) ≤ P.exponent W) :
    ∃ U : Finset F, I ⊆ U ∧ P.exponent U = I.card ∧ e ∉ U ∧
      ∀ V : Finset F, V.Nonempty → Disjoint V U →
        1 ≤ P.exponent (U ∪ V) - P.exponent U := by
  classical
  let B : Finset (Finset F) := Finset.univ.filter (fun U => I ⊆ U ∧ P.exponent U = I.card)
  have hmem : I ∈ B := by simp [B, hI]
  obtain ⟨U, hU, hmax⟩ := B.exists_max_image Finset.card ⟨I, hmem⟩
  have hU' : I ⊆ U ∧ P.exponent U = I.card := (Finset.mem_filter.mp hU).2
  refine ⟨U, hU'.1, hU'.2, ?_, ?_⟩
  · intro heU
    have hh := htest U (Finset.insert_subset heU hU'.1)
    rw [Finset.card_insert_of_notMem he, Nat.cast_add, Nat.cast_one, hU'.2] at hh
    omega
  · intro V hV hd
    have hsub : I ⊆ U ∪ V := hU'.1.trans Finset.subset_union_left
    have hb := hbudget (U ∪ V) hsub
    have hne : P.exponent (U ∪ V) ≠ (I.card : ℤ) := by
      intro heq
      have hm : U ∪ V ∈ B := by simp [B, hsub, heq]
      have hm' := hmax (U ∪ V) hm
      have hc : (U ∪ V).card = U.card + V.card :=
        Finset.card_union_of_disjoint hd.symm
      have hv := Finset.card_pos.mpr hV
      omega
    rw [hU'.2]
    omega

end Pattern
end SparsePattern


end HyperbolicObstruction
end
end
end

end OAI
