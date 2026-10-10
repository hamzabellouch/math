import Mathlib
import OAI.Geometry.HyperbolicGroups.Budget

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction
namespace SparsePattern.Pattern
open scoped BigOperators
variable {F R B : Type*} [Fintype F] [Fintype R] [Fintype B] [DecidableEq F]
  (P : SparsePattern.Pattern F R)

/-- Cost of the unconditioned entries of one star branch supported in A∪V. -/
def branchCost (U A V : Finset F) : ℤ :=
  ∑ r, if P.support r ⊆ A ∪ V ∧ ¬P.support r ⊆ U then P.cost r else 0

/-- Exact critical exponent of a star-coordinate subset. Central coordinates
are counted once, and outside coordinates separately in each branch. -/
def starExponent (U A : Finset F) (V : B → Finset F) : ℤ :=
  P.exponent A + ∑ j, ((V j).card - P.branchCost U A (V j))

lemma branchCost_mono {U A A' V : Finset F} (hA : A ⊆ A') :
    P.branchCost U A V ≤ P.branchCost U A' V := by
  classical
  apply Finset.sum_le_sum
  intro r _
  by_cases h : P.support r ⊆ A ∪ V ∧ ¬P.support r ⊆ U
  · have h' : P.support r ⊆ A' ∪ V ∧ ¬P.support r ⊆ U :=
      ⟨h.1.trans (Finset.union_subset_union_left hA), h.2⟩
    simp [h, h']
  · simp only [h, ↓reduceIte]
    split_ifs <;> simp [P.nonneg]

lemma increment_eq {U V : Finset F} (hd : Disjoint U V) :
    P.exponent (U ∪ V) - P.exponent U = (V.card : ℤ) - P.branchCost U U V := by
  classical
  have hc : ((U ∪ V).card : ℤ) = U.card + V.card := by
    exact_mod_cast Finset.card_union_of_disjoint hd
  have he : (∑ r, if P.support r ⊆ U ∪ V then P.cost r else 0) =
      (∑ r, if P.support r ⊆ U then P.cost r else 0) + P.branchCost U U V := by
    rw [branchCost, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    by_cases hu : P.support r ⊆ U
    · simp [hu, hu.trans Finset.subset_union_left]
    · simp [hu]
  unfold exponent
  rw [hc, he]
  ring

lemma starExponent_lower {U A : Finset F} {V : B → Finset F} (hA : A ⊆ U)
    (hd : ∀ j, Disjoint U (V j)) :
    P.exponent A + ∑ j, (P.exponent (U ∪ V j) - P.exponent U) ≤ P.starExponent U A V := by
  unfold starExponent
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro j _
  rw [P.increment_eq (hd j)]
  exact sub_le_sub_left (P.branchCost_mono hA) _

lemma branchCost_empty {U V : Finset F} (hd : Disjoint U V)
    (hne : ∀ r, (P.support r).Nonempty) :
    P.branchCost U ∅ V = ∑ r, if P.support r ⊆ V then P.cost r else 0 := by
  classical
  apply Finset.sum_congr rfl
  intro r _
  simp only [Finset.empty_union]
  by_cases hv : P.support r ⊆ V
  · have hu : ¬P.support r ⊆ U := by
      intro hu
      obtain ⟨x,hx⟩ := hne r
      exact Finset.disjoint_left.mp hd (hu hx) (hv hx)
    simp [hv, hu]
  · simp [hv]

lemma starExponent_empty {U : Finset F} {V : B → Finset F}
    (hd : ∀ j, Disjoint U (V j)) (hne : ∀ r, (P.support r).Nonempty) :
    P.starExponent U ∅ V = ∑ j, P.exponent (V j) := by
  have hp : P.exponent ∅ = 0 := by
    unfold exponent
    simp only [Finset.card_empty, Nat.cast_zero, Finset.subset_empty]
    have ht (r : R) : P.support r ≠ ∅ := Finset.nonempty_iff_ne_empty.mp (hne r)
    simp [ht]
  unfold starExponent
  rw [hp, zero_add]
  apply Finset.sum_congr rfl
  intro j _
  rw [P.branchCost_empty (hd j) hne]
  rfl

/-- Extension overlaps retain at least one full integer of critical margin. -/
lemma extension_margin {U : Finset F} {V : B → Finset F}
    (hd : ∀ j, Disjoint U (V j)) (ha : ∃ j, (V j).Nonempty)
    (gap : ∀ W, W.Nonempty → Disjoint U W → 1 ≤ P.exponent (U ∪ W) - P.exponent U) :
    1 ≤ ∑ j, ((V j).card - P.branchCost U U (V j)) := by
  classical
  have hnon (j : B) : 0 ≤ (V j).card - P.branchCost U U (V j) := by
    rw [← P.increment_eq (hd j)]
    by_cases hv : (V j).Nonempty
    · exact (gap _ hv (hd j)).trans' (by norm_num)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hv, Finset.union_empty, sub_self]
  obtain ⟨j,hj⟩ := ha
  have hh := gap _ hj (hd j)
  rw [P.increment_eq (hd j)] at hh
  exact hh.trans (Finset.single_le_sum (fun i _ => hnon i) (Finset.mem_univ j))

/-- The leaf overlap margin, including the separate A=∅ case. The `active`
assumption records that W is a union of supports of shared entries, rather than
an arbitrary nonempty collection of coordinates. -/
theorem leaf_margin {U A : Finset F} {V : B → Finset F} {e : F}
    (hA : A ⊆ U) (hd : ∀ j, Disjoint U (V j))
    (budget : ∀ W : Finset F, (min 2 W.card : ℕ) ≤ P.exponent W)
    (supports : ∀ r, 3 ≤ (P.support r).card)
    (gap : ∀ W, W.Nonempty → Disjoint U W → 1 ≤ P.exponent (U ∪ W) - P.exponent U)
    (active : A = ∅ → (∃ j, (V j).Nonempty) ∧ ∀ j, (V j).Nonempty → 3 ≤ (V j).card) :
    1 ≤ P.starExponent U A V - ∑ j, if e ∈ V j then (1 : ℤ) else 0 := by
  classical
  by_cases hA0 : A = ∅
  · subst A
    have hne : ∀ r, (P.support r).Nonempty := fun r => Finset.card_pos.mp (by have := supports r; omega)
    rw [P.starExponent_empty hd hne, ← Finset.sum_sub_distrib]
    obtain ⟨⟨j,hj⟩, hv⟩ := active rfl
    have hlo (i : B) : 0 ≤ P.exponent (V i) - (if e ∈ V i then 1 else 0) := by
      have hh := budget (V i)
      by_cases hi : (V i).Nonempty
      · have hc := hv i hi
        have hm : min 2 (V i).card = 2 := by omega
        rw [hm] at hh
        split_ifs <;> omega
      · rw [Finset.not_nonempty_iff_eq_empty.mp hi] at hh ⊢
        simp only [Finset.notMem_empty, ↓reduceIte, sub_zero]
        simpa using hh
    have hc := hv j hj
    have hh := budget (V j)
    have hm : min 2 (V j).card = 2 := by omega
    rw [hm] at hh
    have hone : 1 ≤ P.exponent (V j) - (if e ∈ V j then 1 else 0) := by split_ifs <;> omega
    exact hone.trans (Finset.single_le_sum (fun i _ => hlo i) (Finset.mem_univ j))
  · have hcard : 0 < A.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hA0)
    have hb := budget A
    have hone : 1 ≤ P.exponent A := by omega
    have hi (j : B) : (if e ∈ V j then (1 : ℤ) else 0) ≤
        P.exponent (U ∪ V j) - P.exponent U := by
      by_cases hv : (V j).Nonempty
      · have hh := gap _ hv (hd j)
        split_ifs <;> omega
      · rw [Finset.not_nonempty_iff_eq_empty.mp hv]
        simp
    have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hi j)
    have hl := P.starExponent_lower hA hd
    omega

end SparsePattern.Pattern
end HyperbolicObstruction
end
end

section

end
end

end OAI
