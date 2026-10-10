import OAI.NumberTheory.TwoPoint.Walks.RetainedEdgeRows
import OAI.NumberTheory.TwoPoint.Bounds.ProgressionBlockTesting
import OAI.NumberTheory.TwoPoint.Bounds.PrimePairCatalog

namespace OAI

/-! Inactive tuple/padding pairs contribute zero. Giving them step zero
lets the actual pair bound control every displacement in the block lemma. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def retainedPrimeStep {J : ℕ} {P : Fin J → Finset ℕ}
    {Q : Finset ℕ} (eligible : ℕ → ℕ → Prop) (h : ℕ)
    (e : ((j : Fin J) → P j) × Q) : ℕ :=
  if eligible (∏ j, (e.1 j).val) e.2.val then h * e.2.val * ∏ j, (e.1 j).val else 0

lemma retainedPrimeEdge_inactive {J : ℕ} (P : Fin J → Finset ℕ)
    (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop)
    (e : ((j : Fin J) → P j) × Q) (n m : ℤ)
    (he : ¬eligible (∏ j, (e.1 j).val) e.2.val) :
    retainedPrimeEdge P Q Qp u eligible L K W extra h gate keep e n m = 0 := by
  simp [retainedPrimeEdge, retainedLiouvilleEdge, he]

lemma retainedPrimeEdge_support_active {J : ℕ} (P : Fin J → Finset ℕ)
    (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop)
    (e : ((j : Fin J) → P j) × Q) (n m : ℤ)
    (hm : m ≠ n + retainedPrimeStep eligible h e) :
    retainedPrimeEdge P Q Qp u eligible L K W extra h gate keep e n m = 0 := by
  by_cases he : eligible (∏ j, (e.1 j).val) e.2.val
  · rw [retainedPrimeStep, ite_eq_left he] at hm
    exact retainedPrimeEdge_support P Q Qp u eligible L K W extra h gate keep e n m hm
  · exact retainedPrimeEdge_inactive P Q Qp u eligible L K W extra h gate keep e n m he

lemma retainedPrimeStep_le {J : ℕ} {P : Fin J → Finset ℕ} {Q : Finset ℕ}
    {L η : ℝ} {eligible : ℕ → ℕ → Prop} (h : ℕ)
    (hη : 0 < η) (hηone : η ≤ 1)
    (heligible : ∀ d q, eligible d q → PaddingPairEligible L η d q)
    (e : ((j : Fin J) → P j) × Q) :
    retainedPrimeStep eligible h e ≤ h * ⌊Real.exp (100 * L + 1)⌋₊ := by
  unfold retainedPrimeStep
  split_ifs with he
  · calc
      _ = h * ((∏ j, (e.1 j).val) * e.2.val) := by ring
      _ ≤ _ := Nat.mul_le_mul_left h (paddingPairEligible_product_upper hη hηone (heligible _ _ he))
  · exact Nat.zero_le _

lemma retainedPrimeEdge_active_step_eq {J : ℕ} (P : Fin J → Finset ℕ)
    (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop)
    (e : ((j : Fin J) → P j) × Q) (n : ℤ) :
    retainedPrimeEdge P Q Qp u eligible L K W extra h gate keep e n
      (n + retainedPrimeStep eligible h e) =
    retainedPrimeEdge P Q Qp u eligible L K W extra h gate keep e n
      (n + (h * e.2.val * ∏ j, (e.1 j).val : ℕ)) := by
  by_cases he : eligible (∏ j, (e.1 j).val) e.2.val
  · rw [retainedPrimeStep, ite_eq_left he]
  · rw [retainedPrimeEdge_inactive P Q Qp u eligible L K W extra h gate keep e n _ he,
      retainedPrimeEdge_inactive P Q Qp u eligible L K W extra h gate keep e n _ he]

lemma ambientLiouvilleBlockForm_active {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (M : ℕ) (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (hgate : ∀ d n m, gate d n m ↔ gate d m n)
    (keep : ℤ → Prop) (t : ℕ) :
    ambientLiouvilleBlockForm P M Q Qp u eligible L K W extra h gate keep t =
      (2 * (L : ℂ)) * edgeBlockSum univ (retainedPrimeStep eligible h)
        (fun e n => retainedPrimeEdge P Q Qp u eligible L K W extra h gate keep e n
          ((n : ℤ) + retainedPrimeStep eligible h e)) M t := by
  unfold ambientLiouvilleBlockForm
  dsimp only
  rw [primeBlockCompression_retained_identity P hprime hdisjoint M Q Qp u eligible
    L K W extra h gate hgate keep]
  rw [directed_block_form_eq _ _ (retainedPrimeEdge_support_active P Q Qp u eligible
    L K W extra h gate keep)]

lemma canonicalTraceFamily_pair_eligible (h : ℕ) (E : Finset ℕ) (W L : ℝ)
    (eligible : ℕ → ℕ → Prop) (hL : 1 ≤ L) (hW : 1 ≤ W)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) (d q : ℕ)
    (he : (d, q) ∈ (canonicalTraceFamily h E W L eligible hL hW hE).pairs) : eligible d q := by
  exact ((actualProhibitedPrimeFamily_pairs h _ _ E _ W L eligible _ _ hE d q).mp he).2.2.2

end TwoPointCorrelations

end OAI
