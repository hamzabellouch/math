import OAI.NumberTheory.TwoPoint.Walks.ProhibitedWordIdentity
import OAI.NumberTheory.TwoPoint.Bounds.DepartureWeightBounds

namespace OAI

/-! Positivity, crude size and retained divisibility of the actual departure weights. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma retainedEdgeDeparture_le_crude (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : SignedStep → ℕ → Prop) (g : ℤ → ℝ) (L K : ℝ)
    (extra : SignedStep → ℤ → Prop) (h : ℕ) (hL : 0 ≤ L)
    (hu : ∀ q, 0 ≤ u q) (hub : ∀ q, u q ≤ crudePaddingWeight q)
    (hg : ∀ n, 1 ≤ (g n) ^ 2) (t : SignedStep) (n : ℤ) :
    retainedEdgeDeparture Q u eligible g L K extra h t n ≤ L * crudePaddingWeight t.padding := by
  unfold retainedEdgeDeparture
  split_ifs
  · exact (div_le_self (mul_nonneg hL (hu _)) (hg n)).trans
      (mul_le_mul_of_nonneg_left (hub _) hL)
  · exact mul_nonneg hL (by unfold crudePaddingWeight; positivity)

theorem retained_word_le_crude {R : ℕ}
    (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : SignedStep → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ) (extra : SignedStep → ℤ → Prop)
    (h : ℕ) (hL : 0 ≤ L) (hu : ∀ q, 0 ≤ u q)
    (hub : ∀ q, u q ≤ crudePaddingWeight q) (hg : ∀ n, 1 ≤ (g n) ^ 2)
    (step : Fin R → SignedStep) (n : ℤ) :
    scalarWalkProduct h (retainedEdgeDeparture Q u eligible g L K extra h) n (List.ofFn step) ≤
      ∏ i, L * crudePaddingWeight (step i).padding := by
  rw [scalarWalkProduct_ofFn]
  apply prod_le_prod₀
  · intro i _
    exact retainedEdgeDeparture_nonneg Q u eligible g L K extra h hL hu _ _
  · intro i _
    exact retainedEdgeDeparture_le_crude Q u eligible g L K extra h hL hu hub hg _ _

theorem retained_word_padding_divisibility {R : ℕ}
    (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : SignedStep → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ) (extra : SignedStep → ℤ → Prop)
    (h : ℕ) (step : Fin R → SignedStep) (n : ℤ)
    (hn : scalarWalkProduct h (retainedEdgeDeparture Q u eligible g L K extra h)
      n (List.ofFn step) ≠ 0) (i : Fin R) :
    ((step i).padding : ℤ) ∣ n + wordDisplacement h ((List.ofFn step).take i.val) := by
  rw [scalarWalkProduct_ofFn] at hn
  have hi : retainedEdgeDeparture Q u eligible g L K extra h (step i)
      (n + wordDisplacement h ((List.ofFn step).take i.val)) ≠ 0 := by
    intro hi
    exact hn (prod_eq_zero (mem_univ i) hi)
  unfold retainedEdgeDeparture at hi
  split_ifs at hi with ht
  · exact ht.2.2.1
  · exact (hi rfl).elim

theorem lifted_retained_word_padding_tests {h J M R B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : SignedStep → ℕ → Prop) (g : ℤ → ℝ) (L K : ℝ)
    (extra : SignedStep → ℤ → Prop) (step : Fin R → SignedStep)
    (x : ↥(data.P ∪ data.Q) → Fin B)
    (hx : data.residueValue (fun n => scalarWalkProduct h
      (retainedEdgeDeparture Q u eligible g L K extra h) n (List.ofFn step)) x ≠ 0) :
    MainPaddingTests Subtype.val h B (List.ofFn step) x := by
  intro k p hp
  have hk : k.val < R := by simpa only [List.length_ofFn] using k.isLt
  let i : Fin R := ⟨k.val, hk⟩
  have he : (List.ofFn step).get k = step i := by
    change (List.ofFn step)[k.val] = step i
    simp only [List.getElem_ofFn]
    rfl
  rw [he] at hp
  have hd := retained_word_padding_divisibility Q u eligible g L K extra h step
    (data.residueOrigin x) hx i
  have hpdiv : (p.val : ℤ) ∣ data.residueOrigin x +
      wordDisplacement h ((List.ofFn step).take k.val) :=
    (show (p.val : ℤ) ∣ ((step i).padding : ℤ) by
      exact_mod_cast (Nat.mem_primeFactors.mp hp).2.1).trans hd
  exact (residue_offset_divisibility ((x p).val : ZMod p.val) _ _
    (data.residueOrigin_spec x p)).mp hpdiv

end TwoPointCorrelations

end OAI
