import OAI.Probability.MatroidProphet.Main

namespace OAI

/-!
# Exact conditional fibers of a finite Bernoulli product law

A fixed outside mask is a genuine conditioning event. Restricting the full
product-law expectation to that event factors into its atom probability times
the expectation over the unrevealed coordinates. The unnormalized identity
also covers zero-probability fibers and endpoint Bernoulli rates.
-/

namespace MatroidProphet
open Finset
variable {α : Type*} [DecidableEq α]

/-- The weighted expectation of a single supported mask atom. -/
lemma bitsExpectation_mask_atom (q : α → ℝ) (V A : Finset α)
    (hA : A ⊆ V) (c : ℝ) :
    bitsExpectation q V (fun S => if S = A then c else 0) =
      bitsWeight q V A * c := by
  simp [bitsExpectation, mul_ite, hA]

/-- Restrict a full product-law expectation to one outside-coordinate fiber.
There are no positivity assumptions: null fibers are handled exactly. -/
theorem bitsExpectation_fixed_outside_event (q : α → ℝ)
    (V G A : Finset α) (hG : G ⊆ V) (hA : A ⊆ V \ G)
    (f : Finset α → ℝ) :
    bitsExpectation q V (fun T => if T \ G = A then f T else 0) =
      bitsWeight q (V \ G) A *
        bitsExpectation q G (fun B => f (A ∪ B)) := by
  rw [bitsExpectation_split q V G hG]
  have hf : bitsExpectation q (V \ G)
      (fun S => bitsExpectation q G
        (fun B => if (S ∪ B) \ G = A then f (S ∪ B) else 0)) =
      bitsExpectation q (V \ G) (fun S =>
        if S = A then bitsExpectation q G (fun B => f (A ∪ B)) else 0) := by
    apply bitsExpectation_congr
    intro S hS
    have hout (B : Finset α) (hB : B ⊆ G) : (S ∪ B) \ G = S := by
      ext e
      simp only [mem_sdiff, mem_union]
      constructor
      · rintro ⟨heS | heB, heG⟩
        · exact heS
        · exact False.elim (heG (hB heB))
      · intro heS
        exact ⟨Or.inl heS, (mem_sdiff.mp (hS heS)).2⟩
    by_cases hSA : S = A
    · subst S
      rw [ite_eq_left rfl]
      apply bitsExpectation_congr
      intro B hB
      rw [hout B hB, ite_eq_left rfl]
    · rw [ite_eq_right hSA]
      calc
        _ = bitsExpectation q G (fun _ => 0) := by
          apply bitsExpectation_congr
          intro B hB
          rw [hout B hB, ite_eq_right hSA]
        _ = 0 := bitsExpectation_const q G 0
  rw [hf]
  exact bitsExpectation_mask_atom q (V \ G) A hA _

/-- The probability of a specified outside mask is exactly its product atom. -/
theorem bitsExpectation_fixed_outside_probability (q : α → ℝ)
    (V G A : Finset α) (hG : G ⊆ V) (hA : A ⊆ V \ G) :
    bitsExpectation q V (fun T => if T \ G = A then 1 else 0) =
      bitsWeight q (V \ G) A := by
  simpa only [bitsExpectation_const, mul_one] using
    bitsExpectation_fixed_outside_event q V G A hG hA (fun _ => 1)

/-- On a nonnull outside fiber, the normalized conditional expectation is
exactly the fresh-coordinate expectation used in the accounting contract. -/
theorem bitsExpectation_condition_on_outside (q : α → ℝ)
    (V G A : Finset α) (hG : G ⊆ V) (hA : A ⊆ V \ G)
    (hpos : bitsWeight q (V \ G) A ≠ 0) (f : Finset α → ℝ) :
    bitsExpectation q V (fun T => if T \ G = A then f T else 0) /
      bitsExpectation q V (fun T => if T \ G = A then 1 else 0) =
    bitsExpectation q G (fun B => f (A ∪ B)) := by
  rw [bitsExpectation_fixed_outside_event q V G A hG hA f,
    bitsExpectation_fixed_outside_probability q V G A hG hA]
  simp [hpos]

/-- Interior coordinate rates make every outside atom positive, including
empty/full masks and the empty outside ground set. -/
lemma bitsWeight_pos_of_interior (q : α → ℝ) (V A : Finset α)
    (hq0 : ∀ e ∈ V, 0 < q e) (hq1 : ∀ e ∈ V, q e < 1) :
    0 < bitsWeight q V A := by
  unfold bitsWeight
  apply Finset.prod_pos
  intro e he
  split_ifs
  · exact hq0 e he
  · exact sub_pos.mpr (hq1 e he)

/-- Constant interior-rate specialization: no nonnull-fiber premise remains.
This applies in particular to the source's `t = 2⁻¹⁴⁰`. -/
theorem bitsExpectation_condition_on_outside_const
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (V G A : Finset α) (hG : G ⊆ V) (hA : A ⊆ V \ G)
    (f : Finset α → ℝ) :
    bitsExpectation (fun _ => t) V (fun T => if T \ G = A then f T else 0) /
      bitsExpectation (fun _ => t) V (fun T => if T \ G = A then 1 else 0) =
    bitsExpectation (fun _ => t) G (fun B => f (A ∪ B)) := by
  exact bitsExpectation_condition_on_outside (fun _ => t) V G A hG hA
    (ne_of_gt (bitsWeight_pos_of_interior _ _ _ (fun _ _ => ht0) (fun _ _ => ht1))) f

end MatroidProphet

end OAI
