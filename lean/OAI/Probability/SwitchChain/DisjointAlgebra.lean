import Mathlib

namespace OAI

namespace Problem315

theorem disjoint_plane_bound (x y ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    -(x ^ 2 + y ^ 2) * (1 - ρ ^ 2) ≤
      2 * x * y * ρ * (1 - ρ ^ 2) := by
  have hquad : 0 ≤ x ^ 2 + y ^ 2 + 2 * x * y * ρ := by
    have h₁ := mul_nonneg hρ0 (sq_nonneg (x + y))
    have h₂ := mul_nonneg (sub_nonneg.mpr hρ1) (add_nonneg (sq_nonneg x) (sq_nonneg y))
    nlinarith
  have hfactor : 0 ≤ 1 - ρ ^ 2 := by nlinarith
  have h := mul_nonneg hquad hfactor
  nlinarith

theorem sum_rows_le {α : Type*} (s : Finset α) (R G : α → α → ℝ)
    (h : ∀ a ∈ s, ∑ b ∈ s, R a b ≤ ∑ b ∈ s, G a b) :
    (∑ a ∈ s, ∑ b ∈ s, R a b) ≤ ∑ a ∈ s, ∑ b ∈ s, G a b := by
  exact Finset.sum_le_sum h

theorem ordered_interactions_nonnegative {α : Type*} (s : Finset α)
    (A R G : α → α → ℝ)
    (hinteraction : ∀ a ∈ s, ∀ b ∈ s,
      2 * G a b - R a b - R b a ≤ 2 * A a b)
    (hrows : ∀ a ∈ s, ∑ b ∈ s, R a b ≤ ∑ b ∈ s, G a b) :
    0 ≤ ∑ a ∈ s, ∑ b ∈ s, A a b := by
  have htotal : (∑ a ∈ s, ∑ b ∈ s,
      (2 * G a b - R a b - R b a)) ≤
      ∑ a ∈ s, ∑ b ∈ s, 2 * A a b := by
    apply Finset.sum_le_sum
    intro a ha
    exact Finset.sum_le_sum (fun b hb => hinteraction a ha b hb)
  have hswap : (∑ a ∈ s, ∑ b ∈ s, R b a) =
      ∑ a ∈ s, ∑ b ∈ s, R a b := Finset.sum_comm
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at htotal
  rw [hswap] at htotal
  have henergy := sum_rows_le s R G hrows
  linarith

theorem disjoint_interaction_of_orthogonal_parts
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v j g r s : E)
    (huj : inner ℝ u j = 0) (hvj : inner ℝ v j = 0)
    (hg : ‖g‖ ^ 2 ≤ ‖j‖ ^ 2)
    (hr : ‖u‖ ^ 2 ≤ ‖r‖ ^ 2) (hs : ‖v‖ ^ 2 ≤ ‖s‖ ^ 2) :
    2 * ‖g‖ ^ 2 - ‖r‖ ^ 2 - ‖s‖ ^ 2 ≤
      2 * inner ℝ (u + j) (v + j) := by
  have huv : 0 ≤ ‖u‖ ^ 2 + 2 * inner ℝ u v + ‖v‖ ^ 2 := by
    rw [← norm_add_sq_real]
    exact sq_nonneg _
  have hjv : inner ℝ j v = 0 := by rw [real_inner_comm, hvj]
  simp only [inner_add_left, inner_add_right, huj, hjv,
    real_inner_self_eq_norm_sq, add_zero, zero_add]
  linarith

theorem disjoint_inner_sum_nonnegative
    {α E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Finset α) (r : α → α → Prop) [DecidableRel r]
    (hr : ∀ {a b}, r a b → r b a) (h : α → E) (g R : α → α → E)
    (hinteraction : ∀ a ∈ s, ∀ b ∈ s, r a b →
      2 * ‖g a b‖ ^ 2 - ‖R a b‖ ^ 2 - ‖R b a‖ ^ 2 ≤
        2 * inner ℝ (h a) (h b))
    (hrows : ∀ a ∈ s,
      (∑ b ∈ s, if r a b then ‖R a b‖ ^ 2 else 0) ≤
        ∑ b ∈ s, if r a b then ‖g a b‖ ^ 2 else 0) :
    0 ≤ ∑ a ∈ s, ∑ b ∈ s, if r a b then inner ℝ (h a) (h b) else 0 := by
  apply ordered_interactions_nonnegative s
    (fun a b => if r a b then inner ℝ (h a) (h b) else 0)
    (fun a b => if r a b then ‖R a b‖ ^ 2 else 0)
    (fun a b => if r a b then ‖g a b‖ ^ 2 else 0)
  · intro a ha b hb
    by_cases hab : r a b
    · simpa only [ite_eq_left hab, ite_eq_left (hr hab)] using hinteraction a ha b hb hab
    · have hba : ¬ r b a := fun hba => hab (hr hba)
      simp only [ite_eq_right hab, ite_eq_right hba]
      norm_num
  · exact hrows

end Problem315

end OAI
