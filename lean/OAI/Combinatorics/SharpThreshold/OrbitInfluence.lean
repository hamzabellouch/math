import Mathlib

namespace OAI

universe u v

noncomputable section

namespace Problem313

/-- A nonnegative weight which is constant on a sufficiently large finite set
is at most the total weight divided by the size lower bound. -/
theorem weight_le_sum_div_of_constant_on
    {ι : Type u} [Fintype ι] (w : ι → ℝ) (O : Finset ι) (e : ι) (m : ℝ)
    (hm : 0 < m) (hw : ∀ j, 0 ≤ w j)
    (hcard : m ≤ (O.card : ℝ))
    (hconstant : ∀ j ∈ O, w j = w e) :
    w e ≤ (∑ j, w j) / m := by
  classical
  apply (le_div_iff₀ hm).2
  have hsum : ∑ j ∈ O, w j = (O.card : ℝ) * w e := by
    calc
      ∑ j ∈ O, w j = ∑ _j ∈ O, w e := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hconstant j hj
      _ = (O.card : ℝ) * w e := by simp
  have hle : ∑ j ∈ O, w j ≤ ∑ j, w j :=
    Finset.sum_le_univ_sum_of_nonneg hw
  have hmul := mul_le_mul_of_nonneg_right hcard (hw e)
  nlinarith

/-- The same bound when each point of a finite injectively indexed family has
weight equal to the distinguished point. This form avoids constructing an orbit. -/
theorem weight_le_sum_div_of_injective_family
    {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (w : ι → ℝ) (e : ι) (φ : κ → ι) (hφ : Function.Injective φ)
    (m : ℝ) (hm : 0 < m) (hcard : m ≤ (Fintype.card κ : ℝ))
    (hw : ∀ j, 0 ≤ w j) (hconstant : ∀ j, w (φ j) = w e) :
    w e ≤ (∑ j, w j) / m := by
  classical
  apply weight_le_sum_div_of_constant_on w (Finset.univ.image φ) e m hm hw
  · simpa [Finset.card_image_of_injective _ hφ] using hcard
  · intro j hj
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hj
    exact hconstant k

end Problem313

end

end OAI
