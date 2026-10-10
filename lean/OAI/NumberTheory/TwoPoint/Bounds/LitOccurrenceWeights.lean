import OAI.NumberTheory.TwoPoint.Bounds.CrudeTraceWeights

namespace OAI

/-! The exact reciprocal exponent of each nonsingleton lit designation. -/

namespace TwoPointCorrelations

open Finset

def litReciprocalExponent (lit unlit : ℕ) : ℕ :=
  unlit + if lit = 0 then 0 else 1

def extraReciprocalExponent (lit unlit : ℕ) : ℕ :=
  litReciprocalExponent lit unlit - 1

lemma litReciprocalExponent_pos (lit unlit : ℕ) (hm : 2 ≤ lit + unlit) :
    1 ≤ litReciprocalExponent lit unlit := by
  unfold litReciprocalExponent
  split_ifs <;> omega

/-- An entirely unlit nonsingleton uses at most half its exponent for the
baseline reciprocal. Each unlit occurrence of a lit label is wholly extra. -/
lemma unlit_le_twice_extra (lit unlit : ℕ) (hm : 2 ≤ lit + unlit) :
    unlit ≤ 2 * extraReciprocalExponent lit unlit := by
  unfold extraReciprocalExponent litReciprocalExponent
  split_ifs <;> omega

lemma total_unlit_le_twice_extra {ι : Type*} [Fintype ι]
    (lit unlit : ι → ℕ) (hm : ∀ i, 2 ≤ lit i + unlit i) :
    ∑ i, unlit i ≤ 2 * ∑ i, extraReciprocalExponent (lit i) (unlit i) := by
  rw [mul_sum]
  exact sum_le_sum (fun i _ => unlit_le_twice_extra _ _ (hm i))

/-- Factor off exactly one baseline reciprocal per nonsingleton label. -/
lemma lit_reciprocal_product_factor {ι : Type*} [Fintype ι]
    (lit unlit : ι → ℕ) (p : ι → ℝ) (hm : ∀ i, 2 ≤ lit i + unlit i) :
    (∏ i, (p i)⁻¹ ^ litReciprocalExponent (lit i) (unlit i)) =
      (∏ i, (p i)⁻¹) * ∏ i, (p i)⁻¹ ^ extraReciprocalExponent (lit i) (unlit i) := by
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  have he : litReciprocalExponent (lit i) (unlit i) =
      extraReciprocalExponent (lit i) (unlit i) + 1 := by
    have hp := litReciprocalExponent_pos _ _ (hm i)
    unfold extraReciprocalExponent
    omega
  rw [he, pow_succ, mul_comm]

/-- Retain the baseline reciprocal weight and bound every extra power by
`H⁻¹`; no nondivisibility condition is imposed on an unlit occurrence. -/
theorem lit_reciprocal_product_bound {ι : Type*} [Fintype ι]
    (lit unlit : ι → ℕ) (p : ι → ℝ) (H : ℝ)
    (hm : ∀ i, 2 ≤ lit i + unlit i) (hH : 0 < H) (hp : ∀ i, H ≤ p i) :
    (∏ i, (p i)⁻¹ ^ litReciprocalExponent (lit i) (unlit i)) ≤
      (∏ i, (p i)⁻¹) * H⁻¹ ^ (∑ i, extraReciprocalExponent (lit i) (unlit i)) := by
  rw [lit_reciprocal_product_factor lit unlit p hm, ← prod_pow_eq_pow_sum]
  apply mul_le_mul_of_nonneg_left
  · apply prod_le_prod₀
    · intro i _
      exact pow_nonneg (inv_nonneg.mpr ((hH.trans_le (hp i)).le)) _
    · intro i _
      exact pow_le_pow_left₀ (inv_nonneg.mpr ((hH.trans_le (hp i)).le))
        (inv_anti₀ hH (hp i)) _
  · exact prod_nonneg (fun i _ => inv_nonneg.mpr ((hH.trans_le (hp i)).le))

end TwoPointCorrelations

end OAI
