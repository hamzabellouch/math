import OAI.NumberTheory.CubicMoment.Estimates.PrimeMellinTransfer

namespace OAI

/-! Exact telescoping on contracting dyads. Functions that vanish below
one have a finite, hence unambiguous, dyadic reconstruction. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def dyadicDifference (F : ℝ → ℂ) (X : ℝ) : ℂ := F X-F (X/2)

lemma dyadicDifference_sum (F : ℝ → ℂ) (X : ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range N, dyadicDifference F (X/(2:ℝ)^j)) =
      F X-F (X/(2:ℝ)^N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih]
    unfold dyadicDifference
    have he : X/(2:ℝ)^N/2 = X/(2:ℝ)^(N+1) := by rw [pow_succ,div_div]
    rw [he]
    ring

lemma dyadicDifference_reconstruct (F : ℝ → ℂ)
    (hF : ∀ X : ℝ, X < 1 → F X = 0) (X : ℝ) :
    (∑' j : ℕ, dyadicDifference F (X/(2:ℝ)^j)) = F X := by
  obtain ⟨N,hN⟩ := pow_unbounded_of_one_lt X (by norm_num : (1:ℝ) < 2)
  have hsmall : X/(2:ℝ)^N < 1 := (div_lt_one (by positivity)).mpr hN
  calc
    _ = ∑ j ∈ Finset.range N, dyadicDifference F (X/(2:ℝ)^j) := by
      apply tsum_eq_sum
      intro j hj
      have hNj : N ≤ j := by simpa only [Finset.mem_range,not_lt] using hj
      have hpow : (2:ℝ)^N ≤ 2^j := pow_le_pow_right₀ (by norm_num) hNj
      have hx : X/(2:ℝ)^j < 1 := (div_lt_one (by positivity)).mpr (hN.trans_le hpow)
      have hx2 : X/(2:ℝ)^j/2 < 1 := by linarith
      simp only [dyadicDifference,hF _ hx,hF _ hx2,sub_self]
    _ = F X := by rw [dyadicDifference_sum,hF _ hsmall,sub_zero]

end CubicFirstMoment

end

end OAI
