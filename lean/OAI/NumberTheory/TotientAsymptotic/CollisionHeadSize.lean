import OAI.NumberTheory.TotientAsymptotic.CollisionCanceled
import OAI.NumberTheory.TotientAsymptotic.PrimeWindow

namespace OAI

/-! The zero-index collision uses the original endpoint and a subpower tail. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma basic_remainder_subpower (H : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ η : RemainderDatum (L x H), IsBasicRemainder x H η →
      (suffixPreimage η 0 : ℝ) ≤ x^ε := by
  filter_upwards [basic_remainder_log_small H,
    subpower_log_ratio.eventually (eventually_lt_nhds hε),eventually_gt_atTop (1 : ℝ)] with x hx hs hx1
  intro η hη
  have hlog : (Real.log x)^(4/5 : ℝ) ≤ ε*Real.log x :=
    (div_le_iff₀ (Real.log_pos hx1)).mp hs.le
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hx1)]
  apply (Real.log_le_iff_le_exp (by exact_mod_cast suffixPreimage_pos hη (i := 0) :
    (0 : ℝ) < suffixPreimage η 0)).mp
  simpa only [mul_comm] using (hx η hη).trans hlog

/-- At the first differing head prime, both the fixed residual and every
canceled shift already fit under the original endpoint to power `1/100`. -/
theorem collision_head_small_factors (H : ℕ) : ∀ᶠ x : ℝ in atTop,
    ∀ k p q : ℕ, L x H < m x → k < L x H → p.Prime → p ≠ q →
    ∀ η ξ : RemainderDatum (L x H), IsBasicRemainder x H η →
    ((suffixPreimage η k).totient : ℝ) ≤ x^(1/100 : ℝ) ∧
    (collisionCanceledProduct p q η ξ 0 k : ℝ) ≤ x^(1/100 : ℝ) := by
  filter_upwards [basic_remainder_subpower H (show (0 : ℝ) < 1/100 by norm_num)] with x hx
  intro k p q hL hk hp hpq η ξ hη
  have hbound := hx η hη
  have hdvd : (suffixPreimage η k).totient ∣ (suffixPreimage η 0).totient := by
    rw [basic_suffix_totient_split hη hL (Nat.zero_le k) hk]
    exact dvd_mul_right _ _
  have hDle := (Nat.le_of_dvd (Nat.totient_pos.mpr (suffixPreimage_pos hη)) hdvd).trans
    (Nat.totient_le (suffixPreimage η 0))
  constructor
  · exact (show ((suffixPreimage η k).totient : ℝ) ≤ suffixPreimage η 0 by exact_mod_cast hDle).trans hbound
  · have hrle := collisionCanceledProduct_le_suffix hη hk.le
      (show wholeWitnessPrime p η 0 ≠ wholeWitnessPrime q ξ 0 from hpq)
    exact (show (collisionCanceledProduct p q η ξ 0 k : ℝ) ≤ suffixPreimage η 0 by exact_mod_cast hrle).trans hbound

end TotientAsymptotic

end

end OAI
