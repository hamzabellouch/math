import OAI.MeasureTheory.Falconer.Estimates.PacketLogBounds
import OAI.MeasureTheory.Falconer.Estimates.SampledRowCardinality

namespace OAI

/-! A putative small fine-tube union bounds all its incidence-selection
logarithms linearly in the original dyadic depth. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem small_union_card_dyadic (n : ℕ) {ε s : ℝ} (hε : ε ≤ 1) (hs : s ≤ 1)
    (m : ℕ) (hm : (m:ℝ) ≤ Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)/((1/(2:ℝ)^n)^s)^4) :
    m ≤ 2^(5*n+2) := by
  have hpow : (1/(2:ℝ)^n)^s = Real.exp (-s*(n:ℝ)*Real.log 2) := by
    simpa only [div_pow,one_pow] using half_power_rpow_exp n s
  have hbound : Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)/((1/(2:ℝ)^n)^s)^4 ≤
      (2:ℝ)^(5*n+2) := by
    rw [hpow,← Real.exp_nat_mul,← Real.exp_sub]
    have heq : (2:ℝ)^(5*n+2) = Real.exp (((5*n+2:ℕ):ℝ)*Real.log 2) := by
      rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ) < 2)]
    rw [heq]
    apply Real.exp_le_exp.mpr
    have he := mul_le_mul_of_nonneg_right hε (show 0 ≤ ((n+2:ℕ):ℝ) by positivity)
    have hs' := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg (α := ℝ) n)
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    push_cast at he ⊢
    nlinarith only [mul_le_mul_of_nonneg_right he hlog.le,mul_le_mul_of_nonneg_right hs' hlog.le]
  exact_mod_cast hm.trans hbound

theorem small_union_selection_logs (n : ℕ) {ε s : ℝ} (hε : ε ≤ 1) (hs : s ≤ 1)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2))
    (hP : InBoundedLineChart P) (hsep : FiniteSeparatedAt ((1/(2:ℝ)^n)^2) P)
    (hsmall : ((P.biUnion T).card:ℝ) ≤
      Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)/((1/(2:ℝ)^n)^s)^4) :
    Nat.log 2 P.card+1 ≤ 4*n+6 ∧
    Nat.log 2 (P.biUnion T).card+1 ≤ 5*n+3 ∧
    Nat.log 2 (∑ p ∈ P, (T p).card)+1 ≤ 9*n+8 := by
  have hscale : (1/(2:ℝ)^n)^2 = 1/(2:ℝ)^(2*n) := by
    rw [div_pow,one_pow,show 2*n = n*2 by omega,pow_mul]
  have hp := bounded_planar_card_dyadic (2*n) P hP (hscale ▸ hsep)
  have hu := small_union_card_dyadic n hε hs (P.biUnion T).card hsmall
  refine ⟨?_,?_,?_⟩
  · convert packet_log_of_card_bound hp using 1
    omega
  · simpa only [Nat.add_assoc] using packet_log_of_card_bound hu
  · convert packet_incidence_log P T hp hu using 1
    omega

end Falconer

end OAI
