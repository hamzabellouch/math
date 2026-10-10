import OAI.NumberTheory.TotientAsymptotic.BootstrapEnvelope
import OAI.NumberTheory.TotientAsymptotic.DyadicValueBounds

namespace OAI

/-! The counting bootstrap at arbitrary real endpoints. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

def countingDyadicIndex (x : ℝ) : ℕ := ⌈Real.log x/Real.log 2⌉₊

lemma counting_dyadic_index_bounds {x : ℝ} (hx : 4 ≤ x) :
    1 ≤ countingDyadicIndex x ∧ x ≤ (2:ℝ)^(countingDyadicIndex x) ∧
    bootstrapHeight (countingDyadicIndex x) ≤ B x+4 := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have h2 : 0 < Real.log (2:ℝ) := by positivity
  have h2lo : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h4 : 1 ≤ Real.log x := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<4) hx
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  let J := countingDyadicIndex x
  have hlo : Real.log x/Real.log 2 ≤ (J:ℝ) := Nat.le_ceil _
  have hhi : (J:ℝ) < Real.log x/Real.log 2+1 := Nat.ceil_lt_add_one (by positivity)
  have hJ : 1 ≤ J := by
    have hp : 0 < (J:ℝ) := (div_pos hlog h2).trans_le hlo
    have hjpos : 0 < J := Nat.cast_pos.mp hp
    omega
  have hJhi : (J:ℝ)+1 ≤ 4*Real.log x := by
    have hh := (div_le_iff₀ h2).mpr (show Real.log x ≤ 2*Real.log x*Real.log 2 by nlinarith)
    linarith
  refine ⟨hJ,?_,?_⟩
  · have hs : Real.log x ≤ (J:ℝ)*Real.log 2 := (div_le_iff₀ h2).mp hlo
    have he := Real.exp_le_exp.mpr hs
    simpa only [Real.exp_log hx0,Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)] using he
  · have hl := Real.log_le_log (by positivity : 0 < (J:ℝ)+1) hJhi
    rw [Real.log_mul (by norm_num : (4:ℝ)≠0) hlog.ne'] at hl
    have hlog4 : Real.log (4:ℝ) ≤ 3 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
      norm_num at hh
      exact hh
    change 1+Real.log ((J:ℝ)+1) ≤ B x+4
    unfold B
    linarith

theorem bootstrap_real_count : ∃ C : ℝ,0 < C ∧ ∀ x : ℝ,4 ≤ x →
    V x ≤ C*x/Real.log x*Real.exp (9*(Real.log (B x+4))^2) := by
  obtain ⟨C,hC,hcount⟩ := bootstrap_envelope_bound
  refine ⟨4*C,by positivity,?_⟩
  intro x hx
  obtain ⟨hJ,hxJ,hheight⟩ := counting_dyadic_index_bounds hx
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hH := bootstrapHeight_one_le (countingDyadicIndex x)
  have hlo : 0 ≤ Real.log (bootstrapHeight (countingDyadicIndex x)) := Real.log_nonneg hH
  have hle := Real.log_le_log (by linarith) hheight
  have hexp : bootstrapMajorant (countingDyadicIndex x) ≤ Real.exp (9*(Real.log (B x+4))^2) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hcountJ : dyadicTotientEnvelope (countingDyadicIndex x) ≤
      C*Real.exp (9*(Real.log (B x+4))^2) :=
    (hcount _).trans (mul_le_mul_of_nonneg_left hexp hC.le)
  calc
    _ ≤ 4*dyadicTotientEnvelope (countingDyadicIndex x)*x/Real.log x := dyadic_real_value_count_bound hx hxJ
    _ ≤ 4*(C*Real.exp (9*(Real.log (B x+4))^2))*x/Real.log x := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcountJ (by norm_num)) (by linarith)) hlog.le
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
