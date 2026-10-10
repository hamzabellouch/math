import OAI.MeasureTheory.Falconer.Estimates.ScalarBunchMargins

namespace OAI

/-! A single explicit parameter choice controls the exceptional-pair
 budget in both the short and long porous bunches. -/
namespace Falconer

 theorem scalar_bunch_log_weight (P H : ℕ) (b : ScalarBunch) {K κ : ℝ} (hK : 0 < K) :
    Real.log (16*(scalarBunchGroup P b:ℝ)^4*K*((5/4:ℝ)*(1/2:ℝ)^H)^κ) =
      4*Real.log 2 + 4*(P:ℝ)*((b.stop-b.start:ℕ):ℝ)*Real.log 2 + Real.log K +
        κ*(Real.log (5/4:ℝ)-(H:ℝ)*Real.log 2) := by
  have hgroup : 0 < (scalarBunchGroup P b:ℝ) := by
    unfold scalarBunchGroup
    positivity
  have h16 : Real.log (16:ℝ) = 4*Real.log 2 := by
    rw [show (16:ℝ) = 2^4 by norm_num,Real.log_pow]
    norm_num
  have hhalf : Real.log (1/2:ℝ) = -Real.log 2 := by
    rw [show (1/2:ℝ) = (2:ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (ne_of_gt hK),Real.log_mul (by norm_num) (by positivity),
    Real.log_pow,Real.log_rpow (by positivity),Real.log_mul (by norm_num) (by positivity),
    Real.log_pow,h16,hhalf]
  simp only [scalarBunchGroup,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow,Nat.cast_mul]
  ring

 theorem scalar_bunch_uniform_budget {P B C : ℕ} {K κ : ℝ} (hK : 0 < K)
    (hC : Real.log (64*K)+κ*Real.log (5/4:ℝ)+4000*(P:ℝ)*Real.log 2 ≤
      κ*(C:ℝ)*Real.log 2)
    (hB : 800*(P:ℝ) ≤ κ*(B:ℝ))
    (b : ScalarBunch) {w : ℕ → ℝ} {theta : ℝ} (hgood : ScalarBunchGood w theta b) :
    16*(scalarBunchGroup P b:ℝ)^4*K*
      ((5/4:ℝ)*(1/2:ℝ)^(C+B*(b.stop-b.cut)))^κ ≤ 1/4 := by
  have hgroup : 0 < (scalarBunchGroup P b:ℝ) := by
    unfold scalarBunchGroup
    positivity
  have ht : (0:ℝ) ≤ ((b.stop-b.cut:ℕ):ℝ) := Nat.cast_nonneg _
  have hp : (0:ℝ) ≤ (P:ℝ) := Nat.cast_nonneg _
  have hlen : 4*(P:ℝ)*((b.stop-b.start:ℕ):ℝ) ≤
      4000*(P:ℝ)+κ*(B:ℝ)*((b.stop-b.cut:ℕ):ℝ) := by
    rcases hgood.gap with ⟨hzero,hsmall⟩ | hlarge
    · have hs : ((b.stop-b.start:ℕ):ℝ) ≤ 1000 := by exact_mod_cast hsmall
      have hz : b.stop-b.cut = 0 := by omega
      simp only [hz,Nat.cast_zero,mul_zero,add_zero]
      nlinarith
    · have hl : ((b.stop-b.start:ℕ):ℝ) ≤ 200*((b.stop-b.cut:ℕ):ℝ) := by exact_mod_cast hlarge
      have hm := mul_le_mul_of_nonneg_right hB ht
      nlinarith
  have hlog64 : Real.log (64*K) = 6*Real.log 2+Real.log K := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hK),show (64:ℝ) = 2^6 by norm_num,Real.log_pow]
    norm_num
  have hquarter : Real.log (1/4:ℝ) = -2*Real.log 2 := by
    rw [show (1/4:ℝ) = ((2:ℝ)^2)⁻¹ by norm_num,Real.log_inv,Real.log_pow]
    norm_num
  apply (Real.log_le_log_iff (by positivity) (by norm_num : (0:ℝ) < 1/4)).1
  rw [scalar_bunch_log_weight P _ b hK,hquarter]
  simp only [Nat.cast_add,Nat.cast_mul]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hm := mul_le_mul_of_nonneg_right hlen hlog2.le
  rw [hlog64] at hC
  nlinarith

end Falconer

end OAI
