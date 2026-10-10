import OAI.NumberTheory.TotientAsymptotic.RenewalLower
import OAI.NumberTheory.TotientAsymptotic.RenewalInput
import OAI.NumberTheory.TotientAsymptotic.RenewalTail

namespace OAI

/-! Positive renewal differences used to construct ordered prime coordinates. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma renewal_difference_lower {n : ℕ} (hn : 1 ≤ n) :
    a 1*g n ≤ g (n+1)-g n := by
  have hsum : (∑ i ∈ Finset.range n,g i*a (n-i)) ≤
      ∑ i ∈ Finset.range n,g i*a (n+1-i) := by
    apply Finset.sum_le_sum
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    have he : n+1-i=(n-i)+1 := by omega
    rw [he]
    exact mul_le_mul_of_nonneg_left (a_le_a_succ (by omega)) (g_pos i).le
  rw [← g_convolution (by omega : 0 < n)] at hsum
  have he := g_convolution (by omega : 0 < n+1)
  rw [Finset.sum_range_succ,show n+1-n=1 by omega] at he
  nlinarith only [hsum,he]

lemma renewal_strictly_increases {n : ℕ} (hn : 1 ≤ n) : g n < g (n+1) := by
  have hp := mul_pos (a_pos (j:=1) le_rfl) (g_pos n)
  linarith only [renewal_difference_lower hn,hp]

theorem renewal_difference_uniform_lower : ∃ c : ℝ,0 < c ∧
    ∀ n : ℕ,1 ≤ n → c*(rho^n)⁻¹ ≤ g (n+1)-g n := by
  obtain ⟨c,hc,hg⟩ := renewal_uniform_lower fordRenewalInput
  refine ⟨a 1*c,mul_pos (a_pos (j:=1) le_rfl) hc,?_⟩
  intro n hn
  calc
    _ = a 1*(c*(rho^n)⁻¹) := by ring
    _ ≤ a 1*g n := mul_le_mul_of_nonneg_left (hg n) (a_pos (j:=1) le_rfl).le
    _ ≤ _ := renewal_difference_lower hn

lemma renewal_uniform_upper : ∃ C : ℝ,0 < C ∧
    ∀ n : ℕ,g n ≤ C*(rho^n)⁻¹ := by
  obtain ⟨K,hK,hbound⟩ := (normalizedRenewal_properties fordRenewalInput).2
  refine ⟨K+1,by linarith,?_⟩
  intro n
  have hh := (le_abs_self (normalizedRenewal n)).trans
    ((by simpa only [Real.norm_eq_abs] using hbound n : |normalizedRenewal n| ≤ K))
  have hb := mul_le_mul_of_nonneg_right hh (inv_pos.mpr (pow_pos rho_pos n)).le
  have he : g n ≤ K*(rho^n)⁻¹ := by
    simpa only [normalizedRenewal,mul_assoc,mul_inv_cancel₀ (pow_pos rho_pos n).ne',mul_one]
      using hb
  exact he.trans (mul_le_mul_of_nonneg_right (by linarith) (inv_pos.mpr (pow_pos rho_pos n)).le)

end TotientAsymptotic

end

end OAI
