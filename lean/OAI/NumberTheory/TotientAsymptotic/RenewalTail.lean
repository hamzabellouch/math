import OAI.NumberTheory.TotientAsymptotic.RenewalConcavity
import OAI.NumberTheory.TotientAsymptotic.RenewalSeparation

namespace OAI

/-! Tail coefficients in (1-F(z))/(1-z/rho). -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma a_le_a_succ {j : ℕ} (hj : 1≤j) : a j≤a (j+1) := by
  have hjR : (1 : ℝ)≤j := by exact_mod_cast hj
  have h0 := log_shift_intervalIntegrable hj 0
  have h1 := log_shift_intervalIntegrable hj 1
  have he1 := a_shift_integral j 1
  simp only [Nat.cast_zero,add_zero] at h0
  simp only [Nat.cast_one] at h1 he1
  rw [a_eq_integral,he1]
  apply intervalIntegral.integral_mono_on (by linarith) h0 h1
  intro t ht
  apply Real.log_le_log (by linarith [ht.1])
  linarith

def renewalTail (n : ℕ) : ℝ := ∑' k : ℕ, a (n+k+1)*rho^(k+1)

lemma summable_renewalTail (n : ℕ) :
    Summable (fun k : ℕ => a (n+k+1)*rho^(k+1)) := by
  have hgeo : Summable (fun k : ℕ => rho^(k+1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one rho_pos.le rho_lt_one)
  have hmajor := (hgeo.mul_left (n : ℝ)).add
    (summable_index_geometric rho_pos.le rho_lt_one 1)
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (a_pos (by omega)).le (pow_pos rho_pos _).le) _ hmajor
  intro k
  have hh := mul_le_mul_of_nonneg_right (a_le_index (j := n+k+1) (by omega))
    (pow_pos rho_pos (k+1)).le
  convert hh using 1
  push_cast
  ring

lemma renewalTail_zero : renewalTail 0=1 := by
  simpa only [renewalTail,Nat.zero_add,renewalSeries] using renewalSeries_rho

lemma renewalTail_nonneg (n : ℕ) : 0≤renewalTail n :=
  tsum_nonneg (fun k => mul_nonneg (a_pos (by omega)).le (pow_pos rho_pos _).le)

lemma renewalTail_le_succ (n : ℕ) : renewalTail n≤renewalTail (n+1) := by
  apply (summable_renewalTail n).tsum_le_tsum _ (summable_renewalTail (n+1))
  intro k
  apply mul_le_mul_of_nonneg_right _ (pow_pos rho_pos _).le
  convert a_le_a_succ (j := n+k+1) (by omega) using 1
  congr 1
  omega

lemma renewalTail_recurrence (n : ℕ) :
    renewalTail n=rho*a (n+1)+rho*renewalTail (n+1) := by
  have hs := (summable_renewalTail n).sum_add_tsum_nat_add 1
  have he : (∑' k : ℕ, a (n+(k+1)+1)*rho^(k+1+1))=rho*renewalTail (n+1) := by
    rw [renewalTail,← tsum_mul_left]
    apply tsum_congr
    intro k
    rw [pow_succ]
    have hn : n+(k+1)+1=(n+1)+k+1 := by omega
    rw [hn]
    ring
  change _=renewalTail n at hs
  simp only [Finset.sum_range_one,Nat.add_zero,Nat.zero_add,pow_one] at hs
  rw [he] at hs
  simpa only [mul_comm] using hs.symm

lemma renewalTail_second_difference_neg (n : ℕ) :
    renewalTail (n+2)-2*renewalTail (n+1)+renewalTail n<0 := by
  have hs0 := summable_renewalTail n
  have hs1 := summable_renewalTail (n+1)
  have hs2 := summable_renewalTail (n+2)
  have he : renewalTail (n+2)+renewalTail n<2*renewalTail (n+1) := by
    rw [renewalTail,renewalTail,renewalTail,← hs2.tsum_add hs0,← tsum_mul_left]
    apply Summable.tsum_lt_tsum (i := 0)
    · intro k
      have hd := a_second_difference_neg (j := n+k+1) (by omega)
      have hpow := pow_pos rho_pos (k+1)
      have he1 : n+k+1+1=n+1+k+1 := by omega
      have he2 : n+k+1+2=n+2+k+1 := by omega
      rw [he1,he2] at hd
      nlinarith
    · have hd := a_second_difference_neg (j := n+1) (by omega)
      simp only [Nat.add_zero,Nat.zero_add,pow_one]
      have he1 : n+1+1=n+2 := by omega
      rw [he1] at hd
      have hp := mul_lt_mul_of_pos_right hd rho_pos
      nlinarith [hp]
    · exact hs2.add hs0
    · exact hs1.mul_left 2
  linarith

end TotientAsymptotic

end

end OAI
