import OAI.NumberTheory.Ostmann.SchwartzCutoff

namespace OAI

open scoped Classical
namespace Ostmann.HybridSieve

lemma log_gap_lower_bound {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    (n:ℝ)-(m:ℝ) ≤ (n:ℝ)*(Real.log n-Real.log m) := by
  have hm' : 0 < (m:ℝ) := by exact_mod_cast hm
  have hn' : 0 < (n:ℝ) := by exact_mod_cast lt_of_lt_of_le hm hmn
  have h := Real.log_le_sub_one_of_pos (div_pos hm' hn')
  rw [Real.log_div hm'.ne' hn'.ne'] at h
  have hd : 1-(m:ℝ)/(n:ℝ) ≤ Real.log n-Real.log m := by linarith
  have heq : ((n:ℝ)-(m:ℝ))/(n:ℝ) = 1-(m:ℝ)/(n:ℝ) := by
    field_simp
  rw [← heq] at hd
  simpa only [mul_comm] using (div_le_iff₀ hn').mp hd

lemma log_window_diameter {N m n : ℕ} {H u : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hm : N < m) (hmn : m ≤ n) (hn : n ≤ 2*N)
    (hmw : |u-H*Real.log m| < (1:ℝ)/8)
    (hnw : |u-H*Real.log n| < (1:ℝ)/8) :
    (n:ℝ)-(m:ℝ) ≤ (N:ℝ)/H := by
  have hm0 : 0 < m := lt_trans hN hm
  have hlog : 0 ≤ Real.log n-Real.log m := by
    apply sub_nonneg.mpr
    apply Real.log_le_log
    · exact_mod_cast hm0
    · exact_mod_cast hmn
  have hnR : (n:ℝ) ≤ 2*(N:ℝ) := by exact_mod_cast hn
  have hgap := (log_gap_lower_bound hm0 hmn).trans
    (mul_le_mul_of_nonneg_right hnR hlog)
  have hmlo := (abs_lt.mp hmw).2
  have hnhi := (abs_lt.mp hnw).1
  have hphase : H*(Real.log n-Real.log m) ≤ (1:ℝ)/4 := by linarith
  have hN0 : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
  have hprod := mul_le_mul_of_nonneg_left hphase (by positivity : 0 ≤ 2*(N:ℝ))
  apply (le_div_iff₀ hH).mpr
  nlinarith [mul_le_mul_of_nonneg_right hgap hH.le]

lemma active_window_interval (N : ℕ) (a : ℕ → ℂ) (H u : ℝ)
    (hN : 0 < N) (hH : 0 < H) :
    ∃ A : ℕ, ∀ n ∈ Finset.Ioc N (2*N),
      a n * Ostmann.SchwartzCutoff.bumpSchwartz (u-H*Real.log n) ≠ 0 →
      A ≤ n ∧ n < A+(⌊(N:ℝ)/H⌋₊+1) := by
  let s := (Finset.Ioc N (2*N)).filter
    (fun n => a n * Ostmann.SchwartzCutoff.bumpSchwartz (u-H*Real.log n) ≠ 0)
  by_cases hs : s.Nonempty
  · let A := s.min' hs
    refine ⟨A, ?_⟩
    have hA : A ∈ s := Finset.min'_mem s hs
    have hA' := Finset.mem_filter.mp hA
    intro n hn hne
    have hns : n ∈ s := Finset.mem_filter.mpr ⟨hn,hne⟩
    have hAn : A ≤ n := Finset.min'_le s n hns
    refine ⟨hAn, ?_⟩
    have hwindow (k : ℕ) (hk : k ∈ s) : |u-H*Real.log k| < (1:ℝ)/8 := by
      by_contra hbad
      have hz := Ostmann.SchwartzCutoff.bumpSchwartz_zero_of_abs_ge (le_of_not_gt hbad)
      have hne' := (Finset.mem_filter.mp hk).2
      exact hne' (by rw [hz,mul_zero])
    have hd := log_window_diameter hN hH (Finset.mem_Ioc.mp hA'.1).1 hAn
      (Finset.mem_Ioc.mp hn).2 (hwindow A hA) (hwindow n hns)
    have hcast : ((n-A:ℕ):ℝ) = (n:ℝ)-(A:ℝ) := Nat.cast_sub hAn
    rw [← hcast] at hd
    have hnat : n-A ≤ ⌊(N:ℝ)/H⌋₊ := (Nat.le_floor_iff (by positivity)).mpr hd
    omega
  · refine ⟨0, ?_⟩
    intro n hn hne
    exact (hs ⟨n,Finset.mem_filter.mpr ⟨hn,hne⟩⟩).elim

end Ostmann.HybridSieve

end OAI
