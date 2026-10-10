import OAI.NumberTheory.Ostmann.Quadratic.QuadraticDyadicGrowth
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticPrimeDilation

namespace OAI

/-! # Adjacent dyadic intervals and the actual prime-dilation image -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticWideRows (M : ℕ) : Finset ℕ :=
  (oddSquarefreeRange (4 * M)).filter (M ≤ ·)

theorem quadraticWideRows_energy (M N : ℕ) (v : ℕ → ℂ) :
    quadraticRowEnergy (quadraticWideRows M) N v ≤
      (∑ m ∈ (oddSquarefreeRange (2 * M)).filter (M ≤ ·), ‖quadraticTransposeSum N v m‖ ^ 2) +
      ∑ m ∈ (oddSquarefreeRange (2 * (2 * M))).filter (2 * M ≤ ·), ‖quadraticTransposeSum N v m‖ ^ 2 := by
  have hs := Finset.sum_filter_add_sum_filter_not (quadraticWideRows M) (fun m => m ≤ 2 * M)
    (fun m => ‖quadraticTransposeSum N v m‖ ^ 2)
  rw [quadraticRowEnergy, ← hs]
  apply add_le_add
  · apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => sq_nonneg _)
    intro m hm
    obtain ⟨hm, hhi⟩ := Finset.mem_filter.mp hm
    obtain ⟨hm, hlo⟩ := Finset.mem_filter.mp hm
    obtain ⟨hi, ho, hsf⟩ := Finset.mem_filter.mp hm
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1, hhi⟩, ho, hsf⟩, hlo⟩
  · apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => sq_nonneg _)
    intro m hm
    obtain ⟨hm, hhi⟩ := Finset.mem_filter.mp hm
    obtain ⟨hm, _⟩ := Finset.mem_filter.mp hm
    apply Finset.mem_filter.mpr
    refine ⟨?_, by omega⟩
    simpa only [show 2 * (2 * M) = 4 * M by omega] using hm

theorem quadratic_wide_rows_growth {ξ : ℝ} (h : QuadraticSieveGrowth ξ)
    (hξ : 1 ≤ ξ) (hξ' : ξ ≤ 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℕ, 0 < M → 0 < N →
      QuadraticRowBound (quadraticWideRows M) N
        (C * ((M : ℝ) * N) ^ ε *
          ((M : ℝ) + (M : ℝ) ^ (1 - ξ) * (N : ℝ) ^ (2 * ξ - 1))) := by
  obtain ⟨C, hC, hc⟩ := quadratic_dyadic_growth h hξ hξ' ε hε
  refine ⟨C * (1 + 2 * 2 ^ ε), by positivity, ?_⟩
  intro M N hM hN v
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hNM : (0 : ℝ) < N := by exact_mod_cast hN
  have hE : 0 ≤ quadraticSieveEnergy N v := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hS : 0 ≤ (M : ℝ) ^ (1 - ξ) * (N : ℝ) ^ (2 * ξ - 1) := by positivity
  have hscale : ((2 * M : ℕ) : ℝ) + ((2 * M : ℕ) : ℝ) ^ (1 - ξ) * (N : ℝ) ^ (2 * ξ - 1) ≤
      2 * ((M : ℝ) + (M : ℝ) ^ (1 - ξ) * (N : ℝ) ^ (2 * ξ - 1)) := by
    have hp : ((2 * M : ℕ) : ℝ) ^ (1 - ξ) ≤ (M : ℝ) ^ (1 - ξ) := by
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      rw [Real.mul_rpow (by norm_num) hMR.le]
      have hh : (2 : ℝ) ^ (1 - ξ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hMR.le _)
    have hh := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hNM.le (2 * ξ - 1))
    simp only [Nat.cast_mul, Nat.cast_ofNat] at hh ⊢
    nlinarith
  have hprod : (((2 * M : ℕ) : ℝ) * N) ^ ε = 2 ^ ε * ((M : ℝ) * N) ^ ε := by
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    rw [mul_assoc, Real.mul_rpow (by norm_num) (by positivity)]
  have hsecond := hc (2 * M) N (by omega) hN v
  rw [hprod] at hsecond
  have hb : C * (2 ^ ε * ((M : ℝ) * N) ^ ε) *
      (((2 * M : ℕ) : ℝ) + ((2 * M : ℕ) : ℝ) ^ (1 - ξ) * (N : ℝ) ^ (2 * ξ - 1)) *
        quadraticSieveEnergy N v ≤
      C * (2 ^ ε * ((M : ℝ) * N) ^ ε) *
        (2 * ((M : ℝ) + (M : ℝ) ^ (1 - ξ) * (N : ℝ) ^ (2 * ξ - 1))) *
          quadraticSieveEnergy N v := by gcongr
  have hfirst := hc M N hM hN v
  have htotal := (quadraticWideRows_energy M N v).trans (add_le_add hfirst (hsecond.trans hb))
  convert htotal using 1
  ring

theorem quadratic_prime_dilation_image {M Q p m : ℕ} (hQ : 2 ≤ Q)
    (hp : p.Prime) (hpQ : Q < p) (hp2Q : p ≤ 2 * Q)
    (hm : m ∈ (oddSquarefreeRange (2 * M)).filter (M ≤ ·)) (hpm : ¬p ∣ m) :
    p * m ∈ quadraticWideRows (Q * M) := by
  obtain ⟨hm, hlow⟩ := Finset.mem_filter.mp hm
  obtain ⟨hm, ho, hsf⟩ := Finset.mem_filter.mp hm
  obtain ⟨hm₁, hm₂⟩ := Finset.mem_Icc.mp hm
  have hcop := hp.coprime_iff_not_dvd.mpr hpm
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by nlinarith [hp.pos], ?_⟩,
    (hp.odd_of_ne_two (by omega)).mul ho, (Nat.squarefree_mul hcop).mpr ⟨hp.squarefree, hsf⟩⟩, ?_⟩
  · have hh := Nat.mul_le_mul hp2Q hm₂
    nlinarith
  · exact Nat.mul_le_mul hpQ.le hlow

end Ostmann

end OAI
