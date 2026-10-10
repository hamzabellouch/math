import OAI.NumberTheory.Ostmann.QuadraticSieveLargeGcdBasic

namespace OAI

namespace Ostmann.QuadraticSieve

lemma quotientSupport_mul_mem {S : Finset ℕ} {d n : ℕ}
    (hn : n ∈ quotientSupport S d) : d*n ∈ S := by
  obtain ⟨m, hm, hdm, rfl⟩ := mem_quotientSupport.mp hn
  simpa only [Nat.mul_div_cancel' hdm] using hm

theorem quotientSupport_coprime {S : Finset ℕ} {d n : ℕ}
    (hS : ∀ m ∈ S, Squarefree m) (hn : n ∈ quotientSupport S d) : n.Coprime d :=
  (Nat.squarefree_mul_iff.mp (hS (d*n) (quotientSupport_mul_mem hn))).1.symm

theorem quotientSupport_factor {S : Finset ℕ} {d n : ℕ}
    (hS : ∀ m ∈ S, Odd m ∧ Squarefree m) (hn : n ∈ quotientSupport S d) :
    Odd d ∧ Squarefree d := by
  have h := hS (d*n) (quotientSupport_mul_mem hn)
  exact ⟨(Nat.odd_mul.mp h.1).1, (Nat.squarefree_mul_iff.mp h.2).2.1⟩

theorem coefficientEnergy_quotientSupport_le (S : Finset ℕ) (a : ℕ → ℂ) (d : ℕ) :
    coefficientEnergy (quotientSupport S d) (fun n => a (d*n)) ≤ coefficientEnergy S a := by
  unfold coefficientEnergy
  rw [sum_quotientSupport S d (fun n => ‖a n‖^2)]
  apply Finset.sum_le_sum
  intro n hn
  split <;> simp_all

theorem quotientSupport_dyadic {S : Finset ℕ} {d n : ℕ} {N₀ : ℝ}
    (hd : 0 < d) (hS : ∀ m ∈ S, N₀ < (m:ℝ) ∧ (m:ℝ) ≤ 2*N₀)
    (hn : n ∈ quotientSupport S d) :
    N₀/d < (n:ℝ) ∧ (n:ℝ) ≤ 2*N₀/d := by
  have h := hS (d*n) (quotientSupport_mul_mem hn)
  have hdr : (0:ℝ) < d := by exact_mod_cast hd
  push_cast at h
  constructor
  · exact (div_lt_iff₀ hdr).mpr (by nlinarith [h.1])
  · exact (le_div_iff₀ hdr).mpr (by nlinarith [h.2])

theorem quotientSupport_one_lt {S : Finset ℕ} {d n : ℕ} {N₀ : ℝ}
    (hdN : (d:ℝ) < N₀) (hS : ∀ m ∈ S, N₀ < (m:ℝ))
    (hn : n ∈ quotientSupport S d) : 1 < n := by
  have h := hS (d*n) (quotientSupport_mul_mem hn)
  have hdr : (0:ℝ) ≤ d := Nat.cast_nonneg d
  by_contra he
  have hnr : (n:ℝ) ≤ 1 := by exact_mod_cast (show n ≤ 1 by omega)
  push_cast at h
  nlinarith [mul_le_mul_of_nonneg_left hnr hdr]

theorem gcdJacobiRow_zero_of_bad_factor {S : Finset ℕ} (a : ℕ → ℂ) {d : ℕ}
    (hd : 0 < d) (hS : ∀ n ∈ S, Odd n ∧ Squarefree n)
    (hbad : ¬ (Odd d ∧ Squarefree d)) (m : ℤ) : gcdJacobiRow S a d m = 0 := by
  unfold gcdJacobiRow
  rw [gcdCorrelation_eq_quotient S _ hd]
  have he : quotientSupport S d = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro n hn
    exact hbad (quotientSupport_factor hS hn)
  simp only [he, Finset.sum_empty]

end Ostmann.QuadraticSieve

end OAI
