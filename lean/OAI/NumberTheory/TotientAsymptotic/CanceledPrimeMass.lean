import OAI.NumberTheory.TotientAsymptotic.CofactorEnvelope

namespace OAI

/-! The reciprocal cost of fixing the canceled primes, from Mertens' input. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma prime_shift_inv_le_log_factor {p : ℕ} (hp : p.Prime) :
    ((p-1 : ℕ) : ℝ)⁻¹ ≤ 2*Real.log ((p : ℝ)/(p-1)) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hm : (0 : ℝ) < p-1 := by linarith
  have hl := Real.one_sub_inv_le_log_of_pos (div_pos hp0 hm)
  have he : 1-((p : ℝ)/(p-1))⁻¹=(p : ℝ)⁻¹ := by field_simp; ring
  rw [he] at hl
  have hs : (p-1 : ℝ)⁻¹ ≤ 2*(p : ℝ)⁻¹ := by
    have hh : 1/((p : ℝ)-1) ≤ 2/(p : ℝ) := (div_le_div_iff₀ hm hp0).mpr (by linarith)
    simpa only [one_div,div_eq_mul_inv,one_mul] using hh
  rw [Nat.cast_sub hp.one_lt.le,Nat.cast_one]
  linarith

lemma primeEulerProduct_pos (N : ℕ) : 0 < primeEulerProduct N := by
  apply Finset.prod_pos
  intro p hp
  have hprime := (Finset.mem_filter.mp hp).2
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
  exact div_pos (by linarith) (by linarith)

lemma canceled_prime_mass_le_log_product (N : ℕ) :
    (∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, ((p-1 : ℕ) : ℝ)⁻¹) ≤
      2*Real.log (primeEulerProduct N) := by
  calc
    _ ≤ ∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, 2*Real.log ((p : ℝ)/(p-1)) :=
      Finset.sum_le_sum (fun p hp => prime_shift_inv_le_log_factor (Finset.mem_filter.mp hp).2)
    _ = 2*Real.log (primeEulerProduct N) := by
      rw [← Finset.mul_sum]
      congr 1
      symm
      apply Real.log_prod
      intro p hp
      have hp1 : (1 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
      exact (div_pos (by linarith : (0 : ℝ) < p) (by linarith : (0 : ℝ) < p-1)).ne'

/-- A canceled prime costs only the logarithm of the prime-product bound,
which is of double-logarithmic size in its allowed prime endpoint. -/
theorem canceled_prime_mass_mertens (hmertens : MertensProductInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      (∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, ((p-1 : ℕ) : ℝ)⁻¹) ≤
        2*(Real.log C+B N) := by
  obtain ⟨C,hC,hbound⟩ := hmertens
  refine ⟨C,hC,?_⟩
  intro N hN
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hl := Real.log_le_log (primeEulerProduct_pos N) (hbound N hN)
  rw [Real.log_mul hC.ne' hlogN.ne'] at hl
  exact (canceled_prime_mass_le_log_product N).trans (by change _ ≤ 2*(Real.log C+Real.log (Real.log (N : ℝ))); linarith)

end TotientAsymptotic

end

end OAI
