import OAI.NumberTheory.Ostmann.QuadraticSieveDualPoissonTruncation

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped SchwartzMap

theorem poisson_tail_scale_bound (A : ℕ) {M e q K R T : ℝ}
    (hM : 0 < M) (he : 0 < e) (hq : 0 < q) (hK : 0 < K) (hT : 0 < T)
    (hR : e*q/M ≤ R) (hcut : R*T ≤ K) :
    (M/(e*q))*Real.sqrt q / ((M/(e*q))^(A+2)*K^A) ≤
      Real.sqrt q * R / T^A := by
  have hx : 0 < e*q/M := by positivity
  have hRp : 0 < R := hx.trans_le hR
  have hratio : (e*q/M)/K ≤ 1/T := by
    apply (div_le_iff₀ hK).mpr
    have h : (e*q/M)*T ≤ K := (mul_le_mul_of_nonneg_right hR hT.le).trans hcut
    simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using (le_div_iff₀ hT).mpr h
  have hid : (M/(e*q))*Real.sqrt q / ((M/(e*q))^(A+2)*K^A) =
      Real.sqrt q * (e*q/M) * ((e*q/M)/K)^A := by
    rw [show A+2 = (A+1)+1 by omega, pow_succ, pow_succ, div_pow, div_pow, mul_pow]
    field_simp
    ring_nf
    simp [inv_pow, mul_assoc, hM.ne']
  rw [hid]
  calc
    _ ≤ Real.sqrt q * R * (1/T)^A := by
      gcongr
    _ = _ := by rw [div_pow,one_pow]; ring

theorem dualPoissonTail_bound_scaled (W : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℝ) (k q : ℕ) [NeZero q] (K T : ℝ),
      0 < M → k ≠ 0 → Odd q → Squarefree q → 0 < K → 0 < T →
      (((k : ℝ)*q/M)*T ≤ K) →
      ‖dualPoissonTail W M k q K‖ ≤
        C * k * Real.sqrt (q : ℝ) * ((k : ℝ)*q/M) / T^A := by
  obtain ⟨C,hC,hbound⟩ := dualPoissonTail_bound W A
  refine ⟨C,hC,?_⟩
  intro M k q _ K T hM hk hq hsq hK hT hcut
  have hqp : 0 < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hkp : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hcard : (k.divisors.card : ℝ) ≤ k := by exact_mod_cast Nat.card_divisors_le_self k
  calc
    _ ≤ C * ∑ e ∈ k.divisors,
        (M / (e * q)) * Real.sqrt (q : ℝ) /
          ((M / (e * q)) ^ (A + 2) * K ^ A) := hbound M k q K hM hk hq hsq hK
    _ ≤ C * ∑ _e ∈ k.divisors, Real.sqrt (q : ℝ) * ((k : ℝ)*q/M) / T^A := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply Finset.sum_le_sum
      intro e he
      have hep : 0 < (e : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors he
      have hek : (e : ℝ) ≤ k := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hk) (Nat.mem_divisors.mp he).1
      apply poisson_tail_scale_bound A hM hep hqp hK hT _ hcut
      gcongr
    _ ≤ C * ((k : ℝ) * (Real.sqrt (q : ℝ) * ((k : ℝ)*q/M) / T^A)) := by
      rw [Finset.sum_const,nsmul_eq_mul]
      gcongr
    _ = _ := by ring

end Ostmann.QuadraticSieve

end OAI
