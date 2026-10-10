import OAI.NumberTheory.Ostmann.Quadratic.QuadraticEulerCover
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSquarefreePart

namespace OAI

/-! # The genuine support of the difference of quadratic Poisson main terms -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadraticMainAlpha_witness {D K w : ℕ} (h : quadraticMainAlpha D K w ≠ 0) :
    ∃ e ∈ D.divisors, ∃ b ∈ oddSquarefreeRange K, e * b = w := by
  by_contra hn
  apply h
  apply Finset.sum_eq_zero
  intro e he
  apply Finset.sum_eq_zero
  intro b hb
  exact ite_eq_right (fun heq => hn ⟨e, he, b, hb, heq⟩)

 theorem quadraticMainBeta_witness {D K w : ℕ} (h : quadraticMainBeta D K w ≠ 0) :
    ∃ u ∈ D.divisors, ∃ v ∈ oddSquarefreeRange K, D.Coprime v ∧ u ^ 2 * v = w := by
  by_contra hn
  apply h
  apply Finset.sum_eq_zero
  intro u hu
  apply Finset.sum_eq_zero
  intro v hv
  obtain ⟨hv, hcop⟩ := Finset.mem_filter.mp hv
  exact ite_eq_right (fun heq => hn ⟨u, hu, v, hv, hcop, heq⟩)

 theorem quadraticMainAlpha_support {D K w : ℕ} (hD : Squarefree D) (hDo : Odd D)
    (h : quadraticMainAlpha D K w ≠ 0) :
    Odd w ∧ w ≤ K * D ∧ quadraticSquarePart w ∣ D := by
  obtain ⟨e, he, b, hb, rfl⟩ := quadraticMainAlpha_witness h
  have hed := Nat.dvd_of_mem_divisors he
  have hes := hD.squarefree_of_dvd hed
  have heo := hDo.of_dvd_nat hed
  obtain ⟨hbr, hbo, hbs⟩ := Finset.mem_filter.mp hb
  refine ⟨heo.mul hbo, ?_, ?_⟩
  · calc
      e * b ≤ D * K := Nat.mul_le_mul (Nat.le_of_dvd (Nat.pos_of_ne_zero hD.ne_zero) hed)
        (Finset.mem_Icc.mp hbr).2
      _ = K * D := Nat.mul_comm _ _
  · rw [(quadraticSquarefreePart_pair hes hbs).1]
    exact (Nat.gcd_dvd_left e b).trans hed

 theorem quadraticMainBeta_support {D K w : ℕ} (hD : Squarefree D) (hDo : Odd D)
    (h : quadraticMainBeta D K w ≠ 0) :
    Odd w ∧ w ≤ K * D ^ 2 ∧ quadraticSquarePart w ∣ D := by
  obtain ⟨u, hu, v, hv, _, rfl⟩ := quadraticMainBeta_witness h
  have hud := Nat.dvd_of_mem_divisors hu
  have huo := hDo.of_dvd_nat hud
  obtain ⟨hvr, hvo, hvs⟩ := Finset.mem_filter.mp hv
  refine ⟨huo.pow.mul hvo, ?_, ?_⟩
  · calc
      u ^ 2 * v ≤ D ^ 2 * K := Nat.mul_le_mul
        (Nat.pow_le_pow_left (Nat.le_of_dvd (Nat.pos_of_ne_zero hD.ne_zero) hud) _)
        (Finset.mem_Icc.mp hvr).2
      _ = K * D ^ 2 := Nat.mul_comm _ _
  · rw [(quadraticSquarefreePart_of_mul_square (Nat.pos_of_mem_divisors hu).ne' hvs).1]
    exact hud

/-- The difference is supported precisely in the required upper interval;
its square part divides the original gcd, with no dependence on the character. -/
theorem quadraticMainGamma_support {D K w : ℕ} (hD : Squarefree D) (hDo : Odd D)
    (h : quadraticMainGamma D K w ≠ 0) :
    K < w ∧ w ≤ K * D ^ 2 ∧ Odd w ∧ quadraticSquarePart w ∣ D := by
  have hlarge : K < w := by
    by_contra hn
    exact h (quadratic_main_gamma_zero hD hDo (by omega))
  refine ⟨hlarge, ?_⟩
  by_cases ha : quadraticMainAlpha D K w = 0
  · have hb : quadraticMainBeta D K w ≠ 0 := by
      intro hb
      exact h (by simp [quadraticMainGamma, ha, hb])
    obtain ⟨ho, hbound, hdvd⟩ := quadraticMainBeta_support hD hDo hb
    exact ⟨hbound, ho, hdvd⟩
  · obtain ⟨ho, hbound, hdvd⟩ := quadraticMainAlpha_support hD hDo ha
    have hDpos := Nat.pos_of_ne_zero hD.ne_zero
    have hDs : D ≤ D ^ 2 := by nlinarith
    exact ⟨hbound.trans (Nat.mul_le_mul_left K hDs), ho, hdvd⟩

end Ostmann

end OAI
