import OAI.NumberTheory.Ostmann.QuadraticSieveGcdSeparationSelection
import OAI.NumberTheory.Ostmann.QuadraticSieveSquareRemoval

namespace OAI

namespace Ostmann.QuadraticSieve
open ComplexConjugate

theorem coprimeProductDivisorJacobiRow_square (S T : Finset ℕ) (a b : ℕ → ℂ)
    (d Δ s : ℕ) (hs : s ∣ Δ) (r : ℤ)
    (hS : ∀ n ∈ S, 0 < n ∧ Nat.Coprime n Δ)
    (hT : ∀ t ∈ T, 0 < t ∧ Nat.Coprime t Δ) :
    coprimeProductDivisorJacobiRow S T a b d ((s : ℤ) ^ 2 * r) =
      coprimeProductDivisorJacobiRow S T a b d r := by
  unfold coprimeProductDivisorJacobiRow
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro t ht
  have hp : 0 < n * t := Nat.mul_pos (hS n hn).1 (hT t ht).1
  let : NeZero (n * t) := ⟨hp.ne'⟩
  have hsn : Nat.Coprime s n := ((hS n hn).2.of_dvd_right hs).symm
  have hst : Nat.Coprime s t := ((hT t ht).2.of_dvd_right hs).symm
  have hcop : (s : ℤ).gcd (n * t : ℕ) = 1 := by
    simpa only [Int.gcd_natCast_natCast, Nat.coprime_iff_gcd_eq_one] using hsn.mul_right hst
  rw [jacobi_square_mul_left, ite_eq_left hcop]

theorem coefficientEnergy_conj (S : Finset ℕ) (a : ℕ → ℂ) :
    coefficientEnergy S (fun n => conj (a n)) = coefficientEnergy S a := by
  simp [coefficientEnergy]

theorem coprime_jacobi_L1_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V S : Finset ℕ) (a : ℕ → ℂ) (N : ℕ),
      0 < N → (∀ v ∈ V, Odd v) → S ⊆ oddSquarefreeUpTo N →
      (∑ v ∈ V, ‖coprimeProductDivisorJacobiRow S S a (fun n => conj (a n)) 1 (v : ℤ)‖) ≤
        C * (N : ℝ) ^ ε * quadraticNorm V (oddSquarefreeUpTo N) * coefficientEnergy S a := by
  obtain ⟨C, hC, hbound⟩ := exists_gcd_separation_scales (2 * ε) (by positivity)
  refine ⟨Real.sqrt C, Real.sqrt_pos.mpr hC, ?_⟩
  intro V S a N hN hV hS
  obtain ⟨d₁, d₂, hd₁, hd₂, hmul, hb⟩ :=
    hbound V S S a (fun n => conj (a n)) 1 N (by norm_num) hV hS hS
  have hd₁1 : d₁ = 1 := by nlinarith
  have hd₂1 : d₂ = 1 := by nlinarith
  subst d₁
  subst d₂
  simp only [Nat.div_one, coefficientEnergy_conj] at hb
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : (N : ℝ) ^ (2 * ε) = ((N : ℝ) ^ ε) ^ 2 := by
    rw [two_mul, Real.rpow_add hNr]
    ring
  have hQ := quadraticNorm_nonneg V (oddSquarefreeUpTo N)
  have hE := coefficientEnergy_nonneg S a
  have hsum : 0 ≤ ∑ v ∈ V,
      ‖coprimeProductDivisorJacobiRow S S a (fun n => conj (a n)) 1 (v : ℤ)‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  apply (sq_le_sq₀ hsum (by positivity : 0 ≤
    Real.sqrt C * (N : ℝ) ^ ε * quadraticNorm V (oddSquarefreeUpTo N) * coefficientEnergy S a)).mp
  apply hb.trans_eq
  rw [hp]
  simp only [mul_pow, Real.sq_sqrt hC.le]
  ring

end Ostmann.QuadraticSieve

end OAI
