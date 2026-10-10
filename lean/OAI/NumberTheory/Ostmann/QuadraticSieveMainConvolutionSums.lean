import OAI.NumberTheory.Ostmann.QuadraticSieveMainConvolution

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped ArithmeticFunction.Moebius

theorem truncatedMainAlpha_sum (K Δ L : ℕ) (hΔ : 0 < Δ) (ho : Odd Δ)
    (hL : K * Δ ≤ L) (f : ℕ → ℂ) :
    (∑ e ∈ Δ.divisors, (μ e : ℂ) * ∑ b ∈ oddSquarefreeUpTo K, f (e * b)) =
      ∑ w ∈ Finset.Icc 1 L, (truncatedMainAlpha K Δ w : ℂ) * f w := by
  calc
    _ = ∑ e ∈ Δ.divisors, ∑ w ∈ Finset.Icc 1 L,
        if Odd w ∧ e ∣ w ∧ Squarefree (w / e) ∧ w / e ≤ K then (μ e : ℂ) * f w else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      have hed := (Nat.mem_divisors.mp he).1
      have hep := Nat.pos_of_mem_divisors he
      have heL : e * K ≤ L := by
        have heΔ := Nat.le_of_dvd hΔ hed
        have h : e * K ≤ K * Δ := by
          simpa only [Nat.mul_comm] using Nat.mul_le_mul_left K heΔ
        exact h.trans hL
      have h := sum_oddSquarefree_multiple e K L hep (ho.of_dvd_nat hed) heL
        (fun _ => True) (fun w => (μ e : ℂ) * f w)
      simpa only [ite_true, and_true, Finset.mul_sum] using h
    _ = ∑ w ∈ Finset.Icc 1 L, ∑ e ∈ Δ.divisors,
        if Odd w ∧ e ∣ w ∧ Squarefree (w / e) ∧ w / e ≤ K then (μ e : ℂ) * f w else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w hw
      unfold truncatedMainAlpha
      by_cases how : Odd w
      · simp only [how, true_and, ite_true, Int.cast_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro e he
        by_cases hc : e ∣ w ∧ Squarefree (w / e) ∧ w / e ≤ K <;> simp [hc]
      · simp [how]

theorem truncatedMainBeta_sum (K Δ L : ℕ) (hΔ : 0 < Δ) (ho : Odd Δ)
    (hL : K * Δ ^ 2 ≤ L) (f : ℕ → ℂ) :
    (∑ u ∈ Δ.divisors, (μ u : ℂ) * ∑ v ∈ oddSquarefreeUpTo K,
      if Nat.Coprime v Δ then f (u ^ 2 * v) else 0) =
      ∑ w ∈ Finset.Icc 1 L, (truncatedMainBeta K Δ w : ℂ) * f w := by
  calc
    _ = ∑ u ∈ Δ.divisors, ∑ w ∈ Finset.Icc 1 L,
        if Odd w ∧ u ^ 2 ∣ w ∧ Squarefree (w / u ^ 2) ∧ w / u ^ 2 ≤ K ∧
          Nat.Coprime (w / u ^ 2) Δ then (μ u : ℂ) * f w else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      have hud := (Nat.mem_divisors.mp hu).1
      have hup := Nat.pos_of_mem_divisors hu
      have huL : u ^ 2 * K ≤ L := by
        have huΔ := Nat.pow_le_pow_left (Nat.le_of_dvd hΔ hud) 2
        have h : u ^ 2 * K ≤ K * Δ ^ 2 := by
          simpa only [Nat.mul_comm] using Nat.mul_le_mul_left K huΔ
        exact h.trans hL
      have h := sum_oddSquarefree_multiple (u ^ 2) K L (pow_pos hup 2)
        ((ho.of_dvd_nat hud).pow) huL (fun v => Nat.Coprime v Δ)
        (fun w => (μ u : ℂ) * f w)
      rw [Finset.mul_sum]
      convert h using 1
      apply Finset.sum_congr rfl
      intro v hv
      split_ifs <;> simp
    _ = ∑ w ∈ Finset.Icc 1 L, ∑ u ∈ Δ.divisors,
        if Odd w ∧ u ^ 2 ∣ w ∧ Squarefree (w / u ^ 2) ∧ w / u ^ 2 ≤ K ∧
          Nat.Coprime (w / u ^ 2) Δ then (μ u : ℂ) * f w else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w hw
      unfold truncatedMainBeta
      by_cases how : Odd w
      · simp only [how, true_and, ite_true, Int.cast_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro u hu
        by_cases hc : u ^ 2 ∣ w ∧ Squarefree (w / u ^ 2) ∧
            Nat.Coprime (w / u ^ 2) Δ ∧ w / u ^ 2 ≤ K
        · have hc' : u ^ 2 ∣ w ∧ Squarefree (w / u ^ 2) ∧ w / u ^ 2 ≤ K ∧
              Nat.Coprime (w / u ^ 2) Δ := by tauto
          simp only [ite_eq_left hc, ite_eq_left hc']
        · have hc' : ¬(u ^ 2 ∣ w ∧ Squarefree (w / u ^ 2) ∧ w / u ^ 2 ≤ K ∧
              Nat.Coprime (w / u ^ 2) Δ) := by tauto
          simp [hc, hc']
      · simp [how]

end Ostmann.QuadraticSieve

end OAI
