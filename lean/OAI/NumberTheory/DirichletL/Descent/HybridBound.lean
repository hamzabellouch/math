import OAI.NumberTheory.DirichletL.Descent.SourceHybrid

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

private theorem hybrid_log_cost_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K N B : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B →
      K ^ (ε / 9) * (K * (N * B) * N) ^ (ε / 9) *
        (columnDyadicLength K + 1 : ℝ) ^ 2 * (columnDyadicLength N + 1 : ℝ) ^ 2 *
          (columnDyadicLength B + 1 : ℝ) ^ 2 ≤ C * (K * N * B) ^ ε := by
  let δ := ε / 9
  let A := 2 + 1 / (δ * Real.log 2)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨A ^ 6, pow_pos hA 6, ?_⟩
  intro K N B hK hN hB
  let Q := K * N * B
  have hQ : 1 ≤ Q := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hK hN) hB
  have hQ0 : 0 < Q := by linarith
  have hKQ : K ≤ Q :=
    (le_mul_of_one_le_right (by linarith : 0 ≤ K) hN).trans
      (le_mul_of_one_le_right (by positivity : 0 ≤ K * N) hB)
  have hNQ : N ≤ Q :=
    (le_mul_of_one_le_left (by linarith : 0 ≤ N) hK).trans
      (le_mul_of_one_le_right (by positivity : 0 ≤ K * N) hB)
  have hBQ : B ≤ Q := le_mul_of_one_le_left (by linarith)
    (one_le_mul_of_one_le_of_one_le hK hN)
  have hquad : K * (N * B) * N ≤ Q ^ 2 := by
    calc
      _ = Q * N := by dsimp only [Q]; ring
      _ ≤ Q * Q := mul_le_mul_of_nonneg_left hNQ hQ0.le
      _ = _ := by ring
  have hlog (Y : ℝ) (hY : 1 ≤ Y) (hYQ : Y ≤ Q) :
      (columnDyadicLength Y + 1 : ℝ) ≤ A * Q ^ δ := by
    exact (columnDyadicLength_small_power δ hδ Y hY).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) hYQ hδ.le) hA.le)
  have hpow2 : (Q ^ 2) ^ δ = (Q ^ δ) ^ 2 := by
    rw [← Real.rpow_natCast_mul hQ0.le 2 δ]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]
    congr 1
    ring
  have hpow9 : (Q ^ δ) ^ 9 = Q ^ ε := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]
    congr 1
    dsimp only [δ]
    ring
  calc
    _ ≤ Q ^ δ * (Q ^ δ) ^ 2 * (A * Q ^ δ) ^ 2 * (A * Q ^ δ) ^ 2 * (A * Q ^ δ) ^ 2 := by
      have hbase := Real.rpow_le_rpow (by positivity : 0 ≤ K * (N * B) * N) hquad hδ.le
      rw [hpow2] at hbase
      gcongr
      · exact hlog K hK hKQ
      · exact hlog N hN hNQ
      · exact hlog B hB hBQ
    _ = A ^ 6 * (Q ^ δ) ^ 9 := by ring
    _ = _ := by rw [hpow9]

theorem supportedHybridRow_energy_sieve_norm (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B →
    ∀ (rows : Finset (Ideal Eis)) (S : Finset (Ideal Eis × Ideal Eis))
      (Pset : Finset (Ideal Eis)) (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ S, Squarefree p.1 ∧ primaryGenerator p.1 ≠ 0 ∧ primaryGenerator p.2 ≠ 0 ∧
        (Ideal.absNorm p.1 : ℝ) ≤ N ∧ (Ideal.absNorm p.2 : ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) → (∀ p ∈ S, ‖beta p.1 p.2‖ ≤ 1) →
      (∑ k ∈ rows, ‖supportedHybridRow S Pset a beta k‖ ^ 2) ≤
      C * (K * N * B) ^ ε * (K + N * B) * B * CubicSieve.sieveNorm N (2 * L) := by
  obtain ⟨C₀, hC₀, he⟩ := supportedHybridRow_energy_log (ε / 9) (by positivity)
  obtain ⟨C₁, hC₁, hlogs⟩ := hybrid_log_cost_bound ε hε
  refine ⟨C₀ * C₁, mul_pos hC₀ hC₁, ?_⟩
  intro K N B L hK hN hB rows S Pset a beta hrows hS hP ha hbeta
  have hb := he K N B L hK hN hB rows S Pset a beta hrows hS hP ha hbeta
  have hs : 0 ≤ CubicSieve.sieveNorm N (2 * L) := sq_nonneg _
  apply hb.trans
  calc
    _ = C₀ * (K ^ (ε / 9) * (K * (N * B) * N) ^ (ε / 9) *
        (columnDyadicLength K + 1 : ℝ) ^ 2 * (columnDyadicLength N + 1 : ℝ) ^ 2 *
          (columnDyadicLength B + 1 : ℝ) ^ 2) *
        (K + N * B) * B * CubicSieve.sieveNorm N (2 * L) := by ring
    _ ≤ C₀ * (C₁ * (K * N * B) ^ ε) * (K + N * B) * B * CubicSieve.sieveNorm N (2 * L) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hlogs K N B hK hN hB) hC₀.le)
            (by positivity)) (by linarith)) hs
    _ = _ := by ring

theorem hybridRow_energy_sieve_norm (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B →
    ∀ (rows nset bset Pset : Finset (Ideal Eis))
      (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n : ℝ) ≤ N) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b : ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) → (∀ n ∈ nset, ∀ b ∈ bset, ‖beta n b‖ ≤ 1) →
      (∑ k ∈ rows, ‖hybridRow Pset nset bset a beta k‖ ^ 2) ≤
      C * (K * N * B) ^ ε * (K + N * B) * B * CubicSieve.sieveNorm N (2 * L) := by
  obtain ⟨C, hC, he⟩ := supportedHybridRow_energy_sieve_norm ε hε
  refine ⟨C, hC, ?_⟩
  intro K N B L hK hN hB rows nset bset Pset a beta hrows hn hb hP ha hbeta
  have hprod : ∀ p ∈ nset ×ˢ bset,
      Squarefree p.1 ∧ primaryGenerator p.1 ≠ 0 ∧ primaryGenerator p.2 ≠ 0 ∧
        (Ideal.absNorm p.1 : ℝ) ≤ N ∧ (Ideal.absNorm p.2 : ℝ) ≤ B := by
    intro p hp
    obtain ⟨hpn, hpb⟩ := Finset.mem_product.mp hp
    exact ⟨(hn p.1 hpn).1.1, (hn p.1 hpn).1.2, (hb p.2 hpb).1,
      (hn p.1 hpn).2, (hb p.2 hpb).2⟩
  have hh := he K N B L hK hN hB rows (nset ×ˢ bset) Pset a beta hrows hprod hP ha
    (fun p hp => hbeta p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2)
  simpa only [supportedHybridRow_product] using hh

end
end SevenEighths.InverseMoment

end OAI
