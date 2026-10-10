import OAI.NumberTheory.Ostmann.QuadraticSieveLargeGcdBasic
import OAI.NumberTheory.Ostmann.QuadraticSieveWeightedNorm

namespace OAI

namespace Ostmann.QuadraticSieve

def largeGcdCoefficients (d k : ℕ) (a : ℕ → ℂ) (r : ℕ) : ℂ :=
  if k ∣ r then a (d * r) else 0

theorem coefficientEnergy_largeGcdCoefficients_le (S : Finset ℕ) (a : ℕ → ℂ) (d k : ℕ) :
    coefficientEnergy (quotientSupport S d) (largeGcdCoefficients d k a) ≤
      coefficientEnergy (quotientSupport S d) (quotientCoefficients d k a) := by
  unfold coefficientEnergy
  apply Finset.sum_le_sum
  intro r hr
  by_cases hk : k ∣ r
  · have hkr : k ∣ d * r := dvd_mul_of_dvd_right hk d
    simp only [largeGcdCoefficients, quotientCoefficients, ite_eq_left hk, ite_eq_left hkr, le_refl]
  · simp only [largeGcdCoefficients, ite_eq_right hk, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact sq_nonneg _

theorem sum_coefficientEnergy_largeGcdCoefficients_le (S : Finset ℕ) (a : ℕ → ℂ) (d N : ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) :
    (∑ k ∈ Finset.Icc 1 N, coefficientEnergy (quotientSupport S d) (largeGcdCoefficients d k a)) ≤
      divisorWeightedEnergy S d a := by
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 N, coefficientEnergy (quotientSupport S d) (quotientCoefficients d k a) :=
      Finset.sum_le_sum (fun k hk => coefficientEnergy_largeGcdCoefficients_le S a d k)
    _ = _ := sum_coefficientEnergy_quotient S a d N hS

theorem gcdJacobiRow_norm_le_divisor_energies (S : Finset ℕ) (a : ℕ → ℂ)
    {d : ℕ} (hd : 0 < d) (N : ℕ) (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) (m : ℤ) :
    ‖gcdJacobiRow S a d m‖ ≤
      ∑ k ∈ Finset.Icc 1 N,
        ‖∑ r ∈ quotientSupport S d, largeGcdCoefficients d k a r * (jacobiSym m r : ℂ)‖ ^ 2 := by
  have hQ : ∀ r ∈ quotientSupport S d, 0 < r ∧ r ≤ N := by
    intro r hr
    refine ⟨quotientSupport_pos (fun n hn => (hS n hn).1) hr, ?_⟩
    obtain ⟨n, hn, hdn, rfl⟩ := mem_quotientSupport.mp hr
    exact (Nat.div_le_self n d).trans (hS n hn).2
  apply (gcdJacobiRow_norm_le_quotient S a hd (fun n hn => (hS n hn).1) m).trans
  convert coprime_correlation_norm_le (quotientSupport S d)
    (fun r => a (d * r) * (jacobiSym m r : ℂ)) N hQ using 1
  apply Finset.sum_congr rfl
  intro k hk
  congr 2
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hkr : k ∣ r <;> simp [largeGcdCoefficients, hkr]

noncomputable def weightedGcdMass (W : Finset ℤ) (S : Finset ℕ)
    (ω : ℤ → ℝ) (a : ℕ → ℂ) (d : ℕ) : ℝ :=
  ∑ m ∈ W, ω m * ‖gcdJacobiRow S a d m‖

lemma weightedGcdMass_nonneg (W : Finset ℤ) (S : Finset ℕ) (ω : ℤ → ℝ)
    (hω : ∀ m ∈ W, 0 ≤ ω m) (a : ℕ → ℂ) (d : ℕ) :
    0 ≤ weightedGcdMass W S ω a d :=
  Finset.sum_nonneg (fun m hm => mul_nonneg (hω m hm) (norm_nonneg _))

theorem weightedGcdMass_le_quotient_norm (W : Finset ℤ) (S : Finset ℕ)
    (ω : ℤ → ℝ) (hω : ∀ m ∈ W, 0 ≤ ω m) (a : ℕ → ℂ)
    {d : ℕ} (hd : 0 < d) (N : ℕ) (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) :
    weightedGcdMass W S ω a d ≤
      weightedNumeratorNorm W (quotientSupport S d) ω * divisorWeightedEnergy S d a := by
  calc
    _ ≤ ∑ m ∈ W, ω m * ∑ k ∈ Finset.Icc 1 N,
        ‖∑ r ∈ quotientSupport S d, largeGcdCoefficients d k a r * (jacobiSym m r : ℂ)‖ ^ 2 :=
      Finset.sum_le_sum (fun m hm => mul_le_mul_of_nonneg_left
        (gcdJacobiRow_norm_le_divisor_energies S a hd N hS m) (hω m hm))
    _ = ∑ k ∈ Finset.Icc 1 N,
        weightedNumeratorEnergy W (quotientSupport S d) ω (largeGcdCoefficients d k a) := by
      simp only [Finset.mul_sum, weightedNumeratorEnergy]
      rw [Finset.sum_comm]
    _ ≤ ∑ k ∈ Finset.Icc 1 N, weightedNumeratorNorm W (quotientSupport S d) ω *
        coefficientEnergy (quotientSupport S d) (largeGcdCoefficients d k a) :=
      Finset.sum_le_sum (fun k hk => weightedNumeratorEnergy_le_norm _ _ _ _)
    _ = weightedNumeratorNorm W (quotientSupport S d) ω *
        (∑ k ∈ Finset.Icc 1 N, coefficientEnergy (quotientSupport S d) (largeGcdCoefficients d k a)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_coefficientEnergy_largeGcdCoefficients_le S a d N hS)
      (weightedNumeratorNorm_nonneg _ _ _)

theorem weighted_quotient_norm_le_prefix (W : Finset ℤ) {S : Finset ℕ}
    (ω : ℤ → ℝ) {N D d : ℕ} (hS : S ⊆ oddSquarefreeUpTo N)
    (hD : 0 < D) (hd : D ≤ d) :
    weightedNumeratorNorm W (quotientSupport S d) ω ≤
      weightedNumeratorNorm W (oddSquarefreeUpTo (N / D)) ω := by
  apply weightedNumeratorNorm_mono_columns
  intro r hr
  obtain ⟨hr1, hrN, hro, hrsq⟩ := mem_oddSquarefreeUpTo.mp
    (quotientSupport_subset_oddSquarefreeUpTo hS hr)
  exact mem_oddSquarefreeUpTo.mpr ⟨hr1, hrN.trans (Nat.div_le_div_left hd hD), hro, hrsq⟩

theorem sum_weightedGcdMass_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : Finset ℤ) (E S : Finset ℕ)
      (ω : ℤ → ℝ) (a : ℕ → ℂ) (N D : ℕ),
      (∀ m ∈ W, 0 ≤ ω m) → S ⊆ oddSquarefreeUpTo N → 0 < D →
      (∀ d ∈ E, D ≤ d) →
      (∑ d ∈ E, weightedGcdMass W S ω a d) ≤
        C * (N : ℝ) ^ ε * weightedNumeratorNorm W (oddSquarefreeUpTo (N / D)) ω *
          coefficientEnergy S a := by
  obtain ⟨C, hC, hdiv⟩ := sum_divisorWeightedEnergy_le_rpow ε hε
  refine ⟨C, hC, ?_⟩
  intro W E S ω a N D hω hS hD hE
  have hSN : ∀ n ∈ S, 0 < n ∧ n ≤ N := fun n hn =>
    ⟨(mem_oddSquarefreeUpTo.mp (hS hn)).1, (mem_oddSquarefreeUpTo.mp (hS hn)).2.1⟩
  calc
    _ ≤ ∑ d ∈ E, weightedNumeratorNorm W (oddSquarefreeUpTo (N / D)) ω *
        divisorWeightedEnergy S d a := by
      apply Finset.sum_le_sum
      intro d hd
      exact (weightedGcdMass_le_quotient_norm W S ω hω a (hD.trans_le (hE d hd)) N hSN).trans
        (mul_le_mul_of_nonneg_right (weighted_quotient_norm_le_prefix W ω hS hD (hE d hd))
          (divisorWeightedEnergy_nonneg _ _ _))
    _ = weightedNumeratorNorm W (oddSquarefreeUpTo (N / D)) ω *
        (∑ d ∈ E, divisorWeightedEnergy S d a) := (Finset.mul_sum _ _ _).symm
    _ ≤ weightedNumeratorNorm W (oddSquarefreeUpTo (N / D)) ω *
        (C * (N : ℝ) ^ ε * coefficientEnergy S a) :=
      mul_le_mul_of_nonneg_left (hdiv N E S a hSN) (weightedNumeratorNorm_nonneg _ _ _)
    _ = _ := by ring

end Ostmann.QuadraticSieve

end OAI
