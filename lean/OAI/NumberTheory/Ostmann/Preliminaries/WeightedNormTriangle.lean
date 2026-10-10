import OAI.NumberTheory.Ostmann.QuadraticCenter.WeightedCorrelationEnergy

namespace OAI

/-! # A finite weighted square norm under divisor summation -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem weighted_correlation_le_sqrt_energy {ι : Type*} (S : Finset ι)
    (μ : ι → ℝ) (f g : ι → ℂ) (hμ : ∀ s ∈ S, 0 ≤ μ s) :
    ‖∑ s ∈ S, (μ s : ℂ) * (f s * conj (g s))‖ ≤
      Real.sqrt (∑ s ∈ S, μ s * ‖f s‖ ^ 2) *
      Real.sqrt (∑ s ∈ S, μ s * ‖g s‖ ^ 2) := by
  have he (a : ι → ℂ) : (∑ s ∈ S, (Real.sqrt (μ s) * ‖a s‖) ^ 2) =
      ∑ s ∈ S, μ s * ‖a s‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro s hs
    rw [mul_pow, Real.sq_sqrt (hμ s hs)]
  calc
    _ ≤ ∑ s ∈ S, μ s * (‖f s‖ * ‖g s‖) := by
      apply (norm_sum_le _ _).trans_eq
      apply Finset.sum_congr rfl
      intro s hs
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hμ s hs), Complex.norm_conj]
    _ = ∑ s ∈ S, (Real.sqrt (μ s) * ‖f s‖) * (Real.sqrt (μ s) * ‖g s‖) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [mul_mul_mul_comm, ← pow_two, Real.sq_sqrt (hμ s hs)]
    _ ≤ _ := by
      simpa only [he] using Real.sum_mul_le_sqrt_mul_sqrt S
        (fun s => Real.sqrt (μ s) * ‖f s‖) (fun s => Real.sqrt (μ s) * ‖g s‖)

theorem sqrt_weighted_sum_energy_le {ι κ : Type*}
    (S : Finset ι) (D : Finset κ) (μ : ι → ℝ) (c : κ → ℂ)
    (G : κ → ι → ℂ) (B : ℝ) (hμ : ∀ s ∈ S, 0 ≤ μ s) (hB : 0 ≤ B)
    (hG : ∀ d ∈ D, Real.sqrt (∑ s ∈ S, μ s * ‖G d s‖ ^ 2) ≤ B) :
    Real.sqrt (∑ s ∈ S, μ s * ‖∑ d ∈ D, c d * G d s‖ ^ 2) ≤
      B * ∑ d ∈ D, ‖c d‖ := by
  have hp (d : κ) (hd : d ∈ D) (e : κ) (he : e ∈ D) :
      ‖∑ s ∈ S, (μ s : ℂ) * (G d s * conj (G e s))‖ ≤ B ^ 2 := by
    apply (weighted_correlation_le_sqrt_energy S μ (G d) (G e) hμ).trans
    simpa only [pow_two] using mul_le_mul (hG d hd) (hG e he) (Real.sqrt_nonneg _) hB
  have hb : (∑ s ∈ S, μ s * ‖∑ d ∈ D, c d * G d s‖ ^ 2) ≤
      (B * ∑ d ∈ D, ‖c d‖) ^ 2 := by
    apply (weighted_sum_energy_le_correlations S D μ c G).trans
    calc
      _ ≤ ∑ d ∈ D, ∑ e ∈ D, (‖c d‖ * ‖c e‖) * B ^ 2 := by
        apply Finset.sum_le_sum
        intro d hd
        apply Finset.sum_le_sum
        intro e he
        exact mul_le_mul_of_nonneg_left (hp d hd e he) (by positivity)
      _ = _ := by
        simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
        rw [← Finset.sum_mul]
        ring
  exact (Real.sqrt_le_sqrt hb).trans_eq (Real.sqrt_sq (by positivity))

end Ostmann

end OAI
