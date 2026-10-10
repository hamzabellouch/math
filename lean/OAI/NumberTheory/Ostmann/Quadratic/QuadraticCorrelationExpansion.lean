import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCorrelationNormalization

namespace OAI

/-! # Expanding the two finite quadratic sums before the kernel average -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem finite_correlation_expansion {ι κ υ : Type*}
    (S : Finset ι) (W : Finset κ) (V : Finset υ) (F : κ → ι → ℂ) (G : υ → ι → ℂ) :
    (∑ s ∈ S, (∑ w ∈ W, F w s) * conj (∑ v ∈ V, G v s)) =
      ∑ w ∈ W, ∑ v ∈ V, ∑ s ∈ S, F w s * conj (G v s) := by
  simp_rw [map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  rw [Finset.sum_comm]

theorem finite_correlation_pair_bound {ι κ υ : Type*}
    (S : Finset ι) (W : Finset κ) (V : Finset υ) (F : κ → ι → ℂ) (G : υ → ι → ℂ)
    (B : ℝ) (hB : ∀ w ∈ W, ∀ v ∈ V, ‖∑ s ∈ S, F w s * conj (G v s)‖ ≤ B) :
    ‖∑ s ∈ S, (∑ w ∈ W, F w s) * conj (∑ v ∈ V, G v s)‖ ≤
      (W.card : ℝ) * V.card * B := by
  rw [finite_correlation_expansion]
  calc
    _ ≤ ∑ w ∈ W, ‖∑ v ∈ V, ∑ s ∈ S, F w s * conj (G v s)‖ := norm_sum_le _ _
    _ ≤ ∑ w ∈ W, ∑ v ∈ V, B := by
      apply Finset.sum_le_sum
      intro w hw
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun v hv => hB w hw v hv))
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

/-- The exact normalized pair count is all that remains after bounding each
expanded pair by the translated periodic estimate. -/
theorem normalized_quadratic_pair_bound {ι κ υ : Type*}
    (S : Finset ι) (W : Finset κ) (V : Finset υ) (σ : ι → ℝ)
    (F : κ → ι → ℂ) (G : υ → ι → ℂ) (R d e v B : ℝ)
    (hR : 0 < R) (hd : 0 < d) (he : 0 < e) (hv : 0 < v)
    (hσ : ∀ s ∈ S, 0 < σ s)
    (hB : ∀ w ∈ W, ∀ v ∈ V, ‖∑ s ∈ S, F w s * conj (G v s)‖ ≤ B) :
    ‖∑ s ∈ S,
      (((Real.sqrt (R * d / (σ s * v)) : ℝ) : ℂ)⁻¹ * ∑ w ∈ W, F w s) *
        conj (((Real.sqrt (R * e / (σ s * v)) : ℝ) : ℂ)⁻¹ * ∑ v ∈ V, G v s) / (σ s : ℂ)‖ ≤
      v / (R * Real.sqrt (d * e)) * ((W.card : ℝ) * V.card * B) := by
  exact quadratic_normalized_correlation_bound S σ _ _ R d e v _ hR hd he hv hσ
    (finite_correlation_pair_bound S W V F G B hB)

/-- The support pair count cancels the normalization and the interval length. -/
theorem quadratic_pair_count_cancellation (R d e v N C A H : ℝ)
    (hR : 0 < R) (hd : 0 < d) (he : 0 < e) (hv : 0 < v) (hN : 0 < N)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (J J' : ℕ)
    (hJ : (J : ℝ) * J' ≤ H * R * Real.sqrt (d * e) / (N * v)) :
    v / (R * Real.sqrt (d * e)) * ((J : ℝ) * J' * (C * A * N)) ≤ H * C * A := by
  have hs : 0 < Real.sqrt (d * e) := Real.sqrt_pos.mpr (mul_pos hd he)
  calc
    _ ≤ v / (R * Real.sqrt (d * e)) *
        ((H * R * Real.sqrt (d * e) / (N * v)) * (C * A * N)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right hJ (by positivity)
    _ = _ := by field_simp

end Ostmann

end OAI
