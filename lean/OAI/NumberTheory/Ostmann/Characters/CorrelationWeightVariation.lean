import OAI.NumberTheory.Ostmann.Characters.SchwartzWeightVariation

namespace OAI

/-! # Uniform variation of the two transform factors in a correlation -/

namespace Ostmann

open scoped BigOperators SchwartzMap ComplexConjugate

theorem discreteVariation_conj (w : ℕ → ℂ) (N : ℕ) :
    discreteVariation (fun n => conj (w n)) N = discreteVariation w N := by
  simp only [discreteVariation, ← map_sub, Complex.norm_conj]

theorem discreteVariation_mul_le (w z : ℕ → ℂ) (N : ℕ) (B C : ℝ)
    (hC : 0 ≤ C) (hw : ∀ n, ‖w n‖ ≤ B) (hz : ∀ n, ‖z n‖ ≤ C) :
    discreteVariation (fun n => w n * z n) N ≤
      B * discreteVariation z N + C * discreteVariation w N := by
  have hstep (j : ℕ) : ‖w (j + 1) * z (j + 1) - w j * z j‖ ≤
      B * ‖z (j + 1) - z j‖ + C * ‖w (j + 1) - w j‖ := by
    calc
      _ = ‖w (j + 1) * (z (j + 1) - z j) + (w (j + 1) - w j) * z j‖ := by
        congr 1
        ring
      _ ≤ ‖w (j + 1) * (z (j + 1) - z j)‖ + ‖(w (j + 1) - w j) * z j‖ := norm_add_le _ _
      _ ≤ B * ‖z (j + 1) - z j‖ + C * ‖w (j + 1) - w j‖ := by
        simp only [norm_mul]
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right (hw _) (norm_nonneg _)
        · rw [mul_comm C]
          exact mul_le_mul_of_nonneg_left (hz _) (norm_nonneg _)
  have hend : ‖w (N - 1) * z (N - 1)‖ ≤
      B * ‖z (N - 1)‖ + C * ‖w (N - 1)‖ := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hw _) (norm_nonneg _)).trans
      (le_add_of_nonneg_right (by positivity))
  unfold discreteVariation
  calc
    _ ≤ (B * ‖z (N - 1)‖ + C * ‖w (N - 1)‖) +
        ∑ j ∈ Finset.range (N - 1), (B * ‖z (j + 1) - z j‖ + C * ‖w (j + 1) - w j‖) :=
      add_le_add hend (Finset.sum_le_sum (fun j _ => hstep j))
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring

/-- The two smooth Fourier-transform weights have uniform variation on any
interval whose length is bounded by both scaling lengths. -/
theorem schwartz_correlation_variation (Φ Ψ : 𝓢(ℝ, ℂ))
    (ξ η Y Z C D : ℝ) (N : ℕ) (hY : 0 < Y) (hZ : 0 < Z)
    (hNY : (N : ℝ) ≤ C * Y) (hNZ : (N : ℝ) ≤ D * Z) :
    discreteVariation (fun n => Φ (((n : ℝ) + ξ) / Y) *
      conj (Ψ (((n : ℝ) + η) / Z))) N ≤
      SchwartzMap.seminorm ℝ 0 0 Φ *
        (SchwartzMap.seminorm ℝ 0 0 Ψ + SchwartzMap.seminorm ℝ 0 1 Ψ * D) +
      SchwartzMap.seminorm ℝ 0 0 Ψ *
        (SchwartzMap.seminorm ℝ 0 0 Φ + SchwartzMap.seminorm ℝ 0 1 Φ * C) := by
  have hB : 0 ≤ SchwartzMap.seminorm ℝ 0 0 Φ :=
    (norm_nonneg _).trans (Φ.norm_le_seminorm ℝ 0)
  have hB' : 0 ≤ SchwartzMap.seminorm ℝ 0 0 Ψ :=
    (norm_nonneg _).trans (Ψ.norm_le_seminorm ℝ 0)
  apply (discreteVariation_mul_le _ _ N _ _ hB'
    (fun n => Φ.norm_le_seminorm ℝ _) (fun n => by
      rw [Complex.norm_conj]
      exact Ψ.norm_le_seminorm ℝ _)).trans
  rw [discreteVariation_conj]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (schwartz_rescaled_variation Ψ η Z D N hZ hNZ) hB)
    (mul_le_mul_of_nonneg_left (schwartz_rescaled_variation Φ ξ Y C N hY hNY) hB')

end Ostmann

end OAI
