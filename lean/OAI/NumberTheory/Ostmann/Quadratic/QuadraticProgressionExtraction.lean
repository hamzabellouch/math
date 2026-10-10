import OAI.NumberTheory.Ostmann.Quadratic.QuadraticProgressionPhase
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticResidueExtraction

namespace OAI

/-! # From the original positive sum to its long weighted progression -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem quadratic_cutoff_scale (q s v : ℕ) (R B : ℝ)
    (hq : 0 < q) (hs : 0 < s) (hv : 0 < v) (hR : 0 < R) (hB : 0 ≤ B) :
    Real.sqrt (B ^ 2 * R * q / ((s : ℝ) * v)) =
      B * q * Real.sqrt (R / ((s : ℝ) * v * q)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  field_simp

theorem quadratic_normalizer_progression_scale (q s v : ℕ) (R : ℝ)
    (hq : 0 < q) (hs : 0 < s) (hv : 0 < v) (hR : 0 < R) :
    Real.sqrt (R * q / ((s : ℝ) * v)) =
      q * Real.sqrt (R / ((s : ℝ) * v * q)) := by
  simpa using quadratic_cutoff_scale q s v R 1 hq hs hv hR zero_le_one

/-- The estimate is extracted from the actual compactly supported positive
series. Its hypothesis is the explicit large-sum event in the manuscript. -/
theorem positiveQuadraticSum_large_progression {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (hg : ∀ x, ¬IsUnit x → g x = 0)
    (henergy : (∑ x : ZMod q, ‖g x‖ ^ 2) ≤ q)
    (a : ZMod q) (h₀ s v : ℕ) (θ R B A : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hs : 0 < s) (hv : 0 < v) (hR : 0 < R) (hB : 3 ≤ B)
    (hY : 1 ≤ Real.sqrt (R / ((s : ℝ) * v * q))) (hA : 0 ≤ A)
    (hΦ : ∀ x : ℝ, B ^ 2 < x → Φ x = 0)
    (hlarge : (Real.sqrt ((2 : ℝ) ^ (q.primeFactors.card + 1)) * q) * A <
      Real.sqrt (R * q / ((s : ℝ) * v)) *
        ‖positiveQuadraticSum g a ((h₀ : ℝ) + θ) Φ R v s‖) :
    ∃ r : ℕ, 0 < r ∧ r ≤ q ∧
      let N := (⌊B * q * Real.sqrt (R / ((s : ℝ) * v * q))⌋₊ + q - r) / q
      Real.sqrt (R / ((s : ℝ) * v * q)) ≤ (N : ℝ) ∧
      (N : ℝ) ≤ (B + 1) * Real.sqrt (R / ((s : ℝ) * v * q)) ∧
      A < ‖∑ j ∈ Finset.range N,
        Φ ((((j : ℝ) + (r : ℝ) / q) / Real.sqrt (R / ((s : ℝ) * v * q))) ^ 2) *
          realQuadraticPhase (((s * v * q : ℕ) : ℝ) * θ) (2 * θ * s * v * r) j‖ := by
  have hq := NeZero.pos q
  rw [positiveQuadraticSum_eq_cutoff g a _ Φ R v (B ^ 2) s s hR
    (by exact_mod_cast hv) hs le_rfl hΦ] at hlarge
  rw [quadraticCompactCutoff, quadratic_cutoff_scale q s v R B hq hs hv hR (by linarith)] at hlarge
  obtain ⟨r, hr⟩ := quadraticDensitySum_large_residue g hg henergy _ a h₀ s v θ R A Φ
    hs hv hR hA hlarge
  obtain ⟨r₀, hr₀, hrq, hrval⟩ := exists_positive_residue_representative r
  refine ⟨r₀, hr₀, hrq, ?_⟩
  dsimp only
  obtain ⟨hNlo, hNhi⟩ := positive_progression_length_bounds q r₀ B _ hq hr₀ hrq hB hY
  refine ⟨hNlo, hNhi, ?_⟩
  rw [← hrval, sum_positive_zmod_progression r₀ _ hr₀ hrq,
    quadratic_progression_sum_norm q s v r₀ _ θ R Φ hq hs hv hR] at hr
  exact hr

end Ostmann

end OAI
