import OAI.NumberTheory.Ostmann.Construction.PrimeGridSupport
import OAI.NumberTheory.Ostmann.Construction.WeightedPrimeNormalization

namespace OAI

/-! # Point masses of the original cutoff-weighted prime priors -/

namespace Ostmann

open scoped BigOperators
open Filter

theorem primeSamplePrior_value_mul (S : Finset ℕ) (w : ℝ → ℝ) (Z : ℝ)
    (p : S) (hp : (p : ℕ) ≠ 0) :
    ((p : ℕ) : ℝ) * primeSamplePrior S w Z p = Z * w (Real.log (p : ℕ)) := by
  have hpR : ((p : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hp
  unfold primeSamplePrior
  field_simp

theorem primeSamplePrior_atom_le (S : Finset ℕ) (w : ℝ → ℝ) (Z W s : ℝ)
    (hZ : 0 ≤ Z) (hW : 0 ≤ W) (p : S) (hp : 0 < (p : ℕ))
    (hw : w (Real.log (p : ℕ)) ≤ W) (hlog : s ≤ Real.log (p : ℕ)) :
    primeSamplePrior S w Z p ≤ Z * W * Real.exp (-s) := by
  have hpR : (0 : ℝ) < (p : ℕ) := by exact_mod_cast hp
  have he : Real.exp s ≤ (p : ℕ) := by
    simpa only [Real.exp_log hpR] using Real.exp_le_exp.mpr hlog
  have hi : (((p : ℕ) : ℝ))⁻¹ ≤ Real.exp (-s) := by
    simpa only [one_div, Real.exp_neg] using one_div_le_one_div_of_le (Real.exp_pos s) he
  unfold primeSamplePrior
  calc
    _ ≤ Z * (W * (((p : ℕ) : ℝ))⁻¹) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hw (by positivity)) hZ
    _ ≤ Z * (W * Real.exp (-s)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hi hW) hZ
    _ = _ := by ring

theorem sum_primeLogCellSet_weight (q a : ℕ) (s t : ℝ) (w : ℝ → ℝ) :
    (∑ p ∈ primeLogCellSet q a s t, w (Real.log p) * (p : ℝ)⁻¹) =
      weightedReciprocalPrimeInterval q a s t w := by
  simp only [primeLogCellSet, Finset.sum_filter, weightedReciprocalPrimeInterval]

/-- The input needed by repeated-prior domination and accidental polynomial
zeros follows from the original prime prior and the published normalization
estimate. The same bound is uniform in every atom of the log interval. -/
theorem PublishedProgressionInput.prime_interval_atom_bounds (P : PublishedProgressionInput) :
    ∀ᶠ u : ℝ in atTop, ∀ (s t : ℝ) (w : ℝ → ℝ) (b W : ℝ),
      s ≤ u → u + 1 ≤ t → 0 < b → 0 ≤ W →
      (∀ y ∈ Set.Ioc s t, 0 ≤ w y) →
      (∀ y ∈ Set.Ioc s t, w y ≤ W) →
      (∀ y ∈ Set.Ioc u (u + 1), b ≤ w y) →
      let S := primeLogCellSet 1 0 s t
      let Z := (weightedReciprocalPrimeInterval 1 0 s t w)⁻¹
      (∑ p : S, primeSamplePrior S w Z p) = 1 ∧
      ∀ p : S, 0 ≤ primeSamplePrior S w Z p ∧
        ((p : ℕ) : ℝ) * primeSamplePrior S w Z p ≤ 2 * (u + 1) * W / b ∧
        primeSamplePrior S w Z p ≤ (2 * (u + 1) * W / b) * Real.exp (-s) := by
  filter_upwards [P.weighted_normalization_bound] with u hu
  intro s t w b W hsu hut hb hW hw hwupper hwlower
  dsimp only
  obtain ⟨hmass, hnorm⟩ := hu s t w b hsu hut hb hw hwlower
  have hZ : 0 ≤ (weightedReciprocalPrimeInterval 1 0 s t w)⁻¹ := inv_nonneg.mpr hmass.le
  constructor
  · rw [← sum_primeLogCellSet_weight 1 0 s t w]
    apply primeSamplePrior_normalized
      (primeLogCellSet 1 0 s t) w (by rw [sum_primeLogCellSet_weight]; exact hmass.ne')
  · intro p
    have hp := mem_primeLogCellSet_iff.mp p.property
    have hWp := hwupper _ hp.2.2
    have hZW : (weightedReciprocalPrimeInterval 1 0 s t w)⁻¹ * W ≤
        2 * (u + 1) * W / b := by
      calc
        _ ≤ (2 * (u + 1) / b) * W := mul_le_mul_of_nonneg_right hnorm hW
        _ = _ := by ring
    refine ⟨primeSamplePrior_nonneg _ w _ hZ (fun p hp =>
      hw _ (mem_primeLogCellSet_iff.mp hp).2.2) p, ?_, ?_⟩
    · rw [primeSamplePrior_value_mul _ w _ p hp.1.ne_zero]
      exact (mul_le_mul_of_nonneg_left hWp hZ).trans hZW
    · exact (primeSamplePrior_atom_le _ w _ W s hZ hW p hp.1.pos hWp hp.2.2.1.le).trans
        (mul_le_mul_of_nonneg_right hZW (Real.exp_pos _).le)

end Ostmann

end OAI
