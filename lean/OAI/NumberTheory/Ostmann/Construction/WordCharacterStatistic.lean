import OAI.NumberTheory.Ostmann.Construction.WordCopyCoordinates

namespace OAI

/-! # The positive word statistic is the real part of the actual tuple mean -/

namespace Ostmann

open scoped BigOperators SchwartzMap ComplexConjugate Classical

theorem bounded_schwartz_mul_summable (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X)
    (F : ℤ → ℂ) (hF : ∀ a, ‖F a‖ ≤ 1) :
    Summable (fun a : ℤ => F a * ψ ((a : ℝ) / X)) := by
  have hs : Summable (fun a : ℤ => ‖ψ ((a : ℝ) / X)‖) := by
    simpa only [positiveDilate_apply, div_eq_mul_inv, mul_comm] using
      schwartz_int_norm_summable (positiveDilate ψ X⁻¹ (inv_pos.mpr hX))
  apply Summable.of_norm_bounded hs
  intro a
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hF a)

theorem characterTupleSum_re {I : Type*} [Fintype I] (p : I → ℕ)
    (χ : I → ∀ q : ℕ, DirichletCharacter ℂ q) (t : ∀ q : ℕ, ZMod q)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) (hψ : ∀ x, (ψ x).im = 0) :
    (characterTupleSum p χ t ψ X).re = ∑' a : ℤ, (ψ ((a : ℝ) / X)).re *
      (∏ i, χ i (p i) ((a : ZMod (p i)) - t (p i))).re := by
  have hs := bounded_schwartz_mul_summable ψ X hX
    (fun a => ∏ i, χ i (p i) ((a : ZMod (p i)) - t (p i)))
    (fun a => by
      rw [norm_prod]
      exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => (χ i (p i)).norm_le_one _))
  change Complex.reCLM (∑' a : ℤ, _ * ψ ((a : ℝ) / X)) = _
  rw [Complex.reCLM.map_tsum hs]
  apply tsum_congr
  intro a
  simp only [Complex.reCLM_apply, Complex.mul_re, hψ, mul_zero, sub_zero]
  ring

theorem wordCopyCorrelation_tsum {A B : Type*} {k m : ℕ} (v : A → ℕ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (t : ∀ p : ℕ, ZMod p)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) (hψ : ∀ x, (ψ x).im = 0)
    (bin : (Fin k → A) → B) (b : B)
    (z : ((Fin k → A) × (Fin m → A)) × ((Fin k → A) × (Fin m → A))) :
    (∑' a : ℤ, (ψ ((a : ℝ) / X)).re *
      (jointWordAmplitude (fun _ p => χ (v p) ((a : ZMod (v p)) - t (v p)))
          (fun _ p => χ (v p) ((a : ZMod (v p)) - t (v p))) bin b z.1 *
        conj (jointWordAmplitude (fun _ p => χ (v p) ((a : ZMod (v p)) - t (v p)))
          (fun _ p => χ (v p) ((a : ZMod (v p)) - t (v p))) bin b z.2)).re) =
      if bin z.1.1 = b ∧ bin z.2.1 = b then
        (characterTupleSum (v ∘ wordCopyEquiv A k m z) (wordCopyCharacter k m χ) t ψ X).re
      else 0 := by
  simp_rw [wordCopyAmplitude_map]
  by_cases hz : bin z.1.1 = b ∧ bin z.2.1 = b
  · simp only [hz]
    exact (characterTupleSum_re _ _ _ ψ X hX hψ).symm
  · simp [hz]

noncomputable def wordCharacterMean {A B : Type*} [Fintype A] {k m : ℕ}
    (v : A → ℕ) (μ : Fin k → A → ℝ) (ν : Fin m → A → ℝ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (t : ∀ p : ℕ, ZMod p)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (bin : (Fin k → A) → B) (b : B) : ℂ :=
  ∑ x, if bin ((wordCopyEquiv A k m).symm x).1.1 = b ∧
      bin ((wordCopyEquiv A k m).symm x).2.1 = b then
    (productPrior (Fin.append (Fin.append μ ν) (Fin.append μ ν)) x : ℂ) *
      characterTupleSum (v ∘ x) (wordCopyCharacter k m χ) t ψ X else 0

theorem word_statistic_eq_character_mean {A B : Type*} [Fintype A] {k m : ℕ}
    (v : A → ℕ) (μ : Fin k → A → ℝ) (ν : Fin m → A → ℝ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (t : ∀ p : ℕ, ZMod p)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) (hψ : ∀ x, (ψ x).im = 0)
    (bin : (Fin k → A) → B) (b : B) :
    (∑' a : ℤ, wordStatisticTerm ψ X
      (fun a => binnedWordAverage μ (fun _ p => χ (v p) ((a : ZMod (v p)) - t (v p))) bin b)
      (fun i a => ∑ p, (ν i p : ℂ) * χ (v p) ((a : ZMod (v p)) - t (v p))) a) =
      (wordCharacterMean v μ ν χ t ψ X bin b).re := by
  rw [word_statistic_tsum_double_expansion ψ X hX μ ν]
  · conv_lhs =>
      enter [2, z, 2, z', 2]
      rw [wordCopyCorrelation_tsum v χ t ψ X hX hψ bin b (z, z')]
    unfold wordCharacterMean
    rw [← (wordCopyEquiv A k m).sum_comp]
    conv_rhs => rw [Fintype.sum_prod_type]
    simp only [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro z' _
    rw [Equiv.symm_apply_apply, wordCopyPrior]
    by_cases h : bin z.1 = b ∧ bin z'.1 = b
    · simp [h, Complex.mul_re]
    · simp [h]
  · exact fun a i p => (χ (v p)).norm_le_one _
  · exact fun a i p => (χ (v p)).norm_le_one _

end Ostmann

end OAI
