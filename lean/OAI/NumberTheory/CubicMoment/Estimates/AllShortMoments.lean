import OAI.NumberTheory.CubicMoment.Estimates.ShortFactorSize

namespace OAI

/-! Uniform exceptional-moment savings when every actual short factor
stays a fixed distance below length exponent one. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

private lemma short_length_le_scale {X Y δ : ℝ} (hY : 1 ≤ Y) (hδ : 0 ≤ δ)
    (hX : X ≤ Y^(1-δ)) : X ≤ Y := by
  calc
    X ≤ Y^(1-δ) := hX
    _ ≤ Y^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hY (by linarith)
    _ = Y := Real.rpow_one Y

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The all-short first exceptional configuration has a uniform power saving.
The actual short arithmetic coefficients and independent bounded twists are
allowed to vary freely; no amplitude or row-cardinality hypotheses remain. -/
theorem all_short_cubic_moment {δ C : ℝ} (hδ : 0 < δ) (hC : 0 < C) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ, ∀ (F : ShortFactorFamily ι) (j : ℕ)
      (Y : ℝ) (S : Finset Eisenstein), Y₀ ≤ Y →
      (∀ i, F.length j i ≤ Y^(1-δ)) →
      (Y/C ≤ ∏ i, F.length j i) → (∏ i, F.length j i) ≤ C*Y →
      (∀ p ∈ S, gramDyad Y p) →
      (∑ p ∈ S, ‖∏ i, F.cubicValue j i p‖^2) ≤ Y^(7/3-ε) := by
  obtain ⟨ε,hε,T₀,huniform⟩ := cubic_short_uniform_power (ι := ι)
    (H := 2) (D := 2) hδ (by norm_num) (by norm_num) hC
  obtain ⟨T,hT,hsize⟩ := shortFactorPolynomial_uniform_quadratic_size
  refine ⟨ε,hε,max T₀ (max T 36),?_⟩
  intro F j Y S hY hshort hlo hhi hS
  have hYT : T ≤ Y := (le_max_left T 36).trans ((le_max_right _ _).trans hY)
  have hY₁ : 1 ≤ Y := hT.trans hYT
  have hY₃₆ : 36 ≤ Y := (le_max_right T 36).trans ((le_max_right _ _).trans hY)
  let x : ShortMomentInstance ι Eisenstein := ⟨Y,F.comp (fun _ => j),S⟩
  have hx : cubicInstanceAdmissible δ 2 2 C x := by
    refine ⟨hshort,⟨hlo,hhi⟩,hS,?_,?_⟩
    · simpa only [Real.rpow_two] using primary_gram_rows_card_quadratic S hY₃₆ hS
    · intro p hp i
      change ‖F.cubicValue j i p‖ ≤ Y^(2:ℝ)
      rw [Real.rpow_two]
      apply hsize (F.cutoff j) (F.length j i) Y (F.coefficient j i)
        (fun n => F.twist j i n*cubicSymbol p n) (F.factor_spec j i)
        (F.length_ge_one j i) (short_length_le_scale hY₁ hδ.le (hshort i)) hYT
      intro n hn
      rw [norm_mul]
      exact (mul_le_mul (F.twist_bound j i n hn) (norm_cubicSymbol_le_one (hS p hp).1 n)
        (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  exact huniform x hx ((le_max_left _ _).trans hY)

/-- The all-short balanced exceptional configuration has the same uniform
saving, using only the published additive large sieve as analytic input. -/
theorem all_short_mixed_moment (hHuxley : HuxleyAdditiveLargeSieve)
    {δ C : ℝ} (hδ : 0 < δ) (hC : 0 < C) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ, ∀ (F : ShortFactorFamily ι) (j : ℕ)
      (Y : ℝ) (S : Finset (Eisenstein × Eisenstein)), Y₀ ≤ Y →
      (∀ i, F.length j i ≤ Y^(1-δ)) →
      (Y/C ≤ ∏ i, F.length j i) → (∏ i, F.length j i) ≤ C*Y →
      (∀ p ∈ S, PrimarySquarefreePair p ∧ norm p.1 ≤ Y^(1/3:ℝ) ∧
        norm p.2 ≤ Y^(1/3:ℝ)) →
      (∑ p ∈ S, ‖∏ i, F.mixedValue j i p‖^2) ≤ Y^(7/3-ε) := by
  obtain ⟨ε,hε,T₀,huniform⟩ := mixed_short_uniform_power (ι := ι) hHuxley
    (H := 2) (D := 2) hδ (by norm_num) (by norm_num) hC
  obtain ⟨T,hT,hsize⟩ := shortFactorPolynomial_uniform_quadratic_size
  refine ⟨ε,hε,max T₀ (max T 324),?_⟩
  intro F j Y S hY hshort hlo hhi hS
  have hYT : T ≤ Y := (le_max_left T 324).trans ((le_max_right _ _).trans hY)
  have hY₁ : 1 ≤ Y := hT.trans hYT
  have hY₃₂₄ : 324 ≤ Y := (le_max_right T 324).trans ((le_max_right _ _).trans hY)
  let x : ShortMomentInstance ι (Eisenstein × Eisenstein) := ⟨Y,F.comp (fun _ => j),S⟩
  have hx : mixedInstanceAdmissible δ 2 2 C x := by
    refine ⟨hshort,⟨hlo,hhi⟩,hS,?_,?_⟩
    · simpa only [Real.rpow_two] using balanced_rows_card_quadratic S hY₃₂₄ hS
    · intro p hp i
      change ‖F.mixedValue j i p‖ ≤ Y^(2:ℝ)
      rw [Real.rpow_two]
      apply hsize (F.cutoff j) (F.length j i) Y (F.coefficient j i)
        (fun n => F.twist j i n*mixedCubic p.1 p.2 n) (F.factor_spec j i)
        (F.length_ge_one j i) (short_length_le_scale hY₁ hδ.le (hshort i)) hYT
      intro n hn
      rw [norm_mul]
      exact (mul_le_mul (F.twist_bound j i n hn)
        (norm_mixedCubic_le_one (hS p hp).1.1 (hS p hp).1.2.1 n)
        (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  exact huniform x hx ((le_max_left _ _).trans hY)

/-- Any larger first-configuration moment forces a factor of almost full
length. This is the finite alternative used in the dominant-factor case. -/
theorem large_cubic_moment_has_long_factor {δ C : ℝ} (hδ : 0 < δ) (hC : 0 < C) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ, ∀ (F : ShortFactorFamily ι) (j : ℕ)
      (Y : ℝ) (S : Finset Eisenstein), Y₀ ≤ Y →
      (Y/C ≤ ∏ i, F.length j i) → (∏ i, F.length j i) ≤ C*Y →
      (∀ p ∈ S, gramDyad Y p) →
      Y^(7/3-ε) < (∑ p ∈ S, ‖∏ i, F.cubicValue j i p‖^2) →
      ∃ i, Y^(1-δ) < F.length j i := by
  obtain ⟨ε,hε,Y₀,hbound⟩ := all_short_cubic_moment (ι := ι) hδ hC
  refine ⟨ε,hε,Y₀,?_⟩
  intro F j Y S hY hlo hhi hS hlarge
  by_contra h
  push Not at h
  exact not_lt_of_ge (hbound F j Y S hY h hlo hhi hS) hlarge

/-- The analogous finite dominant-factor alternative for balanced rows. -/
theorem large_mixed_moment_has_long_factor (hHuxley : HuxleyAdditiveLargeSieve)
    {δ C : ℝ} (hδ : 0 < δ) (hC : 0 < C) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ, ∀ (F : ShortFactorFamily ι) (j : ℕ)
      (Y : ℝ) (S : Finset (Eisenstein × Eisenstein)), Y₀ ≤ Y →
      (Y/C ≤ ∏ i, F.length j i) → (∏ i, F.length j i) ≤ C*Y →
      (∀ p ∈ S, PrimarySquarefreePair p ∧ norm p.1 ≤ Y^(1/3:ℝ) ∧
        norm p.2 ≤ Y^(1/3:ℝ)) →
      Y^(7/3-ε) < (∑ p ∈ S, ‖∏ i, F.mixedValue j i p‖^2) →
      ∃ i, Y^(1-δ) < F.length j i := by
  obtain ⟨ε,hε,Y₀,hbound⟩ := all_short_mixed_moment (ι := ι) hHuxley hδ hC
  refine ⟨ε,hε,Y₀,?_⟩
  intro F j Y S hY hlo hhi hS hlarge
  by_contra h
  push Not at h
  exact not_lt_of_ge (hbound F j Y S hY h hlo hhi hS) hlarge

end CubicFirstMoment

end

end OAI
