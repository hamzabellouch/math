import OAI.NumberTheory.Ostmann.QuadraticSieveNormSupport

namespace OAI

namespace Ostmann.QuadraticSieve

noncomputable def weightedNumeratorEnergy (W : Finset ℤ) (S : Finset ℕ)
    (ω : ℤ → ℝ) (a : ℕ → ℂ) : ℝ :=
  ∑ m ∈ W, ω m * ‖∑ n ∈ S, a n * (jacobiSym m n : ℂ)‖ ^ 2

theorem numerator_row_energy_le (m : ℤ) (S : Finset ℕ) (a : ℕ → ℂ) :
    ‖∑ n ∈ S, a n * (jacobiSym m n : ℂ)‖ ^ 2 ≤
      (S.card : ℝ) * coefficientEnergy S a := by
  have hnorm : ‖∑ n ∈ S, a n * (jacobiSym m n : ℂ)‖ ≤ ∑ n ∈ S, ‖a n‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro n hn
    rcases jacobiSym.trichotomy m n with h | h | h <;> simp [h]
  apply (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
  simpa [coefficientEnergy, mul_comm] using
    Finset.sum_mul_sq_le_sq_mul_sq S (fun n => ‖a n‖) (fun _ => (1 : ℝ))

theorem weightedNumeratorEnergy_le_card_mul (W : Finset ℤ) (S : Finset ℕ)
    (ω : ℤ → ℝ) (a : ℕ → ℂ) :
    weightedNumeratorEnergy W S ω a ≤
      (∑ m ∈ W, |ω m|) * (S.card : ℝ) * coefficientEnergy S a := by
  calc
    _ ≤ ∑ m ∈ W, |ω m| * ((S.card : ℝ) * coefficientEnergy S a) := by
      apply Finset.sum_le_sum
      intro m hm
      exact mul_le_mul (le_abs_self _) (numerator_row_energy_le m S a)
        (sq_nonneg _) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

lemma weightedNumeratorEnergy_nonneg (W : Finset ℤ) (S : Finset ℕ)
    (ω : ℤ → ℝ) (hω : ∀ m ∈ W, 0 ≤ ω m) (a : ℕ → ℂ) :
    0 ≤ weightedNumeratorEnergy W S ω a :=
  Finset.sum_nonneg (fun m hm => mul_nonneg (hω m hm) (sq_nonneg _))

noncomputable def weightedNumeratorNorm (W : Finset ℤ) (S : Finset ℕ) (ω : ℤ → ℝ) : ℝ :=
  sSup (Set.range (fun a : ℕ → ℂ => weightedNumeratorEnergy W S ω a / coefficientEnergy S a))

lemma weighted_numerator_ratios_bddAbove (W : Finset ℤ) (S : Finset ℕ) (ω : ℤ → ℝ) :
    BddAbove (Set.range (fun a : ℕ → ℂ => weightedNumeratorEnergy W S ω a / coefficientEnergy S a)) := by
  refine ⟨(∑ m ∈ W, |ω m|) * (S.card : ℝ), ?_⟩
  rintro x ⟨a, rfl⟩
  by_cases h : coefficientEnergy S a = 0
  · simp only [h, div_zero]
    positivity
  · have hp : 0 < coefficientEnergy S a :=
      lt_of_le_of_ne (coefficientEnergy_nonneg S a) (Ne.symm h)
    exact (div_le_iff₀ hp).mpr (weightedNumeratorEnergy_le_card_mul W S ω a)

theorem weightedNumeratorNorm_nonneg (W : Finset ℤ) (S : Finset ℕ) (ω : ℤ → ℝ) :
    0 ≤ weightedNumeratorNorm W S ω := by
  apply le_csSup (weighted_numerator_ratios_bddAbove W S ω)
  refine ⟨fun _ => 0, ?_⟩
  simp [coefficientEnergy, weightedNumeratorEnergy]

theorem weightedNumeratorEnergy_le_norm (W : Finset ℤ) (S : Finset ℕ)
    (ω : ℤ → ℝ) (a : ℕ → ℂ) :
    weightedNumeratorEnergy W S ω a ≤ weightedNumeratorNorm W S ω * coefficientEnergy S a := by
  by_cases h : coefficientEnergy S a = 0
  · simpa only [h, mul_zero] using weightedNumeratorEnergy_le_card_mul W S ω a
  · have hp : 0 < coefficientEnergy S a :=
      lt_of_le_of_ne (coefficientEnergy_nonneg S a) (Ne.symm h)
    exact (div_le_iff₀ hp).mp (le_csSup (weighted_numerator_ratios_bddAbove W S ω) ⟨a, rfl⟩)

theorem weightedNumeratorNorm_le_of_bound (W : Finset ℤ) (S : Finset ℕ)
    (ω : ℤ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ a : ℕ → ℂ, weightedNumeratorEnergy W S ω a ≤ K * coefficientEnergy S a) :
    weightedNumeratorNorm W S ω ≤ K := by
  apply csSup_le (Set.range_nonempty _)
  rintro x ⟨a, rfl⟩
  by_cases he : coefficientEnergy S a = 0
  · simpa only [he, div_zero] using hK
  · have hp : 0 < coefficientEnergy S a :=
      lt_of_le_of_ne (coefficientEnergy_nonneg S a) (Ne.symm he)
    exact (div_le_iff₀ hp).mpr (h a)

theorem weightedNumeratorEnergy_supportCoefficients (W : Finset ℤ) {S T : Finset ℕ}
    (hST : S ⊆ T) (ω : ℤ → ℝ) (a : ℕ → ℂ) :
    weightedNumeratorEnergy W T ω (supportCoefficients S a) = weightedNumeratorEnergy W S ω a := by
  classical
  unfold weightedNumeratorEnergy
  apply Finset.sum_congr rfl
  intro m hm
  congr 2
  apply congrArg norm
  calc
    _ = ∑ n ∈ S, supportCoefficients S a n * (jacobiSym m n : ℂ) := by
      symm
      apply Finset.sum_subset hST
      intro n hn hnot
      simp [hnot]
    _ = _ := Finset.sum_congr rfl (fun n hn => by simp [hn])

theorem weightedNumeratorNorm_mono_columns (W : Finset ℤ) {S T : Finset ℕ}
    (hST : S ⊆ T) (ω : ℤ → ℝ) :
    weightedNumeratorNorm W S ω ≤ weightedNumeratorNorm W T ω := by
  apply weightedNumeratorNorm_le_of_bound W S ω (weightedNumeratorNorm_nonneg W T ω)
  intro a
  simpa only [weightedNumeratorEnergy_supportCoefficients W hST,
    coefficientEnergy_supportCoefficients hST] using
    weightedNumeratorEnergy_le_norm W T ω (supportCoefficients S a)

end Ostmann.QuadraticSieve

end OAI
