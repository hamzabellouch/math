import OAI.NumberTheory.Ostmann.QuadraticSieve

namespace OAI

namespace Ostmann.QuadraticSieve

theorem jacobi_row_energy_le (v : ℕ) (S : Finset ℕ) (a : ℕ → ℂ) :
    ‖∑ s ∈ S, a s * (jacobiSym (s : ℤ) v : ℂ)‖ ^ 2 ≤
      (S.card : ℝ) * coefficientEnergy S a := by
  have hnorm : ‖∑ s ∈ S, a s * (jacobiSym (s : ℤ) v : ℂ)‖ ≤ ∑ s ∈ S, ‖a s‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro s hs
    rcases jacobiSym.trichotomy (s : ℤ) v with h | h | h <;> simp [h]
  apply (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
  simpa [coefficientEnergy, mul_comm] using
    Finset.sum_mul_sq_le_sq_mul_sq S (fun s => ‖a s‖) (fun _ => (1 : ℝ))

theorem jacobiEnergy_le_card_mul (V S : Finset ℕ) (a : ℕ → ℂ) :
    jacobiEnergy V S a ≤ (V.card : ℝ) * (S.card : ℝ) * coefficientEnergy S a := by
  calc
    jacobiEnergy V S a ≤ ∑ v ∈ V, (S.card : ℝ) * coefficientEnergy S a :=
      Finset.sum_le_sum (fun v _ => jacobi_row_energy_le v S a)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

noncomputable def quadraticNorm (V S : Finset ℕ) : ℝ :=
  sSup (Set.range (fun a : ℕ → ℂ => jacobiEnergy V S a / coefficientEnergy S a))

theorem quadratic_ratios_bddAbove (V S : Finset ℕ) :
    BddAbove (Set.range (fun a : ℕ → ℂ => jacobiEnergy V S a / coefficientEnergy S a)) := by
  refine ⟨(V.card : ℝ) * (S.card : ℝ), ?_⟩
  rintro x ⟨a, rfl⟩
  by_cases h : coefficientEnergy S a = 0
  · simp only [h, div_zero]
    positivity
  · have hp : 0 < coefficientEnergy S a := lt_of_le_of_ne (coefficientEnergy_nonneg S a) (Ne.symm h)
    exact (div_le_iff₀ hp).mpr (jacobiEnergy_le_card_mul V S a)

theorem quadraticNorm_nonneg (V S : Finset ℕ) : 0 ≤ quadraticNorm V S := by
  apply le_csSup (quadratic_ratios_bddAbove V S)
  refine ⟨fun _ => 0, ?_⟩
  simp [coefficientEnergy, jacobiEnergy]

theorem jacobiEnergy_le_quadraticNorm (V S : Finset ℕ) (a : ℕ → ℂ) :
    jacobiEnergy V S a ≤ quadraticNorm V S * coefficientEnergy S a := by
  by_cases h : coefficientEnergy S a = 0
  · have he := jacobiEnergy_le_card_mul V S a
    simpa only [h, mul_zero] using he
  · have hp : 0 < coefficientEnergy S a := lt_of_le_of_ne (coefficientEnergy_nonneg S a) (Ne.symm h)
    exact (div_le_iff₀ hp).mp (le_csSup (quadratic_ratios_bddAbove V S) ⟨a, rfl⟩)

theorem quadraticNorm_le_of_bound (V S : Finset ℕ) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ a : ℕ → ℂ, jacobiEnergy V S a ≤ K * coefficientEnergy S a) :
    quadraticNorm V S ≤ K := by
  apply csSup_le (Set.range_nonempty _)
  rintro x ⟨a, rfl⟩
  by_cases he : coefficientEnergy S a = 0
  · simpa only [he, div_zero] using hK
  · have hp : 0 < coefficientEnergy S a :=
      lt_of_le_of_ne (coefficientEnergy_nonneg S a) (Ne.symm he)
    exact (div_le_iff₀ hp).mpr (h a)

theorem quadraticNorm_le_card_mul (V S : Finset ℕ) :
    quadraticNorm V S ≤ (V.card : ℝ) * (S.card : ℝ) :=
  quadraticNorm_le_of_bound V S (by positivity) (jacobiEnergy_le_card_mul V S)

theorem jacobiEnergy_mono_rows {V W : Finset ℕ} (hVW : V ⊆ W) (S : Finset ℕ)
    (a : ℕ → ℂ) : jacobiEnergy V S a ≤ jacobiEnergy W S a :=
  Finset.sum_le_sum_of_subset_of_nonneg hVW (fun _ _ _ => sq_nonneg _)

theorem quadraticNorm_mono_rows {V W : Finset ℕ} (hVW : V ⊆ W) (S : Finset ℕ) :
    quadraticNorm V S ≤ quadraticNorm W S := by
  apply quadraticNorm_le_of_bound V S (quadraticNorm_nonneg W S)
  intro a
  exact (jacobiEnergy_mono_rows hVW S a).trans (jacobiEnergy_le_quadraticNorm W S a)

end Ostmann.QuadraticSieve

end OAI
