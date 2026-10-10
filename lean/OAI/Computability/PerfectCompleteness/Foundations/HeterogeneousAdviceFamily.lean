import OAI.Computability.PerfectCompleteness.Foundations.GoodAdviceEventsLemmas

namespace OAI

section

namespace PerfectCompleteness.HeterogeneousAdviceFamily

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters (F2)
open UniqueGamesTheorem.Fourier.MatrixLevelBridge
open UniqueGamesTheorem.Appendix.RankLevelFilter
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness.ManyGoodRows

attribute [local instance] linearMapFintype

variable {P : Type*} [Fintype P] {E F Y : P → Type*}
  [∀ p, AddCommGroup (E p)] [∀ p, Module F2 (E p)]
  [∀ p, FiniteDimensional F2 (E p)] [∀ p, Fintype (E p)]
  [∀ p, AddCommGroup (F p)] [∀ p, Module F2 (F p)]
  [∀ p, FiniteDimensional F2 (F p)] [∀ p, Fintype (F p)]
  [∀ p, Fintype (Y p)]

abbrev Sample (r : Nat) := Σ p : P, RowMap (F p) r × (E p →ₗ[F2] F p)

def law (μ : FiniteDistribution P) (r : Nat) :
    FiniteDistribution (Sample (E := E) (F := F) r) :=
  CompletionSoundness.sigmaLaw μ (fun p => GoodAdviceEvents.law (E p) (F p) r)

def J (f : (p : P) → (E p →ₗ[F2] F p) → Option (Y p))
    (r : Nat) (ρ : ℝ) (sample : Sample (E := E) (F := F) r) : Bool :=
  GoodAdviceEvents.J (f sample.1) r ρ sample.2

def I (f : (p : P) → (E p →ₗ[F2] F p) → Option (Y p))
    (r : Nat) (ρ : ℝ) (sample : Sample (E := E) (F := F) r) : Bool :=
  GoodAdviceEvents.I (f sample.1) r ρ sample.2

omit [∀ p, FiniteDimensional F2 (E p)] [∀ p, FiniteDimensional F2 (F p)]
  [∀ p, Fintype (Y p)] in
theorem J_probability_eq_mean (μ : FiniteDistribution P)
    (f : (p : P) → (E p →ₗ[F2] F p) → Option (Y p)) (r : Nat) (ρ : ℝ) :
    (law (E := E) (F := F) μ r).probability (J f r ρ) =
      μ.expectation (fun p =>
        (GoodAdviceEvents.law (E p) (F p) r).probability (GoodAdviceEvents.J (f p) r ρ)) :=
  CompletionSoundness.sigmaLaw_probability μ
    (fun p => GoodAdviceEvents.law (E p) (F p) r) (J f r ρ)

omit [∀ p, FiniteDimensional F2 (E p)] [∀ p, FiniteDimensional F2 (F p)]
  [∀ p, Fintype (Y p)] in
theorem I_probability_eq_mean (μ : FiniteDistribution P)
    (f : (p : P) → (E p →ₗ[F2] F p) → Option (Y p)) (r : Nat) (ρ : ℝ) :
    (law (E := E) (F := F) μ r).probability (I f r ρ) =
      μ.expectation (fun p =>
        (GoodAdviceEvents.law (E p) (F p) r).probability (GoodAdviceEvents.I (f p) r ρ)) :=
  CompletionSoundness.sigmaLaw_probability μ
    (fun p => GoodAdviceEvents.law (E p) (F p) r) (I f r ρ)

private theorem div_pow_le {a : ℝ} (ha : 0 ≤ a) {i j : Nat} (hij : i ≤ j) :
    a / (2 : ℝ) ^ j ≤ a / (2 : ℝ) ^ i := by
  simpa only [one_div, div_eq_mul_inv, one_mul] using
    mul_le_mul_of_nonneg_left
      (one_div_pow_le_one_div_pow_of_le (by norm_num : (1 : ℝ) ≤ 2) hij) ha

omit [∀ p, Fintype (Y p)] in
theorem J_probability_ge_mean_advice (μ : FiniteDistribution P)
    (f : (p : P) → (E p →ₗ[F2] F p) → Option (Y p)) (r ℓ : Nat)
    (hdim : ∀ p, Module.finrank F2 (F p) ≤ ℓ) (ρ : ℝ) :
    μ.expectation (fun p => adviceMass (f p) r ρ) / (2 : ℝ) ^ (r * ℓ) ≤
      (law (E := E) (F := F) μ r).probability (J f r ρ) := by
  have hpoint (p : P) :
      adviceMass (f p) r ρ / (2 : ℝ) ^ (r * ℓ) ≤
        (GoodAdviceEvents.law (E p) (F p) r).probability (GoodAdviceEvents.J (f p) r ρ) :=
    (div_pow_le (FamilyGoodRows.adviceMass_nonneg (f p) r ρ)
      (Nat.mul_le_mul_left r (hdim p))).trans (GoodAdviceEvents.J_probability_ge (f p) r ρ)
  rw [J_probability_eq_mean]
  simp only [FiniteDistribution.expectation, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p _
  simpa only [div_eq_mul_inv, mul_assoc] using
    mul_le_mul_of_nonneg_left (hpoint p) (μ.nonnegative p)

omit [∀ p, FiniteDimensional F2 (E p)] [∀ p, FiniteDimensional F2 (F p)]
  [∀ p, Fintype (Y p)] in
theorem I_probability_ge (μ : FiniteDistribution P)
    (f : (p : P) → (E p →ₗ[F2] F p) → Option (Y p)) (r : Nat) (ρ : ℝ) :
    ρ * (law (E := E) (F := F) μ r).probability (J f r ρ) ≤
      (law (E := E) (F := F) μ r).probability (I f r ρ) := by
  rw [J_probability_eq_mean, I_probability_eq_mean]
  simp only [FiniteDistribution.expectation, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p _
  simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left
    (GoodAdviceEvents.I_probability_ge (f p) r ρ) (μ.nonnegative p)

variable [∀ p, Nontrivial (F p)]

theorem mean_adviceMass_ge (μ : FiniteDistribution P)
    (f : (p : P) → (E p →ₗ[F2] F p) → Option (Y p)) (r ℓ : Nat)
    (hdim : ∀ p, Module.finrank F2 (F p) ≤ ℓ)
    (ρ η : ℝ) (hη : 0 < η) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η / 2)
    (hmean : 2 * η ≤ μ.expectation (fun p => PartialTableInverse.nonzeroAgreement (f p))) :
    (η ^ 2 / 4) / (2 : ℝ) ^ (r * ℓ) ≤
      μ.expectation (fun p => adviceMass (f p) r ρ) := by
  let c : ℝ := (η / 4) / (2 : ℝ) ^ (r * ℓ)
  have hc : 0 ≤ c :=
    div_nonneg (div_nonneg hη.le (by norm_num : (0 : ℝ) ≤ 4)) (by positivity)
  have hmass : η ≤ μ.probability
      (fun p => decide (η ≤ PartialTableInverse.nonzeroAgreement (f p))) :=
    FamilyGoodRows.threshold_probability_ge μ
      (fun p => PartialTableInverse.nonzeroAgreement (f p)) η hη.le
      (fun p => FamilyGoodRows.nonzeroAgreement_le_one (f p)) hmean
  have hweighted :
      μ.probability (fun p => decide (η ≤ PartialTableInverse.nonzeroAgreement (f p))) * c ≤
        μ.expectation (fun p => adviceMass (f p) r ρ) := by
    apply FamilyGoodRows.probability_mul_le_expectation μ
      (fun p => η ≤ PartialTableInverse.nonzeroAgreement (f p))
      (fun p => adviceMass (f p) r ρ) c
    · intro p
      exact FamilyGoodRows.adviceMass_nonneg (f p) r ρ
    · intro p hp
      exact (div_pow_le (div_nonneg hη.le (by norm_num : (0 : ℝ) ≤ 4))
        (Nat.mul_le_mul_left r (hdim p))).trans
          (ManyGoodRows.adviceMass_ge r ρ η hρ hρ1 hconstants (f p) hp)
  calc
    (η ^ 2 / 4) / (2 : ℝ) ^ (r * ℓ) = η * c := by
      dsimp [c]
      ring
    _ ≤ μ.probability (fun p => decide (η ≤ PartialTableInverse.nonzeroAgreement (f p))) * c :=
      mul_le_mul_of_nonneg_right hmass hc
    _ ≤ μ.expectation (fun p => adviceMass (f p) r ρ) := hweighted

theorem J_probability_ge (μ : FiniteDistribution P)
    (f : (p : P) → (E p →ₗ[F2] F p) → Option (Y p)) (r ℓ : Nat)
    (hdim : ∀ p, Module.finrank F2 (F p) ≤ ℓ)
    (ρ η : ℝ) (hη : 0 < η) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η / 2)
    (hmean : 2 * η ≤ μ.expectation (fun p => PartialTableInverse.nonzeroAgreement (f p))) :
    (η ^ 2 / 4) / ((2 : ℝ) ^ (r * ℓ)) ^ 2 ≤
      (law (E := E) (F := F) μ r).probability (J f r ρ) := by
  calc
    _ = ((η ^ 2 / 4) / (2 : ℝ) ^ (r * ℓ)) / (2 : ℝ) ^ (r * ℓ) := by ring
    _ ≤ μ.expectation (fun p => adviceMass (f p) r ρ) / (2 : ℝ) ^ (r * ℓ) :=
      div_le_div_of_nonneg_right
        (mean_adviceMass_ge μ f r ℓ hdim ρ η hη hρ hρ1 hconstants hmean) (by positivity)
    _ ≤ _ := J_probability_ge_mean_advice μ f r ℓ hdim ρ

end
end PerfectCompleteness.HeterogeneousAdviceFamily

end

end OAI
