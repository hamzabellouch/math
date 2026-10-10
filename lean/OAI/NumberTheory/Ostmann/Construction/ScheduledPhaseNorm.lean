import OAI.NumberTheory.Ostmann.Construction.ConstituentInitialAmplitude

namespace OAI

/-! # Uniform modulus bounds for the literal scheduled prime phase -/

namespace Ostmann
open scoped Classical

theorem initialRegularUnary_norm_le_one {I : Type*}
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p) (κ : I → ℕ → ℂ)
    (hκ : ∀ i p, ‖κ i p‖ ≤ 1) (i : I) (v : ℤ) (p : ℕ) :
    ‖initialRegularUnary χ κ i v p‖ ≤ 1 := by
  unfold initialRegularUnary regularUnary
  rw [norm_mul]
  exact (mul_le_mul (hκ i p) (character_zpow_norm_le_one _ _ _)
    (norm_nonneg _) (by norm_num)).trans (by norm_num)

theorem scheduledPrimePhase_norm_le_one {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (hκ : ∀ i p, ‖κ i p‖ ≤ 1) (pivot : ℕ → I)
    (n : ℕ) (t : FrequencyTree ℤ n) (p : CopyScheduleAtoms role n → ℕ)
    [∀ i, Fact (p i).Prime] (center : ∀ p : ℕ, ZMod p) :
    ‖scheduledPrimePhase role χ initialCompleteGraph pivot (initialRegularUnary χ κ)
      n t p center‖ ≤ 1 := by
  apply directedPrimePhase_norm_le_one
  intro i
  exact copyScheduleUnary_norm_le_one χ initialCompleteGraph pivot
    (initialRegularUnary χ κ) (initialRegularUnary_norm_le_one χ κ hκ) n t i.val (p i)

theorem scheduledSamplePhase_norm_le_one {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (hκ : ∀ i p, ‖κ i p‖ ≤ 1) (pivot : ℕ → I)
    (n : ℕ) (t : FrequencyTree ℤ n) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (q : CopyScheduleAtoms role n → P) (center : ∀ p : ℕ, ZMod p) :
    ‖scheduledSamplePhase role χ κ pivot n t P hP q center‖ ≤ 1 := by
  let : ∀ i, Fact (q i : ℕ).Prime := fun i => ⟨hP _ (q i).property⟩
  exact scheduledPrimePhase_norm_le_one role χ κ hκ pivot n t (fun i => (q i : ℕ)) center

end Ostmann

end OAI
