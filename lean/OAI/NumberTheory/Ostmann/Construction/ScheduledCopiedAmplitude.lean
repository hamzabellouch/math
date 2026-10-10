import OAI.NumberTheory.Ostmann.Construction.ScheduledPrimePhase
import OAI.NumberTheory.Ostmann.Arithmetic.ReconstructedPhaseWeight

namespace OAI

/-! # The reconstructed off-diagonal on the actual next schedule -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

/-- The two old frequency histories become the two children of the new root.
Only the forced positive integer pivot is inserted into the inherited weights. -/
noncomputable def scheduledNextAmplitude {I A : Type*} [Fintype I] [Fintype A]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (g : I → I → ℤ) (pivot : ℕ → I) (initial : I → ℤ → ℕ → ℂ)
    (n : ℕ) (hist : A → FrequencyTree ℤ n)
    (L : A → CopyScheduleH role n → ℕ) (U : CopyScheduleY role n → ℕ)
    [∀ a h, Fact (L a h).Prime] [∀ y, Fact (U y).Prime]
    (center : ∀ p : ℕ, ZMod p) (W : ℕ → A → ℂ) (T : Finset ℕ) (V : ℕ) : ℂ :=
  ∑ s ∈ transferFrequencyRange V, ∑ a, ∑ a',
    let N := frequencyRoot n (hist a) * (∏ h, L a' h) -
      frequencyRoot n (hist a') * (∏ h, L a h)
    let M := reconstructedPivot N s
    if validTransferredPivot T N s then
      letI := transferredPrimeFact (L a) (L a') U
      W M a * conj (W M a') *
        scheduledPrimePhase role χ g pivot initial (n + 1) (s, hist a, hist a')
          (fun j => transferredLabels (L a) (L a') U (copyScheduleSurvivorEquiv role n j)) center
    else 0

theorem copiedWeightedAmplitude_eq_scheduledNextAmplitude {I A : Type*}
    [Fintype I] [Fintype A]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (g : I → I → ℤ) (pivot : ℕ → I) (initial : I → ℤ → ℕ → ℂ)
    (n : ℕ) (hist : A → FrequencyTree ℤ n)
    (L : A → CopyScheduleH role n → ℕ) (U : CopyScheduleY role n → ℕ)
    [∀ a h, Fact (L a h).Prime] [∀ y, Fact (U y).Prime]
    (center : ∀ p : ℕ, ZMod p) (W : ℕ → A → ℂ) (T : Finset ℕ) (V : ℕ) :
    copiedWeightedAmplitude L U center
      (fun h => χ (copyScheduleOrigin n h.val)) (fun y => χ (copyScheduleOrigin n y.val))
      (scheduledRetainedGraph role g pivot n)
      (fun a h => copyScheduleUnary χ g pivot initial n (hist a) h.val (L a h))
      (fun a y => copyScheduleUnary χ g pivot initial n (hist a) y.val (U y))
      (fun a => frequencyRoot n (hist a)) W T V =
    scheduledNextAmplitude role χ g pivot initial n hist L U center W T V := by
  unfold copiedWeightedAmplitude scheduledNextAmplitude
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro a' _
  dsimp only
  split_ifs
  · rw [copiedDirectedPhase_scheduled role χ g pivot initial n (s, hist a, hist a')]
  · rfl

/-- The equality carries every inherited weight and every integer-pivot test.
Its support assumptions are only the original branch assumptions. -/
theorem reconstructedOffDiagonal_eq_scheduledNextAmplitude {I A : Type*}
    [Fintype I] [Fintype A]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (g : I → I → ℤ) (pivot : ℕ → I) (initial : I → ℤ → ℕ → ℂ)
    (n : ℕ) (hist : A → FrequencyTree ℤ n)
    (L : A → CopyScheduleH role n → ℕ) (U : CopyScheduleY role n → ℕ)
    [∀ a h, Fact (L a h).Prime] [∀ y, Fact (U y).Prime]
    (center : ∀ p : ℕ, ZMod p) (W : ℕ → A → ℂ) (T : Finset ℕ) (B K V : ℕ)
    (hT : ∀ M ∈ T, 0 < M)
    (hsupport : ∀ M ∈ T, ∀ a, W M a ≠ 0 →
      Pairwise (fun i j => (Sum.elim (L a) U i).Coprime (Sum.elim (L a) U j)) ∧
      M.Coprime ((∏ h, L a h) * ∏ y, U y) ∧
      (frequencyRoot n (hist a)).natAbs ≤ B ∧ (∏ h, L a h) ≤ K)
    (hscale : ∀ M ∈ T, 2 * B * K ≤ V * M)
    (hlargeL : ∀ a h, V < L a h) (hlargeU : ∀ y, V < U y)
    (hg : ∀ y, g y y = 0) :
    reconstructedOffDiagonal T V (fun a => ∏ h, L a h) (fun a => frequencyRoot n (hist a))
      (retainedWeightedCoefficient L U center
        (fun h => χ (copyScheduleOrigin n h.val)) (fun y => χ (copyScheduleOrigin n y.val))
        (scheduledRetainedGraph role g pivot n)
        (fun a h => copyScheduleUnary χ g pivot initial n (hist a) h.val (L a h))
        (fun a y => copyScheduleUnary χ g pivot initial n (hist a) y.val (U y))
        (fun a => frequencyRoot n (hist a)) W) =
    scheduledNextAmplitude role χ g pivot initial n hist L U center W T V := by
  rw [reconstructedOffDiagonal_eq_copiedWeightedAmplitude L U center
    (fun h => χ (copyScheduleOrigin n h.val)) (fun y => χ (copyScheduleOrigin n y.val))
    (scheduledRetainedGraph role g pivot n)
    (fun a h => copyScheduleUnary χ g pivot initial n (hist a) h.val (L a h))
    (fun a y => copyScheduleUnary χ g pivot initial n (hist a) y.val (U y))
    (fun a => frequencyRoot n (hist a)) W T B K V hT hsupport hscale hlargeL hlargeU]
  · exact copiedWeightedAmplitude_eq_scheduledNextAmplitude role χ g pivot initial n hist L U center W T V
  · intro y
    exact copyScheduleGraph_diagonal g pivot hg n y.val

end Ostmann

end OAI
