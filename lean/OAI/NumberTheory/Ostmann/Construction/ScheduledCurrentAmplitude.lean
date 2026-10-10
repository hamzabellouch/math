import OAI.NumberTheory.Ostmann.Construction.ScheduledInputPhase
import OAI.NumberTheory.Ostmann.Construction.OriginalDirectedTransfer

namespace OAI

/-! # The current scheduled amplitude under its original prime priors -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def sampledScheduledPhase {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I) (n r : ℕ)
    (e : Fin r ≃ CurrentPivotConstituent role n) (t : FrequencyTree ℤ n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (x : Fin r → P)
    (L : CopyScheduleH role n → ℕ) (U : CopyScheduleY role n → ℕ)
    [∀ h, Fact (L h).Prime] [∀ y, Fact (U y).Prime]
    (center : ∀ p : ℕ, ZMod p) : ℂ := by
  letI : ∀ i, Fact (x i : ℕ).Prime := fun i => ⟨hP _ (x i).property⟩
  letI := scheduledInputPrimeFact role n r e (fun i => (x i : ℕ)) L U
  exact scheduledPrimePhase role χ initialCompleteGraph pivot (initialRegularUnary χ κ) n t
    (scheduledInputLabels role n r e (fun i => (x i : ℕ)) L U) center

theorem sampledScheduledPhase_factor {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I) (hpivot : ∀ k, role (pivot k) = .pivot k)
    (n r : ℕ) (e : Fin r ≃ CurrentPivotConstituent role n) (t : FrequencyTree ℤ n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (x : Fin r → P) (hx : Function.Injective x)
    (L : CopyScheduleH role n → ℕ) (U : CopyScheduleY role n → ℕ)
    [∀ h, Fact (L h).Prime] [∀ y, Fact (U y).Prime]
    (center : ∀ p : ℕ, ZMod p)
    (hLU : Pairwise (fun i j => (Sum.elim L U i).Coprime (Sum.elim L U j)))
    (hM : (∏ i, (x i : ℕ)).Coprime ((∏ h, L h) * ∏ y, U y))
    (hfreq : ∀ i, ∀ s ∈ allFrequencyList n t, (s : ZMod (x i : ℕ)) ≠ 0) :
    sampledScheduledPhase role χ κ pivot n r e t P hP x L U center =
      primeTupleResidueRow P hP (fun i => χ (e i).val)
        (fun i p => κ (e i).val p) center (∏ y, U y) (fun _ => 1) x
        (primeTuplePivotKey P hP x (∏ h, L h) (frequencyRoot n t)) *
      retainedPrimePhase L U center (fun h => χ (copyScheduleOrigin n h.val))
        (fun y => χ (copyScheduleOrigin n y.val)) (scheduledRetainedGraph role initialCompleteGraph pivot n)
        (fun h => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ) n t h.val (L h))
        (fun y => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ) n t y.val (U y))
        (∏ i, (x i : ℕ)) (frequencyRoot n t) := by
  let : ∀ i, Fact (x i : ℕ).Prime := fun i => ⟨hP _ (x i).property⟩
  let := scheduledInputPrimeFact role n r e (fun i => (x i : ℕ)) L U
  have hcp : Pairwise (fun i j => (x i : ℕ).Coprime (x j : ℕ)) := by
    intro i j hij
    apply (hP _ (x i).property).coprime_iff_not_dvd.mpr
    intro hd
    have he : (x i : ℕ) = (x j : ℕ) :=
      ((Nat.dvd_prime (hP _ (x j).property)).mp hd).resolve_left (hP _ (x i).property).ne_one
    exact hij (hx (Subtype.ext he))
  have h := scheduledInputPhase_factor role χ κ pivot hpivot n r e t
    (fun i => (x i : ℕ)) L U center (pivot_retained_pairwise _ L U hcp hLU hM) hfreq
  simpa only [sampledScheduledPhase, primeTupleResidueRow, primeTuplePivotKey] using h

noncomputable def scheduledCurrentAmplitude {I A Z : Type*}
    [Fintype I] [Fintype A] [Fintype Z]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I) (n r : ℕ)
    (e : Fin r ≃ CurrentPivotConstituent role n) (hist : A → FrequencyTree ℤ n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : Fin r → Finset ℕ) (S : Finset (Fin r → P))
    (L : A → CopyScheduleH role n → ℕ) (U : Z → CopyScheduleY role n → ℕ)
    [∀ a h, Fact (L a h).Prime] [∀ z y, Fact (U z y).Prime]
    (center : ∀ p : ℕ, ZMod p) (W : Z → ℕ → A → ℂ) (μ : Z → ℝ) : ℂ :=
  ∑ z, (μ z : ℂ) * ∑ x ∈ S, (productPrior (fun i => primeSubsetPrior P (Q i)) x : ℂ) *
    ∑ a, W z (∏ i, (x i : ℕ)) a *
      sampledScheduledPhase role χ κ pivot n r e (hist a) P hP x (L a) (U z) center

/-- This equality uses the actual phase and original prime prior on the left,
so the following arithmetic transfer does not assume a recurrence for it. -/
theorem scheduledCurrentAmplitude_eq_grouped {I A Z : Type*}
    [Fintype I] [Fintype A] [Fintype Z]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I) (hpivot : ∀ k, role (pivot k) = .pivot k)
    (n r : ℕ) (e : Fin r ≃ CurrentPivotConstituent role n) (hist : A → FrequencyTree ℤ n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : Fin r → Finset ℕ) (S : Finset (Fin r → P))
    (hS : ∀ x ∈ S, Function.Injective x)
    (L : A → CopyScheduleH role n → ℕ) (U : Z → CopyScheduleY role n → ℕ)
    [∀ a h, Fact (L a h).Prime] [∀ z y, Fact (U z y).Prime]
    (center : ∀ p : ℕ, ZMod p) (W : Z → ℕ → A → ℂ) (μ : Z → ℝ)
    (hsupport : ∀ z x, x ∈ S → ∀ a, W z (∏ i, (x i : ℕ)) a ≠ 0 →
      Pairwise (fun i j => (Sum.elim (L a) (U z) i).Coprime (Sum.elim (L a) (U z) j)) ∧
      (∏ i, (x i : ℕ)).Coprime ((∏ h, L a h) * ∏ y, U z y) ∧
      ∀ i, ∀ s ∈ allFrequencyList n (hist a), (s : ZMod (x i : ℕ)) ≠ 0) :
    scheduledCurrentAmplitude role χ κ pivot n r e hist P hP Q S L U center W μ =
    groupedDirectedAmplitude P hP Q S (fun i => χ (e i).val)
      (fun i p => κ (e i).val p) (fun _ => 1) L U center
      (fun h => χ (copyScheduleOrigin n h.val)) (fun y => χ (copyScheduleOrigin n y.val))
      (scheduledRetainedGraph role initialCompleteGraph pivot n)
      (fun _z a h => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
        n (hist a) h.val (L a h))
      (fun z a y => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
        n (hist a) y.val (U z y)) (fun a => frequencyRoot n (hist a)) W μ := by
  unfold scheduledCurrentAmplitude groupedDirectedAmplitude
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  by_cases hW : W z (∏ i, (x i : ℕ)) a = 0
  · simp only [hW, retainedWeightedCoefficient, zero_mul, mul_zero]
  obtain ⟨hc, hM, hf⟩ := hsupport z x hx a hW
  rw [sampledScheduledPhase_factor role χ κ pivot hpivot n r e (hist a) P hP x
    (hS x hx) (L a) (U z) center hc hM hf]
  unfold retainedWeightedCoefficient
  ring

end Ostmann

end OAI
