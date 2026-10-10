import OAI.NumberTheory.Ostmann.Construction.ScheduledCurrentAmplitude
import OAI.NumberTheory.Ostmann.Construction.ScheduledCopiedAmplitude

namespace OAI

/-! # The arithmetic transfer of the actual original-prior scheduled amplitude -/

namespace Ostmann

open scoped BigOperators Classical

/-- One genuine step of the schedule, including the original harmonic loss,
actual diagonal, all inherited support, and the next copied amplitude. -/
theorem scheduled_arithmetic_transfer {I A Z : Type*}
    [Fintype I] [Fintype A] [Fintype Z]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I) (hpivot : ∀ k, role (pivot k) = .pivot k)
    (n r : ℕ) (e : Fin r ≃ CurrentPivotConstituent role n) (hist : A → FrequencyTree ℤ n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hκ : ∀ i p, p ∈ P → ‖κ i p‖ ≤ 1)
    (Q : Fin r → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQ : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹) ≠ 0)
    (S : Finset (Fin r → P)) (hS : ∀ x ∈ S, Function.Injective x)
    (T : Finset ℕ) (hT : ∀ M ∈ T, 0 < M) (hST : ∀ x ∈ S, (∏ i, (x i : ℕ)) ∈ T)
    (L : A → CopyScheduleH role n → ℕ) (U : Z → CopyScheduleY role n → ℕ)
    [∀ a h, Fact (L a h).Prime] [∀ z y, Fact (U z y).Prime]
    (center : ∀ p : ℕ, ZMod p) (W : Z → ℕ → A → ℂ) (μ : Z → ℝ)
    (hμ : ∀ z, 0 ≤ μ z) (hμsum : ∑ z, μ z ≤ 1)
    (B K V : ℕ)
    (hsupport : ∀ z M, M ∈ T → ∀ a, W z M a ≠ 0 →
      Pairwise (fun i j => (Sum.elim (L a) (U z) i).Coprime (Sum.elim (L a) (U z) j)) ∧
      M.Coprime ((∏ h, L a h) * ∏ y, U z y) ∧
      (frequencyRoot n (hist a)).natAbs ≤ B ∧ (∏ h, L a h) ≤ K)
    (hfreq : ∀ z x, x ∈ S → ∀ a, W z (∏ i, (x i : ℕ)) a ≠ 0 →
      ∀ i, ∀ s ∈ allFrequencyList n (hist a), (s : ZMod (x i : ℕ)) ≠ 0)
    (hscale : ∀ M ∈ T, 2 * B * K ≤ V * M)
    (hlargeL : ∀ a h, V < L a h) (hlargeU : ∀ z y, V < U z y)
    (d : ℝ) (hcost : ((r.factorial : ℝ) * ∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) ≤ Real.exp d) :
    Real.exp (-d) *
      ‖scheduledCurrentAmplitude role χ κ pivot n r e hist P hP Q S L U center W μ‖ ^ 2 ≤
      (∑ z, μ z * ∑ M ∈ T,
        (pivotDiagonal (fun a => ∏ h, L a h) (fun a => frequencyRoot n (hist a))
          (retainedWeightedCoefficient L (U z) center
            (fun h => χ (copyScheduleOrigin n h.val)) (fun y => χ (copyScheduleOrigin n y.val))
            (scheduledRetainedGraph role initialCompleteGraph pivot n)
            (fun a h => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
              n (hist a) h.val (L a h))
            (fun a y => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
              n (hist a) y.val (U z y))
            (fun a => frequencyRoot n (hist a)) (W z) M)).re) +
      ‖∑ z, (μ z : ℂ) * scheduledNextAmplitude role χ initialCompleteGraph pivot
        (initialRegularUnary χ κ) n hist L (U z) center (W z) T V‖ := by
  have hcurrent := scheduledCurrentAmplitude_eq_grouped role χ κ pivot hpivot n r e hist
    P hP Q S hS L U center W μ (by
      intro z x hx a ha
      have hs := hsupport z _ (hST x hx) a ha
      exact ⟨hs.1, hs.2.1, hfreq z x hx a ha⟩)
  rw [hcurrent]
  have ht := original_directed_transfer P hP Q hQP hQ S hS T hT hST
    (fun i => χ (e i).val) (fun i p => κ (e i).val p)
    (fun i p => hκ (e i).val p p.property) (fun _ => 1) L U center
    (fun h => χ (copyScheduleOrigin n h.val)) (fun y => χ (copyScheduleOrigin n y.val))
    (scheduledRetainedGraph role initialCompleteGraph pivot n)
    (fun z a h => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
      n (hist a) h.val (L a h))
    (fun z a y => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
      n (hist a) y.val (U z y)) (fun a => frequencyRoot n (hist a)) W μ hμ hμsum
    B K V hsupport hscale hlargeL hlargeU
    (fun y => scheduledRetainedGraph_diagonal role pivot n (some (.inr y))) d hcost
  simpa only [copiedWeightedAmplitude_eq_scheduledNextAmplitude] using ht

end Ostmann

end OAI
