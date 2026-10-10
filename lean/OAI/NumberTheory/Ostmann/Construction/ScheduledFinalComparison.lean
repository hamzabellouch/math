import OAI.NumberTheory.Ostmann.Construction.ScheduledFullFinalPermutation
import OAI.NumberTheory.Ostmann.Construction.ConstituentEnergyRate
import OAI.NumberTheory.Ostmann.Construction.FinalHistoryCorrelations

namespace OAI

/-! # The final comparison on the actual original prime product law -/

namespace Ostmann
open scoped BigOperators Classical SchwartzMap FourierTransform

noncomputable def scheduledPrimePrior {I A : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (μ : I → A → ℝ)
    (x : CopyScheduleAtoms role n → A) : ℝ :=
  ∏ i, μ (copyScheduleOrigin n i.val) (x i)

theorem scheduledPrimePrior_preserved {I A : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word}) (e : FinalParityReassignments n m)
    (μ : I → A → ℝ) (x : CopyScheduleAtoms role (n + 1) → A) :
    scheduledPrimePrior role (n + 1) μ (scheduledFullSamplePerm role n m word e x) =
      scheduledPrimePrior role (n + 1) μ x :=
  scheduledFullFinalPerm_product_prior role n m word e μ x

theorem scheduledFullSamplePerm_energy {I A : Type*} [Fintype I] [Fintype A]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word}) (e : FinalParityReassignments n m)
    (μ : I → A → ℝ) (F : (CopyScheduleAtoms role (n + 1) → A) → ℂ) :
    (∑ x, scheduledPrimePrior role (n + 1) μ x *
      ‖F (scheduledFullSamplePerm role n m word e x)‖ ^ 2) =
      ∑ x, scheduledPrimePrior role (n + 1) μ x * ‖F x‖ ^ 2 := by
  have h := (scheduledFullSamplePerm (A := A) role n m word e).sum_comp
    (fun x => scheduledPrimePrior role (n + 1) μ x * ‖F x‖ ^ 2)
  simpa only [scheduledPrimePrior_preserved] using h

theorem scheduledPrimePrior_mass {I A : Type*} [Fintype I] [Fintype A]
    (role : I → CopyScheduleRole) (n : ℕ) (μ : I → A → ℝ)
    (hμ : ∀ i, ∑ a, μ i a = 1) :
    (∑ x, scheduledPrimePrior role n μ x) = 1 := by
  simp only [scheduledPrimePrior, ← Fintype.prod_sum, hμ, Finset.prod_const_one]

/-- The diagonal energy is unchanged, and only distinct final pairs require
cancellation. The law is the full original product measure on surviving slots. -/
theorem scheduled_full_final_comparison {I A : Type*} [Fintype I] [Fintype A]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word})
    (μ : I → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a) (hμmass : ∀ i, ∑ a, μ i a = 1)
    (F : (CopyScheduleAtoms role (n + 1) → A) → ℂ) (B E : ℝ) (hE : 0 ≤ E)
    (henergy : ∑ x, scheduledPrimePrior role (n + 1) μ x * ‖F x‖ ^ 2 ≤ B)
    (hpair : ∀ e f : FinalParityReassignments n m, e ≠ f →
      ‖∑ x, (scheduledPrimePrior role (n + 1) μ x : ℂ) *
        (F (scheduledFullSamplePerm role n m word e x) *
          star (F (scheduledFullSamplePerm role n m word f x)))‖ ≤ E) :
    ‖∑ x, (scheduledPrimePrior role (n + 1) μ x : ℂ) * F x‖ ^ 2 ≤
      B / (((Nat.factorial (2 ^ n)) ^ 2) ^ m : ℕ) + E := by
  have h := final_permutation_comparison n m (scheduledPrimePrior role (n + 1) μ)
    (fun x => Finset.prod_nonneg (fun i _ => hμ _ _)) 1 B E
    (scheduledPrimePrior_mass role (n + 1) μ hμmass).le hE
    (fun e x => F (scheduledFullSamplePerm role n m word e x))
    (∑ x, (scheduledPrimePrior role (n + 1) μ x : ℂ) * F x)
    (fun e => scheduledFullSamplePerm_mean role n m word e μ F) (fun e f => ?_)
  · simpa only [one_mul] using h
  by_cases hef : e = f
  · subst f
    simp only [ite_true, Complex.star_def]
    rw [diagonal_pair_eq_energy (scheduledPrimePrior role (n + 1) μ)
      (fun x => Finset.prod_nonneg (fun i _ => hμ _ _)),
      scheduledFullSamplePerm_energy]
    exact henergy
  · simpa only [hef, ite_false] using hpair e f hef

/-- The manuscript's measure includes a shared root frequency. Reassignments
act only on the prime coordinates, so the root is identical in every pair. -/
theorem scheduled_root_final_comparison {I A R : Type*}
    [Fintype I] [Fintype A] [Fintype R]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word})
    (μ : I → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a) (hμmass : ∀ i, ∑ a, μ i a = 1)
    (F : R → (CopyScheduleAtoms role (n + 1) → A) → ℂ) (B E : ℝ) (hE : 0 ≤ E)
    (henergy : ∑ s, ∑ x, scheduledPrimePrior role (n + 1) μ x * ‖F s x‖ ^ 2 ≤ B)
    (hpair : ∀ e f : FinalParityReassignments n m, e ≠ f →
      ‖∑ s, ∑ x, (scheduledPrimePrior role (n + 1) μ x : ℂ) *
        (F s (scheduledFullSamplePerm role n m word e x) *
          star (F s (scheduledFullSamplePerm role n m word f x)))‖ ≤ E) :
    ‖∑ s, ∑ x, (scheduledPrimePrior role (n + 1) μ x : ℂ) * F s x‖ ^ 2 ≤
      (Fintype.card R : ℝ) * (B / (((Nat.factorial (2 ^ n)) ^ 2) ^ m : ℕ) + E) := by
  let ν : R × (CopyScheduleAtoms role (n + 1) → A) → ℝ :=
    fun x => scheduledPrimePrior role (n + 1) μ x.2
  have hν (x) : 0 ≤ ν x := Finset.prod_nonneg (fun i _ => hμ _ _)
  have hmass : ∑ x, ν x = (Fintype.card R : ℝ) := by
    simp only [ν, Fintype.sum_prod_type, scheduledPrimePrior_mass role (n + 1) μ hμmass,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hmean (e : FinalParityReassignments n m) :
      (∑ x : R × (CopyScheduleAtoms role (n + 1) → A), (ν x : ℂ) *
        F x.1 (scheduledFullSamplePerm role n m word e x.2)) =
        ∑ s, ∑ x, (scheduledPrimePrior role (n + 1) μ x : ℂ) * F s x := by
    simp only [ν, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro s _
    exact scheduledFullSamplePerm_mean role n m word e μ (F s)
  apply final_permutation_comparison n m ν hν (Fintype.card R) B E hmass.le hE
    (fun e x => F x.1 (scheduledFullSamplePerm role n m word e x.2)) _ hmean
  intro e f
  by_cases hef : e = f
  · subst f
    simp only [ite_true, Complex.star_def]
    rw [diagonal_pair_eq_energy ν hν]
    simp only [ν, Fintype.sum_prod_type]
    simp_rw [scheduledFullSamplePerm_energy]
    exact henergy
  · simpa only [hef, ite_false, ν, Fintype.sum_prod_type] using hpair e f hef

end Ostmann

end OAI
