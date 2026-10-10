import OAI.NumberTheory.Ostmann.Construction.SelectedFullFinalPermutation
import OAI.NumberTheory.Ostmann.Construction.ScheduledFinalComparison

namespace OAI

/-! # The final comparison restricted to genuine bulk permutations -/
namespace Ostmann
open scoped BigOperators Classical SchwartzMap FourierTransform

theorem selectedPrimePrior_preserved {I A : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word) (e : FinalParityReassignments n m)
    (μ : I → A → ℝ) (x : CopyScheduleAtoms role (n + 1) → A) :
    scheduledPrimePrior role (n + 1) μ (selectedFullSamplePerm role n m bulk hbulk e x) =
      scheduledPrimePrior role (n + 1) μ x :=
  selectedFullFinalPerm_product_prior role n m bulk hbulk e μ x

theorem selectedFullSamplePerm_energy {I A : Type*} [Fintype I] [Fintype A]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word) (e : FinalParityReassignments n m)
    (μ : I → A → ℝ) (F : (CopyScheduleAtoms role (n + 1) → A) → ℂ) :
    (∑ x, scheduledPrimePrior role (n + 1) μ x *
      ‖F (selectedFullSamplePerm role n m bulk hbulk e x)‖ ^ 2) =
      ∑ x, scheduledPrimePrior role (n + 1) μ x * ‖F x‖ ^ 2 := by
  have h := (selectedFullSamplePerm (A := A) role n m bulk hbulk e).sum_comp
    (fun x => scheduledPrimePrior role (n + 1) μ x * ‖F x‖ ^ 2)
  simpa only [selectedPrimePrior_preserved] using h

theorem selected_full_final_comparison {I A : Type*} [Fintype I] [Fintype A]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (μ : I → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a) (hμmass : ∀ i, ∑ a, μ i a = 1)
    (F : (CopyScheduleAtoms role (n + 1) → A) → ℂ) (B E : ℝ) (hE : 0 ≤ E)
    (henergy : ∑ x, scheduledPrimePrior role (n + 1) μ x * ‖F x‖ ^ 2 ≤ B)
    (hpair : ∀ e f : FinalParityReassignments n m, e ≠ f →
      ‖∑ x, (scheduledPrimePrior role (n + 1) μ x : ℂ) *
        (F (selectedFullSamplePerm role n m bulk hbulk e x) *
          star (F (selectedFullSamplePerm role n m bulk hbulk f x)))‖ ≤ E) :
    ‖∑ x, (scheduledPrimePrior role (n + 1) μ x : ℂ) * F x‖ ^ 2 ≤
      B / (((Nat.factorial (2 ^ n)) ^ 2) ^ m : ℕ) + E := by
  have h := final_permutation_comparison n m (scheduledPrimePrior role (n + 1) μ)
    (fun x => Finset.prod_nonneg (fun i _ => hμ _ _)) 1 B E
    (scheduledPrimePrior_mass role (n + 1) μ hμmass).le hE
    (fun e x => F (selectedFullSamplePerm role n m bulk hbulk e x))
    (∑ x, (scheduledPrimePrior role (n + 1) μ x : ℂ) * F x)
    (fun e => selectedFullSamplePerm_mean role n m bulk hbulk e μ F) (fun e f => ?_)
  · simpa only [one_mul] using h
  by_cases hef : e = f
  · subst f
    simp only [ite_true, Complex.star_def]
    rw [diagonal_pair_eq_energy (scheduledPrimePrior role (n + 1) μ)
      (fun x => Finset.prod_nonneg (fun i _ => hμ _ _)),
      selectedFullSamplePerm_energy]
    exact henergy
  · simpa only [hef, ite_false] using hpair e f hef

/-- The manuscript's measure includes a shared root frequency. Reassignments
act only on the prime coordinates, so the root is identical in every pair. -/
theorem selected_root_final_comparison {I A R : Type*}
    [Fintype I] [Fintype A] [Fintype R]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (μ : I → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a) (hμmass : ∀ i, ∑ a, μ i a = 1)
    (F : R → (CopyScheduleAtoms role (n + 1) → A) → ℂ) (B E : ℝ) (hE : 0 ≤ E)
    (henergy : ∑ s, ∑ x, scheduledPrimePrior role (n + 1) μ x * ‖F s x‖ ^ 2 ≤ B)
    (hpair : ∀ e f : FinalParityReassignments n m, e ≠ f →
      ‖∑ s, ∑ x, (scheduledPrimePrior role (n + 1) μ x : ℂ) *
        (F s (selectedFullSamplePerm role n m bulk hbulk e x) *
          star (F s (selectedFullSamplePerm role n m bulk hbulk f x)))‖ ≤ E) :
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
        F x.1 (selectedFullSamplePerm role n m bulk hbulk e x.2)) =
        ∑ s, ∑ x, (scheduledPrimePrior role (n + 1) μ x : ℂ) * F s x := by
    simp only [ν, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro s _
    exact selectedFullSamplePerm_mean role n m bulk hbulk e μ (F s)
  apply final_permutation_comparison n m ν hν (Fintype.card R) B E hmass.le hE
    (fun e x => F x.1 (selectedFullSamplePerm role n m bulk hbulk e x.2)) _ hmean
  intro e f
  by_cases hef : e = f
  · subst f
    simp only [ite_true, Complex.star_def]
    rw [diagonal_pair_eq_energy ν hν]
    simp only [ν, Fintype.sum_prod_type]
    simp_rw [selectedFullSamplePerm_energy]
    exact henergy
  · simpa only [hef, ite_false, ν, Fintype.sum_prod_type] using hpair e f hef

end Ostmann

end OAI
