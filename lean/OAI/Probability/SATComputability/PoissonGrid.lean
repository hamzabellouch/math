import OAI.Probability.SATComputability.PoissonCountProducts
import OAI.Probability.SATComputability.RestoredProcessMoment
import OAI.Probability.SATComputability.PoissonMaskCounts

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal

theorem poissonCountLaw_uncurry {A B : Type*} [Fintype A] [Fintype B] (r : ℝ≥0) :
    Measure.map (fun c : A → B → ℕ => fun p : A × B => c p.1 p.2)
      (Measure.pi (fun _ : A => poissonCountLaw B r)) = poissonCountLaw (A × B) r := by
  apply Measure.ext_of_singleton
  intro c
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton c)]
  have he : (fun x : A → B → ℕ => fun p : A × B => x p.1 p.2) ⁻¹' {c} =
      {fun a b => c (a,b)} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff, Prod.forall]
  rw [he]
  simp only [poissonCountLaw, Measure.pi_singleton, Fintype.prod_prod_type]

theorem poissonCountLaw_uncurry_integral {A B : Type*} [Fintype A] [Fintype B]
    (r : ℝ≥0) (f : (A × B → ℕ) → ℝ) :
    (∫ c : A → B → ℕ, f (fun p => c p.1 p.2)
      ∂Measure.pi (fun _ : A => poissonCountLaw B r)) =
      ∫ c, f c ∂poissonCountLaw (A × B) r := by
  rw [← poissonCountLaw_uncurry r]
  exact (integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable f).aestronglyMeasurable).symm

theorem countsMask_sum {A I X : Type*} [Fintype A] [Fintype I] [Fintype X]
    (mask : A → Finset X) (c : I → A → ℕ) (x : X) :
    (∀ i, x ∈ countsMask mask (c i)) ↔
      x ∈ countsMask mask (fun a => ∑ i, c i a) := by
  simp only [countsMask, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h a
    by_cases hx : x ∈ mask a
    · exact Or.inr hx
    · left
      apply Finset.sum_eq_zero
      intro i _
      exact (h i a).resolve_right hx
  · intro h i a
    rcases h a with hz | hx
    · left
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Nat.zero_le (c j a))).mp hz i
        (Finset.mem_univ i)
    · exact Or.inr hx

theorem frontload_countsMask {A : Type*} [Fintype A] {n M : ℕ}
    (mask : A → Finset (DeletionCandidate n)) (c : Fin M → A → ℕ) :
    frontloadMask (fun j => countsMask mask (c j)) =
      countsMask mask (fun a => ∑ j, c j a) := by
  ext x
  rw [frontloadMask, mem_maskRun]
  simp only [Finset.mem_univ, true_and]
  exact countsMask_sum mask c x

end FixedClauseThreshold.Computability

end OAI
