import OAI.Probability.SATComputability.PoissonGrid

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal

theorem countsMask_product {A B X : Type*} [Fintype A] [Fintype B] [Fintype X]
    (mask : A → Finset X) (c : A × B → ℕ) :
    countsMask (fun p : A × B => mask p.1) c =
      countsMask mask (fun a => ∑ b, c (a,b)) := by
  ext x
  simp only [countsMask, Finset.mem_filter, Finset.mem_univ, true_and, Prod.forall]
  constructor
  · intro h a
    by_cases hx : x ∈ mask a
    · exact Or.inr hx
    · left
      exact Finset.sum_eq_zero (fun b _ => (h a b).resolve_right hx)
  · intro h a b
    rcases h a with hz | hx
    · left
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Nat.zero_le (c (a,j)))).mp hz b
        (Finset.mem_univ b)
    · exact Or.inr hx

theorem poissonCountLaw_redundant_mask {A B X : Type*}
    [Fintype A] [Fintype B] [Fintype X] (r : ℝ≥0)
    (mask : A → Finset X) (f : Finset X → ℝ) :
    (∫ c, f (countsMask (fun p : A × B => mask p.1) c)
      ∂poissonCountLaw (A × B) r) =
      ∫ c, f (countsMask mask c) ∂poissonCountLaw A (Fintype.card B*r) := by
  rw [← poissonCountLaw_uncurry_integral]
  simp only [countsMask_product]
  rw [← poissonCountLaw_row_sums (A := A) (B := B) r,
    integral_map (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aestronglyMeasurable]

theorem poissonCountLaw_total_mean {A : Type*} [Fintype A] (r : ℝ≥0) :
    (∫ c : A → ℕ, ((∑ a, c a : ℕ) : ℝ) ∂poissonCountLaw A r) =
      Fintype.card A * (r : ℝ) := by
  rw [poissonCountLaw, poissonCountLaw_sum_integral]
  rw [poisson_mean]
  simp

end FixedClauseThreshold.Computability

end OAI
