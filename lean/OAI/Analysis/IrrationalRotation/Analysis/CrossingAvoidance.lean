import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Invariant233.CrossingAvoidance

variable {ι Ω : Type*} [MeasurableSpace Ω]

theorem measureReal_avoid_eq_prod (μ : Measure Ω) [IsProbabilityMeasure μ]
    (events : ι → Set Ω) (hind : iIndepSet events μ)
    (hmeas : ∀ i, MeasurableSet (events i)) (s : Finset ι) :
    μ.real (⋂ i ∈ s, (events i)ᶜ) = ∏ i ∈ s, (1 - μ.real (events i)) := by
  have hprod : μ (⋂ i ∈ s, (events i)ᶜ) = ∏ i ∈ s, μ ((events i)ᶜ) := by
    apply (iIndepSet_iff events μ).mp hind s
    intro i hi
    exact (MeasurableSpace.measurableSet_generateFrom (by simp)).compl
  change (μ (⋂ i ∈ s, (events i)ᶜ)).toReal = _
  rw [hprod, ENNReal.toReal_prod]
  congr 1
  funext i
  change μ.real ((events i)ᶜ) = _
  rw [measureReal_compl (hmeas i), probReal_univ]

theorem measureReal_avoid_le_exp (μ : Measure Ω) [IsProbabilityMeasure μ]
    (events : ι → Set Ω) (hind : iIndepSet events μ)
    (hmeas : ∀ i, MeasurableSet (events i)) (s : Finset ι) (p : ℝ)
    (hp : ∀ i ∈ s, p ≤ μ.real (events i)) :
    μ.real (⋂ i ∈ s, (events i)ᶜ) ≤ Real.exp (-(s.card : ℝ) * p) := by
  rw [measureReal_avoid_eq_prod μ events hind hmeas s]
  calc
    ∏ i ∈ s, (1 - μ.real (events i)) ≤ ∏ _i ∈ s, Real.exp (-p) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        rw [← probReal_univ (μ := μ)]
        exact sub_nonneg.mpr (measureReal_mono (Set.subset_univ _))
      · intro i hi
        exact (sub_le_sub_left (hp i hi) 1).trans (Real.one_sub_le_exp_neg p)
    _ = Real.exp (-(s.card : ℝ) * p) := by
      rw [← Real.exp_sum]
      congr 1
      simp

theorem measureReal_le_exp_of_subset_avoid (μ : Measure Ω) [IsProbabilityMeasure μ]
    (events : ι → Set Ω) (hind : iIndepSet events μ)
    (hmeas : ∀ i, MeasurableSet (events i)) (s : Finset ι) (p : ℝ)
    (hp : ∀ i ∈ s, p ≤ μ.real (events i)) (bad : Set Ω)
    (hbad : bad ⊆ ⋂ i ∈ s, (events i)ᶜ) :
    μ.real bad ≤ Real.exp (-(s.card : ℝ) * p) :=
  (measureReal_mono hbad).trans (measureReal_avoid_le_exp μ events hind hmeas s p hp)

theorem exp_card_bound (s : Finset ι) (m ρ : ℝ) (hρ : 0 ≤ ρ)
    (hcard : m / 40 ≤ (s.card : ℝ)) :
    Real.exp (-(s.card : ℝ) * (ρ / 10)) ≤ Real.exp (-m * ρ / 400) := by
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right hcard hρ
  nlinarith

theorem measureReal_le_exp_four_hundred (μ : Measure Ω) [IsProbabilityMeasure μ]
    (events : ι → Set Ω) (hind : iIndepSet events μ)
    (hmeas : ∀ i, MeasurableSet (events i)) (s : Finset ι) (m ρ : ℝ)
    (hρ : 0 ≤ ρ) (hcard : m / 40 ≤ (s.card : ℝ))
    (hp : ∀ i ∈ s, ρ / 10 ≤ μ.real (events i)) (bad : Set Ω)
    (hbad : bad ⊆ ⋂ i ∈ s, (events i)ᶜ) :
    μ.real bad ≤ Real.exp (-m * ρ / 400) :=
  (measureReal_le_exp_of_subset_avoid μ events hind hmeas s (ρ / 10) hp bad hbad).trans
    (exp_card_bound s m ρ hρ hcard)

theorem measureReal_le_exp_intensity (μ : Measure Ω) [IsProbabilityMeasure μ]
    (events : ι → Set Ω) (hind : iIndepSet events μ)
    (hmeas : ∀ i, MeasurableSet (events i)) (s : Finset ι) (m ρ L : ℝ)
    (hρ : 0 ≤ ρ) (hcard : m / 40 ≤ (s.card : ℝ)) (hL : L ≤ m * ρ)
    (hp : ∀ i ∈ s, ρ / 10 ≤ μ.real (events i)) (bad : Set Ω)
    (hbad : bad ⊆ ⋂ i ∈ s, (events i)ᶜ) :
    μ.real bad ≤ Real.exp (-L / 400) := by
  refine (measureReal_le_exp_four_hundred μ events hind hmeas s m ρ hρ hcard hp bad hbad).trans ?_
  apply Real.exp_le_exp.mpr
  linarith


variable {α : Type*} [LinearOrder α] (s : Finset ι) (x y u : ι → α)

theorem below_iff_of_no_crossing
    (horder : ∀ i ∈ s, x i ≤ y i)
    (hno : ∀ i ∈ s, ¬ (x i < u i ∧ u i ≤ y i)) :
    ∀ i ∈ s, x i < u i ↔ y i < u i := by
  intro i hi
  constructor
  · intro hxu
    exact lt_of_not_ge (fun huy => hno i hi ⟨hxu, huy⟩)
  · intro hyu
    exact lt_of_le_of_lt (horder i hi) hyu

theorem below_card_add_above_card
    (horder : ∀ i ∈ s, x i ≤ y i)
    (hno : ∀ i ∈ s, ¬ (x i < u i ∧ u i ≤ y i)) :
    (s.filter (fun i => x i < u i)).card +
      (s.filter (fun i => u i ≤ y i)).card = s.card := by
  classical
  have heq : s.filter (fun i => u i ≤ y i) = s.filter (fun i => ¬ x i < u i) := by
    apply Finset.filter_congr
    intro i hi
    rw [below_iff_of_no_crossing s x y u horder hno i hi, not_lt]
  rw [heq]
  exact Finset.card_filter_add_card_filter_not _

theorem above_half_of_below_not_half
    (horder : ∀ i ∈ s, x i ≤ y i)
    (hno : ∀ i ∈ s, ¬ (x i < u i ∧ u i ≤ y i))
    (hsmall : ¬ s.card ≤ 2 * (s.filter (fun i => x i < u i)).card) :
    s.card ≤ 2 * (s.filter (fun i => u i ≤ y i)).card := by
  classical
  have hsum := below_card_add_above_card s x y u horder hno
  omega

theorem eligible_card_lower_bound (eligible : Finset ι) (m : ℝ)
    (hcandidates : m / 20 ≤ (s.card : ℝ))
    (heligible : s.card ≤ 2 * eligible.card) :
    m / 40 ≤ (eligible.card : ℝ) := by
  have hcast : (s.card : ℝ) ≤ 2 * (eligible.card : ℝ) := by exact_mod_cast heligible
  linarith


end Invariant233.CrossingAvoidance

end OAI
