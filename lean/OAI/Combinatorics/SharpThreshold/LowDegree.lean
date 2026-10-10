import OAI.Combinatorics.SharpThreshold.LowDegreeBounds
import OAI.Combinatorics.SharpThreshold.FourierDerivative
import OAI.Combinatorics.SharpThreshold.FourierVariance
import OAI.Combinatorics.SharpThreshold.BooleanProjection
import OAI.Combinatorics.SharpThreshold.FourierHypercontractive

namespace OAI

universe u

noncomputable section

namespace Problem313.BiasedFourier

open scoped BigOperators Classical

variable {ι : Type u} [Fintype ι]

/-- The biased low-degree influence estimate, with the product noise
contraction as its only remaining analytic premise. -/
theorem low_degree_estimate_of_noise {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) (m : ℝ) (hm : 1 ≤ m)
    (horbit : ∀ i, Reindex.influence p f i ≤ (∑ j, Reindex.influence p f j) / m)
    (hnoise : ∀ a : Finset ι → ℝ,
      (∑ x, weight p x *
        (∑ S, (Real.sqrt (p * (1 - p)) / 4) ^ S.card * a S * char p S x) ^ 4) ≤
          (∑ S, (a S) ^ 2) ^ 2) :
    (∑ S : Finset ι,
      if S.Nonempty ∧ (S.card : ℝ) ≤ Real.sqrt (p * (1 - p)) * Real.log m / 64
      then coeff p (fun x => boolReal (f x)) S ^ 2 else 0) ≤
        m ^ (-1 / 4 : ℝ) * ∑ i, Reindex.influence p f i := by
  have hvar : 0 < p * (1 - p) := mul_pos hp (sub_pos.mpr hp1)
  have hσ : 0 < Real.sqrt (p * (1 - p)) := Real.sqrt_pos.mpr hvar
  have hσhalf : Real.sqrt (p * (1 - p)) ≤ 1 / 2 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · nlinarith [sq_nonneg (p - 1 / 2)]
  have hρ : 0 < Real.sqrt (p * (1 - p)) / 4 := by positivity
  have hρ1 : Real.sqrt (p * (1 - p)) / 4 ≤ 1 := by linarith
  refine lowDegree_bound_of_projection
    (fun S => coeff p (fun x => boolReal (f x)) S ^ 2)
    (fun i S => coeff p (delta i (fun x => boolReal (f x))) S ^ 2)
    (Reindex.influence p f) (Real.sqrt (p * (1 - p))) m hσ hσhalf hm
    (fun S => sq_nonneg _) (fun i S => sq_nonneg _)
    (Reindex.influence_nonneg hp.le hp1.le f) horbit
    (boolean_spectral_mass_le_one hp hp1 f) ?_ ?_
  · intro i S hi
    rw [Real.sq_sqrt hvar.le]
    exact coeff_sq_eq_variance_mul_delta_erase_sq hp hp1
      (fun x => boolReal (f x)) i S hi
  · intro i
    change (∑ S : Finset ι,
      if (S.card : ℝ) ≤ Real.sqrt (p * (1 - p)) * Real.log m / 64
      then coeff p (fun x => boolReal (f (Function.update x i true)) -
        boolReal (f (Function.update x i false))) S ^ 2 else 0) ≤ _
    simpa only [Finset.sum_filter] using
      booleanDifference_lowDegree_energy_le hp hp1
        (Real.sqrt (p * (1 - p)) / 4)
        (Real.sqrt (p * (1 - p)) * Real.log m / 64)
        hρ hρ1 hnoise f i

/-- Version of the low-degree estimate written as a filtered sum with the
literal positive integer degree condition. -/
theorem low_degree_estimate_filter_of_noise {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) (m : ℝ) (hm : 1 ≤ m)
    (horbit : ∀ i, Reindex.influence p f i ≤ (∑ j, Reindex.influence p f j) / m)
    (hnoise : ∀ a : Finset ι → ℝ,
      (∑ x, weight p x *
        (∑ S, (Real.sqrt (p * (1 - p)) / 4) ^ S.card * a S * char p S x) ^ 4) ≤
          (∑ S, (a S) ^ 2) ^ 2) :
    (∑ S ∈ (Finset.univ.filter fun S : Finset ι =>
      1 ≤ S.card ∧ (S.card : ℝ) ≤ Real.sqrt (p * (1 - p)) * Real.log m / 64),
      coeff p (fun x => boolReal (f x)) S ^ 2) ≤
        m ^ (-1 / 4 : ℝ) * ∑ i, Reindex.influence p f i := by
  simpa only [Finset.sum_filter, Finset.one_le_card] using
    low_degree_estimate_of_noise hp hp1 f m hm horbit hnoise

/-- The biased Boolean low-degree estimate.  No monotonicity or symmetry
is required beyond the displayed bound on each coordinate influence. -/
theorem low_degree_estimate {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) (m : ℝ) (hm : 1 ≤ m)
    (horbit : ∀ i, Reindex.influence p f i ≤ (∑ j, Reindex.influence p f j) / m) :
    (∑ S : Finset ι,
      if S.Nonempty ∧ (S.card : ℝ) ≤ Real.sqrt (p * (1 - p)) * Real.log m / 64
      then coeff p (fun x => boolReal (f x)) S ^ 2 else 0) ≤
        m ^ (-1 / 4 : ℝ) * ∑ i, Reindex.influence p f i := by
  exact low_degree_estimate_of_noise hp hp1 f m hm horbit
    (synthesis_fourth_bound hp hp1)

/-- The literal integer-degree filtered-sum form of the low-degree estimate. -/
theorem low_degree_estimate_filter {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) (m : ℝ) (hm : 1 ≤ m)
    (horbit : ∀ i, Reindex.influence p f i ≤ (∑ j, Reindex.influence p f j) / m) :
    (∑ S ∈ (Finset.univ.filter fun S : Finset ι =>
      1 ≤ S.card ∧ (S.card : ℝ) ≤ Real.sqrt (p * (1 - p)) * Real.log m / 64),
      coeff p (fun x => boolReal (f x)) S ^ 2) ≤
        m ^ (-1 / 4 : ℝ) * ∑ i, Reindex.influence p f i := by
  exact low_degree_estimate_filter_of_noise hp hp1 f m hm horbit
    (synthesis_fourth_bound hp hp1)

end Problem313.BiasedFourier

end

end OAI
