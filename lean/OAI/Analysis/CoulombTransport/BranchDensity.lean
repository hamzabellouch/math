import OAI.Analysis.CoulombTransport.DisjointSquares
import OAI.Analysis.CoulombTransport.BranchCoupling

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace Problem356

/-- Probability of a square density gives its ordinary integral normalization. -/
theorem integral_sq_eq_one_of_densityMeasure_probability
    {g : E3 → ℝ} (hg : Measurable g)
    [IsProbabilityMeasure (densityMeasure (fun x => (g x) ^ 2))] :
    (∫ x : E3, (g x) ^ 2 ∂(volume : Measure E3)) = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun x => sq_nonneg (g x)))
    (hg.pow_const 2).aestronglyMeasurable]
  have hmass := measure_univ (μ := densityMeasure (fun x => (g x) ^ 2))
  simp only [densityMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] at hmass
  rw [hmass, ENNReal.toReal_one]

/-- A smooth compact unit square defines a probability measure. -/
theorem isProbabilityMeasure_densityMeasure_unit_sq
    {g : E3 → ℝ}
    (hsm : ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) g)
    (hcs : HasCompactSupport g)
    (hmass : (∫ x : E3, (g x) ^ 2 ∂(volume : Measure E3)) = 1) :
    IsProbabilityMeasure (densityMeasure (fun x => (g x) ^ 2)) := by
  have hcomp : HasCompactSupport (fun x => (g x) ^ 2) := by
    simpa only [Function.comp_def] using
      hcs.comp_left (g := fun y : ℝ => y ^ 2) (by simp)
  have hint : Integrable (fun x => (g x) ^ 2) (volume : Measure E3) :=
    (hsm.continuous.pow 2).integrable_of_hasCompactSupport hcomp
  constructor
  simp only [densityMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall (fun x => sq_nonneg (g x))), hmass]
  exact ENNReal.ofReal_one

/-- The weights of the central and four outer squares. -/
def branchDensityWeight (i : Fin 5) : ℝ := if i = 0 then 1 / 3 else 1 / 6

lemma branchDensityWeight_nonneg (i : Fin 5) : 0 ≤ branchDensityWeight i := by
  unfold branchDensityWeight
  split <;> norm_num

lemma sum_branchDensityWeight : ∑ i : Fin 5, branchDensityWeight i = 1 := by
  norm_num [branchDensityWeight, Fin.sum_univ_succ]

/-- Five disjoint square amplitudes, with the four outer square laws obtained
by the prescribed branch pushforwards, form the exact smooth branch marginal. -/
theorem exists_smooth_density_eq_branchMarginal
    (g : Fin 5 → E3 → ℝ) (H : Fin 4 → E3 → E3)
    (hgn : ∀ i x, 0 ≤ g i x)
    (hgs : ∀ i, ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) (g i))
    (hgc : ∀ i, HasCompactSupport (g i))
    (hgd : Pairwise fun i j =>
      Disjoint (Function.support (g i)) (Function.support (g j)))
    (hzero : (∫ x : E3, (g 0 x) ^ 2 ∂(volume : Measure E3)) = 1)
    (hH : ∀ i, Measurable (H i))
    (hmap : ∀ i : Fin 4,
      densityMeasure (fun x => (g i.succ x) ^ 2) =
        Measure.map (H i) (densityMeasure (fun x => (g 0 x) ^ 2))) :
    ∃ rho : E3 → ℝ,
      IsSmoothCompactProbabilityDensity rho ∧
      densityMeasure rho =
        branchMarginal (densityMeasure (fun x => (g 0 x) ^ 2))
          (H 0) (H 1) (H 2) (H 3) := by
  have := isProbabilityMeasure_densityMeasure_unit_sq (hgs 0) (hgc 0) hzero
  have hmass : ∀ i : Fin 5, (∫ x : E3, (g i x) ^ 2 ∂(volume : Measure E3)) = 1 := by
    intro i
    refine Fin.cases hzero (fun j => ?_) i
    have hp : IsProbabilityMeasure (densityMeasure (fun x => (g j.succ x) ^ 2)) := by
      rw [hmap j]
      exact (Measure.isProbabilityMeasure_map_iff (hH j).aemeasurable).mpr inferInstance
    have := hp
    exact integral_sq_eq_one_of_densityMeasure_probability (hgs j.succ).continuous.measurable
  refine ⟨fun x => ∑ i : Fin 5, branchDensityWeight i * (g i x) ^ 2, ?_, ?_⟩
  · exact isSmoothCompactProbabilityDensity_sum_normalized_disjoint_squares
      Finset.univ branchDensityWeight g
      (fun i _ => branchDensityWeight_nonneg i) (fun i _ => hgn i)
      (fun i _ => hgs i) (fun i _ => hgc i)
      (fun i _ j _ hij => hgd hij) (fun i _ => hmass i) sum_branchDensityWeight
  · rw [densityMeasure_sum_weighted_squares Finset.univ branchDensityWeight g
      (fun i _ => branchDensityWeight_nonneg i)
      (fun i _ => (hgs i).continuous.measurable)]
    simp only [Fin.sum_univ_succ, branchDensityWeight, Fin.succ_ne_zero,
      ite_true, ite_false]
    simp only [hmap]
    unfold branchMarginal
    norm_num [ENNReal.ofReal_div_of_pos, smul_add]
    simp only [add_assoc]

end Problem356

end

end OAI
