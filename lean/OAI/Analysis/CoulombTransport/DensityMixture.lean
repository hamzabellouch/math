import OAI.Analysis.CoulombTransport.Model

namespace OAI

universe uIndex

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- The nonnegative real-density constructor respects finite scalar multiples. -/
theorem densityMeasure_const_mul {a : ℝ} (ha : 0 ≤ a) (rho : E3 → ℝ) :
    densityMeasure (fun x => a * rho x) = ENNReal.ofReal a • densityMeasure rho := by
  unfold densityMeasure
  simp_rw [ENNReal.ofReal_mul ha]
  exact withDensity_smul' _ _ ENNReal.ofReal_ne_top

/-- The real density constructor is additive on nonnegative densities. -/
theorem densityMeasure_add {rho sigma : E3 → ℝ}
    (hrho : ∀ x, 0 ≤ rho x) (hsigma : ∀ x, 0 ≤ sigma x)
    (hm : Measurable rho) :
    densityMeasure (fun x => rho x + sigma x) =
      densityMeasure rho + densityMeasure sigma := by
  unfold densityMeasure
  simp_rw [ENNReal.ofReal_add (hrho _) (hsigma _)]
  exact withDensity_add_left hm.ennreal_ofReal _

/-- Finite nonnegative density mixtures agree with mixtures of the induced
measures. This identifies the smooth marginal with the branch-plan marginal. -/
theorem densityMeasure_finset_mixture {ι : Type uIndex} (s : Finset ι)
    (a : ι → ℝ) (rho : ι → E3 → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hrho : ∀ i ∈ s, ∀ x, 0 ≤ rho i x)
    (hm : ∀ i ∈ s, Measurable (rho i)) :
    densityMeasure (fun x => ∑ i ∈ s, a i * rho i x) =
      ∑ i ∈ s, ENNReal.ofReal (a i) • densityMeasure (rho i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [densityMeasure]
  | @insert i s hi ih =>
    have hai : 0 ≤ a i := ha i (Finset.mem_insert_self _ _)
    have hri : ∀ x, 0 ≤ rho i x := hrho i (Finset.mem_insert_self _ _)
    have hmi : Measurable (rho i) := hm i (Finset.mem_insert_self _ _)
    have has : ∀ j ∈ s, 0 ≤ a j := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hrs : ∀ j ∈ s, ∀ x, 0 ≤ rho j x :=
      fun j hj => hrho j (Finset.mem_insert_of_mem hj)
    have hms : ∀ j ∈ s, Measurable (rho j) :=
      fun j hj => hm j (Finset.mem_insert_of_mem hj)
    simp only [Finset.sum_insert hi]
    rw [densityMeasure_add (fun x => mul_nonneg hai (hri x))
      (fun x => Finset.sum_nonneg (fun j hj => mul_nonneg (has j hj) (hrs j hj x)))
      (measurable_const.mul hmi), densityMeasure_const_mul hai, ih has hrs hms]

/-- Fintype form of the density-mixture identity. -/
theorem densityMeasure_fintype_mixture {ι : Type uIndex} [Fintype ι]
    (a : ι → ℝ) (rho : ι → E3 → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hrho : ∀ i x, 0 ≤ rho i x)
    (hm : ∀ i, Measurable (rho i)) :
    densityMeasure (fun x => ∑ i, a i * rho i x) =
      ∑ i, ENNReal.ofReal (a i) • densityMeasure (rho i) := by
  exact densityMeasure_finset_mixture Finset.univ a rho
    (fun i _ => ha i) (fun i _ => hrho i) (fun i _ => hm i)

theorem densityMeasure_five_component_mixture
    (rho0 : E3 → ℝ) (rho : Fin 4 → E3 → ℝ)
    (h0 : ∀ x, 0 ≤ rho0 x) (h : ∀ i x, 0 ≤ rho i x)
    (hm0 : Measurable rho0) (hm : ∀ i, Measurable (rho i)) :
    densityMeasure (fun x => (1 / 3 : ℝ) * rho0 x +
      ∑ i, (1 / 6 : ℝ) * rho i x) =
      (1 / 3 : ℝ≥0∞) • densityMeasure rho0 +
      ∑ i, (1 / 6 : ℝ≥0∞) • densityMeasure (rho i) := by
  rw [densityMeasure_add (fun x => mul_nonneg (by norm_num) (h0 x))
    (fun x => Finset.sum_nonneg (fun i _ => mul_nonneg (by norm_num) (h i x)))
    (measurable_const.mul hm0)]
  rw [densityMeasure_const_mul (by norm_num),
    densityMeasure_fintype_mixture (fun _ : Fin 4 => (1 / 6 : ℝ)) rho
      (fun _ => by norm_num) h hm]
  norm_num [ENNReal.ofReal_div_of_pos]

end Problem356

end

end OAI
