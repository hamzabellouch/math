import OAI.Probability.InvariantIsing.Cavity.CavityBoundedReweighting
import OAI.Probability.InvariantIsing.Cavity.CavityFullTilt

namespace OAI

/-! Exponential replica tilts on the continuous leaf/residual state space.
Finite-product identities do not require a countable configuration space. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators ENNReal

namespace InvariantIsing

lemma cavity_exp_replica_partition {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ) (r : ℕ) :
    (∫ σ : Fin r → X, Real.exp (∑ i, H (σ i)) ∂Measure.pi (fun _ => ν)) =
      (∫ x, Real.exp (H x) ∂ν)^r := by
  simp_rw [Real.exp_sum]
  simpa only [Fintype.card_fin] using
    integral_fintype_prod_eq_pow (ι := Fin r) (μ := ν) (fun x => Real.exp (H x))

lemma cavity_continuous_replica_tilt {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν) (r : ℕ) :
    (Measure.pi (fun _ : Fin r => ν)).tilted (fun σ => ∑ i, H (σ i)) =
      Measure.pi (fun _ : Fin r => ν.tilted H) := by
  let := isProbabilityMeasure_tilted he
  have hZ : 0 < ∫ x, Real.exp (H x) ∂ν := integral_exp_pos he
  symm
  apply Measure.pi_eq
  intro s hs
  rw [tilted_apply_eq_ofReal_integral' _ (MeasurableSet.univ_pi hs),
    cavity_exp_replica_partition, Measure.restrict_pi_pi]
  have hh (σ : Fin r → X) : Real.exp (∑ i, H (σ i)) /
      (∫ x, Real.exp (H x) ∂ν)^r =
        ∏ i, Real.exp (H (σ i)) / (∫ x, Real.exp (H x) ∂ν) := by
    rw [Real.exp_sum, Finset.prod_div_distrib]
    simp
  simp_rw [hh]
  rw [integral_fintype_prod_eq_prod
    (fun (_ : Fin r) x => Real.exp (H x) / (∫ y, Real.exp (H y) ∂ν))]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun x =>
    div_nonneg (Real.exp_pos _).le hZ.le))]
  congr 1
  funext i
  exact (tilted_apply_eq_ofReal_integral' H (hs i)).symm

lemma cavityWeightedReplicaMean_exp {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν) {r : ℕ}
    (F : (Fin r → X) → ℝ) :
    cavityWeightedReplicaMean ν (fun x => Real.exp (H x)) F =
      ∫ σ, F σ ∂Measure.pi (fun _ : Fin r => ν.tilted H) := by
  rw [← cavity_continuous_replica_tilt ν H he r, integral_tilted_eq_div,
    cavity_exp_replica_partition]
  simp only [cavityWeightedReplicaMean, cavityWeightNormalizer,
    cavityWeightNumerator, Real.exp_sum]

end InvariantIsing

end

end OAI
