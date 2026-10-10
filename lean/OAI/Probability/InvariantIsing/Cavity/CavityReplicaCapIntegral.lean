import OAI.Probability.InvariantIsing.Cavity.CavityReplicaCap

namespace OAI

/-! Integrability and separate-expectation cap errors for bounded replica
tests under the full cavity Gibbs tilt. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavity_exp_replicaMean_integrable {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {r : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (H : Ω × X → ℝ) (hH : Measurable H)
    (F : Ω × (Fin r → X) → ℝ) (hF : Measurable F)
    (he : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (H (ω,x))) (ν ω))
    {B : ℝ} (hFb : ∀ ω σ, |F (ω,σ)| ≤ B) :
    Integrable (fun ω => cavityWeightedReplicaMean (ν ω) (fun x => Real.exp (H (ω,x)))
      (fun σ => F (ω,σ))) P := by
  have hm : Measurable (fun ω => cavityWeightedReplicaMean (ν ω)
      (fun x => Real.exp (H (ω,x))) (fun σ => F (ω,σ))) :=
    (measurable_cavityWeightNumerator ν hν _ hH.exp F hF).div
      ((measurable_cavityWeightNormalizer ν hν _ hH.exp).pow_const r)
  apply (integrable_const B).mono' hm.aestronglyMeasurable
  filter_upwards [he] with ω hω
  rw [cavityWeightedReplicaMean_exp (ν ω) (fun x => H (ω,x)) hω]
  let := isProbabilityMeasure_tilted hω
  have hb := norm_integral_le_of_norm_le_const
    (μ := Measure.pi (fun _ : Fin r => (ν ω).tilted (fun x => H (ω,x))))
    (f := fun σ => F (ω,σ)) (C := B)
    (ae_of_all _ (fun σ => by simpa only [Real.norm_eq_abs] using hFb ω σ))
  simpa only [probReal_univ, mul_one] using hb

lemma cavity_replica_cap_expectation_error {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {r : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (H : Ω × X → ℝ) (hH : Measurable H)
    (F : Ω × (Fin r → X) → ℝ) (hF : Measurable F)
    (he : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (H (ω,x))) (ν ω))
    (hi : ∀ᵐ ω ∂P, Integrable (fun x => H (ω,x)^2) ((ν ω).tilted (fun x => H (ω,x))))
    (hmi : Integrable (fun ω => ∫ x, H (ω,x)^2 ∂(ν ω).tilted (fun x => H (ω,x))) P)
    {B K T : ℝ} (hB : 0 ≤ B) (hT : 0 < T) (hFb : ∀ ω σ, |F (ω,σ)| ≤ B)
    (hK : (∫ ω, ∫ x, H (ω,x)^2 ∂(ν ω).tilted (fun x => H (ω,x)) ∂P) ≤ K) :
    |(∫ ω, cavityWeightedReplicaMean (ν ω) (fun x => Real.exp (min (H (ω,x)) T))
        (fun σ => F (ω,σ)) ∂P) -
      ∫ ω, cavityWeightedReplicaMean (ν ω) (fun x => Real.exp (H (ω,x)))
        (fun σ => F (ω,σ)) ∂P| ≤ 2 * B * r * K / T := by
  have hc : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (min (H (ω,x)) T)) (ν ω) := by
    apply ae_of_all
    intro ω
    exact integrable_of_measurable_abs_le
      (((hH.comp measurable_prodMk_left).min measurable_const).exp)
      (fun x => by rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.mpr (min_le_right _ _))
  have hiC := cavity_exp_replicaMean_integrable P ν hν (fun p => min (H p) T)
    (hH.min measurable_const) F hF hc hFb
  have hiF := cavity_exp_replicaMean_integrable P ν hν H hH F hF he hFb
  rw [← integral_sub hiC hiF]
  exact cavity_replica_cap_mean_error P ν hν H hH F hF he hi hmi hB hT hFb hK

end InvariantIsing

end

end OAI
