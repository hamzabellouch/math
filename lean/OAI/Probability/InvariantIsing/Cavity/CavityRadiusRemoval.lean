import OAI.Probability.InvariantIsing.Cavity.CavitySoftCutoff
import OAI.Probability.InvariantIsing.Cavity.CavityFrameTails

namespace OAI

/-! Removing the continuous radius cutoff from replica observables.
The estimates also cover the convention at a zero cutoff normalizer. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavity_radial_cutoff_moment_error {X : Type*} [MeasurableSpace X] {d : ℕ}
    (ν : Measure X) [IsProbabilityMeasure ν] (Y : X → EuclideanSpace ℝ (Fin d))
    (hY : Measurable Y) (hi : Integrable (fun x => ‖Y x‖^2) ν) {A : ℝ} (hA : 0 < A) :
    1 - cavityWeightNormalizer ν (fun x => cavityRadialCutoff A ‖Y x‖) ≤
      (∫ x, ‖Y x‖^2 ∂ν) / A^2 := by
  have hw : Measurable (fun x => cavityRadialCutoff A ‖Y x‖) :=
    (continuous_cavityRadialCutoff A).measurable.comp hY.norm
  have hiw : Integrable (fun x => cavityRadialCutoff A ‖Y x‖) ν :=
    integrable_of_measurable_abs_le hw (fun x => by
      rw [abs_of_nonneg (cavityRadialCutoff_mem A ‖Y x‖).1]
      exact (cavityRadialCutoff_mem A ‖Y x‖).2)
  have hb x : 1 - cavityRadialCutoff A ‖Y x‖ ≤ ‖Y x‖^2 / A^2 :=
    cavity_radial_defect_bound A hA (fun y => 1 - cavityRadialCutoff A ‖y‖)
      (fun y => ⟨sub_nonneg.mpr (cavityRadialCutoff_mem A ‖y‖).2,
        by linarith [(cavityRadialCutoff_mem A ‖y‖).1]⟩)
      (fun y hy => by rw [cavityRadialCutoff_eq_one hy, sub_self]) (Y x)
  have hh := integral_mono ((integrable_const 1).sub hiw) (hi.div_const (A^2)) hb
  simpa only [Pi.sub_apply, integral_sub (integrable_const 1) hiw, integral_const,
    probReal_univ, one_smul, integral_div, cavityWeightNormalizer] using hh

lemma cavity_soft_radius_replica_error {X : Type*} [MeasurableSpace X] {d r : ℕ}
    (ν : Measure X) [IsProbabilityMeasure ν] (Y : X → EuclideanSpace ℝ (Fin d))
    (hY : Measurable Y) (hi : Integrable (fun x => ‖Y x‖^2) ν)
    (F : (Fin r → X) → ℝ) (hF : Measurable F) {A B : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) (hFb : ∀ σ, |F σ| ≤ B) :
    |cavityWeightedReplicaMean ν (fun x => cavityRadialCutoff A ‖Y x‖) F -
      ∫ σ, F σ ∂Measure.pi (fun _ : Fin r => ν)| ≤
      2 * B * r * ((∫ x, ‖Y x‖^2 ∂ν) / A^2) :=
  (cavity_soft_cutoff_replica_error ν _
    ((continuous_cavityRadialCutoff A).measurable.comp hY.norm)
    (fun x => cavityRadialCutoff_mem A ‖Y x‖) F hF hB hFb).trans
      (mul_le_mul_of_nonneg_left (cavity_radial_cutoff_moment_error ν Y hY hi hA)
        (by positivity))

theorem cavity_soft_radius_mean_error {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {d r : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (Y : Ω × X → EuclideanSpace ℝ (Fin d)) (hY : Measurable Y)
    (F : Ω × (Fin r → X) → ℝ) (hF : Measurable F)
    (hi : ∀ᵐ ω ∂P, Integrable (fun x => ‖Y (ω, x)‖^2) (ν ω))
    (hmi : Integrable (fun ω => ∫ x, ‖Y (ω, x)‖^2 ∂ν ω) P)
    {A B M : ℝ} (hA : 0 < A) (hB : 0 ≤ B)
    (hFb : ∀ ω σ, |F (ω, σ)| ≤ B)
    (hM : (∫ ω, ∫ x, ‖Y (ω, x)‖^2 ∂ν ω ∂P) ≤ M) :
    |∫ ω, cavityWeightedReplicaMean (ν ω) (fun x => cavityRadialCutoff A ‖Y (ω, x)‖)
      (fun σ => F (ω, σ)) - ∫ σ, F (ω, σ) ∂Measure.pi (fun _ : Fin r => ν ω) ∂P| ≤
        2 * B * r * M / A^2 := by
  let w := fun p : Ω × X => cavityRadialCutoff A ‖Y p‖
  have hw : Measurable w := (continuous_cavityRadialCutoff A).measurable.comp hY.norm
  let D := fun ω => cavityWeightedReplicaMean (ν ω) (fun x => w (ω, x))
    (fun σ => F (ω, σ)) - ∫ σ, F (ω, σ) ∂Measure.pi (fun _ : Fin r => ν ω)
  have hmD : Measurable D := by
    apply Measurable.sub
    · exact (measurable_cavityWeightNumerator ν hν w hw F hF).div
        ((measurable_cavityWeightNormalizer ν hν w hw).pow_const r)
    · have hh := measurable_cavityWeightNumerator ν hν (fun _ => 1) measurable_const F hF
      simpa only [cavityWeightNumerator, Finset.prod_const_one, one_mul] using hh
  have hb : ∀ᵐ ω ∂P, |D ω| ≤ 2 * B * r * ((∫ x, ‖Y (ω, x)‖^2 ∂ν ω) / A^2) := by
    filter_upwards [hi] with ω hω
    exact cavity_soft_radius_replica_error (ν ω) (fun x => Y (ω, x))
      (hY.comp measurable_prodMk_left) hω (fun σ => F (ω, σ))
      (hF.comp measurable_prodMk_left) hA hB (hFb ω)
  have hE := (hmi.div_const (A^2)).const_mul (2 * B * r)
  have hD : Integrable D P := hE.mono' hmD.aestronglyMeasurable (by
    simpa only [Real.norm_eq_abs] using hb)
  calc
    _ ≤ ∫ ω, |D ω| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ω, 2 * B * r * ((∫ x, ‖Y (ω, x)‖^2 ∂ν ω) / A^2) ∂P :=
      integral_mono_ae hD.abs hE hb
    _ = 2 * B * r * (∫ ω, ∫ x, ‖Y (ω, x)‖^2 ∂ν ω ∂P) / A^2 := by
      rw [integral_const_mul, integral_div]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hM (by positivity)) (sq_nonneg A)

end InvariantIsing

end

end OAI
