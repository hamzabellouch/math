import OAI.Analysis.IrrationalRotation.Sampling.TrialSamplingSelection
import OAI.Analysis.IrrationalRotation.Sampling.SamplingMeanSquare
import OAI.Analysis.IrrationalRotation.Rotation.CircleRepresentative

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace Invariant233.TrialSampling

lemma pairLaw_probability {N : ℝ} (hN : 0 < N) : IsProbabilityMeasure (pairLaw N) := by
  let : IsProbabilityMeasure circleMeasure := ⟨by
    simp [circleMeasure, AddCircle.measure_univ]⟩
  let : IsProbabilityMeasure
      (ProbabilityTheory.cond volume (Set.Icc (1 / N) (2 / N))) :=
    InvariantProjection.IndependentAngles.intervalLaw_isProbabilityMeasure
      (div_lt_div_of_pos_right (by norm_num) hN)
  dsimp [pairLaw]
  infer_instance

lemma measurable_coordinateSample (m : ℕ) (endpoint : Bool) (n : ℕ) :
    Measurable (coordinateSample m endpoint n) := by
  exact (measurable_orientedKernel_pair m endpoint).comp
    ((CircleParameterData.measurable_rep.comp measurable_snd).prodMk
      (measurable_const.mul measurable_fst).fract)

theorem pairLaw_representative_measurePreserving {N : ℝ} (_hN : 0 < N) :
    MeasurePreserving (fun p : ℝ × Circle => (p.1, CircleParameterData.rep p.2))
      (pairLaw N)
      ((ProbabilityTheory.cond volume (Set.Icc (1 / N) (2 / N))).prod
        (volume.restrict (Set.Ico (0 : ℝ) 1))) := by
  let ν : Measure ℝ := ProbabilityTheory.cond volume (Set.Icc (1 / N) (2 / N))
  let : IsProbabilityMeasure ν :=
    InvariantProjection.IndependentAngles.intervalLaw_isProbabilityMeasure
      (div_lt_div_of_pos_right (by norm_num) _hN)
  let : IsProbabilityMeasure circleMeasure := ⟨by
    simp [circleMeasure, AddCircle.measure_univ]⟩
  exact (MeasurePreserving.id ν).prod CocycleSupport.measurePreserving_circleRepresentative

theorem integral_pairLaw_representative {N : ℝ} (hN : 0 < N) (f : ℝ × ℝ → ℝ) :
    (∫ p, f (p.1, CircleParameterData.rep p.2) ∂pairLaw N) =
      ∫ p, f p ∂(ProbabilityTheory.cond volume (Set.Icc (1 / N) (2 / N))).prod
        (volume.restrict (Set.Ico (0 : ℝ) 1)) := by
  have hr : MeasurableEmbedding (CircleParameterData.rep : Circle → ℝ) := by
    exact (MeasurableEmbedding.subtype_coe measurableSet_Ico).comp
      (AddCircle.measurableEquivIco (1 : ℝ) 0).measurableEmbedding
  exact (pairLaw_representative_measurePreserving hN).integral_comp
    (MeasurableEmbedding.id.prodMap hr) f

theorem expectation_squaredError_eq_pair_integral
    (m : ℕ) {N : ℝ} (hN : 0 < N) (samples : Finset ℕ) (endpoint : Bool) :
    (∫⁻ phase, squaredError m samples endpoint phase ∂phaseLaw m N) =
      ∫⁻ x : Fin m → ℝ × Circle, ENNReal.ofReal
        (((samples.card : ℝ)⁻¹ * (∑ n ∈ samples,
          ∏ i : Fin m, coordinateSample m endpoint n (x i)) - 1) ^ 2)
          ∂Measure.pi (fun _ : Fin m => pairLaw N) := by
  let ν : Measure ℝ := ProbabilityTheory.cond volume (Set.Icc (1 / N) (2 / N))
  let : IsProbabilityMeasure ν :=
    InvariantProjection.IndependentAngles.intervalLaw_isProbabilityMeasure
      (div_lt_div_of_pos_right (by norm_num) hN)
  let : IsProbabilityMeasure circleMeasure := ⟨by
    simp [circleMeasure, AddCircle.measure_univ]⟩
  let F : (Fin m → ℝ) × (Fin m → Circle) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal ((average m samples endpoint p.1 p.2 - 1) ^ 2)
  have hF : Measurable F :=
    (((measurable_average_pair m samples endpoint).sub_const 1).pow_const 2).ennreal_ofReal
  have he := measurePreserving_arrowProdEquivProdArrow ℝ Circle (Fin m)
    (fun _ => ν) (fun _ => circleMeasure)
  have hi := he.lintegral_comp hF
  rw [lintegral_prod F hF.aemeasurable] at hi
  simpa only [phaseLaw_eq_pi m hN, squaredError, spatialLaw, pairLaw,
    F, average, coordinateSample, MeasurableEquiv.arrowProdEquivProdArrow,
    MeasurableEquiv.coe_mk, Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_mk, ν] using hi.symm

theorem memLp_coordinateSample {m : ℕ} (hm : 0 < m) {N : ℝ} (hN : 0 < N)
    (endpoint : Bool) (n : ℕ) :
    MemLp (coordinateSample m endpoint n) 2 (pairLaw N) := by
  let := pairLaw_probability hN
  apply MemLp.of_bound (measurable_coordinateSample m endpoint n).aestronglyMeasurable
    ((m : ℝ) ^ 2 / CircleParameterData.kernelWidth m)
  apply Eventually.of_forall
  intro p
  have h := CircleParameterData.orientedKernel_bounds endpoint hm
    (CircleParameterData.rep p.2) (Int.fract ((n : ℝ) * p.1))
  simpa only [coordinateSample, Real.norm_eq_abs, abs_of_nonneg h.1] using h.2

lemma measurable_coordinateIdeal (m : ℕ) (endpoint : Bool) :
    Measurable (coordinateIdeal m endpoint) := by
  have h : Measurable (fun p : (ℝ × Circle) × ℝ =>
      CircleParameterData.orientedKernel endpoint m (CircleParameterData.rep p.1.2) p.2) :=
    (measurable_orientedKernel_pair m endpoint).comp
      ((CircleParameterData.measurable_rep.comp (measurable_snd.comp measurable_fst)).prodMk
        measurable_snd)
  exact h.stronglyMeasurable.integral_prod_right'.measurable

theorem coordinateIdeal_norm_le {m : ℕ} (hm : 0 < m) (endpoint : Bool) (p : ℝ × Circle) :
    ‖coordinateIdeal m endpoint p‖ ≤ (m : ℝ) ^ 2 / CircleParameterData.kernelWidth m := by
  have hb : ∀ᵐ v : ℝ ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
      ‖CircleParameterData.orientedKernel endpoint m (CircleParameterData.rep p.2) v‖ ≤
        (m : ℝ) ^ 2 / CircleParameterData.kernelWidth m := by
    apply Eventually.of_forall
    intro v
    have h := CircleParameterData.orientedKernel_bounds endpoint hm
      (CircleParameterData.rep p.2) v
    simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2
  have h := norm_integral_le_of_norm_le_const hb
  simpa [coordinateIdeal, Measure.real] using h

theorem memLp_coordinateIdeal {m : ℕ} (hm : 0 < m) {N : ℝ} (hN : 0 < N)
    (endpoint : Bool) : MemLp (coordinateIdeal m endpoint) 2 (pairLaw N) := by
  let := pairLaw_probability hN
  exact MemLp.of_bound (measurable_coordinateIdeal m endpoint).aestronglyMeasurable
    ((m : ℝ) ^ 2 / CircleParameterData.kernelWidth m)
    (Eventually.of_forall (coordinateIdeal_norm_le hm endpoint))

theorem expectation_squaredError_le_meanSquareBound
    (m : ℕ) (hm : 1 ≤ m) {N : ℝ} (hN : 0 < N)
    (samples : Finset ℕ) (hs : samples.Nonempty) (endpoint : Bool)
    (C : ℝ) (hC : 0 ≤ C)
    (hcard : (m : ℝ) ^ ((69 / 100 : ℝ) * m) ≤ (samples.card : ℝ))
    (hmean : (∫ p, coordinateIdeal m endpoint p ∂pairLaw N) =
      SamplingAsymptotics.kernelMass m)
    (hbase : (∫ p, (coordinateIdeal m endpoint p) ^ 2 ∂pairLaw N) ≤
      SamplingAsymptotics.momentBase m)
    (hdiag : ∀ n ∈ samples, (∫ p, (coordinateSample m endpoint n p) ^ 2 ∂pairLaw N) ≤
      8 * (m : ℝ) ^ (3 / 5 : ℝ) * Real.log m)
    (hoff : ∀ n ∈ samples, ∀ n' ∈ samples, n ≠ n' →
      |(∫ p, coordinateSample m endpoint n p * coordinateSample m endpoint n' p ∂pairLaw N) -
        (∫ p, (coordinateIdeal m endpoint p) ^ 2 ∂pairLaw N)| ≤ C * (m : ℝ) ^ (-(50 : ℝ)))
    (hcross : ∀ n ∈ samples,
      |(∫ p, coordinateSample m endpoint n p * coordinateIdeal m endpoint p ∂pairLaw N) -
        (∫ p, (coordinateIdeal m endpoint p) ^ 2 ∂pairLaw N)| ≤ C * (m : ℝ) ^ (-(50 : ℝ))) :
    (∫⁻ phase, squaredError m samples endpoint phase ∂phaseLaw m N) ≤
      ENNReal.ofReal (SamplingAsymptotics.meanSquareBound C m) := by
  let := pairLaw_probability hN
  have hmpos : 0 < m := by omega
  rw [expectation_squaredError_eq_pair_integral m hN samples endpoint]
  rw [SamplingAsymptotics.lintegral_sample_mean_square_eq_ofReal m samples
    (fun n (_ : Fin m) => coordinateSample m endpoint n)
    (fun n _ => memLp_coordinateSample hmpos hN endpoint n)]
  apply ENNReal.ofReal_le_ofReal
  exact SamplingAsymptotics.integral_sample_mean_square_le m hm samples hs
    (fun n (_ : Fin m) => coordinateSample m endpoint n)
    (fun _ : Fin m => coordinateIdeal m endpoint)
    (fun n _ => memLp_coordinateSample hmpos hN endpoint n)
    (fun _ => memLp_coordinateIdeal hmpos hN endpoint)
    C hC hcard (fun _ => hmean) (fun _ => hbase)
    (fun n hn _ => hdiag n hn) (fun n hn n' hn' hne _ => hoff n hn n' hn' hne)
    (fun n hn _ => hcross n hn)

end Invariant233.TrialSampling

end

end OAI
