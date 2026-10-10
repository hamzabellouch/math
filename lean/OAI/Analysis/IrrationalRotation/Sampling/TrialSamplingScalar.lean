import OAI.Analysis.IrrationalRotation.Sampling.TrialSamplingMoments
import OAI.Analysis.IrrationalRotation.Sampling.ScalarSamplingEstimates

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Invariant233.TrialSampling

theorem coordinateSample_eq_scalar {m : ℕ} (hm : 200 ≤ m)
    (endpoint : Bool) (n : ℕ) (p : ℝ × Circle) :
    coordinateSample m endpoint n p =
      if endpoint then ScalarSampling.manuscriptEndpointKernel m (CircleParameterData.rep p.2)
        (Int.fract ((n : ℝ) * p.1))
      else ScalarSampling.manuscriptKernel m (CircleParameterData.rep p.2)
        (Int.fract ((n : ℝ) * p.1)) := by
  exact ScalarSampling.parameter_orientedKernel_eq hm endpoint _
    ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩

theorem coordinateIdeal_eq_scalar {m : ℕ} (hm : 200 ≤ m)
    (endpoint : Bool) (p : ℝ × Circle) :
    coordinateIdeal m endpoint p =
      ∫ v in (0 : ℝ)..1,
        if endpoint then ScalarSampling.manuscriptEndpointKernel m (CircleParameterData.rep p.2) v
        else ScalarSampling.manuscriptKernel m (CircleParameterData.rep p.2) v := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro v hv
  exact ScalarSampling.parameter_orientedKernel_eq hm endpoint _ ⟨hv.1.le, hv.2⟩

theorem integral_coordinate_moment_eq_scalar {m : ℕ} (hm : 200 ≤ m)
    {N : ℝ} (hN : 0 < N) (endpoint : Bool)
    (F : (ℕ → ℝ) → ℝ → ℝ) :
    (∫ p, F (fun n => coordinateSample m endpoint n p) (coordinateIdeal m endpoint p)
      ∂pairLaw N) =
      ∫ p : ℝ × ℝ,
        F (fun n => if endpoint then ScalarSampling.manuscriptEndpointKernel m p.2
            (Int.fract ((n : ℝ) * p.1))
          else ScalarSampling.manuscriptKernel m p.2 (Int.fract ((n : ℝ) * p.1)))
          (∫ v in (0 : ℝ)..1,
            if endpoint then ScalarSampling.manuscriptEndpointKernel m p.2 v
            else ScalarSampling.manuscriptKernel m p.2 v)
        ∂(UniformIntervalPhase.lambdaLaw N).prod
          (volume.restrict (Set.Ico (0 : ℝ) 1)) := by
  simp_rw [coordinateSample_eq_scalar hm, coordinateIdeal_eq_scalar hm]
  rw [UniformIntervalPhase.lambdaLaw_eq_cond N hN]
  exact integral_pairLaw_representative hN (fun p =>
    F (fun n => if endpoint then ScalarSampling.manuscriptEndpointKernel m p.2
          (Int.fract ((n : ℝ) * p.1))
        else ScalarSampling.manuscriptKernel m p.2 (Int.fract ((n : ℝ) * p.1)))
      (∫ v in (0 : ℝ)..1,
        if endpoint then ScalarSampling.manuscriptEndpointKernel m p.2 v
        else ScalarSampling.manuscriptKernel m p.2 v))

theorem integral_pairLaw_representative_iterated {N : ℝ} (hN : 0 < N)
    (f : ℝ × ℝ → ℝ)
    (hf : Integrable (fun p : ℝ × Circle =>
      f (p.1, CircleParameterData.rep p.2)) (pairLaw N)) :
    (∫ p, f (p.1, CircleParameterData.rep p.2) ∂pairLaw N) =
      ∫ s in Set.Ico (0 : ℝ) 1, ∫ t, f (t, s) ∂UniformIntervalPhase.lambdaLaw N := by
  have hr : MeasurableEmbedding (CircleParameterData.rep : Circle → ℝ) :=
    (MeasurableEmbedding.subtype_coe measurableSet_Ico).comp
      (AddCircle.measurableEquivIco (1 : ℝ) 0).measurableEmbedding
  have hfi := (pairLaw_representative_measurePreserving hN).integrable_comp_emb
    (MeasurableEmbedding.id.prodMap hr) |>.mp hf
  rw [integral_pairLaw_representative hN]
  rw [← UniformIntervalPhase.lambdaLaw_eq_cond N hN] at hfi ⊢
  let := UniformIntervalPhase.lambdaLaw_probability N hN
  exact integral_prod_symm f hfi

end Invariant233.TrialSampling

end

end OAI
