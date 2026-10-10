import Mathlib
import OAI.Probability.LatticeSurface.Dynamics.WeightedInitialSupport

namespace OAI

namespace BrownianForcing

open MeasureTheory ProbabilityTheory Set ConvexSkorokhod

theorem weighted_heat_bath_construction (m : ℕ)
    (B : Body (FreeHeightSpace m)) (c : FreeHeightSpace m) (r R : ℝ)
    (hr : 0<r) (hball : Metric.closedBall c r⊆B.carrier)
    (hR : ∀z∈B.carrier,‖z-c‖≤R)
    (μ : Measure (VectorPath (FreeHeightSpace m))) [IsProbabilityMeasure μ]
    (b : FreeHeightSpace m) :
    IsProbabilityMeasure (weightedBodyLaw B b) ∧
    weightedBodyLaw B b B.carrierᶜ=0 ∧
    Continuous (fullReflectedMap B c r R hr hball hR) ∧
    IsProbabilityMeasure (reflectedBathLaw B c r R hr hball hR μ b) ∧
    (reflectedBathLaw B c r R hr hball hR μ b).map (fun f => f ⟨0,by norm_num⟩)=weightedBodyLaw B b := by
  have hw := weightedBodyLaw_probability B c r R hr hball hR b
  let := hw
  have hcont := fullReflectedMap_continuous B c r R hr hball hR
  let F : FreeHeightSpace m × VectorPath (FreeHeightSpace m) → VectorPath (FreeHeightSpace m) :=
    fun p => fullReflectedMap B c r R hr hball hR (p.1,p.2+linearVectorPath b)
  have hF : Continuous F := hcont.comp (continuous_fst.prodMk (continuous_snd.add continuous_const))
  have hprob : IsProbabilityMeasure (reflectedBathLaw B c r R hr hball hR μ b) :=
    (Measure.isProbabilityMeasure_map_iff hF.measurable.aemeasurable).2 inferInstance
  refine ⟨hw,weightedBodyLaw_support B b,hcont,hprob,?_⟩
  have hproj : Continuous (project B) :=
    (LipschitzWith.of_dist_le_mul (K := 1) (by
      intro x y
      simpa only [NNReal.coe_one,one_mul,dist_eq_norm] using project_nonexpansive B x y)).continuous
  have hmem : ∀ᵐ x∂weightedBodyLaw B b,x∈B.carrier := by
    rw [ae_iff]
    exact weightedBodyLaw_support B b
  change ((weightedBodyLaw B b).prod μ |>.map F).map (fun f => f ⟨0,by norm_num⟩)=weightedBodyLaw B b
  have heval : Measurable (fun f : VectorPath (FreeHeightSpace m) => f ⟨0,by norm_num⟩) :=
    (ContinuousMap.evalCLM ℝ (⟨0,by norm_num⟩ : Set.Icc (0:ℝ) 1)).continuous.measurable
  rw [Measure.map_map heval hF.measurable]
  calc
    _ = ((weightedBodyLaw B b).prod μ).map (project B ∘ Prod.fst) := by
      apply Measure.map_congr
      exact Filter.Eventually.of_forall (fun p => fullReflectedMap_zero B c r R hr hball hR
        (p.1,p.2+linearVectorPath b))
    _ = (((weightedBodyLaw B b).prod μ).map Prod.fst).map (project B) :=
      (Measure.map_map hproj.measurable measurable_fst).symm
    _ = (weightedBodyLaw B b).map (project B) := by simp
    _ = (weightedBodyLaw B b).map id := by
      apply Measure.map_congr
      filter_upwards [hmem] with x hx
      exact project_eq_self B x hx
    _ = weightedBodyLaw B b := Measure.map_id

end BrownianForcing

end OAI
