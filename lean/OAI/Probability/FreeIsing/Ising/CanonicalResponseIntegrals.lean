import OAI.Probability.FreeIsing.Brownian.SpatialPrimitive
import OAI.Probability.FreeIsing.Ising.ContinuousResponseEnergy
import OAI.Probability.FreeIsing.Ising.ObservationIndependence

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.IsingObservationInnovation

theorem innovationMap_increments_indep
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (s t : ℝ≥0)
    {v w : TreeVertex d} (hvw : v ≠ w) :
    IndepFun (fun x : Paths d => innovationMap beta x v t - innovationMap beta x v s)
      (fun x => innovationMap beta x w t - innovationMap beta x w s)
      (observationLaw μ) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hp : MeasurePreserving (innovationMap beta) (observationLaw μ)
      (Measure.infinitePi (fun _ : TreeVertex d => WienerSampler.wienerMeasure)) :=
    ⟨measurable_innovationMap beta, map_innovationMap_observationLaw hμ⟩
  apply indepFun_comp_measurePreserving hp
    ((measurable_evaluation v t).sub (measurable_evaluation v s))
    ((measurable_evaluation w t).sub (measurable_evaluation w s))
  exact (iIndepFun_infinitePi (P := fun _ : TreeVertex d => WienerSampler.wienerMeasure)
    (fun _ => (continuous_eval_const t).measurable.sub
      (continuous_eval_const s).measurable)).indepFun hvw

end Problem367.IsingObservationInnovation

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation BrownianArrayFiltration

theorem exists_canonical_root_response_integrals
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hd : 3 ≤ d) (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) :
    ∃ (I : TreeVertex d → ℝ≥0 → Paths d → ℝ) (Y : ℝ≥0 → Paths d → ℝ)
      (hI2 : ∀ a t, MemLp (I a t) 2 (observationLaw μ))
      (hY2 : ∀ t, MemLp (Y t) 2 (observationLaw μ)),
      (∀ a, IsStronglyPredictable (filtration d) (I a) ∧
        Martingale (I a) (filtration d) (observationLaw μ) ∧
        (∀ᵐ x ∂observationLaw μ, Continuous (fun t => I a t x))) ∧
      (∀ a (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
        Tendsto (fun n => ∫ x,
          (BrownianIntegralProcess.stoppedUniformSum
            (fun s x => innovationMap beta x a s) (continuousRootResponse hb a)
            N n t x - I a t x) ^ 2 ∂observationLaw μ) atTop (𝓝 0)) ∧
      IsStronglyPredictable (filtration d) Y ∧
      Martingale Y (filtration d) (observationLaw μ) ∧
      (∀ᵐ x ∂observationLaw μ, Continuous (fun t => Y t x)) ∧
      Y 0 =ᵐ[observationLaw μ] 0 ∧
      (∀ t, (∫ x, Y t x ^ 2 ∂observationLaw μ) =
        ∑' a, ∫ s in (0 : ℝ)..(t : ℝ), ∫ x,
          continuousRootResponse hb a s.toNNReal x ^ 2 ∂observationLaw μ) ∧
      (∀ t, HasSum (fun a => (hI2 a t).toLp (I a t)) ((hY2 t).toLp (Y t))) ∧
      (∀ T : ℝ≥0, Tendsto (fun q : Finset (TreeVertex d) =>
        ∫ x, MartingaleStrongMaximal.maximalSquare
          (MartingaleSpatialLimit.finiteSum I q - Y) T x ∂observationLaw μ)
          atTop (𝓝 0)) ∧
      Martingale (fun t x => Y t x ^ 2 -
        nnrealTimePrimitive (spatialSquareDensity (continuousRootResponse hb)) t x)
        (filtration d) (observationLaw μ) ∧
      (∀ t, Integrable
        (nnrealTimePrimitive (spatialSquareDensity (continuousRootResponse hb)) t)
        (observationLaw μ)) ∧
      (∀ᵐ x ∂observationLaw μ, Continuous (fun t =>
        nnrealTimePrimitive (spatialSquareDensity (continuousRootResponse hb)) t x)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hc (a : TreeVertex d) := continuousRootResponse_continuous_ae hd hμ hb hcrit a
  have henergy (N : ℕ) : Summable (fun a =>
      ∫ s in (0 : ℝ)..(N : ℝ), ∫ x,
        continuousRootResponse hb a s.toNNReal x ^ 2 ∂observationLaw μ) := by
    simpa only [NNReal.coe_natCast] using
      (continuousRootResponse_hasSum_timeEnergy hd hμ hb hcrit (N : ℝ≥0)).summable
  obtain ⟨I, Y, hI2, hY2, hI, hIlim, hYp, hYM, hYc, hY0,
      hYiso, hYsum, hYmax, hQ, hAint, hAsum⟩ :=
    exists_global_continuous_spatial_integral_compensatedSquare
      (B := fun a s x => innovationMap beta x a s)
      (F := filtration d) (H := continuousRootResponse hb)
      (fun a => (innovationMap_isBrownianReal hμ a).toIsPreBrownianReal)
      (innovationMap_stronglyAdapted beta)
      (innovationMap_increment_indep_filtration hμ)
      (fun s t _ _ _ hab => innovationMap_increments_indep hμ s t hab)
      (fun a => (innovationMap_isBrownianReal hμ a).cont)
      (fun a => (continuousRootResponse_progressive hb a).stronglyAdapted) hc
      (C := fun _ => 1) (fun _ => by norm_num)
      (fun a => Eventually.of_forall (fun x t => continuousRootResponse_abs_le_one hb a t x))
      henergy
  have hs (N : ℕ) := hAsum (N : ℝ≥0)
  have heq := ae_spatialCompensator_eq_primitive hc hs
  have hpQ := compensatedSquare_spatial_primitive
    (fun a => continuousRootResponse_progressive hb a) hc hs hYM.stronglyAdapted hQ
  refine ⟨I, Y, hI2, hY2, hI, hIlim, hYp, hYM, hYc, hY0,
    hYiso, hYsum, hYmax, hpQ, ?_, ?_⟩
  · intro t
    apply (hAint t).congr
    filter_upwards [heq] with x hx
    exact hx.1 t
  · filter_upwards [heq] with x hx
    exact hx.2.1

end Problem367.IsingObservationFactor

end

end OAI
