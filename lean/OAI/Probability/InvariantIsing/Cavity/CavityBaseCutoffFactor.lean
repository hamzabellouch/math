import OAI.Probability.InvariantIsing.Cavity.CavityCutoffWeight
import OAI.Probability.InvariantIsing.Cavity.CavityPhysicalGibbsSplit

namespace OAI

/-! Factoring a restricted cavity test over the base Gibbs law. The
cutoff remains inside the weight, so its zero convention is preserved. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Classical

namespace InvariantIsing

lemma cavity_reference_tilt_add {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (μ : Measure X) [IsProbabilityMeasure μ] (J V : X → ℝ)
    (hj : Integrable (fun x => Real.exp (J x)) μ)
    (hfull : Integrable (fun x => Real.exp (J x + V x)) μ)
    {r : ℕ} (F : (Fin r → X) → ℝ) :
    referenceReplicaMean μ (fun x => J x + V x) F =
      referenceReplicaMean (μ.tilted J) V F := by
  let := isProbabilityMeasure_tilted hj
  have hv : Integrable (fun x => Real.exp (V x)) (μ.tilted J) := by
    rw [integrable_tilted_iff hj]
    simpa only [smul_eq_mul, ← Real.exp_add] using hfull
  rw [referenceReplicaMean_eq_tilted μ _ hfull,
    referenceReplicaMean_eq_tilted (μ.tilted J) V hv, tilted_tilted hj]
  rfl

lemma cavity_cutoff_tilt_add {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (μ : Measure X) [IsProbabilityMeasure μ] (J V : X → ℝ)
    (hj : Integrable (fun x => Real.exp (J x)) μ)
    (hfull : Integrable (fun x => Real.exp (J x + V x)) μ)
    (s : Set X) (F : (Fin 2 → X) → ℝ) :
    cavityCutoffReplicaMean μ (fun x => J x + V x) s F =
      cavityCutoffReplicaMean (μ.tilted J) V s F := by
  unfold cavityCutoffReplicaMean
  rw [cavity_reference_tilt_add μ J V hj hfull,
    cavity_reference_tilt_add μ J V hj hfull]

theorem cavity_base_cutoff_indicator {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    [Countable X] [Countable Y] [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (J : X → ℝ) (V : X × Y → ℝ)
    (hj : Integrable (fun x => Real.exp (J x)) μ)
    (hfull : Integrable (fun x => Real.exp (J x.1 + V x)) (μ.prod ν))
    (s : Set (X × Y)) (F : (Fin 2 → X × Y) → ℝ) :
    cavityCutoffReplicaMean (μ.prod ν) (fun x => J x.1 + V x) s F =
      cavityWeightedReplicaMean ((μ.tilted J).prod ν)
        (s.indicator (fun x => Real.exp (V x))) F := by
  let := isProbabilityMeasure_tilted hj
  have hv := cavity_base_product_tilt_integrable μ ν J (measurable_of_countable J) hj V hfull
  rw [cavity_cutoff_tilt_add (μ.prod ν) (fun x => J x.1) V (hj.comp_fst ν) hfull,
    ← cavity_tilt_prod_left μ ν J (measurable_of_countable J)]
  exact cavity_cutoff_replica_indicator ((μ.tilted J).prod ν) V hv s F

end InvariantIsing

end

end OAI
