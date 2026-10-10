import OAI.Analysis.FiniteFactor.Coupling.Marginals
import Mathlib.Probability.ProductMeasure

namespace OAI

namespace FiniteFactor
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace CouplingParameters

/-- The augmented countable product retains each coordinate's label and pair. -/
abbrev CouplingSample := ℕ → Fin 6 × (ℝ × ℝ)

def productCoupling (p : ℕ → CouplingParameters) : Measure CouplingSample :=
  Measure.infinitePi (fun i => (p i).labelledCoupling)

instance productCoupling_probability (p : ℕ → CouplingParameters) :
    IsProbabilityMeasure (productCoupling p) := by
  unfold productCoupling
  infer_instance

def productEndpoint (right : ℕ → Bool) (ω : CouplingSample) (i : ℕ) : ℝ :=
  endpoint (right i) (ω i).2

theorem productEndpoint_measurable (right : ℕ → Bool) : Measurable (productEndpoint right) := by
  apply Measurable.of_eval
  intro i
  exact (endpoint_measurable (right i)).comp (measurable_snd.comp (measurable_pi_apply i))

theorem labelled_endpoint_density (p : CouplingParameters) (right : Bool) :
    p.labelledCoupling.map (fun z => endpoint right z.2) =
      unitIntervalMeasure.withDensity (fun t => ENNReal.ofReal (p.endpointDensity right t)) := by
  rw [← p.coupling_endpoint_density]
  unfold coupling
  rw [Measure.map_map (endpoint_measurable right) measurable_snd]
  rfl

/-- Every coordinatewise choice of endpoint marginals is exactly its product
law, including the mixed prefixes used in biased-identity. -/
theorem productEndpoint_law (p : ℕ → CouplingParameters) (right : ℕ → Bool) :
    (productCoupling p).map (productEndpoint right) =
      Measure.infinitePi (fun i => unitIntervalMeasure.withDensity
        (fun t => ENNReal.ofReal ((p i).endpointDensity (right i) t))) := by
  unfold productCoupling productEndpoint
  rw [Measure.infinitePi_map_pi (fun i => (p i).labelledCoupling)
    (f := fun i (z : Fin 6 × (ℝ × ℝ)) => endpoint (right i) z.2) (fun i => (endpoint_measurable (right i)).comp measurable_snd)]
  simp_rw [labelled_endpoint_density]

/-- Independence is recorded as the exact finite-cylinder product formula. -/
theorem productCoupling_cylinder (p : ℕ → CouplingParameters) (I : Finset ℕ)
    (S : ℕ → Set (Fin 6 × (ℝ × ℝ))) (hS : ∀ i ∈ I, MeasurableSet (S i)) :
    productCoupling p (Set.pi (I : Set ℕ) S) = ∏ i ∈ I, (p i).labelledCoupling (S i) :=
  Measure.infinitePi_pi _ hS

end CouplingParameters
end
end FiniteFactor

end OAI
