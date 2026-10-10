import OAI.Geometry.RCD.Transport.BoundedPlanEntropyBounds

namespace OAI

/-! # Closure of entropy bounds for bounded compressed time marginals -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem bounded_entropy_time_limit (μ : Measure X) [SigmaFinite μ]
    {B : Set X} (hB : MeasurableSet B) [IsFiniteMeasure (μ.restrict B)]
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hs : ∀ t : Time, ∀ᵐ x ∂π.map (fun γ => γ t), x ∈ B)
    (a : Time → ℝ) (ha : Continuous a) {u : ℕ → Time} {t : Time}
    (hu : Tendsto u atTop (𝓝 t))
    (hb : ∀ j, boltzmannEntropy μ (π.map (fun γ => γ (u j))) ≤ a (u j)) :
    boltzmannEntropy μ (π.map (fun γ => γ t)) ≤ a t := by
  let piProb : ProbabilityMeasure C(Time,X) := ⟨π,inferInstance⟩
  let ν := fun s : Time => piProb.map (fun γ => γ s)
  have hν : Continuous ν := continuous_time_marginals piProb
  have hclosed := isClosed_compressedKLConstraint (μ.restrict B) hC ν
    (fun s => a s+(μ.restrict B).real univ-1) hν
    ((ha.add continuous_const).sub continuous_const)
  have hmem : ∀ j, compressedKLConstraint (μ.restrict B) C (ν (u j))
      (a (u j)+(μ.restrict B).real univ-1) := by
    intro j
    exact (entropy_bound_localized_iff μ (ν (u j)) hB hC (hs _) (hc _) _).mp (hb j)
  have ht := hclosed.mem_of_tendsto hu (Eventually.of_forall hmem)
  exact (entropy_bound_localized_iff μ (ν t) hB hC (hs _) (hc _) _).mpr ht

end RegularPointCoordinates

end

end OAI
