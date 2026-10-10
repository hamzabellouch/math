import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Group.Action
import Mathlib.Topology.DenseEmbedding

namespace OAI

/-! # Invariance on a dense set of acting elements

For a continuous action on a compact metric space, a finite measure invariant
under a dense family of group elements is invariant under the whole group.
This turns countably many almost-everywhere identities of conditional kernels
into invariance of their components for a locally compact second countable group.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped CompactlySupported

variable {G X ι : Type*} [Group G] [TopologicalSpace G]
  [FirstCountableTopology G] [LocallyCompactSpace G]
  [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [MulAction G X] [ContinuousSMul G X]
  (ν : Measure X) [IsFiniteMeasure ν]

/-- Dense invariance is sufficient; the dense family need not be a subgroup. -/
theorem smulInvariantMeasure_of_denseRange (a : ι → G) (ha : DenseRange a)
    (hν : ∀ i, ν.map (a i • ·) = ν) : SMulInvariantMeasure G X ν := by
  have hmap (g : G) : ν.map (g • ·) = ν := by
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    have hc : Continuous (fun g : G => ∫ x, f (g • x) ∂ν) := by
      have h := continuous_parametric_integral_of_continuous (μ := ν)
        (f := fun (g : G) (x : X) => f (g • x))
        (show Continuous (fun p : G × X => f (p.1 • p.2)) from
          f.continuous.comp continuous_smul) isCompact_univ
      simpa only [setIntegral_univ] using h
    have hmf (g : G) : (∫ x, f x ∂ν.map (g • ·)) = ∫ x, f (g • x) ∂ν :=
      integral_map (continuous_const_smul g).measurable.aemeasurable
        (show AEStronglyMeasurable (fun x : X => f x) (ν.map (g • ·)) from
          f.continuous.aestronglyMeasurable)
    have he : (fun g : G => ∫ x, f (g • x) ∂ν) = fun _ => ∫ x, f x ∂ν := by
      apply ha.equalizer hc continuous_const
      funext i
      change (∫ x, f (a i • x) ∂ν) = _
      rw [← hmf (a i), hν i]
      rfl
    rw [hmf g, congrFun he g]
  refine ⟨fun g s hs => ?_⟩
  rw [← Measure.map_apply (continuous_const_smul g).measurable hs, hmap g]

end PolycyclicRecognition

end

end OAI
