import OAI.GroupTheory.PolycyclicRecognition.Algebra.OrbitAverageLimitMass
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CountableMeasureTests
import Mathlib.Dynamics.Ergodic.Action.Basic

namespace OAI

/-! # A countable convex-averaging criterion for ergodicity

If indicators in a determining family admit finite orbit averages converging
almost everywhere to constants, restriction to any invariant set is a scalar
multiple of the original probability. Evaluating on its complement gives the
zero-one law.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology

variable {G X : Type*} [Group G] [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X]
  [MulAction G X] [MeasurableConstSMul G X]
  (ν : Measure X) [IsProbabilityMeasure ν] [SMulInvariantMeasure G X ν]

theorem ergodicSMul_of_orbitAverages
    (hav : ∀ I : Finset ℕ, ∃ (A : ℕ → FiniteOrbitAverage G) (c : ℝ),
      ∀ᵐ x ∂ν, Tendsto
        (fun n => (A n).apply ((finiteMeasureTest X I).indicator (fun _ => (1 : ℝ))) x)
        atTop (𝓝 c)) : ErgodicSMul G X ν := by
  refine ⟨fun {s} hs hi => ?_⟩
  let : SMulInvariantMeasure G X (ν.restrict s) :=
    smulInvariantMeasure_restrict_ae ν s hs hi
  have he : ν.restrict s = (ν s) • ν := by
    apply measure_eq_of_finiteMeasureTests X
    intro I
    obtain ⟨A, c, hc⟩ := hav I
    have hcν := orbitAverage_indicator_limit_mass ν (finiteMeasureTest X I)
      (measurableSet_finiteMeasureTest X I) A c hc
    have hcs := orbitAverage_indicator_limit_mass (ν.restrict s) (finiteMeasureTest X I)
      (measurableSet_finiteMeasureTest X I) A c (ae_restrict_of_ae hc)
    simp only [measure_univ, mul_one] at hcν
    rw [hcs, Measure.smul_apply, smul_eq_mul, hcν, Measure.restrict_apply_univ]
    exact mul_comm _ _
  have hz : ν s * ν sᶜ = 0 := by
    have hh := congrArg (fun m : Measure X => m sᶜ) he
    simpa only [Measure.restrict_apply hs.compl, compl_inter_self, measure_empty,
      Measure.smul_apply, smul_eq_mul] using hh.symm
  rcases mul_eq_zero.mp hz with h | h
  · exact eventuallyEmptyOrUniv_iff.2 (Or.inr (measure_eq_zero_iff_ae_notMem.mp h))
  · apply eventuallyEmptyOrUniv_iff.2
    left
    simpa only [mem_compl_iff, not_not] using measure_eq_zero_iff_ae_notMem.mp h

end PolycyclicRecognition

end

end OAI
