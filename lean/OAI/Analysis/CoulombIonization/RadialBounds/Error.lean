import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierTruncationBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric ProbabilityTheory
open scoped BigOperators Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma compactBound_integrable_prod {p : Ω → TFSpace → ℝ}
    (hm : Measurable (Function.uncurry p)) (hb : DeterministicLocalBound p)
    {R : ℝ} (hs : ∀ sample x, R < ‖x‖ → p sample x = 0) :
    Integrable (Function.uncurry p) (P.prod volume) := by
  obtain ⟨C,hC⟩ := hb (closedBall 0 R) (isCompact_closedBall 0 R)
  have hi : Integrable ((closedBall (0 : TFSpace) R).indicator (fun _ => C)) volume :=
    (integrableOn_const (C := C) (isCompact_closedBall (0 : TFSpace) R).measure_lt_top.ne).integrable_indicator
      measurableSet_closedBall
  apply (hi.comp_snd P).mono' hm.aestronglyMeasurable
  exact Eventually.of_forall fun z => by
    by_cases hz : z.2 ∈ closedBall (0 : TFSpace) R
    · rw [indicator_of_mem hz]
      exact hC z.1 z.2 hz
    · rw [indicator_of_notMem hz,Function.uncurry_apply_pair,
        hs z.1 z.2 (lt_of_not_ge (by simpa only [mem_closedBall,dist_zero_right] using hz)),norm_zero]

end CoulombBarrier

end

end OAI
