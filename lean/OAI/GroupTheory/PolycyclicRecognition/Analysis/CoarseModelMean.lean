import OAI.GroupTheory.PolycyclicRecognition.Analysis.MetricFolnerTransfer
import OAI.GroupTheory.PolycyclicRecognition.Analysis.MetricFolnerCount

namespace OAI

/-! # Amenability of the discrete group in the recognition argument -/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability Metric MeasureTheory

theorem invariantMean_of_coarse_virtualPolycyclic
    {P H : Type*} [Group P] [MetricSpace P] [IsIsometricSMul P P] [DecidableEq P]
    [Group H] [MetricSpace H] [DiscreteTopology H] [IsIsometricSMul H H]
    [ProperSpace H] [MeasurableSpace H] [BorelSpace H] [MeasurableMul H] [DecidableEq H]
    (hP : IsVirtuallyPolycyclic P)
    (hfinite : ∀ R : ℝ, (closedBall (1 : P) R).Finite)
    (u : P → H) {c K C : ℝ} (hc : 0 ≤ c) (hK : 0 ≤ K)
    (hsurj : ∀ y, ∃ p, dist y (u p) ≤ c)
    (hlower : ∀ x y, dist x y ≤ K * dist (u x) (u y) + C) :
    Nonempty (InvariantMean H) := by
  let : (Measure.count : Measure H).IsOpenPosMeasure :=
    ⟨fun _ _ hU => Measure.count_ne_zero hU⟩
  let : IsFiniteMeasureOnCompacts (Measure.count : Measure H) :=
    ⟨by intro K hK; exact Measure.count_apply_lt_top.mpr hK.finite_of_discrete⟩
  obtain ⟨A, _hA, hzero, hfin, hratio⟩ := exists_metricFolner_sequence
    (invariantMean_of_isVirtuallyPolycyclic hP).some hfinite Measure.count u hc hK hsurj hlower
  exact invariantMean_of_countMetricFolner
    (fun R => (isCompact_closedBall (1 : H) R).finite_of_discrete)
    A hzero hfin hratio

end PolycyclicRecognition

end

end OAI
