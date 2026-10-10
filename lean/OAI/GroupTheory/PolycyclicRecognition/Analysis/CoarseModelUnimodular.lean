import OAI.GroupTheory.PolycyclicRecognition.Analysis.MetricFolnerTransfer
import OAI.GroupTheory.PolycyclicRecognition.Analysis.MetricFolnerUnimodular

namespace OAI

/-! # Unimodularity of the Lie model follows from the original comparison group

The quasi-isometry contributes its lower bound and coarse surjectivity.
Polycyclicity contributes a proved invariant mean; no model-unimodularity
hypothesis is retained.
-/

noncomputable section

namespace PolycyclicRecognition

open Metric MeasureTheory

theorem isMulRightInvariant_of_coarse_virtualPolycyclic
    {P G : Type*} [Group P] [MetricSpace P] [IsIsometricSMul P P] [DecidableEq P]
    [Group G] [MetricSpace G] [IsTopologicalGroup G] [IsIsometricSMul G G]
    [ProperSpace G] [MeasurableSpace G] [BorelSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsHaarMeasure] [Measure.InnerRegular μ]
    (hP : IsVirtuallyPolycyclic P)
    (hfinite : ∀ R : ℝ, (closedBall (1 : P) R).Finite)
    (u : P → G) {c K C : ℝ} (hc : 0 ≤ c) (hK : 0 ≤ K)
    (hsurj : ∀ y, ∃ p, dist y (u p) ≤ c)
    (hlower : ∀ x y, dist x y ≤ K * dist (u x) (u y) + C) :
    μ.IsMulRightInvariant := by
  obtain ⟨A, hA, hzero, hfin, hratio⟩ := exists_metricFolner_sequence
    (invariantMean_of_isVirtuallyPolycyclic hP).some hfinite μ u hc hK hsurj hlower
  exact isMulRightInvariant_of_metricFolner μ A hA hzero hfin hratio

end PolycyclicRecognition

end

end OAI
