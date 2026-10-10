import OAI.Probability.SLE.Gauge.FiniteStoppedThreshold
import OAI.Probability.SLE.Mass.CanonicalMassRemaining
import OAI.Probability.SLE.Mass.CanonicalPhysicalMass
import OAI.Probability.SLE.Gauge.PrescribedCandidateCover

namespace OAI

/-! Actual adapted tests use canonical mass at the finite test endpoint.
  Terminal candidate failure implies failure of all these earlier tests. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint.CanonicalMass

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (M : CanonicalMass P κ B hBm γ G)

def prescribedBallTest (S : Ω → WithTop ℝ≥0) (z : ℂ) (r : ℝ) (b : ℝ≥0∞) : Set Ω :=
  finiteStoppedThreshold
    (fun t ω => M.process t ω (Subtype.val ⁻¹' closedBall z r)) S b

lemma prescribedBallTest_measurable
    (S : Ω → WithTop ℝ≥0)
    (hS : IsStoppingTime (Filtration.natural B (fun r =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)).stronglyMeasurable)) S)
    (z : ℂ) (r : ℝ) (b : ℝ≥0∞) :
    MeasurableSet[hS.measurableSpace] (M.prescribedBallTest S z r b) := by
  apply finiteStoppedThreshold_measurable _ _ S hS b
  intro t
  exact (Measure.measurable_coe
    (isClosed_closedBall.measurableSet.preimage measurable_subtype_coe)).comp (M.progressive t)

def prescribedTestFailures {J : ℕ} (W : Target.WienerLaw) (n : ℕ)
    (e : Fin J → ℤ×ℕ) (C c : ℝ) (z : ℂ) (S : Fin J → Ω → WithTop ℝ≥0) : Set Ω :=
  ⋂ j, (M.prescribedBallTest (S j) z (C*Target.entryRadius κ W (n,some (e j)))
    (ENNReal.ofReal (c*Target.entryValue (n,some (e j))*
      (Target.entryRadius κ W (n,some (e j)))^Target.d κ)))ᶜ

lemma prescribedTestFailures_measurable_at_end
    {J : ℕ} (W : Target.WienerLaw) (n : ℕ) (e : Fin J → ℤ×ℕ) (C c : ℝ) (z : ℂ)
    (S : Fin J → Ω → WithTop ℝ≥0)
    (hS : ∀ j, IsStoppingTime (Filtration.natural B (fun r =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)).stronglyMeasurable)) (S j))
    (T : Ω → WithTop ℝ≥0)
    (hT : IsStoppingTime (Filtration.natural B (fun r =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)).stronglyMeasurable)) T)
    (hST : ∀ j ω, S j ω≤T ω) :
    MeasurableSet[hT.measurableSpace] (M.prescribedTestFailures W n e C c z S) := by
  apply MeasurableSet.iInter
  intro j
  exact ((hS j).measurableSpace_mono hT (hST j)) _
    (M.prescribedBallTest_measurable (S j) (hS j) _ _ _).compl

lemma prescribed_missed_implies_test_failures
    {J : ℕ} (W : Target.WienerLaw) (n : ℕ) (e : Fin J → ℤ×ℕ) (C c R : ℝ)
    (K : Set ℂ) (ij : ℤ×ℤ) (S : Fin J → Ω → WithTop ℝ≥0) :
    ∀ᵐ ω ∂P,
      ij∈prescribedMissedIndices κ W n e C c R K (range (γ ω)∩K)
        (M.rational.physicalTerminal ω) →
      ω∈M.prescribedTestFailures W n e C c
        (prescribedGridCenter (Target.entryRadius κ W (n,none)) ij) S := by
  classical
  filter_upwards [M.paths] with ω hω hm
  apply mem_iInter.mpr
  intro j hj
  have htest := hj.2
  have hdom := hω.dominated ((S j ω).untopD 0)
  have hball := hdom (Subtype.val ⁻¹' closedBall
    (prescribedGridCenter (Target.entryRadius κ W (n,none)) ij)
    (C*Target.entryRadius κ W (n,some (e j))))
  have hterm := (Finset.mem_filter.mp hm).2.2 j
  rw [M.rational.physicalTerminal_apply ω isClosed_closedBall.measurableSet] at hterm
  exact (not_le_of_gt hterm) (htest.trans hball)

end SLEExactGauge.Multipoint.CanonicalMass

end

end OAI
