import OAI.Probability.SLE.Gauge.PrescribedTestPast
import OAI.Probability.SLE.Gauge.PrescribedCanonicalTests
import OAI.Probability.SLE.Gauge.CanonicalBatchFailure
import OAI.Probability.SLE.Loewner.ActualRadiusStopsRegular
import OAI.Probability.SLE.Mass.DenseCoverMassTests

namespace OAI

/-! The exact chronological batch is adapted to its preceding endpoints.
  The intervening gap remains available for finite-centered angle mixing;
  the half-probability bound is conditioned before that gap. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint.CanonicalMass

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (M : CanonicalMass P κ B hBm γ G)

theorem prescribed_adapted_batch_failure
    (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω))
    (h0 : ∀ ω, B 0 ω=0) (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (hgrowth : PublishedDiskUnivalentGrowth) (W : Target.WienerLaw) (hW : Target.IsWiener W)
    {n J : ℕ} (hn : 3≤n) (e : Fin J → ℤ×ℕ) (hi : Function.Injective e)
    (he : ∀ kj, kj∈range e ↔ kj.2 < Target.multiplicity κ W n kj.1)
    (horder : StrictMono (fun i => Target.entryPosition κ W (n,some (e i))))
    (C c A : ℝ) (z : ℂ) (hz : z∈upperHalfPlane)
    (hl : ∀ o, 0 ≤ Target.entryPhysicalLevel κ W (n,o) A z)
    (V : ℝ) (hV : 0 ≤ V)
    (hstep : ∀ (i : Fin J) (E : Set Ω),
      MeasurableSet[(actual_radiusLevelTime_stopping hB
        (fun t => (hBm.of_uncurry_left : Measurable (B t))) hBm hc h0
        κ hκ hκ8 γ G F hw z hz (Target.prescribedTestPastLevel κ W n e A z i.val)
        (Target.prescribedTestPastLevel_nonneg hκ W n e A z hl i.val)).measurableSpace] E →
      ENNReal.ofReal
        ((centeredDiskLaw P κ B hc (4*(Target.batchLevel κ W n:ℝ)/κ)).real
          {p | MomentBatches.dyadic (e i).1 ≤
            M.diskAtRadius p.1 (4*(Target.batchLevel κ W n:ℝ)/κ) p.2}/2)*
        finiteCenteredLaw P κ B γ G z V E ≤
      finiteCenteredLaw P κ B γ G z V (E∩M.prescribedBallTest
        (fun ω => radiusLevelTime (γ ω) (G ω) z
          (Target.entryPhysicalLevel κ W (n,some (e i)) A z+2*Target.a κ*(Target.batchLevel κ W n:ℝ)))
        z (C*Target.entryRadius κ W (n,some (e i)))
        (ENNReal.ofReal (c*Target.entryValue (n,some (e i))*
          (Target.entryRadius κ W (n,some (e i)))^Target.d κ)))) :
    finiteCenteredLaw P κ B γ G z V
      (M.prescribedTestFailures W n e C c z
        (fun i ω => radiusLevelTime (γ ω) (G ω) z
          (Target.entryPhysicalLevel κ W (n,some (e i)) A z+2*Target.a κ*(Target.batchLevel κ W n:ℝ)))) ≤
      ENNReal.ofReal (Real.exp (-((2:ℝ)^n/16))) := by
  classical
  let hm (t : ℝ≥0) : Measurable (B t) := hBm.of_uncurry_left
  let ℱ := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  let u := Target.prescribedTestPastLevel κ W n e A z
  have hu (j : ℕ) : 0 ≤ u j :=
    Target.prescribedTestPastLevel_nonneg hκ W n e A z hl j
  let S (j : ℕ) (ω : Ω) : WithTop ℝ≥0 := radiusLevelTime (γ ω) (G ω) z (u j)
  have hS (j : ℕ) : IsStoppingTime ℱ (S j) :=
    actual_radiusLevelTime_stopping hB hm hBm hc h0 κ hκ hκ8 γ G F hw z hz (u j) (hu j)
  have hm1 := M.moment_positive hB hc h0 hκ hκ8 F hw hpublished hgrowth W hW 1
  have hJn := M.moment_jensen hB hc h0 hκ hκ8 F hw hgrowth W hW n
  have hei (i) : (e i).2 < Target.multiplicity κ W n (e i).1 := (he _).mp ⟨i,rfl⟩
  have hum : Monotone u := Target.prescribedTestPastLevel_monotone hκ W (by omega) hm1 hJn e hei horder A z hl
  have hSm (ω) : Monotone (fun j => S j ω) := by
    intro i j hij
    exact radiusLevelTime_mono ((hc ω).const_mul _) (hw ω) z (hu i) (hum hij)
  let ℱc := clockStopFiltration ℱ S hS hSm
  let T (i : Fin J) (ω : Ω) : WithTop ℝ≥0 := radiusLevelTime (γ ω) (G ω) z
    (Target.entryPhysicalLevel κ W (n,some (e i)) A z+2*Target.a κ*(Target.batchLevel κ W n:ℝ))
  have hTlevel (i : Fin J) : 0 ≤ Target.entryPhysicalLevel κ W (n,some (e i)) A z+
      2*Target.a κ*(Target.batchLevel κ W n:ℝ) := by
    have ha := Target.internal_a_pos hκ
    exact add_nonneg (hl _) (by positivity)
  have hT (i : Fin J) : IsStoppingTime ℱ (T i) :=
    actual_radiusLevelTime_stopping hB hm hBm hc h0 κ hκ hκ8 γ G F hw z hz _ (hTlevel i)
  let := finiteCenteredLaw_probability hB κ hκ hκ8 γ G F (Eventually.of_forall hw) z hz V hV
  apply M.ordered_batch_failure_bound hB hc h0 hκ hκ8 F hw hpublished hgrowth W hW
    (finiteCenteredLaw P κ B γ G z V) ℱc hn e hi he
    (fun i => M.prescribedBallTest (T i) z (C*Target.entryRadius κ W (n,some (e i)))
      (ENNReal.ofReal (c*Target.entryValue (n,some (e i))*
        (Target.entryRadius κ W (n,some (e i)))^Target.d κ)))
  · intro i
    apply (hT i).measurableSpace_mono (hS (i.val+1)) _ _
      (M.prescribedBallTest_measurable (T i) (hT i) _ _ _)
    intro ω
    change radiusLevelTime (γ ω) (G ω) z _ ≤ radiusLevelTime (γ ω) (G ω) z _
    dsimp only [u]
    rw [Target.prescribedTestPastLevel_succ W n e A z i]
  · intro i E hE
    exact hstep i E hE

end SLEExactGauge.Multipoint.CanonicalMass

end

end OAI
