import OAI.Probability.SLE.Geometry.CanonicalInteriorBound
import OAI.Probability.SLE.Gauge.PrescribedInteriorCost
import OAI.Probability.SLE.Gauge.CanonicalCoverExpectation
import OAI.Probability.SLE.Gauge.ExactMomentGauge

namespace OAI

/-! Concrete finite-law canonical test failures imply the prescribed-gauge
upper bound through boundary estimates, covers, and expectations. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint.CanonicalMass
local instance prescribedUpperPathMeasurable : MeasurableSpace C(ℝ≥0,ℂ) := borel _
local instance prescribedUpperPathBorel : BorelSpace C(ℝ≥0,ℂ) := ⟨rfl⟩

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (M : CanonicalMass P κ B hBm γ G)

theorem prescribed_expectation_of_finite_failures
    (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω))
    (h0 : ∀ ω, B 0 ω=0) (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hγ : ∀ t, Measurable (fun ω => γ ω t))
    (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (hgrowth : PublishedDiskUnivalentGrowth) (W : Target.WienerLaw) (hW : Target.IsWiener W)
    (J : ℕ → ℕ) (e : ∀ n, Fin (J n) → ℤ×ℕ)
    (he : ∀ n i, (e n i).2 < Target.multiplicity κ W n (e n i).1)
    (C c R : ℝ) (hC : 3 ≤ C) (hcpos : 0<c) (hR : 0 ≤ R)
    (K : Set ℂ) (hK : IsClosed K) (hKR : K ⊆ closedBall 0 R) (hH : ∀ z∈K, 0 ≤ z.im)
    (hfailure : ∀ᶠ n in atTop, ∀ ij∈prescribedGridIndex R (Target.entryRadius κ W (n,none)) K,
      Real.exp (-(n:ℝ)) ≤ (prescribedGridCenter (Target.entryRadius κ W (n,none)) ij).im →
      M.prescribedCenteredFailure W n (e n) C c
        (prescribedGridCenter (Target.entryRadius κ W (n,none)) ij) ≤
        ENNReal.ofReal (Real.exp (-((2:ℝ)^n/16)))) :
    (∫⁻ ω, Target.hausdorff (Target.gauge κ W) (range (γ ω)∩K) ∂P) < ∞ := by
  let f := sourceTracePath γ (fun ω => (hw ω).1)
  have hf : Measurable f := source_path_measurable f hγ
  have hm1 := M.moment_one_positive hB hc h0 hκ hκ8 F hw hpublished hgrowth W hW
  have hJm (n : ℕ) (_ : 1≤n) : Target.moment κ W 1^n ≤ Target.moment κ W n :=
    M.moment_jensen hB hc h0 hκ hκ8 F hw hgrowth W hW n
  have hI := M.eventually_prescribed_interior_bound hB hc h0 hκ hκ8 F hw hpublished W
    hm1 hJm J e he C c R K hfailure
  have hcost := prescribed_missed_cost_tendsto_zero_of_interior P f hf hB hκ hκ8 G F
    (Eventually.of_forall hw) M.rational.physicalTerminal M.rational.physicalTerminal_measurable W
    J e C c R hR K hK _ hI
  exact M.rational.prescribed_cover_finite_expectation hκ hκ8 W
    (M.prescribed_gauge_admissible hB hc h0 hκ hκ8 F hw hpublished hgrowth W hW) hm1 hJm
    f hf C c R hC hcpos hR K hK hKR hH (fun n => J (n+1)) (fun n => e (n+1))
    (fun n i => he (n+1) i) (hcost.comp (tendsto_add_atTop_nat 1))

end SLEExactGauge.Multipoint.CanonicalMass

end

end OAI
