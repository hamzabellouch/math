import OAI.Probability.SLE.Gauge.PrescribedCoverExpectation
import OAI.Probability.SLE.Mass.CanonicalPhysicalMass

namespace OAI

/-! Applying the actual finite-cover reduction to canonical terminal mass
leaves precisely the expected missed-cell error to be estimated. -/
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint
local instance canonicalCoverPathMeasurable : MeasurableSpace C(ℝ≥0,ℂ) := borel _
local instance canonicalCoverPathBorel : BorelSpace C(ℝ≥0,ℂ) := ⟨rfl⟩

theorem RationalCanonicalMass.prescribed_cover_finite_expectation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (M : RationalCanonicalMass P κ B hBm γ G) (hκ : 0<κ) (hκ8 : κ<8)
    (W : Target.WienerLaw) (hg : Target.IsHausdorffGauge (Target.gauge κ W))
    (hm1 : 0<Target.moment κ W 1)
    (hJ : ∀ n, 1 ≤ n → Target.moment κ W 1^n ≤ Target.moment κ W n)
    (f : Ω → C(ℝ≥0,ℂ)) (hf : Measurable f)
    (C c R : ℝ) (hC : 3 ≤ C) (hc : 0<c) (hR : 0 ≤ R)
    (K : Set ℂ) (hK : IsClosed K) (hKR : K ⊆ closedBall 0 R)
    (hH : ∀ z∈K, 0 ≤ z.im)
    (J : ℕ → ℕ) (e : ∀ n, Fin (J n) → ℤ×ℕ)
    (he : ∀ n j, (e n j).2<Target.multiplicity κ W (n+1) (e n j).1)
    (herr : Tendsto (fun n => ∫⁻ ω,
      prescribedMissedCost f M.physicalTerminal κ W (n+1) (e n) C c R K ω ∂P)
        atTop (𝓝 0)) :
    (∫⁻ ω, Target.hausdorff (Target.gauge κ W) (range (f ω)∩K) ∂P) < ∞ := by
  refine lt_of_le_of_lt (expected_prescribed_hausdorff_le_of_missed_cost P hκ W hg hm1 hJ
    f hf M.physicalTerminal M.physicalTerminal_measurable C c R hC hc hR K hK hKR hH J e he herr) ?_
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (M.physicalTerminal_bounded_mean_lt_top hκ hκ8 (R+3+C))

end SLEExactGauge.Multipoint

end

end OAI
