import OAI.Probability.SLE.Gauge.PrescribedCoverEvents
import OAI.Probability.SLE.Gauge.PrescribedCoverLimits
import OAI.Probability.SLE.Geometry.BoundedTerminalMean

namespace OAI

/-! The actual prescribed finite covers reduce the Hausdorff expectation
to the fixed terminal-mass charge and vanishing expected missed-cell cost.
The stochastic missed-cell estimate is kept explicit in this reduction. -/
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
local instance prescribedExpectationPathMeasurable : MeasurableSpace C(ℝ≥0,ℂ) := borel _
local instance prescribedExpectationPathBorel : BorelSpace C(ℝ≥0,ℂ) := ⟨rfl⟩

def prescribedMissedCost {Ω : Type*} (f : Ω → C(ℝ≥0,ℂ)) (ν : Ω → Measure ℂ)
    (κ : ℝ) (W : Target.WienerLaw) (n : ℕ) {J : ℕ} (e : Fin J → ℤ×ℕ)
    (C c R : ℝ) (K : Set ℂ) (ω : Ω) : ℝ≥0∞ :=
  (prescribedMissedIndices κ W n e C c R K (range (f ω)∩K) (ν ω)).card *
    ENNReal.ofReal (36*(n:ℝ)*(Target.entryRadius κ W (n,none))^Target.d κ)

theorem expected_prescribed_hausdorff_le_of_missed_cost
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {κ : ℝ} (hκ : 0<κ) (W : Target.WienerLaw)
    (hg : Target.IsHausdorffGauge (Target.gauge κ W))
    (hm1 : 0<Target.moment κ W 1)
    (hJ : ∀ n, 1 ≤ n → Target.moment κ W 1^n ≤ Target.moment κ W n)
    (f : Ω → C(ℝ≥0,ℂ)) (hf : Measurable f)
    (ν : Ω → Measure ℂ) (hν : Measurable ν)
    (C c R : ℝ) (hC : 3 ≤ C) (hc : 0<c) (hR : 0 ≤ R)
    (K : Set ℂ) (hK : IsClosed K) (hKR : K ⊆ closedBall 0 R)
    (hH : ∀ z∈K, 0 ≤ z.im)
    (J : ℕ → ℕ) (e : ∀ n, Fin (J n) → ℤ×ℕ)
    (he : ∀ n j, (e n j).2<Target.multiplicity κ W (n+1) (e n j).1)
    (herr : Tendsto (fun n => ∫⁻ ω, prescribedMissedCost f ν κ W (n+1) (e n) C c R K ω ∂P)
      atTop (𝓝 0)) :
    (∫⁻ ω, Target.hausdorff (Target.gauge κ W) (range (f ω)∩K) ∂P) ≤
      ENNReal.ofReal ((8*C)^2/c)*(∫⁻ ω, ν ω (closedBall 0 (R+3+C)) ∂P) := by
  let A := ENNReal.ofReal ((8*C)^2/c)
  let Q := closedBall (0:ℂ) (R+3+C)
  let error (n : ℕ) := prescribedMissedCost f ν κ W (n+1) (e n) C c R K
  let Z (n : ℕ) (ω : Ω) := A*ν ω Q + error n ω
  have hm (n : ℕ) : Measurable (error n) :=
    prescribed_missed_cost_measurable f hf ν hν κ W (n+1) (e n) C c R K hK _
  have hZ (n : ℕ) : AEMeasurable (Z n) P :=
    ((measurable_const.mul ((Measure.measurable_coe isClosed_closedBall.measurableSet).comp hν)).add (hm n)).aemeasurable
  let δ (n : ℕ) := ENNReal.ofReal (8*C*Real.exp (-((n+1:ℕ):ℝ)^2))
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have h := (ENNReal.continuous_ofReal.tendsto 0).comp
      ((prescribed_cover_diameter_tendsto_zero C).comp (tendsto_add_atTop_nat 1))
    simpa only [ENNReal.ofReal_zero,Function.comp_def] using h
  have hcover : ∀ᵐ ω ∂P, ∀ n, ∃ (N : ℕ) (U : Fin N → Set ℂ),
      range (f ω)∩K ⊆ ⋃ i,U i ∧ (∀ i,ediam (U i) ≤ δ n) ∧
        ∑ i, extendedGauge (Target.gauge κ W) (ediam (U i)) ≤ Z n ω := by
    apply Eventually.of_forall
    intro ω n
    exact prescribed_candidates_finite_cover hκ W hg (by omega) hm1 (hJ (n+1) (by omega))
      (e n) (he n) C c R hC hc hR K (range (f ω)∩K) hKR hH inter_subset_right (ν ω)
  have hcost : Tendsto (fun n => ∫⁻ ω, Z n ω ∂P) atTop
      (𝓝 (A*(∫⁻ ω,ν ω Q ∂P))) := by
    have heq (n) : (∫⁻ ω,Z n ω ∂P) = A*(∫⁻ ω,ν ω Q ∂P) + ∫⁻ ω,error n ω ∂P := by
      dsimp only [Z]
      rw [lintegral_add_right' _ (hm n).aemeasurable,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    simp_rw [heq]
    simpa only [add_zero] using tendsto_const_nhds.add herr
  simp_rw [Target.hausdorff_eq_hausdorffGauge]
  exact expected_hausdorff_le_of_finite_cover_envelopes P (Target.gauge κ W)
    (fun ω => range (f ω)∩K) δ hδ Z hZ hcover _ (le_of_eq hcost.liminf_eq)

end SLEExactGauge

end

end OAI
