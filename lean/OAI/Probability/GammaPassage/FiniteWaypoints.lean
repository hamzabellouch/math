import OAI.Probability.GammaPassage.MovingOrigin

namespace OAI

namespace GammaFPP.IntervalTravelBridge
open PlanarFPP MeasureTheory ProbabilityTheory Filter Set Finset
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- A location-uniform finite union estimate. The common shape-test error is
at the fixed origin, while every tested location may be different. -/
theorem gamma_finite_waypoint_failure_bound
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    {ι : Type*} (J : Finset ι) (a : ι → Vertex) (C n : ℕ) (η δ : ℝ) :
    P.real {ω | ∃ j ∈ J, ¬GoodOrigin (gammaMeanNorm h hs hr)
      (cheapSlope shape rate) C η δ n (fun e => τ (shiftEdge (a j) e) ω)} ≤
      (J.card : ℝ) * P.real {ω | ¬GoodOrigin (gammaMeanNorm h hs hr)
        (cheapSlope shape rate) C η δ n (fun e => τ e ω)} := by
  classical
  let := h.probability
  let A (j : ι) := {ω | ¬GoodOrigin (gammaMeanNorm h hs hr)
    (cheapSlope shape rate) C η δ n (fun e => τ (shiftEdge (a j) e) ω)}
  have hevent : {ω | ∃ j ∈ J, ¬GoodOrigin (gammaMeanNorm h hs hr)
      (cheapSlope shape rate) C η δ n (fun e => τ (shiftEdge (a j) e) ω)} =
      ⋃ j ∈ J, A j := by
    ext ω
    constructor
    · rintro ⟨j, hj, hω⟩
      exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hj, hω⟩⟩
    · intro hω
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hω
      obtain ⟨hJ, hgood⟩ := Set.mem_iUnion.mp hj
      exact ⟨j, hJ, hgood⟩
  rw [hevent]
  have he (j : ι) : P.real (A j) =
      P.real {ω | ¬GoodOrigin (gammaMeanNorm h hs hr)
        (cheapSlope shape rate) C η δ n (fun e => τ e ω)} := by
    exact congrArg ENNReal.toReal (h.translated_event_probability (a j)
      {w | ¬GoodOrigin (gammaMeanNorm h hs hr) (cheapSlope shape rate) C η δ n w}
      (measurableSet_goodOrigin _ _ _ _ _ n).compl)
  calc
    _ ≤ ∑ j ∈ J, P.real (A j) := measureReal_biUnion_finset_le J A
    _ = _ := by simp only [he, sum_const, nsmul_eq_mul]

/-- With a fixed finite number of tests, simultaneous success has failure
probability tending to zero even at arbitrary deterministic moving locations. -/
theorem gamma_finite_waypoint_failure_tendsto
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    {ι : Type*} (J : Finset ι) (a : ℕ → ι → Vertex)
    (C : ℕ) (hC : 0 < C) (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) :
    Tendsto (fun n => P.real {ω | ∃ j ∈ J, ¬GoodOrigin (gammaMeanNorm h hs hr)
      (cheapSlope shape rate) C η δ n (fun e => τ (shiftEdge (a n j) e) ω)})
      atTop (𝓝 0) := by
  have ht := gamma_moving_goodOrigin_failure_tendsto h hs hr C hC η δ hη hδ
    (fun _ => (0 : Vertex))
  have horigin : Tendsto (fun n => P.real {ω | ¬GoodOrigin (gammaMeanNorm h hs hr)
      (cheapSlope shape rate) C η δ n (fun e => τ e ω)}) atTop (𝓝 0) := by
    simpa only [shiftEdge, zero_add] using ht
  apply squeeze_zero (fun _ => measureReal_nonneg)
    (fun n => gamma_finite_waypoint_failure_bound h hs hr J (a n) C n η δ)
  simpa only [mul_zero] using horigin.const_mul (J.card : ℝ)

end GammaFPP.IntervalTravelBridge

end OAI
