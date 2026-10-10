import OAI.Probability.GammaPassage.TubeDeterministic

namespace OAI

namespace GammaFPP.IntervalTravelBridge
open PlanarFPP GammaFPP.RealDirectionBridge MeasureTheory ProbabilityTheory Set Finset Filter
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

theorem gamma_tube_failure_bound
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (β : ℝ) (hβ : 0 ≤ β)
    (hlip : ∀ v u, |gammaMeanNorm h hs hr v-gammaMeanNorm h hs hr u| ≤ β*‖v-u‖)
    (p q : Vertex) (B C n : ℕ) (hB : 0 < B) (D η δ κ : ℝ)
    (hdist : ‖latticeEmbed (q-p)‖ ≤ D*n)
    (hshortdist : D*n/(B : ℝ)+4 ≤ (C : ℝ)*n)
    (hshortcost : β*(D*n)/(B : ℝ)+4*β+κ*n+1 ≤ cheapSlope shape rate*δ*n/6)
    (htotal : (B : ℝ)*(4*β+κ*n+1) ≤ η*n)
    (htube : δ*n/3+2 ≤ δ*n) :
    P.real {ω | ¬LocalTravel (gammaMeanNorm h hs hr) η δ n p q (fun e => τ e ω)} ≤
      (B : ℝ)*P.real {ω | ¬GoodOrigin (gammaMeanNorm h hs hr)
        (cheapSlope shape rate) C κ δ n (fun e => τ e ω)} := by
  let := h.probability
  have hsub : {ω | ¬LocalTravel (gammaMeanNorm h hs hr) η δ n p q (fun e => τ e ω)} ⊆
      {ω | ∃ j ∈ range B, ¬GoodOrigin (gammaMeanNorm h hs hr)
        (cheapSlope shape rate) C κ δ n (fun e => τ (shiftEdge (waypoint p q B j) e) ω)} := by
    intro ω hω
    by_contra hn
    apply hω
    apply localTravel_of_waypoint_tests _ _ (gammaMeanNorm_laws h hs hr) β hβ hlip
      p q B C n hB (cheapSlope shape rate) D η δ κ hdist hshortdist hshortcost htotal htube
    intro j hj
    by_contra hjbad
    exact hn ⟨j, mem_range.mpr hj, hjbad⟩
  refine (measureReal_mono hsub).trans ?_
  simpa only [card_range] using gamma_finite_waypoint_failure_bound h hs hr
    (range B) (waypoint p q B) C n κ δ

/-- Uniform probability statement for all deterministic endpoint pairs at each
large integer scale. It is NOT one event of simultaneous success for all pairs. -/
theorem gamma_tube_travel_nat
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (D η δ : ℝ) (hD : 0 < D) (hη : 0 < η) (hδ : 0 < δ) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ p q : Vertex,
      ‖latticeEmbed (q-p)‖ ≤ D*n →
      P.real {ω | ¬LocalTravel (gammaMeanNorm h hs hr) η δ n p q (fun e => τ e ω)} < ε := by
  obtain ⟨β,hβ,hlip⟩ := timeConstantNorm_lipschitz_bound _ (gammaMeanNorm_laws h hs hr)
  obtain ⟨B,C,κ,hB,hC,hκ,hparams⟩ := localTravel_parameters
    (cheapSlope shape rate) β D η δ (cheapSlope_pos hs hr) hβ.le hD hη hδ
  have ht := gamma_moving_goodOrigin_failure_tendsto h hs hr C hC κ δ hκ hδ
    (fun _ => (0 : Vertex))
  have ht' : Tendsto (fun n => (B : ℝ)*P.real {ω | ¬GoodOrigin (gammaMeanNorm h hs hr)
      (cheapSlope shape rate) C κ δ n (fun e => τ e ω)}) atTop (𝓝 0) := by
    simpa only [shiftEdge, zero_add, mul_zero] using ht.const_mul (B : ℝ)
  intro ε hε
  filter_upwards [hparams, ht'.eventually (gt_mem_nhds hε)] with n hn hprob
  intro p q hpq
  exact (gamma_tube_failure_bound h hs hr β hβ.le hlip p q B C n hB D η δ κ hpq
    hn.1 hn.2.1 hn.2.2.1 hn.2.2.2).trans_lt hprob

end GammaFPP.IntervalTravelBridge

end OAI
