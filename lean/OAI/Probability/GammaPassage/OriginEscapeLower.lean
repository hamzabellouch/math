import OAI.Probability.GammaPassage.OriginEscape

namespace OAI

namespace GammaFPP
open PlanarFPP MeasureTheory Filter
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

lemma gammaMeanNorm_lower_euclidean
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (v : Plane) : cheapSlope shape rate * ‖v‖ ≤ gammaMeanNorm h hs hr v :=
  (mul_le_mul_of_nonneg_left (RealDirectionBridge.plane_norm_le_coordinates v)
    (cheapSlope_pos hs hr).le).trans (gammaMeanNorm_lower h hs hr v)

theorem gammaMeanNorm_exists_positive_lower
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate) :
    ∃ α : ℝ, 0 < α ∧ ∀ v, α*‖v‖ ≤ gammaMeanNorm h hs hr v :=
  ⟨cheapSlope shape rate, cheapSlope_pos hs hr, gammaMeanNorm_lower_euclidean h hs hr⟩

/-- Origin escape with the positive coefficient proved from the actual Gamma
mean lower bound, rather than supplied as an additional hypothesis. -/
theorem GammaEnvironment.ae_eventually_origin_escape
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᵐ ω ∂P, ∀ᶠ s : ℝ in atTop, ∀ z : Vertex,
      δ*s/3 ≤ ‖RealDirectionBridge.latticeEmbed z‖ →
      cheapSlope shape rate*δ*s/6 ≤ passageTime (fun e => τ e ω) 0 z :=
  IntervalTravelBridge.ae_eventually_origin_escape h hs hr (cheapSlope shape rate) δ
    (cheapSlope_pos hs hr) hδ (gammaMeanNorm_lower_euclidean h hs hr)

end GammaFPP

end OAI
