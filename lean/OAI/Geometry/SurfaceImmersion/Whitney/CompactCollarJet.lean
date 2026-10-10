import OAI.Geometry.SurfaceImmersion.Whitney.HomotopyCollarDerivative

namespace OAI

/-! Uniform injectivity of collar jets near a compact family of
 transverse axis frames. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem compact_collar_jet {c : ℝ → W} {V : ℝ × ℝ → W}
    (hc : ContDiff ℝ ∞ c) (hV : ContDiff ℝ ∞ V) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K)
    (hI : ∀ z ∈ K, Function.Injective (homotopyCollarJet c V z.1 z.2 0 0)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K, ∀ u w : ℝ, |u| < δ → |w| < δ →
      Function.Injective (homotopyCollarJet c V z.1 z.2 u w) := by
  let O : Set ((ℝ × ℝ) × Base) := {z | Function.Injective
    (homotopyCollarJet c V z.1.1 z.1.2 (z.2 0) (z.2 1))}
  have hO : IsOpen O := ContinuousLinearMap.isOpen_injective.preimage
    (homotopyCollarJet_continuous hc hV)
  have haxis : K ×ˢ ({0} : Set Base) ⊆ O := by
    rintro ⟨z,x⟩ ⟨hz,hx⟩
    obtain rfl : x = 0 := hx
    exact hI z hz
  obtain ⟨U,B,hU,hB,hKU,h0B,hUB⟩ := generalized_tube_lemma hK isCompact_singleton hO haxis
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hB 0 (h0B (by simp))
  refine ⟨δ,hδ,?_⟩
  intro z hz u w hu hw
  have hn : ‖(![u,w] : Base)‖ < δ := by
    apply (pi_norm_lt_iff hδ).mpr
    intro i
    fin_cases i
    · change |u| < δ
      exact hu
    · change |w| < δ
      exact hw
  have hm : (![u,w] : Base) ∈ B := hball (by simpa only [mem_ball,dist_zero_right] using hn)
  have hzO : (z,(![u,w] : Base)) ∈ O := hUB ⟨hKU hz,hm⟩
  exact hzO

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
