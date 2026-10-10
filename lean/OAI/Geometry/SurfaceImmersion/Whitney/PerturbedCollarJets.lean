import OAI.Geometry.SurfaceImmersion.Whitney.CompactCollarJet

namespace OAI

/-! Compact transverse frames also tolerate a small arbitrary derivative
remainder, as required when matching actual collars. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem perturbed_collar_jets {c : ℝ → W} {V : ℝ × ℝ → W}
    (hc : ContDiff ℝ ∞ c) (hV : ContDiff ℝ ∞ V) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K)
    (hI : ∀ z ∈ K, Function.Injective (homotopyCollarJet c V z.1 z.2 0 0)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K, ∀ u w : ℝ, ∀ E : Base →L[ℝ] W,
      |u| < δ → |w| < δ → ‖E‖ < δ →
      Function.Injective (homotopyCollarJet c V z.1 z.2 u w + E) := by
  let P := Base × (Base →L[ℝ] W)
  let J : (ℝ × ℝ) × P → (Base →L[ℝ] W) := fun z =>
    homotopyCollarJet c V z.1.1 z.1.2 (z.2.1 0) (z.2.1 1) + z.2.2
  have hJ : Continuous J := by
    have hq : Continuous (fun z : (ℝ × ℝ) × P => (z.1,z.2.1)) :=
      continuous_fst.prodMk continuous_snd.fst
    exact ((homotopyCollarJet_continuous hc hV).comp hq).add continuous_snd.snd
  let O := J ⁻¹' {L : Base →L[ℝ] W | Function.Injective L}
  have hO : IsOpen O := ContinuousLinearMap.isOpen_injective.preimage hJ
  have haxis : K ×ˢ ({0} : Set P) ⊆ O := by
    rintro ⟨z,x⟩ ⟨hz,hx⟩
    obtain rfl : x = 0 := hx
    change Function.Injective (homotopyCollarJet c V z.1 z.2 0 0 + (0 : Base →L[ℝ] W))
    simpa only [add_zero] using hI z hz
  obtain ⟨U,B,hU,hB,hKU,h0B,hUB⟩ := generalized_tube_lemma hK isCompact_singleton hO haxis
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hB 0 (h0B (by simp))
  refine ⟨δ,hδ,?_⟩
  intro z hz u w E hu hw hE
  have hn : ‖(![u,w] : Base)‖ < δ := by
    apply (pi_norm_lt_iff hδ).mpr
    intro i
    fin_cases i
    · change |u| < δ
      exact hu
    · change |w| < δ
      exact hw
  have hpair : ‖((![u,w] : Base),E)‖ < δ := by
    rw [Prod.norm_def,max_lt_iff]
    exact ⟨hn,hE⟩
  have hm : ((![u,w] : Base),E) ∈ B :=
    hball (by simpa only [mem_ball,dist_zero_right] using hpair)
  have hzO : (z,((![u,w] : Base),E)) ∈ O := hUB ⟨hKU hz,hm⟩
  exact hzO

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
