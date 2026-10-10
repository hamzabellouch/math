import OAI.Probability.SLE.Geometry.NormalizedRiemannUniqueness
import Mathlib.Analysis.Calculus.Deriv.Star

namespace OAI

/-! The positive-real derivative normalization makes the conformal chart
of a reflection-invariant domain commute with complex conjugation. -/
noncomputable section
open Set Complex Metric Function
open scoped Topology ComplexConjugate

namespace SLEExactGauge

theorem normalized_riemann_chart_conj {D : Set ℂ}
    (ho : IsOpen D) (h0D : (0:ℂ) ∈ D) (hD : MapsTo conj D D)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f D) (hb : BijOn f D (ball 0 1))
    (h0 : f 0=0) {a : ℝ} (hd : deriv f 0=(a:ℂ)) :
    ∀ z ∈ D, f (conj z)=conj (f z) := by
  let g := conj ∘ f ∘ conj
  have hgd : DifferentiableOn ℂ g D := by
    intro z hz
    have hh := (hf.differentiableAt (ho.mem_nhds (hD hz))).conj_conj
    simpa only [conj_conj] using hh.differentiableWithinAt
  have hgm : MapsTo g D (ball 0 1) := by
    intro z hz
    have hh := hb.mapsTo (hD hz)
    simpa only [g,Function.comp_apply,mem_ball,dist_zero_right,norm_conj] using hh
  have hg0 : g 0=0 := by simp [g,h0]
  have hgder : deriv g 0=deriv f 0 := by
    dsimp only [g]
    rw [deriv_conj_conj]
    simp only [Function.comp_apply,map_zero,hd,conj_ofReal]
  have he := riemann_chart_eq_of_deriv_eq ho h0D hgd hf hgm hb hg0 h0 hgder
  intro z hz
  have hh := congrArg conj (he hz)
  simpa only [g,Function.comp_apply,conj_conj] using hh

lemma reflectedArcSet_conj (p : C(unitInterval,ℂ)) :
    MapsTo conj (reflectedArcSet p) (reflectedArcSet p) := by
  intro z hz
  rcases hz with hz|⟨w,hw,rfl⟩
  · exact Or.inr ⟨z,hz,rfl⟩
  · rw [conj_conj]
    exact Or.inl hw

lemma invertedExterior_conj {K : Set ℂ} (hK : MapsTo conj K K) :
    MapsTo conj (invertedExterior K) (invertedExterior K) := by
  intro z hz
  rcases hz with rfl|hz
  · exact Or.inl (map_zero conj)
  · right
    intro h
    apply hz
    have hh := hK h
    simpa only [map_inv₀,conj_conj] using hh

end SLEExactGauge

end

end OAI
