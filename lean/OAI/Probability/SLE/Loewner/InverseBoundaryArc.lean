import OAI.Probability.SLE.Loewner.InverseBoundaryCluster
import OAI.Probability.SLE.Geometry.FiniteEnergyArcExtension

namespace OAI

/-! Endpoint values of continuously extended inverse-chart arcs lie on
the physical frontier, independently of a global boundary extension. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology

namespace SLEExactGauge

lemma inverse_limit_mem_frontier_filter {A : Type*} {l : Filter A} [l.NeBot]
    {D : Set ℂ} (hD : IsOpen D) {g f : ℂ → ℂ} (hg : ContinuousOn g D)
    (hgH : MapsTo g D upperHalfPlane) (hfD : MapsTo f upperHalfPlane D)
    (hinv : ∀ w∈upperHalfPlane, g (f w)=w)
    {w : A → ℂ} (hw : ∀ᶠ a in l, w a∈upperHalfPlane) {x : ℂ}
    (hx : x∉upperHalfPlane) (hlim : Tendsto w l (𝓝 x)) {z : ℂ}
    (hz : Tendsto (fun a => f (w a)) l (𝓝 z)) : z∈frontier D := by
  have hcl : z∈closure D := mem_closure_of_tendsto hz (hw.mono fun _ ha => hfD ha)
  have hnot : z∉D := by
    intro hzin
    have hg' := ((hg z hzin).continuousAt (hD.mem_nhds hzin)).tendsto.comp hz
    have he : Tendsto w l (𝓝 (g z)) := hg'.congr' (hw.mono fun a ha => hinv (w a) ha)
    have heq : g z=x := tendsto_nhds_unique he hlim
    exact hx (heq ▸ hgH hzin)
  exact ⟨hcl,by simpa only [hD.interior_eq] using hnot⟩

lemma inverse_arc_endpoint_mem_frontier {D : Set ℂ} (hD : IsOpen D)
    {g f : ℂ → ℂ} (hg : ContinuousOn g D)
    (hgH : MapsTo g D upperHalfPlane) (hfD : MapsTo f upperHalfPlane D)
    (hinv : ∀ w∈upperHalfPlane, g (f w)=w)
    {w c : ℝ → ℂ} (hw : Continuous w) (hc : Continuous c)
    {a b s : ℝ} (hab : a<b) (hs : s∈Icc a b)
    (hwin : MapsTo w (Ioo a b) upperHalfPlane)
    (hws : w s∉upperHalfPlane) (heq : EqOn c (f ∘ w) (Ioo a b)) :
    c s∈frontier D := by
  have hscl : s∈closure (Ioo a b) := by rwa [closure_Ioo (ne_of_lt hab)]
  have : (𝓝[Ioo a b] s).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hscl
  have hmem : ∀ᶠ θ in 𝓝[Ioo a b] s, θ∈Ioo a b := self_mem_nhdsWithin
  apply inverse_limit_mem_frontier_filter hD hg hgH hfD hinv
    (hmem.mono fun _ h => hwin h) hws
    ((hw.tendsto s).mono_left nhdsWithin_le_nhds)
  exact ((hc.tendsto s).mono_left nhdsWithin_le_nhds).congr'
    (hmem.mono fun _ hθ => heq hθ)

end SLEExactGauge

end

end OAI
