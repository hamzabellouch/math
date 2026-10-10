import OAI.Probability.SLE.Loewner.HydrodynamicHeight
import Mathlib.Analysis.Complex.OpenMapping

namespace OAI

/-! A normalized half-plane map with a normalized holomorphic inverse is
the identity. The height comparison fixes its imaginary part, and the
normalization removes the remaining real translation. -/
noncomputable section
open Set Filter Complex Function Metric
open scoped Topology

namespace SLEExactGauge

theorem normalized_halfPlane_left_inverse_eq_id {G F : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G upperHalfPlane) (hF : DifferentiableOn ℂ F upperHalfPlane)
    (hGm : MapsTo G upperHalfPlane upperHalfPlane) (hFm : MapsTo F upperHalfPlane upperHalfPlane)
    (hFG : ∀ z ∈ upperHalfPlane, F (G z)=z)
    (hGn : Tendsto (fun z : ℂ => G z/z) (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 1))
    (hFn : Tendsto (fun z : ℂ => F z/z) (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 1))
    (hG0 : Tendsto (fun z : ℂ => G z-z) (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 0)) :
    EqOn G id upperHalfPlane := by
  have him (z : ℂ) (hz : z ∈ upperHalfPlane) : (G z-z).im=0 := by
    have h1 := normalized_halfPlane_height hG hGm hGn hz
    have h2 := normalized_halfPlane_height hF hFm hFn (hGm hz)
    rw [hFG z hz] at h2
    simp only [sub_im]
    linarith
  have hc : IsConnected upperHalfPlane :=
    ⟨⟨I,by simp [upperHalfPlane]⟩,(convex_halfSpace_im_gt (0:ℝ)).isPreconnected⟩
  have ha : AnalyticOnNhd ℂ (fun z => G z-z) upperHalfPlane :=
    (hG.sub differentiableOn_id).analyticOnNhd isOpen_upperHalfPlane
  obtain ⟨c,hc⟩ := ha.eq_const_of_im_eq_const him isOpen_upperHalfPlane hc
  have ht : Tendsto (fun _ : ℕ => c) atTop (𝓝 0) := by
    apply (hG0.comp verticalInfinity_tendsto).congr
    intro n
    exact hc _ (verticalInfinity_mem n)
  have hc0 : c=0 := tendsto_nhds_unique tendsto_const_nhds ht
  intro z hz
  exact sub_eq_zero.mp ((hc z hz).trans hc0)

end SLEExactGauge

end

end OAI
