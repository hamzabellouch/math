import OAI.Probability.SLE.Geometry.HalfPlaneNormalizedUniqueness

namespace OAI

/-! Normalized half-plane uniqueness using only the vertical asymptotics
preserved by bounded-capacity limits. -/
noncomputable section
open Set Filter Complex Function
open scoped Topology

namespace SLEExactGauge

lemma halfPlane_height_of_vertical_normalization {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F upperHalfPlane) (hm : MapsTo F upperHalfPlane upperHalfPlane)
    (hn : Tendsto (fun n : ℕ => F (verticalInfinity n)/(((n:ℝ)+1:ℝ):ℂ))
      atTop (𝓝 I)) {z : ℂ} (hz : z∈upperHalfPlane) : z.im≤(F z).im := by
  apply halfPlane_julia_at_infinity hF hm (fun n : ℕ => (n:ℝ)+1)
    (fun n => by positivity) _ hn hz
  exact tendsto_inv_atTop_zero.comp verticalHeights_tendsto

lemma vertical_halfPlane_left_inverse_eq_id {G F : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G upperHalfPlane) (hF : DifferentiableOn ℂ F upperHalfPlane)
    (hGm : MapsTo G upperHalfPlane upperHalfPlane) (hFm : MapsTo F upperHalfPlane upperHalfPlane)
    (hFG : ∀ z∈upperHalfPlane, F (G z)=z)
    (hGn : Tendsto (fun n : ℕ => G (verticalInfinity n)/(((n:ℝ)+1:ℝ):ℂ)) atTop (𝓝 I))
    (hFn : Tendsto (fun n : ℕ => F (verticalInfinity n)/(((n:ℝ)+1:ℝ):ℂ)) atTop (𝓝 I))
    (hG0 : Tendsto (fun n : ℕ => G (verticalInfinity n)-verticalInfinity n) atTop (𝓝 0)) :
    EqOn G id upperHalfPlane := by
  have him (z : ℂ) (hz : z∈upperHalfPlane) : (G z-z).im=0 := by
    have h1 := halfPlane_height_of_vertical_normalization hG hGm hGn hz
    have h2 := halfPlane_height_of_vertical_normalization hF hFm hFn (hGm hz)
    rw [hFG z hz] at h2
    simp only [sub_im]
    linarith
  have hc : IsConnected upperHalfPlane :=
    ⟨⟨I,by simp [upperHalfPlane]⟩,(convex_halfSpace_im_gt (0:ℝ)).isPreconnected⟩
  have ha := (hG.sub differentiableOn_id).analyticOnNhd isOpen_upperHalfPlane
  obtain ⟨c,hc⟩ := ha.eq_const_of_im_eq_const him isOpen_upperHalfPlane hc
  have ht : Tendsto (fun _ : ℕ => c) atTop (𝓝 0) := by
    apply hG0.congr
    intro n
    exact hc _ (verticalInfinity_mem n)
  have hc0 : c=0 := tendsto_nhds_unique tendsto_const_nhds ht
  intro z hz
  exact sub_eq_zero.mp ((hc z hz).trans hc0)

end SLEExactGauge

end

end OAI
