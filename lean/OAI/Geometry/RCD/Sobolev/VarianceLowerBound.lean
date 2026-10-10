import Mathlib

namespace OAI

/-! # The scalar estimate turning variance differentiation into a gradient bound -/

open Set

namespace RegularPointCoordinates

/-- A weighted differential inequality yields a uniform endpoint estimate.
The exponential constant is deliberately sufficient for short-time use. -/
theorem variance_lower_bound {F : ℝ → ℝ} {K T E : ℝ} (hT : 0 < T) (hE : 0 ≤ E)
    (hc : ContinuousOn F (Icc 0 T))
    (hd : ∀ s ∈ Ioo 0 T, ∃ G : ℝ, HasDerivAt F (2*G) s ∧
      E ≤ Real.exp (-2*K*s)*G) :
    2*T*Real.exp (-2*|K| *T)*E ≤ F T-F 0 := by
  have hbound (s : ℝ) (hs : s ∈ Ioo 0 T) (G : ℝ)
      (hG : E ≤ Real.exp (-2*K*s)*G) :
      2*Real.exp (-2*|K| *T)*E ≤ 2*G := by
    have hinv : Real.exp (2*K*s)*Real.exp (-2*K*s) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    have hG' : Real.exp (2*K*s)*E ≤ G := by
      have hm := mul_le_mul_of_nonneg_left hG (Real.exp_pos (2*K*s)).le
      calc
        _ ≤ Real.exp (2*K*s)*(Real.exp (-2*K*s)*G) := hm
        _ = G := by rw [← mul_assoc,hinv,one_mul]
    have harg : -2*|K| *T ≤ 2*K*s := by
      have h1 := mul_nonneg (abs_nonneg K) (sub_nonneg.mpr hs.2.le)
      have h2 := mul_nonneg (by linarith [neg_abs_le K] : 0 ≤ K+|K|) hs.1.le
      nlinarith
    have hmono := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr harg) hE
    linarith
  have hdiff : DifferentiableOn ℝ F (interior (Icc 0 T)) := by
    rw [interior_Icc]
    intro s hs
    exact (hd s hs).choose_spec.1.differentiableAt.differentiableWithinAt
  have hlower : ∀ s ∈ interior (Icc 0 T), 2*Real.exp (-2*|K| *T)*E ≤ deriv F s := by
    rw [interior_Icc]
    intro s hs
    obtain ⟨G,hG,hGE⟩ := hd s hs
    rw [hG.deriv]
    exact hbound s hs G hGE
  have hh := (convex_Icc (0:ℝ) T).mul_sub_le_image_sub_of_le_deriv hc hdiff hlower
    0 ⟨le_rfl,hT.le⟩ T ⟨hT.le,le_rfl⟩ hT.le
  nlinarith

end RegularPointCoordinates

end OAI
