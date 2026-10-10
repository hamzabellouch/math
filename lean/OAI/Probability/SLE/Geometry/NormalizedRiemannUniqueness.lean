import OAI.Probability.SLE.Geometry.NormalizedRiemannChart
import Mathlib.Analysis.Complex.Schwarz

namespace OAI

/-! Uniqueness at a fixed derivative, in the form needed to reflect the
normalized exterior chart. Only the reference map must be onto the disk. -/
noncomputable section
open Set Complex Metric Function
open scoped Topology

namespace SLEExactGauge

lemma disk_selfMap_eq_id_of_deriv_one {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (hm : MapsTo f (ball 0 1) (ball 0 1)) (h0 : f 0=0) (hd : deriv f 0=1) :
    EqOn f id (ball 0 1) := by
  have hclosed : MapsTo f (ball 0 1) (closedBall (f 0) 1) := by
    rw [h0]
    exact hm.mono_right ball_subset_closedBall
  have h := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div hf hclosed
    (mem_ball_self zero_lt_one) (by simp [hd])
  intro z hz
  simpa only [h0,sub_zero,dslope_same,hd,smul_eq_mul,mul_one,zero_add,id_eq] using h hz

theorem riemann_chart_eq_of_deriv_eq {D : Set ℂ} (ho : IsOpen D) (h0D : (0:ℂ) ∈ D)
    {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f D) (hg : DifferentiableOn ℂ g D)
    (hfm : MapsTo f D (ball 0 1)) (hgb : BijOn g D (ball 0 1))
    (hf0 : f 0=0) (hg0 : g 0=0) (hd : deriv f 0=deriv g 0) : EqOn f g D := by
  let j := invFunOn g D
  have hjm : MapsTo j (ball 0 1) D := hgb.surjOn.mapsTo_invFunOn
  have hjd : DifferentiableOn ℂ j (ball 0 1) := by
    simpa only [hgb.image_eq] using DifferentiableOn.invFunOn hg ho hgb.injOn
  have hj0 : j 0=0 := by
    change invFunOn g D 0=0
    simpa only [hg0] using hgb.injOn.leftInvOn_invFunOn h0D
  have hjAt : HasDerivAt j (deriv g 0)⁻¹ 0 := by
    simpa only [hg0] using TauCeti.hasDerivAt_invFunOn hg ho hgb.injOn h0D
  have hgd : deriv g 0 ≠ 0 := TauCeti.deriv_ne_zero_of_injOn hg ho hgb.injOn h0D
  let H := f ∘ j
  have hHd : DifferentiableOn ℂ H (ball 0 1) := hf.comp hjd hjm
  have hHm : MapsTo H (ball 0 1) (ball 0 1) := hfm.comp hjm
  have hH0 : H 0=0 := by simp only [H,Function.comp_apply,hj0,hf0]
  have hH1 : deriv H 0=1 := by
    have hfAt : HasDerivAt f (deriv f 0) (j 0) := by
      rw [hj0]
      exact (hf.differentiableAt (ho.mem_nhds h0D)).hasDerivAt
    have he := (hfAt.comp 0 hjAt).deriv
    change deriv H 0=1
    rw [he,hd,mul_inv_cancel₀ hgd]
  have hHi := disk_selfMap_eq_id_of_deriv_one hHd hHm hH0 hH1
  intro z hz
  have hh := hHi (hgb.mapsTo hz)
  change f (invFunOn g D (g z))=g z at hh
  rwa [hgb.injOn.leftInvOn_invFunOn hz] at hh

end SLEExactGauge

end

end OAI
