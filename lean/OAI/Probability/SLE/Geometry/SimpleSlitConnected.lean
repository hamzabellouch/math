import OAI.Probability.SLE.Geometry.HalfPlaneExteriorConnected

namespace OAI

/-! The domain left by an arbitrary finite simple attached arc is
connected, and its complement is connected and unbounded. These are the
topological inputs for constructing its normalized conformal charts. -/
noncomputable section
open Set Complex Metric

namespace SLEExactGauge

theorem simple_arc_halfPlane_complement_connected
    (p : C(unitInterval,ℂ)) (hi : Function.Injective p) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane) :
    IsConnected (upperHalfPlane \ range p) :=
  halfPlane_complement_connected_of_unbounded_components
    (isCompact_range p.continuous).isBounded
    (fun _ hz => simple_arc_halfPlane_component_unbounded p hi h0 hH hz)

theorem attached_arc_domain_complement_preconnected
    (p : C(unitInterval,ℂ)) (h0 : p 0=0) :
    IsPreconnected (upperHalfPlane \ range p)ᶜ := by
  have he : (upperHalfPlane \ range p)ᶜ = {z : ℂ | z.im ≤ 0} ∪ range p := by
    ext z
    change (¬ (0 < z.im ∧ z ∉ range p)) ↔ z.im ≤ 0 ∨ z ∈ range p
    simp only [not_and_or,not_lt,not_not]
  rw [he]
  exact (convex_halfSpace_im_le (0:ℝ)).isPreconnected.union 0 (by simp)
    (by rw [← h0]; exact mem_range_self 0)
    (isPreconnected_range p.continuous)

theorem attached_arc_domain_complement_unbounded (p : C(unitInterval,ℂ)) :
    ¬ Bornology.IsBounded (upperHalfPlane \ range p)ᶜ := by
  intro hb
  obtain ⟨R,hR,hbound⟩ := hb.subset_ball_lt 0 (0:ℂ)
  have hz : -((R+1:ℝ):ℂ)*I ∈ (upperHalfPlane \ range p)ᶜ := by
    intro hz
    have hi := hz.1
    change 0 < (-((R+1:ℝ):ℂ)*I).im at hi
    simp only [mul_im,neg_re,ofReal_re,I_im,neg_im,ofReal_im,I_re,
      mul_one,neg_zero,mul_zero,add_zero] at hi
    linarith
  have hn := hbound hz
  simp only [mem_ball,dist_zero_right,norm_mul,norm_neg,Complex.norm_real,
    Real.norm_eq_abs,norm_I,mul_one,abs_of_pos (by linarith : 0 < R+1)] at hn
  linarith

end SLEExactGauge

end

end OAI
