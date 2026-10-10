import OAI.Probability.SLE.Loewner.InverseRectangleEnergy
import OAI.Probability.SLE.Loewner.InverseVerticalEnergy

namespace OAI

/-! A thin mapped crossing with a small physical image forces large
Dirichlet energy whenever the inverse is separated at a fixed height. -/
noncomputable section
open Set Filter Function Complex Metric MeasureTheory
open scoped Topology ENNReal

namespace SLEExactGauge

theorem initialInverse_thin_crossing_bound (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {R : ℝ} (hR : 0<R) (hp : ∀ t : unitInterval, ‖p t‖<R)
    (s : unitInterval) {a b L h δ ε : ℝ} (hab : a<b)
    (hh : 0<h) (hh1 : h≤1) (hδ : 0≤δ) (c : ℂ)
    (hx : ∀ x∈Ioo a b, |x|≤L)
    (hhigh : ∀ x∈Ioo a b, δ+ε≤
      ‖initialInverseChart p hi h0 hH s ((x:ℂ)+(h:ℂ)*I)-c‖)
    (hlow : ∀ x∈Ioo a b, ∃ y∈Ioc 0 h,
      ‖initialInverseChart p hi h0 hH s ((x:ℂ)+(y:ℂ)*I)-c‖≤ε) :
    (b-a)*δ^2≤h*(volume (closedBall (0:ℂ) (L+2+3*R))).toReal := by
  obtain ⟨hbound,hiE,hsections⟩ := initialInverse_rectangle_energy p hi h0 hH hR hp s
    a b L hh hh1 hx
  have hpoint : ∀ᵐ x : ℝ ∂volume.restrict (Ioo a b),
      δ^2≤h*(∫ y in Ioc 0 h,
        ‖deriv (initialInverseChart p hi h0 hH s) ((x:ℂ)+(y:ℂ)*I)‖^2) := by
    filter_upwards [hsections,ae_restrict_mem measurableSet_Ioo] with x hxE hxI
    exact holomorphic_vertical_separation (initialInverseChart_differentiableOn p hi h0 hH s)
      x hh hδ c (hhigh x hxI) (hlow x hxI) hxE
  have h := integral_mono_ae (integrable_const (δ^2)) (hiE.const_mul h) hpoint
  rw [integral_const,integral_const_mul] at h
  have hm : (volume.restrict (Ioo a b)).real Set.univ=b-a := by
    simp only [Measure.real,Measure.restrict_apply_univ,Real.volume_Ioo]
    exact ENNReal.toReal_ofReal (sub_pos.mpr hab).le
  simp only [smul_eq_mul,hm] at h
  exact h.trans (mul_le_mul_of_nonneg_left hbound hh.le)

end SLEExactGauge

end

end OAI
