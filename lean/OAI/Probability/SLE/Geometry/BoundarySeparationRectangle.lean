import OAI.Probability.SLE.Geometry.ThinCrossingEnergy

namespace OAI

/-! A nonconstant continuous boundary value remains separated on a
small upper rectangle. -/
noncomputable section
open Set Filter Function Complex Metric MeasureTheory
open scoped Topology

namespace SLEExactGauge

lemma boundary_separation_rectangle {B F : ℂ → ℂ}
    (hB : ContinuousOn B {z : ℂ | 0≤z.im})
    (hBF : ∀ z∈upperHalfPlane, B z=F z)
    {a b x : ℝ} (hx : x∈Ioo a b) {c : ℂ} (hne : B (x:ℂ)≠c) :
    ∃ a' b' H δ : ℝ, a<a' ∧ a'<b' ∧ b'<b ∧ 0<H ∧ 0<δ ∧
      ∀ u∈Icc a' b', ∀ y∈Ioc 0 H, 3*δ<‖F ((u:ℂ)+(y:ℂ)*I)-c‖ := by
  let d := ‖B (x:ℂ)-c‖
  have hd : 0<d := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨r,hr,hclose⟩ := Metric.continuousWithinAt_iff.mp
    (hB (x:ℂ) (by simp)) (d/2) (half_pos hd)
  let η := min (r/4) (min ((x-a)/2) ((b-x)/2))
  have hη : 0<η := lt_min (by positivity) (lt_min (by linarith [hx.1]) (by linarith [hx.2]))
  have hηr : η≤r/4 := min_le_left _ _
  have hηa : η≤(x-a)/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hηb : η≤(b-x)/2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨x-η,x+η,η,d/8,by linarith,by linarith,by linarith,hη,by positivity,?_⟩
  intro u hu y hy
  let z : ℂ := (u:ℂ)+(y:ℂ)*I
  have hzH : z∈upperHalfPlane := by simpa [z,upperHalfPlane] using hy.1
  have hzr : dist z (x:ℂ)<r := by
    have hb := norm_le_abs_re_add_abs_im (z-(x:ℂ))
    have hux : |u-x|≤η := abs_le.mpr ⟨by linarith [hu.1],by linarith [hu.2]⟩
    have hre : (z-(x:ℂ)).re=u-x := by simp [z]
    have him : (z-(x:ℂ)).im=y := by simp [z]
    rw [hre,him,abs_of_pos hy.1] at hb
    rw [dist_eq_norm]
    linarith [hy.2]
  have hzclosed : z∈{z : ℂ | 0≤z.im} := (show 0<z.im from hzH).le
  have hc := hclose hzclosed hzr
  rw [dist_eq_norm,hBF z hzH] at hc
  have ht := norm_sub_le_norm_sub_add_norm_sub (B (x:ℂ)) (F z) c
  rw [norm_sub_rev (B (x:ℂ)) (F z)] at ht
  change 3*(d/8)<‖F z-c‖
  change d≤_ at ht
  linarith

end SLEExactGauge

end

end OAI
