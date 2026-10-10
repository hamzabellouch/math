import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedBoundary
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialShootingInnerEquation

namespace OAI

/-! A globally differentiable, nonvanishing radial profile from actual matched boundary data. -/

open Set Filter
namespace DefocusingNLS
open ProfileCertificate

noncomputable def radialMatchedProfile (n : ℕ) (z : ProfileMatchingBall) (r : ℝ) : ℂ :=
  if r ≤ innerBoundaryRadius then radialShootingInnerComplex n (profileMatchingParameter z) r
  else radialShootingExteriorProfile n z r

theorem radialMatchedProfile_differentiable (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) : Differentiable ℝ (radialMatchedProfile n z) := by
  obtain ⟨hv,hd⟩ := radialMatchingMap_zero_boundary n z hX hz
  intro r
  rcases lt_trichotomy r innerBoundaryRadius with hr | rfl | hr
  · apply HasDerivAt.differentiableAt
    apply ((radialShootingInner_differentiable n (profileMatchingParameter z) r).hasDerivAt).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hr] with t ht
    exact ite_eq_left ht.le
  · have hI := (radialShootingInner_differentiable n (profileMatchingParameter z) innerBoundaryRadius).hasDerivAt
    have hE := (radialShootingExteriorProfile_differentiableAt n z hX innerBoundaryRadius le_rfl).hasDerivAt
    rw [hd] at hE
    have hleft : HasDerivWithinAt (radialMatchedProfile n z)
        (deriv (radialShootingInnerComplex n (profileMatchingParameter z)) innerBoundaryRadius)
        (Iic innerBoundaryRadius) innerBoundaryRadius := by
      apply hI.hasDerivWithinAt.congr
      · intro t ht
        exact ite_eq_left ht
      · exact ite_eq_left le_rfl
    have hright : HasDerivWithinAt (radialMatchedProfile n z)
        (deriv (radialShootingInnerComplex n (profileMatchingParameter z)) innerBoundaryRadius)
        (Ici innerBoundaryRadius) innerBoundaryRadius := by
      apply hE.hasDerivWithinAt.congr
      · intro t ht
        rcases (show innerBoundaryRadius ≤ t from ht).eq_or_lt with rfl | ht
        · simpa only [radialMatchedProfile,ite_eq_left le_rfl] using hv.symm
        · exact ite_eq_right ht.not_ge
      · simpa only [radialMatchedProfile,ite_eq_left le_rfl] using hv.symm
    have hh := hleft.union hright
    rw [Iic_union_Ici] at hh
    exact (hh.hasDerivAt (by simp)).differentiableAt
  · apply HasDerivAt.differentiableAt
    apply ((radialShootingExteriorProfile_differentiableAt n z hX r hr.le).hasDerivAt).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hr] with t ht
    exact ite_eq_right ht.not_ge

theorem radialMatchedProfile_ne_zero (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (r : ℝ) (hr : 0 ≤ r) : radialMatchedProfile n z r ≠ 0 := by
  unfold radialMatchedProfile
  split_ifs with h
  · have hn := radialShootingInner_norm n (profileMatchingParameter z) r ⟨hr,h⟩
    apply norm_pos_iff.mp
    rw [hn]
    exact radialShootingInner_positive n (profileMatchingParameter z) r ⟨hr,h⟩
  · exact radialShootingExteriorProfile_ne_zero n z hX r (not_le.mp h).le

theorem radialMatchedProfile_origin (n : ℕ) (z : ProfileMatchingBall) :
    0 < (radialMatchedProfile n z 0).re ∧ (radialMatchedProfile n z 0).im=0 := by
  rw [radialMatchedProfile,ite_eq_left (by linarith [innerBoundaryRadius_bounds.1])]
  exact radialShootingInner_origin n (profileMatchingParameter z)

theorem exists_radialMatchedProfile :
    ∀ᶠ n in atTop, ∃ z : ProfileMatchingBall,
      Differentiable ℝ (radialMatchedProfile n z) ∧
      (∀ r, 0 ≤ r → radialMatchedProfile n z r ≠ 0) ∧
      0 < (radialMatchedProfile n z 0).re ∧ (radialMatchedProfile n z 0).im=0 := by
  have hs : Tendsto (fun n : ℕ => n+radialInnerShootingThreshold) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right n _) tendsto_id
  filter_upwards [exists_radialMatchingMap_zero,hs.eventually radialShootingExterior_exists] with n hn hX
  obtain ⟨z,hz⟩ := hn
  exact ⟨z,radialMatchedProfile_differentiable n z (hX z) hz,
    radialMatchedProfile_ne_zero n z (hX z),radialMatchedProfile_origin n z⟩

end DefocusingNLS

end OAI
