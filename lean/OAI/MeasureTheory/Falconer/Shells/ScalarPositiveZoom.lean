import OAI.MeasureTheory.Falconer.Measures.ScalarDensityMassControl

namespace OAI

/-! The density zoom placed inside the positive coefficient interval. -/
namespace Falconer

 theorem scalar_positive_zoom_bounds {z R : ℝ} (hR : 0 < R) (E : Finset ℝ)
    (hE : ∀ x ∈ E, |x-z| ≤ R) :
    ∀ t ∈ scalarZoom (z-3*R) (6*R) E, 1/3 ≤ t ∧ t ≤ 1 := by
  intro t ht
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
  have hb := (abs_le.mp (hE x hx))
  constructor
  · apply (le_div_iff₀ (by positivity : 0 < 6*R)).2
    linarith
  · apply (div_le_iff₀ (by positivity : 0 < 6*R)).2
    linarith

 theorem scalar_positive_zoom_local_mass {δ κ z R : ℝ} (hδ : 0 < δ) (hR : 0 < R)
    (E : Finset ℝ)
    (hlocal : ∀ u r : ℝ, δ ≤ r → scalarBallMass E u r ≤
      2^κ*(r/R)^κ*scalarBallMass E z R)
    (F : Finset ℝ) (hFE : F ⊆ E) (hF : scalarBallMass E z R = (F.card:ℝ)) :
    ∀ u r : ℝ, δ ≤ 6*R*r →
      scalarBallMass (scalarZoom (z-3*R) (6*R) F) u r ≤
        (12:ℝ)^κ*r^κ*((scalarZoom (z-3*R) (6*R) F).card:ℝ) := by
  intro u r hr
  have hr0 : 0 ≤ r := by nlinarith
  rw [scalarZoom_ball_mass (by positivity),scalarZoom_card (by positivity)]
  have hh := (scalarBallMass_mono hFE (z-3*R+6*R*u) (6*R*r)).trans
    (hlocal (z-3*R+6*R*u) (6*R*r) hr)
  rw [hF,show 6*R*r/R = 6*r by field_simp,Real.mul_rpow (by norm_num) hr0] at hh
  convert hh using 1
  rw [show (12:ℝ) = 2*6 by norm_num,Real.mul_rpow (by norm_num) (by norm_num)]
  ring

end Falconer

end OAI
