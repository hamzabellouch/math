import OAI.Geometry.NodalSets.Elliptic.CorrugationPeriodicJets

namespace OAI

namespace Yau.Geometry
open Real
noncomputable section

lemma corrugationPeriodicWell_center_first (a : ℝ) (m : ℤ × ℤ) :
    fderiv ℝ (corrugationPeriodicWell a) ((m.1:ℝ),(m.2:ℝ)) = 0 := by
  have hs := (corrugationPeriodicWell_shift_jets a m 0).1
  have hc := (corrugationPeriodicWell_cell_jets a 0 (by norm_num) (by norm_num)).1
  simp only [Prod.fst_zero,Prod.snd_zero,zero_add] at hs
  rw [hs,hc]
  apply ContinuousLinearMap.ext
  intro v
  simp [corrugationDiskWell_fderiv]

lemma corrugationPeriodicWell_center_positive {a : ℝ} (ha : 0 ≤ a) (m : ℤ × ℤ) (v : ℝ × ℝ) :
    0 ≤ fderiv ℝ (fderiv ℝ (corrugationPeriodicWell a)) ((m.1:ℝ),(m.2:ℝ)) v v := by
  have hs := (corrugationPeriodicWell_shift_jets a m 0).2
  have hc := (corrugationPeriodicWell_cell_jets a 0 (by norm_num) (by norm_num)).2
  simp only [Prod.fst_zero,Prod.snd_zero,zero_add] at hs
  rw [hs,hc]
  exact corrugationDiskWell_center_positive ha (1/4) v

lemma corrugationPeriodicWell_flat_jets (a : ℝ) (m : ℤ × ℤ) (z : ℝ × ℝ)
    (hz₁ : |z.1| < 1/2) (hz₂ : |z.2| < 1/2)
    (hz : (1/4:ℝ)^2 ≤ z.1^2+z.2^2) :
    fderiv ℝ (corrugationPeriodicWell a) (z.1+(m.1:ℝ),z.2+(m.2:ℝ)) = 0 ∧
    fderiv ℝ (fderiv ℝ (corrugationPeriodicWell a)) (z.1+(m.1:ℝ),z.2+(m.2:ℝ)) = 0 := by
  have hs := corrugationPeriodicWell_shift_jets a m z
  have hc := corrugationPeriodicWell_cell_jets a z hz₁ hz₂
  rw [hs.1,hs.2,hc.1,hc.2]
  have ht : (1/4:ℝ)^2-z.1^2-z.2^2 ≤ 0 := by linarith
  constructor
  · apply ContinuousLinearMap.ext
    intro v
    rw [corrugationDiskWell_fderiv,expNegInvGlue.zero_of_nonpos ht]
    simp
  · apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    rw [corrugationDiskWell_second,expNegInvGlue.zero_of_nonpos ht]
    simp

lemma corrugationPeriodicWell_derivative_bound_nonneg {a : ℝ} (ha : 0 ≤ a)
    (m : ℤ × ℤ) (z : ℝ × ℝ) (hz₁ : |z.1| < 1/2) (hz₂ : |z.2| < 1/2)
    {r : ℝ} (hr : 0 ≤ r) (hz : r^2=z.1^2+z.2^2) :
    ‖fderiv ℝ (corrugationPeriodicWell a) (z.1+(m.1:ℝ),z.2+(m.2:ℝ))‖ ≤
      2*corrugationSlope a (1/4) r := by
  rcases hr.eq_or_lt with hr | hr
  · have hz1 : z.1 = 0 := by nlinarith [sq_nonneg z.2]
    have hz2 : z.2 = 0 := by nlinarith [sq_nonneg z.1]
    rw [← hr,hz1,hz2,zero_add,zero_add,corrugationPeriodicWell_center_first]
    simp [corrugationSlope_center]
  · exact corrugationPeriodicWell_derivative_bound ha m z hz₁ hz₂ hr hz

end
end Yau.Geometry

end OAI
