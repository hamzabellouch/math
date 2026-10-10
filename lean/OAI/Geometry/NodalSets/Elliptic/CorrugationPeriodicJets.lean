import OAI.Geometry.NodalSets.Elliptic.CorrugationAffineJets
import OAI.Geometry.NodalSets.Elliptic.CorrugationRadialJetsLemmas

namespace OAI

namespace Yau.Geometry
noncomputable section

lemma corrugationPeriodicWell_shift_jets (a : ℝ) (m : ℤ × ℤ) (z : ℝ × ℝ) :
    fderiv ℝ (corrugationPeriodicWell a) (z.1+(m.1:ℝ),z.2+(m.2:ℝ)) =
      fderiv ℝ (corrugationPeriodicWell a) z ∧
    fderiv ℝ (fderiv ℝ (corrugationPeriodicWell a)) (z.1+(m.1:ℝ),z.2+(m.2:ℝ)) =
      fderiv ℝ (fderiv ℝ (corrugationPeriodicWell a)) z := by
  let k : ℝ × ℝ := ((m.1:ℝ),(m.2:ℝ))
  have he : (fun w : ℝ × ℝ ↦ corrugationPeriodicWell a
      ((ContinuousLinearMap.id ℝ (ℝ × ℝ)) (w-(-k)))) = corrugationPeriodicWell a := by
    funext w
    change corrugationPeriodicWell a (w-(-k)) = _
    rw [sub_neg_eq_add]
    exact corrugationPeriodicWell_periodic a m w
  have hzadd : z+k = (z.1+(m.1:ℝ),z.2+(m.2:ℝ)) := rfl
  constructor
  · apply ContinuousLinearMap.ext
    intro v
    have h := affine_scalar_first (corrugationPeriodicWell a) (corrugationPeriodicWell_smooth a)
      (ContinuousLinearMap.id ℝ (ℝ × ℝ)) (-k) z v
    rw [he] at h
    simpa only [ContinuousLinearMap.id_apply,sub_neg_eq_add,hzadd] using h.symm
  · apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    have h := affine_scalar_second (corrugationPeriodicWell a) (corrugationPeriodicWell_smooth a)
      (ContinuousLinearMap.id ℝ (ℝ × ℝ)) (-k) z u v
    rw [he] at h
    simpa only [ContinuousLinearMap.id_apply,sub_neg_eq_add,hzadd] using h.symm

lemma corrugationPeriodicWell_radial_jets (a : ℝ) (m : ℤ × ℤ) (z : ℝ × ℝ)
    (hz₁ : |z.1| < 1/2) (hz₂ : |z.2| < 1/2) {r : ℝ}
    (hr : r ≠ 0) (hz : r^2=z.1^2+z.2^2) (u v : ℝ × ℝ) :
    fderiv ℝ (corrugationPeriodicWell a) (z.1+(m.1:ℝ),z.2+(m.2:ℝ)) v =
      corrugationSlope a (1/4) r*radialComponent z v r ∧
    fderiv ℝ (fderiv ℝ (corrugationPeriodicWell a)) (z.1+(m.1:ℝ),z.2+(m.2:ℝ)) u v =
      deriv (corrugationSlope a (1/4)) r*radialComponent z u r*radialComponent z v r +
      (corrugationSlope a (1/4) r/r)*angularComponent z u r*angularComponent z v r := by
  have hs := corrugationPeriodicWell_shift_jets a m z
  have hc := corrugationPeriodicWell_cell_jets a z hz₁ hz₂
  rw [hs.1,hs.2,hc.1,hc.2]
  exact ⟨corrugationDiskWell_radial_first a (1/4) z v hr hz,
    corrugationDiskWell_radial_second a (1/4) z u v hr hz⟩

lemma radialComponent_bound (z v : ℝ × ℝ) {r : ℝ} (hr : 0 < r)
    (hz : r^2=z.1^2+z.2^2) : |radialComponent z v r| ≤ 2*‖v‖ := by
  have h1 : |z.1| ≤ r := by nlinarith [sq_abs z.1,sq_nonneg z.2,abs_nonneg z.1]
  have h2 : |z.2| ≤ r := by nlinarith [sq_abs z.2,sq_nonneg z.1,abs_nonneg z.2]
  have hv1 : |v.1| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le v
  have hv2 : |v.2| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_snd_le v
  rw [radialComponent,abs_div,abs_of_pos hr]
  apply (div_le_iff₀ hr).mpr
  calc
    _ ≤ |z.1| *|v.1|+|z.2| *|v.2| := by simpa only [abs_mul] using abs_add_le (z.1*v.1) (z.2*v.2)
    _ ≤ r*‖v‖+r*‖v‖ := add_le_add (mul_le_mul h1 hv1 (abs_nonneg _) hr.le)
      (mul_le_mul h2 hv2 (abs_nonneg _) hr.le)
    _ = _ := by ring

lemma corrugationPeriodicWell_derivative_bound {a : ℝ} (ha : 0 ≤ a)
    (m : ℤ × ℤ) (z : ℝ × ℝ) (hz₁ : |z.1| < 1/2) (hz₂ : |z.2| < 1/2)
    {r : ℝ} (hr : 0 < r) (hz : r^2=z.1^2+z.2^2) :
    ‖fderiv ℝ (corrugationPeriodicWell a) (z.1+(m.1:ℝ),z.2+(m.2:ℝ))‖ ≤
      2*corrugationSlope a (1/4) r := by
  have hl := corrugationSlope_nonneg (R := (1/4:ℝ)) ha hr.le
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [Real.norm_eq_abs,(corrugationPeriodicWell_radial_jets a m z hz₁ hz₂ hr.ne' hz v v).1,
    abs_mul,abs_of_nonneg hl]
  exact (mul_le_mul_of_nonneg_left (radialComponent_bound z v hr hz) hl).trans_eq (by ring)

end
end Yau.Geometry

end OAI
