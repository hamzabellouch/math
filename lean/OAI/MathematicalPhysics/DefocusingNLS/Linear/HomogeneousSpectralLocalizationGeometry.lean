import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSpectralLocalizationEquation
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace OAI

/-! Monotonicity and the uniformly oscillatory remote region of the actual
Liouville frequency.  These are the geometric inputs to outgoing transfer. -/

open Set
namespace DefocusingNLS

theorem homogeneousSpectralLocalizationFrequency_hasDerivAt
    (h b eta omega r : ℝ) (hr : 0 < r) :
    HasDerivAt (homogeneousSpectralLocalizationFrequency h b eta omega)
      (r / 8 + 2 * (eta + 99 / 4) / r^3) r := by
  have hs := ((hasDerivAt_id r).pow 2).div_const 16
  have hi := (((hasDerivAt_id r).pow 2).inv (pow_ne_zero 2 hr.ne')).const_mul
    (eta + 99 / 4)
  convert ((hs.add_const b).sub_const (h * omega)).sub hi using 1
  · funext t
    simp only [homogeneousSpectralLocalizationFrequency, div_eq_mul_inv,
      Pi.sub_apply, Pi.pow_apply, Pi.inv_apply, id_eq]
  · simp only [Pi.pow_apply, id_eq]
    field_simp [hr.ne']
    ring

theorem homogeneousSpectralLocalizationFrequency_strictMono
    (h b eta omega : ℝ) (heta : 0 ≤ eta) :
    StrictMonoOn (homogeneousSpectralLocalizationFrequency h b eta omega) (Ioi 0) := by
  have hd := homogeneousSpectralLocalizationFrequency_hasDerivAt h b eta omega
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro r hr
    exact (hd r hr).continuousAt.continuousWithinAt
  · intro r hr
    have hr0 : 0 < r := by simpa only [interior_Ioi, mem_Ioi] using hr
    rw [(hd r hr0).deriv]
    positivity

theorem homogeneousSpectralLocalizationFrequency_unique_zero
    (h b eta omega : ℝ) (heta : 0 ≤ eta) {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s)
    (hzr : homogeneousSpectralLocalizationFrequency h b eta omega r = 0)
    (hzs : homogeneousSpectralLocalizationFrequency h b eta omega s = 0) : r = s :=
  (homogeneousSpectralLocalizationFrequency_strictMono h b eta omega heta).injOn
    hr hs (hzr.trans hzs.symm)

theorem homogeneousSpectralLocalizationFrequency_remote
    (ell : ℕ) (h b omega S r : ℝ) (hh : |h| ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (homega : 0 ≤ omega) (hS : (ell : ℝ) + 1 ≤ S) (hωS : omega ≤ S)
    (hr : 0 < r) (hrS : 256 * S ≤ r^2) :
    r^2 / 32 ≤ homogeneousSpectralLocalizationFrequency h b
      ((ell : ℝ) * (ell + 10)) omega r ∧
    homogeneousSpectralLocalizationFrequency h b
      ((ell : ℝ) * (ell + 10)) omega r ≤ r^2 / 8 := by
  let L : ℝ := (ell : ℝ) * (ell + 10) + 99 / 4
  have hell : 0 ≤ (ell : ℝ) := Nat.cast_nonneg ell
  have hS0 : 0 ≤ S := by linarith
  have hr2 : 0 < r^2 := sq_pos_of_pos hr
  have hr256 : 256 ≤ r^2 := by linarith
  have hL0 : 0 ≤ L := by dsimp only [L]; positivity
  have hL : L ≤ 25 * ((ell : ℝ) + 1)^2 := by dsimp only [L]; nlinarith
  have hLS : L ≤ 25 * S^2 := hL.trans (mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (by positivity) hS0).mpr hS) (by norm_num))
  have hSsq : S^2 ≤ (r^2 / 256)^2 :=
    (sq_le_sq₀ hS0 (by positivity)).mpr (by linarith)
  have hLr : L ≤ r^4 / 1024 := by nlinarith
  have hωr : omega * r^2 ≤ r^4 / 256 := by
    have hp := mul_le_mul_of_nonneg_right (hωS.trans (by linarith : S ≤ r^2 / 256)) hr2.le
    nlinarith
  have hhω : -omega ≤ h * omega ∧ h * omega ≤ omega := by
    exact ⟨by nlinarith [abs_le.mp hh], by nlinarith [abs_le.mp hh]⟩
  have hhωr := mul_le_mul_of_nonneg_right hhω.2 hr2.le
  have hnegωr := mul_le_mul_of_nonneg_right hhω.1 hr2.le
  have hbr : 0 ≤ b * r^2 := mul_nonneg hb hr2.le
  have hb1r := mul_le_mul_of_nonneg_right hb1 hr2.le
  have he : r^2 * homogeneousSpectralLocalizationFrequency h b
      ((ell : ℝ) * (ell + 10)) omega r =
      r^4 / 16 + b * r^2 - h * omega * r^2 - L := by
    dsimp only [homogeneousSpectralLocalizationFrequency, L]
    field_simp [hr.ne']
  constructor
  · apply (mul_le_mul_iff_left₀ hr2).mp
    rw [mul_comm (homogeneousSpectralLocalizationFrequency h b
      ((ell : ℝ) * (ell + 10)) omega r) (r^2), he]
    nlinarith
  · apply (mul_le_mul_iff_left₀ hr2).mp
    rw [mul_comm (homogeneousSpectralLocalizationFrequency h b
      ((ell : ℝ) * (ell + 10)) omega r) (r^2), he]
    nlinarith

end DefocusingNLS

end OAI
