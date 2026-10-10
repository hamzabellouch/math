import Mathlib

namespace OAI

/-! Disk Automorphism. -/

noncomputable section

open Set Filter Metric Topology Function

open scoped ComplexConjugate

namespace CrouzeixHilbert.Conformal

def diskShift (w z : ℂ) : ℂ := (z - w) / (1 - conj w * z)

theorem diskShift_den_ne {w z : ℂ} (hw : ‖w‖ < 1) (hz : ‖z‖ ≤ 1) :
    1 - conj w * z ≠ 0 := by
  intro h
  have he : conj w * z = 1 := (sub_eq_zero.mp h).symm
  have hn : ‖conj w * z‖ < 1 := by
    calc
      ‖conj w * z‖ = ‖w‖ * ‖z‖ := by rw [norm_mul, Complex.norm_conj]
      _ ≤ ‖w‖ * 1 := mul_le_mul_of_nonneg_left hz (norm_nonneg _)
      _ < 1 := by simpa using hw
  simp [he] at hn

theorem diskShift_norm_identity (w z : ℂ) :
    ‖1 - conj w * z‖ ^ 2 - ‖z - w‖ ^ 2 = (1 - ‖w‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im]
  ring

theorem diskShift_into_disk {w z : ℂ} (hw : ‖w‖ < 1) (hz : ‖z‖ < 1) :
    ‖diskShift w z‖ < 1 := by
  have hpos : 0 < (1 - ‖w‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
    apply mul_pos <;> nlinarith [norm_nonneg w, norm_nonneg z]
  rw [diskShift, norm_div, div_lt_one₀ (norm_pos_iff.mpr (diskShift_den_ne hw hz.le))]
  have := diskShift_norm_identity w z
  nlinarith [norm_nonneg (1 - conj w * z), norm_nonneg (z - w)]

@[simp] theorem diskShift_self (w : ℂ) : diskShift w w = 0 := by simp [diskShift]

@[simp] theorem diskShift_zero (w : ℂ) : diskShift w 0 = -w := by simp [diskShift]

theorem diskShift_eq_zero_iff {w z : ℂ} (hw : ‖w‖ < 1) (hz : ‖z‖ ≤ 1) :
    diskShift w z = 0 ↔ z = w := by
  simp [diskShift, div_eq_zero_iff, diskShift_den_ne hw hz, sub_eq_zero]

theorem diskShift_injOn {w : ℂ} (hw : ‖w‖ < 1) :
    InjOn (diskShift w) (closedBall 0 1) := by
  intro z hz v hv he
  have hz' : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
  have hv' : ‖v‖ ≤ 1 := mem_closedBall_zero_iff.mp hv
  have hm : w * conj w ≠ 1 := by
    intro he'
    have hh := congrArg norm he'
    rw [norm_mul, Complex.norm_conj, norm_one] at hh
    nlinarith [norm_nonneg w]
  have he' := (div_eq_div_iff (diskShift_den_ne hw hz') (diskShift_den_ne hw hv')).mp he
  have hh : (z - v) * (1 - w * conj w) = 0 := by linear_combination he'
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right (sub_ne_zero.mpr hm.symm))

theorem hasDerivAt_diskShift {w z : ℂ} (hw : ‖w‖ < 1) (hz : ‖z‖ ≤ 1) :
    HasDerivAt (diskShift w) ((1 - conj w * w) / (1 - conj w * z) ^ 2) z := by
  convert! ((hasDerivAt_id z).sub_const w).div
    ((hasDerivAt_const z 1).sub ((hasDerivAt_id z).const_mul (conj w)))
    (diskShift_den_ne hw hz) using 1
  congr 1
  dsimp
  ring

theorem norm_deriv_diskShift_zero {w : ℂ} (hw : ‖w‖ < 1) :
    ‖deriv (diskShift w) 0‖ = 1 - ‖w‖ ^ 2 := by
  rw [(hasDerivAt_diskShift hw (by simp : ‖(0 : ℂ)‖ ≤ 1)).deriv]
  simp only [mul_zero, sub_zero, one_pow, div_one]
  rw [mul_comm (conj w) w, Complex.mul_conj, ← Complex.ofReal_one,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    Complex.normSq_eq_norm_sq, abs_of_pos]
  nlinarith [norm_nonneg w]

theorem norm_deriv_diskShift_self {w : ℂ} (hw : ‖w‖ < 1) :
    ‖deriv (diskShift w) w‖ = (1 - ‖w‖ ^ 2)⁻¹ := by
  rw [(hasDerivAt_diskShift hw hw.le).deriv]
  have he : (1 - conj w * w) / (1 - conj w * w) ^ 2 = (1 - conj w * w)⁻¹ := by
    field_simp
  rw [he, norm_inv]
  congr 1
  rw [mul_comm (conj w) w, Complex.mul_conj, ← Complex.ofReal_one,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    Complex.normSq_eq_norm_sq, abs_of_pos]
  nlinarith [norm_nonneg w]

end CrouzeixHilbert.Conformal

end

end OAI
