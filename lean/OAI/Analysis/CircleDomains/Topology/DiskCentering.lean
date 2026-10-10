import OAI.Analysis.CircleDomains.Modulus.NormalizedArgument

namespace OAI

/-! The explicit disk automorphism used to move the marked endpoint to
the origin in a Jordan disk coordinate. -/

open Set Function Filter Metric
open scoped Topology ComplexConjugate

noncomputable section
namespace CircleDomainRigidity

def diskCentering (a z : ℂ) : ℂ := (z - a) / (1 - conj a * z)

theorem diskCentering_den_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    1 - conj a * z ≠ 0 := by
  have hnorm : ‖conj a * z‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    exact (mul_le_mul_of_nonneg_left hz (norm_nonneg a)).trans_lt (by simpa using ha)
  intro h
  rw [(sub_eq_zero.mp h).symm, norm_one] at hnorm
  exact lt_irrefl _ hnorm

theorem diskCentering_normSq_identity (a z : ℂ) :
    Complex.normSq (1 - conj a * z) - Complex.normSq (z - a) =
      (1 - Complex.normSq a) * (1 - Complex.normSq z) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

theorem diskCentering_norm_le {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    ‖diskCentering a z‖ ≤ 1 := by
  have ha2 : 0 ≤ 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hz2 : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hi := diskCentering_normSq_identity a z
  simp only [← Complex.sq_norm] at hi
  have hsq : ‖z - a‖ ^ 2 ≤ ‖1 - conj a * z‖ ^ 2 := by
    nlinarith [mul_nonneg ha2 hz2]
  have hn : ‖z - a‖ ≤ ‖1 - conj a * z‖ := by
    nlinarith [norm_nonneg (z - a), norm_nonneg (1 - conj a * z)]
  rw [diskCentering, norm_div]
  exact (div_le_one (norm_pos_iff.mpr (diskCentering_den_ne_zero ha hz))).mpr hn

theorem diskCentering_norm_lt {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    ‖diskCentering a z‖ < 1 := by
  have ha2 : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hz2 : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hi := diskCentering_normSq_identity a z
  simp only [← Complex.sq_norm] at hi
  have hsq : ‖z - a‖ ^ 2 < ‖1 - conj a * z‖ ^ 2 := by
    nlinarith [mul_pos ha2 hz2]
  have hn : ‖z - a‖ < ‖1 - conj a * z‖ := by
    nlinarith [norm_nonneg (z - a), norm_nonneg (1 - conj a * z)]
  rw [diskCentering, norm_div]
  exact (div_lt_one (norm_pos_iff.mpr (diskCentering_den_ne_zero ha hz.le))).mpr hn

theorem diskCentering_norm_eq_one {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ = 1) :
    ‖diskCentering a z‖ = 1 := by
  have hi := diskCentering_normSq_identity a z
  simp only [← Complex.sq_norm, hz, one_pow, sub_self, mul_zero] at hi
  have hn : ‖z - a‖ = ‖1 - conj a * z‖ := by
    nlinarith [norm_nonneg (z - a), norm_nonneg (1 - conj a * z)]
  rw [diskCentering, norm_div, hn, div_self (norm_ne_zero_iff.mpr (diskCentering_den_ne_zero ha hz.le))]

@[simp] theorem diskCentering_self (a : ℂ) : diskCentering a a = 0 := by
  simp only [diskCentering, sub_self, zero_div]

theorem continuousOn_diskCentering {a : ℂ} (ha : ‖a‖ < 1) :
    ContinuousOn (diskCentering a) (closedBall (0 : ℂ) 1) := by
  apply (continuous_id.sub continuous_const).continuousOn.div
    (continuous_const.sub (continuous_const.mul continuous_id)).continuousOn
  intro z hz
  exact diskCentering_den_ne_zero ha (by simpa only [mem_closedBall_zero_iff, id_eq] using hz)

theorem diskCentering_inverse {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    diskCentering (-a) (diskCentering a z) = z := by
  have hden := diskCentering_den_ne_zero ha hz
  have haa := diskCentering_den_ne_zero ha ha.le
  have hneg : ‖-a‖ < 1 := by simpa only [norm_neg] using ha
  have hout := diskCentering_den_ne_zero hneg (diskCentering_norm_le ha hz)
  unfold diskCentering at hout ⊢
  simp only [map_neg, neg_mul, sub_neg_eq_add] at hout ⊢
  have haux : 1 + conj a * ((z - a) / (1 - conj a * z)) =
      (1 - conj a * a) / (1 - conj a * z) := by
    field_simp
    ring
  rw [haux]
  have hden' : 1 - z * conj a ≠ 0 := by simpa only [mul_comm] using hden
  have haa' : 1 - a * conj a ≠ 0 := by simpa only [mul_comm] using haa
  field_simp [hden, hden', haa, haa']
  ring

end CircleDomainRigidity

end

end OAI
