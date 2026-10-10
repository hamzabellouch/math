import OAI.Analysis.CircleDomains.Topology.RealPartBoundaryMaximum

namespace OAI

/-! The explicit positive harmonic barrier in an upper half disk. Its
poles lie at the two endpoints of the diameter. -/
open Set Function Complex
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

def semidiskBarrier (R : ℝ) (z : ℂ) : ℂ := (R : ℂ)/((R : ℂ)-z)-(R : ℂ)/((R : ℂ)+z)

lemma semidiskBarrier_den_ne_zero {R : ℝ} {z : ℂ} (hz : 0<z.im) :
    (R : ℂ)-z≠0 ∧ (R : ℂ)+z≠0 := by
  constructor <;> intro he
  · have hi := congrArg Complex.im he
    simp only [sub_im,ofReal_im,zero_im,zero_sub] at hi
    linarith
  · have hi := congrArg Complex.im he
    simp only [add_im,ofReal_im,zero_im,zero_add] at hi
    linarith

lemma differentiableAt_semidiskBarrier {R : ℝ} {z : ℂ}
    (hz₁ : (R : ℂ)-z≠0) (hz₂ : (R : ℂ)+z≠0) :
    DifferentiableAt ℂ (semidiskBarrier R) z :=
  ((differentiableAt_const _).div ((differentiableAt_const _).sub differentiableAt_id) hz₁).sub
    ((differentiableAt_const _).div ((differentiableAt_const _).add differentiableAt_id) hz₂)

lemma semidiskBarrier_im (R : ℝ) (z : ℂ) :
    (semidiskBarrier R z).im=R*z.im/normSq ((R : ℂ)-z)+R*z.im/normSq ((R : ℂ)+z) := by
  simp only [semidiskBarrier,sub_im,div_im,ofReal_im,ofReal_re,zero_mul,
    sub_im,add_im,zero_sub,zero_add]
  ring

lemma semidiskBarrier_im_nonneg {R : ℝ} {z : ℂ} (hR : 0≤R) (hz : 0≤z.im) :
    0≤(semidiskBarrier R z).im := by
  rw [semidiskBarrier_im]
  exact add_nonneg (div_nonneg (mul_nonneg hR hz) (normSq_nonneg _))
    (div_nonneg (mul_nonneg hR hz) (normSq_nonneg _))

lemma semidiskBarrier_im_on_arc {R : ℝ} {z : ℂ} (hR : 0<R)
    (hz : 0<z.im) (hn : ‖z‖=R) : (semidiskBarrier R z).im=R/z.im := by
  have hcircle : z.re^2+z.im^2=R^2 := by
    calc
      _ = normSq z := by simp only [normSq_apply,pow_two]
      _ = ‖z‖^2 := normSq_eq_norm_sq z
      _ = R^2 := by rw [hn]
  have hm : normSq ((R : ℂ)-z)=2*R*(R-z.re) := by
    simp only [normSq_apply,sub_re,sub_im,ofReal_re,ofReal_im]
    nlinarith
  have hp : normSq ((R : ℂ)+z)=2*R*(R+z.re) := by
    simp only [normSq_apply,add_re,add_im,ofReal_re,ofReal_im]
    nlinarith
  have hsum : normSq ((R : ℂ)-z)+normSq ((R : ℂ)+z)=4*R^2 := by rw [hm,hp];ring
  have hprod : normSq ((R : ℂ)-z)*normSq ((R : ℂ)+z)=4*R^2*z.im^2 := by
    rw [hm,hp]
    nlinarith [sq_nonneg (R*z.re),sq_nonneg (R*z.im)]
  have hd₁ : normSq ((R : ℂ)-z)≠0 := (normSq_pos.mpr (semidiskBarrier_den_ne_zero hz).1).ne'
  have hd₂ : normSq ((R : ℂ)+z)≠0 := (normSq_pos.mpr (semidiskBarrier_den_ne_zero hz).2).ne'
  rw [semidiskBarrier_im]
  calc
    _ = R*z.im*(normSq ((R : ℂ)-z)+normSq ((R : ℂ)+z))/
        (normSq ((R : ℂ)-z)*normSq ((R : ℂ)+z)) := by field_simp;ring
    _ = R/z.im := by rw [hsum,hprod];field_simp

lemma semidiskBarrier_im_ge_one_on_arc {R : ℝ} {z : ℂ} (hR : 0<R)
    (hz : 0<z.im) (hn : ‖z‖=R) : 1≤(semidiskBarrier R z).im := by
  rw [semidiskBarrier_im_on_arc hR hz hn]
  apply (one_le_div hz).mpr
  exact (im_le_norm z).trans_eq hn

lemma semidiskBarrier_im_le {R : ℝ} {z : ℂ} (hR : 0<R) (hz : 0≤z.im)
    (hn : ‖z‖≤R/2) : (semidiskBarrier R z).im≤8*z.im/R := by
  have h₁ : R/2≤‖(R : ℂ)-z‖ := by
    have h := norm_le_norm_sub_add (R : ℂ) z
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR] at h
    linarith
  have h₂ : R/2≤‖(R : ℂ)+z‖ := by
    have h := norm_le_norm_sub_add (R : ℂ) (-z)
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR,norm_neg,sub_neg_eq_add] at h
    linarith
  have hsq₁ : R^2≤4*normSq ((R : ℂ)-z) := by rw [normSq_eq_norm_sq];nlinarith
  have hsq₂ : R^2≤4*normSq ((R : ℂ)+z) := by rw [normSq_eq_norm_sq];nlinarith
  have hp₁ : 0<normSq ((R : ℂ)-z) := by nlinarith [sq_pos_of_pos hR]
  have hp₂ : 0<normSq ((R : ℂ)+z) := by nlinarith [sq_pos_of_pos hR]
  have hb₁ : R*z.im/normSq ((R : ℂ)-z)≤4*z.im/R := by
    apply (div_le_div_iff₀ hp₁ hR).mpr
    nlinarith [mul_nonneg hz (sub_nonneg.mpr hsq₁)]
  have hb₂ : R*z.im/normSq ((R : ℂ)+z)≤4*z.im/R := by
    apply (div_le_div_iff₀ hp₂ hR).mpr
    nlinarith [mul_nonneg hz (sub_nonneg.mpr hsq₂)]
  rw [semidiskBarrier_im]
  calc
    _ ≤ 4*z.im/R+4*z.im/R := add_le_add hb₁ hb₂
    _ = 8*z.im/R := by ring

end CircleDomainRigidity

end

end OAI
