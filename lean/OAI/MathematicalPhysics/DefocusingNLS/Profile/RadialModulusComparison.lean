import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeDifference

namespace OAI

/-! Quantitative direction of the free starting-radius perturbation. -/

open Set
namespace DefocusingNLS

theorem complex_norm_decrease_of_small_left_direction (z d : ℂ) (x : ℝ)
    (hx : 0 < x) (hxsmall : x ≤ (1/1000 : ℝ)) (hz : ‖z-1‖ ≤ (1/1000 : ℝ))
    (hdre : d.re ≤ -(16/100 : ℝ)*x) (hd : ‖d‖ ≤ (35/100 : ℝ)*x) :
    ‖z+d‖ < ‖z‖ := by
  have hc : (starRingEnd ℂ z*d).re=d.re+(starRingEnd ℂ (z-1)*d).re := by
    simp only [map_sub,map_one,sub_mul,one_mul,Complex.sub_re]
    ring
  have hcNorm : (starRingEnd ℂ (z-1)*d).re ≤ (1/1000 : ℝ)*‖d‖ := calc
    _ ≤ ‖starRingEnd ℂ (z-1)*d‖ := Complex.re_le_norm _
    _ = ‖z-1‖*‖d‖ := by rw [norm_mul,Complex.norm_conj]
    _ ≤ _ := mul_le_mul_of_nonneg_right hz (norm_nonneg d)
  have hcB : (starRingEnd ℂ z*d).re ≤ -(16/100 : ℝ)*x+(1/1000 : ℝ)*‖d‖ := by
    rw [hc]; linarith
  have hds : ‖d‖ ≤ (1/1000 : ℝ) := by nlinarith
  have hsq : ‖d‖^2 ≤ (1/1000 : ℝ)*‖d‖ := by
    nlinarith [mul_le_mul_of_nonneg_left hds (norm_nonneg d)]
  have hid : ‖z+d‖^2=‖z‖^2+2*(starRingEnd ℂ z*d).re+‖d‖^2 := by
    simp only [Complex.sq_norm,Complex.normSq_apply,Complex.add_re,Complex.add_im,
      Complex.mul_re,Complex.conj_re,Complex.conj_im]
    ring
  have hlt : ‖z+d‖^2 < ‖z‖^2 := by nlinarith
  nlinarith [norm_nonneg (z+d),norm_nonneg z]

theorem radial_free_difference_direction (b δ v : ℝ) (d : ℂ)
    (hb : b ∈ Icc (334/1000 : ℝ) (335/1000)) (hδ : 0 ≤ δ) (hv : 0 ≤ v)
    (he : ‖d+(b : ℂ)/2*(δ : ℂ)^2+(b : ℂ)*(δ : ℂ)*(v : ℂ)‖ ≤
      (6/1000 : ℝ)*δ*(δ+v)) :
    d.re ≤ -(16/100 : ℝ)*δ*(δ+v) ∧ ‖d‖ ≤ (35/100 : ℝ)*δ*(δ+v) := by
  have hb0 : 0 ≤ b := by linarith [hb.1]
  let t := b/2*δ^2+b*δ*v
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have heq : d+(b : ℂ)/2*(δ : ℂ)^2+(b : ℂ)*(δ : ℂ)*(v : ℂ)=d+(t : ℂ) := by
    dsimp [t]; push_cast; ring
  rw [heq] at he
  have htlo : (167/1000 : ℝ)*δ*(δ+v) ≤ t := by
    have h₁ := mul_le_mul_of_nonneg_right hb.1 (sq_nonneg δ)
    have h₂ := mul_le_mul_of_nonneg_right hb.1 (mul_nonneg hδ hv)
    dsimp [t]
    nlinarith [mul_nonneg hδ hv]
  have hthi : t ≤ (335/1000 : ℝ)*δ*(δ+v) := by
    have h₁ := mul_le_mul_of_nonneg_right hb.2 (sq_nonneg δ)
    have h₂ := mul_le_mul_of_nonneg_right hb.2 (mul_nonneg hδ hv)
    dsimp [t]
    nlinarith [sq_nonneg δ]
  have hr := (Complex.re_le_norm (d+(t : ℂ))).trans he
  have hn : ‖d‖ ≤ ‖d+(t : ℂ)‖+t := by
    have hh := norm_sub_le (d+(t : ℂ)) (t : ℂ)
    simpa only [add_sub_cancel_right,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht0] using hh
  simp only [Complex.add_re,Complex.ofReal_re] at hr
  constructor <;> nlinarith [mul_nonneg hδ hv,sq_nonneg δ]

end DefocusingNLS

end OAI
