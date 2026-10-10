import Mathlib

namespace OAI

section
section
noncomputable section
open scoped Topology

namespace CriticalPercolation.EuclideanEllipse

def diagonal (a b : ℝ) (z : ℂ) : ℂ := ⟨a*z.re,b*z.im⟩

lemma diagonal_add (a b : ℝ) (z w : ℂ) :
    diagonal a b (z+w)=diagonal a b z+diagonal a b w := by
  apply Complex.ext <;> simp [diagonal,mul_add]
lemma diagonal_sub (a b : ℝ) (z w : ℂ) :
    diagonal a b (z-w)=diagonal a b z-diagonal a b w := by
  apply Complex.ext <;> simp [diagonal,mul_sub]
lemma diagonal_comp (a b c d : ℝ) (z : ℂ) :
    diagonal a b (diagonal c d z)=diagonal (a*c) (b*d) z := by
  apply Complex.ext <;> simp [diagonal,mul_assoc]
lemma diagonal_one (z : ℂ) : diagonal 1 1 z=z := by apply Complex.ext <;> simp [diagonal]
lemma diagonal_neg (a b : ℝ) (z : ℂ) : diagonal a b (-z)= -diagonal a b z := by
  apply Complex.ext <;> simp [diagonal]

lemma diagonal_norm_le (a b M : ℝ) (hM : 0≤M) (ha : |a|≤M) (hb : |b|≤M) (z : ℂ) :
    ‖diagonal a b z‖≤M*‖z‖ := by
  have ha2 : a^2≤M^2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hM).mpr ha
  have hb2 : b^2≤M^2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hM).mpr hb
  have hsq : ‖diagonal a b z‖^2≤(M*‖z‖)^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply,mul_pow,Complex.sq_norm,Complex.normSq_apply]
    dsimp [diagonal]
    nlinarith [mul_le_mul_of_nonneg_right ha2 (sq_nonneg z.re),
      mul_le_mul_of_nonneg_right hb2 (sq_nonneg z.im)]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).mp hsq

def normalize (R W : ℝ) (c : Circle) (z : ℂ) : ℂ :=
  (c : ℂ)*diagonal (1/R) (1/W) ((c : ℂ)⁻¹*z)

def expand (R W : ℝ) (c : Circle) (z : ℂ) : ℂ :=
  (c : ℂ)*diagonal R W ((c : ℂ)⁻¹*z)

lemma normalize_sub (R W : ℝ) (c : Circle) (z w : ℂ) :
    normalize R W c (z-w)=normalize R W c z-normalize R W c w := by
  simp only [normalize,mul_sub,diagonal_sub]

lemma expand_normalize (R W : ℝ) (hR : R≠0) (hW : W≠0) (c : Circle) (z : ℂ) :
    expand R W c (normalize R W c z)=z := by
  simp only [normalize,expand,←mul_assoc,inv_mul_cancel₀ c.coe_ne_zero,one_mul,
    diagonal_comp,mul_one_div_cancel hR,mul_one_div_cancel hW,diagonal_one]
  rw [mul_assoc,mul_inv_cancel_left₀ c.coe_ne_zero]

lemma normalize_expand (R W : ℝ) (hR : R≠0) (hW : W≠0) (c : Circle) (z : ℂ) :
    normalize R W c (expand R W c z)=z := by
  simp only [normalize,expand,←mul_assoc,inv_mul_cancel₀ c.coe_ne_zero,one_mul,
    diagonal_comp,one_div_mul_cancel hR,one_div_mul_cancel hW,diagonal_one]
  rw [mul_assoc,mul_inv_cancel_left₀ c.coe_ne_zero]

lemma normalize_norm_le (R W : ℝ) (hW : 0<W) (hWR : W≤R) (c : Circle) (z : ℂ) :
    ‖normalize R W c z‖≤‖z‖/W := by
  have hR : 0<R := hW.trans_le hWR
  have h1 : |1/R|≤1/W := by rw [abs_of_pos (one_div_pos.mpr hR)]; exact one_div_le_one_div_of_le hW hWR
  have h2 : |1/W|≤1/W := (abs_of_pos (one_div_pos.mpr hW)).le
  have h := diagonal_norm_le (1/R) (1/W) (1/W) (by positivity) h1 h2 ((c : ℂ)⁻¹*z)
  simpa [normalize,norm_mul,Circle.norm_coe,div_eq_mul_inv,mul_comm]
    using h

lemma expand_norm_le (R W : ℝ) (hW : 0≤W) (hWR : W≤R) (c : Circle) (z : ℂ) :
    ‖expand R W c z‖≤R*‖z‖ := by
  have hR := hW.trans hWR
  have h := diagonal_norm_le R W R hR (by simp [abs_of_nonneg hR])
    (by simpa [abs_of_nonneg hW] using hWR) ((c : ℂ)⁻¹*z)
  simpa only [expand,norm_mul,Circle.norm_coe,norm_inv,inv_one,one_mul] using h

lemma normalize_center (W : ℝ) (c : Circle) (z : ℂ) :
    normalize W W c z=(1/W : ℝ)•z := by
  have he : ∀ w : ℂ, diagonal (1/W) (1/W) w=(1/W : ℝ)•w := by intro w; apply Complex.ext <;> simp [diagonal]
  rw [normalize,he,mul_smul_comm,←mul_assoc,mul_inv_cancel₀ c.coe_ne_zero,one_mul]

lemma normalize_neg (R W : ℝ) (c : Circle) (z : ℂ) :
    normalize R W (-c) z=normalize R W c z := by
  simp only [normalize,Circle.coe_neg,inv_neg,neg_mul,diagonal_neg,mul_neg,neg_neg]

lemma normalize_components (R W : ℝ) (c : Circle) (z : ℂ) :
    (((c : ℂ)⁻¹*normalize R W c z).re=(1/R)*((c : ℂ)⁻¹*z).re) ∧
    (((c : ℂ)⁻¹*normalize R W c z).im=(1/W)*((c : ℂ)⁻¹*z).im) := by
  simp [normalize,diagonal]

lemma normalize_origin (R W : ℝ) (c : Circle) : normalize R W c 0=0 := by
  simp [normalize,diagonal,Complex.ext_iff]

lemma normalize_real_linear (R W : ℝ) (c : Circle) (z w : ℂ) (a b : ℝ) :
    normalize R W c (a•z+b•w)=a•normalize R W c z+b•normalize R W c w := by
  have hd : ∀ q : ℂ, ∀ t : ℝ, diagonal (1/R) (1/W) (t•q)=t•diagonal (1/R) (1/W) q := by
    intro q t
    apply Complex.ext <;> simp [diagonal,Complex.mul_re,Complex.mul_im] <;> ring
  simp only [normalize,mul_add,mul_smul_comm,diagonal_add,hd]

end CriticalPercolation.EuclideanEllipse
end
end
end

end OAI
