import OAI.Probability.SLE.Geometry.ComplexJordanExtension
import OAI.Probability.SLE.Geometry.ArcBoundaryReplacement

namespace OAI

/-! The upper semicircle supplies the fixed boundary arc for the first
relative Schoenflies extension of a compactified half-plane crosscut. -/
noncomputable section
open Set Complex

namespace SLEExactGauge

def diskUpperArc (s : ℝ) : ℂ :=
  (-Real.cos (Real.pi*s) : ℂ)+(Real.sin (Real.pi*s) : ℂ)*I

lemma diskUpperArc_continuous : Continuous diskUpperArc := by
  unfold diskUpperArc
  fun_prop

lemma diskUpperArc_zero : diskUpperArc 0 = -1 := by simp [diskUpperArc]
lemma diskUpperArc_one : diskUpperArc 1 = 1 := by simp [diskUpperArc]

lemma diskUpperArc_re (s : ℝ) : (diskUpperArc s).re = -Real.cos (Real.pi*s) := by
  simp only [diskUpperArc,Complex.add_re,Complex.neg_re,Complex.ofReal_re,
    Complex.mul_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,
    sub_zero,add_zero]

lemma diskUpperArc_im (s : ℝ) : (diskUpperArc s).im = Real.sin (Real.pi*s) := by
  simp only [diskUpperArc,Complex.add_im,Complex.neg_im,Complex.ofReal_im,neg_zero,
    Complex.mul_im,Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,
    add_zero,zero_add]

lemma diskUpperArc_norm (s : ℝ) : ‖diskUpperArc s‖=1 := by
  have hn : Complex.normSq (diskUpperArc s)=1 := by
    rw [Complex.normSq_apply,diskUpperArc_re,diskUpperArc_im]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi*s)]
  rw [Complex.normSq_eq_norm_sq] at hn
  nlinarith [norm_nonneg (diskUpperArc s)]

lemma diskUpperArc_injOn : InjOn diskUpperArc (Icc 0 1) := by
  intro s hs t ht he
  have hr : -Real.cos (Real.pi*s) = -Real.cos (Real.pi*t) := by
    simpa only [diskUpperArc_re] using congrArg Complex.re he
  have heq : Real.pi*s=Real.pi*t := Real.strictAntiOn_cos.injOn
    ⟨mul_nonneg Real.pi_pos.le hs.1,mul_le_of_le_one_right Real.pi_pos.le hs.2⟩
    ⟨mul_nonneg Real.pi_pos.le ht.1,mul_le_of_le_one_right Real.pi_pos.le ht.2⟩ (by linarith)
  exact mul_left_cancel₀ Real.pi_ne_zero heq

lemma disk_crosscut_meets_upper_at_endpoints
    (p : ℝ → ℂ) (hp : ∀ s ∈ Ioo 0 1, ‖p s‖ < 1)
    (s : ℝ) (hs : s ∈ Icc 0 1) (hmem : p s ∈ diskUpperArc '' Icc 0 1) :
    s=0 ∨ s=1 := by
  by_contra hn
  have hs0 : 0 < s := lt_of_le_of_ne hs.1 (by intro he; exact hn (Or.inl he.symm))
  have hs1 : s < 1 := lt_of_le_of_ne hs.2 (by intro he; exact hn (Or.inr he))
  obtain ⟨t,_ht,he⟩ := hmem
  have hh := hp s ⟨hs0,hs1⟩
  rw [← he,diskUpperArc_norm] at hh
  exact lt_irrefl _ hh

theorem disk_crosscut_upper_jordan
    (p : ℝ → ℂ) (hc : ContinuousOn p (Icc 0 1)) (hi : InjOn p (Icc 0 1))
    (h0 : p 0=-1) (h1 : p 1=1) (hp : ∀ s ∈ Ioo 0 1, ‖p s‖ < 1) :
    Schoenflies.IsJordanCurve
      (complexPlaneCoordinates '' (p '' Icc 0 1 ∪ diskUpperArc '' Icc 0 1)) := by
  have hpArc := complexPlaneCoordinates_isArcBetween p hc hi
  have haArc := complexPlaneCoordinates_isArcBetween diskUpperArc
    diskUpperArc_continuous.continuousOn diskUpperArc_injOn
  rw [diskUpperArc_zero,diskUpperArc_one,← h0,← h1] at haArc
  rw [image_union]
  apply Schoenflies.isJordanCurve_union hpArc haArc
  rintro _ ⟨_,⟨s,hs,rfl⟩,rfl⟩ ⟨_,⟨t,ht,rfl⟩,he⟩
  have het : diskUpperArc t=p s := complexPlaneCoordinates.injective he
  rcases disk_crosscut_meets_upper_at_endpoints p hp s hs ⟨t,ht,het⟩ with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

end SLEExactGauge

end

end OAI
