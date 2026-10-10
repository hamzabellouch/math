import Mathlib

namespace OAI

noncomputable section

section
open Set
namespace NeutralAtom

lemma inv_upper_of_half_le {T a : ℝ} (hT : 0 < T) (ha : T/2 ≤ a) :
    a⁻¹ ≤ 2/T := by
  have ha0 : 0 < a := lt_of_lt_of_le (half_pos hT) ha
  calc
    a⁻¹ ≤ (T/2)⁻¹ := (inv_le_inv₀ ha0 (half_pos hT)).mpr ha
    _ = 2/T := by simp [div_eq_mul_inv]

lemma inv_sub_bound_of_half_le {T a b : ℝ}
    (hT : 0 < T) (ha : T/2 ≤ a) (hb : T/2 ≤ b) :
    |a⁻¹-b⁻¹| ≤ (4/T^2)*|a-b| := by
  have ha0 : 0 < a := lt_of_lt_of_le (half_pos hT) ha
  have hb0 : 0 < b := lt_of_lt_of_le (half_pos hT) hb
  rw [inv_sub_inv' ha0.ne' hb0.ne', abs_mul,abs_mul,
    abs_of_pos (inv_pos.mpr ha0),abs_of_pos (inv_pos.mpr hb0),abs_sub_comm b a]
  calc
    _ ≤ ((2/T)*|a-b|)*(2/T) := mul_le_mul
      (mul_le_mul_of_nonneg_right (inv_upper_of_half_le hT ha) (abs_nonneg _))
      (inv_upper_of_half_le hT hb) (inv_nonneg.mpr hb0.le)
      (mul_nonneg (by positivity) (abs_nonneg _))
    _ = _ := by ring

lemma inv_cube_sub_bound_of_half_le {T a b : ℝ}
    (hT : 0 < T) (ha : T/2 ≤ a) (hb : T/2 ≤ b) :
    |(a^3)⁻¹-(b^3)⁻¹| ≤ (48/T^4)*|a-b| := by
  have ha0 : 0 < a := lt_of_lt_of_le (half_pos hT) ha
  have hb0 : 0 < b := lt_of_lt_of_le (half_pos hT) hb
  have href : ∀ z ∈ Ici (T/2),
      HasDerivWithinAt (fun x : ℝ => x^(-3:ℝ)) (-3*z^(-4:ℝ)) (Ici (T/2)) z := by
    intro z hz
    have hd := (Real.hasDerivAt_rpow_const (x := z) (p := -3)
      (Or.inl (ne_of_gt (lt_of_lt_of_le (half_pos hT) hz)))).hasDerivWithinAt (s := Ici (T/2))
    norm_num only at hd
    exact hd
  have hbd : ∀ z ∈ Ici (T/2), ‖-3*z^(-4:ℝ)‖ ≤ 48/T^4 := by
    intro z hz
    have hz0 : 0 < z := lt_of_lt_of_le (half_pos hT) hz
    rw [norm_mul,Real.norm_eq_abs,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<3),
      Real.norm_of_nonneg (Real.rpow_nonneg hz0.le _)]
    calc
      _ ≤ 3*(T/2)^(-4:ℝ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (half_pos hT) hz (by norm_num)) (by norm_num)
      _ = 48/T^4 := by norm_num [Real.rpow_neg (le_of_lt (half_pos hT)),Real.rpow_natCast]; ring
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le href hbd (convex_Ici _)
    (show a ∈ Ici (T/2) from ha) (show b ∈ Ici (T/2) from hb)
  simpa only [Real.norm_eq_abs,show (-3:ℝ) = -(3:ℝ) by norm_num,
    Real.rpow_neg ha0.le,Real.rpow_neg hb0.le,Real.rpow_ofNat,abs_sub_comm] using hh

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def scaledCenterKernel (φ : E → ℝ) (t : E → ℝ) (z y : E) :=
  ((t z)^3)⁻¹ * φ ((t z)⁻¹ • (y-z))

lemma inverse_scaled_argument_bound {T a b : ℝ} (hT : 0 < T)
    (ha : T/2 ≤ a) (hb : T/2 ≤ b) (x v : E) (hv : ‖v‖ ≤ 2*T) :
    ‖a⁻¹ • x-b⁻¹ • v‖ ≤ (2/T)*‖x-v‖+(8/T)*|a-b| := by
  have ha0 : 0<a := lt_of_lt_of_le (half_pos hT) ha
  have he : a⁻¹ • x-b⁻¹ • v = a⁻¹ • (x-v)+(a⁻¹-b⁻¹) • v := by module
  rw [he]
  calc
    _ ≤ ‖a⁻¹ • (x-v)‖+‖(a⁻¹-b⁻¹) • v‖ := norm_add_le _ _
    _ = a⁻¹*‖x-v‖+|a⁻¹-b⁻¹| *‖v‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha0)]
    _ ≤ (2/T)*‖x-v‖+((4/T^2)*|a-b|)*(2*T) := add_le_add
      (mul_le_mul_of_nonneg_right (inv_upper_of_half_le hT ha) (norm_nonneg _))
      (mul_le_mul (inv_sub_bound_of_half_le hT ha hb) hv (norm_nonneg _)
        (mul_nonneg (by positivity) (abs_nonneg _)))
    _ = _ := by field_simp; ring

theorem scaled_kernel_local_bound {T a b B L : ℝ} (hT : 0 < T)
    (ha : T/2 ≤ a) (hb : T/2 ≤ b) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (φ : E → ℝ) (hφ : ∀ x, |φ x| ≤ B)
    (hφL : ∀ x v, |φ x-φ v| ≤ L*‖x-v‖)
    (x v : E) (hv : ‖v‖ ≤ 2*T) :
    |(a^3)⁻¹*φ (a⁻¹ • x)-(b^3)⁻¹*φ (b⁻¹ • v)| ≤
      ((48*B+64*L)/T^4)*|a-b|+(16*L/T^4)*‖x-v‖ := by
  have hb0 : 0<b := lt_of_lt_of_le (half_pos hT) hb
  have hb3 : (b^3)⁻¹ ≤ 8/T^3 := by
    have hh := pow_le_pow_left₀ (inv_nonneg.mpr hb0.le) (inv_upper_of_half_le hT hb) 3
    simpa only [inv_pow,div_pow,show (2:ℝ)^3=8 by norm_num] using hh
  have he : (a^3)⁻¹*φ (a⁻¹ • x)-(b^3)⁻¹*φ (b⁻¹ • v) =
      ((a^3)⁻¹-(b^3)⁻¹)*φ (a⁻¹ • x)+(b^3)⁻¹*(φ (a⁻¹ • x)-φ (b⁻¹ • v)) := by ring
  rw [he]
  calc
    _ ≤ |((a^3)⁻¹-(b^3)⁻¹)*φ (a⁻¹ • x)|+
        |(b^3)⁻¹*(φ (a⁻¹ • x)-φ (b⁻¹ • v))| := abs_add_le _ _
    _ = |(a^3)⁻¹-(b^3)⁻¹| *|φ (a⁻¹ • x)|+
        (b^3)⁻¹*|φ (a⁻¹ • x)-φ (b⁻¹ • v)| := by
      rw [abs_mul,abs_mul,abs_of_pos (inv_pos.mpr (pow_pos hb0 _))]
    _ ≤ ((48/T^4)*|a-b|)*B+(8/T^3)*
        (L*((2/T)*‖x-v‖+(8/T)*|a-b|)) := add_le_add
      ((mul_le_mul_of_nonneg_left (hφ _) (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (inv_cube_sub_bound_of_half_le hT ha hb) hB))
      (mul_le_mul hb3 ((hφL _ _).trans (mul_le_mul_of_nonneg_left
        (inverse_scaled_argument_bound hT ha hb x v hv) hL))
        (abs_nonneg _) (by positivity))
    _ = _ := by field_simp; ring

end NeutralAtom

end
open Set
namespace NeutralAtom
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma scaledCenterKernel_support (φ : E → ℝ) (t : E → ℝ)
    (hs : ∀ x, 1 < ‖x‖ → φ x = 0) (ht : ∀ z, 0 < t z)
    (z y : E) (hK : scaledCenterKernel φ t z y ≠ 0) : ‖y-z‖ ≤ t z := by
  by_contra h
  have hu : 1 < ‖(t z)⁻¹ • (y-z)‖ := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (ht z).le),←div_eq_inv_mul]
    exact (lt_div_iff₀ (ht z)).mpr (by simpa using lt_of_not_ge h)
  exact hK (by simp [scaledCenterKernel,hs _ hu])

lemma scaledCenterKernel_support_width (φ : E → ℝ) (t : E → ℝ)
    (hs : ∀ x, 1 < ‖x‖ → φ x = 0) (ht : ∀ z, 0 < t z)
    (hLip : ∀ x v, |t x-t v| ≤ ‖x-v‖/4)
    (z y : E) (hK : scaledCenterKernel φ t z y ≠ 0) :
    t z ∈ Icc (4*t y/5) (4*t y/3) ∧ ‖y-z‖ ≤ 4*t y/3 := by
  have hc := scaledCenterKernel_support φ t hs ht z y hK
  have hl := hLip z y
  rw [norm_sub_rev z y] at hl
  have hh : |t z-t y| ≤ t z/4 := hl.trans (by linarith)
  have hab := abs_le.mp hh
  constructor
  · constructor <;> linarith
  · linarith

lemma scaledCenterKernel_uniform_bound (φ : E → ℝ) (t : E → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hs : ∀ x, 1 < ‖x‖ → φ x = 0)
    (hφ : ∀ x, |φ x| ≤ B) (ht : ∀ z, 0 < t z)
    (hLip : ∀ x v, |t x-t v| ≤ ‖x-v‖/4) (z y : E) :
    |scaledCenterKernel φ t z y| ≤ 8*B/(t y)^3 := by
  have hT := ht y
  by_cases hK : scaledCenterKernel φ t z y=0
  · rw [hK,abs_zero]; positivity
  have hc := (scaledCenterKernel_support_width φ t hs ht hLip z y hK).1.1
  have hi := inv_upper_of_half_le (ht y) (show t y/2 ≤ t z by linarith [ht y])
  have hh := pow_le_pow_left₀ (inv_nonneg.mpr (ht z).le) hi 3
  have hh' : ((t z)^3)⁻¹ ≤ 8/(t y)^3 := by
    simpa only [inv_pow,div_pow,show (2:ℝ)^3=8 by norm_num] using hh
  rw [scaledCenterKernel,abs_mul,abs_of_pos (inv_pos.mpr (pow_pos (ht z) _))]
  calc
    _ ≤ (8/(t y)^3)*B := mul_le_mul hh' (hφ _) (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem scaledCenterKernel_center_lipschitz (φ : E → ℝ) (t : E → ℝ)
    {B L : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hs : ∀ x, 1 < ‖x‖ → φ x = 0) (hφ : ∀ x, |φ x| ≤ B)
    (hφL : ∀ x v, |φ x-φ v| ≤ L*‖x-v‖) (ht : ∀ z, 0 < t z)
    (hLip : ∀ x v, |t x-t v| ≤ ‖x-v‖/4) (z z' y : E) :
    |scaledCenterKernel φ t z y-scaledCenterKernel φ t z' y| ≤
      ((64*B+80*L)/(t y)^4)*‖z-z'‖ := by
  have hT := ht y
  have hordered (z z' : E) (hK : scaledCenterKernel φ t z y≠0) :
      |scaledCenterKernel φ t z y-scaledCenterKernel φ t z' y| ≤
        ((64*B+80*L)/(t y)^4)*‖z-z'‖ := by
    have hc := scaledCenterKernel_support_width φ t hs ht hLip z y hK
    by_cases hf : t y/4 ≤ ‖z-z'‖
    · calc
        _ ≤ |scaledCenterKernel φ t z y|+|scaledCenterKernel φ t z' y| := by simpa only [sub_zero,zero_sub,abs_neg] using (abs_sub_le (scaledCenterKernel φ t z y) 0 (scaledCenterKernel φ t z' y))
        _ ≤ 16*B/(t y)^3 := by
          have h₁ := scaledCenterKernel_uniform_bound φ t hB hs hφ ht hLip z y
          have h₂ := scaledCenterKernel_uniform_bound φ t hB hs hφ ht hLip z' y
          calc
            _ ≤ 8*B/(t y)^3+8*B/(t y)^3 := add_le_add h₁ h₂
            _ = _ := by ring
        _ = ((64*B)/(t y)^4)*(t y/4) := by field_simp; ring
        _ ≤ ((64*B+80*L)/(t y)^4)*‖z-z'‖ := mul_le_mul
          (div_le_div_of_nonneg_right (show 64*B ≤ 64*B+80*L by linarith) (pow_nonneg (ht y).le _)) hf
          (by positivity) (by positivity)
    · have hnear : ‖z-z'‖ < t y/4 := lt_of_not_ge hf
      have hab := abs_le.mp (hLip z z')
      have hb : t y/2 ≤ t z' := by linarith [hc.1.1]
      have ha : t y/2 ≤ t z := by linarith [hc.1.1,ht y]
      have hv : ‖y-z'‖ ≤ 2*t y := by
        have hh : ‖y-z'‖ ≤ ‖y-z‖+‖z-z'‖ := by
          simpa only [sub_add_sub_cancel] using (norm_add_le (y-z) (z-z'))
        linarith [hc.2]
      have hh := scaled_kernel_local_bound (ht y) ha hb hB hL φ hφ hφL (y-z) (y-z') hv
      have he : (y-z)-(y-z')=z'-z := by abel
      rw [he,norm_sub_rev z' z] at hh
      have had : |t z-t z'| ≤ ‖z-z'‖ := (hLip z z').trans (by linarith [norm_nonneg (z-z')])
      apply hh.trans
      calc
        _ ≤ ((48*B+64*L)/(t y)^4)*‖z-z'‖+(16*L/(t y)^4)*‖z-z'‖ :=
          add_le_add (mul_le_mul_of_nonneg_left had (by positivity)) le_rfl
        _ = ((48*B+80*L)/(t y)^4)*‖z-z'‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (show 48*B+80*L ≤ 64*B+80*L by linarith) (pow_nonneg (ht y).le _)) (norm_nonneg _)
  by_cases hz : scaledCenterKernel φ t z y=0
  · by_cases hz' : scaledCenterKernel φ t z' y=0
    · rw [hz,hz',sub_self,abs_zero]; positivity
    · simpa only [abs_sub_comm,norm_sub_rev] using hordered z' z hz'
  · exact hordered z z' hz

end NeutralAtom

end

end OAI
