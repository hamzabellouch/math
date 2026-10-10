import OAI.Geometry.RCD.Transport.RenyiTangent

namespace OAI

/-! # The quadratic remainder for finite Rényi reweighting

For the negative power of a positive density, its matching primitive is
`(q-1)/q * r^q`. Multiplying the power derivative by the initial density
leaves only a quadratic remainder. This is the scalar estimate needed to
identify the transport first variation.
-/

open Set
noncomputable section
namespace RegularPointCoordinates

def renyiDualPower (q r : ℝ) : ℝ := (q-1)/q*r^q

theorem renyiDualPower_hasDerivAt {q r : ℝ} (hq : q≠0) (hr : 0<r) :
    HasDerivAt (renyiDualPower q) ((q-1)*r^(q-1)) r := by
  have h := (Real.hasDerivAt_rpow_const (p := q) (Or.inl hr.ne')).const_mul ((q-1)/q)
  convert h using 1
  · rfl
  · field_simp

theorem renyi_reweight_remainder {ε a b q : ℝ} (hε : 0<ε)
    (ha : ε≤a) (hb : ε≤b) (hq0 : 0<q) (hq1 : q<1) :
    |(renyiDualPower q b-renyiDualPower q a)/a-(b^(q-1)-a^(q-1))| ≤
      (|q-1|/ε*ε^(q-2))*(b-a)^2 := by
  let F : ℝ → ℝ := fun s => (renyiDualPower q s-renyiDualPower q a)/a-
    (s^(q-1)-a^(q-1))
  let D : ℝ → ℝ := fun s => (q-1)/a*s^(q-2)*(s-a)
  have hap : 0<a := hε.trans_le ha
  have hs (s : ℝ) (hs : s∈uIcc a b) : ε ≤ s :=
    (le_min ha hb).trans hs.1
  have hd (s : ℝ) (hsm : s∈uIcc a b) : HasDerivAt F (D s) s := by
    have hp : 0 < s := hε.trans_le (hs s hsm)
    have h := ((renyiDualPower_hasDerivAt hq0.ne' hp).sub_const
      (renyiDualPower q a)).div_const a |>.sub
      ((Real.hasDerivAt_rpow_const (p := q-1) (Or.inl hp.ne')).sub_const (a^(q-1)))
    convert h using 1
    have he : s^(q-2)*s=s^(q-1) := by
      conv_lhs => arg 2; rw [←Real.rpow_one s]
      rw [←Real.rpow_add hp]
      congr 1
      ring
    dsimp [D]
    rw [show q-1-1=q-2 by ring]
    field_simp
    nlinarith only [congrArg (fun z : ℝ => (q-1)*z) he]
  have hbound (s : ℝ) (hsm : s∈uIcc a b) :
      ‖D s‖≤(|q-1|/ε*ε^(q-2))*|b-a| := by
    have hp := hε.trans_le (hs s hsm)
    have hi : |q-1|/a≤|q-1|/ε :=
      div_le_div_of_nonneg_left (abs_nonneg _) hε ha
    have hpow : s^(q-2)≤ε^(q-2) :=
      Real.rpow_le_rpow_of_nonpos hε (hs s hsm) (by linarith)
    have hr := abs_sub_left_of_mem_uIcc hsm
    dsimp [D]
    rw [abs_mul,abs_mul,abs_div,abs_of_pos hap,
      abs_of_nonneg (Real.rpow_nonneg hp.le _)]
    exact mul_le_mul (mul_le_mul hi hpow (Real.rpow_nonneg hp.le _)
      (div_nonneg (abs_nonneg _) hε.le)) hr (abs_nonneg _)
      (mul_nonneg (div_nonneg (abs_nonneg _) hε.le) (Real.rpow_nonneg hε.le _))
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (hd s hs).hasDerivWithinAt) hbound (convex_uIcc a b)
    (left_mem_uIcc : a∈uIcc a b) (right_mem_uIcc : b∈uIcc a b)
  have he : |b-a| * |b-a| = (b-a)^2 := by rw [←pow_two,sq_abs]
  simpa only [F,sub_self,zero_div,sub_zero,Real.norm_eq_abs,mul_assoc,he] using h

end RegularPointCoordinates

end

end OAI
