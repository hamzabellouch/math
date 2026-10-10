import OAI.Geometry.RCD.Harmonic.LogCoshQuadratic
import OAI.Geometry.RCD.Transport.ReducedDistortionPositive

namespace OAI

/-! # The midpoint dimension comparison before the conjugate radius -/

open Set Filter
noncomputable section
namespace RegularPointCoordinates

def logCosQuadraticNumerator (x : ℝ) : ℝ :=
  -x*(Real.sin x/Real.cos x)-2*Real.log (Real.cos x)

theorem logCosQuadraticNumerator_hasDerivAt {x : ℝ} (hc : Real.cos x ≠ 0) :
    HasDerivAt logCosQuadraticNumerator
      ((Real.sin x*Real.cos x-x)/(Real.cos x)^2) x := by
  have hd := (((hasDerivAt_id x).neg).mul
    ((Real.hasDerivAt_sin x).div (Real.hasDerivAt_cos x) hc)).sub
      (((Real.hasDerivAt_cos x).log hc).const_mul 2)
  convert hd using 1
  · rfl
  · dsimp only [id_eq,Pi.div_apply,Pi.neg_apply]
    field_simp
    nlinarith only [congrArg (fun y : ℝ => x*y) (Real.sin_sq_add_cos_sq x)]

theorem logCosQuadraticNumerator_nonpos {x : ℝ} (hx : 0 ≤ x) (hxp : x < Real.pi/2) :
    logCosQuadraticNumerator x ≤ 0 := by
  have hc (y : ℝ) (hy : y∈Ico 0 (Real.pi/2)) : Real.cos y ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hy.1,Real.pi_pos],hy.2⟩).ne'
  have hmono : AntitoneOn logCosQuadraticNumerator (Ico 0 (Real.pi/2)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ico (0:ℝ) (Real.pi/2))
      (fun y hy => (logCosQuadraticNumerator_hasDerivAt (hc y hy)).continuousAt.continuousWithinAt)
      (fun y hy => (logCosQuadraticNumerator_hasDerivAt (hc y (interior_subset hy))).hasDerivWithinAt)
    intro y hy
    have hy0 : 0 ≤ y := (interior_subset hy : y∈Ico 0 (Real.pi/2)).1
    have hs := Real.sin_le (show 0 ≤ 2*y by linarith)
    rw [Real.sin_two_mul] at hs
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
  have h := hmono (by constructor <;> linarith [Real.pi_pos] : (0:ℝ)∈Ico 0 (Real.pi/2)) ⟨hx,hxp⟩ hx
  simpa [logCosQuadraticNumerator] using h

theorem log_cos_div_sq_hasDerivAt {x : ℝ} (hx : x ≠ 0) (hc : Real.cos x ≠ 0) :
    HasDerivAt (fun y : ℝ => Real.log (Real.cos y)/y^2)
      (logCosQuadraticNumerator x/x^3) x := by
  have hd := ((Real.hasDerivAt_cos x).log hc).div
    ((hasDerivAt_id x).pow 2) (pow_ne_zero 2 hx)
  convert hd using 1
  · rfl
  · dsimp only [id_eq,Pi.pow_apply]
    norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one]
    change (-x*(Real.sin x/Real.cos x)-2*Real.log (Real.cos x))/x^3 =
      (-Real.sin x/Real.cos x*x^2-Real.log (Real.cos x)*(2*x))/(x^2)^2
    field_simp

theorem log_cos_div_sq_antitone :
    AntitoneOn (fun x : ℝ => Real.log (Real.cos x)/x^2) (Ioo 0 (Real.pi/2)) := by
  have hc (x : ℝ) (hx : x∈Ioo 0 (Real.pi/2)) : Real.cos x ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1,Real.pi_pos],hx.2⟩).ne'
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioo (0:ℝ) (Real.pi/2))
    (fun x hx => (log_cos_div_sq_hasDerivAt hx.1.ne' (hc x hx)).continuousAt.continuousWithinAt)
    (fun x hx => (log_cos_div_sq_hasDerivAt (interior_subset hx).1.ne'
      (hc x (interior_subset hx))).hasDerivWithinAt)
  intro x hx
  have hxx : x∈Ioo 0 (Real.pi/2) := interior_subset hx
  exact div_nonpos_of_nonpos_of_nonneg (logCosQuadraticNumerator_nonpos hxx.1.le hxx.2)
    (pow_nonneg hxx.1.le 3)

theorem log_cos_sqrt_mul_ge {c x : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hx : 0 ≤ x) (hxp : x < Real.pi/2) :
    c*Real.log (Real.cos x) ≤ Real.log (Real.cos (Real.sqrt c*x)) := by
  by_cases hx0 : x=0
  · simp [hx0]
  by_cases hc : c=0
  · simp [hc]
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hcp : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hc)
  have hspos := Real.sqrt_pos.mpr hcp
  have hs1 : Real.sqrt c ≤ 1 := by nlinarith [Real.sq_sqrt hc0]
  have hy : 0 < Real.sqrt c*x := mul_pos hspos hxpos
  have hxy : Real.sqrt c*x ≤ x := by nlinarith
  have h := log_cos_div_sq_antitone ⟨hy,hxy.trans_lt hxp⟩ ⟨hxpos,hxp⟩ hxy
  have hxs : 0 < x^2 := sq_pos_of_pos hxpos
  have hys : 0 < (Real.sqrt c*x)^2 := sq_pos_of_pos hy
  have he : (Real.sqrt c*x)^2 = c*x^2 := by rw [mul_pow,Real.sq_sqrt hc0]
  have hh := (div_le_div_iff₀ hxs hys).mp h
  rw [he] at hh
  have hmul : (c*Real.log (Real.cos x))*x^2 ≤ Real.log (Real.cos (Real.sqrt c*x))*x^2 := by
    simpa only [mul_comm,mul_left_comm,mul_assoc] using hh
  exact (mul_le_mul_iff_left₀ hxs).mp hmul

end RegularPointCoordinates

end

end OAI
