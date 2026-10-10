import OAI.Geometry.RCD.Transport.ReducedDistortionRecurrence

namespace OAI

/-! # The midpoint comparison for negative-curvature distortion

The logarithm of cosh divided by the square is decreasing. This gives
the exact dimension interpolation needed to compare the full CD and
reduced CD midpoint coefficients, rather than a Gaussian approximation.
-/

open Set Filter
noncomputable section
namespace RegularPointCoordinates

def logCoshQuadraticNumerator (x : ℝ) : ℝ :=
  x*(Real.sinh x/Real.cosh x)-2*Real.log (Real.cosh x)

theorem logCoshQuadraticNumerator_hasDerivAt (x : ℝ) :
    HasDerivAt logCoshQuadraticNumerator
      ((x-Real.sinh x*Real.cosh x)/(Real.cosh x)^2) x := by
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have hd := ((hasDerivAt_id x).mul
    ((Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc)).sub
      (((Real.hasDerivAt_cosh x).log hc).const_mul 2)
  convert hd using 1
  · rfl
  · dsimp only [id_eq,Pi.div_apply]
    rw [one_mul]
    change (x-Real.sinh x*Real.cosh x)/(Real.cosh x)^2 =
      Real.sinh x/Real.cosh x+x*((Real.cosh x*Real.cosh x-Real.sinh x*Real.sinh x)/
        (Real.cosh x)^2)-2*(Real.sinh x/Real.cosh x)
    field_simp
    nlinarith only [congrArg (fun y : ℝ => x*y) (Real.cosh_sq_sub_sinh_sq x)]

theorem logCoshQuadraticNumerator_nonpos {x : ℝ} (hx : 0 ≤ x) :
    logCoshQuadraticNumerator x ≤ 0 := by
  have hmono : AntitoneOn logCoshQuadraticNumerator (Ici 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici (0:ℝ))
      (fun x _ => (logCoshQuadraticNumerator_hasDerivAt x).continuousAt.continuousWithinAt)
      (fun x _ => (logCoshQuadraticNumerator_hasDerivAt x).hasDerivWithinAt)
    intro y hy
    have hy0 : 0 ≤ y := le_of_lt (by simpa only [interior_Ici,mem_Ioi] using hy : 0 < y)
    have hs := Real.self_le_sinh_iff.mpr (show 0 ≤ 2*y by linarith)
    rw [Real.sinh_two_mul] at hs
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
  have h := hmono (by simp : (0:ℝ)∈Ici 0) hx hx
  simpa [logCoshQuadraticNumerator] using h

theorem log_cosh_div_sq_hasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => Real.log (Real.cosh y)/y^2)
      (logCoshQuadraticNumerator x/x^3) x := by
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have hd := ((Real.hasDerivAt_cosh x).log hc).div
    ((hasDerivAt_id x).pow 2) (pow_ne_zero 2 hx)
  convert hd using 1
  · rfl
  · dsimp only [id_eq,Pi.pow_apply]
    norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one]
    change (x*(Real.sinh x/Real.cosh x)-2*Real.log (Real.cosh x))/x^3 =
      (Real.sinh x/Real.cosh x*x^2-Real.log (Real.cosh x)*(2*x))/(x^2)^2
    field_simp

theorem log_cosh_div_sq_antitone :
    AntitoneOn (fun x : ℝ => Real.log (Real.cosh x)/x^2) (Ioi 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi (0:ℝ))
    (fun x hx => (log_cosh_div_sq_hasDerivAt (ne_of_gt hx)).continuousAt.continuousWithinAt)
    (fun x hx => (log_cosh_div_sq_hasDerivAt (ne_of_gt (by simpa only [interior_Ioi,mem_Ioi] using hx : 0 < x))).hasDerivWithinAt)
  intro x hx
  have hx0 : 0 < x := by simpa only [interior_Ioi,mem_Ioi] using hx
  exact div_nonpos_of_nonpos_of_nonneg (logCoshQuadraticNumerator_nonpos hx0.le)
    (pow_nonneg hx0.le 3)

theorem log_cosh_sqrt_mul_ge {c x : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hx : 0 ≤ x) :
    c*Real.log (Real.cosh x) ≤ Real.log (Real.cosh (Real.sqrt c*x)) := by
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
  have h := log_cosh_div_sq_antitone hy hxpos hxy
  have hxs : 0 < x^2 := sq_pos_of_pos hxpos
  have hys : 0 < (Real.sqrt c*x)^2 := sq_pos_of_pos hy
  have he : (Real.sqrt c*x)^2 = c*x^2 := by rw [mul_pow,Real.sq_sqrt hc0]
  have hh := (div_le_div_iff₀ hxs hys).mp h
  rw [he] at hh
  have hmul : (c*Real.log (Real.cosh x))*x^2 ≤ Real.log (Real.cosh (Real.sqrt c*x))*x^2 := by
    simpa only [mul_comm,mul_left_comm,mul_assoc] using hh
  exact (mul_le_mul_iff_left₀ hxs).mp hmul

end RegularPointCoordinates

end

end OAI
