import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPressureRatio
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMinimumPrinciple

namespace OAI

/-! The derivative maximum argument used to control inner pressure transport. -/

open Set Filter
namespace DefocusingNLS

theorem radial_local_max_second_nonpos (f : ℝ → ℝ) (x : ℝ)
    (hf : ContinuousAt f x) (hmax : IsLocalMax f x) :
    deriv (deriv f) x ≤ 0 := by
  have hh := radial_local_min_second_nonneg (fun t => -f t) x hf.neg hmax.neg
  have hn : deriv (fun t => -f t)=fun t => -deriv f t := deriv.neg'
  rw [hn] at hh
  change 0 ≤ deriv (-deriv f) x at hh
  rw [deriv.neg] at hh
  linarith

theorem radial_positive_slope_maximum (A : ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (hD : ContinuousOn (deriv A) (Icc 0 R))
    (hD0 : deriv A 0 ≤ 0) (hDR : deriv A R ≤ 0)
    (r : ℝ) (hr : r ∈ Icc 0 R) (hd : 0 < deriv A r) :
    ∃ x ∈ Ioo 0 R, 0 < deriv A x ∧
      (∀ t ∈ Icc 0 R, deriv A t ≤ deriv A x) ∧
      deriv (deriv A) x=0 ∧ deriv (deriv (deriv A)) x ≤ 0 := by
  obtain ⟨x,hx,hm⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hR.le) hD
  have hp : 0 < deriv A x := hd.trans_le (hm hr)
  have hx0 : 0 < x := by
    apply lt_of_le_of_ne hx.1
    intro he
    rw [← he] at hp
    exact (not_lt_of_ge hD0) hp
  have hxR : x < R := by
    apply lt_of_le_of_ne hx.2
    intro he
    rw [he] at hp
    exact (not_lt_of_ge hDR) hp
  have hl := hm.isLocalMax (Icc_mem_nhds hx0 hxR)
  exact ⟨x,⟨hx0,hxR⟩,hp,hm,hl.deriv_eq_zero,
    radial_local_max_second_nonpos _ x ((hD x hx).continuousAt (Icc_mem_nhds hx0 hxR)) hl⟩

theorem radial_amplitude_slope_max_relation (m : ℕ) (A V : ℝ → ℝ) (r d e v' : ℝ)
    (hr : r ≠ 0) (ha : 0 ≤ A r) (hd : 0 ≤ d) (he : e ≤ 0)
    (hA : HasDerivAt A d r) (hD : HasDerivAt (deriv A) 0 r)
    (hDD : HasDerivAt (deriv (deriv A)) e r) (hV : HasDerivAt V v' r)
    (hEq : (fun t => -deriv (deriv A) t-11/t*deriv A t+(A t)^(2*m+1))
      =ᶠ[nhds r] (fun t => V t*A t)) :
    (2*(m : ℝ))*(A r)^(2*m)*d ≤ V r*d+v'*A r := by
  have hquot := (hasDerivAt_const r (11 : ℝ)).div (hasDerivAt_id r) hr
  have hl := (hDD.neg.sub (hquot.mul hD)).add (hA.pow (2*m+1))
  have hh := hl.unique ((hV.mul hA).congr_of_eventuallyEq hEq)
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,Nat.add_sub_cancel,
    mul_zero,add_zero,id_eq] at hh
  rw [hA.deriv] at hh
  simp only [zero_mul,mul_one,zero_sub,neg_div,neg_mul,sub_neg_eq_add] at hh
  have hpos := mul_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 11) (sq_nonneg r)) hd
  have hP := mul_nonneg (pow_nonneg ha (2*m)) hd
  nlinarith [hh]

theorem radial_pressure_slope_bound (m : ℝ) (hm : 40 ≤ m)
    (A d P V w v' : ℝ) (ha : 0 < A) (ha1 : A ≤ 1) (hd : 0 ≤ d)
    (hP : (1/5 : ℝ) ≤ P) (hV : V+w^2 ≤ 4)
    (hmax : 2*m*P*d ≤ V*d+v'*A) (hv : v' ≤ 20/m+w^2*d/A) :
    d ≤ 100/m^2 := by
  have hm0 : 0 < m := by linarith
  have hva := mul_le_mul_of_nonneg_right hv ha.le
  have htwenty : 20/m*A ≤ 20/m := mul_le_of_le_one_right (by positivity) ha1
  have hcancel : w^2*d/A*A=w^2*d := by field_simp [ha.ne']
  rw [add_mul,hcancel] at hva
  have hmain : 2*m*P*d ≤ 4*d+20/m := by
    have hvd := mul_le_mul_of_nonneg_right hV hd
    nlinarith
  have hlower := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hP (by positivity : 0 ≤ 2*m)) hd
  have hmd : m/5*d ≤ 20/m := by nlinarith
  have hfinal := mul_le_mul_of_nonneg_right hmd hm0.le
  have hdiv : 20/m*m=(20 : ℝ) := by field_simp [hm0.ne']
  rw [hdiv] at hfinal
  apply (le_div_iff₀ (sq_pos_of_pos hm0)).2
  nlinarith

end DefocusingNLS

end OAI
