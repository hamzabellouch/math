import Mathlib

namespace OAI

namespace CylinderCovering.BeamAlgebra

theorem radial_cancellation_first (a N p c : ℝ) :
    (1 - a * N * p ^ 2) - (1 - a * N * c ^ 2) =
      -2 * a * N * (p-c) * p + a * N * (p-c)^2 := by
  ring

theorem radial_cancellation_second (a N p c : ℝ) :
    (-1 + a * N * (1-p)^2) - (-1 + a * N * (1-c)^2) =
      -2 * a * N * (p-c) * (1-p) - a * N * (p-c)^2 := by
  ring

theorem exact_gap_sum (a d p t : ℝ) :
    (-1 + (2-a+d)*p + t*(1-a*(2-a)*p^2)) +
      (-1 + (2-a+d)*(1-p) + t*(-1+a*(2-a)*(1-p)^2)) =
      -a - 2*a*t*((2-a)*(2*p-1)/2) + d := by
  ring

theorem exact_gap_difference (a d p t : ℝ) (ha : a ≠ 2) :
    ((-1 + (2-a+d)*p + t*(1-a*(2-a)*p^2)) -
      (-1 + (2-a+d)*(1-p) + t*(-1+a*(2-a)*(1-p)^2)))/2 =
      t + (2-a)*(2*p-1)/2 + d*(2*p-1)/2 -
        a*t*((2-a)/4 + ((2-a)*(2*p-1)/2)^2/(2-a)) := by
  have hN : 2 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  field_simp
  ring

theorem strict_gain_coefficient : (19 / 30 : ℝ) - Real.sqrt 2 / 2 < 0 := by
  have hsq := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hnonneg := Real.sqrt_nonneg (2:ℝ)
  nlinarith

theorem hasDerivAt_velocity_first (a N p : ℝ) :
    HasDerivAt (fun x : ℝ => 1-a*N*x^2) (-2*a*N*p) p := by
  have h := ((((hasDerivAt_id p).pow 2).const_mul (a*N)).const_sub (1:ℝ))
  convert h using 1
  all_goals first | rfl | (norm_num; ring)

theorem hasDerivAt_velocity_second (a N p : ℝ) :
    HasDerivAt (fun x : ℝ => -1+a*N*(1-x)^2) (-2*a*N*(1-p)) p := by
  have h := (((((hasDerivAt_id p).const_sub (1:ℝ)).pow 2).const_mul
    (a*N)).const_add (-1:ℝ))
  convert h using 1
  all_goals first | rfl | (norm_num; ring)

theorem parameter_bounds {a q : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1/2)
    (hq : |q| ≤ 1) :
    |(2-a)*q/2| ≤ 1 ∧
    0 ≤ (2-a)/4 + ((2-a)*q/2)^2/(2-a) ∧
    (2-a)/4 + ((2-a)*q/2)^2/(2-a) ≤ 1 := by
  have hN : 0 < 2-a := by linarith
  have hq2 : q^2 ≤ 1 := by nlinarith [abs_le.mp hq, sq_nonneg q]
  have hform : (2-a)/4 + ((2-a)*q/2)^2/(2-a) = (2-a)*(1+q^2)/4 := by
    field_simp
    ring
  rw [hform]
  have hb : |(2-a)*q/2| ≤ 1 := by
    rw [abs_div, abs_mul, abs_of_pos hN]
    norm_num
    have := mul_le_mul_of_nonneg_left hq (le_of_lt hN)
    nlinarith
  refine ⟨hb, ?_, ?_⟩
  · positivity
  · have := mul_le_mul_of_nonneg_left hq2 (le_of_lt hN)
    nlinarith

theorem sum_and_excess_bounds {a t s b b' d d' : ℝ}
    (ha : 0 ≤ a) (ht : |t| ≤ 1) (hb : |b| ≤ 1) (hb' : |b'| ≤ 1)
    (hd : 0 ≤ d) (hd' : 0 ≤ d')
    (hs : s = -a-2*a*t*b+d) (hs' : -s = -a-2*a*t*b'+d') :
    |s| ≤ 3*a ∧ d ≤ 6*a ∧ d' ≤ 6*a := by
  have htb : |t*b| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul ht hb (abs_nonneg b) (by norm_num)).trans_eq (by norm_num)
  have htb' : |t*b'| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul ht hb' (abs_nonneg b') (by norm_num)).trans_eq (by norm_num)
  have hlo := mul_le_mul_of_nonneg_left (abs_le.mp htb).1 ha
  have hhi := mul_le_mul_of_nonneg_left (abs_le.mp htb).2 ha
  have hlo' := mul_le_mul_of_nonneg_left (abs_le.mp htb').1 ha
  have hhi' := mul_le_mul_of_nonneg_left (abs_le.mp htb').2 ha
  refine ⟨abs_le.mpr ⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith

theorem radial_parameter_error {a t l b d q Q : ℝ}
    (ha : 0 ≤ a) (ht : |t| ≤ 1) (hq : |q| ≤ 1)
    (hd : 0 ≤ d) (hd' : d ≤ 6*a) (hQ : 0 ≤ Q) (hQ' : Q ≤ 1)
    (hl : l = t+b+d*q/2-a*t*Q) : |b-(l-t)| ≤ 4*a := by
  have hdq : |d*q/2| ≤ 3*a := by
    rw [abs_div, abs_mul, abs_of_nonneg hd]
    norm_num
    have := mul_le_mul_of_nonneg_left hq hd
    nlinarith
  have hatQ : |a*t*Q| ≤ a := by
    rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hQ]
    have hprod : |t| * Q ≤ 1 := by
      have := mul_le_mul_of_nonneg_right ht hQ
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hprod ha]
  calc
    |b-(l-t)| = |-(d*q/2) + a*t*Q| := by rw [hl]; congr 1; ring
    _ ≤ |-(d*q/2)| + |a*t*Q| := abs_add_le _ _
    _ ≤ 4*a := by rw [abs_neg]; linarith

theorem quadratic_parameter_error {a b z : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1/2) (hb : |b| ≤ 1) (hz : |z| ≤ 2)
    (herr : |b-z| ≤ 4*a) :
    |(2-a)/4 + b^2/(2-a) - (1+z^2)/2| ≤ 10*a := by
  have hN : 0 < 2-a := by linarith
  have hb2 : b^2 ≤ 1 := by nlinarith [abs_le.mp hb, sq_nonneg b]
  have hdecomp : (2-a)/4+b^2/(2-a)-(1+z^2)/2 =
      -a/4 + a*b^2/(2*(2-a)) + (b-z)*(b+z)/2 := by
    field_simp
    ring
  have hterm0 : |-a/4| = a/4 := by
    rw [abs_div, abs_neg, abs_of_nonneg ha]
    norm_num
  have hterm1nonneg : 0 ≤ a*b^2/(2*(2-a)) := by positivity
  have hterm1 : |a*b^2/(2*(2-a))| ≤ a/3 := by
    rw [abs_of_nonneg hterm1nonneg]
    apply (div_le_iff₀ (by positivity : 0 < 2*(2-a))).2
    have hprod := mul_nonneg ha (show 0 ≤ 1-2*a by linarith)
    have := mul_le_mul_of_nonneg_left hb2 ha
    nlinarith
  have hsum : |b+z| ≤ 3 := (abs_add_le b z).trans (by linarith)
  have hterm2 : |(b-z)*(b+z)/2| ≤ 6*a := by
    rw [abs_div, abs_mul]
    norm_num
    have := mul_le_mul herr hsum (abs_nonneg (b+z)) (by linarith : 0 ≤ 4*a)
    nlinarith
  rw [hdecomp]
  calc
    |-a/4 + a*b^2/(2*(2-a)) + (b-z)*(b+z)/2|
        ≤ |-a/4 + a*b^2/(2*(2-a))| + |(b-z)*(b+z)/2| := abs_add_le _ _
    _ ≤ (|-a/4| + |a*b^2/(2*(2-a))|) + |(b-z)*(b+z)/2| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ ≤ 10*a := by rw [hterm0]; linarith

theorem radial_factor_nonneg {a t q : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1/2)
    (ht : |t| ≤ 1) (hq : |q| ≤ 1) : 0 ≤ 1+a*t*q := by
  have hprod : |t*q| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul ht hq (abs_nonneg q) (by norm_num)).trans_eq (by norm_num)
  have := mul_le_mul_of_nonneg_left (abs_le.mp hprod).1 ha
  nlinarith

theorem central_strip_lower {a t s l b d q Q : ℝ}
    (ha : 0 ≤ a) (ht : |t| ≤ 1) (hd : 0 ≤ d)
    (hfactor : 0 ≤ 1+a*t*q)
    (hs : s = -a-2*a*t*b+d)
    (hl : l = t+b+d*q/2-a*t*Q)
    (hQ : |Q-(1+(l-t)^2)/2| ≤ 10*a) :
    -(a*(1-2*t^2)+a^2*t^2*(1+l^2+t^2)+20*a^3) ≤
      s+(2*a*t-2*a^2*t^3)*l := by
  have ht2 : t^2 ≤ 1 := by nlinarith [abs_le.mp ht, sq_nonneg t]
  have hcombine : s+2*a*t*l = -a+2*a*t^2-2*a^2*t^2*Q+d*(1+a*t*q) := by
    rw [hs, hl]
    ring
  have hscaled := mul_le_mul_of_nonneg_left (abs_le.mp hQ).2
    (show 0 ≤ 2*a^2*t^2 by positivity)
  have hcube : 0 ≤ 20*a^3 := by positivity
  have hterr := mul_le_mul_of_nonneg_left ht2 hcube
  have hradial := mul_nonneg hd hfactor
  nlinarith

theorem central_strip {a t s l b b' d d' q q' Q Q' : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1/2) (ht : |t| ≤ 1)
    (hd : 0 ≤ d) (hd' : 0 ≤ d') (hq : |q| ≤ 1) (hq' : |q'| ≤ 1)
    (hs : s = -a-2*a*t*b+d) (hs' : -s = -a-2*a*t*b'+d')
    (hl : l = t+b+d*q/2-a*t*Q) (hl' : -l = t+b'+d'*q'/2-a*t*Q')
    (hQ : |Q-(1+(l-t)^2)/2| ≤ 10*a)
    (hQ' : |Q'-(1+(-l-t)^2)/2| ≤ 10*a) :
    |s+(2*a*t-2*a^2*t^3)*l| ≤
      a*(1-2*t^2)+a^2*t^2*(1+l^2+t^2)+20*a^3 := by
  have hlow := central_strip_lower ha ht hd (radial_factor_nonneg ha ha' ht hq) hs hl hQ
  have hupp := central_strip_lower ha ht hd' (radial_factor_nonneg ha ha' ht hq') hs' hl' hQ'
  rw [neg_sq] at hupp
  exact abs_le.mpr ⟨hlow, by linarith⟩

theorem narrow_strip {a t s l : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1/2) (ht : |t| ≤ 1)
    (hs : |s| ≤ 3*a) (hl : |l| ≤ 1-|t|+|s|/2)
    (hstrip : |s+(2*a*t-2*a^2*t^3)*l| ≤
      a*(1-2*t^2)+a^2*t^2*(1+l^2+t^2)+20*a^3) :
    |s+(2*a*t-2*a^2*t^3)*l| ≤
      a*(1-2*t^2)+a^2*t^2*(1+(1-|t|)^2+t^2)+25*a^3 := by
  have hl' : |l| ≤ 1-|t|+3*a/2 := by linarith
  have hl2 := mul_self_le_mul_self (abs_nonneg l) hl'
  have habs2 : |l| * |l| = l^2 := by rw [← sq, sq_abs]
  rw [habs2] at hl2
  have ha2 := mul_le_mul_of_nonneg_left ha' ha
  have hat := mul_nonneg ha (abs_nonneg t)
  have hlbound : l^2 ≤ (1-|t|)^2+5*a := by nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hlbound
    (show 0 ≤ a^2*t^2 by positivity)
  have ht2 : t^2 ≤ 1 := by nlinarith [abs_le.mp ht, sq_nonneg t]
  have hterr := mul_le_mul_of_nonneg_left ht2 (show 0 ≤ 5*a^3 by positivity)
  nlinarith

theorem explicit_strip_bound {a t s l b b' d d' q q' : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1/2) (ht : |t| ≤ 1) (hlbound : |l| ≤ 1)
    (hgeom : |l| ≤ 1-|t|+|s|/2)
    (hd : 0 ≤ d) (hd' : 0 ≤ d') (hq : |q| ≤ 1) (hq' : |q'| ≤ 1)
    (hbdef : b = (2-a)*q/2) (hbdef' : b' = (2-a)*q'/2)
    (hs : s = -a-2*a*t*b+d) (hs' : -s = -a-2*a*t*b'+d')
    (hl : l = t+b+d*q/2-a*t*((2-a)/4+b^2/(2-a)))
    (hl' : -l = t+b'+d'*q'/2-a*t*((2-a)/4+b'^2/(2-a))) :
    |s+(2*a*t-2*a^2*t^3)*l| ≤
      max (a*(1-2*t^2)+a^2*t^2*(1+(1-|t|)^2+t^2)+25*a^3) 0 := by
  have hbdata := parameter_bounds ha ha' hq
  have hbdata' := parameter_bounds ha ha' hq'
  rw [← hbdef] at hbdata
  rw [← hbdef'] at hbdata'
  obtain ⟨hsbound, hdbound, hdbound'⟩ :=
    sum_and_excess_bounds ha ht hbdata.1 hbdata'.1 hd hd' hs hs'
  have hberr := radial_parameter_error ha ht hq hd hdbound hbdata.2.1 hbdata.2.2 hl
  have hberr' := radial_parameter_error ha ht hq' hd' hdbound' hbdata'.2.1 hbdata'.2.2 hl'
  have hz : |l-t| ≤ 2 := (abs_sub l t).trans (by linarith only [hlbound, ht])
  have hz' : |-l-t| ≤ 2 :=
    (abs_sub (-l) t).trans (by rw [abs_neg]; linarith only [hlbound, ht])
  have hQ := quadratic_parameter_error ha ha' hbdata.1 hz hberr
  have hQ' := quadratic_parameter_error ha ha' hbdata'.1 hz' hberr'
  have hcentral := central_strip ha ha' ht hd hd' hq hq' hs hs' hl hl' hQ hQ'
  exact (narrow_strip ha ha' ht hsbound hgeom hcentral).trans (le_max_left _ _)

end CylinderCovering.BeamAlgebra

end OAI
