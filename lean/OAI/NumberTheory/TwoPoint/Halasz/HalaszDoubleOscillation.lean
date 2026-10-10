import OAI.NumberTheory.TwoPoint.Halasz.HalaszAffineAmplitude

namespace OAI

/-! Two integrations by parts for an affine-weighted logarithmic phase.
The exact boundary formula is used on the two sides of a triangular weight. -/
namespace TwoPointCorrelations

open MeasureTheory

noncomputable def halaszLogAmplitude0 (u v m c x : ℝ) : ℝ :=
  (m*x+c) / halaszLogSlope u v x

noncomputable def halaszLogAmplitude2 (u v m c x : ℝ) : ℝ :=
  m/(halaszLogSlope u v x)^2 +
    (m*x+c)*u/(x^2*(halaszLogSlope u v x)^3)

noncomputable def halaszLogAmplitude2Deriv (u v m c x : ℝ) : ℝ :=
  3*m*u/(x^2*(halaszLogSlope u v x)^3) -
    2*(m*x+c)*u/(x^3*(halaszLogSlope u v x)^3) +
    3*(m*x+c)*u^2/(x^4*(halaszLogSlope u v x)^4)

lemma halasz_log_amplitude0_deriv (u v m c x : ℝ) (hx : x ≠ 0)
    (hd : halaszLogSlope u v x ≠ 0) :
    HasDerivAt (halaszLogAmplitude0 u v m c)
      (m/(halaszLogSlope u v x) +
        (m*x+c)*halaszLogReciprocalDeriv u v x) x := by
  have hh := (((hasDerivAt_id x).const_mul m).add_const c).mul
    (halasz_log_reciprocal_deriv u v x hx hd)
  convert hh using 1
  · funext y
    simp only [halaszLogAmplitude0, div_eq_mul_inv, Pi.mul_apply, id_eq]
  · dsimp only [id_eq]
    ring

lemma halasz_log_amplitude2_deriv (u v m c x : ℝ) (hx : x ≠ 0)
    (hd : halaszLogSlope u v x ≠ 0) :
    HasDerivAt (halaszLogAmplitude2 u v m c)
      (halaszLogAmplitude2Deriv u v m c x) x := by
  have hD : HasDerivAt (halaszLogSlope u v) (-u/x^2) x := by
    convert ((hasDerivAt_const x u).div (hasDerivAt_id x) hx).sub_const v using 1
    · rfl
    · simp only [id_eq, zero_mul, mul_one, zero_sub, neg_div]
  have hw := ((hasDerivAt_id x).const_mul m).add_const c
  have h1 := (hasDerivAt_const x m).div (hD.pow 2) (pow_ne_zero 2 hd)
  have h2 := (hw.mul_const u).div
    (((hasDerivAt_id x).pow 2).mul (hD.pow 3))
    (mul_ne_zero (pow_ne_zero 2 hx) (pow_ne_zero 3 hd))
  convert h1.add h2 using 1
  · rfl
  · dsimp only [halaszLogAmplitude2Deriv, id_eq, Pi.pow_apply, Pi.mul_apply]
    norm_num only [Nat.cast_ofNat, Nat.reduceSub]
    field_simp [hx, hd]
    ring

noncomputable def halaszLogDoublePrimitive (u v m c x : ℝ) : ℂ :=
  halaszLogPhase u v x * ((halaszLogAmplitude2 u v m c x:ℂ) -
    Complex.I*(halaszLogAmplitude0 u v m c x:ℂ))

lemma halasz_log_double_primitive_deriv (u v m c x : ℝ) (hx : x ≠ 0)
    (hd : halaszLogSlope u v x ≠ 0) :
    HasDerivAt (halaszLogDoublePrimitive u v m c)
      (((m*x+c:ℝ):ℂ)*halaszLogPhase u v x +
        (halaszLogAmplitude2Deriv u v m c x:ℂ)*halaszLogPhase u v x) x := by
  have hh := (halasz_log_phase_deriv u v x hx).mul
    ((halasz_log_amplitude2_deriv u v m c x hx hd).ofReal_comp.sub
      ((halasz_log_amplitude0_deriv u v m c x hx hd).ofReal_comp.const_mul Complex.I))
  convert hh using 1
  · rfl
  · dsimp only [halaszLogAmplitude0, halaszLogAmplitude2, halaszLogReciprocalDeriv, Pi.sub_apply]
    push_cast
    have hx' : (x:ℂ) ≠ 0 := by exact_mod_cast hx
    have hd' : (halaszLogSlope u v x:ℂ) ≠ 0 := by exact_mod_cast hd
    field_simp [hx', hd']
    ring_nf
    simp only [Complex.I_sq]
    ring

lemma halasz_log_amplitude2_deriv_continuousOn (u v m c a b : ℝ) (ha : 0 < a)
    (hd : ∀ x ∈ Set.Icc a b, halaszLogSlope u v x ≠ 0) :
    ContinuousOn (halaszLogAmplitude2Deriv u v m c) (Set.Icc a b) := by
  have hx (x : ℝ) (h : x ∈ Set.Icc a b) : x ≠ 0 := (ha.trans_le h.1).ne'
  have hD : ContinuousOn (halaszLogSlope u v) (Set.Icc a b) :=
    (continuousOn_const.div continuousOn_id hx).sub continuousOn_const
  have hw : ContinuousOn (fun x : ℝ => m*x+c) (Set.Icc a b) :=
    (continuousOn_const.mul continuousOn_id).add continuousOn_const
  apply ContinuousOn.add
  · apply ContinuousOn.sub
    · exact continuousOn_const.div ((continuousOn_id.pow 2).mul (hD.pow 3))
        (fun x h => mul_ne_zero (pow_ne_zero 2 (hx x h)) (pow_ne_zero 3 (hd x h)))
    · exact ((continuousOn_const.mul hw).mul continuousOn_const).div
        ((continuousOn_id.pow 3).mul (hD.pow 3))
        (fun x h => mul_ne_zero (pow_ne_zero 3 (hx x h)) (pow_ne_zero 3 (hd x h)))
  · exact ((continuousOn_const.mul hw).mul continuousOn_const).div
      ((continuousOn_id.pow 4).mul (hD.pow 4))
      (fun x h => mul_ne_zero (pow_ne_zero 4 (hx x h)) (pow_ne_zero 4 (hd x h)))

theorem halasz_log_double_integral (u v m c a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hd : ∀ x ∈ Set.Icc a b, halaszLogSlope u v x ≠ 0) :
    (∫ x in a..b, ((m*x+c:ℝ):ℂ)*halaszLogPhase u v x) =
      halaszLogDoublePrimitive u v m c b - halaszLogDoublePrimitive u v m c a -
        ∫ x in a..b, (halaszLogAmplitude2Deriv u v m c x:ℂ)*halaszLogPhase u v x := by
  have hphase := halasz_log_phase_continuousOn u v a b ha
  have hwi : IntervalIntegrable (fun x => ((m*x+c:ℝ):ℂ)*halaszLogPhase u v x) volume a b :=
    ((Complex.continuous_ofReal.comp_continuousOn
      ((continuousOn_const.mul continuousOn_id).add continuousOn_const)).mul hphase).intervalIntegrable_of_Icc hab
  have hdi : IntervalIntegrable (fun x => (halaszLogAmplitude2Deriv u v m c x:ℂ)*
      halaszLogPhase u v x) volume a b :=
    ((Complex.continuous_ofReal.comp_continuousOn
      (halasz_log_amplitude2_deriv_continuousOn u v m c a b ha hd)).mul hphase).intervalIntegrable_of_Icc hab
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => halasz_log_double_primitive_deriv u v m c x
      (ha.trans_le (show x ∈ Set.Icc a b from by simpa only [Set.uIcc_of_le hab] using hx).1).ne'
      (hd x (by simpa only [Set.uIcc_of_le hab] using hx))) (hwi.add hdi)
  rw [intervalIntegral.integral_add hwi hdi] at he
  exact eq_sub_of_add_eq he

end TwoPointCorrelations

end OAI
