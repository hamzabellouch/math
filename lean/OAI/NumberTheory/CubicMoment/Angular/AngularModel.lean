import OAI.NumberTheory.CubicMoment.Estimates.FixedAngularHecke

namespace OAI

/-!
# The sharp fixed-angular prime model

The input is the explicit published Hecke prime estimate, not a weighted
prime-model asymptotic.  Partial summation with `x^(-1/6)/log x` derives
the required little-oh at the sharp first-moment scale.
-/

noncomputable section
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology

namespace CubicFirstMoment

lemma fixedAngular_chebyshev_div_tendsto_zero (hEF : FixedAngularPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) :
    Tendsto (fun X => ‖primeChebyshev (theta ℓ) X‖ / X) atTop (𝓝 0) := by
  obtain ⟨C, X₀, hC, hX₀, hbound⟩ :=
    fixedAngular_chebyshev_logSaving hEF ℓ hℓ 1 1 zero_lt_one zero_lt_one
  have hlim : Tendsto (fun X : ℝ => C / Real.log X) atTop (𝓝 0) :=
    Real.tendsto_log_atTop.const_div_atTop C
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hsmall := (tendsto_order.mp hlim).2 ε hε
  filter_upwards [hsmall, eventually_ge_atTop X₀,
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with X hsmall hX hlog
  have hX₁ : 1 < X := hX₀.trans_le hX
  have hXpos : 0 < X := zero_lt_one.trans hX₁
  have hc := hbound X hX 1 1 primary_one primary_one
    squarefree_one squarefree_one (isCoprime_one_left)
    (by simpa [norm] using hlog)
  have he : angularMixedCubic ℓ 1 1 = theta ℓ := by
    funext p
    simp [angularMixedCubic, mixedCubic, cubicSymbol_one_lower]
  rw [he] at hc
  have hr : ‖primeChebyshev (theta ℓ) X‖ / X ≤ C / Real.log X := by
    apply (div_le_div_of_nonneg_right hc hXpos.le).trans_eq
    simp only [Real.rpow_one]
    field_simp
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (_root_.norm_nonneg _) hXpos.le)]
  exact hr.trans_lt hsmall

def angularAbelWeight (X : ℝ) : ℝ := X ^ (-1 / 6 : ℝ) / Real.log X

def angularAbelDerivative (X : ℝ) : ℝ :=
  -(X ^ (-7 / 6 : ℝ) / Real.log X) * (1 / 6 + 1 / Real.log X)

lemma hasDerivAt_angularAbelWeight {X : ℝ} (hX : 1 < X) :
    HasDerivAt angularAbelWeight (angularAbelDerivative X) X := by
  have hXpos : 0 < X := zero_lt_one.trans hX
  have hp := Real.hasDerivAt_rpow_const (x := X) (p := (-1 / 6 : ℝ))
    (Or.inl hXpos.ne')
  have hl := Real.hasDerivAt_log hXpos.ne'
  have hm : X ^ (-1 / 6 : ℝ) = X ^ (-7 / 6 : ℝ) * X := by
    rw [← Real.rpow_add_one hXpos.ne']
    norm_num
  convert hp.div hl (Real.log_pos hX).ne' using 1
  · rfl
  · norm_num only at *
    dsimp [angularAbelDerivative]
    rw [hm]
    field_simp [(Real.log_pos hX).ne']
    ring

lemma angularAbelDerivative_continuousOn :
    ContinuousOn angularAbelDerivative (Set.Ioi 1) := by
  intro X hX
  have hXpos : 0 < X := zero_lt_one.trans hX
  have hlog : Real.log X ≠ 0 := (Real.log_pos hX).ne'
  exact (((Real.continuousAt_rpow_const X (-7 / 6) (Or.inl hXpos.ne')).div
    (Real.continuousAt_log hXpos.ne') hlog).neg.mul
    (continuousAt_const.add (continuousAt_const.div
      (Real.continuousAt_log hXpos.ne') hlog))).continuousWithinAt

lemma angularAbel_boundary_ratio (a X : ℝ) (hX : 1 < X) :
    angularAbelWeight X * a / firstMomentScale X = a / X := by
  have hXpos : 0 < X := zero_lt_one.trans hX
  have hm : X ^ (5 / 6 : ℝ) = X ^ (-1 / 6 : ℝ) * X := by
    rw [← Real.rpow_add_one hXpos.ne']
    norm_num
  unfold angularAbelWeight firstMomentScale
  rw [hm]
  field_simp [(Real.log_pos hX).ne']

lemma angularAbel_integrand_ratio (a X : ℝ) (hX : 1 < X)
    (hlog : 2 < Real.log X) :
    |angularAbelDerivative X| * a / firstMomentScaleDerivative X =
      (a / X) * ((1 / 6 + 1 / Real.log X) / (5 / 6 - 1 / Real.log X)) := by
  have hXpos : 0 < X := zero_lt_one.trans hX
  have hlogpos : 0 < Real.log X := Real.log_pos hX
  have hderiv : angularAbelDerivative X ≤ 0 := by
    unfold angularAbelDerivative
    have : 0 ≤ 1 / 6 + 1 / Real.log X := by positivity
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) this
  have hm : X ^ (-1 / 6 : ℝ) = X ^ (-7 / 6 : ℝ) * X := by
    rw [← Real.rpow_add_one hXpos.ne']
    norm_num
  have hi : 1 / Real.log X < 1 / 2 := one_div_lt_one_div_of_lt (by norm_num) hlog
  have hd : (5 / 6 : ℝ) - 1 / Real.log X ≠ 0 := by linarith
  rw [abs_of_nonpos hderiv]
  unfold angularAbelDerivative firstMomentScaleDerivative
  rw [hm]
  field_simp

/-- The version of scale comparison starting at two, where the logarithmic
Abel weight is regular. Only its limit-zero case is needed. -/
lemma integral_from_two_div_scale_tendsto_zero (f : ℝ → ℝ)
    (hint : ∀ X : ℝ, 2 ≤ X → IntervalIntegrable f volume 2 X)
    (hlim : Tendsto (fun X => f X / firstMomentScaleDerivative X) atTop (𝓝 0)) :
    Tendsto (fun X => (∫ t in 2..X, f t) / firstMomentScale X) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hr := Metric.tendsto_nhds.mp hlim (ε / 2) (by positivity)
  have hlog := Real.tendsto_log_atTop.eventually (eventually_gt_atTop (2 : ℝ))
  obtain ⟨A, hA⟩ := eventually_atTop.mp
    ((hr.and hlog).and (eventually_ge_atTop (2 : ℝ)))
  have hA₂ : 2 ≤ A := (hA A le_rfl).2
  have hA₁ : 1 < A := lt_of_lt_of_le (by norm_num) hA₂
  let C := ∫ t in 2..A, f t
  have hC : Tendsto (fun X => |C| / firstMomentScale X) atTop (𝓝 0) :=
    tendsto_firstMomentScale.const_div_atTop |C|
  have he := (tendsto_order.mp hC).2 (ε / 2) (by positivity)
  filter_upwards [eventually_ge_atTop A, he] with X hX hsmall
  have hX₂ : 2 ≤ X := hA₂.trans hX
  have hX₁ : 1 < X := hA₁.trans_le hX
  have hsX : 0 < firstMomentScale X := firstMomentScale_pos hX₁
  have hsA : 0 < firstMomentScale A := firstMomentScale_pos hA₁
  have hdint : IntervalIntegrable firstMomentScaleDerivative volume A X := by
    apply ContinuousOn.intervalIntegrable_of_Icc hX
    apply firstMomentScaleDerivative_continuousOn.mono
    intro t ht
    exact hA₁.trans_le ht.1
  have hFTC : (∫ t in A..X, firstMomentScaleDerivative t) =
      firstMomentScale X - firstMomentScale A := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hdint
    intro t ht
    rw [Set.uIcc_of_le hX] at ht
    exact hasDerivAt_firstMomentScale (hA₁.trans_le ht.1)
  have hfint : IntervalIntegrable f volume A X :=
    (hint A hA₂).symm.trans (hint X hX₂)
  have htail : ‖∫ t in A..X, f t‖ ≤
      ε / 2 * (firstMomentScale X - firstMomentScale A) := by
    have hb : ∀ᵐ t : ℝ, t ∈ Set.Ioc A X →
        ‖f t‖ ≤ ε / 2 * firstMomentScaleDerivative t := by
      apply Filter.Eventually.of_forall
      intro t ht
      have hat := hA t ht.1.le
      have hdt : 0 < firstMomentScaleDerivative t :=
        firstMomentScaleDerivative_pos (lt_of_lt_of_le (by norm_num) hat.2) hat.1.2
      have hclose : |f t / firstMomentScaleDerivative t| < ε / 2 := by
        simpa only [Real.dist_eq, sub_zero] using hat.1.1
      rw [← div_mul_cancel₀ (f t) hdt.ne', norm_mul, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos hdt]
      exact mul_le_mul_of_nonneg_right hclose.le hdt.le
    have hi := intervalIntegral.norm_integral_le_of_norm_le hX hb (hdint.const_mul (ε / 2))
    simpa only [intervalIntegral.integral_const_mul, hFTC] using hi
  have heq : (∫ t in 2..X, f t) = C + ∫ t in A..X, f t := by
    exact (intervalIntegral.integral_add_adjacent_intervals (hint A hA₂) hfint).symm
  have hbound : |∫ t in 2..X, f t| ≤ |C| + ε / 2 * firstMomentScale X := by
    rw [heq]
    calc
      _ ≤ |C| + |∫ t in A..X, f t| := abs_add_le _ _
      _ ≤ |C| + ε / 2 * (firstMomentScale X - firstMomentScale A) := by
        simpa only [Real.norm_eq_abs] using add_le_add (le_refl |C|) htail
      _ ≤ _ := by nlinarith
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hsX]
  calc
    _ ≤ (|C| + ε / 2 * firstMomentScale X) / firstMomentScale X :=
      div_le_div_of_nonneg_right hbound hsX.le
    _ = |C| / firstMomentScale X + ε / 2 := by field_simp
    _ < ε := by linarith

def angularChebyshevIntegrand (ℓ : ℤ) (t : ℝ) : ℝ :=
  |angularAbelDerivative t| * ‖primeChebyshev (theta ℓ) t‖

lemma angularChebyshevIntegrand_intervalIntegrable (ℓ : ℤ) {X : ℝ} (hX : 2 ≤ X) :
    IntervalIntegrable (angularChebyshevIntegrand ℓ) volume 2 X := by
  have hd : IntegrableOn (fun t : ℝ => (angularAbelDerivative t : ℂ)) (Set.Icc 2 X) := by
    apply ContinuousOn.integrableOn_Icc
    exact Complex.continuous_ofReal.comp_continuousOn
      (angularAbelDerivative_continuousOn.mono (fun t ht => lt_of_lt_of_le (by norm_num) ht.1))
  have hi := (integrableOn_mul_sum_Icc (m := 0)
    (primeNormCoefficient X (fun p => theta ℓ p * (Real.log (norm p) : ℂ)))
    (by norm_num : (0 : ℝ) ≤ 2) hd).norm
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hX]
  apply IntegrableOn.congr_fun hi _ measurableSet_Icc
  intro t ht
  dsimp only
  rw [primeNormCoefficient_cumulative X t _ (by linarith [ht.1]) ht.2]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, angularChebyshevIntegrand,
    primeChebyshev]

lemma angularChebyshev_integral_div_scale_tendsto_zero
    (hEF : FixedAngularPrimeExplicitEstimate) (ℓ : ℤ) (hℓ : ℓ ≠ 0) :
    Tendsto (fun X => (∫ t in 2..X, angularChebyshevIntegrand ℓ t) / firstMomentScale X)
      atTop (𝓝 0) := by
  apply integral_from_two_div_scale_tendsto_zero _
    (fun X hX => angularChebyshevIntegrand_intervalIntegrable ℓ hX)
  have hi : Tendsto (fun X : ℝ => 1 / Real.log X) atTop (𝓝 0) := by
    have h := Real.tendsto_log_atTop.inv_tendsto_atTop
    change Tendsto (fun X : ℝ => (Real.log X)⁻¹) atTop (𝓝 0) at h
    simpa only [one_div] using h
  have hr : Tendsto (fun X => (1 / 6 + 1 / Real.log X) / (5 / 6 - 1 / Real.log X))
      atTop (𝓝 ((1 / 6 + 0 : ℝ) / (5 / 6 - 0))) :=
    (tendsto_const_nhds.add hi).div (tendsto_const_nhds.sub hi)
      (by norm_num : (5 / 6 : ℝ) - 0 ≠ 0)
  have hm := (fixedAngular_chebyshev_div_tendsto_zero hEF ℓ hℓ).mul hr
  norm_num only [zero_mul] at hm
  apply hm.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (2 : ℝ))] with X hX hlog
  exact (angularAbel_integrand_ratio _ X hX hlog).symm

private lemma primaryPrime_norm_gt_one {p : Eisenstein} (hp : primaryPrime p) :
    1 < norm p := by
  have hp₀ := normNat_ne_zero hp.2.ne_zero
  have hp₁ : normNat p ≠ 1 := by
    intro h
    apply hp.2.not_isUnit
    apply isUnit_of_norm_eq_one
    rw [← normNat_cast, h, Nat.cast_one]
  rw [← normNat_cast]
  exact_mod_cast (show 1 < normNat p by omega)

private lemma primeNormCoefficient_log (R : ℝ) (χ : Eisenstein → ℂ) (n : ℕ) :
    primeNormCoefficient R (fun p => χ p * (Real.log (norm p) : ℂ)) n =
      primeNormCoefficient R χ n * (Real.log (n : ℝ) : ℂ) := by
  unfold primeNormCoefficient
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hn : n = normNat p
  · have he : norm p = (n : ℝ) := by rw [← normNat_cast, ← hn]
    simp [hn, he]
  · simp [hn]

private lemma primeNormCoefficient_weighted_prefix (X : ℝ) (f : ℝ → ℂ)
    (χ : Eisenstein → ℂ) (hX : 0 ≤ X) :
    (∑ n ∈ Finset.Icc 0 ⌊X⌋₊, f n * primeNormCoefficient X χ n) =
      ∑ p ∈ primeCutoff X, f (norm p) * χ p := by
  simp only [primeNormCoefficient, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  have hpn : normNat p ≤ ⌊X⌋₊ := (Nat.le_floor_iff hX).mpr
    (by rw [normNat_cast]; exact (mem_primeCutoff.mp hp).2)
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_Icc,
    Nat.zero_le, true_and, ite_eq_left hpn, normNat_cast]

/-- The angular power-weighted sum before multiplying by `cStar`. -/
def angularWeightedPrimeSum (ℓ : ℤ) (X : ℝ) : ℂ :=
  primeCutoffSum (fun p => theta ℓ p * ((norm p ^ (-1 / 6 : ℝ) : ℝ) : ℂ)) X

lemma angularWeightedPrimeSum_abel (ℓ : ℤ) {X : ℝ} (hX : 2 ≤ X) :
    angularWeightedPrimeSum ℓ X =
      (angularAbelWeight X : ℂ) * primeChebyshev (theta ℓ) X -
        ∫ t in 2..X, (angularAbelDerivative t : ℂ) * primeChebyshev (theta ℓ) t := by
  let χ := fun p => theta ℓ p * (Real.log (norm p) : ℂ)
  let c := primeNormCoefficient X χ
  let f := fun t : ℝ => (angularAbelWeight t : ℂ)
  have hc₀ : c 0 = 0 := by simp [c, χ, primeNormCoefficient_log]
  have hc₁ : c 1 = 0 := by simp [c, χ, primeNormCoefficient_log]
  have hderiv : ∀ t ∈ Set.Icc 2 X, deriv f t = (angularAbelDerivative t : ℂ) := by
    intro t ht
    exact (hasDerivAt_angularAbelWeight (lt_of_lt_of_le (by norm_num) ht.1)).ofReal_comp.deriv
  have hdiff : ∀ t ∈ Set.Icc 2 X, DifferentiableAt ℝ f t := by
    intro t ht
    exact (hasDerivAt_angularAbelWeight
      (lt_of_lt_of_le (by norm_num) ht.1)).ofReal_comp.differentiableAt
  have hint : IntegrableOn (deriv f) (Set.Icc 2 X) := by
    apply IntegrableOn.congr_fun ?_ (fun t ht => (hderiv t ht).symm) measurableSet_Icc
    apply ContinuousOn.integrableOn_Icc
    exact Complex.continuous_ofReal.comp_continuousOn
      (angularAbelDerivative_continuousOn.mono (fun t ht => lt_of_lt_of_le (by norm_num) ht.1))
  have h := sum_mul_eq_sub_integral_mul₁ c hc₀ hc₁ X hdiff hint
  have hleft : (∑ n ∈ Finset.Icc 0 ⌊X⌋₊, f n * c n) = angularWeightedPrimeSum ℓ X := by
    rw [primeNormCoefficient_weighted_prefix X f χ (by linarith)]
    unfold angularWeightedPrimeSum
    rw [primeCutoffSum_eq_sum]
    apply Finset.sum_congr rfl
    intro p hp
    have hl : Real.log (norm p) ≠ 0 :=
      (Real.log_pos (primaryPrime_norm_gt_one (mem_primeCutoff.mp hp).1)).ne'
    dsimp [f, χ, angularAbelWeight]
    push_cast
    field_simp [show (Real.log (norm p) : ℂ) ≠ 0 by exact_mod_cast hl]
  rw [hleft, primeNormCoefficient_cumulative X X χ (by linarith) le_rfl,
    ← intervalIntegral.integral_of_le hX] at h
  have hi : (∫ t in 2..X, deriv f t * ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) =
      ∫ t in 2..X, (angularAbelDerivative t : ℂ) * primeChebyshev (theta ℓ) t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hX] at ht
    dsimp only
    rw [hderiv t ht, primeNormCoefficient_cumulative X t χ (by linarith [ht.1]) ht.2]
    rfl
  rw [hi] at h
  exact h

lemma angularWeightedPrimeSum_norm_le (ℓ : ℤ) {X : ℝ} (hX : 2 ≤ X) :
    ‖angularWeightedPrimeSum ℓ X‖ ≤
      angularAbelWeight X * ‖primeChebyshev (theta ℓ) X‖ +
        ∫ t in 2..X, angularChebyshevIntegrand ℓ t := by
  have hW : 0 ≤ angularAbelWeight X := by
    unfold angularAbelWeight
    exact div_nonneg (Real.rpow_nonneg (by linarith) _)
      (Real.log_pos (by linarith)).le
  rw [angularWeightedPrimeSum_abel ℓ hX]
  have hi : ‖∫ t in 2..X, (angularAbelDerivative t : ℂ) * primeChebyshev (theta ℓ) t‖ ≤
      ∫ t in 2..X, angularChebyshevIntegrand ℓ t := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, angularChebyshevIntegrand] using
      (intervalIntegral.norm_integral_le_integral_norm
        (f := fun t => (angularAbelDerivative t : ℂ) * primeChebyshev (theta ℓ) t) hX)
  have hb : ‖(angularAbelWeight X : ℂ) * primeChebyshev (theta ℓ) X‖ =
      angularAbelWeight X * ‖primeChebyshev (theta ℓ) X‖ := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hW]
  calc
    _ ≤ ‖(angularAbelWeight X : ℂ) * primeChebyshev (theta ℓ) X‖ +
        ‖∫ t in 2..X, (angularAbelDerivative t : ℂ) * primeChebyshev (theta ℓ) t‖ :=
      norm_sub_le _ _
    _ ≤ _ := add_le_add hb.le hi

theorem angularWeightedPrimeSum_isLittleO (hEF : FixedAngularPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) :
    angularWeightedPrimeSum ℓ =o[atTop] firstMomentScale := by
  have hb : Tendsto (fun X => angularAbelWeight X * ‖primeChebyshev (theta ℓ) X‖ /
      firstMomentScale X) atTop (𝓝 0) := by
    apply (fixedAngular_chebyshev_div_tendsto_zero hEF ℓ hℓ).congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    exact (angularAbel_boundary_ratio _ X hX).symm
  have hi := angularChebyshev_integral_div_scale_tendsto_zero hEF ℓ hℓ
  have hsum : Tendsto (fun X =>
      angularAbelWeight X * ‖primeChebyshev (theta ℓ) X‖ / firstMomentScale X +
      (∫ t in 2..X, angularChebyshevIntegrand ℓ t) / firstMomentScale X) atTop (𝓝 0) := by
    simpa only [add_zero] using hb.add hi
  have hratio : Tendsto (fun X => ‖angularWeightedPrimeSum ℓ X‖ / firstMomentScale X)
      atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hsmall := (tendsto_order.mp hsum).2 ε hε
    filter_upwards [hsmall, eventually_ge_atTop (2 : ℝ)] with X hsmall hX
    have hs : 0 < firstMomentScale X := firstMomentScale_pos (by linarith)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (_root_.norm_nonneg _) hs.le)]
    have hbound := div_le_div_of_nonneg_right (angularWeightedPrimeSum_norm_le ℓ hX) hs.le
    rw [add_div] at hbound
    exact hbound.trans_lt hsmall
  apply IsLittleO.of_norm_left
  apply isLittleO_of_tendsto' _ hratio
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  exact fun hz => False.elim ((firstMomentScale_pos hX).ne' hz)

/-- The sharp nonzero-angular prime model is negligible at the precise
`X^(5/6)/log X` scale, derived from the published explicit Hecke input. -/
theorem angularPrimeModel_isLittleO (hEF : FixedAngularPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) :
    primeCutoffSum (angularPrimeModel ℓ) =o[atTop] firstMomentScale := by
  have h := (angularWeightedPrimeSum_isLittleO hEF ℓ hℓ).const_mul_left (cStar : ℂ)
  refine h.congr' ?_ Filter.EventuallyEq.rfl
  apply Filter.Eventually.of_forall
  intro X
  unfold angularWeightedPrimeSum
  dsimp only
  rw [primeCutoffSum_eq_sum, primeCutoffSum_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [angularPrimeModel, Complex.ofReal_mul]
  ring

end CubicFirstMoment

end

end OAI
