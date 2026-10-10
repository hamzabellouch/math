import OAI.NumberTheory.CubicMoment.Estimates.PowerSavings

namespace OAI

/-!
# The elementary prime model from the ordinary prime ideal theorem

The only number-theoretic hypothesis used here is the ordinary asymptotic
for the number of primary prime elements.  The power-weighted consequence
is derived by Abel summation.
-/

noncomputable section

open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology

namespace CubicFirstMoment

/-- The derivative of the scale appearing in the first moment. -/
def firstMomentScaleDerivative (X : ℝ) : ℝ :=
  X ^ (-1 / 6 : ℝ) / Real.log X * (5 / 6 - 1 / Real.log X)

lemma hasDerivAt_firstMomentScale {X : ℝ} (hX : 1 < X) :
    HasDerivAt firstMomentScale (firstMomentScaleDerivative X) X := by
  have hX₀ : 0 < X := lt_trans zero_lt_one hX
  have hlog : Real.log X ≠ 0 := (Real.log_pos hX).ne'
  have hp := Real.hasDerivAt_rpow_const (x := X) (p := (5 / 6 : ℝ)) (Or.inl hX₀.ne')
  have hl := Real.hasDerivAt_log hX₀.ne'
  have hm : X ^ (-1 / 6 : ℝ) * X = X ^ (5 / 6 : ℝ) := by
    rw [← Real.rpow_add_one hX₀.ne']
    norm_num
  convert hp.div hl hlog using 1
  · rfl
  · norm_num only at *
    dsimp [firstMomentScaleDerivative]
    field_simp
    nlinarith [hm]

lemma firstMomentScaleDerivative_continuousOn :
    ContinuousOn firstMomentScaleDerivative (Set.Ioi 1) := by
  intro X hX
  have hX₀ : X ≠ 0 := ne_of_gt (lt_trans zero_lt_one hX)
  have hlog : Real.log X ≠ 0 := (Real.log_pos hX).ne'
  exact (((Real.continuousAt_rpow_const X (-1 / 6) (Or.inl hX₀)).div
    (Real.continuousAt_log hX₀) hlog).mul
      (continuousAt_const.sub (continuousAt_const.div (Real.continuousAt_log hX₀) hlog))).continuousWithinAt

lemma firstMomentScaleDerivative_pos {X : ℝ} (hX₁ : 1 < X) (hX : 2 < Real.log X) :
    0 < firstMomentScaleDerivative X := by
  have hl : 0 < Real.log X := lt_trans (by norm_num) hX
  have hX₀ : 0 < X := lt_trans zero_lt_one hX₁
  have hinv : 1 / Real.log X < 1 / 2 := one_div_lt_one_div_of_lt (by norm_num) hX
  unfold firstMomentScaleDerivative
  exact mul_pos (div_pos (Real.rpow_pos_of_pos hX₀ _) hl) (by linarith)

lemma tendsto_firstMomentScale : Tendsto firstMomentScale atTop atTop := by
  have h : Tendsto (fun X : ℝ => Real.log X / X ^ (5 / 6 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 5 / 6)).tendsto_div_nhds_zero
  have hpos : ∀ᶠ X : ℝ in atTop, 0 < Real.log X / X ^ (5 / 6 : ℝ) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    exact div_pos (Real.log_pos hX) (Real.rpow_pos_of_pos (lt_trans zero_lt_one hX) _)
  have hright : Tendsto (fun X : ℝ => Real.log X / X ^ (5 / 6 : ℝ))
      atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨h, hpos⟩
  have hi := hright.inv_tendsto_nhdsGT_zero
  change Tendsto (fun X : ℝ => (Real.log X / X ^ (5 / 6 : ℝ))⁻¹) atTop atTop at hi
  change Tendsto (fun X : ℝ => firstMomentScale X) atTop atTop
  simpa only [inv_div, firstMomentScale] using hi

/-- Cumulative count of an arithmetic sequence collected by integer norm. -/
def normCountingSum (c : ℕ → ℝ) (X : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊X⌋₊, c n

/-- Its power-weighted cumulative sum. -/
def normWeightedSum (c : ℕ → ℝ) (X : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊X⌋₊, (n : ℝ) ^ (-1 / 6 : ℝ) * c n

lemma normWeightedSum_abel (c : ℕ → ℝ) (hc₀ : c 0 = 0) (X : ℝ) (hX : 1 ≤ X) :
    normWeightedSum c X = X ^ (-1 / 6 : ℝ) * normCountingSum c X +
      (1 / 6 : ℝ) * ∫ t in 1..X, t ^ (-7 / 6 : ℝ) * normCountingSum c t := by
  have hdiff : ∀ t ∈ Set.Icc 1 X,
      DifferentiableAt ℝ (fun t : ℝ => t ^ (-1 / 6 : ℝ)) t := by
    intro t ht
    exact (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)))).differentiableAt
  have hderiv : ∀ t ∈ Set.Icc 1 X,
      deriv (fun t : ℝ => t ^ (-1 / 6 : ℝ)) t = (-1 / 6 : ℝ) * t ^ (-7 / 6 : ℝ) := by
    intro t ht
    convert (Real.hasDerivAt_rpow_const (x := t) (p := (-1 / 6 : ℝ))
      (Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)))).deriv using 1
    norm_num
  have hint : IntegrableOn (deriv (fun t : ℝ => t ^ (-1 / 6 : ℝ))) (Set.Icc 1 X) := by
    apply IntegrableOn.congr_fun ?_ (fun t ht => (hderiv t ht).symm) measurableSet_Icc
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    exact (continuousAt_const.mul (Real.continuousAt_rpow_const t (-7 / 6)
      (Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1))))).continuousWithinAt
  have h := sum_mul_eq_sub_integral_mul₀ c hc₀ X hdiff hint
  change normWeightedSum c X = X ^ (-1 / 6 : ℝ) * normCountingSum c X -
    ∫ t in Set.Ioc 1 X, deriv (fun t : ℝ => t ^ (-1 / 6 : ℝ)) t * normCountingSum c t at h
  rw [← intervalIntegral.integral_of_le hX] at h
  rw [h]
  have hi : (∫ t in 1..X, deriv (fun t : ℝ => t ^ (-1 / 6 : ℝ)) t * normCountingSum c t) =
      (-1 / 6 : ℝ) * ∫ t in 1..X, t ^ (-7 / 6 : ℝ) * normCountingSum c t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hX] at ht
    dsimp only
    rw [hderiv t ht]
    ring
  rw [hi]
  ring

/-- Integrating an asymptotic against the derivative of the first-moment scale.
This is the elementary comparison step in partial summation. -/
lemma integral_div_firstMomentScale_tendsto (f : ℝ → ℝ) (L : ℝ)
    (hint : ∀ X : ℝ, 1 ≤ X → IntervalIntegrable f volume 1 X)
    (hlim : Tendsto (fun X => f X / firstMomentScaleDerivative X) atTop (𝓝 L)) :
    Tendsto (fun X => (∫ t in 1..X, f t) / firstMomentScale X) atTop (𝓝 L) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hr := Metric.tendsto_nhds.mp hlim (ε / 2) (by positivity)
  have hlog := Real.tendsto_log_atTop.eventually (eventually_gt_atTop (2 : ℝ))
  obtain ⟨A, hA⟩ := eventually_atTop.mp
    ((hr.and hlog).and (eventually_gt_atTop (1 : ℝ)))
  have hA₁ : 1 < A := (hA A le_rfl).2
  let C := (∫ t in 1..A, f t) - L * firstMomentScale A
  have hC : Tendsto (fun X => |C| / firstMomentScale X) atTop (𝓝 0) :=
    tendsto_firstMomentScale.const_div_atTop |C|
  have he := (tendsto_order.mp hC).2 (ε / 2) (by positivity)
  filter_upwards [eventually_ge_atTop A, he] with X hX hsmall
  have hX₁ : 1 < X := lt_of_lt_of_le hA₁ hX
  have hsX : 0 < firstMomentScale X := firstMomentScale_pos hX₁
  have hsA : 0 < firstMomentScale A := firstMomentScale_pos hA₁
  have hdint : IntervalIntegrable firstMomentScaleDerivative volume A X := by
    apply ContinuousOn.intervalIntegrable_of_Icc hX
    apply firstMomentScaleDerivative_continuousOn.mono
    intro t ht
    exact lt_of_lt_of_le hA₁ ht.1
  have hFTC : (∫ t in A..X, firstMomentScaleDerivative t) =
      firstMomentScale X - firstMomentScale A := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hdint
    intro t ht
    rw [Set.uIcc_of_le hX] at ht
    exact hasDerivAt_firstMomentScale (lt_of_lt_of_le hA₁ ht.1)
  have hfint : IntervalIntegrable f volume A X :=
    (hint A hA₁.le).symm.trans (hint X hX₁.le)
  have herr : ‖∫ t in A..X, (f t - L * firstMomentScaleDerivative t)‖ ≤
      ε / 2 * (firstMomentScale X - firstMomentScale A) := by
    have hb : ∀ᵐ t : ℝ, t ∈ Set.Ioc A X →
        ‖f t - L * firstMomentScaleDerivative t‖ ≤ ε / 2 * firstMomentScaleDerivative t := by
      apply Filter.Eventually.of_forall
      intro t ht
      have hat := hA t ht.1.le
      have hdt : 0 < firstMomentScaleDerivative t :=
        firstMomentScaleDerivative_pos hat.2 hat.1.2
      have hclose : |f t / firstMomentScaleDerivative t - L| < ε / 2 := by
        simpa only [Real.dist_eq] using hat.1.1
      have heq : f t - L * firstMomentScaleDerivative t =
          (f t / firstMomentScaleDerivative t - L) * firstMomentScaleDerivative t := by
        field_simp
      rw [heq, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hdt]
      exact mul_le_mul_of_nonneg_right hclose.le hdt.le
    have hi := intervalIntegral.norm_integral_le_of_norm_le hX hb (hdint.const_mul (ε / 2))
    simpa only [intervalIntegral.integral_const_mul, hFTC] using hi
  have heq : (∫ t in 1..X, f t) - L * firstMomentScale X =
      C + ∫ t in A..X, (f t - L * firstMomentScaleDerivative t) := by
    rw [intervalIntegral.integral_sub hfint (hdint.const_mul L),
      intervalIntegral.integral_const_mul, hFTC]
    have hadd := intervalIntegral.integral_add_adjacent_intervals (hint A hA₁.le) hfint
    dsimp [C]
    linarith
  have hbound : |(∫ t in 1..X, f t) - L * firstMomentScale X| ≤
      |C| + ε / 2 * firstMomentScale X := by
    rw [heq]
    calc
      |C + ∫ t in A..X, (f t - L * firstMomentScaleDerivative t)| ≤
          |C| + |∫ t in A..X, (f t - L * firstMomentScaleDerivative t)| := abs_add_le _ _
      _ ≤ |C| + ε / 2 * (firstMomentScale X - firstMomentScale A) :=
        by simpa only [Real.norm_eq_abs] using add_le_add (le_refl |C|) herr
      _ ≤ |C| + ε / 2 * firstMomentScale X := by nlinarith
  rw [Real.dist_eq]
  have heq' : (∫ t in 1..X, f t) / firstMomentScale X - L =
      ((∫ t in 1..X, f t) - L * firstMomentScale X) / firstMomentScale X := by
    field_simp
  rw [heq', abs_div, abs_of_pos hsX]
  calc
    |(∫ t in 1..X, f t) - L * firstMomentScale X| / firstMomentScale X ≤
        (|C| + ε / 2 * firstMomentScale X) / firstMomentScale X :=
      div_le_div_of_nonneg_right hbound hsX.le
    _ = |C| / firstMomentScale X + ε / 2 := by field_simp
    _ < ε := by linarith

private lemma weighted_boundary_ratio (a X : ℝ) (hX : 1 < X) :
    X ^ (-1 / 6 : ℝ) * a / firstMomentScale X = a * Real.log X / X := by
  have hx : 0 < X := lt_trans zero_lt_one hX
  have hp : X ^ (5 / 6 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  have hm : X ^ (-1 / 6 : ℝ) * X = X ^ (5 / 6 : ℝ) := by
    rw [← Real.rpow_add_one hx.ne']
    norm_num
  unfold firstMomentScale
  field_simp
  norm_num only [neg_div] at hm
  linear_combination (a * Real.log X) * hm

private lemma weighted_integrand_ratio (a X : ℝ) (hX : 1 < X)
    (hlog : 2 < Real.log X) :
    (X ^ (-7 / 6 : ℝ) * a) / firstMomentScaleDerivative X =
      (a * Real.log X / X) / (5 / 6 - 1 / Real.log X) := by
  have hx : 0 < X := lt_trans zero_lt_one hX
  have hp : X ^ (-7 / 6 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  have hl : Real.log X ≠ 0 := (Real.log_pos hX).ne'
  have hi : 1 / Real.log X < 1 / 2 := one_div_lt_one_div_of_lt (by norm_num) hlog
  have hd : (5 / 6 : ℝ) - 1 / Real.log X ≠ 0 := by linarith
  have hm : X ^ (-7 / 6 : ℝ) * X = X ^ (-1 / 6 : ℝ) := by
    rw [← Real.rpow_add_one hx.ne']
    norm_num
  unfold firstMomentScaleDerivative
  rw [← hm]
  field_simp

/-- Abel summation of an ordinary counting asymptotic; no weighted prime
estimate is among the hypotheses. -/
lemma normWeightedSum_tendsto_of_pnt (c : ℕ → ℝ) (hc₀ : c 0 = 0)
    (hpnt : Tendsto (fun X => normCountingSum c X * Real.log X / X) atTop (𝓝 1)) :
    Tendsto (fun X => normWeightedSum c X / firstMomentScale X) atTop (𝓝 (6 / 5 : ℝ)) := by
  have hi : Tendsto (fun X : ℝ => 1 / Real.log X) atTop (𝓝 0) := by
    have h := Real.tendsto_log_atTop.inv_tendsto_atTop
    change Tendsto (fun X : ℝ => (Real.log X)⁻¹) atTop (𝓝 0) at h
    simpa only [one_div] using h
  have hr : Tendsto (fun X =>
      (X ^ (-7 / 6 : ℝ) * normCountingSum c X) / firstMomentScaleDerivative X)
      atTop (𝓝 (6 / 5 : ℝ)) := by
    have hh := hpnt.div (tendsto_const_nhds.sub hi) (by norm_num : (5 / 6 : ℝ) - 0 ≠ 0)
    have hc : (1 : ℝ) / (5 / 6 - 0) = 6 / 5 := by norm_num
    rw [hc] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      Real.tendsto_log_atTop.eventually (eventually_gt_atTop (2 : ℝ))] with X hX hlog
    exact (weighted_integrand_ratio _ X hX hlog).symm
  have hint : ∀ X : ℝ, 1 ≤ X → IntervalIntegrable
      (fun t => t ^ (-7 / 6 : ℝ) * normCountingSum c t) volume 1 X := by
    intro X hX
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hX]
    apply integrableOn_mul_sum_Icc c (by norm_num)
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    exact (Real.continuousAt_rpow_const t (-7 / 6)
      (Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)))).continuousWithinAt
  have hIntegral := integral_div_firstMomentScale_tendsto _ (6 / 5) hint hr
  have hfinal := hpnt.add (hIntegral.const_mul (1 / 6))
  have hv : (1 : ℝ) + 1 / 6 * (6 / 5) = 6 / 5 := by norm_num
  rw [hv] at hfinal
  apply hfinal.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  rw [normWeightedSum_abel c hc₀ X hX.le, add_div, mul_div_assoc,
    weighted_boundary_ratio _ _ hX]
  ring

/-- The ordinary count of primary prime elements in the norm ball. -/
def primaryPrimeCount (X : ℝ) : ℝ := (primeCutoff X).card

/-- The ordinary prime ideal theorem, in the normalization used here.
The weighted first moment is proved below, rather than included in this input. -/
def PrimaryPrimePNT : Prop :=
  Tendsto (fun X => primaryPrimeCount X * Real.log X / X) atTop (𝓝 1)

/-- The number of primary primes having a specified integer norm. -/
def primaryPrimeMultiplicity (n : ℕ) : ℝ :=
  ((primeCutoff (n : ℝ)).filter (fun p => normNat p = n)).card

private lemma primaryPrimeFiber_eq (n : ℕ) (X : ℝ) (hn : (n : ℝ) ≤ X) :
    (primeCutoff (n : ℝ)).filter (fun p => normNat p = n) =
      (primeCutoff X).filter (fun p => normNat p = n) := by
  ext p
  simp only [Finset.mem_filter, mem_primeCutoff]
  constructor
  · intro hp
    exact ⟨⟨hp.1.1, hp.1.2.trans hn⟩, hp.2⟩
  · intro hp
    have he : norm p = (n : ℝ) := by rw [← normNat_cast p, hp.2]
    exact ⟨⟨hp.1.1, he.le⟩, hp.2⟩

lemma primaryPrimeMultiplicity_zero : primaryPrimeMultiplicity 0 = 0 := by
  have he : (primeCutoff (0 : ℝ)).filter (fun p => normNat p = 0) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro p hp
    have hp' := (mem_primeCutoff.mp (Finset.mem_filter.mp hp).1).1
    have hn : norm p = 0 := by
      rw [← normNat_cast p, (Finset.mem_filter.mp hp).2, Nat.cast_zero]
    have hz : p = 0 := by
      apply Subtype.ext
      exact Complex.normSq_eq_zero.mp hn
    exact hp'.2.ne_zero hz
  simp only [primaryPrimeMultiplicity, Nat.cast_zero, he, Finset.card_empty]

lemma primeNorm_sum_eq (g : ℕ → ℝ) {X : ℝ} (hX : 0 ≤ X) :
    (∑ n ∈ Finset.Icc 0 ⌊X⌋₊, g n * primaryPrimeMultiplicity n) =
      ∑ p ∈ primeCutoff X, g (normNat p) := by
  have hmaps : ∀ p ∈ primeCutoff X, normNat p ∈ Finset.Icc 0 ⌊X⌋₊ := by
    intro p hp
    simp only [Finset.mem_Icc, Nat.zero_le, true_and]
    apply (Nat.le_floor_iff hX).mpr
    rw [normNat_cast]
    exact (mem_primeCutoff.mp hp).2
  rw [← Finset.sum_fiberwise_of_maps_to' hmaps g]
  apply Finset.sum_congr rfl
  intro n hn
  have hnX : (n : ℝ) ≤ X := (Nat.le_floor_iff hX).mp (Finset.mem_Icc.mp hn).2
  rw [primaryPrimeMultiplicity, primaryPrimeFiber_eq n X hnX]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

lemma normCountingSum_primaryPrimeMultiplicity {X : ℝ} (hX : 0 ≤ X) :
    normCountingSum primaryPrimeMultiplicity X = primaryPrimeCount X := by
  simpa only [normCountingSum, one_mul, Finset.sum_const, nsmul_eq_mul, mul_one,
    primaryPrimeCount] using primeNorm_sum_eq (fun _ => 1) hX

lemma normWeightedSum_primaryPrimeMultiplicity {X : ℝ} (hX : 0 ≤ X) :
    normWeightedSum primaryPrimeMultiplicity X =
      ∑ p ∈ primeCutoff X, norm p ^ (-1 / 6 : ℝ) := by
  simpa only [normWeightedSum, normNat_cast] using
    primeNorm_sum_eq (fun n => (n : ℝ) ^ (-1 / 6 : ℝ)) hX

/-- The power-weighted ordinary prime model, obtained solely from the ordinary PNT. -/
lemma primaryPrime_weighted_asymptotic (hpnt : PrimaryPrimePNT) :
    Tendsto (fun X => (∑ p ∈ primeCutoff X, norm p ^ (-1 / 6 : ℝ)) / firstMomentScale X)
      atTop (𝓝 (6 / 5 : ℝ)) := by
  have hcount : Tendsto
      (fun X => normCountingSum primaryPrimeMultiplicity X * Real.log X / X)
      atTop (𝓝 1) := by
    apply hpnt.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with X hX
    rw [normCountingSum_primaryPrimeMultiplicity hX]
  have h := normWeightedSum_tendsto_of_pnt primaryPrimeMultiplicity
    primaryPrimeMultiplicity_zero hcount
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with X hX
  rw [normWeightedSum_primaryPrimeMultiplicity hX]

lemma primaryPrime_weighted_remainder (hpnt : PrimaryPrimePNT) :
    (fun X => (∑ p ∈ primeCutoff X, norm p ^ (-1 / 6 : ℝ)) -
      (6 / 5 : ℝ) * firstMomentScale X) =o[atTop] firstMomentScale := by
  apply isLittleO_of_tendsto'
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    exact fun hz => False.elim ((firstMomentScale_pos hX).ne' hz)
  · have h := (primaryPrime_weighted_asymptotic hpnt).sub_const (6 / 5)
    norm_num only [sub_self] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    have hs : firstMomentScale X ≠ 0 := (firstMomentScale_pos hX).ne'
    field_simp

/-- The elementary model has the claimed main term, conditionally only on
ordinary prime counting. -/
theorem primeModel_asymptotic_of_PNT (hpnt : PrimaryPrimePNT) :
    (fun X => primeCutoffSum (angularPrimeModel 0) X -
      (((6 / 5 : ℝ) * cStar * firstMomentScale X : ℝ) : ℂ))
      =o[atTop] firstMomentScale := by
  have hr := (primaryPrime_weighted_remainder hpnt).const_mul_left cStar
  have hc : (fun X => ((cStar * ((∑ p ∈ primeCutoff X, norm p ^ (-1 / 6 : ℝ)) -
      (6 / 5 : ℝ) * firstMomentScale X) : ℝ) : ℂ)) =o[atTop] firstMomentScale := by
    apply IsLittleO.of_norm_left
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hr.norm_left
  refine hc.congr' ?_ Filter.EventuallyEq.rfl
  apply Filter.Eventually.of_forall
  intro X
  dsimp only
  rw [primeCutoffSum_eq_sum]
  simp only [angularPrimeModel, theta_zero, one_mul]
  push_cast
  rw [← Finset.mul_sum]
  ring

end CubicFirstMoment

end

end OAI
