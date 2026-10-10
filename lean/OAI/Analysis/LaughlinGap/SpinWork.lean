import Mathlib

namespace OAI

/-! Spin Work. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators Topology
open Filter

noncomputable def highestFactor (n m z k : ℕ) : ℝ :=
  ((m : ℝ) - z + k + 1) / ((n : ℝ) - k)

noncomputable def highestWeight (n m z p : ℕ) : ℝ :=
  (z.choose p : ℝ) * ∏ k ∈ Finset.range p, highestFactor n m z k

noncomputable def highestNormalization (n m z : ℕ) : ℝ :=
  ∑ p ∈ Finset.range (z+1), highestWeight n m z p

noncomputable def highestCoefficient (n m z p : ℕ) : ℝ :=
  (-1 : ℝ) ^ (z-p) * Real.sqrt (highestWeight n m z p) /
    Real.sqrt (highestNormalization n m z)

lemma highestFactor_pos {n m z k : ℕ} (hz : z ≤ min n m) (hk : k < z) :
    0 < highestFactor n m z k := by
  have hzN : (z : ℝ) ≤ n := by exact_mod_cast (le_min_iff.mp hz).1
  have hzM : (z : ℝ) ≤ m := by exact_mod_cast (le_min_iff.mp hz).2
  have hkZ : (k : ℝ) < z := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := by positivity
  exact div_pos (by linarith) (by linarith)

lemma highestWeight_nonneg {n m z p : ℕ} (hz : z ≤ min n m) :
    0 ≤ highestWeight n m z p := by
  by_cases hp : p ≤ z
  · apply mul_nonneg (by positivity)
    exact Finset.prod_nonneg fun k hk =>
      (highestFactor_pos hz ((Finset.mem_range.mp hk).trans_le hp)).le
  · simp [highestWeight, Nat.choose_eq_zero_of_lt (by omega : z < p)]

@[simp] lemma highestWeight_zero (n m z : ℕ) : highestWeight n m z 0 = 1 := by
  simp [highestWeight]

lemma highestNormalization_pos {n m z : ℕ} (hz : z ≤ min n m) :
    0 < highestNormalization n m z := by
  apply Finset.sum_pos' (fun p _ => highestWeight_nonneg hz)
  exact ⟨0, by simp, by simp⟩

lemma highestCoefficient_sq {n m z p : ℕ} (hz : z ≤ min n m) :
    highestCoefficient n m z p ^ 2 =
      highestWeight n m z p / highestNormalization n m z := by
  simp only [highestCoefficient, div_pow, mul_pow, ← pow_mul (-1 : ℝ),
    mul_comm (z-p) 2, pow_mul (-1 : ℝ) 2, neg_one_sq, one_pow, one_mul,
    Real.sq_sqrt (highestWeight_nonneg hz), Real.sq_sqrt (highestNormalization_pos hz).le]

theorem highestCoefficient_sum_sq {n m z : ℕ} (hz : z ≤ min n m) :
    ∑ p ∈ Finset.range (z+1), highestCoefficient n m z p ^ 2 = 1 := by
  simp_rw [highestCoefficient_sq hz]
  rw [← Finset.sum_div]
  exact div_self (highestNormalization_pos hz).ne'

lemma highestCoefficient_eq_zero {n m z p : ℕ} (hp : z < p) :
    highestCoefficient n m z p = 0 := by
  simp [highestCoefficient, highestWeight, Nat.choose_eq_zero_of_lt hp]

lemma highestWeight_step {n m z p : ℕ} (hz : z ≤ min n m) (hp : p < z) :
    highestWeight n m z (p+1) * ((p : ℝ)+1) * ((n : ℝ)-p) =
      highestWeight n m z p * ((z : ℝ)-p) * ((m : ℝ)-z+p+1) := by
  have hnp : (n : ℝ) - p ≠ 0 := by
    have hn : p < n := hp.trans_le (le_min_iff.mp hz).1
    exact sub_ne_zero.mpr (Ne.symm (by exact_mod_cast hn.ne))
  have hc : (z.choose (p+1) : ℝ) * ((p : ℝ)+1) = (z.choose p : ℝ) * ((z : ℝ)-p) := by
    have H := congrArg (fun a : ℕ => (a : ℝ)) (Nat.choose_succ_right_eq z p)
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hp.le] using H
  simp only [highestWeight, Finset.prod_range_succ, highestFactor]
  rw [mul_assoc (z.choose (p+1) : ℝ), mul_comm _ ((p : ℝ)+1),
    ← mul_assoc (z.choose (p+1) : ℝ), hc]
  field_simp

theorem highestCoefficient_raising {n m z p : ℕ} (hz : z ≤ min n m) (hp : p < z) :
    highestCoefficient n m z (p+1) * Real.sqrt (((p : ℝ)+1)*((n : ℝ)-p)) +
      highestCoefficient n m z p * Real.sqrt (((z : ℝ)-p)*((m : ℝ)-z+p+1)) = 0 := by
  have he : Real.sqrt (highestWeight n m z (p+1)) *
      Real.sqrt (((p : ℝ)+1)*((n : ℝ)-p)) =
      Real.sqrt (highestWeight n m z p) *
      Real.sqrt (((z : ℝ)-p)*((m : ℝ)-z+p+1)) := by
    rw [← Real.sqrt_mul (highestWeight_nonneg hz),
      ← Real.sqrt_mul (highestWeight_nonneg hz)]
    congr 1
    simpa only [mul_assoc] using highestWeight_step hz hp
  have hpz : z-p = (z-(p+1))+1 := by omega
  simp only [highestCoefficient, hpz, pow_succ, mul_neg_one]
  linear_combination
    ((-1 : ℝ) ^ (z-(p+1)) / Real.sqrt (highestNormalization n m z)) * he

theorem highestFactor_tendsto {n m : ℕ → ℕ} {r : ℝ}
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hmn : Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 r)) (z k : ℕ) :
    Tendsto (fun q => highestFactor (n q) (m q) z k) atTop (𝓝 r) := by
  have hquot : Tendsto
      (fun q => ((m q : ℝ) / n q + (-(z : ℝ) + k + 1) / n q) /
        (1 - (k : ℝ) / n q)) atTop (𝓝 r) := by
    simpa only [add_zero, sub_zero, div_one, Pi.div_def] using
      (hmn.add (hn.const_div_atTop (-(z : ℝ) + k + 1))).div
        ((tendsto_const_nhds (x := (1 : ℝ))).sub (hn.const_div_atTop (k : ℝ)))
        (by norm_num : (1 : ℝ) - 0 ≠ 0)
  apply hquot.congr'
  filter_upwards [hn.eventually (eventually_gt_atTop (k : ℝ))] with q hq
  have hN : (n q : ℝ) ≠ 0 := by
    have hk : (0 : ℝ) ≤ k := by positivity
    linarith
  have hNk : (n q : ℝ) - k ≠ 0 := by linarith
  dsimp [highestFactor]
  field_simp
  ring

theorem highestWeight_tendsto {n m : ℕ → ℕ} {r : ℝ}
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hmn : Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 r)) (z p : ℕ) :
    Tendsto (fun q => highestWeight (n q) (m q) z p) atTop
      (𝓝 ((z.choose p : ℝ) * r ^ p)) := by
  have h := (tendsto_const_nhds (x := (z.choose p : ℝ))).mul
    (tendsto_finsetProd (Finset.range p) (fun k _ => highestFactor_tendsto hn hmn z k))
  simpa only [Finset.prod_const, Finset.card_range, highestWeight] using h

theorem highestNormalization_tendsto {n m : ℕ → ℕ} {r : ℝ}
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hmn : Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 r)) (z : ℕ) :
    Tendsto (fun q => highestNormalization (n q) (m q) z) atTop (𝓝 ((r+1)^z)) := by
  have hsum : (∑ p ∈ Finset.range (z+1), (z.choose p : ℝ) * r^p) = (r+1)^z := by
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro p hp
    simp [mul_comm]
  simpa only [highestNormalization, hsum] using
    tendsto_finsetSum (Finset.range (z+1)) (fun p _ => highestWeight_tendsto hn hmn z p)

theorem highestCoefficient_tendsto_ratio {n m : ℕ → ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hmn : Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 r)) (z p : ℕ) :
    Tendsto (fun q => highestCoefficient (n q) (m q) z p) atTop
      (𝓝 ((-1 : ℝ)^(z-p) * Real.sqrt ((z.choose p : ℝ) * r^p) /
        Real.sqrt ((r+1)^z))) := by
  have hpos : 0 < (r+1)^z := pow_pos (by linarith) z
  exact ((tendsto_const_nhds.mul (highestWeight_tendsto hn hmn z p).sqrt).div
    (highestNormalization_tendsto hn hmn z).sqrt (Real.sqrt_pos.mpr hpos).ne')

lemma sqrt_nat_pow {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    Real.sqrt (x ^ k) = Real.sqrt x ^ k := by
  induction k with
  | zero => simp
  | succ k hk => rw [pow_succ, Real.sqrt_mul (pow_nonneg hx k), hk, pow_succ]

noncomputable def limitingHighestCoefficient (u v : ℝ) (z p : ℕ) : ℝ :=
  (-1 : ℝ)^(z-p) * Real.sqrt (z.choose p : ℝ) * u^p * v^(z-p)

lemma highest_ratio_eq {r : ℝ} (hr : 0 ≤ r) (z p : ℕ) :
    (-1 : ℝ)^(z-p) * Real.sqrt ((z.choose p : ℝ) * r^p) /
      Real.sqrt ((r+1)^z) =
    limitingHighestCoefficient (Real.sqrt r / Real.sqrt (r+1))
      (1 / Real.sqrt (r+1)) z p := by
  by_cases hp : p ≤ z
  · have he : z = p + (z-p) := (Nat.add_sub_of_le hp).symm
    have hpos : Real.sqrt (r+1) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
    rw [Real.sqrt_mul (by positivity), sqrt_nat_pow hr,
      sqrt_nat_pow (by linarith : 0 ≤ r+1)]
    unfold limitingHighestCoefficient
    rw [div_pow, div_pow, one_pow]
    rw [show Real.sqrt (r+1)^z = Real.sqrt (r+1)^p * Real.sqrt (r+1)^(z-p) by
      rw [← pow_add, Nat.add_sub_of_le hp]]
    ring
  · simp [Nat.choose_eq_zero_of_lt (by omega : z < p), limitingHighestCoefficient]

theorem highestCoefficient_tendsto {n m : ℕ → ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hmn : Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 r)) (z p : ℕ) :
    Tendsto (fun q => highestCoefficient (n q) (m q) z p) atTop
      (𝓝 (limitingHighestCoefficient (Real.sqrt r / Real.sqrt (r+1))
        (1 / Real.sqrt (r+1)) z p)) := by
  simpa only [highest_ratio_eq hr] using highestCoefficient_tendsto_ratio hr hn hmn z p

lemma firstAffineRatio_tendsto {n m : ℕ → ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hmn : Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 r)) (a b : ℝ) :
    Tendsto (fun q => ((n q : ℝ) + a) / ((n q : ℝ) + m q + b)) atTop
      (𝓝 (1 / (1+r))) := by
  have h : Tendsto (fun q => (1 + a / (n q : ℝ)) /
      (1 + (m q : ℝ) / n q + b / n q)) atTop (𝓝 (1 / (1+r))) := by
    simpa only [add_zero, Pi.div_def] using
      ((tendsto_const_nhds (x := (1 : ℝ))).add (hn.const_div_atTop a)).div
        (((tendsto_const_nhds (x := (1 : ℝ))).add hmn).add (hn.const_div_atTop b))
        (by linarith : 1 + r + 0 ≠ 0)
  apply h.congr'
  filter_upwards [hn.eventually (eventually_gt_atTop (0 : ℝ))] with q hq
  simpa only [add_div, div_self hq.ne'] using
    div_div_div_cancel_right₀ hq.ne' ((n q : ℝ) + a) ((n q : ℝ) + m q + b)

lemma secondAffineRatio_tendsto {n m : ℕ → ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hmn : Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 r)) (a b : ℝ) :
    Tendsto (fun q => ((m q : ℝ) + a) / ((n q : ℝ) + m q + b)) atTop
      (𝓝 (r / (1+r))) := by
  have h : Tendsto (fun q => ((m q : ℝ) / n q + a / n q) /
      (1 + (m q : ℝ) / n q + b / n q)) atTop (𝓝 (r / (1+r))) := by
    simpa only [add_zero, Pi.div_def] using
      (hmn.add (hn.const_div_atTop a)).div
        (((tendsto_const_nhds (x := (1 : ℝ))).add hmn).add (hn.const_div_atTop b))
        (by linarith : 1 + r + 0 ≠ 0)
  apply h.congr'
  filter_upwards [hn.eventually (eventually_gt_atTop (0 : ℝ))] with q hq
  simpa only [add_div, div_self hq.ne'] using
    div_div_div_cancel_right₀ hq.ne' ((m q : ℝ) + a) ((n q : ℝ) + m q + b)

lemma firstSqrtRatio_tendsto {n m : ℕ → ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hmn : Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 r)) (a b : ℝ) :
    Tendsto (fun q => Real.sqrt ((n q : ℝ) + a) /
      Real.sqrt ((n q : ℝ) + m q + b)) atTop (𝓝 (1 / Real.sqrt (1+r))) := by
  have h := (firstAffineRatio_tendsto hr hn hmn a b).sqrt
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one] at h
  apply h.congr'
  filter_upwards [hn.eventually (eventually_gt_atTop (-b))] with q hq
  have hm : (0 : ℝ) ≤ m q := by positivity
  rw [Real.sqrt_div' _ (by linarith)]

lemma secondSqrtRatio_tendsto {n m : ℕ → ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hmn : Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 r)) (a b : ℝ) :
    Tendsto (fun q => Real.sqrt ((m q : ℝ) + a) /
      Real.sqrt ((n q : ℝ) + m q + b)) atTop
      (𝓝 (Real.sqrt r / Real.sqrt (1+r))) := by
  have h := (secondAffineRatio_tendsto hr hn hmn a b).sqrt
  rw [Real.sqrt_div hr] at h
  apply h.congr'
  filter_upwards [hn.eventually (eventually_gt_atTop (-b))] with q hq
  have hm : (0 : ℝ) ≤ m q := by positivity
  rw [Real.sqrt_div' _ (by linarith)]

noncomputable def firstLoweringCoefficient (n m z l p : ℕ) : ℝ :=
  Real.sqrt ((p : ℝ) * ((n : ℝ)-p+1)) /
    Real.sqrt (((l : ℝ)+1) * ((n : ℝ)+m-2*z-l))

noncomputable def secondLoweringCoefficient (n m z l p : ℕ) : ℝ :=
  Real.sqrt (((z : ℝ)+l-p+1) * ((m : ℝ)-z-l+p)) /
    Real.sqrt (((l : ℝ)+1) * ((n : ℝ)+m-2*z-l))

lemma firstLoweringCoefficient_tendsto {n m : ℕ → ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hmn : Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 r)) (z l p : ℕ) :
    Tendsto (fun q => firstLoweringCoefficient (n q) (m q) z l p) atTop
      (𝓝 (Real.sqrt (p : ℝ) / Real.sqrt ((l : ℝ)+1) / Real.sqrt (1+r))) := by
  have h := (firstSqrtRatio_tendsto hr hn hmn (1-(p : ℝ)) (-2*(z : ℝ)-l)).const_mul
    (Real.sqrt (p : ℝ) / Real.sqrt ((l : ℝ)+1))
  have hf (q : ℕ) : firstLoweringCoefficient (n q) (m q) z l p =
      Real.sqrt (p : ℝ) / Real.sqrt ((l : ℝ)+1) *
        (Real.sqrt ((n q : ℝ)+(1-(p : ℝ))) /
          Real.sqrt ((n q : ℝ)+m q+(-2*(z : ℝ)-l))) := by
    simp only [firstLoweringCoefficient, Real.sqrt_mul (Nat.cast_nonneg p),
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (l : ℝ)+1)]
    ring_nf
  simpa only [hf, mul_one_div] using h

lemma secondLoweringCoefficient_tendsto {n m : ℕ → ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hmn : Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 r)) (z l p : ℕ)
    (hp : p ≤ z+l+1) :
    Tendsto (fun q => secondLoweringCoefficient (n q) (m q) z l p) atTop
      (𝓝 (Real.sqrt ((z : ℝ)+l-p+1) / Real.sqrt ((l : ℝ)+1) *
        (Real.sqrt r / Real.sqrt (1+r)))) := by
  have hp' : (0 : ℝ) ≤ (z : ℝ)+l-p+1 := by
    have h : (p : ℝ) ≤ (z : ℝ)+l+1 := by exact_mod_cast hp
    linarith
  have h := (secondSqrtRatio_tendsto hr hn hmn (-(z : ℝ)-l+p) (-2*(z : ℝ)-l)).const_mul
    (Real.sqrt ((z : ℝ)+l-p+1) / Real.sqrt ((l : ℝ)+1))
  have hf (q : ℕ) : secondLoweringCoefficient (n q) (m q) z l p =
      Real.sqrt ((z : ℝ)+l-p+1) / Real.sqrt ((l : ℝ)+1) *
        (Real.sqrt ((m q : ℝ)+(-(z : ℝ)-l+p)) /
          Real.sqrt ((n q : ℝ)+m q+(-2*(z : ℝ)-l))) := by
    simp only [secondLoweringCoefficient, Real.sqrt_mul hp',
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (l : ℝ)+1)]
    ring_nf
  simpa only [hf] using h

noncomputable def coupledCoefficient (n m z : ℕ) : ℕ → ℕ → ℝ
  | 0, p => highestCoefficient n m z p
  | l+1, p =>
      (if p = 0 then 0 else firstLoweringCoefficient n m z l p *
        coupledCoefficient n m z l (p-1)) +
      secondLoweringCoefficient n m z l p * coupledCoefficient n m z l p

noncomputable def limitingCoupledCoefficient (u v : ℝ) (z : ℕ) : ℕ → ℕ → ℝ
  | 0, p => limitingHighestCoefficient u v z p
  | l+1, p =>
      ((if p = 0 then 0 else Real.sqrt (p : ℝ) * v *
        limitingCoupledCoefficient u v z l (p-1)) +
      Real.sqrt ((z : ℝ)+l-p+1) * u * limitingCoupledCoefficient u v z l p) /
        Real.sqrt ((l : ℝ)+1)

lemma coupledCoefficient_eq_zero {n m z l p : ℕ} (hp : z+l < p) :
    coupledCoefficient n m z l p = 0 := by
  induction l generalizing p with
  | zero => exact highestCoefficient_eq_zero (by omega)
  | succ l ih =>
    simp [coupledCoefficient, ih (show z+l < p-1 by omega), ih (show z+l < p by omega)]

lemma limitingCoupledCoefficient_eq_zero {u v : ℝ} {z l p : ℕ} (hp : z+l < p) :
    limitingCoupledCoefficient u v z l p = 0 := by
  induction l generalizing p with
  | zero => simp [limitingCoupledCoefficient, limitingHighestCoefficient,
      Nat.choose_eq_zero_of_lt (show z < p by omega)]
  | succ l ih =>
    simp [limitingCoupledCoefficient, ih (show z+l < p-1 by omega), ih (show z+l < p by omega)]

theorem coupledCoefficient_tendsto {n m : ℕ → ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hmn : Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 r)) (z l p : ℕ) :
    Tendsto (fun q => coupledCoefficient (n q) (m q) z l p) atTop
      (𝓝 (limitingCoupledCoefficient (Real.sqrt r / Real.sqrt (1+r))
        (1 / Real.sqrt (1+r)) z l p)) := by
  induction l generalizing p with
  | zero => simpa only [coupledCoefficient, limitingCoupledCoefficient, add_comm 1 r] using
      highestCoefficient_tendsto hr hn hmn z p
  | succ l ih =>
    by_cases hp : p ≤ z+l+1
    · have h₁ : Tendsto (fun q => if p = 0 then (0 : ℝ) else
          firstLoweringCoefficient (n q) (m q) z l p * coupledCoefficient (n q) (m q) z l (p-1))
        atTop (𝓝 (if p = 0 then 0 else
          Real.sqrt (p : ℝ) / Real.sqrt ((l : ℝ)+1) / Real.sqrt (1+r) *
            limitingCoupledCoefficient (Real.sqrt r / Real.sqrt (1+r))
              (1 / Real.sqrt (1+r)) z l (p-1))) := by
        split_ifs with hp0
        · exact tendsto_const_nhds
        · exact (firstLoweringCoefficient_tendsto hr hn hmn z l p).mul (ih (p-1))
      have h₂ := (secondLoweringCoefficient_tendsto hr hn hmn z l p hp).mul (ih p)
      convert h₁.add h₂ using 1
      · rfl
      · congr 1
        simp only [limitingCoupledCoefficient]
        split_ifs <;> ring
    · simpa only [coupledCoefficient_eq_zero (show z+(l+1) < p by omega),
        limitingCoupledCoefficient_eq_zero (show z+(l+1) < p by omega)] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

open Polynomial

noncomputable def couplingPolynomial (u v : ℝ) (z l : ℕ) : ℝ[X] :=
  C (1 / (Real.sqrt (z.factorial : ℝ) * Real.sqrt (l.factorial : ℝ))) *
    (C u * X - C v)^z * (C v * X + C u)^l

noncomputable def monomialWeight (T p : ℕ) : ℝ :=
  Real.sqrt ((p.factorial : ℝ) * ((T-p).factorial : ℝ))

lemma monomialWeight_pos (T p : ℕ) : 0 < monomialWeight T p := by
  apply Real.sqrt_pos.mpr
  exact mul_pos (by exact_mod_cast p.factorial_pos)
    (by exact_mod_cast (T-p).factorial_pos)

lemma binomial_linear_coeff (u v : ℝ) (z p : ℕ) :
    ((C u * X - C v)^z).coeff p = (z.choose p : ℝ) * u^p * (-v)^(z-p) := by
  have h := comp_C_mul_X_coeff (p := (X + C (-v))^z) (r := u) (n := p)
  simp only [pow_comp, add_comp, X_comp, C_comp, coeff_X_add_C_pow] at h
  rw [map_neg] at h
  rw [sub_eq_add_neg]
  rw [h]
  ring

lemma monomialWeight_choose {z p : ℕ} (hp : p ≤ z) :
    monomialWeight z p * (z.choose p : ℝ) / Real.sqrt (z.factorial : ℝ) =
      Real.sqrt (z.choose p : ℝ) := by
  have hc : (z.choose p : ℝ) * (p.factorial : ℝ) * ((z-p).factorial : ℝ) =
      (z.factorial : ℝ) := by exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hp)
  have hs : Real.sqrt (z.choose p : ℝ) * monomialWeight z p =
      Real.sqrt (z.factorial : ℝ) := by
    rw [monomialWeight, ← Real.sqrt_mul (by positivity)]
    congr 1
    simpa only [mul_assoc] using hc
  apply (div_eq_iff (Real.sqrt_pos.mpr (by exact_mod_cast z.factorial_pos)).ne').mpr
  rw [← hs]
  have he : Real.sqrt (z.choose p : ℝ) ^ 2 = (z.choose p : ℝ) :=
    Real.sq_sqrt (by positivity)
  calc
    _ = monomialWeight z p * Real.sqrt (z.choose p : ℝ) ^ 2 := by rw [he]
    _ = _ := by ring

lemma highestCoefficient_eq_polynomial (u v : ℝ) (z p : ℕ) :
    limitingHighestCoefficient u v z p =
      monomialWeight z p * (couplingPolynomial u v z 0).coeff p := by
  simp only [couplingPolynomial, Nat.factorial_zero, Nat.cast_one, Real.sqrt_one,
    mul_one, pow_zero, coeff_C_mul, binomial_linear_coeff]
  by_cases hp : p ≤ z
  · rw [show (-v)^(z-p) = (-1 : ℝ)^(z-p)*v^(z-p) by rw [← mul_pow]; congr 1; ring]
    calc
      limitingHighestCoefficient u v z p =
          (monomialWeight z p * (z.choose p : ℝ) / Real.sqrt (z.factorial : ℝ)) *
            (-1 : ℝ)^(z-p)*u^p*v^(z-p) := by
        rw [monomialWeight_choose hp]
        unfold limitingHighestCoefficient
        ring
      _ = _ := by ring
  · simp [limitingHighestCoefficient, Nat.choose_eq_zero_of_lt (show z < p by omega)]

lemma couplingPolynomial_step (u v : ℝ) (z l : ℕ) :
    couplingPolynomial u v z (l+1) =
      C (1 / Real.sqrt ((l : ℝ)+1)) *
        ((C v * X + C u) * couplingPolynomial u v z l) := by
  have hf : Real.sqrt ((l+1).factorial : ℝ) =
      Real.sqrt ((l : ℝ)+1) * Real.sqrt (l.factorial : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Real.sqrt_mul (by positivity)]
  have hn : 1 / (Real.sqrt (z.factorial : ℝ) * Real.sqrt ((l+1).factorial : ℝ)) =
      (1 / Real.sqrt ((l : ℝ)+1)) *
        (1 / (Real.sqrt (z.factorial : ℝ) * Real.sqrt (l.factorial : ℝ))) := by
    rw [hf]
    ring
  unfold couplingPolynomial
  rw [hn, map_mul, pow_succ]
  ring

lemma couplingPolynomial_natDegree_le (u v : ℝ) (z l : ℕ) :
    (couplingPolynomial u v z l).natDegree ≤ z+l := by
  have ha : (C u * X - C v : ℝ[X]).natDegree ≤ 1 := by
    exact (natDegree_sub_le _ _).trans
      (max_le ((natDegree_C_mul_le _ _).trans natDegree_X_le) (by simp))
  have hb : (C v * X + C u : ℝ[X]).natDegree ≤ 1 := by
    exact (natDegree_add_le _ _).trans
      (max_le ((natDegree_C_mul_le _ _).trans natDegree_X_le) (by simp))
  unfold couplingPolynomial
  apply natDegree_mul_le.trans
  apply add_le_add
  · exact (natDegree_C_mul_le _ _).trans (natDegree_pow_le.trans (by nlinarith))
  · exact natDegree_pow_le.trans (by nlinarith)

lemma couplingPolynomial_coeff_eq_zero {u v : ℝ} {z l p : ℕ} (hp : z+l < p) :
    (couplingPolynomial u v z l).coeff p = 0 :=
  coeff_eq_zero_of_natDegree_lt ((couplingPolynomial_natDegree_le u v z l).trans_lt hp)

lemma monomialWeight_first {T p : ℕ} (hp : 0 < p) (hpT : p ≤ T+1) :
    monomialWeight (T+1) p = Real.sqrt (p : ℝ) * monomialWeight T (p-1) := by
  have hpp : (p-1)+1 = p := by omega
  have hfac : p.factorial = p * (p-1).factorial := by
    simpa only [hpp] using Nat.factorial_succ (p-1)
  have hTp : (T+1)-p = T-(p-1) := by omega
  simp only [monomialWeight, hfac, Nat.cast_mul, hTp]
  rw [← Real.sqrt_mul (Nat.cast_nonneg p)]
  congr 1
  ring

lemma monomialWeight_second {T p : ℕ} (hp : p ≤ T) :
    monomialWeight (T+1) p =
      Real.sqrt ((T : ℝ)-p+1) * monomialWeight T p := by
  have hTp : (T+1)-p = (T-p)+1 := by omega
  simp only [monomialWeight, hTp, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, Nat.cast_sub hp]
  rw [← Real.sqrt_mul (by
    have h : (p : ℝ) ≤ T := by exact_mod_cast hp
    linarith : (0 : ℝ) ≤ (T : ℝ)-p+1)]
  congr 1
  ring

lemma couplingPolynomial_step_coeff (u v : ℝ) (z l p : ℕ) :
    (couplingPolynomial u v z (l+1)).coeff p =
      ((if p = 0 then 0 else v * (couplingPolynomial u v z l).coeff (p-1)) +
        u * (couplingPolynomial u v z l).coeff p) / Real.sqrt ((l : ℝ)+1) := by
  rw [couplingPolynomial_step, coeff_C_mul, add_mul, mul_assoc (C v), coeff_add]
  simp only [coeff_C_mul]
  cases p with
  | zero => simp [div_eq_mul_inv, mul_comm]
  | succ p => simp [coeff_X_mul, mul_add, mul_comm, div_eq_mul_inv, mul_left_comm]

theorem limitingCoupledCoefficient_eq_polynomial (u v : ℝ) (z l p : ℕ) :
    limitingCoupledCoefficient u v z l p =
      monomialWeight (z+l) p * (couplingPolynomial u v z l).coeff p := by
  induction l generalizing p with
  | zero => simpa only [Nat.add_zero, limitingCoupledCoefficient] using
      highestCoefficient_eq_polynomial u v z p
  | succ l ih =>
    by_cases hp : p ≤ z+l+1
    · have hfirst : monomialWeight (z+l+1) p *
          (if p = 0 then 0 else v * (couplingPolynomial u v z l).coeff (p-1)) =
        (if p = 0 then 0 else Real.sqrt (p : ℝ) * v *
          (monomialWeight (z+l) (p-1) * (couplingPolynomial u v z l).coeff (p-1))) := by
        split_ifs with hp0
        · simp
        · rw [monomialWeight_first (by omega : 0 < p) hp]
          ring
      have hsecond : monomialWeight (z+l+1) p *
          (u * (couplingPolynomial u v z l).coeff p) =
        Real.sqrt ((z : ℝ)+l-p+1) * u *
          (monomialWeight (z+l) p * (couplingPolynomial u v z l).coeff p) := by
        by_cases hpT : p ≤ z+l
        · rw [monomialWeight_second hpT, Nat.cast_add]
          ring
        · rw [couplingPolynomial_coeff_eq_zero (by omega : z+l < p)]
          ring
      simp only [limitingCoupledCoefficient, ih, couplingPolynomial_step_coeff,
        ← Nat.add_assoc]
      rw [← mul_div_assoc, mul_add, hfirst, hsecond]
    · rw [limitingCoupledCoefficient_eq_zero (by omega : z+(l+1) < p),
        couplingPolynomial_coeff_eq_zero (by omega : z+(l+1) < p), mul_zero]

theorem coupledCoefficient_tendsto_polynomial {n m : ℕ → ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hmn : Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 r)) (z l p : ℕ) :
    Tendsto (fun q => coupledCoefficient (n q) (m q) z l p) atTop
      (𝓝 (monomialWeight (z+l) p *
        (couplingPolynomial (Real.sqrt r / Real.sqrt (1+r))
          (1 / Real.sqrt (1+r)) z l).coeff p)) := by
  simpa only [limitingCoupledCoefficient_eq_polynomial] using
    coupledCoefficient_tendsto hr hn hmn z l p

lemma ratio_to_total_ratio {n m : ℕ → ℕ} {s : ℝ} (hs : s < 1)
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hm : Tendsto (fun q => (m q : ℝ) / ((n q : ℝ)+m q)) atTop (𝓝 s)) :
    Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 (s / (1-s))) := by
  have h := hm.div ((tendsto_const_nhds (x := (1 : ℝ))).sub hm) (by linarith)
  apply h.congr'
  filter_upwards [hn.eventually (eventually_gt_atTop (0 : ℝ))] with q hq
  have hm0 : 0 ≤ (m q : ℝ) := by positivity
  have hsum : (n q : ℝ)+m q ≠ 0 := by linarith
  have hden : 1 - (m q : ℝ) / ((n q : ℝ)+m q) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    have he' := (eq_div_iff hsum).mp he
    linarith
  dsimp
  field_simp [hq.ne']
  ring

theorem fixed_deficit_coupling_limit {n m : ℕ → ℕ} {u : ℝ}
    (hu : 0 < u) (hu1 : u < 1)
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hm : Tendsto (fun q => (m q : ℝ) / ((n q : ℝ)+m q)) atTop (𝓝 (u^2)))
    (z l p : ℕ) :
    Tendsto (fun q => coupledCoefficient (n q) (m q) z l p) atTop
      (𝓝 (monomialWeight (z+l) p *
        (couplingPolynomial u (Real.sqrt (1-u^2)) z l).coeff p)) := by
  have huu : u^2 < 1 := by nlinarith
  have hd : 0 < 1-u^2 := by linarith
  have hv : Real.sqrt (1-u^2) ≠ 0 := (Real.sqrt_pos.mpr hd).ne'
  have hr : 0 ≤ u^2 / (1-u^2) := div_nonneg (sq_nonneg u) hd.le
  have hrr : 1 + u^2 / (1-u^2) = 1 / (1-u^2) := by field_simp; ring
  have hs₁ : Real.sqrt (u^2 / (1-u^2)) = u / Real.sqrt (1-u^2) := by
    rw [Real.sqrt_div (sq_nonneg u), Real.sqrt_sq_eq_abs, abs_of_pos hu]
  have hs₂ : Real.sqrt (1 + u^2 / (1-u^2)) = 1 / Real.sqrt (1-u^2) := by
    rw [hrr, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
  have hU : Real.sqrt (u^2 / (1-u^2)) / Real.sqrt (1 + u^2 / (1-u^2)) = u := by
    rw [hs₁, hs₂]
    field_simp
  have hV : 1 / Real.sqrt (1 + u^2 / (1-u^2)) = Real.sqrt (1-u^2) := by
    rw [hs₂, one_div_one_div]
  simpa only [hU, hV] using
    coupledCoefficient_tendsto_polynomial hr hn (ratio_to_total_ratio huu hn hm) z l p

end LaughlinGap.Spin

end

end OAI
