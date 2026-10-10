import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingSobolevWeights

namespace OAI

/-! # The scale-uniform one-dimensional inverse-weight bound -/

open Set MeasureTheory

namespace DefocusingNLS

theorem continuous_expandingOneDimKernel (a k L : ℝ) (hk : 8 < k) (hL : 1 ≤ L) :
    Continuous (expandingOneDimKernel a k L) := by
  have hlow : Continuous (fun x : ℝ => (1 + x ^ 2) ^ ((6 - a) / 12)) :=
    (continuous_const.add (continuous_id.pow 2)).rpow_const
      (fun x : ℝ => Or.inl (ne_of_gt (show 0 < 1 + x ^ 2 by positivity)))
  have hhigh : Continuous (fun x : ℝ => |x| ^ (k / 6)) :=
    continuous_abs.rpow_const (fun _ => Or.inr (by linarith))
  exact ((continuous_const.mul hlow).add (continuous_const.mul hhigh)).inv₀
    (fun x => (expandingOneDimWeight_pos a k L x hL).ne')

private theorem expanding_low_integral (a L : ℝ) (ha : 0 < a) (hL : 1 ≤ L) :
    (∫ x in Ioc 0 L, L ^ (-a / 6) * x ^ (a / 6 - 1)) = 1 / (a / 6) := by
  have hLp : 0 < L := by linarith
  rw [← intervalIntegral.integral_of_le hLp.le, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by linarith))]
  have he : a / 6 - 1 + 1 = a / 6 := by ring
  rw [he, Real.zero_rpow (by positivity : a / 6 ≠ 0), sub_zero]
  calc
    _ = (L ^ (-a / 6) * L ^ (a / 6)) / (a / 6) := by ring
    _ = _ := by
      rw [← Real.rpow_add hLp, show -a / 6 + a / 6 = 0 by ring, Real.rpow_zero]

private theorem expanding_high_integral (k L : ℝ) (hk : 8 < k) (hL : 1 ≤ L) :
    (∫ x in Ioi L, L ^ (k / 6 - 1) * x ^ (-k / 6)) = 1 / (k / 6 - 1) := by
  have hLp : 0 < L := by linarith
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hLp]
  have he : -k / 6 + 1 = -(k / 6 - 1) := by ring
  rw [he, div_neg, neg_div, neg_neg]
  calc
    _ = (L ^ (k / 6 - 1) * L ^ (-(k / 6 - 1))) / (k / 6 - 1) := by ring
    _ = _ := by
      rw [← Real.rpow_add hLp, add_neg_cancel, Real.rpow_zero]

/-- The inverse one-dimensional weight has an integral bounded independently of `L`. -/
theorem expandingOneDimKernel_integrable_bound (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) :
    IntegrableOn (expandingOneDimKernel a k L) (Ioi 0) ∧
      (∫ x in Ioi 0, expandingOneDimKernel a k L x) ≤
        1 / (a / 6) + 1 / (k / 6 - 1) := by
  have hLp : 0 < L := by linarith
  have hlow : IntegrableOn (fun x : ℝ => L ^ (-a / 6) * x ^ (a / 6 - 1)) (Ioc 0 L) := by
    have hp : IntegrableOn (fun x : ℝ => x ^ (a / 6 - 1)) (Ioc 0 L) := by
      apply (integrableOn_Ioc_iff_integrableOn_Ioo
        (f := fun x : ℝ => x ^ (a / 6 - 1)) (by finiteness)).mpr
      exact (intervalIntegral.integrableOn_Ioo_rpow_iff hLp).mpr (by linarith)
    exact hp.const_mul _
  have hhigh : IntegrableOn (fun x : ℝ => L ^ (k / 6 - 1) * x ^ (-k / 6)) (Ioi L) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hLp).const_mul _
  have hc : AEStronglyMeasurable (expandingOneDimKernel a k L) (volume : Measure ℝ) :=
    (continuous_expandingOneDimKernel a k L hk hL).aestronglyMeasurable
  have hklow : IntegrableOn (expandingOneDimKernel a k L) (Ioc 0 L) := by
    apply hlow.mono' hc.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (expandingOneDimKernel_nonneg a k L x hL)]
    exact expandingOneDimKernel_le_low a k L x ha ha1 hL hx.1
  have hkhigh : IntegrableOn (expandingOneDimKernel a k L) (Ioi L) := by
    apply hhigh.mono' hc.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (expandingOneDimKernel_nonneg a k L x hL)]
    exact expandingOneDimKernel_le_high a k L x hL (hLp.trans hx)
  have hunion : Ioc 0 L ∪ Ioi L = Ioi (0 : ℝ) := Ioc_union_Ioi_eq_Ioi hLp.le
  have hdis : Disjoint (Ioc (0 : ℝ) L) (Ioi L) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact (not_lt_of_ge hx.2) hy
  refine ⟨by rw [← hunion]; exact hklow.union hkhigh, ?_⟩
  rw [← hunion, setIntegral_union hdis measurableSet_Ioi hklow hkhigh]
  calc
    _ ≤ (∫ x in Ioc 0 L, L ^ (-a / 6) * x ^ (a / 6 - 1)) +
        ∫ x in Ioi L, L ^ (k / 6 - 1) * x ^ (-k / 6) := by
      apply add_le_add
      · exact setIntegral_mono_on hklow hlow measurableSet_Ioc
          (fun x hx => expandingOneDimKernel_le_low a k L x ha ha1 hL hx.1)
      · exact setIntegral_mono_on hkhigh hhigh measurableSet_Ioi
          (fun x hx => expandingOneDimKernel_le_high a k L x hL (hLp.trans hx))
    _ = _ := by rw [expanding_low_integral a L ha hL, expanding_high_integral k L hk hL]

/-- The full integer inverse-weight sum is uniformly bounded on all expanding scales. -/
theorem expandingOneDimKernel_integer_sum_bound (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) :
    Summable (fun n : ℤ => expandingOneDimKernel a k L n) ∧
      (∑' n : ℤ, expandingOneDimKernel a k L n) ≤
        1 + 2 * (1 / (a / 6) + 1 / (k / 6 - 1)) := by
  have hanti := expandingOneDimKernel_antitone a k L ha ha1 hk hL
  obtain ⟨hint, hib⟩ := expandingOneDimKernel_integrable_bound a k L ha ha1 hk hL
  have hnon : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ expandingOneDimKernel a k L x :=
    fun x _ => expandingOneDimKernel_nonneg a k L x hL
  have hs : Summable (fun n : ℕ => expandingOneDimKernel a k L (n : ℝ)) :=
    hanti.summable_of_integrableOn_Ioi_zero hint hnon
  have hs1 : Summable (fun n : ℕ => expandingOneDimKernel a k L (n + 1)) :=
    by simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hs
  have hneg : Summable (fun n : ℕ =>
      expandingOneDimKernel a k L (((-((n : ℤ) + 1)) : ℤ) : ℝ)) := by
    simpa only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
      expandingOneDimKernel_even] using hs1
  have hnat : Summable (fun n : ℕ => expandingOneDimKernel a k L ((n : ℤ) : ℝ)) :=
    by simpa only [Int.cast_natCast] using hs
  have hintsum : Summable (fun n : ℤ => expandingOneDimKernel a k L (n : ℝ)) :=
    Summable.of_nat_of_neg_add_one
      (f := fun n : ℤ => expandingOneDimKernel a k L (n : ℝ)) hnat hneg
  refine ⟨hintsum, ?_⟩
  rw [tsum_of_nat_of_neg_add_one
    (f := fun n : ℤ => expandingOneDimKernel a k L (n : ℝ)) hnat hneg]
  simp only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
    expandingOneDimKernel_even]
  have hb0 : (∑' n : ℕ, expandingOneDimKernel a k L (n : ℝ)) ≤
      expandingOneDimKernel a k L 0 + (1 / (a / 6) + 1 / (k / 6 - 1)) :=
    (hanti.tsum_le_integral hint hnon).trans
    (add_le_add le_rfl hib)
  have hb1 : (∑' n : ℕ, expandingOneDimKernel a k L (n + 1 : ℕ)) ≤
      1 / (a / 6) + 1 / (k / 6 - 1) :=
    (hanti.tsum_add_one_le_integral hint hnon).trans hib
  simp only [Nat.cast_add, Nat.cast_one] at hb1
  have hz := expandingOneDimKernel_zero_le a k L ha hk hL
  linarith

end DefocusingNLS

end OAI
