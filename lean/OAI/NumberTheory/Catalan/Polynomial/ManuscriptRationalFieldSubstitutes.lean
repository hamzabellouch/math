import OAI.NumberTheory.Catalan.Energy.ManuscriptBarrierFieldIntervals
import OAI.NumberTheory.Catalan.FirstBarrier.BarrierCaseOnePointY1
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogApprox

namespace OAI

section

namespace InternalCatalan
open scoped BigOperators

theorem manuscript_rat_interval_add {a b : ℚ × ℚ} {x y : ℚ}
    (hx : x ∈ Set.Icc a.1 a.2) (hy : y ∈ Set.Icc b.1 b.2) :
    x + y ∈ Set.Icc (manuscriptIntervalAdd a b).1
      (manuscriptIntervalAdd a b).2 := by
  change a.1 + b.1 ≤ x + y ∧ x + y ≤ a.2 + b.2
  exact ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

theorem manuscript_rat_interval_scale (c : ℚ) {a : ℚ × ℚ} {x : ℚ}
    (hx : x ∈ Set.Icc a.1 a.2) :
    c * x ∈ Set.Icc (manuscriptIntervalScale c a).1
      (manuscriptIntervalScale c a).2 := by
  by_cases hc : 0 ≤ c
  · rw [manuscriptIntervalScale, ite_eq_left hc]
    change c * a.1 ≤ c * x ∧ c * x ≤ c * a.2
    exact ⟨mul_le_mul_of_nonneg_left hx.1 hc, mul_le_mul_of_nonneg_left hx.2 hc⟩
  · rw [manuscriptIntervalScale, ite_eq_right hc]
    change c * a.2 ≤ c * x ∧ c * x ≤ c * a.1
    have hc' : c ≤ 0 := le_of_lt (lt_of_not_ge hc)
    exact ⟨mul_le_mul_of_nonpos_left hx.2 hc', mul_le_mul_of_nonpos_left hx.1 hc'⟩

theorem manuscript_rat_interval_sum {ι : Type*} (xs : List ι)
    (iv : ι → ℚ × ℚ) (f : ι → ℚ)
    (h : ∀ a ∈ xs, f a ∈ Set.Icc (iv a).1 (iv a).2) :
    (xs.map f).sum ∈ Set.Icc (manuscriptIntervalSum (xs.map iv)).1
      (manuscriptIntervalSum (xs.map iv)).2 := by
  revert h
  induction xs with
  | nil => intro h; simp [manuscriptIntervalSum]
  | cons a xs ih =>
    intro h
    have ha := h a (by simp)
    have ht := ih (fun b hb => h b (by simp [hb]))
    simpa [manuscriptIntervalAdd, manuscriptIntervalSum] using manuscript_rat_interval_add ha ht

theorem manuscript_logHErrorRat_nonneg (y : ℚ) (hy : y ∈ Set.Icc (1 : ℚ) 2) :
    0 ≤ manuscriptLogHErrorRat y := by
  have hyp : 0 < y + 1 := by linarith [hy.1]
  have hq0 : 0 ≤ (y - 1) / (y + 1) :=
    div_nonneg (sub_nonneg.mpr hy.1) hyp.le
  have hq1 : (y - 1) / (y + 1) ≤ (1 / 3 : ℚ) := by
    apply (div_le_iff₀ hyp).mpr
    linarith [hy.2]
  have hq2 : ((y - 1) / (y + 1)) ^ 2 ≤ (1 / 9 : ℚ) := by
    have h := mul_le_mul hq1 hq1 hq0 (by norm_num : (0 : ℚ) ≤ 1 / 3)
    nlinarith
  have hden : 0 ≤ 37 * (1 - ((y - 1) / (y + 1)) ^ 2) := by
    nlinarith
  unfold manuscriptLogHErrorRat
  exact div_nonneg (mul_nonneg (by norm_num) (pow_nonneg hq0 37)) hden

theorem manuscript_logHRat_interval (y : ℚ) (hy : y ∈ Set.Icc (1 : ℚ) 2) :
    barrierLogHRat y ∈ Set.Icc (manuscriptLogHInterval y).1
      (manuscriptLogHInterval y).2 := by
  change barrierLogHRat y ≤ barrierLogHRat y ∧
    barrierLogHRat y ≤ barrierLogHRat y + manuscriptLogHErrorRat y
  exact ⟨le_rfl, by linarith [manuscript_logHErrorRat_nonneg y hy]⟩

theorem manuscript_atanJRat_interval (t : ℚ) :
    barrierAtanJRat t ∈ Set.Icc (manuscriptAtanInterval t).1
      (manuscriptAtanInterval t).2 := by
  have he : (0 : ℚ) ≤ |t| ^ 49 / 49 :=
    div_nonneg (pow_nonneg (abs_nonneg t) 49) (by norm_num)
  by_cases ht : 0 ≤ t
  · rw [manuscriptAtanInterval, ite_eq_left ht]
    change barrierAtanJRat t ≤ barrierAtanJRat t ∧
      barrierAtanJRat t ≤ barrierAtanJRat t + |t| ^ 49 / 49
    exact ⟨le_rfl, by linarith⟩
  · rw [manuscriptAtanInterval, ite_eq_right ht]
    change barrierAtanJRat t - |t| ^ 49 / 49 ≤ barrierAtanJRat t ∧
      barrierAtanJRat t ≤ barrierAtanJRat t
    exact ⟨by linarith, le_rfl⟩

theorem manuscript_scaledLogRat_interval (m : ℤ) (y : ℚ)
    (hy : y ∈ Set.Icc (1 : ℚ) 2) :
    barrierScaledLogRat m y ∈ Set.Icc (manuscriptScaledLogInterval m y).1
      (manuscriptScaledLogInterval m y).2 := by
  exact manuscript_rat_interval_add
    (manuscript_rat_interval_scale (m : ℚ) (manuscript_logHRat_interval 2 (by norm_num)))
    (manuscript_logHRat_interval y hy)

theorem manuscript_argApproxRat_interval (k : ℤ) (t : ℚ) :
    barrierArgApproxRat k t ∈ Set.Icc (manuscriptArgInterval k t).1
      (manuscriptArgInterval k t).2 := by
  have hpi : barrierAtanJRat (1 / 2) + barrierAtanJRat (1 / 3) ∈
      Set.Icc manuscriptPiQuarterInterval.1 manuscriptPiQuarterInterval.2 :=
    manuscript_rat_interval_add (manuscript_atanJRat_interval (1 / 2))
      (manuscript_atanJRat_interval (1 / 3))
  exact manuscript_rat_interval_add (manuscript_rat_interval_scale (k : ℚ) hpi)
    (manuscript_atanJRat_interval t)

theorem manuscript_weightedComplexLogRat_interval (c d : ℚ) (m k : ℤ) (y t : ℚ)
    (hy : y ∈ Set.Icc (1 : ℚ) 2) :
    barrierWeightedComplexLogRat c d m k y t ∈
      Set.Icc (manuscriptWeightedComplexLogInterval c d m k y t).1
        (manuscriptWeightedComplexLogInterval c d m k y t).2 := by
  have h := manuscript_rat_interval_add
    (manuscript_rat_interval_scale (c / 2) (manuscript_scaledLogRat_interval m y hy))
    (manuscript_rat_interval_scale (-d) (manuscript_argApproxRat_interval k t))
  have he : barrierWeightedComplexLogRat c d m k y t =
      (c / 2) * barrierScaledLogRat m y + (-d) * barrierArgApproxRat k t := by
    unfold barrierWeightedComplexLogRat
    ring
  rw [he]
  exact h

theorem manuscript_atanJRat_neg (t : ℚ) : barrierAtanJRat (-t) = -barrierAtanJRat t := by
  unfold barrierAtanJRat
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [(odd_two_mul_add_one j).neg_pow t]
  ring

theorem manuscript_argApproxRat_neg (k : ℤ) (t : ℚ) :
    barrierArgApproxRat (-k) (-t) = -barrierArgApproxRat k t := by
  unfold barrierArgApproxRat
  rw [Int.cast_neg, manuscript_atanJRat_neg]
  ring

theorem manuscript_weightedComplexLogRat_conj (c d : ℚ) (m k : ℤ) (y t : ℚ) :
    barrierWeightedComplexLogRat c (-d) m (-k) y (-t) =
      barrierWeightedComplexLogRat c d m k y t := by
  unfold barrierWeightedComplexLogRat
  rw [manuscript_argApproxRat_neg]
  ring

end InternalCatalan

end

section

namespace InternalCatalan

theorem manuscript_x_substitute_interval (c v : ℚ)
    (m0 m1 m2 : ℤ) (y0 y1 y2 : ℚ)
    (h0 : y0 ∈ Set.Icc (1 : ℚ) 2) (h1 : y1 ∈ Set.Icc (1 : ℚ) 2)
    (h2 : y2 ∈ Set.Icc (1 : ℚ) 2) :
    (19 / 48 : ℚ) * barrierScaledLogRat m0 y0 +
      (1 / 12 : ℚ) * barrierScaledLogRat m1 y1 -
      c * barrierScaledLogRat m2 y2 + v ∈
        Set.Icc (manuscriptXLogFieldInterval c v m0 m1 m2 y0 y1 y2).1
          (manuscriptXLogFieldInterval c v m0 m1 m2 y0 y1 y2).2 := by
  have h := manuscript_rat_interval_add
    (manuscript_rat_interval_add
      (manuscript_rat_interval_add
        (manuscript_rat_interval_scale (19 / 48)
          (manuscript_scaledLogRat_interval m0 y0 h0))
        (manuscript_rat_interval_scale (1 / 12)
          (manuscript_scaledLogRat_interval m1 y1 h1)))
      (manuscript_rat_interval_scale (-c)
        (manuscript_scaledLogRat_interval m2 y2 h2)))
    (show v ∈ Set.Icc (((v, v) : ℚ × ℚ).1) (((v, v) : ℚ × ℚ).2)
      from ⟨le_rfl, le_rfl⟩)
  simpa only [manuscriptXLogFieldInterval, sub_eq_add_neg, neg_mul] using h

theorem manuscript_y_substitute_interval (v : ℚ)
    (m0 m1 : ℤ) (y0 y1 : ℚ)
    (h0 : y0 ∈ Set.Icc (1 : ℚ) 2) (h1 : y1 ∈ Set.Icc (1 : ℚ) 2) :
    (7 / 48 : ℚ) * barrierScaledLogRat m0 y0 +
      (1 / 12 : ℚ) * barrierScaledLogRat m1 y1 + v ∈
        Set.Icc (manuscriptYLogFieldInterval v m0 m1 y0 y1).1
          (manuscriptYLogFieldInterval v m0 m1 y0 y1).2 := by
  have h := manuscript_rat_interval_add
    (manuscript_rat_interval_add
      (manuscript_rat_interval_scale (7 / 48)
        (manuscript_scaledLogRat_interval m0 y0 h0))
      (manuscript_rat_interval_scale (1 / 12)
        (manuscript_scaledLogRat_interval m1 y1 h1)))
    (show v ∈ Set.Icc (((v, v) : ℚ × ℚ).1) (((v, v) : ℚ × ℚ).2)
      from ⟨le_rfl, le_rfl⟩)
  simpa only [manuscriptYLogFieldInterval] using h

end InternalCatalan

end

end OAI
