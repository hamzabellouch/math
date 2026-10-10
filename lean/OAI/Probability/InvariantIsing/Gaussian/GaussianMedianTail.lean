import OAI.Probability.InvariantIsing.Haar.ProbabilityMedian

namespace OAI

/-! Conversion of two Gaussian tails about a center to tails about any median. -/
noncomputable section
open MeasureTheory Set
namespace InvariantIsing

theorem gaussian_median_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (c m k : ℝ) (hk : 0 < k)
    (hm1 : (1/2:ℝ) ≤ μ.real {ω | f ω ≤ m})
    (hm2 : (1/2:ℝ) ≤ μ.real {ω | m ≤ f ω})
    (hplus : ∀ r > 0, μ.real {ω | r ≤ f ω-c} ≤ Real.exp (-k*r^2))
    (hminus : ∀ r > 0, μ.real {ω | r ≤ c-f ω} ≤ Real.exp (-k*r^2))
    {r : ℝ} (hr : 0 < r) :
    μ.real {ω | r ≤ |f ω-m|} ≤ Real.exp 1*Real.exp (-k*r^2/8) := by
  let a := Real.sqrt (2/k)
  have ha : 0 < a := Real.sqrt_pos.mpr (div_pos (by norm_num) hk)
  have ha2 : a^2 = 2/k := Real.sq_sqrt (div_pos (by norm_num) hk).le
  have hka : k*a^2 = 2 := by rw [ha2]; field_simp
  have hexp : Real.exp (-2) < (1/2:ℝ) := by
    have he := Real.add_one_le_exp (2:ℝ)
    have hp := Real.exp_pos (-2)
    have hm : Real.exp (-2)*Real.exp 2 = 1 := by rw [← Real.exp_add]; norm_num
    nlinarith
  have hpa : μ.real {ω | a ≤ f ω-c} < (1/2:ℝ) := by
    have h := hplus a ha
    have he : -k*a^2 = -(2:ℝ) := by nlinarith [hka]
    rw [he] at h
    exact h.trans_lt hexp
  have hma : μ.real {ω | a ≤ c-f ω} < (1/2:ℝ) := by
    have h := hminus a ha
    have he : -k*a^2 = -(2:ℝ) := by nlinarith [hka]
    rw [he] at h
    exact h.trans_lt hexp
  have hmc : |m-c| ≤ a := by
    apply abs_le.mpr
    constructor
    · by_contra h
      have hs : {ω | f ω ≤ m} ⊆ {ω | a ≤ c-f ω} := by
        intro ω hω
        simp only [mem_ofPred_eq] at *
        linarith
      exact (not_lt_of_ge (hm1.trans (measureReal_mono hs))) hma
    · by_contra h
      have hs : {ω | m ≤ f ω} ⊆ {ω | a ≤ f ω-c} := by
        intro ω hω
        simp only [mem_ofPred_eq] at *
        linarith
      exact (not_lt_of_ge (hm2.trans (measureReal_mono hs))) hpa
  by_cases hsmall : r ≤ 2*a
  · have hkr : k*r^2/8 ≤ 1 := by
      have hsq : r^2 ≤ 4*a^2 := by nlinarith
      have hm := mul_le_mul_of_nonneg_left hsq hk.le
      nlinarith [hka]
    have hex : 1 ≤ Real.exp 1*Real.exp (-k*r^2/8) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp_iff.mpr (by linarith)
    exact measureReal_le_one.trans hex
  · have hhalf : 0 < r/2 := half_pos hr
    have hs : {ω | r ≤ |f ω-m|} ⊆ {ω | r/2 ≤ |f ω-c|} := by
      intro ω hω
      have htri : |f ω-m| ≤ |f ω-c|+|m-c| := by
        simpa only [sub_add_sub_cancel,abs_sub_comm c m] using abs_add_le (f ω-c) (c-m)
      simp only [mem_ofPred_eq] at *
      linarith
    have he : {ω | r/2 ≤ |f ω-c|} =
        {ω | r/2 ≤ f ω-c} ∪ {ω | r/2 ≤ c-f ω} := by
      ext ω
      simp only [mem_ofPred_eq,mem_union,le_abs,neg_sub]
    have ht : μ.real {ω | r/2 ≤ |f ω-c|} ≤ 2*Real.exp (-k*(r/2)^2) := by
      rw [he]
      have hu := measureReal_union_le (μ := μ) {ω | r/2 ≤ f ω-c} {ω | r/2 ≤ c-f ω}
      linarith [hplus (r/2) hhalf,hminus (r/2) hhalf]
    calc
      _ ≤ μ.real {ω | r/2 ≤ |f ω-c|} := measureReal_mono hs
      _ ≤ 2*Real.exp (-k*(r/2)^2) := ht
      _ ≤ Real.exp 1*Real.exp (-k*r^2/8) := by
        apply mul_le_mul
        · simpa only [show (1:ℝ)+1=2 by norm_num] using Real.add_one_le_exp (1:ℝ)
        · apply Real.exp_le_exp.mpr
          nlinarith [mul_nonneg hk.le (sq_nonneg r)]
        · exact (Real.exp_pos _).le
        · exact (Real.exp_pos _).le

end InvariantIsing

end

end OAI
