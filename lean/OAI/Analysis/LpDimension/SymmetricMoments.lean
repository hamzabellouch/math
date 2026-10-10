import OAI.Analysis.LpDimension.BelowTwo

namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set
open scoped BigOperators Topology Matrix ENNReal NNReal
universe u

namespace SubpolynomialLp

lemma symmetric_power_near (q : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 ≤ u → u ≤ 1/2 →
      ((1+u)^q+(1-u)^q)/2 ≤ 1+C*u^2 := by
  let f : ℝ → ℝ := fun u => ((1+u)^q+(1-u)^q)/2
  have hf : ContDiffOn ℝ 2 f (Icc 0 (1/2)) := by
    apply ContDiffOn.div_const
    apply ContDiffOn.add
    · exact (contDiffOn_const.add contDiffOn_id).rpow_const_of_ne
        (fun x hx => ne_of_gt (by linarith [hx.1] : 0 < 1+x))
    · exact (contDiffOn_const.sub contDiffOn_id).rpow_const_of_ne
        (fun x hx => ne_of_gt (by linarith [hx.2] : 0 < 1-x))
  obtain ⟨C,hC⟩ := exists_taylor_mean_remainder_bound (n := 1) (by norm_num : (0:ℝ) ≤ 1/2) hf
  have hd : HasDerivAt f 0 0 := by
    have h₁ := ((hasDerivAt_const (0:ℝ) (1:ℝ)).add (hasDerivAt_id (0:ℝ))).rpow_const
      (p := q) (Or.inl (by norm_num : (1:ℝ)+0 ≠ 0))
    have h₂ := ((hasDerivAt_const (0:ℝ) (1:ℝ)).sub (hasDerivAt_id (0:ℝ))).rpow_const
      (p := q) (Or.inl (by norm_num : (1:ℝ)-0 ≠ 0))
    simpa [f] using (h₁.add h₂).div_const 2
  have ht (u : ℝ) : taylorWithinEval f 1 (Icc 0 (1/2)) 0 u = 1 := by
    rw [taylorWithinEval_succ, taylor_within_zero_eval,
      iteratedDerivWithin_one, hd.hasDerivWithinAt.derivWithin
        (uniqueDiffOn_Icc (by norm_num : (0:ℝ) < 1/2) 0 (by constructor <;> norm_num))]
    simp [f]
  refine ⟨max C 0, le_max_right _ _, fun u hu hu' => ?_⟩
  have hh := hC u ⟨hu,hu'⟩
  rw [ht, sub_zero, Real.norm_eq_abs] at hh
  have hc := mul_le_mul_of_nonneg_right (le_max_left C 0) (sq_nonneg u)
  have hl := le_abs_self (f u-1)
  dsimp [f] at hl hh
  linarith

lemma symmetric_power_unit_upper (q ε : ℝ) (hq : 0 < q) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 ≤ u →
      (|1+u|^q+|1-u|^q)/2 ≤ 1+(1+ε)*u^q+C*u^2 := by
  obtain ⟨C,hC,hnear⟩ := symmetric_power_near q
  let δ := (1+ε)^(1/q)-1
  have hδ : 0 < δ := by
    have hh := Real.one_lt_rpow (by linarith : (1:ℝ) < 1+ε) (by positivity : 0 < 1/q)
    dsimp [δ]; linarith
  have hδq : (1+δ)^q = 1+ε := by
    dsimp [δ]
    rw [show 1+((1+ε)^(1/q)-1) = (1+ε)^(1/q) by ring, ← Real.rpow_mul (by linarith : 0 ≤ 1+ε),
      one_div_mul_cancel hq.ne', Real.rpow_one]
  let R := max 2 δ⁻¹
  have hR : 0 < R := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  let K := max C (4*(1+R)^q)
  have hK : 0 ≤ K := hC.trans (le_max_left _ _)
  refine ⟨K,hK,fun u hu => ?_⟩
  by_cases hsmall : u ≤ 1/2
  · rw [abs_of_nonneg (by linarith : 0 ≤ 1+u), abs_of_nonneg (by linarith : 0 ≤ 1-u)]
    have hh := hnear u hu hsmall
    have hk := mul_le_mul_of_nonneg_right (le_max_left C (4*(1+R)^q)) (sq_nonneg u)
    have hn : 0 ≤ (1+ε)*u^q := by positivity
    dsimp [K] at *
    linarith
  by_cases hlarge : R ≤ u
  · have hu0 : 0 < u := hR.trans_le hlarge
    have hdu : 1 ≤ δ*u := by
      have hi : δ⁻¹ ≤ u := (le_max_right _ _).trans hlarge
      have hh := mul_le_mul_of_nonneg_left hi hδ.le
      rwa [mul_inv_cancel₀ hδ.ne'] at hh
    have ha : |1+u| ≤ (1+δ)*u := by rw [abs_of_nonneg (by linarith)]; nlinarith
    have hb : |1-u| ≤ (1+δ)*u := by
      exact (abs_sub _ _).trans (by simp only [abs_one, abs_of_nonneg hu]; nlinarith)
    have hp₁ := Real.rpow_le_rpow (abs_nonneg _) ha hq.le
    have hp₂ := Real.rpow_le_rpow (abs_nonneg _) hb hq.le
    rw [Real.mul_rpow (by linarith : 0 ≤ 1+δ) hu, hδq] at hp₁ hp₂
    nlinarith [mul_nonneg hK (sq_nonneg u)]
  · have hur : u ≤ R := le_of_not_ge hlarge
    have ha : |1+u| ≤ 1+R := by rw [abs_of_nonneg (by linarith)]; linarith
    have hb : |1-u| ≤ 1+R := (abs_sub _ _).trans (by simpa only [abs_one, abs_of_nonneg hu] using add_le_add_right hur 1)
    have hp₁ := Real.rpow_le_rpow (abs_nonneg _) ha hq.le
    have hp₂ := Real.rpow_le_rpow (abs_nonneg _) hb hq.le
    have hu2 : 1/4 ≤ u^2 := by nlinarith
    have hpow : 0 ≤ (1+R)^q := Real.rpow_nonneg (by linarith) _
    have hk : 4*(1+R)^q ≤ K := le_max_right _ _
    have hh := mul_le_mul_of_nonneg_left hu2 (by positivity : 0 ≤ 4*(1+R)^q)
    have hh' := mul_le_mul_of_nonneg_right hk (sq_nonneg u)
    have hn : 0 ≤ (1+ε)*u^q := by positivity
    nlinarith

lemma sq_rpow_half_abs (x q : ℝ) : (x^2)^(q/2) = |x|^q := by
  rw [← sq_abs x, ← Real.rpow_natCast_mul (abs_nonneg x)]
  congr 1
  ring

lemma symmetric_power_lower (q : ℝ) (hq : 2 ≤ q) (a b : ℝ) :
    |a|^q+|b|^q ≤ (|a+b|^q+|a-b|^q)/2 := by
  have hconv := (convexOn_rpow (by linarith : 1 ≤ q/2)).2
    (show (a+b)^2 ∈ Ici (0:ℝ) from sq_nonneg (a+b)) (show (a-b)^2 ∈ Ici (0:ℝ) from sq_nonneg (a-b))
    (by norm_num : 0 ≤ (1/2:ℝ)) (by norm_num : 0 ≤ (1/2:ℝ)) (by norm_num : (1/2:ℝ)+1/2=1)
  simp only [smul_eq_mul, sq_rpow_half_abs] at hconv
  have halg : (1/2:ℝ)*(a+b)^2+1/2*(a-b)^2 = a^2+b^2 := by ring
  rw [halg] at hconv
  have hlow := Real.add_rpow_le_rpow_add (sq_nonneg a) (sq_nonneg b) (by linarith : 1 ≤ q/2)
  rw [sq_rpow_half_abs, sq_rpow_half_abs] at hlow
  linarith

lemma symmetric_power_abs (q a b : ℝ) :
    |a+b|^q+|a-b|^q = (|a|+|b|)^q+|(|a|-|b|)|^q := by
  rcases le_total 0 a with ha|ha <;> rcases le_total 0 b with hb|hb
  · simp only [abs_of_nonneg ha, abs_of_nonneg hb, abs_of_nonneg (add_nonneg ha hb)]
  · rw [abs_of_nonneg ha, abs_of_nonpos hb]
    have h₁ : a-b = a+-b := by ring
    have h₂ : a- -b = a+b := by ring
    rw [h₂, h₁, abs_of_nonneg (by linarith : 0 ≤ a+-b), add_comm]
  · rw [abs_of_nonpos ha, abs_of_nonneg hb]
    have h₁ : a-b = -(-a+b) := by ring
    have h₂ : -a-b = -(a+b) := by ring
    rw [h₁, h₂, abs_neg, abs_neg, abs_of_nonneg (by linarith : 0 ≤ -a+b), add_comm]
  · rw [abs_of_nonpos ha, abs_of_nonpos hb, abs_of_nonpos (add_nonpos ha hb)]
    have h₁ : -(a+b) = -a+-b := by ring
    have h₂ : -a- -b = -(a-b) := by ring
    rw [h₁, h₂, abs_neg]

lemma symmetric_power_upper (q ε : ℝ) (hq : 2 < q) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℝ,
      (|a+b|^q+|a-b|^q)/2 ≤ |a|^q+(1+ε)* |b|^q+C* |a|^(q-2)*b^2 := by
  obtain ⟨C,hC,hh⟩ := symmetric_power_unit_upper q ε (by linarith) hε
  refine ⟨C,hC,fun a b => ?_⟩
  by_cases ha : a=0
  · subst a
    simp only [zero_add, zero_sub, abs_neg, abs_zero, Real.zero_rpow (by linarith : q ≠ 0),
      Real.zero_rpow (by linarith : q-2 ≠ 0), mul_zero, zero_mul, add_zero]
    nlinarith [Real.rpow_nonneg (abs_nonneg b) q]
  have ha0 : 0 < |a| := abs_pos.mpr ha
  have he := hh (|b|/|a|) (by positivity)
  have he' := mul_le_mul_of_nonneg_left he (Real.rpow_nonneg ha0.le q)
  rw [symmetric_power_abs]
  have hsum : |a|+|b| = |a| *(1+|b|/|a|) := by field_simp
  have hsub : |(|a|-|b|)| = |a| * |(1-|b|/|a|)| := by
    calc
      _ = |(|a| *(1-|b|/|a|))| := by congr 1; field_simp
      _ = _ := by rw [abs_mul, abs_of_pos ha0]
  have hpow : |a|^q*(|b|/|a|)^q = |b|^q := by
    rw [← Real.mul_rpow ha0.le (by positivity), mul_div_cancel₀ _ ha0.ne']
  have hq2 : |a|^q*(|b|/|a|)^2 = |a|^(q-2)*b^2 := by
    rw [div_pow, sq_abs, Real.rpow_sub ha0, Real.rpow_two]
    ring
  rw [hsum, hsub, Real.mul_rpow ha0.le (by positivity), Real.mul_rpow ha0.le (abs_nonneg _)]
  rw [abs_of_nonneg (by positivity : 0 ≤ 1+|b|/|a|)] at he'
  have halg : |a|^q*(1+(1+ε)*(|b|/|a|)^q+C*(|b|/|a|)^2) =
      |a|^q+(1+ε)* |b|^q+C* |a|^(q-2)*b^2 := by
    calc
      _ = |a|^q+(1+ε)*(|a|^q*(|b|/|a|)^q)+C*(|a|^q*(|b|/|a|)^2) := by ring
      _ = _ := by rw [hpow,hq2]; ring
  rw [halg] at he'
  linarith


lemma bounded_conv (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A B : ℝ) (hμ : ∀ᵐ x ∂μ, |x| ≤ A) (hν : ∀ᵐ x ∂ν, |x| ≤ B) :
    ∀ᵐ x ∂(μ ∗ ν), |x| ≤ A+B := by
  rw [Measure.conv, ae_map_iff (by fun_prop) (measurableSet_le (by fun_prop) measurable_const)]
  apply (Measure.ae_prod_iff_ae_ae (p := fun x : ℝ × ℝ => |x.1+x.2| ≤ A+B)
    (measurableSet_le (by fun_prop) measurable_const)).mpr
  exact hμ.mono (fun x hx => hν.mono (fun y hy =>
    (abs_add_le x y).trans (add_le_add hx hy)))

lemma bounded_abs_moment_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (B q : ℝ) (hB : ∀ᵐ x ∂μ, |x| ≤ B) (hq : 0 ≤ q) :
    Integrable (fun x => |x|^q) μ := by
  apply (integrable_const (B^q)).mono' (by fun_prop)
  filter_upwards [hB] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact Real.rpow_le_rpow (abs_nonneg _) hx hq

lemma bounded_abs_shift_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (B q a : ℝ) (hB : ∀ᵐ x ∂μ, |x| ≤ B) (hq : 0 ≤ q) :
    Integrable (fun x => |a+x|^q) μ := by
  apply (integrable_const ((|a|+B)^q)).mono' (by fun_prop)
  filter_upwards [hB] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact Real.rpow_le_rpow (abs_nonneg _) ((abs_add_le _ _).trans (add_le_add_right hx _)) hq

lemma symmetric_integral (μ : Measure ℝ) (hs : μ.map (fun x => -x) = μ)
    (f : ℝ → ℝ) (hf : AEStronglyMeasurable f μ) :
    (∫ x, f (-x) ∂μ) = ∫ x, f x ∂μ := by
  have hh := integral_map (μ := μ) (φ := fun x : ℝ => -x) (by fun_prop)
    (f := f) (by rwa [hs])
  simpa only [hs] using hh.symm

lemma bounded_moment_interpolation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (B q : ℝ) (hq : 2 < q) (hB : ∀ᵐ x ∂μ, |x| ≤ B) :
    (∫ x, |x|^(q-2) ∂μ) ≤ (∫ x, |x|^q ∂μ)^((q-2)/q) := by
  have hq0 : 0 < q := by linarith
  have hr : 0 ≤ (q-2)/q := by positivity
  have hr1 : (q-2)/q ≤ 1 := (div_le_one hq0).mpr (by linarith)
  have he (x : ℝ) : (|x|^q)^((q-2)/q) = |x|^(q-2) := by
    rw [← Real.rpow_mul (abs_nonneg _)]
    congr 1
    field_simp
  have hi := bounded_abs_moment_integrable μ B (q-2) hB (by linarith)
  have hh := (Real.concaveOn_rpow hr hr1).le_map_integral
    (Real.continuous_rpow_const hr).continuousOn isClosed_Ici
    (ae_of_all μ (fun x => Real.rpow_nonneg (abs_nonneg x) q))
    (bounded_abs_moment_integrable μ B q hB hq0.le)
    (show Integrable ((fun x : ℝ => x^((q-2)/q)) ∘ (fun x : ℝ => |x|^q)) μ by
      simpa only [Function.comp_def, he] using hi)
  simpa only [he] using hh

lemma symmetric_conv_moment (q ε C : ℝ) (hq : 2 < q) (hC : 0 ≤ C)
    (hscalar : ∀ a b : ℝ,
      (|a+b|^q+|a-b|^q)/2 ≤ |a|^q+(1+ε)* |b|^q+C* |a|^(q-2)*b^2)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A B : ℝ) (hμ : ∀ᵐ x ∂μ, |x| ≤ A) (hν : ∀ᵐ x ∂ν, |x| ≤ B)
    (hs : ν.map (fun x => -x) = ν) :
    (∫ x, |x|^q ∂μ)+(∫ x, |x|^q ∂ν) ≤ ∫ x, |x|^q ∂(μ ∗ ν) ∧
    (∫ x, |x|^q ∂(μ ∗ ν)) ≤ (∫ x, |x|^q ∂μ)+(1+ε)*(∫ x, |x|^q ∂ν)+
      C*(∫ x, |x|^q ∂μ)^((q-2)/q)*(∫ x, x^2 ∂ν) := by
  have hq0 : 0 ≤ q := by linarith
  have hiμ := bounded_abs_moment_integrable μ A q hμ hq0
  have hiν := bounded_abs_moment_integrable ν B q hν hq0
  have hiν2 : Integrable (fun x => x^2) ν := by
    simpa only [Real.rpow_two, sq_abs] using bounded_abs_moment_integrable ν B 2 hν (by norm_num)
  have hiμr := bounded_abs_moment_integrable μ A (q-2) hμ (by linarith)
  have hic := bounded_abs_moment_integrable (μ ∗ ν) (A+B) q (bounded_conv μ ν A B hμ hν) hq0
  have hisub (a : ℝ) : Integrable (fun x => |a-x|^q) ν := by
    apply (integrable_const ((|a|+B)^q)).mono' (by fun_prop)
    filter_upwards [hν] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact Real.rpow_le_rpow (abs_nonneg _) ((abs_sub _ _).trans (add_le_add_right hx _)) hq0
  have he (a : ℝ) : (∫ x, (|a+x|^q+|a-x|^q)/2 ∂ν) = ∫ x, |a+x|^q ∂ν := by
    rw [integral_div, integral_add (bounded_abs_shift_integrable ν B q a hν hq0) (hisub a)]
    have hs' := symmetric_integral ν hs (fun x => |a+x|^q) (by fun_prop)
    simp only [← sub_eq_add_neg] at hs'
    rw [hs']; ring
  have hl (a : ℝ) : |a|^q+(∫ x, |x|^q ∂ν) ≤ ∫ x, |a+x|^q ∂ν := by
    rw [← he]
    have hh := integral_mono ((integrable_const (|a|^q)).add hiν)
      (((bounded_abs_shift_integrable ν B q a hν hq0).add (hisub a)).div_const 2)
      (fun b => symmetric_power_lower q hq.le a b)
    simpa only [Pi.add_apply, integral_add (integrable_const _) hiν, integral_const, probReal_univ, smul_eq_mul, one_mul] using hh
  have hu (a : ℝ) : (∫ x, |a+x|^q ∂ν) ≤ |a|^q+(1+ε)*(∫ x, |x|^q ∂ν)+
      C* |a|^(q-2)*(∫ x, x^2 ∂ν) := by
    rw [← he]
    have hh := integral_mono
      (((bounded_abs_shift_integrable ν B q a hν hq0).add (hisub a)).div_const 2)
      (((integrable_const (|a|^q)).add (hiν.const_mul (1+ε))).add (hiν2.const_mul (C* |a|^(q-2))))
      (hscalar a)
    simp only [Pi.add_apply] at hh
    have hi12 : Integrable (fun x => |a|^q+(1+ε)* |x|^q) ν :=
      (integrable_const (|a|^q)).add (hiν.const_mul (1+ε))
    rw [integral_add hi12 (hiν2.const_mul (C* |a|^(q-2))),
      integral_add (integrable_const (|a|^q)) (hiν.const_mul (1+ε)),
      integral_const_mul, integral_const_mul, integral_const, probReal_univ, smul_eq_mul, one_mul] at hh
    exact hh
  rw [integral_conv hic]
  have hif := (integrable_conv_iff (by fun_prop)).mp hic
  have houter : Integrable (fun a => ∫ b, |a+b|^q ∂ν) μ := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] using hif.2
  constructor
  · have hh := integral_mono (hiμ.add (integrable_const _)) houter hl
    simpa only [Pi.add_apply, integral_add hiμ (integrable_const _), integral_const, probReal_univ, smul_eq_mul, one_mul] using hh
  · have hh := integral_mono houter
      ((hiμ.add (integrable_const _)).add ((hiμr.const_mul C).mul_const _)) hu
    simp only [Pi.add_apply] at hh
    have hi12 : Integrable (fun x => |x|^q+(1+ε)*(∫ x, |x|^q ∂ν)) μ :=
      hiμ.add (integrable_const _)
    have hi3 : Integrable (fun x => C* |x|^(q-2)*(∫ x, x^2 ∂ν)) μ :=
      (hiμr.const_mul C).mul_const _
    rw [integral_add hi12 hi3,
      integral_add hiμ (integrable_const _)] at hh
    simp only [integral_mul_const, integral_const_mul,
      integral_const, probReal_univ, smul_eq_mul, one_mul] at hh
    have hi := bounded_moment_interpolation μ A q hq hμ
    have hn : 0 ≤ (∫ x, x^2 ∂ν) := integral_nonneg (fun x => sq_nonneg x)
    exact hh.trans (add_le_add_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi hC) hn) _)

lemma sublinear_absorption (r δ a b x : ℝ) (_hr0 : 0 ≤ r) (hr1 : r < 1)
    (hδ : 0 < δ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x)
    (h : x ≤ a+b*x^r) :
    x ≤ (1+δ)*a+(b*(1+δ)/δ)^(1/(1-r)) := by
  by_cases hs : x ≤ (1+δ)*a
  · exact hs.trans (le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) _))
  have hx0 : 0 < x := lt_of_le_of_lt (by positivity : 0 ≤ (1+δ)*a) (lt_of_not_ge hs)
  have hxb : x ≤ b*((1+δ)/δ)*x^r := by
    have hsmall : a < x/(1+δ) := (lt_div_iff₀ (by positivity : 0 < 1+δ)).mpr (by nlinarith)
    have hh : x*δ ≤ b*x^r*(1+δ) := by
      have hm := (mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ 1+δ))
      nlinarith
    apply (le_div_iff₀ hδ).mpr at hh
    calc x ≤ b*x^r*(1+δ)/δ := hh
         _ = _ := by ring
  have hpower : x^(1-r) ≤ b*(1+δ)/δ := by
    have hp0 : 0 < x^r := Real.rpow_pos_of_pos hx0 _
    rw [Real.rpow_sub hx0, Real.rpow_one]
    apply (div_le_iff₀ hp0).mpr
    simpa only [mul_div_assoc] using hxb
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg hx _) hpower (by positivity : 0 ≤ 1/(1-r))
  rw [← Real.rpow_mul hx, mul_one_div_cancel (by linarith : 1-r ≠ 0), Real.rpow_one] at hh
  exact hh.trans (le_add_of_nonneg_left (by positivity))

lemma near_additive_recurrence (r δ C m a : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hδ : 0 < δ) (hC : 0 ≤ C) (hm : 0 ≤ m) (ha : 0 ≤ a)
    (M : ℕ → ℝ) (hzero : M 0 = 0) (hstep : ∀ k,
      M k+m ≤ M (k+1) ∧ M (k+1) ≤ M k+(1+δ)*m+C*a*(M k)^r) (N : ℕ) :
    (N:ℝ)*m ≤ M N ∧ M N ≤ (1+δ)^2*(N:ℝ)*m+
      (C*(1+δ)/δ)^(1/(1-r))*((N:ℝ)*a)^(1/(1-r)) := by
  have hmono : Monotone M := monotone_nat_of_le_succ (fun k =>
    (le_add_of_nonneg_right hm).trans (hstep k).1)
  have hnonneg (k : ℕ) : 0 ≤ M k := by simpa only [hzero] using hmono (Nat.zero_le k)
  have hl (k : ℕ) : (k:ℝ)*m ≤ M k := by
    induction k with
    | zero => simp [hzero]
    | succ k ih =>
      have hh := (hstep k).1
      push_cast
      nlinarith
  have hu : ∀ k, k ≤ N → M k ≤ (k:ℝ)*((1+δ)*m+C*a*(M N)^r) := by
    intro k hk
    induction k with
    | zero => simp [hzero]
    | succ k ih =>
      have hkn : k ≤ N := by omega
      have hrp := Real.rpow_le_rpow (hnonneg k) (hmono hkn) hr0
      have hh := (hstep k).2
      have hmul := mul_le_mul_of_nonneg_left hrp (mul_nonneg hC ha)
      have hi := ih hkn
      push_cast
      nlinarith
  have hineq : M N ≤ ((1+δ)*(N:ℝ)*m)+(C*((N:ℝ)*a))*(M N)^r := by
    have hh := hu N le_rfl
    nlinarith
  have habs := sublinear_absorption r δ ((1+δ)*(N:ℝ)*m) (C*((N:ℝ)*a)) (M N)
    hr0 hr1 hδ (by positivity) (by positivity) (hnonneg N) hineq
  have he : C*((N:ℝ)*a)*(1+δ)/δ = (C*(1+δ)/δ)*((N:ℝ)*a) := by ring
  rw [he, Real.mul_rpow (by positivity : 0 ≤ C*(1+δ)/δ) (by positivity)] at habs
  refine ⟨hl N, ?_⟩
  convert habs using 1; ring

lemma convolutionPower_bounded (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (B : ℝ) (hB : ∀ᵐ x ∂μ, |x| ≤ B) (n : ℕ) :
    ∀ᵐ x ∂convolutionPower μ n, |x| ≤ (n:ℝ)*B := by
  induction n with
  | zero => simp [convolutionPower]
  | succ n ih =>
    have h := bounded_conv (convolutionPower μ n) μ ((n:ℝ)*B) B ih hB
    simpa only [convolutionPower, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using h

lemma convolutionPower_near_moment (q ε : ℝ) (hq : 2 < q) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ]
      (B : ℝ), (∀ᵐ x ∂μ, |x| ≤ B) → μ.map (fun x => -x) = μ → ∀ n : ℕ,
      (n:ℝ)*(∫ x, |x|^q ∂μ) ≤ ∫ x, |x|^q ∂convolutionPower μ n ∧
      (∫ x, |x|^q ∂convolutionPower μ n) ≤
        (1+ε)^2*(n:ℝ)*(∫ x, |x|^q ∂μ)+C*((n:ℝ)*(∫ x, x^2 ∂μ))^(q/2) := by
  obtain ⟨C,hC,hscalar⟩ := symmetric_power_upper q ε hq hε
  have hr0 : 0 ≤ (q-2)/q := by positivity
  have hr1 : (q-2)/q < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have he : 1/(1-(q-2)/q) = q/2 := by field_simp; ring
  refine ⟨(C*(1+ε)/ε)^(q/2), by positivity, ?_⟩
  intro μ _ B hB hs n
  let M : ℕ → ℝ := fun k => ∫ x, |x|^q ∂convolutionPower μ k
  have hz : M 0 = 0 := by simp [M, convolutionPower, Real.zero_rpow (by linarith : q ≠ 0)]
  have hstep (k : ℕ) : M k+(∫ x, |x|^q ∂μ) ≤ M (k+1) ∧
      M (k+1) ≤ M k+(1+ε)*(∫ x, |x|^q ∂μ)+C*(∫ x, x^2 ∂μ)*(M k)^((q-2)/q) := by
    have h := symmetric_conv_moment q ε C hq hC hscalar (convolutionPower μ k) μ
      ((k:ℝ)*B) B (convolutionPower_bounded μ B hB k) hB hs
    simpa only [M, convolutionPower, mul_right_comm C] using h
  have h := near_additive_recurrence ((q-2)/q) ε C (∫ x, |x|^q ∂μ)
    (∫ x, x^2 ∂μ) hr0 hr1 hε hC
    (integral_nonneg (fun x => Real.rpow_nonneg (abs_nonneg _) _))
    (integral_nonneg (fun x => sq_nonneg x)) M hz hstep n
  simpa only [he, M] using h

end SubpolynomialLp

end

end OAI
