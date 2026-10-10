import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.StoppingMeasurability

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

 
 

 

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace ExactSLEGenerator
instance : MeasurableSpace C(ℝ≥0, ℝ) := borel _
instance : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
abbrev Driver := {b : C(ℝ≥0, ℝ) // b 0 = 0}
instance : MeasurableSpace Driver := borel Driver
instance : BorelSpace Driver := ⟨rfl⟩
lemma driver_eval_measurable (t : ℝ≥0) : StronglyMeasurable (fun b : Driver => b.1 t) :=
  ((continuous_eval_const t).comp continuous_subtype_val).stronglyMeasurable
noncomputable def rawFiltration : Filtration ℝ≥0 (borel Driver) :=
  Filtration.natural (fun t (b : Driver) => b.1 t) driver_eval_measurable

def increment (s h : ℝ≥0) (b : Driver) : ℝ := b.1 (s+h) - b.1 s
lemma increment_measurable (s h : ℝ≥0) : Measurable (increment s h) :=
  (driver_eval_measurable (s+h)).measurable.sub (driver_eval_measurable s).measurable
lemma increment_law (W : Measure Driver)
    (hW : IsBrownianReal (fun t (b : Driver) => b.1 t) W) (s h : ℝ≥0) :
    HasLaw (increment s h) (gaussianReal 0 h) W := by
  exact (hW.toIsPreBrownianReal.shift s).hasLaw_eval h
lemma increment_integrable (W : Measure Driver)
    (hW : IsBrownianReal (fun t (b : Driver) => b.1 t) W) (s h : ℝ≥0) :
    Integrable (increment s h) W :=
  (increment_law W hW s h).hasGaussianLaw.integrable
lemma increment_mean (W : Measure Driver)
    (hW : IsBrownianReal (fun t (b : Driver) => b.1 t) W) (s h : ℝ≥0) :
    ∫ b, increment s h b ∂W = 0 := by
  rw [(increment_law W hW s h).integral_eq, integral_id_gaussianReal]
lemma increment_abs_moment_integrable (W : Measure Driver)
    (hW : IsBrownianReal (fun t (b : Driver) => b.1 t) W) (s h : ℝ≥0) (n : ℕ) (hn : n ≠ 0) :
    Integrable (fun b => |increment s h b| ^ n) W := by
  simpa only [Real.norm_eq_abs] using
    ((increment_law W hW s h).hasGaussianLaw.memLp (p := (n : ℝ≥0∞)) (by simp)).integrable_norm_pow hn
lemma increment_sq_integrable (W : Measure Driver)
    (hW : IsBrownianReal (fun t (b : Driver) => b.1 t) W) (s h : ℝ≥0) :
    Integrable (fun b => increment s h b ^ 2) W := by
  simpa only [sq_abs] using increment_abs_moment_integrable W hW s h 2 (by norm_num)
lemma increment_second_moment (W : Measure Driver)
    (hW : IsBrownianReal (fun t (b : Driver) => b.1 t) W) (s h : ℝ≥0) :
    ∫ b, increment s h b ^ 2 ∂W = (h : ℝ) := by
  have hg : ∫ x, x ^ 2 ∂gaussianReal 0 h = (h : ℝ) := by
    have hg := variance_fun_id_gaussianReal (μ := 0) (v := h)
    rw [variance_eq_integral (X := fun x : ℝ => x) measurable_id.aemeasurable,
      integral_id_gaussianReal] at hg
    simpa using hg
  calc
    _ = ∫ x, x ^ 2 ∂gaussianReal 0 h :=
      (increment_law W hW s h).integral_comp (measurable_id.pow_const 2).aestronglyMeasurable
    _ = _ := hg

noncomputable def absMoment (n : ℕ) : ℝ := ∫ x, |x| ^ n ∂gaussianReal 0 1
lemma absMoment_nonneg (n : ℕ) : 0 ≤ absMoment n :=
  integral_nonneg fun value => pow_nonneg (abs_nonneg value) _
lemma gaussian_abs_moment (h : ℝ≥0) (n : ℕ) :
    ∫ x, |x| ^ n ∂gaussianReal 0 h = (Real.sqrt h) ^ n * absMoment n := by
  have he : gaussianReal 0 h = (gaussianReal 0 1).map (fun x => Real.sqrt h * x) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp only [NNReal.coe_mk, mul_one]
      exact (Real.sq_sqrt h.coe_nonneg).symm
  rw [he]
  have hm : AEMeasurable (fun x : ℝ => Real.sqrt h * x) (gaussianReal 0 1) :=
    (measurable_const.mul measurable_id).aemeasurable
  have hf : AEStronglyMeasurable (fun x : ℝ => |x| ^ n)
      ((gaussianReal 0 1).map (fun x => Real.sqrt h * x)) :=
    ((measurable_id.abs).pow_const n).aestronglyMeasurable
  rw [integral_map hm hf]
  simp_rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
  rw [integral_const_mul]
  rfl
lemma increment_abs_moment (W : Measure Driver)
    (hW : IsBrownianReal (fun t (b : Driver) => b.1 t) W) (s h : ℝ≥0) (n : ℕ) :
    ∫ b, |increment s h b| ^ n ∂W = (Real.sqrt h) ^ n * absMoment n := by
  calc
    _ = ∫ x, |x| ^ n ∂gaussianReal 0 h :=
      (increment_law W hW s h).integral_comp ((measurable_id.abs).pow_const n).aestronglyMeasurable
    _ = _ := gaussian_abs_moment h n

lemma increment_indep (W : Measure Driver)
    (hW : IsBrownianReal (fun t (b : Driver) => b.1 t) W) (s h : ℝ≥0)
    {Z : Driver → ℝ} (hZ : Measurable[rawFiltration s] Z) :
    IndepFun Z (increment s h) W := by
  let fut : Driver → (ℝ≥0 → ℝ) := fun b t => b.1 (s+t) - b.1 s
  have hi : Indep (rawFiltration s) (MeasurableSpace.comap fut inferInstance) W := by
    rw [rawFiltration, Filtration.natural_eq_comap]
    exact (IndepFun_iff_Indep _ _ _).mp (hW.toIsPreBrownianReal.indepFun_shift s).symm
  apply (IndepFun_iff_Indep _ _ _).mpr
  apply indep_of_indep_of_le hi hZ.comap_le
  have hm : @Measurable Driver ℝ (MeasurableSpace.comap fut inferInstance) _
      (increment s h) := (measurable_pi_apply h).comp (comap_measurable fut)
  exact hm.comap_le

lemma increment_weighted_mean (W : Measure Driver)
    (hW : IsBrownianReal (fun t (b : Driver) => b.1 t) W) (s h : ℝ≥0)
    {Z : Driver → ℝ} (hZ : Measurable[rawFiltration s] Z) :
    ∫ b, Z b * increment s h b ∂W = 0 := by
  rw [(increment_indep W hW s h hZ).integral_fun_mul_eq_mul_integral
    ((hZ.mono (rawFiltration.le s) le_rfl).aestronglyMeasurable)
    (increment_measurable s h).aestronglyMeasurable, increment_mean W hW, mul_zero]

lemma increment_weighted_second_moment (W : Measure Driver)
    (hW : IsBrownianReal (fun t (b : Driver) => b.1 t) W) (s h : ℝ≥0)
    {Z : Driver → ℝ} (hZ : Measurable[rawFiltration s] Z) :
    ∫ b, Z b * increment s h b ^ 2 ∂W = (h : ℝ) * ∫ b, Z b ∂W := by
  have hi : IndepFun Z (fun b => increment s h b ^ 2) W :=
    (increment_indep W hW s h hZ).comp measurable_id (measurable_id.pow_const 2)
  rw [hi.integral_fun_mul_eq_mul_integral
    ((hZ.mono (rawFiltration.le s) le_rfl).aestronglyMeasurable)
    ((increment_measurable s h).pow_const 2).aestronglyMeasurable,
    increment_second_moment W hW, mul_comm]

 

theorem expected_taylor_step (W : Measure Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : Driver) => b.1 t) W)
    (s h : ℝ≥0) (F₀ F₁ Z Y V : Driver → ℝ)
    (hF₀ : Integrable F₀ W) (hF₁ : Integrable F₁ W) (hV : Integrable V W)
    (hZm : Measurable[rawFiltration s] Z) (hYm : Measurable[rawFiltration s] Y)
    (hZi : Integrable Z W) (hYi : Integrable Y W)
    (C K : ℝ) (_hC : 0 ≤ C) (_hK : 0 ≤ K)
    (hTaylor : ∀ b, |F₁ b - F₀ b - Z b * increment s h b -
        Y b * increment s h b ^ 2 / 2 - V b| ≤
      C * (K * h * (|increment s h b| + K * h) + |increment s h b| ^ 3)) :
    |(∫ b, F₁ b ∂W) - (∫ b, F₀ b ∂W) - (h : ℝ) / 2 * (∫ b, Y b ∂W) -
      (∫ b, V b ∂W)| ≤
      C * (K * h * (Real.sqrt h * absMoment 1 + K * h) + Real.sqrt h ^ 3 * absMoment 3) := by
  have hprod : Integrable (fun b => Z b * increment s h b) W :=
    (increment_indep W hW s h hZm).integrable_mul hZi (increment_integrable W hW s h)
  have hprod₂ : Integrable (fun b => Y b * increment s h b ^ 2 / 2) W := by
    apply Integrable.div_const
    exact ((increment_indep W hW s h hYm).comp measurable_id (measurable_id.pow_const 2)).integrable_mul
      hYi (increment_sq_integrable W hW s h)
  let R := fun b => F₁ b - F₀ b - Z b * increment s h b - Y b * increment s h b ^ 2 / 2 - V b
  have hRi : Integrable R W := (((hF₁.sub hF₀).sub hprod).sub hprod₂).sub hV
  have hright : Integrable (fun b => C *
      (K * h * (|increment s h b| + K * h) + |increment s h b| ^ 3)) W := by
    apply Integrable.const_mul
    apply Integrable.add
    · exact ((increment_integrable W hW s h).abs.add (integrable_const _)).const_mul _
    · exact increment_abs_moment_integrable W hW s h 3 (by norm_num)
  have he : (∫ b, R b ∂W) = (∫ b, F₁ b ∂W) - (∫ b, F₀ b ∂W) -
      (h : ℝ) / 2 * (∫ b, Y b ∂W) - (∫ b, V b ∂W) := by
    dsimp [R]
    have he₃ := integral_sub (((hF₁.sub hF₀).sub hprod).sub hprod₂) hV
    have he₂ := integral_sub ((hF₁.sub hF₀).sub hprod) hprod₂
    have he₁ := integral_sub (hF₁.sub hF₀) hprod
    simp only [Pi.sub_apply] at he₃ he₂ he₁
    rw [he₃, he₂, he₁, integral_sub hF₁ hF₀,
      increment_weighted_mean W hW s h hZm, integral_div,
      increment_weighted_second_moment W hW s h hYm]
    ring
  rw [← he]
  calc
    _ ≤ ∫ b, |R b| ∂W := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm R
    _ ≤ ∫ b, C * (K * h * (|increment s h b| + K * h) + |increment s h b| ^ 3) ∂W :=
      integral_mono hRi.abs hright hTaylor
    _ = _ := by
      have ha := integral_add
        (((increment_integrable W hW s h).abs.add (integrable_const (K * (h : ℝ)))).const_mul (K * (h : ℝ)))
        (increment_abs_moment_integrable W hW s h 3 (by norm_num))
      have hb := integral_add (increment_integrable W hW s h).abs (integrable_const (K * (h : ℝ)))
      simp only [Pi.add_apply] at ha hb
      rw [integral_const_mul, ha, integral_const_mul, hb,
        integral_const, probReal_univ, smul_eq_mul, one_mul,
        increment_abs_moment W hW s h 3]
      have habs := increment_abs_moment W hW s h 1
      simp only [pow_one] at habs
      rw [habs]

 

theorem expected_taylor_sum (W : Measure Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : Driver) => b.1 t) W)
    (start : ℝ≥0) (N : ℕ) (h : ℝ≥0) (F Z Y V : ℕ → Driver → ℝ)
    (hF : ∀ i, Integrable (F i) W) (hV : ∀ i, Integrable (V i) W)
    (hZm : ∀ i : ℕ, Measurable[rawFiltration (start + i * h)] (Z i))
    (hYm : ∀ i : ℕ, Measurable[rawFiltration (start + i * h)] (Y i))
    (hZi : ∀ i, Integrable (Z i) W) (hYi : ∀ i, Integrable (Y i) W)
    (C K : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hTaylor : ∀ i < N, ∀ b, |F (i+1) b - F i b - Z i b * increment (start+i*h) h b -
        Y i b * increment (start+i*h) h b ^ 2 / 2 - V i b| ≤
      C * (K * h * (|increment (start+i*h) h b| + K * h) + |increment (start+i*h) h b| ^ 3)) :
    |(∫ b, F N b ∂W) - (∫ b, F 0 b ∂W) -
      ∑ i ∈ Finset.range N, ((h : ℝ) / 2 * (∫ b, Y i b ∂W) + (∫ b, V i b ∂W))| ≤
      (N : ℝ) * C * h * ((K * absMoment 1 + absMoment 3) * Real.sqrt h + K ^ 2 * h) := by
  let e : ℕ → ℝ := fun i => (∫ b, F (i+1) b ∂W) - (∫ b, F i b ∂W) -
      (h : ℝ) / 2 * (∫ b, Y i b ∂W) - (∫ b, V i b ∂W)
  have he (i : ℕ) (hi : i < N) : |e i| ≤
      C * h * ((K * absMoment 1 + absMoment 3) * Real.sqrt h + K ^ 2 * h) := by
    have hs := expected_taylor_step W hW (start+i*h) h (F i) (F (i+1)) (Z i) (Y i) (V i)
      (hF i) (hF (i+1)) (hV i) (hZm i) (hYm i) (hZi i) (hYi i) C K hC hK (hTaylor i hi)
    change |e i| ≤ _ at hs
    convert hs using 1
    rw [show Real.sqrt h ^ 3 = (h : ℝ) * Real.sqrt h by rw [pow_succ, Real.sq_sqrt h.coe_nonneg]]
    ring
  have htel : ∑ i ∈ Finset.range N, e i = (∫ b, F N b ∂W) - (∫ b, F 0 b ∂W) -
      ∑ i ∈ Finset.range N, ((h : ℝ) / 2 * (∫ b, Y i b ∂W) + (∫ b, V i b ∂W)) := by
    have heq : e = fun i => ((∫ b, F (i+1) b ∂W) - (∫ b, F i b ∂W)) -
        ((h : ℝ) / 2 * (∫ b, Y i b ∂W) + (∫ b, V i b ∂W)) := by
      funext i
      dsimp [e]
      ring
    rw [heq, Finset.sum_sub_distrib, Finset.sum_range_sub (fun i => ∫ b, F i b ∂W) N]
  rw [← htel]
  calc
    _ ≤ ∑ i ∈ Finset.range N, |e i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range N,
        C * h * ((K * absMoment 1 + absMoment 3) * Real.sqrt h + K ^ 2 * h) :=
      Finset.sum_le_sum fun i hi => he i (Finset.mem_range.mp hi)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

 
lemma taylor_error_tendsto_zero (T C K : ℝ) :
    Tendsto (fun n : ℕ => C * T * ((K * absMoment 1 + absMoment 3) *
      Real.sqrt (T / (n+1 : ℕ)) + K ^ 2 * (T / (n+1 : ℕ)))) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => T / (n+1 : ℕ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat T).comp (tendsto_add_atTop_nat 1)
  have hs : Tendsto (fun n : ℕ => Real.sqrt (T / (n+1 : ℕ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp h
  simpa using ((hs.const_mul (K * absMoment 1 + absMoment 3)).add (h.const_mul (K^2))).const_mul (C*T)
end ExactSLEGenerator

 

open scoped Topology
open Set
namespace ExactSLEGenerator

lemma scalar_taylor_cubic (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f)
    (C : ℝ) (hC : ∀ x, |iteratedDeriv 3 f x| ≤ C) (w : ℝ) :
    |f w - f 0 - deriv f 0 * w - iteratedDeriv 2 f 0 * w ^ 2 / 2| ≤
      C * |w| ^ 3 := by
  by_cases hw : w = 0
  · subst w
    simp
  have hn : (0 : ℝ) ≠ w := Ne.symm hw
  obtain ⟨u, hu, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) hn hf.contDiffOn
  have hid (n : ℕ) (hnn : n ≤ 3) : iteratedDerivWithin n f (Set.uIcc 0 w) 0 =
      iteratedDeriv n f 0 := by
    rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedDeriv_eq_iteratedFDeriv]
    congr 1
    exact iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_uIcc hn)
      ((hf.of_le (by exact_mod_cast hnn)).contDiffAt) (left_mem_uIcc)
  have hp : taylorWithinEval f 2 (Set.uIcc 0 w) 0 w =
      f 0 + deriv f 0 * w + iteratedDeriv 2 f 0 * w^2/2 := by
    rw [taylorWithinEval_succ f 1 (Set.uIcc 0 w) 0 w,
      taylorWithinEval_succ f 0 (Set.uIcc 0 w) 0 w, taylor_within_zero_eval]
    rw [hid 1 (by norm_num), hid 2 (by norm_num)]
    simp only [iteratedDeriv_one, sub_zero, Nat.factorial, Nat.cast_mul, Nat.cast_one,
      zero_add, pow_one, smul_eq_mul]
    ring
  rw [hp] at he
  have hh : |f w - f 0 - deriv f 0 * w - iteratedDeriv 2 f 0 * w ^ 2 / 2| =
      |iteratedDeriv 3 f u| * |w| ^ 3 / 6 := by
    have he' : f w - f 0 - deriv f 0 * w - iteratedDeriv 2 f 0 * w ^ 2 / 2 =
        iteratedDeriv 3 f u * w ^ 3 / 6 := by
      norm_num at he
      linarith only [he]
    rw [he', abs_div, abs_mul, abs_pow]
    norm_num
  rw [hh]
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC u)
  calc
    _ ≤ C * |w| ^ 3 / 6 := by gcongr; exact hC u
    _ ≤ _ := by nlinarith [mul_nonneg hC0 (pow_nonneg (abs_nonneg w) 3)]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma first_order_remainder (f : E → ℝ) (D : E → E →L[ℝ] ℝ)
    (hD : ∀ x, HasFDerivAt f (D x) x) (C : ℝ)
    (hLip : ∀ x y, ‖D y - D x‖ ≤ C * ‖y-x‖) (x v : E) :
    |f (x+v) - f x - D x v| ≤ C * ‖v‖^2 := by
  let F := fun u => f u - D x u
  have hF : ∀ u ∈ Metric.closedBall x ‖v‖,
      HasFDerivWithinAt F (D u - D x) (Metric.closedBall x ‖v‖) u := by
    intro u hu
    exact ((hD u).sub (D x).hasFDerivAt).hasFDerivWithinAt
  have hbound : ∀ u ∈ Metric.closedBall x ‖v‖, ‖D u - D x‖ ≤ C * ‖v‖ := by
    intro u hu
    have hC : 0 ≤ C ∨ v = 0 := by
      by_cases hv : v = 0
      · exact Or.inr hv
      · left
        have hp : 0 < ‖v‖ := norm_pos_iff.mpr hv
        have ht := (norm_nonneg (D (x+v)-D x)).trans (hLip x (x+v))
        simp only [add_sub_cancel_left] at ht
        exact nonneg_of_mul_nonneg_left ht hp
    rcases hC with hC | rfl
    · exact (hLip x u).trans (mul_le_mul_of_nonneg_left (by simpa [dist_eq_norm] using hu) hC)
    · have hu' : u = x := by simpa using hu
      subst u
      simp
  have hb := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hF hbound
    (convex_closedBall x ‖v‖) (Metric.mem_closedBall_self (norm_nonneg v))
    (show x+v ∈ Metric.closedBall x ‖v‖ by simp [Metric.mem_closedBall, dist_eq_norm])
  simpa [F, map_add, Real.norm_eq_abs, pow_two, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
    mul_assoc] using hb

 

lemma mixed_taylor_remainder (f : E → ℝ) (D : E → E →L[ℝ] ℝ)
    (hD : ∀ x, HasFDerivAt f (D x) x) (e : E) (he : ‖e‖ ≤ 1)
    (C : ℝ) (hC : 0 ≤ C)
    (hLip : ∀ x y, ‖D y - D x‖ ≤ C * ‖y-x‖)
    (hSmooth : ∀ x, ContDiff ℝ 3 (fun w : ℝ => f (x + w • e)))
    (hThird : ∀ x w, |iteratedDeriv 3 (fun r : ℝ => f (x + r • e)) w| ≤ C)
    (x v : E) (w : ℝ) :
    |f (x + w • e + v) - f x - D x e * w -
      iteratedDeriv 2 (fun r : ℝ => f (x + r • e)) 0 * w^2/2 - D x v| ≤
    C * (‖v‖ * (|w| + ‖v‖) + |w|^3) := by
  have hd : deriv (fun r : ℝ => f (x + r • e)) 0 = D x e := by
    have hi := ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x
    have ho := (hD (x + (0 : ℝ) • e)).comp_hasDerivAt 0 hi
    simpa only [Function.comp_def, id_eq, zero_smul, one_smul, add_zero] using ho.deriv
  have hb := scalar_taylor_cubic (fun r : ℝ => f (x + r • e)) (hSmooth x) C
    (hThird x) w
  rw [hd] at hb
  simp only [zero_smul, add_zero] at hb
  have hv := first_order_remainder f D hD C hLip (x + w • e) v
  have hc : |(D (x+w•e)-D x) v| ≤ C * |w| * ‖v‖ := by
    calc
      _ ≤ ‖D (x+w•e)-D x‖ * ‖v‖ := by
        simpa only [Real.norm_eq_abs] using (D (x+w•e)-D x).le_opNorm v
      _ ≤ (C * ‖(x+w•e)-x‖) * ‖v‖ := by gcongr; exact hLip x (x+w•e)
      _ = (C * (|w| * ‖e‖)) * ‖v‖ := by simp [norm_smul, Real.norm_eq_abs]
      _ ≤ _ := by
        have hw := mul_le_mul_of_nonneg_left he (abs_nonneg w)
        simpa only [mul_one] using mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hw hC) (norm_nonneg v)
  have hsum := (abs_add_le (f (x+w•e+v)-f (x+w•e)-D (x+w•e) v)
    (f (x+w•e)-f x-D x e*w-
      iteratedDeriv 2 (fun r : ℝ => f (x+r•e)) 0*w^2/2)).trans (add_le_add hv hb)
  have hsum' := (abs_add_le ((f (x+w•e+v)-f (x+w•e)-D (x+w•e) v)+
    (f (x+w•e)-f x-D x e*w-
      iteratedDeriv 2 (fun r : ℝ => f (x+r•e)) 0*w^2/2)) ((D (x+w•e)-D x) v)).trans
        (add_le_add hsum hc)
  have heq : ((f (x+w•e+v)-f (x+w•e)-D (x+w•e) v)+
    (f (x+w•e)-f x-D x e*w-
      iteratedDeriv 2 (fun r : ℝ => f (x+r•e)) 0*w^2/2)) + ((D (x+w•e)-D x) v) =
      f (x+w•e+v)-f x-D x e*w-
        iteratedDeriv 2 (fun r : ℝ => f (x+r•e)) 0*w^2/2-D x v := by
    simp only [sub_apply]
    ring
  rw [heq] at hsum'
  calc
    _ ≤ (C * ‖v‖^2 + C * |w|^3) + C * |w| * ‖v‖ := hsum'
    _ = _ := by ring

end ExactSLEGenerator

 
open MeasureTheory Filter
open scoped Topology
namespace ExactSLEGenerator

lemma riemann_sum_error_le (f : ℝ → ℝ) (hf : Continuous f) (T : ℝ) (hT : 0 ≤ T)
    (N : ℕ) (hN : 0 < N) (ε : ℝ) (_hε : 0 ≤ ε)
    (hmod : ∀ u ∈ Set.Icc 0 T, ∀ v ∈ Set.Icc 0 T,
      |u-v| ≤ T / N → |f u-f v| ≤ ε) :
    |(∑ i ∈ Finset.range N, (T/N) * f (i*(T/N))) - ∫ s in 0..T, f s| ≤ ε*T := by
  let h := T / (N : ℝ)
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hh : 0 ≤ h := div_nonneg hT hNr.le
  have hNh : (N : ℝ) * h = T := by dsimp [h]; field_simp
  let G : ℕ → ℝ := fun i => ∫ s in 0..(i : ℝ)*h, f s
  have hG (i : ℕ) : ∫ s in (i : ℝ)*h..((i+1 : ℕ) : ℝ)*h, f s = G (i+1)-G i := by
    have ha := intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (μ := volume) 0 ((i : ℝ)*h))
      (hf.intervalIntegrable (μ := volume) ((i : ℝ)*h) (((i+1 : ℕ) : ℝ)*h))
    dsimp [G]
    linarith only [ha]
  have hdiff (i : ℕ) : ((i+1 : ℕ) : ℝ)*h-(i : ℝ)*h = h := by push_cast; ring
  have he (i : ℕ) (hi : i < N) : |h*f ((i : ℝ)*h) - (G (i+1)-G i)| ≤ ε*h := by
    have hai : (i : ℝ) * h ∈ Set.Icc 0 T := by
      refine ⟨mul_nonneg (Nat.cast_nonneg _) hh, ?_⟩
      rw [← hNh]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi.le) hh
    have hbi : ((i+1 : ℕ) : ℝ) * h ∈ Set.Icc 0 T := by
      refine ⟨by positivity, ?_⟩
      rw [← hNh]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hh
    have hab : (i : ℝ)*h ≤ ((i+1 : ℕ) : ℝ)*h := by linarith [hdiff i]
    have hbound : ∀ s ∈ Set.uIoc ((i : ℝ)*h) (((i+1 : ℕ) : ℝ)*h),
        ‖f ((i : ℝ)*h)-f s‖ ≤ ε := by
      intro s hs
      rw [Set.uIoc_of_le hab] at hs
      rw [Real.norm_eq_abs]
      apply hmod _ hai _ ⟨hai.1.trans hs.1.le, hs.2.trans hbi.2⟩
      rw [abs_of_nonpos (by linarith [hs.1])]
      linarith [hs.2, hdiff i]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    have hc : IntervalIntegrable (fun _ : ℝ => f ((i : ℝ)*h)) volume
        ((i : ℝ)*h) (((i+1 : ℕ) : ℝ)*h) := intervalIntegrable_const
    rw [intervalIntegral.integral_sub hc (hf.intervalIntegrable _ _),
      intervalIntegral.integral_const, smul_eq_mul, hdiff, hG, Real.norm_eq_abs,
      abs_of_nonneg hh] at hb
    exact hb
  have hs : ∑ i ∈ Finset.range N, (G (i+1)-G i) = ∫ s in 0..T, f s := by
    rw [Finset.sum_range_sub]
    simp [G, hNh]
  change |(∑ i ∈ Finset.range N, h*f ((i : ℝ)*h)) - _| ≤ _
  rw [← hs, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.range N, |h*f ((i : ℝ)*h)-(G (i+1)-G i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range N, ε*h := Finset.sum_le_sum fun i hi => he i (Finset.mem_range.mp hi)
    _ = ε*T := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; rw [← hNh]; ring

end ExactSLEGenerator
end

end OAI
