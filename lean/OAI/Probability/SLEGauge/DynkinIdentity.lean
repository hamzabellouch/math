import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.RiemannIntegrals

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
open scoped Topology
open Set
open MeasureTheory Filter
open scoped NNReal Topology
namespace ExactSLEGenerator
variable {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace Ω]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
theorem additive_brownian_dynkin (W : Measure Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : Driver) => b.1 t) W)
    (X : ℝ≥0 → Driver → E) (hXc : ∀ b, Continuous (fun t => X t b))
    (hXm : ∀ t, Measurable[rawFiltration t] (X t))
    (A : E → E) (hAc : Continuous A) (K : ℝ) (hK : 0 ≤ K) (hAb : ∀ x, ‖A x‖ ≤ K)
    (e : E) (he : ‖e‖ ≤ 1)
    (hXeq : ∀ (s h : ℝ≥0) b, X (s+h) b = X s b + increment s h b • e +
      ∫ t in (s : ℝ)..((s+h : ℝ≥0) : ℝ), A (X t.toNNReal b))
    (f : E → ℝ) (D : E → E →L[ℝ] ℝ) (hD : ∀ x, HasFDerivAt f (D x) x)
    (hDc : Continuous D)
    (C M : ℝ) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hLip : ∀ x y, ‖D y - D x‖ ≤ C * ‖y-x‖)
    (hSmooth : ∀ x, ContDiff ℝ 3 (fun w : ℝ => f (x + w • e)))
    (hThird : ∀ x w, |iteratedDeriv 3 (fun r : ℝ => f (x + r • e)) w| ≤ C)
    (hQc : Continuous (fun x => iteratedDeriv 2 (fun r : ℝ => f (x + r • e)) 0))
    (hfb : ∀ x, |f x| ≤ M) (hDb : ∀ x, ‖D x‖ ≤ M)
    (hQb : ∀ x, |iteratedDeriv 2 (fun r : ℝ => f (x + r • e)) 0| ≤ M)
    (T : ℝ≥0) :
    (∫ b, f (X T b) ∂W) - (∫ b, f (X 0 b) ∂W) =
      (1/2 : ℝ) * (∫ b, (∫ t in 0..(T : ℝ),
        iteratedDeriv 2 (fun r : ℝ => f (X t.toNNReal b + r • e)) 0) ∂W) +
      (∫ b, (∫ t in 0..(T : ℝ), D (X t.toNNReal b) (A (X t.toNNReal b))) ∂W) := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hD x).continuousAt)
  let X' : ℝ → Driver → E := fun t b => X t.toNNReal b
  have hX'c (b : Driver) : Continuous (fun t => X' t b) :=
    (hXc b).comp continuous_real_toNNReal
  have hX'm (t : ℝ) : Measurable (X' t) := (hXm t.toNNReal).mono (rawFiltration.le _) le_rfl
  have hXs (t : ℝ≥0) (b : Driver) : X' t b = X t b := by simp [X']
  let Q : E → ℝ := fun x => iteratedDeriv 2 (fun r : ℝ => f (x + r • e)) 0
  have hZc : Continuous (fun x => D x e) := hDc.clm_apply continuous_const
  have hZi (t : ℝ) : Integrable (fun b => D (X' t b) e) W := by
    apply Integrable.of_bound (hZc.measurable.comp (hX'm t)).aestronglyMeasurable M
    refine ae_of_all W (fun b => ?_)
    calc
      _ ≤ ‖D (X' t b)‖ * ‖e‖ := (D _).le_opNorm _
      _ ≤ M * 1 := mul_le_mul (hDb _) he (norm_nonneg _) hM
      _ = M := mul_one _
  have hVm (u v : ℝ) : AEStronglyMeasurable
      (fun b => D (X' u b) (∫ t in u..v, A (X' t b))) W := by
    have hd : AEStronglyMeasurable (fun b => D (X' u b)) W :=
      hDc.comp_aestronglyMeasurable (hX'm u).aestronglyMeasurable
    have hi : StronglyMeasurable (fun b => ∫ t in u..v, A (X' t b)) :=
      stronglyMeasurable_intervalIntegral_of_continuous (fun t b => A (X' t b))
        (fun b => hAc.comp (hX'c b)) (fun t => hAc.measurable.comp (hX'm t)) u v
    exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hd.prodMk hi.aestronglyMeasurable)
  have hTaylor (s h : ℝ≥0) (b : Driver) :
      |f (X' ((s+h : ℝ≥0) : ℝ) b) - f (X' s b) - D (X' s b) e * increment s h b -
        Q (X' s b) * increment s h b ^ 2 / 2 -
          D (X' s b) (∫ t in (s : ℝ)..((s+h : ℝ≥0) : ℝ), A (X' t b))| ≤
      C * (K*h*(|increment s h b|+K*h)+|increment s h b|^3) := by
    have hv : ‖∫ t in (s : ℝ)..((s+h : ℝ≥0) : ℝ), A (X' t b)‖ ≤ K * (h : ℝ) := by
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (s : ℝ)) (b := ((s+h : ℝ≥0) : ℝ)) (fun t ht => hAb (X' t b))
      simpa only [NNReal.coe_add, add_sub_cancel_left, abs_of_nonneg h.coe_nonneg] using hb
    have ht := mixed_taylor_remainder f D hD e he C hC hLip hSmooth hThird (X s b)
      (∫ t in (s : ℝ)..((s+h : ℝ≥0) : ℝ), A (X' t b)) (increment s h b)
    rw [← hXeq s h b] at ht
    simp only [hXs]
    change |f (X (s+h) b) - f (X s b) - D (X s b) e * increment s h b -
      Q (X s b) * increment s h b ^ 2 / 2 - D (X s b) (∫ t in (s : ℝ)..((s+h : ℝ≥0) : ℝ), A (X' t b))| ≤ _ at ht
    have hs : |increment s h b| + ‖∫ t in (s : ℝ)..((s+h : ℝ≥0) : ℝ), A (X' t b)‖ ≤
        |increment s h b| + K*(h : ℝ) := by linarith
    have hm := mul_le_mul hv hs
      (add_nonneg (abs_nonneg (increment s h b)) (norm_nonneg _))
      (mul_nonneg hK h.coe_nonneg)
    exact ht.trans (mul_le_mul_of_nonneg_left (add_le_add hm (le_refl _)) hC)
  have hg := dynkin_of_mixed_taylor W hW 0
    (fun t b => f (X' t b)) (fun t b => D (X' t b) e) (fun t b => Q (X' t b))
    (fun t b => D (X' t b)) (fun t b => A (X' t b))
    (fun t => Integrable.of_bound (hfc.measurable.comp (hX'm t)).aestronglyMeasurable M
      (ae_of_all W (fun b => by simpa only [Real.norm_eq_abs] using hfb (X' t b))))
    (fun t => by
      have ht : rawFiltration (0+t) = rawFiltration t := congrArg rawFiltration (zero_add t)
      rw [ht]
      simpa only [hXs, Function.comp_def] using hZc.measurable.comp (hXm t))
    (fun t => by
      have ht : rawFiltration (0+t) = rawFiltration t := congrArg rawFiltration (zero_add t)
      rw [ht]
      simpa only [hXs, Function.comp_def, Q] using hQc.measurable.comp (hXm t))
    (fun t => hZi t) (fun b => hQc.comp (hX'c b))
    (fun t => (hQc.measurable.comp (hX'm t)).aestronglyMeasurable)
    (fun b => hDc.comp (hX'c b)) (fun b => hAc.comp (hX'c b)) hVm C M K hC hM hK
    (fun b t => hQb _) (fun b t => hDb _) (fun b t => hAb _)
    (fun s h b => by simpa only [NNReal.coe_add, zero_add] using hTaylor s h b) T
  simpa only [hXs, X', Q, Real.toNNReal_zero] using hg

end ExactSLEGenerator

namespace ExactSLEGenerator
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 

theorem weighted_dynkin_of_mixed_taylor (W : Measure Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : Driver) => b.1 t) W)
    (start : ℝ≥0) (F Z Y : ℝ → Driver → ℝ) (D : ℝ → Driver → E →L[ℝ] ℝ) (A : ℝ → Driver → E)
    (hF : ∀ t : ℝ≥0, Integrable (F t) W)
    (hZm : ∀ t : ℝ≥0, Measurable[rawFiltration (start+t)] (Z t))
    (hYm : ∀ t : ℝ≥0, Measurable[rawFiltration (start+t)] (Y t))
    (hZi : ∀ t : ℝ≥0, Integrable (Z t) W)
    (hYc : ∀ b, Continuous (fun t => Y t b))
    (hYm' : ∀ t, AEStronglyMeasurable (Y t) W)
    (hDc : ∀ b, Continuous (fun t => D t b))
    (hAc : ∀ b, Continuous (fun t => A t b))
    (hVm : ∀ u v, AEStronglyMeasurable (fun b => D u b (∫ t in u..v, A t b)) W)
    (C M K : ℝ) (hC : 0 ≤ C) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hYb : ∀ b t, |Y t b| ≤ M) (hDb : ∀ b t, ‖D t b‖ ≤ M)
    (hAb : ∀ b t, ‖A t b‖ ≤ K)
    (hTaylor : ∀ (s h : ℝ≥0) b,
      |F (s+h) b - F s b - Z s b * increment (start+s) h b -
        Y s b * increment (start+s) h b ^ 2 / 2 - D s b (∫ t in (s : ℝ)..(s+h : ℝ≥0), A t b)| ≤
      C * (K * h * (|increment (start+s) h b| + K * h) + |increment (start+s) h b| ^ 3))
    (J : Driver → ℝ) (hJm : Measurable[rawFiltration start] J) (hJb : ∀ b, |J b| ≤ 1)
    (T : ℝ≥0) :
    (∫ b, J b * F T b ∂W) - (∫ b, J b * F 0 b ∂W) =
      (1/2 : ℝ) * (∫ b, J b * (∫ t in 0..(T : ℝ), Y t b) ∂W) +
      (∫ b, J b * (∫ t in 0..(T : ℝ), D t b (A t b)) ∂W) := by
  have hJ : AEStronglyMeasurable J W := (hJm.mono (rawFiltration.le _) le_rfl).aestronglyMeasurable
  have hJbound : ∀ᵐ b ∂W, ‖J b‖ ≤ 1 := ae_of_all W (fun b => by simpa using hJb b)
  have hJmt (t : ℝ≥0) : Measurable[rawFiltration (start+t)] J :=
    hJm.mono (rawFiltration.mono (le_self_add)) le_rfl
  have h := dynkin_of_mixed_taylor W hW start
    (fun t b => J b * F t b) (fun t b => J b * Z t b) (fun t b => J b * Y t b)
    (fun t b => J b • D t b) A
    (fun t => (hF t).bdd_mul hJ hJbound)
    (fun t => (hJmt t).mul (hZm t)) (fun t => (hJmt t).mul (hYm t))
    (fun t => (hZi t).bdd_mul hJ hJbound)
    (fun b => continuous_const.mul (hYc b))
    (fun t => hJ.mul (hYm' t))
    (fun b => (continuous_const : Continuous (fun _ : ℝ => J b)).smul (hDc b)) hAc
    (fun u v => hJ.mul (hVm u v))
    C M K hC hM hK
    (fun b t => by
      rw [abs_mul]
      exact (mul_le_mul (hJb b) (hYb b t) (abs_nonneg _) (by norm_num)).trans (by simp))
    (fun b t => by
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul (hJb b) (hDb b t) (norm_nonneg _) (by norm_num)).trans (by simp))
    hAb
    (fun s h b => by
      simp only [smul_apply, smul_eq_mul]
      have he : J b * F (s+h) b - J b * F s b - J b * Z s b * increment (start+s) h b -
          J b * Y s b * increment (start+s) h b ^ 2 / 2 -
          J b * D s b (∫ t in (s : ℝ)..(s+h : ℝ≥0), A t b) =
          J b * (F (s+h) b - F s b - Z s b * increment (start+s) h b -
          Y s b * increment (start+s) h b ^ 2 / 2 - D s b (∫ t in (s : ℝ)..(s+h : ℝ≥0), A t b)) := by ring
      rw [he, abs_mul]
      exact (mul_le_mul_of_nonneg_right (hJb b) (abs_nonneg _)).trans (by simpa only [one_mul] using hTaylor s h b)) T
  simpa only [smul_apply, smul_eq_mul, intervalIntegral.integral_const_mul] using h

end ExactSLEGenerator

namespace ExactSLEGenerator
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

 
theorem additive_brownian_weighted_dynkin (W : Measure Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : Driver) => b.1 t) W)
    (start : ℝ≥0) (X : ℝ≥0 → Driver → E) (hXc : ∀ b, Continuous (fun t => X t b))
    (hXm : ∀ t, Measurable[rawFiltration (start+t)] (X t))
    (A : E → E) (hAc : Continuous A) (K : ℝ) (hK : 0 ≤ K) (hAb : ∀ x, ‖A x‖ ≤ K)
    (e : E) (he : ‖e‖ ≤ 1)
    (hXeq : ∀ (s h : ℝ≥0) b, X (s+h) b = X s b + increment (start+s) h b • e +
      ∫ t in (s : ℝ)..((s+h : ℝ≥0) : ℝ), A (X t.toNNReal b))
    (f : E → ℝ) (D : E → E →L[ℝ] ℝ) (hD : ∀ x, HasFDerivAt f (D x) x)
    (hDc : Continuous D)
    (C M : ℝ) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hLip : ∀ x y, ‖D y - D x‖ ≤ C * ‖y-x‖)
    (hSmooth : ∀ x, ContDiff ℝ 3 (fun w : ℝ => f (x + w • e)))
    (hThird : ∀ x w, |iteratedDeriv 3 (fun r : ℝ => f (x + r • e)) w| ≤ C)
    (hQc : Continuous (fun x => iteratedDeriv 2 (fun r : ℝ => f (x + r • e)) 0))
    (hfb : ∀ x, |f x| ≤ M) (hDb : ∀ x, ‖D x‖ ≤ M)
    (hQb : ∀ x, |iteratedDeriv 2 (fun r : ℝ => f (x + r • e)) 0| ≤ M)
    (J : Driver → ℝ) (hJm : Measurable[rawFiltration start] J) (hJb : ∀ b, |J b| ≤ 1)
    (T : ℝ≥0) :
    (∫ b, J b * f (X T b) ∂W) - (∫ b, J b * f (X 0 b) ∂W) =
      (1/2 : ℝ) * (∫ b, J b * (∫ t in 0..(T : ℝ),
        iteratedDeriv 2 (fun r : ℝ => f (X t.toNNReal b + r • e)) 0) ∂W) +
      (∫ b, J b * (∫ t in 0..(T : ℝ), D (X t.toNNReal b) (A (X t.toNNReal b))) ∂W) := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hD x).continuousAt)
  let X' : ℝ → Driver → E := fun t b => X t.toNNReal b
  have hX'c (b : Driver) : Continuous (fun t => X' t b) :=
    (hXc b).comp continuous_real_toNNReal
  have hX'm (t : ℝ) : Measurable (X' t) := (hXm t.toNNReal).mono (rawFiltration.le _) le_rfl
  have hXs (t : ℝ≥0) (b : Driver) : X' t b = X t b := by simp [X']
  let Q : E → ℝ := fun x => iteratedDeriv 2 (fun r : ℝ => f (x + r • e)) 0
  have hZc : Continuous (fun x => D x e) := hDc.clm_apply continuous_const
  have hZi (t : ℝ) : Integrable (fun b => D (X' t b) e) W := by
    apply Integrable.of_bound (hZc.measurable.comp (hX'm t)).aestronglyMeasurable M
    refine ae_of_all W (fun b => ?_)
    calc
      _ ≤ ‖D (X' t b)‖ * ‖e‖ := (D _).le_opNorm _
      _ ≤ M * 1 := mul_le_mul (hDb _) he (norm_nonneg _) hM
      _ = M := mul_one _
  have hVm (u v : ℝ) : AEStronglyMeasurable
      (fun b => D (X' u b) (∫ t in u..v, A (X' t b))) W := by
    have hd : AEStronglyMeasurable (fun b => D (X' u b)) W :=
      hDc.comp_aestronglyMeasurable (hX'm u).aestronglyMeasurable
    have hi : StronglyMeasurable (fun b => ∫ t in u..v, A (X' t b)) :=
      stronglyMeasurable_intervalIntegral_of_continuous (fun t b => A (X' t b))
        (fun b => hAc.comp (hX'c b)) (fun t => hAc.measurable.comp (hX'm t)) u v
    exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hd.prodMk hi.aestronglyMeasurable)
  have hTaylor (s h : ℝ≥0) (b : Driver) :
      |f (X' ((s+h : ℝ≥0) : ℝ) b) - f (X' s b) - D (X' s b) e * increment (start+s) h b -
        Q (X' s b) * increment (start+s) h b ^ 2 / 2 -
          D (X' s b) (∫ t in (s : ℝ)..((s+h : ℝ≥0) : ℝ), A (X' t b))| ≤
      C * (K*h*(|increment (start+s) h b|+K*h)+|increment (start+s) h b|^3) := by
    have hv : ‖∫ t in (s : ℝ)..((s+h : ℝ≥0) : ℝ), A (X' t b)‖ ≤ K * (h : ℝ) := by
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (s : ℝ)) (b := ((s+h : ℝ≥0) : ℝ)) (fun t ht => hAb (X' t b))
      simpa only [NNReal.coe_add, add_sub_cancel_left, abs_of_nonneg h.coe_nonneg] using hb
    have ht := mixed_taylor_remainder f D hD e he C hC hLip hSmooth hThird (X s b)
      (∫ t in (s : ℝ)..((s+h : ℝ≥0) : ℝ), A (X' t b)) (increment (start+s) h b)
    rw [← hXeq s h b] at ht
    simp only [hXs]
    change |f (X (s+h) b) - f (X s b) - D (X s b) e * increment (start+s) h b -
      Q (X s b) * increment (start+s) h b ^ 2 / 2 - D (X s b) (∫ t in (s : ℝ)..((s+h : ℝ≥0) : ℝ), A (X' t b))| ≤ _ at ht
    have hs : |increment (start+s) h b| + ‖∫ t in (s : ℝ)..((s+h : ℝ≥0) : ℝ), A (X' t b)‖ ≤
        |increment (start+s) h b| + K*(h : ℝ) := by linarith
    have hm := mul_le_mul hv hs
      (add_nonneg (abs_nonneg (increment (start+s) h b)) (norm_nonneg _))
      (mul_nonneg hK h.coe_nonneg)
    exact ht.trans (mul_le_mul_of_nonneg_left (add_le_add hm (le_refl _)) hC)
  have hg := weighted_dynkin_of_mixed_taylor W hW start
    (fun t b => f (X' t b)) (fun t b => D (X' t b) e) (fun t b => Q (X' t b))
    (fun t b => D (X' t b)) (fun t b => A (X' t b))
    (fun t => Integrable.of_bound (hfc.measurable.comp (hX'm t)).aestronglyMeasurable M
      (ae_of_all W (fun b => by simpa only [Real.norm_eq_abs] using hfb (X' t b))))
    (fun t => by
      simpa only [hXs, Function.comp_def] using hZc.measurable.comp (hXm t))
    (fun t => by
      simpa only [hXs, Function.comp_def, Q] using hQc.measurable.comp (hXm t))
    (fun t => hZi t) (fun b => hQc.comp (hX'c b))
    (fun t => (hQc.measurable.comp (hX'm t)).aestronglyMeasurable)
    (fun b => hDc.comp (hX'c b)) (fun b => hAc.comp (hX'c b)) hVm C M K hC hM hK
    (fun b t => hQb _) (fun b t => hDb _) (fun b t => hAb _)
    (fun s h b => by simpa only [NNReal.coe_add] using hTaylor s h b) J hJm hJb T
  simpa only [hXs, X', Q, Real.toNNReal_zero] using hg

end ExactSLEGenerator
 

open MeasureTheory Filter Set Metric Function ODE
open scoped NNReal Topology
namespace ExactSLEFlow
variable {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

omit [CompleteSpace E] in
lemma stronglyMeasurable_intervalIntegral_of_continuous
    (A : ℝ → Ω → E) (hc : ∀ b, Continuous (fun t => A t b))
    (hm : ∀ t, Measurable (A t)) (u v : ℝ) :
    StronglyMeasurable (fun b => ∫ t in u..v, A t b) := by
  have hj : StronglyMeasurable (Function.uncurry A) :=
    (measurable_uncurry_of_continuous_of_measurable hc hm).stronglyMeasurable
  by_cases huv : u ≤ v
  · simp_rw [intervalIntegral.integral_of_le huv]
    exact hj.integral_prod_left
  · simp_rw [intervalIntegral.integral_of_ge (le_of_not_ge huv)]
    exact hj.integral_prod_left.neg

omit [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
lemma bounded_forcing_picard (A : E → E) (L K : ℝ≥0) (hA : LipschitzWith K A)
    (hb : ∀ x, ‖A x‖ ≤ L) (u : ℝ → E) (hu : Continuous u) (x : E) (T : ℝ≥0) :
    IsPicardLindelof (fun t y => A (y + u t))
      (⟨0, by simp⟩ : Icc (0 : ℝ) T) x (L*T) 0 L K := by
  constructor
  · intro t ht
    simpa only [mul_one, Function.comp_def, NNReal.coe_mul] using
      (hA.comp (isometry_add_right (u t)).lipschitzWith).lipschitzOnWith
        (s := closedBall x (L*T))
  · intro y hy
    exact (hA.continuous.comp (continuous_const.add hu)).continuousOn
  · intro t ht y hy
    exact hb _
  · simp

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma picard_iterates_tendsto {f : ℝ → E → E} {tmin tmax : ℝ}
    {t₀ : Icc tmin tmax} {x : E} {a L K : ℝ≥0}
    (hf : IsPicardLindelof f t₀ x a 0 L K)
    (α : ODE.FunSpace t₀ x 0 L)
    (hα : IsFixedPt (ODE.FunSpace.next hf (mem_closedBall_self (by simp))) α)
    (β : ODE.FunSpace t₀ x 0 L) (t : ℝ) :
    Tendsto (fun n : ℕ => ((ODE.FunSpace.next hf (mem_closedBall_self (by simp)))^[n] β).compProj t)
      atTop (𝓝 (α.compProj t)) := by
  let t' : Icc tmin tmax := projIcc tmin tmax (le_trans t₀.2.1 t₀.2.2) t
  rw [tendsto_iff_dist_tendsto_zero]
  have hb (n : ℕ) := ODE.FunSpace.dist_iterate_next_apply_le hf
    (mem_closedBall_self (by simp)) β α n t'
  have he : ∀ n : ℕ, ((ODE.FunSpace.next hf (mem_closedBall_self (by simp)))^[n] α) = α :=
    fun n => hα.iterate n
  simp only [he] at hb
  have ht := (FloorSemiring.tendsto_pow_div_factorial_atTop
    ((K : ℝ) * |(t' : ℝ) - (t₀ : ℝ)|)).mul_const (dist β α)
  simp only [zero_mul] at ht
  exact squeeze_zero (fun n => dist_nonneg)
    (fun n => hb n) ht

 

theorem measurable_additive_flow_on_interval
    (A : E → E) (L K : ℝ≥0) (hA : LipschitzWith K A) (hb : ∀ x, ‖A x‖ ≤ L)
    (u : ℝ → Ω → E) (huc : ∀ ω, Continuous (fun t => u t ω))
    (hum : ∀ t, Measurable (u t)) (x : Ω → E) (hxm : Measurable x) (T : ℝ≥0) :
    ∃ Y : ℝ → Ω → E,
      (∀ ω, Continuous (fun t => Y t ω)) ∧
      (∀ t, Measurable (Y t)) ∧
      (∀ ω t, t ∈ Icc (0 : ℝ) T →
        Y t ω = x ω + ∫ v in 0..t, A (Y v ω + u v ω)) ∧
      (∀ ω t, t ∈ Icc (0 : ℝ) T →
        HasDerivWithinAt (fun v => Y v ω) (A (Y t ω + u t ω)) (Icc (0 : ℝ) T) t) := by
  let t₀ : Icc (0 : ℝ) T := ⟨0, by simp⟩
  have hf (ω : Ω) : IsPicardLindelof (fun t y => A (y + u t ω))
      t₀ (x ω) (L*T) 0 L K := bounded_forcing_picard A L K hA hb _ (huc ω) _ _
  have hfix (ω : Ω) := ODE.FunSpace.exists_isFixedPt_next (hf ω)
    (mem_closedBall_self (by simp) : x ω ∈ closedBall (x ω) (0 : ℝ))
  choose α hα using hfix
  let Y : ℝ → Ω → E := fun t ω => (α ω).compProj t
  let β : (ω : Ω) → ODE.FunSpace t₀ (x ω) 0 L := fun ω => default
  let N (ω : Ω) := ODE.FunSpace.next (hf ω)
    (mem_closedBall_self (by simp) : x ω ∈ closedBall (x ω) (0 : ℝ))
  have hm (n : ℕ) (t : ℝ) : Measurable (fun ω => ((N ω)^[n] (β ω)).compProj t) := by
    induction n generalizing t with
    | zero => change Measurable x; exact hxm
    | succ n ih =>
      have hc (ω : Ω) : Continuous (fun v => A (((N ω)^[n] (β ω)).compProj v + u v ω)) :=
        hA.continuous.comp ((ODE.FunSpace.continuous_compProj _).add (huc ω))
      have hi := stronglyMeasurable_intervalIntegral_of_continuous
        (fun v ω => A (((N ω)^[n] (β ω)).compProj v + u v ω)) hc
        (fun v => hA.continuous.measurable.comp ((ih v).add (hum v)))
        0 (projIcc (0 : ℝ) T T.coe_nonneg t)
      simp only [iterate_succ_apply']
      change Measurable (fun ω => x ω + ∫ v in (0 : ℝ)..
        (projIcc (0 : ℝ) T T.coe_nonneg t : ℝ),
          A (((N ω)^[n] (β ω)).compProj v + u v ω))
      exact hxm.add hi.measurable
  refine ⟨Y, fun ω => (α ω).continuous_compProj, fun t => ?_, ?_, ?_⟩
  · exact measurable_of_tendsto_metrizable (fun n => hm n t)
      (tendsto_pi_nhds.mpr (fun ω => picard_iterates_tendsto (hf ω) (α ω) (hα ω) (β ω) t))
  · intro ω t ht
    have he := (ODE.FunSpace.isFixedPt_next_iff (hf ω)
      (mem_closedBall_self (by simp))).mp (hα ω) ⟨t, ht⟩
    change (α ω).compProj t = x ω + ∫ v in 0..t, A ((α ω).compProj v + u v ω)
    rw [ODE.FunSpace.compProj_of_mem ht]
    exact he
  · intro ω t ht
    apply ODE.hasDerivWithinAt_picard_Icc t₀.2 (hf ω).continuousOn_uncurry
      (α ω).continuous_compProj.continuousOn
      (fun _ _ => (α ω).compProj_mem_closedBall (hf ω).mul_max_le) (x ω) ht |>.congr_of_mem _ ht
    intro v hv
    change (α ω).compProj v = _
    nth_rw 1 [← hα ω]
    rw [ODE.FunSpace.compProj_of_mem hv]
    rfl

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma additive_flow_unique {A : E → E} {K : ℝ≥0} (hA : LipschitzWith K A)
    {u : ℝ → E} {f g : ℝ → E} {T : ℝ≥0}
    (hfc : ContinuousOn f (Icc 0 (T : ℝ))) (hgc : ContinuousOn g (Icc 0 (T : ℝ)))
    (hfd : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt f (A (f t + u t)) (Icc 0 (T : ℝ)) t)
    (hgd : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt g (A (g t + u t)) (Icc 0 (T : ℝ)) t)
    (hinit : f 0 = g 0) : EqOn f g (Icc 0 (T : ℝ)) := by
  apply ODE_solution_unique (K := K) (v := fun t y => A (y + u t))
    (fun t => by simpa only [mul_one, Function.comp_def] using hA.comp (isometry_add_right (u t)).lipschitzWith)
    hfc (fun t ht => (hfd t (mem_Icc_of_Ico ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht))
    hgc (fun t ht => (hgd t (mem_Icc_of_Ico ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)) hinit

 

theorem measurable_additive_flow
    (A : E → E) (L K : ℝ≥0) (hA : LipschitzWith K A) (hb : ∀ x, ‖A x‖ ≤ L)
    (u : ℝ≥0 → Ω → E) (huc : ∀ ω, Continuous (fun t => u t ω))
    (hum : ∀ t, Measurable (u t)) (x : Ω → E) (hxm : Measurable x) :
    ∃ Y : ℝ≥0 → Ω → E,
      (∀ ω, Continuous (fun t => Y t ω)) ∧
      (∀ t, Measurable (Y t)) ∧
      (∀ ω t, Y t ω = x ω + ∫ v in (0 : ℝ)..(t : ℝ),
        A (Y v.toNNReal ω + u v.toNNReal ω)) := by
  have hex (T : ℝ≥0) := measurable_additive_flow_on_interval A L K hA hb
    (fun t ω => u t.toNNReal ω) (fun ω => (huc ω).comp continuous_real_toNNReal)
    (fun t => hum _) x hxm T
  choose F hFc hFm hFe hFd using hex
  have hF0 (T : ℝ≥0) (ω : Ω) : F T 0 ω = x ω := by
    simpa using hFe T ω 0 (by simp)
  have hcompat {S T : ℝ≥0} (hST : S ≤ T) (ω : Ω) (v : ℝ) (hv : v ∈ Icc 0 (S : ℝ)) :
      F S v ω = F T v ω := by
    have hsub : Icc (0 : ℝ) S ⊆ Icc (0 : ℝ) T := Icc_subset_Icc_right hST
    apply additive_flow_unique hA (hFc S ω).continuousOn (hFc T ω).continuousOn
      (hFd S ω) (fun t ht => (hFd T ω t (hsub ht)).mono hsub)
      (by rw [hF0, hF0]) hv
  let Y : ℝ≥0 → Ω → E := fun t ω => F t t ω
  have hYF {T t : ℝ≥0} (ht : t ≤ T) (ω : Ω) : Y t ω = F T t ω :=
    hcompat ht ω t (by simp)
  refine ⟨Y, ?_, fun t => hFm t t, ?_⟩
  · intro ω
    apply continuous_iff_continuousAt.mpr
    intro t
    have hc : ContinuousAt (fun v : ℝ≥0 => F (t+1) v ω) t :=
      ((hFc (t+1) ω).comp continuous_subtype_val).continuousAt
    apply hc.congr
    filter_upwards [eventually_lt_nhds (show t < t+1 by simp)] with v hv
    exact (hYF hv.le ω).symm
  · intro ω t
    rw [hYF le_rfl ω, hFe t ω t (by simp)]
    congr 1
    apply intervalIntegral.integral_congr
    intro v hv
    have hv' : v ∈ Icc (0 : ℝ) t := by simpa [uIcc_of_le t.coe_nonneg] using hv
    have hvt : v.toNNReal ≤ t := (Real.toNNReal_le_toNNReal hv'.2).trans_eq (by simp)
    dsimp only
    rw [hYF hvt ω, Real.coe_toNNReal _ hv'.1]

end ExactSLEFlow
end

end OAI
