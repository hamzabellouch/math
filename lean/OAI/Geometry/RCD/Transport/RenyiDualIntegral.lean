import OAI.Geometry.RCD.Transport.RenyiDual

namespace OAI

/-! # Dual scores and the absolutely continuous density

The singular part of a finite measure is retained explicitly. In
particular the tangent inequality does not assume absolute continuity.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
theorem integral_renyiDualScore_logTest_tendsto (μ : Measure X) [IsFiniteMeasure μ]
    {ρ : X → ℝ} (hρ : Measurable ρ) (hi : Integrable ρ μ)
    (hρ0 : ∀ x, 0 ≤ ρ x) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Tendsto (fun k : ℕ => ∫ x, renyiDualScore q (ρ x) (entropyLogTest (k+1) (ρ x)) ∂μ)
      atTop (𝓝 (∫ x, (ρ x)^q ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => 1+ρ x)
  · intro k
    have hlog : Measurable (fun x => entropyLogTest (k+1) (ρ x)) :=
      (continuous_entropyLogTest _).measurable.comp hρ
    exact (by unfold renyiDualScore; fun_prop :
      Measurable (fun x => renyiDualScore q (ρ x) (entropyLogTest (k+1) (ρ x)))).aestronglyMeasurable
  · exact (integrable_const 1).add hi
  · intro k
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (renyiDualScore_nonneg hq0.le hq1.le (hρ0 x) _)]
    exact renyiDualScore_logTest_bound hq0 hq1 (by positivity) (hρ0 x)
  · exact Eventually.of_forall fun x => renyiDualScore_logTest_tendsto hq0 hq1 (hρ0 x)

omit [MetricSpace X] [BorelSpace X] in
theorem renyiDualValue_decomposition (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {q : ℝ}
    {f : X → ℝ} (hf : Measurable f) {M : ℝ} (hb : ∀ x, |f x| ≤ M) :
    renyiDualValue μ ν q f =
      (∫ x, renyiDualScore q (ν.rnDeriv μ x).toReal (f x) ∂μ)+
        q*(∫ x, Real.exp ((q-1)*f x) ∂ν.singularPart μ) := by
  let ξ := ν.singularPart μ
  let η := μ.withDensity (ν.rnDeriv μ)
  let : IsFiniteMeasure ξ := isFiniteMeasure_of_le ν (Measure.singularPart_le ν μ)
  let : IsFiniteMeasure η := isFiniteMeasure_of_le ν (Measure.withDensity_rnDeriv_le ν μ)
  have hexp (a : ℝ) (m : Measure X) [IsFiniteMeasure m] :
      Integrable (fun x => Real.exp (a*f x)) m := by
    apply bounded_exp_integrable m (measurable_const.mul hf)
    intro x
    exact (le_abs_self _).trans ((abs_mul _ _).trans_le
      (mul_le_mul_of_nonneg_left (hb x) (abs_nonneg a)))
  have hid : Integrable (fun x => (ν.rnDeriv μ x).toReal*Real.exp ((q-1)*f x)) μ := by
    simpa only [smul_eq_mul] using
      (integrable_withDensity_iff_integrable_smul' (ν.measurable_rnDeriv μ)
        (Measure.rnDeriv_lt_top ν μ)).mp (hexp (q-1) η)
  have he : (∫ x, Real.exp ((q-1)*f x) ∂ν) =
      (∫ x, Real.exp ((q-1)*f x) ∂ξ)+
        (∫ x, (ν.rnDeriv μ x).toReal*Real.exp ((q-1)*f x) ∂μ) := by
    calc
      _ = (∫ x, Real.exp ((q-1)*f x) ∂ξ)+(∫ x, Real.exp ((q-1)*f x) ∂η) := by
        conv_lhs => rw [Measure.haveLebesgueDecomposition_add ν μ]
        exact integral_add_measure (hexp (q-1) ξ) (hexp (q-1) η)
      _ = _ := by
        rw [show (∫ x, Real.exp ((q-1)*f x) ∂η) =
          ∫ x, (ν.rnDeriv μ x).toReal*Real.exp ((q-1)*f x) ∂μ from by
            change (∫ x, Real.exp ((q-1)*f x) ∂μ.withDensity (ν.rnDeriv μ)) = _
            rw [integral_withDensity_eq_integral_toReal_smul
              (ν.measurable_rnDeriv μ) (Measure.rnDeriv_lt_top ν μ)]
            rfl]
  have hs : (∫ x, renyiDualScore q (ν.rnDeriv μ x).toReal (f x) ∂μ) =
      q*(∫ x, (ν.rnDeriv μ x).toReal*Real.exp ((q-1)*f x) ∂μ)+
        (1-q)*(∫ x, Real.exp (q*f x) ∂μ) := by
    unfold renyiDualScore
    simp_rw [mul_assoc]
    rw [integral_add (hid.const_mul q) ((hexp q μ).const_mul (1-q)),
      integral_const_mul,integral_const_mul]
  rw [hs]
  unfold renyiDualValue
  rw [he]
  ring

omit [MetricSpace X] [BorelSpace X] in
theorem renyiPower_le_dualValue (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    {f : X → ℝ} (hf : Measurable f) {M : ℝ} (hb : ∀ x, |f x| ≤ M) :
    (∫ x, (ν.rnDeriv μ x).toReal^q ∂μ) ≤ renyiDualValue μ ν q f := by
  have hpow := integrable_density_power μ _ (ν.measurable_rnDeriv μ).ennreal_toReal
    Measure.integrable_toReal_rnDeriv (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
      hq0.le hq1.le
  have hib (a : ℝ) : ∀ x, Real.exp (a*f x) ≤ Real.exp (|a| *M) := by
    intro x
    apply Real.exp_le_exp.mpr
    exact (le_abs_self _).trans ((abs_mul _ _).trans_le
      (mul_le_mul_of_nonneg_left (hb x) (abs_nonneg a)))
  have hi0 : Integrable (fun x => (ν.rnDeriv μ x).toReal*Real.exp ((q-1)*f x)) μ := by
    apply Integrable.mul_bdd (Measure.integrable_toReal_rnDeriv (μ := ν) (ν := μ))
      (by fun_prop) (c := Real.exp (|q-1| *M))
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hib (q-1) x
  have hi1 := bounded_exp_integrable μ (measurable_const.mul hf)
    (fun x => (le_abs_self _).trans ((abs_mul _ _).trans_le
      (mul_le_mul_of_nonneg_left (hb x) (abs_nonneg q))))
  have hs : Integrable (fun x => renyiDualScore q (ν.rnDeriv μ x).toReal (f x)) μ := by
    apply ((hi0.const_mul q).add (hi1.const_mul (1-q))).congr
    filter_upwards [] with x
    simp only [Pi.add_apply,Pi.mul_apply,renyiDualScore]
    ring
  have hle := integral_mono hpow hs (fun x =>
    rpow_le_renyiDualScore hq0 hq1 ENNReal.toReal_nonneg (f x))
  rw [renyiDualValue_decomposition μ ν hf hb]
  exact hle.trans (le_add_of_nonneg_right (mul_nonneg hq0.le
    (integral_nonneg fun _ => (Real.exp_pos _).le)))

theorem renyiPower_le_dual (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ENNReal.ofReal (∫ x, (ν.rnDeriv μ x).toReal^q ∂μ) ≤ renyiDual μ ν q := by
  apply le_iInf
  intro f
  exact ENNReal.ofReal_le_ofReal (renyiPower_le_dualValue μ ν hq0 hq1
    f.continuous.measurable (fun x => f.norm_coe_le_norm x))

end RegularPointCoordinates

end

end OAI
