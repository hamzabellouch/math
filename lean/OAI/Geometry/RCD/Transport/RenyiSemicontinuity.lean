import OAI.Geometry.RCD.Transport.RenyiDualIntegral

namespace OAI

/-! # Weak upper semicontinuity of the finite-volume Rényi integral

The dual formula includes measures with singular parts. The logarithmic
test is sent to positive infinity on the singular support and clipped on
its complement, so that no absolute continuity of a weak limit is assumed.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
theorem renyiDualValue_nonneg (μ ν : Measure X) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (f : X → ℝ) :
    0 ≤ renyiDualValue μ ν q f := by
  unfold renyiDualValue
  exact add_nonneg (mul_nonneg hq0 (integral_nonneg fun _ => (Real.exp_pos _).le))
    (mul_nonneg (sub_nonneg.mpr hq1) (integral_nonneg fun _ => (Real.exp_pos _).le))

omit [BorelSpace X] in
theorem renyiDual_ne_top (μ ν : Measure X) (q : ℝ) : renyiDual μ ν q ≠ ∞ := by
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iInf_le _ (0 : X →ᵇ ℝ))

theorem renyiDual_le_measurable [ProperSpace X] [SeparableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {f : X → ℝ} (hf : Measurable f) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |f x| ≤ M) :
    (renyiDual μ ν q).toReal ≤ renyiDualValue μ ν q f := by
  apply renyiDualValue_measurable_ge μ ν hq0 hq1 hf hM hb
  intro g
  have h := (ENNReal.toReal_le_toReal (renyiDual_ne_top μ ν q)
    ENNReal.ofReal_ne_top).mpr (iInf_le (fun g : X →ᵇ ℝ =>
      ENNReal.ofReal (renyiDualValue μ ν q g)) g)
  simpa only [ENNReal.toReal_ofReal (renyiDualValue_nonneg μ ν hq0 hq1 g)] using h

theorem renyiDual_eq_power [ProperSpace X] [SeparableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    renyiDual μ ν q = ENNReal.ofReal (∫ x, (ν.rnDeriv μ x).toReal^q ∂μ) := by
  classical
  apply le_antisymm _ (renyiPower_le_dual μ ν hq0 hq1)
  let ρ := fun x => (ν.rnDeriv μ x).toReal
  let ξ := ν.singularPart μ
  let : IsFiniteMeasure ξ := isFiniteMeasure_of_le ν (Measure.singularPart_le ν μ)
  have hρ : Measurable ρ := (ν.measurable_rnDeriv μ).ennreal_toReal
  obtain ⟨S,hS,hμS,hξSc⟩ := (Measure.mutuallySingular_singularPart ν μ).symm
  have hμae : ∀ᵐ x ∂μ, x ∉ S := by simpa [ae_iff] using hμS
  have hξae : ∀ᵐ x ∂ξ, x ∈ S := by
    apply ae_iff.mpr
    rw [show {x | ¬x ∈ S} = Sᶜ by ext x; rfl]
    exact hξSc
  let f : ℕ → X → ℝ := fun k x => if x ∈ S then (k:ℝ)+1 else entropyLogTest (k+1) (ρ x)
  have hfm (k : ℕ) : Measurable (f k) :=
    Measurable.ite hS measurable_const ((continuous_entropyLogTest _).measurable.comp hρ)
  have hfb (k : ℕ) (x : X) : |f k x| ≤ (k:ℝ)+1 := by
    dsimp only [f]
    split_ifs
    · rw [abs_of_nonneg (by positivity)]
    · exact entropyLogTest_abs_le (by positivity) _
  have heq (k : ℕ) : renyiDualValue μ ν q (f k) =
      (∫ x, renyiDualScore q (ρ x) (entropyLogTest (k+1) (ρ x)) ∂μ)+
        q*(ξ.real univ*Real.exp ((q-1)*((k:ℝ)+1))) := by
    rw [renyiDualValue_decomposition μ ν (hfm k) (hfb k)]
    congr 1
    · apply integral_congr_ae
      filter_upwards [hμae] with x hx
      simp only [f,ite_eq_right hx,ρ]
    · congr 1
      calc
        _ = ∫ _ : X, Real.exp ((q-1)*((k:ℝ)+1)) ∂ξ := by
          apply integral_congr_ae
          filter_upwards [hξae] with x hx
          simp only [f,ite_eq_left hx]
        _ = _ := by rw [integral_const,smul_eq_mul]
  have hs := integral_renyiDualScore_logTest_tendsto μ hρ
    (Measure.integrable_toReal_rnDeriv (μ := ν) (ν := μ))
    (fun _ => ENNReal.toReal_nonneg) hq0 hq1
  have hnat : Tendsto (fun k : ℕ => (k:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hzero : Tendsto (fun k : ℕ => Real.exp ((q-1)*((k:ℝ)+1))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (Filter.Tendsto.const_mul_atTop_of_neg (by linarith)
      (tendsto_atTop_add_const_right _ 1 hnat))
  have hlim : Tendsto (fun k => renyiDualValue μ ν q (f k)) atTop
      (𝓝 (∫ x, (ρ x)^q ∂μ)) := by
    simp_rw [heq]
    simpa only [mul_zero,add_zero] using hs.add
      (tendsto_const_nhds.mul (tendsto_const_nhds.mul hzero))
  have hle : (renyiDual μ ν q).toReal ≤ ∫ x, (ρ x)^q ∂μ :=
    ge_of_tendsto hlim (Eventually.of_forall fun k =>
      renyiDual_le_measurable μ ν hq0.le hq1.le (hfm k) (by positivity) (hfb k))
  rw [← ENNReal.ofReal_toReal (renyiDual_ne_top μ ν q)]
  exact ENNReal.ofReal_le_ofReal hle

theorem upperSemicontinuous_renyiPower [ProperSpace X] [SeparableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    UpperSemicontinuous (fun ν : ProbabilityMeasure X =>
      ENNReal.ofReal (∫ x, ((ν : Measure X).rnDeriv μ x).toReal^q ∂μ)) := by
  simpa only [renyiDual_eq_power μ _ hq0 hq1] using upperSemicontinuous_renyiDual μ q

end RegularPointCoordinates

end

end OAI
