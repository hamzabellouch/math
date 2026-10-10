import OAI.MeasureTheory.Falconer.Slicing.GaussianChartPairKernel
import OAI.MeasureTheory.Falconer.Recursion.PotentialPair

namespace OAI

/-! # Transferring original exceptional pairs to the actual Gaussian slices -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ}

theorem chart_exceptional_pair_transfer (μ : Measure (Space n)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ 1) (E : Set (Space n × Space n)) (hE : MeasurableSet E)
    {K q : ℝ} (hK : 0 ≤ K) (hq : (h:ℝ) < q) (g N : ℕ) (hg : g ≤ N)
    (hball : ∀ x : Space n, ∀ j : ℕ, j ≤ N →
      μ (ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (K*(1/(2:ℝ)^j)^q)) :
    (∫⁻ A : Fin h → Space (n+1), ((gaussianChartSliceMeasure μ A (1/(2:ℝ)^N)).prod
      (gaussianChartSliceMeasure μ A (1/(2:ℝ)^N))) E ∂gaussianRows (n+1) h) ≤
      ENNReal.ofReal ((4*gaussianPairBandConstant)^h) *
        (ENNReal.ofReal (((2:ℝ)^g)^(h:ℝ))*(μ.prod μ) E +
          ENNReal.ofReal (K*((2:ℝ)^g)^((h:ℝ)-q)*
            (1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-q))))) := by
  let r := 1/(2:ℝ)^N
  let B : Set (Space n × Space n) := {p | dist p.1 p.2 < 1/(2:ℝ)^g}
  let f : Space n × Space n → ℝ≥0∞ :=
    fun p => ENNReal.ofReal ((1/(dist p.1 p.2+r))^(h:ℝ))
  let C := ENNReal.ofReal ((4*gaussianPairBandConstant)^h)
  let D := ENNReal.ofReal (((2:ℝ)^g)^(h:ℝ))
  have hB : MeasurableSet B := measurableSet_lt (by fun_prop) measurable_const
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hmass : ∀ᵐ p : Space n × Space n ∂(μ.prod μ).restrict E,
      ‖p.1‖ ≤ 1 ∧ ‖p.2‖ ≤ 1 := by
    apply ae_restrict_of_ae
    exact (Measure.quasiMeasurePreserving_fst.ae hμ).and (Measure.quasiMeasurePreserving_snd.ae hμ)
  have hpoint : ∀ p, f p ≤ B.indicator f p+D := by
    intro p
    by_cases hp : p ∈ B
    · rw [indicator_of_mem hp]
      exact le_add_right le_rfl
    · rw [indicator_of_notMem hp,zero_add]
      have hd : 1/(2:ℝ)^g ≤ dist p.1 p.2 := le_of_not_gt hp
      apply ENNReal.ofReal_le_ofReal
      apply Real.rpow_le_rpow (by positivity) _ (Nat.cast_nonneg _)
      apply (div_le_iff₀ (by dsimp [r]; positivity : 0 < dist p.1 p.2+r)).mpr
      have hr : 0 ≤ r := by dsimp [r]; positivity
      calc
        1 = (2:ℝ)^g*(1/(2:ℝ)^g) := by field_simp
        _ ≤ (2:ℝ)^g*(dist p.1 p.2+r) := by gcongr; linarith
  rw [gaussian_chart_pair_average μ _ E hE]
  calc
    _ ≤ ∫⁻ p in E, C*f p ∂μ.prod μ := lintegral_mono_ae (by
      filter_upwards [hmass] with p hp
      exact gaussian_chart_pair_kernel hp.1 hp.2 (by positivity))
    _ = C*∫⁻ p in E, f p ∂μ.prod μ := lintegral_const_mul' C _ ENNReal.ofReal_ne_top
    _ ≤ C*(∫⁻ p in E, B.indicator f p+D ∂μ.prod μ) :=
      mul_le_mul' le_rfl (lintegral_mono hpoint)
    _ = C*((∫⁻ p in E, B.indicator f p ∂μ.prod μ)+D*(μ.prod μ) E) := by
      rw [lintegral_add_left (hf.indicator hB),lintegral_const,Measure.restrict_apply_univ]
    _ ≤ C*((∫⁻ p in B, f p ∂μ.prod μ)+D*(μ.prod μ) E) := by
      apply mul_le_mul' le_rfl
      apply add_le_add _ le_rfl
      rw [← lintegral_indicator hB]
      exact lintegral_mono' Measure.restrict_le_self le_rfl
    _ ≤ _ := by
      have hh := regularized_pair_potential μ hK (Nat.cast_nonneg _) hq g N hg (by simp) hball
      change C*((∫⁻ p in B, f p ∂μ.prod μ)+D*(μ.prod μ) E) ≤ _
      rw [add_comm]
      exact mul_le_mul' le_rfl (add_le_add le_rfl hh)

end Falconer

end OAI
