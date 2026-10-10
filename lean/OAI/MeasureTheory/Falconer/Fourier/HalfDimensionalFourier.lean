import OAI.MeasureTheory.Falconer.Shells.HalfDimensionalShell
import OAI.MeasureTheory.Falconer.Recursion.FrequencyIntervals
import OAI.MeasureTheory.Falconer.Geometry.FiniteScaleBall

namespace OAI

/-! # The half-dimensional Fourier bound at the required dyadic scales -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem radial_unit_interval_mass (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    (hmass : ν univ ≤ 1) : radialIntervalMeasure ν 1 univ ≤ 2 := by
  have hm : Measurable (@radialFrequencyMap d) := by unfold radialFrequencyMap; fun_prop
  rw [radialIntervalMeasure,Measure.map_apply hm MeasurableSet.univ,preimage_univ]
  rw [← univ_prod_univ,Measure.prod_prod,Measure.restrict_apply_univ,Real.volume_Icc]
  norm_num
  exact (mul_le_mul_right hmass 2).trans_eq (mul_one _)

theorem radial_low_fourier (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    (ν : Measure (Sphere d)) [IsFiniteMeasure ν] (hmass : ν univ ≤ 1) :
    (∫⁻ v, ENNReal.ofReal (‖PlanarFalconer.sourceFourier μ v‖^2)
      ∂radialIntervalMeasure ν 1) ≤ 2 := by
  calc
    _ ≤ ∫⁻ _v, (1:ℝ≥0∞) ∂radialIntervalMeasure ν 1 := by
      apply lintegral_mono
      intro v
      have hn : ‖PlanarFalconer.sourceFourier μ v‖ ≤ 1 := by
        simpa [PlanarFalconer.sourceFourier] using
          norm_charFun_le (μ := μ) ((-(2*Real.pi)) • v)
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hn 2
      simpa only [one_pow,ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hsq
    _ = radialIntervalMeasure ν 1 univ := by simp
    _ ≤ 2 := radial_unit_interval_mass ν hmass

theorem dyadic_half_dimensional_fourier (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    {D R K L : ℝ} (hD : 0 ≤ D) (hsupport : ∀ᵐ x ∂μ, ‖x‖ ≤ D)
    (n : ℕ) (hR : (2:ℝ)^n ≤ R) (hK : 1 ≤ K) (hL : 1 ≤ L) (hmass : ν univ ≤ 1)
    (hμ : ∀ x : Space d, ∀ r : ℝ, 1/(2:ℝ)^n ≤ r → r ≤ 1 →
      μ (ball x r) ≤ ENNReal.ofReal (K*r^((d:ℝ)/2)))
    (hν : ∀ x : Space d, ∀ r : ℝ, 1/R ≤ r → r ≤ 1 →
      ν {w : Sphere d | dist (w:Space d) x < r} ≤ ENNReal.ofReal (L*r^((d:ℝ)/2))) :
    (∫⁻ v, ENNReal.ofReal (‖PlanarFalconer.sourceFourier μ v‖^2)
      ∂radialIntervalMeasure ν ((2:ℝ)^n)) ≤
      ENNReal.ofReal (2+(n:ℝ)*(halfDimensionalShellConstant d*
        (Real.exp ((Real.pi^2/2)*D^2))^2*K*L)) := by
  let T : ℝ := halfDimensionalShellConstant d*(Real.exp ((Real.pi^2/2)*D^2))^2*K*L
  have hT : 0 ≤ T := by
    have := halfDimensionalShellConstant_nonneg d
    dsimp [T]
    positivity
  have hμ' := finite_scale_ball_extend μ (by simp) hK (show 0 ≤ (d:ℝ)/2 by positivity) hμ
  have hterm (j : ℕ) (hj : j ∈ Finset.range n) :
      (∫⁻ v, ENNReal.ofReal (‖PlanarFalconer.sourceFourier μ v‖^2)
        ∂radialFrequencyMeasure ν ((2:ℝ)^j)) ≤ ENNReal.ofReal T := by
    have hjn : j ≤ n := (Finset.mem_range.mp hj).le
    have hB : 1 ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
    have hBn : (2:ℝ)^j ≤ (2:ℝ)^n := pow_le_pow_right₀ (by norm_num) hjn
    apply half_dimensional_shell μ ν hD hsupport hB (hBn.trans hR) (zero_le_one.trans hK) hL hmass
    · intro x r hr
      exact hμ' x r ((one_div_le_one_div_of_le (by positivity) hBn).trans hr)
    · exact hν
  calc
    _ ≤ ∫⁻ v, ENNReal.ofReal (‖PlanarFalconer.sourceFourier μ v‖^2)
        ∂(radialIntervalMeasure ν 1+∑ j ∈ Finset.range n, radialFrequencyMeasure ν ((2:ℝ)^j)) :=
      lintegral_mono' (radial_interval_dyadic_cover ν n) le_rfl
    _ = (∫⁻ v, ENNReal.ofReal (‖PlanarFalconer.sourceFourier μ v‖^2) ∂radialIntervalMeasure ν 1)+
        ∑ j ∈ Finset.range n, ∫⁻ v, ENNReal.ofReal (‖PlanarFalconer.sourceFourier μ v‖^2)
          ∂radialFrequencyMeasure ν ((2:ℝ)^j) := by
      rw [lintegral_add_measure,lintegral_finsetSum_measure]
    _ ≤ 2+∑ _j ∈ Finset.range n, ENNReal.ofReal T :=
      add_le_add (radial_low_fourier μ ν hmass) (Finset.sum_le_sum hterm)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (by positivity),
        show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by norm_num,
        ← ENNReal.ofReal_add (by norm_num) (by positivity)]

end Falconer

end OAI
