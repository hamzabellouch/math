import OAI.MeasureTheory.Falconer.Fourier.IntegratedSmoothing
import OAI.MeasureTheory.Falconer.Estimates.CriticalScale
import OAI.MeasureTheory.Falconer.Slicing.GaussianAmplification

namespace OAI

/-! # The critical half-dimensional estimate on one frequency shell -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def halfDimensionalShellConstant (d : ℕ) : ℝ :=
  ((Real.pi/2)^((d:ℝ)/2))⁻¹ *
    (Real.exp 1*8*(2:ℝ)^((d:ℝ)/2)*gaussianBallConstant (Nat.ceil ((d:ℝ)/2+1))) *
    (16*Real.pi)^((d:ℝ)/2)*gaussianBallConstant (Nat.ceil ((d:ℝ)/2))

theorem halfDimensionalShellConstant_nonneg (d : ℕ) :
    0 ≤ halfDimensionalShellConstant d := by
  have h₁ := gaussianBallConstant_nonneg (Nat.ceil ((d:ℝ)/2+1))
  have h₂ := gaussianBallConstant_nonneg (Nat.ceil ((d:ℝ)/2))
  unfold halfDimensionalShellConstant
  positivity

theorem damped_half_dimensional_shell (β : Measure (Space d)) [IsFiniteMeasure β]
    (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    {B R K L : ℝ} (hB : 1 ≤ B) (hBR : B ≤ R) (hK : 0 ≤ K) (hL : 1 ≤ L)
    (hmass : ν univ ≤ 1)
    (hβ : ∀ x : Space d, ∀ r : ℝ, 1/B ≤ r →
      β (ball x r) ≤ ENNReal.ofReal (K*r^((d:ℝ)/2)))
    (hν : ∀ x : Space d, ∀ r : ℝ, 1/R ≤ r → r ≤ 1 →
      ν {w : Sphere d | dist (w:Space d) x < r} ≤ ENNReal.ofReal (L*r^((d:ℝ)/2))) :
    (∫⁻ v, ENNReal.ofReal (‖PlanarFalconer.sourceFourier (gaussianDampedMeasure β) v‖^2)
      ∂radialFrequencyMeasure ν B) ≤
        ENNReal.ofReal (halfDimensionalShellConstant d*β.real univ*K*L) := by
  let s : ℝ := (d:ℝ)/2
  let A : ℝ := 8*(2:ℝ)^s*L/B^s
  let C : ℝ := ((Real.pi/2)^s)⁻¹
  let D : ℝ := Real.exp 1*A*gaussianBallConstant (Nat.ceil (s+1))
  have hB₀ : 0 < B := zero_lt_one.trans_le hB
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg (Real.exp_pos _).le hA) (gaussianBallConstant_nonneg _)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbase := gaussian_integrated_smoothing β (radialFrequencyMeasure ν B) hB hA
    (Nat.le_ceil (s+1)) ((radial_frequency_support ν B).mono (fun _ h => h.2))
    (radial_frequency_polynomial_balls ν hB hBR hL hs hmass hν)
  have henergy := gaussian_shell_energy_lintegral β hB₀ hK (Nat.le_ceil s) hβ
  calc
    _ ≤ ENNReal.ofReal (C*D)*
        ∫⁻ u : Space d, ENNReal.ofReal (Real.exp (-‖u‖^2/(16*B^2)))*
          ENNReal.ofReal (‖PlanarFalconer.sourceFourier β u‖^2) := hbase
    _ ≤ ENNReal.ofReal (C*D)*ENNReal.ofReal ((16*Real.pi*B^2)^s*
        (β.real univ*(K*(1/B)^s*gaussianBallConstant (Nat.ceil s)))) :=
      mul_le_mul_right henergy _
    _ = ENNReal.ofReal (C*D*((16*Real.pi*B^2)^s*
        (β.real univ*(K*(1/B)^s*gaussianBallConstant (Nat.ceil s))))) :=
      (ENNReal.ofReal_mul (mul_nonneg hC hD)).symm
    _ = _ := by
      congr 1
      calc
        C*D*((16*Real.pi*B^2)^s*(β.real univ*(K*(1/B)^s*gaussianBallConstant (Nat.ceil s)))) =
            (C*(Real.exp 1*8*(2:ℝ)^s*gaussianBallConstant (Nat.ceil (s+1)))*
              gaussianBallConstant (Nat.ceil s)*β.real univ*K*L)*
                ((16*Real.pi*B^2)^s*(1/B)^s/B^s) := by dsimp [D,A]; ring
        _ = _ := by
          rw [critical_gaussian_scale hB₀ (by positivity : (0:ℝ) ≤ 16*Real.pi)]
          dsimp [halfDimensionalShellConstant,C,s]
          ring


/-- One frequency shell for a bounded original probability, with no lower-scale ball bounds. -/
theorem half_dimensional_shell (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    {D B R K L : ℝ} (hD : 0 ≤ D) (hsupport : ∀ᵐ x ∂μ, ‖x‖ ≤ D)
    (hB : 1 ≤ B) (hBR : B ≤ R) (hK : 0 ≤ K) (hL : 1 ≤ L) (hmass : ν univ ≤ 1)
    (hμ : ∀ x : Space d, ∀ r : ℝ, 1/B ≤ r →
      μ (ball x r) ≤ ENNReal.ofReal (K*r^((d:ℝ)/2)))
    (hν : ∀ x : Space d, ∀ r : ℝ, 1/R ≤ r → r ≤ 1 →
      ν {w : Sphere d | dist (w:Space d) x < r} ≤ ENNReal.ofReal (L*r^((d:ℝ)/2))) :
    (∫⁻ v, ENNReal.ofReal (‖PlanarFalconer.sourceFourier μ v‖^2) ∂radialFrequencyMeasure ν B) ≤
      ENNReal.ofReal (halfDimensionalShellConstant d*
        (Real.exp ((Real.pi^2/2)*D^2))^2*K*L) := by
  let E := Real.exp ((Real.pi^2/2)*D^2)
  let := gaussianAmplifiedMeasure_finite μ hD hsupport
  have hβ : (gaussianAmplifiedMeasure μ).real univ ≤ E := by
    have hh := gaussianAmplifiedMeasure_le μ hD hsupport univ
    simp only [Measure.smul_apply,smul_eq_mul,measure_univ,mul_one] at hh
    have hh' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
    simpa only [measureReal_def,E,ENNReal.toReal_ofReal (Real.exp_pos _).le] using hh'
  have h := damped_half_dimensional_shell (gaussianAmplifiedMeasure μ) ν hB hBR
    (mul_nonneg (Real.exp_pos _).le hK) hL hmass
    (gaussianAmplifiedMeasure_ball_bound μ hD hsupport hμ) hν
  rw [gaussianDampedMeasure_amplified] at h
  refine h.trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hC := halfDimensionalShellConstant_nonneg d
  calc
    halfDimensionalShellConstant d*(gaussianAmplifiedMeasure μ).real univ*(E*K)*L ≤
        halfDimensionalShellConstant d*E*(E*K)*L := by
      gcongr
    _ = _ := by dsimp [E]; ring

end Falconer

end OAI
