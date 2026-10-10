import OAI.MeasureTheory.Falconer.Fourier.HalfDimensionalFourier

namespace OAI

/-! # Converting the proved frequency bound back to angular averages -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem radial_interval_lintegral (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (ν : Measure (Sphere d)) [IsFiniteMeasure ν] (H : ℝ) :
    (∫⁻ v, ENNReal.ofReal (‖PlanarFalconer.sourceFourier μ v‖^2) ∂radialIntervalMeasure ν H) =
      ∫⁻ r : ℝ in Icc (-H) H, ∫⁻ w : Sphere d,
        ENNReal.ofReal (‖PlanarFalconer.sourceFourier μ (r • (w:Space d))‖^2) ∂ν := by
  rw [radialIntervalMeasure,lintegral_map (by unfold PlanarFalconer.sourceFourier; fun_prop)
    (by unfold radialFrequencyMap; fun_prop)]
  exact lintegral_prod _ (by unfold radialFrequencyMap PlanarFalconer.sourceFourier; fun_prop)

theorem dyadic_half_dimensional_average (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    {D R K L : ℝ} (hD : 0 ≤ D) (hsupport : ∀ᵐ x ∂μ, ‖x‖ ≤ D)
    (n : ℕ) (hR : (2:ℝ)^n ≤ R) (hK : 1 ≤ K) (hL : 1 ≤ L) (hmass : ν univ ≤ 1)
    (hμ : ∀ x : Space d, ∀ r : ℝ, 1/(2:ℝ)^n ≤ r → r ≤ 1 →
      μ (ball x r) ≤ ENNReal.ofReal (K*r^((d:ℝ)/2)))
    (hν : ∀ x : Space d, ∀ r : ℝ, 1/R ≤ r → r ≤ 1 →
      ν {w : Sphere d | dist (w:Space d) x < r} ≤ ENNReal.ofReal (L*r^((d:ℝ)/2))) :
    (∫⁻ w : Sphere d, (∫⁻ r : ℝ in Icc (-((2:ℝ)^n)) ((2:ℝ)^n),
      ENNReal.ofReal (‖PlanarFalconer.sourceFourier μ (r • (w:Space d))‖^2)) ∂ν) ≤
      ENNReal.ofReal (2+(n:ℝ)*(halfDimensionalShellConstant d*
        (Real.exp ((Real.pi^2/2)*D^2))^2*K*L)) := by
  have hswap : (∫⁻ w : Sphere d, (∫⁻ r : ℝ in Icc (-((2:ℝ)^n)) ((2:ℝ)^n),
      ENNReal.ofReal (‖PlanarFalconer.sourceFourier μ (r • (w:Space d))‖^2)) ∂ν) =
      ∫⁻ r : ℝ in Icc (-((2:ℝ)^n)) ((2:ℝ)^n), ∫⁻ w : Sphere d,
        ENNReal.ofReal (‖PlanarFalconer.sourceFourier μ (r • (w:Space d))‖^2) ∂ν := by
    apply lintegral_lintegral_swap
    unfold PlanarFalconer.sourceFourier
    fun_prop
  rw [hswap,← radial_interval_lintegral]
  exact dyadic_half_dimensional_fourier μ ν hD hsupport n hR hK hL hmass hμ hν

end Falconer

end OAI
