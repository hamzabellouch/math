import OAI.MeasureTheory.Falconer.Fourier.FourierEnergy

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem sourceFourier_convolution (μ ν : Measure V) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (ξ : V) :
    sourceFourier (μ ∗ ν) ξ = sourceFourier μ ξ * sourceFourier ν ξ := by
  exact charFun_conv _

theorem sourceFourier_convolution_norm_le (μ ν : Measure V) [IsFiniteMeasure μ]
    [IsProbabilityMeasure ν] (ξ : V) :
    ‖sourceFourier (μ ∗ ν) ξ‖ ≤ ‖sourceFourier μ ξ‖ := by
  rw [sourceFourier_convolution,norm_mul]
  have norm_bound : ‖sourceFourier ν ξ‖ ≤ 1 :=
    norm_charFun_le_one (μ := ν) ((-(2 * Real.pi)) • ξ)
  exact (mul_le_mul_of_nonneg_left norm_bound (norm_nonneg _)).trans_eq (mul_one _)

theorem rieszEnergyOn_convolution_probability_le (μ ν : Measure V) [IsFiniteMeasure μ]
    [IsProbabilityMeasure ν] {u : ℝ} (hu : 0 < u) (hun : u < Module.finrank ℝ V) :
    rieszEnergyOn (μ ∗ ν) u ≤ rieszEnergyOn μ u := by
  rw [source_fourier_energy_identity (μ ∗ ν) hu hun,source_fourier_energy_identity μ hu hun]
  apply mul_le_mul_right
  apply lintegral_mono
  intro ξ
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  exact pow_le_pow_left₀ (norm_nonneg _) (sourceFourier_convolution_norm_le μ ν ξ) 2

theorem rieszEnergy_convolution_probability_le (μ ν : Measure Plane) [IsFiniteMeasure μ]
    [IsProbabilityMeasure ν] {u : ℝ} (hu : 0 < u) (hu2 : u < 2) :
    rieszEnergy (μ ∗ ν) u ≤ rieszEnergy μ u := by
  rw [← rieszEnergyOn_plane,← rieszEnergyOn_plane]
  exact rieszEnergyOn_convolution_probability_le μ ν hu (by simpa [Plane] using hu2)

end PlanarFalconer

end OAI
