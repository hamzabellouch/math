import OAI.Geometry.RCD.Sobolev.GammaL2Stability
import OAI.Geometry.RCD.Sobolev.GammaLpNorm

namespace OAI

/-! # Weak energy convergence of bounded energy densities -/

open Set Filter MeasureTheory
open scoped NNReal Topology

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem gamma_representatives_tendsto
    {us Gs : ℕ → SobolevSpace μ hQ} {u G : SobolevSpace μ hQ} (L : ℝ≥0)
    (hus : ∀ k, ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ (us k) x ≤ L)
    (hu : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ u x ≤ L)
    (hconv : Tendsto us atTop (𝓝 u))
    (hGs : ∀ k, SobolevSpace.toLp μ hQ (Gs k) =ᵐ[μ] localGamma μ hQ (us k) (us k))
    (hG : SobolevSpace.toLp μ hQ G =ᵐ[μ] localGamma μ hQ u u) :
    Tendsto (fun k => SobolevSpace.toLp μ hQ (Gs k)) atTop (𝓝 (SobolevSpace.toLp μ hQ G)) := by
  have hEq (k : ℕ) : SobolevSpace.toLp μ hQ (Gs k) =
      (localGamma_memLp_of_bounded_gradient μ hQ (us k) (us k) L (hus k)).toLp
        (localGamma μ hQ (us k) (us k)) :=
    Lp.ext ((hGs k).trans
      (localGamma_memLp_of_bounded_gradient μ hQ (us k) (us k) L (hus k)).coeFn_toLp.symm)
  have hEqG : SobolevSpace.toLp μ hQ G =
      (localGamma_memLp_of_bounded_gradient μ hQ u u L hu).toLp (localGamma μ hQ u u) :=
    Lp.ext (hG.trans (localGamma_memLp_of_bounded_gradient μ hQ u u L hu).coeFn_toLp.symm)
  simp_rw [hEq, hEqG]
  exact gammaL2_tendsto μ hQ L hus hu hconv

theorem gamma_representatives_energy_tendsto
    {us Gs : ℕ → SobolevSpace μ hQ} {u G : SobolevSpace μ hQ} (L : ℝ≥0)
    (hus : ∀ k, ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ (us k) x ≤ L)
    (hu : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ u x ≤ L)
    (hconv : Tendsto us atTop (𝓝 u))
    (hGs : ∀ k, SobolevSpace.toLp μ hQ (Gs k) =ᵐ[μ] localGamma μ hQ (us k) (us k))
    (hG : SobolevSpace.toLp μ hQ G =ᵐ[μ] localGamma μ hQ u u)
    {B : ℝ} (hB : 0 ≤ B) (hE : ∀ k, energyForm μ hQ (Gs k) (Gs k) ≤ B)
    (w : SobolevSpace μ hQ) :
    Tendsto (fun k => energyForm μ hQ (Gs k) w) atTop (𝓝 (energyForm μ hQ G w)) := by
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto us hconv).exists_norm_le
  have hnorm (k : ℕ) : ‖SobolevSpace.toLp μ hQ (Gs k)‖ ≤ (L : ℝ) * C := by
    have he : SobolevSpace.toLp μ hQ (Gs k) =
        (localGamma_memLp_of_bounded_gradient μ hQ (us k) (us k) L (hus k)).toLp
          (localGamma μ hQ (us k) (us k)) :=
      Lp.ext ((hGs k).trans
        (localGamma_memLp_of_bounded_gradient μ hQ (us k) (us k) L (hus k)).coeFn_toLp.symm)
    rw [he]
    exact (gammaLp_norm_le μ hQ (us k) (us k) L (hus k) _).trans
      (mul_le_mul_of_nonneg_left (hC (us k) (mem_range_self k)) L.coe_nonneg)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (us 0) (mem_range_self 0))
  have hbound (k : ℕ) : ‖Gs k‖ ≤ Real.sqrt (((L : ℝ) * C) ^ 2 + B) := by
    have hs := SobolevSpace.norm_sq μ hQ (Gs k)
    have he := hE k
    rw [energyForm_self] at he
    simp only [SobolevSpace.normSq] at hs
    have hn := pow_le_pow_left₀ (norm_nonneg _) (hnorm k) 2
    have hsq := Real.sq_sqrt (show 0 ≤ ((L : ℝ) * C) ^ 2 + B by positivity)
    nlinarith [norm_nonneg (Gs k), Real.sqrt_nonneg (((L : ℝ) * C) ^ 2 + B)]
  exact SobolevSpace.energyForm_tendsto_of_toLp_tendsto_bounded μ hQ hbound
    (gamma_representatives_tendsto μ hQ L hus hu hconv hGs hG) w

end RegularPointCoordinates

end OAI
