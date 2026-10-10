import OAI.MeasureTheory.Falconer.Fourier.WeightedDistancePositiveKernel
import OAI.MeasureTheory.Falconer.Fourier.DistanceBandKernelBound

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
namespace PositiveDistanceData

theorem dominated_distance_band (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : μ ≤ ENNReal.ofReal (d.levelMass^(-2:ℤ)) • d.distance) :
    (2:ℝ)^(-(d.a:ℝ)) *
      (∫ r in Icc (-((2:ℝ)^d.t)) ((2:ℝ)^d.t), ‖charFun μ r‖^2) ≤
        (32*binKernelConstant.toReal) * d.coincidence.toReal := by
  have h := mul_le_mul_right (distance_band_kernel_bound_ennreal μ
    (by positivity : 0 < (2:ℝ)^d.t)) (ENNReal.ofReal ((2:ℝ)^(-(d.a:ℝ))))
  have hkernel := mul_le_mul_right (d.normalized_dominated_distance_kernel μ hμ) (32:ℝ≥0∞)
  have he : (2:ℝ)^(-(d.a:ℝ))*(32*(2:ℝ)^d.t) = 32*(2:ℝ)^((d.t:ℝ)-d.a) := by
    rw [mul_left_comm,← Real.rpow_natCast,
      ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 2
    ring
  have hc : ENNReal.ofReal ((2:ℝ)^(-(d.a:ℝ))) * ENNReal.ofReal (32*(2:ℝ)^d.t) =
      32*ENNReal.ofReal ((2:ℝ)^((d.t:ℝ)-d.a)) := by
    rw [← ENNReal.ofReal_mul (by positivity),he,ENNReal.ofReal_mul (by norm_num)]
    norm_num
  rw [← mul_assoc,hc,mul_assoc] at h
  have hh := h.trans hkernel
  have hr := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by norm_num) (ENNReal.mul_ne_top binKernelConstant_ne_top d.coincidence_ne_top)) hh
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (integral_nonneg (fun r => sq_nonneg ‖charFun μ r‖)),
    ENNReal.toReal_mul,ENNReal.toReal_mul] at hr
  norm_num only [ENNReal.toReal_ofNat] at hr
  simpa only [mul_assoc] using hr

end PositiveDistanceData

theorem uniform_actual_distance_low_band {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ (d : PositiveDistanceData) [IsFiniteMeasure d.ρ],
      N₀ ≤ d.N → d.sig = sig → d.J = J → d.Q.side = 1 →
      d.StronglySeparated → d.ρ d.Q.carrierᶜ = 0 → 0 < d.q → d.t ≤ d.N →
      ∀ v ≤ d.t, (2:ℝ)^(-(d.a:ℝ)) *
        (∫ r in Icc (-((2:ℝ)^v)) ((2:ℝ)^v), ‖charFun d.weightedDistance r‖^2) ≤
          (32*binKernelConstant.toReal) *
            ({d with t := v,i := d.i+1} : PositiveDistanceData).coincidence.toReal := by
  obtain ⟨N₀,h₀⟩ := uniform_weighted_distance_nested_domination hsig hJ
  refine ⟨N₀,?_⟩
  intro d _ hN hsig' hJ' hQ hs hcarry hq ht v hv
  let := d.weightedDistance_isFinite (by rw [hQ]; norm_num) hs
  exact ({d with t := v,i := d.i+1} : PositiveDistanceData).dominated_distance_band
    d.weightedDistance (h₀ d hN hsig' hJ' hQ hs hcarry hq ht v hv)

end PlanarFalconer

end OAI
