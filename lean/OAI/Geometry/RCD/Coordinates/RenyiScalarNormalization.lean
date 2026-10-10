import OAI.Geometry.RCD.Transport.RenyiIntegralAdditivity

namespace OAI

/-! # Cancellation of component mass in scalar Rényi bounds -/

open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X]

theorem renyiIntegral_normalized_bound (μ ν₀ νm ν₁ : Measure X) [SigmaFinite μ]
    [IsFiniteMeasure ν₀] [IsFiniteMeasure νm] [IsFiniteMeasure ν₁]
    {c s : ℝ≥0∞} (hc0 : c≠0) (hct : c≠∞) {N : ℝ} (hN : 1<N)
    (h : s*(renyiIntegral μ (c⁻¹ • ν₀) N+renyiIntegral μ (c⁻¹ • ν₁) N)≤
      renyiIntegral μ (c⁻¹ • νm) N) :
    s*(renyiIntegral μ ν₀ N+renyiIntegral μ ν₁ N)≤renyiIntegral μ νm N := by
  have hi : c⁻¹≠∞ := ENNReal.inv_ne_top.mpr hc0
  have hi0 : c⁻¹≠0 := ENNReal.inv_ne_zero.mpr hct
  let k := (c⁻¹)^(1-1/N)
  have hk0 : k≠0 := (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hi0) hi).ne'
  have hkt : k≠∞ := ENNReal.rpow_ne_top_of_ne_zero hi0 hi
  rw [renyiIntegral_smul μ ν₀ hi hN,renyiIntegral_smul μ ν₁ hi hN,
    renyiIntegral_smul μ νm hi hN] at h
  have hh : k*(s*(renyiIntegral μ ν₀ N+renyiIntegral μ ν₁ N))≤k*renyiIntegral μ νm N := by
    convert h using 1
    dsimp only [k]
    ring
  calc
    _ = k⁻¹*(k*(s*(renyiIntegral μ ν₀ N+renyiIntegral μ ν₁ N))) := by
      rw [←mul_assoc,ENNReal.inv_mul_cancel hk0 hkt,one_mul]
    _ ≤ k⁻¹*(k*renyiIntegral μ νm N) := mul_le_mul' le_rfl hh
    _ = _ := by rw [←mul_assoc,ENNReal.inv_mul_cancel hk0 hkt,one_mul]

end RegularPointCoordinates

end

end OAI
