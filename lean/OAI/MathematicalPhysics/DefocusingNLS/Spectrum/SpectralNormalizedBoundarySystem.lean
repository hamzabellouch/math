import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCoupledBoundarySystem
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralOscillatoryData

namespace OAI

/-! Convert normalized scalar comparison solutions into the exact boundary
systems used in the coupled absorption theorem. -/

open Set
namespace DefocusingNLS

theorem spectralOscillatoryData_frequency_robin (h F : ℝ) :
    (spectralOscillatoryData h (Real.sqrt (Real.sqrt F))).2 =
      ((h : ℂ)*Complex.I*(Real.sqrt F : ℂ))*
        (spectralOscillatoryData h (Real.sqrt (Real.sqrt F))).1 := by
  by_cases hk : Real.sqrt (Real.sqrt F) = 0
  · simp [spectralOscillatoryData,hk]
  · have hs : (Real.sqrt (Real.sqrt F) : ℂ)^2 = (Real.sqrt F : ℂ) := by
      exact_mod_cast Real.sq_sqrt (Real.sqrt_nonneg F)
    simpa only [hs] using spectralOscillatoryData_robin h (Real.sqrt (Real.sqrt F)) hk

noncomputable def spectralNormalizedBoundarySystem
    (R E A h F : ℝ) (hRE : R ≤ E) (k : ℝ → ℝ) (V : ℝ → ℂ)
    (D U : ℝ → ℂ × ℂ) (W : ℂ)
    (hk : ContinuousOn k (Icc R E)) (hkp : ∀ r ∈ Icc R E, 0 < k r)
    (hD : ContinuousOn D (Icc R E)) (hU : ContinuousOn U (Icc R E))
    (hDD : ∀ r ∈ Icc R E, HasDerivAt D (spectralScalarField (V r) (D r)) r)
    (hUD : ∀ r ∈ Icc R E, HasDerivAt U (spectralScalarField (V r) (U r)) r)
    (hDR : D R = (0,(k R : ℂ)))
    (hUE : U E = spectralOscillatoryData h (Real.sqrt (Real.sqrt F)))
    (hW : W ≠ 0) (hdet : ∀ r ∈ Icc R E, spectralScalarWronskian (D r) (U r) = W)
    (hgreen : ∀ r ∈ Icc R E, ∀ t ∈ Icc R E,
      spectralShellNorm (k r) (spectralScalarGreenState D U W r t) ≤ A/k t) :
    SpectralScalarBoundarySystem R E A where
  k := k
  V := V
  beta := (h : ℂ)*Complex.I*(Real.sqrt F : ℂ)
  D := D
  U := U
  W := W
  continuous_k := hk
  positive_k := hkp
  continuous_D := hD
  continuous_U := hU
  ode_D := hDD
  ode_U := hUD
  left_D := by rw [hDR]
  left_U := by
    intro he
    have hd := hdet R ⟨le_rfl,hRE⟩
    simp only [hDR,spectralScalarWronskian,he,mul_zero,zero_mul,sub_self] at hd
    exact hW hd.symm
  right_U := by rw [hUE]; exact spectralOscillatoryData_frequency_robin h F
  wronskian_ne := hW
  wronskian := hdet
  green := hgreen

end DefocusingNLS

end OAI
