import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGaugeCoreBoundary
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeFluxGauge

namespace OAI

/-! Value, slope and core traces of the physical two-channel profile gauge. -/

open Set
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable def spectralPhysicalGaugePair (Q f g : ℝ → ℂ) (r : ℝ) : E₄ :=
  ((Q r*(f r+Complex.I*g r),
     deriv Q r*(f r+Complex.I*g r)+Q r*(deriv f r+Complex.I*deriv g r)),
   (star (Q r)*(f r-Complex.I*g r),
     star (deriv Q r)*(f r-Complex.I*g r)+star (Q r)*(deriv f r-Complex.I*deriv g r)))

theorem spectralPhysicalGaugePair_value (Q f g : ℝ → ℂ) (r : ℝ) :
    spectralPhysicalValueMap (spectralPhysicalGaugePair Q f g r)=
      spectralGaugeColumns (Q r) (f r,g r) := by
  apply Prod.ext <;>
    simp [spectralPhysicalValueMap,spectralPhysicalGaugePair,spectralGaugeColumns,
      spectralTwoColumns] <;> ring

theorem spectralPhysicalGaugePair_slope (Q f g : ℝ → ℂ) (r : ℝ) :
    spectralPhysicalDerivativeMap (spectralPhysicalGaugePair Q f g r)=
      spectralGaugeColumns (Q r) (deriv f r,deriv g r)+
        spectralGaugeColumns (deriv Q r) (f r,g r) := by
  apply Prod.ext <;>
    simp [spectralPhysicalDerivativeMap,spectralPhysicalGaugePair,spectralGaugeColumns,
      spectralTwoColumns] <;> ring

theorem spectralPhysicalGaugePair_continuousOn (Q f g : ℝ → ℂ) (s : Set ℝ)
    (hQ : ContinuousOn Q s) (hDQ : ContinuousOn (deriv Q) s)
    (hf : ContinuousOn f s) (hDf : ContinuousOn (deriv f) s)
    (hg : ContinuousOn g s) (hDg : ContinuousOn (deriv g) s) :
    ContinuousOn (spectralPhysicalGaugePair Q f g) s := by
  unfold spectralPhysicalGaugePair
  fun_prop

theorem spectralPhysicalGaugePair_core (ell : ℕ) (Q f g : ℝ → ℂ) (r : ℝ)
    (hQ : Q r=1) (hDQ : deriv Q r=0) (hf : f r=0)
    (hg : deriv g r=(ell : ℂ)/(r : ℂ)*g r) :
    spectralFreeCoreBoundary ell r (spectralPhysicalGaugePair Q f g r)=0 := by
  have he : spectralPhysicalGaugePair Q f g r=
      ((f r+Complex.I*g r,deriv f r+Complex.I*deriv g r),
       (f r-Complex.I*g r,deriv f r-Complex.I*deriv g r)) := by
    simp [spectralPhysicalGaugePair,hQ,hDQ]
  rw [he]
  exact spectralGaugeCoreBoundary_zero ell r (f r) (g r) (deriv f r) (deriv g r) hf hg

theorem spectralPhysicalGaugePair_robin (Q f g : ℝ → ℂ) (r : ℝ)
    (M : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hB : spectralGaugeColumns (Q r) (deriv f r,deriv g r)+
      spectralGaugeColumns (deriv Q r) (f r,g r)=M (spectralGaugeColumns (Q r) (f r,g r))) :
    spectralPhysicalDerivativeMap (spectralPhysicalGaugePair Q f g r)=
      M (spectralPhysicalValueMap (spectralPhysicalGaugePair Q f g r)) := by
  rw [spectralPhysicalGaugePair_slope,spectralPhysicalGaugePair_value]
  exact hB

end DefocusingNLS

end OAI
