import OAI.Analysis.LipschitzHilbert.Fourier.LineSamplingInverseDerivative
import OAI.Analysis.LipschitzHilbert.Fourier.LineSamplingEnergy

namespace OAI

/-! Actual forward and inverse sampling operators on Schwartz functions. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace LipschitzHilbert.PacketRepresentation

theorem lineSampling_temperate (u : ℝ → ℝ) (hc : ContDiff ℝ ∞ u)
    (hcompact : HasCompactSupport u) (t : ℝ) :
    Function.HasTemperateGrowth (lineSampling u t) := by
  have hu := (hcompact.toSchwartzMap hc).hasTemperateGrowth
  exact Function.HasTemperateGrowth.id'.sub ((Function.HasTemperateGrowth.const t).mul hu)

theorem lineSamplingInverse_temperate (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (hc : ContDiff ℝ ∞ u) (hcompact : HasCompactSupport u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (ht : |t|≤1/2) :
    Function.HasTemperateGrowth (lineSamplingInverse u t) := by
  let b := (lineSamplingGenerator_compact u hu hcompact B hB hb t ht).toSchwartzMap
    (lineSamplingGenerator_contDiff u hu hc B hB hb t ht)
  have heq : lineSamplingInverse u t=fun y => y-t*b y := by
    funext y
    have hh := lineSampling_inverse_apply u hu B hB hb t y
    change lineSamplingInverse u t y-t*u (lineSamplingInverse u t y)=y at hh
    have hb' : b y = -u (lineSamplingInverse u t y) := by
      change -u ((lineSamplingHomeomorph u hu B hB hb t ht).symm y)=_
      rw [lineSamplingInverse_eq u hu B hB hb t ht]
    rw [hb']
    linarith
  rw [heq]
  exact Function.HasTemperateGrowth.id'.sub
    ((Function.HasTemperateGrowth.const t).mul b.hasTemperateGrowth)

theorem lineSamplingInverse_antilipschitz (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (ht : |t|≤1/2) :
    AntilipschitzWith 2 (lineSamplingInverse u t) :=
  (lineSampling_lipschitz u hu t ht).to_rightInverse
    (lineSampling_inverse_apply u hu B hB hb t)

def lineSamplingSchwartz (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (hc : ContDiff ℝ ∞ u) (hcompact : HasCompactSupport u) (t : ℝ) (ht : |t|≤1/2) :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (lineSampling_temperate u hc hcompact t)
    (lineSampling_antilipschitz u hu t ht)

def lineSamplingInverseSchwartz (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (hc : ContDiff ℝ ∞ u) (hcompact : HasCompactSupport u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (ht : |t|≤1/2) :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℂ
    (lineSamplingInverse_temperate u hu hc hcompact B hB hb t ht)
    (lineSamplingInverse_antilipschitz u hu B hB hb t ht)

@[simp] theorem lineSamplingSchwartz_apply (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (hc : ContDiff ℝ ∞ u) (hcompact : HasCompactSupport u) (t : ℝ) (ht : |t|≤1/2)
    (f : SchwartzMap ℝ ℂ) (y : ℝ) :
    lineSamplingSchwartz u hu hc hcompact t ht f y=f (lineSampling u t y) := rfl

@[simp] theorem lineSamplingInverseSchwartz_apply (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (hc : ContDiff ℝ ∞ u) (hcompact : HasCompactSupport u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (ht : |t|≤1/2)
    (f : SchwartzMap ℝ ℂ) (y : ℝ) :
    lineSamplingInverseSchwartz u hu hc hcompact B hB hb t ht f y=
      f (lineSamplingInverse u t y) := rfl

theorem lineSamplingSchwartz_inverse (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (hc : ContDiff ℝ ∞ u) (hcompact : HasCompactSupport u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (ht : |t|≤1/2)
    (f : SchwartzMap ℝ ℂ) :
    lineSamplingSchwartz u hu hc hcompact t ht
      (lineSamplingInverseSchwartz u hu hc hcompact B hB hb t ht f)=f := by
  ext y
  simp only [lineSamplingSchwartz_apply,lineSamplingInverseSchwartz_apply,
    lineSamplingInverse_apply u hu t ht]

theorem lineSamplingInverseSchwartz_forward (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (hc : ContDiff ℝ ∞ u) (hcompact : HasCompactSupport u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (ht : |t|≤1/2)
    (f : SchwartzMap ℝ ℂ) :
    lineSamplingInverseSchwartz u hu hc hcompact B hB hb t ht
      (lineSamplingSchwartz u hu hc hcompact t ht f)=f := by
  ext y
  simp only [lineSamplingSchwartz_apply,lineSamplingInverseSchwartz_apply,
    lineSampling_inverse_apply u hu B hB hb t]

theorem lineCompositionL2_schwartz (phi : ℝ → ℝ) (hg : phi.HasTemperateGrowth)
    (ha : AntilipschitzWith 2 phi) (f : SchwartzMap ℝ ℂ) :
    lineCompositionL2 phi hg.1.continuous.measurable ha (f.toLp 2 volume)=
      (SchwartzMap.compCLMOfAntilipschitz ℂ hg ha f).toLp 2 volume := by
  rw [lineCompositionL2_onSchwartz]
  rfl

end LipschitzHilbert.PacketRepresentation

end

end OAI
