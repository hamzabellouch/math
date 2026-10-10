import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBAmplitude
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBSquareRoot

namespace OAI

/-! The scalar WKB frame is constructed from integrals, including its
normalization. Its constant Wronskian and differential equation are derived. -/

open Set MeasureTheory
namespace DefocusingNLS

noncomputable def spectralWKBInitialAmplitude (z : ℂ) : ℂ := (Complex.sqrt z)⁻¹

noncomputable def spectralWKBPhase (R : ℝ) (chi : ℂ) (p : ℝ → ℂ) (r : ℝ) : ℂ :=
  chi*(∫ t in R..r, p t)

noncomputable def spectralWKBFrame (R : ℝ) (chi : ℂ) (p v : ℝ → ℂ) (r : ℝ) : ℂ × ℂ :=
  spectralWKBState chi (p r) (v r)
    (spectralWKBAmplitude R (spectralWKBInitialAmplitude (p R)) p v r)
    (spectralWKBPhase R chi p r)

theorem spectralWKBInitialAmplitude_normalization (z : ℂ) (hz : z≠0) :
    z*(spectralWKBInitialAmplitude z)^2=1 := by
  have hs := spectralComplexSqrt_ne_zero z hz
  have he := spectralComplexSqrt_sq z
  dsimp only [spectralWKBInitialAmplitude]
  field_simp
  exact he.symm

theorem spectralWKBPhase_continuousOn (R E : ℝ) (hRE : R≤ E) (chi : ℂ)
    (p : ℝ → ℂ) (hp : ContinuousOn p (Icc R E)) :
    ContinuousOn (spectralWKBPhase R chi p) (Icc R E) := by
  have hi : IntervalIntegrable p volume R E := ContinuousOn.intervalIntegrable_of_Icc hRE hp
  have hc := intervalIntegral.continuousOn_primitive_interval' hi (show R ∈ uIcc R E from left_mem_uIcc)
  rw [uIcc_of_le hRE] at hc
  exact continuousOn_const.mul hc

theorem spectralWKBPhase_hasDerivAt (R E : ℝ) (chi : ℂ)
    (p : ℝ → ℂ) (hp : ContinuousOn p (Icc R E)) (r : ℝ) (hr : r ∈ Ioo R E) :
    HasDerivAt (spectralWKBPhase R chi p) (chi*p r) r :=
  (spectralShellPrimitive_hasDerivAt R E p hp r hr).const_mul chi

theorem spectralWKBFrame_continuousOn (R E : ℝ) (hRE : R≤ E) (chi : ℂ)
    (p v : ℝ → ℂ) (hp : ContinuousOn p (Icc R E))
    (hv : ContinuousOn v (Icc R E)) (hp0 : ∀ r ∈ Icc R E, p r≠0) :
    ContinuousOn (spectralWKBFrame R chi p v) (Icc R E) := by
  have ha := spectralWKBAmplitude_continuousOn R E hRE
    (spectralWKBInitialAmplitude (p R)) p v hp hv hp0
  have hS := spectralWKBPhase_continuousOn R E hRE chi p hp
  have hL : ContinuousOn (fun r => homogeneousSpectralWKBLog chi (p r) (v r)) (Icc R E) :=
    (continuousOn_const.mul hp).sub (hv.div (continuousOn_const.mul hp)
      (fun r hr => mul_ne_zero (by norm_num) (hp0 r hr)))
  have hz := ha.mul (Complex.continuous_exp.comp_continuousOn hS)
  exact hz.prodMk (hL.mul hz)

theorem spectralWKBFrame_wronskian (R E : ℝ) (hRE : R≤ E) (chi : ℂ)
    (p v : ℝ → ℂ) (hp : ContinuousOn p (Icc R E))
    (hv : ContinuousOn v (Icc R E)) (hp0 : ∀ r ∈ Icc R E, p r≠0)
    (hpD : ∀ r ∈ Ioo R E, HasDerivAt p (v r) r)
    (r : ℝ) (hr : r ∈ Icc R E) :
    spectralScalarWronskian (spectralWKBFrame R chi p v r)
      (spectralWKBFrame R (-chi) p v r)= -2*chi := by
  have ha := spectralWKBAmplitude_normalization R E hRE
    (spectralWKBInitialAmplitude (p R)) p v hp hv hp0 hpD
    (spectralWKBInitialAmplitude_normalization (p R) (hp0 R ⟨le_rfl,hRE⟩)) r hr
  have hS : spectralWKBPhase R (-chi) p r= -spectralWKBPhase R chi p r := neg_mul _ _
  dsimp only [spectralWKBFrame]
  rw [hS]
  exact spectralWKBState_wronskian _ _ _ _ _ ha

theorem spectralWKBFrame_hasDerivAt (R E : ℝ) (chi : ℂ) (p v : ℝ → ℂ)
    (hp : ContinuousOn p (Icc R E)) (hv : ContinuousOn v (Icc R E))
    (hp0 : ∀ r ∈ Icc R E, p r≠0) (w : ℂ) (r : ℝ) (hr : r ∈ Ioo R E)
    (hpD : HasDerivAt p (v r) r) (hvD : HasDerivAt v w r) :
    HasDerivAt (spectralWKBFrame R chi p v)
      (spectralScalarField (-(chi^2*(p r)^2+homogeneousSpectralWKBResidual (p r) (v r) w))
        (spectralWKBFrame R chi p v r)) r := by
  have hd := spectralWKBState_hasDerivAt chi p v
    (spectralWKBAmplitude R (spectralWKBInitialAmplitude (p R)) p v)
    (spectralWKBPhase R chi p) w r (hp0 r ⟨hr.1.le,hr.2.le⟩)
    hpD hvD (spectralWKBAmplitude_hasDerivAt R E _ p v hp hv hp0 r hr)
    (spectralWKBPhase_hasDerivAt R E chi p hp r hr)
  apply hd.congr_deriv
  simp only [spectralScalarField,spectralWKBFrame,neg_neg]

end DefocusingNLS

end OAI
