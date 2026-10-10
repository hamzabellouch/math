import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSpectralLocalizationWKB
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarGreen

namespace OAI

/-! An explicit WKB frame with constant Wronskian, for the scalar transfer
on either side of the turning interval. -/

namespace DefocusingNLS

noncomputable def spectralWKBValue (a S : ℂ) : ℂ := a*Complex.exp S

noncomputable def spectralWKBState (chi p v a S : ℂ) : ℂ × ℂ :=
  (spectralWKBValue a S,homogeneousSpectralWKBLog chi p v*spectralWKBValue a S)

theorem spectralWKBValue_product (a S : ℂ) :
    spectralWKBValue a S*spectralWKBValue a (-S)=a^2 := by
  dsimp only [spectralWKBValue]
  calc
    _ = a^2*(Complex.exp S*Complex.exp (-S)) := by ring
    _ = a^2 := by rw [← Complex.exp_add,add_neg_cancel,Complex.exp_zero,mul_one]

theorem spectralWKBState_wronskian (chi p v a S : ℂ) (ha : p*a^2=1) :
    spectralScalarWronskian (spectralWKBState chi p v a S)
      (spectralWKBState (-chi) p v a (-S))= -2*chi := by
  have hp := spectralWKBValue_product a S
  calc
    _ = -2*chi*p*(spectralWKBValue a S*spectralWKBValue a (-S)) := by
      dsimp only [spectralScalarWronskian,spectralWKBState,homogeneousSpectralWKBLog]
      ring
    _ = -2*chi := by rw [hp]; linear_combination -2*chi*ha

theorem spectralWKBValue_hasDerivAt
    (chi : ℂ) (p v a S : ℝ → ℂ) (r : ℝ)
    (ha : HasDerivAt a (-(v r/(2*p r))*a r) r)
    (hS : HasDerivAt S (chi*p r) r) :
    HasDerivAt (fun t => spectralWKBValue (a t) (S t))
      (homogeneousSpectralWKBLog chi (p r) (v r)*spectralWKBValue (a r) (S r)) r := by
  apply (ha.mul hS.cexp).congr_deriv
  dsimp only [homogeneousSpectralWKBLog,spectralWKBValue]
  ring

theorem spectralWKBState_hasDerivAt
    (chi : ℂ) (p v a S : ℝ → ℂ) (w : ℂ) (r : ℝ)
    (hp0 : p r≠0) (hp : HasDerivAt p (v r) r) (hv : HasDerivAt v w r)
    (ha : HasDerivAt a (-(v r/(2*p r))*a r) r)
    (hS : HasDerivAt S (chi*p r) r) :
    HasDerivAt (fun t => spectralWKBState chi (p t) (v t) (a t) (S t))
      ((spectralWKBState chi (p r) (v r) (a r) (S r)).2,
        (chi^2*(p r)^2+homogeneousSpectralWKBResidual (p r) (v r) w)*
          (spectralWKBState chi (p r) (v r) (a r) (S r)).1) r := by
  have hz := spectralWKBValue_hasDerivAt chi p v a S r ha hS
  exact hz.prodMk (homogeneousSpectralWKB_acceleration chi p v
    (fun t => spectralWKBValue (a t) (S t)) w r hp0 hp hv hz)

end DefocusingNLS

end OAI
