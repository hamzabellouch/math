import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFirstClassicalFlux

namespace OAI

/-! The weak limiting equation is a classical four-component flux ODE outside the core. -/

open Set MeasureTheory
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable def spectralFluxState (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w a : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R) (x : ℝ) : E₄ :=
  ((spectralHarmonicRepresentative ell R hR u.fst x,
    spectralHarmonicRepresentative ell R hR u.snd x),
   (spectralSecondClassicalFlux ell R hR w (spectralNegWeight a) (spectralSwapPair ell R u) x,
    spectralSecondClassicalFlux ell R hR w a u x))

noncomputable def spectralFluxField (ell : ℕ) (μ A : ℝ) (c ζ : ℂ) (r : ℝ) (U : E₄) : E₄ :=
  (((U.2.1/(r : ℂ)^11+(A : ℂ)*U.1.2)/(μ : ℂ),
    (U.2.2/(r : ℂ)^11-(A : ℂ)*U.1.1)/(μ : ℂ)),
   (((ell : ℂ)*((ell : ℂ)+10)*(r : ℂ)^9*(μ : ℂ)*U.1.1-
     (c-ζ)*(r : ℂ)^11*(μ : ℂ)*U.1.2),
    ((ell : ℂ)*((ell : ℂ)+10)*(r : ℂ)^9*(μ : ℂ)*U.1.2+
     (c-ζ)*(r : ℂ)^11*(μ : ℂ)*U.1.1)))

theorem spectralFluxState_hasDerivAt (ell : ℕ) (R l : ℝ) (hR : 0 < R) (hl : 0 < l)
    (w a : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R) (c ζ : ℂ)
    (B : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hw : ContinuousOn w.density (Ioo 0 R)) (ha : ContinuousOn a.density (Ioo 0 R))
    (hpos : ∀ x ∈ Ioo 0 R, 0 < w.density x)
    (he : ∀ v : spectralHarmonicCoreSubspace ell R l,
      spectralHarmonicPairComplexForm ell R w u v=
      inner ℂ (spectralLowerOrderOperator ell R hR
        (spectralRadialWeightMultiplier R w) (spectralRadialWeightMultiplier R a) c ζ B
        (spectralHarmonicObservation ell R hR u)) v)
    (x : ℝ) (hx : x ∈ Ioo l R) :
    HasDerivAt (spectralFluxState ell R hR w a u)
      (spectralFluxField ell (w.density x) (a.density x) c ζ x
        (spectralFluxState ell R hR w a u x)) x := by
  have hx0 : x ∈ Ioo 0 R := ⟨hl.trans hx.1,hx.2⟩
  obtain ⟨hf,_,hF⟩ := spectralFirst_classical ell R l hR hl w a u c ζ B hw ha hpos he
  obtain ⟨hg,_,hG⟩ := spectralSecond_classical ell R hR w a u c ζ B hw ha hpos
    (fun f => he ⟨spectralSecondTest ell R f,spectralSecondTest_core ell R l f⟩)
  have hdf := ((hf x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt
  have hdg := ((hg x hx0).differentiableAt (isOpen_Ioo.mem_nhds hx0)).hasDerivAt
  apply ((hdf.prodMk hdg).prodMk ((hF x hx).prodMk (hG x hx0))).congr_deriv
  have hxn : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.1.ne'
  have hmn : (w.density x : ℂ) ≠ 0 := by exact_mod_cast (hpos x hx0).ne'
  have hsf : (spectralSwapPair ell R u).fst=u.snd := rfl
  have hss : (spectralSwapPair ell R u).snd=u.fst := rfl
  apply Prod.ext <;> apply Prod.ext
  · dsimp only [spectralFluxField,spectralFluxState,spectralSecondClassicalFlux,spectralNegWeight]
    rw [hsf,hss]
    push_cast
    field_simp
    ring
  · dsimp only [spectralFluxField,spectralFluxState,spectralSecondClassicalFlux]
    field_simp
    ring
  · dsimp only [spectralFluxField,spectralFluxState,spectralSecondContinuousSource]
    rw [hsf,hss]
    simp only [Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_ofNat,
      Complex.real_smul]
    ring
  · dsimp only [spectralFluxField,spectralFluxState,spectralSecondContinuousSource]
    simp only [Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_ofNat,
      Complex.real_smul]
    ring

end DefocusingNLS

end OAI
