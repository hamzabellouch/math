import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFluxSystem
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralChainFirstFlux

namespace OAI

/-! The actual first chain obeys the derivative of the classical flux ODE. -/

open Set MeasureTheory
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable def spectralFluxFieldSlope (μ : ℝ) (r : ℝ) (U : E₄) : E₄ :=
  ((0,0),((r : ℂ)^11*(μ : ℂ)*U.1.2,-(r : ℂ)^11*(μ : ℂ)*U.1.1))

theorem spectralFluxState_chain_hasDerivAt (ell : ℕ) (R l : ℝ) (hR : 0 < R) (hl : 0 < l)
    (w a : SpectralHarmonicWeight R) (u₀ u₁ : SpectralHarmonicPair ell R) (c ζ : ℂ)
    (B B' : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hw : ContinuousOn w.density (Ioo 0 R)) (ha : ContinuousOn a.density (Ioo 0 R))
    (hpos : ∀ x ∈ Ioo 0 R, 0 < w.density x)
    (he : ∀ v : spectralHarmonicCoreSubspace ell R l,
      spectralHarmonicPairComplexForm ell R w u₁ v=
      inner ℂ (spectralLowerOrderOperator ell R hR
        (spectralRadialWeightMultiplier R w) (spectralRadialWeightMultiplier R a) c ζ B
        (spectralHarmonicObservation ell R hR u₁) +
        spectralLowerOrderSlope ell R hR (spectralRadialWeightMultiplier R w) B'
          (spectralHarmonicObservation ell R hR u₀)) v)
    (x : ℝ) (hx : x ∈ Ioo l R) :
    HasDerivAt (spectralFluxState ell R hR w a u₁)
      (spectralFluxField ell (w.density x) (a.density x) c ζ x
        (spectralFluxState ell R hR w a u₁ x) +
        spectralFluxFieldSlope (w.density x) x (spectralFluxState ell R hR w a u₀ x)) x := by
  have hx0 : x ∈ Ioo 0 R := ⟨hl.trans hx.1,hx.2⟩
  obtain ⟨hf,_,hF⟩ := spectralFirstChain_classical ell l R hl.le hR w a u₀ u₁ c ζ B B' hw ha hpos he
  obtain ⟨hg,_,hG⟩ := spectralSecondChain_classical ell R hR w a u₀ u₁ c ζ B B' hw ha hpos
    (fun f => he ⟨spectralSecondTest ell R f,spectralSecondTest_core ell R l f⟩)
  have hdf := ((hf x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt
  have hdg := ((hg x hx0).differentiableAt (isOpen_Ioo.mem_nhds hx0)).hasDerivAt
  apply ((hdf.prodMk hdg).prodMk ((hF x hx).prodMk (hG x hx0))).congr_deriv
  have hxn : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.1.ne'
  have hmn : (w.density x : ℂ) ≠ 0 := by exact_mod_cast (hpos x hx0).ne'
  have hsf : (spectralSwapPair ell R u₁).fst=u₁.snd := rfl
  have hss : (spectralSwapPair ell R u₁).snd=u₁.fst := rfl
  apply Prod.ext <;> apply Prod.ext
  · dsimp only [spectralFluxField,spectralFluxFieldSlope,Prod.fst_add,Prod.snd_add,spectralFluxState,spectralSecondClassicalFlux,spectralNegWeight]
    rw [hsf,hss]
    push_cast
    simp only [add_zero]
    field_simp
    ring
  · dsimp only [spectralFluxField,spectralFluxFieldSlope,Prod.fst_add,Prod.snd_add,spectralFluxState,spectralSecondClassicalFlux]
    simp only [add_zero]
    field_simp
    ring
  · dsimp only [spectralFluxField,spectralFluxFieldSlope,Prod.fst_add,Prod.snd_add,spectralFluxState,spectralFirstChainSource,spectralSecondContinuousSource]
    rw [hsf,hss]
    simp only [Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_ofNat,
      Complex.real_smul]
    ring
  · dsimp only [spectralFluxField,spectralFluxFieldSlope,Prod.fst_add,Prod.snd_add,spectralFluxState,spectralSecondChainSource,spectralSecondContinuousSource]
    simp only [Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_ofNat,
      Complex.real_smul]
    ring

end DefocusingNLS

end OAI
