import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFirstTest
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPencilVariational

namespace OAI

/-! Schwartz tests in both coordinates determine the complete weak equation. -/

open scoped SchwartzMap
namespace DefocusingNLS

theorem spectralPairFunctional_ext (ell : ℕ) (R : ℝ)
    (L M : SpectralHarmonicPair ell R →L[ℝ] ℝ)
    (hf : ∀ f : 𝓢(ℝ,ℂ), L (spectralFirstTest ell R f)=M (spectralFirstTest ell R f))
    (hg : ∀ f : 𝓢(ℝ,ℂ), L (spectralSecondTest ell R f)=M (spectralSecondTest ell R f)) :
    L=M := by
  let J := (WithLp.prodContinuousLinearEquiv 2 ℂ
    (SpectralHarmonicEnergy ell R) (SpectralHarmonicEnergy ell R)).symm
  have hfirst : (fun v : SpectralHarmonicEnergy ell R => L (J (v,0)))=
      (fun v : SpectralHarmonicEnergy ell R => M (J (v,0))) :=
    (spectralHarmonicSmooth_dense ell R).equalizer
      (L.continuous.comp (J.continuous.comp (continuous_id.prodMk continuous_const)))
      (M.continuous.comp (J.continuous.comp (continuous_id.prodMk continuous_const))) (funext hf)
  have hsecond : (fun v : SpectralHarmonicEnergy ell R => L (J (0,v)))=
      (fun v : SpectralHarmonicEnergy ell R => M (J (0,v))) :=
    (spectralHarmonicSmooth_dense ell R).equalizer
      (L.continuous.comp (J.continuous.comp (continuous_const.prodMk continuous_id)))
      (M.continuous.comp (J.continuous.comp (continuous_const.prodMk continuous_id))) (funext hg)
  apply DFunLike.ext
  intro v
  have hv : v=J (v.fst,0)+J (0,v.snd) := by
    change v=WithLp.toLp 2 (v.fst,0)+WithLp.toLp 2 (0,v.snd)
    apply (WithLp.prodContinuousLinearEquiv 2 ℂ
      (SpectralHarmonicEnergy ell R) (SpectralHarmonicEnergy ell R)).injective
    change (v.fst,v.snd)=(v.fst+0,0+v.snd)
    simp
  rw [hv,map_add,map_add,congrFun hfirst,congrFun hsecond]

namespace SpectralPenaltyFamily
variable {R l : ℝ}

theorem compactPencil_of_smooth_tests (s : SpectralPenaltyFamily R l) (ell n : ℕ)
    (hR : 0 < R) (K : SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R)
    (u : SpectralHarmonicPair ell R)
    (hf : ∀ f : 𝓢(ℝ,ℂ), s.penaltyForm ell n u (spectralFirstTest ell R f)=
      inner ℝ (K (spectralHarmonicObservation ell R hR u)) (spectralFirstTest ell R f))
    (hg : ∀ f : 𝓢(ℝ,ℂ), s.penaltyForm ell n u (spectralSecondTest ell R f)=
      inner ℝ (K (spectralHarmonicObservation ell R hR u)) (spectralSecondTest ell R f)) :
    s.compactPencil ell hR n K (spectralHarmonicObservation ell R hR u)=
      spectralHarmonicObservation ell R hR u := by
  apply (s.compactPencil_variational ell n hR K _).mpr
  refine ⟨u,rfl,?_⟩
  have he := spectralPairFunctional_ext ell R (s.penaltyForm ell n u)
    (InnerProductSpace.toDual ℝ (SpectralHarmonicPair ell R)
      (K (spectralHarmonicObservation ell R hR u))) hf hg
  exact fun v => DFunLike.congr_fun he v

end SpectralPenaltyFamily
end DefocusingNLS

end OAI
