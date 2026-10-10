import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralOutgoingComparison
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningPositiveReverse

namespace OAI

/-! Construct the normalized outgoing scalar solution on the full comparison
interval and bound its Cauchy data just to the right of the turning point. -/

open Set
namespace DefocusingNLS

theorem spectralTurning_outgoing_comparison_bound
    (ell : ℕ) (h b omega gamma r₀ d M R E : ℝ)
    (hh : h^2=1) (hb : 0≤b) (hb1 : b≤1) (hr₀ : 16≤r₀) (hd : 0<d) (hM : 32≤M)
    (hR : 0<R) (hRhalf : R≤r₀/2) (hMd : M*d≤r₀/2)
    (hE : 2*r₀≤E) (hEscale : E^2=256*max ((ell : ℝ)+1) omega) (hgamma : |gamma|≤8)
    (hz : homogeneousSpectralLocalizationFrequency h b ((ell : ℝ)*(ell+10)) omega r₀=0)
    (hscale : spectralLiouvilleSlope ((ell : ℝ)*(ell+10)) r₀*d^3=1) :
    ∃ q : ℝ → ℂ × ℂ, Continuous q ∧
      q E=spectralOscillatoryData h
        (Real.sqrt (Real.sqrt (homogeneousSpectralLocalizationFrequency h b ((ell : ℝ)*(ell+10)) omega E))) ∧
      spectralScalarFlux (q E)=h ∧
      spectralShellNorm (Real.sqrt ‖spectralLiouvilleMomentum 1 h b
        ((ell : ℝ)*(ell+10)) omega gamma (r₀+M*d)‖) (q (r₀+M*d))≤
        (75/2 : ℝ)*Real.exp (|gamma| * 288+(25/4)*(5/(3*(Real.sqrt (M/8))^3)+
          3*d/(r₀*Real.sqrt (M/8))+8/r₀^2)) ∧
      ∀ t ∈ Icc R E, HasDerivAt q
        (spectralScalarField ((homogeneousSpectralLocalizationFrequency h b
          ((ell : ℝ)*(ell+10)) omega t : ℂ)+Complex.I*(gamma : ℂ)) (q t)) t := by
  let eta : ℝ := (ell : ℝ)*(ell+10)
  have heta : 0≤eta := by dsimp only [eta]; positivity
  have hr₀p : 0<r₀ := by linarith
  have hEpos : 0<E := by linarith
  have hFElo := (spectralTurning_far_geometry h b eta omega r₀ E heta hr₀p hE hz).1
  have hFE : 0<homogeneousSpectralLocalizationFrequency h b eta omega E :=
    (show 0<E^2/32 by positivity).trans_le hFElo
  have hgammaF : |gamma|≤homogeneousSpectralLocalizationFrequency h b eta omega E := by
    nlinarith
  have hRE : R≤E := by linarith
  obtain ⟨q,hq,hqE,hflux,hnorm,hqD⟩ := spectralLiouville_outgoing_exists h b eta omega gamma R E
    hh hR hRE hFE hgammaF
  refine ⟨q,hq,hqE,hflux,?_,hqD⟩
  have hRa : R≤r₀+M*d := by nlinarith
  have hbound := spectralTurning_positive_reverse_transfer ell h b omega gamma r₀ d M E
    hh hb hb1 (by linarith) hd hM (by linarith) hE hEscale hz hscale q hq.continuousOn
    (fun t ht => hqD t ⟨hRa.trans ht.1.le,ht.2.le⟩)
  calc
    _ ≤ ((25/2 : ℝ)*Real.exp (|gamma| * 288+(25/4)*(5/(3*(Real.sqrt (M/8))^3)+
        3*d/(r₀*Real.sqrt (M/8))+8/r₀^2)))*
        spectralShellNorm (Real.sqrt ‖spectralLiouvilleMomentum 1 h b eta omega gamma E‖) (q E) := hbound
    _ ≤ ((25/2 : ℝ)*Real.exp (|gamma| * 288+(25/4)*(5/(3*(Real.sqrt (M/8))^3)+
        3*d/(r₀*Real.sqrt (M/8))+8/r₀^2)))*3 := mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = _ := by ring

end DefocusingNLS

end OAI
