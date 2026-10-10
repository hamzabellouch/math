import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningPositiveTransfer
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleNormPositive
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarReverseTransfer

namespace OAI

/-! A uniform reverse bound for actual outgoing scalar data in the oscillatory
outer interval, obtained from the proved forward estimate by Wronskian duality. -/

open Set
namespace DefocusingNLS

theorem spectralTurning_positive_reverse_transfer
    (ell : ℕ) (h b omega gamma r₀ d M E : ℝ)
    (hh : h^2=1) (hb : 0≤b) (hb1 : b≤1) (hr₀ : 2≤r₀) (hd : 0<d) (hM : 32≤M)
    (hMd : M*d≤r₀) (hE : 2*r₀≤E) (hEscale : E^2=256*max ((ell : ℝ)+1) omega)
    (hz : homogeneousSpectralLocalizationFrequency h b ((ell : ℝ)*(ell+10)) omega r₀=0)
    (hscale : spectralLiouvilleSlope ((ell : ℝ)*(ell+10)) r₀*d^3=1)
    (q : ℝ → ℂ × ℂ) (hq : ContinuousOn q (Icc (r₀+M*d) E))
    (hODE : ∀ t ∈ Ioo (r₀+M*d) E, HasDerivAt q
      (spectralScalarField ((homogeneousSpectralLocalizationFrequency h b
        ((ell : ℝ)*(ell+10)) omega t : ℂ)+Complex.I*(gamma : ℂ)) (q t)) t) :
    spectralShellNorm (Real.sqrt ‖spectralLiouvilleMomentum 1 h b
      ((ell : ℝ)*(ell+10)) omega gamma (r₀+M*d)‖) (q (r₀+M*d))≤
      ((25/2 : ℝ)*Real.exp (|gamma| * 288+(25/4)*(5/(3*(Real.sqrt (M/8))^3)+
        3*d/(r₀*Real.sqrt (M/8))+8/r₀^2)))*
      spectralShellNorm (Real.sqrt ‖spectralLiouvilleMomentum 1 h b
        ((ell : ℝ)*(ell+10)) omega gamma E‖) (q E) := by
  let eta : ℝ := (ell : ℝ)*(ell+10)
  let a := r₀+M*d
  let V := fun t => (homogeneousSpectralLocalizationFrequency h b eta omega t : ℂ)+Complex.I*(gamma : ℂ)
  let k := fun t => Real.sqrt ‖spectralLiouvilleMomentum 1 h b eta omega gamma t‖
  let C := (25/4 : ℝ)*Real.exp (|gamma| * 288+(25/4)*(5/(3*(Real.sqrt (M/8))^3)+
    3*d/(r₀*Real.sqrt (M/8))+8/r₀^2))
  have heta : 0≤eta := by dsimp only [eta]; positivity
  have hr₀p : 0<r₀ := by linarith
  have ha : r₀<a := by dsimp only [a]; nlinarith
  have ha0 : 0<a := hr₀p.trans ha
  have haE : a≤E := by dsimp only [a]; linarith
  have hkp (t : ℝ) (ht : t ∈ Icc a E) : 0<k t := by
    apply spectralLiouville_norm_weight_pos 1 h b eta omega gamma t (by norm_num)
    have hh' := homogeneousSpectralLocalizationFrequency_strictMono h b eta omega heta
      hr₀p (ha0.trans_le ht.1) (ha.trans_le ht.1)
    have hz' : homogeneousSpectralLocalizationFrequency h b eta omega r₀=0 := hz
    rw [hz'] at hh'
    exact hh'.ne'
  have hV : ContinuousOn V (Icc a E) := by
    apply ContinuousOn.add _ continuousOn_const
    apply Complex.continuous_ofReal.comp_continuousOn
    intro t ht
    exact (homogeneousSpectralLocalizationFrequency_hasDerivAt h b eta omega t
      (ha0.trans_le ht.1)).continuousAt.continuousWithinAt
  have hfwd (u : ℝ → ℂ × ℂ) (hu : ContinuousOn u (Icc a E))
      (huD : ∀ t ∈ Ioo a E, HasDerivAt u (spectralScalarField (V t) (u t)) t) :
      spectralShellNorm (k E) (u E)≤C*spectralShellNorm (k a) (u a) := by
    have ht := spectralTurning_positive_endpoint_transfer ell h b omega gamma r₀ d M E
      hh hb hb1 hr₀ hd hM hMd hE hEscale hz hscale u hu huD
    convert ht using 1
    dsimp only [C]
    ring
  have ht := spectralScalar_reverse_transfer a E (k a) (k E) C haE
    (hkp a ⟨le_rfl,haE⟩) (hkp E ⟨haE,le_rfl⟩) V hV hfwd q hq hODE
  calc
    _ ≤ (2*C)*spectralShellNorm (k E) (q E) := ht
    _ = _ := by dsimp only [C,k,eta]; ring

end DefocusingNLS

end OAI
