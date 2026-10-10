import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningOutgoingBranch
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleBranchMargin
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarFluxLower

namespace OAI

/-! An explicit flux lower bound for the actual normalized outgoing solution
at the positive turning cutoff. The error tends to zero first in the fixed
cutoff and then along the escaping parameter sequence. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralTurning_outgoing_flux_lower
    (ell : ℕ) (h b omega gamma r₀ d M E : ℝ)
    (hh : h^2 = 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) (hr₀ : 16 ≤ r₀) (hd : 0 < d) (hM : 32 ≤ M)
    (hMd : M*d ≤ r₀) (hE : 2*r₀ ≤ E) (hEscale : E^2 = 256*max ((ell : ℝ)+1) omega)
    (hgamma : |gamma| ≤ 8)
    (hz : homogeneousSpectralLocalizationFrequency h b ((ell : ℝ)*(ell+10)) omega r₀ = 0)
    (hscale : spectralLiouvilleSlope ((ell : ℝ)*(ell+10)) r₀*d^3 = 1)
    (q : ℝ → ℂ × ℂ) (hq : ContinuousOn q (Icc (r₀+M*d) E))
    (hqE : q E = spectralOscillatoryData h (Real.sqrt (Real.sqrt
      (homogeneousSpectralLocalizationFrequency h b ((ell : ℝ)*(ell+10)) omega E))))
    (hODE : ∀ t ∈ Ioo (r₀+M*d) E, HasDerivAt q
      (spectralScalarField ((homogeneousSpectralLocalizationFrequency h b
        ((ell : ℝ)*(ell+10)) omega t : ℂ)+Complex.I*(gamma : ℂ)) (q t)) t) :
    let B := |gamma| * 288
    let C := (5/2 : ℝ)*Real.exp B
    let J := 5/(3*(Real.sqrt (M/8))^3)+3*d/(r₀*Real.sqrt (M/8))+8/r₀^2
    let delta := (6*(C^2)^2*Real.exp (C^2*J)*J)+C^2*((32*|gamma|+8)/E^2)
    (Real.exp (-B))^2/6 - delta*(10*Real.exp B+delta) ≤
      h*spectralScalarFlux (q (r₀+M*d)) := by
  dsimp only
  let eta : ℝ := (ell : ℝ)*(ell+10)
  let a := r₀+M*d
  let p := spectralLiouvilleMomentum 1 h b eta omega gamma
  let v := fun t => (spectralLiouvilleSlope eta t : ℂ)/(2*p t)
  let k := fun t => Real.sqrt ‖p t‖
  let B := |gamma| * 288
  let C := (5/2 : ℝ)*Real.exp B
  let J := 5/(3*(Real.sqrt (M/8))^3)+3*d/(r₀*Real.sqrt (M/8))+8/r₀^2
  let delta := (6*(C^2)^2*Real.exp (C^2*J)*J)+C^2*((32*|gamma|+8)/E^2)
  let D := spectralWKBFrame a ((h : ℂ)*Complex.I) p v
  let z := (q E).1/(D E).1
  have heta : 0 ≤ eta := by dsimp only [eta]; positivity
  have hr₀p : 0 < r₀ := by linarith
  have hMp : 0 < M := by linarith
  have ha : r₀ < a := by dsimp only [a]; nlinarith
  have ha0 : 0 < a := hr₀p.trans ha
  have haE : a ≤ E := by dsimp only [a]; linarith
  have hEpos : 0 < E := by linarith
  have hF (t : ℝ) (ht : t ∈ Icc a E) :
      0 < homogeneousSpectralLocalizationFrequency h b eta omega t := by
    have hf := homogeneousSpectralLocalizationFrequency_strictMono h b eta omega heta
      hr₀p (ha0.trans_le ht.1) (ha.trans_le ht.1)
    simpa only [eta,hz] using hf
  have hsmall (t : ℝ) (ht : t ∈ Icc a E) : |spectralLiouvilleSlope eta t| ≤ 2*‖p t‖^3 :=
    spectralTurning_positive_derivative_small 1 h b eta omega gamma r₀ d M t
      (by norm_num) heta (by linarith) hd hM ht.1 hz hscale
  have hFar := spectralTurning_far_geometry h b eta omega r₀ E heta hr₀p hE hz
  have hgammaFar : |gamma| ≤ homogeneousSpectralLocalizationFrequency h b eta omega E := by
    nlinarith
  have hnormE : spectralShellNorm (k E) (q E) ≤ 3 := by
    rw [hqE]
    simpa only [k,p,spectralLiouvilleMomentum,spectralWKBSquaredMomentum,Complex.ofReal_one,one_mul] using
      spectralOscillatoryData_complex_norm h (homogeneousSpectralLocalizationFrequency h b eta omega E)
        gamma hh (hF E ⟨haE,le_rfl⟩) hgammaFar
  have hA : (∫ t in a..E, 1/Real.sqrt (homogeneousSpectralLocalizationFrequency h b eta omega t)) ≤ 288 :=
    spectralTurning_positive_outer_phase ell h b omega r₀ d M E
      hh hb hb1 hr₀p hd hMp hMd hE hEscale hz
  have hchi : ‖(h : ℂ)*Complex.I‖ = 1 := by
    have hha : |h| = 1 := by nlinarith [sq_abs h,abs_nonneg h]
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,hha,Complex.norm_I,mul_one]
  have hchire : ((h : ℂ)*Complex.I).re = 0 := by simp
  have hphase := spectralLiouville_positive_phase_bound h b eta omega gamma a E 288 ha0 haE
    ((h : ℂ)*Complex.I) hchi hchire hF hA
  have hbranch := spectralLiouville_outgoing_branch_margin h b eta omega gamma a E B hh ha0 haE hF
    (hsmall a ⟨le_rfl,haE⟩) (hphase E ⟨haE,le_rfl⟩) hgammaFar
  dsimp only at hbranch
  rw [← hqE] at hbranch
  change (Real.exp (-B))^2/6 ≤ h*spectralScalarFlux (z • D a) ∧
    spectralShellNorm (k a) (z • D a) ≤ 5*Real.exp B at hbranch
  have herr := spectralTurning_positive_branch_error ell h b omega gamma r₀ d M E hh hb hb1
    (by linarith) hd hM hMd hE hEscale hz hscale q hq hqE hODE
  change spectralShellNorm (k a) (q a-z • D a) ≤
    (2*(C^2)^2*Real.exp (C^2*J)*J)*spectralShellNorm (k E) (q E) +
      C^2*((32*|gamma|+8)/E^2) at herr
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  have hclose : spectralShellNorm (k a) (q a-z • D a) ≤ delta := by
    apply herr.trans
    calc
      _ ≤ (2*(C^2)^2*Real.exp (C^2*J)*J)*3 + C^2*((32*|gamma|+8)/E^2) :=
        add_le_add (mul_le_mul_of_nonneg_left hnormE (by positivity)) le_rfl
      _ = delta := by dsimp only [delta]; ring
  have hk : 0 < k a := by
    apply Real.sqrt_pos.mpr
    apply lt_of_lt_of_le (Real.sqrt_pos.mpr (hF a ⟨le_rfl,haE⟩))
    simpa only [p,spectralLiouvilleMomentum,abs_of_pos (hF a ⟨le_rfl,haE⟩)] using
      spectralWKBSqrt_frequency_lower 1 (homogeneousSpectralLocalizationFrequency h b eta omega a)
        gamma (by norm_num)
  have hqa : spectralShellNorm (k a) (q a) ≤ delta+5*Real.exp B := by
    have he : q a = (q a-z • D a)+z • D a := by abel
    calc
      _ ≤ spectralShellNorm (k a) (q a-z • D a)+spectralShellNorm (k a) (z • D a) := by
        conv_lhs => rw [he]
        exact spectralShellNorm_add_le (k a) hk.le _ _
      _ ≤ _ := add_le_add hclose hbranch.2
  have hf := spectralScalarFlux_lower_of_close h (k a) ((Real.exp (-B))^2/6)
    (delta+5*Real.exp B) (5*Real.exp B) delta (q a) (z • D a)
    hh hk hbranch.1 hqa hbranch.2 hclose
  convert hf using 1; dsimp only [B,C,J,delta,a]; ring

end DefocusingNLS

end OAI
