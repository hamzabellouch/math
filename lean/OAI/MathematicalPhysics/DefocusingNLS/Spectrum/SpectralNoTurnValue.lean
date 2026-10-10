import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNoTurnErrorLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleBranchData
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralBranchCloseness

namespace OAI

/-! A small explicit no-turn error gives a uniform nonzero outgoing value
and controls its logarithmic slope. -/

open Set
namespace DefocusingNLS

theorem spectralNoTurn_outgoing_value
    (b eta omega gamma C R E : ℝ)
    (hb : 0 ≤ b) (heta : 0 ≤ eta) (hw : 0 < omega) (hC : 0 ≤ C) (hCw : C ≤ omega)
    (hR : 0 < R) (hRE : R ≤ E) (hE : 0 < E) (hEs : E^2 = 256*omega)
    (hL : eta+99/4 ≤ C*omega) (hCR : 2*C ≤ R^2)
    (hgamma : |gamma| ≤ 8) (hEbound : E ≤ 32*Real.sqrt (omega/2))
    (hlarge : 2/R+4*C/R^3 ≤ 2*Real.sqrt (omega/2))
    (hgF : |gamma| ≤ homogeneousSpectralLocalizationFrequency (-1) b eta omega E)
    (herrSmall : spectralNoTurnBranchError C R omega E ≤ Real.exp (-256)/2)
    (q : ℝ → ℂ × ℂ) (hq : ContinuousOn q (Icc R E))
    (hqE : q E = spectralOscillatoryData (-1)
      (Real.sqrt (Real.sqrt (homogeneousSpectralLocalizationFrequency (-1) b eta omega E))))
    (hODE : ∀ t ∈ Ioo R E, HasDerivAt q
      (spectralScalarField ((homogeneousSpectralLocalizationFrequency (-1) b eta omega t : ℂ)+
        Complex.I*(gamma : ℂ)) (q t)) t) :
    let p := spectralLiouvilleMomentum 1 (-1) b eta omega gamma R
    let L := homogeneousSpectralWKBLog (-Complex.I) p ((spectralLiouvilleSlope eta R : ℂ)/(2*p))
    Real.exp (-256)/2 ≤ Real.sqrt ‖p‖*‖(q R).1‖ ∧ (q R).1 ≠ 0 ∧
      ‖(q R).2/(q R).1-L‖ ≤
        (5*spectralNoTurnBranchError C R omega E/Real.exp (-256))*‖p‖ := by
  let p := spectralLiouvilleMomentum 1 (-1) b eta omega gamma
  let v := fun t => (spectralLiouvilleSlope eta t : ℂ)/(2*p t)
  let D := spectralWKBFrame R (-Complex.I) p v
  let z := (q E).1/(D E).1
  let k := Real.sqrt ‖p R‖
  let err := spectralNoTurnBranchError C R omega E
  have hF (t : ℝ) (ht : t ∈ Icc R E) :
      0 < homogeneousSpectralLocalizationFrequency (-1) b eta omega t :=
    lt_of_lt_of_le (by positivity) (spectralNoTurn_frequency_lower b eta omega C R t hb hw hR ht.1 hL hCR)
  have hsm (t : ℝ) (ht : t ∈ Icc R E) := spectralNoTurn_derivative_small b eta omega gamma C R t
    hb heta hw hC hR ht.1 hL hCR hlarge
  have hp := spectralLiouville_positive_phase_bound (-1) b eta omega gamma R E 32 hR hRE
    (-Complex.I) (by simp only [norm_neg,Complex.norm_I])
    (by simp only [Complex.neg_re,Complex.I_re,neg_zero]) hF
    (spectralNoTurn_phase_bound b eta omega C R E 32 hb hw hR hRE hL hCR hEbound)
  have hdat := spectralLiouville_outgoing_branch_data (-1) b eta omega gamma R E 256
    (by norm_num) hR hRE hF (hsm R ⟨le_rfl,hRE⟩)
    (by simpa only [Complex.ofReal_neg,Complex.ofReal_one,neg_mul,one_mul] using
      (hp E ⟨hRE,le_rfl⟩).trans (by linarith : |gamma| *32 ≤ 256)) hgF
  have hz : Real.exp (-256) ≤ ‖z‖ := by
    simpa only [z,hqE,D,p,v,Complex.ofReal_neg,Complex.ofReal_one,neg_mul,one_mul] using hdat.1.1
  have hDn : k*‖(D R).1‖ = 1 := by
    simpa only [D,k,p,v,Complex.ofReal_neg,Complex.ofReal_one,neg_mul,one_mul] using hdat.2.1
  have hLn : ‖homogeneousSpectralWKBLog (-Complex.I) (p R) (v R)‖ ≤ (3/2 : ℝ)*k^2 := by
    rw [Real.sq_sqrt (norm_nonneg _)]
    simpa only [p,v,Complex.ofReal_neg,Complex.ofReal_one,neg_mul,one_mul] using hdat.2.2
  have hNE : spectralShellNorm (Real.sqrt ‖p E‖) (q E) ≤ 3 := by
    rw [hqE]
    simpa only [p,spectralLiouvilleMomentum,spectralWKBSquaredMomentum,Complex.ofReal_one,one_mul] using
      spectralOscillatoryData_complex_norm (-1) (homogeneousSpectralLocalizationFrequency (-1) b eta omega E)
        gamma (by norm_num) (hF E ⟨hRE,le_rfl⟩) hgF
  have he := spectralNoTurn_outgoing_branch_error b eta omega gamma C R E hb heta hw hC hCw
    hR hRE hE hEs hL hCR hgamma hEbound hlarge q hq hqE hODE
  have hJ : 0 ≤ spectralNoTurnResidualBound C R omega := by
    dsimp only [spectralNoTurnResidualBound]
    positivity
  let B0 : ℝ := (5/2)*Real.exp 256
  let J0 := spectralNoTurnResidualBound C R omega
  change spectralShellNorm k (q R-z • D R) ≤
    (2*(B0^2)^2*Real.exp (B0^2*J0)*J0)*spectralShellNorm (Real.sqrt ‖p E‖) (q E)+
      B0^2*((32*|gamma|+8)/E^2) at he
  have hc0 : 0 ≤ 2*(B0^2)^2*Real.exp (B0^2*J0)*J0 := by
    dsimp only [J0]
    positivity
  have hmismatch : B0^2*((32*|gamma|+8)/E^2) ≤ B0^2*(264/E^2) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith) (sq_nonneg E)) (sq_nonneg B0)
  have herr : spectralShellNorm k (q R-z • D R) ≤ err := by
    apply he.trans
    apply (add_le_add (mul_le_mul_of_nonneg_left hNE hc0) hmismatch).trans_eq
    dsimp only [err,spectralNoTurnBranchError,B0,J0]
    ring
  have he0 : 0 ≤ err := (spectralShellNorm_nonneg k (Real.sqrt_nonneg _) _).trans herr
  have hk : 0 < k := spectralLiouville_norm_weight_pos 1 (-1) b eta omega gamma R
    (by norm_num) (hF R ⟨le_rfl,hRE⟩).ne'
  obtain ⟨hval,hq0⟩ := spectralBranch_value_lower k (Real.exp (-256)) err hk (Real.exp_pos _)
    herrSmall (q R) (D R) z hDn hz herr
  have hlog := (spectralBranch_logarithmic_bound k (3/2) (Real.exp (-256)) err hk (by norm_num)
    (Real.exp_pos _) he0 herrSmall (q R) (D R) z
    (homogeneousSpectralWKBLog (-Complex.I) (p R) (v R)) hDn hz rfl hLn herr).2
  refine ⟨hval,hq0,?_⟩
  convert hlog using 1
  rw [show 2*(1+(3/2 : ℝ)) = 5 by norm_num,Real.sq_sqrt (norm_nonneg _)]

end DefocusingNLS

end OAI
