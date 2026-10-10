import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBTerminalError
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBFrameValue
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFrameBranch

namespace OAI

/-! Separate the selected WKB branch from the true solution. The two errors
are the integrated residual and the mismatch of the prescribed terminal data. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralWKB_single_branch_error
    (R E B J eps : ℝ) (hRE : R ≤ E) (chi : ℂ) (hchi : ‖chi‖ = 1)
    (p v w : ℝ → ℂ) (q : ℝ → ℂ × ℂ) (k : ℝ → ℝ)
    (hp : ContinuousOn p (Icc R E)) (hv : ContinuousOn v (Icc R E))
    (hw : ContinuousOn w (Icc R E)) (hq : ContinuousOn q (Icc R E))
    (hk : ContinuousOn k (Icc R E)) (hk0 : ∀ r ∈ Icc R E, 0 < k r)
    (hkp : ∀ r ∈ Icc R E, (k r)^2 = ‖p r‖)
    (hpD : ∀ r ∈ Ioo R E, HasDerivAt p (v r) r)
    (hvD : ∀ r ∈ Ioo R E, HasDerivAt v (w r) r)
    (hsmall : ∀ r ∈ Icc R E, ‖v r‖ ≤ ‖p r‖^2)
    (hphase : ∀ r ∈ Icc R E, |(spectralWKBPhase R chi p r).re| ≤ B)
    (hJ : (∫ r in R..E, ‖homogeneousSpectralWKBResidual (p r) (v r) (w r)‖/(k r)^2) ≤ J)
    (hODE : ∀ r ∈ Ioo R E, HasDerivAt q (spectralScalarField (-chi^2*(p r)^2) (q r)) r)
    (hend : spectralShellNorm (k E) (q E -
      ((q E).1/(spectralWKBFrame R chi p v E).1) • spectralWKBFrame R chi p v E) ≤ eps) :
    let D := spectralWKBFrame R chi p v
    let C := (5/2 : ℝ)*Real.exp B
    spectralShellNorm (k R) (q R - ((q E).1/(D E).1) • D R) ≤
      (2*(C^2)^2*Real.exp (C^2*J)*J)*spectralShellNorm (k E) (q E) + C^2*eps := by
  dsimp only
  let D := spectralWKBFrame R chi p v
  let U := spectralWKBFrame R (-chi) p v
  let C := (5/2 : ℝ)*Real.exp B
  let W := (-2 : ℂ)*chi
  let z := (q E).1/(D E).1
  let P := spectralFrameTransfer D U W R E (q E)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hp0 (r : ℝ) (hr : r ∈ Icc R E) : p r ≠ 0 := by
    apply norm_pos_iff.mp
    rw [← hkp r hr]
    exact sq_pos_of_pos (hk0 r hr)
  have hN (sig : ℂ) (hsig : ‖sig‖ = 1)
      (hS : ∀ r ∈ Icc R E, (spectralWKBPhase R sig p r).re ≤ B)
      (r : ℝ) (hr : r ∈ Icc R E) :
      spectralShellNorm (k r) (spectralWKBFrame R sig p v r) ≤ C := by
    have hb := spectralWKBState_shell_bound sig (p r) (v r)
      (spectralWKBAmplitude R (spectralWKBInitialAmplitude (p R)) p v r)
      (spectralWKBPhase R sig p r) (k r) (hk0 r hr) (hkp r hr)
      (spectralWKBAmplitude_normalization R E hRE _ p v hp hv hp0 hpD
        (spectralWKBInitialAmplitude_normalization (p R) (hp0 R ⟨le_rfl,hRE⟩)) r hr)
      hsig.le (hsmall r hr)
    exact hb.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hS r hr)) (by norm_num))
  have hDb (r : ℝ) (hr : r ∈ Icc R E) : spectralShellNorm (k r) (D r) ≤ C :=
    hN chi hchi (fun t ht => (le_abs_self _).trans (hphase t ht)) r hr
  have hUb (r : ℝ) (hr : r ∈ Icc R E) : spectralShellNorm (k r) (U r) ≤ C := by
    apply hN (-chi) (by simpa only [norm_neg] using hchi) _ r hr
    intro t ht
    have he : (spectralWKBPhase R (-chi) p t).re = -(spectralWKBPhase R chi p t).re := by
      simp only [spectralWKBPhase,neg_mul,Complex.neg_re]
    rw [he]
    exact (neg_le_abs _).trans (hphase t ht)
  have hWnorm : ‖W‖ = 2 := by dsimp only [W]; rw [norm_mul,hchi,mul_one]; norm_num
  have hWe : W ≠ 0 := norm_ne_zero_iff.mp (by rw [hWnorm]; norm_num)
  have hdet : spectralScalarWronskian (D E) (U E) = W :=
    spectralWKBFrame_wronskian R E hRE chi p v hp hv hp0 hpD E ⟨hRE,le_rfl⟩
  have hterm : spectralShellNorm (k R) (P-z • D R) ≤ C^2*eps := by
    rw [← spectralFrameTransfer_sub_branch D U W R E (q E) z hWe hdet]
    have hb := spectralScalarInitialTerm_bound D U W (q E-z • D E)
      (k R) (k E) C 2 0 0 R E (hk0 R ⟨le_rfl,hRE⟩).le (hk0 E ⟨hRE,le_rfl⟩) hC
      (by norm_num) (by rw [hWnorm])
      (by simpa using hDb R ⟨le_rfl,hRE⟩) (by simpa using hDb E ⟨hRE,le_rfl⟩)
      (by simpa using hUb R ⟨le_rfl,hRE⟩) (by simpa using hUb E ⟨hRE,le_rfl⟩)
    have hb' : spectralShellNorm (k R) (spectralFrameTransfer D U W R E (q E-z • D E)) ≤
        C^2*spectralShellNorm (k E) (q E-z • D E) := by
      simpa only [spectralFrameTransfer,sub_self,abs_zero,Real.exp_zero,mul_one,show 2*C^2/2=C^2 by ring] using hb
    exact hb'.trans (mul_le_mul_of_nonneg_left hend (sq_nonneg C))
  have herr := spectralWKB_terminal_error R E B J hRE chi hchi p v w q k
    hp hv hw hq hk hk0 hkp hpD hvD hsmall hphase hJ hODE
  have heq : q R-z • D R = (q R-P)+(P-z • D R) := by abel
  rw [heq]
  exact (spectralShellNorm_add_le (k R) (hk0 R ⟨le_rfl,hRE⟩).le _ _).trans (add_le_add herr hterm)

end DefocusingNLS

end OAI
