import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteGapSymbol
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteHadamardOperator

namespace OAI

/-! Uniform symbols for the actual, separated remote Sylvester inverse. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralRemote_gap_entries_symbol
    {L : ℕ → ℝ} {c : ℕ → ℝ → Fin 2 → ℝ}
    (hc : HasUniformLogJetBound L 0 c)
    (hsmall : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n), ∀ i, |c n t i| ≤ 1/32) :
    HasUniformLogJetBound L 0
      (fun n t (ij : SpectralRemoteIndex × SpectralRemoteIndex) =>
        spectralRemoteGapMatrix (spectralRemoteDiagonalRoot (c n t)) ij.1 ij.2) := by
  apply HasUniformLogJetBound.pi
  rintro ⟨i,j⟩
  by_cases hij : spectralRemoteBlock i = spectralRemoteBlock j
  · simpa only [spectralRemoteGapMatrix,hij,ite_true] using
      (HasUniformLogJetBound.zero (L := L) 0 :
        HasUniformLogJetBound L 0 (fun _ _ => (0 : ℂ)))
  · simpa only [spectralRemoteGapMatrix,hij,ite_false] using
      (spectralRemote_gap_inverse_symbol hc hsmall i j hij).neg

theorem spectralRemote_sylvester_uniform_symbol
    {L : ℕ → ℝ} {c : ℕ → ℝ → Fin 2 → ℝ} (hL : Tendsto L atTop atTop)
    (hc : HasUniformLogJetBound L 0 c)
    (hsmall : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n), ∀ i, |c n t i| ≤ 1/32) :
    HasUniformLogJetBound L (-2) (fun n t => spectralRemoteSylvesterOperator
      (Real.exp t) (spectralRemoteDiagonalRoot (c n t))) := by
  have hgap := spectralRemote_gap_entries_symbol hc hsmall
  have he : HasUniformLogJetBound L (-2) (fun (_ : ℕ) (t : ℝ) => (Real.exp (-2*t) : ℂ)) := by
    simpa only [Complex.real_smul,mul_one] using
      HasUniformLogJetBound.of_single (HasLogJetBound.exponential (-2) (1 : ℂ)) hL
  have hp : HasUniformLogJetBound L (-2)
      (fun n t => (Real.exp (-2*t) : ℂ) • (fun ij : SpectralRemoteIndex × SpectralRemoteIndex =>
        spectralRemoteGapMatrix (spectralRemoteDiagonalRoot (c n t)) ij.1 ij.2)) := by
    simpa only [add_zero,ContinuousLinearMap.lsmul_apply] using
      he.bilinear hgap (ContinuousLinearMap.lsmul ℝ ℂ)
  have hres := hp.map (B := SpectralRemoteSuperOperator) {
    toFun := fun v => spectralRemoteHadamardOperatorL (fun i j => v (i,j))
    map_add' := by
      intro v w
      change spectralRemoteHadamardOperatorL
        ((fun i j => v (i,j))+(fun i j => w (i,j))) = _
      exact map_add spectralRemoteHadamardOperatorL _ _
    map_smul' := by
      intro a v
      change spectralRemoteHadamardOperatorL (a • (fun i j => v (i,j))) = _
      exact map_smul spectralRemoteHadamardOperatorL _ _
    cont := spectralRemoteHadamardOperatorL.continuous.comp
      (continuous_pi (fun i => continuous_pi (fun j => continuous_apply (i,j)))) }
  have hident (t : ℝ) : (((Real.exp t : ℝ) : ℂ)^2)⁻¹ = (Real.exp (-2*t) : ℂ) := by
    norm_cast
    rw [← Real.exp_nat_mul,← Real.exp_neg]
    congr 1
    norm_num
  convert hres using 1
  funext n t
  rw [spectralRemoteSylvesterOperator_hadamard,hident]
  rfl

end DefocusingNLS

end OAI
