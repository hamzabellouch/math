import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteInitialEquation
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteFrameBounds

namespace OAI

/-! Finite reduction applied to solutions of the physical four-coordinate system. -/

open Set Filter Topology
namespace DefocusingNLS

noncomputable def spectralRemotePhysicalReducedSolution
    (c : ℕ → ℝ → Fin 2 → ℝ) (B : ℕ → ℝ → SpectralRemoteOperator)
    (Y : ℕ → ℝ → SpectralRemoteSpace) (m n : ℕ) (t : ℝ) : SpectralRemoteSpace :=
  let Lambda := fun n t => spectralRemoteLeadingOperator (c n t) t
  let K := fun n t => spectralRemoteSylvesterOperator (Real.exp t) (spectralRemoteDiagonalRoot (c n t))
  let B' := spectralRemoteInitialRemainder c B
  let T := spectralRemoteReductionFrame Lambda B' spectralRemoteBlockOperator K m
  Ring.inverse (T n t) (Ring.inverse (spectralRemoteInitialFrame (c n t)) (Y n t))

theorem spectralRemote_physical_reduced_equation
    {L : ℕ → ℝ} {c : ℕ → ℝ → Fin 2 → ℝ} (hL : Tendsto L atTop atTop)
    (B : ℕ → ℝ → SpectralRemoteOperator) (Y : ℕ → ℝ → SpectralRemoteSpace)
    (hc : HasUniformLogJetBound L 0 c)
    (hsmall : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n), ∀ i, |c n t i| ≤ 1/32)
    (hB : HasUniformLogJetBound L 0 B) (m : ℕ) :
    let Lambda := fun n t => spectralRemoteLeadingOperator (c n t) t
    let K := fun n t => spectralRemoteSylvesterOperator (Real.exp t) (spectralRemoteDiagonalRoot (c n t))
    let B' := spectralRemoteInitialRemainder c B
    let d := spectralRemoteReductionData Lambda B' spectralRemoteBlockOperator K m
    let Z := spectralRemotePhysicalReducedSolution c B Y m
    ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n),
      HasDerivAt (Y n) (((Real.exp t : ℂ)^2 • spectralRemotePhysicalLeading (c n t)+B n t) (Y n t)) t →
      HasDerivAt (Z n) ((Lambda n t+d.1 n t+d.2 n t) (Z n t)) t := by
  dsimp only
  let Lambda := fun n t => spectralRemoteLeadingOperator (c n t) t
  let K := fun n t => spectralRemoteSylvesterOperator (Real.exp t) (spectralRemoteDiagonalRoot (c n t))
  let B' := spectralRemoteInitialRemainder c B
  let T := spectralRemoteReductionFrame Lambda B' spectralRemoteBlockOperator K m
  have hB' := spectralRemote_initial_remainder_symbol hc hsmall hB
  have hred := (spectralRemote_root_reduction hL hc hsmall B' hB' m).2.2.2.2
  have hP := (spectralRemote_initial_frame_symbols hc hsmall).1.smooth
  filter_upwards [hred,hP,hsmall] with n hn hPn hcn
  intro t ht hY
  have hdP : DifferentiableAt ℝ (fun s => spectralRemoteInitialFrame (c n s)) t :=
    ((hPn t ht).contDiffAt (Ioi_mem_nhds ht)).differentiableAt (by simp)
  have hfirst := spectralRemote_initial_solution c B (Y n) n t (hcn t ht) hdP hY
  exact spectralRemote_intertwining_solution (T n)
    (fun s => Ring.inverse (spectralRemoteInitialFrame (c n s)) (Y n s))
    (Lambda n t+B' n t) _ t (hn t ht).2.1 (hn t ht).2.2.2.2 hfirst

end DefocusingNLS

end OAI
