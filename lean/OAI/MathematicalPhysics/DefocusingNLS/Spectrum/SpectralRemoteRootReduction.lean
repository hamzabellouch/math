import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteSylvesterSymbol
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteFrameInverse

namespace OAI

/-! Finite block reduction for the actual remote leading roots. The
Sylvester equations and all uniform derivative bounds are discharged here. -/

open Set Filter Topology
namespace DefocusingNLS

noncomputable def spectralRemoteLeadingOperator (c : Fin 2 → ℝ) (t : ℝ) :
    SpectralRemoteOperator :=
  spectralRemoteMatrixOperator (Matrix.diagonal
    (fun i => (Real.exp t : ℂ)^2*spectralRemoteDiagonalRoot c i))

theorem spectralRemote_root_sylvester
    {L : ℕ → ℝ} {c : ℕ → ℝ → Fin 2 → ℝ}
    (hsmall : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n), ∀ i, |c n t i| ≤ 1/32) :
    ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n), ∀ X : SpectralRemoteOperator,
      spectralRemoteLeadingOperator (c n t) t*
        spectralRemoteSylvesterOperator (Real.exp t) (spectralRemoteDiagonalRoot (c n t)) X-
      spectralRemoteSylvesterOperator (Real.exp t) (spectralRemoteDiagonalRoot (c n t)) X*
        spectralRemoteLeadingOperator (c n t) t = spectralRemoteBlockOperator X-X := by
  filter_upwards [hsmall] with n hn
  intro t ht X
  exact spectralRemoteSylvesterOperator_commutator (Real.exp t) (Real.exp_pos t).ne'
    (spectralRemoteDiagonalRoot (c n t))
    (fun i j hij => sub_ne_zero.mp (norm_pos_iff.mp
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/4)
        (spectralRemote_block_gap (c n t) (hn t ht) i j hij)))) X

theorem spectralRemote_root_reduction
    {L : ℕ → ℝ} {c : ℕ → ℝ → Fin 2 → ℝ} (hL : Tendsto L atTop atTop)
    (hc : HasUniformLogJetBound L 0 c)
    (hsmall : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n), ∀ i, |c n t i| ≤ 1/32)
    (B : ℕ → ℝ → SpectralRemoteOperator) (hB : HasUniformLogJetBound L 0 B) (m : ℕ) :
    let Lambda := fun n t => spectralRemoteLeadingOperator (c n t) t
    let K := fun n t => spectralRemoteSylvesterOperator (Real.exp t) (spectralRemoteDiagonalRoot (c n t))
    let d := spectralRemoteReductionData Lambda B spectralRemoteBlockOperator K m
    let T := spectralRemoteReductionFrame Lambda B spectralRemoteBlockOperator K m
    HasUniformLogJetBound L 0 d.1 ∧
    HasUniformLogJetBound L (-2*(m : ℝ)) d.2 ∧
    HasUniformLogJetBound L (-2) (fun n t => T n t-1) ∧
    HasUniformLogJetBound L 0 (fun n t => Ring.inverse (T n t)) ∧
    (∀ᶠ n in atTop, ∀ t ∈ Ioi (L n),
      spectralRemoteBlockOperator (d.1 n t) = d.1 n t ∧
      IsUnit (T n t) ∧ ‖T n t‖ ≤ 2 ∧ ‖Ring.inverse (T n t)‖ ≤ 2 ∧
      HasDerivAt (T n) ((Lambda n t+B n t)*T n t-T n t*(Lambda n t+d.1 n t+d.2 n t)) t) := by
  dsimp only
  let Lambda := fun n t => spectralRemoteLeadingOperator (c n t) t
  let K := fun n t => spectralRemoteSylvesterOperator (Real.exp t) (spectralRemoteDiagonalRoot (c n t))
  have hK := spectralRemote_sylvester_uniform_symbol hL hc hsmall
  have hcomm := spectralRemote_root_sylvester hsmall
  have hd := spectralRemote_finite_reduction hL Lambda B spectralRemoteBlockOperator K
    spectralRemoteBlockOperator_idempotent hB hK hcomm m
  have hframe := spectralRemote_reduction_frame_symbol hL Lambda B spectralRemoteBlockOperator K
    spectralRemoteBlockOperator_idempotent hB hK hcomm m
  have hinv := spectralRemote_reduction_frame_inverse_symbol hL Lambda B spectralRemoteBlockOperator K
    spectralRemoteBlockOperator_idempotent hB hK hcomm m
  have hu := spectralRemote_reduction_frame_inverse hL Lambda B spectralRemoteBlockOperator K
    spectralRemoteBlockOperator_idempotent hB hK hcomm m
  have he := spectralRemote_reduction_frame_equation hL Lambda B spectralRemoteBlockOperator K
    spectralRemoteBlockOperator_idempotent hB hK hcomm m
  refine ⟨hd.1,hd.2.1,hframe,hinv,?_⟩
  filter_upwards [hd.2.2,hu,he] with n hn hun hen
  intro t ht
  exact ⟨hn t ht,(hun t ht).1,(hun t ht).2.1,(hun t ht).2.2,hen t ht⟩

end DefocusingNLS

end OAI
