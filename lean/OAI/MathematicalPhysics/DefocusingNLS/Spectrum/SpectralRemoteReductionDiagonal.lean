import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteFiniteReduction

namespace OAI

/-! The bounded diagonal part changes by only two inverse powers. Thus its
leading bound can be fixed before choosing the finite reduction order. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralRemote_reduction_diagonal_symbol
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop)
    (Lambda B : ℕ → ℝ → SpectralRemoteOperator)
    (P : SpectralRemoteSuperOperator) (K : ℕ → ℝ → SpectralRemoteSuperOperator)
    (hP : ∀ X, P (P X) = P X) (hB : HasUniformLogJetBound L 0 B)
    (hK : HasUniformLogJetBound L (-2) K)
    (hcomm : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n), ∀ X,
      Lambda n t*K n t X-K n t X*Lambda n t = P X-X)
    (m : ℕ) :
    HasUniformLogJetBound L (-2) (fun n t =>
      (spectralRemoteReductionData Lambda B P K (m+1)).1 n t-P (B n t)) := by
  induction m with
  | zero =>
      simpa only [spectralRemoteReductionData,zero_add,sub_self] using
        (HasUniformLogJetBound.zero (L := L) (-2) :
          HasUniformLogJetBound L (-2) (fun _ _ => (0 : SpectralRemoteOperator)))
  | succ m ih =>
      have hr := (spectralRemote_finite_reduction hL Lambda B P K hP hB hK hcomm (m+1)).2.1
      have hr' := hr.mono hL (show -2*((m+1 : ℕ) : ℝ) ≤ -2 by
        push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) m])
      have hp := ih.add (hr'.map P)
      convert hp using 1
      funext n t
      change (spectralRemoteReductionData Lambda B P K (m+1)).1 n t+
          P ((spectralRemoteReductionData Lambda B P K (m+1)).2 n t)-P (B n t) = _
      abel

end DefocusingNLS

end OAI
