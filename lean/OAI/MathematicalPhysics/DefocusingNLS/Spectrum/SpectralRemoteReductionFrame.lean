import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteFiniteReduction

namespace OAI

/-! The finite product of the remote near-identity changes. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS

noncomputable def spectralRemoteReductionChange
    (Lambda B : ℕ → ℝ → SpectralRemoteOperator)
    (P : SpectralRemoteSuperOperator) (K : ℕ → ℝ → SpectralRemoteSuperOperator)
    (m n : ℕ) (t : ℝ) : SpectralRemoteOperator :=
  K n t ((spectralRemoteReductionData Lambda B P K m).2 n t)

noncomputable def spectralRemoteReductionFrame
    (Lambda B : ℕ → ℝ → SpectralRemoteOperator)
    (P : SpectralRemoteSuperOperator) (K : ℕ → ℝ → SpectralRemoteSuperOperator) :
    ℕ → ℕ → ℝ → SpectralRemoteOperator
  | 0 => fun _ _ => 1
  | m+1 => fun n t => spectralRemoteReductionFrame Lambda B P K m n t *
    (1+spectralRemoteReductionChange Lambda B P K m n t)

theorem spectralRemote_reduction_change_symbol
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop)
    (Lambda B : ℕ → ℝ → SpectralRemoteOperator)
    (P : SpectralRemoteSuperOperator) (K : ℕ → ℝ → SpectralRemoteSuperOperator)
    (hP : ∀ X, P (P X) = P X) (hB : HasUniformLogJetBound L 0 B)
    (hK : HasUniformLogJetBound L (-2) K)
    (hcomm : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n), ∀ X,
      Lambda n t*K n t X-K n t X*Lambda n t = P X-X)
    (m : ℕ) :
    HasUniformLogJetBound L (-2*((m+1 : ℕ) : ℝ))
      (spectralRemoteReductionChange Lambda B P K m) := by
  have hr := (spectralRemote_finite_reduction hL Lambda B P K hP hB hK hcomm m).2.1
  have hs := hK.apply hr
  have he : (-2 : ℝ)+(-2*(m : ℝ)) = -2*((m+1 : ℕ) : ℝ) := by push_cast; ring
  unfold spectralRemoteReductionChange
  rw [← he]
  exact hs

theorem spectralRemote_reduction_frame_symbol
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop)
    (Lambda B : ℕ → ℝ → SpectralRemoteOperator)
    (P : SpectralRemoteSuperOperator) (K : ℕ → ℝ → SpectralRemoteSuperOperator)
    (hP : ∀ X, P (P X) = P X) (hB : HasUniformLogJetBound L 0 B)
    (hK : HasUniformLogJetBound L (-2) K)
    (hcomm : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n), ∀ X,
      Lambda n t*K n t X-K n t X*Lambda n t = P X-X)
    (m : ℕ) :
    HasUniformLogJetBound L (-2)
      (fun n t => spectralRemoteReductionFrame Lambda B P K m n t-1) := by
  induction m with
  | zero => simpa [spectralRemoteReductionFrame] using
      (HasUniformLogJetBound.zero (L := L) (-2) :
        HasUniformLogJetBound L (-2) (fun _ _ => (0 : SpectralRemoteOperator)))
  | succ m ih =>
      have hs := (spectralRemote_reduction_change_symbol hL Lambda B P K hP hB hK hcomm m).mono hL
        (show -2*((m+1 : ℕ) : ℝ) ≤ -2 by push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) m])
      have ht : HasUniformLogJetBound L 0 (spectralRemoteReductionFrame Lambda B P K m) := by
        have hh := (HasUniformLogJetBound.const (L := L) (1 : SpectralRemoteOperator)).add
          (ih.mono hL (by norm_num))
        convert hh using 1
        funext n t
        abel
      have hp : HasUniformLogJetBound L (-2) (fun n t =>
          spectralRemoteReductionFrame Lambda B P K m n t*
            spectralRemoteReductionChange Lambda B P K m n t) := by
        simpa only [zero_add] using ht.mul hs
      have hh : HasUniformLogJetBound L (-2) (fun n t =>
          (spectralRemoteReductionFrame Lambda B P K m n t-1)+
            spectralRemoteReductionFrame Lambda B P K m n t*
              spectralRemoteReductionChange Lambda B P K m n t) := by
        exact ih.add hp
      convert hh using 1
      funext n t
      simp only [spectralRemoteReductionFrame,mul_add,mul_one]
      abel

end DefocusingNLS

end OAI
