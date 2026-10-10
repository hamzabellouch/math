import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteFrameEquation

namespace OAI

/-! Uniform invertibility of the constructed finite change of variables. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralRemote_reduction_frame_inverse
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop)
    (Lambda B : ℕ → ℝ → SpectralRemoteOperator)
    (P : SpectralRemoteSuperOperator) (K : ℕ → ℝ → SpectralRemoteSuperOperator)
    (hP : ∀ X, P (P X) = P X) (hB : HasUniformLogJetBound L 0 B)
    (hK : HasUniformLogJetBound L (-2) K)
    (hcomm : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n), ∀ X,
      Lambda n t*K n t X-K n t X*Lambda n t = P X-X)
    (m : ℕ) :
    ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n),
      IsUnit (spectralRemoteReductionFrame Lambda B P K m n t) ∧
      ‖spectralRemoteReductionFrame Lambda B P K m n t‖ ≤ 2 ∧
      ‖Ring.inverse (spectralRemoteReductionFrame Lambda B P K m n t)‖ ≤ 2 := by
  have hs := spectralRemote_reduction_frame_symbol hL Lambda B P K hP hB hK hcomm m
  filter_upwards [hs.eventually_small hL (by norm_num) (1/2) (by norm_num)] with n hn
  intro t ht
  let T := spectralRemoteReductionFrame Lambda B P K m n t
  have hh : ‖T-1‖ ≤ 1/2 := (hn t ht).le
  have he : (1 : SpectralRemoteOperator)+(T-1) = T := by abel
  have hi := spectralRemote_near_identity_inverse (T-1) hh
  rw [he] at hi
  refine ⟨hi.1,?_,hi.2⟩
  calc
    ‖T‖ = ‖(1 : SpectralRemoteOperator)+(T-1)‖ := by rw [he]
    _ ≤ ‖(1 : SpectralRemoteOperator)‖+‖T-1‖ := norm_add_le _ _
    _ ≤ 2 := by rw [norm_one]; linarith

theorem spectralRemote_reduction_frame_inverse_symbol
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop)
    (Lambda B : ℕ → ℝ → SpectralRemoteOperator)
    (P : SpectralRemoteSuperOperator) (K : ℕ → ℝ → SpectralRemoteSuperOperator)
    (hP : ∀ X, P (P X) = P X) (hB : HasUniformLogJetBound L 0 B)
    (hK : HasUniformLogJetBound L (-2) K)
    (hcomm : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n), ∀ X,
      Lambda n t*K n t X-K n t X*Lambda n t = P X-X)
    (m : ℕ) :
    HasUniformLogJetBound L 0
      (fun n t => Ring.inverse (spectralRemoteReductionFrame Lambda B P K m n t)) := by
  have hs := spectralRemote_reduction_frame_symbol hL Lambda B P K hP hB hK hcomm m
  have hi := spectralRemote_uniform_inverse hL (by norm_num) hs
  have he (n : ℕ) (t : ℝ) : (1 : SpectralRemoteOperator)+
      (spectralRemoteReductionFrame Lambda B P K m n t-1) =
      spectralRemoteReductionFrame Lambda B P K m n t := by abel
  simpa only [he] using hi

end DefocusingNLS

end OAI
