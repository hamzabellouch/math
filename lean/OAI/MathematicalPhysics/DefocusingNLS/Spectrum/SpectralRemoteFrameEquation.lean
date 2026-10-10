import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteReductionFrame

namespace OAI

/-! Exact intertwining of the original and finitely reduced equations. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS

theorem spectralRemote_reduction_conjugacy (Lambda B A S dS : SpectralRemoteOperator)
    (hu : IsUnit (1+S)) :
    (1+S)*(Lambda+A+spectralRemoteReducedRemainder Lambda B A S dS) =
      (Lambda+B)*(1+S)-dS := by
  have he : Lambda+A+spectralRemoteReducedRemainder Lambda B A S dS =
      Ring.inverse (1+S)*((Lambda+B)*(1+S)-dS) := by
    unfold spectralRemoteReducedRemainder
    abel
  rw [he,Ring.mul_inverse_cancel_left _ _ hu]

theorem spectralRemote_frame_step
    (T S : ℝ → SpectralRemoteOperator) (t : ℝ)
    (M N N' dS : SpectralRemoteOperator)
    (hT : HasDerivAt T (M*T t-T t*N) t)
    (hS : HasDerivAt S dS t)
    (hc : (1+S t)*N' = N*(1+S t)-dS) :
    HasDerivAt (fun r => T r*(1+S r))
      (M*(T t*(1+S t))-(T t*(1+S t))*N') t := by
  apply (hT.mul (hS.const_add 1)).congr_deriv
  calc
    _ = M*(T t*(1+S t))-T t*(N*(1+S t)-dS) := by
      simp only [sub_mul,mul_sub,mul_add,mul_one,mul_assoc]
      abel
    _ = _ := by rw [← hc,mul_assoc]

theorem spectralRemote_reduction_data_step
    (Lambda B : ℕ → ℝ → SpectralRemoteOperator)
    (P : SpectralRemoteSuperOperator) (K : ℕ → ℝ → SpectralRemoteSuperOperator)
    (m n : ℕ) (t : ℝ)
    (hu : IsUnit (1+spectralRemoteReductionChange Lambda B P K m n t)) :
    let S := spectralRemoteReductionChange Lambda B P K m
    let d := spectralRemoteReductionData Lambda B P K m
    let d' := spectralRemoteReductionData Lambda B P K (m+1)
    (1+S n t)*(Lambda n t+d'.1 n t+d'.2 n t) =
      (Lambda n t+d.1 n t+d.2 n t)*(1+S n t)-deriv (S n) t := by
  dsimp only
  have he := spectralRemote_reduction_conjugacy (Lambda n t)
    ((spectralRemoteReductionData Lambda B P K m).1 n t+
      (spectralRemoteReductionData Lambda B P K m).2 n t)
    ((spectralRemoteReductionData Lambda B P K m).1 n t+
      P ((spectralRemoteReductionData Lambda B P K m).2 n t))
    (spectralRemoteReductionChange Lambda B P K m n t)
    (deriv (spectralRemoteReductionChange Lambda B P K m n) t) hu
  have hf : spectralRemoteReductionChange Lambda B P K m n =
      (fun t => K n t ((spectralRemoteReductionData Lambda B P K m).2 n t)) := by
    funext t
    rfl
  rw [hf] at he ⊢
  simpa only [spectralRemoteReductionData,spectralRemoteReductionChange,add_assoc] using he

theorem spectralRemote_reduction_frame_equation
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop)
    (Lambda B : ℕ → ℝ → SpectralRemoteOperator)
    (P : SpectralRemoteSuperOperator) (K : ℕ → ℝ → SpectralRemoteSuperOperator)
    (hP : ∀ X, P (P X) = P X) (hB : HasUniformLogJetBound L 0 B)
    (hK : HasUniformLogJetBound L (-2) K)
    (hcomm : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n), ∀ X,
      Lambda n t*K n t X-K n t X*Lambda n t = P X-X)
    (m : ℕ) :
    ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n),
      let T := spectralRemoteReductionFrame Lambda B P K m
      let d := spectralRemoteReductionData Lambda B P K m
      HasDerivAt (T n)
        ((Lambda n t+B n t)*T n t-T n t*(Lambda n t+d.1 n t+d.2 n t)) t := by
  induction m with
  | zero =>
      apply Eventually.of_forall
      intro n t ht
      simpa only [spectralRemoteReductionFrame,spectralRemoteReductionData,mul_one,one_mul,
        add_zero,sub_self] using (hasDerivAt_const t (1 : SpectralRemoteOperator))
  | succ m ih =>
      let T := spectralRemoteReductionFrame Lambda B P K m
      let S := spectralRemoteReductionChange Lambda B P K m
      let d := spectralRemoteReductionData Lambda B P K m
      have hs := spectralRemote_reduction_change_symbol hL Lambda B P K hP hB hK hcomm m
      have hneg : -2*((m+1 : ℕ) : ℝ) < 0 := by
        push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) m]
      filter_upwards [ih,hs.smooth,hs.eventually_small hL hneg (1/2) (by norm_num)] with n hn hsn hsmall
      intro t ht
      have hdS : HasDerivAt (S n) (deriv (S n) t) t :=
        ((hsn t ht).contDiffAt (Ioi_mem_nhds ht)).differentiableAt (by simp) |>.hasDerivAt
      have he := spectralRemote_reduction_data_step Lambda B P K m n t
        (spectralRemote_near_identity_inverse (S n t) (hsmall t ht).le).1
      exact spectralRemote_frame_step (T n) (S n) t (Lambda n t+B n t)
        (Lambda n t+d.1 n t+d.2 n t)
        (Lambda n t+(spectralRemoteReductionData Lambda B P K (m+1)).1 n t+
          (spectralRemoteReductionData Lambda B P K (m+1)).2 n t)
        (deriv (S n) t) (hn t ht) hdS he

end DefocusingNLS

end OAI
