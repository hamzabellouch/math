import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteUniformIncoming
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteUniformExponent
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemotePhysicalIndividual

namespace OAI

/-! Uniform incoming smallness for the actual reduced physical solution.
The reduction order is chosen after the bounded-part exponent and before
discarding any further parameter indices. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralRemote_physical_incoming
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop) (sigma : ℝ)
    (c : ℕ → ℝ → Fin 2 → ℝ) (B : ℕ → ℝ → SpectralRemoteOperator)
    (Y : ℕ → ℝ → SpectralRemoteSpace)
    (hc : HasUniformLogJetBound L 0 c) (hB : HasUniformLogJetBound L 0 B)
    (hci : ∀ᶠ n in atTop, HasLogJetBound 0 (c n))
    (hBi : ∀ᶠ n in atTop, HasLogJetBound 0 (B n))
    (hYi : ∀ᶠ n in atTop, HasLogJetBound sigma (Y n))
    (hsmall : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n), ∀ k, |c n t k| ≤ 1/32)
    (hode : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n),
      HasDerivAt (Y n) (((Real.exp t : ℂ)^2 • spectralRemotePhysicalLeading (c n t)+B n t) (Y n t)) t) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop, ∀ T ∈ Ioi (L n),
      ‖spectralPhysicalDerivativeMap (spectralRemotePhysicalReducedSolution c B Y m n T)‖ ≤
        K*Real.exp (-2*T)*‖spectralRemotePhysicalReducedSolution c B Y m n T‖ := by
  let Lambda := fun n t => spectralRemoteLeadingOperator (c n t) t
  let S := fun n t => spectralRemoteSylvesterOperator (Real.exp t) (spectralRemoteDiagonalRoot (c n t))
  let B' := spectralRemoteInitialRemainder c B
  have hB' := spectralRemote_initial_remainder_symbol hc hsmall hB
  obtain ⟨C,hC,hCb⟩ := spectralRemote_uniform_exponent hL B' hc hsmall hB'
  obtain ⟨m,hm⟩ := exists_nat_gt (5*C+|sigma|+1)
  generalize hqdef : m+1 = q
  have hq : 1 ≤ q := by omega
  have hgap : 5*C < 2*(q : ℝ) := by rw [← hqdef]; push_cast; nlinarith [abs_nonneg sigma]
  have hdecay : C+(sigma-2*(q : ℝ)) < 0 := by
    rw [← hqdef]
    push_cast
    nlinarith [le_abs_self sigma,abs_nonneg sigma]
  let d := spectralRemoteReductionData Lambda B' spectralRemoteBlockOperator S q
  let Z := spectralRemotePhysicalReducedSolution c B Y q
  have hCbq := hCb m
  rw [hqdef] at hCbq
  have hd := spectralRemote_root_reduction hL hc hsmall B' hB' q
  have hdi : ∀ᶠ n in atTop, HasLogJetBound 0 (d.1 n) ∧
      HasLogJetBound (-2*(q : ℝ)) (d.2 n) := by
    filter_upwards [hci,hBi,hsmall] with n hcn hBn hn
    have hs : ∀ᶠ t in atTop, ∀ k, |c n t k| ≤ 1/32 :=
      (eventually_gt_atTop (L n)).mono (fun t ht => hn t ht)
    have hBn' := (spectralRemote_initial_individual c B n hcn hBn hs).2.2
    have hdn := spectralRemote_root_reduction_single c B' q n hcn hBn' hs
    exact ⟨hdn.1,hdn.2.1⟩
  have hZi : ∀ᶠ n in atTop, HasLogJetBound sigma (Z n) := by
    filter_upwards [hci,hBi,hYi,hsmall] with n hcn hBn hYn hn
    exact spectralRemote_physical_reduced_individual c B Y q n sigma hcn hBn hYn
      ((eventually_gt_atTop (L n)).mono (fun t ht => hn t ht))
  have hZode : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n),
      HasDerivAt (Z n) ((Lambda n t+d.1 n t+d.2 n t) (Z n t)) t := by
    filter_upwards [spectralRemote_physical_reduced_equation hL B Y hc hsmall hB q,hode]
      with n hn hYn
    intro t ht
    exact hn t ht (hYn t ht)
  have hblock : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n),
      spectralRemoteBlockOperator (d.1 n t) = d.1 n t := by
    filter_upwards [hd.2.2.2.2] with n hn
    exact fun t ht => (hn t ht).1
  have hAb : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n), ‖d.1 n t‖ ≤ C := by
    filter_upwards [hCbq] with n hn
    exact fun t ht => (hn t ht).1
  have hAR : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n), ‖d.1 n t+d.2 n t‖ ≤ C := by
    filter_upwards [hCbq] with n hn
    exact fun t ht => (hn t ht).2
  obtain ⟨K,hK,hbound⟩ := spectralRemote_uniform_incoming hL C sigma q hC.le hq hgap hdecay
    c d.1 d.2 Z hc hd.1 hd.2.1 hci (hdi.mono (fun _ hn => hn.1))
    (hdi.mono (fun _ hn => hn.2)) hZi hsmall hblock hAb hAR hZode
  exact ⟨q,hq,K,hK,hbound⟩

end DefocusingNLS

end OAI
