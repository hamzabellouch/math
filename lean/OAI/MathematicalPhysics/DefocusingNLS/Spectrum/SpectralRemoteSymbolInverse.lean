import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteSymbolProduct
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteInverseJets

namespace OAI

/-! Inversion of a decaying near-identity change preserves uniform symbol
bounds. Consequently an exact block cancellation improves every fixed jet
by the same two powers. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS

theorem spectralRemote_uniform_inverse {L : ℕ → ℝ} {sigma : ℝ}
    {S : ℕ → ℝ → SpectralRemoteOperator} (hL : Tendsto L atTop atTop)
    (hsigma : sigma < 0) (hS : HasUniformLogJetBound L sigma S) :
    HasUniformLogJetBound L 0 (fun n t => Ring.inverse (1+S n t)) := by
  have hsmall := hS.eventually_small hL hsigma (1/2) (by norm_num)
  have hS0 := hS.mono hL hsigma.le
  have hsm : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n), ‖S n t‖ ≤ 1/2 :=
    hsmall.mono (fun _ hn t ht => (hn t ht).le)
  refine ⟨?_,?_⟩
  · filter_upwards [hS.smooth,hsmall] with n hn hsn
    exact spectralRemoteInverseMap_smooth.comp hn (by
      intro t ht
      change dist (S n t) 0 < 1
      rw [dist_zero_right]
      exact (hsn t ht).trans (by norm_num))
  · intro k
    choose C hC hb using hS0.bound
    let B := ∑ i ∈ Finset.range (k+1), C i
    obtain ⟨D,hD,hd⟩ := spectralRemote_inverse_jet_bound k B
    refine ⟨D,hD,?_⟩
    have hfb : ∀ᶠ n in atTop, ∀ i ∈ Finset.range (k+1), ∀ t ∈ Ioi (L n),
        ‖iteratedDeriv i (S n) t‖ ≤ C i := by
      simpa only [zero_mul,Real.exp_zero,mul_one] using
        ((eventually_all_finset (Finset.range (k+1))).mpr (fun i _ => hb i))
    filter_upwards [hfb,hS.smooth,hsm] with n hn hsn hsmalln
    intro t ht
    have hj (i : ℕ) (hi : i ≤ k) : ‖iteratedDeriv i (S n) t‖ ≤ B :=
      (hn i (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)) t ht).trans
        (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)))
    simpa only [zero_mul,Real.exp_zero,mul_one] using
      hd (Ioi (L n)) isOpen_Ioi (S n) hsn hsmalln t ht hj k le_rfl

theorem spectralRemote_uniform_reduction {L : ℕ → ℝ} {sigma : ℝ}
    (hL : Tendsto L atTop atTop) (hsigma : sigma < 0)
    (Lambda B B₀ S : ℕ → ℝ → SpectralRemoteOperator)
    (hB : HasUniformLogJetBound L 0 B) (hB₀ : HasUniformLogJetBound L 0 B₀)
    (hS : HasUniformLogJetBound L sigma S)
    (hcomm : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n),
      Lambda n t*S n t-S n t*Lambda n t = B₀ n t-B n t) :
    HasUniformLogJetBound L sigma (fun n t =>
      spectralRemoteReducedRemainder (Lambda n t) (B n t) (B₀ n t) (S n t) (deriv (S n) t)) := by
  have hInv := spectralRemote_uniform_inverse hL hsigma hS
  have hBS : HasUniformLogJetBound L sigma (fun n t => B n t*S n t) := by
    simpa only [zero_add] using hB.mul hS
  have hSB : HasUniformLogJetBound L sigma (fun n t => S n t*B₀ n t) := by
    simpa only [add_zero] using hS.mul hB₀
  have hprod : HasUniformLogJetBound L sigma (fun n t =>
      Ring.inverse (1+S n t)*(B n t*S n t-S n t*B₀ n t-deriv (S n) t)) := by
    simpa only [zero_add] using hInv.mul ((hBS.sub hSB).sub hS.deriv)
  apply hprod.eventually_congr
  filter_upwards [hcomm,hS.eventually_small hL hsigma (1/2) (by norm_num)] with n hn hsn
  intro t ht
  exact (spectralRemote_reduction_identity _ _ _ _ _
    (spectralRemote_near_identity_inverse (S n t) (hsn t ht).le).1 (hn t ht)).symm

end DefocusingNLS

end OAI
