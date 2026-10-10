import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteReductionStep
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

/-! Fixed-order bounds for inversion of the remote changes of variables.
The same constant works for every path whose jets obey the stated bounds. -/

open Set
open scoped ContDiff
namespace DefocusingNLS

noncomputable def spectralRemoteInverseMap (S : SpectralRemoteOperator) : SpectralRemoteOperator :=
  Ring.inverse (1+S)

theorem spectralRemoteInverseMap_smooth :
    ContDiffOn ℝ ∞ spectralRemoteInverseMap (Metric.ball 0 1) := by
  intro S hS
  have hs : ‖S‖ < 1 := by simpa only [Metric.mem_ball,dist_zero_right] using hS
  have hneg : ‖-S‖ < 1 := by simpa only [norm_neg] using hs
  have hu : IsUnit (1+S) := by
    simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one hneg
  have hi : ContDiffAt ℝ ∞ (Ring.inverse : SpectralRemoteOperator → SpectralRemoteOperator) (1+S) := by
    obtain ⟨u,he⟩ := hu
    rw [← he]
    exact contDiffAt_ringInverse ℝ u
  exact (hi.comp S (contDiffAt_const.add contDiffAt_id)).contDiffWithinAt

theorem spectralRemote_inverse_jet_bound (N : ℕ) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Set ℝ), IsOpen s →
      ∀ f : ℝ → SpectralRemoteOperator, ContDiffOn ℝ ∞ f s →
      (∀ t ∈ s, ‖f t‖ ≤ 1/2) →
      ∀ t ∈ s, (∀ i : ℕ, i ≤ N → ‖iteratedDeriv i f t‖ ≤ B) →
      ∀ n : ℕ, n ≤ N →
        ‖iteratedDeriv n (fun r => Ring.inverse (1+f r)) t‖ ≤ C := by
  let O : Set SpectralRemoteOperator := Metric.ball 0 1
  let K : Set SpectralRemoteOperator := Metric.closedBall 0 (1/2)
  have hKO : K ⊆ O := by
    intro x hx
    change dist x 0 < 1
    change dist x 0 ≤ 1/2 at hx
    linarith
  have hO : IsOpen O := Metric.isOpen_ball
  have hg := spectralRemoteInverseMap_smooth
  let M : SpectralRemoteOperator → ℝ := fun x => ∑ i ∈ Finset.range (N+1),
    ‖iteratedFDerivWithin ℝ i spectralRemoteInverseMap O x‖
  have hMc : ContinuousOn M O := by
    apply continuousOn_finsetSum
    intro i hi
    exact (hg.continuousOn_iteratedFDerivWithin (by simp) hO.uniqueDiffOn).norm
  obtain ⟨C₀,hC₀⟩ := (isCompact_closedBall (0 : SpectralRemoteOperator) (1/2)).exists_bound_of_continuousOn (hMc.mono hKO)
  let A := max C₀ 0
  let D := max B 1
  let C := ∑ n ∈ Finset.range (N+1), (n.factorial : ℝ)*A*D^n
  have hA : 0 ≤ A := le_max_right _ _
  have hD : 1 ≤ D := le_max_right _ _
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro s hs f hf hsmall t ht hjets n hn
  have hft : f t ∈ K := by simpa only [K,Metric.mem_closedBall,dist_zero_right] using hsmall t ht
  have hmap : MapsTo f s O := fun r hr => hKO (by
    simpa only [K,Metric.mem_closedBall,dist_zero_right] using hsmall r hr)
  have houter (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDerivWithin ℝ i spectralRemoteInverseMap O (f t)‖ ≤ A := by
    have hb : ‖iteratedFDerivWithin ℝ i spectralRemoteInverseMap O (f t)‖ ≤ M (f t) :=
      Finset.single_le_sum (f := fun j => ‖iteratedFDerivWithin ℝ j spectralRemoteInverseMap O (f t)‖)
        (fun _ _ => norm_nonneg _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le (hi.trans hn)))
    exact hb.trans ((le_abs_self _).trans ((hC₀ (f t) hft).trans (le_max_left _ _)))
  have hinner (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
      ‖iteratedFDerivWithin ℝ i f s t‖ ≤ D^i := by
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hs.uniqueDiffOn
      (((hf t ht).contDiffAt (hs.mem_nhds ht)).of_le (by simp)) ht,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact (hjets i (hin.trans hn)).trans ((le_max_left B 1).trans
      (by simpa only [pow_one] using pow_le_pow_right₀ hD hi))
  have hc := norm_iteratedFDerivWithin_comp_le hg hf (by simp : (n : ℕ∞ω) ≤ ∞)
    hO.uniqueDiffOn hs.uniqueDiffOn hmap ht houter hinner
  have hcomp : ContDiffAt ℝ n (spectralRemoteInverseMap ∘ f) t :=
    (((hg.comp hf hmap) t ht).contDiffAt (hs.mem_nhds ht)).of_le (by simp)
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hs.uniqueDiffOn hcomp ht,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hc
  apply hc.trans
  exact Finset.single_le_sum (f := fun j => (j.factorial : ℝ)*A*D^j) (fun j _ => by positivity)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))

end DefocusingNLS

end OAI
