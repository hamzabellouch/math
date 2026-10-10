import OAI.NumberTheory.JointDickman.Counting.SamplingErrorEnvelope
import OAI.NumberTheory.JointDickman.Amplification.AmplificationSquareRate
import OAI.NumberTheory.JointDickman.Counting.SamplingComparisonLimit

namespace OAI

/-! # Sampling transfer for a model controlled by the singular-factor lag envelope -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

theorem sampling_lag_model {C q D c U e ε : ℝ}
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hD : 0 ≤ D) (hc : 0 < c) (hU : 0 ≤ U)
    (he : 0 ≤ e) (hε : 0 < ε) :
    ∀ᶠ B : ℕ in atTop, ∀ (M : ℕ) (A : Type*) [Fintype A] [DecidableEq A],
      0 < M → FiniteMcDiarmidInput (Fin M) A →
      ∀ (p : Fin M → A → ℝ), (∀ i a, 0 ≤ p i a) → (∀ i, ∑ a, p i a = 1) →
      ∀ (K J : Fin M → Fin M → A → A → ℝ),
      (∀ i j a b, K i j a b = K j i b a) → (∀ i j a b, J i j a b = J j i b a) →
      (∀ i a, K i i a a = 0) → (∀ i a, J i i a a = 0) →
      (∀ i j a b, 0 ≤ K i j a b) →
      (∀ i j a b, |J i j a b| ≤ lagEnvelope (amplificationMultiplier B) D i j) →
      c*(B : ℝ)^(0.32 : ℝ) ≤ M → (M : ℝ) ≤ U*(B : ℝ)^(0.32 : ℝ) →
      (∀ i a, |siteRowMean p K i a| ≤ C) →
      (∀ i, siteRowSquareMass p K i ≤ q*(B : ℝ)^(-0.21 : ℝ)) →
      (∀ g h : Fin M → A → ℝ, (∀ i a, |g i a| ≤ 1) → (∀ i a, |h i a| ≤ 1) →
        siteTestMean p (fun i j a b => K i j a b-J i j a b) g h ≤ (M : ℝ)*e) →
      finiteExpectation (siteProductMass p) (fun x =>
        kernelCutNorm (realizedSiteKernel (fun i j a b => K i j a b-J i j a b) x)) ≤ e+ε := by
  have hs := (samplingComparison_eventually
    (show 0 ≤ C+2*D*Real.exp 24 by positivity)
    (show 0 ≤ 2*q+1 by positivity) hc hU he hε)
  have hsNat := tendsto_natCast_atTop_atTop.eventually hs
  filter_upwards [hsNat,amplification_inverse_square_rate (4*D^2*Real.exp 1200),
    amplificationMultiplier_comparable] with B hs hsmall hT
  intro M A _ _ hM hMC p hp hpone K J hKsym hJsym hKd hJd hKpos hJbound hMlo hMhi hrow hquad htest
  have : NeZero M := ⟨hM.ne'⟩
  let E := fun i j a b => K i j a b-J i j a b
  let H := addLagEnvelope K (amplificationMultiplier B) D
  obtain ⟨hHrow,hHquad,hEquad⟩ := addLagEnvelope_moments hT.1 hD p hp hpone K J hJbound hrow hquad
  have hquadBound : q*(B : ℝ)^(-0.21 : ℝ)*2+4*D^2*Real.exp 1200/(amplificationMultiplier B : ℝ) ≤
      (2*q+1)*(B : ℝ)^(-0.21 : ℝ) := by
    have hsmall' : 4*D^2*Real.exp 1200/(amplificationMultiplier B : ℝ) ≤ (B : ℝ)^(-0.21 : ℝ) := by
      convert hsmall using 1
      norm_num
    nlinarith
  apply hs (Fin M) A hMC p hp hpone E H
  · intro i j a b
    dsimp only [E]
    rw [hKsym,hJsym]
  · intro i j a b
    simp only [H,addLagEnvelope,hKsym i j a b,lagEnvelope,ne_comm,Nat.dist_comm]
  · intro i a
    simp only [E,hKd,hJd,sub_self]
  · intro i a
    simp only [H,addLagEnvelope,hKd,lagEnvelope,ne_eq,not_true_eq_false,false_and,ite_false,add_zero]
  · exact addLagEnvelope_dominates K J hKpos hJbound
  · simpa only [Fintype.card_fin] using hMlo
  · simpa only [Fintype.card_fin] using hMhi
  · exact hHrow
  · intro i
    exact (hHquad i).trans hquadBound
  · intro i
    exact (hEquad i).trans hquadBound
  · simpa only [Fintype.card_fin] using htest

end JointDickman

end OAI
