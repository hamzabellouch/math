import OAI.NumberTheory.JointDickman.Amplification.CandidateArithmeticPeriod
import OAI.NumberTheory.JointDickman.Counting.RealPeriodicMoments

namespace OAI

/-! # Ordinary long means of the actual candidate fluctuation kernel -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem actualCandidateKernel_explicit (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) (u : ℕ) :
    actualCandidateKernel B L T H M τ C χ u =
      candidateMatrix
        (fun e : blockCandidates B L T H M τ C (fun i => coefficientPrimeSet B (u+(i.val+1))) => e.val.1.1)
        (fun e => e.val.1.2)
        (fun e => candidateRootWeight B L τ C (fun i => coefficientPrimeSet B (u+(i.val+1))) χ e.val
          (coefficientPrimeSet B (candidateArithmeticQuotient u e.val))) := by
  funext i k
  unfold actualCandidateKernel independentCandidateKernel candidateMatrix
  simp only [arithmeticCandidatePrimeFamily_transpose]

theorem actualCandidateKernel_modEq {B L T H M u v : ℕ} {τ C : ℝ}
    (hT : T ≤ auxiliaryCutoff B) (h : u ≡ v [MOD auxiliarySquarePeriod B])
    (χ : BlockCandidateIndex M → ℝ) :
    actualCandidateKernel B L T H M τ C χ u = actualCandidateKernel B L T H M τ C χ v := by
  rw [actualCandidateKernel_explicit,actualCandidateKernel_explicit]
  have hs := blockPrimeSites_modEq (M := M) h
  rw [hs]
  funext i k
  unfold candidateMatrix
  apply sum_congr rfl
  intro e _
  have he : e.val ∈ blockCandidates B L T H M τ C
      (fun i => coefficientPrimeSet B (u+(i.val+1))) := by
    rw [hs]
    exact e.property
  dsimp only
  rw [candidateArithmeticQuotient_modEq hT h he]

theorem actualCandidateCutError_modEq {B L T H M u v : ℕ} {τ C : ℝ}
    (hT : T ≤ auxiliaryCutoff B) (h : u ≡ v [MOD auxiliarySquarePeriod B])
    (χ : BlockCandidateIndex M → ℝ) :
    actualCandidateCutError B L T H M τ C χ u = actualCandidateCutError B L T H M τ C χ v := by
  unfold actualCandidateCutError
  rw [actualCandidateKernel_modEq hT h χ,blockPrimeSites_modEq h]

noncomputable def residueCandidateCutError (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) (a : ZMod (auxiliarySquarePeriod B)) : ℝ :=
  actualCandidateCutError B L T H M τ C χ a.val

theorem residueCandidateCutError_natCast {B L T H M : ℕ} {τ C : ℝ}
    (hT : T ≤ auxiliaryCutoff B) (χ : BlockCandidateIndex M → ℝ) (u : ℕ) :
    residueCandidateCutError B L T H M τ C χ u = actualCandidateCutError B L T H M τ C χ u := by
  unfold residueCandidateCutError
  rw [ZMod.val_natCast]
  exact actualCandidateCutError_modEq hT (Nat.mod_modEq u _) χ

theorem actualCandidateCutError_mean_tendsto {B L T H M : ℕ} {τ C : ℝ}
    (hT : T ≤ auxiliaryCutoff B) (χ : BlockCandidateIndex M → ℝ) :
    Tendsto (fun N : ℕ => (∑ u ∈ range N, actualCandidateCutError B L T H M τ C χ u)/(N : ℝ))
      atTop (𝓝 (arithmeticSquareMean B (actualCandidateCutError B L T H M τ C χ))) := by
  let f := residueCandidateCutError B L T H M τ C χ
  have hf (u : ℕ) : f u = actualCandidateCutError B L T H M τ C χ u :=
    residueCandidateCutError_natCast hT χ u
  have ht := real_periodic_moment_tendsto f 1
  simp only [pow_one,hf] at ht
  have hs := residue_sum_eq_range (fun a : ZMod (auxiliarySquarePeriod B) => (f a : ℂ))
  have hs' : (∑ a : ZMod (auxiliarySquarePeriod B), f a) =
      ∑ u ∈ range (auxiliarySquarePeriod B), actualCandidateCutError B L T H M τ C χ u := by
    simp only [hf] at hs
    exact_mod_cast hs
  have hQ : auxiliarySquarePeriod B = ∏ p ∈ auxiliaryPrimes B, p^2 := by
    unfold auxiliarySquarePeriod
    exact (prod_pow _ _ _).symm
  have hQr : (auxiliarySquarePeriod B : ℝ) = ∏ p ∈ auxiliaryPrimes B, (p : ℝ)^2 := by
    rw [hQ]
    simp only [Nat.cast_prod,Nat.cast_pow]
  rw [hs',hQr,hQ] at ht
  exact ht

end JointDickman

end OAI
