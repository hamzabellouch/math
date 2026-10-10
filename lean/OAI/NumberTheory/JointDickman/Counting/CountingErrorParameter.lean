import OAI.NumberTheory.JointDickman.Counting.CountingEntryVariation
import OAI.NumberTheory.JointDickman.Probability.RampedKernelVariation
import OAI.NumberTheory.JointDickman.Counting.CountingArithmeticMean
import OAI.NumberTheory.JointDickman.Counting.CountingSiteTest

namespace OAI

/-! # Regularity of the actual sampling error in the counting parameter -/
namespace JointDickman
open Finset Classical

theorem countingError_parameter_bound (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B L T H M : ℕ) (τ C w : ℝ)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (D : (Fin 4 →₀ ℕ) → ℕ)
    {A K : ℝ} (_hA : 0 ≤ A) (hK : 0 ≤ K) (hw : 0 < w) (hM : 0 < M)
    (hcap : ∀ x : Fin M → (auxiliaryPrimes B).powerset,
      kernelAbsoluteMass (latentCandidateKernel B L T H M τ C (fun i => (x i).val)
        (smoothCandidateCutoff B T)) ≤ A)
    (hkernel : ∀ (j : ℕ) (s t : ℝ), H < j → j < T → |s| ≤ 3 → |t| ≤ 3 → ∀ x y,
      |countingPrimeKernel P m B j c D T s x y-countingPrimeKernel P m B j c D T t x y| ≤ K*|s-t|) :
    ∀ (s t : ℝ), |s| ≤ 3 → |t| ≤ 3 → ∀ x : Fin M → (auxiliaryPrimes B).powerset,
      |kernelCutNorm (realizedSiteKernel (countingSiteError P m B L T H M τ C w c D s) x)-
        kernelCutNorm (realizedSiteKernel (countingSiteError P m B L T H M τ C w c D t) x)| ≤
      (A/w+(M : ℝ)*(∑ j ∈ range (T+1), |independentRootMean B L τ C*(singularSeries j/(j : ℝ))| *K))*|s-t| := by
  intro s t hs ht x
  let V := ∑ j ∈ range (T+1), |independentRootMean B L τ C*(singularSeries j/(j : ℝ))| *K
  let R := fun a => latentCandidateKernel B L T H M τ C (fun i => (x i).val)
    (rampedCandidateCutoff B T w a)
  let J := fun a => realizedSiteKernel (countingSiteModel P m B L T H M τ C c D a) x
  have he (a : ℝ) : realizedSiteKernel (countingSiteError P m B L T H M τ C w c D a) x =
      fun i k => R a i k-J a i k := by
    funext i k
    change realizedSiteKernel (latentPrimeSiteKernel B L T H M τ C (rampedCandidateCutoff B T w a)) x i k-
      J a i k = _
    rw [latentPrimeSiteKernel_realizes]
  rw [he,he]
  have hR : kernelAbsoluteMass (fun i k => R s i k-R t i k) ≤ (A/w)*|s-t| := by
    apply (rampedKernel_absolute_variation hw (fun i => (x i).val)).trans
    exact (mul_le_mul_of_nonneg_left (hcap x) (by positivity)).trans_eq (by ring)
  have hJ : kernelAbsoluteMass (fun i k => J s i k-J t i k) ≤ (M : ℝ)*V*|s-t| := by
    apply (kernelAbsoluteMass_entry_bound hM _ (fun i k => ?_)).trans_eq (mul_assoc _ _ _).symm
    exact countingSiteWithSeries_entry_variation singularSeries P m B L T H M τ C c D hK
      (fun j hj hjT => hkernel j s t hj hjT hs ht) i k (x i) (x k)
  exact (kernel_error_parameter_bound (R s) (R t) (J s) (J t) hR hJ).trans_eq (by ring)

end JointDickman

end OAI
