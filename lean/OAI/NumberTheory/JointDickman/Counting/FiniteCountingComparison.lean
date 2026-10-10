import OAI.NumberTheory.JointDickman.Counting.CountingOriginParameter
import OAI.NumberTheory.JointDickman.Counting.CountingSlowMean
import OAI.NumberTheory.JointDickman.Amplification.FiniteRampApproximation
import OAI.NumberTheory.JointDickman.Counting.EnergyMeanComparison
import OAI.NumberTheory.JointDickman.Amplification.GraphSquareRemoval

namespace OAI

/-! # Comparing the original finite graph with the counting model -/
namespace JointDickman
open Finset Classical

theorem countingArithmeticCutError_eq
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ)
    (B L T H M u : ℕ) (τ C w σ : ℝ)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (D : (Fin 4 →₀ ℕ) → ℕ) :
    countingArithmeticCutError P m B L T H M τ C w c D σ u =
      kernelCutNorm (fun i k =>
        latentCandidateKernel B L T H M τ C
          (fun j => coefficientPrimeSet B (u+(j.val+1))) (rampedCandidateCutoff B T w σ) i k-
        countingArithmeticKernel singularSeries P m B L T H M u τ C c D σ i k) := by
  let S : Fin M → (auxiliaryPrimes B).powerset := fun i =>
    ⟨coefficientPrimeSet B (u+(i.val+1)),by simp [coefficientPrimeSet]⟩
  have hS : blockPatternEquiv B M (arithmeticPrimePatterns B M u) = S := by
    funext i
    apply Subtype.ext
    exact primePatternsSites_arithmetic B M u i
  unfold countingArithmeticCutError
  rw [hS]
  apply congrArg kernelCutNorm
  funext i k
  change realizedSiteKernel (latentPrimeSiteKernel B L T H M τ C (rampedCandidateCutoff B T w σ)) S i k-
      countingSiteModel P m B L T H M τ C c D σ i k (S i) (S k) = _
  rw [latentPrimeSiteKernel_realizes]
  rfl

theorem finite_graph_counting_energy_compare
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ)
    (B L T H M N u : ℕ) (τ C w : ℝ)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (D : (Fin 4 →₀ ℕ) → ℕ)
    (hT : 0 < T) (hM : 0 < M) (hw : 0 < w)
    (z : Fin M → ℂ) (hz : ∀ i, ‖z i‖ ≤ 2) :
    |(complexEnergy (finiteGraphKernel B L T H M N u τ C) z).re|/(M : ℝ) ≤
      |(complexEnergy (countingArithmeticKernel singularSeries P m B L T H M u τ C c D
        (countingOriginParameter T N u)) z).re|/(M : ℝ)+
      16*(finiteGraphLatentError B L T H M N u τ C+
        finiteRampCutError B L T H M N u τ C w+
        countingArithmeticCutError P m B L T H M τ C w c D (countingOriginParameter T N u) u) := by
  apply (normalized_energy_comparison hM (finiteGraphKernel B L T H M N u τ C)
    (countingArithmeticKernel singularSeries P m B L T H M u τ C c D
      (countingOriginParameter T N u)) z hz).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hh := (kernelCutNorm_sub_triangle
    (finiteGraphKernel B L T H M N u τ C)
    (latentCandidateKernel B L T H M τ C (fun j => coefficientPrimeSet B (u+(j.val+1)))
      (finiteCandidateCutoff B T N u))
    (countingArithmeticKernel singularSeries P m B L T H M u τ C c D
      (countingOriginParameter T N u)))
  have hr := kernelCutNorm_sub_triangle
    (latentCandidateKernel B L T H M τ C (fun j => coefficientPrimeSet B (u+(j.val+1)))
      (finiteCandidateCutoff B T N u))
    (latentCandidateKernel B L T H M τ C (fun j => coefficientPrimeSet B (u+(j.val+1)))
      (rampedCandidateCutoff B T w (countingOriginParameter T N u)))
    (countingArithmeticKernel singularSeries P m B L T H M u τ C c D
      (countingOriginParameter T N u))
  have he : rampedCandidateCutoff (M := M) B T w (countingOriginParameter T N u) =
      rampedCandidateCutoff B T w ((u : ℝ)/((T : ℝ)*(N+1))) :=
    funext (rampedCandidateCutoff_originParameter hT hw B N u)
  rw [← countingArithmeticCutError_eq] at hr
  rw [he] at hr
  simpa only [finiteGraphLatentError,finiteRampCutError,add_assoc] using
    hh.trans (add_le_add le_rfl hr)

end JointDickman

end OAI
