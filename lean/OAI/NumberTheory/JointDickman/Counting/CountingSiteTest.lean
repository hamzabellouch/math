import OAI.NumberTheory.JointDickman.Counting.CountingSiteModel
import OAI.NumberTheory.JointDickman.Amplification.SubsetPairTests
import OAI.NumberTheory.JointDickman.Probability.SitePairTestSum
import OAI.NumberTheory.JointDickman.Counting.LagEnvelopeMoments

namespace OAI

/-! # The block test estimate for the actual counting-feature error -/
namespace JointDickman
open Finset Classical PublishedInputs

theorem finiteExpectation_swap {A B : Type*} [Fintype A] [Fintype B]
    (p : A → ℝ) (q : B → ℝ) (F : A → B → ℝ) :
    finiteExpectation p (fun a => finiteExpectation q (F a)) =
      finiteExpectation q (fun b => finiteExpectation p (fun a => F a b)) := by
  unfold finiteExpectation
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro a _
  ring

noncomputable def countingSiteError (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B L T H M : ℕ) (τ C w : ℝ)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (D : (Fin 4 →₀ ℕ) → ℕ) (σ : ℝ)
    (i k : Fin M) (a b : (auxiliaryPrimes B).powerset) : ℝ :=
  latentPrimeSiteKernel B L T H M τ C (rampedCandidateCutoff B T w σ) i k a b-
    countingSiteModel P m B L T H M τ C c D σ i k a b

theorem countingSiteError_symm (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B L T H M : ℕ) (τ C w : ℝ)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (D : (Fin 4 →₀ ℕ) → ℕ) (σ : ℝ)
    (i k : Fin M) (a b : (auxiliaryPrimes B).powerset) :
    countingSiteError P m B L T H M τ C w c D σ i k a b =
      countingSiteError P m B L T H M τ C w c D σ k i b a := by
  unfold countingSiteError latentPrimeSiteKernel
  rw [candidateSiteKernel_symm,countingSiteModel_symm]

end JointDickman

end OAI
