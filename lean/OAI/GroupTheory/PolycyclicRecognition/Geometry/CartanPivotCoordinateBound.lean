import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPivotCancellation
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConeQuotientBounds
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponentialOperations

namespace OAI

/-! # The source pivot leaves only a subexponential coordinate loss -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter
open scoped Topology

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)

/-- Scalar dilation cancels before estimating the residual action. -/
theorem exists_pivot_cancelled_coordinate_bound (β : M.Bases) :
    ∃ (A : ℝ) (p : ℕ), 0 ≤ A ∧ ∀ (h : H) (v : cartanRootIdeal H),
      ‖(WordBasisSelections.basis M.letter M.wordList β).equivFun
        (cartanIdealAdjointAutomorphism T H (-h) (cartanIdealWeightDilation T H h v))‖ ≤
      A * (1 + ‖(finBasis ℝ H).equivFun h‖) ^ p *
        ‖(WordBasisSelections.basis M.letter M.wordList β).equivFun v‖ := by
  obtain ⟨A, p, hA, hb⟩ := M.exists_residual_coordinate_bound T β
  refine ⟨A, p, hA, ?_⟩
  intro h v
  rw [cartan_adjoint_neg_dilation]
  simpa only [map_neg, norm_neg] using hb (-h) v

/-- Every family of bounded pivot logarithms has one subexponential loss,
uniform in the small exponential rate of the bridge input. -/
theorem exists_sequence_pivot_coordinate_bound (β : M.Bases)
    (scale RH R : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hRH0 : ∀ n, 0 ≤ RH n) (hR0 : ∀ n, 0 ≤ R n)
    (hRH : HasSubexponentialUpperBoundSeq scale RH)
    (hR : HasSubexponentialUpperBoundSeq scale R) :
    ∃ S : ℕ → ℝ, (∀ n, 0 ≤ S n) ∧ HasSubexponentialUpperBoundSeq scale S ∧
      ∀ n (δ : ℝ) (h : H) (v : cartanRootIdeal H),
        ‖(finBasis ℝ H).equivFun h‖ ≤ RH n →
        ‖(WordBasisSelections.basis M.letter M.wordList β).equivFun v‖ ≤
          R n * Real.exp (δ * scale n) →
        ‖(WordBasisSelections.basis M.letter M.wordList β).equivFun
          (cartanIdealAdjointAutomorphism T H (-h) (cartanIdealWeightDilation T H h v))‖ ≤
          S n * Real.exp (δ * scale n) := by
  obtain ⟨A, p, hA, hb⟩ := M.exists_pivot_cancelled_coordinate_bound T β
  let S := fun n => A * (1 + RH n) ^ p * R n
  have hS0 : ∀ n, 0 ≤ S n := fun n =>
    mul_nonneg (mul_nonneg hA (pow_nonneg (by linarith [hRH0 n]) _)) (hR0 n)
  have hS : HasSubexponentialUpperBoundSeq scale S :=
    ((sequence_subexponential_upper_const hs A).mul
      (((sequence_subexponential_upper_const hs 1).add hRH hs).pow hs
        (Eventually.of_forall (fun n => by linarith [hRH0 n])) p)
      (Eventually.of_forall (fun _ => hA))).mul hR
      (Eventually.of_forall (fun n => mul_nonneg hA (pow_nonneg (by linarith [hRH0 n]) _)))
  refine ⟨S, hS0, hS, ?_⟩
  intro n δ h v hh hv
  have hp : (1 + ‖(finBasis ℝ H).equivFun h‖) ^ p ≤ (1 + RH n) ^ p :=
    pow_le_pow_left₀ (by positivity) (by linarith) p
  calc
    _ ≤ A * (1 + ‖(finBasis ℝ H).equivFun h‖) ^ p *
        ‖(WordBasisSelections.basis M.letter M.wordList β).equivFun v‖ := hb h v
    _ ≤ A * (1 + RH n) ^ p * (R n * Real.exp (δ * scale n)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hp hA) hv (norm_nonneg _)
        (mul_nonneg hA (pow_nonneg (by linarith [hRH0 n]) _))
    _ = _ := by dsimp [S]; ring

end PolycyclicRecognition.CartanWordModel

end

end OAI
