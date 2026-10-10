import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSmallHeight
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.SequenceVanishingRate

namespace OAI

/-! # A common subexponential bound for vanishing-height conjugations

The height error is allowed to tend to zero with the scale. The full Cartan
logarithm has only a subexponential bound; the adjoint action still sends
every bounded correction to one common subexponential coordinate ball.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter
open scoped Topology

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

include hunimod in
theorem exists_vanishing_height_adjoint_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {J : Type*} [Fintype J] (b : Basis J ℝ (cartanRootIdeal H))
    (scale RH RV η : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hscale : ∀ n, 0 ≤ scale n) (hRH0 : ∀ n, 0 ≤ RH n) (hRV0 : ∀ n, 0 ≤ RV n)
    (hRH : HasSubexponentialUpperBoundSeq scale RH)
    (hRV : HasSubexponentialUpperBoundSeq scale RV) (hη : Tendsto η atTop (𝓝 0)) :
    ∃ S : ℕ → ℝ, (∀ n, 0 ≤ S n) ∧ HasSubexponentialUpperBoundSeq scale S ∧
      ∀ n (γ : M.Bases) (h : H) (v : cartanRootIdeal H),
        ‖(finBasis ℝ H).equivFun h‖ ≤ RH n →
        ‖eW (heightProjection T.character (h : L))‖ ≤ η n * scale n →
        ‖(WordBasisSelections.basis M.letter M.wordList γ).equivFun v‖ ≤ RV n →
        ‖b.equivFun (cartanIdealAdjointAutomorphism T H h v)‖ ≤ S n := by
  obtain ⟨A, K, p, hA, hK, hbound⟩ :=
    M.exists_small_height_adjoint_bound_in_basis T hunimod eW b₀ b
  let P := fun n => A * (1 + RH n) ^ p
  let S := fun n => P n * Real.exp ((K * η n) * scale n) * RV n
  have hP0 (n : ℕ) : 0 ≤ P n := mul_nonneg hA
    (pow_nonneg (by linarith [hRH0 n]) p)
  have hP : HasSubexponentialUpperBoundSeq scale P :=
    (sequence_subexponential_upper_const hs A).mul
      (((sequence_subexponential_upper_const hs 1).add hRH hs).pow hs
        (Eventually.of_forall (fun n => by linarith [hRH0 n])) p)
      (Eventually.of_forall (fun _ => hA))
  have hKη : Tendsto (fun n => K * η n) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hη
  have he := sequence_subexponential_exp_of_vanishing_rate hscale hKη
  refine ⟨S, fun n => mul_nonneg (mul_nonneg (hP0 n) (Real.exp_nonneg _)) (hRV0 n),
    (hP.mul he (Eventually.of_forall hP0)).mul hRV
      (Eventually.of_forall (fun n => mul_nonneg (hP0 n) (Real.exp_nonneg _))), ?_⟩
  intro n γ h v hh hw hv
  calc
    _ ≤ A * (1 + ‖(finBasis ℝ H).equivFun h‖) ^ p *
        Real.exp (K * ‖eW (heightProjection T.character (h : L))‖) *
          ‖(WordBasisSelections.basis M.letter M.wordList γ).equivFun v‖ := hbound γ h v
    _ ≤ S n := by
      apply mul_le_mul _ hv (norm_nonneg _) (mul_nonneg (hP0 n) (Real.exp_nonneg _))
      apply mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
          (by linarith) p) hA)
        (Real.exp_le_exp.mpr ?_) (Real.exp_nonneg _) (hP0 n)
      calc
        K * ‖eW (heightProjection T.character (h : L))‖ ≤ K * (η n * scale n) :=
          mul_le_mul_of_nonneg_left hw hK
        _ = (K * η n) * scale n := by ring

end PolycyclicRecognition.CartanWordModel

end

end OAI
