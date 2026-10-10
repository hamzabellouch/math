import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSmallHeight

namespace OAI

/-! # Small-height control chosen before the probe path constants -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric Filter
open scoped Topology
open scoped Pointwise

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

include hunimod in
theorem exists_uniform_small_height_adjoint_sequence_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {J : Type*} [Fintype J] (b : Basis J ℝ (cartanRootIdeal H))
    : ∃ B : ℝ, 0 < B ∧ ∀ (scale RH RE : ℕ → ℝ),
      Tendsto scale atTop atTop → (∀ n, 0 ≤ RH n) →
      HasSubexponentialUpperBoundSeq scale RH →
      HasSubexponentialUpperBoundSeq scale RE →
      ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
        ∀ (γ : M.Bases) (h : H) (v : cartanRootIdeal H),
          ‖(finBasis ℝ H).equivFun h‖ ≤ RH n →
          ‖eW (heightProjection T.character (h : L))‖ ≤ δ * scale n →
          ‖(WordBasisSelections.basis M.letter M.wordList γ).equivFun v‖ ≤
            RE n * Real.exp (δ * scale n) →
          ‖b.equivFun (cartanIdealAdjointAutomorphism T H h v)‖ ≤
            Real.exp (B * δ * scale n) := by
  obtain ⟨A, K, p, hA, hK, hbound⟩ :=
    M.exists_small_height_adjoint_bound_in_basis T hunimod eW b₀ b
  refine ⟨K + 2, by linarith, ?_⟩
  intro scale RH RE hs hRH0 hRH hRE
  let R := fun n => A * (1 + RH n) ^ p * RE n
  have hR : HasSubexponentialUpperBoundSeq scale R :=
    ((sequence_subexponential_upper_const hs A).mul
      (((sequence_subexponential_upper_const hs 1).add hRH hs).pow hs
        (Eventually.of_forall (fun n => by linarith [hRH0 n])) p)
      (Eventually.of_forall (fun _ => hA))).mul hRE
      (Eventually.of_forall (fun n => mul_nonneg hA (pow_nonneg (by linarith [hRH0 n]) _)))
  intro δ hδ
  filter_upwards [hR δ hδ] with n hn γ h v hh hw hv
  have hpow : (1 + ‖(finBasis ℝ H).equivFun h‖) ^ p ≤ (1 + RH n) ^ p :=
    pow_le_pow_left₀ (by positivity) (by linarith) p
  have he : Real.exp (K * ‖eW (heightProjection T.character (h : L))‖) ≤
      Real.exp (K * (δ * scale n)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hw hK)
  have hr0 : 0 ≤ A * (1 + RH n) ^ p * Real.exp (K * (δ * scale n)) := by
    exact mul_nonneg (mul_nonneg hA (pow_nonneg (by linarith [hRH0 n]) _))
      (Real.exp_nonneg _)
  calc
    _ ≤ A * (1 + ‖(finBasis ℝ H).equivFun h‖) ^ p *
        Real.exp (K * ‖eW (heightProjection T.character (h : L))‖) *
          ‖(WordBasisSelections.basis M.letter M.wordList γ).equivFun v‖ := hbound γ h v
    _ ≤ A * (1 + RH n) ^ p * Real.exp (K * (δ * scale n)) *
        (RE n * Real.exp (δ * scale n)) := by
      apply mul_le_mul _ hv (norm_nonneg _) hr0
      exact mul_le_mul (mul_le_mul_of_nonneg_left hpow hA) he
        (Real.exp_nonneg _) (mul_nonneg hA (pow_nonneg (by linarith [hRH0 n]) _))
    _ = R n * Real.exp ((K + 1) * δ * scale n) := by
      dsimp [R]
      rw [show (K + 1) * δ * scale n = K * (δ * scale n) + δ * scale n by ring,
        Real.exp_add]
      ring
    _ ≤ Real.exp (δ * scale n) * Real.exp ((K + 1) * δ * scale n) :=
      mul_le_mul_of_nonneg_right hn (Real.exp_nonneg _)
    _ = Real.exp ((K + 2) * δ * scale n) := by
      rw [← Real.exp_add]
      congr 1
      ring


end PolycyclicRecognition.CartanWordModel

end

end OAI
