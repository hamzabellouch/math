import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanActualConjugation

namespace OAI

/-! # Cancellation of the scalar height action at the probe pivot

After conjugating back by the Cartan pivot, only its polynomial residual
action remains. The root-space calculation is extended to the generated
nilpotent ideal, so mixed bracket words are included.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {a : ℕ} (T : TriangularAdjoint L a)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

theorem cartanIdealWeightDilation_apply_root (h : H) (χ : Weight ℝ H L)
    (v : cartanRootIdeal H) (hv : (v : L) ∈ rootSpace H χ) :
    cartanIdealWeightDilation T H h v = Real.exp (χ h) • v := by
  apply Subtype.ext
  exact cartanWeightScale_apply_root T H h χ hv

theorem cartan_residual_commutes_dilation (h k : H) (v : cartanRootIdeal H) :
    cartanIdealResidualAutomorphism T H h (cartanIdealWeightDilation T H k v) =
      cartanIdealWeightDilation T H k (cartanIdealResidualAutomorphism T H h v) := by
  have hv : v ∈ LieSubalgebra.lieSpan ℝ (cartanRootIdeal H) (cartanGeneratorPool H) := by
    rw [cartanGeneratorPool_lieSpan H T]
    trivial
  induction hv using LieSubalgebra.lieSpan_induction with
  | mem x hx =>
    obtain ⟨χ, _, hx⟩ := hx
    rw [cartanIdealWeightDilation_apply_root T H k χ x hx, map_smul,
      cartanIdealWeightDilation_apply_root T H k χ _
        (cartanIdealResidualAutomorphism_root_mem T H h χ x hx)]
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul t x _ hx => simp only [map_smul, hx]
  | lie x y _ _ hx hy => simp only [LieEquiv.map_lie, hx, hy]

/-- The height dilation cancels exactly, with no estimate on its size. -/
theorem cartan_adjoint_neg_dilation (h : H) (v : cartanRootIdeal H) :
    cartanIdealAdjointAutomorphism T H (-h) (cartanIdealWeightDilation T H h v) =
      cartanIdealResidualAutomorphism T H (-h) v := by
  change cartanIdealWeightDilation T H (-h)
    (cartanIdealResidualAutomorphism T H (-h) (cartanIdealWeightDilation T H h v)) = _
  rw [cartan_residual_commutes_dilation]
  exact (cartanIdealWeightDilation T H h).left_inv _

end PolycyclicRecognition

end

end OAI
