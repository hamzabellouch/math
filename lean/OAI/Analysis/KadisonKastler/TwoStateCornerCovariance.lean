import OAI.Analysis.KadisonKastler.TwoStateCornerCocycle
import OAI.Analysis.KadisonKastler.TwoStateCornerEmbedding

namespace OAI

/-! # The modular implementation of each corner action -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H) (Ω ξ : H)
  (m : ModularSpectralResolution (twoStateMatrixAlgebra M) (twoStateMatrixVector Ω ξ))

theorem twoStateCornerAction_reconstruct (t : Multiplicative ℝ) (i : Fin 2)
    (a : Algebra M) :
    twoStateMatrixAut M Ω ξ m t (matrixSlot i i a) =
      matrixSlot i i (twoStateCornerAction M Ω ξ m i t a) :=
  matrixSlot_image_reconstruct _ _ _ (twoStateMatrixAut_fixes_diagonal M Ω ξ m t i)
    (twoStateMatrixAut_fixes_diagonal M Ω ξ m t i) a

theorem twoStateCornerAction_vector (t : Multiplicative ℝ) (i : Fin 2) (a : Algebra M) :
    twoStateCornerEmbedding i ((twoStateCornerAction M Ω ξ m i t a).val
      (twoStateVectorAt Ω ξ i)) =
        (m.group t : TwoStateMatrixHilbert H H →L[ℂ] TwoStateMatrixHilbert H H)
          (twoStateCornerEmbedding i (a.val (twoStateVectorAt Ω ξ i))) := by
  rw [twoStateCornerEmbedding_vector,
    ← twoStateCornerAction_reconstruct M Ω ξ m t i a,
    twoStateCornerEmbedding_vector]
  have he : twoStateMatrixEquiv M (twoStateMatrixAut M Ω ξ m t (matrixSlot i i a)) =
      modularAlgebraAut m t (twoStateMatrixEquiv M (matrixSlot i i a)) := by
    change (twoStateMatrixEquiv M) ((twoStateMatrixEquiv M).symm _) = _
    exact (twoStateMatrixEquiv M).apply_symm_apply _
  rw [he, modularAlgebraAut_coe]
  have hf : (star (m.group t) : TwoStateMatrixHilbert H H →L[ℂ] TwoStateMatrixHilbert H H)
      (twoStateMatrixVector Ω ξ) = twoStateMatrixVector Ω ξ := by
    have he : star (m.group t) = m.group t⁻¹ := by
      change (m.group t)⁻¹ = m.group t⁻¹
      exact (map_inv m.group t).symm
    rw [← Unitary.coe_star, he]
    exact m.isModular.fixes_vector _
  change (m.group t : TwoStateMatrixHilbert H H →L[ℂ] TwoStateMatrixHilbert H H) ((twoStateMatrixEquiv M (matrixSlot i i a)).val
    ((star (m.group t) : TwoStateMatrixHilbert H H →L[ℂ] TwoStateMatrixHilbert H H) (twoStateMatrixVector Ω ξ))) = _
  rw [hf]

end

end KadisonKastler

end OAI
