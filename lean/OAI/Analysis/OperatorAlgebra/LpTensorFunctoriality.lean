import OAI.Analysis.Nuclearity.MinimalCornerNorm
import OAI.Analysis.OperatorAlgebra.CanonicalLpOperations

namespace OAI

/-! Contractive tensor maps into the canonical L² operator algebra.  The
operator structures are fixed before substituting concrete representations. -/
noncomputable section
open MeasureTheory
namespace WeakPureInfiniteness
universe u
variable {A B H : Type u} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma lp_norm_minimalSum_map_le {I : Type*} [Fintype I]
    (φ : A →⋆ₙₐ[ℂ] (Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)))
    (ψ : B →⋆ₙₐ[ℂ] (Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))ᵐᵒᵖ)
    (a : I → A) (b : I → B) :
    ‖∑ i, minimalElementary (canonicalLpOperator (φ (a i)))
      (MulOpposite.op (canonicalLpOperator (ψ (b i)).unop))‖ ≤
      ‖∑ i, minimalElementary (a i) (b i)‖ := by
  have h := NonUnitalStarAlgHom.norm_apply_le (minimalMapAny φ ψ)
    (∑ i, minimalElementary (a i) (b i))
  simp only [map_sum, minimalMapAny_elementary] at h
  simpa only [canonicalLpOperator_eq, MulOpposite.op_unop] using h

end WeakPureInfiniteness

end

end OAI
