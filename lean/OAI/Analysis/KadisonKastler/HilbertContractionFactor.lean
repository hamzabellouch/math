import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Operator.Extend

namespace OAI

/-! # Contractive factorization through a Hilbert-space operator

This is the range-extension step used for contractive block completions in
the finite-nest distance argument. The factor is constructed on the closed
range and extended by zero on its orthogonal complement.
-/

namespace KadisonKastler

noncomputable section

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- The same operator, with target restricted to the closure of its range. -/
def operatorClosedRangeMap (S : E →L[ℂ] F) :
    E →L[ℂ] S.toLinearMap.range.topologicalClosure :=
  S.codRestrict _ (fun x => Submodule.le_topologicalClosure _ ⟨x, rfl⟩)

omit [CompleteSpace F] in
theorem operatorClosedRangeMap_dense (S : E →L[ℂ] F) :
    DenseRange (operatorClosedRangeMap S) := by
  apply Metric.denseRange_iff.mpr
  intro z ε hε
  obtain ⟨x, hx⟩ := Metric.mem_closure_range_iff.mp z.property ε hε
  exact ⟨x, hx⟩

/-- Norm domination gives a contractive factor on the entire middle Hilbert
space, including when the original operator has nonclosed range. -/
theorem exists_contraction_factor (S : E →L[ℂ] F) (T : E →L[ℂ] G)
    (h : ∀ x, ‖T x‖ ≤ ‖S x‖) :
    ∃ C : F →L[ℂ] G, ‖C‖ ≤ 1 ∧ C.comp S = T := by
  let W := S.toLinearMap.range.topologicalClosure
  let s := operatorClosedRangeMap S
  let c : W →L[ℂ] G := T.toLinearMap.extendOfNorm s.toLinearMap
  have hs : DenseRange s := operatorClosedRangeMap_dense S
  have hn : ∀ x, ‖T.toLinearMap x‖ ≤ (1 : ℝ) * ‖s.toLinearMap x‖ := by
    intro x
    change ‖T x‖ ≤ 1 * ‖S x‖
    simpa only [one_mul] using h x
  have hc : ‖c‖ ≤ 1 := LinearMap.opNorm_extendOfNorm_le hs zero_le_one hn
  refine ⟨c.comp W.orthogonalProjectionOnto, ?_, ?_⟩
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hc W.orthogonalProjectionOnto_norm_le (norm_nonneg W.orthogonalProjectionOnto)
        zero_le_one).trans_eq (mul_one 1))
  · apply ContinuousLinearMap.ext
    intro x
    change c (W.orthogonalProjectionOnto (S x)) = T x
    have hp : W.orthogonalProjectionOnto (S x) = s x :=
      W.orthogonalProjectionOnto_mem_subspace_eq_self (s x)
    rw [hp]
    exact LinearMap.extendOfNorm_eq hs ⟨1, hn⟩ x

end

end KadisonKastler

end OAI
