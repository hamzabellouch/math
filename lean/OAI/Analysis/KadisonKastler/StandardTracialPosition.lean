import OAI.Analysis.KadisonKastler.TracialHilbertConjugation
import OAI.Analysis.KadisonKastler.BoundaryFiniteIsomorphism

namespace OAI

/-! # Concrete standard tracial position

A faithful vector trace and cyclicity suffice to construct the standard
tracial conjugation. Its isometry and involution are proved rather than
included in the common-position input.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The minimal concrete data for a standard tracial representation. -/
structure StandardTracialPosition (M : VonNeumannAlgebra H) where
  trace : FaithfulTracialState (Algebra M)
  vector : H
  trace_eq : ∀ a : Algebra M, trace.toLinearMap a = inner ℂ vector (a.val vector)
  cyclic : DenseRange (algebraVectorMap M vector)

namespace StandardTracialPosition

variable {M : VonNeumannAlgebra H} (p : StandardTracialPosition M)

theorem vector_norm : ‖p.vector‖ = 1 := by
  have h : inner ℂ p.vector p.vector = 1 := by
    simpa only [OneMemClass.coe_one, one_apply_eq_self, p.trace.map_one] using
      (p.trace_eq 1).symm
  have hn := congrArg Complex.re h
  have hs : ‖p.vector‖ ^ 2 = 1 :=
    (inner_self_eq_norm_sq (𝕜 := ℂ) p.vector).symm.trans hn
  nlinarith [norm_nonneg p.vector]

theorem vectorMap_norm (a : Algebra M) :
    ‖algebraVectorMap M p.vector a‖ = traceTwoNorm p.trace a := by
  unfold traceTwoNorm
  rw [p.trace_eq]
  change ‖a.val p.vector‖ =
    Real.sqrt (inner ℂ p.vector ((star a.val * a.val) p.vector)).re
  rw [ContinuousLinearMap.star_eq_adjoint]
  exact ContinuousLinearMap.apply_norm_eq_sqrt_inner_adjoint_right a.val p.vector

theorem finiteVectorTrace : FiniteVectorTrace p.trace := by
  refine ⟨1, fun _ => p.vector, fun _ => p.vector, ?_⟩
  intro a
  simpa only [Fin.sum_univ_one] using p.trace_eq a

theorem separating : Function.Injective (algebraVectorMap M p.vector) :=
  traceHilbert_injective _ p.vectorMap_norm

/-- The standard conjugation, constructed from the actual vector trace. -/
def conjugation : H ≃ₗᵢ⋆[ℂ] H :=
  tracialHilbertConjugation p.trace (algebraVectorMap M p.vector) p.vectorMap_norm p.cyclic

@[simp]
theorem conjugation_algebraVector (a : Algebra M) :
    p.conjugation (a.val p.vector) = (star a).val p.vector :=
  tracialHilbertConjugation_embedding p.trace (algebraVectorMap M p.vector)
    p.vectorMap_norm p.cyclic a

theorem conjugation_involutive : Function.Involutive p.conjugation :=
  tracialHilbertConjugation_involutive p.trace (algebraVectorMap M p.vector)
    p.vectorMap_norm p.cyclic

@[simp]
theorem conjugation_vector : p.conjugation p.vector = p.vector := by
  simpa only [OneMemClass.coe_one, one_apply_eq_self, star_one] using
    p.conjugation_algebraVector 1

end StandardTracialPosition

end

end KadisonKastler

end OAI
