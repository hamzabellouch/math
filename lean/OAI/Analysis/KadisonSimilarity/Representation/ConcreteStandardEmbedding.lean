import OAI.Analysis.KadisonSimilarity.Tracial.TracialGraphClosability
import OAI.Analysis.KadisonSimilarity.Tracial.ConcreteGNSNormality

namespace OAI

/-! The normal standard embedding is proved when the faithful finite trace
is supplied by a separating vector in the concrete representation. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

/-- A concrete faithful vector trace supplies the standard representation
embedding, including countable multiplicity, with no separate Hiai input. -/
theorem normal_standard_embedding_of_concrete_trace
    (M : VonNeumannAlgebra H)
    [IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H))]
    (υ : TracialRepresentation M) (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (hτ : ∀ a, τ a = υ.trace a) :
    HiaiNormalStandardEmbeddingInput τ M.toStarSubalgebra.subtype := by
  let e : M.toStarSubalgebra ≃⋆ₐ[ℂ] M.toStarSubalgebra := StarAlgEquiv.refl _ _
  have hτe : ∀ a, τ a = υ.trace (e a) := hτ
  let I := concreteGNSIsometry τ M υ e hτe
  have htr (a b : M.toStarSubalgebra) : τ (a * b) = τ (b * a) := by
    rw [hτ, hτ, υ.trace_mul_comm]
  let G := gnsTracialGeometry τ htr
  have hIv (a : M.toStarSubalgebra) : I (G.vector a) = (a : H →L[ℂ] H) υ.vector :=
    concreteGNSIsometry_vector τ M υ e hτe a
  have hI (a : M.toStarSubalgebra) :
      I.toContinuousLinearMap.comp (G.left a) =
        (a : H →L[ℂ] H).comp I.toContinuousLinearMap := by
    ext x
    refine G.dense_vector.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro b
    change I (G.left a (G.vector b)) = (a : H →L[ℂ] H) (I (G.vector b))
    calc
      I (G.left a (G.vector b)) = I (G.vector (a * b)) :=
        congrArg I (G.left_vector a b)
      _ = ((a * b : M.toStarSubalgebra) : H →L[ℂ] H) υ.vector := hIv (a * b)
      _ = (a : H →L[ℂ] H) (I (G.vector b)) :=
        congrArg (fun x : H => (a : H →L[ℂ] H) x) (hIv b).symm
  have hIone : I (G.vector 1) = υ.vector := by
    exact (hIv 1).trans (one_apply_eq_self υ.vector)
  have hsep (a : M.toStarSubalgebra) :
      (a : H →L[ℂ] H) (I (G.vector 1)) = 0 → a = 0 := by
    intro ha
    apply υ.separating a
    exact (congrArg (fun x : H => (a : H →L[ℂ] H) x) hIone).symm.trans ha
  have h := countable_embedding_of_separating_trace_vector G M.toStarSubalgebra.subtype M
    (fun a => a.property) I hI hsep
  exact h

end KadisonSimilarity

end

end OAI
