import OAI.Analysis.BoundedHochschild.SpectralProjections

namespace OAI

/-! Vanishing of the diagonal projection defects implies the full right
module identity, by the density of the span of projections. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [PartialOrder M] [StarOrderedRing M] in
lemma right_module_on_projections (T : M →L[ℂ] M)
    (hT : ∀ a p : M, IsStarProjection p → T a * p - T (a * p) * p = 0)
    (a p : M) (hp : IsStarProjection p) : T (a * p) = T a * p := by
  have hd := sub_eq_zero.mp (hT a p hp)
  have hc := sub_eq_zero.mp (hT (a * p) (1-p) hp.one_sub)
  have hz : a * p * (1-p) = 0 := by rw [mul_assoc, hp.mul_one_sub_self, mul_zero]
  rw [hz, map_zero, zero_mul] at hc
  calc
    T (a * p) = T (a * p) * p + T (a * p) * (1-p) := by
      rw [← mul_add, add_sub_cancel, mul_one]
    _ = T a * p := by rw [← hd, hc, add_zero]

theorem right_module_of_projection_defects (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (T : M →L[ℂ] M)
    (hT : ∀ a p : M, IsStarProjection p → T a * p - T (a * p) * p = 0) :
    ∀ a b : M, T (a * b) = T a * b := by
  intro a
  let L := T.comp (ContinuousLinearMap.mul ℂ M a) - ContinuousLinearMap.mul ℂ M (T a)
  have hspan : Submodule.span ℂ {p : M | IsStarProjection p} ≤ L.ker := by
    apply Submodule.span_le.mpr
    intro p hp
    change T (a * p) - T a * p = 0
    rw [right_module_on_projections T hT a p hp, sub_self]
  have hclosed := Submodule.topologicalClosure_minimal _ hspan L.isClosed_ker
  rw [HochschildSakai.projection_span_dense e] at hclosed
  intro b
  exact sub_eq_zero.mp (hclosed (show b ∈ (⊤ : Submodule ℂ M) from trivial))

end BoundedHochschild.KadisonRingrose

end

end OAI
