import OAI.Analysis.KadisonKastler.ProjectionStratumFields
import OAI.Analysis.KadisonKastler.MeasurableFiberRepresentations

namespace OAI

/-! # The compressed field agrees with the genuine fixed-fiber representation -/

namespace KadisonKastler

open scoped lp

noncomputable section

variable {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : X → H →L[ℂ] H) (hP : ∀ x, IsIdempotentElem (P x))
  (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤)

theorem compressedStratumField_eq_operator (R : X → H →L[ℂ] H)
    (hR : ∀ x v, v ∈ (P x).range → R x v ∈ (P x).range)
    (n : ℕ) (x : projectionRankStratum P b n) :
    compressedStratumField P hP b hb R n x = projectionStratumOperator P hP b hb R hR n x := by
  apply ContinuousLinearMap.ext
  intro v
  let e := projectionStratumCoordinates P hP b hb n x
  let w := e.symm v
  have hw : R x.val (w : H) ∈ (P x.val).range := hR x.val w w.property
  have hfix : P x.val (R x.val (w : H)) = R x.val (w : H) := by
    obtain ⟨z, hz⟩ := hw
    rw [← hz]
    exact congrArg (fun T : H →L[ℂ] H => T z) (hP x.val)
  rw [projectionStratumOperator_apply]
  change e ⟨P x.val (R x.val (w : H)), ⟨R x.val (w : H), rfl⟩⟩ =
    e ⟨R x.val (w : H), hw⟩
  exact congrArg e (Subtype.ext hfix)

variable {A : Type*} [CStarAlgebra A]

theorem compressedStratumField_eq_fixedFiberRepresentation
    (ρ : X → A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (a : A) (n : ℕ)
    (x : projectionRankStratum (representationUnitProjection ρ) b n) :
    compressedStratumField (representationUnitProjection ρ)
      (representationUnitProjection_idempotent ρ) b hb (fun x => ρ x a) n x =
        fixedFiberRepresentation ρ b hb n x a := by
  rw [fixedFiberRepresentation_eq]
  exact compressedStratumField_eq_operator _ _ b hb _
    (representationUnitProjection_invariant ρ a) n x

end

end KadisonKastler

end OAI
