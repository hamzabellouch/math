import OAI.Analysis.KadisonKastler.ProductBoundaryCocycle
import OAI.Analysis.KadisonKastler.CountableTraceGroup

namespace OAI

/-! # Scalar invariant vectors in common standard position -/

namespace KadisonKastler

noncomputable section

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Group G] {M : VonNeumannAlgebra H}

namespace StandardTracialPosition

variable (p : StandardTracialPosition M) (U : G →* unitary (Algebra M))

/-- Restrict the actual product representation to the diagonal group. -/
def diagonalRepresentation : G →* unitary (H →L[ℂ] H) :=
  (productBoundaryRepresentation p U).comp
    { toFun := fun g => (g, g)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

@[simp]
theorem diagonalRepresentation_vector (g : G) (x : Algebra M) :
    (p.diagonalRepresentation U g : H →L[ℂ] H) (algebraVectorMap M p.vector x) =
      algebraVectorMap M p.vector ((U g : Algebra M) * x * star (U g : Algebra M)) := by
  change ((productBoundaryRepresentation p U (g, g) : H →L[ℂ] H)) (x.val p.vector) = _
  rw [productBoundaryRepresentation_coe]
  change (U g : Algebra M).val
    (conjugationOperator p.conjugation (U g : Algebra M).val (x.val p.vector)) = _
  rw [conjugationOperator_algebraVector M p.conjugation p.vector p.conjugation_algebraVector]
  change (((U g : Algebra M) * (x * star (U g : Algebra M))).val p.vector) = _
  rw [← mul_assoc]
  rfl

/-- Trace density suffices to identify every invariant vector of the
diagonal representation; no extra invariant-vector input is needed. -/
theorem scalar_of_diagonal_invariant
    (hfactor : ∀ a : Algebra M,
      (∀ b : Algebra M, b * a = a * b) → ∃ c : ℂ, a = c • (1 : Algebra M))
    (hU : ∀ u : unitary (Algebra M), ∀ ε : ℝ, 0 < ε →
      ∃ g, traceTwoNorm p.trace ((u : Algebra M) - U g) < ε)
    (v : H) (hv : ∀ g, (p.diagonalRepresentation U g : H →L[ℂ] H) v = v) :
    ∃ z : ℂ, v = z • p.vector := by
  have hscalar := scalar_of_relative_invariant_coefficients p.trace
    (algebraVectorMap M p.vector) p.vectorMap_norm p.finiteVectorTrace p.cyclic
    (fun x => by
      change inner ℂ ((1 : H →L[ℂ] H) p.vector) (x.val p.vector) = _
      rw [one_apply_eq_self]
      exact (p.trace_eq x).symm)
    (StarAlgHom.id ℂ (Algebra M)) hfactor v
  have hcoeff (g : G) (x : Algebra M) :
      inner ℂ v (algebraVectorMap M p.vector
        ((U g : Algebra M) * x * star (U g : Algebra M))) =
        inner ℂ v (algebraVectorMap M p.vector x) := by
    calc
      _ = inner ℂ ((p.diagonalRepresentation U g : H →L[ℂ] H) v)
          ((p.diagonalRepresentation U g : H →L[ℂ] H)
            (algebraVectorMap M p.vector x)) := by
        rw [hv g, p.diagonalRepresentation_vector U g x]
      _ = _ := Unitary.inner_map_map (p.diagonalRepresentation U g) v
        (algebraVectorMap M p.vector x)
  have hs := hscalar (fun u x => inner_conjugation_invariant_of_traceDense
    p.trace (algebraVectorMap M p.vector) p.vectorMap_norm U hU v hcoeff u x)
  simpa only [algebraVectorMap, LinearMap.coe_mk, AddHom.coe_mk,
    OneMemClass.coe_one, one_apply_eq_self] using hs

end StandardTracialPosition

end

end KadisonKastler

end OAI
