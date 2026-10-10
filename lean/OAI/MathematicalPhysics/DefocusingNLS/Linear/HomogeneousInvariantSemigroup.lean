import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFiniteSemigroup
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Analysis.Normed.Operator.Banach

namespace OAI

/-! # Restriction to the finite-dimensional contour space

A projection commuting with the actual evolution has an invariant range.
Strong continuity therefore gives a matrix generator on that range.
-/

open Set
open scoped NNReal

namespace DefocusingNLS

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Explicit topological-ring structure for endomorphisms of the projection range. -/
instance projectionRangeEnd_isTopologicalRing (Q : E →L[ℂ] E) :
    IsTopologicalRing (Q.range →L[ℂ] Q.range) :=
  NonUnitalSeminormedRing.toIsTopologicalRing (α := Q.range →L[ℂ] Q.range)

private theorem projection_range_invariant (S Q : E →L[ℂ] E)
    (h : Commute S Q) : ∀ x ∈ Q.range, S x ∈ Q.range := by
  rintro x ⟨y, rfl⟩
  refine ⟨S y, ?_⟩
  exact (congrArg (fun L : E →L[ℂ] E => L y) h.eq).symm

noncomputable def projectionSemigroupRestriction (S : ℝ≥0 → E →L[ℂ] E)
    (Q : E →L[ℂ] E) (hcomm : ∀ t, Commute (S t) Q) (t : ℝ≥0) :
    Q.range →L[ℂ] Q.range :=
  (S t).restrict (projection_range_invariant (S t) Q (hcomm t))

@[simp] theorem projectionSemigroupRestriction_apply
    (S : ℝ≥0 → E →L[ℂ] E) (Q : E →L[ℂ] E)
    (hcomm : ∀ t, Commute (S t) Q) (t : ℝ≥0) (x : Q.range) :
    (projectionSemigroupRestriction S Q hcomm t x : E) = S t x := rfl

/-- The finite contour space of a strongly continuous semigroup has an
actual matrix generator. -/
theorem projectionSemigroupRestriction_eq_exp
    (S : ℝ≥0 → E →L[ℂ] E) (Q : E →L[ℂ] E)
    (hcomm : ∀ t, Commute (S t) Q)
    (hfin : FiniteDimensional ℂ Q.range)
    (hS : ∀ x : E, Continuous (fun t => S t x)) (hzero : S 0 = 1)
    (hadd : ∀ s t : ℝ≥0, S (s + t) = S t * S s) :
    ∃ G : Q.range →L[ℂ] Q.range, ∀ t : ℝ≥0,
      projectionSemigroupRestriction S Q hcomm t =
        NormedSpace.exp ((t : ℝ) • G) := by
  let : FiniteDimensional ℂ Q.range := hfin
  let R := projectionSemigroupRestriction S Q hcomm
  have hRc (x : Q.range) : Continuous (fun t => R t x) := by
    exact (hS x).subtype_mk (fun t => projection_range_invariant
      (S t) Q (hcomm t) x x.property)
  have hR0 : R 0 = 1 := by
    ext x
    change S 0 (x : E) = x
    rw [hzero]
    rfl
  have hRadd (s t : ℝ≥0) : R (s + t) = R t * R s := by
    ext x
    change S (s + t) (x : E) = S t (S s (x : E))
    rw [hadd]
    rfl
  exact finiteDimensional_semigroup_eq_exp R hRc hR0 hRadd

end

end DefocusingNLS

end OAI
