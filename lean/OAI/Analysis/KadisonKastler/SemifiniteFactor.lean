import OAI.Analysis.KadisonKastler.PublishedProperInfiniteProjection

namespace OAI

/-! # Finite matrix corners in semifinite diffuse factors

The type-II-infinity predicate uses scalar center, two orthogonal isometries,
projection semifiniteness, and diffuseness. Choosing one finite nonzero
projection and applying the countable-copy theorem constructs the
matrix corner and its II₁ factor structure. There is no trace or stability
conclusion in the type predicate. Projection semifiniteness is exactly the
criterion in Blackadar III.1.4.2; III.1.4.6 identifies the properly infinite
continuous semifinite part as type II∞.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

/-- The projection-theoretic description of a type II∞ factor. -/
structure TypeIIInfinityFactor (M : VonNeumannAlgebra H) : Prop where
  factor : ScalarCenter M
  properlyInfinite : ProperlyInfiniteIdentity M
  semifinite : ∀ p : AlgebraProjection M, p.val ≠ 0 →
    ∃ q : AlgebraProjection M, q ≤ p ∧ q.val ≠ 0 ∧ FiniteProjectionIn M q.val
  diffuse : ∀ p : Algebra M, IsStarProjection p → p ≠ 0 →
    ∃ q : Algebra M, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q

/-- One finite nonzero projection is selected from projection semifiniteness. -/
theorem TypeIIInfinityFactor.exists_nonzero_finite_projection (hM : TypeIIInfinityFactor M) :
    ∃ p : AlgebraProjection M, p.val ≠ 0 ∧ FiniteProjectionIn M p.val := by
  let p : AlgebraProjection M := ⟨1, IsStarProjection.one (Algebra M)⟩
  have hp : p.val ≠ 0 := by
    intro hz
    exact hM.properlyInfinite.nonzero (congrArg Subtype.val hz)
  obtain ⟨q, _, hq, hqfinite⟩ := hM.semifinite p hp
  exact ⟨q, hq, hqfinite⟩

/-- The geometric corner data, including the proved II₁ structure of the
initial represented corner. -/
structure FiniteFullMatrixCornerData (M : VonNeumannAlgebra H) where
  projection : AlgebraProjection M
  projection_nonzero : projection.val ≠ 0
  projection_finite : FiniteProjectionIn M projection.val
  matrix : FullMatrixCorner (typeIIIInitialSpace projection)
  matrix_mem : ∀ i j, matrix.entry i j ∈ M
  corner_isII1 : Generator.IsII1Factor
    (representedCorner (typeIIIInitialSpace projection) M
      (matrix.zero_zero ▸ matrix_mem 0 0)).toStarSubalgebra

/-- A type II∞ factor has the concrete finite full matrix-corner data needed
for semifinite perturbation. -/
theorem TypeIIInfinityFactor.nonempty_finiteMatrixCornerData
    [TopologicalSpace.SeparableSpace H] (hM : TypeIIInfinityFactor M)
    (hCopies : PublishedProperInfiniteProjectionCopies.{u}) :
    Nonempty (FiniteFullMatrixCornerData M) := by
  obtain ⟨p, hp, hpfinite⟩ := hM.exists_nonzero_finite_projection
  obtain ⟨q, hq, hqfinite, F, hF⟩ := exists_finite_fullMatrixCorner_of_factor
    hCopies hM.properlyInfinite hM.factor p hp hpfinite
  have hE0 : (typeIIIInitialSpace q).starProjection ≠ (0 : H →L[ℂ] H) := by
    intro hz
    apply hq
    apply Subtype.ext
    exact (typeIIIInitialSpace_projection q).trans hz
  have hFinite : FiniteProjectionIn M
      ⟨(typeIIIInitialSpace q).starProjection, F.zero_zero ▸ hF 0 0⟩ := by
    have he : (⟨(typeIIIInitialSpace q).starProjection,
        F.zero_zero ▸ hF 0 0⟩ : Algebra M) = q.val :=
      Subtype.ext (typeIIIInitialSpace_projection q).symm
    rw [he]
    exact hqfinite
  exact ⟨{
    projection := q
    projection_nonzero := hq
    projection_finite := hqfinite
    matrix := F
    matrix_mem := hF
    corner_isII1 := F.representedCorner_isII1 M hF hM.factor hE0 hFinite hM.diffuse }⟩

end

end KadisonKastler

end OAI
