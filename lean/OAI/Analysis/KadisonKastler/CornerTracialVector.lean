import OAI.Analysis.KadisonKastler.TracialVectorExistence
import OAI.Analysis.KadisonKastler.CornerFactorStructure

namespace OAI

/-! # A trace vector in a finite diffuse corner of a separating representation -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E] {M : VonNeumannAlgebra H}

theorem representedCorner_vector_separating (hE : E.starProjection ∈ M)
    (Ω : H) (hs : Function.Injective (algebraVectorMap M Ω)) :
    Function.Injective (algebraVectorMap (representedCorner E M hE)
      (E.orthogonalProjectionOnto Ω)) := by
  intro a b hab
  let A : Algebra M := ⟨cornerExtension E a.val, a.property⟩
  let B : Algebra M := ⟨cornerExtension E b.val, b.property⟩
  have hAB : A = B := by
    apply hs
    change cornerExtension E a.val Ω = cornerExtension E b.val Ω
    exact congrArg Subtype.val hab
  apply Subtype.ext
  apply cornerExtension_injective
  exact congrArg Subtype.val hAB

theorem corner_vector_rightIdeal_separating (hE : E.starProjection ∈ M)
    (η : E) (hs : Function.Injective (algebraVectorMap (representedCorner E M hE) η))
    (a : Algebra M) (ha : a.val η.val = 0) : a.val * E.starProjection = 0 := by
  let b : Algebra (representedCorner E M hE) :=
    ⟨cornerCompression E (star a.val * a.val), cornerCompression_mem E hE
      (M.mul_mem (M.star_mem' a.property) a.property)⟩
  have hbη : b.val η = 0 := by
    change E.orthogonalProjectionOnto (star a.val (a.val η.val)) = 0
    rw [ha, map_zero, map_zero]
  have hb0 : b = 0 := hs (by exact hbη)
  have hzero := congrArg (cornerExtension E) (congrArg Subtype.val hb0)
  change cornerExtension E (cornerCompression E (star a.val * a.val)) = cornerExtension E 0 at hzero
  rw [cornerExtension_compression, map_zero] at hzero
  apply (CStarRing.star_mul_self_eq_zero_iff (a.val * E.starProjection)).mp
  simpa only [star_mul, (isStarProjection_starProjection (U := E)).isSelfAdjoint.star_eq,
    mul_assoc] using hzero

theorem corner_vector_tracial (hE : E.starProjection ∈ M) (η : E)
    (ht : ∀ a b : Algebra (representedCorner E M hE),
      inner ℂ η ((a.val * b.val) η) = inner ℂ η ((b.val * a.val) η))
    (a b : Algebra M) :
    inner ℂ η.val ((E.starProjection * a.val * E.starProjection * b.val * E.starProjection) η.val) =
      inner ℂ η.val ((E.starProjection * b.val * E.starProjection * a.val * E.starProjection) η.val) := by
  let A : Algebra (representedCorner E M hE) :=
    ⟨cornerCompression E a.val, cornerCompression_mem E hE a.property⟩
  let B : Algebra (representedCorner E M hE) :=
    ⟨cornerCompression E b.val, cornerCompression_mem E hE b.property⟩
  have he (a b : H →L[ℂ] H) :
      E.starProjection * a * E.starProjection * b * E.starProjection =
        cornerExtension E (cornerCompression E a * cornerCompression E b) := by
    rw [cornerExtension_mul, cornerExtension_compression, cornerExtension_compression]
    have hp := (isStarProjection_starProjection (U := E)).isIdempotentElem.eq
    simp only [← mul_assoc]
    rw [mul_assoc (E.starProjection * a) E.starProjection E.starProjection, hp]
  rw [he, he, cornerExtension_apply, cornerExtension_apply,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  exact ht A B

variable [TopologicalSpace.SeparableSpace H]

theorem exists_corner_tracial_vector (hE : E.starProjection ∈ M)
    (hN : Generator.IsII1Factor (representedCorner E M hE).toStarSubalgebra)
    (Ω : H) (hs : Function.Injective (algebraVectorMap M Ω)) :
    ∃ η : E, ‖η‖ = 1 ∧
      (∀ a : Algebra M, a.val η.val = 0 → a.val * E.starProjection = 0) ∧
      ∀ a b : Algebra M,
        inner ℂ η.val ((E.starProjection * a.val * E.starProjection * b.val * E.starProjection) η.val) =
          inner ℂ η.val ((E.starProjection * b.val * E.starProjection * a.val * E.starProjection) η.val) := by
  obtain ⟨η, hn, hsep, ht⟩ := exists_tracial_vector_of_II1_separating hN
    (E.orthogonalProjectionOnto Ω) (representedCorner_vector_separating hE Ω hs)
  exact ⟨η, hn, corner_vector_rightIdeal_separating hE η hsep,
    corner_vector_tracial hE η ht⟩

end

end KadisonKastler

end OAI
