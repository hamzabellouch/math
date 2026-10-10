import OAI.Analysis.KadisonKastler.MeasurableFiberRepresentations
import OAI.Analysis.KadisonKastler.RepresentationCommutantInclusion
import OAI.Analysis.KadisonKastler.PublishedCentralDecomposition
import OAI.Analysis.KadisonSimilarity.Representation.GlobalFiberRestriction

namespace OAI

/-! # Scalar centers transported from the actual range to fixed coordinates -/

namespace KadisonKastler

open KadisonSimilarity
open scoped lp

noncomputable section

variable {X A B H : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (ρ : X → B →⋆ₙₐ[ℂ] (H →L[ℂ] H))
  (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤)

theorem fixedFiber_scalarCenter_of_range (ι : A →⋆ₐ[ℂ] B) (n : ℕ)
    (x : projectionRankStratum (representationUnitProjection ρ) b n)
    (hfactor : ∀ a : (representationVonNeumannAlgebra
        (nonunitalRangeRepresentation ((ρ x.val).comp ι.toNonUnitalStarAlgHom))).toStarSubalgebra,
      (∀ c, a * c = c * a) → ∃ z : ℂ, a = algebraMap ℂ _ z) :
    ScalarCenter (generatedVonNeumannAlgebra
      ((fixedFiberRepresentation ρ b hb n x).comp ι).range) := by
  let : CompleteSpace (representationUnitProjection ρ x.val).range :=
    (ContinuousLinearMap.IsIdempotentElem.isClosed_range
      (representationUnitProjection_idempotent ρ x.val)).completeSpace_coe
  let old := nonunitalRangeRepresentation ((ρ x.val).comp ι.toNonUnitalStarAlgHom)
  let new := (fixedFiberRepresentation ρ b hb n x).comp ι
  let e := (nonunitalRestrictionFiberEquiv ι (ρ x.val)).trans
    (projectionStratumCoordinates (representationUnitProjection ρ)
      (representationUnitProjection_idempotent ρ) b hb n x)
  have he (a : A) : e.conjStarAlgEquiv (old a) = new a := by
    apply ContinuousLinearMap.ext
    intro v
    change (projectionStratumCoordinates (representationUnitProjection ρ)
      (representationUnitProjection_idempotent ρ) b hb n x)
        (nonunitalRestrictionFiberEquiv ι (ρ x.val)
          (old a (e.symm v))) = new a v
    rw [nonunitalRestrictionFiberEquiv_intertwines]
    change (projectionStratumCoordinates (representationUnitProjection ρ)
      (representationUnitProjection_idempotent ρ) b hb n x)
        (nonunitalRangeRepresentation (ρ x.val) (ι a)
          ((projectionStratumCoordinates (representationUnitProjection ρ)
            (representationUnitProjection_idempotent ρ) b hb n x).symm v)) = new a v
    rfl
  have hnew : ∀ a : (representationVonNeumannAlgebra new).toStarSubalgebra,
      (∀ c, a * c = c * a) → ∃ z : ℂ, a = algebraMap ℂ _ z := by
    apply scalar_center_of_representation_equiv e.symm.conjStarAlgEquiv new old
    · intro a
      apply e.conjStarAlgEquiv.injective
      change e.conjStarAlgEquiv (e.conjStarAlgEquiv.symm (new a)) = e.conjStarAlgEquiv (old a)
      rw [StarAlgEquiv.apply_symm_apply, he]
    · exact hfactor
  intro T hT hcentral
  have hT' : T ∈ representationVonNeumannAlgebra new := by
    rw [representationVonNeumannAlgebra_eq_generated]
    exact hT
  let a : (representationVonNeumannAlgebra new).toStarSubalgebra := ⟨T, hT'⟩
  obtain ⟨z, hz⟩ := hnew a (fun c => Subtype.ext (by
    exact (hcentral c.val (by
      rw [← representationVonNeumannAlgebra_eq_generated]
      exact c.property)).symm))
  refine ⟨z, ?_⟩
  have hv := congrArg Subtype.val hz
  change T = algebraMap ℂ (ℓ²(projectionDimensionIndex n, ℂ) →L[ℂ]
    ℓ²(projectionDimensionIndex n, ℂ)) z at hv
  simpa only [Algebra.algebraMap_eq_smul_one] using hv

end

end KadisonKastler

end OAI
