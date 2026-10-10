import OAI.Analysis.KadisonSimilarity.Tracial.TracialSubalgebraModels

namespace OAI

/-! Recovery through an intermediate generated algebra. The free-corner
argument is carried out on that algebra's own GNS space; its compression
still recovers the original operator with no change in the bound. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {A P : Type*} [CStarAlgebra A] [CStarAlgebra P]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder P] [StarOrderedRing P]
  (τA : A →ₚ[ℂ] ℂ) (τP : P →ₚ[ℂ] ℂ)
  (L : StarSubalgebra ℂ P) [IsClosed (L : Set P)]
  (φ : A →⋆ₐ[ℂ] P) (hmem : ∀ a, φ a ∈ L) (hφ : ∀ a, τP (φ a) = τA a)

include hφ in
omit [StarOrderedRing A] in
theorem restrictedHom_preserves_trace :
    ∀ a, restrictedPositiveTrace τP L (φ.codRestrict L hmem a) = τA a := hφ

/-- The source embeds in the intermediate algebra's GNS space. -/
def generatedGNSInclusion : τA.GNS →ₗᵢ[ℂ] (restrictedPositiveTrace τP L).GNS :=
  gnsTracialHomIsometry τA (restrictedPositiveTrace τP L) (φ.codRestrict L hmem)
    (restrictedHom_preserves_trace τA τP L φ hmem hφ)

@[simp] theorem generatedGNSInclusion_vector (a : A) :
    generatedGNSInclusion τA τP L φ hmem hφ (gnsTracialVector τA a) =
      gnsTracialVector (restrictedPositiveTrace τP L) (φ.codRestrict L hmem a) :=
  gnsTracialHomIsometry_vector τA (restrictedPositiveTrace τP L) (φ.codRestrict L hmem)
    (restrictedHom_preserves_trace τA τP L φ hmem hφ) a

/-- The intermediate GNS embedding followed by its inclusion is the
original GNS embedding, on all completed vectors. -/
theorem generatedGNSInclusion_comp :
    (restrictedTracialGNSInclusion τP L).toContinuousLinearMap.comp
      (generatedGNSInclusion τA τP L φ hmem hφ).toContinuousLinearMap =
    (gnsTracialHomIsometry τA τP φ hφ).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro ξ
  refine (gnsTracialVector_dense τA).induction_on ξ
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  change restrictedTracialGNSInclusion τP L
    (generatedGNSInclusion τA τP L φ hmem hφ (gnsTracialVector τA a)) =
    gnsTracialHomIsometry τA τP φ hφ (gnsTracialVector τA a)
  rw [generatedGNSInclusion_vector, restrictedTracialGNSInclusion_vector,
    gnsTracialHomIsometry_vector]
  rfl

/-- Compress an ambient operator to the intermediate generated algebra. -/
def generatedGNSCompression (S : τP.GNS →L[ℂ] τP.GNS) :
    (restrictedPositiveTrace τP L).GNS →L[ℂ] (restrictedPositiveTrace τP L).GNS :=
  (restrictedTracialGNSInclusion τP L).toContinuousLinearMap.adjoint.comp
    (S.comp (restrictedTracialGNSInclusion τP L).toContinuousLinearMap)

/-- The GNS restriction preserves every ambient commutator bound. -/
theorem norm_generatedGNSCompression_commutator_le
    (S : τP.GNS →L[ℂ] τP.GNS) (a : L) {c : ℝ}
    (hbound : ‖commutator S (τP.gnsStarAlgHom (a : P))‖ ≤ c) :
    ‖commutator (generatedGNSCompression τP L S)
      ((restrictedPositiveTrace τP L).gnsStarAlgHom a)‖ ≤ c := by
  apply norm_reducing_compression_commutator_le (restrictedTracialGNSInclusion τP L)
    S (τP.gnsStarAlgHom (a : P)) ((restrictedPositiveTrace τP L).gnsStarAlgHom a)
  · exact (gnsTracialHomIsometry_intertwines (restrictedPositiveTrace τP L) τP
      L.subtype (fun _ => rfl) a).symm
  · have h := (gnsTracialHomIsometry_intertwines (restrictedPositiveTrace τP L) τP
        L.subtype (fun _ => rfl) (star a)).symm
    simp only [map_star, ContinuousLinearMap.star_eq_adjoint] at h
    convert h using 1 <;> rfl
  · exact hbound

/-- Small-corner bounds restrict to the generated algebra's GNS model. -/
theorem generatedGNSCompression_traceCornerBound
    (trP : ∀ a b : P, τP (a * b) = τP (b * a))
    (D : StarSubalgebra ℂ P) (S : τP.GNS →L[ℂ] τP.GNS) {t ε : ℝ}
    (hbound : (gnsTracialGeometry τP trP).TraceCornerBound D S t ε) :
    (gnsTracialGeometry (restrictedPositiveTrace τP L)
      (restrictedPositiveTrace_tracial τP L trP)).TraceCornerBound
      (D.comap L.subtype) (generatedGNSCompression τP L S) t ε := by
  intro e he heD hte x
  have h := hbound (e : P) (he.map L.subtype) heD hte
    (TracialCornerGeometry.cornerInclusion L e he x)
  exact norm_generatedGNSCompression_commutator_le τP L S (x : L) h

/-- Commutation with the free subfactor also survives the restriction. -/
theorem generatedGNSCompression_commutes
    (D : StarSubalgebra ℂ P) (S : τP.GNS →L[ℂ] τP.GNS)
    (hcomm : ∀ a : D, S.comp (τP.gnsStarAlgHom (a : P)) =
      (τP.gnsStarAlgHom (a : P)).comp S) :
    ∀ a : D.comap L.subtype,
      (generatedGNSCompression τP L S).comp
        ((restrictedPositiveTrace τP L).gnsStarAlgHom (a : L)) =
      ((restrictedPositiveTrace τP L).gnsStarAlgHom (a : L)).comp
        (generatedGNSCompression τP L S) := by
  intro a
  have hzero : commutator S (τP.gnsStarAlgHom ((a : L) : P)) = 0 :=
    sub_eq_zero.mpr (hcomm ⟨((a : L) : P), a.property⟩)
  have hbound := norm_generatedGNSCompression_commutator_le τP L S (a : L)
    (show ‖commutator S (τP.gnsStarAlgHom ((a : L) : P))‖ ≤ 0 by rw [hzero, norm_zero])
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hbound)

/-- The original compression identity survives insertion of the generated
algebra between the two Hilbert spaces. -/
theorem generatedGNSCompression_recover
    (T : τA.GNS →L[ℂ] τA.GNS) (S : τP.GNS →L[ℂ] τP.GNS)
    (hT : (gnsTracialHomIsometry τA τP φ hφ).toContinuousLinearMap.adjoint.comp
      (S.comp (gnsTracialHomIsometry τA τP φ hφ).toContinuousLinearMap) = T) :
    (generatedGNSInclusion τA τP L φ hmem hφ).toContinuousLinearMap.adjoint.comp
      ((generatedGNSCompression τP L S).comp
        (generatedGNSInclusion τA τP L φ hmem hφ).toContinuousLinearMap) = T := by
  unfold generatedGNSCompression
  rw [compression_through_composite, generatedGNSInclusion_comp τA τP L φ hmem hφ, hT]

/-- A free-corner bound on the intermediate algebra bounds the original
commutator, using the same constant. -/
theorem norm_commutator_le_generated_GNS_compression
    (trP : ∀ a b : P, τP (a * b) = τP (b * a))
    (T : τA.GNS →L[ℂ] τA.GNS) (S : τP.GNS →L[ℂ] τP.GNS)
    (hT : (gnsTracialHomIsometry τA τP φ hφ).toContinuousLinearMap.adjoint.comp
      (S.comp (gnsTracialHomIsometry τA τP φ hφ).toContinuousLinearMap) = T)
    (a : A) :
    ‖commutator T (τA.gnsStarAlgHom a)‖ ≤
      ‖(gnsTracialGeometry (restrictedPositiveTrace τP L)
          (restrictedPositiveTrace_tracial τP L trP)).baseOperator
        (φ.codRestrict L hmem).range
        (commutator (generatedGNSCompression τP L S)
          ((restrictedPositiveTrace τP L).gnsStarAlgHom (φ.codRestrict L hmem a)))‖ :=
  norm_commutator_le_tracial_range_compression τA (restrictedPositiveTrace τP L)
    (restrictedPositiveTrace_tracial τP L trP) (φ.codRestrict L hmem)
    (restrictedHom_preserves_trace τA τP L φ hmem hφ) T (generatedGNSCompression τP L S)
    (generatedGNSCompression_recover τA τP L φ hmem hφ T S hT) a

end KadisonSimilarity

end

end OAI
