import OAI.Analysis.KadisonSimilarity.Tracial.GeneratedFiniteFactorModel
import OAI.Analysis.KadisonSimilarity.Representation.ConcreteIrreducibleSubfactor
import OAI.Analysis.KadisonSimilarity.Representation.FiniteTypeIStructure
import OAI.Analysis.KadisonSimilarity.Tracial.DiffuseProjectionStructure

namespace OAI

/-! The finite diffuse branch has a constructed normal trace and an actual
irreducible matrix source. Its sole remaining local input is Popa freeness. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open BoundedHochschild.KadisonRingrose
open scoped ComplexOrder

section GNS
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (htr : ∀ a b, τ (a * b) = τ (b * a))
  (hf : ∀ a, τ (star a * a) = 0 → a = 0) (hnormal : HasNormalGNS τ)

def normalGNSRepresentation :
    TracialRepresentation (representationVonNeumannAlgebra τ.gnsStarAlgHom) :=
  (gnsTracialGeometry τ htr).normalTracialRepresentation h1
    (gnsTracialVector_injective τ hf) _ hnormal

def normalGNSEquivalence :
    A ≃⋆ₐ[ℂ] (representationVonNeumannAlgebra τ.gnsStarAlgHom).toStarSubalgebra :=
  equivalenceOfConcreteRange _ τ.gnsStarAlgHom
    ((gnsTracialGeometry τ htr).left_injective (gnsTracialVector_injective τ hf)) hnormal

theorem normalGNSRepresentation_trace (a : A) :
    (normalGNSRepresentation τ h1 htr hf hnormal).trace
      (normalGNSEquivalence τ htr hf hnormal a) = τ a :=
  (gnsTracialGeometry τ htr).normalTracialRepresentation_trace h1
    (gnsTracialVector_injective τ hf) _ hnormal a

end GNS

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : VonNeumannAlgebra H)

local instance finitePresentationClosed : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (P : Set (H →L[ℂ] H))
  infer_instance

/-- The constructed normalized faithful normal trace. -/
structure NormalFiniteTrace where
  trace : P.toStarSubalgebra →ₚ[ℂ] ℂ
  normal_predual : BoundedHochschild.TraceInPredual (concretePredualEquiv P) trace
  one : trace 1 = 1
  tracial : ∀ a b, trace (a * b) = trace (b * a)
  faithful : ∀ a, trace (star a * a) = 0 → a = 0

/-- The actual increasing irreducible matrix source in a fixed normal representation. -/
structure IrreducibleMatrixSource {K : Type u} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (N : VonNeumannAlgebra K) where
  stages : ℕ → FiniteMatrixStage N
  monotone : Monotone (fun n => (stages n).units.concreteAlgebra)
  source_factor : IsII1Factor (FiniteMatrixStage.generated stages)
  irreducible : ∀ c : N.toStarSubalgebra,
    (∀ a : FiniteMatrixStage.generated stages, a.val * c.val = c.val * a.val) →
    ∃ z : ℂ, c = z • 1

/-- All finite-factor presentation data except the local free position.
The represented Hilbert space is bundled to keep the GNS implementation opaque. -/
structure FiniteFactorPresentation where
  traceData : NormalFiniteTrace P
  K : Type u
  [normed : NormedAddCommGroup K]
  [innerProduct : InnerProductSpace ℂ K]
  [complete : CompleteSpace K]
  N : VonNeumannAlgebra K
  representation : TracialRepresentation N
  equivalence : P.toStarSubalgebra ≃⋆ₐ[ℂ] N.toStarSubalgebra
  trace_equivalence : ∀ a, representation.trace (equivalence a) = traceData.trace a
  source : IrreducibleMatrixSource N

attribute [instance] FiniteFactorPresentation.normed FiniteFactorPresentation.innerProduct
  FiniteFactorPresentation.complete

theorem exists_finiteFactorPresentation [Nontrivial H] [TopologicalSpace.SeparableSpace H]
    (hP : IsII1Factor P.toStarSubalgebra) : Nonempty (FiniteFactorPresentation P) := by
  obtain ⟨τ, hnormal, h1, htr, hf, hn⟩ := exists_faithful_normal_trace P hP.finite
    (fun a ha => hP.factor a (fun b => (ha b).symm))
  obtain ⟨F, _, hmono, _, hII, _, hirr⟩ := exists_gns_irreducible_matrix_subfactor
    (concretePredualEquiv P) τ h1 htr hf hnormal hP.factor hP.diffuse
  exact ⟨{
    traceData := {
      trace := τ
      normal_predual := hnormal
      one := h1
      tracial := htr
      faithful := hf }
    K := τ.GNS
    N := representationVonNeumannAlgebra τ.gnsStarAlgHom
    representation := normalGNSRepresentation τ h1 htr hf hn
    equivalence := normalGNSEquivalence τ htr hf hn
    trace_equivalence := normalGNSRepresentation_trace τ h1 htr hf hn
    source := {
      stages := F
      monotone := hmono
      source_factor := hII
      irreducible := hirr } }⟩

/-- The structural factor split is proved before invoking any free-position input. -/
theorem factor_structural_cases [Nontrivial H]
    (hfactor : ∀ a : P.toStarSubalgebra, (∀ b, a * b = b * a) →
      ∃ c : ℂ, a = algebraMap ℂ P.toStarSubalgebra c) :
    IsII1Factor P.toStarSubalgebra ∨ HasInternalIsometryRows P ∨
      Nonempty (FiniteMatrixFactorModel P) := by
  by_cases hfinite : FiniteAlgebra P.toStarSubalgebra
  · by_cases hab : ∃ p : P.toStarSubalgebra, FinitePathMain.AbelianProjection p ∧ p ≠ 0
    · obtain ⟨p, hp, hp0⟩ := hab
      exact Or.inr (Or.inr (finiteMatrixFactorModel_of_abelian_projection P
        hfinite hfactor p hp hp0))
    · left
      refine {
        nonzero := zero_ne_one
        weaklyClosed := vonNeumann_wotClosed P
        factor := fun a ha => hfactor a (fun b => (ha b).symm)
        finite := hfinite
        diffuse := diffuse_projections_of_no_abelian_projection (concretePredualEquiv P) ?_ }
      intro p hp
      by_contra hp0
      exact hab ⟨p, hp, hp0⟩
  · exact Or.inr (Or.inl (internal_isometry_rows_of_infinite_factor P hfactor hfinite))

namespace FiniteFactorPresentation
variable {P} (F : FiniteFactorPresentation P)

theorem normal : HasNormalGNS F.traceData.trace :=
  hasNormalGNS_of_predual (concretePredualEquiv P) F.traceData.trace F.traceData.normal_predual F.traceData.tracial

def inclusion : (FiniteMatrixStage.generatedVonNeumann F.source.stages).toStarSubalgebra →⋆ₐ[ℂ]
    P.toStarSubalgebra := generatedOriginalInclusion F.equivalence F.source.stages

theorem trace_inclusion (a : (FiniteMatrixStage.generatedVonNeumann F.source.stages).toStarSubalgebra) :
    F.traceData.trace (F.inclusion a) = generatedMatrixTrace F.source.stages F.representation a :=
  generatedOriginalInclusion_trace F.traceData.trace F.representation F.equivalence
    F.trace_equivalence F.source.stages a

def FreePosition (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.cofinite) : Prop :=
  FiniteFactorFreeCornerInputs (generatedMatrixTrace F.source.stages F.representation) F.traceData.trace
    (generatedMatrixTrace_one F.source.stages F.representation) F.traceData.one ω
    (generatedMatrixTrace_tracial F.source.stages F.representation) F.traceData.tracial
    F.inclusion F.trace_inclusion hω

def model (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    (hfree : F.FreePosition ω hω) : FiniteFactorModel P := by
  let e := F.equivalence
  let : Nontrivial F.N.toStarSubalgebra :=
    nontrivial_of_ne (e 0) (e 1) (fun h => by
      have he : (0 : P.toStarSubalgebra) = 1 := e.injective h
      have ht := congrArg F.traceData.trace he
      rw [map_zero, F.traceData.one] at ht
      exact zero_ne_one ht)
  exact generatedFiniteFactorModel F.traceData.trace F.representation F.equivalence
    F.trace_equivalence F.source.stages F.traceData.one F.traceData.tracial
    F.traceData.faithful F.normal F.source.monotone F.source.source_factor.diffuse ω hω hfree

end FiniteFactorPresentation

/-- Factor classification and the normal matrix presentation reduce the
finite diffuse case to prescribed-source free position. -/
theorem publishedFactorCases_of_free_position [Nontrivial H] [TopologicalSpace.SeparableSpace H]
    (hfactor : ∀ a : P.toStarSubalgebra, (∀ b, a * b = b * a) →
      ∃ c : ℂ, a = algebraMap ℂ P.toStarSubalgebra c)
    (hfree : ∀ F : FiniteFactorPresentation P,
      ∃ (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.cofinite), F.FreePosition ω hω) :
    PublishedFactorCasesInput P := by
  rcases factor_structural_cases P hfactor with hfinite | hinfinite | hmatrix
  · obtain ⟨F⟩ := exists_finiteFactorPresentation P hfinite
    obtain ⟨ω, hω, hF⟩ := hfree F
    exact Or.inl ⟨F.model ω hω hF⟩
  · exact Or.inr (Or.inl hinfinite)
  · exact Or.inr (Or.inr hmatrix)

end KadisonSimilarity

end

end OAI
