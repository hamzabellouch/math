import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Nonunital.UniformGamma
import OAI.Analysis.JiangSu.Nuclearity.NuclearUnitization
import OAI.Analysis.JiangSu.TensorProducts.Spatial

namespace OAI

section
attribute [-instance] Pureness.CStarAlgebraNorm.completionCStarAlgebra
noncomputable section
open scoped InnerProductSpace ComplexOrder TensorProduct

local instance (priority := 2000) spatialHilbertFastNonunitalCanonicalSpatialGroup (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    NormedAddCommGroup (UnitalTomsWinter.StabilizationHilbert H) :=
  @UniformSpace.Completion.instNormedAddCommGroup (H ⊗[ℂ] TraceCone.StandardHilbert)
    TensorProduct.instNormedAddCommGroup.toSeminormedAddCommGroup
local instance (priority := 2000) spatialHilbertFastNonunitalCanonicalSpatialSemi (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    SeminormedAddCommGroup (UnitalTomsWinter.StabilizationHilbert H) :=
  (spatialHilbertFastNonunitalCanonicalSpatialGroup H).toSeminormedAddCommGroup
local instance (priority := 2000) spatialHilbertFastNonunitalCanonicalSpatialInner (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    InnerProductSpace ℂ (UnitalTomsWinter.StabilizationHilbert H) :=
  UniformSpace.Completion.innerProductSpace
local instance (priority := 2000) nonunitalSpatialInlineNonunitalCanonicalSpatialRing (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    Ring (UnitalTomsWinter.StabilizationOperators H) := ContinuousLinearMap.ring
local instance (priority := 2000) nonunitalSpatialInlineNonunitalCanonicalSpatialCStar (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    CStarAlgebra (UnitalTomsWinter.StabilizationOperators H) := instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace
local instance (priority := 2000) nonunitalSpatialInlineNonunitalCanonicalSpatialSemiring (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    Semiring (UnitalTomsWinter.StabilizationOperators H) := (nonunitalSpatialInlineNonunitalCanonicalSpatialRing H).toSemiring
local instance (priority := 2000) nonunitalSpatialInlineNonunitalCanonicalSpatialNonSemiring (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    NonUnitalSemiring (UnitalTomsWinter.StabilizationOperators H) := (nonunitalSpatialInlineNonunitalCanonicalSpatialRing H).toNonUnitalSemiring
local instance (priority := 2000) nonunitalSpatialInlineNonunitalCanonicalSpatialNonAssoc (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    NonUnitalNonAssocSemiring (UnitalTomsWinter.StabilizationOperators H) :=
  (nonunitalSpatialInlineNonunitalCanonicalSpatialRing H).toNonUnitalNonAssocSemiring
local instance (priority := 2000) nonunitalSpatialInlineNonunitalCanonicalSpatialAdd (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    AddMonoid (UnitalTomsWinter.StabilizationOperators H) := ContinuousLinearMap.instAddMonoid

namespace NonunitalGamma.Spatial
open TraceCone Pureness
open scoped CStarAlgebra

variable (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def canonicalRepresentation :=
  (stateHilbertRepresentation (Unitization ℂ A)).toNonUnitalStarAlgHom.comp
    (Unitization.inrNonUnitalStarAlgHom ℂ A)

omit [PartialOrder A] [StarOrderedRing A] in
lemma canonicalRepresentation_injective : Function.Injective (canonicalRepresentation A) :=
  (stateHilbertRepresentation_injective (Unitization ℂ A)).comp Unitization.inr_injective

abbrev CanonicalStabilization := SpatialStabilization (canonicalRepresentation A)

def canonicalSpatialEquiv : MatrixLimit A ≃⋆ₐ[ℂ] CanonicalStabilization A :=
  spatialEquiv (canonicalRepresentation A) (canonicalRepresentation_injective A)

end NonunitalGamma.Spatial

end
end

noncomputable section
namespace NonunitalGamma
open Pureness CurrentMain Filter
open scoped ComplexOrder

variable {A : Type} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (NormalizedTrace A)] [TopologicalSpace.SeparableSpace A]
variable [CompactSpace (NormalizedTrace A)]

theorem stably_projectionless_uniform_gamma
    (U : Ultrafilter ℕ) (hfree : (U : Filter ℕ) ≤ atTop)
    (hsimple : NonunitalGamma.TopologicallySimple A) (hstable : StablyProjectionless A)
    (hcone : AllDenselyFiniteTracesBounded A) (hcmp : NonunitalGamma.StrictComparison hcone)
    (hnuc : NuclearUnitization.IsNuclear A) : UniformGamma A U :=
  stably_projectionless_uniform_gamma_of_nuclear_unitization U hfree hsimple hstable hcone hcmp
    (NuclearUnitization.nuclear_unitization hnuc)

end NonunitalGamma

end

end OAI
