import OAI.Analysis.KadisonSimilarity.FreeProduct.SourceConjugateFreeness
import OAI.Analysis.KadisonSimilarity.Tracial.ConstantMomentTransport
import OAI.Analysis.KadisonSimilarity.Tracial.GNSSeparableTransport
import OAI.Analysis.KadisonSimilarity.Tracial.TracialInclusionQuantization

namespace OAI

/-! Prescribed-source freeness for an abstract normal tracial inclusion. -/

noncomputable section
namespace KadisonSimilarity
open Generator Generator.Tracial
open UltrapowerBridge (TracialRepresentation)
open HochschildPatching HochschildUltrapower
open scoped ComplexOrder

universe u
variable {A B : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  {φ : A →⋆ₐ[ℂ] B} {τ : B →ₚ[ℂ] ℂ}

namespace TracialInclusionModel
variable (F : TracialInclusionModel φ τ)

local instance modelMomentAmbientClosed : IsClosed (F.M.toStarSubalgebra : Set (F.K →L[ℂ] F.K)) := by
  change IsClosed (F.M : Set (F.K →L[ℂ] F.K))
  infer_instance
local instance modelMomentSourceClosed : IsClosed (F.N.toStarSubalgebra : Set (F.K →L[ℂ] F.K)) := by
  change IsClosed (F.N : Set (F.K →L[ℂ] F.K))
  infer_instance

include F in
omit [PartialOrder A] [StarOrderedRing A] in
theorem exists_source_moments [TopologicalSpace.SeparableSpace τ.GNS]
    (h1 : τ 1 = 1) (tr : ∀ a b, τ (a * b) = τ (b * a))
    (hfactor : ∀ c : A, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1)
    (hdiff : ∀ p : A, IsStarProjection p → p ≠ 0 →
      ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
    (hirr : ∀ c : B, (∀ a : A, φ a * c = c * φ a) → ∃ z : ℂ, c = z • 1)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.atTop) :
    ∃ u : ℕ → unitary A,
      ConstantIntegerMoments τ h1 ω tr (fun n => mapUnitary φ (u n)) := by
  let τF := vectorPositiveFunctional F.M F.representation.vector
  let : TopologicalSpace.SeparableSpace τF.GNS :=
    gns_separable_of_trace_equiv τ τF F.ambientEquiv F.trace_eq
  obtain ⟨v, hv⟩ := exists_source_constant_integer_moments F.representation F.le
    (F.source_factor hfactor) (F.source_diffuse hdiff) (F.source_irreducible hirr) ω hω
  let u : ℕ → unitary A := fun n => mapUnitary F.sourceEquiv.symm.toStarAlgHom (v n)
  have he (n : ℕ) : mapUnitary F.ambientEquiv.toStarAlgHom (mapUnitary φ (u n)) =
      mapUnitary (coordinateInclusion F.le) (v n) := by
    apply Subtype.ext
    change F.ambientEquiv (φ (F.sourceEquiv.symm (v n : F.N.toStarSubalgebra))) =
      coordinateInclusion F.le (v n : F.N.toStarSubalgebra)
    rw [← F.compatible, F.sourceEquiv.apply_symm_apply]
  refine ⟨u, constantIntegerMoments_of_map τ τF h1 F.representation.trace_one ω tr
    F.representation.trace_mul_comm F.ambientEquiv.toStarAlgHom F.trace_eq
    (fun n => mapUnitary φ (u n)) ?_⟩
  simpa only [he] using hv

end TracialInclusionModel

/-- The source-unitary conclusion for a normal tracial inclusion with separable
ambient predual. This is the specialization required by the matrix application. -/
theorem popa1995_of_predual
    {X Y : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    [TopologicalSpace.SeparableSpace Y]
    (eA : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (eB : StrongDual ℂ Y ≃ₗᵢ⋆[ℂ] B)
    (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
    (hnA : BoundedHochschild.TraceInPredual eA τA)
    (hnB : BoundedHochschild.TraceInPredual eB τB)
    (h1A : τA 1 = 1) (h1B : τB 1 = 1)
    (trA : ∀ a b, τA (a * b) = τA (b * a))
    (trB : ∀ a b, τB (a * b) = τB (b * a))
    (hfB : ∀ a, τB (star a * a) = 0 → a = 0)
    (ψ : A →⋆ₐ[ℂ] B) (hi : Function.Injective ψ)
    (ht : ∀ a, τB (ψ a) = τA a)
    (hfactor : ∀ c : A, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1)
    (hdiff : ∀ p : A, IsStarProjection p → p ≠ 0 →
      ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
    (hirr : ∀ c : B, (∀ a : A, ψ a * c = c * ψ a) → ∃ z : ℂ, c = z • 1)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    {D : Type*} [CStarAlgebra D] (ρ : D →⋆ₐ[ℂ] A) :
    Popa1995ConjugateFreenessInput τA τB h1A h1B ω trA trB ψ ht hω ρ := by
  let : TopologicalSpace.SeparableSpace τB.GNS := gns_separable_of_predual eB τB hnB
  obtain ⟨F⟩ := exists_tracialInclusionModel eA eB τA τB hnA hnB h1B trB hfB ψ hi ht
  obtain ⟨v, hv⟩ := F.exists_source_moments h1B trB hfactor hdiff hirr ω
    (hω.trans_eq Nat.cofinite_eq_atTop)
  exact popaConjugateFreeness_of_constant_moments τA τB h1A h1B ω trA trB ψ ht hω ρ v hv

end KadisonSimilarity

end

end OAI
