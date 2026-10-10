import OAI.Analysis.KadisonSimilarity.FreeProduct.TracialInclusionFreeness
import OAI.Analysis.KadisonSimilarity.Tracial.NormalTracialInclusionModel

namespace OAI

/-! The free-position specialization from normal trace models and closed
source trace balls. No predual construction for a matrix algebra is needed. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial HochschildPatching HochschildUltrapower
open scoped ComplexOrder

universe u
variable {A B : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem popa1995_of_normal_traces
    (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
    [TopologicalSpace.SeparableSpace τB.GNS]
    (hclosed : ∀ C : ℝ, IsClosed (gnsTracialVector τA '' Metric.closedBall (0 : A) C))
    (h1A : τA 1 = 1) (h1B : τB 1 = 1)
    (trA : ∀ a b, τA (a * b) = τA (b * a))
    (trB : ∀ a b, τB (a * b) = τB (b * a))
    (hfB : ∀ a, τB (star a * a) = 0 → a = 0) (hnB : HasNormalGNS τB)
    (ψ : A →⋆ₐ[ℂ] B) (hi : Function.Injective ψ)
    (ht : ∀ a, τB (ψ a) = τA a)
    (hfactor : ∀ c : A, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1)
    (hdiff : ∀ p : A, IsStarProjection p → p ≠ 0 →
      ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
    (hirr : ∀ c : B, (∀ a : A, ψ a * c = c * ψ a) → ∃ z : ℂ, c = z • 1)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    {D : Type*} [CStarAlgebra D] (ρ : D →⋆ₐ[ℂ] A) :
    Popa1995ConjugateFreenessInput τA τB h1A h1B ω trA trB ψ ht hω ρ := by
  obtain ⟨F⟩ := exists_tracialInclusionModel_of_trace_balls τA τB hclosed h1B trB hfB hnB ψ hi ht
  obtain ⟨v, hv⟩ := F.exists_source_moments h1B trB hfactor hdiff hirr ω
    (hω.trans_eq Nat.cofinite_eq_atTop)
  exact popaConjugateFreeness_of_constant_moments τA τB h1A h1B ω trA trB ψ ht hω ρ v hv

end KadisonSimilarity

end

end OAI
