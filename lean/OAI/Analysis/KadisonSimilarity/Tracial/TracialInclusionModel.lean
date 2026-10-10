import OAI.Analysis.KadisonSimilarity.Tracial.FiniteFactorPresentation
import OAI.Analysis.KadisonSimilarity.Tracial.TracialInclusionNormality

namespace OAI

/-! Simultaneous normal representations of a trace-preserving inclusion.
The source range is proved closed, retaining the given source algebra. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

universe u
variable {A B : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

structure TracialInclusionModel (φ : A →⋆ₐ[ℂ] B) (τ : B →ₚ[ℂ] ℂ) where
  K : Type u
  [normed : NormedAddCommGroup K]
  [innerProduct : InnerProductSpace ℂ K]
  [complete : CompleteSpace K]
  N : VonNeumannAlgebra K
  M : VonNeumannAlgebra K
  le : N ≤ M
  representation : TracialRepresentation M
  sourceEquiv : A ≃⋆ₐ[ℂ] N.toStarSubalgebra
  ambientEquiv : B ≃⋆ₐ[ℂ] M.toStarSubalgebra
  compatible : ∀ a, coordinateInclusion le (sourceEquiv a) = ambientEquiv (φ a)
  trace_eq : ∀ b, representation.trace (ambientEquiv b) = τ b

attribute [instance] TracialInclusionModel.normed TracialInclusionModel.innerProduct
  TracialInclusionModel.complete

/-- Both given algebras occur as normal ranges on one Hilbert space. -/
theorem exists_tracialInclusionModel
    {X Y : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    (eA : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (eB : StrongDual ℂ Y ≃ₗᵢ⋆[ℂ] B)
    (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
    (hnA : BoundedHochschild.TraceInPredual eA τA)
    (hnB : BoundedHochschild.TraceInPredual eB τB)
    (h1B : τB 1 = 1) (htrB : ∀ a b, τB (a * b) = τB (b * a))
    (hfB : ∀ a, τB (star a * a) = 0 → a = 0)
    (φ : A →⋆ₐ[ℂ] B) (hi : Function.Injective φ)
    (ht : ∀ a, τB (φ a) = τA a) : Nonempty (TracialInclusionModel φ τB) := by
  let hnormal := hasNormalGNS_of_predual eB τB hnB htrB
  let M := representationVonNeumannAlgebra τB.gnsStarAlgHom
  let υ := normalGNSRepresentation τB h1B htrB hfB hnormal
  let f := normalGNSEquivalence τB htrB hfB hnormal
  have hf (b : B) : υ.trace (f b) = τB b :=
    normalGNSRepresentation_trace τB h1B htrB hfB hnormal b
  let ψ : A →⋆ₐ[ℂ] M.toStarSubalgebra := f.toStarAlgHom.comp φ
  have hψ (a : A) : υ.trace (ψ a) = τA a := (hf (φ a)).trans (ht a)
  let σ := M.toStarSubalgebra.subtype.comp ψ
  let N := representationVonNeumannAlgebra σ
  have hrange : σ.range = N.toStarSubalgebra :=
    tracialInclusion_normal_range_of_predual υ τA ψ hψ eA hnA
  have hNM : N ≤ M := by
    intro x hx
    have hx' : x ∈ σ.range := by rw [hrange]; exact hx
    obtain ⟨a, rfl⟩ := hx'
    exact (ψ a).property
  have hσ : Function.Injective σ := by
    intro a b hab
    apply hi
    apply f.injective
    exact Subtype.ext hab
  let g := equivalenceOfConcreteRange N σ hσ hrange
  refine ⟨{
    K := τB.GNS
    N := N
    M := M
    le := hNM
    representation := υ
    sourceEquiv := g
    ambientEquiv := f
    compatible := fun a => ?_
    trace_eq := hf }⟩
  rfl

end KadisonSimilarity

end

end OAI
