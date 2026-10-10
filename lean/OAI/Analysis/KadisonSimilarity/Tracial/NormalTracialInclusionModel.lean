import OAI.Analysis.KadisonSimilarity.Tracial.TracialInclusionModel

namespace OAI

/-! A common normal model from closed trace-vector balls. This formulation
applies directly to normalized finite matrix traces. -/

noncomputable section
namespace KadisonSimilarity
open Generator Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

universe u
variable {A B : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem exists_tracialInclusionModel_of_trace_balls
    (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
    (hclosed : ∀ C : ℝ, IsClosed (gnsTracialVector τA '' Metric.closedBall (0 : A) C))
    (h1B : τB 1 = 1) (htrB : ∀ a b, τB (a * b) = τB (b * a))
    (hfB : ∀ a, τB (star a * a) = 0 → a = 0)
    (hnormal : HasNormalGNS τB)
    (φ : A →⋆ₐ[ℂ] B) (hi : Function.Injective φ)
    (ht : ∀ a, τB (φ a) = τA a) : Nonempty (TracialInclusionModel φ τB) := by
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
    tracialInclusion_normal_range υ τA ψ hψ hclosed
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
