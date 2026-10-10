import OAI.Analysis.KadisonKastler.PublishedTypeIIIProjection
import OAI.Analysis.KadisonKastler.CompressedUltraproductSimplicity
import OAI.Analysis.KadisonKastler.ApproximateCommutatorRange

namespace OAI

/-! # Simplicity and commutator correction for type III norm ultraproducts

Spectral cuts, projection comparison, and Sakai innerness give simplicity
of the norm ultraproduct and a uniform coordinate correction for its
invariant derivations.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem TypeIIIFactor.algebraNontrivial {M : VonNeumannAlgebra H}
    (hM : TypeIIIFactor M) : Nontrivial (Algebra M) := by
  refine ⟨⟨1, 0, ?_⟩⟩
  intro h
  exact hM.nonzero (congrArg Subtype.val h)

variable {K : ℕ → Type u} [∀ j, NormedAddCommGroup (K j)]
  [∀ j, InnerProductSpace ℂ (K j)] [∀ j, CompleteSpace (K j)]
  [∀ j, TopologicalSpace.SeparableSpace (K j)]

theorem typeIII_normUltraproduct_simple
    (hSpectral : PublishedVonNeumannSpectralCut.{u})
    (hCompare : PublishedTypeIIIProjectionComparison.{u})
    (M : ∀ j, VonNeumannAlgebra (K j)) (hM : ∀ j, TypeIIIFactor (M j))
    (ω : Ultrafilter ℕ) :
    letI : ∀ j, Nontrivial (Algebra (M j)) := fun j => (hM j).algebraNontrivial
    CStarSimple (NormUltraproduct (fun j => Algebra (M j)) ω) := by
  let : ∀ j, Nontrivial (Algebra (M j)) := fun j => (hM j).algebraNontrivial
  let : ∀ j, LE (Algebra (M j)) := fun j => (CStarAlgebra.spectralOrder _).toLE
  let : ∀ j, PartialOrder (Algebra (M j)) := fun j => CStarAlgebra.spectralOrder _
  let : ∀ j, StarOrderedRing (Algebra (M j)) := fun j => CStarAlgebra.spectralOrderedRing _
  apply normUltraproduct_simple_of_positive_compressions
  intro j x ε hε hx
  exact typeIII_positive_compression hSpectral hCompare (M j) (hM j) x hε hx

theorem exists_typeIII_uniform_commutator_correction
    (hSpectral : PublishedVonNeumannSpectralCut.{u})
    (hCompare : PublishedTypeIIIProjectionComparison.{u})
    (hSakai : PublishedSimpleDerivationInner.{u})
    (M : ∀ j, VonNeumannAlgebra (K j)) (hM : ∀ j, TypeIIIFactor (M j))
    (ω : Ultrafilter ℕ) (T : VaryingBoundedSequence (fun j => K j →L[ℂ] K j))
    (hT : IsSelfAdjoint T) (ε : ℕ → ℝ)
    (hε : Tendsto ε (ω : Filter ℕ) (𝓝 0)) (hε0 : ∀ j, 0 ≤ ε j)
    {R : ℝ} (hR : ∀ j, ε j ≤ R)
    (happrox : ∀ j (x : Algebra (M j)), ∃ y : Algebra (M j),
      ‖T j * (x : K j →L[ℂ] K j) - (x : K j →L[ℂ] K j) * T j -
        (y : K j →L[ℂ] K j)‖ ≤ ε j * ‖x‖) :
    ∃ a : VaryingBoundedSequence (fun j => Algebra (M j)), IsSelfAdjoint a ∧
      Tendsto (fun j => ‖commutatorAlong (M j).toStarSubalgebra.subtype
        (T j - (a j : K j →L[ℂ] K j))‖) (ω : Filter ℕ) (𝓝 0) := by
  let : ∀ j, Nontrivial (Algebra (M j)) := fun j => (hM j).algebraNontrivial
  let : ∀ j, Nontrivial (K j →L[ℂ] K j) := fun j => ⟨⟨1, 0, (hM j).nonzero⟩⟩
  let φ := fun j => (M j).toStarSubalgebra.subtype
  have hφ : ∀ j, Function.Injective (φ j) := fun _ => Subtype.val_injective
  apply exists_uniform_commutator_correction hSakai φ hφ ω
    (typeIII_normUltraproduct_simple hSpectral hCompare M hM ω) T hT
  exact exists_normNull_commutator_approximation φ hφ ω T ε hε hε0 hR happrox

end

end KadisonKastler

end OAI
