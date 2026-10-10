import OAI.Analysis.KadisonSimilarity.Derivation.CyclicCommutativeModel
import OAI.Analysis.KadisonSimilarity.Representation.StandardEmbeddingAssembly

namespace OAI

/-! The orthogonal cyclic decomposition of a commutative representation,
expressed as an actual Hilbert sum of scalar spectral L² spaces. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A : Type*} [CommCStarAlgebra A]
  (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))

local instance spectralSumMeasurable : MeasurableSpace (WeakDual.characterSpace ℂ A) :=
  borel (WeakDual.characterSpace ℂ A)
local instance spectralSumBorel : BorelSpace (WeakDual.characterSpace ℂ A) := ⟨rfl⟩

variable (D : CyclicDecompositionData π.range)

abbrev CyclicSpectralSpace (i : D.generators) : Type _ :=
  Lp ℂ 2 (commutativeVectorMeasure π (i : H))

theorem cyclic_spectral_range (ξ : H) :
    Set.range (commutativeCyclicIsometry π ξ) = (orbitClosure π.range ξ : Set H) := by
  rw [commutativeCyclicIsometry_range]
  change closure (Set.range (fun a : A => π a ξ)) =
    closure (Set.range (fun a : π.range => (a : H →L[ℂ] H) ξ))
  congr 1
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨π.rangeRestrict a, rfl⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := a.property
    exact ⟨b, congrArg (fun T : H →L[ℂ] H => T ξ) hb⟩

def cyclicSpectralSummands : OrthogonalSummandDecomposition (CyclicSpectralSpace π D) H where
  inclusion i := commutativeCyclicIsometry π (i : H)
  orthogonal i j hij x y := by
    apply D.orthogonal i.property j.property (fun h => hij (Subtype.ext h))
    · have hx := Set.mem_range_self (f := commutativeCyclicIsometry π (i : H)) x
      rw [cyclic_spectral_range π] at hx
      exact hx
    · have hy := Set.mem_range_self (f := commutativeCyclicIsometry π (j : H)) y
      rw [cyclic_spectral_range π] at hy
      exact hy
  dense_span := by
    change (Submodule.span ℂ (⋃ i : D.generators,
      Set.range (commutativeCyclicIsometry π (i : H)))).topologicalClosure = ⊤
    have hs : (⋃ i : D.generators,
        Set.range (commutativeCyclicIsometry π (i : H))) =
        ⋃ ξ ∈ D.generators, (orbitClosure π.range ξ : Set H) := by
      simp only [cyclic_spectral_range π, Set.iUnion_coe_set]
    rw [hs]
    exact D.dense_span

theorem cyclicSpectral_isHilbertSum : IsHilbertSum ℂ (CyclicSpectralSpace π D)
    (cyclicSpectralSummands π D).inclusion := by
  apply IsHilbertSum.mk (cyclicSpectralSummands π D).orthogonal
  have heq : (⨆ i, LinearMap.range ((cyclicSpectralSummands π D).inclusion i).toLinearMap) =
      Submodule.span ℂ (⋃ i, Set.range ((cyclicSpectralSummands π D).inclusion i)) := by
    apply le_antisymm
    · refine iSup_le fun i => ?_
      rintro x ⟨y, rfl⟩
      exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨i, y, rfl⟩)
    · refine Submodule.span_le.mpr ?_
      intro x hx
      obtain ⟨i, y, rfl⟩ := Set.mem_iUnion.mp hx
      exact Submodule.mem_iSup_of_mem i ⟨y, rfl⟩
  rw [heq, (cyclicSpectralSummands π D).dense_span]

def cyclicSpectralEquiv : H ≃ₗᵢ[ℂ] lp (CyclicSpectralSpace π D) 2 :=
  (cyclicSpectral_isHilbertSum π D).linearIsometryEquiv

end KadisonSimilarity

end

end OAI
