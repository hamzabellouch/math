import OAI.Analysis.KadisonKastler.FreeHaarConjugation
import OAI.Analysis.KadisonKastler.PopaPosition

namespace OAI

/-! # Applying second-stage independence to the actual finite base projection -/

namespace KadisonKastler

noncomputable section

variable {B : Type*} [CStarAlgebra B]

theorem traceBaseProjection_finiteBaseExpectation (τ : FaithfulTracialState B)
    (D : StarSubalgebra ℂ B) [FiniteDimensional ℂ D] :
    TraceBaseProjection τ D (finiteBaseExpectation τ D) where
  mem := finiteBaseExpectation_mem τ D
  pairing := fun _ hb x => finiteBaseExpectation_pairing τ D x hb

/-- The exact test space used by the second finite-base independence
application yields scalar freeness relative to the prescribed algebra. -/
theorem freeHaarMoments_of_position_independence
    {τ : FaithfulTracialState B} {D A : StarSubalgebra ℂ B}
    [FiniteDimensional ℂ D] (hDA : D ≤ A) {s w : unitary B}
    (hs : FreeHaarMoments τ D s)
    (hw : ∀ d ∈ D, Commute (w : B) d)
    (hind : HaarEndpointIndependence τ D (positionTestSpace τ D A (s : B)) w) :
    FreeHaarMoments τ A (w * s * star w) := by
  have hAT : A ≤ positionAlgebra A (s : B) := by
    intro a ha
    exact StarAlgebra.subset_adjoin ℂ _ (Or.inl ha)
  have hsT : (s : B) ∈ positionAlgebra A (s : B) :=
    StarAlgebra.subset_adjoin ℂ _ (Or.inr (Set.mem_singleton _))
  exact freeHaarMoments_of_second_independence
    (traceBaseProjection_finiteBaseExpectation τ D) hs
    (hDA.trans hAT) hAT hsT hw hind

/-- Popa's finite-base independence, together with the proved scalar
conversion, moves a model Haar unitary into free position relative to `A`. -/
theorem FiniteBaseIndependence.exists_conjugated_freeHaar
    {τ : FaithfulTracialState B} (h : FiniteBaseIndependence τ)
    (D A : StarSubalgebra ℂ B) [FiniteDimensional ℂ D]
    (hDA : D ≤ A) (hA : TraceSeparable τ (A : Set B))
    (s : unitary B) (hs : FreeHaarMoments τ D s) :
    ∃ w : unitary B, (∀ d ∈ D, Commute (w : B) d) ∧
      FreeHaarMoments τ A (w * s * star w) := by
  obtain ⟨w, hw, _, hind⟩ := h.exists_position D A hA (s : B)
  exact ⟨w, hw, freeHaarMoments_of_position_independence hDA hs hw hind⟩

end

end KadisonKastler

end OAI
