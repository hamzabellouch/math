import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialQuotientSection
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConeQuotientRestriction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorBridgeComposition

namespace OAI

/-! # The two probe restrictions in the same section coordinates

The first path controls the quotient orbit point in the base frame. The
absorbed bridge controls the ideal residual in the tile-anchor frame.
These restrictions apply simultaneously to each point of the right cell.
-/

noncomputable section
namespace PolycyclicRecognition

open Module Set
open scoped Pointwise

def exponentialIdealKernelRegion {V N Q : Type*} [LieRing V] [LieAlgebra ℝ V]
    [Group N] [Group Q] (U : LieIdeal ℝ V) (π : N →* Q)
    (Exp : V → N) (I : Set U) : Set π.ker :=
  {n | ∃ i ∈ I, (n : N) = Exp (i : V)}

variable {V J EN EQ N Q D G : Type*} [LieRing V] [LieAlgebra ℝ V] [Fintype J]
  [AddCommGroup EN] [Module ℝ EN] [TopologicalSpace EN]
  [IsTopologicalAddGroup EN] [ContinuousSMul ℝ EN]
  [AddCommGroup EQ] [Module ℝ EQ] [TopologicalSpace EQ] [T2Space EQ]
  [IsTopologicalAddGroup EQ] [ContinuousSMul ℝ EQ] [FiniteDimensional ℝ EQ]
  [TopologicalSpace N] [TopologicalSpace Q] [Group N] [Group Q] [Group D] [Group G]
  (U : LieIdeal ℝ V) (bQ : Basis J ℝ (V ⧸ U.toSubmodule))
  (lift : J → V) (hlift : ∀ j, U.toSubmodule.mkQ (lift j) = bQ j)
  (eN : V ≃ₗ[ℝ] EN) (eQ : (V ⧸ U.toSubmodule) ≃ₗ[ℝ] EQ)
  (chartN : EN ≃ₜ N) (chartQ : EQ ≃ₜ Q)
  (π : N →* Q) (hπ : ∀ v, π (chartN (eN v)) = chartQ (eQ (U.toSubmodule.mkQ v)))

omit [Fintype J] in
/-- An actual ideal-times-section factorization places its residual in the
intrinsic kernel region. This is the ideal restriction used in packing. -/
theorem exponential_section_residual_mem
    (hzeroQ : chartQ (eQ 0) = 1) (I : Set U) {n : N}
    (hn : ∃ i ∈ I, ∃ q : V ⧸ U.toSubmodule,
      n = chartN (eN (i : V)) * chartN (eN (quotientLinearSection U bQ lift q))) :
    quotientSectionResidual π
      (exponentialQuotientSection U bQ lift eN eQ chartN chartQ)
      (exponentialQuotientSection_rightInverse U bQ lift hlift eN eQ chartN chartQ π hπ) n ∈
        exponentialIdealKernelRegion U π (chartN ∘ eN) I := by
  obtain ⟨i, hi, q, rfl⟩ := hn
  exact ⟨i, hi,
    exponentialQuotientSection_residual U bQ lift hlift eN eQ chartN chartQ π hπ hzeroQ i q⟩

omit [Fintype J] in
/-- The containing product region is valid for the actual thickened
endpoints and their fixed lifts, with arbitrary quotient translation. -/
theorem thickened_probe_section_restriction
    (hzeroQ : chartQ (eQ 0) = 1)
    (φ : D →* MulAut N) (ι : N →* G) (κ : D →* G)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (α : D →* MulAut Q) (act : G →* Equiv.Perm Q)
    (hact : ∀ n d q, act (ι n * κ d) q = π n * α d q)
    (base anchor endpoint : G) (p : N × D) (n₀ : N) (d₀ : D)
    (hp : anchor⁻¹ * endpoint = ι p.1 * κ p.2)
    (hframe : anchor⁻¹ * base = ι n₀ * κ d₀)
    (cell : Set (N × D)) (T : Set Q) (I : Set U) (B : Set D)
    (hfirst : ∀ z ∈ cell, act (base⁻¹ * (endpoint * (ι z.1 * κ z.2))) 1 ∈ T)
    (hideal : ∀ z ∈ cell, ∃ i ∈ I, ∃ q : V ⧸ U.toSubmodule,
      (factorTranslate φ p z).1 = chartN (eN (i : V)) *
        chartN (eN (quotientLinearSection U bQ lift q)))
    (hD : ∀ z ∈ cell, (factorTranslate φ p z).2 ∈ B) :
    factorTranslate φ p '' cell ⊆
      {n | π n ∈ π n₀ • (α d₀ '' T) ∧
        quotientSectionResidual π
          (exponentialQuotientSection U bQ lift eN eQ chartN chartQ)
          (exponentialQuotientSection_rightInverse U bQ lift hlift eN eQ chartN chartQ π hπ) n ∈
            exponentialIdealKernelRegion U π (chartN ∘ eN) I} ×ˢ B := by
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨⟨?_, ?_⟩, hD z hz⟩
  · have hthick : anchor⁻¹ * (endpoint * (ι z.1 * κ z.2)) =
        ι (factorTranslate φ p z).1 * κ (factorTranslate φ p z).2 := by
      rw [← mul_assoc, hp]
      exact (factorTranslate_projection φ ι κ hc p z).symm
    exact quotient_restriction_in_anchor_frame ι κ π α act hact base anchor
      (endpoint * (ι z.1 * κ z.2))
      (factorTranslate φ p z).1 n₀ (factorTranslate φ p z).2 d₀
      hthick hframe T (hfirst z hz)
  · obtain ⟨i, hi, q, he⟩ := hideal z hz
    refine ⟨i, hi, ?_⟩
    rw [he]
    exact exponentialQuotientSection_residual U bQ lift hlift eN eQ chartN chartQ π hπ hzeroQ i q

end PolycyclicRecognition

end

end OAI
