import OAI.GroupTheory.PolycyclicRecognition.Analysis.IdealSectionBoxCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Algebra.QuotientSectionCoordinates
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

/-! # The selected pure-word section in actual exponential coordinates -/

noncomputable section
namespace PolycyclicRecognition

open Module

variable {V J EN EQ N Q : Type*} [LieRing V] [LieAlgebra ℝ V] [Fintype J]
  [AddCommGroup EN] [Module ℝ EN] [TopologicalSpace EN]
  [IsTopologicalAddGroup EN] [ContinuousSMul ℝ EN]
  [AddCommGroup EQ] [Module ℝ EQ] [TopologicalSpace EQ] [T2Space EQ]
  [IsTopologicalAddGroup EQ] [ContinuousSMul ℝ EQ] [FiniteDimensional ℝ EQ]
  [TopologicalSpace N] [TopologicalSpace Q] [Group N] [Group Q]
  (U : LieIdeal ℝ V) (bQ : Basis J ℝ (V ⧸ U.toSubmodule))
  (lift : J → V) (hlift : ∀ j, U.toSubmodule.mkQ (lift j) = bQ j)
  (eN : V ≃ₗ[ℝ] EN) (eQ : (V ⧸ U.toSubmodule) ≃ₗ[ℝ] EQ)
  (chartN : EN ≃ₜ N) (chartQ : EQ ≃ₜ Q)

/-- The prescribed linear quotient section, transported through the two
actual global exponential charts. -/
def exponentialQuotientSection : C(Q, N) :=
  let σ := (eN.toLinearMap.comp (quotientLinearSection U bQ lift)).comp eQ.symm.toLinearMap
  ⟨fun q => chartN (σ (chartQ.symm q)),
    chartN.continuous.comp (σ.continuous_of_finiteDimensional.comp chartQ.symm.continuous)⟩

omit [Fintype J] [Group N] [Group Q] in
@[simp] theorem exponentialQuotientSection_apply (q : V ⧸ U.toSubmodule) :
    exponentialQuotientSection U bQ lift eN eQ chartN chartQ (chartQ (eQ q)) =
      chartN (eN (quotientLinearSection U bQ lift q)) := by
  simp [exponentialQuotientSection]

omit [Fintype J] in
include hlift in
/-- Naturality of the actual quotient exponential proves that this is a
right inverse of the group quotient. -/
theorem exponentialQuotientSection_rightInverse (π : N →* Q)
    (hπ : ∀ v, π (chartN (eN v)) = chartQ (eQ (U.toSubmodule.mkQ v))) :
    ∀ q, π (exponentialQuotientSection U bQ lift eN eQ chartN chartQ q) = q := by
  intro q
  obtain ⟨v, rfl⟩ := chartQ.surjective q
  obtain ⟨v, rfl⟩ := eQ.surjective v
  rw [exponentialQuotientSection_apply, hπ, quotientLinearSection_rightInverse U bQ lift hlift]

include hlift in
omit [Fintype J] in
/-- Factoring off the selected pure-word section gives exactly the kernel
residual used by quotient integration. -/
theorem exponentialQuotientSection_residual (π : N →* Q)
    (hπ : ∀ v, π (chartN (eN v)) = chartQ (eQ (U.toSubmodule.mkQ v)))
    (hzeroQ : chartQ (eQ 0) = 1)
    (u : U) (q : V ⧸ U.toSubmodule) :
    ((quotientSectionResidual π
      (exponentialQuotientSection U bQ lift eN eQ chartN chartQ)
      (exponentialQuotientSection_rightInverse U bQ lift hlift eN eQ chartN chartQ π hπ)
      (chartN (eN (u : V)) * chartN (eN (quotientLinearSection U bQ lift q)))) : N) =
      chartN (eN (u : V)) := by
  have hu : π (chartN (eN (u : V))) = 1 := by
    rw [hπ]
    have hz : U.toSubmodule.mkQ (u : V) = 0 :=
      (Submodule.Quotient.mk_eq_zero U.toSubmodule).mpr u.property
    rw [hz, hzeroQ]
  have hq : π (chartN (eN (quotientLinearSection U bQ lift q))) = chartQ (eQ q) := by
    rw [hπ, quotientLinearSection_rightInverse U bQ lift hlift]
  change (chartN (eN (u : V)) * chartN (eN (quotientLinearSection U bQ lift q))) *
    (exponentialQuotientSection U bQ lift eN eQ chartN chartQ
      (π (chartN (eN (u : V)) * chartN (eN (quotientLinearSection U bQ lift q)))))⁻¹ = _
  rw [map_mul, hu, hq, one_mul, exponentialQuotientSection_apply, mul_inv_cancel_right]

end PolycyclicRecognition

end

end OAI
