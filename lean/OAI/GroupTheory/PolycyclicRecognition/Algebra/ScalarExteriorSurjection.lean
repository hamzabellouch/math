import OAI.GroupTheory.PolycyclicRecognition.Algebra.ScalarAlternatingExtension
import Mathlib.LinearAlgebra.ExteriorPower.Basic

namespace OAI

/-! # Scalar extension preserves a surjective exterior presentation

This uses the integral generators of the exterior power, so it requires no
factorial inversion or freeness assumption.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct
variable (K : Type) [Field K]
variable {M V : Type} [AddCommGroup M] [AddCommGroup V]

def scalarExteriorPresentation {n : ℕ} (F : M [⋀^Fin n]→ₗ[ℤ] V) :
    (⋀[K]^n (K ⊗[ℤ] M)) →ₗ[K] K ⊗[ℤ] V :=
  exteriorPower.alternatingMapLinearEquiv (scalarAlternatingExtension K
    ((scalarTensorUnit K V).compAlternatingMap F))

@[simp] theorem scalarExteriorPresentation_unit {n : ℕ} (F : M [⋀^Fin n]→ₗ[ℤ] V)
    (v : Fin n → M) :
    scalarExteriorPresentation K F
      (exteriorPower.ιMulti K n (fun i => scalarTensorUnit K M (v i))) =
      scalarTensorUnit K V (F v) := by
  rw [scalarExteriorPresentation, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    scalarAlternatingExtension_unit]
  rfl

theorem scalarExteriorPresentation_range_unit {n : ℕ} (F : M [⋀^Fin n]→ₗ[ℤ] V)
    (x : ⋀[ℤ]^n M) :
    scalarTensorUnit K V (exteriorPower.alternatingMapLinearEquiv F x) ∈
      LinearMap.range (scalarExteriorPresentation K F) := by
  have hx : x ∈ Submodule.span ℤ (Set.range (exteriorPower.ιMulti ℤ n)) := by
    rw [exteriorPower.ιMulti_span ℤ n M]
    trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    exact ⟨exteriorPower.ιMulti K n (fun i => scalarTensorUnit K M (v i)),
      scalarExteriorPresentation_unit K F v⟩
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    rw [map_smul, map_smul]
    exact ((LinearMap.range
      (scalarExteriorPresentation K F)).restrictScalars ℤ).smul_mem r hx

theorem scalarExteriorPresentation_surjective {n : ℕ} (F : M [⋀^Fin n]→ₗ[ℤ] V)
    (hF : Function.Surjective (exteriorPower.alternatingMapLinearEquiv F)) :
    Function.Surjective (scalarExteriorPresentation K F) := by
  apply LinearMap.range_eq_top.mp
  suffices ∀ z, z ∈ LinearMap.range (scalarExteriorPresentation K F) from
    top_unique (fun z _ => this z)
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul r v =>
    obtain ⟨x, rfl⟩ := hF v
    simpa only [← scalarTensorUnit_smul] using
      (LinearMap.range (scalarExteriorPresentation K F)).smul_mem r
        (scalarExteriorPresentation_range_unit K F x)
  | add x y hx hy => exact Submodule.add_mem _ hx hy

end PolycyclicRecognition

end

end OAI
