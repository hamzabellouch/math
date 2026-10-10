import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanWeightDilation
import Mathlib.Algebra.Lie.Derivation.Basic

namespace OAI

/-! # The semisimple derivations attached to canonical height

On a generalized Cartan root space the operator is scalar multiplication by
the root. Its dependence on the canonical height, rather than a choice of
Cartan representative, is proved here.
-/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra LieModule
open scoped DirectSum

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

def cartanWeightOperator (h : H) : L →ₗ[ℝ] L := by
  classical
  exact (DirectSum.toModule ℝ (Weight ℝ H L) L
    (fun χ => χ h • (genWeightSpace L χ).toSubmodule.subtype)).comp
      (cartanWeightDecomposition T H).symm.toLinearMap

theorem cartanWeightOperator_apply_root (h : H) (χ : Weight ℝ H L) {x : L}
    (hx : x ∈ rootSpace H χ) : cartanWeightOperator T H h x = χ h • x := by
  classical
  let S := fun χ : Weight ℝ H L => (genWeightSpace L χ).toSubmodule
  have he : cartanWeightDecomposition T H
      (DirectSum.lof ℝ (Weight ℝ H L) (fun χ => S χ) χ ⟨x, hx⟩) = x :=
    DirectSum.coeLinearMap_lof S χ ⟨x, hx⟩
  change (DirectSum.toModule ℝ (Weight ℝ H L) L
    (fun χ => χ h • (S χ).subtype)) ((cartanWeightDecomposition T H).symm x) = _
  rw [← he, LinearEquiv.symm_apply_apply, DirectSum.toModule_lof]
  rw [he]
  rfl

theorem cartanWeightOperator_apply_genWeight (h : H) (χ : H → ℝ) {x : L}
    (hx : x ∈ genWeightSpace L χ) : cartanWeightOperator T H h x = χ h • x := by
  by_cases hχ : genWeightSpace L χ = ⊥
  · have hx0 : x = 0 := by simpa only [hχ, LieSubmodule.mem_bot] using hx
    simp [hx0]
  · exact cartanWeightOperator_apply_root T H h ⟨χ, hχ⟩ hx

theorem cartanWeightOperator_lie (h : H) (x y : L) :
    cartanWeightOperator T H h ⁅x, y⁆ =
      ⁅x, cartanWeightOperator T H h y⁆ + ⁅cartanWeightOperator T H h x, y⁆ := by
  apply cartan_root_induction T H (x := x)
  · intro χ u hu
    apply cartan_root_induction T H (x := y)
    · intro ψ v hv
      rw [cartanWeightOperator_apply_genWeight T H h (χ + ψ)
        (lie_mem_genWeightSpace_of_mem_genWeightSpace hu hv),
        cartanWeightOperator_apply_root T H h χ hu,
        cartanWeightOperator_apply_root T H h ψ hv]
      simp only [Pi.add_apply, lie_smul, smul_lie, add_smul, add_comm]
    · simp
    · intro v w hv hw
      simp only [lie_add, map_add, hv, hw]
      abel
  · simp
  · intro u v hu hv
    simp only [add_lie, map_add, hu, hv]
    abel

def cartanWeightDerivation (h : H) : LieDerivation ℝ L L where
  toLinearMap := cartanWeightOperator T H h
  leibniz' x y := by
    rw [cartanWeightOperator_lie]
    rw [← lie_skew (cartanWeightOperator T H h x) y]
    exact (sub_eq_add_neg _ _).symm

@[simp]
theorem cartanWeightDerivation_apply_root (h : H) (χ : Weight ℝ H L) {x : L}
    (hx : x ∈ rootSpace H χ) : cartanWeightDerivation T H h x = χ h • x :=
  cartanWeightOperator_apply_root T H h χ hx

theorem cartanWeightDerivation_add (h k : H) :
    cartanWeightDerivation T H (h + k) = cartanWeightDerivation T H h +
      cartanWeightDerivation T H k := by
  apply LieDerivation.ext
  intro x
  apply cartan_root_induction T H (x := x)
  · intro χ u hu
    simp only [LieDerivation.add_apply, cartanWeightDerivation_apply_root T H _ χ hu,
      map_add, add_smul]
  · simp
  · intro u v hu hv
    simp only [map_add, LieDerivation.add_apply] at hu hv ⊢
    rw [hu, hv]

theorem cartanWeightDerivation_smul (r : ℝ) (h : H) :
    cartanWeightDerivation T H (r • h) = r • cartanWeightDerivation T H h := by
  apply LieDerivation.ext
  intro x
  apply cartan_root_induction T H (x := x)
  · intro χ u hu
    simp only [LieDerivation.smul_apply, cartanWeightDerivation_apply_root T H _ χ hu,
      map_smul, smul_eq_mul, smul_smul]
  · simp
  · intro u v hu hv
    simp only [map_add, LieDerivation.smul_apply] at hu hv ⊢
    rw [hu, hv]

def cartanWeightDerivationLinear : H →ₗ[ℝ] LieDerivation ℝ L L where
  toFun := cartanWeightDerivation T H
  map_add' := cartanWeightDerivation_add T H
  map_smul' := cartanWeightDerivation_smul T H

theorem cartanWeightDerivation_commute (h k : H) :
    ⁅cartanWeightDerivation T H h, cartanWeightDerivation T H k⁆ = 0 := by
  apply LieDerivation.ext
  intro x
  change cartanWeightDerivation T H h (cartanWeightDerivation T H k x) -
    cartanWeightDerivation T H k (cartanWeightDerivation T H h x) = 0
  apply cartan_root_induction T H (x := x)
  · intro χ u hu
    rw [cartanWeightDerivation_apply_root T H k χ hu, map_smul,
      cartanWeightDerivation_apply_root T H h χ hu, map_smul,
      cartanWeightDerivation_apply_root T H k χ hu]
    simp only [smul_smul, mul_comm, sub_self]
  · simp
  · intro u v hu hv
    simp only [map_add, sub_eq_zero.mp hu, sub_eq_zero.mp hv, sub_self]

/-- The chosen Cartan section disappears from the eigenvalues: they are the
canonical height weights. -/
def heightSemisimpleAction : L →ₗ[ℝ] LieDerivation ℝ L L :=
  (cartanWeightDerivationLinear T H).comp
    ((cartanHeightSection T H).comp (heightProjection T.character))

theorem heightSemisimpleAction_apply_root (x : L) (χ : Weight ℝ H L) {y : L}
    (hy : y ∈ rootSpace H χ) :
    heightSemisimpleAction T H x y =
      cartanHeightWeight T H χ (heightProjection T.character x) • y :=
  cartanWeightDerivation_apply_root T H _ χ hy

theorem heightSemisimpleAction_lie (x y : L) :
    heightSemisimpleAction T H ⁅x, y⁆ = 0 := by
  change cartanWeightDerivationLinear T H
    (cartanHeightSection T H (heightProjection T.character ⁅x, y⁆)) = 0
  rw [T.height_lie, map_zero, map_zero]

theorem heightSemisimpleAction_commute (x y : L) :
    ⁅heightSemisimpleAction T H x, heightSemisimpleAction T H y⁆ = 0 :=
  cartanWeightDerivation_commute T H _ _

theorem heightSemisimpleAction_height_zero (x y : L) :
    heightProjection T.character (heightSemisimpleAction T H x y) = 0 := by
  apply cartan_root_induction T H (x := y)
  · intro χ v hv
    rw [heightSemisimpleAction_apply_root T H x χ hv, map_smul]
    by_cases hχ : χ.IsNonZero
    · have hk : v ∈ T.kernelIdeal := cartanRootIdeal_le_kernel H T
        (LieSubmodule.subset_lieSpan ⟨χ, hχ, hv⟩)
      rw [show heightProjection T.character v = 0 from
        (Submodule.Quotient.mk_eq_zero _).mpr hk, smul_zero]
    · have hz : (χ : H → ℝ) = 0 := not_not.mp hχ
      have hc : cartanHeightWeight T H χ (heightProjection T.character x) = 0 :=
        congrFun hz _
      rw [hc, zero_smul]
  · simp
  · intro u v hu hv
    simp only [map_add, hu, hv, add_zero]

theorem heightSemisimpleAction_annihilate (x y : L) :
    heightSemisimpleAction T H (heightSemisimpleAction T H x y) = 0 := by
  change cartanWeightDerivationLinear T H (cartanHeightSection T H
    (heightProjection T.character (heightSemisimpleAction T H x y))) = 0
  rw [heightSemisimpleAction_height_zero, map_zero, map_zero]

end PolycyclicRecognition

end

end OAI
