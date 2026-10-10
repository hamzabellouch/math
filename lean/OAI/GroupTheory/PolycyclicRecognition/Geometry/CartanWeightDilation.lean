import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanWeights
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanGenerators
import Mathlib.Analysis.SpecialFunctions.Exp

namespace OAI

/-! # Exact dilations of generalized Cartan weight spaces

Scalar multiplication by `exp (χ h)` on every generalized root space defines
an actual Lie automorphism. The nilpotent parts of the Cartan action do not
enter this construction. These are the exact weight dilations used in the
box-translation argument.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule
open scoped DirectSum

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

include T

def cartanWeightDecomposition :
    (⨁ χ : Weight ℝ H L, (genWeightSpace L χ).toSubmodule) ≃ₗ[ℝ] L := by
  classical
  let := T.isTriangularizable
  exact LinearEquiv.ofBijective (DirectSum.coeLinearMap
    (fun χ : Weight ℝ H L => (genWeightSpace L χ).toSubmodule))
    (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (LieSubmodule.iSupIndep_toSubmodule.mpr (iSupIndep_genWeightSpace' ℝ H L))
      (LieSubmodule.iSup_toSubmodule_eq_top.mpr (iSup_genWeightSpace_eq_top' ℝ H L)))

/-- Scalar dilation on the actual generalized-root direct sum. -/
def cartanWeightScale (h : H) : L →ₗ[ℝ] L := by
  classical
  exact (DirectSum.toModule ℝ (Weight ℝ H L) L
    (fun χ => Real.exp (χ h) • (genWeightSpace L χ).toSubmodule.subtype)).comp
      (cartanWeightDecomposition T H).symm.toLinearMap

theorem cartanWeightScale_apply_root (h : H) (χ : Weight ℝ H L) {x : L}
    (hx : x ∈ rootSpace H χ) : cartanWeightScale T H h x = Real.exp (χ h) • x := by
  classical
  let S := fun χ : Weight ℝ H L => (genWeightSpace L χ).toSubmodule
  have he : cartanWeightDecomposition T H
      (DirectSum.lof ℝ (Weight ℝ H L) (fun χ => S χ) χ ⟨x, hx⟩) = x :=
    DirectSum.coeLinearMap_lof S χ ⟨x, hx⟩
  change (DirectSum.toModule ℝ (Weight ℝ H L) L
    (fun χ => Real.exp (χ h) • (S χ).subtype))
      ((cartanWeightDecomposition T H).symm x) = _
  rw [← he, LinearEquiv.symm_apply_apply, DirectSum.toModule_lof]
  rw [he]
  rfl

/-- This also applies when the weight function is zero or its root space is
zero; it does not require choosing a nonzero root vector. -/
theorem cartanWeightScale_apply_genWeight (h : H) (χ : H → ℝ) {x : L}
    (hx : x ∈ genWeightSpace L χ) :
    cartanWeightScale T H h x = Real.exp (χ h) • x := by
  by_cases hχ : genWeightSpace L χ = ⊥
  · have hx0 : x = 0 := by simpa only [hχ, LieSubmodule.mem_bot] using hx
    simp [hx0]
  · exact cartanWeightScale_apply_root T H h ⟨χ, hχ⟩ hx

theorem cartan_root_induction {p : L → Prop}
    (hp : ∀ (χ : Weight ℝ H L) (x : L), x ∈ rootSpace H χ → p x)
    (hzero : p 0) (hadd : ∀ x y, p x → p y → p (x + y)) (x : L) : p x := by
  let := T.isTriangularizable
  have hx : x ∈ ⨆ χ : Weight ℝ H L, (genWeightSpace L χ).toSubmodule := by
    rw [LieSubmodule.iSup_toSubmodule_eq_top.mpr (iSup_genWeightSpace_eq_top' ℝ H L)]
    trivial
  exact Submodule.iSup_induction (fun χ : Weight ℝ H L =>
    (genWeightSpace L χ).toSubmodule) (motive := p) hx hp hzero hadd

/-- Addition of generalized weights makes the scalar dilation respect Lie
brackets, even when the Cartan representation is not semisimple. -/
theorem cartanWeightScale_map_lie (h : H) (x y : L) :
    cartanWeightScale T H h ⁅x, y⁆ =
      ⁅cartanWeightScale T H h x, cartanWeightScale T H h y⁆ := by
  apply cartan_root_induction T H (x := x)
  · intro χ u hu
    apply cartan_root_induction T H (x := y)
    · intro ψ v hv
      rw [cartanWeightScale_apply_genWeight T H h (χ + ψ)
        (lie_mem_genWeightSpace_of_mem_genWeightSpace hu hv),
        cartanWeightScale_apply_root T H h χ hu,
        cartanWeightScale_apply_root T H h ψ hv]
      simp only [Pi.add_apply, Real.exp_add, lie_smul, smul_lie, smul_smul, mul_comm]
    · simp
    · intro v w hv hw
      simp only [lie_add, map_add, hv, hw]
  · simp
  · intro u v hu hv
    simp only [add_lie, map_add, hu, hv]

@[simp] theorem cartanWeightScale_add_apply (h k : H) (x : L) :
    cartanWeightScale T H (h + k) x =
      cartanWeightScale T H h (cartanWeightScale T H k x) := by
  apply cartan_root_induction T H (x := x)
  · intro χ u hu
    rw [cartanWeightScale_apply_root T H (h + k) χ hu,
      cartanWeightScale_apply_root T H k χ hu, map_smul,
      cartanWeightScale_apply_root T H h χ hu]
    simp only [map_add, Real.exp_add, smul_smul, mul_comm]
  · simp
  · intro u v hu hv
    simp only [map_add, hu, hv]

@[simp] theorem cartanWeightScale_zero_apply (x : L) : cartanWeightScale T H 0 x = x := by
  apply cartan_root_induction T H (x := x)
  · intro χ u hu
    rw [cartanWeightScale_apply_root T H 0 χ hu]
    simp
  · simp
  · intro u v hu hv
    simp only [map_add, hu, hv]

/-- Exact dilation as a Lie algebra automorphism, with inverse parameter `-h`. -/
def cartanWeightDilation (h : H) : L ≃ₗ⁅ℝ⁆ L where
  toFun := cartanWeightScale T H h
  map_add' := (cartanWeightScale T H h).map_add
  map_smul' := (cartanWeightScale T H h).map_smul
  invFun := cartanWeightScale T H (-h)
  left_inv := fun x => by
    rw [← cartanWeightScale_add_apply, neg_add_cancel, cartanWeightScale_zero_apply]
  right_inv := fun x => by
    rw [← cartanWeightScale_add_apply, add_neg_cancel, cartanWeightScale_zero_apply]
  map_lie' := fun {x y} => cartanWeightScale_map_lie T H h x y

@[simp] theorem cartanWeightDilation_apply (h : H) (x : L) :
    cartanWeightDilation T H h x = cartanWeightScale T H h x := rfl

/-- Exact dilations preserve the nilpotent ideal generated by nonzero roots. -/
theorem cartanWeightDilation_mem_ideal (h : H) {x : L} (hx : x ∈ cartanRootIdeal H) :
    cartanWeightDilation T H h x ∈ cartanRootIdeal H := by
  have heq := cartanRootSubalgebra_eq_ideal H T
  have hx' : x ∈ cartanRootSubalgebra H := by
    change x ∈ (cartanRootSubalgebra H).toSubmodule
    rw [heq]
    exact hx
  suffices cartanWeightDilation T H h x ∈ cartanRootSubalgebra H by
    change cartanWeightDilation T H h x ∈ (cartanRootIdeal H).toSubmodule
    rwa [← heq]
  clear hx
  change x ∈ LieSubalgebra.lieSpan ℝ L
    {v | ∃ χ : Weight ℝ H L, χ.IsNonZero ∧ v ∈ rootSpace H χ} at hx'
  induction hx' using LieSubalgebra.lieSpan_induction with
  | mem x hx =>
    obtain ⟨χ, hχ, hx⟩ := hx
    rw [cartanWeightDilation_apply, cartanWeightScale_apply_root T H h χ hx]
    exact (cartanRootSubalgebra H).smul_mem _ (LieSubalgebra.subset_lieSpan ⟨χ, hχ, hx⟩)
  | zero => simp only [map_zero]; exact (cartanRootSubalgebra H).zero_mem
  | add x y _ _ hx hy =>
    rw [map_add]
    exact (cartanRootSubalgebra H).add_mem hx hy
  | smul a x _ hx =>
    rw [map_smul]
    exact (cartanRootSubalgebra H).smul_mem a hx
  | lie x y _ _ hx hy =>
    rw [LieEquiv.map_lie]
    exact (cartanRootSubalgebra H).lie_mem hx hy

/-- Restriction to the actual nilpotent Cartan ideal. -/
def cartanIdealWeightDilation (h : H) : cartanRootIdeal H ≃ₗ⁅ℝ⁆ cartanRootIdeal H where
  toFun x := ⟨cartanWeightDilation T H h x, cartanWeightDilation_mem_ideal T H h x.property⟩
  invFun x := ⟨cartanWeightDilation T H (-h) x,
    cartanWeightDilation_mem_ideal T H (-h) x.property⟩
  left_inv x := by
    apply Subtype.ext
    change cartanWeightScale T H (-h) (cartanWeightScale T H h x) = _
    rw [← cartanWeightScale_add_apply, neg_add_cancel, cartanWeightScale_zero_apply]
  right_inv x := by
    apply Subtype.ext
    change cartanWeightScale T H h (cartanWeightScale T H (-h) x) = _
    rw [← cartanWeightScale_add_apply, add_neg_cancel, cartanWeightScale_zero_apply]
  map_add' x y := by apply Subtype.ext; exact map_add (cartanWeightDilation T H h) (x : L) (y : L)
  map_smul' a x := by apply Subtype.ext; exact map_smul (cartanWeightDilation T H h) a (x : L)
  map_lie' {x y} := by apply Subtype.ext; exact LieEquiv.map_lie (cartanWeightDilation T H h) x y

end PolycyclicRecognition

end

end OAI
