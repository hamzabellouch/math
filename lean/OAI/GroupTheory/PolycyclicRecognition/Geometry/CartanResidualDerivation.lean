import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanWeightDilation
import Mathlib.Algebra.Lie.Derivation.Basic

namespace OAI

/-! # The actual nilpotent residual derivation

Subtracting the scalar weight derivation from the Cartan adjoint action gives
one globally nilpotent derivation, not merely separate nilpotent operators on
its root spaces. Its finite exponential is therefore an actual Lie automorphism.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule
open scoped DirectSum

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

/-- The scalar part of the Cartan adjoint operator on the generalized-root
sum, before exponentiation. -/
def cartanScalarOperator (h : H) : L →ₗ[ℝ] L := by
  classical
  exact (DirectSum.toModule ℝ (Weight ℝ H L) L
    (fun χ => χ h • (genWeightSpace L χ).toSubmodule.subtype)).comp
      (cartanWeightDecomposition T H).symm.toLinearMap

theorem cartanScalarOperator_apply_root (h : H) (χ : Weight ℝ H L) {x : L}
    (hx : x ∈ rootSpace H χ) : cartanScalarOperator T H h x = χ h • x := by
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

theorem cartanScalarOperator_apply_genWeight (h : H) (χ : H → ℝ) {x : L}
    (hx : x ∈ genWeightSpace L χ) : cartanScalarOperator T H h x = χ h • x := by
  by_cases hχ : genWeightSpace L χ = ⊥
  · have hx0 : x = 0 := by simpa only [hχ, LieSubmodule.mem_bot] using hx
    simp [hx0]
  · exact cartanScalarOperator_apply_root T H h ⟨χ, hχ⟩ hx

/-- Weight addition in brackets is precisely the derivation identity for
the scalar part. -/
theorem cartanScalarOperator_leibniz (h : H) (x y : L) :
    cartanScalarOperator T H h ⁅x, y⁆ =
      ⁅x, cartanScalarOperator T H h y⁆ + ⁅cartanScalarOperator T H h x, y⁆ := by
  apply cartan_root_induction T H (x := x)
  · intro χ u hu
    apply cartan_root_induction T H (x := y)
    · intro ψ v hv
      rw [cartanScalarOperator_apply_genWeight T H h (χ + ψ)
        (lie_mem_genWeightSpace_of_mem_genWeightSpace hu hv),
        cartanScalarOperator_apply_root T H h χ hu,
        cartanScalarOperator_apply_root T H h ψ hv]
      simp only [Pi.add_apply, add_smul, lie_smul, smul_lie, add_comm]
    · simp
    · intro v w hv hw
      simp only [lie_add, map_add, hv, hw]
      abel
  · simp
  · intro u v hu hv
    simp only [add_lie, map_add, hu, hv]
    abel

/-- The scalar part as a genuine derivation of the ambient Lie algebra. -/
def cartanScalarDerivation (h : H) : LieDerivation ℝ L L where
  __ := cartanScalarOperator T H h
  leibniz' x y := by
    rw [cartanScalarOperator_leibniz, sub_eq_add_neg,
      ← lie_skew (cartanScalarOperator T H h x) y]

/-- The globally defined residual action. The library's `inner h` sends
`x` to `[x,h]`, hence the minus sign. -/
def cartanResidualDerivation (h : H) : LieDerivation ℝ L L :=
  -LieDerivation.inner ℝ L L (h : L) - cartanScalarDerivation T H h

theorem cartanResidualDerivation_apply_root (h : H) (χ : Weight ℝ H L) {x : L}
    (hx : x ∈ rootSpace H χ) :
    cartanResidualDerivation T H h x = ⁅(h : L), x⁆ - χ h • x := by
  change -⁅x, (h : L)⁆ - cartanScalarOperator T H h x = _
  rw [cartanScalarOperator_apply_root T H h χ hx, ← lie_skew, neg_neg]

theorem cartanResidualDerivation_root_mem (h : H) (χ : Weight ℝ H L) {x : L}
    (hx : x ∈ rootSpace H χ) : cartanResidualDerivation T H h x ∈ rootSpace H χ := by
  rw [cartanResidualDerivation_apply_root T H h χ hx]
  exact (rootSpace H χ).sub_mem ((rootSpace H χ).lie_mem hx) ((rootSpace H χ).smul_mem _ hx)

theorem cartanResidualDerivation_pow_root (h : H) (χ : Weight ℝ H L) (k : ℕ) {x : L}
    (hx : x ∈ rootSpace H χ) :
    ((cartanResidualDerivation T H h).toLinearMap ^ k) x =
      ((ad ℝ L h - χ h • 1) ^ k) x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply]
    change ((cartanResidualDerivation T H h).toLinearMap ^ k)
      (cartanResidualDerivation T H h x) = _
    rw [ih (cartanResidualDerivation_root_mem T H h χ hx),
      cartanResidualDerivation_apply_root T H h χ hx,
      pow_succ, Module.End.mul_apply]
    rfl

/-- The ambient dimension is a simultaneous nilpotence bound on every root. -/
theorem cartanResidualDerivation_pow_eq_zero (h : H) :
    (cartanResidualDerivation T H h).toLinearMap ^ finrank ℝ L = 0 := by
  apply LinearMap.ext
  intro x
  change ((cartanResidualDerivation T H h).toLinearMap ^ finrank ℝ L) x = 0
  apply cartan_root_induction T H (x := x)
  · intro χ v hv
    rw [cartanResidualDerivation_pow_root T H h χ (finrank ℝ L) hv]
    have he := genWeightSpace_le_genWeightSpaceOf L h (χ : H → ℝ) hv
    change v ∈ (ad ℝ L h).maxGenEigenspace (χ h) at he
    rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank,
      Module.End.genEigenspace_nat] at he
    exact he
  · simp
  · intro u v hu hv
    rw [map_add, hu, hv, add_zero]

/-- The residual action exponentiates by a finite polynomial to an actual
Lie automorphism. -/
def cartanResidualAutomorphism (h : H) : L ≃ₗ⁅ℝ⁆ L := by
  letI : Module ℚ L := Module.compHom L (algebraMap ℚ ℝ)
  exact (cartanResidualDerivation T H h).exp
    ⟨finrank ℝ L, cartanResidualDerivation_pow_eq_zero T H h⟩

/-- The scalar derivation preserves the actual nilpotent Cartan ideal. -/
theorem cartanScalarOperator_mem_ideal (h : H) {x : L} (hx : x ∈ cartanRootIdeal H) :
    cartanScalarOperator T H h x ∈ cartanRootIdeal H := by
  have heq := cartanRootSubalgebra_eq_ideal H T
  have hx' : x ∈ cartanRootSubalgebra H := by
    change x ∈ (cartanRootSubalgebra H).toSubmodule
    rwa [heq]
  suffices cartanScalarOperator T H h x ∈ cartanRootSubalgebra H by
    change cartanScalarOperator T H h x ∈ (cartanRootIdeal H).toSubmodule
    rwa [← heq]
  clear hx
  change x ∈ LieSubalgebra.lieSpan ℝ L
    {v | ∃ χ : Weight ℝ H L, χ.IsNonZero ∧ v ∈ rootSpace H χ} at hx'
  induction hx' using LieSubalgebra.lieSpan_induction with
  | mem x hx =>
    obtain ⟨χ, hχ, hx⟩ := hx
    rw [cartanScalarOperator_apply_root T H h χ hx]
    exact (cartanRootSubalgebra H).smul_mem _ (LieSubalgebra.subset_lieSpan ⟨χ, hχ, hx⟩)
  | zero => simp only [map_zero]; exact (cartanRootSubalgebra H).zero_mem
  | add x y _ _ hx hy =>
    rw [map_add]
    exact (cartanRootSubalgebra H).add_mem hx hy
  | smul a x _ hx =>
    rw [map_smul]
    exact (cartanRootSubalgebra H).smul_mem a hx
  | lie x y hx hy ihx ihy =>
    rw [cartanScalarOperator_leibniz]
    exact (cartanRootSubalgebra H).add_mem
      ((cartanRootSubalgebra H).lie_mem hx ihy) ((cartanRootSubalgebra H).lie_mem ihx hy)

/-- Consequently the full residual derivation preserves the ideal. -/
theorem cartanResidualDerivation_mem_ideal (h : H) {x : L} (hx : x ∈ cartanRootIdeal H) :
    cartanResidualDerivation T H h x ∈ cartanRootIdeal H := by
  change -⁅x, (h : L)⁆ - cartanScalarOperator T H h x ∈ cartanRootIdeal H
  rw [lie_skew (h : L) x]
  exact (cartanRootIdeal H).sub_mem ((cartanRootIdeal H).lie_mem hx)
    (cartanScalarOperator_mem_ideal T H h hx)

/-- Restrict the residual derivation before taking its finite exponential. -/
def cartanIdealResidualDerivation (h : H) :
    LieDerivation ℝ (cartanRootIdeal H) (cartanRootIdeal H) where
  toFun x := ⟨cartanResidualDerivation T H h x,
    cartanResidualDerivation_mem_ideal T H h x.property⟩
  map_add' x y := by apply Subtype.ext; exact map_add (cartanResidualDerivation T H h) (x : L) (y : L)
  map_smul' a x := by apply Subtype.ext; exact map_smul (cartanResidualDerivation T H h) a (x : L)
  leibniz' x y := by
    apply Subtype.ext
    exact (cartanResidualDerivation T H h).leibniz' (x : L) (y : L)

theorem cartanIdealResidualDerivation_pow_coe (h : H) (k : ℕ) (x : cartanRootIdeal H) :
    (((cartanIdealResidualDerivation T H h).toLinearMap ^ k) x : L) =
      ((cartanResidualDerivation T H h).toLinearMap ^ k) (x : L) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
    rfl

theorem cartanIdealResidualDerivation_pow_eq_zero (h : H) :
    (cartanIdealResidualDerivation T H h).toLinearMap ^ finrank ℝ L = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (((cartanIdealResidualDerivation T H h).toLinearMap ^ finrank ℝ L) x : L) = 0
  rw [cartanIdealResidualDerivation_pow_coe, cartanResidualDerivation_pow_eq_zero]
  rfl

/-- The residual automorphism of the nilpotent factor used in box estimates. -/
def cartanIdealResidualAutomorphism (h : H) : cartanRootIdeal H ≃ₗ⁅ℝ⁆ cartanRootIdeal H := by
  letI : Module ℚ (cartanRootIdeal H) := Module.compHom _ (algebraMap ℚ ℝ)
  exact (cartanIdealResidualDerivation T H h).exp
    ⟨finrank ℝ L, cartanIdealResidualDerivation_pow_eq_zero T H h⟩

end PolycyclicRecognition

end

end OAI
