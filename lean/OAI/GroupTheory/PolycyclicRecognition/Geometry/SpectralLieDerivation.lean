import OAI.GroupTheory.PolycyclicRecognition.Algebra.SpectralLogValue
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SemisimpleSpectralOperator
import Mathlib.Algebra.Lie.Derivation.Basic
import Mathlib.Algebra.Lie.OfAssociative

namespace OAI

/-! # A compatible spectral logarithm is a Lie derivation

The multiplicative relations among eigenvalues are essential: brackets of
eigenvectors have the product eigenvalue, so their logarithmic weights add.
-/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] LieRing.ofAssociativeRing

variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem semisimple_bilinear_ext (S : Module.End ℂ V) (hS : S.IsSemisimple)
    {B C : V →ₗ[ℂ] V →ₗ[ℂ] V}
    (h : ∀ μ ν x y, x ∈ S.eigenspace μ → y ∈ S.eigenspace ν → B x y = C x y) : B = C := by
  apply semisimple_eigenspace_ext S hS
  intro μ x hx
  apply semisimple_eigenspace_ext S hS
  intro ν y hy
  exact h μ ν x y hx hy

variable {L : Type} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

def spectralLieDerivation (S : L ≃ₗ⁅ℂ⁆ L) (hS : Module.End.IsSemisimple S.toLinearMap)
    (l : spectralUnitGroup S.toLinearMap →* Multiplicative ℂ) : LieDerivation ℂ L L := by
  let D := semisimpleSpectralOperator S.toLinearMap hS (spectralLogValue S.toLinearMap l)
  let B := (LieAlgebra.ad ℂ L).toLinearMap
  let F : L →ₗ[ℂ] L →ₗ[ℂ] L :=
    { toFun := fun x => D.comp (B x)
      map_add' := by intros; simp [LinearMap.comp_add]
      map_smul' := by intros; simp [LinearMap.comp_smul] }
  let G : L →ₗ[ℂ] L →ₗ[ℂ] L :=
    { toFun := fun x => B (D x) + (B x).comp D
      map_add' := by intros; simp [LinearMap.add_comp]; abel
      map_smul' := by intros; simp [smul_add, LinearMap.smul_comp] }
  have he : F = G := by
    apply semisimple_bilinear_ext S.toLinearMap hS
    intro μ ν x y hx hy
    change D ⁅x, y⁆ = ⁅D x, y⁆ + ⁅x, D y⁆
    by_cases hx0 : x = 0
    · simp [hx0]
    by_cases hy0 : y = 0
    · simp [hy0]
    have hμ : Module.End.HasEigenvalue S.toLinearMap μ :=
      Module.End.hasEigenvalue_of_hasEigenvector ⟨hx, hx0⟩
    have hν : Module.End.HasEigenvalue S.toLinearMap ν :=
      Module.End.hasEigenvalue_of_hasEigenvector ⟨hy, hy0⟩
    have hu : IsUnit S.toLinearMap := (Module.End.isUnit_iff _).mpr S.bijective
    let z := spectralEigenvalue S.toLinearMap hu μ hμ
    let w := spectralEigenvalue S.toLinearMap hu ν hν
    have hm : spectralLogValue S.toLinearMap l (μ * ν) =
        spectralLogValue S.toLinearMap l μ + spectralLogValue S.toLinearMap l ν :=
      spectralLogValue_mul S.toLinearMap l z w
    have hb : ⁅x, y⁆ ∈ Module.End.eigenspace S.toLinearMap (μ * ν) := by
      rw [Module.End.mem_eigenspace_iff]
      change S ⁅x, y⁆ = (μ * ν) • ⁅x, y⁆
      have hx' : S x = μ • x := Module.End.mem_eigenspace_iff.mp hx
      have hy' : S y = ν • y := Module.End.mem_eigenspace_iff.mp hy
      rw [S.map_lie, hx', hy', smul_lie, lie_smul, smul_smul]
    rw [show D ⁅x, y⁆ = _ from semisimpleSpectralOperator_apply _ _ _ hb,
      show D x = _ from semisimpleSpectralOperator_apply _ _ _ hx,
      show D y = _ from semisimpleSpectralOperator_apply _ _ _ hy,
      hm, smul_lie, lie_smul, add_smul]
  refine { D with leibniz' := ?_ }
  intro x y
  have h := congrArg (fun T : L →ₗ[ℂ] L →ₗ[ℂ] L => T x y) he
  change D ⁅x, y⁆ = ⁅D x, y⁆ + ⁅x, D y⁆ at h
  rw [h, sub_eq_add_neg, lie_skew (D x) y, add_comm]

end PolycyclicRecognition

end

end OAI
