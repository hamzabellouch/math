import OAI.GroupTheory.PolycyclicRecognition.Finiteness.HomologyRankOneLimit
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.Submodule.Equiv

namespace OAI

/-! # Rationalizing a torsion-free commensurable homology group -/

noncomputable section
namespace PolycyclicRecognition

open scoped TensorProduct
variable {M : Type} [AddCommGroup M] [Module ℤ M]

theorem rational_rankOne_span
    (hcomm : ∀ x y : M, x ≠ 0 → y ≠ 0 →
      ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • x = b • y)
    (x : M) (hx : x ≠ 0) :
    Submodule.span ℚ ({1 ⊗ₜ[ℤ] x} : Set (ℚ ⊗[ℤ] M)) = ⊤ := by
  have hy (y : M) : (1 : ℚ) ⊗ₜ[ℤ] y ∈
      Submodule.span ℚ ({1 ⊗ₜ[ℤ] x} : Set (ℚ ⊗[ℤ] M)) := by
    by_cases hzero : y = 0
    · simp [hzero]
    obtain ⟨a, b, ha, _, hab⟩ := hcomm y x hzero hx
    have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast ha
    have ht : (a : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] y) =
        (b : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] x) := by
      calc
        (a : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] y) = (a • (1 : ℚ)) ⊗ₜ[ℤ] y := by
          simp only [TensorProduct.smul_tmul', smul_eq_mul, zsmul_eq_mul, mul_one]
        _ = (1 : ℚ) ⊗ₜ[ℤ] (a • y) := by
          have h₁ := LinearMap.congr_fun ((TensorProduct.mk ℤ ℚ M).map_smul a 1) y
          have h₂ := ((TensorProduct.mk ℤ ℚ M) 1).map_smul a y
          exact (h₁.trans h₂.symm).trans (congrArg (fun z : M => (1 : ℚ) ⊗ₜ[ℤ] z)
            (int_smul_eq_zsmul (inferInstance : Module ℤ M) a y))
        _ = (1 : ℚ) ⊗ₜ[ℤ] (b • x) := congrArg (fun z : M => (1 : ℚ) ⊗ₜ[ℤ] z) hab
        _ = (b • (1 : ℚ)) ⊗ₜ[ℤ] x := by
          have h₁ := LinearMap.congr_fun ((TensorProduct.mk ℤ ℚ M).map_smul b 1) x
          have h₂ := ((TensorProduct.mk ℤ ℚ M) 1).map_smul b x
          exact (congrArg (fun z : M => (1 : ℚ) ⊗ₜ[ℤ] z)
            (int_smul_eq_zsmul (inferInstance : Module ℤ M) b x)).symm.trans (h₂.trans h₁.symm)
        _ = (b : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] x) := by
          simp only [TensorProduct.smul_tmul', smul_eq_mul, zsmul_eq_mul, mul_one]
    have he : (1 : ℚ) ⊗ₜ[ℤ] y =
        (a : ℚ)⁻¹ • ((b : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] x)) := by
      rw [← ht, inv_smul_smul₀ haQ]
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  apply top_unique
  intro z hz
  clear hz
  induction z using TensorProduct.inductionOn with
  | tmul r y =>
    have h := Submodule.smul_mem (Submodule.span ℚ ({1 ⊗ₜ[ℤ] x} : Set (ℚ ⊗[ℤ] M))) r (hy y)
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using h
  | add z w hz hw => exact Submodule.add_mem _ hz hw

theorem rational_rankOne_equiv
    (htor : ∀ (a : ℤ) (x : M), a • x = 0 → a = 0 ∨ x = 0)
    (hcomm : ∀ x y : M, x ≠ 0 → y ≠ 0 →
      ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • x = b • y)
    (x : M) (hx : x ≠ 0) : Nonempty ((ℚ ⊗[ℤ] M) ≃ₗ[ℚ] ℚ) := by
  let : Module.IsTorsionFree ℤ M := Module.isTorsionFree_iff_smul_eq_zero.mpr (by
    intro a x hx
    apply htor a x
    change (inferInstance : Module ℤ M).smul a x = 0 at hx
    rwa [int_smul_eq_zsmul] at hx)
  have hi := Module.Flat.tensorProduct_mk_injective ℤ M ℚ
  have hxQ : (1 : ℚ) ⊗ₜ[ℤ] x ≠ 0 := by
    intro h
    exact hx (hi (h.trans (TensorProduct.tmul_zero M 1).symm))
  have hspan := rational_rankOne_span hcomm x hx
  let e := LinearEquiv.toSpanNonzeroSingleton ℚ (ℚ ⊗[ℤ] M) (1 ⊗ₜ[ℤ] x) hxQ
  exact ⟨(e.trans ((LinearEquiv.ofEq _ _ hspan).trans Submodule.topEquiv)).symm⟩

end PolycyclicRecognition

end

end OAI
