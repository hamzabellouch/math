import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import OAI.Algebra.Finitistic.Selection.MatrixModel

namespace OAI
open scoped BigOperators

namespace LittleFinitistic
namespace CharacterModule

open MonoidAlgebra

variable {H F : Type*} [Group H] [Group F] [Fintype H]
variable (ψ : H →* F) (χ : H →* ℂˣ)

/-- The unnormalized character projector. Its identity coefficient is one,
so normalization is unnecessary for constructing the nonzero test module. -/
noncomputable def projector : MonoidAlgebra ℂ F :=
  ∑ h : H, single (ψ h) ((χ h : ℂ)⁻¹)

theorem projector_coeff_one (hψ : Function.Injective ψ) :
    (projector ψ χ).coeff 1 = 1 := by
  classical
  have hp (h : H) : ψ h = 1 ↔ h = 1 := by
    rw [← map_one ψ]
    exact hψ.eq_iff
  simp [projector, coeff_sum, coeff_single, Finsupp.single_apply, hp]

theorem projector_ne_zero (hψ : Function.Injective ψ) : projector ψ χ ≠ 0 := by
  intro h
  have := projector_coeff_one ψ χ hψ
  rw [h] at this
  simp at this

theorem projector_eigen (h : H) :
    single (ψ h) (1 : ℂ) * projector ψ χ = (χ h : ℂ) • projector ψ χ := by
  classical
  unfold projector
  rw [Finset.mul_sum, Finset.smul_sum]
  have he := Equiv.sum_comp (Equiv.mulLeft h) (fun k : H =>
    (χ h : ℂ) • single (ψ k) ((χ k : ℂ)⁻¹))
  rw [← he]
  apply Finset.sum_congr rfl
  intro k _
  change single (ψ h) (1 : ℂ) * single (ψ k) ((χ k : ℂ)⁻¹) =
    (χ h : ℂ) • single (ψ (h*k)) ((χ (h*k) : ℂ)⁻¹)
  simp only [map_mul,Units.val_mul,single_mul_single,one_mul,
    smul_single,smul_eq_mul]
  congr 1
  field_simp

variable (hc : ∀ h g, Commute (ψ h) g)

/-- All vectors on which the central subgroup acts by the selected character. -/
noncomputable def eigenspace : Submodule (MonoidAlgebra ℂ F) (MonoidAlgebra ℂ F) where
  carrier := {x | ∀ h, single (ψ h) (1 : ℂ) * x = (χ h : ℂ) • x}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb h
    simp [mul_add,ha h,hb h,smul_add]
  smul_mem' := by
    intro a x hx h
    change single (ψ h) (1 : ℂ) * (a*x) = (χ h : ℂ) • (a*x)
    rw [← mul_assoc, (MonoidAlgebra.single_commute (hc h) Commute.one_left a).eq,
      mul_assoc,hx h,mul_smul_comm]

theorem projector_mem : projector ψ χ ∈ eigenspace ψ χ hc :=
  projector_eigen ψ χ

theorem eigenspace_nontrivial (hψ : Function.Injective ψ) :
    Nontrivial (eigenspace ψ χ hc) := by
  refine ⟨⟨⟨projector ψ χ,projector_mem ψ χ hc⟩,0,?_⟩⟩
  intro h
  exact projector_ne_zero ψ χ hψ (congrArg Subtype.val h)

omit [Fintype H] in
theorem eigenspace_finiteDimensional [Finite F] :
    FiniteDimensional ℂ (eigenspace ψ χ hc) := by
  have : FiniteDimensional ℂ (MonoidAlgebra ℂ F) :=
    Module.Finite.equiv (MonoidAlgebra.coeffLinearEquiv ℂ : MonoidAlgebra ℂ F ≃ₗ[ℂ] (F →₀ ℂ)).symm
  exact FiniteDimensional.of_injective ((eigenspace ψ χ hc).restrictScalars ℂ).subtype
    Subtype.val_injective

end CharacterModule
end LittleFinitistic

end OAI
