import OAI.GroupTheory.PolycyclicRecognition.Algebra.MonoidRingOrbitSpan
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.LinearAlgebra.TensorProduct.Tower

namespace OAI

/-! # Finite generation of the scalar-extended integral representation -/

noncomputable section
namespace PolycyclicRecognition
variable (K : Type) [Field K]
open scoped MonoidAlgebra TensorProduct
variable {G M : Type} [Group G] [AddCommGroup M] [Module ℤ M]

def scalarExtendedRepresentation (ρ : Representation ℤ G M) : Representation K G (K ⊗[ℤ] M) :=
  (Module.End.baseChangeHom ℤ K M).toMonoidHom.comp ρ

@[simp] theorem scalarExtendedRepresentation_tmul (ρ : Representation ℤ G M)
    (g : G) (q : K) (m : M) :
    scalarExtendedRepresentation K ρ g (q ⊗ₜ[ℤ] m) = q ⊗ₜ[ℤ] ρ g m := rfl

theorem scalarExtendedRepresentation_finite (ρ : Representation ℤ G M)
    [Module.Finite ℤ[G] ρ.asModule] :
    Module.Finite K[G] (scalarExtendedRepresentation K ρ).asModule := by
  classical
  let σ := scalarExtendedRepresentation K ρ
  let v : ρ.asModule →ₗ[ℤ] σ.asModule :=
    (show ρ.asModule →+ σ.asModule from
      { toFun := fun x => σ.asModuleEquiv.symm ((1 : K) ⊗ₜ[ℤ] ρ.asModuleEquiv x)
        map_zero' := by simp
        map_add' := by intros; simp only [map_add, TensorProduct.tmul_add] }).toIntLinearMap
  obtain ⟨s, hs⟩ := exists_finite_monoidOrbitSpan (Q := G) (M := ρ.asModule)
  let T : Finset σ.asModule := s.image v
  let W : Submodule K[G] σ.asModule := Submodule.span K[G] (T : Set σ.asModule)
  let V : Submodule ℤ ρ.asModule := (W.restrictScalars ℤ).comap v
  have heq (g : G) (y : ρ.asModule) :
      v (MonoidAlgebra.of ℤ G g • y) = MonoidAlgebra.of K G g • v y := by
    apply σ.asModuleEquiv.injective
    change (1 : K) ⊗ₜ[ℤ] (ρ.asModuleEquiv (MonoidAlgebra.of ℤ G g • y)) =
      σ.asModuleEquiv (MonoidAlgebra.of K G g •
        σ.asModuleEquiv.symm ((1 : K) ⊗ₜ[ℤ] ρ.asModuleEquiv y))
    simp only [LinearEquiv.apply_symm_apply, MonoidAlgebra.of_apply,
      Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_single_one]
    rfl
  have hspan : Submodule.span ℤ (monoidOrbitSet (Q := G) (s : Set ρ.asModule)) ≤ V := by
    apply Submodule.span_le.mpr
    rintro x ⟨g, y, hy, rfl⟩
    change v (MonoidAlgebra.of ℤ G g • y) ∈ W
    rw [heq]
    exact W.smul_mem _ (Submodule.subset_span (Finset.mem_image.mpr ⟨y, hy, rfl⟩))
  have hpure (m : M) : σ.asModuleEquiv.symm ((1 : K) ⊗ₜ[ℤ] m) ∈ W := by
    have h := hspan (hs ▸ (Submodule.mem_top : ρ.asModuleEquiv.symm m ∈ ⊤))
    change σ.asModuleEquiv.symm
      ((1 : K) ⊗ₜ[ℤ] ρ.asModuleEquiv (ρ.asModuleEquiv.symm m)) ∈ W at h
    simpa only [LinearEquiv.apply_symm_apply] using h
  have hWtop : W = ⊤ := by
    apply top_unique
    suffices hh : ∀ x : K ⊗[ℤ] M, σ.asModuleEquiv.symm x ∈ W by
      intro y _
      obtain ⟨x, rfl⟩ := σ.asModuleEquiv.symm.surjective y
      exact hh x
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul q m =>
      have h := (W.restrictScalars K).smul_mem q (hpure m)
      have he : q • σ.asModuleEquiv.symm ((1 : K) ⊗ₜ[ℤ] m) =
          σ.asModuleEquiv.symm (q ⊗ₜ[ℤ] m) := by
        rw [← map_smul]
        congr 1
        simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      exact he ▸ h
    | add x y hx hy => simpa only [map_add] using W.add_mem hx hy
  exact Module.Finite.of_fg_top ⟨T, hWtop⟩

end PolycyclicRecognition

end

end OAI
