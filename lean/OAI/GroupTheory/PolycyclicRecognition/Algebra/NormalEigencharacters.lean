import OAI.GroupTheory.PolycyclicRecognition.Algebra.CommonEigenvectors
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index

namespace OAI

/-! # Finite-index stabilizers of normal-subgroup eigenspaces

Conjugation permutes the common eigenvalue functions of a normal subgroup.
There are only finitely many nonzero common eigenspaces. Consequently every
one of them is invariant under a subgroup of finite index in the ambient
group. This separates the finite permutation from the linear action.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative

variable {G K V : Type*} [Group G] [Field K] [AddCommGroup V] [Module K V]
  (A : Subgroup G) [A.Normal]

def conjugateWeightPerm : G →* Equiv.Perm (A → K) where
  toFun g :=
    { toFun := fun χ a => χ (MulAut.conjNormal (H := A) g⁻¹ a)
      invFun := fun χ a => χ (MulAut.conjNormal (H := A) g a)
      left_inv := by
        intro χ
        funext a
        apply congrArg χ
        apply Subtype.ext
        simp only [MulAut.conjNormal_apply, inv_inv]
        group
      right_inv := by
        intro χ
        funext a
        apply congrArg χ
        apply Subtype.ext
        simp only [MulAut.conjNormal_apply, inv_inv]
        group }
  map_one' := by
    ext χ a
    simp only [inv_one, map_one]
    rfl
  map_mul' g h := by
    ext χ a
    change χ (MulAut.conjNormal (H := A) (g * h)⁻¹ a) =
      χ (MulAut.conjNormal (H := A) h⁻¹ (MulAut.conjNormal (H := A) g⁻¹ a))
    rw [mul_inv_rev, map_mul]
    rfl

def normalCommonEigenspace (ρ : G →* (V ≃ₗ[K] V)) (χ : A → K) : Submodule K V :=
  commonEigenspace (fun a : A => (ρ a).toLinearMap) χ

omit [A.Normal] in
theorem mem_normalCommonEigenspace (ρ : G →* (V ≃ₗ[K] V)) (χ : A → K) (v : V) :
    v ∈ normalCommonEigenspace A ρ χ ↔ ∀ a : A, ρ a v = χ a • v :=
  mem_commonEigenspace _ _ _

theorem normalCommonEigenspace_conjugate (ρ : G →* (V ≃ₗ[K] V))
    (χ : A → K) (g : G) {v : V} (hv : v ∈ normalCommonEigenspace A ρ χ) :
    ρ g v ∈ normalCommonEigenspace A ρ (conjugateWeightPerm A g χ) := by
  rw [mem_normalCommonEigenspace] at hv ⊢
  intro a
  have he : ρ (a : G) * ρ g = ρ g * ρ (MulAut.conjNormal (H := A) g⁻¹ a : A) := by
    rw [← map_mul, ← map_mul]
    congr 1
    simp only [MulAut.conjNormal_apply, inv_inv]
    group
  calc
    ρ a (ρ g v) = ρ g (ρ (MulAut.conjNormal (H := A) g⁻¹ a : A) v) :=
      congrArg (fun e : V ≃ₗ[K] V => e v) he
    _ = χ (MulAut.conjNormal (H := A) g⁻¹ a) • ρ g v := by rw [hv, map_smul]
    _ = _ := rfl

theorem normalCommonEigenspace_conjugate_ne_bot (ρ : G →* (V ≃ₗ[K] V))
    (χ : A → K) (g : G) (hχ : normalCommonEigenspace A ρ χ ≠ ⊥) :
    normalCommonEigenspace A ρ (conjugateWeightPerm A g χ) ≠ ⊥ := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  intro he
  have hh := normalCommonEigenspace_conjugate A ρ χ g hv
  rw [he, Submodule.mem_bot] at hh
  exact hv0 ((ρ g).injective (hh.trans (map_zero _).symm))

theorem exists_finiteIndex_preserving_commonEigenspace [Module.Finite K V]
    (ρ : G →* (V ≃ₗ[K] V)) (χ : A → K)
    (hχ : normalCommonEigenspace A ρ χ ≠ ⊥) :
    ∃ H : Subgroup G, H.FiniteIndex ∧
      ∀ g ∈ H, ∀ v ∈ normalCommonEigenspace A ρ χ,
        ρ g v ∈ normalCommonEigenspace A ρ χ := by
  let : MulAction G (A → K) := MulAction.compHom (A → K) (conjugateWeightPerm (K := K) A)
  have hfinite : (MulAction.orbit G χ).Finite := by
    apply (finite_commonEigenspaces (fun a : A => (ρ a).toLinearMap)).subset
    rintro _ ⟨g, rfl⟩
    exact normalCommonEigenspace_conjugate_ne_bot A ρ χ g hχ
  let H := MulAction.stabilizer G χ
  let : Finite (MulAction.orbit G χ) := hfinite
  have hH : H.FiniteIndex := by
    let : Finite (G ⧸ H) := Finite.of_equiv (MulAction.orbit G χ)
      (MulAction.orbitEquivQuotientStabilizer G χ)
    exact Subgroup.finiteIndex_of_finite_quotient
  refine ⟨H, hH, ?_⟩
  intro g hg v hv
  have he : conjugateWeightPerm A g χ = χ := hg
  simpa only [he] using normalCommonEigenspace_conjugate A ρ χ g hv

theorem exists_finiteIndex_nonzero_commonEigenspace [Module.Finite K V]
    [Nontrivial V] [IsAlgClosed K] [IsMulCommutative A]
    (ρ : G →* (V ≃ₗ[K] V)) :
    ∃ (χ : A → K) (H : Subgroup G), H.FiniteIndex ∧
      normalCommonEigenspace A ρ χ ≠ ⊥ ∧
      ∀ g ∈ H, ∀ v ∈ normalCommonEigenspace A ρ χ,
        ρ g v ∈ normalCommonEigenspace A ρ χ := by
  have hcomm (a b : A) : Commute (ρ a).toLinearMap (ρ b).toLinearMap := by
    exact (Commute.all a b).map
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (ρ.comp A.subtype))
  obtain ⟨χ, hχ⟩ := exists_commonEigenspace
    (fun a : A => (ρ a).toLinearMap) hcomm
  obtain ⟨H, hH, hpres⟩ := exists_finiteIndex_preserving_commonEigenspace A ρ χ hχ
  exact ⟨χ, H, hH, hχ, hpres⟩

end PolycyclicRecognition

end

end OAI
