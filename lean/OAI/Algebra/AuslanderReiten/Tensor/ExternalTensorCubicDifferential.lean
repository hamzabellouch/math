import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorCubicComm
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorDifferential

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor

open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)
local notation "E" => A ⊗[k] B

@[simp] theorem inclusion_eq_cubicInsert (i j n : ℕ) (h : i+j=n) :
    (inclusion k A B P Q i j n h).hom = cubicInsert k A B P Q n ⟨(i,j),h⟩ :=
  inclusion_eq_directSum k A B P Q i j n h

theorem cubicInsert_d (i j n m : ℕ) (h : i+j=n)
    (x : moduleObject k A B (P.X i) (Q.X j)) :
    (complex k A B P Q).d n m (cubicInsert k A B P Q n ⟨(i,j),h⟩ x) =
      horizontal k A B P Q i j m x + vertical k A B P Q i j m x := by
  have hh := congrArg (fun f => f.hom x) (inclusion_d k A B P Q i j n m h)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, inclusion_eq_cubicInsert,
    ModuleCat.hom_add, LinearMap.add_apply] using hh

@[simp] theorem horizontal_succ_apply (i j n : ℕ) (h : i+j=n)
    (x : moduleObject k A B (P.X (i+1)) (Q.X j)) :
    horizontal k A B P Q (i+1) j n x =
      cubicInsert k A B P Q n ⟨(i,j),h⟩
        (map k A B (P.d (i+1) i).hom (LinearMap.id : Q.X j →ₗ[B] Q.X j) x) := by
  rw [horizontal_succ k A B P Q i j n h]
  change (inclusion k A B P Q i j n h).hom _ = _
  rw [inclusion_eq_cubicInsert]
  rfl

variable [CharP k 2]

private theorem module_neg_eq (M : ModuleCat.{u} E) (x : M) : -x=x := by
  apply neg_eq_iff_add_eq_zero.mpr
  have ht : (2 : k)=0 := CharP.cast_eq_zero k 2
  rw [← two_smul k, ht, zero_smul]

private theorem signed_hom_eq {M N : ModuleCat.{u} E} (f : M ⟶ N) (v : ℤˣ) : v • f = f := by
  rcases Int.units_eq_one_or v with rfl | rfl
  · exact one_smul _ _
  · change (-1 : ℤ) • f = f
    rw [neg_one_smul]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact module_neg_eq k A B N (f x)

@[simp] theorem vertical_succ_apply (i j n : ℕ) (h : i+j=n)
    (x : moduleObject k A B (P.X i) (Q.X (j+1))) :
    vertical k A B P Q i (j+1) n x =
      cubicInsert k A B P Q n ⟨(i,j),h⟩
        (map k A B (LinearMap.id : P.X i →ₗ[A] P.X i) (Q.d (j+1) j).hom x) := by
  rw [vertical_succ k A B P Q i j n h, signed_hom_eq k A B]
  change (inclusion k A B P Q i j n h).hom _ = _
  rw [inclusion_eq_cubicInsert]
  rfl

end ArExplicit.ExternalTensor

end

end OAI
