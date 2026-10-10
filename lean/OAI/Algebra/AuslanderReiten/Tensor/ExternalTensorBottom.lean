import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorCubicDifferential

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

def bottomProjection (n : ℕ) : (complex k A B P Q).X n →ₗ[E]
    moduleObject k A B (P.X n) (Q.X 0) :=
  (DFinsupp.lapply ⟨(n,0), Nat.add_zero n⟩).comp
    (termDirectSumEquiv k A B P Q n).toLinearMap

@[simp] theorem bottomProjection_bottom (n : ℕ)
    (x : moduleObject k A B (P.X n) (Q.X 0)) :
    bottomProjection k A B P Q n (cubicInsert k A B P Q n ⟨(n,0), Nat.add_zero n⟩ x) = x := by
  simp [bottomProjection, cubicInsert]

@[simp] theorem bottomProjection_positive (n i j : ℕ) (h : i+(j+1)=n)
    (x : moduleObject k A B (P.X i) (Q.X (j+1))) :
    bottomProjection k A B P Q n (cubicInsert k A B P Q n ⟨(i,j+1),h⟩ x) = 0 := by
  have hh : (⟨(n,0), Nat.add_zero n⟩ : Diagonal n) ≠ ⟨(i,j+1),h⟩ := by
    intro he
    have := congrArg (fun t : Diagonal n => t.val.2) he
    simp only at this
    omega
  simp [bottomProjection, cubicInsert, DFinsupp.single_apply, Ne.symm hh]

variable (U : ChainComplex (ModuleCat.{u} A) ℕ) (V : ChainComplex (ModuleCat.{u} B) ℕ)

def bottomMap (s t : ℕ) (f : U.X s ⟶ P.X t) (g : V.X 0 ⟶ Q.X 0) :
    (complex k A B U V).X s →ₗ[E] (complex k A B P Q).X t :=
  (cubicInsert k A B P Q t ⟨(t,0),Nat.add_zero t⟩).comp
    ((map k A B f.hom g.hom).comp (bottomProjection k A B U V s))

@[simp] theorem bottomMap_bottom (s t : ℕ) (f : U.X s ⟶ P.X t) (g : V.X 0 ⟶ Q.X 0)
    (x : moduleObject k A B (U.X s) (V.X 0)) :
    bottomMap k A B P Q U V s t f g
      (cubicInsert k A B U V s ⟨(s,0),Nat.add_zero s⟩ x) =
      cubicInsert k A B P Q t ⟨(t,0),Nat.add_zero t⟩ (map k A B f.hom g.hom x) := by
  simp only [bottomMap, LinearMap.comp_apply, bottomProjection_bottom]

@[simp] theorem bottomMap_positive (s t i j : ℕ) (h : i+(j+1)=s)
    (f : U.X s ⟶ P.X t) (g : V.X 0 ⟶ Q.X 0)
    (x : moduleObject k A B (U.X i) (V.X (j+1))) :
    bottomMap k A B P Q U V s t f g
      (cubicInsert k A B U V s ⟨(i,j+1),h⟩ x) = 0 := by
  simp only [bottomMap, LinearMap.comp_apply, bottomProjection_positive, map_zero]

end ArExplicit.ExternalTensor

end

end OAI
