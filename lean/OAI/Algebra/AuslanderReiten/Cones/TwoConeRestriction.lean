import OAI.Algebra.AuslanderReiten.Cones.TwoConeProjective
import OAI.Algebra.AuslanderReiten.Homology.RestrictKernelCokernel

namespace OAI

noncomputable section
open CategoryTheory

namespace ArExplicit.TwoCone

universe u
variable {R S : Type u} [Ring R] [Ring S] (j : S →+* R) (D : Data R)

def Data.restrict : Data S where
  term n := (ModuleCat.restrictScalars j).obj (D.term n)
  d n := ((ModuleCat.restrictScalars j).map (ModuleCat.ofHom (D.d n))).hom
  first n := ((ModuleCat.restrictScalars j).map (ModuleCat.ofHom (D.first n))).hom
  second n := ((ModuleCat.restrictScalars j).map (ModuleCat.ofHom (D.second n))).hom
  square n := by ext x; exact DFunLike.congr_fun (D.square n) x
  first_comm n := by ext x; exact DFunLike.congr_fun (D.first_comm n) x
  second_comm n := by ext x; exact DFunLike.congr_fun (D.second_comm n) x
  comparisons_comm n := by ext x; exact DFunLike.congr_fun (D.comparisons_comm n) x

def termRestrictionEquiv (n : ℕ) :
    (ModuleCat.restrictScalars j).obj (term D n) ≃ₗ[S] term (D.restrict j) n where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def cokernelRestrictionEquiv (n : ℕ) :
    (ModuleCat.restrictScalars j).obj (ModuleCat.of R (Cokernel D n)) ≃ₗ[S]
      Cokernel (D.restrict j) n where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem restricted_exact (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n)) (n : ℕ) :
    Function.Exact ((D.restrict j).d (n+1)) ((D.restrict j).d n) := hex n

theorem C₁_side_projective
    (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n))
    (hp : ∀ n, Module.Projective S ((D.restrict j).term n))
    [Module.Projective S (BaseCokernel (D.restrict j) 0)] :
    Module.Projective S ((ModuleCat.restrictScalars j).obj (ModuleCat.of R (C₁ D))) := by
  let := C₁_projective (D.restrict j) (restricted_exact j D hex) hp
  exact Module.Projective.of_equiv (cokernelRestrictionEquiv j D 1).symm

end ArExplicit.TwoCone

end

end OAI
