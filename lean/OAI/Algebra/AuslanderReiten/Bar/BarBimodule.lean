import OAI.Algebra.AuslanderReiten.Bar.BarComplex
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.AbsoluteBar
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]

abbrev Enveloping := R ⊗[k] Rᵐᵒᵖ

def representation (n : ℕ) : Enveloping k R →ₐ[k] Module.End k (object k R n) :=
  Algebra.TensorProduct.lift (left k R n) (right k R n) fun a b => by
    apply LinearMap.ext
    intro x
    exact left_right k R n a b x

@[instance_reducible]
def bimodule (n : ℕ) : Module (Enveloping k R) (object k R n) :=
  Module.compHom (object k R n) (representation k R n).toRingHom

def moduleObject (n : ℕ) : ModuleCat.{u} (Enveloping k R) :=
  letI := bimodule k R n
  ModuleCat.of (Enveloping k R) (object k R n)

instance baseModule (n : ℕ) : Module k (moduleObject k R n) :=
  (object k R n).isModule

instance bimoduleTower (n : ℕ) : IsScalarTower k (Enveloping k R) (moduleObject k R n) :=
  IsScalarTower.of_algebraMap_smul (A := Enveloping k R) fun a x => by
    change (representation k R n (algebraMap k (Enveloping k R) a)) x = a • x
    rw [AlgHom.commutes]
    rfl

theorem bimodule_smul_tmul (n : ℕ) (a : R) (b : Rᵐᵒᵖ) (x : moduleObject k R n) :
    (a ⊗ₜ[k] b) • x = left k R n a (right k R n b x) := rfl

def differential (n : ℕ) : moduleObject k R (n + 1) →ₗ[Enveloping k R] moduleObject k R n where
  toAddHom := (boundary k R n).toAddHom
  map_smul' a x := by
    let y : object k R (n + 1) := x
    change boundary k R n ((representation k R (n + 1) a) y) =
      (representation k R n a) (boundary k R n y)
    induction a using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
    | tmul a b =>
      change boundary k R n (left k R (n + 1) a (right k R (n + 1) b y)) =
        left k R n a (right k R n b (boundary k R n y))
      rw [boundary_left, boundary_right]

@[simp] theorem differential_apply (n : ℕ) (x : object k R (n + 1)) :
    differential k R n x = boundary k R n x := rfl

variable [CharP k 2]

def complex : ChainComplex (ModuleCat.{u} (Enveloping k R)) ℕ :=
  ChainComplex.of (fun n => moduleObject k R (n + 1))
    (fun n => ModuleCat.ofHom (X := moduleObject k R (n + 1 + 1))
      (Y := moduleObject k R (n + 1)) (differential k R (n + 1)))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact boundary_squared k R (n + 1))

theorem differential_exact (n : ℕ) :
    LinearMap.range (differential k R (n + 1)) = LinearMap.ker (differential k R n) := by
  ext x
  change (∃ y, boundary k R (n + 1) y = x) ↔ boundary k R n x = 0
  exact SetLike.ext_iff.mp (boundary_exact k R n) x

end ArExplicit.AbsoluteBar

end

end OAI
