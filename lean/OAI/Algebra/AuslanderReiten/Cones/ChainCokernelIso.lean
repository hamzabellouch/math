import OAI.Algebra.AuslanderReiten.Homology.LinearCokernelMap
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Basic

namespace OAI

noncomputable section
namespace ArExplicit.ChainCokernel
open CategoryTheory
universe u
variable {R : Type u} [Ring R]
variable {P Q : ChainComplex (ModuleCat.{u} R) ℕ}

abbrev cokernel (P : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :=
  P.X n ⧸ LinearMap.range (P.d (n+1) n).hom

def iso (e : P ≅ Q) (n : ℕ) : cokernel P n ≃ₗ[R] cokernel Q n :=
  LinearCokernel.equiv (P.d (n+1) n).hom (Q.d (n+1) n).hom
    (HomologicalComplex.Hom.isoApp e (n+1)).toLinearEquiv
    (HomologicalComplex.Hom.isoApp e n).toLinearEquiv
    (congrArg ModuleCat.Hom.hom (e.hom.comm (n+1) n).symm)

@[simp] theorem iso_mk (e : P ≅ Q) (n : ℕ) (z : P.X n) :
    iso e n (Submodule.Quotient.mk z) = Submodule.Quotient.mk (e.hom.f n z) := rfl

def cubic (p : ∀ n, P.X (n+3) ⟶ P.X n)
    (hp : ∀ n, p (n+1) ≫ P.d (n+1) n = P.d (n+4) (n+3) ≫ p n) (n : ℕ) :
    cokernel P (n+3) →ₗ[R] cokernel P n :=
  LinearCokernel.map (P.d (n+4) (n+3)).hom (P.d (n+1) n).hom
    (p (n+1)).hom (p n).hom (congrArg ModuleCat.Hom.hom (hp n).symm)

@[simp] theorem cubic_mk (p : ∀ n, P.X (n+3) ⟶ P.X n)
    (hp : ∀ n, p (n+1) ≫ P.d (n+1) n = P.d (n+4) (n+3) ≫ p n)
    (n : ℕ) (z : P.X (n+3)) :
    cubic p hp n (Submodule.Quotient.mk z) = Submodule.Quotient.mk (p n z) := rfl

theorem iso_cubic (e : P ≅ Q)
    (p : ∀ n, P.X (n+3) ⟶ P.X n) (q : ∀ n, Q.X (n+3) ⟶ Q.X n)
    (hp : ∀ n, p (n+1) ≫ P.d (n+1) n = P.d (n+4) (n+3) ≫ p n)
    (hq : ∀ n, q (n+1) ≫ Q.d (n+1) n = Q.d (n+4) (n+3) ≫ q n)
    (h : ∀ n, p n ≫ e.hom.f n = e.hom.f (n+3) ≫ q n)
    (n : ℕ) (z : cokernel P (n+3)) :
    iso e n (cubic p hp n z) = cubic q hq n (iso e (n+3) z) := by
  obtain ⟨z,rfl⟩ := (LinearMap.range (P.d (n+4) (n+3)).hom).mkQ_surjective z
  change Submodule.Quotient.mk (e.hom.f n (p n z)) =
    Submodule.Quotient.mk (q n (e.hom.f (n+3) z))
  exact congrArg Submodule.Quotient.mk (DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (h n)) z)

end ArExplicit.ChainCokernel

end

end OAI
