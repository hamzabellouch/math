import OAI.Algebra.Finitistic.Ordinary.OrdinaryBimoduleTotalFunctor
import OAI.Algebra.Finitistic.Bimodule.BimoduleTotalUnderlying

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotalPresentation
open ExternalTensor.Section4
universe u
private theorem addHom_smul_zero {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    (f : M →+ N) (r : R) : f (r • 0) = r • f 0 := by simp

private theorem addHom_smul_add {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    (f : M →+ N) (r : R) (x y : M)
    (hx : f (r • x) = r • f x) (hy : f (r • y) = r • f y) :
    f (r • (x + y)) = r • f (x + y) := by
  simp only [smul_add, map_add, hx, hy]

variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B) (Z : CochainComplex (ModuleCat.{u} B) ℤ)

/-- The canonical balanced quotient comparison retains the outside B action. -/
def termEquiv (r q : ℤ) :
    BimoduleComplexTensor.term k B B P Z r q ≃ₗ[B] BimoduleTotal.Term k B P Z r q :=
  { (BimoduleComplexTensor.forgetEquiv k B B P Z r q).toAddEquiv with
    map_smul' := by
      intro b x
      change BimoduleComplexTensor.forgetEquiv k B B P Z r q (b • x) =
        b • (show BimoduleTotal.Term k B P Z r q from
          BimoduleComplexTensor.forgetEquiv k B B P Z r q x)
      let F : BimoduleComplexTensor.term k B B P Z r q →+ BimoduleTotal.Term k B P Z r q :=
        (BimoduleComplexTensor.forgetEquiv k B B P Z r q).toAddEquiv.toAddMonoidHom
      induction x using BalancedTensor.induction_on with
      | hz => exact addHom_smul_zero F b
      | ht m n => rfl
      | ha x y hx hy => exact addHom_smul_add F b x y hx hy }

variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

def totalTermEquiv (n : ℤ) :
    BimoduleComplexTensor.totalTerm k B B P Z p n ≃ₗ[B]
      BimoduleTotal.TotalTerm k B P p Z n :=
  LinearEquiv.piCongrRight (fun i => termEquiv k B P Z (p i) (n + -(p i)))

/-- The two signed totals coincide through their actual tensor-summand equivalences. -/
def totalIso : BimoduleComplexTensor.total k B B P Z p hp ≅
    BimoduleTotal.total k B P p hp Z :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (totalTermEquiv k B P Z p n).toModuleIso) (by
    intro n m h
    change n + 1 = m at h
    subst m
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have h := congrArg (fun f => f.hom x)
      ((BimoduleComplexTensor.forgetTotalIso k B B P Z p hp).hom.comm n (n+1))
    exact h)

variable {Z} {Z' : CochainComplex (ModuleCat.{u} B) ℤ}
theorem totalIso_natural (f : Z ⟶ Z') :
    BimoduleComplexTensor.totalMap k B B P f p hp ≫ (totalIso k B P Z' p hp).hom =
      (totalIso k B P Z p hp).hom ≫ BimoduleTotal.totalMap k B P p hp f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact BimoduleComplexTensor.forget_totalInputMap k B B P f p hp n x

/-- Natural comparison on all input complexes, with the complete outside action. -/
def totalFunctorIso : BimoduleComplexTensor.totalFunctor k B B P p hp ≅
    BimoduleTotal.functor k B P p hp :=
  NatIso.ofComponents (fun Z => totalIso k B P Z p hp)
    (fun f => totalIso_natural k B P p hp f)
end LittleFinitistic.BimoduleTotalPresentation

end

end OAI
