import OAI.Algebra.Finitistic.Ordinary.OrdinaryBimoduleTensorTotal
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.BimoduleComplexTensor
universe u
variable (k S A : Type u) [Field k] [Ring S] [Ring A] [Algebra k S] [Algebra k A]
variable (Q : CochainComplex (ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ)) ℤ)
variable (Z : CochainComplex (ModuleCat.{u} A) ℤ)
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

abbrev forgetTotal : CochainComplex (ModuleCat.{u} k) ℤ :=
  ((ModuleCat.restrictScalars (algebraMap k S)).mapHomologicalComplex (.up ℤ)).obj (total k S A Q Z p hp)

def forgetTermIso (n : ℤ) : (forgetTotal k S A Q Z p hp).X n ≅
    (ComplexTensor.finiteTotal k A (rightComplex k S A Q) Z p hp).X n := by
  let e : (forgetTotal k S A Q Z p hp).X n ≃ₗ[k] totalTerm k S A Q Z p n :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        have h (y : totalTerm k S A Q Z p n) : (algebraMap k S r) • y = r • y :=
          algebraMap_smul S r y
        exact h x }
  exact (e.trans (forgetTotalEquiv k S A Q Z p n)).toModuleIso

/-- The genuine outside-action total forgets to the actual previously verified k-total. -/
def forgetTotalIso : forgetTotal k S A Q Z p hp ≅
    ComplexTensor.finiteTotal k A (rightComplex k S A Q) Z p hp :=
  HomologicalComplex.Hom.isoOfComponents (forgetTermIso k S A Q Z p hp) (by
    intro n m h
    change n+1=m at h
    subst m
    have h₁ : (total k S A Q Z p hp).d n (n+1) = ModuleCat.ofHom (differential k S A Q Z p n) :=
      CochainComplex.of_d (fun n => ModuleCat.of S (totalTerm k S A Q Z p n))
        (fun n => ModuleCat.ofHom (differential k S A Q Z p n)) n
    have h₂ : (ComplexTensor.finiteTotal k A (rightComplex k S A Q) Z p hp).d n (n+1) =
        ModuleCat.ofHom ((FiniteColumnComplex.totalDifferential
          (ComplexTensor.columns k A (rightComplex k S A Q) Z p)
          (ComplexTensor.tensorHorizontal k A (rightComplex k S A Q) Z p hp)).d n) :=
      CochainComplex.of_d (fun n => ModuleCat.of k
        (FiniteColumnComplex.term (ComplexTensor.columns k A (rightComplex k S A Q) Z p) n))
        (fun n => ModuleCat.ofHom ((FiniteColumnComplex.totalDifferential
          (ComplexTensor.columns k A (rightComplex k S A Q) Z p)
          (ComplexTensor.tensorHorizontal k A (rightComplex k S A Q) Z p hp)).d n)) n
    change (forgetTermIso k S A Q Z p hp n).hom ≫ _ =
      (ModuleCat.restrictScalars (algebraMap k S)).map ((total k S A Q Z p hp).d n (n+1)) ≫
        (forgetTermIso k S A Q Z p hp (n+1)).hom
    rw [h₁,h₂]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact (forget_differential k S A Q Z p hp n z).symm)
end LittleFinitistic.BimoduleComplexTensor

end

end OAI
