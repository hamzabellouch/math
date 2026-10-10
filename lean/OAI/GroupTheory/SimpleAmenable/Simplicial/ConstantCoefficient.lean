import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.CoefficientUCT
import OAI.GroupTheory.SimpleAmenable.Simplicial.CoefficientNerve

namespace OAI

open CategoryTheory Limits Simplicial Opposite HomologicalComplex AlgebraicTopology MonoidalCategory
namespace CoefficientNerve
open FreeChains

variable {C:Type} [Category.{0} C]
noncomputable def constant (M:A) : C ⥤ A := (Functor.const C).obj M
noncomputable def constIso (M:A) (n:ℕ) :
    Obj (constant (C:=C) M) n ≅ ((ModuleCat.free ℤ).obj (Simplex C n)) ⊗ M := by
  classical
  exact ((finsuppLEquivDirectSum ℤ M (Simplex C n)).symm ≪≫ₗ
    (TensorProduct.finsuppScalarLeft ℤ M (Simplex C n)).symm).toModuleIso
lemma constIso_single (M:A) {n:ℕ} (s:Simplex C n) (m:M) :
    (constIso M n).hom (single (constant M) s m) = (ModuleCat.freeMk (R:=ℤ) s) ⊗ₜ[ℤ] m := by
  classical
  change (TensorProduct.finsuppScalarLeft ℤ M (Simplex C n)).symm
    ((finsuppLEquivDirectSum ℤ M (Simplex C n)).symm (DirectSum.lof ℤ _ _ s m)) = _
  simp only [finsuppLEquivDirectSum_symm_lof,TensorProduct.finsuppScalarLeft_symm_apply_single]
  rfl
noncomputable def constantSimplicialIso (M:A) :
    simplicial (constant (C:=C) M) ≅ nerve Cᵒᵖ ⋙ ModuleCat.free ℤ ⋙ tensorRight M :=
  NatIso.ofComponents (fun p=>constIso M p.unop.len) (by
    intro p q f
    apply hom_ext; intro s
    change single (constant M) s ≫ map (constant M) f.unop ≫ _ = _
    erw [single_map_assoc]
    change (𝟙 M) ≫ single (constant M) (trunc f.unop s) ≫ _ = _
    rw [Category.id_comp]
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro m
    change (constIso M _).hom (single (constant M) (trunc f.unop s) m) =
      ((tensorRight M).map ((ModuleCat.free ℤ).map ((nerve Cᵒᵖ).map f)))
        ((constIso M _).hom (single (constant M) s m))
    rw [constIso_single,constIso_single]
    change _ = ((ModuleCat.free ℤ).map ((nerve Cᵒᵖ).map f) (ModuleCat.freeMk s)) ⊗ₜ[ℤ] m
    erw [ModuleCat.free_map_apply]
    rfl)
noncomputable def constantComplexIso (M:A) :
    complex (constant (C:=C) M) ≅ (TensorCoefficient.functor (FreeChains.complex (nerve Cᵒᵖ))).obj M :=
  (alternatingFaceMapComplex A).mapIso (constantSimplicialIso M) ≪≫
    (eqToIso (congrArg (fun T => T.obj (nerve Cᵒᵖ ⋙ ModuleCat.free ℤ))
      (map_alternatingFaceMapComplex (tensorRight M)))).symm
lemma constant_finite (M:A) [Module.Finite ℤ M] (n:ℕ)
    (h:∀i,i≤n → Module.Finite ℤ ((nerve Cᵒᵖ).homology Z i : A)) :
    Module.Finite ℤ ((complex (constant (C:=C) M)).homology n) := by
  let K:=FreeChains.complex (nerve Cᵒᵖ)
  have hf (i:ℕ) (hi:i≤n) : Module.Finite ℤ (K.homology i) := by
    exact (Module.Finite.equiv_iff ((homologyFunctor A c i).mapIso (FreeChains.complexIso _)).toLinearEquiv).mp (h i hi)
  have : ∀i,Module.Flat ℤ (K.X i) := by
    intro index
    change Module.Flat ℤ (Simplex C index →₀ ℤ)
    infer_instance
  have hh : Module.Finite ℤ ((TensorCoefficient.homologyFunctor K n).obj M) := by
    cases n with
    | zero => have:=hf 0 le_rfl; exact TensorCoefficient.finite_coefficient_zero K M
    | succ n => have:=hf n (by omega); have:=hf (n+1) le_rfl
                exact TensorCoefficient.finite_coefficient_succ K M n
  exact (Module.Finite.equiv_iff ((homologyFunctor A c n).mapIso (constantComplexIso (C:=C) M)).symm.toLinearEquiv).mp hh
end CoefficientNerve

end OAI
