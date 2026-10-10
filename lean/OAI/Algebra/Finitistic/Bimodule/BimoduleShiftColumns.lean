import OAI.Algebra.Finitistic.Bimodule.BimoduleInputFunctor
import OAI.Algebra.Finitistic.Bimodule.BimoduleTotalTermMaps
import OAI.Algebra.Finitistic.Bimodule.BimoduleTotalFunctor

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B) (Z : CochainComplex (ModuleCat.{u} B) ℤ)

/-- The B-valued column has exactly the frozen signed differential on underlying elements. -/
theorem fullColumn_d (p n m : ℤ) (x : Term k B P Z p (n + -p)) :
    (((columnFunctor k B P p).obj Z).d n m).hom x =
      ((ComplexTensor.column k B (right k B P) Z p).d n m).hom x := by
  induction x using BalancedTensor.induction_on with
  | hz => exact (map_zero _).trans (map_zero _).symm
  | ht a b => rfl
  | ha a b ha hb =>
    exact (map_add _ _ _).trans ((congrArg₂ (· + ·) ha hb).trans (map_add _ _ _).symm)

/-- The tensor shift has the Koszul sign (-1)^(s*p) on its pth column. -/
def shiftColumnIso (s p : ℤ) :
    (columnFunctor k B P p).obj (Z⟦s⟧) ≅ ((columnFunctor k B P p).obj Z)⟦s⟧ :=
  OrdinarySimulation.integerUnitIso _ (s*p).negOnePow ≪≫
    (shiftFunctor _ (-p)).mapIso
      (((inputFunctor k B (P.X p)).mapHomologicalComplex (.up ℤ)).commShiftIso s |>.app Z) ≪≫
    (shiftFunctorComm (CochainComplex (ModuleCat.{u} B) ℤ) s (-p)).app
      (((inputFunctor k B (P.X p)).mapHomologicalComplex (.up ℤ)).obj Z)

def shiftReindex (s a n : ℤ) :
    ((columnFunctor k B P a).obj (Z⟦s⟧)).X n ≅
      (((columnFunctor k B P a).obj Z)⟦s⟧).X n :=
  eqToIso (congrArg (fun q => ModuleCat.of B (Term k B P Z a q))
    (show n + -a + s = n + s + -a by omega))

theorem shiftColumn_hom_f (s a n : ℤ) :
    ((shiftColumnIso k B P Z s a).hom).f n =
      (s*a).negOnePow • (shiftReindex k B P Z s a n).hom := by
  simp only [shiftColumnIso, Iso.trans_hom, HomologicalComplex.comp_f]
  change ((s*a).negOnePow • 𝟙 (((columnFunctor k B P a).obj (Z⟦s⟧)).X n)) ≫ _ = _
  rw [Linear.units_smul_comp, Category.id_comp]
  congr 1
  simp only [Functor.mapIso_hom, Iso.app_hom, CochainComplex.shiftFunctor_map_f',
    Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
    CochainComplex.shiftFunctorComm_hom_app_f]
  rfl
end LittleFinitistic.BimoduleTotal

end

end OAI
