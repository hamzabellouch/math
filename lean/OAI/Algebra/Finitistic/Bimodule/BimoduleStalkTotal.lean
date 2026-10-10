import OAI.Algebra.Finitistic.Bimodule.BimoduleAugmentedResolution
import OAI.Algebra.Finitistic.Bimodule.BimoduleShiftColumns

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (X : ModuleCat.{u} (Enveloping k B))
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p) (i₀ : Fin l) (hi₀ : p i₀=0)

include hp hi₀ in
/-- Every off-zero column of the stalk bimodule total is actually zero. -/
theorem stalkTerm_isZero (Z : CochainComplex (ModuleCat.{u} B) ℤ) (n : ℤ)
    (i : Fin l) (hi : i ≠ i₀) :
    IsZero (ModuleCat.of B (Term k B (bimoduleStalk k B X) Z (p i) (n + -(p i)))) := by
  have hpi : p i ≠ 0 := fun h => hi (hp.injective (h.trans hi₀.symm))
  exact (BimoduleBalancedTensor.functor k B (ComplexTensor.leftTerm k B Z (n + -(p i)))).map_isZero
    (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 X (p i) hpi)

/-- Projecting onto its sole nonzero column is a genuine B-linear chain isomorphism. -/
def stalkTotalColumnIso (Z : CochainComplex (ModuleCat.{u} B) ℤ) :
    total k B (bimoduleStalk k B X) p hp Z ≅
      (columnFunctor k B (bimoduleStalk k B X) (p i₀)).obj Z :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (piSingleEquiv (fun i => Term k B (bimoduleStalk k B X) Z (p i) (n + -(p i)))
      i₀ (fun i hi => ModuleCat.subsingleton_of_isZero
        (stalkTerm_isZero k B X p hp i₀ hi₀ Z n i hi))).toModuleIso)
    (by
      intro n m h
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (((columnFunctor k B (bimoduleStalk k B X) (p i₀)).obj Z).d n m).hom (x i₀) =
        ((total k B (bimoduleStalk k B X) p hp Z).d n m).hom x i₀
      erw [fullColumn_d,total_d_apply k B (bimoduleStalk k B X) Z p hp n m h]
      have hd (a b : ℤ) : (bimoduleStalk k B X).d a b = 0 := by
        simp [bimoduleStalk]
      have he (i : Fin l) : entryBetween k B (bimoduleStalk k B X) Z n m (p i) (p i₀) h = 0 := by
        unfold entryBetween horizontalBetween
        split_ifs
        · rw [hd,← tensorAcross_eq_termMap,tensorAcross_zero_left]
        · rfl
      simp only [he,LinearMap.zero_apply,Finset.sum_const_zero]
      exact (add_zero _).symm)

/-- The stalk-total comparison is natural in the entire input complex. -/
def stalkTotalColumnNatIso : functor k B (bimoduleStalk k B X) p hp ≅
    columnFunctor k B (bimoduleStalk k B X) (p i₀) :=
  NatIso.ofComponents (stalkTotalColumnIso k B X p hp i₀ hi₀) (by
    intro Z Z' f
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ((ComplexTensor.finiteTotalMap k B (right k B (bimoduleStalk k B X)) p hp f).f n).hom x i₀ = _
    erw [ComplexTensor.finiteTotalMap_apply]
    change ComplexTensor.inputMap k B (right k B (bimoduleStalk k B X)) f
      (p i₀) (n + -(p i₀)) (x i₀) =
        inputModuleMap k B ((bimoduleStalk k B X).X (p i₀)) (f.f (n + -(p i₀))) (x i₀)
    induction x i₀ using BalancedTensor.induction_on with
    | hz => simp
    | ht m n => rfl
    | ha x y hx hy => simpa only [map_add] using congrArg₂ HAdd.hAdd hx hy)

/-- An actual bimodule isomorphism induces a natural isomorphism of input tensor functors. -/
def inputBimoduleIso {M M' : ModuleCat.{u} (Enveloping k B)} (e : M ≅ M') :
    inputFunctor k B M ≅ inputFunctor k B M' :=
  NatIso.ofComponents (fun N =>
    (BimoduleBalancedTensor.functor k B (BalancedTensor.ScalarLeftModule k B N)).mapIso e)
    (by intro N N' f; exact input_tensor_square k B e.hom f)

/-- Finite total with the stalk bimodule is the ordinary tensor functor on all
integer complexes. The only indexing condition is that degree zero is included. -/
def stalkTotalIso : functor k B (bimoduleStalk k B X) p hp ≅
    (inputFunctor k B X).mapHomologicalComplex (.up ℤ) := by
  refine stalkTotalColumnNatIso k B X p hp i₀ hi₀ ≪≫ ?_
  rw [hi₀]
  exact Functor.isoWhiskerLeft
      ((inputFunctor k B ((bimoduleStalk k B X).X 0)).mapHomologicalComplex (.up ℤ))
      (shiftFunctorZero (CochainComplex (ModuleCat.{u} B) ℤ) ℤ) ≪≫
    Functor.rightUnitor _ ≪≫
    NatIso.mapHomologicalComplex
      (inputBimoduleIso k B (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 X 0 rfl)) (.up ℤ)
end LittleFinitistic.BimoduleTotal

end

end OAI
