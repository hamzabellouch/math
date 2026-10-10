import OAI.Algebra.Finitistic.Bimodule.BimoduleSingleTerms
import OAI.Algebra.Finitistic.Bimodule.BimoduleInputNaturality
import OAI.Algebra.Finitistic.Bimodule.BimoduleTotalDifferential

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B) (N : ModuleCat.{u} B)

/-- On the unique nonzero summands, the total differential becomes the original native tensor differential. -/
theorem single_horizontal (n m : ℤ) (h : n+1=m) :
    ModuleCat.ofHom (horizontalBetween k B P (singleInput B N) n m n m h h) ≫
      (singleTermIso k B P N m m rfl).hom =
    (singleTermIso k B P N n n rfl).hom ≫ (moduleEvaluation k B P N).d n m := by
  let φn := (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 N (n + -n) (by omega)).hom
  let φm := (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 N (m + -m) (by omega)).hom
  let e := eqToHom (congrArg (singleInput B N).X (show n + -n = m + -m by omega))
  have he : e ≫ φm = φn := by
    simp only [e,φn,φm,HomologicalComplex.singleObjXIsoOfEq,eqToIso.hom,eqToHom_trans]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using BalancedTensor.induction_on with
  | hz => simp
  | ht a b =>
    change BalancedTensor.mk k B (BimoduleBalancedTensor.Input k B (P.X m))
        (BalancedTensor.ScalarLeftModule k B N) ((P.d n m).hom a) (φm.hom (e.hom b)) =
      BalancedTensor.mk k B (BimoduleBalancedTensor.Input k B (P.X m))
        (BalancedTensor.ScalarLeftModule k B N) ((P.d n m).hom a) (φn.hom b)
    exact congrArg (fun t => BalancedTensor.mk k B (BimoduleBalancedTensor.Input k B (P.X m))
      (BalancedTensor.ScalarLeftModule k B N) ((P.d n m).hom a) t)
      (congrArg (fun f => f.hom b) he)
  | ha x y hx hy =>
    exact (map_add _ _ _).trans
      ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

theorem single_total_d (i j : Fin l) (h : p i+1=p j)
    (x : TotalTerm k B P p (singleInput B N) (p i)) :
    ((total k B P p hp (singleInput B N)).d (p i) (p j)).hom x j =
      horizontalBetween k B P (singleInput B N) (p i) (p j) (p i) (p j) h h (x i) := by
  rw [total_d_apply k B P (singleInput B N) p hp (p i) (p j) h]
  have hv : ((ComplexTensor.column k B (right k B P) (singleInput B N) (p j)).d (p i) (p j)).hom (x j) = 0 := by
    rw [ComplexTensor.column_d]
    simp only [singleInput,HomologicalComplex.single_obj_d,ComplexTensor.map_zero_right,
       smul_zero]
    rfl
  erw [hv,zero_add]
  classical
  rw [Finset.sum_eq_single i]
  · simp only [entryBetween,dite_eq_left h]
  · intro t _ ht
    let := ModuleCat.subsingleton_of_isZero
      (singleTerm_isZero k B P N (p i) (p t) (fun he => ht (hp.injective he)))
    have hx : x t=0 := Subsingleton.elim _ _
    rw [hx,map_zero]
  · simp

/-- The degreewise comparison intertwines the full native differential at every pair of included consecutive degrees. -/
theorem evaluationAtIndex_comm (i j : Fin l) (h : p i+1=p j) :
    (evaluationAtIndex k B P N p hp i).hom ≫ (moduleEvaluation k B P N).d (p i) (p j) =
      (total k B P p hp (singleInput B N)).d (p i) (p j) ≫
        (evaluationAtIndex k B P N p hp j).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((moduleEvaluation k B P N).d (p i) (p j)).hom
      ((singleTermIso k B P N (p i) (p i) rfl).hom.hom (x i)) =
    (singleTermIso k B P N (p j) (p j) rfl).hom.hom
      (((total k B P p hp (singleInput B N)).d (p i) (p j)).hom x j)
  rw [single_total_d k B P N p hp i j h]
  exact (congrArg (fun f => f.hom (x i)) (single_horizontal k B P N (p i) (p j) h)).symm
end LittleFinitistic.BimoduleTotal

end

end OAI
