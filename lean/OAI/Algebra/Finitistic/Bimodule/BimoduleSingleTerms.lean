import OAI.Algebra.Finitistic.Bimodule.BimoduleInputFunctor
import OAI.Algebra.Finitistic.Bimodule.BimoduleTotalFunctor
import Mathlib.Algebra.Homology.Single

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B) (N : ModuleCat.{u} B)

abbrev singleInput := (HomologicalComplex.single (ModuleCat.{u} B) (.up ℤ) 0).obj N

/-- The native degree-zero-module evaluation, retaining its original B action and differential. -/
abbrev moduleEvaluation :=
  ((BimoduleBalancedTensor.functor k B (BalancedTensor.ScalarLeftModule k B N)).mapHomologicalComplex
    (.up ℤ)).obj P

def singleTermIso (n a : ℤ) (h : a=n) :
    ModuleCat.of B (Term k B P (singleInput B N) a (n + -a)) ≅ (moduleEvaluation k B P N).X n :=
  (inputFunctor k B (P.X a)).mapIso
      (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 N (n + -a) (by omega)) ≪≫
    (BimoduleBalancedTensor.functor k B (BalancedTensor.ScalarLeftModule k B N)).mapIso (P.XIsoOfEq h)

theorem singleTerm_isZero (n a : ℤ) (h : a ≠ n) :
    IsZero (ModuleCat.of B (Term k B P (singleInput B N) a (n + -a))) :=
  (inputFunctor k B (P.X a)).map_isZero
    (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 N (n + -a) (by omega))

variable {k B}
/-- A finite product with only one possibly nonzero factor is that actual factor. -/
def piSingleEquiv {l : ℕ} (V : Fin l → Type u) [∀ i, AddCommGroup (V i)] [∀ i, Module B (V i)]
    (i : Fin l) (hz : ∀ j, j ≠ i → Subsingleton (V j)) : (∀ j, V j) ≃ₗ[B] V i where
  toFun x := x i
  invFun x := Pi.single i x
  left_inv x := by
    funext j
    by_cases h : j=i
    · subst j; simp
    · let := hz j h
      exact Subsingleton.elim _ _
  right_inv x := by simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (k B) {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

def evaluationAtIndex (i : Fin l) :
    ModuleCat.of B (TotalTerm k B P p (singleInput B N) (p i)) ≅
      (moduleEvaluation k B P N).X (p i) :=
  (piSingleEquiv (fun j => Term k B P (singleInput B N) (p j) (p i + -(p j))) i
    (fun j h => ModuleCat.subsingleton_of_isZero
      (singleTerm_isZero k B P N (p i) (p j) (fun hji => h (hp.injective hji))))).toModuleIso ≪≫
    singleTermIso k B P N (p i) (p i) rfl

theorem totalSingle_isZero (n : ℤ) (hn : ∀ i, p i ≠ n) :
    IsZero (ModuleCat.of B (TotalTerm k B P p (singleInput B N) n)) := by
  let (i : Fin l) := ModuleCat.subsingleton_of_isZero (singleTerm_isZero k B P N n (p i) (hn i))
  exact ModuleCat.isZero_of_subsingleton _

/-- The finite total and the native module evaluation agree in every degree, provided every nonzero P-degree is included. -/
def evaluationTermIso
    (hP : ∀ n, (∀ i, p i ≠ n) → IsZero (P.X n)) (n : ℤ) :
    ModuleCat.of B (TotalTerm k B P p (singleInput B N) n) ≅ (moduleEvaluation k B P N).X n := by
  classical
  by_cases h : ∃ i, p i=n
  · let i := h.choose
    have hi : p i=n := h.choose_spec
    exact eqToIso (congrArg (fun n => ModuleCat.of B (TotalTerm k B P p (singleInput B N) n)) hi.symm) ≪≫
      evaluationAtIndex k B P N p hp i ≪≫ (moduleEvaluation k B P N).XIsoOfEq hi
  · have hn : ∀ i, p i ≠ n := by simpa only [not_exists] using h
    exact (totalSingle_isZero k B P N p n hn).iso
      ((BimoduleBalancedTensor.functor k B (BalancedTensor.ScalarLeftModule k B N)).map_isZero (hP n hn))
end LittleFinitistic.BimoduleTotal

end

end OAI
