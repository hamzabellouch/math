import OAI.Algebra.Finitistic.Bimodule.BimoduleSingleDifferential
import OAI.Algebra.Finitistic.Bimodule.BimoduleDerivedFunctor

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B) (N : ModuleCat.{u} B)
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)
variable (hP : ∀ n, (∀ i, p i ≠ n) → IsZero (P.X n))

theorem evaluationAtIndex_transport (i j : Fin l) (h : i=j) :
    eqToIso (congrArg (fun n => ModuleCat.of B (TotalTerm k B P p (singleInput B N) n))
      (congrArg p h).symm) ≪≫ evaluationAtIndex k B P N p hp i ≪≫
      (moduleEvaluation k B P N).XIsoOfEq (congrArg p h) = evaluationAtIndex k B P N p hp j := by
  subst j
  simp [HomologicalComplex.XIsoOfEq]

theorem evaluationTermIso_at (i : Fin l) :
    evaluationTermIso k B P N p hp hP (p i) = evaluationAtIndex k B P N p hp i := by
  classical
  unfold evaluationTermIso
  split_ifs with h
  · have hi : h.choose=i := hp.injective h.choose_spec
    exact evaluationAtIndex_transport k B P N p hp h.choose i hi
  · exact False.elim (h ⟨i,rfl⟩)

/-- The ordinary signed total on an input module in degree zero is the exact native P tensor_B N complex. -/
def singleEvaluationIso : total k B P p hp (singleInput B N) ≅ moduleEvaluation k B P N :=
  HomologicalComplex.Hom.isoOfComponents (evaluationTermIso k B P N p hp hP) (by
    intro n m h
    classical
    by_cases hn : ∃ i, p i=n
    · obtain ⟨i,rfl⟩ := hn
      by_cases hm : ∃ j, p j=m
      · obtain ⟨j,rfl⟩ := hm
        rw [evaluationTermIso_at,evaluationTermIso_at]
        exact evaluationAtIndex_comm k B P N p hp i j h
      · exact ((BimoduleBalancedTensor.functor k B (BalancedTensor.ScalarLeftModule k B N)).map_isZero
          (hP m (by simpa only [not_exists] using hm))).eq_of_tgt _ _
    · exact (totalSingle_isZero k B P N p n (by simpa only [not_exists] using hn)).eq_of_src _ _)

variable [HasDerivedCategory.{u+1} (ModuleCat.{u} B)]
variable [∀ i, Module.Projective Bᵐᵒᵖ (ComplexTensor.rightTerm k B (right k B P) (p i))]

/-- Evaluation of the actual derived endofunctor on a degree-zero module is the native tensor complex in D(B-Mod). -/
def derivedSingleEvaluation :
    (derived k B P p hp).obj (DerivedCategory.Q.obj (singleInput B N)) ≅
      DerivedCategory.Q.obj (moduleEvaluation k B P N) :=
  (derivedComparison k B P p hp).app (singleInput B N) ≪≫
    DerivedCategory.Q.mapIso (singleEvaluationIso k B P N p hp hP)
end LittleFinitistic.BimoduleTotal

end

end OAI
