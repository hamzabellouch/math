import Mathlib
import OAI.Probability.SKGap.Localization.PrimaryPrediction
import OAI.Probability.SKGap.Stability.OrdinaryRecipe
import OAI.Probability.SKGap.Matrix.CorrectionTrace
import OAI.Probability.SKGap.Localization.RecipeError

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe.OrdinaryData
open Primary Matrix SKGap.Noncrossing.Primary
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]
variable (D : OrdinaryData n ι κ σ)

def startedEvaluate (D : OrdinaryData n ι κ σ) (w y : VectorFields n) (a : ℕ) : VectorFields n×VectorFields n :=
  match a with
  | 0 => (w,y)
  | a+1 => let prev:=fun b : Fin (a+1)=>startedEvaluate D w y b
      (D.sourceOf (a+1) (fun b=>(prev b).2),
       D.fieldOf (a+1) (fun b=>(prev b).1) (fun b=>(prev b).2))
termination_by a

def startedSource (w y : VectorFields n) (a : ℕ) : VectorFields n := (D.startedEvaluate w y a).1
def startedAuxiliary (w y : VectorFields n) (a : ℕ) : VectorFields n := (D.startedEvaluate w y a).2
def startedPartial (w y : VectorFields n) (a : ℕ) (l : ι) : VectorFields n :=
  D.partialOf a l (fun b=>D.startedAuxiliary w y b)

@[simp] lemma startedSource_zero (w y : VectorFields n) : D.startedSource w y 0=w := by
  rw [startedSource,startedEvaluate]
@[simp] lemma startedAuxiliary_zero (w y : VectorFields n) : D.startedAuxiliary w y 0=y := by
  rw [startedAuxiliary,startedEvaluate]
lemma startedSource_eq (w y : VectorFields n) {a : ℕ} (ha : 0<a) :
    D.startedSource w y a=D.sourceOf a (fun b=>D.startedAuxiliary w y b) := by
  obtain ⟨a,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : a≠0)
  rw [startedSource,startedEvaluate];rfl
lemma startedAuxiliary_eq (w y : VectorFields n) {a : ℕ} (ha : 0<a) :
    D.startedAuxiliary w y a=D.fieldOf a (fun b=>D.startedSource w y b) (fun b=>D.startedAuxiliary w y b) := by
  obtain ⟨a,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : a≠0)
  rw [startedAuxiliary,startedEvaluate];rfl

lemma startedSource_one (w y : VectorFields n) :
    D.startedSource w y 1=D.sourceOf 1 (fun _=>y) := by
  rw [D.startedSource_eq w y (by omega)]
  congr 1;funext index
  simp
lemma startedAuxiliary_one (w y : VectorFields n) :
    D.startedAuxiliary w y 1=D.fieldOf 1 (fun _=>w) (fun _=>y) := by
  rw [D.startedAuxiliary_eq w y (by omega)]
  congr 1 <;> funext index
  all_goals simp

lemma started_duplicate (w y : VectorFields n)
    (hw : w=D.sourceOf 1 (fun _=>y))
    (hy : y=D.fieldOf 1 (fun _=>w) (fun _=>y)) :
    D.startedSource w y 1=w ∧ D.startedAuxiliary w y 1=y := by
  exact ⟨(D.startedSource_one w y).trans hw.symm,(D.startedAuxiliary_one w y).trans hy.symm⟩

lemma started_source_derivative (w y : VectorFields n) {a : ℕ} (ha : 0<a) (x : Spin n) :
    derivativeMatrix (D.startedSource w y a) x=
      (∑l,Matrix.diagonal (D.startedPartial w y a l x)*derivativeMatrix (D.H l) x)+
      (∑b:Fin a,Matrix.diagonal (D.auxCoefficient a b x)*derivativeMatrix (D.startedAuxiliary w y b) x)+
      D.sourceAtoms a (fun b=>D.startedAuxiliary w y b) x := by
  rw [D.startedSource_eq w y ha,D.sourceOf_derivative]
  dsimp only [startedPartial]
  abel

lemma started_field_derivative (w y : VectorFields n) {a : ℕ} (ha : 0<a) (x : Spin n) :
    derivativeMatrix (D.startedAuxiliary w y a) x=
      D.J*derivativeMatrix (D.startedSource w y a) x-
      (∑l,(D.j*siteMean (D.startedPartial w y a l) x) • derivativeMatrix (D.predecessor l) x)-
      (∑b:Fin a,(D.j*siteMean (D.auxCoefficient a b) x) • derivativeMatrix (D.startedSource w y b) x)-
      D.j • ((∑l,averageError (siteMean (D.startedPartial w y a l)) (D.predecessor l) x)+
        ∑b:Fin a,averageError (siteMean (D.auxCoefficient a b)) (D.startedSource w y b) x) := by
  rw [D.startedAuxiliary_eq w y ha,D.fieldOf_derivative,D.startedSource_eq w y ha]
  rfl

end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI
