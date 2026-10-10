import Mathlib
import OAI.Probability.SKGap.Stability.OrdinaryRecipe
import OAI.Probability.SKGap.Localization.StartedRecipe
import OAI.Probability.SKGap.Matrix.CorrectionTrace
import OAI.Probability.SKGap.Matrix.ClosedTreeMatrix

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe.OrdinaryData
open Primary Matrix SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.Tensor.Series
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

def startedTree (D : OrdinaryData n ι κ σ) (w y : VectorFields n)
    (T : ι→SourceTree (Fin n→ℝ)) (t₀ : ClosedTree (Fin n→ℝ)) (x : Spin n)
    (a : ℕ) : ClosedTree (Fin n→ℝ) :=
  match a with
  | 0 => t₀
  | a+1 => ClosedTree.branches
      ((Finset.univ.toList.map (fun l=>(D.startedPartial w y (a+1) l x,ClosedTree.ofOrdinary (T l))))++
       (Finset.univ.toList.map (fun b : Fin (a+1)=>(D.auxCoefficient (a+1) b x,startedTree D w y T t₀ x b))))
termination_by a

lemma startedTree_pos (D : OrdinaryData n ι κ σ) (w y : VectorFields n)
    (T : ι→SourceTree (Fin n→ℝ)) (t₀ : ClosedTree (Fin n→ℝ)) (x : Spin n)
    {a : ℕ} (ha : 0<a) : D.startedTree w y T t₀ x a=ClosedTree.branches
      ((Finset.univ.toList.map (fun l=>(D.startedPartial w y a l x,ClosedTree.ofOrdinary (T l))))++
       (Finset.univ.toList.map (fun b : Fin a=>(D.auxCoefficient a b x,D.startedTree w y T t₀ x b)))) := by
  obtain ⟨a,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : a≠0)
  rw [startedTree]

lemma startedTree_leafMass (D : OrdinaryData n ι κ σ) (w y : VectorFields n)
    (T : ι→SourceTree (Fin n→ℝ)) (t₀ : ClosedTree (Fin n→ℝ)) (ht : t₀.leafMass=0)
    (x : Spin n) (a : ℕ) : (D.startedTree w y T t₀ x a).leafMass=0 := by
  cases a with
  | zero => simpa only [startedTree] using ht
  | succ a => rw [startedTree,ClosedTree.branches_leafMass]

variable (D : OrdinaryData n ι κ σ) (w y : VectorFields n)
    (T : ι→SourceTree (Fin n→ℝ)) (t₀ : ClosedTree (Fin n→ℝ)) (a₀ : Fin n→ℝ) (x : Spin n)
def startedRetainedSource (a : ℕ) := (D.startedTree w y T t₀ x a).sourceMatrix D.j a₀ D.J
def startedRetainedField (a : ℕ) := (D.startedTree w y T t₀ x a).fieldMatrix D.j a₀ D.J

lemma startedRetainedSource_eq {a : ℕ} (ha : 0<a) :
    D.startedRetainedSource w y T t₀ a₀ x a=
      (∑l,Matrix.diagonal (D.startedPartial w y a l x)*SourceTree.fieldMatrix D.j D.J (T l))+
      ∑b:Fin a,Matrix.diagonal (D.auxCoefficient a b x)*D.startedRetainedField w y T t₀ a₀ x b := by
  rw [startedRetainedSource,D.startedTree_pos w y T t₀ x ha,ClosedTree.branches_source]
  simp [List.map_append,List.sum_append,List.map_map,Function.comp_def,startedRetainedField,
    ClosedTree.fieldMatrix_ofOrdinary]

lemma startedRetainedField_eq {a : ℕ} (ha : 0<a) :
    D.startedRetainedField w y T t₀ a₀ x a=D.J*D.startedRetainedSource w y T t₀ a₀ x a-
      (∑l,(D.j*siteMean (D.startedPartial w y a l) x) • SourceTree.sourceMatrix D.j D.J (T l))-
      ∑b:Fin a,(D.j*siteMean (D.auxCoefficient a b) x) • D.startedRetainedSource w y T t₀ a₀ x b := by
  have h:=ClosedTree.branches_field D.j a₀ D.J
    ((Finset.univ.toList.map (fun l=>(D.startedPartial w y a l x,ClosedTree.ofOrdinary (T l))))++
      (Finset.univ.toList.map (fun b:Fin a=>(D.auxCoefficient a b x,D.startedTree w y T t₀ x b))))
  rw [←D.startedTree_pos w y T t₀ x ha] at h
  simpa [List.map_append,List.sum_append,List.map_map,Function.comp_def,
    startedRetainedField,startedRetainedSource,siteMean,SKGap.Noncrossing.Diagram.mean,
    sub_add_eq_sub_sub,ClosedTree.sourceMatrix_ofOrdinary] using h

theorem started_prediction_zero (ht : t₀.leafMass=0) (a : ℕ) (z : ℝ) (i : Fin n) :
    GradedWords.prediction D.j a₀ z ((D.startedTree w y T t₀ x a).words D.j a₀).1 i=0 ∧
    GradedWords.prediction D.j a₀ z ((D.startedTree w y T t₀ x a).words D.j a₀).2 i=0 := by
  exact ⟨ClosedTree.source_prediction_zero D.j a₀ _ (D.startedTree_leafMass w y T t₀ ht x a) z i,
    ClosedTree.field_prediction_zero ..⟩

end SKGapCutoff.Recipe.OrdinaryData

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe.OrdinaryData
open Primary Matrix SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.Tensor.Series
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]
variable (D : OrdinaryData n ι κ σ) (w y : VectorFields n)
    (T : ι→SourceTree (Fin n→ℝ)) (t₀ : ClosedTree (Fin n→ℝ)) (a₀ : Fin n→ℝ) (x : Spin n)

def startedSourceError (a : ℕ) : Interaction n :=
  derivativeMatrix (D.startedSource w y a) x-D.startedRetainedSource w y T t₀ a₀ x a
def startedFieldError (a : ℕ) : Interaction n :=
  derivativeMatrix (D.startedAuxiliary w y a) x-D.startedRetainedField w y T t₀ a₀ x a

lemma started_source_error_recursion {a : ℕ} (ha : 0<a) :
    D.startedSourceError w y T t₀ a₀ x a=
      (∑b:Fin a,Matrix.diagonal (D.auxCoefficient a b x)*D.startedFieldError w y T t₀ a₀ x b)+
      (∑l,Matrix.diagonal (D.startedPartial w y a l x)*
        (derivativeMatrix (D.H l) x-SourceTree.fieldMatrix D.j D.J (T l)))+
      D.sourceAtoms a (fun b=>D.startedAuxiliary w y b) x := by
  rw [startedSourceError,D.started_source_derivative w y ha,D.startedRetainedSource_eq w y T t₀ a₀ x ha]
  simp only [startedFieldError,mul_sub,Finset.sum_sub_distrib]
  abel

lemma started_field_error_recursion {a : ℕ} (ha : 0<a) :
    D.startedFieldError w y T t₀ a₀ x a=D.J*D.startedSourceError w y T t₀ a₀ x a-
      (∑b:Fin a,(D.j*siteMean (D.auxCoefficient a b) x) • D.startedSourceError w y T t₀ a₀ x b)+
      (-(∑l,(D.j*siteMean (D.startedPartial w y a l) x) •
        (derivativeMatrix (D.predecessor l) x-SourceTree.sourceMatrix D.j D.J (T l)))-
      D.j • ((∑l,averageError (siteMean (D.startedPartial w y a l)) (D.predecessor l) x)+
        ∑b:Fin a,averageError (siteMean (D.auxCoefficient a b)) (D.startedSource w y b) x)) := by
  rw [startedFieldError,D.started_field_derivative w y ha,D.startedRetainedField_eq w y T t₀ a₀ x ha]
  simp only [startedSourceError,smul_sub,Finset.sum_sub_distrib,mul_sub]
  abel

@[simp] lemma startedSourceError_zero : D.startedSourceError w y T t₀ a₀ x 0=
    derivativeMatrix w x-t₀.sourceMatrix D.j a₀ D.J := by
  simp [startedSourceError,startedRetainedSource,startedTree]
@[simp] lemma startedFieldError_zero : D.startedFieldError w y T t₀ a₀ x 0=
    derivativeMatrix y x-t₀.fieldMatrix D.j a₀ D.J := by
  simp [startedFieldError,startedRetainedField,startedTree]

end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI
