import Mathlib
import OAI.Probability.SKGap.Stability.OrdinaryRecipe
import OAI.Probability.SKGap.Localization.PrimaryDifferentiation
import OAI.Probability.SKGap.Stability.OrdinaryGraph

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary.SourceTree
open Diagram
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def branches : List ((ι→ℝ)×SourceTree (ι→ℝ))→SourceTree (ι→ℝ)
  | [] => .leaf 0
  | (p,t)::ts => .branch p t (branches ts)

omit [Fintype ι] [DecidableEq ι] in
lemma branches_leafMass (ts : List ((ι→ℝ)×SourceTree (ι→ℝ))) : (branches ts).leafMass=0 := by
  induction ts with
  | nil => rfl
  | cons t ts ih => exact ih

lemma branches_source (j : ℝ) (J : Matrix ι ι ℝ) (ts : List ((ι→ℝ)×SourceTree (ι→ℝ))) :
    sourceMatrix j J (branches ts)=(ts.map (fun t=>Matrix.diagonal t.1*fieldMatrix j J t.2)).sum := by
  induction ts with
  | nil => simp [branches,sourceMatrix_leaf]
  | cons t ts ih => simp [branches,sourceMatrix_branch,ih]

lemma branches_field (j : ℝ) (J : Matrix ι ι ℝ) (ts : List ((ι→ℝ)×SourceTree (ι→ℝ))) :
    fieldMatrix j J (branches ts)=J*sourceMatrix j J (branches ts)-
      (ts.map (fun t=>(j*Diagram.mean t.1) • sourceMatrix j J t.2)).sum := by
  induction ts with
  | nil => simp [branches,sourceMatrix_leaf,fieldMatrix_leaf]
  | cons t ts ih =>
    simp only [branches,sourceMatrix_branch,fieldMatrix_branch,List.map_cons,List.sum_cons,ih,mul_add]
    abel

end SKGap.Noncrossing.Primary.SourceTree
namespace SKGapCutoff.Primary
open SKGap.Noncrossing.Primary
variable {n : ℕ}

def primaryTree (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) : ℕ→SourceTree (Fin n→ℝ)
  | 0 => .leaf 1
  | k+1 => .branch (primaryDiagonal j J h x k) (primaryTree j J h x k) (.leaf 0)

lemma primaryTree_matrices (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) (k : ℕ) :
    SourceTree.sourceMatrix j J (primaryTree j J h x k)=formalMag j J h x k ∧
    SourceTree.fieldMatrix j J (primaryTree j J h x k)=formalField j J h x k := by
  induction k with
  | zero => simp [primaryTree,SourceTree.sourceMatrix_leaf,SourceTree.fieldMatrix_leaf,
      formalMag,formalField,primaryMatrix]
  | succ k ih =>
    constructor
    · simp [primaryTree,SourceTree.sourceMatrix_branch,SourceTree.sourceMatrix_leaf,ih.2,formalMag]
    · simp only [primaryTree,SourceTree.fieldMatrix_branch,SourceTree.fieldMatrix_leaf,zero_smul,
        add_zero,ih.1,ih.2]
      rw [formalField_succ,formalMag]

end SKGapCutoff.Primary
namespace SKGapCutoff.Recipe.OrdinaryData
open SKGap.Noncrossing.Primary SKGap.Noncrossing.Diagram Primary Matrix
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

def retainedTree (D : OrdinaryData n ι κ σ) (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n)
    (a : ℕ) : SourceTree (Fin n→ℝ) :=
  SourceTree.branches ((Finset.univ.toList.map (fun l=>(D.sourcePartial a l x,T l)))++
    (Finset.univ.toList.map (fun b : Fin a=>(D.auxCoefficient a b x,retainedTree D T x b))))
termination_by a

lemma retainedTree_leafMass (D : OrdinaryData n ι κ σ) (T : ι→SourceTree (Fin n→ℝ))
    (x : Spin n) (a : ℕ) : (D.retainedTree T x a).leafMass=0 := by
  rw [retainedTree,SourceTree.branches_leafMass]

def retainedSource (D : OrdinaryData n ι κ σ) (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (a : ℕ) :=
  SourceTree.sourceMatrix D.j D.J (D.retainedTree T x a)
def retainedField (D : OrdinaryData n ι κ σ) (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (a : ℕ) :=
  SourceTree.fieldMatrix D.j D.J (D.retainedTree T x a)

lemma retainedSource_eq (D : OrdinaryData n ι κ σ) (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (a : ℕ) :
    D.retainedSource T x a=
      (∑l,Matrix.diagonal (D.sourcePartial a l x)*SourceTree.fieldMatrix D.j D.J (T l))+
      ∑b:Fin a,Matrix.diagonal (D.auxCoefficient a b x)*D.retainedField T x b := by
  rw [retainedSource,retainedTree,SourceTree.branches_source]
  simp [List.map_append,List.sum_append,List.map_map,Function.comp_def,retainedField]

lemma retainedField_eq (D : OrdinaryData n ι κ σ) (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (a : ℕ) :
    D.retainedField T x a=D.J*D.retainedSource T x a-
      (∑l,(D.j*siteMean (D.sourcePartial a l) x) • SourceTree.sourceMatrix D.j D.J (T l))-
      ∑b:Fin a,(D.j*siteMean (D.auxCoefficient a b) x) • D.retainedSource T x b := by
  have h:=SourceTree.branches_field D.j D.J
    ((Finset.univ.toList.map (fun l=>(D.sourcePartial a l x,T l)))++
      (Finset.univ.toList.map (fun b:Fin a=>(D.auxCoefficient a b x,D.retainedTree T x b))))
  rw [show SourceTree.branches _=D.retainedTree T x a from (by rw [retainedTree])] at h
  simpa [List.map_append,List.sum_append,List.map_map,Function.comp_def,
    retainedField,retainedSource,siteMean,SKGap.Noncrossing.Diagram.mean,
    sub_add_eq_sub_sub] using h

theorem retained_prediction_zero (D : OrdinaryData n ι κ σ) (T : ι→SourceTree (Fin n→ℝ))
    (x : Spin n) (a : ℕ) (i : Fin n) :
    polynomialPrediction D.j ((D.retainedTree T x a).words D.j).1 i=0 ∧
    polynomialPrediction D.j ((D.retainedTree T x a).words D.j).2 i=0 := by
  constructor
  · rw [SourceTree.source_prediction,retainedTree_leafMass]
  · exact SourceTree.field_prediction_zero ..

end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI
