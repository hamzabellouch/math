import Mathlib
import OAI.Probability.SKGap.Localization.RecipeGraph
import OAI.Probability.SKGap.Matrix.ClosedTrace

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary.MarkedPolynomial
open Diagram
variable {n : ℕ}

def diagonalWords (s : Fin n→ℝ) (P : WordPolynomial (ι:=Fin n)) : MarkedPolynomial n :=
  P.map (fun t=>(t.1,SmallMark.diagonal [] s t.2))
def averageWords (c : ℝ) (s : Fin n→ℝ) (P : WordPolynomial (ι:=Fin n)) : MarkedPolynomial n :=
  P.map (fun t=>(c*t.1,SmallMark.average s t.2))
def mass (P : WordPolynomial (ι:=Fin n)) : ℝ := (P.map (fun t=>|t.1|)).sum

lemma plain_diagonalWords (s : Fin n→ℝ) (P : WordPolynomial (ι:=Fin n)) :
    (diagonalWords s P).plain=prependWords [.diag s] P := by
  simp [diagonalWords,plain,prependWords,List.map_map,Function.comp_def,SmallMark.scalar,SmallMark.word]
lemma plain_averageWords (c : ℝ) (s : Fin n→ℝ) (P : WordPolynomial (ι:=Fin n)) :
    (averageWords c s P).plain=Primary.scale (c*Diagram.mean s) P := by
  simp only [averageWords,plain,Primary.scale,List.map_map,Function.comp_def,SmallMark.scalar,SmallMark.word]
  congr 1; funext t; congr 1; ring
lemma budget_diagonalWords (s : Fin n→ℝ) (P : WordPolynomial (ι:=Fin n)) :
    (diagonalWords s P).budget=SKGapCutoff.Recipe.vectorNorm s*mass P := by
  induction P with
  | nil => simp [diagonalWords,budget,mass]
  | cons t P ih =>
    simp only [diagonalWords,List.map_cons,budget,List.sum_cons,SmallMark.vector,mass] at *
    rw [ih]; ring
lemma budget_averageWords (c : ℝ) (s : Fin n→ℝ) (P : WordPolynomial (ι:=Fin n)) :
    (averageWords c s P).budget=|c| *SKGapCutoff.Recipe.vectorNorm s*mass P := by
  induction P with
  | nil => simp [averageWords,budget,mass]
  | cons t P ih =>
    simp only [averageWords,List.map_cons,budget,List.sum_cons,SmallMark.vector,mass,abs_mul] at *
    rw [ih]; ring

abbrev Pair (n : ℕ) := MarkedPolynomial n×MarkedPolynomial n

def pairPlain (V : Pair n) : WordPolynomial (ι:=Fin n)×WordPolynomial (ι:=Fin n) := (V.1.plain,V.2.plain)

def zeroPair : Pair n := ([(0,.average 0 [])],[(0,.average 0 [.noise])])
lemma zeroPair_plain (j : ℝ) : pairPlain (zeroPair (n:=n))=(SourceTree.leaf 0).words j := by
  simp [pairPlain,zeroPair,plain,SmallMark.scalar,SmallMark.word,SourceTree.words]

def smallBranch (j : ℝ) (p : Fin n→ℝ) (T : SourceTree (Fin n→ℝ)) (V : Pair n) : Pair n :=
  (diagonalWords p (T.words j).2++V.1,
    ((diagonalWords p (T.words j).2).prepend [.noise]++averageWords (-j) p (T.words j).1)++V.2)

def boundedBranch (j : ℝ) (p : Fin n→ℝ) (U V : Pair n) : Pair n :=
  (U.2.prepend [.diag p]++V.1,
    (U.2.prepend [.noise,.diag p]++U.1.scale (-(j*Diagram.mean p)))++V.2)

lemma smallBranch_plain (j : ℝ) (p : Fin n→ℝ) (T S : SourceTree (Fin n→ℝ)) (V : Pair n)
    (hV : pairPlain V=S.words j) : pairPlain (smallBranch j p T V)=(SourceTree.branch p T S).words j := by
  have hv₁ : V.1.plain=(S.words j).1 := congrArg Prod.fst hV
  have hv₂ : V.2.plain=(S.words j).2 := congrArg Prod.snd hV
  simp only [pairPlain,smallBranch,plain_append,plain_prefix,plain_diagonalWords,plain_averageWords,hv₁,hv₂,
    SourceTree.words]
  congr 1
  simp [prependWords,List.map_map,Function.comp_def,neg_mul]

lemma boundedBranch_plain (j : ℝ) (p : Fin n→ℝ) (T S : SourceTree (Fin n→ℝ)) (U V : Pair n)
    (hU : pairPlain U=T.words j) (hV : pairPlain V=S.words j) :
    pairPlain (boundedBranch j p U V)=(SourceTree.branch p T S).words j := by
  have hu₁ : U.1.plain=(T.words j).1 := congrArg Prod.fst hU
  have hu₂ : U.2.plain=(T.words j).2 := congrArg Prod.snd hU
  have hv₁ : V.1.plain=(S.words j).1 := congrArg Prod.fst hV
  have hv₂ : V.2.plain=(S.words j).2 := congrArg Prod.snd hV
  simp only [pairPlain,boundedBranch,plain_append,plain_prefix,plain_scale,hu₁,hu₂,hv₁,hv₂,SourceTree.words]

lemma fold_plain {α : Type*} (j : ℝ) (xs : List α) (p : α→Fin n→ℝ)
    (T : α→SourceTree (Fin n→ℝ)) (step : α→Pair n→Pair n)
    (hstep : ∀a V S,pairPlain V=S.words j→pairPlain (step a V)=(SourceTree.branch (p a) (T a) S).words j) :
    pairPlain (xs.foldr step zeroPair)=(SourceTree.branches (xs.map (fun a=>(p a,T a)))).words j := by
  induction xs with
  | nil => exact zeroPair_plain j
  | cons a xs ih => exact hstep a _ _ ih

end SKGap.Noncrossing.Primary.MarkedPolynomial
namespace SKGapCutoff.Recipe.OrdinaryData
open SKGap.Noncrossing.Primary SKGap.Noncrossing.Diagram MarkedPolynomial
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

def markedRecipe (D : OrdinaryData n ι κ σ) (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (a : ℕ) : Pair n :=
  let entries : List (ι⊕Fin a) := Finset.univ.toList.map Sum.inl++Finset.univ.toList.map Sum.inr
  entries.foldr (fun e V=>match e with
    | .inl l => smallBranch D.j (D.sourcePartial a l x) (T l) V
    | .inr b => boundedBranch D.j (D.auxCoefficient a b x) (markedRecipe D T x b) V) zeroPair
termination_by a

theorem markedRecipe_plain (D : OrdinaryData n ι κ σ) (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (a : ℕ) :
    pairPlain (D.markedRecipe T x a)=(D.retainedTree T x a).words D.j := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
    rw [markedRecipe,retainedTree]
    have H:=fold_plain D.j (Finset.univ.toList.map (Sum.inl : ι→ι⊕Fin a)++Finset.univ.toList.map Sum.inr)
      (Sum.elim (fun l=>D.sourcePartial a l x) (fun b=>D.auxCoefficient a b x))
      (Sum.elim T (fun b=>D.retainedTree T x b))
      (fun e V=>match e with
        | .inl l=>smallBranch D.j (D.sourcePartial a l x) (T l) V
        | .inr b=>boundedBranch D.j (D.auxCoefficient a b x) (D.markedRecipe T x b) V)
      (by
        intro e V S hV
        cases e with
        | inl l=>exact smallBranch_plain D.j _ _ _ _ hV
        | inr b=>exact boundedBranch_plain D.j _ _ _ _ _ (ih b b.isLt) hV)
    simpa only [List.map_append,List.map_map,Function.comp_def,Sum.elim_inl,Sum.elim_inr] using H

end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI
