import Mathlib
import OAI.Probability.SKGap.Localization.StartedGraph
import OAI.Probability.SKGap.Localization.ClosedMarked

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.ClosedMarked.SmallTree
open Primary Primary.Tensor.Series
variable {n : ℕ}

def smallBranches (xs : List ((Fin n→ℝ)×ClosedTree (Fin n→ℝ))) (U : SmallTree n) : SmallTree n :=
  xs.foldr (fun t v=>.small t.1 t.2 v) U
def boundedBranches (xs : List ((Fin n→ℝ)×SmallTree n)) (U : SmallTree n) : SmallTree n :=
  xs.foldr (fun t v=>.bounded t.1 t.2 v) U
lemma tree_smallBranches (xs : List ((Fin n→ℝ)×ClosedTree (Fin n→ℝ))) (U : SmallTree n) :
    (smallBranches xs U).tree=xs.foldr (fun t v=>ClosedTree.branch t.1 t.2 v) U.tree := by
  induction xs with
  | nil => rfl
  | cons t xs ih => simpa only [smallBranches,List.foldr_cons,tree] using congrArg (ClosedTree.branch t.1 t.2) ih
lemma tree_boundedBranches (xs : List ((Fin n→ℝ)×SmallTree n)) (U : SmallTree n) :
    (boundedBranches xs U).tree=(xs.map (fun t=>(t.1,t.2.tree))).foldr (fun t v=>ClosedTree.branch t.1 t.2 v) U.tree := by
  induction xs with
  | nil => rfl
  | cons t xs ih =>
    simpa only [boundedBranches,List.foldr_cons,tree,List.map_cons] using congrArg (ClosedTree.branch t.1 t.2.tree) ih
end SKGap.Noncrossing.ClosedMarked.SmallTree

namespace SKGapCutoff.Recipe.OrdinaryData
open Primary Matrix SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.Tensor.Series
open SKGap.Noncrossing.ClosedMarked
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

def startedSmallTree (D : OrdinaryData n ι κ σ) (w y : VectorFields n)
    (T : ι→SourceTree (Fin n→ℝ)) (t₀ : SmallTree n) (x : Spin n) (a : ℕ) : SmallTree n :=
  match a with
  | 0 => t₀
  | a+1 => SmallTree.smallBranches
      (Finset.univ.toList.map (fun l=>(D.startedPartial w y (a+1) l x,ClosedTree.ofOrdinary (T l))))
      (SmallTree.boundedBranches
        (Finset.univ.toList.map (fun b : Fin (a+1)=>(D.auxCoefficient (a+1) b x,startedSmallTree D w y T t₀ x b))) .zero)
termination_by a

lemma startedSmallTree_tree (D : OrdinaryData n ι κ σ) (w y : VectorFields n)
    (T : ι→SourceTree (Fin n→ℝ)) (t₀ : SmallTree n) (x : Spin n) (a : ℕ) :
    (D.startedSmallTree w y T t₀ x a).tree=D.startedTree w y T t₀.tree x a := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
    cases a with
    | zero => simp only [startedSmallTree,startedTree]
    | succ a =>
      rw [startedSmallTree,SmallTree.tree_smallBranches,SmallTree.tree_boundedBranches,startedTree]
      simp only [ClosedTree.branches,List.foldr_append,List.map_map,Function.comp_def,SmallTree.tree]
      congr 2
      apply List.map_congr_left
      intro b hb
      exact congrArg (fun t=>(D.auxCoefficient (a+1) b x,t)) (ih b b.isLt)

theorem started_retained_diagonal (D : OrdinaryData n ι κ σ) (w y : VectorFields n)
    (T : ι→SourceTree (Fin n→ℝ)) (t₀ : SmallTree n) (a₀ : Fin n→ℝ) (x : Spin n)
    (a : ℕ) (hn : 0<n) {B : ℝ} (hB : 0≤B)
    (hb : ∀d:Fin n→ℝ,(∀i,|d i|≤1)→∀P∈[
        ((D.startedSmallTree w y T t₀ x a).marked D.j a₀).1,
        ((D.startedSmallTree w y T t₀ x a).marked D.j a₀).2],∀t∈P,
      diagonalSeminorm (exactWord D.j a₀ (t.2.diagnostic d) D.J-
        Matrix.diagonal (wordPrediction D.j a₀ 1 (t.2.diagnostic d)))≤B) :
    (∑i,|D.startedRetainedSource w y T t₀.tree a₀ x a i i|)≤
        ((D.startedSmallTree w y T t₀ x a).marked D.j a₀).1.budget*B ∧
    (∑i,|D.startedRetainedField w y T t₀.tree a₀ x a i i|)≤
        ((D.startedSmallTree w y T t₀ x a).marked D.j a₀).2.budget*B := by
  have H:=(D.startedSmallTree w y T t₀ x a).diagonal D.j a₀ D.J hn hB hb
  rw [D.startedSmallTree_tree w y T t₀ x a] at H
  exact H

end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI
