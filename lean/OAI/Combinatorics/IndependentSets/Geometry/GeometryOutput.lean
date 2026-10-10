import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.EnumerationSimple
import OAI.Combinatorics.IndependentSets.Geometry.GeometryLocations
import OAI.Combinatorics.IndependentSets.Geometry.GeometryAntipodes
import OAI.Combinatorics.IndependentSets.Encoding.GraphPrinter

namespace OAI

namespace LargeIndependentSets.GeometryNames
open IndependentSetsCut.CounterMachine UniformLC ShortestPaths
open IndependentSetsGames.Foundations.Complexity Turing
open scoped Classical BigOperators ENNReal
noncomputable section
attribute [-instance] mixedTupleComputableFintype mixedTupleDecidableEq

variable (L R : Type) [Fintype L] [Fintype R] (p : SamplerParameters) (q : ℕ) (hq : 0<q)

def output (t : Table L R) : Graph :=
  if p.CliqueTest t.lc then Graph.clique q hq
  else Graph.ofEnumeration (p.graph t.lc) (vertexCount_pos L R p t) (vertexEquiv L R p t).symm

def outputRenaming (t : Table L R) : Graph.Renaming (output L R p q hq t) (p.output q hq t.lc) :=
  p.decisionOutput_renaming q hq t.lc (vertexCount_pos L R p t) (vertexEquiv L R p t).symm

def locationDistanceExpr (x : Expr) : Expr := payloadApply (locationExpr L R p (.arg 0)) x

lemma locationDistanceExpr_eval (t : Table L R) (x : Expr) (a : ℕ → ℕ)
    (i : Fin (vertexCount L R p t))
    (hi : x.eval (distances L R p.n (p.m*2^p.k) t).bits a=i.val) :
    (locationDistanceExpr L R p x).eval (distances L R p.n (p.m*2^p.k) t).bits a=
      (locationName L R p t ((vertexEquiv L R p t).symm i)).val := by
  rw [locationDistanceExpr,payloadApply_eval]
  exact locationExpr_eval L R p t (.arg 0) _ i hi

def outputCountExpr : Expr := Expr.cond (cliqueExpr L R p.n (p.m*2^p.k)) (.const q)
  (fromTable (vertexCountExpr L R p))

lemma outputCountExpr_eval (t : Table L R) (a : ℕ → ℕ) :
    (outputCountExpr L R p q).eval (distances L R p.n (p.m*2^p.k) t).bits a=
      (output L R p q hq t).vertices := by
  simp only [outputCountExpr,Expr.cond_eval,cliqueExpr_nonzero,Expr.eval,fromTable_eval,
    vertexCountExpr_eval,output]
  split_ifs <;> rfl

def adjacencyExpr (x y : Expr) : Expr :=
  .mul (.zero (Expr.equal x y)) (Expr.cond (cliqueExpr L R p.n (p.m*2^p.k)) (.const 1)
    (closeExpr (p.m*2^p.k) (locationDistanceExpr L R p x)
      (antiDistanceExpr L R p.n (p.m*2^p.k) (locationDistanceExpr L R p y))))

lemma equal_adj {G H : Graph} (h : G=H) (i j : Fin G.vertices) :
    G.adj i j=H.adj (Fin.cast (congrArg Graph.vertices h) i) (Fin.cast (congrArg Graph.vertices h) j) := by
  subst H
  rfl

lemma clique_adj {G : Graph} (h : G=Graph.clique q hq) (i j : Fin G.vertices) :
    G.adj i j=decide (i≠j) := by
  subst G
  rfl

lemma adjacencyExpr_eval (t : Table L R) (x y : Expr) (a : ℕ → ℕ)
    (i j : Fin (output L R p q hq t).vertices)
    (hi : x.eval (distances L R p.n (p.m*2^p.k) t).bits a=i.val)
    (hj : y.eval (distances L R p.n (p.m*2^p.k) t).bits a=j.val) :
    decide ((adjacencyExpr L R p x y).eval (distances L R p.n (p.m*2^p.k) t).bits a≠0)=
      (output L R p q hq t).adj i j := by
  have hind (P : Prop) [Decidable P] : (if P then (1:ℕ) else 0)=0 ↔ ¬P := by
    split_ifs <;> simp_all
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  have hnon (P : Prop) [Decidable P] : (if P then (1:ℕ) else 0)≠0 ↔ P := by
    split_ifs <;> simp_all
  simp only [adjacencyExpr,Expr.eval,Expr.equal_eval,hi,hj,Expr.cond_eval,cliqueExpr_nonzero,
    mul_ne_zero_iff,hind,hnon]
  by_cases hc : p.CliqueTest t.lc
  · simp only [hc,ite_true]
    rw [clique_adj q hq (by rw [output,ite_eq_left hc]) i j,decide_eq_true_eq]
    constructor
    · rintro ⟨h,_⟩; exact fun he => h (congrArg Fin.val he)
    · intro h; exact ⟨fun he => h (Fin.ext he),by decide⟩
  · have hv : (output L R p q hq t).vertices=vertexCount L R p t := by rw [output,ite_eq_right hc]; rfl
    let ii : Fin (vertexCount L R p t) := ⟨i.val,hv ▸ i.isLt⟩
    let jj : Fin (vertexCount L R p t) := ⟨j.val,hv ▸ j.isLt⟩
    have hli := locationDistanceExpr_eval L R p t x a ii hi
    have hlj := locationDistanceExpr_eval L R p t y a jj hj
    simp only [hc,ite_false]
    rw [closeExpr_nonzero L R p.n (p.m*2^p.k) t _ _ _
      (locationName L R p t ((vertexEquiv L R p t).symm ii))
      (antiName L R p.n (p.m*2^p.k) t (locationName L R p t ((vertexEquiv L R p t).symm jj)))
      hli (antiDistanceExpr_eval L R p.n (p.m*2^p.k) t _ _ _ hlj),antiName_exact,
      locationName_exact,locationName_exact]
    have he : (output L R p q hq t).adj i j=
        decide ((p.graph t.lc).Adj ((vertexEquiv L R p t).symm ii) ((vertexEquiv L R p t).symm jj)) := by
      have hh : output L R p q hq t=Graph.ofEnumeration (p.graph t.lc)
          (vertexCount_pos L R p t) (vertexEquiv L R p t).symm := by rw [output,ite_eq_right hc]
      exact equal_adj hh i j
    rw [he,decide_eq_true_eq]
    change (_ ∧ _) ↔ (_ ∧ _)
    apply and_congr_left
    intro _
    simp only [ne_eq,Equiv.apply_eq_iff_eq,Fin.ext_iff,ii,jj]

def flatAdjacencyExpr : Expr := adjacencyExpr L R p
  (Expr.quotient (.arg 0) (outputCountExpr L R p q))
  (Expr.remainder (.arg 0) (outputCountExpr L R p q))

lemma flatAdjacencyExpr_eval (t : Table L R)
    (i : Fin ((output L R p q hq t).vertices*(output L R p q hq t).vertices)) :
    decide ((flatAdjacencyExpr L R p q).eval (distances L R p.n (p.m*2^p.k) t).bits (fun _ => i.val)≠0)=
      (output L R p q hq t).adj i.divNat i.modNat := by
  apply adjacencyExpr_eval L R p q hq t _ _ _ i.divNat i.modNat
  · simp only [Expr.quotient_eval,Expr.eval,outputCountExpr_eval L R p q hq,Fin.divNat]
  · simp only [Expr.remainder_eval,Expr.eval,outputCountExpr_eval L R p q hq,Fin.modNat]

def graphSerializer : TM2ComputableInPolyTime (fun t => (distances L R p.n (p.m*2^p.k) t).bits)
    graphBits (output L R p q hq) :=
  GraphPrinter.encodedComputer _ _ (outputCountExpr L R p q) (flatAdjacencyExpr L R p q)
    (outputCountExpr_eval L R p q hq) (flatAdjacencyExpr_eval L R p q hq)

lemma graphSerializer_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet (graphSerializer L R p q hq).tm :=
  GraphPrinter.encodedComputer_finiteAlphabet _ _ _ _ _ _

def distanceView : TM2ComputableInPolyTime Table.bits
    (fun t => (distances L R p.n (p.m*2^p.k) t).bits) id where
  tm := (distanceComputer L R p.n (p.m*2^p.k)).tm
  inputAlphabet := (distanceComputer L R p.n (p.m*2^p.k)).inputAlphabet
  outputAlphabet := (distanceComputer L R p.n (p.m*2^p.k)).outputAlphabet
  time := (distanceComputer L R p.n (p.m*2^p.k)).time
  outputsFun := (distanceComputer L R p.n (p.m*2^p.k)).outputsFun

def graphComputer : TM2ComputableInPolyTime Table.bits graphBits (output L R p q hq) :=
  MachineSequential.composeBits (distanceView L R p) (graphSerializer L R p q hq)

lemma graphComputer_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet (graphComputer L R p q hq).tm :=
  MachineFiniteAlphabet.composeBits (distanceView L R p) (graphSerializer L R p q hq)
    (distanceComputer_finiteAlphabet L R p.n (p.m*2^p.k)) (graphSerializer_finiteAlphabet L R p q hq)

attribute [instance 1100] mixedTupleComputableFintype
attribute [instance] mixedTupleDecidableEq
end
end LargeIndependentSets.GeometryNames

end OAI
