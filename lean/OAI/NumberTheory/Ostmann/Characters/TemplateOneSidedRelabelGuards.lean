import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationCore
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedRelabelTemplate

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedRelabel
open SymbolicHistory TemplateOneSidedCancellation Template
variable {ι κ ν : Type*}

def relabelGuard (π : ι → κ) (g : Guard ι) : Guard κ :=
  ⟨relabel π g.expression,g.threshold,g.above,g.strict⟩

def relabelResidueGuard (π : ι → κ) (g : ResidueGuard ι) : ResidueGuard κ :=
  ⟨relabel π g.expression,g.frequency⟩

@[simp] theorem relabelGuard_holds (π : ι → κ) (g : Guard ι) (a : κ → ℤ) :
    (relabelGuard π g).holds a ↔ g.holds (fun i=>a (π i)) := by
  simp only [Guard.holds,relabelGuard,relabel_integerEval]

@[simp] theorem relabelResidueGuard_holds (π : ι → κ) (g : ResidueGuard ι) (a : κ → ℤ) :
    (relabelResidueGuard π g).holds a ↔ g.holds (fun i=>a (π i)) := by
  simp only [ResidueGuard.holds,relabelResidueGuard,relabel_integerEval,relabel_integralAt]
  rfl

@[simp] theorem relabelResidueGuard_modulus (π : ι → κ) (g : ResidueGuard ι) :
    (relabelResidueGuard π g).modulus = g.modulus := by
  simp only [ResidueGuard.modulus,relabelResidueGuard,relabel_supportModulus,relabel_denominator]

@[simp] theorem residueModulus_relabel (π : ι → κ) (gs : List (ResidueGuard ι)) :
    residueModulus (gs.map (relabelResidueGuard π)) = residueModulus gs := by
  simp only [residueModulus,List.map_map,Function.comp_def,relabelResidueGuard_modulus]

@[simp] theorem rootResidueGuards_relabel (π : ι → κ) (k j : ℕ) (s : ℤ)
    (e : Expressions (ι:=ι) k j) :
    rootResidueGuards k j s (relabelExpressions π e) =
      (rootResidueGuards k j s e).map (relabelResidueGuard π) := by
  simp only [rootResidueGuards,List.map_ofFn,Function.comp_def,relabelResidueGuard,relabelExpressions]

@[simp] theorem nodeResidueGuards_relabel (π : ι → κ) (k j : ℕ)
    (e : Expressions (ι:=ι) k (j+1)) (s v w : ℤ) :
    nodeResidueGuards k j (relabelExpressions π e) s v w =
      (nodeResidueGuards k j e s v w).map (relabelResidueGuard π) := by
  simp only [nodeResidueGuards,pivotExpression_relabel,copiedExpression_relabel,
    List.map_cons,List.map_nil,relabelResidueGuard]

@[simp] theorem historyResidueGuards_relabel (π : ι → κ) (k j : ℕ) (s : ℤ)
    (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j) :
    historyResidueGuards k j s (relabelExpressions π e) t =
      (historyResidueGuards k j s e t).map (relabelResidueGuard π) := by
  induction j generalizing s with
  | zero => exact rootResidueGuards_relabel π k 0 s e
  | succ j ih => simp only [historyResidueGuards,rootResidueGuards_relabel,
      nodeResidueGuards_relabel,pivotExpression_relabel,childExpressions_relabel,ih,List.map_append]

@[simp] theorem historyResidueModulus_relabel (π : ι → κ) (k j : ℕ) (s : ℤ)
    (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j) :
    residueModulus (historyResidueGuards k j s (relabelExpressions π e) t) =
      residueModulus (historyResidueGuards k j s e t) := by
  rw [historyResidueGuards_relabel,residueModulus_relabel]

@[simp] theorem substituteGuard_relabel (π : ι → κ) (g : Guard ν) (x : ν → Expr ι) :
    g.substitute (fun i=>relabel π (x i)) = relabelGuard π (g.substitute x) := by
  cases g
  simp only [Guard.substitute,relabelGuard,relabel_substitute]

@[simp] theorem substituteGuard_relabelExpressions (π : ι → κ) (k j : ℕ)
    (g : Guard (schedule k j).Slot) (e : Expressions (ι:=ι) k j) :
    g.substitute (relabelExpressions π e) = relabelGuard π (g.substitute e) :=
  substituteGuard_relabel π g e

@[simp] theorem positiveGuards_relabel (π : ι → κ) (k j : ℕ)
    (e : Expressions (ι:=ι) k j) :
    positiveGuards k j (relabelExpressions π e) =
      (positiveGuards k j e).map (relabelGuard π) := by
  simp only [positiveGuards,List.map_ofFn,Function.comp_def,relabelGuard,relabelExpressions]

@[simp] theorem nodeGuards_relabel (π : ι → κ) (k j : ℕ)
    (e : Expressions (ι:=ι) k (j+1)) (s v w B V : ℤ) :
    nodeGuards k j (relabelExpressions π e) s v w B V =
      (nodeGuards k j e s v w B V).map (relabelGuard π) := by
  simp only [nodeGuards,pivotExpression_relabel,copiedExpression_relabel,
    List.map_cons,List.map_nil,relabelGuard]

@[simp] theorem historyGuards_relabel (π : ι → κ) (k : ℕ) (B V : ℕ → ℤ)
    (g : (j:ℕ) → ℤ → List (Guard (schedule k j).Slot)) (j : ℕ) (s : ℤ)
    (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j) :
    historyGuards k B V g j s (relabelExpressions π e) t =
      (historyGuards k B V g j s e t).map (relabelGuard π) := by
  induction j generalizing s with
  | zero => simp only [historyGuards,positiveGuards_relabel,List.map_append,List.map_map,
      substituteGuard_relabelExpressions π k 0,Function.comp_def]
  | succ j ih => simp only [historyGuards,positiveGuards_relabel,nodeGuards_relabel,
      pivotExpression_relabel,childExpressions_relabel,ih,List.map_append,List.map_map,
      substituteGuard_relabelExpressions π k (j+1),Function.comp_def]

@[simp] theorem maskGuards_relabel (π : ι → κ) (k : ℕ)
    (g : (j:ℕ) → ℤ → List (Guard (schedule k j).Slot)) (j : ℕ) (s : ℤ)
    (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j) :
    maskGuards k g j s (relabelExpressions π e) t =
      (maskGuards k g j s e t).map (relabelGuard π) := by
  induction j generalizing s with
  | zero => simp only [maskGuards,List.map_map,
      substituteGuard_relabelExpressions π k 0,Function.comp_def]
  | succ j ih => simp only [maskGuards,pivotExpression_relabel,childExpressions_relabel,
      ih,List.map_append,List.map_map,substituteGuard_relabelExpressions π k (j+1),Function.comp_def]

@[simp] theorem coreGuardList_relabel (π : ι → κ) (k : ℕ) (B V : ℕ → ℤ)
    (g m : (j:ℕ) → ℤ → List (Guard (schedule k j).Slot)) (j : ℕ) (s : ℤ)
    (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j) :
    coreGuardList k B V g m j s (relabelExpressions π e) t =
      (coreGuardList k B V g m j s e t).map (relabelGuard π) := by
  simp only [coreGuardList,historyGuards_relabel,maskGuards_relabel,List.map_append]

end Ostmann.Characters.TemplateOneSidedRelabel

end

end OAI
