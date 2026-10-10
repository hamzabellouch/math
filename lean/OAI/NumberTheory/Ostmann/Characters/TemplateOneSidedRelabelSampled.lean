import OAI.NumberTheory.Ostmann.Characters.TemplateConstituentActions
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedBudget
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedRelabelGuards

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedRelabel
open SymbolicHistory TemplateOneSidedCancellation Template TemplateOneSidedBudget
open HistoryFrequencyLabels HistoryFrequencyBudget Preliminaries
variable {ι κ : Type*}

@[simp] theorem relabel_divisorsBelow (π : ι → κ) (e : Expr ι) (p : ℕ) :
    (relabel π e).DivisorsBelow p ↔ e.DivisorsBelow p := by
  induction e <;> simp_all [relabel,substitute,Expr.DivisorsBelow]

@[simp] theorem obstructionExpressions_relabel (π : ι → κ) (k j : ℕ) (b : Bool) (s : ℤ)
    (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j) :
    obstructionExpressions k j b s (relabelExpressions π e) t =
      (obstructionExpressions k j b s e t).map (relabel π) := by
  simp only [obstructionExpressions,pivotExpressions_relabel,bottomExpressions_relabel,
    List.map_append,List.map_map,Function.comp_def,relabelBottom,periodExpression_relabel]

def permutedSampledExpressions (k j : ℕ) (width : Role → ℕ)
    (π : Equiv.Perm ((schedule k j).Constituent width)) :
    Expressions (ι:=(schedule k j).Constituent width) k j :=
  relabelExpressions π.symm (sampledExpressions k j width)

theorem permutedSampledExpressions_prime_eval (k j : ℕ) (width : Role → ℕ)
    (π : Equiv.Perm ((schedule k j).Constituent width)) {Q : ℕ}
    (a : (schedule k j).Constituent width → PrimeUpTo Q) :
    evalExpressions (fun i=>(a i).val) (permutedSampledExpressions k j width π) =
      constituentSampleState (schedule k j) width
        (constituentAssignment (schedule k j) width π a) := by
  rw [permutedSampledExpressions,relabelExpressions_eval]
  exact sampledExpressions_prime_eval k j width (constituentAssignment (schedule k j) width π a)

theorem permutedSampledExpressions_good (k j : ℕ) (width : Role → ℕ)
    (π : Equiv.Perm ((schedule k j).Constituent width))
    (a : (schedule k j).Constituent width → ℤ) (i : (schedule k j).Slot) :
    HistoryReconstruction.Good a (permutedSampledExpressions k j width π i) := by
  exact (relabel_good π.symm _ a).mpr (sampledExpressions_good k j width _ i)

theorem permutedSampledExpressions_syntaxSize (k j : ℕ) (width : Role → ℕ)
    (π : Equiv.Perm ((schedule k j).Constituent width)) (i : (schedule k j).Slot) :
    (permutedSampledExpressions k j width π i).syntaxSize ≤ 2*(width ((schedule k j).role i)+1) := by
  simpa only [permutedSampledExpressions,relabelExpressions,relabel_syntaxSize] using
    sampledExpressions_syntaxSize k j width i

theorem permutedSampledExpressions_fixedBound (k j : ℕ) (width : Role → ℕ)
    (π : Equiv.Perm ((schedule k j).Constituent width)) {B : ℝ} (hB : 1 ≤ B)
    (i : (schedule k j).Slot) :
    (permutedSampledExpressions k j width π i).FixedBound B :=
  (relabel_fixedBound π.symm _ B).mpr (sampledExpressions_fixedBound k j width hB i)

@[simp] theorem permutedSampledResidueModulus (k j : ℕ) (width : Role → ℕ)
    (π : Equiv.Perm ((schedule k j).Constituent width)) (s : ℤ) (t : HistoryReconstruction.Tree j) :
    residueModulus (historyResidueGuards k j s (permutedSampledExpressions k j width π) t) =
      residueModulus (historyResidueGuards k j s (sampledExpressions k j width) t) :=
  historyResidueModulus_relabel π.symm k j s _ t

theorem permutedSampled_obstructions_size (k j : ℕ) (width : Role → ℕ)
    (π : Equiv.Perm ((schedule k j).Constituent width)) (m : ℕ)
    (hm : ∀r,width r ≤ m) (b : Bool) (s : ℤ) (t : HistoryReconstruction.Tree j) :
    ∀q∈obstructionExpressions k j b s (permutedSampledExpressions k j width π) t,
      q.syntaxSize ≤ (3*obstructionSizeFactor k j)*(m+1) ∧
      q.degreeBudget ≤ (3*obstructionSizeFactor k j)*(m+1) := by
  intro q hq
  rw [permutedSampledExpressions,obstructionExpressions_relabel] at hq
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
  simpa only [relabel_syntaxSize,relabel_degreeBudget] using sampled_obstructions_size k j width m hm b s t r hr

theorem permutedSampled_obstructions_fixedLogBound {a m : ℝ} (ha : 0 ≤ a) (hm : 1 ≤ m)
    (k j : ℕ) (width : Role → ℕ) (π : Equiv.Perm ((schedule k j).Constituent width))
    (b : Bool) (s : ℤ) (t : HistoryReconstruction.Tree j)
    (ht : RangeSupported (ranges a m j) j [] s t) :
    ∀q∈obstructionExpressions k j b s (permutedSampledExpressions k j width π) t,
      q.FixedLogBound (linearEnvelope a j*m) := by
  intro q hq
  rw [permutedSampledExpressions,obstructionExpressions_relabel] at hq
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
  exact (relabel_fixedLogBound π.symm _ _).mpr (sampled_obstructions_fixedLogBound ha hm k j width b s t ht r hr)

theorem permutedSampled_residueModulus_le_historyPolynomialCost {a : ℝ} (ha : 0 ≤ a)
    (k j : ℕ) (z L : ℝ) (hm : 1 ≤ ⌊z*L⌋₊)
    (width : Role → ℕ) (hw : ∀r,width r ≤ ⌊z*L⌋₊+1)
    (π : Equiv.Perm ((schedule k j).Constituent width))
    (s : ℤ) (t : HistoryReconstruction.Tree j)
    (ht : RangeSupported (ranges a (⌊z*L⌋₊:ℝ) j) j [] s t) :
    ((residueModulus (historyResidueGuards k j s
      (permutedSampledExpressions k j width π) t)).natAbs:ℝ) ≤
      Real.exp (historyPolynomialCost (residuePolynomialConstant a k j) z 3 L) := by
  rw [permutedSampledResidueModulus]
  exact sampled_residueModulus_le_historyPolynomialCost ha k j z L hm width hw s t ht

end Ostmann.Characters.TemplateOneSidedRelabel

end

end OAI
