import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedBudgetFrequency
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedBudgetGuards
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationFrequencySupport

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedBudget
open SymbolicHistory Template TemplateOneSidedCancellation HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable
variable {ι : Type*}

def residueCount (k : ℕ) : ℕ → ℕ
  | 0 => Fintype.card (schedule k 0).Slot
  | j+1 => Fintype.card (schedule k (j+1)).Slot+3+2*residueCount k j

theorem historyResidueGuards_length (k j : ℕ) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) :
    (historyResidueGuards k j s e t).length=residueCount k j := by
  induction j generalizing s with
  | zero => simp only [historyResidueGuards,rootResidueGuards,List.length_ofFn,residueCount]
  | succ j ih =>
    simp only [historyResidueGuards,rootResidueGuards,List.length_ofFn,List.length_append,
      nodeResidueGuards,List.length_cons,List.length_nil,ih,residueCount]
    omega

lemma rootResidueGuards_size (k j : ℕ) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (M : ℕ) (he : ∀i,(e i).syntaxSize ≤ M) :
    ∀q∈rootResidueGuards k j s e,q.expression.syntaxSize ≤ M := by
  intro q hq
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
  exact he _

lemma nodeResidueGuards_size (k j : ℕ) (s v w : ℤ) (e : Expressions (ι:=ι) k (j+1))
    (M : ℕ) (he : ∀i,(e i).syntaxSize ≤ M) :
    ∀q∈nodeResidueGuards k j e s v w,q.expression.syntaxSize ≤ expressionStepFactor k j*(M+1) := by
  have hp := pivotExpression_syntaxSize k j e s v w M he
  have hc (b : Bool) : (copiedExpression k j b e).syntaxSize ≤ expressionStepFactor k j*(M+1) := by
    have hh := finiteProductExpression_syntaxSize
      (fun i : {i:(schedule k j).Slot // (schedule k j).IsCopied j i}=>e (.inl (i,b))) M (fun _=>he _)
    change (copiedExpression k j b e).syntaxSize ≤ _ at hh
    unfold expressionStepFactor
    nlinarith
  intro q hq
  simp only [nodeResidueGuards,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl
  · exact hp
  · exact hc true
  · exact hc false

theorem historyResidueGuards_size (k j : ℕ) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) (M : ℕ) (he : ∀i,(e i).syntaxSize ≤ M) :
    ∀q∈historyResidueGuards k j s e t,
      q.expression.syntaxSize ≤ recursiveSizeFactor k j*(M+1) := by
  induction j generalizing s M with
  | zero =>
    intro q hq
    simpa only [recursiveSizeFactor,one_mul] using
      (rootResidueGuards_size k 0 s e M he q hq).trans (Nat.le_succ M)
  | succ j ih =>
    let C := recursiveSizeFactor k j
    let A := expressionStepFactor k j
    let P := pivotExpression k j e s t.1.1 t.1.2
    have hc (b : Bool) : ∀i,(childExpressions k j b e P i).syntaxSize ≤ A*(M+1) :=
      childExpressions_syntaxSize k j b e s _ _ M he
    have hl := ih t.1.1 (childExpressions k j true e P) t.2.1 (A*(M+1)) (hc true)
    have hr := ih t.1.2 (childExpressions k j false e P) t.2.2 (A*(M+1)) (hc false)
    have hscale : C*(A*(M+1)+1) ≤ ((C+1)*(A+1))*(M+1) := by nlinarith
    have hp : A*(M+1) ≤ ((C+1)*(A+1))*(M+1) :=
      Nat.mul_le_mul_right (M+1) (by nlinarith)
    have hm : M ≤ recursiveSizeFactor k (j+1)*(M+1) := by
      have hpos : 1 ≤ recursiveSizeFactor k (j+1) := recursiveSizeFactor_pos k (j+1)
      nlinarith
    intro q hq
    change q∈rootResidueGuards _ _ _ _ ++ (_ ++ (_ ++ _)) at hq
    rcases List.mem_append.mp hq with hq|hq
    · exact (rootResidueGuards_size k (j+1) s e M he q hq).trans hm
    · rcases List.mem_append.mp hq with hq|hq
      · exact (nodeResidueGuards_size k j s _ _ e M he q hq).trans hp
      · rcases List.mem_append.mp hq with hq|hq
        · exact (hl q hq).trans hscale
        · exact (hr q hq).trans hscale

lemma natAbs_real (s : ℤ) : (s.natAbs:ℝ)=|(s:ℝ)| := by
  simpa only [Int.cast_natCast,Int.cast_abs] using
    congrArg (fun z : ℤ=>(z:ℝ)) (Int.natCast_natAbs s)

lemma rootResidueGuards_fixed (k j : ℕ) (s : ℤ) (e : Expressions (ι:=ι) k j)
    {B : ℝ} (he : ∀i,(e i).FixedBound B) (hs : |(s:ℝ)| ≤ B) :
    ∀q∈rootResidueGuards k j s e,q.expression.FixedBound B ∧ (q.frequency:ℝ) ≤ B := by
  intro q hq
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
  exact ⟨he _,(natAbs_real s).trans_le hs⟩

lemma nodeResidueGuards_fixed (k j : ℕ) (s v w : ℤ) (e : Expressions (ι:=ι) k (j+1))
    {B : ℝ} (hB : 1 ≤ B) (he : ∀i,(e i).FixedBound B)
    (hs : |(s:ℝ)| ≤ B) (hv : |(v:ℝ)| ≤ B) (hw : |(w:ℝ)| ≤ B) :
    ∀q∈nodeResidueGuards k j e s v w,q.expression.FixedBound B ∧ (q.frequency:ℝ) ≤ B := by
  have hp := pivotExpression_fixedBound k j e hB he s v w hs hv hw
  have hc (b : Bool) : (copiedExpression k j b e).FixedBound B :=
    finiteProductExpression_fixedBound _ hB (fun _=>he _)
  intro q hq
  simp only [nodeResidueGuards,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl
  · exact ⟨hp,(natAbs_real w).trans_le hw⟩
  · exact ⟨hc true,(natAbs_real s).trans_le hs⟩
  · exact ⟨hc false,(natAbs_real s).trans_le hs⟩

theorem historyResidueGuards_fixed (k j : ℕ) (S : List Bool → Finset ℤ)
    {B : ℝ} (hB : 1 ≤ B) (hS : ∀p s,s∈S p → |(s:ℝ)| ≤ B)
    (p : List Bool) (s : ℤ) (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j)
    (he : ∀i,(e i).FixedBound B) (ht : RangeSupported S j p s t) :
    ∀q∈historyResidueGuards k j s e t,q.expression.FixedBound B ∧ (q.frequency:ℝ) ≤ B := by
  induction j generalizing p s with
  | zero => exact rootResidueGuards_fixed k 0 s e he (hS p s ht)
  | succ j ih =>
    let P := pivotExpression k j e s t.1.1 t.1.2
    have hs := hS p s ht.1
    have hv := hS _ _ (rangeSupported_root_mem S j _ _ _ ht.2.1)
    have hw := hS _ _ (rangeSupported_root_mem S j _ _ _ ht.2.2)
    have hP : P.FixedBound B := pivotExpression_fixedBound k j e hB he s _ _ hs hv hw
    have hc (b : Bool) : ∀i,(childExpressions k j b e P i).FixedBound B :=
      childExpressions_preserves k j b e P (fun q=>q.FixedBound B) he hP
    have hl := ih (false::p) t.1.1 (childExpressions k j true e P) t.2.1 (hc true) ht.2.1
    have hr := ih (true::p) t.1.2 (childExpressions k j false e P) t.2.2 (hc false) ht.2.2
    intro q hq
    change q∈rootResidueGuards _ _ _ _ ++ (_ ++ (_ ++ _)) at hq
    rcases List.mem_append.mp hq with hq|hq
    · exact rootResidueGuards_fixed k (j+1) s e he hs q hq
    · rcases List.mem_append.mp hq with hq|hq
      · exact nodeResidueGuards_fixed k j s _ _ e hB he hs hv hw q hq
      · rcases List.mem_append.mp hq with hq|hq
        · exact hl q hq
        · exact hr q hq

end Ostmann.Characters.TemplateOneSidedBudget

end

end OAI
