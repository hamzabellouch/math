import OAI.NumberTheory.Ostmann.Characters.HistoryFrequencyBudgetBasic
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedBudgetModulus
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedBudgetStructure

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedBudget
open SymbolicHistory Template HistoryFrequencyLabels HistoryFrequencyBudget
attribute [local instance] Classical.propDecidable
variable {ι : Type*}

lemma rangeSupported_root_mem (S : List Bool → Finset ℤ) (j : ℕ) (p : List Bool)
    (s : ℤ) (t : HistoryReconstruction.Tree j) (h : RangeSupported S j p s t) : s ∈ S p := by
  cases j with
  | zero => exact h
  | succ j => exact h.1

theorem pivotExpression_fixedBound (k j : ℕ) (e : Expressions (ι:=ι) k (j+1))
    {B : ℝ} (hB : 1 ≤ B) (he : ∀i,(e i).FixedBound B) (s v w : ℤ)
    (hs : |(s:ℝ)| ≤ B) (hv : |(v:ℝ)| ≤ B) (hw : |(w:ℝ)| ≤ B) :
    (pivotExpression k j e s v w).FixedBound B := by
  have hc (b : Bool) : (copiedExpression k j b e).FixedBound B :=
    finiteProductExpression_fixedBound _ hB (fun _=>he _)
  exact ⟨⟨⟨hv,hc false⟩,⟨hw,hc true⟩⟩,hs⟩

theorem recursiveExpressions_fixedBound (k j : ℕ) (S : List Bool → Finset ℤ)
    {B : ℝ} (hB : 1 ≤ B) (hS : ∀p s,s∈S p → |(s:ℝ)| ≤ B)
    (p : List Bool) (b : Bool) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) (he : ∀i,(e i).FixedBound B)
    (ht : RangeSupported S j p s t) :
    (∀q∈pivotExpressions k j s e t,q.FixedBound B) ∧
    (∀z∈bottomExpressions k j b s e t,∀i,(z.2.2 i).FixedBound B) := by
  induction j generalizing p b s with
  | zero =>
    constructor
    · simp only [pivotExpressions,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
    · intro z hz i
      have hz' : z=(b,s,e) := List.mem_singleton.mp hz
      subst z
      exact he i
  | succ j ih =>
    let P := pivotExpression k j e s t.1.1 t.1.2
    have hP : P.FixedBound B := pivotExpression_fixedBound k j e hB he s _ _
      (hS p s ht.1)
      (hS _ _ (rangeSupported_root_mem S j _ _ _ ht.2.1))
      (hS _ _ (rangeSupported_root_mem S j _ _ _ ht.2.2))
    have hc (v : Bool) : ∀i,(childExpressions k j v e P i).FixedBound B :=
      childExpressions_preserves k j v e P (fun q=>q.FixedBound B) he hP
    have hl := ih (false::p) b t.1.1 (childExpressions k j true e P) t.2.1 (hc true) ht.2.1
    have hr := ih (true::p) (!b) t.1.2 (childExpressions k j false e P) t.2.2 (hc false) ht.2.2
    constructor
    · intro q hq
      change q∈P::(_++_) at hq
      rcases List.mem_cons.mp hq with hq|hq
      · subst q;exact hP
      · rcases List.mem_append.mp hq with hq|hq
        · exact hl.1 q hq
        · exact hr.1 q hq
    · intro z hz i
      change z∈(_++_) at hz
      rcases List.mem_append.mp hz with hz|hz
      · exact hl.2 z hz i
      · exact hr.2 z hz i

theorem obstructionExpressions_fixedBound (k j : ℕ) (S : List Bool → Finset ℤ)
    {B : ℝ} (hB : 1 ≤ B) (hS : ∀p s,s∈S p → |(s:ℝ)| ≤ B)
    (p : List Bool) (b : Bool) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) (he : ∀i,(e i).FixedBound B)
    (ht : RangeSupported S j p s t) :
    ∀q∈obstructionExpressions k j b s e t,q.FixedBound B := by
  obtain ⟨hp,hb⟩ := recursiveExpressions_fixedBound k j S hB hS p b s e t he ht
  intro q hq
  rcases List.mem_append.mp hq with hq|hq
  · exact hp q hq
  · obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hq
    exact finiteProductExpression_fixedBound _ hB (hb z hz)

theorem actual_frequency_abs_le_exp {a m : ℝ} (ha : 0 ≤ a) (hm : 1 ≤ m)
    (j : ℕ) (p : List Bool) (s : ℤ) (hs : s∈ranges a m j p) :
    |(s:ℝ)| ≤ Real.exp (linearEnvelope a j*m) := by
  have hn := (mem_signedRange _ _).mp hs |>.2
  have hc : (s.natAbs:ℝ) ≤ (bound a m (j-p.length):ℝ) := by exact_mod_cast hn
  have hh := hc.trans ((bound_le_exp _ _ _).trans
    (Real.exp_le_exp.mpr (exponent_le_linear ha hm (Nat.sub_le _ _))))
  have hcast : (s.natAbs:ℝ)=|(s:ℝ)| := by
    simpa only [Int.cast_natCast,Int.cast_abs] using
      congrArg (fun z : ℤ=>(z:ℝ)) (Int.natCast_natAbs s)
  rwa [hcast] at hh

theorem sampled_obstructions_fixedLogBound {a m : ℝ} (ha : 0 ≤ a) (hm : 1 ≤ m)
    (k j : ℕ) (width : Role → ℕ) (b : Bool) (s : ℤ)
    (t : HistoryReconstruction.Tree j) (ht : RangeSupported (ranges a m j) j [] s t) :
    ∀q∈obstructionExpressions k j b s (sampledExpressions k j width) t,
      q.FixedLogBound (linearEnvelope a j*m) := by
  have hB : 1 ≤ Real.exp (linearEnvelope a j*m) := Real.one_le_exp_iff.mpr
    (mul_nonneg (linearEnvelope_pos ha j).le (by linarith))
  exact obstructionExpressions_fixedBound k j (ranges a m j) hB
    (actual_frequency_abs_le_exp ha hm j) [] b s _ t
    (sampledExpressions_fixedBound k j width hB) ht

end Ostmann.Characters.TemplateOneSidedBudget

end

end OAI
