import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCanonicalGuardsSize

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template TemplateOneSidedBudget HigherBiasSource.SourceTemplate
attribute [local instance] Classical.propDecidable
variable {ι : Type*}

def canonicalSourceGuardListSplitWidth (k : ℕ) (B V : ℕ → ℤ) (T : ℕ → ℝ)
    (J : ℤ) (X Δ Wp Wl : ℝ) (j : ℕ) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) : List (Guard ι) :=
  canonicalPivotCoreGuards k B V T Wp j s e t ++
    maskGuards k (canonicalSourceLeafGuardData k J X Δ Wl) j s e t

theorem canonicalSourceCoreWeightSplitWidth_eq_profiles (k : ℕ) (B V : ℕ → ℤ) (T : ℕ → ℝ)
    (J : ℤ) (X Δ Wp Wl : ℝ) (hX : 0 < X) (j : ℕ) (b : Bool) (s : ℤ)
    (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j) (a : ι → ℤ) :
    conjugateBy b (coreHistoryWeight k (fun l _ => B l) (fun l _ => V l)
      (canonicalHistoryExtra k (fun l => pivotWindow (T l) Wp))
      (canonicalHistoryMask k (sourceRangeLeafMask k J X Δ Wl))
      X Δ Wl j s (evalExpressions a e) t) =
      if frequencyArithmetic k V j s (evalExpressions a e) t ∧
        (guardsHold (canonicalSourceGuardListSplitWidth k B V T J X Δ Wp Wl j s e t) a ∧
          ∀i : Fin (2^j),(leafLowerGuard k X Δ Wl (indexedBottomExpressions k j b s e t i)).holds a)
      then ∏i : Fin (2^j),profileValue k X
        (evalBottom k a (indexedBottomExpressions k j b s e t i)) else 0 := by
  have hcore := canonicalPivotCoreSupport_iff k B V T Wp j s e t a
  unfold coreHistoryWeight
  by_cases hc : TransferCoreSupport k (fun l _ => B l) (fun l _ => V l)
      (canonicalHistoryExtra k (fun l => pivotWindow (T l) Wp)) j s (evalExpressions a e) t
  · rw [ite_eq_left hc,weight_eq_fixed_symbolic_profiles_indicator k _ X Δ Wl hX j b s e t a,
      canonicalSourceWeightSupport_iff k _ _ _ J X Δ Wl j s _ t hc,
      weightSupport_iff_fixed_leaf_guards k (canonicalSourceLeafGuardData k J X Δ Wl)
        X Δ Wl j b s e t a]
    have hh := hcore.mp hc
    simp only [canonicalSourceGuardListSplitWidth,guardsHold_append,hh.1,hh.2,true_and]
    split_ifs <;> rfl
  · rw [ite_eq_right hc]
    have hn : ¬(frequencyArithmetic k V j s (evalExpressions a e) t ∧
        (guardsHold (canonicalSourceGuardListSplitWidth k B V T J X Δ Wp Wl j s e t) a ∧
          ∀i : Fin (2^j),(leafLowerGuard k X Δ Wl (indexedBottomExpressions k j b s e t i)).holds a)) := by
      intro h
      exact hc (hcore.mpr ⟨h.1,(guardsHold_append _ _ _).mp h.2.1 |>.1⟩)
    rw [ite_eq_right hn]
    simp [conjugateBy]

theorem canonicalSourceGuardListSplitWidth_good (k : ℕ) (B V : ℕ → ℤ) (T : ℕ → ℝ)
    (J : ℤ) (X Δ Wp Wl : ℝ) (j : ℕ) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) (a : ι → ℤ)
    (he : ∀i,HistoryReconstruction.Good a (e i))
    (hf : frequencyArithmetic k V j s (evalExpressions a e) t) :
    ∀q ∈ canonicalSourceGuardListSplitWidth k B V T J X Δ Wp Wl j s e t,
      HistoryReconstruction.Good a q.expression := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · rcases List.mem_append.mp hq with hq | hq
    · exact historyGuards_good k B V (fun _ _ => [])
        (fun _ _ _ _ h => False.elim (List.not_mem_nil h)) j s e t a he hf q hq
    · exact pivotCellGuards_good k V T Wp j s e t a he hf q hq
  · exact maskGuards_good k V (canonicalSourceLeafGuardData k J X Δ Wl)
      (canonicalSourceLeafGuardData_good k J X Δ Wl) j s e t a he hf q hq

theorem canonicalSourceGuardListSplitWidth_length_le (k : ℕ) (B V : ℕ → ℤ) (T : ℕ → ℝ)
    (J : ℤ) (X Δ Wp Wl : ℝ) (j : ℕ) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) :
    (canonicalSourceGuardListSplitWidth k B V T J X Δ Wp Wl j s e t).length ≤ guardCountFactor k j+8*2^j := by
  have hh := historyGuards_length k j B V (fun _ _ => []) 0 (by simp) s e t
  have hp := pivotCellGuards_length k T Wp j s e t
  have hm := sourceLeafMaskGuards_length k J X Δ Wl j s e t
  simp only [Nat.zero_add,Nat.mul_one] at hh
  simp only [canonicalSourceGuardListSplitWidth,canonicalPivotCoreGuards,List.length_append,hm]
  rw [pow_succ] at hp
  omega

theorem canonicalSourceGuardListSplitWidth_size (k : ℕ) (B V : ℕ → ℤ) (T : ℕ → ℝ)
    (J : ℤ) (X Δ Wp Wl : ℝ) (j : ℕ) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) (M : ℕ) (he : ∀i,(e i).syntaxSize ≤ M) :
    ∀q ∈ canonicalSourceGuardListSplitWidth k B V T J X Δ Wp Wl j s e t,
      q.expression.syntaxSize ≤ recursiveSizeFactor k j *
        (2*(Fintype.card (schedule k 0).Slot+1)+1)*(M+1) := by
  let G := 2*(Fintype.card (schedule k 0).Slot+1)
  have hscale : recursiveSizeFactor k j*(M+1) ≤ recursiveSizeFactor k j*(G+1)*(M+1) := by
    exact Nat.mul_le_mul_right (M+1)
      (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (recursiveSizeFactor k j) (Nat.succ_le_succ (Nat.zero_le G)))
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · rcases List.mem_append.mp hq with hq | hq
    · have hh := historyGuards_size k j B V (fun _ _ => []) 0
        (fun _ _ _ h => False.elim (List.not_mem_nil h)) s e t M he q hq
      have hh' : q.expression.syntaxSize ≤ recursiveSizeFactor k j*(M+1) := by
        simpa only [Nat.zero_add,Nat.mul_one] using hh
      exact hh'.trans hscale
    · exact (pivotCellGuards_size k T Wp j s e t M he q hq).trans hscale
  · exact historyGuards_size k j B V (canonicalSourceLeafGuardData k J X Δ Wl) G
      (canonicalSourceLeafGuardData_size k J X Δ Wl) s e t M he q
      (maskGuards_mem_historyGuards k B V _ j s e t q hq)

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
