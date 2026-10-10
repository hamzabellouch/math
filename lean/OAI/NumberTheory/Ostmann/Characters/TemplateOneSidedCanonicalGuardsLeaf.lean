import OAI.NumberTheory.Ostmann.Characters.SourceTemplateLeafMask
import OAI.NumberTheory.Ostmann.Characters.TemplateLeafSymbolic
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCanonicalGuardsPivot

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template HigherBiasSource.SourceTemplate
attribute [local instance] Classical.propDecidable
variable {ι : Type*}

def binGuardList (e : Expr ι) (J : ℤ) : List (Guard ι) :=
  windowGuardList e (Real.exp J) (Real.exp ((J:ℝ)+1)) true

theorem binGuardList_holds (e : Expr ι) (J : ℤ) (a : ι → ℤ)
    (hp : 0 < (e.integerEval a : ℝ)) :
    guardsHold (binGuardList e J) a ↔ ⌊Real.log (e.integerEval a : ℝ)⌋ = J := by
  rw [binGuardList,windowGuardList_holds]
  simpa only [binGuards,windowGuards_holds] using binGuards_holds_iff e J a hp

def sourceRangeLeafGuards (k : ℕ) (J : ℤ) (X Δ W : ℝ)
    (e : Expressions (ι:=ι) k 0) : List (Guard ι) :=
  binGuardList (e (.word,true)) J ++
    (binGuardList (e (.word,false)) J ++
      windowGuardList (periodExpression k e) (X*Real.exp (Δ-W)) (X*Real.exp (Δ+W)) false)

theorem sourceRangeLeafGuards_holds (k : ℕ) (J s : ℤ) (X Δ W : ℝ)
    (e : Expressions (ι:=ι) k 0) (a : ι → ℤ)
    (hp : ∀b : Bool,0 < evalExpressions a e (.word,b)) :
    guardsHold (sourceRangeLeafGuards k J X Δ W e) a ↔
      sourceRangeLeafMask k J X Δ W s (evalExpressions a e) := by
  have hpT : 0 < ((e (.word,true)).integerEval a : ℝ) := by exact_mod_cast hp true
  have hpF : 0 < ((e (.word,false)).integerEval a : ℝ) := by exact_mod_cast hp false
  rw [sourceRangeLeafGuards,guardsHold_append,guardsHold_append,
    binGuardList_holds _ _ _ hpT,binGuardList_holds _ _ _ hpF,windowGuardList_holds]
  simp only [Bool.false_eq_true,ite_false,periodExpression_eval,
    sourceRangeLeafMask,sourceLeafMask,evalExpressions]
  tauto

def canonicalSourceLeafGuardData (k : ℕ) (J : ℤ) (X Δ W : ℝ) :
    (j : ℕ) → ℤ → List (Guard (schedule k j).Slot)
  | 0,_ => sourceRangeLeafGuards k J X Δ W (fun i => .atom i)
  | _+1,_ => []

theorem canonicalSourceLeafGuardData_zero (k : ℕ) (J s : ℤ) (X Δ W : ℝ)
    (x : State k 0) (hp : ∀b : Bool,0 < x (.word,b)) :
    canonicalMask k (canonicalSourceLeafGuardData k J X Δ W) 0 s x ↔
      canonicalHistoryMask k (sourceRangeLeafMask k J X Δ W) 0 s x := by
  exact sourceRangeLeafGuards_holds k J s X Δ W (fun i => .atom i) x hp

theorem canonicalSourceLeafGuardData_succ (k j : ℕ) (J s : ℤ) (X Δ W : ℝ)
    (x : State k (j+1)) :
    canonicalMask k (canonicalSourceLeafGuardData k J X Δ W) (j+1) s x ↔
      canonicalHistoryMask k (sourceRangeLeafMask k J X Δ W) (j+1) s x := by
  simp [canonicalMask,canonicalSourceLeafGuardData,canonicalHistoryMask,guardsHold]

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
