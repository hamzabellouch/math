import OAI.NumberTheory.Ostmann.Characters.HistoryFrequencyBudgetBasic
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationFrequencySupport

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template HistoryFrequencyLabels HistoryFrequencyBudget
attribute [local instance] Classical.propDecidable
variable {ι : Type*}

theorem expressionProduct_valid (l : List (Expr ι)) (h : ∀ e ∈ l, e.Valid) :
    (HistoryReconstruction.expressionProduct l).Valid := by
  induction l with
  | nil => trivial
  | cons e l ih => exact ⟨h e (by simp),ih (fun q hq => h q (by simp [hq]))⟩

theorem finiteProductExpression_valid {α : Type*} [Fintype α]
    (e : α → Expr ι) (he : ∀ i, (e i).Valid) : (finiteProductExpression e).Valid := by
  apply expressionProduct_valid
  intro q hq
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
  exact he _

theorem pivotExpression_valid (k j : ℕ) (e : Expressions (ι:=ι) k (j+1))
    (s v w : ℤ) (hs : s ≠ 0) (he : ∀ i, (e i).Valid) :
    (pivotExpression k j e s v w).Valid := by
  have hc (b : Bool) : (copiedExpression k j b e).Valid :=
    finiteProductExpression_valid _ (fun _ => he _)
  exact ⟨⟨⟨trivial,hc false⟩,⟨trivial,hc true⟩⟩,hs⟩

theorem nodeResidueGuards_valid (k j : ℕ) (e : Expressions (ι:=ι) k (j+1))
    (s v w : ℤ) (hs : s ≠ 0) (hw : w ≠ 0) (he : ∀ i, (e i).Valid) :
    ∀ q ∈ nodeResidueGuards k j e s v w, q.Valid := by
  have hc (b : Bool) : (copiedExpression k j b e).Valid :=
    finiteProductExpression_valid _ (fun _ => he _)
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact ⟨pivotExpression_valid k j e s v w hs he,Int.natAbs_pos.mpr hw⟩
  · rcases List.mem_cons.mp hq with rfl | hq
    · exact ⟨hc _,Int.natAbs_pos.mpr hs⟩
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨hc _,Int.natAbs_pos.mpr hs⟩
      · exact False.elim (List.not_mem_nil hq)

theorem historyResidueGuards_valid (k : ℕ) (V : ℕ → ℤ) (j : ℕ)
    (s : ℤ) (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j)
    (he : ∀ i, (e i).Valid) (hf : historyFrequencyBounds V j s t) :
    ∀ q ∈ historyResidueGuards k j s e t, q.Valid := by
  induction j generalizing s with
  | zero => exact rootResidueGuards_valid k 0 s e hf he
  | succ j ih =>
    let P := pivotExpression k j e s t.1.1 t.1.2
    have hp := pivotExpression_valid k j e s t.1.1 t.1.2 hf.1 he
    have hl := ih t.1.1 (childExpressions k j true e P) t.2.1
      (childExpressions_preserves k j true e P Expr.Valid he hp) hf.2.2.2.1
    have hr := ih t.1.2 (childExpressions k j false e P) t.2.2
      (childExpressions_preserves k j false e P Expr.Valid he hp) hf.2.2.2.2
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact rootResidueGuards_valid k (j+1) s e hf.1 he q hq
    · rcases List.mem_append.mp hq with hq | hq
      · exact nodeResidueGuards_valid k j e s _ _ hf.1
          (historyFrequencyBounds_root V j _ _ hf.2.2.2.2) he q hq
      · rcases List.mem_append.mp hq with hq | hq
        · exact hl q hq
        · exact hr q hq

theorem actual_historyFrequencyBounds (a m : ℝ) (J j : ℕ) (p : List Bool)
    (hp : j+p.length=J) (s : ℤ) (t : HistoryReconstruction.Tree j)
    (h : RangeSupported (ranges a m J) j p s t) :
    historyFrequencyBounds (fun i => (bound a m i:ℤ)) j s t := by
  induction j generalizing p s with
  | zero => exact ((mem_signedRange _ _).mp h).1
  | succ j ih =>
    have hl := ih (false::p) (by simp only [List.length_cons]; omega) t.1.1 t.2.1 h.2.1
    have hr := ih (true::p) (by simp only [List.length_cons]; omega) t.1.2 t.2.2 h.2.2
    have hroot := ((mem_signedRange _ _).mp h.1).1
    have rootmem (j : ℕ) (p : List Bool) (s : ℤ) (t : HistoryReconstruction.Tree j)
        (hs : RangeSupported (ranges a m J) j p s t) : s ∈ ranges a m J p := by
      cases j with
      | zero => exact hs
      | succ j => exact hs.1
    have hv := ((mem_signedRange _ _).mp (rootmem j (false::p) _ _ h.2.1)).2
    have hw := ((mem_signedRange _ _).mp (rootmem j (true::p) _ _ h.2.2)).2
    have hidx : J-(false::p).length=j := by simp only [List.length_cons]; omega
    have hidx' : J-(true::p).length=j := by simp only [List.length_cons]; omega
    rw [hidx] at hv
    rw [hidx'] at hw
    refine ⟨hroot,?_,?_,hl,hr⟩
    · change |t.1.1| ≤ (bound a m j:ℤ)
      simpa only [Int.natCast_natAbs] using (Int.ofNat_le.mpr hv)
    · change |t.1.2| ≤ (bound a m j:ℤ)
      simpa only [Int.natCast_natAbs] using (Int.ofNat_le.mpr hw)

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
