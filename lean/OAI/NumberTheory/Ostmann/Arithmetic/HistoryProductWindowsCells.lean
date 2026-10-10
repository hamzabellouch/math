import OAI.NumberTheory.Ostmann.Arithmetic.HistoryProductWindowsSlots
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryProductWindowsTemplates

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryProductWindows
open Construction Characters.RationalHistory HistorySymbolicSlots HistorySymbolicState
variable {ι : Type*}

theorem matches_metadata_fin_sum {T : List SourceSlot} {xs : List SmallSlot}
    (h : Template.Matches T xs) (F : SlotRole → ℕ → ℝ) :
    (∑i : Fin xs.length, F (xs.get i).role (xs.get i).origin) =
      sourceSum (fun q => F q.role q.origin) T := by
  have he := congrArg List.sum (List.ofFn_getElem_eq_map xs (fun q => F q.role q.origin))
  rw [List.sum_ofFn] at he
  exact he.trans (matches_metadata_sum h F)

theorem small_log_error {T : List SourceSlot} {xs : List SmallSlot}
    (hm : Template.Matches T xs) (f : Fin xs.length → Expr ι) (x : ι → ℝ)
    (center : ℕ → ℝ)
    (hc : ∀i, (xs.get i).role ≠ .bulk →
      |Real.log ((f i).realEval x) - center (xs.get i).origin| ≤ 1) :
    |(∑i, Real.log ((f i).realEval x)) - bulkLog xs f x -
      sourceSum (fixedCenter center) T| ≤ sourceSum fixedCount T := by
  have hmC := matches_metadata_fin_sum hm (fun r o => if r = .bulk then 0 else center o)
  have hmN := matches_metadata_fin_sum hm (fun r _ => if r = .bulk then (0:ℝ) else 1)
  change (∑i, if (xs.get i).role = .bulk then 0 else center (xs.get i).origin) =
    sourceSum (fixedCenter center) T at hmC
  change (∑i, if (xs.get i).role = .bulk then (0:ℝ) else 1) = sourceSum fixedCount T at hmN
  rw [←hmC,←hmN]
  unfold bulkLog slotSum
  rw [←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  dsimp only
  by_cases hi : (xs.get i).role = .bulk
  · simp only [hi,↓reduceIte, sub_self, abs_zero, le_refl]
  · simpa only [hi,↓reduceIte, sub_zero] using hc i hi

def realProduct (xs : List SmallSlot) (f : Fin xs.length → Expr ι) (x : ι → ℝ) : ℝ :=
  ∏i,(f i).realEval x

theorem realProduct_pos (xs : List SmallSlot) (f : Fin xs.length → Expr ι) (x : ι → ℝ)
    (hp : ∀i,0 < (f i).realEval x) : 0 < realProduct xs f x :=
  Finset.prod_pos (fun i _ => hp i)

theorem log_realProduct (xs : List SmallSlot) (f : Fin xs.length → Expr ι) (x : ι → ℝ)
    (hp : ∀i,0 < (f i).realEval x) :
    Real.log (realProduct xs f x) = ∑i, Real.log ((f i).realEval x) :=
  Real.log_prod (fun i _ => (hp i).ne')

def halfProduct (giant : Expr ι) (xs : List SmallSlot)
    (f : Fin xs.length → Expr ι) (x : ι → ℝ) : ℝ := giant.realEval x * realProduct xs f x

theorem halfProduct_log_bound {T : List SourceSlot} {xs : List SmallSlot}
    (hm : Template.Matches T xs) (giant : Expr ι) (f : Fin xs.length → Expr ι) (x : ι → ℝ)
    (center : ℕ → ℝ) (G B E : ℝ)
    (hp : 0 < giant.realEval x) (hf : ∀i,0 < (f i).realEval x)
    (hg : |Real.log (giant.realEval x) - G| ≤ 1)
    (hb : |bulkLog xs f x-B| ≤ E)
    (hc : ∀i, (xs.get i).role ≠ .bulk →
      |Real.log ((f i).realEval x) - center (xs.get i).origin| ≤ 1) :
    |Real.log (halfProduct giant xs f x) - (G+B+sourceSum (fixedCenter center) T)| ≤
      1+E+sourceSum fixedCount T := by
  have hs := small_log_error hm f x center hc
  rw [halfProduct, Real.log_mul hp.ne' (realProduct_pos xs f x hf).ne', log_realProduct xs f x hf]
  have hid : Real.log (giant.realEval x) + (∑i,Real.log ((f i).realEval x)) -
      (G+B+sourceSum (fixedCenter center) T) =
    (Real.log (giant.realEval x)-G)+(bulkLog xs f x-B)+
      ((∑i,Real.log ((f i).realEval x))-bulkLog xs f x-sourceSum (fixedCenter center) T) := by ring
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add hg hb)) hs)

theorem compensation_log_bound {T : List SourceSlot} {u : List SmallSlot} (j : ℕ)
    (hm : Template.Matches T u) (hu : ∀q∈u,q.role = .compensation j)
    (f : Fin u.length → Expr ι) (x : ι → ℝ) (center : ℕ → ℝ)
    (hp : ∀i,0 < (f i).realEval x)
    (hc : ∀i,|Real.log ((f i).realEval x) - center (u.get i).origin| ≤ 1) :
    |Real.log (realProduct u f x)-sourceSum (fixedCenter center) T| ≤ sourceSum fixedCount T := by
  have he := small_log_error hm f x center (fun i _ => hc i)
  rw [bulkLog_compensation j u hu,sub_zero] at he
  simpa only [log_realProduct u f x hp] using he

theorem realProduct_eq_product_realEval (xs : List SmallSlot)
    (f : Fin xs.length → Expr ι) (x : ι → ℝ) :
    realProduct xs f x = (HistorySymbolicStep.product (List.ofFn f)).realEval x := by
  simp only [realProduct, HistorySymbolicStep.product_realEval, List.map_ofFn,
    List.prod_ofFn, Function.comp_def]

end Ostmann.Arithmetic.HistoryProductWindows

end

end OAI
