import OAI.NumberTheory.Ostmann.Construction.CounterpartNormalizationBoundTemplates

namespace OAI

noncomputable section
namespace Ostmann.Construction.CounterpartNormalizationBound
open Arithmetic.HistoryProductWindows

lemma list_product_le_exp_sum (T : List SourceSlot) (f g : SourceSlot → ℝ)
    (hf : ∀q∈T,0≤f q) (hg : ∀q∈T,f q≤Real.exp (g q)) :
    (T.map f).prod≤Real.exp (sourceSum g T) := by
  induction T with
  | nil => simp [sourceSum]
  | cons q T ih =>
    rw [List.map_cons,List.prod_cons]
    have hb := mul_le_mul (hg q (by simp))
      (ih (fun r hr => hf r (by simp [hr])) (fun r hr => hg r (by simp [hr])))
      (List.prod_nonneg (fun r hr => by obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hr; exact hf x (by simp [hx])))
      (Real.exp_pos _).le
    simpa only [sourceSum,List.map_cons,List.sum_cons,Real.exp_add] using hb

theorem remaining_product_bound (m k l : ℕ) (f : ℕ→ℝ) (A L : ℝ) (hL : 0≤L)
    (hf : ∀q∈Template.remainder (l+1) (Template.current (Template.initial m k) l),0≤f q.origin)
    (hbound : ∀q∈Template.remainder (l+1) (Template.current (Template.initial m k) l),
      f q.origin≤Real.exp (A*bulkCount q+L*fixedCount q)) :
    ((Template.remainder (l+1) (Template.current (Template.initial m k) l)).map
      (fun q => f q.origin)).prod≤
      Real.exp (A*((2:ℝ)^l*m)+L*((2:ℝ)^l*(6+4*(k:ℝ)))) := by
  have hh := list_product_le_exp_sum _ (fun q => f q.origin)
    (fun q => A*bulkCount q+L*fixedCount q) hf hbound
  have he (T : List SourceSlot) :
      sourceSum (fun q => A*bulkCount q+L*fixedCount q) T=
      A*sourceSum bulkCount T+L*sourceSum fixedCount T := by
    simp only [sourceSum,List.sum_map_add,List.sum_map_mul_left]
  rw [he,sourceSum_bulkCount_remaining] at hh
  apply hh.trans (Real.exp_le_exp.mpr _)
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (fixedCount_current_filter_le _ m k l) hL)

end Ostmann.Construction.CounterpartNormalizationBound

end

end OAI
