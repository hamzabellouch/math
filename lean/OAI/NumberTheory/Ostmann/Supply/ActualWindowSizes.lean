import OAI.NumberTheory.Ostmann.Supply.ActualCenteredBudget
import OAI.NumberTheory.Ostmann.Supply.SupplyRadiusBounds

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Supply
open Filter Ostmann.Preliminaries
open scoped BigOperators

theorem eventually_actualWindow_card_bound (d : Decomposition) :
    ∃ C:ℝ,0<C ∧ ∀ᶠL:ℝ in atTop,
      (upperWindow d.A ((supplyRadius L)^2)).Nonempty ∧
      (upperWindow d.B ((supplyRadius L)^2)).Nonempty ∧
      ((upperWindow d.A ((supplyRadius L)^2)).card:ℝ)≤
        1536*(supplyRadius L:ℝ)*Real.exp (C*Real.sqrt L) ∧
      ((upperWindow d.B ((supplyRadius L)^2)).card:ℝ)≤
        1536*(supplyRadius L:ℝ)*Real.exp (C*Real.sqrt L) := by
  obtain ⟨C,hC,hbudget⟩ := eventually_actual_centered_energy_budgets d
  refine ⟨C,hC,?_⟩
  filter_upwards [supplyRadius_tendsto.eventually hbudget,
    supplyRadius_tendsto.eventually (eventually_actualWindow_supports d),
    eventually_ge_atTop (1:ℝ)] with L hb hs hL
  have hR : 1≤ supplyRadius L := supplyRadius_pos L
  have ht : ∀t∈({1}:Finset ℕ),Squarefree t ∧ t≤ supplyRadius L := by
    intro t ht
    simp only [Finset.mem_singleton] at ht
    subst t
    exact ⟨squarefree_one,hR⟩
  have hcop : ∀t∈({1}:Finset ℕ),∑p∈t.primeFactors,(1:ℝ)/p≤1/16 := by
    intro t ht
    simp only [Finset.mem_singleton] at ht
    subst t
    norm_num
  obtain ⟨ha,hb⟩ := hb {1} ht hcop
  simp only [Finset.sum_singleton,centeredEnergy_one _ hs.1 _] at ha
  simp only [Finset.sum_singleton,centeredEnergy_one _ hs.2.1 _] at hb
  have hexp : Real.exp (C*Real.sqrt (Real.log (Real.log (supplyRadius L:ℝ))))≤
      Real.exp (C*Real.sqrt L) := Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (supplyRadius_loglog_le hL)) hC.le)
  have hApos : (0:ℝ)<(upperWindow d.A ((supplyRadius L)^2)).card :=
    Nat.cast_pos.mpr hs.1.card_pos
  have hBpos : (0:ℝ)<(upperWindow d.B ((supplyRadius L)^2)).card :=
    Nat.cast_pos.mpr hs.2.1.card_pos
  refine ⟨hs.1,hs.2.1,?_,?_⟩
  · have h := (mul_le_mul_of_nonneg_right ha hApos.le).trans_eq (by
      field_simp
      : (1536*(supplyRadius L:ℝ)/(upperWindow d.A ((supplyRadius L)^2)).card*
        Real.exp (C*Real.sqrt (Real.log (Real.log (supplyRadius L:ℝ)))))*
          (upperWindow d.A ((supplyRadius L)^2)).card =
        1536*(supplyRadius L:ℝ)*Real.exp (C*Real.sqrt (Real.log (Real.log (supplyRadius L:ℝ)))))
    simp only [one_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
  · have h := (mul_le_mul_of_nonneg_right hb hBpos.le).trans_eq (by
      field_simp
      : (1536*(supplyRadius L:ℝ)/(upperWindow d.B ((supplyRadius L)^2)).card*
        Real.exp (C*Real.sqrt (Real.log (Real.log (supplyRadius L:ℝ)))))*
          (upperWindow d.B ((supplyRadius L)^2)).card =
        1536*(supplyRadius L:ℝ)*Real.exp (C*Real.sqrt (Real.log (Real.log (supplyRadius L:ℝ)))))
    simp only [one_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_left hexp (by positivity))

end Ostmann.Supply

end

end OAI
