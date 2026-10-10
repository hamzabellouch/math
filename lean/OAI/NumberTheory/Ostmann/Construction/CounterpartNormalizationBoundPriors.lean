import OAI.NumberTheory.Ostmann.Construction.CounterpartNormalization
import OAI.NumberTheory.Ostmann.Construction.CounterpartNormalizationBoundTemplates
import OAI.NumberTheory.Ostmann.Construction.RepeatedPriorBoundsBasic
import OAI.NumberTheory.Ostmann.Construction.RepeatedPriorBoundsCenters

namespace OAI

open Erdos970

noncomputable section
open Filter
namespace Ostmann.Construction.CounterpartNormalizationBound
open Arithmetic.HistoryProductWindows

theorem cell_inverse_exp_bound_eventually :
    ∀ᶠ L : ℝ in atTop, ∀c:ℝ, favorableBlockWidth L/100≤c → c≤Real.exp L/2 →
      ∀E:Finset ℕ,E.card≤2 → (logCellMass c E)⁻¹≤Real.exp L := by
  obtain ⟨M,hM⟩ := eventually_atTop.mp logCell_normalization_eventually
  filter_upwards [(exp_mul_tendsto (by norm_num : (0:ℝ)<1/100)).eventually_ge_atTop
    (100*max M 1)] with L hL
  intro c hc hcu E hE
  have hMc : M≤c := by
    change 100*max M 1≤favorableBlockWidth L at hL
    linarith [le_max_left M 1]
  exact (hM c hMc E hE).2.2.trans (by linarith)

theorem sourceNormalization_nonneg {d : Decomposition} {Bs BD Bz : ℝ}
    {k : ℕ} {L : ℝ} {E : Finset ℕ} (C : InitialSourceChoice d Bs BD Bz k L E)
    (origin : ℕ) : 0≤C.sourceNormalization origin := by
  unfold InitialSourceChoice.sourceNormalization initialSourceValue
  split_ifs
  · exact (inv_pos.mpr C.bulkPositive).le
  · exact (inv_pos.mpr (C.cells.top_balanced _ E C.deleted_card).choose).le
  · exact (inv_pos.mpr (C.cells.comp_balanced _ _ E C.deleted_card).choose).le
  · exact (inv_pos.mpr C.bulkPositive).le

theorem sourceNormalization_exp_bound_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop, ∀(E:Finset ℕ)(C:InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      (logCellMass C.giantCenter ∅)⁻¹≤Real.exp L ∧
      ∀q:SourceSlot,q.origin<Conclusion.bulkSize k L+6+4*k →
      (q.role=.bulk ↔ q.origin<Conclusion.bulkSize k L) →
      C.sourceNormalization q.origin≤
        Real.exp ((Real.log 1000-Real.log L)*bulkCount q+L*fixedCount q) := by
  filter_upwards [cell_inverse_exp_bound_eventually,
    RepeatedPriorBounds.initial_cell_centers_eventually d Bs BD Bz hk,
    RepeatedPriorBounds.bulk_mass_lower_eventually,eventually_gt_atTop (0:ℝ)]
    with L hcell hcenters hbulk hL
  intro E C hG hGu hcl hcu hb hd
  have hc := hcenters E C hG hGu hcl hcu hb hd
  have ht (i : Fin 3) : (logCellMass (C.cells.top i) E)⁻¹≤Real.exp L :=
    hcell _ (hc.2 (.inl i)).1 (hc.2 (.inl i)).2 E C.deleted_card
  have ha (j : Fin k) (i : Fin 2) : (logCellMass (C.cells.comp j i) E)⁻¹≤Real.exp L :=
    hcell _ (hc.2 (.inr (j,i))).1 (hc.2 (.inr (j,i))).2 E C.deleted_card
  have hbulkInv : (harmonicPrimeMass (bulkPrimeBand L E))⁻¹≤1000/L := by
    have h := one_div_le_one_div_of_le (by positivity : 0<L/(1000:ℝ)) (hbulk E C.deleted_card)
    simpa only [one_div,inv_div] using h
  have hm : 2*(Conclusion.bulkSize k L/2)=Conclusion.bulkSize k L := by
    obtain ⟨n,hn⟩ := Conclusion.bulkSize_even k L
    omega
  refine ⟨hcell _ hc.1.1 hc.1.2 ∅ (by simp),?_⟩
  intro q hq hrole
  by_cases hqb : q.role=.bulk
  · have hqo : q.origin<2*(Conclusion.bulkSize k L/2) := by rw [hm]; exact hrole.mp hqb
    unfold InitialSourceChoice.sourceNormalization
    rw [initialSourceValue_bulk _ _ _ _ _ hqo]
    simpa only [bulkCount,fixedCount,hqb,ite_true,mul_one,mul_zero,add_zero,
      Real.exp_sub,Real.exp_log (by norm_num : (0:ℝ)<1000),Real.exp_log hL] using hbulkInv
  · have hqo : ¬q.origin<2*(Conclusion.bulkSize k L/2) := by rw [hm]; exact fun h => hqb (hrole.mpr h)
    simp only [bulkCount,fixedCount,hqb,ite_false,mul_zero,mul_one,zero_add]
    unfold InitialSourceChoice.sourceNormalization initialSourceValue
    rw [ite_eq_right hqo]
    split_ifs with ht' hj
    · exact ht _
    · exact ha _ _
    · omega

end Ostmann.Construction.CounterpartNormalizationBound

end

end OAI
