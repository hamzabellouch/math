import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationNormalizationBudgetCounts

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryCompensationNormalizationBudget
open Construction CanonicalOccurrenceTransport CounterpartNormalizationBound HistoryProductWindows Filter

theorem paired_sourceNormalization_exp_bound_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop, ∀(E:Finset ℕ)(C:InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀l : ℕ, ∀i : Internal (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l ⊕
        Internal (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l,
      0≤C.sourceNormalization (pairedInternalOrigin
        (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l i) ∧
      C.sourceNormalization (pairedInternalOrigin
        (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l i)≤Real.exp L := by
  filter_upwards [sourceNormalization_exp_bound_eventually d Bs BD Bz hk] with L hL
  intro E C hG hGu hcl hcu hb hd l i
  have hnorm := (hL E C hG hGu hcl hcu hb hd).2
  have hm : 2*(Conclusion.bulkSize k L/2)=Conclusion.bulkSize k L := by
    obtain ⟨n,hn⟩ := Conclusion.bulkSize_even k L
    omega
  have hs (j : Internal (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l) :
      C.sourceNormalization (internalSource (Template.initial (2*(Conclusion.bulkSize k L/2)) k) j).origin ≤
        Real.exp L := by
    obtain ⟨ho,hr,hb⟩ := internalSource_origin_metadata (2*(Conclusion.bulkSize k L/2)) k l j
    have hh := hnorm (internalSource (Template.initial (2*(Conclusion.bulkSize k L/2)) k) j)
      (ho.trans_le (by omega))
      (hb.trans ⟨fun h => h.trans_le hm.le, fun h => h.trans_le hm.ge⟩)
    simpa only [bulkCount,fixedCount,hr,ite_false,mul_zero,mul_one,zero_add] using hh
  refine ⟨sourceNormalization_nonneg C _,?_⟩
  cases i with
  | inl i => exact hs i
  | inr i => exact hs i

end Ostmann.Arithmetic.HistoryCompensationNormalizationBudget

end

end OAI
