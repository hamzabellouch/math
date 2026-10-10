import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairedFrequencyAverageActual
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairedFrequencyAverageSupported

namespace OAI

open Erdos970

noncomputable section
open Filter
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairedFrequencyAverage
open Construction Conclusion Characters FrequencyTreeSum PairedFrequencyActualBudget

theorem supported_bulk_frequency_average_eventually {Bs BD Bz : ℝ}
    (hBs : 0≤Bs) (hBD : 0≤BD) (hBz : 0≤Bz) {k : ℕ} (hk : 0<k)
    {ρ : ℝ} (hρ : 0<ρ) :
    ∀ᶠ L : ℝ in atTop, ∀ l≤k, ∀ K m : ℕ, 0 < m →
      ∀ ι : Type, ∀ [Fintype ι], ∀ h h' : ι → History l, ∀ outside : List ℕ,
      ∀ hs : ∀i,(h i).Supported (frequencyBound Bs BD Bz k L) outside,
      ∀ hs' : ∀i,(h' i).Supported (frequencyBound Bs BD Bz k L) outside,
      Function.Injective (fun i =>
        supportedHistoryAssignment Bs BD Bz k L (h i) (h' i) (hs i) (hs' i)) →
      (∑i,canonicalUnitBulkAverage K (h i) (h' i) (hs i) (hs' i) m) ≤
          Real.exp (2*(2:ℝ)^l*initialGap Bs k L+ρ*(bulkSize k L:ℝ)) ∧
      (∑i,canonicalMixedBulkAverage K (h i) (h' i) (hs i) (hs' i) m) ≤
          Real.exp (2*(2:ℝ)^l*initialGap Bs k L+ρ*(bulkSize k L:ℝ)) := by
  obtain ⟨ε,δ,hε,hδ,C,hC,D,hD,hcount,htotal,hscale⟩ :=
    exists_actual_paired_frequency_bound hBs hBD hBz hk hρ
  filter_upwards [hscale] with L hL
  intro l hl K m hm ι _ h h' outside hs hs' hinj
  have hb := sum_supported_bulk_average_le_total hcount Bs BD Bz k L K l m hm
    h h' outside hs hs' hinj
  exact ⟨hb.1.trans (hL l hl).2,hb.2.trans (hL l hl).2⟩

end Ostmann.Arithmetic.HistoryPairedFrequencyAverage

end

end OAI
