import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceFrequencyFamilyOptions
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairedFrequencyAverage

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceFrequencyFamily
open Construction Conclusion HistoryPairedFrequencyAverage Filter
open scoped BigOperators

theorem reference_frequency_average_eventually {Bs BD Bz : ℝ}
    (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) {k : ℕ} (hk : 0 < k)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ L : ℝ in atTop, ∀ l ≤ k, ∀ K m : ℕ, 0 < m →
      ∀ (sources : SourceFamily) (seed : List SourceSlot) (outside : List ℕ),
      ∀ (x y : InternalSourceDraws sources seed l) (s t : ℤ),
      ∀ refs : ReferenceFamily sources seed (frequencyBound Bs BD Bz k L) outside l x y s t,
      (∑fg, optionValue refs (fun _ r => referenceUnitAverage K m r) fg) ≤
          Real.exp (2 * (2 : ℝ)^l * initialGap Bs k L + ρ * (bulkSize k L : ℝ)) ∧
      (∑fg, optionValue refs (fun _ r => referenceRingUnitAverage K m r) fg) ≤
          Real.exp (2 * (2 : ℝ)^l * initialGap Bs k L + ρ * (bulkSize k L : ℝ)) := by
  filter_upwards [supported_bulk_frequency_average_eventually hBs hBD hBz hk hρ,
    supported_ringUnit_frequency_average_eventually hBs hBD hBz hk hρ] with L hunit hring
  intro l hl K m hm sources seed outside x y s t refs
  have hi := supported_assignment_injective Bs BD Bz k L sources seed outside l x y s t refs
  have hu := hunit l hl K m hm (Present refs) (leftHistory refs) (rightHistory refs) outside
    (leftHistory_supported refs) (rightHistory_supported refs) hi
  have hr := hring l hl K m hm (Present refs) (leftHistory refs) (rightHistory refs) outside
    (leftHistory_supported refs) (rightHistory_supported refs) hi
  constructor
  · rw [sum_optionValue_eq_present]
    exact hu.1
  · rw [sum_optionValue_eq_present]
    exact hr

end Ostmann.Arithmetic.HistoryBulkReferenceFrequencyFamily

end

end OAI
