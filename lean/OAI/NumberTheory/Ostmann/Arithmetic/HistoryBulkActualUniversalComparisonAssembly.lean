import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementPlainStatement
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalComparisonBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalComparisonPrincipalStatement
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalComparisonStatement
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedComparisonAbsorption

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualUniversalComparison
open Construction Conclusion Filter HistoryBulkActualTotalReplacement

theorem universal_comparisons_of_estimates (d : Decomposition) (BD Bz : ℝ)
    (k : ℕ) (hk : 2≤k)
    (hprincipal : ActualPlainFinalEstimate d BD Bz k)
    (hresidual : PlainTotalEstimate d 200 BD Bz 0 k) :
    ActualUniversalEstimates d BD Bz k := by
  have hkpos : 0<k := by omega
  filter_upwards [hprincipal,
    hresidual,
    HistorySelectedComparisonAbsorption.selected_universal_absorption_eventually
      200 (by norm_num) hkpos] with L hmain herr habsorb
  intro P hP hZ E C hsource
  obtain ⟨hactual,hfinal⟩ := hmain P hP hZ E C hsource
  obtain ⟨hactual',herror⟩ := herr E C hsource.block_lower hsource.block_upper
    hsource.center_lower hsource.center_upper hsource.bulk_bin hsource.spectator_bin
    (harmonicPrimeSource P hP hZ) (fun p=>hsource.band p.val p.property)
  intro l hl
  obtain ⟨hV,hfinal⟩ := hfinal l hl
  obtain ⟨hV',herror⟩ := herror l hl
  have horiginal (mixed : Bool) :
      ‖plainOriginalAverage C (harmonicPrimeSource P hP hZ) (l:=l) (Equiv.refl _) mixed‖ ≤
        Real.exp ((2:ℝ)^l*(initialGap 200 k L+17*(bulkSize k L:ℝ))) := by
    have he := (herror (Equiv.refl _) mixed).2
    have he' : ‖plainOriginalAverage C (harmonicPrimeSource P hP hZ) (l:=l) (Equiv.refl _) mixed -
        plainFinalAverage C (harmonicPrimeSource P hP hZ) hactual hl (Equiv.refl _) mixed hV‖ ≤ 1 := by
      simpa only [zero_mul,neg_zero,Real.exp_zero] using he
    calc
      _ ≤ ‖plainOriginalAverage C (harmonicPrimeSource P hP hZ) (l:=l) (Equiv.refl _) mixed -
            plainFinalAverage C (harmonicPrimeSource P hP hZ) hactual hl (Equiv.refl _) mixed hV‖ +
          ‖plainFinalAverage C (harmonicPrimeSource P hP hZ) hactual hl (Equiv.refl _) mixed hV‖ :=
        by simpa only [sub_add_cancel] using
          (norm_add_le (plainOriginalAverage C (harmonicPrimeSource P hP hZ) (l:=l) (Equiv.refl _) mixed -
            plainFinalAverage C (harmonicPrimeSource P hP hZ) hactual hl (Equiv.refl _) mixed hV)
            (plainFinalAverage C (harmonicPrimeSource P hP hZ) hactual hl (Equiv.refl _) mixed hV))
      _ ≤ 1+Real.exp ((2:ℝ)^l*(initialGap 200 k L+16*(bulkSize k L:ℝ))) :=
        add_le_add he' (hfinal mixed)
      _ ≤ _ := by simpa only [add_comm] using habsorb l 1 le_rfl
  exact ⟨(singleEnergy_le_norm_plainOriginal C _).trans (horiginal true),
    fun σ τ=>(covariance_le_norm_plainOriginal C _ σ τ).trans (horiginal false)⟩

end Ostmann.Arithmetic.HistoryBulkActualUniversalComparison

end

end OAI
