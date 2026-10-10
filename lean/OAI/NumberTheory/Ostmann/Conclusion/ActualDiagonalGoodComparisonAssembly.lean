import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedStatement
import OAI.NumberTheory.Ostmann.Conclusion.ActualComparisonSourceDefs
import OAI.NumberTheory.Ostmann.Conclusion.ActualDiagonalGoodComparisonPoint
import OAI.NumberTheory.Ostmann.Conclusion.ActualDiagonalGoodComparisonPrincipal
import OAI.NumberTheory.Ostmann.Construction.SelectedDiagonalGoodNormalizerBasic
import OAI.NumberTheory.Ostmann.Construction.SelectedDiagonalSplit

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Conclusion
open Construction Arithmetic Filter
open HistoryBulkActualTotalReplacement

theorem actual_diagonal_good_comparison_of_residual (d : Decomposition)
    (hres : ∀ BD Bz H : ℝ, ∀ {k : ℕ}, 0 ≤ H → 2 ≤ k →
      CorrectedTotalEstimate d 200 BD Bz H k) :
    ∀ BD Bz : ℝ, 0 ≤ BD → 9 ≤ Bz → ∀ k : ℕ, 2 ≤ k →
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (P : Finset ℕ) (hP : ∀ p∈P,p.Prime) (hZ : 0<harmonicPrimeMass P)
        (E : Finset ℕ) (C : InitialSourceChoice d 200 BD Bz k L E),
        ActualComparisonSource C P hP hZ ε →
        ∀ j<k, ∀ e, InitialSourceChoice.diagonalGoodPermutation (2*(bulkSize k L/2)) k j e →
          ‖C.selectedDiagonalCovariance (harmonicPrimeSource P hP hZ)
            (bulkSize k L/2) C.scale j e‖ ≤
            Real.exp (-(selectedDiagonalGoodRate k+67*(2:ℝ)^k)*(bulkSize k L:ℝ)) :=
  fun BD Bz _hBD _hBz k hk =>
  let A : ℝ := selectedDiagonalGoodRate k+67*(2:ℝ)^k
  let hk0 : 0<k := lt_of_lt_of_le (Nat.zero_lt_succ 1) hk
  let hA : 0 ≤ A := add_nonneg (selectedDiagonalGoodRate_pos hk0).le
    (mul_nonneg (Nat.cast_nonneg 67) (pow_nonneg (Nat.cast_nonneg 2) k))
  let hH : 0 ≤ A+1 := add_nonneg hA zero_le_one
  (exists_correctedFinalAverage_budget (k:=k) d BD Bz (A+1) hk hH).elim
    (fun ε h => ⟨ε,h.1,
      ((h.2.and (hres BD Bz (A+1) (k:=k) hH hk)).and
        ((bulkSize_tendsto_atTop hk0).eventually (eventually_ge_atTop (1:ℝ)))).mono
      (fun L hL P hPrime hZ E C hs j hj e he =>
        let hp := hL.1.1 P hPrime hZ E C hs j hj
        let hr := hL.1.2 E C hs.block_lower hs.block_upper hs.center_lower hs.center_upper
          hs.bulk_bin hs.spectator_bin (harmonicPrimeSource P hPrime hZ) hs.spectator_band j hj
        diagonal_good_covariance_estimate hA hL.2 j
          (C.selectedDiagonalCovariance (harmonicPrimeSource P hPrime hZ)
            (bulkSize k L/2) C.scale j e)
          (correctedFinalAverage C (harmonicPrimeSource P hPrime hZ) hj e hr.choose)
          (hr.choose_spec e).2 (hp.choose_spec e he))⟩)

end Ostmann.Conclusion

end

end OAI
