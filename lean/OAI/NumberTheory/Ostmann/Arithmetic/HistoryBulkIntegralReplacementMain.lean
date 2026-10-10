import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIntegralReplacement

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkIntegralReplacement
open Construction Conclusion HistoryBulkPriorGrid HistoryPrincipalIntegralAverage
open HistoryPrincipalIntegralFinite PrimeCellFreezing ScaleBudget Filter
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem primeIntegral_bulkMain (L : ℝ) (E : Finset ℕ) {M : ℕ} [NeZero M]
    (F : (ι→(ZMod M)ˣ)→ℂ) (lo hi Z : κ→ℝ)
    (f : (κ→ℝ)→(ι→ℝ)→ℂ) :
    primeIntegral lo hi Z (fun y=>bulkMain L E F (f y)) =
      primeIntegral lo hi Z (fun y=>primeIntegral (fun _ : ι=>bulkLogLower L)
        (fun _=>bulkLogUpper L) (fun _=>bulkNormalizer L E) (f y))*
          ResidueHaar.average F := by
  simp only [bulkMain,mul_comm _ (ResidueHaar.average F)]
  rw [primeIntegral_const_mul]

theorem mixedIntegral_bulkMain (L : ℝ) (E : Finset ℕ) {M : ℕ} [NeZero M]
    (F : (ι→(ZMod M)ˣ)→ℂ) (loI hiI G : ℝ) (φ : ℝ→ℝ) (lo hi Z : κ→ℝ)
    (f : (Option κ→ℝ)→(ι→ℝ)→ℂ) :
    mixedIntegral loI hiI G φ lo hi Z (fun y=>bulkMain L E F (f y)) =
      mixedIntegral loI hiI G φ lo hi Z (fun y=>primeIntegral (fun _ : ι=>bulkLogLower L)
        (fun _=>bulkLogUpper L) (fun _=>bulkNormalizer L E) (f y))*
          ResidueHaar.average F := by
  simp only [bulkMain,mul_comm _ (ResidueHaar.average F)]
  rw [mixedIntegral_const_mul]

theorem norm_le_main_and_error {S I H : ℂ} {A B ε : ℝ}
    (herr : ‖S-I*H‖≤ε) (hI : ‖I‖≤A) (hH : ‖H‖≤B) :
    ‖S‖≤A*B+ε := by
  have hmain : ‖I*H‖≤A*B := by
    rw [norm_mul]
    exact mul_le_mul hI hH (norm_nonneg _) ((norm_nonneg _).trans hI)
  calc
    ‖S‖ ≤ ‖I*H‖+‖S-I*H‖ := by
      simpa only [add_sub_cancel] using norm_add_le (I*H) (S-I*H)
    _ ≤ A*B+ε := add_le_add hmain herr

end Ostmann.Arithmetic.HistoryBulkIntegralReplacement

end

end OAI
