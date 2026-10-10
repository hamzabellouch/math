import OAI.NumberTheory.Ostmann.Characters.HistoryFrequencyBudgetBasic
import OAI.NumberTheory.Ostmann.Characters.SourceTemplatePhase

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Construction Preliminaries Template HistoryFrequencyLabels HistoryFrequencyBudget
open scoped BigOperators FourierTransform
attribute [local instance] Classical.propDecidable

theorem fourier_cutoff_of_period_le {X P : ℝ} (hX : 0 < X) (hP : 0 < P)
    (V : ℕ) (hPV : P ≤ 4*X*V) (s : ℤ) (hs : V < s.natAbs) :
    𝓕 SchwartzCutoff.psi (-(s:ℝ)*X/P) = 0 := by
  apply SchwartzCutoff.fourier_psi_zero_of_abs_ge
  rw [abs_div,abs_mul,abs_neg,abs_of_pos hX,abs_of_pos hP]
  have ha : (V:ℝ) ≤ |(s:ℝ)| := by
    rw [← Int.cast_abs,Int.abs_eq_natAbs]
    exact_mod_cast hs.le
  apply (le_div_iff₀ hP).mpr
  nlinarith [mul_le_mul_of_nonneg_right ha hX.le]

theorem leafWeight_eq_zero_of_outside {k : ℕ} (X Δ W : ℝ) (hX : 0 < X)
    (x : State k 0) (V : ℕ) (hPV : (period k 0 x:ℝ) ≤ 4*X*V)
    (s : ℤ) (hs : V < s.natAbs) : leafWeight k X Δ W s x = 0 := by
  unfold leafWeight
  split_ifs with h
  · rw [fourier_cutoff_of_period_le hX h.1 V hPV s hs,mul_zero]
  · rfl

theorem sum_supportedHistory_zero (S : List Bool → Finset ℤ)
    (f : ℤ → HistoryReconstruction.Tree 0 → ℂ) :
    (∑z:SupportedHistory S 0 [],f z.val.1 z.val.2) =
      ∑s∈S [],f s PUnit.unit := by
  rw [← sum_reindex S 0 [] f]
  change (∑s:{s:ℤ // s∈S []},f s.val PUnit.unit) = _
  exact Finset.sum_coe_sort (S []) (fun s => f s PUnit.unit)

theorem leaf_phase_tsum_eq_sum {k : ℕ} (X Δ W : ℝ) (hX : 0 < X)
    (x : State k 0) (V : ℕ) (hPV : (period k 0 x:ℝ) ≤ 4*X*V)
    (f : ℤ → ℂ) (hf : f 0 = 0) :
    (∑'s:ℤ,leafWeight k X Δ W s x*f s) =
      ∑s∈signedRange V,leafWeight k X Δ W s x*f s := by
  apply tsum_eq_sum
  intro s hs
  by_cases hz : s = 0
  · simp only [hz,hf,mul_zero]
  · have hn : V < s.natAbs := by
      by_contra hn
      exact hs ((mem_signedRange V s).mpr ⟨hz,by omega⟩)
    rw [leafWeight_eq_zero_of_outside X Δ W hX x V hPV s hn,zero_mul]

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
