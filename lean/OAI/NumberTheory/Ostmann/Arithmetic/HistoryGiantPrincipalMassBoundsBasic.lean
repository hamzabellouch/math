import OAI.NumberTheory.Ostmann.Arithmetic.MixedCellGridReplacementBasic
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellSmoothReplacement
import OAI.NumberTheory.Ostmann.Section07SmoothPartitionBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantPrincipalMassBounds
open PrimeProgression PrimeCellReplacement LogCellPartition MixedCellIntegralFreezing
open MeasureTheory
open scoped BigOperators

theorem giant_harmonicIntegral_bounds (M : ℕ) (hM : 0 < M) {G : ℝ} (hG : 2 ≤ G) :
    0 ≤ harmonicIntegral M (G-1) (G+1) ∧ harmonicIntegral M (G-1) (G+1) ≤ 2 := by
  have hlo : 0 < G-1 := by linarith
  have hhi : 0 < G+1 := by linarith
  have ht : (0:ℝ) < M.totient := by exact_mod_cast Nat.totient_pos.mpr hM
  have hti : (M.totient:ℝ)⁻¹ ≤ 1 :=
    (inv_le_one₀ ht).mpr (by exact_mod_cast Nat.totient_pos.mpr hM)
  have hr0 : 0 < (G+1)/(G-1) := div_pos hhi hlo
  have hr1 : 1 ≤ (G+1)/(G-1) := (le_div_iff₀ hlo).mpr (by linarith)
  have hr3 : (G+1)/(G-1) ≤ 3 := (div_le_iff₀ hlo).mpr (by linarith)
  have hl0 : 0 ≤ Real.log ((G+1)/(G-1)) := Real.log_nonneg hr1
  have hl2 : Real.log ((G+1)/(G-1)) ≤ 2 :=
    (Real.log_le_sub_one_of_pos hr0).trans (by linarith)
  rw [harmonicIntegral,integral_inv_of_pos hlo hhi]
  exact ⟨mul_nonneg (inv_nonneg.mpr ht.le) hl0,
    (mul_le_mul_of_nonneg_right hti hl0).trans (by simpa using hl2)⟩

theorem giant_normalized_harmonic_bounds (M : ℕ) (hM : 0 < M)
    {G Z : ℝ} (hG : 2 ≤ G) (hZ : 0 < Z) :
    0 ≤ harmonicIntegral M (G-1) (G+1)/Z ∧
      harmonicIntegral M (G-1) (G+1)/Z ≤ 2*Z⁻¹ := by
  have hh := giant_harmonicIntegral_bounds M hM hG
  rw [div_eq_mul_inv]
  exact ⟨mul_nonneg hh.1 (inv_nonneg.mpr hZ.le),
    mul_le_mul_of_nonneg_right hh.2 (inv_nonneg.mpr hZ.le)⟩

theorem giant_integerDensityMass_bounds (M : ℕ) (hM : 0 < M) (G : ℝ) :
    0 ≤ IntegerCell.integerDensityMass M (G-1) (G+1) G smoothPartition ∧
      IntegerCell.integerDensityMass M (G-1) (G+1) G smoothPartition ≤ 2*Real.exp 1 := by
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  have hMi : (M:ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hMr).mpr (by exact_mod_cast hM)
  have hI : 0 ≤ ∫t in (G-1)..(G+1),Real.exp (t-G)*smoothPartition (t-G) := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro t ht
    exact mul_nonneg (Real.exp_nonneg _) (smoothPartition_nonneg _)
  have hbound := IntegerCell.log_density_mass_abs_le smoothPartition G (G-1) (G+1) 1
    (by linarith) le_rfl le_rfl smoothPartition_continuous
    (fun t _=>by rw [abs_of_nonneg (smoothPartition_nonneg _)]; exact smoothPartition_le_one _)
  have hle : (∫t in (G-1)..(G+1),Real.exp (t-G)*smoothPartition (t-G)) ≤ 2*Real.exp 1 := by
    simpa only [abs_of_nonneg hI,mul_one] using hbound
  rw [IntegerCell.integerDensityMass,div_eq_mul_inv]
  exact ⟨mul_nonneg hI (inv_nonneg.mpr hMr.le),
    (mul_le_mul_of_nonneg_right hle (inv_nonneg.mpr hMr.le)).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hMi (by positivity : 0 ≤ 2*Real.exp 1))⟩

end Ostmann.Arithmetic.HistoryGiantPrincipalMassBounds

end

end OAI
