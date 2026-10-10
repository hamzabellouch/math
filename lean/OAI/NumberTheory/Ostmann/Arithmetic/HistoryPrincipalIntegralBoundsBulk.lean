import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPriorGridMass
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPrincipalIntegralBoundsBasic
import OAI.NumberTheory.Ostmann.Construction.RepeatedPriorBoundsBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryPrincipalIntegralBounds
open MeasureTheory Filter Construction PrimeCellFreezing HistoryPrincipalIntegralAverage HistoryBulkPriorGrid
open scoped BigOperators

theorem bulk_harmonic_integral (L : ℝ) :
    (∫ t in bulkLogLower L..bulkLogUpper L, (t : ℝ)⁻¹) = L/500 := by
  unfold bulkLogLower bulkLogUpper
  rw [integral_inv_of_pos (Real.exp_pos _) (Real.exp_pos _)]
  rw [Real.log_div (Real.exp_ne_zero _) (Real.exp_ne_zero _)]
  simp only [Real.log_exp]
  ring

theorem norm_bulk_primeIntegral_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L A : ℝ} (hL : 0 < L) (hA : 0 ≤ A) (E : Finset ℕ)
    (hZ : L/1000 ≤ bulkNormalizer L E) (f : (ι → ℝ) → ℂ)
    (hf : ∀ t ∈ logRectangle (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L),
      ‖f (fun i => Real.exp (t i))‖ ≤ A) :
    ‖primeIntegral (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L)
      (fun _ => bulkNormalizer L E) f‖ ≤ 2^Fintype.card ι*A := by
  have hZ0 : 0 < bulkNormalizer L E := (by positivity : 0 < L/1000).trans_le hZ
  have horder : bulkLogLower L ≤ bulkLogUpper L := Real.exp_le_exp.mpr (by linarith)
  have h := primeIntegral_norm_le_prod (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L)
    (fun _ => bulkNormalizer L E) (fun _ => Real.exp_pos _) (fun _ => horder)
    (fun _ => hZ0) f hf
  simp only [Finset.prod_const,Finset.card_univ,bulk_harmonic_integral] at h
  have hm : (bulkNormalizer L E)⁻¹*(L/500) ≤ 2 := by
    rw [show (bulkNormalizer L E)⁻¹*(L/500) = (L/500)/bulkNormalizer L E by ring]
    exact (div_le_iff₀ hZ0).mpr (by linarith)
  exact h.trans ((mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity : 0 ≤ (bulkNormalizer L E)⁻¹*(L/500)) hm _) hA).trans_eq (mul_comm _ _))

theorem eventually_norm_bulk_primeIntegral_le :
    ∀ᶠ L : ℝ in atTop, ∀ (ι : Type*) [Fintype ι] [DecidableEq ι]
      (E : Finset ℕ), E.card ≤ 2 → ∀ {A : ℝ}, 0 ≤ A → ∀ f : (ι → ℝ) → ℂ,
      (∀ t ∈ logRectangle (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L),
        ‖f (fun i => Real.exp (t i))‖ ≤ A) →
      ‖primeIntegral (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L)
        (fun _ => bulkNormalizer L E) f‖ ≤ 2^Fintype.card ι*A := by
  filter_upwards [RepeatedPriorBounds.bulk_mass_lower_eventually,eventually_gt_atTop (0 : ℝ)] with L hm hL
  intro ι _ _ E hE A hA f hf
  exact norm_bulk_primeIntegral_le hL hA E (hm E hE) f hf

end Ostmann.Arithmetic.HistoryPrincipalIntegralBounds

end

end OAI
