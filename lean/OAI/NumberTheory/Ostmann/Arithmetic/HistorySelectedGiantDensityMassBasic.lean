import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPrincipalIntegralBoundsMixed

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistorySelectedGiantDensityMass
open Construction HistoryPrincipalIntegralBounds

def primeDensityMass (G Z : ℝ) : ℝ :=
  PrimeCellFreezing.logCellMass (fun _ : Bool => Z⁻¹) (fun _ => G-1) (fun _ => G+1)

def mixedDensityMass (G Z : ℝ) : ℝ :=
  MixedCellIntegralFreezing.mixedLogMass 1 (G-1) (G+1) G smoothPartition
    (fun _ : Unit => Z⁻¹) (fun _ => G-1) (fun _ => G+1)

theorem primeDensityMass_bounds {G Z : ℝ} (hG : 2 ≤ G) (hZ : 0 < Z)
    (hZi : Z⁻¹ ≤ 2*G) : 0 ≤ primeDensityMass G Z ∧ primeDensityMass G Z ≤ 64 := by
  have hlo : 0 < G-1 := by linarith
  constructor
  · exact PrimeCellFreezing.logCellMass_nonneg _ _ _
      (fun _ => inv_nonneg.mpr hZ.le) (fun _ => hlo)
  · unfold primeDensityMass
    rw [PrimeCellFreezing.logCellMass_eq_prod _ _ _ (fun _ => by linarith)]
    have hn : 0 ≤ Z⁻¹*(∫ t in (G-1)..(G+1), (t:ℝ)⁻¹) := by
      apply mul_nonneg (inv_nonneg.mpr hZ.le)
      apply intervalIntegral.integral_nonneg (by linarith)
      intro t ht
      exact inv_nonneg.mpr (by linarith [ht.1])
    have hb := pow_le_pow_left₀ hn (normalized_giant_harmonic_mass_le hG hZ hZi) 2
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_bool,
      show (8:ℝ)^2 = 64 by norm_num] using hb

theorem mixedDensityMass_bounds {G Z : ℝ} (hG : 2 ≤ G) (hZ : 0 < Z)
    (hZi : Z⁻¹ ≤ 2*G) : 0 ≤ mixedDensityMass G Z ∧ mixedDensityMass G Z ≤ 64 := by
  constructor
  · exact MixedCellIntegralFreezing.mixedLogMass_nonneg _ _ _ _ _ _ _ _
      (fun _ _ => smoothPartition_nonneg _) (fun _ => inv_nonneg.mpr hZ.le)
      (fun _ => by linarith)
  · exact (mixed_giantLogMass_le hG hZ hZi).trans (by linarith [Real.exp_one_lt_three])

theorem three_error_mass_le {r M : ℝ} (hr : 0 ≤ r) (hM : M ≤ 64) :
    3*r*M ≤ 192*r := by nlinarith [mul_nonneg hr (sub_nonneg.mpr hM)]

end Ostmann.Arithmetic.HistorySelectedGiantDensityMass

end

end OAI
