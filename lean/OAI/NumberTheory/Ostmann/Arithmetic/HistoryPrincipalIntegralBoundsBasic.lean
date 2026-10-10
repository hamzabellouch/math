import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPrincipalIntegralAverageBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryPrincipalIntegralBounds
open MeasureTheory PrimeCellFreezing HistoryPrincipalIntegralAverage
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem primeIntegral_norm_le_mass (lo hi Z : ι → ℝ)
    (hlo : ∀ i, 0 < lo i) (hZ : ∀ i, 0 < Z i)
    (f : (ι → ℝ) → ℂ) {A : ℝ}
    (hf : ∀ t ∈ logRectangle lo hi, ‖f (fun i => Real.exp (t i))‖ ≤ A) :
    ‖primeIntegral lo hi Z f‖ ≤ A*PrimeCellFreezing.logCellMass (fun i => (Z i)⁻¹) lo hi := by
  have hwi := integrableOn_logCellDensity (fun i => (Z i)⁻¹) lo hi hlo
  unfold primeIntegral logCellIntegral
  calc
    _ ≤ ∫ t in logRectangle lo hi, logCellDensity (fun i => (Z i)⁻¹) t*A := by
      apply norm_integral_le_of_norm_le (hwi.mul_const A)
      filter_upwards [ae_restrict_mem (isCompact_logRectangle lo hi).measurableSet] with t ht
      have hn := logCellDensity_nonneg (fun i => (Z i)⁻¹) lo hi
        (fun i => inv_nonneg.mpr (hZ i).le) hlo ht
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hn]
      exact mul_le_mul_of_nonneg_left (hf t ht) hn
    _ = _ := by rw [integral_mul_const]; exact mul_comm _ _

omit [DecidableEq ι] in
theorem primeIntegral_norm_le_prod (lo hi Z : ι → ℝ)
    (hlo : ∀ i, 0 < lo i) (horder : ∀ i, lo i ≤ hi i) (hZ : ∀ i, 0 < Z i)
    (f : (ι → ℝ) → ℂ) {A : ℝ}
    (hf : ∀ t ∈ logRectangle lo hi, ‖f (fun i => Real.exp (t i))‖ ≤ A) :
    ‖primeIntegral lo hi Z f‖ ≤ A*∏ i, (Z i)⁻¹*(∫ t in lo i..hi i, (t : ℝ)⁻¹) := by
  rw [← logCellMass_eq_prod _ lo hi horder]
  exact primeIntegral_norm_le_mass lo hi Z hlo hZ f hf

theorem normalized_giant_harmonic_mass_le {G Z : ℝ} (hG : 2 ≤ G)
    (hZ : 0 < Z) (hZi : Z⁻¹ ≤ 2*G) :
    Z⁻¹*(∫ t in (G-1)..(G+1), (t : ℝ)⁻¹) ≤ 8 := by
  have hlo : 0 < G-1 := by linarith
  have horder : G-1 ≤ G+1 := by linarith
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (f:=fun t : ℝ => t⁻¹) (C:=(G-1)⁻¹) (a:=G-1) (b:=G+1) (fun t ht => by
      rw [Set.uIoc_of_le horder] at ht
      have ht0 := hlo.trans ht.1
      rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht0)]
      exact inv_le_inv₀ ht0 hlo |>.mpr ht.1.le)
  have hwidth : |(G+1)-(G-1)| = (2 : ℝ) := by rw [show (G+1)-(G-1)=2 by ring]; norm_num
  rw [Real.norm_eq_abs,hwidth] at hh
  have hb : (2*G)*((G-1)⁻¹*2) ≤ 8 := by
    calc
      _ = (4*G)/(G-1) := by ring
      _ ≤ 8 := (div_le_iff₀ hlo).mpr (by linarith)
  calc
    _ ≤ Z⁻¹*((G-1)⁻¹*2) := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hh) (inv_nonneg.mpr hZ.le)
    _ ≤ (2*G)*((G-1)⁻¹*2) := mul_le_mul_of_nonneg_right hZi (by positivity)
    _ ≤ 8 := hb

end Ostmann.Arithmetic.HistoryPrincipalIntegralBounds

end

end OAI
