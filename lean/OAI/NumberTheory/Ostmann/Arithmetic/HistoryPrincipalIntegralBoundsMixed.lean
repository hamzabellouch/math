import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantPrincipalMassBoundsBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantPriorGridMixed
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPrincipalIntegralAverage
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPrincipalIntegralBoundsBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryPrincipalIntegralBounds
open MeasureTheory PrimeCellFreezing MixedCellIntegralFreezing HistoryPrincipalIntegralAverage
open HistoryGiantPriorGrid HistoryGiantPrincipalMassBounds
open scoped BigOperators

theorem unit_giant_logCellMass_le {G Z : ℝ} (hG : 2 ≤ G) (hZ : 0 < Z)
    (hZi : Z⁻¹ ≤ 2*G) :
    logCellMass (fun _ : Unit=>Z⁻¹) (fun _=>G-1) (fun _=>G+1) ≤ 8 := by
  rw [logCellMass_eq_prod _ _ _ (fun _=>by linarith)]
  simpa only [Finset.univ_unique,Finset.prod_singleton] using
    normalized_giant_harmonic_mass_le hG hZ hZi

theorem mixed_giantLogMass_le {G Z : ℝ} (hG : 2 ≤ G) (hZ : 0 < Z)
    (hZi : Z⁻¹ ≤ 2*G) :
    mixedLogMass 1 (G-1) (G+1) G smoothPartition
      (fun _ : Unit=>Z⁻¹) (fun _=>G-1) (fun _=>G+1) ≤ 16*Real.exp 1 := by
  rw [mixedLogMass_eq _ _ _ _ _ _ _ _ (by linarith)]
  have hi := giant_integerDensityMass_bounds 1 (by norm_num) G
  have hp0 := logCellMass_nonneg (fun _ : Unit=>Z⁻¹) (fun _=>G-1) (fun _=>G+1)
    (fun _=>inv_nonneg.mpr hZ.le) (fun _=>by linarith)
  calc
    _ ≤ (2*Real.exp 1)*8 := mul_le_mul hi.2 (unit_giant_logCellMass_le hG hZ hZi)
      hp0 (by positivity)
    _ = _ := by ring

theorem norm_mixed_giantIntegral_le {G Z A : ℝ}
    (hG : 2 ≤ G) (hZ : 0 < Z) (hZi : Z⁻¹ ≤ 2*G) (hA : 0 ≤ A)
    (f : (Option Unit→ℝ)→ℂ)
    (hf : ∀z∈logRectangle (fun _ : Option Unit=>G-1) (fun _=>G+1),
      ‖f (fun i=>Real.exp (z i))‖ ≤ A) :
    ‖mixedIntegral (G-1) (G+1) G smoothPartition
      (fun _ : Unit=>G-1) (fun _=>G+1) (fun _=>Z) (mixedGiantPrimeTest G f)‖ ≤
        16*Real.exp 1*A := by
  let D := mixedLogRectangle (G-1) (G+1) (fun _ : Unit=>G-1) (fun _=>G+1)
  let density := mixedLogDensity 1 G smoothPartition (fun _ : Unit=>Z⁻¹)
  have hcompact : IsCompact D := isCompact_mixedLogRectangle _ _ _ _
  have hdi : IntegrableOn density D := integrableOn_mixedLogDensity 1 (G-1) (G+1) G
    smoothPartition (fun _ : Unit=>Z⁻¹) (fun _=>G-1) (fun _=>G+1)
    smoothPartition_continuous (fun _=>by linarith)
  have hd0 : ∀t∈D,0 ≤ density t := fun t ht=>
    mixedLogDensity_nonneg 1 (G-1) (G+1) G smoothPartition
      (fun _ : Unit=>Z⁻¹) (fun _=>G-1) (fun _=>G+1)
      (fun _ _=>smoothPartition_nonneg _) (fun _=>inv_nonneg.mpr hZ.le)
      (fun _=>by linarith) ht
  have htest : ∀t∈D,‖mixedGiantPrimeTest G f (optionCoordinates (mixedExp t))‖ ≤ A := by
    intro t ht
    have hz : optionCoordinates t∈logRectangle (fun _ : Option Unit=>G-1) (fun _=>G+1) := by
      intro i hi
      cases i with
      | none => exact ht.1
      | some i => exact ht.2 i (Set.mem_univ i)
    have hff := hf (optionCoordinates t) hz
    rw [←optionCoordinates_mixedExp] at hff
    rw [mixedGiantPrimeTest,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (smoothPartition_nonneg _)]
    exact (mul_le_mul (smoothPartition_le_one _) hff (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  change ‖∫t in D,density t • mixedGiantPrimeTest G f (optionCoordinates (mixedExp t))‖ ≤ _
  calc
    _ ≤ ∫t in D,density t*A := by
      apply norm_integral_le_of_norm_le (hdi.mul_const A)
      filter_upwards [ae_restrict_mem hcompact.measurableSet] with t ht
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hd0 t ht)]
      exact mul_le_mul_of_nonneg_left (htest t ht) (hd0 t ht)
    _ = mixedLogMass 1 (G-1) (G+1) G smoothPartition
        (fun _ : Unit=>Z⁻¹) (fun _=>G-1) (fun _=>G+1)*A := by
      rw [integral_mul_const]
      rfl
    _ ≤ 16*Real.exp 1*A := mul_le_mul_of_nonneg_right (mixed_giantLogMass_le hG hZ hZi) hA

end Ostmann.Arithmetic.HistoryPrincipalIntegralBounds

end

end OAI
