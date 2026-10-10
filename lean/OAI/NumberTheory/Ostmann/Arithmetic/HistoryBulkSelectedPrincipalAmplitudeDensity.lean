import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantCorrectedBoundsCutoff
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPrincipalIntegralBoundsGiant
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedGiantDensityMass

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSelectedPrincipalAmplitude
open Construction MeasureTheory PrimeCellFreezing MixedCellIntegralFreezing
open HistoryPrincipalIntegralAverage HistoryPrincipalIntegralBounds HistoryGiantPriorGrid
open HistoryBulkGiantCorrectedBounds HistorySelectedGiantDensityMass

def primeGiantScalar {ι : Type*} (G Z : ℝ)
    (f : (Bool→ℝ)→(ι→ℝ)→ℂ) (x : ι→ℝ) : ℂ :=
  primeIntegral (fun _ : Bool=>G-1) (fun _=>G+1) (fun _=>Z)
    (fun y=>primeJointCutoff G f y x)

def mixedGiantScalar {ι : Type*} (G Z : ℝ)
    (f : (Option Unit→ℝ)→(ι→ℝ)→ℂ) (x : ι→ℝ) : ℂ :=
  mixedIntegral (G-1) (G+1) G smoothPartition
    (fun _ : Unit=>G-1) (fun _=>G+1) (fun _=>Z)
    (fun y=>mixedJointCutoff G f y x)

theorem norm_primeGiantScalar_le {ι : Type*} {G Z A : ℝ}
    (hG : 1<G) (hZ : 0<Z) (hA : 0≤A)
    (hM : primeDensityMass G Z ≤ 64)
    (f : (Bool→ℝ)→(ι→ℝ)→ℂ) (x : ι→ℝ)
    (hf : ∀z∈logRectangle (fun _ : Bool=>G-1) (fun _=>G+1),
      ‖f (fun i=>Real.exp (z i)) x‖≤A) :
    ‖primeGiantScalar G Z f x‖≤64*A := by
  have hcut : ∀z∈logRectangle (fun _ : Bool=>G-1) (fun _=>G+1),
      ‖primeJointCutoff G f (fun i=>Real.exp (z i)) x‖≤A := by
    intro z hz
    have ha := giantCell_bounds G (Real.exp (z false))
    have hb := giantCell_bounds G (Real.exp (z true))
    rw [primeJointCutoff,primeCutoff,norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
      Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg ha.1,abs_of_nonneg hb.1]
    exact (mul_le_mul ((mul_le_mul ha.2 hb.2 hb.1 zero_le_one).trans_eq (one_mul 1))
      (hf z hz) (norm_nonneg _) zero_le_one).trans_eq (one_mul A)
  have h := primeIntegral_norm_le_mass (fun _ : Bool=>G-1) (fun _=>G+1) (fun _=>Z)
    (fun _=>by linarith) (fun _=>hZ) _ hcut
  exact h.trans ((mul_le_mul_of_nonneg_left hM hA).trans_eq (mul_comm A 64))

theorem norm_mixedGiantScalar_le {ι : Type*} {G Z A : ℝ}
    (hG : 1<G) (hZ : 0<Z) (hA : 0≤A)
    (hM : mixedDensityMass G Z ≤ 64)
    (f : (Option Unit→ℝ)→(ι→ℝ)→ℂ) (x : ι→ℝ)
    (hf : ∀z∈logRectangle (fun _ : Option Unit=>G-1) (fun _=>G+1),
      ‖f (fun i=>Real.exp (z i)) x‖≤A) :
    ‖mixedGiantScalar G Z f x‖≤64*A := by
  let S := mixedLogRectangle (G-1) (G+1) (fun _ : Unit=>G-1) (fun _=>G+1)
  let density := mixedLogDensity 1 G smoothPartition (fun _ : Unit=>Z⁻¹)
  have hc : IsCompact S := isCompact_mixedLogRectangle _ _ _ _
  have hdi : IntegrableOn density S := integrableOn_mixedLogDensity 1 (G-1) (G+1) G
    smoothPartition (fun _ : Unit=>Z⁻¹) (fun _=>G-1) (fun _=>G+1)
    smoothPartition_continuous (fun _=>by linarith)
  have hd0 : ∀t∈S,0≤density t := fun t ht=>
    mixedLogDensity_nonneg 1 (G-1) (G+1) G smoothPartition
      (fun _ : Unit=>Z⁻¹) (fun _=>G-1) (fun _=>G+1)
      (fun _ _=>smoothPartition_nonneg _) (fun _=>inv_nonneg.mpr hZ.le)
      (fun _=>by linarith) ht
  have htest : ∀t∈S,‖mixedJointCutoff G f (optionCoordinates (mixedExp t)) x‖≤A := by
    intro t ht
    have hz : optionCoordinates t∈logRectangle (fun _ : Option Unit=>G-1) (fun _=>G+1) := by
      intro i hi
      cases i with
      | none => exact ht.1
      | some i => exact ht.2 i (Set.mem_univ i)
    have hh := hf (optionCoordinates t) hz
    rw [←optionCoordinates_mixedExp] at hh
    rw [mixedJointCutoff,mixedGiantPrimeTest,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (smoothPartition_nonneg _)]
    exact (mul_le_mul (smoothPartition_le_one _) hh (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  change ‖∫t in S,density t • mixedJointCutoff G f (optionCoordinates (mixedExp t)) x‖≤_
  calc
    _ ≤ ∫t in S,density t*A := by
      apply norm_integral_le_of_norm_le (hdi.mul_const A)
      filter_upwards [ae_restrict_mem hc.measurableSet] with t ht
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hd0 t ht)]
      exact mul_le_mul_of_nonneg_left (htest t ht) (hd0 t ht)
    _ = mixedDensityMass G Z*A := by rw [integral_mul_const]; rfl
    _ ≤ 64*A := mul_le_mul_of_nonneg_right hM hA

end Ostmann.Arithmetic.HistoryBulkSelectedPrincipalAmplitude

end

end OAI
