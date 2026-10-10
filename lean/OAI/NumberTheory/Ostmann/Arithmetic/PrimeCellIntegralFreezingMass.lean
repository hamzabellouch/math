import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellFreezingLog
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeProgression

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.PrimeCellFreezing
open MeasureTheory
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

def logCellDensity (w : ι → ℝ) (t : ι → ℝ) : ℝ := ∏ i, w i / t i

def logCellMass (w lo hi : ι → ℝ) : ℝ :=
  ∫ t in logRectangle lo hi, logCellDensity w t

theorem logCellMass_eq_prod (w lo hi : ι → ℝ) (horder : ∀ i, lo i ≤ hi i) :
    logCellMass w lo hi = ∏ i, w i * ∫ t in lo i..hi i, (t : ℝ)⁻¹ := by
  unfold logCellMass logCellDensity logRectangle
  change (∫ t, ∏ i, w i / t i ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))).restrict
    (Set.univ.pi (fun i => Set.Icc (lo i) (hi i)))) = _
  rw [Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp_rw [div_eq_mul_inv]
  rw [integral_const_mul, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (horder i)]

theorem residue_logCellMass_eq_prod (M : ℕ) (Z lo hi : ι → ℝ)
    (horder : ∀ i, lo i ≤ hi i) :
    logCellMass (fun i => ((Nat.totient M : ℝ) * Z i)⁻¹) lo hi =
      ∏ i, PrimeProgression.harmonicIntegral M (lo i) (hi i) / Z i := by
  rw [logCellMass_eq_prod _ lo hi horder]
  apply Finset.prod_congr rfl
  intro i _
  simp only [PrimeProgression.harmonicIntegral, mul_inv_rev, div_eq_mul_inv]
  ring

omit [Fintype ι] in
theorem isCompact_logRectangle (lo hi : ι → ℝ) : IsCompact (logRectangle lo hi) :=
  isCompact_univ_pi fun _ => isCompact_Icc

theorem continuousOn_logCellDensity (w lo hi : ι → ℝ) (hlo : ∀ i, 0 < lo i) :
    ContinuousOn (logCellDensity w) (logRectangle lo hi) := by
  apply continuousOn_finsetProd
  intro i _
  exact continuousOn_const.div (continuous_apply i).continuousOn fun t ht =>
    ne_of_gt ((hlo i).trans_le (ht i (Set.mem_univ i)).1)

theorem integrableOn_logCellDensity (w lo hi : ι → ℝ) (hlo : ∀ i, 0 < lo i) :
    IntegrableOn (logCellDensity w) (logRectangle lo hi) :=
  (continuousOn_logCellDensity w lo hi hlo).integrableOn_compact
    (isCompact_logRectangle lo hi)

theorem logCellDensity_nonneg (w lo hi : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hlo : ∀ i, 0 < lo i) {t : ι → ℝ} (ht : t ∈ logRectangle lo hi) :
    0 ≤ logCellDensity w t :=
  Finset.prod_nonneg fun i _ => div_nonneg (hw i)
    (le_trans (hlo i).le (ht i (Set.mem_univ i)).1)

theorem logCellMass_nonneg (w lo hi : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hlo : ∀ i, 0 < lo i) : 0 ≤ logCellMass w lo hi := by
  apply setIntegral_nonneg (isCompact_logRectangle lo hi).measurableSet
  intro t ht
  exact logCellDensity_nonneg w lo hi hw hlo ht

end Ostmann.Arithmetic.PrimeCellFreezing

end

end OAI
