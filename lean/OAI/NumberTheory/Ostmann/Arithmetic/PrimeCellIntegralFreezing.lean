import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellIntegralFreezingMass

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.PrimeCellFreezing
open MeasureTheory Characters.RationalHistory
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def logCellIntegral (w lo hi : ι → ℝ) (f : (ι → ℝ) → ℂ) : ℂ :=
  ∫ t in logRectangle lo hi, logCellDensity w t • f (fun j => Real.exp (t j))

omit [DecidableEq ι] in
theorem logCell_freezing_of_variation (w lo hi : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hlo : ∀ i, 0 < lo i)
    (F : (ι → ℝ) → ℂ) (hF : ContinuousOn F (logRectangle lo hi))
    (base : ι → ℝ) {C : ℝ}
    (hvar : ∀ t ∈ logRectangle lo hi, ‖F t - F base‖ ≤ C) :
    ‖(∫ t in logRectangle lo hi, logCellDensity w t • F t) -
      logCellMass w lo hi • F base‖ ≤ C * logCellMass w lo hi := by
  have hcompact := isCompact_logRectangle lo hi
  have hwc := continuousOn_logCellDensity w lo hi hlo
  have hwi := integrableOn_logCellDensity w lo hi hlo
  have hFi : IntegrableOn (fun t => logCellDensity w t • F t) (logRectangle lo hi) :=
    (hwc.smul hF).integrableOn_compact hcompact
  have hbi : IntegrableOn (fun t => logCellDensity w t • F base) (logRectangle lo hi) :=
    (hwc.smul continuousOn_const).integrableOn_compact hcompact
  have heq : (∫ t in logRectangle lo hi, logCellDensity w t • F t) -
      logCellMass w lo hi • F base =
      ∫ t in logRectangle lo hi, logCellDensity w t • (F t - F base) := by
    unfold logCellMass
    rw [← integral_smul_const, ← integral_sub hFi hbi]
    congr 1
    funext t
    exact (smul_sub _ _ _).symm
  rw [heq]
  calc
    _ ≤ ∫ t in logRectangle lo hi, logCellDensity w t * C := by
      apply norm_integral_le_of_norm_le (hwi.mul_const C)
      filter_upwards [ae_restrict_mem hcompact.measurableSet] with t ht
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (logCellDensity_nonneg w lo hi hw hlo ht)]
      exact mul_le_mul_of_nonneg_left (hvar t ht)
        (logCellDensity_nonneg w lo hi hw hlo ht)
    _ = C * logCellMass w lo hi := by rw [integral_mul_const]; exact mul_comm _ _

omit [Fintype ι] [DecidableEq ι] in
theorem logRectangle_coordinate_dist_le (lo hi : ι → ℝ) {mesh : ℝ}
    (hwidth : ∀ i, hi i - lo i ≤ mesh)
    {x y : ι → ℝ} (hx : x ∈ logRectangle lo hi) (hy : y ∈ logRectangle lo hi) :
    ∀ i, |x i - y i| ≤ mesh := by
  intro i
  have hxi := hx i (Set.mem_univ i)
  have hyi := hy i (Set.mem_univ i)
  exact abs_le.mpr ⟨by linarith [hwidth i, hxi.1, hyi.2], by linarith [hwidth i, hyi.1, hxi.2]⟩

theorem positive_integral_freezing_bound (w lo hi : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hlo : ∀ i, 0 < lo i)
    (f : (ι → ℝ) → ℂ) {D mesh : ℝ} (hD : 0 ≤ D) (hm : 0 ≤ mesh)
    (hwidth : ∀ i, hi i - lo i ≤ mesh)
    (hf : ∀ z ∈ logRectangle lo hi,
      DifferentiableAt ℝ (fun y => f (fun j => Real.exp (y j))) z)
    (hd : ∀ z ∈ logRectangle lo hi, ∀ i,
      ‖deriv (fun t => f (Expr.logCurve (fun j => Real.exp (z j)) i t)) 0‖ ≤ D)
    {base : ι → ℝ} (hbase : base ∈ logRectangle lo hi) :
    ‖logCellIntegral w lo hi f -
      logCellMass w lo hi • f (fun j => Real.exp (base j))‖ ≤
      (Fintype.card ι : ℝ) * D * mesh * logCellMass w lo hi := by
  apply logCell_freezing_of_variation w lo hi hw hlo
    (fun y => f (fun j => Real.exp (y j)))
    (fun z hz => (hf z hz).continuousAt.continuousWithinAt) base
  intro z hz
  exact positive_norm_sub_le f lo hi hD hm hf hd hz hbase
    (logRectangle_coordinate_dist_le lo hi hwidth hz hbase)

theorem residue_integral_freezing_bound (M : ℕ) (Z lo hi : ι → ℝ)
    (hZ : ∀ i, 0 < Z i) (hlo : ∀ i, 0 < lo i)
    (horder : ∀ i, lo i ≤ hi i)
    (f : (ι → ℝ) → ℂ) {D mesh : ℝ} (hD : 0 ≤ D) (hm : 0 ≤ mesh)
    (hwidth : ∀ i, hi i - lo i ≤ mesh)
    (hf : ∀ z ∈ logRectangle lo hi,
      DifferentiableAt ℝ (fun y => f (fun j => Real.exp (y j))) z)
    (hd : ∀ z ∈ logRectangle lo hi, ∀ i,
      ‖deriv (fun t => f (Expr.logCurve (fun j => Real.exp (z j)) i t)) 0‖ ≤ D)
    {base : ι → ℝ} (hbase : base ∈ logRectangle lo hi) :
    ‖logCellIntegral (fun i => ((Nat.totient M : ℝ) * Z i)⁻¹) lo hi f -
      (∏ i, PrimeProgression.harmonicIntegral M (lo i) (hi i) / Z i) •
        f (fun j => Real.exp (base j))‖ ≤
      (Fintype.card ι : ℝ) * D * mesh *
        ∏ i, PrimeProgression.harmonicIntegral M (lo i) (hi i) / Z i := by
  rw [← residue_logCellMass_eq_prod M Z lo hi horder]
  exact positive_integral_freezing_bound _ lo hi
    (fun i => inv_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) (hZ i).le))
    hlo f hD hm hwidth hf hd hbase

end Ostmann.Arithmetic.PrimeCellFreezing

end

end OAI
