import OAI.NumberTheory.Ostmann.Arithmetic.MixedCellIntegralFreezingMass

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.MixedCellIntegralFreezing
open MeasureTheory PrimeCellFreezing
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def mixedExp (t : ℝ × (ι → ℝ)) : ℝ × (ι → ℝ) :=
  (Real.exp t.1, fun i => Real.exp (t.2 i))

def mixedLogIntegral (M : ℕ) (loI hiI G : ℝ) (φ : ℝ → ℝ)
    (w lo hi : ι → ℝ) (f : (ℝ × (ι → ℝ)) → ℂ) : ℂ :=
  ∫ t in mixedLogRectangle loI hiI lo hi, mixedLogDensity M G φ w t • f (mixedExp t)

omit [DecidableEq ι] in
theorem mixed_freezing_of_variation (M : ℕ) (loI hiI G : ℝ) (φ : ℝ → ℝ)
    (w lo hi : ι → ℝ) (hφ : Continuous φ)
    (hφ0 : ∀ t ∈ Set.Icc loI hiI, 0 ≤ φ (t-G))
    (hw : ∀ i, 0 ≤ w i) (hlo : ∀ i, 0 < lo i)
    (F : (ℝ × (ι → ℝ)) → ℂ)
    (hF : ContinuousOn F (mixedLogRectangle loI hiI lo hi))
    (base : ℝ × (ι → ℝ)) {C : ℝ}
    (hvar : ∀ t ∈ mixedLogRectangle loI hiI lo hi, ‖F t - F base‖ ≤ C) :
    ‖(∫ t in mixedLogRectangle loI hiI lo hi, mixedLogDensity M G φ w t • F t) -
      mixedLogMass M loI hiI G φ w lo hi • F base‖ ≤
      C * mixedLogMass M loI hiI G φ w lo hi := by
  have hc := isCompact_mixedLogRectangle loI hiI lo hi
  have hdc := continuousOn_mixedLogDensity M loI hiI G φ w lo hi hφ hlo
  have hdi := integrableOn_mixedLogDensity M loI hiI G φ w lo hi hφ hlo
  have hFi : IntegrableOn (fun t => mixedLogDensity M G φ w t • F t)
      (mixedLogRectangle loI hiI lo hi) :=
    (hdc.smul hF).integrableOn_compact hc
  have hbi : IntegrableOn (fun t => mixedLogDensity M G φ w t • F base)
      (mixedLogRectangle loI hiI lo hi) :=
    (hdc.smul continuousOn_const).integrableOn_compact hc
  have heq : (∫ t in mixedLogRectangle loI hiI lo hi, mixedLogDensity M G φ w t • F t) -
      mixedLogMass M loI hiI G φ w lo hi • F base =
      ∫ t in mixedLogRectangle loI hiI lo hi, mixedLogDensity M G φ w t • (F t-F base) := by
    unfold mixedLogMass
    rw [← integral_smul_const, ← integral_sub hFi hbi]
    congr 1
    funext t
    exact (smul_sub _ _ _).symm
  rw [heq]
  calc
    _ ≤ ∫ t in mixedLogRectangle loI hiI lo hi, mixedLogDensity M G φ w t * C := by
      apply norm_integral_le_of_norm_le (hdi.mul_const C)
      filter_upwards [ae_restrict_mem hc.measurableSet] with t ht
      have hn := mixedLogDensity_nonneg M loI hiI G φ w lo hi hφ0 hw hlo ht
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hn]
      exact mul_le_mul_of_nonneg_left (hvar t ht) hn
    _ = C * mixedLogMass M loI hiI G φ w lo hi := by
      rw [integral_mul_const]
      exact mul_comm _ _

omit [Fintype ι] [DecidableEq ι] in
theorem mixedLogRectangle_convex (loI hiI : ℝ) (lo hi : ι → ℝ) :
    Convex ℝ (mixedLogRectangle loI hiI lo hi) :=
  (convex_Icc loI hiI).prod (logRectangle_convex lo hi)

omit [DecidableEq ι] in
theorem mixedLogRectangle_dist_le (loI hiI : ℝ) (lo hi : ι → ℝ)
    {mesh : ℝ} (hm : 0 ≤ mesh) (hwidthI : hiI-loI ≤ mesh)
    (hwidth : ∀ i, hi i-lo i ≤ mesh)
    {x y : ℝ × (ι → ℝ)}
    (hx : x ∈ mixedLogRectangle loI hiI lo hi)
    (hy : y ∈ mixedLogRectangle loI hiI lo hi) : ‖x-y‖ ≤ mesh := by
  rw [Prod.norm_def, max_le_iff]
  constructor
  · simp only [Prod.fst_sub, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hx.1.1, hy.1.2], by linarith [hy.1.1, hx.1.2]⟩
  · apply (pi_norm_le_iff_of_nonneg hm).mpr
    intro i
    simpa only [Prod.snd_sub, Pi.sub_apply, Real.norm_eq_abs] using
      logRectangle_coordinate_dist_le lo hi hwidth hx.2 hy.2 i

omit [DecidableEq ι] in
theorem mixed_positive_integral_freezing_bound (M : ℕ) (loI hiI G : ℝ) (φ : ℝ → ℝ)
    (w lo hi : ι → ℝ) (hφ : Continuous φ)
    (hφ0 : ∀ t ∈ Set.Icc loI hiI, 0 ≤ φ (t-G))
    (hw : ∀ i, 0 ≤ w i) (hlo : ∀ i, 0 < lo i)
    (f : (ℝ × (ι → ℝ)) → ℂ) {D mesh : ℝ} (hD : 0 ≤ D) (hm : 0 ≤ mesh)
    (hwidthI : hiI-loI ≤ mesh) (hwidth : ∀ i, hi i-lo i ≤ mesh)
    (hf : ∀ z ∈ mixedLogRectangle loI hiI lo hi,
      DifferentiableAt ℝ (fun y => f (mixedExp y)) z)
    (hd : ∀ z ∈ mixedLogRectangle loI hiI lo hi,
      ‖fderiv ℝ (fun y => f (mixedExp y)) z‖ ≤ D)
    {base : ℝ × (ι → ℝ)} (hbase : base ∈ mixedLogRectangle loI hiI lo hi) :
    ‖mixedLogIntegral M loI hiI G φ w lo hi f -
      mixedLogMass M loI hiI G φ w lo hi • f (mixedExp base)‖ ≤
      D * mesh * mixedLogMass M loI hiI G φ w lo hi := by
  apply mixed_freezing_of_variation M loI hiI G φ w lo hi hφ hφ0 hw hlo
    (fun y => f (mixedExp y))
    (fun z hz => (hf z hz).continuousAt.continuousWithinAt) base
  intro z hz
  have h := (mixedLogRectangle_convex loI hiI lo hi).norm_image_sub_le_of_norm_fderiv_le
    hf hd hbase hz
  exact h.trans (mul_le_mul_of_nonneg_left
    (mixedLogRectangle_dist_le loI hiI lo hi hm hwidthI hwidth hz hbase) hD)

omit [DecidableEq ι] in
theorem residue_mixed_integral_freezing_bound (M : ℕ) (loI hiI G : ℝ) (φ : ℝ → ℝ)
    (Z lo hi : ι → ℝ) (hφ : Continuous φ)
    (hφ0 : ∀ t ∈ Set.Icc loI hiI, 0 ≤ φ (t-G))
    (hZ : ∀ i, 0 < Z i) (hlo : ∀ i, 0 < lo i)
    (hI : loI ≤ hiI) (horder : ∀ i, lo i ≤ hi i)
    (f : (ℝ × (ι → ℝ)) → ℂ) {D mesh : ℝ} (hD : 0 ≤ D) (hm : 0 ≤ mesh)
    (hwidthI : hiI-loI ≤ mesh) (hwidth : ∀ i, hi i-lo i ≤ mesh)
    (hf : ∀ z ∈ mixedLogRectangle loI hiI lo hi,
      DifferentiableAt ℝ (fun y => f (mixedExp y)) z)
    (hd : ∀ z ∈ mixedLogRectangle loI hiI lo hi,
      ‖fderiv ℝ (fun y => f (mixedExp y)) z‖ ≤ D)
    {base : ℝ × (ι → ℝ)} (hbase : base ∈ mixedLogRectangle loI hiI lo hi) :
    ‖mixedLogIntegral M loI hiI G φ (fun i => ((Nat.totient M : ℝ) * Z i)⁻¹) lo hi f -
      (IntegerCell.integerDensityMass M loI hiI G φ *
        ∏ i, PrimeProgression.harmonicIntegral M (lo i) (hi i) / Z i) • f (mixedExp base)‖ ≤
      D * mesh * (IntegerCell.integerDensityMass M loI hiI G φ *
        ∏ i, PrimeProgression.harmonicIntegral M (lo i) (hi i) / Z i) := by
  rw [← residue_mixedLogMass_eq M loI hiI G φ Z lo hi hI horder]
  exact mixed_positive_integral_freezing_bound M loI hiI G φ _ lo hi hφ hφ0
    (fun i => inv_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) (hZ i).le))
    hlo f hD hm hwidthI hwidth hf hd hbase

end Ostmann.Arithmetic.MixedCellIntegralFreezing

end

end OAI
