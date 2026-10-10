import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CompactnessWeightIntegrals

namespace OAI

/-!
# Finite measures obtained from the compactness weight

The positive decaying compactness weight turns a globally growing measure into a finite
measure. Integral formulas give quantitative tail control and transfer a lower mass bound
on the unit ball to a lower bound for the weighted total mass.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter
open scoped ENNReal

def compactnessWeightedMeasure {d : ℕ} (n : ℕ) (μ : Measure (Ambient d)) :
    Measure (Ambient d) := μ.withDensity (fun x => ENNReal.ofReal (compactnessWeight n x))

theorem compactnessWeightedMeasure_apply {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    {s : Set (Ambient d)} (hs : MeasurableSet s)
    (hi : IntegrableOn (compactnessWeight n) s μ) :
    compactnessWeightedMeasure n μ s = ENNReal.ofReal (∫ x in s, compactnessWeight n x ∂μ) := by
  rw [compactnessWeightedMeasure, withDensity_apply _ hs]
  exact (ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun x => (compactnessWeight_pos n x).le))).symm

theorem compactnessWeightedMeasure_finite {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (C : ℝ) (hg : GlobalUpperGrowth n C μ) : IsFiniteMeasure (compactnessWeightedMeasure n μ) := by
  refine ⟨?_⟩
  rw [compactnessWeightedMeasure_apply n μ MeasurableSet.univ
    (compactnessWeight_integrable n μ C hg).integrableOn]
  exact ENNReal.ofReal_lt_top

def compactnessFiniteMeasure {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (C : ℝ) (hg : GlobalUpperGrowth n C μ) : FiniteMeasure (Ambient d) :=
  ⟨compactnessWeightedMeasure n μ, compactnessWeightedMeasure_finite n μ C hg⟩

theorem compactnessWeightedMeasure_real {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    {s : Set (Ambient d)} (hs : MeasurableSet s)
    (hi : IntegrableOn (compactnessWeight n) s μ) :
    (compactnessWeightedMeasure n μ).real s = ∫ x in s, compactnessWeight n x ∂μ := by
  rw [Measure.real, compactnessWeightedMeasure_apply n μ hs hi,
    ENNReal.toReal_ofReal (integral_nonneg (fun x => (compactnessWeight_pos n x).le))]

theorem compactnessFiniteMeasure_mass_bound {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (C : ℝ) (hg : GlobalUpperGrowth n C μ) :
    ((compactnessFiniteMeasure n μ C hg).mass : ℝ) ≤ 3 * C * 2 ^ n := by
  change (compactnessWeightedMeasure n μ).real univ ≤ _
  rw [compactnessWeightedMeasure_real n μ MeasurableSet.univ
    (compactnessWeight_integrable n μ C hg).integrableOn, Measure.restrict_univ]
  exact compactnessWeight_integral_bound n μ C hg

theorem compactnessFiniteMeasure_tail_bound {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (C : ℝ) (hg : GlobalUpperGrowth n C μ) (R : ℝ) (hR : 0 < R) :
    ((compactnessFiniteMeasure n μ C hg) (closedBall (0 : Ambient d) R)ᶜ : ℝ) ≤
      2 * (C * 2 ^ n / R) := by
  have heq : (closedBall (0 : Ambient d) R)ᶜ = {x | R < dist (0 : Ambient d) x} := by
    ext x
    simp only [mem_ofPred_eq, mem_compl_iff, mem_closedBall, not_le]
    rw [dist_comm]
  change (compactnessWeightedMeasure n μ).real (closedBall (0 : Ambient d) R)ᶜ ≤ _
  have hs : MeasurableSet {x | R < dist (0 : Ambient d) x} :=
    (isOpen_lt continuous_const (continuous_const.dist continuous_id)).measurableSet
  rw [heq, compactnessWeightedMeasure_real n μ hs
    (compactnessWeight_integrableOn_exterior n μ C hg R hR)]
  exact compactnessWeight_exterior_integral_bound n μ C hg R hR

theorem compactnessWeight_lower_on_unit_ball {d : ℕ} (n : ℕ) (x : Ambient d)
    (hx : x ∈ ball (0 : Ambient d) 1) : (2 : ℝ)⁻¹ ^ (n + 1) ≤ compactnessWeight n x := by
  have hn : ‖x‖ < 1 := by simpa only [mem_ball, dist_zero_right] using! hx
  have hpow : (1 + ‖x‖) ^ (n + 1) ≤ (2 : ℝ) ^ (n + 1) :=
    pow_le_pow_left₀ (by positivity) (by linarith) (n + 1)
  simpa only [compactnessWeight, one_div, inv_pow] using!
    one_div_le_one_div_of_le (by positivity : 0 < (1 + ‖x‖) ^ (n + 1)) hpow

theorem compactnessWeight_integral_lower {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (C c : ℝ) (hg : GlobalUpperGrowth n C μ)
    (hm : c ≤ μ.real (ball (0 : Ambient d) 1)) :
    c * (2 : ℝ)⁻¹ ^ (n + 1) ≤ ∫ x, compactnessWeight n x ∂μ := by
  have hi := compactnessWeight_integrable n μ C hg
  have : IsFiniteMeasure (μ.restrict (ball (0 : Ambient d) 1)) :=
    isFiniteMeasure_restrict.mpr
      ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall (0 : Ambient d) 1).measure_lt_top).ne
  have hlocal : μ.real (ball (0 : Ambient d) 1) * (2 : ℝ)⁻¹ ^ (n + 1) ≤
      ∫ x in ball (0 : Ambient d) 1, compactnessWeight n x ∂μ := by
    have h := integral_mono_ae (μ := μ.restrict (ball (0 : Ambient d) 1))
      (integrable_const ((2 : ℝ)⁻¹ ^ (n + 1))) hi.integrableOn
      (by
        filter_upwards [ae_restrict_mem (μ := μ) measurableSet_ball] with x hx
        exact compactnessWeight_lower_on_unit_ball n x hx)
    simpa only [integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply_univ] using! h
  exact (mul_le_mul_of_nonneg_right hm (by positivity)).trans
    (hlocal.trans (setIntegral_le_integral hi (Eventually.of_forall
      (fun x => (compactnessWeight_pos n x).le))))

theorem compactnessFiniteMeasure_mass_lower {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (C c : ℝ) (hg : GlobalUpperGrowth n C μ)
    (hm : c ≤ μ.real (ball (0 : Ambient d) 1)) :
    c * (2 : ℝ)⁻¹ ^ (n + 1) ≤ ((compactnessFiniteMeasure n μ C hg).mass : ℝ) := by
  change _ ≤ (compactnessWeightedMeasure n μ).real univ
  rw [compactnessWeightedMeasure_real n μ MeasurableSet.univ
    (compactnessWeight_integrable n μ C hg).integrableOn, Measure.restrict_univ]
  exact compactnessWeight_integral_lower n μ C c hg hm

end

end RieszRectifiability

end OAI
