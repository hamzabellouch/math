import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CompactnessWeight
import OAI.Analysis.RieszRectifiability.Kernel.TailBounds

namespace OAI

/-!
# Integrability of the compactness weight

Local finiteness controls the weight on closed balls, while polynomial upper growth controls
its exterior integral. Together these give global integrability and a quantitative mass bound.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter
open scoped ENNReal

theorem compactnessWeight_integrableOn_closedBall {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ] (R : ℝ) :
    IntegrableOn (compactnessWeight n) (closedBall (0 : Ambient d) R) μ := by
  have : IsFiniteMeasure (μ.restrict (closedBall (0 : Ambient d) R)) :=
    isFiniteMeasure_restrict.mpr (ne_of_lt (isCompact_closedBall (0 : Ambient d) R).measure_lt_top)
  apply (integrable_const (1 : ℝ)).mono' (compactnessWeight_continuous n).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    simpa only [Real.norm_of_nonneg (compactnessWeight_pos n x).le] using! compactnessWeight_le_one n x)

theorem compactnessWeight_integrableOn_exterior {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) (C : ℝ) (hg : GlobalUpperGrowth n C μ)
    (R : ℝ) (hR : 0 < R) :
    IntegrableOn (compactnessWeight n) {x | R < dist (0 : Ambient d) x} μ := by
  apply (inverseDistancePow_integrableOn_exterior n C μ hg 0 R hR).mono'
    (compactnessWeight_continuous n).aestronglyMeasurable
  have hs : MeasurableSet {x | R < dist (0 : Ambient d) x} :=
    (isOpen_lt continuous_const (continuous_const.dist continuous_id)).measurableSet
  filter_upwards [ae_restrict_mem (μ := μ) hs] with x hx
  rw [Real.norm_of_nonneg (compactnessWeight_pos n x).le]
  exact compactnessWeight_le_inverseDistance n x (dist_pos.mp (hR.trans hx)).symm

theorem compactnessWeight_exterior_integral_bound {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) (C : ℝ) (hg : GlobalUpperGrowth n C μ)
    (R : ℝ) (hR : 0 < R) :
    (∫ x in {x | R < dist (0 : Ambient d) x}, compactnessWeight n x ∂μ) ≤
      2 * (C * 2 ^ n / R) := by
  have hs : MeasurableSet {x | R < dist (0 : Ambient d) x} :=
    (isOpen_lt continuous_const (continuous_const.dist continuous_id)).measurableSet
  apply le_trans _ (inverseDistancePow_exterior_integral_bound n C μ hg 0 R hR)
  apply integral_mono_ae (compactnessWeight_integrableOn_exterior n μ C hg R hR)
    (inverseDistancePow_integrableOn_exterior n C μ hg 0 R hR)
  filter_upwards [ae_restrict_mem (μ := μ) hs] with x hx
  exact compactnessWeight_le_inverseDistance n x (dist_pos.mp (hR.trans hx)).symm

theorem compactnessWeight_integrable {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (C : ℝ) (hg : GlobalUpperGrowth n C μ) : Integrable (compactnessWeight n) μ := by
  have hi := compactnessWeight_integrableOn_closedBall n μ 1
  have ho := compactnessWeight_integrableOn_exterior n μ C hg 1 zero_lt_one
  have heq : {x | (1 : ℝ) < dist (0 : Ambient d) x} = (closedBall (0 : Ambient d) 1)ᶜ := by
    ext x
    simp only [mem_ofPred_eq, mem_compl_iff, mem_closedBall, not_le]
    rw [dist_comm]
  rw [heq] at ho
  have h := hi.union ho
  rw [union_compl_self] at h
  exact integrableOn_univ.mp h

theorem compactnessWeight_integral_bound {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (C : ℝ) (hg : GlobalUpperGrowth n C μ) :
    (∫ x, compactnessWeight n x ∂μ) ≤ 3 * C * 2 ^ n := by
  have hglobal := compactnessWeight_integrable n μ C hg
  have : IsFiniteMeasure (μ.restrict (closedBall (0 : Ambient d) 1)) :=
    isFiniteMeasure_restrict.mpr (ne_of_lt (isCompact_closedBall (0 : Ambient d) 1).measure_lt_top)
  have hm : μ.real (closedBall (0 : Ambient d) 1) ≤ C * 2 ^ n :=
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg hg.1 (by positivity))
      ((measure_mono (closedBall_subset_ball (by norm_num : (1 : ℝ) < 2))).trans
        (hg.2 0 2 (by norm_num)))
  have hi : (∫ x in closedBall (0 : Ambient d) 1, compactnessWeight n x ∂μ) ≤ C * 2 ^ n := by
    have h := integral_mono (μ := μ.restrict (closedBall (0 : Ambient d) 1))
      hglobal.integrableOn (integrable_const (1 : ℝ))
      (compactnessWeight_le_one n)
    have h' : (∫ x in closedBall (0 : Ambient d) 1, compactnessWeight n x ∂μ) ≤
        μ.real (closedBall (0 : Ambient d) 1) := by
      simpa only [integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply_univ, mul_one] using! h
    exact h'.trans hm
  have heq : (closedBall (0 : Ambient d) 1)ᶜ = {x | (1 : ℝ) < dist (0 : Ambient d) x} := by
    ext x
    simp only [mem_ofPred_eq, mem_compl_iff, mem_closedBall, not_le]
    rw [dist_comm]
  rw [← integral_add_compl (s := closedBall (0 : Ambient d) 1) measurableSet_closedBall hglobal, heq]
  calc
    _ ≤ C * 2 ^ n + 2 * (C * 2 ^ n / 1) :=
      add_le_add hi (compactnessWeight_exterior_integral_bound n μ C hg 1 zero_lt_one)
    _ = _ := by ring

end

end RieszRectifiability

end OAI
