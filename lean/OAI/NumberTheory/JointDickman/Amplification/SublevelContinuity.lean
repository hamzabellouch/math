import OAI.NumberTheory.JointDickman.Arithmetic.PrimeBoxBoundary
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! # Continuity in the product cutoff -/
namespace JointDickman
open Filter MeasureTheory
open scoped Topology NNReal ENNReal

theorem sublevel_measure_continuousAt {Ω : Type*} [MeasurableSpace Ω]
    (μ : FiniteMeasure Ω) {R : Set Ω} (hR : MeasurableSet R)
    {f : Ω → ℝ} (hf : Measurable f) {u : ℝ}
    (hu : (μ : Measure Ω) {t | f t = u} = 0) :
    ContinuousAt (fun v : ℝ => (μ (R ∩ {t | f t ≤ v}) : ℝ)) u := by
  classical
  let g (v : ℝ) : Ω → ℝ := (R ∩ {t | f t ≤ v}).indicator 1
  have hgmeas (v : ℝ) : AEStronglyMeasurable (g v) (μ : Measure Ω) :=
    (measurable_const.indicator (hR.inter (hf measurableSet_Iic))).aestronglyMeasurable
  have hbound (v : ℝ) (t : Ω) : ‖g v t‖ ≤ 1 := by
    simp only [g, Set.indicator_apply, Pi.one_apply]
    split_ifs <;> norm_num
  have hne : ∀ᵐ t ∂(μ : Measure Ω), f t ≠ u := by
    rw [ae_iff]
    simpa only [not_not] using hu
  have hlim : ∀ᵐ t ∂(μ : Measure Ω), Tendsto (fun v => g v t) (𝓝 u) (𝓝 (g u t)) := by
    filter_upwards [hne] with t ht
    by_cases htR : t ∈ R
    · rcases lt_or_gt_of_ne ht with htu | hut
      · have he : (fun _ : ℝ => (1 : ℝ)) =ᶠ[𝓝 u] (fun v => g v t) := by
          filter_upwards [eventually_gt_nhds htu] with v hv
          simp [g, htR, hv.le]
        simpa [g, htR, htu.le] using tendsto_const_nhds.congr' he
      · have he : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 u] (fun v => g v t) := by
          filter_upwards [eventually_lt_nhds hut] with v hv
          simp [g, htR, not_le.mpr hv]
        simpa [g, htR, not_le.mpr hut] using tendsto_const_nhds.congr' he
    · simp [g, htR]
  have h := tendsto_integral_filter_of_dominated_convergence (μ := (μ : Measure Ω))
    (fun _ => (1 : ℝ)) (.of_forall hgmeas)
    (.of_forall (fun v => .of_forall (hbound v))) (integrable_const 1) hlim
  have he (v : ℝ) : (∫ t, g v t ∂(μ : Measure Ω)) = (μ (R ∩ {t | f t ≤ v}) : ℝ) := by
    exact integral_indicator_one (hR.inter (hf measurableSet_Iic))
  simpa only [ContinuousAt, he] using h

theorem primeBoxCutoff_measure_continuous {c : ℝ} (n : ℕ)
    (a b : Fin (n+1) → ℝ) :
    Continuous (fun u : ℝ => ((FiniteMeasure.pi (fun _ : Fin (n+1) => logarithmicPrimeMeasure c))
      (primeBoxCutoff (n+1) a b u) : ℝ)) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  apply sublevel_measure_continuousAt _ (MeasurableSet.univ_pi (fun _ => measurableSet_Ioc))
    (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i))
  exact pi_sum_level_null _ n u

end JointDickman

end OAI
