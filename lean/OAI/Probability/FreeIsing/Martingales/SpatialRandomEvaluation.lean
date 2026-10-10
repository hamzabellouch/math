import OAI.Probability.FreeIsing.Martingales.RandomEvaluation
import OAI.Probability.FreeIsing.Martingales.SpatialLimit
import OAI.Probability.FreeIsing.Stochastic.IntegralAssociativityLimit

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology

namespace Problem367.MartingaleSpatialRandomEvaluation

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {I : ι → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ}

theorem tendsto_finiteSum_random_evaluation
    (hI : ∀ a, Martingale (I a) F P) (hY : Martingale Y F P)
    (hI2 : ∀ a t, MemLp (I a t) 2 P) (hY2 : ∀ t, MemLp (Y t) 2 P)
    (hcI : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => I a t ω))
    (hcY : ∀ᵐ ω ∂P, Continuous (fun t => Y t ω))
    (T : ℝ≥0)
    (hsum : HasSum (fun a => (hI2 a T).toLp (I a T)) ((hY2 T).toLp (Y T)))
    (r : Finset ι → Ω → ℝ≥0) (hr : ∀ q, Measurable (r q))
    (hb : ∀ q ω, r q ω ≤ T) :
    Tendsto (fun q : Finset ι => ∫ ω,
      ((∑ a ∈ q, I a (r q ω) ω) - Y (r q ω) ω) ^ 2 ∂P) atTop (𝓝 0) := by
  classical
  have ht := PredictableL2.tendsto_integral_sq_error_of_hasSum
    (fun a => I a T) (fun a => hI2 a T) (hY2 T) hsum
  apply squeeze_zero (fun q => integral_nonneg (fun ω => sq_nonneg _))
    (fun q => ?_) (by simpa only [mul_zero] using ht.const_mul 4)
  have hc : ∀ᵐ ω ∂P, Continuous
      (fun t => (MartingaleSpatialLimit.finiteSum I q - Y) t ω) := by
    filter_upwards [MartingaleSpatialLimit.finiteSum_ae_continuous hcI q, hcY]
      with ω hq hy
    exact hq.sub hy
  simpa only [MartingaleSpatialLimit.finiteSum, Pi.sub_apply] using
    MartingaleRandomEvaluation.integral_sq_random_evaluation_le
      ((MartingaleSpatialLimit.finiteSum_martingale hI q).sub hY)
      (fun t => (MartingaleSpatialLimit.finiteSum_memLp hI2 q t).sub (hY2 t))
      hc (hr q) (hb q)

theorem exists_hasSum_random_evaluation
    (hI : ∀ a, Martingale (I a) F P) (hY : Martingale Y F P)
    (hI2 : ∀ a t, MemLp (I a t) 2 P) (hY2 : ∀ t, MemLp (Y t) 2 P)
    (hcI : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => I a t ω))
    (hcY : ∀ᵐ ω ∂P, Continuous (fun t => Y t ω))
    (T : ℝ≥0)
    (hsum : HasSum (fun a => (hI2 a T).toLp (I a T)) ((hY2 T).toLp (Y T)))
    (r : Ω → ℝ≥0) (hr : Measurable r) (hb : ∀ ω, r ω ≤ T) :
    ∃ (hIr : ∀ a, MemLp (fun ω => I a (r ω) ω) 2 P)
      (hYr : MemLp (fun ω => Y (r ω) ω) 2 P),
      HasSum (fun a => (hIr a).toLp (fun ω => I a (r ω) ω))
        (hYr.toLp (fun ω => Y (r ω) ω)) := by
  classical
  have hIr (a : ι) : MemLp (fun ω => I a (r ω) ω) 2 P :=
    MartingaleRandomEvaluation.memLp_random_evaluation (hI a) (hI2 a) (hcI a) hr hb
  have hYr : MemLp (fun ω => Y (r ω) ω) 2 P :=
    MartingaleRandomEvaluation.memLp_random_evaluation hY hY2 hcY hr hb
  refine ⟨hIr, hYr, ?_⟩
  have hl := (SimpleIntegral.tendsto_toLp_iff_meanSquare
    (fun q : Finset ι => memLp_finsetSum q (fun a _ => hIr a)) hYr).mpr
      (tendsto_finiteSum_random_evaluation hI hY hI2 hY2 hcI hcY T hsum
        (fun _ => r) (fun _ => hr) (fun _ => hb))
  change Tendsto (fun q : Finset ι => ∑ a ∈ q, (hIr a).toLp (fun ω => I a (r ω) ω))
    atTop (𝓝 (hYr.toLp (fun ω => Y (r ω) ω)))
  exact hl.congr (fun q => PredictableL2.toLp_finsetSum
    (fun a ω => I a (r ω) ω) hIr q)

theorem exists_hasSum_stoppedProcess
    (hI : ∀ a, Martingale (I a) F P) (hY : Martingale Y F P)
    (hI2 : ∀ a t, MemLp (I a t) 2 P) (hY2 : ∀ t, MemLp (Y t) 2 P)
    (hcI : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => I a t ω))
    (hcY : ∀ᵐ ω ∂P, Continuous (fun t => Y t ω))
    (T : ℝ≥0)
    (hsum : HasSum (fun a => (hI2 a T).toLp (I a T)) ((hY2 T).toLp (Y T)))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    {t : ℝ≥0} (ht : t ≤ T) :
    ∃ (hIs : ∀ a, MemLp (stoppedProcess (I a) τ t) 2 P)
      (hYs : MemLp (stoppedProcess Y τ t) 2 P),
      HasSum (fun a => (hIs a).toLp (stoppedProcess (I a) τ t))
        (hYs.toLp (stoppedProcess Y τ t)) := by
  exact exists_hasSum_random_evaluation hI hY hI2 hY2 hcI hcY T hsum
    (fun ω => (min (t : WithTop ℝ≥0) (τ ω)).untopA)
    (WithTop.measurable_untopA.comp
      (measurable_const.min (hτ.measurable.mono hτ.measurableSpace_le le_rfl)))
    (fun ω => (WithTop.untopA_le (min_le_left _ _)).trans ht)

end Problem367.MartingaleSpatialRandomEvaluation

end

end OAI
