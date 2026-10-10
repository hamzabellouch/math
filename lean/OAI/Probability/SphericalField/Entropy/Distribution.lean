import Mathlib
import OAI.Probability.SphericalField.Model

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
def realTail (μ : Measure Time) (x : ℝ) : ℝ :=
  ∫ s, 1 - max x (s : ℝ) ∂μ

def realCDF (μ : Measure Time) (x : ℝ) : ℝ := μ.real {s : Time | (s : ℝ) ≤ x}

lemma continuous_time_integrable (μ : Measure Time) [IsFiniteMeasure μ]
    {f : Time → ℝ} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma realTail_integrable (μ : Measure Time) [IsFiniteMeasure μ] (x : ℝ) :
    Integrable (fun s : Time => 1 - max x (s : ℝ)) μ :=
  continuous_time_integrable μ (by fun_prop)

lemma hasDerivWithinAt_max_right (x s : ℝ) :
    HasDerivWithinAt (fun y => max y s) (if s ≤ x then 1 else 0) (Ioi x) x := by
  split_ifs with h
  · exact (hasDerivAt_id x).hasDerivWithinAt.congr
      (fun y hy => max_eq_left (h.trans (le_of_lt hy))) (max_eq_left h)
  · have hd : HasDerivAt (fun y => max y s) 0 x := by
      apply (hasDerivAt_const x s).congr_of_eventuallyEq
      filter_upwards [gt_mem_nhds (lt_of_not_ge h)] with y hy
      exact max_eq_right (le_of_lt hy)
    exact hd.hasDerivWithinAt

lemma realTail_right_derivative (μ : Measure Time) [IsFiniteMeasure μ] (x : ℝ) :
    HasDerivWithinAt (realTail μ) (-realCDF μ x) (Ioi x) x := by
  have hlim (s : Time) :
      Tendsto (slope (fun y => 1 - max y (s : ℝ)) x) (𝓝[Ioi x] x)
        (𝓝 (-(if (s : ℝ) ≤ x then 1 else 0))) := by
    have hd := (hasDerivAt_const x (1 : ℝ)).hasDerivWithinAt.sub
      (hasDerivWithinAt_max_right x (s : ℝ))
    change HasDerivWithinAt (fun y => 1 - max y (s : ℝ))
      (0 - (if (s : ℝ) ≤ x then 1 else 0)) (Ioi x) x at hd
    have hh := hasDerivWithinAt_iff_tendsto_slope.mp hd
    simpa using hh
  have hint : (∫ s : Time, -(if (s : ℝ) ≤ x then 1 else 0) ∂μ) = -realCDF μ x := by
    rw [integral_neg]
    congr 1
    change (∫ s : Time, {s : Time | (s : ℝ) ≤ x}.indicator (fun _ => (1 : ℝ)) s ∂μ) = _
    rw [integral_indicator (measurableSet_le (by fun_prop) measurable_const)]
    simp [realCDF]
  apply hasDerivWithinAt_iff_tendsto_slope.mpr
  have hd := tendsto_integral_filter_of_dominated_convergence (μ := μ)
    (F := fun y (s : Time) => slope (fun z => 1 - max z (s : ℝ)) x y)
    (fun _ => (1 : ℝ))
    (Eventually.of_forall fun y => by unfold slope; fun_prop)
    (by
      filter_upwards [self_mem_nhdsWithin] with y hy
      filter_upwards [] with s
      rw [slope_def_field, Real.norm_eq_abs, abs_div]
      have h := abs_max_sub_max_le_max y (s : ℝ) x (s : ℝ)
      simp only [sub_self, abs_zero, max_eq_left (abs_nonneg (y - x))] at h
      have he : |(1 - max y (s : ℝ)) - (1 - max x (s : ℝ))| =
          |max y (s : ℝ) - max x (s : ℝ)| := by
        rw [show (1 - max y (s : ℝ)) - (1 - max x (s : ℝ)) =
          -(max y (s : ℝ) - max x (s : ℝ)) by ring, abs_neg]
      rw [he]
      exact (div_le_one (abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt hy)))).mpr h)
    (integrable_const _) (Eventually.of_forall hlim)
  rw [hint] at hd
  convert hd using 1
  · ext y
    rw [slope_def_field, realTail, realTail, ← integral_sub (realTail_integrable μ y)
    (realTail_integrable μ x), ← integral_div]
    simp only [slope_def_field]
  · simp

lemma abs_realTail_sub_le (μ : Measure Time) [IsProbabilityMeasure μ] (x y : ℝ) :
    |realTail μ x - realTail μ y| ≤ |x - y| := by
  rw [realTail, realTail, ← integral_sub (realTail_integrable μ x) (realTail_integrable μ y)]
  have hh := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun s : Time => (1 - max x (s : ℝ)) - (1 - max y (s : ℝ)))
    (C := |x - y|) (Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, show (1 - max x (s : ℝ)) - (1 - max y (s : ℝ)) =
        -(max x (s : ℝ) - max y (s : ℝ)) by ring, abs_neg]
      simpa using abs_max_sub_max_le_max x (s : ℝ) y (s : ℝ))
  simpa using hh

lemma realTail_continuous (μ : Measure Time) [IsProbabilityMeasure μ] :
    Continuous (realTail μ) := by
  have h : LipschitzWith 1 (realTail μ) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simpa [Real.dist_eq] using abs_realTail_sub_le μ x y
  exact h.continuous

lemma realCDF_monotone (μ : Measure Time) [IsFiniteMeasure μ] :
    Monotone (realCDF μ) := by
  intro x y hxy
  exact measureReal_mono (fun _ hs => hs.trans hxy)

lemma realCDF_integrable (μ : Measure Time) [IsFiniteMeasure μ] (a b : ℝ) :
    IntervalIntegrable (realCDF μ) volume a b :=
  (realCDF_monotone μ).intervalIntegrable

lemma integral_cdf_mul (μ : Measure Time) [IsFiniteMeasure μ] {r : ℝ} (hr : 0 ≤ r)
    {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 r) :
    (∫ t in 0..r, realCDF μ t * f t) =
      ∫ s : Time, if (s : ℝ) ≤ r then ∫ t in (s : ℝ)..r, f t else 0 ∂μ := by
  let ν : Measure ℝ := volume.restrict (Icc 0 r)
  have hfi : Integrable f ν := (intervalIntegrable_iff_integrableOn_Icc_of_le hr).mp hf
  have hmeas : MeasurableSet {p : ℝ × Time | (p.2 : ℝ) ≤ p.1} :=
    measurableSet_le (by fun_prop) measurable_fst
  have hbase : Integrable (fun p : ℝ × Time => f p.1) (ν.prod μ) := by
    simpa using hfi.mul_prod (integrable_const (1 : ℝ) (μ := μ))
  have hswap := integral_integral_swap (μ := ν) (ν := μ)
    (f := fun t s => {p : ℝ × Time | (p.2 : ℝ) ≤ p.1}.indicator (fun p => f p.1) (t, s))
    (hbase.indicator hmeas)
  have hleft (t : ℝ) :
      (∫ s : Time, {p : ℝ × Time | (p.2 : ℝ) ≤ p.1}.indicator
        (fun p => f p.1) (t, s) ∂μ) = realCDF μ t * f t := by
    change (∫ s : Time, {s : Time | (s : ℝ) ≤ t}.indicator (fun _ => f t) s ∂μ) = _
    rw [integral_indicator (measurableSet_le (by fun_prop) measurable_const)]
    simp [realCDF]
  have hright (s : Time) :
      (∫ t, {p : ℝ × Time | (p.2 : ℝ) ≤ p.1}.indicator
        (fun p => f p.1) (t, s) ∂ν) =
        if (s : ℝ) ≤ r then ∫ t in (s : ℝ)..r, f t else 0 := by
    change (∫ t, (Ici (s : ℝ)).indicator f t ∂ν) = _
    rw [integral_indicator measurableSet_Ici]
    have hset : Icc 0 r ∩ Ici (s : ℝ) = Icc (s : ℝ) r := by
      ext t
      simp only [mem_inter_iff, mem_Icc, mem_Ici]
      constructor
      · intro h; exact ⟨h.2, h.1.2⟩
      · intro h; exact ⟨⟨s.property.1.trans h.1, h.2⟩, h.1⟩
    dsimp only [ν]
    rw [Measure.restrict_restrict measurableSet_Ici, inter_comm, hset]
    split_ifs with hs
    · rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hs]
    · simp [Icc_eq_empty_of_lt (lt_of_not_ge hs)]
  have hl : (∫ (t : ℝ), realCDF μ t * f t ∂ν) = ∫ t in 0..r, realCDF μ t * f t := by
    dsimp only [ν]
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hr]
  simpa only [Function.uncurry_apply_pair, hleft, hright, hl] using hswap

lemma realTail_lower (μ : Measure Time) [IsProbabilityMeasure μ] {B x : ℝ}
    (hμ : ∀ᵐ s : Time ∂μ, (s : ℝ) ≤ B) (hx : x ≤ B) :
    1 - B ≤ realTail μ x := by
  calc
    _ = ∫ _ : Time, 1 - B ∂μ := by simp
    _ ≤ _ := integral_mono_ae (integrable_const _) (realTail_integrable μ x) (by
      filter_upwards [hμ] with s hs
      exact sub_le_sub_left (max_le hx hs) 1)

end SphericalPerceptron
end
end

end OAI
