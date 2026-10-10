import OAI.Probability.FreeIsing.Brownian.UniformGrid
import OAI.Probability.FreeIsing.Stochastic.RandomRiemannCompensator

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace Problem367.SelectedCompensator

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

def squareSum (H : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n,
    ((min t (BrownianGrid.uniformGrid T n (i + 1)) : ℝ) -
      (min t (BrownianGrid.uniformGrid T n i) : ℝ)) *
        (H (BrownianGrid.uniformGrid T n i) ω) ^ 2

theorem coe_uniformGrid (T : ℝ≥0) (n i : ℕ) :
    (BrownianGrid.uniformGrid T n i : ℝ) = EnergyRiemann.point T n i := by
  simp only [BrownianGrid.uniformGrid, NNReal.coe_div, NNReal.coe_mul,
    NNReal.coe_natCast, EnergyRiemann.point]
  ring

omit mΩ in
theorem squareSum_eq_stoppedSum (H : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) :
    squareSum H T n t = fun ω => RandomRiemann.stoppedSum
      (fun s => (H s.toNNReal ω) ^ 2) T t n := by
  funext ω
  unfold squareSum RandomRiemann.stoppedSum RandomRiemann.stoppedPoint
  apply Finset.sum_congr rfl
  intro i hi
  simp only [← coe_uniformGrid, Real.toNNReal_coe]

theorem squareSum_stronglyAdapted {F : Filtration ℝ≥0 mΩ}
    {H : ℝ≥0 → Ω → ℝ} (hH : StronglyAdapted F H) (T : ℝ≥0) (n : ℕ) :
    StronglyAdapted F (squareSum H T n) := by
  intro t
  unfold squareSum
  apply Finset.stronglyMeasurable_fun_sum
  intro i hi
  by_cases hit : BrownianGrid.uniformGrid T n i ≤ t
  · exact (((hH _).mono (F.mono hit)).pow 2).const_mul _
  · have hti : t ≤ BrownianGrid.uniformGrid T n i := le_of_not_ge hit
    have hti' := hti.trans (BrownianGrid.uniformGrid_mono T n (Nat.le_succ i))
    have htiR : (t : ℝ) ≤ (BrownianGrid.uniformGrid T n i : ℝ) := hti
    have htiR' : (t : ℝ) ≤ (BrownianGrid.uniformGrid T n (i+1) : ℝ) := hti'
    simpa only [min_eq_left htiR, min_eq_left htiR', sub_self, zero_mul] using
      (stronglyMeasurable_const : StronglyMeasurable[F t] (fun _ : Ω => (0 : ℝ)))

def selected (H : ℝ≥0 → Ω → ℝ) (T t : ℝ≥0) (ω : Ω) : ℝ :=
  limUnder atTop (fun n => squareSum H T n t ω)

theorem selected_stronglyAdapted {F : Filtration ℝ≥0 mΩ}
    {H : ℝ≥0 → Ω → ℝ} (hH : StronglyAdapted F H) (T : ℝ≥0) :
    StronglyAdapted F (selected H T) := by
  intro t
  have hm (n : ℕ) := squareSum_stronglyAdapted hH T n t
  let : MeasurableSpace Ω := F t
  exact StronglyMeasurable.limUnder hm

omit mΩ in
theorem selected_eq_integral_of_continuous {H : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (fun s => H s ω)) (T t : ℝ≥0) :
    selected H T t ω = ∫ s in (0 : ℝ)..min (t : ℝ) T, (H s.toNNReal ω) ^ 2 := by
  apply Filter.Tendsto.limUnder_eq
  have hcR : Continuous (fun s : ℝ => (H s.toNNReal ω) ^ 2) := by fun_prop
  have h := RandomRiemann.tendsto_stoppedSum hcR T.coe_nonneg t.coe_nonneg
  simpa only [squareSum_eq_stoppedSum, Function.comp_apply, Pi.pow_apply] using h

theorem ae_selected_eq_integral {μ : Measure Ω} {H : ℝ≥0 → Ω → ℝ}
    (hc : ∀ᵐ ω ∂μ, Continuous (fun s => H s ω)) (T : ℝ≥0) :
    ∀ᵐ ω ∂μ, ∀ t, selected H T t ω =
      ∫ s in (0 : ℝ)..min (t : ℝ) T, (H s.toNNReal ω) ^ 2 := by
  filter_upwards [hc] with ω hω
  exact selected_eq_integral_of_continuous hω T

theorem ae_continuous_selected {μ : Measure Ω} {H : ℝ≥0 → Ω → ℝ}
    (hc : ∀ᵐ ω ∂μ, Continuous (fun s => H s ω)) (T : ℝ≥0) :
    ∀ᵐ ω ∂μ, Continuous (fun t => selected H T t ω) := by
  filter_upwards [hc] with ω hω
  have hf : Continuous (fun s : ℝ => (H s.toNNReal ω) ^ 2) := by fun_prop
  have hp := intervalIntegral.continuous_primitive (μ := volume)
    (fun a b => hf.intervalIntegrable a b) (0 : ℝ)
  have heq : (fun t => selected H T t ω) =
      fun t : ℝ≥0 => ∫ s in (0 : ℝ)..min (t : ℝ) T, (H s.toNNReal ω) ^ 2 := by
    funext t
    exact selected_eq_integral_of_continuous hω T t
  rw [heq]
  exact hp.comp (by fun_prop)

omit mΩ in
@[simp] theorem selected_zero (H : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) :
    selected H T 0 ω = 0 := by
  apply Filter.Tendsto.limUnder_eq
  simp [squareSum]

omit mΩ in
theorem abs_squareSum_le {H : ℝ≥0 → Ω → ℝ} {ω : Ω} {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ s, |H s ω| ≤ C) (T t : ℝ≥0) (n : ℕ) :
    |squareSum H T n t ω| ≤ C ^ 2 * min (t : ℝ) T := by
  rw [squareSum_eq_stoppedSum]
  apply RandomRiemann.abs_stoppedSum_le T.coe_nonneg t.coe_nonneg
  intro s
  rw [abs_of_nonneg (sq_nonneg _)]
  nlinarith [hb s.toNNReal, abs_nonneg (H s.toNNReal ω), sq_abs (H s.toNNReal ω)]

omit mΩ in
theorem abs_selected_le {H : ℝ≥0 → Ω → ℝ} {ω : Ω} {C : ℝ}
    (hc : Continuous (fun s => H s ω))
    (hC : 0 ≤ C) (hb : ∀ s, |H s ω| ≤ C) (T t : ℝ≥0) :
    |selected H T t ω| ≤ C ^ 2 * min (t : ℝ) T := by
  rw [selected_eq_integral_of_continuous hc T t, ← Real.norm_eq_abs]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := min (t : ℝ) T) (C := C ^ 2)
    (f := fun s : ℝ => (H s.toNNReal ω) ^ 2) (fun s _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [hb s.toNNReal, abs_nonneg (H s.toNNReal ω), sq_abs (H s.toNNReal ω)])
  simpa only [sub_zero, abs_of_nonneg (le_min t.coe_nonneg T.coe_nonneg)] using h

theorem squareSum_memLp {μ : Measure Ω} [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {H : ℝ≥0 → Ω → ℝ}
    (hH : StronglyAdapted F H) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ ω ∂μ, ∀ s, |H s ω| ≤ C) (T t : ℝ≥0) (n : ℕ) (p : ℝ≥0∞) :
    MemLp (squareSum H T n t) p μ := by
  apply MemLp.of_bound (squareSum_stronglyAdapted hH T n).stronglyMeasurable.aestronglyMeasurable
    (C ^ 2 * min (t : ℝ) T)
  filter_upwards [hb] with ω hω
  simpa only [Real.norm_eq_abs] using abs_squareSum_le hC hω T t n

theorem selected_memLp {μ : Measure Ω} [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {H : ℝ≥0 → Ω → ℝ}
    (hH : StronglyAdapted F H) (hc : ∀ᵐ ω ∂μ, Continuous (fun s => H s ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂μ, ∀ s, |H s ω| ≤ C)
    (T t : ℝ≥0) (p : ℝ≥0∞) : MemLp (selected H T t) p μ := by
  apply MemLp.of_bound (selected_stronglyAdapted hH T).stronglyMeasurable.aestronglyMeasurable
    (C ^ 2 * min (t : ℝ) T)
  filter_upwards [hc, hb] with ω hcω hbω
  simpa only [Real.norm_eq_abs] using abs_selected_le hcω hC hbω T t

omit mΩ in
theorem selected_monotone_of_continuous {H : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (fun s => H s ω)) (T : ℝ≥0) :
    Monotone (fun t => selected H T t ω) := by
  intro s t hst
  change selected H T s ω ≤ selected H T t ω
  rw [selected_eq_integral_of_continuous hc T s, selected_eq_integral_of_continuous hc T t]
  have hf : Continuous (fun r : ℝ => (H r.toNNReal ω) ^ 2) := by fun_prop
  apply intervalIntegral.integral_mono_interval le_rfl
    (le_min s.coe_nonneg T.coe_nonneg)
    (min_le_min_right _ (show (s : ℝ) ≤ t from hst))
  · exact Filter.Eventually.of_forall (fun r => sq_nonneg _)
  · exact hf.intervalIntegrable _ _

omit mΩ in
theorem abs_selected_sub_le {H : ℝ≥0 → Ω → ℝ} {ω : Ω} {C : ℝ}
    (hc : Continuous (fun s => H s ω))
    (hC : 0 ≤ C) (hb : ∀ s, |H s ω| ≤ C) (T s t : ℝ≥0) :
    |selected H T t ω - selected H T s ω| ≤ C ^ 2 * |(t : ℝ) - s| := by
  rw [selected_eq_integral_of_continuous hc T t, selected_eq_integral_of_continuous hc T s]
  have hf : Continuous (fun r : ℝ => (H r.toNNReal ω) ^ 2) := by fun_prop
  rw [intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := min (s : ℝ) T) (b := min (t : ℝ) T) (C := C ^ 2)
    (f := fun r : ℝ => (H r.toNNReal ω) ^ 2) (fun r _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [hb r.toNNReal, abs_nonneg (H r.toNNReal ω), sq_abs (H r.toNNReal ω)])
  rw [Real.norm_eq_abs] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg C))
  simpa only [sub_self, abs_zero, max_eq_left (abs_nonneg ((t : ℝ) - s))] using
    abs_min_sub_min_le_max (t : ℝ) T (s : ℝ) T

theorem tendsto_squareSum_L1_selected
    {μ : Measure Ω} [IsFiniteMeasure μ] {H : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, AEStronglyMeasurable (H t) μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂μ, ∀ s, |H s ω| ≤ C) (T t : ℝ≥0) :
    Tendsto (fun n => eLpNorm (squareSum H T n t - selected H T t) 1 μ)
      atTop (𝓝 0) := by
  have h := RandomRiemann.tendsto_stoppedSquareSum_L1_nnreal hm hc hC hb T t
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro n
  apply eLpNorm_congr_ae
  filter_upwards [ae_selected_eq_integral hc T] with ω hω
  simp only [Pi.sub_apply, squareSum_eq_stoppedSum, hω t]

end Problem367.SelectedCompensator

end

end OAI
