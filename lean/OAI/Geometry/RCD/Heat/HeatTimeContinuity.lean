import OAI.Geometry.RCD.Heat.AveragedHeatSource

namespace OAI

/-! # Positive-time continuity derived from the actual heat semigroup -/

open Set MeasureTheory
open scoped InnerProductSpace Topology ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)

/-- Moving time into the L2 heat flow leaves a fixed positive kernel row. -/
theorem kernelHeat_eq_delayed {a t : ℝ} (ha : 0 < a) (hat : a < t)
    (f : Lp ℝ 2 μ) (x : X) :
    kernelHeat μ hQ hk t f x =
      ⟪heatKernelRow μ hQ hk a x, heatAt μ hQ (t - a) f⟫_ℝ := by
  rw [← heatAt_inner, heatKernelRow_evolves μ hQ hk (sub_pos.mpr hat) ha]
  simp only [sub_add_cancel, kernelHeat]

/-- Positive-time continuity requires no extra time-regularity hypothesis
on the published kernel representative. -/
theorem kernelHeat_continuousOn_time_space (f : Lp ℝ 2 μ) :
    ContinuousOn (fun tz : ℝ × X => kernelHeat μ hQ hk tz.1 f tz.2) (Ioi 0 ×ˢ univ) := by
  intro tz htz
  have ht : 0 < tz.1 := htz.1
  let a := tz.1 / 2
  have ha : 0 < a := half_pos ht
  have hat : a < tz.1 := by dsimp [a]; linarith
  have hc : Continuous (fun sz : ℝ × X =>
      ⟪heatKernelRow μ hQ hk a sz.2, heatAt μ hQ (sz.1 - a) f⟫_ℝ) :=
    ((heatKernelRow_continuous μ hQ hk ha).comp continuous_snd).inner
      ((heatAt_continuous μ hQ f).comp (continuous_fst.sub continuous_const))
  apply ContinuousAt.continuousWithinAt
  apply hc.continuousAt.congr_of_eventuallyEq
  filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hat)] with sz hsz
  exact kernelHeat_eq_delayed μ hQ hk ha hsz f sz.2

include hk in
/-- The kernel at a fixed first pole is jointly continuous in positive
time and its second pole. -/
theorem kernel_continuousOn_time_right (x : X) :
    ContinuousOn (fun tz : ℝ × X => ker tz.1 x tz.2) (Ioi 0 ×ˢ univ) := by
  intro tz htz
  have ht : 0 < tz.1 := htz.1
  let a := tz.1 / 2
  have ha : 0 < a := half_pos ht
  have hat : a < tz.1 := by dsimp [a]; linarith
  have hc := (kernelHeat_continuousOn_time_space μ hQ hk (heatKernelRow μ hQ hk a x))
  have hm : Continuous (fun sz : ℝ × X => (sz.1 - a, sz.2)) :=
    (continuous_fst.sub continuous_const).prodMk continuous_snd
  have ht' : (tz.1 - a, tz.2) ∈ Ioi 0 ×ˢ (univ : Set X) := ⟨sub_pos.mpr hat, mem_univ _⟩
  have heq : ∀ sz : ℝ × X, a < sz.1 →
      kernelHeat μ hQ hk (sz.1 - a) (heatKernelRow μ hQ hk a x) sz.2 = ker sz.1 x sz.2 := by
    intro sz hs
    rw [kernelHeat, heatKernelRow_inner μ hQ hk (sub_pos.mpr hs) ha]
    simp only [sub_add_cancel, hk.symmetric sz.1 (ha.trans hs)]
  have hcont := (hc _ ht').continuousAt
    (isOpen_Ioi.prod isOpen_univ |>.mem_nhds ht')
  apply ContinuousAt.continuousWithinAt
  have hc' : ContinuousAt (fun sz : ℝ × X =>
      kernelHeat μ hQ hk (sz.1 - a) (heatKernelRow μ hQ hk a x) sz.2) tz :=
    hcont.comp (f := fun sz : ℝ × X => (sz.1 - a, sz.2)) (x := tz) hm.continuousAt
  apply hc'.congr_of_eventuallyEq
  filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hat)] with sz hsz
  exact (heq sz hsz).symm

include hk in
/-- The same joint continuity holds for the actual average kernel. -/
theorem kernelAverage_continuousOn_time_space (A : Set X)
    (hA : MeasurableSet A) (hAt : μ A ≠ ⊤) :
    ContinuousOn (fun tz : ℝ × X => kernelAverage μ ker tz.1 A tz.2) (Ioi 0 ×ˢ univ) := by
  apply (kernelHeat_continuousOn_time_space μ hQ hk (uniformDensityLp μ A hA hAt)).congr
  intro tz htz
  exact kernelAverage_eq_kernelHeat μ hQ hk htz.1 A hA hAt tz.2

end RegularPointCoordinates

end

end OAI
