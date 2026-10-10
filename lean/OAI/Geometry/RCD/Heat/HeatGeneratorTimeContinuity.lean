import OAI.Geometry.RCD.Heat.HeatTimeContinuity
import OAI.Geometry.RCD.Heat.KernelHeatGeneratorDerivative

namespace OAI

/-! # Joint positive-time continuity of the actual heat source

A fixed positive-time kernel row transfers continuity of the L2 heat
generator to the pointwise source, including its spatial variable.
-/

open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (Q : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ Q ker)

theorem kernelHeatGeneratorSource_eq_delayed {a t : ℝ} (ha : 0 < a) (hat : a < t)
    (f : Lp ℝ 2 μ) (x : X) :
    kernelHeatGeneratorSource μ Q hk t f x =
      inner ℝ (heatKernelRow μ Q hk a x) (-heatGeneratorAt μ Q (t-a) f) := by
  have hd := (hasDerivAt_const t (heatKernelRow μ Q hk a x)).inner ℝ
    ((heatAt_hasDerivAt μ Q (t-a) (sub_pos.mpr hat) f).scomp t
      ((hasDerivAt_id t).sub_const a))
  have hd' : HasDerivAt
      (fun s => inner ℝ (heatKernelRow μ Q hk a x) (heatAt μ Q (s-a) f))
      (inner ℝ (heatKernelRow μ Q hk a x) (-heatGeneratorAt μ Q (t-a) f)) t := by
    simpa only [inner_zero_left,add_zero,one_smul,Function.comp_def,id_eq] using hd
  have he : HasDerivAt (fun s => kernelHeat μ Q hk s f x)
      (inner ℝ (heatKernelRow μ Q hk a x) (-heatGeneratorAt μ Q (t-a) f)) t := by
    apply hd'.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hat] with s hs
    exact kernelHeat_eq_delayed μ Q hk ha hs f x
  exact (kernelHeat_generator_hasDerivAt μ Q hk f (ha.trans hat) x).unique he

theorem kernelHeatGeneratorSource_continuousOn_time_space (f : Lp ℝ 2 μ) :
    ContinuousOn (fun tx : ℝ × X => kernelHeatGeneratorSource μ Q hk tx.1 f tx.2)
      (Ioi 0 ×ˢ univ) := by
  intro tx htx
  have ht : 0 < tx.1 := htx.1
  let a := tx.1/2
  have ha : 0 < a := half_pos ht
  have hat : a < tx.1 := by dsimp only [a]; linarith
  have htime : ContinuousAt (fun sx : ℝ × X => sx.1-a) tx :=
    (continuous_fst.sub continuous_const).continuousAt
  have hg : ContinuousAt (fun sx : ℝ × X => -heatGeneratorAt μ Q (sx.1-a) f) tx :=
    ((heatGeneratorAt_continuousAt μ Q f (tx.1-a) (sub_pos.mpr hat)).comp
      (f := fun sx : ℝ × X => sx.1-a) (x := tx) htime).neg
  have hc : ContinuousAt (fun sx : ℝ × X =>
      inner ℝ (heatKernelRow μ Q hk a sx.2) (-heatGeneratorAt μ Q (sx.1-a) f)) tx :=
    ((heatKernelRow_continuous μ Q hk ha).comp continuous_snd).continuousAt.inner hg
  apply ContinuousAt.continuousWithinAt
  apply hc.congr_of_eventuallyEq
  filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hat)] with sx hsx
  exact kernelHeatGeneratorSource_eq_delayed μ Q hk ha hsx f sx.2

theorem kernelHeat_log_derivative_continuousOn (f : Lp ℝ 2 μ)
    {U : Set (ℝ × X)} (hU : U ⊆ Ioi 0 ×ˢ univ)
    (hpos : ∀ tx ∈ U, kernelHeat μ Q hk tx.1 f tx.2 ≠ 0) :
    ContinuousOn (fun tx : ℝ × X =>
      kernelHeatGeneratorSource μ Q hk tx.1 f tx.2 / kernelHeat μ Q hk tx.1 f tx.2) U :=
  ((kernelHeatGeneratorSource_continuousOn_time_space μ Q hk f).mono hU).div
    ((kernelHeat_continuousOn_time_space μ Q hk f).mono hU) hpos

end RegularPointCoordinates

end

end OAI
