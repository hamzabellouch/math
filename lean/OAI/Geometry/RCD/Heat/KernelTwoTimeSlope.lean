import OAI.Geometry.RCD.Heat.HeatPointwiseTwoTimeDual
import OAI.Geometry.RCD.Heat.KernelHeatOrder

namespace OAI

/-! # The two-time quadratic bound with the actual local slope of the datum -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X]

theorem NoncollapsedRCD.kernel_two_time_slope_bound
    (K : ℝ) (n : ℕ) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (hK : K ≤ 0) {N : ℝ} (hN : (n:ℝ) ≤ N)
    {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ)
    (p : X) (R : ℝ) (hsupp : ∀ x, R < dist p x → φ x = 0)
    (f H : Lp ℝ 2 (hausdorff n X)) (hf : φ =ᵐ[hausdorff n X] f)
    {r σ s t : ℝ} (hσ : 0 < σ) (hr : 2*σ*(L:ℝ) < r)
    (hH : (fun x => (slopeAtScale φ r x).toReal^2) =ᵐ[hausdorff n X] H)
    (hs : 0 < s) (ht : 0 < t) (x y : X) :
    kernelHeat (hausdorff n X) hX.quadratic hk s f x-
      kernelHeat (hausdorff n X) hX.quadratic hk t f y ≤
    σ/2*kernelHeat (hausdorff n X) hX.quadratic hk s H x+
      Real.exp (-K*(s+t))*(dist x y^2+2*N*(Real.sqrt s-Real.sqrt t)^2)/(2*σ) := by
  let μ := hausdorff n X
  have hψ := hopfLax_lipschitz hφ hX.geodesic hσ
  have hm := hopfLax_compact_memLp μ hX.geodesic hφ p R hsupp hσ
  let g : Lp ℝ 2 μ := hm.toLp (hopfLax φ σ)
  have hg : hopfLax φ σ =ᵐ[μ] g := hm.coeFn_toLp.symm
  let M := |φ p|+(L:ℝ)*max R 0
  have hM : ∀ x, |φ x| ≤ M := compact_lipschitz_abs_bound hφ p R hsupp
  have hB : ∀ x, |hopfLax φ σ x| ≤ M+σ*(L:ℝ)^2/2 := by
    intro z
    have hb := hopfLax_bounds hφ hσ z
    have hm := abs_le.mp (hM z)
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (L:ℝ)]
  have hdual := hX.heat_pointwise_two_time_dual K n hn hK hN f g hφ.continuous.measurable
    hψ.continuous.measurable hf hg M _ hM hB (by positivity : 0 ≤ 1/(2*σ))
    (fun z w => by
      have hh := hopfLax_le_cost hφ hσ z w
      simp only [div_eq_mul_inv,one_mul] at hh ⊢
      nlinarith [hh]) hs ht
    (kernelHeat μ hX.quadratic hk s g) (kernelHeat μ hX.quadratic hk t f)
    (kernelHeat_continuous μ hX.quadratic hk hs g) (kernelHeat_continuous μ hX.quadratic hk ht f)
    (kernelHeat_represents_L2 μ hX.quadratic hk hs g).symm
    (kernelHeat_represents_L2 μ hX.quadratic hk ht f).symm
  have hle : f-g ≤ (σ/2) • H := by
    apply (Lp.coeFn_le _ _).mp
    filter_upwards [hf,hg,hH,Lp.coeFn_sub f g,Lp.coeFn_smul (σ/2) H] with z hf hg hH hfg hsH
    rw [hfg,hsH]
    change f z-g z ≤ σ/2*H z
    rw [←hf,←hg,←hH]
    have hh := hopfLax_gap_le_scale hφ hσ hr z
    nlinarith [hh]
  have hp := kernelHeat_mono μ hX.quadratic hk hs hle x
  rw [kernelHeat_sub,kernelHeat_smul] at hp
  calc
    _ = (kernelHeat μ hX.quadratic hk s f x-kernelHeat μ hX.quadratic hk s g x)+
        (kernelHeat μ hX.quadratic hk s g x-kernelHeat μ hX.quadratic hk t f y) := by ring
    _ ≤ σ/2*kernelHeat μ hX.quadratic hk s H x+
        1/(2*σ)*Real.exp (-K*(s+t))*(dist x y^2+2*N*(Real.sqrt s-Real.sqrt t)^2) :=
      add_le_add hp (hdual x y)
    _ = _ := by ring

end RegularPointCoordinates

end

end OAI
