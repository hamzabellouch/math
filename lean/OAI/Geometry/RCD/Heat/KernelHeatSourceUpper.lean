import OAI.Geometry.RCD.Heat.KernelHeatComplementMonotone
import OAI.Geometry.RCD.Coordinates.KernelHeatBoundedRegularity

namespace OAI

/-! # A two-sided bound for the source of nonnegative bounded heat data -/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn p in
theorem kernelHeat_source_upper (hK : K ≤ 0)
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (f : Lp ℝ 2 (hausdorff n X)) (hf0 : 0 ≤ f) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {t : ℝ} (ht : 0 < t) (x : X) :
    kernelHeatGeneratorSource (hausdorff n X) hX.quadratic hk t f x ≤
      (n:ℝ)*(|K|+1/t)*((A:ℝ)-kernelHeat (hausdorff n X) hX.quadratic hk t f x) := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let H := fun s => kernelHeat μ Q hk s f x
  let E := fun s => Real.exp ((n:ℝ)*(Real.log s+|K| * s))
  let D := kernelHeatGeneratorSource μ Q hk t f x
  have hE := (((Real.hasDerivAt_log ht.ne').add
    ((hasDerivAt_id t).const_mul |K|)).const_mul (n:ℝ)).exp
  have hH := kernelHeat_generator_hasDerivAt μ Q hk f ht x
  have hd : HasDerivAt (fun s => E s*((A:ℝ)-H s))
      (E t*((n:ℝ)*(|K|+1/t)*((A:ℝ)-H t)-D)) t := by
    convert hE.mul ((hasDerivAt_const t (A:ℝ)).sub hH) using 1
    · rfl
    · simp only [E,H,D,Pi.sub_apply,Pi.add_apply,id_eq,mul_one,one_div]
      ring
  have hm := hX.kernelHeat_complement_monotone hn p hK hk f hf0 A hf x
  have hnonneg := hm.derivWithin_nonneg (x:=t)
  rw [derivWithin_of_isOpen isOpen_Ioi ht,hd.deriv] at hnonneg
  have hz := nonneg_of_mul_nonneg_right hnonneg (Real.exp_pos _)
  dsimp only [D,H] at hz
  linarith only [hz]

include hn p in
theorem kernelHeat_source_abs_bound_nonneg (hK : K ≤ 0)
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (f : Lp ℝ 2 (hausdorff n X)) (hf0 : 0 ≤ f) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {t : ℝ} (ht : 0 < t) (x : X) :
    |kernelHeatGeneratorSource (hausdorff n X) hX.quadratic hk t f x| ≤
      (n:ℝ)*(|K|+1/t)*(A:ℝ) := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  have hlo := hX.kernelHeat_source_lower hn p hK hk f hf0 A hf ht x
  have hup := hX.kernelHeat_source_upper hn p hK hk f hf0 A hf ht x
  have hHB := (hX.kernelHeat_bounded_regularity hn p hk f A hf t ht).2 x
  have hH0 : 0 ≤ kernelHeat μ Q hk t f x := by
    rw [kernelHeat_eq_integral μ Q hk ht]
    apply integral_nonneg_of_ae
    filter_upwards [(Lp.coeFn_nonneg _).mpr hf0] with y hy
    exact mul_nonneg (hk.nonneg t ht x y) hy
  have hc : 0 ≤ (n:ℝ)*(|K|+1/t) := by positivity
  rw [abs_le]
  constructor
  · have hb := mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans hHB) hc
    nlinarith only [hlo,hb]
  · have hb := mul_nonneg hc hH0
    nlinarith only [hup,hb]

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
