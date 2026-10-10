import OAI.Geometry.RCD.Heat.KernelHeatSourceLower

namespace OAI

/-! # Integrating the pointwise heat-source lower bound in time -/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2≤n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn p

theorem kernelHeat_time_monotone (hK : K≤0)
    {kernel : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic kernel)
    (f : Lp ℝ 2 (hausdorff n X)) (hf0 : 0≤f) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x|≤A)
    {a b : ℝ} (ha : 0<a) (hab : a≤b) (x : X) :
    Real.exp ((n:ℝ)*(Real.log a+|K| * a))*kernelHeat (hausdorff n X) hX.quadratic hk a f x ≤
      Real.exp ((n:ℝ)*(Real.log b+|K| * b))*kernelHeat (hausdorff n X) hX.quadratic hk b f x := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let F := fun t => Real.exp ((n:ℝ)*(Real.log t+|K| * t))*kernelHeat μ Q hk t f x
  have hd (t : ℝ) (ht : 0<t) : ∃ rate : ℝ, HasDerivAt F rate t ∧ 0≤rate := by
    have hw := (((Real.hasDerivAt_log ht.ne').add
      ((hasDerivAt_id t).const_mul |K|)).const_mul (n:ℝ)).exp
    have hheat := kernelHeat_generator_hasDerivAt μ Q hk f ht x
    have hder := hw.mul hheat
    have hb := hX.kernelHeat_source_lower hn p hK hk f hf0 A hf ht x
    have hpos := mul_nonneg (Real.exp_pos ((n:ℝ)*(Real.log t+|K| * t))).le
      (sub_nonneg.mpr hb)
    refine ⟨_,hder,?_⟩
    simp only [Pi.add_apply,id_eq,mul_one,one_div] at hpos ⊢
    nlinarith only [hpos]
  have hmono : MonotoneOn F (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    · intro t ht
      exact (hd t (ha.trans_le ht.1)).choose_spec.1.continuousAt.continuousWithinAt
    · rw [interior_Icc]
      intro t ht
      exact (hd t (ha.trans ht.1)).choose_spec.1.differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      obtain ⟨d,hd,hn⟩ := hd t (ha.trans ht.1)
      rwa [hd.deriv]
  exact hmono ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
