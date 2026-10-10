import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.CongrAeLeft
import OAI.Geometry.WeakHessian.Calculus.NormSqLintegralEnorm

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set
open scoped NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace

namespace WeakHessian

section NormConvergence
open MeasureTheory Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

lemma upperGradient_tendsto_of_norm_tendsto {fn Dn : ℕ → Lp ℝ 2 m} {f D : Lp ℝ 2 m}
    (hn : ∀ n, IsLocalWeakUpperGradient m (fn n) (Dn n))
    (hf : Tendsto fn atTop (𝓝 f)) (hD : IsLocalWeakUpperGradient m f D)
    (hmin : ∀ E : Lp ℝ 2 m, IsLocalWeakUpperGradient m f E → ‖D‖ ≤ ‖E‖)
    (hNorm : Tendsto (fun n => ‖Dn n‖) atTop (𝓝 ‖D‖)) :
    Tendsto Dn atTop (𝓝 D) := by
  let fm : ℕ → Lp ℝ 2 m := fun n => (1/2 : ℝ) • fn n + (1/2 : ℝ) • f
  let Dm : ℕ → Lp ℝ 2 m := fun n => (1/2 : ℝ) • Dn n + (1/2 : ℝ) • D
  have hmid (n : ℕ) : IsLocalWeakUpperGradient m (fm n) (Dm n) := by
    exact convex_l2GradientGraph (m := m)
      (x := WithLp.toLp 2 (fn n, Dn n)) (y := WithLp.toLp 2 (f,D))
      (hn n) hD (by norm_num) (by norm_num) (by norm_num)
  have hfm : Tendsto fm atTop (𝓝 f) := by
    have H := (hf.const_smul (1/2 : ℝ)).add
      (tendsto_const_nhds (x := (1/2 : ℝ) • f))
    simpa only [← add_smul, show (1/2:ℝ)+(1/2)=1 by norm_num, one_smul] using H
  have hlow (a : ℝ) (ha : a < ‖D‖) : ∀ᶠ n in atTop, a < ‖Dm n‖ := by
    have hout : f ∈ {u : Lp ℝ 2 m | ∃ E : Lp ℝ 2 m,
        IsLocalWeakUpperGradient m u E ∧ ‖E‖ ≤ a}ᶜ := by
      rintro ⟨E,hE,he⟩
      exact (not_le_of_gt ha) ((hmin E hE).trans he)
    have H := hfm.eventually ((isClosed_upperGradient_sublevel (m := m) a).isOpen_compl.mem_nhds hout)
    filter_upwards [H] with n hn'
    exact lt_of_not_ge (fun hle => hn' ⟨Dm n,hmid n,hle⟩)
  have hupper (n : ℕ) : ‖Dm n‖ ≤ (‖Dn n‖+‖D‖)/2 := by
    calc
      ‖Dm n‖ ≤ ‖(1/2 : ℝ) • Dn n‖ + ‖(1/2 : ℝ) • D‖ := norm_add_le _ _
      _ = (‖Dn n‖+‖D‖)/2 := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
        ring
  have hmajor : Tendsto (fun n => (‖Dn n‖+‖D‖)/2) atTop (𝓝 ‖D‖) := by
    convert (hNorm.add_const ‖D‖).div_const 2 using 1
    ring_nf
  have hmidNorm : Tendsto (fun n => ‖Dm n‖) atTop (𝓝 ‖D‖) := by
    apply tendsto_order.mpr
    refine ⟨hlow, fun b hb => ?_⟩
    filter_upwards [hmajor.eventually (gt_mem_nhds hb)] with n hn'
    exact (hupper n).trans_lt hn'
  have hsq (n : ℕ) : ‖Dn n - D‖^2 = 2*‖Dn n‖^2+2*‖D‖^2-4*‖Dm n‖^2 := by
    have hm : ‖Dm n‖ = ‖Dn n+D‖/2 := by
      simp only [Dm, ← smul_add, norm_smul,
        Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
      ring
    rw [hm]
    nlinarith [parallelogram_law_with_norm ℝ (Dn n) D]
  have hs : Tendsto (fun n => ‖Dn n-D‖^2) atTop (𝓝 0) := by
    simp_rw [hsq]
    convert ((hNorm.pow 2).const_mul 2 |>.add_const (2*‖D‖^2)).sub
      ((hmidNorm.pow 2).const_mul 4) using 1
    ring_nf
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have H := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using H

omit [BorelSpace X] in
lemma IsMinimalLocalWeakUpperGradient.norm_le {f D : Lp ℝ 2 m}
    (hD : IsMinimalLocalWeakUpperGradient m (f : X → ℝ) D)
    {E : Lp ℝ 2 m} (hE : IsLocalWeakUpperGradient m f E) : ‖D‖ ≤ ‖E‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [hD.2 E hE, hD.1.2.1, hE.2.1] with x hx hd he
  simpa only [Real.norm_eq_abs, abs_of_nonneg hd, abs_of_nonneg he] using hx

lemma IsMinimalLocalWeakUpperGradient.tendsto_of_norm_tendsto
    {fn Dn : ℕ → Lp ℝ 2 m} {f D : Lp ℝ 2 m}
    (hD : IsMinimalLocalWeakUpperGradient m (f : X → ℝ) D)
    (hn : ∀ n, IsLocalWeakUpperGradient m (fn n) (Dn n))
    (hf : Tendsto fn atTop (𝓝 f))
    (hNorm : Tendsto (fun n => ‖Dn n‖) atTop (𝓝 ‖D‖)) :
    Tendsto Dn atTop (𝓝 D) :=
  upperGradient_tendsto_of_norm_tendsto hn hf hD.1 (fun _ hE => hD.norm_le hE) hNorm
end NormConvergence

open WeakHessianFunctional MeasureTheory Set Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSpace X] [BorelSpace X] {m ν : Measure X} [IsProbabilityMeasure ν]

lemma CurvatureDimension.reference_relaxedGradient_isMinimal {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hν : ν ≪ m)
    {f D : Lp ℝ 2 ν} (hD : WithLp.toLp 2 (f,D) ∈ l2RelaxedGraph ν)
    (he : cheegerEnergy ν (f : X → ℝ) = ENNReal.ofReal (‖D‖^2/2)) :
    IsMinimalLocalWeakUpperGradient ν (f : X → ℝ) (D : X → ℝ) := by
  apply norm_minimal_is_minimal (relaxedGraph_isUpperGradient (fun B _ => measure_lt_top ν B) hD)
  intro E hE
  change IsLocalWeakUpperGradient ν (f : X → ℝ) (E : X → ℝ) at hE
  change ‖D‖ ≤ ‖E‖
  have H := hcd.reference_cheegerEnergy_le_weak hν hE
  rw [he] at H
  have HR : ‖D‖^2/2 ≤ ‖E‖^2/2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp H
  nlinarith [norm_nonneg D,norm_nonneg E]

lemma CurvatureDimension.reference_exists_relaxedGradient_le {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hν : ν ≪ m)
    {f W : Lp ℝ 2 ν} (hf : IsLocalWeakUpperGradient ν (f : X → ℝ) (W : X → ℝ)) :
    ∃ D : Lp ℝ 2 ν,WithLp.toLp 2 (f,D) ∈ l2RelaxedGraph ν ∧
      (∀ᵐ x ∂ν,0 ≤ D x ∧ D x ≤ W x) := by
  have he := hcd.reference_cheegerEnergy_le_weak hν hf
  obtain ⟨D,hD,_hmin,he⟩ := exists_relaxedGradient_energy_eq (he.trans_lt ENNReal.ofReal_lt_top)
  have hm := hcd.reference_relaxedGradient_isMinimal hν hD he
  exact ⟨D,hD,hm.1.2.1.and (hm.2 W hf)⟩
end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
