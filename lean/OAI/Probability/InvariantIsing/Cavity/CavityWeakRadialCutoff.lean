import OAI.Probability.InvariantIsing.Cavity.CavityBoundaryCutoff

namespace OAI

/-! Weak convergence of a bounded continuous replica test restricted by
a continuous radius, at any radius with zero limiting boundary mass. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

def cavityBoundaryProfile {E : Type*} [TopologicalSpace E]
    (R : E → ℝ) (hR : Continuous R) (r B c : ℝ) : E →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => cavityRadialCutoff 0 (r*(R x-B)+c))
    ((continuous_cavityRadialCutoff 0).comp (by fun_prop)) 1 (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (cavityRadialCutoff_mem 0 _).1]
      exact (cavityRadialCutoff_mem 0 _).2)

theorem cavity_weak_radial_cutoff_integral {E : Type*} [TopologicalSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : ℕ → ProbabilityMeasure E) (ν : ProbabilityMeasure E)
    (hμ : Tendsto μ atTop (𝓝 ν)) (R : E → ℝ) (hR : Continuous R)
    (F : E →ᵇ ℝ) (B : ℝ)
    (hnull : (ν : Measure E) {x | R x=B}=0) :
    Tendsto (fun n => ∫ x, {x | R x ≤ B}.indicator (fun x => F x) x ∂(μ n : Measure E))
      atTop (𝓝 (∫ x, {x | R x ≤ B}.indicator (fun x => F x) x ∂(ν : Measure E))) := by
  let U (j : ℕ) := cavityBoundaryProfile R hR ((j : ℝ)+1) B 0
  let L (j : ℕ) := cavityBoundaryProfile R hR ((j : ℝ)+1) B 1
  let A (j : ℕ) : E →ᵇ ℝ := F*U j
  let G (j : ℕ) : E →ᵇ ℝ := BoundedContinuousFunction.const E ‖F‖*(U j-L j)
  have hg j x : G j x = ‖F‖*cavityBoundaryGap ((j : ℝ)+1) B (R x) := by
    simp only [G,U,L,cavityBoundaryProfile,BoundedContinuousFunction.mul_apply,
      BoundedContinuousFunction.sub_apply,BoundedContinuousFunction.const_apply,
      BoundedContinuousFunction.coe_ofNormedAddCommGroup,cavityBoundaryGap,
      cavityBoundaryUpper,cavityBoundaryLower,add_zero]
  have hfm : Measurable ({x | R x ≤ B}.indicator (fun x => F x)) :=
    F.continuous.measurable.indicator (measurableSet_le hR.measurable measurable_const)
  have hfb x : |{x | R x ≤ B}.indicator (fun x => F x) x| ≤ ‖F‖ := by
    by_cases hx : R x ≤ B
    · rw [Set.indicator_of_mem (show x ∈ {y | R y ≤ B} from hx)]
      simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm x
    · rw [Set.indicator_of_notMem (show x ∉ {y | R y ≤ B} from hx),abs_zero]
      exact norm_nonneg F
  apply cavity_weak_integral_of_continuous_approximation μ ν hμ _ hfm hfb A G
  · intro j x
    rw [hg]
    have he := cavityBoundaryUpper_error (r := (j : ℝ)+1) (B := B) (x := R x)
      (a := F x) (by positivity)
    have hb := mul_le_mul_of_nonneg_right (F.norm_coe_le_norm x)
      (cavityBoundaryGap_mem (r := (j : ℝ)+1) (B := B) (x := R x) (by positivity)).1
    apply (show |{x | R x ≤ B}.indicator (fun x => F x) x - A j x| ≤
      |F x| *cavityBoundaryGap ((j : ℝ)+1) B (R x) from ?_).trans hb
    simpa only [A,U,cavityBoundaryProfile,BoundedContinuousFunction.mul_apply,
      BoundedContinuousFunction.coe_ofNormedAddCommGroup,add_zero,
      Set.indicator_apply,Set.mem_ofPred_eq,cavityBoundaryUpper] using he
  · have hneq : ∀ᵐ x ∂(ν : Measure E), R x ≠ B := compl_mem_ae_iff.mpr hnull
    have hlim : ∀ᵐ x ∂(ν : Measure E), Tendsto (fun j => G j x) atTop (𝓝 0) := by
      filter_upwards [hneq] with x hx
      simp_rw [hg]
      simpa only [mul_zero] using tendsto_const_nhds.mul (cavityBoundaryGap_tendsto hx)
    have hb j x : ‖G j x‖ ≤ ‖F‖ := by
      rw [hg,Real.norm_eq_abs,abs_mul,abs_of_nonneg (norm_nonneg F),
        abs_of_nonneg (cavityBoundaryGap_mem (r := (j : ℝ)+1) (B := B) (x := R x) (by positivity)).1]
      exact mul_le_of_le_one_right (norm_nonneg F)
        (cavityBoundaryGap_mem (r := (j : ℝ)+1) (B := B) (x := R x) (by positivity)).2
    have ht := tendsto_integral_of_dominated_convergence (fun _ : E => ‖F‖)
      (fun j => (G j).continuous.measurable.aestronglyMeasurable) (integrable_const _)
      (fun j => ae_of_all _ (hb j)) hlim
    simpa only [integral_zero] using ht

end InvariantIsing

end

end OAI
