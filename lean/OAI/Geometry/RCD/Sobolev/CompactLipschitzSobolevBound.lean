import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # A uniform Sobolev bound from compact support and Lipschitz bounds -/

open Set Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  (Q : QuadraticCheegerEnergy μ)

theorem compact_lipschitz_sobolev_uniform_bound {s : Set X} (hs : IsCompact s)
    (A L : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : SobolevSpace μ Q) (f : X → ℝ),
      LipschitzWith L f → (∀ x, |f x| ≤ A) → (∀ x ∉ s, f x = 0) →
      SobolevSpace.toLp μ Q u =ᵐ[μ] f → ‖u‖ ≤ C := by
  let U : Lp ℝ 2 μ := indicatorConstLp 2 hs.measurableSet hs.measure_lt_top.ne (A:ℝ)
  let V : Lp ℝ 2 μ := indicatorConstLp 2 hs.measurableSet hs.measure_lt_top.ne (L:ℝ)
  have hU : U =ᵐ[μ] s.indicator (fun _ => (A:ℝ)) := indicatorConstLp_coeFn
  have hV : V =ᵐ[μ] s.indicator (fun _ => (L:ℝ)) := indicatorConstLp_coeFn
  refine ⟨‖U‖+‖V‖,by positivity,?_⟩
  intro u f hf hb hz he
  have hv : ‖SobolevSpace.toLp μ Q u‖ ≤ ‖U‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [he,hU] with x hx hux
    rw [hx,hux,Real.norm_eq_abs,Real.norm_eq_abs]
    by_cases hxs : x ∈ s
    · simpa only [indicator_of_mem hxs,abs_of_nonneg A.coe_nonneg] using hb x
    · simp only [indicator_of_notMem hxs,hz x hxs,abs_zero,le_refl]
  have hd : ‖SobolevSpace.minimalSlope μ Q u‖ ≤ ‖V‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [SobolevSpace.minimalSlope_le_lipschitz μ Q u hf he,
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ Q u),
      SobolevSpace.minimalSlope_zero_on_zero μ Q u,he,hV] with x hx hn hzero heq hvx
    rw [Real.norm_eq_abs,abs_of_nonneg hn,hvx,Real.norm_eq_abs]
    by_cases hxs : x ∈ s
    · simpa only [indicator_of_mem hxs,abs_of_nonneg L.coe_nonneg] using hx
    · rw [indicator_of_notMem hxs,abs_zero,hzero (heq.trans (hz x hxs))]
  have hnorm := SobolevSpace.norm_sq μ Q u
  rw [SobolevSpace.normSq,← SobolevSpace.minimalSlope_norm_sq] at hnorm
  have hu := norm_nonneg (SobolevSpace.toLp μ Q u)
  have hd0 := norm_nonneg (SobolevSpace.minimalSlope μ Q u)
  nlinarith [norm_nonneg u,norm_nonneg U,norm_nonneg V]

end RegularPointCoordinates

end

end OAI
