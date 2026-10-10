import Mathlib
import OAI.Geometry.CAT0Fillings.Calculus.ClosedBivariate

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
open ClosedCalculus

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma closed_compact_bivariate {r : X → ℝ} {K : ℝ≥0} (hr : LipschitzWith K r)
    {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hs : HasCompactSupport F) (P : q.Sobolev) :
    ∃ Q : q.Sobolev,
      (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => F (r x,q.inclusion P x)) ∧
      (q.closedGradient Q : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => fderiv ℝ F (r (q.atlasParam w),q.inclusion P (q.atlasParam w)) (1,0) • q.gradient hr w +
          fderiv ℝ F (r (q.atlasParam w),q.inclusion P (q.atlasParam w)) (0,1) • q.closedGradient P w) := by
  obtain ⟨B,hB⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hF one_ne_zero
  exact q.closed_bivariate hr hB (hasFDerivAt_binary (hF.differentiable one_ne_zero))
    ((hF.continuous_fderiv one_ne_zero).clm_apply continuous_const)
    ((hF.continuous_fderiv one_ne_zero).clm_apply continuous_const)
    B.coe_nonneg (fun t => (binary_coeff_bound hB t).1) (fun t => (binary_coeff_bound hB t).2) P

lemma closed_bounded_bivariate {r : X → ℝ} {K : ℝ≥0} (hr : LipschitzWith K r)
    {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 1 F) (P : q.Sobolev) {M : ℝ}
    (hb : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, ‖(r x,q.inclusion P x)‖ ≤ M) :
    ∃ Q : q.Sobolev,
      (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => F (r x,q.inclusion P x)) ∧
      (q.closedGradient Q : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => fderiv ℝ F (r (q.atlasParam w),q.inclusion P (q.atlasParam w)) (1,0) • q.gradient hr w +
          fderiv ℝ F (r (q.atlasParam w),q.inclusion P (q.atlasParam w)) (0,1) • q.closedGradient P w) := by
  let η : ContDiffBump (0 : ℝ × ℝ) :=
    { rIn := max M 0+1, rOut := max M 0+2,
      rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  let G (t : ℝ × ℝ) := η t * F t
  have hG : ContDiff ℝ 1 G := η.contDiff.mul hF
  have he (t : ℝ × ℝ) (ht : ‖t‖ ≤ M) : G =ᶠ[𝓝 t] F := by
    have hball : t ∈ Metric.ball 0 η.rIn := by
      simp only [Metric.mem_ball,dist_zero_right]
      dsimp [η]
      exact lt_of_le_of_lt (ht.trans (le_max_left _ _)) (lt_add_one _)
    filter_upwards [η.eventuallyEq_one_of_mem_ball hball] with z hz
    dsimp [G]
    rw [hz,Pi.one_apply,one_mul]
  obtain ⟨Q,hQ,hQG⟩ := q.closed_compact_bivariate hr hG (η.hasCompactSupport.mul_right) P
  refine ⟨Q,?_,?_⟩
  · filter_upwards [hQ,hb] with x hx hb
    rw [hx,(he _ hb).eq_of_nhds]
  · have ha : ∀ᵐ w ∂q.atlasMeasure, ‖(r (q.atlasParam w),q.inclusion P (q.atlasParam w))‖ ≤ M :=
      q.atlas_preserving.quasiMeasurePreserving.ae (p := fun x : X => ‖(r x,q.inclusion P x)‖ ≤ M) hb
    filter_upwards [hQG,ha] with w hw ha
    rw [hw,(he _ ha).fderiv_eq]

end CAT0Fillings.ChartGeometry
end

section

open Set Filter
open scoped Topology

namespace CAT0Fillings.ClosedCalculus

lemma positive_strip_extension {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F {z | 0 < z.2}) {ε N : ℝ}
    (he : 0 < ε) (hN : ε ≤ N) :
    ∃ G : ℝ × ℝ → ℝ, ContDiff ℝ 1 G ∧
      ∀ z : ℝ × ℝ, z.2 ∈ Icc ε N → G =ᶠ[𝓝 z] F := by
  let c : ℝ := (N+ε)/2
  let η : ContDiffBump c :=
    { rIn := (N-ε)/2+ε/4, rOut := (N-ε)/2+ε/2,
      rIn_pos := by nlinarith, rIn_lt_rOut := by nlinarith }
  let G (z : ℝ × ℝ) := η z.2 * F z
  have hs (z : ℝ × ℝ) (hz : z.2 ≤ 0) : G =ᶠ[𝓝 z] 0 := by
    have ho : z.2 ∉ Metric.closedBall c η.rOut := by
      rw [Metric.mem_closedBall,Real.dist_eq]
      dsimp [c,η]
      have hneg : z.2-(N+ε)/2 < 0 := by nlinarith
      rw [abs_of_neg hneg]
      nlinarith
    have ht : z.2 ∉ tsupport η := by simpa only [η.tsupport_eq] using ho
    have hzero := notMem_tsupport_iff_eventuallyEq.mp ht
    filter_upwards [hzero.comp_tendsto continuous_snd.continuousAt] with w hw
    change η w.2 * F w = 0
    change η w.2 = 0 at hw
    rw [hw,zero_mul]
  have hG : ContDiff ℝ 1 G := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : 0 < z.2
    · exact ((η.contDiff.comp contDiff_snd).contDiffAt).mul
        (hF.contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds hz))
    · exact contDiffAt_const.congr_of_eventuallyEq (hs z (le_of_not_gt hz))
  refine ⟨G,hG,?_⟩
  intro z hz
  have hb : z.2 ∈ Metric.ball c η.rIn := by
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    dsimp [c,η]
    constructor <;> nlinarith [hz.1,hz.2]
  have hone := η.eventuallyEq_one_of_mem_ball hb
  filter_upwards [hone.comp_tendsto continuous_snd.continuousAt] with w hw
  dsimp [G]
  change η w.2 = 1 at hw
  rw [hw,one_mul]
end CAT0Fillings.ClosedCalculus
end

end OAI
