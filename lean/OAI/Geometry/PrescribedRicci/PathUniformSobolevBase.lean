import Mathlib
import OAI.Geometry.PrescribedPotential.CompletedResolvent
import OAI.Geometry.PrescribedPotential.QuantitativeResolvent
import OAI.Geometry.PrescribedRicci.CurvatureCompactBounds
import OAI.Geometry.PrescribedRicci.KahlerL2Comparison
import OAI.Geometry.PrescribedRicci.MatrixComponentBounds
import OAI.Geometry.PrescribedRicci.MongeAmpereC0
import OAI.Geometry.PrescribedRicci.UniformMetricBounds
import OAI.Geometry.PrescribedPotential.RealSmoothOperator
import OAI.Geometry.PrescribedPotential.VolumePath

namespace OAI

/-! Path Uniform Sobolev Base. -/

section

 

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff Classical Matrix.Norms.Elementwise
namespace Anticanonical.SourceSmooth.KaehlerMetric
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X}

structure NormalizedPathSolution (g : KaehlerMetric A) (line : SemipositiveAnticanonicalMetric A) where
  potential : SmoothRealFunction A
  positive : g.PositivePotential potential
  mean_zero : g.integral potential.value = 0
  time : ℝ
  time_mem : time ∈ Icc (0:ℝ) 1
  constant : ℝ
  equation : ∀ x, (g.logRatio (g.deform potential positive)).value x =
    time*(prescribedForcing g line).value x+constant

lemma volumePath_background_laplacian_bound (g : KaehlerMetric A)
    (line : SemipositiveAnticanonicalMetric A) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : g.NormalizedPathSolution line, ∀ x,
      |(g.laplacian z.potential).value x| ≤ C := by
  obtain ⟨K,hK,hk⟩ := g.volumePath_metric_bounds line hd
  obtain ⟨M,hM,hm⟩ := g.compact_background_bounds (prescribedForcing g line)
  have hM0 : 0 ≤ M := by linarith
  refine ⟨(d:ℝ)^2*M*(K+M),by positivity,fun z x => ?_⟩
  obtain ⟨q,hq⟩ := exists_partition_chart (A:=A) x
  have hx := chartPartition_support q hq
  have hb := hm q x hq
  have hH := (hk z.potential z.positive z.mean_zero z.time z.constant z.time_mem z.equation q x hq).1
  have hp (i j : Fin d) : ‖z.potential.hessian q (A.chart q x) i j‖ ≤ K+M := by
    have he : z.potential.hessian q (A.chart q x) i j =
        (g.deform z.potential z.positive).matrix q (A.chart q x) i j-g.matrix q (A.chart q x) i j := by
      change _ = (g.matrix q (A.chart q x) i j+_)-_
      ring
    rw [he]
    apply (norm_sub_le _ _).trans
    exact add_le_add ((norm_le_pi_norm _ j).trans ((norm_le_pi_norm _ i).trans hH)) (hb.1 i j)
  change |g.laplacianValue z.potential x| ≤ _
  rw [g.laplacianValue_local z.potential q hx]
  exact (Complex.abs_re_le_norm _).trans (by
    simpa only [Fintype.card_fin] using MongeAmpere.trace_mul_entry_bound hM0 hb.2.1 hp)
end Anticanonical.SourceSmooth.KaehlerMetric

namespace GlobalElliptic
open Anticanonical SourceSmooth SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]

omit [ConnectedSpace X] in
lemma Localizers.uniform_zero_of_bound (D : Localizers A ι) (g : KaehlerMetric A)
    {Z : Type*} (F : Z → Smooth A) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ z x, ‖F z x‖ ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖D.embed 0 (F z)‖ ≤ C := by
  obtain ⟨B,Q,hB,hQ,hbq⟩ := D.kahler_L2_comparison g
  let C : ℝ := B*(M^2*g.integral (fun _ => (1:ℝ)))
  have hC : 0 ≤ C := mul_nonneg hB.le (mul_nonneg (sq_nonneg _) (g.integral_nonneg (fun _ => zero_le_one)))
  refine ⟨Real.sqrt C,Real.sqrt_nonneg _,fun z => (Real.le_sqrt (norm_nonneg _) hC).mpr ?_⟩
  apply (hbq (F z)).1.trans
  apply mul_le_mul_of_nonneg_left _ hB.le
  rw [← g.integral_const_mul (M^2) (fun _ => (1:ℝ))]
  apply g.integral_mono ((F z).continuous.norm.pow 2) continuous_const
  intro x
  change ‖F z x‖^2 ≤ M^2*1
  rw [mul_one]
  exact (sq_le_sq₀ (norm_nonneg _) hM).mpr (hb z x)

namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

theorem volumePath_uniform_H2 (line : SemipositiveAnticanonicalMetric A) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : g.NormalizedPathSolution line,
      ‖D.localizers.embed 2 (Smooth.ofReal z.potential)‖ ≤ C := by
  obtain ⟨M,hM,hm⟩ := g.volumePath_C0_bound line hd
  obtain ⟨B,hB,hb⟩ := D.localizers.uniform_zero_of_bound g
    (fun z : g.NormalizedPathSolution line => Smooth.ofReal z.potential) hM (fun z x => by
      simpa only [Smooth.ofReal_apply,Complex.norm_real,Real.norm_eq_abs] using
        hm z.potential z.positive z.mean_zero z.time z.constant z.time_mem z.equation x)
  obtain ⟨L,hL,hl⟩ := g.volumePath_background_laplacian_bound line hd
  obtain ⟨J,hJ,hj⟩ := D.localizers.uniform_zero_of_bound g
    (fun z : g.NormalizedPathSolution line => Smooth.ofReal (g.laplacian z.potential)) hL (fun z x => by
      simpa only [Smooth.ofReal_apply,Complex.norm_real,Real.norm_eq_abs] using hl z x)
  obtain ⟨m,hm,he⟩ := D.exists_completedError_small
  refine ⟨‖D.completedResolvent m hm he‖*(m^2*B+J),by positivity,fun z => ?_⟩
  have h := D.elliptic_estimate m hm he (D.localizers.embed 2 (Smooth.ofReal z.potential))
  rw [D.localizers.lower_embed (by norm_num : (0:ℝ) ≤ 2),
    completedL,D.localizers.extendCore_embed D.complexL_bound,complexL_ofReal] at h
  exact h.trans (mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_left (hb z) (sq_nonneg m)) (hj z)) (norm_nonneg (D.completedResolvent m hm he)))
end GluingData
end GlobalElliptic

end
end

end OAI
