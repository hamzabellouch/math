import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.FlowPointwise
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.UniformSpace.HeineCantor

namespace OAI

/-! Differentiation of a smooth finite-dimensional field on compact path space.
Compactness makes the derivative remainder uniform over the path; this is the
analytic ingredient needed to apply the implicit function theorem to Picard's
integral equation. -/

noncomputable section
namespace ForcedComputation.Flow

open Set Filter Metric
open scoped Topology ContDiff

variable {K E F : Type} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def postcompose (f : C(E, F)) (u : C(K, E)) : C(K, F) := f.comp u

omit [CompactSpace K] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F] in
theorem postcompose_continuous (f : C(E, F)) :
    Continuous (postcompose (K := K) f) := f.continuous_postcomp

theorem postcompose_hasFDerivAt (f : C(E, F))
    (hf : ContDiff ℝ 1 (f : E → F)) (u : C(K, E)) :
    HasFDerivAt (postcompose f)
      (applyPath ⟨fun t => fderiv ℝ f (u t),
        (hf.continuous_fderiv (by simp)).comp u.continuous⟩) u := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have hdf := hf.continuous_fderiv (by simp)
  have huc : UniformContinuousOn (fderiv ℝ f)
      (closedBall (0 : E) (‖u‖ + 1)) :=
    (isCompact_closedBall (0 : E) (‖u‖ + 1)).uniformContinuousOn_of_continuous
      hdf.continuousOn
  obtain ⟨δ, hδ, hcontrol⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  filter_upwards [Metric.ball_mem_nhds u (lt_min hδ zero_lt_one)] with v hv
  have hvnorm : ‖v - u‖ < min δ 1 := by simpa only [mem_ball, dist_eq_norm] using hv
  apply (ContinuousMap.norm_le _
    (mul_nonneg hε.le (norm_nonneg (v - u)))).mpr
  intro t
  change ‖f (v t) - f (u t) - fderiv ℝ f (u t) (v t - u t)‖ ≤ ε * ‖v - u‖
  have hu : u t ∈ closedBall (0 : E) (‖u‖ + 1) := by
    rw [mem_closedBall, dist_zero_right]
    exact (u.norm_coe_le_norm t).trans (by linarith)
  have hdiff : ‖v t - u t‖ ≤ ‖v - u‖ := (v - u).norm_coe_le_norm t
  have hv' : v t ∈ closedBall (0 : E) (‖u‖ + 1) := by
    rw [mem_closedBall, dist_zero_right]
    calc
      ‖v t‖ ≤ ‖v t - u t‖ + ‖u t‖ := by
        simpa only [sub_add_cancel] using norm_add_le (v t - u t) (u t)
      _ ≤ ‖v - u‖ + ‖u‖ := add_le_add hdiff (u.norm_coe_le_norm t)
      _ ≤ ‖u‖ + 1 := by linarith [lt_of_lt_of_le hvnorm (min_le_right δ 1)]
  have hsegment := (convex_closedBall (0 : E) (‖u‖ + 1)).segment_subset hu hv'
  have hr := remainder_bound (fun z => (hf.differentiable (by simp) z).hasFDerivAt)
    (u t) (v t) (ε := ε) (by
      intro z hz
      have hzδ : dist z (u t) < δ := by
        rw [dist_eq_norm]
        exact (norm_sub_le_of_mem_segment hz).trans_lt
          (hdiff.trans_lt (lt_of_lt_of_le hvnorm (min_le_left δ 1)))
      simpa only [dist_eq_norm] using (hcontrol z (hsegment hz) (u t) hu hzδ).le)
  exact hr.trans (mul_le_mul_of_nonneg_left hdiff hε.le)

theorem postcompose_contDiff_nat (n : ℕ) (f : C(E, F))
    (hf : ContDiff ℝ n (f : E → F)) :
    ContDiff ℝ n (postcompose (K := K) f) := by
  induction n generalizing F with
  | zero =>
      exact contDiff_zero.mpr (postcompose_continuous f)
  | succ n ih =>
      have h1 : ContDiff ℝ 1 (f : E → F) := hf.of_le (by norm_cast; omega)
      let df : C(E, E →L[ℝ] F) :=
        ⟨fderiv ℝ f, h1.continuous_fderiv (by simp)⟩
      have hdf : ContDiff ℝ n (df : E → E →L[ℝ] F) :=
        hf.fderiv_right (m := n) (by simp)
      apply contDiff_succ_iff_hasFDerivAt.mpr
      refine ⟨fun u => applyPathL (postcompose df u), ?_, ?_⟩
      · exact (applyPathL (K := K) (E := E) (F := F)).contDiff.comp (ih df hdf)
      · intro u
        exact postcompose_hasFDerivAt f h1 u

theorem postcompose_contDiff (f : C(E, F)) (hf : ContDiff ℝ ∞ (f : E → F)) :
    ContDiff ℝ ∞ (postcompose (K := K) f) := by
  rw [contDiff_infty]
  intro n
  exact postcompose_contDiff_nat n f (hf.of_le (by simp))

end ForcedComputation.Flow

end

end OAI
