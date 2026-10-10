import OAI.Probability.SLE.Geometry.EndpointClusterLimit
import Mathlib.Analysis.Complex.Basic

namespace OAI

/-! Lifting a real cluster value when the imaginary coordinate tends to
zero. -/
noncomputable section
open Set Filter Metric Complex
open scoped Topology

namespace SLEExactGauge

lemma complex_cluster_of_real_cluster {α : Type*} {l : Filter α} {f : α → ℂ} {a : ℝ}
    (him : Tendsto (fun x => (f x).im) l (𝓝 0))
    (ha : MapClusterPt a l (fun x => (f x).re)) : MapClusterPt (a:ℂ) l f := by
  apply (Metric.nhds_basis_ball.mapClusterPt_iff_frequently).mpr
  intro ε hε
  have hre := ha.frequently (ball_mem_nhds a (half_pos hε))
  have himsmall : ∀ᶠ x in l, |(f x).im|<ε/2 := by
    have hh : Tendsto (fun x => |(f x).im|) l (𝓝 0) := by
      simpa only [norm_zero,Real.norm_eq_abs] using him.norm
    exact hh.eventually (gt_mem_nhds (half_pos hε))
  apply (hre.and_eventually himsmall).mono
  intro x hx
  rw [mem_ball,dist_eq_norm]
  have hr : |(f x).re-a|<ε/2 := by
    simpa only [mem_ball,Real.dist_eq] using hx.1
  calc
    ‖f x-(a:ℂ)‖ ≤ |(f x).re-a|+|(f x).im| := by
      simpa only [sub_re,ofReal_re,sub_im,ofReal_im,sub_zero] using
        norm_le_abs_re_add_abs_im (f x-(a:ℂ))
    _ < ε := by linarith [hx.2]

lemma cluster_value_eq_limit {α X : Type*} [TopologicalSpace X] [T2Space X]
    {l : Filter α} {f : α → X} {a b : X}
    (ha : MapClusterPt a l f) (hb : Tendsto f l (𝓝 b)) : a=b := by
  let : NeBot (𝓝 a ⊓ map f l) := ha
  have h1 : Tendsto id (𝓝 a ⊓ map f l) (𝓝 a) := inf_le_left
  have h2 : Tendsto id (𝓝 a ⊓ map f l) (𝓝 b) := inf_le_right.trans hb
  exact tendsto_nhds_unique h1 h2

end SLEExactGauge

end

end OAI
