import Mathlib
import OAI.Geometry.WeakHessian.Transport.BoundedHopfMap

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile82
noncomputable section
namespace WeakHessianTransport
open WeakHessian Set Filter MeasureTheory
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [ProperSpace X]

lemma boundedHopfMap_support_bound (f : X →ᵇ ℝ) (o : X) {R : ℝ} (hR : 0 ≤ R)
    (hs : Function.support f ⊆ Metric.closedBall o R) {s : ℝ} (hs0 : 0 < s) :
    Function.support (boundedHopfMap f s) ⊆ Metric.closedBall o (R+s+‖f‖+1) := by
  lift R to ℝ≥0 using hR
  intro x hx
  by_contra hout
  have hxD : R+s+‖f‖+1 < dist x o := lt_of_not_ge hout
  have hx0 : f x = 0 := by
    by_contra hh
    have := hs hh
    change dist x o ≤ R at this
    linarith [norm_nonneg f]
  have hqne : hopfLax f s x ≠ 0 := by simpa only [Function.mem_support,boundedHopfMap_apply_pos f hs0] using hx
  have hq : hopfLax f s x < 0 := lt_of_le_of_ne (by simpa only [hx0] using hopfLax_le_self (fun x => (boundedContinuous_bounds f x).1) hs0 x) hqne
  obtain ⟨y,hy⟩ := exists_hopf_minimizer f.continuous (fun x => (boundedContinuous_bounds f x).1) hs0 x
  have hfneg : f y < 0 := by
    have hc : 0 ≤ dist x y^2/(2*s) := by positivity
    dsimp only [hopfObjective] at hy
    linarith
  have hyR : dist y o ≤ R := hs (ne_of_lt hfneg)
  have hd := hopf_minimizer_distance_sq (fun x => (boundedContinuous_bounds f x).1) hs0 hy
  rw [hx0] at hd
  have htri := dist_triangle x y o
  have hn := norm_nonneg f
  have hsqd : (s+‖f‖+1)^2 < dist x y^2 := (sq_lt_sq₀ (by positivity) dist_nonneg).mpr (by linarith)
  nlinarith [sq_nonneg s,sq_nonneg ‖f‖]

lemma boundedHopfMap_compactSupport (f : X →ᵇ ℝ) (o : X)
    (hf : HasCompactSupport (f : X → ℝ)) {s : ℝ} (hs : 0 < s) :
    HasCompactSupport (boundedHopfMap f s : X → ℝ) := by
  obtain ⟨R,hR,hsub⟩ := hf.isCompact.isBounded.subset_closedBall_lt 0 o
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall o (R+s+‖f‖+1))
  exact boundedHopfMap_support_bound f o hR.le ((subset_tsupport f).trans hsub) hs

variable [MeasurableSpace X] [BorelSpace X] {m : Measure X}

lemma boundedHopfMap_memLp_compact (hfin : FiniteOnBoundedSets m) (f : X →ᵇ ℝ) (o : X)
    (hf : HasCompactSupport (f : X → ℝ)) {s : ℝ} (hs : 0 < s) :
    MemLp (boundedHopfMap f s) 2 m := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin _ Metric.isBounded_ball⟩⟩
  apply (boundedHopfMap_compactSupport f o hf hs).memLp_of_bound (boundedHopfMap f s).continuous.aestronglyMeasurable
  exact ae_of_all _ fun x => (boundedHopfMap f s).norm_coe_le_norm x

lemma boundedHopfMap_memLp_nonneg (f : X →ᵇ ℝ) (hf : MemLp f 2 m)
    (hn : ∀ x,0 ≤ f x) {s : ℝ} (hs : 0 < s) : MemLp (boundedHopfMap f s) 2 m := by
  apply hf.mono' (boundedHopfMap f s).continuous.aestronglyMeasurable
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs,boundedHopfMap_apply_pos f hs]
  rw [abs_of_nonneg (lower_le_hopfLax hn hs x)]
  exact hopfLax_le_self hn hs x
end WeakHessianTransport

end
end InlinedFile82

end OAI
