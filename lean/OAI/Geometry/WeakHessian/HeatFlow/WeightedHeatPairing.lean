import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.CheegerHeatDavies
import OAI.Geometry.WeakHessian.HeatFlow.CheegerHeatContinuous
import OAI.Geometry.WeakHessian.LocalBounds.WeightedPairing
import OAI.Geometry.WeakHessian.LocalBounds.RadialRoots

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile42
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

lemma radial_tail_memLp {f : X → ℝ} (hf : MemLp f 2 m) (o : X) (n : ℕ) :
    MemLp (fun x => f x*(1-radialCutoff o n x)) 2 m := by
  convert hf.sub (radial_mul_memLp hf o n) using 1
  funext x
  simp only [Pi.sub_apply]
  ring

lemma radial_tail_norm_tendsto {f : X → ℝ} (hf : MemLp f 2 m) (o : X) :
    Tendsto (fun n => ‖(radial_tail_memLp hf o n).toLp
      (fun x => f x*(1-radialCutoff o n x))‖) atTop (𝓝 0) := by
  have H := ((tendsto_const_nhds (x := hf.toLp f)).sub (radial_mul_tendsto hf o)).norm
  have he (n : ℕ) : (radial_tail_memLp hf o n).toLp (fun x => f x*(1-radialCutoff o n x)) =
      hf.toLp f-(radial_mul_memLp hf o n).toLp (fun x => f x*radialCutoff o n x) := by
    rw [← MemLp.toLp_sub]
    congr 1
    funext x
    simp only [Pi.sub_apply]
    ring
  simpa only [he,sub_self,norm_zero] using H

lemma weighted_pairing_cutoff_error {V f φ : X → ℝ}
    (hf : MemLp (fun x => f x*Real.exp (V x)) 2 m)
    (hφ : MemLp (fun x => φ x*Real.exp (-V x)) 2 m) (o : X) (n : ℕ) :
    ‖(∫ x,f x*φ x ∂m)-(∫ x,f x*φ x*radialCutoff o n x ∂m)‖ ≤
      ‖hf.toLp (fun x => f x*Real.exp (V x))‖*
      ‖(radial_tail_memLp hφ o n).toLp (fun x => (φ x*Real.exp (-V x))*(1-radialCutoff o n x))‖ := by
  have hi := (weighted_pairing hf hφ).1
  have hic := hi.mul_bdd (radialCutoff_lipschitz o n).continuous.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (radialCutoff_nonneg o n x)]; exact radialCutoff_le_one o n x)
  rw [← integral_sub hi hic]
  have hc : MemLp (fun x => (φ x*(1-radialCutoff o n x))*Real.exp (-V x)) 2 m := by
    convert radial_tail_memLp hφ o n using 1
    funext x; ring
  convert (weighted_pairing hf hc).2 using 1
  · congr 2; funext x; ring
  · congr 2
    apply Lp.ext
    filter_upwards [hc.coeFn_toLp,(radial_tail_memLp hφ o n).coeFn_toLp] with x hx hy
    rw [hx,hy]; ring

omit [MetricSpace X] [BorelSpace X] in
lemma integral_mul_eq_inner_toLp (f : Lp ℝ 2 m) {φ : X → ℝ} (hφ : MemLp φ 2 m) :
    (∫ x,f x*φ x ∂m) = ⟪hφ.toLp φ,f⟫_ℝ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hφ.coeFn_toLp] with x hx
  simp only [hx,RCLike.inner_apply,conj_trivial]

lemma weighted_pairing_tendsto {ι : Type*} {l : Filter ι}
    {V φ : X → ℝ} (hφ : MemLp (fun x => φ x*Real.exp (-V x)) 2 m) (o : X)
    (hcut : ∀ n, MemLp (fun x => φ x*radialCutoff o n x) 2 m)
    {fs : ι → Lp ℝ 2 m} {f : Lp ℝ 2 m} (hlim : Tendsto fs l (𝓝 f))
    (hf : MemLp (fun x => f x*Real.exp (V x)) 2 m)
    (hfs : ∀ i, MemLp (fun x => fs i x*Real.exp (V x)) 2 m)
    {B : ℝ} (hB : ∀ᶠ i in l, ‖(hfs i).toLp (fun x => fs i x*Real.exp (V x))‖ ≤ B) :
    Tendsto (fun i => ∫ x,fs i x*φ x ∂m) l (𝓝 (∫ x,f x*φ x ∂m)) := by
  let D := ‖hf.toLp (fun x => f x*Real.exp (V x))‖
  have htail : Tendsto (fun n => (B+D)*‖(radial_tail_memLp hφ o n).toLp
      (fun x => (φ x*Real.exp (-V x))*(1-radialCutoff o n x))‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using (radial_tail_norm_tendsto hφ o).const_mul (B+D)
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n,hn⟩ := (htail.eventually_lt_const (half_pos hε)).exists
  have hc : Tendsto (fun i => ∫ x,fs i x*φ x*radialCutoff o n x ∂m) l
      (𝓝 (∫ x,f x*φ x*radialCutoff o n x ∂m)) := by
    simp_rw [mul_assoc,integral_mul_eq_inner_toLp _ (hcut n)]
    exact (innerSL ℝ ((hcut n).toLp _)).continuous.continuousAt.tendsto.comp hlim
  filter_upwards [hB,(Metric.tendsto_nhds.mp hc) (ε/2) (half_pos hε)] with i hi hic
  have he1 := (weighted_pairing_cutoff_error (hfs i) hφ o n).trans
    (mul_le_mul_of_nonneg_right hi (norm_nonneg _))
  have he2 := weighted_pairing_cutoff_error hf hφ o n
  have ht1 := dist_triangle (∫ x,fs i x*φ x ∂m)
    (∫ x,fs i x*φ x*radialCutoff o n x ∂m) (∫ x,f x*φ x ∂m)
  have ht2 := dist_triangle (∫ x,fs i x*φ x*radialCutoff o n x ∂m)
    (∫ x,f x*φ x*radialCutoff o n x ∂m) (∫ x,f x*φ x ∂m)
  simp only [dist_eq_norm] at ht1 ht2 hic ⊢
  rw [norm_sub_rev (∫ x,f x*φ x*radialCutoff o n x ∂m)] at ht2
  dsimp only [D] at hn
  nlinarith

variable [ProperSpace X] [TopologicalSpace.SeparableSpace X]

lemma CurvatureDimension.cheegerHeat_weighted_pairing_continuous {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    {φ : X → ℝ} (hφ : MemLp (fun x => φ x*Real.exp (-V x)) 2 m)
    (hcut : ∀ n, MemLp (fun x => φ x*radialCutoff o n x) 2 m) :
    Continuous (fun t : ℝ => ∫ x,cheegerHeat h (max t 0) u x*φ x ∂m) := by
  have hc : Continuous (fun t : ℝ => cheegerHeat h (max t 0) u) :=
    (cheegerHeat_continuousOn hfin h u).comp_continuous (continuous_id.max continuous_const)
      (fun t => le_max_right t 0)
  apply continuous_iff_continuousAt.mpr
  intro t
  apply weighted_pairing_tendsto hφ o hcut hc.continuousAt
    (hcd.cheegerHeat_weighted hfin o h u hV hU (le_max_right t 0)).1
    (fun s => (hcd.cheegerHeat_weighted hfin o h u hV hU (le_max_right s 0)).1)
  filter_upwards [((continuous_id.max continuous_const : Continuous (fun s : ℝ => max s 0)).continuousAt.eventually_lt_const
    (lt_add_one (max t 0)))] with s hs
  exact (hcd.cheegerHeat_weighted_norm hfin o h u hV hU (le_max_right s 0)).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.le (sq_nonneg _))) (norm_nonneg _))
end WeakHessian

end
end InlinedFile42

end OAI
