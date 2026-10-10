import Mathlib
import OAI.Geometry.WeakHessian.Transport.HopfMap

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter
open scoped Topology ENNReal NNReal


namespace WeakHessianTransport
open WeakHessian MeasureTheory
open scoped InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [ProperSpace X]
  [MeasurableSpace X] [BorelSpace X] (m : Measure X) [IsFiniteMeasure m]

omit [ProperSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma boundedContinuous_bounds (f : X →ᵇ ℝ) : ∀ x, -‖f‖ ≤ f x ∧ f x ≤ ‖f‖ := by
  intro x
  simpa only [Real.norm_eq_abs, abs_le] using f.norm_coe_le_norm x

omit [MeasurableSpace X] [BorelSpace X] in

def boundedHopfMap (f : X →ᵇ ℝ) (t : ℝ) : X →ᵇ ℝ :=
  if ht : 0 < t then
    BoundedContinuousFunction.ofNormedAddCommGroup (hopfLax f t)
      (hopfLax_continuous f.continuous (fun x => (boundedContinuous_bounds f x).1)
        (fun x => (boundedContinuous_bounds f x).2) (by linarith [norm_nonneg f]) ht)
      ‖f‖ (fun x => by
        rw [Real.norm_eq_abs]
        exact abs_le.mpr ⟨lower_le_hopfLax (fun x => (boundedContinuous_bounds f x).1) ht x,
          (hopfLax_le_self (fun x => (boundedContinuous_bounds f x).1) ht x).trans
            (boundedContinuous_bounds f x).2⟩)
  else f

omit [MeasurableSpace X] [BorelSpace X] in
@[simp] lemma boundedHopfMap_zero (f : X →ᵇ ℝ) : boundedHopfMap f 0 = f := by simp [boundedHopfMap]

omit [MeasurableSpace X] [BorelSpace X] in
lemma boundedHopfMap_apply_pos (f : X →ᵇ ℝ) {t : ℝ} (ht : 0 < t) (x : X) :
    boundedHopfMap f t x = hopfLax f t x := by simp [boundedHopfMap, ht]

omit [MeasurableSpace X] [BorelSpace X] in
lemma boundedHopfMap_time_lipschitz (f : X →ᵇ ℝ) {a : ℝ} (ha : 0 < a) :
    LipschitzOnWith ⟨2*‖f‖/a, by positivity⟩ (boundedHopfMap f) (Ici a) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro t ht s hs
  apply (BoundedContinuousFunction.dist_le (by positivity : 0 ≤ 2*‖f‖/a*dist t s)).mpr
  intro x
  rw [boundedHopfMap_apply_pos f (ha.trans_le ht), boundedHopfMap_apply_pos f (ha.trans_le hs)]
  have H := hopf_time_abs_bound f.continuous (fun x => (boundedContinuous_bounds f x).1)
    (fun x => (boundedContinuous_bounds f x).2) (by linarith [norm_nonneg f]) ha ht hs x
  simpa only [Real.dist_eq, sub_neg_eq_add, ← two_mul] using H

omit [MeasurableSpace X] [BorelSpace X] in
lemma boundedHopfMap_dist_initial {f : X →ᵇ ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {t : ℝ} (ht : 0 ≤ t) : dist (boundedHopfMap f t) f ≤ t*(L:ℝ)^2/2 := by
  rcases ht.eq_or_lt with rfl | ht
  · simp
  apply (BoundedContinuousFunction.dist_le (by positivity : 0 ≤ t*(L:ℝ)^2/2)).mpr
  intro x
  rw [boundedHopfMap_apply_pos f ht, Real.dist_eq]
  have H := hopfLax_ge_lipschitz hf ht x
  have H' := hopfLax_le_self (fun x => (boundedContinuous_bounds f x).1) ht x
  exact abs_le.mpr ⟨by linarith, by linarith⟩

omit [MeasurableSpace X] [BorelSpace X] in
lemma continuousOn_boundedHopfMap {f : X →ᵇ ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    ContinuousOn (boundedHopfMap f) (Ici 0) := by
  intro t ht
  change 0 ≤ t at ht
  rcases ht.eq_or_lt with rfl | ht
  · rw [ContinuousWithinAt, boundedHopfMap_zero]
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg)
      (show ∀ᶠ s in 𝓝[≥] (0:ℝ), dist (boundedHopfMap f s) f ≤ s*(L:ℝ)^2/2 from
        Filter.Eventually.mono self_mem_nhdsWithin (fun s hs => boundedHopfMap_dist_initial hf hs))
    have H : Tendsto (fun s : ℝ => s*(L:ℝ)^2/2) (𝓝[≥] (0:ℝ)) (𝓝 (0*(L:ℝ)^2/2)) :=
      (((tendsto_id : Tendsto (fun s : ℝ => s) (𝓝 (0:ℝ)) (𝓝 0)).mul_const
        ((L:ℝ)^2)).div_const 2).mono_left nhdsWithin_le_nhds
    simpa using H
  · exact ((boundedHopfMap_time_lipschitz f (by positivity : 0 < t/2)).continuousOn.continuousAt
      (Ici_mem_nhds (by linarith : t/2 < t))).continuousWithinAt

def boundedHopfLp (f : X →ᵇ ℝ) (t : ℝ) : Lp ℝ 2 m := BoundedContinuousFunction.toLp 2 m ℝ (boundedHopfMap f t)

lemma continuousOn_boundedHopfLp {f : X →ᵇ ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    ContinuousOn (boundedHopfLp m f) (Ici 0) :=
  (BoundedContinuousFunction.toLp 2 m ℝ).continuous.comp_continuousOn (continuousOn_boundedHopfMap hf)

lemma boundedHopfLp_coe_ae (f : X →ᵇ ℝ) {t : ℝ} (ht : 0 < t) :
    (boundedHopfLp m f t : X → ℝ) =ᵐ[m] hopfLax f t := by
  apply (BoundedContinuousFunction.coeFn_toLp 2 m ℝ (boundedHopfMap f t)).trans
  exact Eventually.of_forall (boundedHopfMap_apply_pos f ht)
lemma boundedHopfLp_energy_bound (f : X →ᵇ ℝ) {t : ℝ} (ht : 0 < t) :
    cheegerEnergy m (boundedHopfLp m f t : X → ℝ) < ∞ ∧
      (cheegerEnergy m (boundedHopfLp m f t : X → ℝ)).toReal ≤
        (∫ x, (localSlope (hopfLax f t) x).toReal^2 ∂m)/2 := by
  have hf := hopfLax_lipschitz_radius f.continuous (fun x => (boundedContinuous_bounds f x).1)
    (fun x => (boundedContinuous_bounds f x).2) (by linarith [norm_nonneg f]) ht
    (Real.sqrt_nonneg (2*t*(‖f‖-(-‖f‖)))) (Real.sq_sqrt (by have := norm_nonneg f; nlinarith : 0 ≤ 2*t*(‖f‖-(-‖f‖)))).ge
  have hm : MemLp (hopfLax f t) 2 m := (memLp_congr_ae (boundedHopfLp_coe_ae m f ht)).mp (Lp.memLp (boundedHopfLp m f t))
  have H := cheegerEnergy_le_integral_localSlope m hf hm
  rw [← cheegerEnergy_congr_ae (boundedHopfLp_coe_ae m f ht)] at H
  have hfin := H.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hfin, ?_⟩
  have Hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top H
  rwa [ENNReal.toReal_ofReal (by positivity)] at Hr

end WeakHessianTransport

end

end OAI
