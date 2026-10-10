import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.SlopeApprox
import OAI.Geometry.WeakHessian.Sobolev.CheegerEnergyCongrAe
import OAI.Geometry.WeakHessian.Transport.HopfObjective

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set Filter
open scoped Topology ENNReal NNReal

namespace WeakHessianTransport
open WeakHessian

variable {X : Type*} [MetricSpace X] [ProperSpace X]

lemma hopf_forward_increment {f : X → ℝ} {B U t s : ℝ}
    (hf : Continuous f) (hlower : ∀ y, B ≤ f y) (hupper : ∀ y, f y ≤ U)
    (hBU : B ≤ U) (ht : 0 < t) (hts : t ≤ s) (x : X) :
    hopfLax f s x - hopfLax f t x ≤
      -(s-t)*t/(2*s) * (localSlope (hopfLax f t) x).toReal^2 := by
  have hs : 0 < s := ht.trans_le hts
  obtain ⟨y,hy⟩ := exists_farthest_hopf_minimizer hf hlower hupper hBU ht x
  have hi := hopf_time_increment hlower hs ht hy.1
  have hsl := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (hopf_localSlope_le hf hlower hupper hBU ht hy)
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ dist x y/t)] at hsl
  have hsq := (sq_le_sq₀ ENNReal.toReal_nonneg (by positivity : 0 ≤ dist x y/t)).mpr hsl
  have hcoef : 0 ≤ (s-t)*t/(2*s) := by positivity
  have heq : dist x y^2*(t-s)/(2*s*t) = -((s-t)*t/(2*s))*(dist x y/t)^2 := by
    field_simp
    ring
  rw [heq] at hi
  simpa only [neg_div, neg_mul, localSlope] using
    hi.trans (mul_le_mul_of_nonpos_left hsq (neg_nonpos.mpr hcoef))

end WeakHessianTransport

namespace WeakHessianTransport
open WeakHessian MeasureTheory
open scoped InnerProductSpace

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (m : Measure X) [IsFiniteMeasure m]

omit [MeasurableSpace X] [BorelSpace X] in
lemma continuousMap_bounds (f : C(X,ℝ)) : ∀ x, -‖f‖ ≤ f x ∧ f x ≤ ‖f‖ := by
  intro x
  simpa only [Real.norm_eq_abs, abs_le] using f.norm_coe_le_norm x

omit [MeasurableSpace X] [BorelSpace X] in

def hopfMap (f : C(X,ℝ)) (t : ℝ) : C(X,ℝ) :=
  if ht : 0 < t then
    ⟨hopfLax f t, hopfLax_continuous f.continuous (fun x => (continuousMap_bounds f x).1)
      (fun x => (continuousMap_bounds f x).2) (by linarith [norm_nonneg f]) ht⟩
  else f

omit [MeasurableSpace X] [BorelSpace X] in
@[simp] lemma hopfMap_zero (f : C(X,ℝ)) : hopfMap f 0 = f := by simp [hopfMap]

omit [MeasurableSpace X] [BorelSpace X] in
lemma hopfMap_apply_pos (f : C(X,ℝ)) {t : ℝ} (ht : 0 < t) (x : X) :
    hopfMap f t x = hopfLax f t x := by simp [hopfMap, ht]

omit [MeasurableSpace X] [BorelSpace X] in
lemma hopfMap_time_lipschitz (f : C(X,ℝ)) {a : ℝ} (ha : 0 < a) :
    LipschitzOnWith ⟨2*‖f‖/a, by positivity⟩ (hopfMap f) (Ici a) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro t ht s hs
  apply (ContinuousMap.dist_le (by positivity : 0 ≤ 2*‖f‖/a*dist t s)).mpr
  intro x
  rw [hopfMap_apply_pos f (ha.trans_le ht), hopfMap_apply_pos f (ha.trans_le hs)]
  have H := hopf_time_abs_bound f.continuous (fun x => (continuousMap_bounds f x).1)
    (fun x => (continuousMap_bounds f x).2) (by linarith [norm_nonneg f]) ha ht hs x
  simpa only [Real.dist_eq, sub_neg_eq_add, ← two_mul] using H

omit [MeasurableSpace X] [BorelSpace X] in
lemma hopfMap_dist_initial {f : C(X,ℝ)} {L : ℝ≥0} (hf : LipschitzWith L f)
    {t : ℝ} (ht : 0 ≤ t) : dist (hopfMap f t) f ≤ t*(L:ℝ)^2/2 := by
  rcases ht.eq_or_lt with rfl | ht
  · simp
  apply (ContinuousMap.dist_le (by positivity : 0 ≤ t*(L:ℝ)^2/2)).mpr
  intro x
  rw [hopfMap_apply_pos f ht, Real.dist_eq]
  have H := hopfLax_ge_lipschitz hf ht x
  have H' := hopfLax_le_self (fun x => (continuousMap_bounds f x).1) ht x
  exact abs_le.mpr ⟨by linarith, by linarith⟩

omit [MeasurableSpace X] [BorelSpace X] in
lemma continuousOn_hopfMap {f : C(X,ℝ)} {L : ℝ≥0} (hf : LipschitzWith L f) :
    ContinuousOn (hopfMap f) (Ici 0) := by
  intro t ht
  change 0 ≤ t at ht
  rcases ht.eq_or_lt with rfl | ht
  · rw [ContinuousWithinAt, hopfMap_zero]
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg)
      (show ∀ᶠ s in 𝓝[≥] (0:ℝ), dist (hopfMap f s) f ≤ s*(L:ℝ)^2/2 from
        Filter.Eventually.mono self_mem_nhdsWithin (fun s hs => hopfMap_dist_initial hf hs))
    have H : Tendsto (fun s : ℝ => s*(L:ℝ)^2/2) (𝓝[≥] (0:ℝ)) (𝓝 (0*(L:ℝ)^2/2)) :=
      (((tendsto_id : Tendsto (fun s : ℝ => s) (𝓝 (0:ℝ)) (𝓝 0)).mul_const
        ((L:ℝ)^2)).div_const 2).mono_left nhdsWithin_le_nhds
    simpa using H
  · exact ((hopfMap_time_lipschitz f (by positivity : 0 < t/2)).continuousOn.continuousAt
      (Ici_mem_nhds (by linarith : t/2 < t))).continuousWithinAt

def hopfLp (f : C(X,ℝ)) (t : ℝ) : Lp ℝ 2 m := ContinuousMap.toLp 2 m ℝ (hopfMap f t)

lemma continuousOn_hopfLp {f : C(X,ℝ)} {L : ℝ≥0} (hf : LipschitzWith L f) :
    ContinuousOn (hopfLp m f) (Ici 0) :=
  (ContinuousMap.toLp 2 m ℝ).continuous.comp_continuousOn (continuousOn_hopfMap hf)

lemma hopfLp_coe_ae (f : C(X,ℝ)) {t : ℝ} (ht : 0 < t) :
    (hopfLp m f t : X → ℝ) =ᵐ[m] hopfLax f t := by
  apply (ContinuousMap.coeFn_toLp m (hopfMap f t)).trans
  exact Eventually.of_forall (hopfMap_apply_pos f ht)

omit [CompactSpace X] in
lemma integrable_localSlope_sq {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    Integrable (fun x => (localSlope f x).toReal^2) m := by
  apply Integrable.of_bound (((measurable_localSlope hf.continuous).ennreal_toReal.pow_const 2).aestronglyMeasurable)
    ((L:ℝ)^2)
  refine Eventually.of_forall fun x => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have H := ENNReal.toReal_mono (by simp : (L:ℝ≥0∞) ≠ ∞) (localSlope_le_lipschitz hf x)
  simpa only [ENNReal.coe_toReal] using (sq_le_sq₀ ENNReal.toReal_nonneg L.coe_nonneg).mpr H

omit [CompactSpace X] in
lemma cheegerEnergy_le_integral_localSlope {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (hm : MemLp f 2 m) :
    cheegerEnergy m f ≤ ENNReal.ofReal ((∫ x, (localSlope f x).toReal^2 ∂m)/2) := by
  have H := cheegerEnergy_le_liminf hm (fs := fun _ => f)
    (fun _ => ⟨⟨L,hf⟩,hm⟩) (by simp)
  rw [liminf_const] at H
  have he : (∫⁻ x, localSlope f x^2 ∂m) = ENNReal.ofReal (∫ x, (localSlope f x).toReal^2 ∂m) := by
    rw [ofReal_integral_eq_lintegral_ofReal (integrable_localSlope_sq m hf)
      (Eventually.of_forall fun _ => sq_nonneg _)]
    apply lintegral_congr
    intro x
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal ((localSlope_le_lipschitz hf x).trans_lt (by simp)).ne]
  rw [he] at H
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2), ENNReal.ofReal_ofNat]
  simpa only [div_eq_mul_inv, mul_comm] using H

lemma hopfLp_energy_bound (f : C(X,ℝ)) {t : ℝ} (ht : 0 < t) :
    cheegerEnergy m (hopfLp m f t : X → ℝ) < ∞ ∧
      (cheegerEnergy m (hopfLp m f t : X → ℝ)).toReal ≤
        (∫ x, (localSlope (hopfLax f t) x).toReal^2 ∂m)/2 := by
  have hf := hopfLax_lipschitz_radius f.continuous (fun x => (continuousMap_bounds f x).1)
    (fun x => (continuousMap_bounds f x).2) (by linarith [norm_nonneg f]) ht
    (Real.sqrt_nonneg (2*t*(‖f‖-(-‖f‖)))) (Real.sq_sqrt (by have := norm_nonneg f; nlinarith : 0 ≤ 2*t*(‖f‖-(-‖f‖)))).ge
  have hm : MemLp (hopfLax f t) 2 m := (memLp_congr_ae (hopfLp_coe_ae m f ht)).mp (Lp.memLp (hopfLp m f t))
  have H := cheegerEnergy_le_integral_localSlope m hf hm
  rw [← cheegerEnergy_congr_ae (hopfLp_coe_ae m f ht)] at H
  have hfin := H.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hfin, ?_⟩
  have Hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top H
  rwa [ENNReal.toReal_ofReal (by positivity)] at Hr

end WeakHessianTransport

end
end InlinedFile0

end OAI
