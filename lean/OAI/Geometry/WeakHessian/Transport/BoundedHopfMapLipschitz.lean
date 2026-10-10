import Mathlib
import OAI.Geometry.WeakHessian.Transport.BoundedHopfMap
import OAI.Geometry.WeakHessian.Entropy.FisherDensity

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessianTransport
open WeakHessian MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {m : Measure X}

omit [MeasurableSpace X] [BorelSpace X] in
lemma boundedHopfMap_lipschitz (f : X →ᵇ ℝ) {t : ℝ} (ht : 0 < t) :
    GloballyLipschitz (boundedHopfMap f t : X → ℝ) := by
  have H := hopfLax_lipschitz_radius f.continuous (fun x => (boundedContinuous_bounds f x).1)
    (fun x => (boundedContinuous_bounds f x).2) (by linarith [norm_nonneg f]) ht
    (Real.sqrt_nonneg (2*t*(‖f‖-(-‖f‖))))
    (Real.sq_sqrt (by have := norm_nonneg f; nlinarith : 0 ≤ 2*t*(‖f‖-(-‖f‖)))).ge
  have he : (boundedHopfMap f t : X → ℝ) = hopfLax f t := funext (boundedHopfMap_apply_pos f ht)
  rw [he]
  exact ⟨_,H⟩

omit [ProperSpace X] in
lemma integrable_bounded_pairing {u : X → ℝ} (hi : Integrable u m) (f : X →ᵇ ℝ) :
    Integrable (fun x => u x*f x) m :=
  hi.mul_bdd f.continuous.aestronglyMeasurable (ae_of_all _ fun x => f.norm_coe_le_norm x)

omit [BorelSpace X] [ProperSpace X] in
lemma norm_integral_bounded_pairing {u : X → ℝ} (hi : Integrable u m) (f : X →ᵇ ℝ) :
    ‖∫ x,u x*f x ∂m‖ ≤ ‖f‖*(∫ x,‖u x‖ ∂m) := by
  have H := norm_integral_le_of_norm_le (f := fun x => u x*f x) (hi.norm.const_mul ‖f‖) (by
    apply ae_of_all
    intro x
    rw [norm_mul,mul_comm ‖f‖]
    exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (norm_nonneg _))
  simpa only [integral_const_mul] using H

omit [ProperSpace X] in
lemma integral_bounded_pairing_sub_left {u v : X → ℝ} (hu : Integrable u m)
    (hv : Integrable v m) (q : X →ᵇ ℝ) :
    (∫ x,(v x-u x)*q x ∂m) = (∫ x,v x*q x ∂m)-(∫ x,u x*q x ∂m) := by
  rw [← integral_sub (integrable_bounded_pairing hv q) (integrable_bounded_pairing hu q)]
  exact integral_congr_ae (ae_of_all _ fun x => by ring)

omit [ProperSpace X] in
lemma integral_bounded_pairing_sub_right {u : X → ℝ} (hu : Integrable u m)
    (q r : X →ᵇ ℝ) :
    (∫ x,u x*(r-q) x ∂m) = (∫ x,u x*r x ∂m)-(∫ x,u x*q x ∂m) := by
  rw [← integral_sub (integrable_bounded_pairing hu r) (integrable_bounded_pairing hu q)]
  exact integral_congr_ae (ae_of_all _ fun x => by simp only [BoundedContinuousFunction.sub_apply]; ring)

omit [ProperSpace X] in
lemma integral_bounded_pairing_evolution {u v : X → ℝ} (hu : Integrable u m)
    (hv : Integrable v m) (q r : X →ᵇ ℝ) :
    (∫ x,v x*r x ∂m)-(∫ x,u x*q x ∂m) =
      (∫ x,u x*(r-q) x ∂m) + ((∫ x,v x*q x ∂m)-(∫ x,u x*q x ∂m)) +
      (∫ x,(v x-u x)*(r-q) x ∂m) := by
  rw [integral_bounded_pairing_sub_left hu hv,
    integral_bounded_pairing_sub_right hu,integral_bounded_pairing_sub_right hv]
  ring

lemma boundedHopfMap_L1_increment (hfin : FiniteOnBoundedSets m) (f : X →ᵇ ℝ)
    {u : X → ℝ} (hi : Integrable u m) (hu : ∀ᵐ x ∂m,0 ≤ u x)
    {t s : ℝ} (ht : 0 < t) (hts : t ≤ s) :
    (∫ x,u x*(boundedHopfMap f s-boundedHopfMap f t) x ∂m) ≤
      (-(s-t)*t/(2*s))*(∫ x,u x*(localSlope (boundedHopfMap f t) x).toReal^2 ∂m) := by
  obtain ⟨L,hL⟩ := boundedHopfMap_lipschitz f ht
  rw [← integral_const_mul]
  apply integral_mono_ae (integrable_bounded_pairing hi _) ((integrable_density_slope_sq hfin hi hL).const_mul _)
  filter_upwards [hu] with x hx
  have H := mul_le_mul_of_nonneg_left (hopf_forward_increment f.continuous
    (fun x => (boundedContinuous_bounds f x).1) (fun x => (boundedContinuous_bounds f x).2)
    (by linarith [norm_nonneg f]) ht hts x) hx
  have hqt : (boundedHopfMap f t : X → ℝ) = hopfLax f t := funext (boundedHopfMap_apply_pos f ht)
  simpa only [BoundedContinuousFunction.sub_apply,boundedHopfMap_apply_pos f ht,
    boundedHopfMap_apply_pos f (ht.trans_le hts),hqt,mul_left_comm,mul_assoc] using H

omit [ProperSpace X] in
lemma tendsto_bounded_pairing_L1 {ι : Type*} {l : Filter ι}
    {u : ι → X → ℝ} {v : X → ℝ} (hu : ∀ i,Integrable (u i) m) (hv : Integrable v m)
    {q : ι → X →ᵇ ℝ} {r : X →ᵇ ℝ} (hq : Tendsto q l (𝓝 r))
    (hL1 : Tendsto (fun i => ∫ x,‖u i x-v x‖ ∂m) l (𝓝 0)) :
    Tendsto (fun i => ∫ x,u i x*q i x ∂m) l (𝓝 (∫ x,v x*r x ∂m)) := by
  have hD : Tendsto (fun i => ‖q i-r‖) l (𝓝 0) := by
    simpa only [sub_self,norm_zero] using (hq.sub (tendsto_const_nhds (x := r))).norm
  have H (i : ι) : ‖(∫ x,u i x*q i x ∂m)-(∫ x,v x*r x ∂m)‖ ≤
      ‖q i-r‖*(∫ x,‖v x‖ ∂m)+‖q i‖*(∫ x,‖u i x-v x‖ ∂m) := by
    have he : (∫ x,u i x*q i x ∂m)-(∫ x,v x*r x ∂m) =
        (∫ x,v x*(q i-r) x ∂m)+(∫ x,(u i x-v x)*q i x ∂m) := by
      rw [integral_bounded_pairing_sub_right hv,integral_bounded_pairing_sub_left hv (hu i)]
      ring
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add (norm_integral_bounded_pairing hv _)
      (norm_integral_bounded_pairing ((hu i).sub hv) _))
  rw [← tendsto_sub_nhds_zero_iff]
  apply squeeze_zero_norm H
  simpa only [zero_mul,mul_zero,add_zero] using (hD.mul_const _).add (hq.norm.mul hL1)

lemma hopf_L1_upper_slope (hfin : FiniteOnBoundedSets m) (f : X →ᵇ ℝ)
    {ρ : ℝ → X → ℝ} (hi : ∀ s,0 ≤ s → Integrable (ρ s) m)
    {t A : ℝ} (ht : 0 < t) (hpos : ∀ᵐ x ∂m,0 ≤ ρ t x)
    (hL1 : Tendsto (fun s => ∫ x,‖ρ s x-ρ t x‖ ∂m) (𝓝[>] t) (𝓝 0))
    (hd : HasDerivWithinAt (fun s => ∫ x,ρ s x*boundedHopfMap f t x ∂m) A (Ici t) t)
    {r : ℝ} (hr : A-(∫ x,ρ t x*(localSlope (boundedHopfMap f t) x).toReal^2 ∂m)/2 < r) :
    ∀ᶠ s in 𝓝[>] t, slope (fun z => ∫ x,ρ z x*boundedHopfMap f z x ∂m) t s < r := by
  let D := ∫ x,ρ t x*(localSlope (boundedHopfMap f t) x).toReal^2 ∂m
  let C := 2*‖f‖/t
  let H (s : ℝ) := (∫ x,ρ s x*boundedHopfMap f t x ∂m)
  let J (s : ℝ) := (∫ x,ρ s x*boundedHopfMap f s x ∂m)
  have hds : Tendsto (slope H t) (𝓝[>] t) (𝓝 A) :=
    (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl t)).mp hd.Ioi_of_Ici
  have hrat : Tendsto (fun s : ℝ => -t/(2*s)*D) (𝓝[>] t) (𝓝 (-D/2)) := by
    have hid : Tendsto (fun s : ℝ => s) (𝓝[>] t) (𝓝 t) := tendsto_id.mono_left nhdsWithin_le_nhds
    have H := ((tendsto_const_nhds (x := -t)).div
      (hid.const_mul 2) (by positivity : 2*t ≠ 0)).mul_const D
    have he : -t/(2*t)*D = -D/2 := by field_simp [ht.ne']
    rw [he] at H
    exact H
  have hl : Tendsto (fun s => -t/(2*s)*D+slope H t s+C*(∫ x,‖ρ s x-ρ t x‖ ∂m))
      (𝓝[>] t) (𝓝 (A-D/2)) := by
    simpa only [mul_zero, add_zero, neg_div, neg_add_eq_sub] using
      (hrat.add hds).add (hL1.const_mul C)
  filter_upwards [hl.eventually_lt_const hr,self_mem_nhdsWithin] with s hs hst
  have hst' : 0 < s-t := sub_pos.mpr hst
  have hs0 : 0 ≤ s := (ht.trans hst).le
  have hqt : ‖boundedHopfMap f s-boundedHopfMap f t‖ ≤ C*(s-t) := by
    have H := (boundedHopfMap_time_lipschitz f ht).dist_le_mul s (show s ∈ Ici t from (show t ≤ s from hst.le)) t (show t ∈ Ici t from (show t ≤ t from le_rfl))
    change dist (boundedHopfMap f s) (boundedHopfMap f t) ≤ (2*‖f‖/t)*dist s t at H
    simpa only [dist_eq_norm,Real.norm_eq_abs,abs_of_pos hst',C] using H
  have hcross : (∫ x,(ρ s x-ρ t x)*(boundedHopfMap f s-boundedHopfMap f t) x ∂m)/(s-t) ≤
      C*(∫ x,‖ρ s x-ρ t x‖ ∂m) := by
    have H := (le_abs_self _).trans (norm_integral_bounded_pairing ((hi s hs0).sub (hi t ht.le))
      (boundedHopfMap f s-boundedHopfMap f t))
    simp only [Pi.sub_apply] at H
    apply (div_le_iff₀ hst').mpr
    have H' := H.trans (mul_le_mul_of_nonneg_right hqt (integral_nonneg fun x => norm_nonneg _))
    convert H' using 1
    ring
  have hdq : (∫ x,ρ t x*(boundedHopfMap f s-boundedHopfMap f t) x ∂m)/(s-t) ≤
      -t/(2*s)*D := by
    have H := div_le_div_of_nonneg_right (boundedHopfMap_L1_increment hfin f (hi t ht.le) hpos ht hst.le) hst'.le
    have he : (-(s-t)*t/(2*s)*D)/(s-t) = -t/(2*s)*D := by field_simp
    exact H.trans_eq he
  have he : slope J t s =
      (∫ x,ρ t x*(boundedHopfMap f s-boundedHopfMap f t) x ∂m)/(s-t)+slope H t s+
      (∫ x,(ρ s x-ρ t x)*(boundedHopfMap f s-boundedHopfMap f t) x ∂m)/(s-t) := by
    rw [slope_def_field,slope_def_field]
    change (J s-J t)/(s-t) = _
    rw [show J s-J t = _ from integral_bounded_pairing_evolution (hi t ht.le) (hi s hs0) _ _]
    dsimp only [H]
    ring
  change slope J t s < r
  rw [he]
  exact lt_of_le_of_lt (add_le_add (add_le_add hdq le_rfl) hcross) hs
end WeakHessianTransport
end

end OAI
