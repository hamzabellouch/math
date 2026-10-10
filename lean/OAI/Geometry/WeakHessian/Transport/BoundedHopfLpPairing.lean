import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.CheegerClosedQuadraticEnergy
import OAI.Geometry.WeakHessian.HeatFlow.FormGeneratorYoung
import OAI.Geometry.WeakHessian.Transport.BoundedHopfMap

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
open WeakHessian MeasureTheory
open scoped InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [ProperSpace X]
  [MeasurableSpace X] [BorelSpace X] (m : Measure X) [IsFiniteMeasure m]

lemma boundedHopfLp_pairing_increment (f : X →ᵇ ℝ) {t s α : ℝ} (ht : 0 < t) (hts : t ≤ s)
    (hα : 0 ≤ α) (ρ : Lp ℝ 2 m) (hρ : ∀ᵐ x ∂m, α ≤ ρ x) :
    ⟪boundedHopfLp m f s-boundedHopfLp m f t,ρ⟫_ℝ ≤
      -(s-t)*t/s*α*(cheegerEnergy m (boundedHopfLp m f t : X → ℝ)).toReal := by
  have hs : 0 < s := ht.trans_le hts
  let k : ℝ := (s-t)*t/(2*s)
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hf := hopfLax_lipschitz_radius f.continuous (fun x => (boundedContinuous_bounds f x).1)
    (fun x => (boundedContinuous_bounds f x).2) (by linarith [norm_nonneg f]) ht
    (Real.sqrt_nonneg (2*t*(‖f‖-(-‖f‖))))
    (Real.sq_sqrt (by have := norm_nonneg f; nlinarith : 0 ≤ 2*t*(‖f‖-(-‖f‖)))).ge
  have he := (boundedHopfLp_energy_bound m f ht).2
  have HI := integral_mono_ae (L2.integrable_inner (boundedHopfLp m f s-boundedHopfLp m f t) ρ (𝕜 := ℝ))
    ((integrable_localSlope_sq m hf).const_mul (-k*α)) (show
      ∀ᵐ x ∂m, ⟪(boundedHopfLp m f s-boundedHopfLp m f t) x,ρ x⟫_ℝ ≤
      (-k*α)*(localSlope (hopfLax f t) x).toReal^2 from by
        filter_upwards [Lp.coeFn_sub (boundedHopfLp m f s) (boundedHopfLp m f t),
          boundedHopfLp_coe_ae m f hs, boundedHopfLp_coe_ae m f ht, hρ] with x hx hxs hxt hxρ
        rw [hx, Pi.sub_apply, hxs, hxt, RCLike.inner_apply, conj_trivial]
        have H := hopf_forward_increment f.continuous (fun x => (boundedContinuous_bounds f x).1)
          (fun x => (boundedContinuous_bounds f x).2) (by linarith [norm_nonneg f]) ht hts x
        have Hnorm : hopfLax f s x-hopfLax f t x ≤ -k*(localSlope (hopfLax f t) x).toReal^2 := by
          simpa only [k, neg_mul, neg_div] using H
        have H' := mul_le_mul_of_nonneg_left Hnorm (hα.trans hxρ)
        have H'' := mul_le_mul_of_nonpos_left hxρ
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk) (sq_nonneg ((localSlope (hopfLax f t) x).toReal)))
        change ρ x * (hopfLax f s x-hopfLax f t x) ≤ _
        calc
          _ ≤ ρ x * (-k*(localSlope (hopfLax f t) x).toReal^2) := H'
          _ = (-k*(localSlope (hopfLax f t) x).toReal^2)*ρ x := by ring
          _ ≤ (-k*(localSlope (hopfLax f t) x).toReal^2)*α := H''
          _ = _ := by ring)
  rw [integral_const_mul] at HI
  rw [L2.inner_def]
  apply HI.trans
  have H := mul_le_mul_of_nonpos_left he (by nlinarith [mul_nonneg hk hα] : -2*k*α ≤ 0)
  calc
    -k*α*(∫ x, (localSlope (hopfLax f t) x).toReal^2 ∂m) =
      (-2*k*α)*((∫ x, (localSlope (hopfLax f t) x).toReal^2 ∂m)/2) := by ring
    _ ≤ (-2*k*α)*(cheegerEnergy m (boundedHopfLp m f t : X → ℝ)).toReal := H
    _ = _ := by dsimp [k]; ring

end WeakHessianTransport

namespace WeakHessianTransport
open WeakHessian WeakHessianFunctional MeasureTheory
open scoped InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [ProperSpace X]
  [MeasurableSpace X] [BorelSpace X] (m : Measure X) [IsFiniteMeasure m]

lemma boundedHopfLp_transport_pairing_le (h : QuadraticCheegerEnergy m)
    {f : X →ᵇ ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {ρ u A : ℝ → Lp ℝ 2 m} {b α c C : ℝ}
    (hb : 0 ≤ b) (hα : 0 < α) (hρ : ContinuousOn ρ (Icc 0 b))
    (hlower : ∀ t ∈ Ico 0 b, ∀ᵐ x ∂m, α ≤ ρ t x)
    (hgen : ∀ t ∈ Ico 0 b, (cheeger_closedQuadraticEnergy h).IsFormGenerator (u t) (A t))
    (hener : ∀ t ∈ Ico 0 b, (cheegerEnergy m (u t : X → ℝ)).toReal ≤ C)
    (hderiv : ∀ t ∈ Ico 0 b, HasDerivWithinAt ρ (c • A t) (Ici t) t) :
    ⟪boundedHopfLp m f b,ρ b⟫_ℝ - ⟪BoundedContinuousFunction.toLp 2 m ℝ f,ρ 0⟫_ℝ ≤ b*c^2/α*C := by
  rcases hb.eq_or_lt with rfl | hb
  · simp [boundedHopfLp]
  have H (a : ℝ) (ha : 0 < a) (hab : a ≤ b) :
      ⟪boundedHopfLp m f b,ρ b⟫_ℝ - ⟪boundedHopfLp m f a,ρ a⟫_ℝ ≤ (b-a)*c^2/α*C := by
    have hsub : Icc a b ⊆ Icc 0 b := Icc_subset_Icc ha.le le_rfl
    have hq : ContinuousOn (boundedHopfLp m f) (Icc a b) := (continuousOn_boundedHopfLp m hf).mono
      (fun t ht => ha.le.trans ht.1)
    apply (cheeger_closedQuadraticEnergy h).transport_pairing_le ha hab hα hq (hρ.mono hsub)
    · intro t ht
      exact (boundedHopfLp_energy_bound m f (ha.trans_le ht.1)).1
    · intro t ht
      exact hgen t ⟨ha.le.trans ht.1,ht.2⟩
    · intro t ht
      exact hener t ⟨ha.le.trans ht.1,ht.2⟩
    · intro t ht
      exact hderiv t ⟨ha.le.trans ht.1,ht.2⟩
    · intro t ht s hs
      exact boundedHopfLp_pairing_increment m f (ha.trans_le ht.1) hs.1.le hα.le (ρ t)
        (hlower t ⟨ha.le.trans ht.1,ht.2⟩)
  have hq0 : Tendsto (boundedHopfLp m f) (𝓝[>] (0:ℝ)) (𝓝 (BoundedContinuousFunction.toLp 2 m ℝ f)) := by
    simpa only [boundedHopfLp, boundedHopfMap_zero] using
      ((continuousOn_boundedHopfLp m hf) 0 (by simp)).mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have hρ0 : Tendsto ρ (𝓝[>] (0:ℝ)) (𝓝 (ρ 0)) :=
    (hρ 0 ⟨le_rfl,hb.le⟩).mono_left (nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem ⟨le_rfl,hb⟩))
  have hleft : Tendsto (fun a : ℝ => ⟪boundedHopfLp m f b,ρ b⟫_ℝ-⟪boundedHopfLp m f a,ρ a⟫_ℝ)
      (𝓝[>] (0:ℝ)) (𝓝 (⟪boundedHopfLp m f b,ρ b⟫_ℝ-⟪BoundedContinuousFunction.toLp 2 m ℝ f,ρ 0⟫_ℝ)) :=
    tendsto_const_nhds.sub (hq0.inner hρ0)
  have hright : Tendsto (fun a : ℝ => (b-a)*c^2/α*C) (𝓝[>] (0:ℝ)) (𝓝 (b*c^2/α*C)) := by
    have hc : Continuous (fun a : ℝ => (b-a)*c^2/α*C) := by fun_prop
    simpa only [sub_zero] using (hc.tendsto (0:ℝ)).mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [Ioc_mem_nhdsGT hb] with a ha
  exact H a ha.1 ha.2

end WeakHessianTransport

open Set

end
end InlinedFile0

end OAI
