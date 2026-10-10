import Mathlib
import OAI.Geometry.WeakHessian.Transport.HopfMap

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
open scoped InnerProductSpace

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (m : Measure X) [IsFiniteMeasure m]

lemma hopfLp_pairing_increment (f : C(X,ℝ)) {t s α : ℝ} (ht : 0 < t) (hts : t ≤ s)
    (hα : 0 ≤ α) (ρ : Lp ℝ 2 m) (hρ : ∀ᵐ x ∂m, α ≤ ρ x) :
    ⟪hopfLp m f s-hopfLp m f t,ρ⟫_ℝ ≤
      -(s-t)*t/s*α*(cheegerEnergy m (hopfLp m f t : X → ℝ)).toReal := by
  have hs : 0 < s := ht.trans_le hts
  let k : ℝ := (s-t)*t/(2*s)
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hf := hopfLax_lipschitz_radius f.continuous (fun x => (continuousMap_bounds f x).1)
    (fun x => (continuousMap_bounds f x).2) (by linarith [norm_nonneg f]) ht
    (Real.sqrt_nonneg (2*t*(‖f‖-(-‖f‖))))
    (Real.sq_sqrt (by have := norm_nonneg f; nlinarith : 0 ≤ 2*t*(‖f‖-(-‖f‖)))).ge
  have he := (hopfLp_energy_bound m f ht).2
  have HI := integral_mono_ae (L2.integrable_inner (hopfLp m f s-hopfLp m f t) ρ (𝕜 := ℝ))
    ((integrable_localSlope_sq m hf).const_mul (-k*α)) (show
      ∀ᵐ x ∂m, ⟪(hopfLp m f s-hopfLp m f t) x,ρ x⟫_ℝ ≤
      (-k*α)*(localSlope (hopfLax f t) x).toReal^2 from by
        filter_upwards [Lp.coeFn_sub (hopfLp m f s) (hopfLp m f t),
          hopfLp_coe_ae m f hs, hopfLp_coe_ae m f ht, hρ] with x hx hxs hxt hxρ
        rw [hx, Pi.sub_apply, hxs, hxt, RCLike.inner_apply, conj_trivial]
        have H := hopf_forward_increment f.continuous (fun x => (continuousMap_bounds f x).1)
          (fun x => (continuousMap_bounds f x).2) (by linarith [norm_nonneg f]) ht hts x
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
    _ ≤ (-2*k*α)*(cheegerEnergy m (hopfLp m f t : X → ℝ)).toReal := H
    _ = _ := by dsimp [k]; ring

end WeakHessianTransport

end
end InlinedFile0

end OAI
