import Mathlib
import OAI.Geometry.WeakHessian.Calculus.GammaLimits
import OAI.Geometry.WeakHessian.LocalBounds.PotentialPairing

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile20
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X]
variable {m : Measure X}

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X] in
lemma entropy_pairing_twice (_ : FiniteOnBoundedSets m) {u φ : X → ℝ}
    (_ : LocalSobolev m u) (_ : LocalSobolev m φ) :
    (∫ x,2*u x*gamma m φ u x ∂m) = 2*(∫ x,u x*gamma m u φ x ∂m) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [gamma_comm (m := m) φ u] with x hx
  rw [hx]; ring

lemma CurvatureDimension.entropy_pairing_tendsto {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m)
    (hq : QuadraticCheegerEnergy m) (o : X) (R : ℝ≥0)
    {vs : ℕ → X → ℝ} {w : X → ℝ} (hvs : ∀ n, Sobolev m (vs n)) (hw : Sobolev m w)
    {A : ℝ} (hA : ∀ᵐ x ∂m, |w x| ≤ A)
    (hws : ∀ᵐ x ∂m, x ∉ Metric.closedBall o R → w x = 0)
    (hV : Tendsto (fun n => (hvs n).1.toLp (vs n)) atTop (𝓝 (hw.1.toLp w)))
    (hE : Tendsto (fun n => ‖((hvs n).sub hfin hw).2.2.toLp
      (weakGradient m (fun x => vs n x-w x))‖) atTop (𝓝 0))
    {M : ℝ} (hM : ∀ n, ‖(hvs n).2.2.toLp (weakGradient m (vs n))‖ ≤ M)
    {φs : ℕ → X → ℝ} {φ : X → ℝ} {L : ℝ≥0}
    (hφs : ∀ n, LipschitzWith L (φs n)) (hφ : LipschitzWith L φ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ n, |φs n o| ≤ B) (hbφ : |φ o| ≤ B)
    (hT : ∀ x, Tendsto (fun n => φs n x) atTop (𝓝 (φ x))) :
    Tendsto (fun n => ∫ x,2*vs n x*gamma m (φs n) (vs n) x ∂m) atTop
      (𝓝 (∫ x,2*w x*gamma m φ w x ∂m)) := by
  have hpar := hcd.global_localGradientParallelogram hfin o hq
  have hnorm : Tendsto (fun n => ‖((hvs n).1.sub hw.1).toLp (fun x => vs n x-w x)‖)
      atTop (𝓝 0) := by
    have he (n : ℕ) : ((hvs n).1.sub hw.1).toLp (fun x => vs n x-w x) =
        (hvs n).1.toLp (vs n)-hw.1.toLp w := MemLp.toLp_sub (hvs n).1 hw.1
    simp_rw [he]
    simpa only [sub_self,norm_zero] using (hV.sub_const (hw.1.toLp w)).norm
  have hboundT := ((hnorm.const_mul (L:ℝ)).mul_const M).add
    (hE.const_mul ((L:ℝ)*‖hw.1.toLp w‖))
  simp only [mul_zero,zero_mul,zero_add] at hboundT
  have hdiff : Tendsto (fun n => (∫ x,vs n x*gamma m (vs n) (φs n) x ∂m)-
      (∫ x,w x*gamma m w (φs n) x ∂m)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _) _ hboundT
    intro n
    rw [Real.norm_eq_abs]
    exact (weighted_gamma_root_difference_bound hfin hpar (hvs n) hw (hφs n)).trans
      (add_le_add (mul_le_mul_of_nonneg_left (hM n)
        (mul_nonneg L.coe_nonneg (norm_nonneg _))) le_rfl)
  have hg := hw.square_bounded hfin hA
  have hgs : ∀ᵐ x ∂m, x ∉ Metric.closedBall o R → w x^2 = 0 :=
    hws.mono fun x hx h => by rw [hx h]; norm_num
  have hfixed := hcd.potential_pairing_tendsto hfin hq o R hφs hφ hB hb hbφ hT hg hgs
  have he (v : X → ℝ) (hv : LipschitzWith L v) :
      (∫ x,gamma m v (fun x => w x^2) x ∂m) = 2*(∫ x,w x*gamma m w v x ∂m) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [gamma_comm (m := m) v (fun x => w x^2),
      gamma_square_bounded hfin hpar hw (localSobolev_of_lipschitz hfin hv) hA] with x hc hs
    rw [hc,hs]; ring
  have H := (hdiff.const_mul 2).add hfixed
  simp only [mul_zero,zero_add,he _ (hφs _),he φ hφ] at H
  simp_rw [entropy_pairing_twice hfin (hvs _).2.1 (localSobolev_of_lipschitz hfin (hφs _)),
    entropy_pairing_twice hfin hw.2.1 (localSobolev_of_lipschitz hfin hφ)]
  convert H using 1
  funext n
  ring
end WeakHessian

end
end InlinedFile20

end OAI
