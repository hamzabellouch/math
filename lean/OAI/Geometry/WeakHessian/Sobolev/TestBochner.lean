import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.GradientSquare
import OAI.Geometry.WeakHessian.Sobolev.SobolevBochner
import OAI.Geometry.WeakHessian.LocalBounds.CoreAlgebra

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile111
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.test_gradientSquare_sobolev {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {g : X → ℝ} (hg : IsTestFunction m g) :
    Sobolev m (fun x => (weakGradient m g x)^2) := by
  have hL := laplacian_isLaplacian hg.1
  let u := hL.1.1.toLp g
  let A := hL.2.1.toLp (laplacian m g)
  have hu : IsLaplacian m (u : X → ℝ) A := hL.congr_ae hL.1.1.coeFn_toLp.symm hL.2.1.coeFn_toLp.symm
  obtain ⟨L,hlip⟩ := hg.2.2.1
  have hgrad : weakGradient m (u : X → ℝ) =ᵐ[m] weakGradient m g := weakGradient_congr_ae hL.1.1.coeFn_toLp
  have HH := hrcd.gradientSquare_sobolev hN hfull hfin hrcd.2 o
    (hrcd.1.global_formGenerator_of_isLaplacian hfin o hrcd.2 u A hu)
    ((sobolev_congr_ae hL.2.1.coeFn_toLp.symm).mp hg.2.2.2) L.coe_nonneg
    (show ∀ᵐ x ∂m,weakGradient m (u : X → ℝ) x ≤ L from by
      filter_upwards [hgrad,weakGradient_le_lipschitz hfin hlip] with x hx hb
      rwa [hx])
  exact (sobolev_congr_ae (hgrad.pow_const 2)).mp HH

lemma RCD.test_gammaHalf_sobolev {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {g : X → ℝ} (hg : IsTestFunction m g) :
    Sobolev m (fun x => gamma m g g x/2) := by
  have HH := (hrcd.test_gradientSquare_sobolev hN hfull hfin o hg).const_mul (1/2)
  apply (sobolev_congr_ae _).mp HH
  filter_upwards [gamma_self (m := m) g] with x hx
  rw [hx]
  ring

lemma RCD.test_integratedBochner {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {g e : X → ℝ} (hg : IsTestFunction m g)
    {L : ℝ≥0} (hel : LipschitzWith L e) (hec : HasCompactSupport e)
    (hen : ∀ x,0 ≤ e x) :
    K*(∫ x,e x*gamma m g g x ∂m) ≤ integratedBochner m g e := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin _ Metric.isBounded_ball⟩⟩
  have hp := hrcd.1.global_localGradientParallelogram hfin o hrcd.2
  have hL := laplacian_isLaplacian hg.1
  let u := hL.1.1.toLp g
  let A := hL.2.1.toLp (laplacian m g)
  have hu : IsLaplacian m (u : X → ℝ) A := hL.congr_ae hL.1.1.coeFn_toLp.symm hL.2.1.coeFn_toLp.symm
  have hes := sobolev_of_lipschitz_compactSupport hfin hel hec
  let ξ := hes.1.toLp e
  have hξ := (sobolev_congr_ae hes.1.coeFn_toLp.symm).mp hes
  have hξi : Integrable (ξ : X → ℝ) m := (hel.continuous.integrable_of_hasCompactSupport hec).congr hes.1.coeFn_toLp.symm
  obtain ⟨C,hC⟩ := (hec.isCompact_range hel.continuous).isBounded |>.exists_norm_le
  have heB : ∀ x,|e x| ≤ |C| := fun x => by
    have HH : |e x| ≤ C := by simpa only [Real.norm_eq_abs] using hC (e x) ⟨x,rfl⟩
    exact HH.trans (le_abs_self C)
  have hgs := hrcd.test_gradientSquare_sobolev hN hfull hfin o hg
  have hgrad := weakGradient_congr_ae hL.1.1.coeFn_toLp
  have hqu : Sobolev m (fun x => (weakGradient m (u : X → ℝ) x)^2) := (sobolev_congr_ae (hgrad.pow_const 2).symm).mp hgs
  have HH := hrcd.original_bochner_sobolev_multiplier hN hfull hfin hrcd.2 o hu hξ hξi hel
    hes.1.coeFn_toLp.symm (ae_of_all m hen) (abs_nonneg C) (ae_of_all m heB) hqu
  have eq1 : (∫ x,e x*(weakGradient m (u : X → ℝ) x)^2 ∂m) = ∫ x,e x*gamma m g g x ∂m := by
    apply integral_congr_ae
    filter_upwards [hgrad,gamma_self (m := m) g] with x hx hy
    rw [hx,hy]
  have eq2 : (1/2)*(∫ x,gamma m e (fun y => (weakGradient m (u : X → ℝ) y)^2) x ∂m) =
      ∫ x,gamma m e (fun y => gamma m g g y/2) x ∂m := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    have heq : (fun y => gamma m g g y/2) =ᵐ[m] (fun y => (1/2)*(weakGradient m (u : X → ℝ) y)^2) := by
      filter_upwards [hgrad,gamma_self (m := m) g] with x hx hy
      rw [hx,hy]
      ring
    filter_upwards [gamma_congr_ae (m := m) (f := e) .rfl heq,
      gamma_const_mul_right hfin hp hes.2.1 hqu.2.1 (1/2)] with x hx hy
    rw [hx,hy]
  have eq3 : (∫ x,A x*(e x*A x+gamma m e u x) ∂m) =
      ∫ x,(e x*laplacian m g x+gamma m e g x)*laplacian m g x ∂m := by
    apply integral_congr_ae
    filter_upwards [hL.2.1.coeFn_toLp,gamma_congr_ae (m := m) (f := e) .rfl hL.1.1.coeFn_toLp] with x hx hy
    rw [hx,hy]
    ring
  rw [eq1,neg_mul,eq2,eq3] at HH
  exact HH
end WeakHessian

end
end InlinedFile111

end OAI
