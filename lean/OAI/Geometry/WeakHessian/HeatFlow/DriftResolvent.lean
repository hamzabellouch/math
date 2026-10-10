import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.ReLp
import OAI.Geometry.WeakHessian.Sobolev.GlobalCheegerEnergyReal
import OAI.Geometry.WeakHessian.Calculus.NormLpSqIntegral
import OAI.Geometry.WeakHessian.Sobolev.CompContDiff2

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile148
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

def driftResolvent (h : QuadraticCheegerEnergy m) {τ : ℝ} (hτ : 0 < τ) : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m :=
  τ • ((cheeger_closedQuadraticEnergy h).scale hτ).resolventLinear

omit [BorelSpace X] [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma driftResolvent_formGenerator (h : QuadraticCheegerEnergy m) {τ : ℝ} (hτ : 0 < τ) (u : Lp ℝ 2 m) :
    (cheeger_closedQuadraticEnergy h).IsFormGenerator (driftResolvent h hτ u)
      (τ⁻¹ • driftResolvent h hτ u-u) := by
  let Q := cheeger_closedQuadraticEnergy h
  change Q.IsFormGenerator (τ • (Q.scale hτ).resolvent u)
    (τ⁻¹ • (τ • (Q.scale hτ).resolvent u)-u)
  rw [smul_smul,inv_mul_cancel₀ hτ.ne',one_smul]
  have H := Q.formGenerator_smul τ ((Q.scaled_resolvent_iff hτ u ((Q.scale hτ).resolvent u)).mp rfl)
  simpa only [smul_smul,mul_inv_cancel₀ hτ.ne',one_smul] using H

omit [CompleteSpace X] [SigmaFinite m] in
lemma CurvatureDimension.driftResolvent_isLaplacian {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m) (h : QuadraticCheegerEnergy m)
    (o : X) {τ : ℝ} (hτ : 0 < τ) (u : Lp ℝ 2 m) :
    IsLaplacian m (driftResolvent h hτ u) (τ⁻¹ • driftResolvent h hτ u-u : Lp ℝ 2 m) :=
  hcd.global_isLaplacian_of_formGenerator hfin o h _ _ (driftResolvent_formGenerator h hτ u)

omit [BorelSpace X] [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma driftResolvent_norm_le (h : QuadraticCheegerEnergy m) {τ : ℝ} (hτ : 0 < τ) (u : Lp ℝ 2 m) :
    ‖driftResolvent h hτ u‖ ≤ τ*‖u‖ := by
  rw [driftResolvent,smul_apply,norm_smul,Real.norm_of_nonneg hτ.le]
  apply mul_le_mul_of_nonneg_left _ hτ.le
  exact (((cheeger_closedQuadraticEnergy h).scale hτ).resolvent_norm_le_one.trans_eq rfl |> fun H =>
    (((cheeger_closedQuadraticEnergy h).scale hτ).resolventLinear.le_opNorm u).trans
      (by simpa using mul_le_mul_of_nonneg_right H (norm_nonneg u)))

omit [CompleteSpace X] [SigmaFinite m] in
lemma CurvatureDimension.driftResolvent_gradient_norm {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m) (h : QuadraticCheegerEnergy m)
    (o : X) {τ : ℝ} (hτ : 0 < τ) (u : Lp ℝ 2 m) :
    ‖(hcd.driftResolvent_isLaplacian hfin h o hτ u).1.2.2.toLp
      (weakGradient m (driftResolvent h hτ u))‖ ≤ Real.sqrt τ*‖u‖ := by
  let Q := cheeger_closedQuadraticEnergy h
  let z := (Q.scale hτ).resolvent u
  let r := driftResolvent h hτ u
  have he := Q.formGenerator_energy (driftResolvent_formGenerator h hτ u)
  have hs := (hcd.driftResolvent_isLaplacian hfin h o hτ u).1
  have hid : 2*(cheegerEnergy m (r : X → ℝ)).toReal = ‖hs.2.2.toLp (weakGradient m r)‖^2 := by
    rw [hcd.global_cheegerEnergy_toReal hfin o h hs,norm_toLp_sq_eq_integral]
    ring
  change 2*(cheegerEnergy m (r : X → ℝ)).toReal = -⟪τ⁻¹ • r-u,r⟫_ℝ at he
  rw [hid] at he
  have her : τ⁻¹ • r=z := by dsimp [r,driftResolvent,z]; rw [smul_apply,smul_smul,inv_mul_cancel₀ hτ.ne',one_smul]; rfl
  rw [her,inner_sub_left] at he
  have hzr : ⟪z,r⟫_ℝ=τ*‖z‖^2 := by change ⟪z,τ • z⟫_ℝ= _; rw [real_inner_smul_right,real_inner_self_eq_norm_sq]
  have hur : ⟪u,r⟫_ℝ=τ*⟪u,z⟫_ℝ := by change ⟪u,τ • z⟫_ℝ= _; rw [real_inner_smul_right]
  rw [hzr,hur] at he
  have hz : ‖z‖ ≤ ‖u‖ := by
    simpa only [(Q.scale hτ).resolvent_zero,sub_zero] using (Q.scale hτ).resolvent_nonexpansive u 0
  have hb : ‖hs.2.2.toLp (weakGradient m r)‖^2 ≤ τ*‖u‖^2 := by
    have H := mul_le_mul_of_nonneg_left ((real_inner_le_norm u z).trans
      (mul_le_mul_of_nonneg_left hz (norm_nonneg u))) hτ.le
    nlinarith only [he,H,mul_nonneg hτ.le (sq_nonneg ‖z‖)]
  have hr : (Real.sqrt τ*‖u‖)^2 = τ*‖u‖^2 := by rw [mul_pow,Real.sq_sqrt hτ.le]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  exact hb.trans_eq hr.symm

omit [ProperSpace X] [SigmaFinite m] in
lemma norm_gamma_toLp_le (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {V u : X → ℝ}
    {L : ℝ≥0} (hV : LipschitzWith L V) (hu : Sobolev m u) :
    ‖(memLp_gamma_of_lipschitz hfinite hpar hV hu).toLp (gamma m V u)‖ ≤
      (L:ℝ)*‖hu.2.2.toLp (weakGradient m u)‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(memLp_gamma_of_lipschitz hfinite hpar hV hu).coeFn_toLp,hu.2.2.coeFn_toLp,
    abs_gamma_le hfinite hpar (localSobolev_of_lipschitz hfinite hV) hu.2.1,
    weakGradient_le_lipschitz hfinite hV,weakGradient_nonneg (m := m) u]
    with x hb hd hab hv hn
  rw [hb,hd,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hn]
  exact hab.trans (mul_le_mul_of_nonneg_right hv hn)
end WeakHessian

end
end InlinedFile148

end OAI
