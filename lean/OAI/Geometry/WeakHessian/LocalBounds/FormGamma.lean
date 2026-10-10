import Mathlib
import OAI.Geometry.WeakHessian.Entropy.LocalGradientParallelogramCheeger
import OAI.Geometry.WeakHessian.HeatFlow.DriftResolvent

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile163
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]
variable {K N : ℝ} (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m)
variable (h : QuadraticCheegerEnergy m) (o : X) {χ : X → ℝ} {L : ℝ≥0} (hχ : LipschitzWith L χ)

include hcd hfin o in
omit [CompleteSpace X] [SigmaFinite m] in
lemma CurvatureDimension.sobolev_formDomain (u : (cheeger_closedQuadraticEnergy h).domain) :
    Sobolev m ((u : Lp ℝ 2 m) : X → ℝ) := by
  exact (hcd.global_sobolev_iff_cheeger_lt_top hfin o (Lp.memLp (u : Lp ℝ 2 m))).mpr u.property

def CurvatureDimension.formGammaLp :
    (cheeger_closedQuadraticEnergy h).domain →ₗ[ℝ] Lp ℝ 2 m where
  toFun u := (memLp_gamma_of_lipschitz hfin (hcd.global_localGradientParallelogram hfin o h) hχ
    (hcd.sobolev_formDomain hfin h o u)).toLp (gamma m χ (u : Lp ℝ 2 m))
  map_add' u v := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_gamma_of_lipschitz hfin (hcd.global_localGradientParallelogram hfin o h) hχ (hcd.sobolev_formDomain hfin h o (u+v))),
      MemLp.coeFn_toLp (memLp_gamma_of_lipschitz hfin (hcd.global_localGradientParallelogram hfin o h) hχ (hcd.sobolev_formDomain hfin h o u)),
      MemLp.coeFn_toLp (memLp_gamma_of_lipschitz hfin (hcd.global_localGradientParallelogram hfin o h) hχ (hcd.sobolev_formDomain hfin h o v)),
      Lp.coeFn_add ((memLp_gamma_of_lipschitz hfin (hcd.global_localGradientParallelogram hfin o h) hχ (hcd.sobolev_formDomain hfin h o u)).toLp _)
        ((memLp_gamma_of_lipschitz hfin (hcd.global_localGradientParallelogram hfin o h) hχ (hcd.sobolev_formDomain hfin h o v)).toLp _),
      gamma_congr_ae (m := m) (f := χ) EventuallyEq.rfl (Lp.coeFn_add (u : Lp ℝ 2 m) (v : Lp ℝ 2 m)),
      gamma_add_right hfin (hcd.global_localGradientParallelogram hfin o h) (localSobolev_of_lipschitz hfin hχ)
        (hcd.sobolev_formDomain hfin h o u).2.1 (hcd.sobolev_formDomain hfin h o v).2.1] with x ha hb hc hd he hf
    simp only [ha,hd,Pi.add_apply,hb,hc]
    exact (he.trans hf)
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_gamma_of_lipschitz hfin (hcd.global_localGradientParallelogram hfin o h) hχ (hcd.sobolev_formDomain hfin h o (c • u))),
      MemLp.coeFn_toLp (memLp_gamma_of_lipschitz hfin (hcd.global_localGradientParallelogram hfin o h) hχ (hcd.sobolev_formDomain hfin h o u)),
      Lp.coeFn_smul c ((memLp_gamma_of_lipschitz hfin (hcd.global_localGradientParallelogram hfin o h) hχ (hcd.sobolev_formDomain hfin h o u)).toLp _),
      gamma_congr_ae (m := m) (f := χ) EventuallyEq.rfl (Lp.coeFn_smul c (u : Lp ℝ 2 m)),
      gamma_const_mul_right hfin (hcd.global_localGradientParallelogram hfin o h) (localSobolev_of_lipschitz hfin hχ)
        (hcd.sobolev_formDomain hfin h o u).2.1 c] with x ha hb hc hd he
    simp only [ha,hc,Pi.smul_apply,smul_eq_mul,hb,RingHom.id_apply]
    exact hd.trans he

omit [SigmaFinite m] in
lemma CurvatureDimension.formGammaLp_ae (u : (cheeger_closedQuadraticEnergy h).domain) :
    hcd.formGammaLp hfin h o hχ u =ᵐ[m] gamma m χ (u : Lp ℝ 2 m) := by
  exact (memLp_gamma_of_lipschitz hfin (hcd.global_localGradientParallelogram hfin o h) hχ
    (hcd.sobolev_formDomain hfin h o u)).coeFn_toLp

omit [CompleteSpace X] [SigmaFinite m] in
lemma CurvatureDimension.formDomain_gradient_norm_sq (u : (cheeger_closedQuadraticEnergy h).domain) :
    ‖(hcd.sobolev_formDomain hfin h o u).2.2.toLp (weakGradient m (u : Lp ℝ 2 m))‖^2 =
      2*(cheeger_closedQuadraticEnergy h).realEnergy u := by
  change _ = 2*(cheegerEnergy m ((u : Lp ℝ 2 m) : X → ℝ)).toReal
  rw [hcd.global_cheegerEnergy_toReal hfin o h (hcd.sobolev_formDomain hfin h o u),norm_toLp_sq_eq_integral]
  ring

omit [SigmaFinite m] in
lemma CurvatureDimension.formGammaLp_norm_le (u : (cheeger_closedQuadraticEnergy h).domain) :
    ‖hcd.formGammaLp hfin h o hχ u‖ ≤
      (2*(L:ℝ))*Real.sqrt ((cheeger_closedQuadraticEnergy h).realEnergy u) := by
  apply (norm_gamma_toLp_le hfin (hcd.global_localGradientParallelogram hfin o h) hχ
    (hcd.sobolev_formDomain hfin h o u)).trans
  have H := hcd.formDomain_gradient_norm_sq hfin h o u
  have Hs := Real.sq_sqrt ((cheeger_closedQuadraticEnergy h).realEnergy_quadratic.nonneg u)
  have hs := Real.sqrt_nonneg ((cheeger_closedQuadraticEnergy h).realEnergy u)
  have hn : ‖(hcd.sobolev_formDomain hfin h o u).2.2.toLp (weakGradient m (u : Lp ℝ 2 m))‖ ≤
      2*Real.sqrt ((cheeger_closedQuadraticEnergy h).realEnergy u) := by
    nlinarith only [H,Hs,hs,norm_nonneg ((hcd.sobolev_formDomain hfin h o u).2.2.toLp (weakGradient m (u : Lp ℝ 2 m)))]
  simpa only [mul_assoc,mul_left_comm (L:ℝ) 2] using mul_le_mul_of_nonneg_left hn L.coe_nonneg
end WeakHessian

end
end InlinedFile163

end OAI
