import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.ResolventSmoothing
import OAI.Geometry.WeakHessian.HeatFlow.DriftResolvent

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile149
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]
variable {K N : ℝ} (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m)
variable (h : QuadraticCheegerEnergy m) (o : X) {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
variable {τ : ℝ} (hτ : 0 < τ)

def CurvatureDimension.driftPerturbation (u : Lp ℝ 2 m) : Lp ℝ 2 m :=
  (memLp_gamma_of_lipschitz hfin (hcd.global_localGradientParallelogram hfin o h) hV
    (hcd.driftResolvent_isLaplacian hfin h o hτ u).1).toLp (gamma m V (driftResolvent h hτ u))

omit [SigmaFinite m] in
lemma CurvatureDimension.driftPerturbation_ae (u : Lp ℝ 2 m) :
    hcd.driftPerturbation hfin h o hV hτ u =ᵐ[m] gamma m V (driftResolvent h hτ u) :=
  MemLp.coeFn_toLp _

omit [SigmaFinite m] in
lemma CurvatureDimension.driftPerturbation_norm (u : Lp ℝ 2 m) :
    ‖hcd.driftPerturbation hfin h o hV hτ u‖ ≤ (L:ℝ)*Real.sqrt τ*‖u‖ := by
  apply (norm_gamma_toLp_le hfin (hcd.global_localGradientParallelogram hfin o h) hV
    (hcd.driftResolvent_isLaplacian hfin h o hτ u).1).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hcd.driftResolvent_gradient_norm hfin h o hτ u) L.coe_nonneg

omit [SigmaFinite m] in
lemma CurvatureDimension.driftPerturbation_sub (u v : Lp ℝ 2 m) :
    hcd.driftPerturbation hfin h o hV hτ (u-v) =
      hcd.driftPerturbation hfin h o hV hτ u-hcd.driftPerturbation hfin h o hV hτ v := by
  let P := hcd.driftPerturbation hfin h o hV hτ
  let R := driftResolvent h hτ
  have hpar := hcd.global_localGradientParallelogram hfin o h
  have hSu := (hcd.driftResolvent_isLaplacian hfin h o hτ u).1
  have hSv := (hcd.driftResolvent_isLaplacian hfin h o hτ v).1
  have he : (R (u-v) : X → ℝ) =ᵐ[m] fun x => R u x-R v x := by
    rw [map_sub]
    exact Lp.coeFn_sub _ _
  have hg := gamma_congr_ae (m := m) (f := V) EventuallyEq.rfl he
  apply Lp.ext
  filter_upwards [hcd.driftPerturbation_ae hfin h o hV hτ (u-v),
    hcd.driftPerturbation_ae hfin h o hV hτ u,hcd.driftPerturbation_ae hfin h o hV hτ v,
    Lp.coeFn_sub (P u) (P v),hg,gamma_comm (m := m) V (fun x => R u x-R v x),
    gamma_sub_left hfin hpar hSu.2.1 hSv.2.1 (localSobolev_of_lipschitz hfin hV),
    gamma_comm (m := m) (R u) V,gamma_comm (m := m) (R v) V] with x ha hb hc hd he hf hi hj hk
  change P (u-v) x=(P u-P v) x
  rw [ha,hd]
  change gamma m V (R (u-v)) x=P u x-P v x
  rw [hb,hc,he,hf,hi,hj,hk]

omit [SigmaFinite m] in
lemma CurvatureDimension.driftPerturbation_lipschitz :
    LipschitzWith (Real.toNNReal ((L:ℝ)*Real.sqrt τ)) (hcd.driftPerturbation hfin h o hV hτ) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [dist_eq_norm,← hcd.driftPerturbation_sub hfin h o hV hτ,
    Real.coe_toNNReal _ (by positivity),dist_eq_norm]
  exact hcd.driftPerturbation_norm hfin h o hV hτ (u-v)

lemma RCD.driftPerturbation_bounded (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (u : Lp ℝ 2 m) {B : ℝ} (hB : 0 ≤ B)
    (hu : ∀ᵐ x ∂m,|u x| ≤ B) :
    ∀ᵐ x ∂m,|hrcd.1.driftPerturbation hfin h o hV hτ u x| ≤
      5*(L:ℝ)*B*Real.exp (|K| *τ)*Real.sqrt τ := by
  obtain ⟨g,hg,he⟩ := hrcd.cheeger_resolvent_lipschitz hN hfull hfin h o u hB hu hτ
  have he' : g =ᵐ[m] driftResolvent h hτ u := he
  have hpar := hrcd.1.global_localGradientParallelogram hfin o h
  have hSu := (hrcd.1.driftResolvent_isLaplacian hfin h o hτ u).1
  filter_upwards [hrcd.1.driftPerturbation_ae hfin h o hV hτ u,
    abs_gamma_le hfin hpar (localSobolev_of_lipschitz hfin hV) hSu.2.1,
    weakGradient_le_lipschitz hfin hV,weakGradient_le_lipschitz hfin hg,
    weakGradient_congr_ae he',weakGradient_nonneg (m := m) (driftResolvent h hτ u)] with x ha hb hc hd he hn
  rw [ha]
  rw [he,Real.coe_toNNReal _ (by positivity)] at hd
  calc
    _ ≤ weakGradient m V x*weakGradient m (driftResolvent h hτ u) x := hb
    _ ≤ (L:ℝ)*(5*B*Real.exp (|K| *τ)*Real.sqrt τ) := mul_le_mul hc hd hn L.coe_nonneg
    _ = _ := by ring
end WeakHessian

end
end InlinedFile149

end OAI
