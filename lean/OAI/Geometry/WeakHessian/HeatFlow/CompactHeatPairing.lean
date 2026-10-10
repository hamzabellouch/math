import Mathlib
import OAI.Geometry.WeakHessian.Transport.LipschitzTransport
import OAI.Geometry.WeakHessian.LocalBounds.BoundedCost
import OAI.Geometry.WeakHessian.Transport.CompactContraction
import OAI.Geometry.WeakHessian.HeatFlow.HeatProbability

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile77
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable [SigmaFinite m]

omit [SigmaFinite m] in
lemma CurvatureDimension.heatProbability_moment {K N : ℝ} (hcd : CurvatureDimension m K N)
    (hN : 1 < N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m,0 ≤ u x)
    (hm : ∫ x,u x ∂m = 1) {R : ℝ} (hsu : ∀ᵐ x ∂m,R < dist x o → u x = 0)
    {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun x => dist x o^2) (hcd.heatProbability hN hfull hfin o h u hun hm t:Measure X) := by
  rw [hcd.heatProbability_coe hN hfull hfin o h u hun hm ht]
  obtain ⟨a,ha,hi,h2,hD,hh,hhi,hW⟩ := hcd.exists_comparison_confinement hN hfull hfin o
  simpa only [NNReal.coe_zero,add_zero] using densityMeasure_quadratic_integrable o 0 _
    (cheegerHeat_nonneg h ht u hun)
    (hcd.cheegerHeat_weighted hfin o h u (lipschitz_mul_dist o a)
      (memLp_exp_weight_of_supported u o ha.le hsu) ht).1 (hW 0).1

lemma sqrt_transport_contraction {c R z : ℝ} (hc : 0 ≤ c) (hR : 0 ≤ R)
    (h : Real.exp (2*z)*c ≤ R^2) : Real.sqrt c ≤ Real.exp (-z)*R := by
  have he : Real.exp (2*z) = (Real.exp z)^2 := by rw [two_mul,Real.exp_add,pow_two]
  rw [he] at h
  have hsq := Real.sq_sqrt hc
  have hmul : Real.exp z*Real.sqrt c ≤ R := by
    nlinarith [Real.exp_pos z,Real.sqrt_nonneg c]
  have H := mul_le_mul_of_nonneg_left hmul (Real.exp_pos (-z)).le
  simpa only [← mul_assoc,← Real.exp_add,neg_add_cancel,Real.exp_zero,one_mul] using H

lemma RCD.cheegerHeat_pairing_balls {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hf2 : MemLp f 2 m) {D : ℝ} (hfB : ∀ x,|f x| ≤ D)
    (u v : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m,0 ≤ u x) (hvn : ∀ᵐ x ∂m,0 ≤ v x)
    (hum : ∫ x,u x ∂m = 1) (hvm : ∫ x,v x ∂m = 1)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (huB : ∀ᵐ x ∂m,|u x| ≤ B) (hvC : ∀ᵐ x ∂m,|v x| ≤ C)
    (a b : X) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hsu : ∀ᵐ x ∂m,r < dist x a → u x = 0) (hsv : ∀ᵐ x ∂m,s < dist x b → v x = 0)
    {t : ℝ} (ht : 0 ≤ t) :
    |⟪cheegerHeat h t (hf2.toLp f),u⟫_ℝ-⟪cheegerHeat h t (hf2.toLp f),v⟫_ℝ| ≤
      (L:ℝ)*Real.exp (-K*t)*(r+s+dist a b) := by
  let μ := hrcd.1.heatProbability hN hfull hfin a h u hun hum
  let ν := hrcd.1.heatProbability hN hfull hfin a h v hvn hvm
  have hμ (t : ℝ) (ht : 0 ≤ t) : (μ t:Measure X) = densityMeasure m (cheegerHeat h t u) :=
    hrcd.1.heatProbability_coe hN hfull hfin a h u hun hum ht
  have hν (t : ℝ) (ht : 0 ≤ t) : (ν t:Measure X) = densityMeasure m (cheegerHeat h t v) :=
    hrcd.1.heatProbability_coe hN hfull hfin a h v hvn hvm ht
  have hsv' : ∀ᵐ x ∂m,s+dist b a < dist x a → v x = 0 := by
    filter_upwards [hsv] with x hx hh
    apply hx
    have := dist_triangle x b a
    linarith
  have hμm := hrcd.1.heatProbability_moment hN hfull hfin a h u hun hum hsu ht
  have hνm := hrcd.1.heatProbability_moment hN hfull hfin a h v hvn hvm hsv' ht
  have H := lipschitz_integral_sub_le_cost (μ t) (ν t) a hμm hνm hf hfB
  have hc := hrcd.cheegerHeat_contraction_compact hN hfull hfin a h u v hun hvn hum hvm
    hB hC huB hvC hsu hsv' μ ν hμ hν ht
  have hμ0 : (μ 0:Measure X) = densityMeasure m u := by rw [hμ 0 le_rfl,cheegerHeat_zero h]; rfl
  have hν0 : (ν 0:Measure X) = densityMeasure m v := by rw [hν 0 le_rfl,cheegerHeat_zero h]; rfl
  have h0 := quadraticWassersteinSq_le_of_balls (μ 0) (ν 0) a b hr hs
    (by rw [hμ0]; exact densityMeasure_ae_ball u a hsu)
    (by rw [hν0]; exact densityMeasure_ae_ball v b hsv)
  have hsq := sqrt_transport_contraction (show 0 ≤ quadraticWassersteinSq (μ t:Measure X) (ν t:Measure X) from ENNReal.toReal_nonneg) (show 0 ≤ r+s+dist a b by positivity)
    (show Real.exp (2*(K*t))*quadraticWassersteinSq (μ t:Measure X) (ν t:Measure X) ≤ (r+s+dist a b)^2 by
      simpa only [mul_assoc] using hc.trans h0)
  have huI : (∫ x,f x ∂(μ t:Measure X)) = ⟪cheegerHeat h t (hf2.toLp f),u⟫_ℝ := by
    rw [hμ t ht,← cheegerHeat_density_duality h u _ ht hun]
    apply integral_congr_ae
    exact (densityMeasure_ac m _).ae_le hf2.coeFn_toLp.symm
  have hvI : (∫ x,f x ∂(ν t:Measure X)) = ⟪cheegerHeat h t (hf2.toLp f),v⟫_ℝ := by
    rw [hν t ht,← cheegerHeat_density_duality h v _ ht hvn]
    apply integral_congr_ae
    exact (densityMeasure_ac m _).ae_le hf2.coeFn_toLp.symm
  rw [huI,hvI] at H
  exact H.trans (by simpa only [neg_mul,mul_assoc] using mul_le_mul_of_nonneg_left hsq L.coe_nonneg)
end WeakHessian

end
end InlinedFile77

end OAI
