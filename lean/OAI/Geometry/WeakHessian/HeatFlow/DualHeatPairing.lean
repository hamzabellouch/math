import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.CompactHeatPairing

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile78
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]

lemma quadratic_dual_integral_le_cost (μ ν : ProbabilityMeasure X) (o : X)
    (hμ : Integrable (fun x => dist x o^2) (μ:Measure X))
    (hν : Integrable (fun x => dist x o^2) (ν:Measure X))
    {f g : X → ℝ} (hf : Continuous f) (hg : Continuous g)
    {B C A : ℝ} (hfB : ∀ x,|f x| ≤ B) (hgC : ∀ x,|g x| ≤ C)
    (hdual : ∀ x y,f x-g y ≤ A*dist x y^2) :
    (∫ x,f x ∂(μ:Measure X))-(∫ x,g x ∂(ν:Measure X)) ≤
      A*quadraticWassersteinSq (μ:Measure X) (ν:Measure X) := by
  obtain ⟨q,hqp,hq,hqt⟩ := exists_optimal_coupling_of_moments μ ν o hμ hν
  let : IsProbabilityMeasure q := hqp
  have hfq : Integrable (fun p : X×X => f p.1) q := Integrable.of_bound
    (hf.comp continuous_fst).aestronglyMeasurable B (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hfB p.1)
  have hgq : Integrable (fun p : X×X => g p.2) q := Integrable.of_bound
    (hg.comp continuous_snd).aestronglyMeasurable C (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hgC p.2)
  have H := integral_mono_ae (hfq.sub hgq)
    ((integrable_squared_distance_of_cost hqt).const_mul A) (ae_of_all _ fun p : X×X => hdual p.1 p.2)
  simp only [Pi.sub_apply] at H
  rw [integral_sub hfq hgq,integral_const_mul,
    ← integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable,
    ← integral_map measurable_snd.aemeasurable hg.aestronglyMeasurable,hq.1.1,hq.1.2] at H
  have he : quadraticWassersteinSq (μ:Measure X) (ν:Measure X) = ∫ p : X×X,dist p.1 p.2^2 ∂q := by
    rw [hq.quadraticWassersteinSq_eq,quadraticTransportCost_eq_integral hqt,ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
  simpa only [he] using H

variable {m : Measure X} [SigmaFinite m]

lemma RCD.cheegerHeat_dual_pairing_balls {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) {f g : X → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hf2 : MemLp f 2 m) (hg2 : MemLp g 2 m)
    {D E A : ℝ} (hfB : ∀ x,|f x| ≤ D) (hgB : ∀ x,|g x| ≤ E) (hA : 0 ≤ A)
    (hdual : ∀ x y,f x-g y ≤ A*dist x y^2)
    (u v : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m,0 ≤ u x) (hvn : ∀ᵐ x ∂m,0 ≤ v x)
    (hum : ∫ x,u x ∂m = 1) (hvm : ∫ x,v x ∂m = 1)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (huB : ∀ᵐ x ∂m,|u x| ≤ B) (hvC : ∀ᵐ x ∂m,|v x| ≤ C)
    (a b : X) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hsu : ∀ᵐ x ∂m,r < dist x a → u x = 0) (hsv : ∀ᵐ x ∂m,s < dist x b → v x = 0)
    {t : ℝ} (ht : 0 ≤ t) :
    ⟪cheegerHeat h t (hf2.toLp f),u⟫_ℝ-⟪cheegerHeat h t (hg2.toLp g),v⟫_ℝ ≤
      A*Real.exp (-2*K*t)*(r+s+dist a b)^2 := by
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
  have H := quadratic_dual_integral_le_cost (μ t) (ν t) a
    (hrcd.1.heatProbability_moment hN hfull hfin a h u hun hum hsu ht)
    (hrcd.1.heatProbability_moment hN hfull hfin a h v hvn hvm hsv' ht) hf hg hfB hgB hdual
  have hc := hrcd.cheegerHeat_contraction_compact hN hfull hfin a h u v hun hvn hum hvm
    hB hC huB hvC hsu hsv' μ ν hμ hν ht
  have hμ0 : (μ 0:Measure X) = densityMeasure m u := by rw [hμ 0 le_rfl,cheegerHeat_zero h]; rfl
  have hν0 : (ν 0:Measure X) = densityMeasure m v := by rw [hν 0 le_rfl,cheegerHeat_zero h]; rfl
  have h0 := quadraticWassersteinSq_le_of_balls (μ 0) (ν 0) a b hr hs
    (by rw [hμ0]; exact densityMeasure_ae_ball u a hsu)
    (by rw [hν0]; exact densityMeasure_ae_ball v b hsv)
  have hc' : quadraticWassersteinSq (μ t:Measure X) (ν t:Measure X) ≤
      Real.exp (-2*K*t)*(r+s+dist a b)^2 := by
    have H := mul_le_mul_of_nonneg_left (hc.trans h0) (Real.exp_pos (-2*K*t)).le
    have he : Real.exp (-2*K*t)*Real.exp (2*K*t) = 1 := by
      rw [← Real.exp_add, show -2*K*t+2*K*t = 0 by ring, Real.exp_zero]
    simpa only [← mul_assoc,he,one_mul] using H
  have huI : (∫ x,f x ∂(μ t:Measure X)) = ⟪cheegerHeat h t (hf2.toLp f),u⟫_ℝ := by
    rw [hμ t ht,← cheegerHeat_density_duality h u _ ht hun]
    apply integral_congr_ae
    exact (densityMeasure_ac m _).ae_le hf2.coeFn_toLp.symm
  have hvI : (∫ x,g x ∂(ν t:Measure X)) = ⟪cheegerHeat h t (hg2.toLp g),v⟫_ℝ := by
    rw [hν t ht,← cheegerHeat_density_duality h v _ ht hvn]
    apply integral_congr_ae
    exact (densityMeasure_ac m _).ae_le hg2.coeFn_toLp.symm
  rw [huI,hvI] at H
  exact H.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hc' hA)
end WeakHessian

end
end InlinedFile78

end OAI
