import Mathlib
import OAI.Geometry.WeakHessian.Entropy.EntropySlope

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]

omit [CompleteSpace X] [ProperSpace X] in
lemma coupling_firstMoment_le {μ ν : Measure X} {p : Measure (X×X)}
    [IsProbabilityMeasure p] (hp : IsCoupling p μ ν) (o : X)
    (hμ : Integrable (fun x => dist x o) μ) {r A : ℝ} (hA : 0 ≤ A)
    (hs : ∀ᵐ x ∂ν,dist x o ≤ r) (hc : QuadraticTransportCost p ≤ ENNReal.ofReal A) :
    (∫ x,dist x o ∂μ) ≤ r+Real.sqrt A := by
  have hpt : QuadraticTransportCost p ≠ ∞ := ne_of_lt (hc.trans_lt ENNReal.ofReal_lt_top)
  have hd : MemLp (fun z : X×X => dist z.1 z.2) 2 p :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr (integrable_squared_distance_of_cost hpt)
  have hdf := (integrable_map_measure (by fun_prop : AEStronglyMeasurable (fun x => dist x o) (p.map Prod.fst))
    measurable_fst.aemeasurable).mp (by rwa [hp.1])
  have hs' : ∀ᵐ z : X×X ∂p,dist z.2 o ≤ r :=
    ae_of_ae_map (μ := p) (f := Prod.snd) measurable_snd.aemeasurable (by rwa [hp.2])
  have hm : (∫ z : X×X,dist z.1 o ∂p) ≤ (∫ z : X×X,dist z.1 z.2 ∂p)+r := by
    have H := integral_mono_ae hdf ((hd.integrable (by norm_num)).add (integrable_const r))
      (hs'.mono fun z hz => by
        change dist z.1 o ≤ dist z.1 z.2+r
        linarith [dist_triangle z.1 z.2 o])
    simpa only [Function.comp_apply,Pi.add_apply,integral_add (hd.integrable (by norm_num)) (integrable_const r),
      integral_const,probReal_univ,one_smul] using H
  have hcs : (∫ z : X×X,dist z.1 z.2 ∂p) ≤ Real.sqrt (∫ z : X×X,dist z.1 z.2^2 ∂p) := by
    simpa using integral_mul_le_sqrt_integral_sq hd (memLp_const (1:ℝ))
  have he : (∫ z : X×X,dist z.1 z.2^2 ∂p) ≤ A := by
    rw [quadraticTransportCost_eq_integral hpt] at hc
    exact (ENNReal.ofReal_le_ofReal_iff hA).mp hc
  rw [← hp.1,integral_map measurable_fst.aemeasurable (by fun_prop)]
  exact hm.trans (by linarith [hcs.trans (Real.sqrt_le_sqrt he)])

omit [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma lipschitz_integral_deviation {μ : Measure X} [IsProbabilityMeasure μ]
    (o : X) (hμ : Integrable (fun x => dist x o) μ)
    {F : X → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F) {C : ℝ} (hC : ∀ x,|F x| ≤ C) :
    |(∫ x,F x ∂μ)-F o| ≤ (L:ℝ)*(∫ x,dist x o ∂μ) := by
  have hi : Integrable F μ := Integrable.of_bound hF.continuous.aestronglyMeasurable C
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hC x)
  have H : |(∫ x,F x-F o ∂μ)| ≤ (L:ℝ)*(∫ x,dist x o ∂μ) := by
    apply abs_integral_le_integral_abs.trans
    rw [← integral_const_mul]
    apply integral_mono_ae (hi.sub (integrable_const _)).abs (hμ.const_mul _)
    exact ae_of_all _ fun x => by simpa only [Real.dist_eq,Pi.sub_apply] using hF.dist_le_mul x o
  simpa only [integral_sub hi (integrable_const _),integral_const,probReal_univ,one_smul] using H

lemma firstMoment_entropy_absorption {y r T D a C c : ℝ}
    (hy : 0 ≤ y) (hr : 0 ≤ r) (hT : 0 ≤ T) (hD : 0 ≤ D)
    (ha : 0 ≤ a) (hC : 0 ≤ C) (hc : 0 ≤ c)
    (H : y ≤ r+Real.sqrt (2*T*(D+2*a*C+c*y))) :
    y^2 ≤ 4*r^2+8*T*D+16*(T*a)*C+16*T^2*c^2 := by
  have hq : 0 ≤ 2*T*(D+2*a*C+c*y) := by positivity
  have hs := Real.sq_sqrt hq
  have hsn := Real.sqrt_nonneg (2*T*(D+2*a*C+c*y))
  have h1 : y^2 ≤ 2*r^2+4*T*(D+2*a*C+c*y) := by
    have hyq := (sq_le_sq₀ hy (add_nonneg hr hsn)).mpr H
    nlinarith [sq_nonneg (r-Real.sqrt (2*T*(D+2*a*C+c*y)))]
  nlinarith [sq_nonneg (y-4*T*c)]

end WeakHessian

end
end

end OAI
