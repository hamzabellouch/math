import Mathlib
import OAI.Geometry.WeakHessian.Transport.PlanEnergy

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile36
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X]

omit [TopologicalSpace.SeparableSpace X] in
lemma hopf_dual_le_planEnergy (μ ν : ProbabilityMeasure X)
    {π : Measure (Curve X)} [IsProbabilityMeasure π]
    (hi : Integrable (fun γ : Curve X => dist (γ timeZero) (γ timeOne)^2) π)
    (h0 : interpolation π timeZero = (μ:Measure X))
    (h1 : interpolation π timeOne = (ν:Measure X)) (f : X →ᵇ ℝ) :
    (∫ x, WeakHessianTransport.hopfLax f 1 x ∂(μ:Measure X))-(∫ x,f x ∂(ν:Measure X)) ≤ planEnergy π/2 := by
  let Q := WeakHessianTransport.boundedHopfMap f 1
  have he : (Q:X → ℝ) = WeakHessianTransport.hopfLax f 1 :=
    funext (WeakHessianTransport.boundedHopfMap_apply_pos f (by norm_num))
  have iQ : Integrable (fun γ : Curve X => Q (γ timeZero)) π :=
    Integrable.of_bound (Q.continuous.comp (continuous_eval_const timeZero)).aestronglyMeasurable ‖Q‖
      (ae_of_all _ fun γ => Q.norm_coe_le_norm (γ timeZero))
  have iF : Integrable (fun γ : Curve X => f (γ timeOne)) π :=
    Integrable.of_bound (f.continuous.comp (continuous_eval_const timeOne)).aestronglyMeasurable ‖f‖
      (ae_of_all _ fun γ => f.norm_coe_le_norm (γ timeOne))
  have H : (∫ γ,Q (γ timeZero)-f (γ timeOne) ∂π) ≤ planEnergy π/2 := by
    apply le_trans (integral_mono (iQ.sub iF) (hi.div_const 2) ?_)
    · exact le_of_eq (integral_div _ _)
    · intro γ
      rw [he]
      have h := WeakHessianTransport.hopfLax_le_objective
        (fun x => (WeakHessianTransport.boundedContinuous_bounds f x).1)
        (by norm_num : (0:ℝ)<1) (γ timeZero) (γ timeOne)
      simp only [WeakHessianTransport.hopfObjective,mul_one] at h
      dsimp only [Pi.sub_apply]
      linarith
  rw [integral_sub iQ iF] at H
  have eq0 : (∫ γ,Q (γ timeZero) ∂π) = ∫ x,Q x ∂(μ:Measure X) := by
    rw [← h0]
    exact (integral_map (continuous_eval_const timeZero).measurable.aemeasurable Q.continuous.aestronglyMeasurable).symm
  have eq1 : (∫ γ,f (γ timeOne) ∂π) = ∫ x,f x ∂(ν:Measure X) := by
    rw [← h1]
    exact (integral_map (continuous_eval_const timeOne).measurable.aemeasurable f.continuous.aestronglyMeasurable).symm
  rw [eq0,eq1] at H
  simpa only [he] using H

lemma exists_coupling_of_energy_limit (μ ν : ProbabilityMeasure X)
    (μs : ℕ → ProbabilityMeasure X) (hμs : Tendsto μs atTop (𝓝 μ))
    (ps : ℕ → ProbabilityMeasure (Curve X))
    (hi : ∀ n, Integrable (fun γ : Curve X => dist (γ timeZero) (γ timeOne)^2) (ps n:Measure (Curve X)))
    (h0 : ∀ n, interpolation (ps n:Measure (Curve X)) timeZero = (μs n:Measure X))
    (h1 : ∀ n, interpolation (ps n:Measure (Curve X)) timeOne = (ν:Measure X))
    {E : ℝ} (hE : Tendsto (fun n => planEnergy (ps n:Measure (Curve X))) atTop (𝓝 E)) :
    ∃ q : Measure (X×X), IsProbabilityMeasure q ∧ IsCoupling q μ ν ∧ QuadraticTransportCost q ≤ ENNReal.ofReal E := by
  obtain ⟨q,hq,hq0,hq1,hcost⟩ := WeakHessianTransport.exists_proper_coupling_cost_of_hopf_bound
    (μ:Measure X) (ν:Measure X) E (by
      intro f hf
      have H := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμs (WeakHessianTransport.boundedHopfMap f 1)
      have he : (WeakHessianTransport.boundedHopfMap f 1:X → ℝ) = WeakHessianTransport.hopfLax f 1 :=
        funext (WeakHessianTransport.boundedHopfMap_apply_pos f (by norm_num))
      simp only [he] at H
      exact le_of_tendsto_of_tendsto' (H.sub_const _) (hE.div_const 2)
        (fun n => hopf_dual_le_planEnergy (μs n) ν (hi n) (h0 n) (h1 n) f))
  exact ⟨q,hq,⟨hq0,hq1⟩,hcost⟩

lemma planEnergy_le_coupling_of_restricted_contact
    {π : Measure (Curve X)} [IsProbabilityMeasure π] {q : Measure (X×X)}
    (hiq : QuadraticTransportCost q ≠ ∞)
    (μ ν : ProbabilityMeasure X) (hq : IsCoupling q μ ν)
    (h1 : interpolation π timeOne = (ν:Measure X))
    {φ ψ : X → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (hiφπ : Integrable φ (interpolation π timeZero)) (hiφμ : Integrable φ (μ:Measure X))
    (hiψν : Integrable ψ (ν:Measure X))
    {S : Set X} (hS : MeasurableSet S) (hs : ∀ᵐ y ∂(ν:Measure X), y ∈ S)
    (hd : ∀ x y, y ∈ S → φ x+ψ y ≤ dist x y^2/2)
    (hc : ∀ᵐ γ ∂π, φ (γ timeZero)+ψ (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2) :
    planEnergy π-(∫ p : X×X,dist p.1 p.2^2 ∂q) ≤
      2*((∫ x,φ x ∂interpolation π timeZero)-(∫ x,φ x ∂(μ:Measure X))) := by
  have iφπ := (integrable_map_measure hφ.aestronglyMeasurable (continuous_eval_const timeZero).measurable.aemeasurable).mp hiφπ
  have iψπ := (integrable_map_measure hψ.aestronglyMeasurable (continuous_eval_const timeOne).measurable.aemeasurable).mp (h1 ▸ hiψν)
  have iφq := (integrable_map_measure hφ.aestronglyMeasurable measurable_fst.aemeasurable).mp (hq.1 ▸ hiφμ)
  have iψq := (integrable_map_measure hψ.aestronglyMeasurable measurable_snd.aemeasurable).mp (hq.2 ▸ hiψν)
  simp only [Function.comp_def] at iφπ iψπ iφq iψq
  have hsq : ∀ᵐ p : X×X ∂q, p.2 ∈ S :=
    (ae_map_iff measurable_snd.aemeasurable hS).mp (hq.2 ▸ hs)
  have H : (∫ γ,φ (γ timeZero)+ψ (γ timeOne) ∂π) = planEnergy π/2 := by
    rw [integral_congr_ae hc]; exact integral_div _ _
  have J : (∫ p : X×X,φ p.1+ψ p.2 ∂q) ≤ (∫ p : X×X,dist p.1 p.2^2 ∂q)/2 := by
    apply (integral_mono_ae (iφq.add iψq) ((integrable_squared_distance_of_cost hiq).div_const 2)
      (hsq.mono fun p hp => hd p.1 p.2 hp)).trans
    exact le_of_eq (integral_div _ _)
  rw [integral_add iφπ iψπ,
    ← integral_map (continuous_eval_const timeZero).measurable.aemeasurable hφ.aestronglyMeasurable,
    ← integral_map (continuous_eval_const timeOne).measurable.aemeasurable hψ.aestronglyMeasurable] at H
  change (∫ x,φ x ∂interpolation π timeZero)+(∫ x,ψ x ∂interpolation π timeOne) = _ at H
  rw [h1] at H
  rw [integral_add iφq iψq,
    ← integral_map measurable_fst.aemeasurable hφ.aestronglyMeasurable,
    ← integral_map measurable_snd.aemeasurable hψ.aestronglyMeasurable,hq.1,hq.2] at J
  linarith
end WeakHessian

end
end InlinedFile36

end OAI
