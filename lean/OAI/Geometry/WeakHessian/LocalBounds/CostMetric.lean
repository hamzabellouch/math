import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.HeatCost
import OAI.Geometry.WeakHessian.LocalBounds.CostExistence

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile58
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]

omit [ProperSpace X] in
lemma cost_ne_top_iff_integrable_sq {q : Measure (X×X)} :
    QuadraticTransportCost q ≠ ∞ ↔ Integrable (fun p : X×X => dist p.1 p.2^2) q := by
  simpa only [QuadraticTransportCost,edist_dist,ENNReal.ofReal_pow dist_nonneg] using
    lintegral_ofReal_ne_top_iff_integrable
      (measurable_fst.dist measurable_snd |>.pow_const 2).aestronglyMeasurable
      (ae_of_all q fun p : X×X => sq_nonneg (dist p.1 p.2))

lemma product_coupling_finite_cost (μ ν : ProbabilityMeasure X) (o : X)
    (hμ : Integrable (fun x => dist x o^2) (μ:Measure X))
    (hν : Integrable (fun x => dist x o^2) (ν:Measure X)) :
    IsCoupling ((μ:Measure X).prod (ν:Measure X)) μ ν ∧
      QuadraticTransportCost ((μ:Measure X).prod (ν:Measure X)) ≠ ∞ := by
  refine ⟨⟨by simp [Measure.map_fst_prod],by simp [Measure.map_snd_prod]⟩,?_⟩
  apply cost_ne_top_iff_integrable_sq.mpr
  apply (((hμ.comp_fst (ν:Measure X)).add (hν.comp_snd (μ:Measure X))).const_mul 2).mono' (by fun_prop)
  exact ae_of_all _ fun p => by
    change |dist p.1 p.2^2| ≤ 2*(dist p.1 o^2+dist p.2 o^2)
    rw [abs_of_nonneg (sq_nonneg _)]
    have H := dist_triangle p.1 o p.2
    rw [dist_comm o p.2] at H
    nlinarith [dist_nonneg (x := p.1) (y := p.2),sq_nonneg (dist p.1 o-dist p.2 o)]

lemma exists_optimal_coupling_of_moments (μ ν : ProbabilityMeasure X) (o : X)
    (hμ : Integrable (fun x => dist x o^2) (μ:Measure X))
    (hν : Integrable (fun x => dist x o^2) (ν:Measure X)) :
    ∃ q : Measure (X×X), IsProbabilityMeasure q ∧ IsOptimalCoupling q μ ν ∧ QuadraticTransportCost q ≠ ∞ :=
  exists_optimal_coupling_of_finite μ ν (product_coupling_finite_cost μ ν o hμ hν).1
    (product_coupling_finite_cost μ ν o hμ hν).2

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] in
lemma IsCoupling.swap {q : Measure (X×X)} {μ ν : Measure X} (hq : IsCoupling q μ ν) :
    IsCoupling (q.map Prod.swap) ν μ := by
  constructor
  · rw [Measure.map_map measurable_fst measurable_swap]; exact hq.2
  · rw [Measure.map_map measurable_snd measurable_swap]; exact hq.1

omit [ProperSpace X] in
lemma quadraticTransportCost_swap (q : Measure (X×X)) :
    QuadraticTransportCost (q.map Prod.swap) = QuadraticTransportCost q := by
  rw [QuadraticTransportCost,lintegral_map (measurable_fst.edist measurable_snd |>.pow_const 2) measurable_swap]
  simp only [Prod.swap,edist_comm,QuadraticTransportCost]

omit [ProperSpace X] in
lemma quadraticWassersteinSq_comm (μ ν : Measure X) : quadraticWassersteinSq μ ν = quadraticWassersteinSq ν μ := by
  unfold quadraticWassersteinSq
  congr 1
  apply le_antisymm
  · apply le_iInf; intro q; apply le_iInf; intro hq
    exact (iInf_le_of_le (q.map Prod.swap) (iInf_le _ hq.swap)).trans_eq (quadraticTransportCost_swap q)
  · apply le_iInf; intro q; apply le_iInf; intro hq
    exact (iInf_le_of_le (q.map Prod.swap) (iInf_le _ hq.swap)).trans_eq (quadraticTransportCost_swap q)

omit [BorelSpace X] [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma quadraticWassersteinSq_le_cost {μ ν : Measure X} {q : Measure (X×X)}
    (hq : IsCoupling q μ ν) (hqt : QuadraticTransportCost q ≠ ∞) :
    quadraticWassersteinSq μ ν ≤ (QuadraticTransportCost q).toReal :=
  ENNReal.toReal_mono hqt (iInf_le_of_le q (iInf_le _ hq))

lemma sqrt_integral_sq_eq_norm_toLp {A : Type*} [MeasurableSpace A] {q : Measure A} {f : A → ℝ}
    (hf : MemLp f 2 q) : Real.sqrt (∫ x,f x^2 ∂q) = ‖hf.toLp f‖ := by
  rw [← norm_toLp_sq_eq_integral hf,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]

lemma integral_sq_triangle {A : Type*} [MeasurableSpace A] {q : Measure A} {f g k : A → ℝ}
    (hf : MemLp f 2 q) (hg : MemLp g 2 q) (hkm : AEStronglyMeasurable k q)
    (hk : ∀ᵐ x ∂q,|k x| ≤ |f x+g x|) :
    MemLp k 2 q ∧ Real.sqrt (∫ x,k x^2 ∂q) ≤ Real.sqrt (∫ x,f x^2 ∂q)+Real.sqrt (∫ x,g x^2 ∂q) := by
  have hK : MemLp k 2 q := (hf.add hg).mono hkm hk
  refine ⟨hK,?_⟩
  rw [sqrt_integral_sq_eq_norm_toLp hK,sqrt_integral_sq_eq_norm_toLp hf,sqrt_integral_sq_eq_norm_toLp hg]
  apply (show ‖hK.toLp k‖ ≤ ‖hf.toLp f+hg.toLp g‖ from ?_).trans (norm_add_le _ _)
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [hK.coeFn_toLp,hf.coeFn_toLp,hg.coeFn_toLp,Lp.coeFn_add (hf.toLp f) (hg.toLp g),hk] with x hx hy hz ha hk
  simpa only [hx,ha,Pi.add_apply,hy,hz,Real.norm_eq_abs] using hk

omit [ProperSpace X] in
lemma exists_coupling_triangle (μ ν ξ : ProbabilityMeasure X)
    {q r : Measure (X×X)} [IsProbabilityMeasure q] [IsProbabilityMeasure r]
    (hq : IsCoupling q μ ν) (hr : IsCoupling r ν ξ)
    (hqt : QuadraticTransportCost q ≠ ∞) (hrt : QuadraticTransportCost r ≠ ∞) :
    ∃ s : Measure (X×X), IsCoupling s μ ξ ∧ QuadraticTransportCost s ≠ ∞ ∧
      Real.sqrt (QuadraticTransportCost s).toReal ≤
        Real.sqrt (QuadraticTransportCost q).toReal+Real.sqrt (QuadraticTransportCost r).toReal := by
  let : Nonempty X := (μ:Measure X).nonempty_of_neZero
  obtain ⟨p,hp,hp0,hp1,hjoin⟩ := exists_fiber_gluing_supported q r Prod.snd Prod.fst
    measurable_snd measurable_fst (hq.2.trans hr.1.symm)
  let := hp
  let F : (X×X)×(X×X) → X×X := fun p => (p.1.1,p.2.2)
  have hFm : Measurable F := (measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)
  have hsq : IsCoupling (p.map F) μ ξ := by
    constructor
    · rw [Measure.map_map measurable_fst hFm]
      change p.map (Prod.fst ∘ Prod.fst) = _
      rw [← Measure.map_map measurable_fst measurable_fst,hp0,hq.1]
    · rw [Measure.map_map measurable_snd hFm]
      change p.map (Prod.snd ∘ Prod.snd) = _
      rw [← Measure.map_map measurable_snd measurable_snd,hp1,hr.2]
  have hq2 : MemLp (fun z : X×X => dist z.1 z.2) 2 q :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr (integrable_squared_distance_of_cost hqt)
  have hr2 : MemLp (fun z : X×X => dist z.1 z.2) 2 r :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr (integrable_squared_distance_of_cost hrt)
  have hqP := hq2.comp_measurePreserving (show MeasurePreserving Prod.fst p q from ⟨measurable_fst,hp0⟩)
  have hrP := hr2.comp_measurePreserving (show MeasurePreserving Prod.snd p r from ⟨measurable_snd,hp1⟩)
  have hK := integral_sq_triangle hqP hrP (show AEStronglyMeasurable (fun z => dist z.1.1 z.2.2) p from by fun_prop) (by
    filter_upwards [hjoin] with z hz
    simp only [Function.comp_def,abs_of_nonneg dist_nonneg,abs_of_nonneg (add_nonneg dist_nonneg dist_nonneg)]
    rw [← hz]
    exact dist_triangle z.1.1 z.1.2 z.2.2)
  have hki : Integrable (fun z => dist z.1.1 z.2.2^2) p := (memLp_two_iff_integrable_sq (by fun_prop)).mp hK.1
  have hsi : Integrable (fun z : X×X => dist z.1 z.2^2) (p.map F) :=
    (integrable_map_measure ((measurable_fst.dist measurable_snd).pow_const 2).aestronglyMeasurable hFm.aemeasurable).mpr hki
  have hst := cost_ne_top_iff_integrable_sq.mpr hsi
  refine ⟨p.map F,hsq,hst,?_⟩
  rw [quadraticTransportCost_eq_integral hst,quadraticTransportCost_eq_integral hqt,quadraticTransportCost_eq_integral hrt]
  simp only [ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
  rw [integral_map hFm.aemeasurable ((measurable_fst.dist measurable_snd).pow_const 2).aestronglyMeasurable]
  have hqeq : (∫ z, (dist z.1 z.2)^2 ∂q) = ∫ z : (X×X)×(X×X),dist z.1.1 z.1.2^2 ∂p := by
    rw [← hp0,integral_map measurable_fst.aemeasurable (by fun_prop)]
  have hreq : (∫ z, (dist z.1 z.2)^2 ∂r) = ∫ z : (X×X)×(X×X),dist z.2.1 z.2.2^2 ∂p := by
    rw [← hp1,integral_map measurable_snd.aemeasurable (by fun_prop)]
  rw [hqeq,hreq]
  exact hK.2

lemma quadraticWassersteinSq_triangle (μ ν ξ : ProbabilityMeasure X) (o : X)
    (hμ : Integrable (fun x => dist x o^2) (μ:Measure X))
    (hν : Integrable (fun x => dist x o^2) (ν:Measure X))
    (hξ : Integrable (fun x => dist x o^2) (ξ:Measure X)) :
    Real.sqrt (quadraticWassersteinSq (μ:Measure X) (ξ:Measure X)) ≤
      Real.sqrt (quadraticWassersteinSq (μ:Measure X) (ν:Measure X))+
        Real.sqrt (quadraticWassersteinSq (ν:Measure X) (ξ:Measure X)) := by
  obtain ⟨q,hqp,hq,hqt⟩ := exists_optimal_coupling_of_moments μ ν o hμ hν
  obtain ⟨r,hrp,hr,hrt⟩ := exists_optimal_coupling_of_moments ν ξ o hν hξ
  let := hqp; let := hrp
  obtain ⟨s,hs,hst,H⟩ := exists_coupling_triangle μ ν ξ hq.1 hr.1 hqt hrt
  rw [hq.quadraticWassersteinSq_eq,hr.quadraticWassersteinSq_eq]
  exact (Real.sqrt_le_sqrt (quadraticWassersteinSq_le_cost hs hst)).trans H
end WeakHessian

end
end InlinedFile58

end OAI
