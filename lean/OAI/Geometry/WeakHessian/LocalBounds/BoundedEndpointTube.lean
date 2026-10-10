import Mathlib
import OAI.Geometry.WeakHessian.Curvature.Nonbranching
import OAI.Geometry.WeakHessian.Calculus.RnDerivSmul

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

def boundedEndpointTube (o : X) (R : ℝ) : Set (Curve X) :=
  {γ | IsGeodesic γ ∧ dist (γ timeZero) o ≤ R ∧ dist (γ timeOne) o ≤ R}

omit [MeasurableSpace X] [BorelSpace X] in
lemma isClosed_boundedEndpointTube (o : X) (R : ℝ) : IsClosed (boundedEndpointTube o R) :=
  isClosed_isGeodesic.inter
    ((isClosed_le ((continuous_eval_const timeZero).dist continuous_const) continuous_const).inter
      (isClosed_le ((continuous_eval_const timeOne).dist continuous_const) continuous_const))

omit [MeasurableSpace X] [BorelSpace X] in
lemma boundedEndpointTube_length_le {o : X} {R : ℝ} {γ : Curve X}
    (hγ : γ ∈ boundedEndpointTube o R) : dist (γ timeZero) (γ timeOne) ≤ 2*R := by
  have H := dist_triangle (γ timeZero) o (γ timeOne)
  rw [dist_comm o (γ timeOne)] at H
  linarith [hγ.2.1,hγ.2.2]

omit [MeasurableSpace X] [BorelSpace X] in
lemma boundedEndpointTube_range {o : X} {R : ℝ} {γ : Curve X}
    (hγ : γ ∈ boundedEndpointTube o R) (t : Time) : γ t ∈ Metric.closedBall o (3*R) := by
  have H := hγ.1 t timeZero
  have htime : |(t:ℝ)-(timeZero:ℝ)| ≤ 1 := by
    change |(t:ℝ)-0| ≤ 1
    simpa only [sub_zero,abs_of_nonneg t.property.1] using t.property.2
  have hend := boundedEndpointTube_length_le hγ
  have hdist : dist (γ t) (γ timeZero) ≤ 2*R := by
    rw [H]
    exact (mul_le_of_le_one_left dist_nonneg htime).trans hend
  rw [Metric.mem_closedBall]
  exact (dist_triangle _ _ _).trans (by linarith [hγ.2.1])

omit [MeasurableSpace X] [BorelSpace X] in
lemma isCompact_boundedEndpointTube [ProperSpace X] (o : X) (R : ℝ≥0) :
    IsCompact (boundedEndpointTube o R) := by
  apply isCompact_curve_family _ (isClosed_boundedEndpointTube o R)
    (Metric.closedBall o (3*(R:ℝ))) (isCompact_closedBall _ _) (2*R)
  · exact fun γ hγ t => boundedEndpointTube_range hγ t
  · intro γ hγ
    apply LipschitzWith.of_dist_le_mul
    intro s t
    rw [hγ.1 s t]
    rw [Subtype.dist_eq,Real.dist_eq,mul_comm]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast boundedEndpointTube_length_le hγ) (abs_nonneg _)

lemma isCompact_probability_supported {Y : Type*} [MetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] {T : Set Y} (hT : IsCompact T) :
    IsCompact {π : ProbabilityMeasure Y | (π:Measure Y) Tᶜ = 0} := by
  have H := isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le
    (u := fun _ : ℕ => (0:ℝ≥0)) (K := fun _ => T) tendsto_const_nhds (fun _ => hT)
    (Or.inl inferInstance)
  convert H using 1
  ext π
  simp only [mem_ofPred_eq,nonpos_iff_eq_zero,forall_const]
  change (π:Measure Y) Tᶜ = 0 ↔ ((π:Measure Y) Tᶜ).toNNReal = 0
  simp only [ENNReal.toNNReal_eq_zero_iff,measure_ne_top,or_false]

lemma isCompact_midpoint_constraints {T : Set (Curve X)} (hT : IsCompact T)
    (μ₀ μ₁ : ProbabilityMeasure X) (f : Curve X →ᵇ ℝ) (c : ℝ) (t : Time) :
    IsCompact {μ : ProbabilityMeasure X | ∃ π : ProbabilityMeasure (Curve X),
      (π:Measure (Curve X)) Tᶜ = 0 ∧
      π.map (fun γ => γ timeZero) = μ₀ ∧
      π.map (fun γ => γ timeOne) = μ₁ ∧
      (∫ γ, f γ ∂(π:Measure (Curve X))) ≤ c ∧
      μ = π.map (fun γ => γ t)} := by
  let S : Set (ProbabilityMeasure (Curve X)) := {π |
      (π:Measure (Curve X)) Tᶜ = 0 ∧
      π.map (fun γ => γ timeZero) = μ₀ ∧
      π.map (fun γ => γ timeOne) = μ₁ ∧
      (∫ γ, f γ ∂(π:Measure (Curve X))) ≤ c}
  have hc : IsCompact S := by
    apply (isCompact_probability_supported hT).inter_right
    exact (isClosed_eq (ProbabilityMeasure.continuous_map (continuous_eval_const timeZero)) continuous_const).inter
      ((isClosed_eq (ProbabilityMeasure.continuous_map (continuous_eval_const timeOne)) continuous_const).inter
        (isClosed_le (ProbabilityMeasure.continuous_integral_boundedContinuousFunction f) continuous_const))
  convert hc.image (ProbabilityMeasure.continuous_map (continuous_eval_const t)) using 1
  ext μ
  simp only [mem_ofPred_eq,mem_image,S]
  constructor
  · rintro ⟨π,hπ,h0,h1,hcost,rfl⟩
    exact ⟨π,⟨hπ,h0,h1,hcost⟩,rfl⟩
  · rintro ⟨π,⟨hπ,h0,h1,hcost⟩,rfl⟩
    exact ⟨π,hπ,h0,h1,hcost,rfl⟩

def clippedEndpointCost (R : ℝ≥0) : Curve X →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun γ => min ((dist (γ timeZero) (γ timeOne))^2) ((2*(R:ℝ))^2),
      (((continuous_eval_const timeZero).dist (continuous_eval_const timeOne)).pow 2).min continuous_const⟩
    ((2*(R:ℝ))^2) (by
      intro γ η
      change |min ((dist (γ timeZero) (γ timeOne))^2) ((2*(R:ℝ))^2) -
        min ((dist (η timeZero) (η timeOne))^2) ((2*(R:ℝ))^2)| ≤ _
      have hγ : 0 ≤ min ((dist (γ timeZero) (γ timeOne))^2) ((2*(R:ℝ))^2) := le_min (sq_nonneg _) (sq_nonneg _)
      have hη : 0 ≤ min ((dist (η timeZero) (η timeOne))^2) ((2*(R:ℝ))^2) := le_min (sq_nonneg _) (sq_nonneg _)
      exact abs_le.mpr ⟨by linarith [min_le_right ((dist (η timeZero) (η timeOne))^2) ((2*(R:ℝ))^2)],
        by linarith [min_le_right ((dist (γ timeZero) (γ timeOne))^2) ((2*(R:ℝ))^2)]⟩)

omit [MeasurableSpace X] [BorelSpace X] in
lemma clippedEndpointCost_nonneg (R : ℝ≥0) (γ : Curve X) : 0 ≤ clippedEndpointCost R γ :=
  le_min (sq_nonneg _) (sq_nonneg _)

omit [MeasurableSpace X] [BorelSpace X] in
lemma clippedEndpointCost_eq {o : X} {R : ℝ≥0} {γ : Curve X}
    (hγ : γ ∈ boundedEndpointTube o R) :
    clippedEndpointCost R γ = (dist (γ timeZero) (γ timeOne))^2 := by
  change min _ _ = _
  apply min_eq_left
  exact pow_le_pow_left₀ dist_nonneg (boundedEndpointTube_length_le hγ) 2

variable [SecondCountableTopology X]

lemma endpointCost_eq_clipped_integral (π : Measure (Curve X)) [IsFiniteMeasure π]
    {o : X} {R : ℝ≥0} (hs : π (boundedEndpointTube o R)ᶜ = 0) :
    QuadraticTransportCost (endpointCoupling π) =
      ENNReal.ofReal (∫ γ, clippedEndpointCost R γ ∂π) := by
  have hmem : ∀ᵐ γ ∂π, γ ∈ boundedEndpointTube o R := by
    exact ae_iff.mpr hs
  have hm : Measurable (fun γ : Curve X => (γ timeZero,γ timeOne)) :=
    (continuous_eval_const timeZero).measurable.prodMk (continuous_eval_const timeOne).measurable
  rw [QuadraticTransportCost,endpointCoupling,lintegral_map (measurable_fst.edist measurable_snd |>.pow_const 2) hm]
  rw [ofReal_integral_eq_lintegral_ofReal ((clippedEndpointCost R).integrable π)
    (ae_of_all _ (clippedEndpointCost_nonneg R))]
  apply lintegral_congr_ae
  filter_upwards [hmem] with γ hγ
  rw [clippedEndpointCost_eq hγ,edist_dist,ENNReal.ofReal_pow dist_nonneg]

def optimalTimeLaws (μ₀ μ₁ : ProbabilityMeasure X) (t : Time) : Set (ProbabilityMeasure X) :=
  {μ | ∃ π : ProbabilityMeasure (Curve X),
    (∀ᵐ γ ∂(π:Measure (Curve X)), IsGeodesic γ) ∧
    IsOptimalCoupling (endpointCoupling (π:Measure (Curve X))) μ₀ μ₁ ∧
    μ = π.map (fun γ => γ t)}

omit [SecondCountableTopology X] in
lemma optimalPlan_supported_tube (π : ProbabilityMeasure (Curve X))
    {μ₀ μ₁ : ProbabilityMeasure X} {o : X} {R : ℝ≥0}
    (hgeo : ∀ᵐ γ ∂(π:Measure (Curve X)), IsGeodesic γ)
    (hends : IsCoupling (endpointCoupling (π:Measure (Curve X))) μ₀ μ₁)
    (h₀ : (μ₀:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (h₁ : (μ₁:Measure X) (Metric.closedBall o R)ᶜ = 0) :
    (π:Measure (Curve X)) (boundedEndpointTube o R)ᶜ = 0 := by
  have he₀ : ∀ᵐ γ ∂(π:Measure (Curve X)), dist (γ timeZero) o ≤ R := by
    apply ae_of_ae_map (f := fun γ : Curve X => γ timeZero)
      (p := fun x => dist x o ≤ R) (continuous_eval_const timeZero).measurable.aemeasurable
    change ∀ᵐ x ∂interpolation (π:Measure (Curve X)) timeZero, dist x o ≤ R
    rw [hends.interpolation_endpoints.1]
    exact ae_iff.mpr h₀
  have he₁ : ∀ᵐ γ ∂(π:Measure (Curve X)), dist (γ timeOne) o ≤ R := by
    apply ae_of_ae_map (f := fun γ : Curve X => γ timeOne)
      (p := fun x => dist x o ≤ R) (continuous_eval_const timeOne).measurable.aemeasurable
    change ∀ᵐ x ∂interpolation (π:Measure (Curve X)) timeOne, dist x o ≤ R
    rw [hends.interpolation_endpoints.2]
    exact ae_iff.mpr h₁
  apply ae_iff.mp
  filter_upwards [hgeo,he₀,he₁] with γ hg h0 h1
  exact ⟨hg,h0,h1⟩

theorem isCompact_optimalTimeLaws [ProperSpace X]
    {μ₀ μ₁ : ProbabilityMeasure X} (o : X) (R : ℝ≥0)
    (h₀ : (μ₀:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (h₁ : (μ₁:Measure X) (Metric.closedBall o R)ᶜ = 0) (t : Time) :
    IsCompact (optimalTimeLaws μ₀ μ₁ t) := by
  by_cases hne : (optimalTimeLaws μ₀ μ₁ t).Nonempty
  · obtain ⟨μ,π₀,hgeo₀,hopt₀,hμ⟩ := hne
    let c := ∫ γ, clippedEndpointCost R γ ∂(π₀:Measure (Curve X))
    have hc : 0 ≤ c := integral_nonneg (clippedEndpointCost_nonneg R)
    have hπs := optimalPlan_supported_tube π₀ hgeo₀ hopt₀.1 h₀ h₁
    have hcost₀ := endpointCost_eq_clipped_integral (π₀:Measure (Curve X)) hπs
    have hset : optimalTimeLaws μ₀ μ₁ t =
        {μ : ProbabilityMeasure X | ∃ π : ProbabilityMeasure (Curve X),
          (π:Measure (Curve X)) (boundedEndpointTube o R)ᶜ = 0 ∧
          π.map (fun γ => γ timeZero) = μ₀ ∧
          π.map (fun γ => γ timeOne) = μ₁ ∧
          (∫ γ, clippedEndpointCost R γ ∂(π:Measure (Curve X))) ≤ c ∧
          μ = π.map (fun γ => γ t)} := by
      ext η
      constructor
      · rintro ⟨π,hg,ho,rfl⟩
        have hs := optimalPlan_supported_tube π hg ho.1 h₀ h₁
        refine ⟨π,hs,?_,?_,?_,rfl⟩
        · apply Subtype.ext
          exact ho.1.interpolation_endpoints.1
        · apply Subtype.ext
          exact ho.1.interpolation_endpoints.2
        · apply (ENNReal.ofReal_le_ofReal_iff hc).mp
          rw [← endpointCost_eq_clipped_integral (π:Measure (Curve X)) hs,← hcost₀]
          exact ho.2 _ hopt₀.1
      · rintro ⟨π,hs,h0,h1,hcost,rfl⟩
        have hend : IsCoupling (endpointCoupling (π:Measure (Curve X))) μ₀ μ₁ := by
          have H := endpointCoupling_couples (π:Measure (Curve X))
          have he0 : interpolation (π:Measure (Curve X)) timeZero = (μ₀:Measure X) := congrArg Subtype.val h0
          have he1 : interpolation (π:Measure (Curve X)) timeOne = (μ₁:Measure X) := congrArg Subtype.val h1
          rwa [he0,he1] at H
        refine ⟨π,?_,⟨hend,?_⟩,rfl⟩
        · exact (ae_iff.mpr hs).mono fun γ hγ => hγ.1
        · intro q hq
          apply le_trans ?_ (hopt₀.2 q hq)
          rw [endpointCost_eq_clipped_integral (π:Measure (Curve X)) hs,hcost₀]
          exact ENNReal.ofReal_le_ofReal hcost
    rw [hset]
    exact isCompact_midpoint_constraints (isCompact_boundedEndpointTube o R) μ₀ μ₁
      (clippedEndpointCost R) c t
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact isCompact_empty

end WeakHessian

end
end InlinedFile0

end OAI
