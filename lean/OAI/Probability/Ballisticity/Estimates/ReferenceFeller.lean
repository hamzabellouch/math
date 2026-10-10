import Mathlib
import OAI.Probability.Ballisticity.Estimates.ReferenceContinuity
import OAI.Probability.Ballisticity.Geometry.FiniteCoordinateApproximation

namespace OAI

section

open MeasureTheory ProbabilityTheory TopologicalSpace Filter
open scoped ENNReal Topology BoundedContinuousFunction
namespace DirectionalTransience.ReferenceClasses

variable {H R : Type*} [AddCommGroup H] [Countable H]
  [TopologicalSpace H] [DiscreteTopology H] [MeasurableSpace H] [BorelSpace H]
  [MeasurableSpace (OnePoint H)] [BorelSpace (OnePoint H)]
  [UniformSpace R] [CompactSpace R] [SecondCountableTopology R]
  [MeasurableSpace R] [BorelSpace R]

noncomputable def referenceProb (ν : Measure R) [IsProbabilityMeasure ν]
    (O : Data H) : ProbabilityMeasure (AllFields H R) := ⟨reference ν O,inferInstance⟩

lemma integral_uniform_error {Y : Type*} [TopologicalSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] (f g : Y →ᵇ ℝ)
    {ε : ℝ} (h : ∀ x, |f x-g x|≤ε) :
    |(∫ x, f x ∂μ)-(∫ x, g x ∂μ)|≤ε := by
  rw [← integral_sub (f.integrable μ) (g.integrable μ)]
  calc
    _ ≤ ∫ x, |f x-g x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _ : Y, ε ∂μ := integral_mono ((f.integrable μ).sub (g.integrable μ)).abs
      (integrable_const ε) h
    _ = ε := by simp

lemma reference_integral_continuous (ν : Measure R) [IsProbabilityMeasure ν]
    (f : (AllFields H R) →ᵇ ℝ) :
    Continuous (fun O : Data H => ∫ φ, f φ ∂reference ν O) := by
  have : Nonempty R := nonempty_of_isProbabilityMeasure ν
  let r : AllFields H R := fun _ => Classical.choice ‹Nonempty R›
  apply continuous_iff_continuousAt.mpr
  intro O
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨S,hS⟩ := Entropy.finiteFiller_approx f.toContinuousMap r (div_pos hε (show (0:ℝ)<3 by norm_num))
  let gf : C((S → R),ℝ) := ⟨fun x => f (Entropy.finiteFiller r S x),
    f.continuous.comp (Entropy.finiteFiller_continuous r S)⟩
  let g : (AllFields H R) →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun φ => gf (fun i : S => φ i),gf.continuous.comp (continuous_pi fun i => continuous_apply (i : Site H))⟩
  have heq : ∀ᶠ O' in 𝓝 O, (∫ φ, g φ ∂reference ν O')=(∫ φ, g φ ∂reference ν O) := by
    filter_upwards [reference_projection_locally_constant ν O (fun i : S => (i : Site H))] with O' hO'
    have hm : Measurable (fun φ : AllFields H R => fun i : S => φ i) := by fun_prop
    have hi (D : Data H) := integral_map hm.aemeasurable gf.continuous.measurable.aestronglyMeasurable
      (μ:=reference ν D)
    exact (hi O').symm.trans ((congrArg (fun μ => ∫ x, gf x ∂μ) hO').trans (hi O))
  have herr (D : Data H) : |(∫ φ, f φ ∂reference ν D)-(∫ φ, g φ ∂reference ν D)|≤ε/3 :=
    integral_uniform_error _ f g (fun φ => (hS φ).le)
  filter_upwards [heq] with O' hO'
  rw [Real.dist_eq]
  have h1 := herr O'
  have h2 := herr O
  rw [hO'] at h1
  have hh := abs_sub_le (∫ φ, f φ ∂reference ν O') (∫ φ, g φ ∂reference ν O) (∫ φ, f φ ∂reference ν O)
  rw [abs_sub_comm (∫ φ, g φ ∂reference ν O)] at hh
  linarith

theorem referenceProb_continuous (ν : Measure R) [IsProbabilityMeasure ν] :
    Continuous (referenceProb (H:=H) ν) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuous_integral.mpr
  exact reference_integral_continuous ν

end DirectionalTransience.ReferenceClasses

end

section

open MeasureTheory ProbabilityTheory TopologicalSpace Filter
open scoped ENNReal Topology BoundedContinuousFunction
namespace DirectionalTransience.Entropy

variable {X Y I : Type*} [TopologicalSpace X]
  [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

lemma continuous_joint_integral [MeasurableSpace X] [BorelSpace X]
    (P : X → ProbabilityMeasure Y) (hP : Continuous P)
    (F : C(X × Y,ℝ)) : Continuous (fun x => ∫ y, F (x,y) ∂(P x : Measure Y)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hε2 : 0<ε/2 := half_pos hε
  have h1 : ∀ᶠ x' in 𝓝 x, ‖F.curry x'-F.curry x‖<ε/2 := by
    have hc : ContinuousAt (fun x' => ‖F.curry x'-F.curry x‖) x :=
      (F.curry.continuous.sub continuous_const).norm.continuousAt
    exact hc.eventually_lt continuousAt_const (by simpa using hε2)
  let g : Y →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact (F.curry x)
  have hg := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction g).comp hP
  have h2 : ∀ᶠ x' in 𝓝 x, dist (∫ y, g y ∂(P x' : Measure Y))
      (∫ y, g y ∂(P x : Measure Y)) < ε/2 :=
    (Metric.tendsto_nhds.mp hg.continuousAt) (ε/2) hε2
  filter_upwards [h1,h2] with x' hx' hx''
  have hint : |(∫ y, F (x',y) ∂(P x' : Measure Y))-(∫ y, F (x,y) ∂(P x' : Measure Y))| ≤
      ‖F.curry x'-F.curry x‖ := by
    exact ReferenceClasses.integral_uniform_error _
      (BoundedContinuousFunction.mkOfCompact (F.curry x')) g
      (fun y => by
        change |(F.curry x'-F.curry x) y| ≤ _
        simpa only [Real.norm_eq_abs] using (F.curry x'-F.curry x).norm_coe_le_norm y)
  rw [Real.dist_eq] at hx'' ⊢
  have hh := abs_sub_le (∫ y, F (x',y) ∂(P x' : Measure Y))
    (∫ y, F (x,y) ∂(P x' : Measure Y)) (∫ y, F (x,y) ∂(P x : Measure Y))
  change |(∫ y, F (x,y) ∂(P x' : Measure Y))-(∫ y, F (x,y) ∂(P x : Measure Y))|<ε/2 at hx''
  linarith

variable [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [SecondCountableTopology X] [SecondCountableTopology Y]

noncomputable def compProdProb (μ : ProbabilityMeasure X) (K : Kernel X Y) [IsMarkovKernel K] :
    ProbabilityMeasure (X×Y) := ⟨(μ : Measure X).compProd K,inferInstance⟩

noncomputable def kernelProb (K : Kernel X Y) [IsMarkovKernel K] (x : X) :
    ProbabilityMeasure Y := ⟨K x,inferInstance⟩

lemma compProdProb_tendsto (K : Kernel X Y) [IsMarkovKernel K]
    (hK : Continuous (kernelProb K))
    {l : Filter I} {μs : I → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    (hμ : Tendsto μs l (𝓝 μ)) : Tendsto (fun i => compProdProb (μs i) K) l (𝓝 (compProdProb μ K)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  let g : X →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun x => ∫ y, f (x,y) ∂K x,continuous_joint_integral _ hK f.toContinuousMap⟩
  have heq (ρ : ProbabilityMeasure X) :
      (∫ p, f p ∂(compProdProb ρ K : Measure (X×Y)))=(∫ x, g x ∂(ρ : Measure X)) := by
    exact integral_compProd (f.integrable ((ρ : Measure X).compProd K))
  simp_rw [heq]
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ g

end DirectionalTransience.Entropy

end

end OAI
