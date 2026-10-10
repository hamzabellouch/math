import Mathlib
import OAI.Analysis.HardSphere.Operators.KilledTransitionAdd
import OAI.Analysis.HardSphere.Geometry.KilledAverage
import OAI.Analysis.HardSphere.Operators.KilledTransitionContinuousAe

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere
open Wiener ContinuousLinearMap
open scoped ComplexConjugate

lemma killedAverage_zero_of_not_allowed (N : ℕ) (L : Length) (a t : ℝ)
    (g : Configuration N L→ℂ) {X : Configuration N L} (hX : X∉allowed N L a) :
    killedAverage N L a t g X=0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [coordinateWiener_start_zero N] with w hw
  have hn : freeTrajectory N L t w X∉staysAllowed N L a := by
    intro h
    have h0 := h (Set.mem_range_self (0:Time))
    rw [freeTrajectory_start N L t hw X] at h0
    exact hX h0
  exact Set.indicator_of_notMem hn _

def allowedProjection (N : ℕ) (L : Length) (a : ℝ) : ScalarL2 N L→L[ℂ] ScalarL2 N L :=
  L2Multiplier.clm ((allowed N L a).indicator (fun _ ↦ (1:ℂ)))
    ((memLp_top_const (1:ℂ)).indicator (isOpen_allowed N L a).measurableSet)

lemma allowedProjection_ae (N : ℕ) (L : Length) (a : ℝ) (f : ScalarL2 N L) :
    allowedProjection N L a f =ᵐ[volume] (allowed N L a).indicator f := by
  filter_upwards [L2Multiplier.coe_clm ((allowed N L a).indicator (fun _ ↦ (1:ℂ)))
    ((memLp_top_const (1:ℂ)).indicator (isOpen_allowed N L a).measurableSet) f] with X hX
  change (L2Multiplier.clm _ _ f) X=_
  rw [hX]
  by_cases h : X∈allowed N L a <;> simp [h]

lemma killedTransition_zero (N : ℕ) (L : Length) (a : ℝ) :
    killedTransition N L a 0=allowedProjection N L a := by
  apply ContinuousLinearMap.ext_on (s := Set.range (ContinuousMap.toLp 2 volume ℂ))
  · exact (ContinuousMap.toLp_denseRange ℂ volume ℂ (by norm_num : (2:ℝ≥0∞)≠∞)).mono
      (Submodule.subset_span)
  · rintro _ ⟨g,rfl⟩
    apply Lp.ext
    filter_upwards [killedTransition_continuous_ae N L a 0 g,
      allowedProjection_ae N L a (ContinuousMap.toLp 2 volume ℂ g),
      ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) volume g] with X h1 h2 h3
    rw [h1,killedAverage_zero,h2]
    by_cases h : X∈allowed N L a
    · simpa only [Set.indicator_of_mem h] using h3.symm
    · simp only [Set.indicator_of_notMem h]

lemma allowedProjection_killedTransition (N : ℕ) (L : Length) (a t : ℝ) :
    (allowedProjection N L a).comp (killedTransition N L a t)=killedTransition N L a t := by
  apply ContinuousLinearMap.ext_on (s := Set.range (ContinuousMap.toLp 2 volume ℂ))
  · exact (ContinuousMap.toLp_denseRange ℂ volume ℂ (by norm_num : (2:ℝ≥0∞)≠∞)).mono
      (Submodule.subset_span)
  · rintro _ ⟨g,rfl⟩
    apply Lp.ext
    filter_upwards [killedTransition_continuous_ae N L a t g,
      allowedProjection_ae N L a (killedTransition N L a t (ContinuousMap.toLp 2 volume ℂ g))]
      with X h1 h2
    change (allowedProjection N L a (killedTransition N L a t (ContinuousMap.toLp 2 volume ℂ g))) X=_
    rw [h2]
    by_cases h : X∈allowed N L a
    · exact Set.indicator_of_mem h _
    · rw [Set.indicator_of_notMem h,h1,killedAverage_zero_of_not_allowed N L a t g h]

lemma killedTransition_allowedProjection (N : ℕ) (L : Length) (a t : ℝ) :
    (killedTransition N L a t).comp (allowedProjection N L a)=killedTransition N L a t := by
  have he := congrArg ContinuousLinearMap.adjoint (allowedProjection_killedTransition N L a t)
  rw [adjoint_comp,← killedTransition_zero N L a,
    (killedTransition_selfAdjoint N L a 0).adjoint_eq,
    (killedTransition_selfAdjoint N L a t).adjoint_eq] at he
  simpa only [killedTransition_zero] using he

lemma killedTransition_support (N : ℕ) (L : Length) (a t : ℝ) (f : ScalarL2 N L) :
    ∀ᵐ X ∂(volume : Measure (Configuration N L)), X∉allowed N L a → killedTransition N L a t f X=0 := by
  have he := congrArg (fun A : ScalarL2 N L→L[ℂ] ScalarL2 N L ↦ A f)
    (allowedProjection_killedTransition N L a t)
  change allowedProjection N L a (killedTransition N L a t f)=killedTransition N L a t f at he
  filter_upwards [allowedProjection_ae N L a (killedTransition N L a t f)] with X hX
  rw [he] at hX
  intro hn
  rw [hX,Set.indicator_of_notMem hn]

lemma killedTransition_add_nonneg (N : ℕ) (L : Length) (a s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    killedTransition N L a (s+t)=(killedTransition N L a s).comp (killedTransition N L a t) := by
  rcases hs.eq_or_lt with hs | hs
  · rw [← hs,zero_add,killedTransition_zero,allowedProjection_killedTransition]
  rcases ht.eq_or_lt with ht | ht
  · rw [← ht,add_zero,killedTransition_zero,killedTransition_allowedProjection]
  exact killedTransition_add N L a s t hs ht

end HardSphere

namespace HardSphere

lemma exists_bounded_lift_of_tendsto {E F ι : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ E] [InnerProductSpace ℂ F]
    [CompleteSpace E] [CompleteSpace F]
    {l : Filter ι} [l.NeBot] (A : E →L[ℂ] F) (f : ι → E)
    {C : ℝ} (hb : ∀ i, ‖f i‖≤C) {u : F}
    (hu : Tendsto (fun i ↦ A (f i)) l (𝓝 u)) :
    ∃ x : E, ‖x‖≤C ∧ A x=u := by
  let φ : ι → WeakDual ℂ E := fun i ↦ (InnerProductSpace.toDual ℂ E (f i)).toWeakDual
  have hφ : ∀ i, φ i∈WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 C := by
    intro i
    simpa only [Set.mem_preimage,Metric.mem_closedBall,dist_zero_right,φ,
      StrongDual.toStrongDual_toWeakDual,(InnerProductSpace.toDual ℂ E).norm_map] using hb i
  obtain ⟨ψ,hψ,hcluster⟩ := (WeakDual.isCompact_closedBall (0 : StrongDual ℂ E) C).exists_mapClusterPt
    (show Filter.map φ l≤𝓟 (WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 C) from
      Filter.le_principal_iff.mpr (Filter.eventually_map.mpr (Eventually.of_forall hφ)))
  let x : E := (InnerProductSpace.toDual ℂ E).symm ψ.toStrongDual
  refine ⟨x,?_,?_⟩
  · change ‖(InnerProductSpace.toDual ℂ E).symm ψ.toStrongDual‖≤C
    simpa only [Set.mem_preimage,Metric.mem_closedBall,dist_zero_right,
      (InnerProductSpace.toDual ℂ E).symm.norm_map] using hψ
  · apply ext_inner_right ℂ
    intro v
    have hv : Tendsto (fun d : WeakDual ℂ E ↦ d (A.adjoint v))
        (Filter.map φ l) (𝓝 (inner ℂ u v)) := by
      rw [tendsto_map'_iff]
      have h := hu.inner (𝕜 := ℂ) (tendsto_const_nhds (x := v))
      simpa only [Function.comp_def,φ,StrongDual.toWeakDual_apply,
        InnerProductSpace.toDual_apply_apply,ContinuousLinearMap.adjoint_inner_right] using h
    have hct := hcluster.map (WeakDual.eval_continuous (A.adjoint v)).continuousAt hv
    have he : ψ (A.adjoint v)=inner ℂ u v := by
      exact eq_of_nhds_neBot hct
    simpa only [x,← WeakDual.toStrongDual_apply,← InnerProductSpace.toDual_symm_apply,
      ContinuousLinearMap.adjoint_inner_right] using he

end HardSphere

end

end OAI
