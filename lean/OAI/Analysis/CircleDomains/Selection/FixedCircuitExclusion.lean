import OAI.Analysis.CircleDomains.Topology.BoundaryPairNeighborhood
import Mathlib.Analysis.InnerProductSpace.Calculus

namespace OAI

/-! A single actual smooth source coordinate supplies a fixed real lift
and an open neighborhood of boundary-map/disk data. Its lower integral
is the same functional used to exclude diagonal Stokes limits. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology NNReal

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem exists_smooth_real_circuit_lift
    {O : Set ℂ} (hO : IsOpen O) {w : ℂ → UnitAddCircle} (hw : SmoothCircleOn w O)
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) (hγO : ∀ t, γ t ∈ O) :
    ∃ v : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) v ∧ ∀ t, (v t : UnitAddCircle) = w (γ t) := by
  let : ContractibleSpace (univ : Set ℝ) := convex_univ.contractibleSpace Set.univ_nonempty
  let : LocallyPathConnectedSpace (univ : Set ℝ) := isOpen_univ.locallyPathConnectedSpace
  have hc : Continuous (w ∘ γ) :=
    continuous_iff_continuousAt.mpr (fun t =>
      (hw.continuousOn.continuousAt (hO.mem_nhds (hγO t))).comp hγ.continuous.continuousAt)
  obtain ⟨v, hv, _, hp⟩ := exists_continuous_circle_lift (w ∘ γ) hc.continuousOn
    (mem_univ 0) ((AddCircle.equivIco (1 : ℝ) 0 (w (γ 0))) : ℝ) (by
      simp only [Function.comp_apply, AddCircle.coe_equivIco])
  have hv' := continuousOn_univ.mp hv
  have hp' : ∀ t, (v t : UnitAddCircle) = w (γ t) := fun t => hp t (mem_univ t)
  exact ⟨v, contDiff_real_lift_along hw hγ hγO hv' hp', hp'⟩

 theorem contDiffOn_distance_from_disk_comp
    {O : Set ℂ} {f : ℂ → ℂ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f O)
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (houtside : ∀ z ∈ O, r < dist (f z) c) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => infDist (f z) (closedBall c r)) O := by
  have hne : ∀ z ∈ O, f z ≠ c := by
    intro z hz h
    have := houtside z hz
    rw [h, dist_self] at this
    linarith
  have hs := (hf.dist ℝ contDiffOn_const hne).sub (contDiffOn_const (c := r))
  apply hs.congr
  intro z hz
  exact infDist_closedBall_of_dist_gt c (f z) hr (houtside z hz)

 theorem circleFormIntegral_eq_boundaryPairFunctional
    {O : Set ℂ} (hO : IsOpen O) {w : ℂ → UnitAddCircle} (hw : SmoothCircleOn w O)
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) (hγO : ∀ t, γ t ∈ O)
    (f : ℂ → ℂ) (hf : ContinuousOn f O) (c : ℂ) (r : ℝ≥0)
    (v : ℝ → ℝ) (hv : Continuous v) (hproj : ∀ t, (v t : UnitAddCircle) = w (γ t)) :
    circleFormIntegral (fun z => infDist (f z) (closedBall c (r : ℝ))) w γ =
      boundaryPairFunctional v
        (boundaryCurveTrace (f ∘ γ) (hf.comp_continuous hγ.continuous hγO), c, r) := by
  rw [boundaryPairFunctional_trace,
    circleFormIntegral_eq_real_lift hO hw _ γ (hγ.differentiable (by simp)) hγO v hv hproj]
  rfl

 theorem exists_open_fixed_circuit_exclusion
    {O : Set ℂ} (hO : IsOpen O) {w : ℂ → UnitAddCircle} (hw : SmoothCircleOn w O)
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) (hγO : ∀ t, γ t ∈ O)
    (f : ℂ → ℂ) (hf : ContinuousOn f O) (c : ℂ) (r : ℝ≥0) (budget : ℝ)
    (hlower : budget < |circleFormIntegral (fun z => infDist (f z) (closedBall c (r : ℝ))) w γ|) :
    ∃ v : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) v ∧
      (∀ t, (v t : UnitAddCircle) = w (γ t)) ∧
      IsOpen (boundaryExclusionSet v budget) ∧
      (boundaryCurveTrace (f ∘ γ) (hf.comp_continuous hγ.continuous hγO), c, r) ∈
        boundaryExclusionSet v budget := by
  obtain ⟨v, hv, hproj⟩ := exists_smooth_real_circuit_lift hO hw hγ hγO
  refine ⟨v, hv, hproj, isOpen_boundaryExclusionSet v hv budget, ?_⟩
  change budget < |boundaryPairFunctional v _|
  rwa [← circleFormIntegral_eq_boundaryPairFunctional hO hw hγ hγO f hf c r v hv.continuous hproj]

end CircleDomainRigidity

end

end OAI
