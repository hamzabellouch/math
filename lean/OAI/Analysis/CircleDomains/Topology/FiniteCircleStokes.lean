import OAI.Analysis.CircleDomains.Topology.FiniteCircleGreen
import OAI.Analysis.CircleDomains.Sobolev.CircleDifferentialClosed
import OAI.Analysis.CircleDomains.Sobolev.ComplexWedgeIntegral
import OAI.Analysis.CircleDomains.Topology.CircleChainRule
import OAI.Analysis.CircleDomains.Sobolev.SmoothRealLift

namespace OAI

/-! The finite-region Stokes identity and area bound for the actual
intrinsic differential of a smooth circle coordinate. The only additional
published input is the precisely stated classical Green formula. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 def circleFormIntegral (φ : ℂ → ℝ) (u : ℂ → UnitAddCircle) (γ : ℝ → ℂ) : ℝ :=
  planarFormIntegral (φ * fun z => circleFDeriv u z 1)
    (φ * fun z => circleFDeriv u z Complex.I) γ

 theorem circleFormIntegral_eq_real_lift
    {O : Set ℂ} (hO : IsOpen O) {u : ℂ → UnitAddCircle} (hu : SmoothCircleOn u O)
    (φ : ℂ → ℝ) (γ : ℝ → ℂ) (hγ : Differentiable ℝ γ) (hγO : ∀ t, γ t ∈ O)
    (v : ℝ → ℝ) (hv : Continuous v) (hproj : ∀ t, (v t : UnitAddCircle) = u (γ t)) :
    circleFormIntegral φ u γ = ∫ t in (0 : ℝ)..1, φ (γ t) * deriv v t := by
  have hd (t : ℝ) : deriv v t = circleFDeriv u (γ t) (deriv γ t) := by
    have he : fderiv ℝ v t = circleFDeriv (u ∘ γ) t := by
      symm
      apply circleFDeriv_eq_lift
        ((hu.continuousOn.continuousAt (hO.mem_nhds (hγO t))).comp (hγ t).continuousAt)
        hv.continuousAt
      exact Eventually.of_forall hproj
    rw [← fderiv_apply_one_eq_deriv, he, circleFDeriv_comp hO hu (hγ t) (hγO t)]
    simp only [ContinuousLinearMap.comp_apply, fderiv_apply_one_eq_deriv]
  unfold circleFormIntegral planarFormIntegral
  apply intervalIntegral.integral_congr
  intro t _
  change (φ (γ t) * circleFDeriv u (γ t) 1) * (deriv γ t).re +
    (φ (γ t) * circleFDeriv u (γ t) Complex.I) * (deriv γ t).im =
    φ (γ t) * deriv v t
  conv_rhs => rw [hd t, complexCovector_apply]
  ring

 theorem finite_circle_stokes_area_bound
    (hgreen : FiniteCircleGreenFormula)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : PositiveJordanParametrization H γ)
    (n : ℕ) (c : Fin n → ℂ) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (hd : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    (hin : ∀ i, closedBall (c i) (r i) ⊆ jordanInterior H)
    (O : Set ℂ) (hO : IsOpen O)
    (hsub : (closure (jordanInterior H) \ ⋃ i, ball (c i) (r i)) ⊆ O)
    (φ : ℂ → ℝ) (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ O) (hφlip : LipschitzWith 1 φ)
    (u : ℂ → UnitAddCircle) (hu : SmoothCircleOn u O)
    {R : ℝ} (hR : 0 ≤ R)
    (hbounded : jordanInterior H \ ⋃ i, closedBall (c i) (r i) ⊆ closedBall 0 R)
    (henergy : MemLp (circleFDeriv u) 2
      (volume.restrict (jordanInterior H \ ⋃ i, closedBall (c i) (r i)))) :
    |circleFormIntegral φ u γ - ∑ i, circleFormIntegral φ u (unitCircleParam (c i) (r i))| ≤
      Real.sqrt Real.pi * R * Real.sqrt
        (∫ z in jordanInterior H \ ⋃ i, closedBall (c i) (r i), ‖circleFDeriv u z‖ ^ 2) := by
  have hc := contDiffOn_circleFDeriv hO hu
  have he := finiteCircleGreen_weighted_closed_form hgreen H γ hγ n c r hr hd hin O hO hsub
    φ (fun z => circleFDeriv u z 1) (fun z => circleFDeriv u z Complex.I) hφ
    (hc.clm_apply contDiffOn_const) (hc.clm_apply contDiffOn_const)
    (fun z hz => circleFDeriv_closed_complex hO hu hz)
  change |planarFormIntegral _ _ γ - ∑ i, planarFormIntegral _ _ (unitCircleParam (c i) (r i))| ≤ _
  rw [he]
  have hΩ : MeasurableSet (jordanInterior H \ ⋃ i, closedBall (c i) (r i)) :=
    (jordanInterior_isOpen H).measurableSet.diff (MeasurableSet.iUnion fun _ => isClosed_closedBall.measurableSet)
  have hΩO : jordanInterior H \ ⋃ i, closedBall (c i) (r i) ⊆ O := by
    intro z hz
    apply hsub
    refine ⟨subset_closure hz.1, ?_⟩
    intro hm
    obtain ⟨i, hi⟩ := mem_iUnion.mp hm
    exact hz.2 (mem_iUnion.mpr ⟨i, ball_subset_closedBall hi⟩)
  exact integral_complexCovector_wedge_le hΩ hR hbounded (fderiv ℝ φ) (circleFDeriv u)
    ((hφ.fderiv_of_isOpen (m := 0) hO (by simp)).continuousOn.mono hΩO)
    (hc.continuousOn.mono hΩO) henergy (fun z _ => by
      simpa only [NNReal.coe_one] using norm_fderiv_le_of_lipschitz ℝ hφlip (x₀ := z))

end CircleDomainRigidity

end

end OAI
