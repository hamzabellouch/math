import OAI.Analysis.CircleDomains.Topology.RegularJordanParametrization
import OAI.Analysis.CircleDomains.Topology.FiniteCircleStokes

namespace OAI

/-! The orientation-independent form of the same published Green input.

M. Spivak, Calculus on Manifolds (1965), Theorem 5-5, p.124. A regular
once-traversed Jordan boundary has one of the two orientations; the sign
below changes its integral to the positive boundary orientation. Inner
circles retain their positive disk orientation. This is the signed
parametrized specialization of the same manifold Stokes theorem cited in
`FiniteCircleGreen.lean`, not an energy or uniformization assumption.
The sign is chosen before the holes and the differential form.
-/

open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 def UnorientedFiniteCircleGreenFormula : Prop :=
  ∀ (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ), RegularJordanParametrization H γ →
    ∃ e : ℝ, |e| = 1 ∧
    ∀ (n : ℕ) (c : Fin n → ℂ) (r : Fin n → ℝ),
      (∀ i, 0 < r i) →
      Pairwise (Disjoint on fun i => Metric.closedBall (c i) (r i)) →
      (∀ i, Metric.closedBall (c i) (r i) ⊆ jordanInterior H) →
    ∀ O : Set ℂ, IsOpen O →
      (closure (jordanInterior H) \ ⋃ i, Metric.ball (c i) (r i)) ⊆ O →
    ∀ P Q : ℂ → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) P O → ContDiffOn ℝ (⊤ : ℕ∞) Q O →
      e * planarFormIntegral P Q γ -
        ∑ i, planarFormIntegral P Q (unitCircleParam (c i) (r i)) =
        ∫ z in jordanInterior H \ ⋃ i, Metric.closedBall (c i) (r i),
          (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I

 theorem finiteCircleGreen_regular_weighted_closed_form
    (hgreen : UnorientedFiniteCircleGreenFormula)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : RegularJordanParametrization H γ)
    (n : ℕ) (c : Fin n → ℂ) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (hd : Pairwise (Disjoint on fun i => Metric.closedBall (c i) (r i)))
    (hin : ∀ i, Metric.closedBall (c i) (r i) ⊆ jordanInterior H)
    (O : Set ℂ) (hO : IsOpen O)
    (hsub : (closure (jordanInterior H) \ ⋃ i, Metric.ball (c i) (r i)) ⊆ O)
    (φ P Q : ℂ → ℝ) (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ O)
    (hP : ContDiffOn ℝ (⊤ : ℕ∞) P O) (hQ : ContDiffOn ℝ (⊤ : ℕ∞) Q O)
    (hclosed : ∀ z ∈ O, (fderiv ℝ Q z) 1 = (fderiv ℝ P z) Complex.I) :
    ∃ e : ℝ, |e| = 1 ∧
      e * planarFormIntegral (φ * P) (φ * Q) γ -
        ∑ i, planarFormIntegral (φ * P) (φ * Q) (unitCircleParam (c i) (r i)) =
        ∫ z in jordanInterior H \ ⋃ i, Metric.closedBall (c i) (r i),
          (fderiv ℝ φ z) 1 * Q z - (fderiv ℝ φ z) Complex.I * P z := by
  obtain ⟨e, he, hg⟩ := hgreen H γ hγ
  refine ⟨e, he, ?_⟩
  rw [hg n c r hr hd hin O hO hsub (φ * P) (φ * Q) (hφ.mul hP) (hφ.mul hQ)]
  apply setIntegral_congr_fun
  · exact (jordanInterior_isOpen H).measurableSet.diff
      (MeasurableSet.iUnion fun _ => isClosed_closedBall.measurableSet)
  · intro z hz
    have hzO : z ∈ O := hsub ⟨subset_closure hz.1, fun hm => by
      obtain ⟨i, hi⟩ := mem_iUnion.mp hm
      exact hz.2 (mem_iUnion.mpr ⟨i, Metric.ball_subset_closedBall hi⟩)⟩
    have hφd := (hφ.differentiableOn (by simp)).differentiableAt (hO.mem_nhds hzO)
    have hPd := (hP.differentiableOn (by simp)).differentiableAt (hO.mem_nhds hzO)
    have hQd := (hQ.differentiableOn (by simp)).differentiableAt (hO.mem_nhds hzO)
    change (fderiv ℝ (φ * Q) z) 1 - (fderiv ℝ (φ * P) z) Complex.I = _
    rw [fderiv_mul hφd hQd, fderiv_mul hφd hPd]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    rw [hclosed z hzO]
    ring

 theorem finite_circle_stokes_area_bound_regular
    (hgreen : UnorientedFiniteCircleGreenFormula)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : RegularJordanParametrization H γ)
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
    ∃ e : ℝ, |e| = 1 ∧
    |e * circleFormIntegral φ u γ - ∑ i, circleFormIntegral φ u (unitCircleParam (c i) (r i))| ≤
      Real.sqrt Real.pi * R * Real.sqrt
        (∫ z in jordanInterior H \ ⋃ i, closedBall (c i) (r i), ‖circleFDeriv u z‖ ^ 2) := by
  have hc := contDiffOn_circleFDeriv hO hu
  obtain ⟨e, he, hformula⟩ := finiteCircleGreen_regular_weighted_closed_form hgreen H γ hγ n c r hr hd hin O hO hsub
    φ (fun z => circleFDeriv u z 1) (fun z => circleFDeriv u z Complex.I) hφ
    (hc.clm_apply contDiffOn_const) (hc.clm_apply contDiffOn_const)
    (fun z hz => circleFDeriv_closed_complex hO hu hz)
  refine ⟨e, he, ?_⟩
  change |e * planarFormIntegral _ _ γ - ∑ i, planarFormIntegral _ _ (unitCircleParam (c i) (r i))| ≤ _
  rw [hformula]
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
