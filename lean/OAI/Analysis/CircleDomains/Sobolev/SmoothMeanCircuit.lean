import OAI.Analysis.CircleDomains.Topology.BoundaryCollarLift
import OAI.Analysis.CircleDomains.Topology.MeanIndexCircle
import OAI.Analysis.CircleDomains.Topology.CircleFormBoundary
import OAI.Analysis.CircleDomains.Topology.ReparametrizedBoundaryLowerBound

namespace OAI

/-! A physical smooth circle coordinate has an actual smooth, period-one
real lift on a circuit whenever it is the perturbed mean on a lifted
punctured-disk circuit. No smoothness of the boundary angle is required. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem exists_smooth_mean_circuit_lift
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (L : ℝ → ClosedUpperHalfPlane) (hL : Continuous L)
    (hmiss : ∀ t, ∀ᵐ α : K ∂(η : Measure K), diskRayProjection (L t).val ∉ range α.val)
    (hperiod : L 1 = (L 0).translate 1)
    (O : Set ℂ) (w : ℂ → UnitAddCircle) (hw : SmoothCircleOn w O)
    (γ : ℝ → ℂ) (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) (hγO : ∀ t, γ t ∈ O)
    (hloop : γ 1 = γ 0) (R : ℂ → ℝ) (hR : Continuous (R ∘ γ))
    (hvalue : ∀ t, w (γ t) = diskMeanCircle hsch K hKS η (diskRayProjection (L t).val) +
      (R (γ t) : UnitAddCircle)) :
    ∃ v : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) v ∧
      (∀ t, v t = meanGeometricIndex hsch K hKS η (L t) + R (γ t)) ∧
      (∀ t, (v t : UnitAddCircle) = w (γ t)) ∧ v 1 = v 0 + 1 := by
  let v : ℝ → ℝ := fun t => meanGeometricIndex hsch K hKS η (L t) + R (γ t)
  have hc : Continuous v := by
    apply Continuous.add _ hR
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (continuousAt_meanGeometricIndex hsch hsep K hK hKS η (L t) (hmiss t)).comp
      hL.continuousAt
  have hp (t : ℝ) : (v t : UnitAddCircle) = w (γ t) := by
    rw [hvalue t, diskMeanCircle_projection hsch hsep K hK hKS η]
    simp only [v, AddCircle.coe_add]
  refine ⟨v, contDiff_real_lift_along hw hγ hγO hc hp, fun _ => rfl, hp, ?_⟩
  change meanGeometricIndex hsch K hKS η (L 1) + R (γ 1) =
    (meanGeometricIndex hsch K hKS η (L 0) + R (γ 0)) + 1
  rw [hperiod, hloop, meanGeometricIndex_translate hsch hsep K hK hKS η]
  simp only [Int.cast_one]
  ring

 theorem mean_circuit_integral_lower_bound
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K)
    [NullSingletonClass (compactArcStartingAngleLaw K η : Measure UnitAddCircle)]
    (q : ℝ ≃o ℝ) (hq0 : q 0 = 0) (hq1 : q 1 = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (L : ℝ → ClosedUpperHalfPlane), Continuous L →
      (∀ t, ∀ᵐ α : K ∂(η : Measure K), diskRayProjection (L t).val ∉ range α.val) →
      L 1 = (L 0).translate 1 →
      ∀ (O : Set ℂ), IsOpen O → ∀ (w : ℂ → UnitAddCircle), SmoothCircleOn w O →
      ∀ (γ : ℝ → ℂ), ContDiff ℝ (⊤ : ℕ∞) γ → (∀ t, γ t ∈ O) → γ 1 = γ 0 →
      ∀ (R : ℂ → ℝ), Continuous (R ∘ γ) →
      (∀ t, w (γ t) = diskMeanCircle hsch K hKS η (diskRayProjection (L t).val) +
        (R (γ t) : UnitAddCircle)) →
      (∀ t ∈ Icc (0 : ℝ) 1, |R (γ t)| ≤ ε) →
      (∀ t ∈ Icc (0 : ℝ) 1, dist (L t).val (q t : ℂ) < δ) →
      ∀ (Φ : ℂ → ℝ), ContDiffOn ℝ (⊤ : ℕ∞) Φ O →
      ∀ c : ℝ, (∀ᵐ a : UnitAddCircle ∂(compactArcStartingAngleLaw K η : Measure UnitAddCircle),
        c ≤ Φ (γ (q.symm (unitCircleCut a)))) →
      c ≤ circleFormIntegral Φ w γ +
        (2 * ε) * ∫ t in (0 : ℝ)..1, |deriv (Φ ∘ γ) t| := by
  obtain ⟨δ, hδ, hbound⟩ := exists_mean_collar_boundary_lower_bound hsch hsep K hK hKS η
    q hq0 hq1 hε
  refine ⟨δ, hδ, ?_⟩
  intro L hL hmiss hperiod O hO w hw γ hγ hγO hloop R hR hvalue hRbound hnear Φ hΦ c hpositive
  obtain ⟨v, hv, hvvalue, hvproj, hvperiod⟩ := exists_smooth_mean_circuit_lift hsch hsep
    K hK hKS η L hL hmiss hperiod O w hw γ hγ hγO hloop R hR hvalue
  have hΦγ : ContDiff ℝ (⊤ : ℕ∞) (Φ ∘ γ) := by
    apply contDiffOn_univ.mp
    intro t _
    exact ((hΦ.contDiffAt (hO.mem_nhds (hγO t))).comp t hγ.contDiffAt).contDiffWithinAt
  have hb := hbound L (Φ ∘ γ) (deriv (Φ ∘ γ)) v (deriv v)
    (fun t => (hΦγ.differentiable (by simp) t).hasDerivAt)
    (hΦγ.continuous_deriv (by simp)) (by simp only [Function.comp_apply, hloop])
    (fun t _ => (hv.differentiable (by simp) t).hasDerivAt)
    ((hv.continuous_deriv (by simp)).intervalIntegrable 0 1) hvperiod hnear
    (fun t ht => by rw [hvvalue t]; simpa only [add_sub_cancel_left] using hRbound t ht)
    c hpositive
  rw [circleFormIntegral_eq_real_lift hO hw Φ γ (hγ.differentiable (by simp)) hγO v
    hv.continuous hvproj]
  exact hb

end CircleDomainRigidity

end

end OAI
