import OAI.Analysis.CircleDomains.Topology.UnorientedCircleGreen
import OAI.Analysis.CircleDomains.Sobolev.FinitePeriodStokes

namespace OAI

/-! Offset estimates with either orientation of the outer regular circuit. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology BigOperators
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem finite_offset_stokes_bound_with_period_regular
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
      (volume.restrict (jordanInterior H \ ⋃ i, closedBall (c i) (r i))))
    (b : Fin n) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (v : Fin n → ℝ → ℝ) (hv : ∀ i, Continuous (v i))
    (hproj : ∀ i t, (v i t : UnitAddCircle) = u (unitCircleParam (c i) (r i) t))
    (hφb : ∀ t ∈ Icc (0 : ℝ) 1, φ (unitCircleParam (c b) (r b) t) = ρ)
    (hzero : ∀ i ≠ b, v i 1 = v i 0)
    (A : Fin n → ℝ) (hA : ∀ i ≠ b, ∀ t ∈ Icc (0 : ℝ) 1, |v i t - v i 0| ≤ A i) :
    |circleFormIntegral φ u γ| ≤
      Real.sqrt Real.pi * R * Real.sqrt
        (∫ z in jordanInterior H \ ⋃ i, closedBall (c i) (r i), ‖circleFDeriv u z‖ ^ 2) +
      ρ * |v b 1 - v b 0| + ∑ i ∈ Finset.univ.erase b, 2 * Real.pi * r i * A i := by
  have hc (i : Fin n) := circle_boundary_mem_smooth_region H c r
    (fun i => (hr i).le) hd hin hsub i
  obtain ⟨e, he, harea⟩ := finite_circle_stokes_area_bound_regular hgreen H γ hγ
    n c r hr hd hin O hO hsub φ hφ hφlip u hu hR hbounded henergy
  have hresult := abs_le_of_boundary_costs b _ _ _ (ρ * |v b 1 - v b 0|)
    (fun i => 2 * Real.pi * r i * A i) harea
  rw [abs_mul, he, one_mul] at hresult
  apply hresult
  · rw [circleFormIntegral_constant_weight hO hu φ _ (contDiff_unitCircleParam _ _)
      (hc b) (v b) (hv b) (hproj b) ρ hφb, abs_mul, abs_of_nonneg hρ]
  · intro i hi
    exact circleFormIntegral_unitCircle_zero_period hO hu φ hφ hφlip _ (hr i).le
      (hc i) (v i) (hv i) (hproj i) (hzero i hi) (A i) (hA i hi)


end CircleDomainRigidity

end

end OAI
