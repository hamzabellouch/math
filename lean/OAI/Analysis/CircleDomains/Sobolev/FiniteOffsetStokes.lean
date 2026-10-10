import OAI.Analysis.CircleDomains.Topology.CircleFormBoundary
import OAI.Analysis.CircleDomains.Topology.ParallelDiskTolls

namespace OAI

/-! The finite offset estimate from Green's formula. The nonzero period
is kept at the distinguished hole. All other boundary costs use the
oscillations of their real lifts. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology BigOperators

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem circle_boundary_mem_smooth_region
    {n : ℕ} (H : ℂ ≃ₜ ℂ) (c : Fin n → ℂ) (r : Fin n → ℝ)
    (hr : ∀ i, 0 ≤ r i)
    (hd : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    (hin : ∀ i, closedBall (c i) (r i) ⊆ jordanInterior H)
    {O : Set ℂ} (hsub : (closure (jordanInterior H) \ ⋃ i, ball (c i) (r i)) ⊆ O)
    (i : Fin n) (t : ℝ) : unitCircleParam (c i) (r i) t ∈ O := by
  have hs : unitCircleParam (c i) (r i) t ∈ sphere (c i) (r i) :=
    circleMap_mem_sphere _ (hr i) _
  have hc := sphere_subset_closedBall hs
  apply hsub
  refine ⟨subset_closure (hin i hc), ?_⟩
  rintro hm
  obtain ⟨j, hj⟩ := mem_iUnion.mp hm
  by_cases hij : i = j
  · subst j
    have he := mem_sphere.mp hs
    have hl := mem_ball.mp hj
    linarith
  · exact Set.disjoint_left.mp (hd hij) hc (ball_subset_closedBall hj)

 theorem abs_le_of_distinguished_boundary
    {I : Type*} [Fintype I] [DecidableEq I]
    (b : I) (outer : ℝ) (inner : I → ℝ) (E ρ : ℝ) (cost : I → ℝ)
    (harea : |outer - ∑ i, inner i| ≤ E)
    (hb : inner b = ρ) (hρ : 0 ≤ ρ)
    (hother : ∀ i ≠ b, |inner i| ≤ cost i) :
    |outer| ≤ E + ρ + ∑ i ∈ Finset.univ.erase b, cost i := by
  have hsum : |∑ i, inner i| ≤ ρ + ∑ i ∈ Finset.univ.erase b, cost i := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ b), hb, add_comm]
    calc
      |ρ + ∑ i ∈ Finset.univ.erase b, inner i| ≤
          |ρ| + |∑ i ∈ Finset.univ.erase b, inner i| := abs_add_le _ _
      _ ≤ ρ + ∑ i ∈ Finset.univ.erase b, |inner i| := by
        rw [abs_of_nonneg hρ]
        exact add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _)
      _ ≤ _ := add_le_add le_rfl (Finset.sum_le_sum fun i hi =>
        hother i (Finset.mem_erase.mp hi).1)
  calc
    |outer| = |(outer - ∑ i, inner i) + ∑ i, inner i| := by congr 1; ring
    _ ≤ |outer - ∑ i, inner i| + |∑ i, inner i| := abs_add_le _ _
    _ ≤ E + (ρ + ∑ i ∈ Finset.univ.erase b, cost i) := add_le_add harea hsum
    _ = _ := by ring

 theorem finite_offset_stokes_bound
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
      (volume.restrict (jordanInterior H \ ⋃ i, closedBall (c i) (r i))))
    (b : Fin n) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (v : Fin n → ℝ → ℝ) (hv : ∀ i, Continuous (v i))
    (hproj : ∀ i t, (v i t : UnitAddCircle) = u (unitCircleParam (c i) (r i) t))
    (hb : v b 1 - v b 0 = 1)
    (hφb : ∀ t ∈ Icc (0 : ℝ) 1, φ (unitCircleParam (c b) (r b) t) = ρ)
    (hzero : ∀ i ≠ b, v i 1 = v i 0)
    (A : Fin n → ℝ) (hA : ∀ i ≠ b, ∀ t ∈ Icc (0 : ℝ) 1, |v i t - v i 0| ≤ A i) :
    |circleFormIntegral φ u γ| ≤
      Real.sqrt Real.pi * R * Real.sqrt
        (∫ z in jordanInterior H \ ⋃ i, closedBall (c i) (r i), ‖circleFDeriv u z‖ ^ 2) +
      ρ + ∑ i ∈ Finset.univ.erase b, 2 * Real.pi * r i * A i := by
  have hc (i : Fin n) := circle_boundary_mem_smooth_region H c r
    (fun i => (hr i).le) hd hin hsub i
  refine abs_le_of_distinguished_boundary b _ _ _ ρ _
    (finite_circle_stokes_area_bound hgreen H γ hγ n c r hr hd hin O hO hsub
      φ hφ hφlip u hu hR hbounded henergy) ?_ hρ ?_
  · rw [circleFormIntegral_constant_weight hO hu φ _ (contDiff_unitCircleParam _ _)
      (hc b) (v b) (hv b) (hproj b) ρ hφb, hb, mul_one]
  · intro i hi
    exact circleFormIntegral_unitCircle_zero_period hO hu φ hφ hφlip _ (hr i).le
      (hc i) (v i) (hv i) (hproj i) (hzero i hi) (A i) (hA i hi)

 theorem circle_costs_le_square_norm
    {I : Type*} [DecidableEq I] (s : Finset I) (r A : I → ℝ) {L : ℝ}
    (hL : 0 ≤ L) (hr : ∑ i ∈ s, r i ^ 2 ≤ L ^ 2) :
    (∑ i ∈ s, 2 * Real.pi * r i * A i) ≤
      2 * Real.pi * L * Real.sqrt (∑ i ∈ s, A i ^ 2) := by
  have hs : Real.sqrt (∑ i ∈ s, r i ^ 2) ≤ L := by
    simpa only [Real.sqrt_sq hL] using Real.sqrt_le_sqrt hr
  calc
    _ = (2 * Real.pi) * ∑ i ∈ s, r i * A i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ (2 * Real.pi) * (Real.sqrt (∑ i ∈ s, r i ^ 2) *
        Real.sqrt (∑ i ∈ s, A i ^ 2)) :=
      mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt s r A) (by positivity)
    _ ≤ (2 * Real.pi) * (L * Real.sqrt (∑ i ∈ s, A i ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _)) (by positivity)
    _ = _ := by ring

end CircleDomainRigidity

end

end OAI
