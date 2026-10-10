import OAI.Analysis.CircleDomains.Sobolev.ZeroOffsetStokes

namespace OAI

/-! The distinguished offset disappears for every fixed finite period.
No normalization of that period is needed for the Stokes upper bound. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology BigOperators

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem abs_le_of_boundary_costs
    {I : Type*} [Fintype I] [DecidableEq I] (b : I)
    (outer : ℝ) (inner : I → ℝ) (E B : ℝ) (cost : I → ℝ)
    (harea : |outer - ∑ i, inner i| ≤ E) (hb : |inner b| ≤ B)
    (hother : ∀ i ≠ b, |inner i| ≤ cost i) :
    |outer| ≤ E + B + ∑ i ∈ Finset.univ.erase b, cost i := by
  have hsum : (∑ i, |inner i|) ≤ B + ∑ i ∈ Finset.univ.erase b, cost i := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ b), add_comm]
    exact add_le_add hb (Finset.sum_le_sum fun i hi => hother i (Finset.mem_erase.mp hi).1)
  calc
    |outer| = |(outer - ∑ i, inner i) + ∑ i, inner i| := by congr 1; ring
    _ ≤ |outer - ∑ i, inner i| + |∑ i, inner i| := abs_add_le _ _
    _ ≤ E + ∑ i, |inner i| := add_le_add harea (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ E + (B + ∑ i ∈ Finset.univ.erase b, cost i) := add_le_add le_rfl hsum
    _ = _ := by ring

 theorem finite_offset_stokes_bound_with_period
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
    (hφb : ∀ t ∈ Icc (0 : ℝ) 1, φ (unitCircleParam (c b) (r b) t) = ρ)
    (hzero : ∀ i ≠ b, v i 1 = v i 0)
    (A : Fin n → ℝ) (hA : ∀ i ≠ b, ∀ t ∈ Icc (0 : ℝ) 1, |v i t - v i 0| ≤ A i) :
    |circleFormIntegral φ u γ| ≤
      Real.sqrt Real.pi * R * Real.sqrt
        (∫ z in jordanInterior H \ ⋃ i, closedBall (c i) (r i), ‖circleFDeriv u z‖ ^ 2) +
      ρ * |v b 1 - v b 0| + ∑ i ∈ Finset.univ.erase b, 2 * Real.pi * r i * A i := by
  have hc (i : Fin n) := circle_boundary_mem_smooth_region H c r
    (fun i => (hr i).le) hd hin hsub i
  refine abs_le_of_boundary_costs b _ _ _ _ _
    (finite_circle_stokes_area_bound hgreen H γ hγ n c r hr hd hin O hO hsub
      φ hφ hφlip u hu hR hbounded henergy) ?_ ?_
  · rw [circleFormIntegral_constant_weight hO hu φ _ (contDiff_unitCircleParam _ _)
      (hc b) (v b) (hv b) (hproj b) ρ hφb, abs_mul, abs_of_nonneg hρ]
  · intro i hi
    exact circleFormIntegral_unitCircle_zero_period hO hu φ hφ hφlip _ (hr i).le
      (hc i) (v i) (hv i) (hproj i) (hzero i hi) (A i) (hA i hi)

 theorem zero_offset_stokes_bound_of_period
    {I : Type*} (s : Finset I) (r A : I → ℝ) (hA : ∀ i ∈ s, 0 ≤ A i)
    (outer E k : ℝ)
    (hbound : ∀ ε > 0, ∃ ρ > 0, ρ ≤ ε ∧
      |outer| ≤ E + ε + ρ * |k| + ∑ i ∈ s, 2 * Real.pi * (r i + ρ) * (A i + ε)) :
    |outer| ≤ E + ∑ i ∈ s, 2 * Real.pi * r i * A i := by
  let g : ℝ → ℝ := fun ε => E + ε + ε * |k| + ∑ i ∈ s, 2 * Real.pi * (r i + ε) * (A i + ε)
  have hg : Continuous g := by dsimp only [g]; fun_prop
  have hlim : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 (E + ∑ i ∈ s, 2 * Real.pi * r i * A i)) := by
    simpa only [g, add_zero, zero_mul] using
      (hg.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  obtain ⟨ρ, _, hρε, hI⟩ := hbound ε hε
  refine hI.trans ?_
  apply add_le_add
  · exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hρε (abs_nonneg k))
  · apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hρε) (by positivity))
      (add_nonneg (hA i hi) hε.le)

end CircleDomainRigidity

end

end OAI
