import OAI.Geometry.IsometricImmersion.Caps.CapFlowUniqueness
import OAI.Geometry.IsometricImmersion.Obstructions.PatchAdmissibility

namespace OAI

noncomputable section
open Set Filter Function Metric
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem capChart_eqOn_of_same_open_ode
    {q : Coord → ℝ} {U : Set Coord} {Y Z : ℝ → ℝ → ℝ}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hYstart : ∀ s ∈ Ioo (-2 : ℝ) 2, Y s 0 = s)
    (hYode : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Ioo (-2 : ℝ) 2) t)
    (hYdisp : ∀ p ∈ capChartDomain, |capFlowHeight Y p-p 1| ≤ (1 : ℝ)/50)
    (hZstart : ∀ s ∈ Ioo (-2 : ℝ) 2, Z s 0 = s)
    (hZode : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2,
      HasDerivWithinAt (Z s) (-q (coordinatePoint t (Z s t))) (Ioo (-2 : ℝ) 2) t)
    (hZdisp : ∀ p ∈ capChartDomain, |capFlowHeight Z p-p 1| ≤ (1 : ℝ)/50) :
    EqOn (capChart Y) (capChart Z) capChartDomain := by
  obtain ⟨K, hK⟩ := exists_flowField_lipschitz hq hU hSU
  have hsame (s : ℝ) (hs : s ∈ Ioo (-2 : ℝ) 2) : EqOn (Y s) (Z s) (Ioo (-2 : ℝ) 2) := by
    apply ODE_solution_unique_of_mem_Ioo
      (v := flowField q) (s := fun _ => closedBall (0 : ℝ) 3)
      (fun t ht => hK t ⟨ht.1.le, ht.2.le⟩) (t₀ := 0) (by norm_num)
    · intro t ht
      exact ⟨(hYode s hs t ht).hasDerivAt (isOpen_Ioo.mem_nhds ht),
        cap_trajectory_mem_ball_of_displacement hYdisp hs ht⟩
    · intro t ht
      exact ⟨(hZode s hs t ht).hasDerivAt (isOpen_Ioo.mem_nhds ht),
        cap_trajectory_mem_ball_of_displacement hZdisp hs ht⟩
    · rw [hYstart s hs, hZstart s hs]
  intro p hp
  unfold capChart capFlowHeight
  rw [hsame (p 1) hp.2 hp.1]

theorem actual_height_capCharts_eq_of_closed_open_ode
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {Y Z : ℝ → ℝ → ℝ}
    (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (hSU : modelSquare ⊆ U) (hyy : ∀ p ∈ modelSquare, covHessian g z p 1 1 ≠ 0)
    (hYstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hYode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-hessianQuotient g z (coordinatePoint t (Y s t)))
        (Icc (-2 : ℝ) 2) t)
    (hYdisp : ∀ p ∈ capChartDomain, |capFlowHeight Y p-p 1| ≤ (1 : ℝ)/50)
    (hZstart : ∀ s ∈ Icc (-2 : ℝ) 2, Z s 0 = s)
    (hZode : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2,
      HasDerivWithinAt (Z s) (-hessianQuotient g z (coordinatePoint t (Z s t)))
        (Ioo (-2 : ℝ) 2) t)
    (hZdisp : ∀ p ∈ capChartDomain, |capFlowHeight Z p-p 1| ≤ (1 : ℝ)/50) :
    EqOn (capChart Y) (capChart Z) capChartDomain := by
  obtain ⟨W, hW, hSW, hWU, hne, hqW⟩ := exists_open_hessianQuotient_domain hg hU hz hSU hyy
  exact capChart_eqOn_of_same_open_ode hqW hW hSW
    (fun s hs => hYstart s ⟨hs.1.le, hs.2.le⟩)
    (fun s hs t ht => (hYode s ⟨hs.1.le, hs.2.le⟩ t ⟨ht.1.le, ht.2.le⟩).mono Ioo_subset_Icc_self)
    hYdisp (fun s hs => hZstart s ⟨hs.1.le, hs.2.le⟩) hZode hZdisp

end SmoothLocal.Flow

end

end OAI
