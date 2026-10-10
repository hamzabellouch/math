import OAI.Geometry.IsometricImmersion.Flows.FlowHeightCoefficients
import OAI.Geometry.IsometricImmersion.Obstructions.PatchAdmissibility

namespace OAI

noncomputable section
open Set Function
open scoped ContDiff

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def modelOpenSquare : Set Coord := coordinateRectangle 3 (-3) 3

theorem modelOpenSquare_isOpen : IsOpen modelOpenSquare := coordinateRectangle_isOpen _ _ _

theorem modelOpenSquare_subset : modelOpenSquare ⊆ modelSquare := by
  intro p hp
  constructor <;> intro i <;> fin_cases i
  · exact hp.1.1.le
  · exact hp.2.1.le
  · exact hp.1.2.le
  · exact hp.2.2.le

theorem capChart_mem_modelOpenSquare {Y : ℝ → ℝ → ℝ} {p : Coord}
    (hp : p ∈ capChartDomain) (hdisp : |capFlowHeight Y p - p 1| ≤ (1 : ℝ) / 50) :
    capChart Y p ∈ modelOpenSquare := by
  change (capChart Y p) 0 ∈ Ioo (-3 : ℝ) 3 ∧ (capChart Y p) 1 ∈ Ioo (-3 : ℝ) 3
  rw [capChart_zero, capChart_one]
  constructor
  · constructor <;> linarith [hp.1.1, hp.1.2]
  · constructor <;> linarith [hp.2.1, hp.2.2, (abs_le.mp hdisp).1, (abs_le.mp hdisp).2]

theorem exists_admissible_height_operator_chart
    {g : MetricField} {z : Coord → ℝ} (h : PatchAdmissibleHeight g z) :
    ∃ Y : ℝ → ℝ → ℝ,
      ContDiffOn ℝ ∞ (capChart Y) capChartDomain ∧
      MapsTo (capChart Y) capChartDomain modelOpenSquare ∧
      (∀ p ∈ capChartDomain, |capFlowHeight Y p - p 1| ≤ (1 : ℝ) / 50) ∧
      ContDiffOn ℝ ∞ (capChartRho Y) capChartDomain ∧
      ContDiffOn ℝ ∞ (capChartSigma Y) capChartDomain ∧
      (∀ p ∈ capChartDomain, 0 < capChartRho Y p ∧ 0 < heightChartG1 g z Y p) ∧
      (∀ ell : ℕ, ContDiffOn ℝ ∞ (heightChartC g z Y ell) capChartDomain ∧
        ContDiffOn ℝ ∞ (heightChartRemainder g z Y ell) capChartDomain ∧
        ∀ p ∈ capChartDomain,
          heightChartC g z Y ell p = ((ell : ℝ) + 1) * coordPartial 1 (heightChartA g z Y) p +
            heightChartA g z Y p * heightChartRemainder g z Y ell p) ∧
      (∀ u : Coord → ℝ, ContDiffOn ℝ ∞ u modelOpenSquare → ∀ p ∈ capChartDomain,
        coordPartial 0 (capPullback Y u) p =
          coordinateDrift (hessianQuotient g z) u (capChart Y p) ∧
        capPullback Y (coordPartial 1 u) p = capChartRho Y p * coordPartial 1 (capPullback Y u) p ∧
        capPullback Y (coordPartial 1 (coordPartial 1 u)) p =
          (capChartRho Y p)^2 * coordPartial 1 (coordPartial 1 (capPullback Y u)) p +
            capChartSigma Y p * coordPartial 1 (capPullback Y u) p ∧
        ∀ ell : ℕ,
          capPullback Y (driftOperator (hessianQuotient g z) (heightOriginalA g z)
            (heightOriginalB g z ell) (heightOriginalC0 g z ell) u) p =
            multiplierOperator (heightChartA g z Y) (heightChartB g z Y ell)
              (heightChartC g z Y ell) (capPullback Y u) p) := by
  obtain ⟨Y, hY, hstart, hode, hdisp, hvar⟩ := patchAdmissibleHeight_exists_smooth_flow h
  obtain ⟨U, hU, hSU, hg, hz, hD, hE, hyy, hsmall⟩ := h
  have hOU : modelOpenSquare ⊆ U := modelOpenSquare_subset.trans hSU
  have hgo : SmoothPositiveOn g modelOpenSquare :=
    ⟨fun i j => (hg.1 i j).mono hOU, fun p hp => hg.2 p (hOU hp)⟩
  have hzo : ContDiffOn ℝ ∞ z modelOpenSquare := hz.mono hOU
  have hDo : ∀ p ∈ modelOpenSquare,
      (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p :=
    fun p hp => hD p (modelOpenSquare_subset hp)
  have hEo : ∀ p ∈ modelOpenSquare, 0 < heightEnergy g z p :=
    fun p hp => hE p (modelOpenSquare_subset hp)
  have hyyo : ∀ p ∈ modelOpenSquare, covHessian g z p 1 1 ≠ 0 :=
    fun p hp => hyy p (modelOpenSquare_subset hp)
  have hvarpos : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2,
      0 < deriv (fun r => Y r t) s := fun s hs t ht => (hvar s hs t ht).2
  have hdisp' : ∀ p ∈ capChartDomain, |capFlowHeight Y p - p 1| ≤ (1 : ℝ) / 50 := by
    intro p hp
    exact hdisp (p 1) ⟨hp.2.1.le, hp.2.2.le⟩ (p 0) ⟨hp.1.1.le, hp.1.2.le⟩
  have hmap : MapsTo (capChart Y) capChartDomain modelOpenSquare :=
    fun p hp => capChart_mem_modelOpenSquare hp (hdisp' p hp)
  refine ⟨Y, capChart_contDiffOn hY, hmap, hdisp', capChartRho_contDiffOn hY hvarpos,
    capChartSigma_contDiffOn hY hvarpos, ?_, ?_, ?_⟩
  · intro p hp
    exact ⟨capChartRho_pos hY hvarpos hp,
      heightChartG1_pos g z hY hvarpos hp (hEo _ (hmap hp)) (hyyo _ (hmap hp))⟩
  · intro ell
    exact ⟨heightChartC_contDiffOn hgo modelOpenSquare_isOpen hzo hDo hyyo hEo hY hvarpos hmap ell,
      heightChartRemainder_contDiffOn hgo modelOpenSquare_isOpen hzo hyyo hEo hY hvarpos hmap ell,
      fun p hp => heightChartC_factor hgo modelOpenSquare_isOpen hzo hDo hyyo hEo hY hvarpos hmap hp ell⟩
  · intro u hu p hp
    have hud : DifferentiableAt ℝ u (capChart Y p) :=
      ((hu.contDiffAt (modelOpenSquare_isOpen.mem_nhds (hmap hp))).differentiableAt (by simp))
    exact ⟨capPullback_partial_time hY hode hp hud,
      capPullback_original_y hY hvarpos hp hud,
      capPullback_original_yy hY hvarpos hu modelOpenSquare_isOpen hmap hp,
      fun ell => height_coefficient_operator_transport hgo modelOpenSquare_isOpen hzo hyyo hY hode hvarpos hmap hu hp ell⟩

end SmoothLocal.Flow

end

end OAI
