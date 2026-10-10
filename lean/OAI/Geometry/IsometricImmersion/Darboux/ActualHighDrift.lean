import OAI.Geometry.IsometricImmersion.Estimates.ActualHighEquation
import OAI.Geometry.IsometricImmersion.Darboux.DriftOperatorIdentity
import OAI.Geometry.IsometricImmersion.Flows.ConstructedHeightFlow

namespace OAI

noncomputable section
open Set Function
open scoped ContDiff

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.Weighted

theorem actual_differentiated_drift
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (m : ℕ) {p : Coord} (hp : p ∈ U) :
    driftOperator (hessianQuotient g z) (heightOriginalA g z)
      (heightOriginalB g z (m + 3)) (heightOriginalC0 g z (m + 3))
      (verticalJet z (m + 3)) p = actualHighRemainder g z m p := by
  have hid := driftOperator_linearized_identity
    (hessianQuotient_contDiffOn hg hU hz hyy) (verticalJet_contDiffOn hU hz (m + 3))
    (heightOriginalA_contDiffOn hg hU hz hyy) hU hp
    (heightPFirst g z 0) (heightPFirst g z 1) (m + 3)
  have hC : (fun r => coordinateDrift (hessianQuotient g z) (hessianQuotient g z) r -
      heightPFirst g z 0 r * hessianQuotient g z r - heightPFirst g z 1 r +
      (m + 3 : ℝ) * coordPartial 1 (heightOriginalA g z) r) =
      heightOriginalC0 g z (m + 3) := by
    funext r
    simp only [heightOriginalC0, Nat.cast_add, Nat.cast_ofNat]
    ring
  simp only [Nat.cast_add, Nat.cast_ofNat] at hid
  rw [hC] at hid
  have hB : (fun r => -heightPFirst g z 0 r -
      2 * (m + 3 : ℝ) * coordPartial 1 (hessianQuotient g z) r) =
      heightOriginalB g z (m + 3) := by
    funext r
    simp only [heightOriginalB, Nat.cast_add, Nat.cast_ofNat]
  rw [hB] at hid
  rw [hid]
  have h := actual_differentiated_Darboux_at hg hU hz hD hyy m hp
  unfold directLinearization secondJetCorrection at h
  simp only [heightOriginalA] at *
  linarith only [h]

theorem exists_admissible_height_high_equation
    {g : MetricField} {z : Coord → ℝ} (h : PatchAdmissibleHeight g z) :
    ∃ Y : ℝ → ℝ → ℝ,
      ContDiffOn ℝ ∞ (capChart Y) capChartDomain ∧
      MapsTo (capChart Y) capChartDomain modelOpenSquare ∧
      (∀ p ∈ capChartDomain, 0 < capChartRho Y p ∧ 0 < heightChartG1 g z Y p) ∧
      (∀ ell : ℕ, ContDiffOn ℝ ∞ (heightChartC g z Y ell) capChartDomain ∧
        ContDiffOn ℝ ∞ (heightChartRemainder g z Y ell) capChartDomain ∧
        ∀ p ∈ capChartDomain,
          heightChartC g z Y ell p = ((ell : ℝ) + 1) * coordPartial 1 (heightChartA g z Y) p +
            heightChartA g z Y p * heightChartRemainder g z Y ell p) ∧
      (∀ m : ℕ, ∀ p ∈ capChartDomain,
        multiplierOperator (heightChartA g z Y) (heightChartB g z Y (m + 3))
          (heightChartC g z Y (m + 3)) (capPullback Y (verticalJet z (m + 3))) p =
          capPullback Y (actualHighRemainder g z m) p) := by
  obtain ⟨Y, hY, hmap, _, _, _, hpos, hcoef, htransport⟩ :=
    exists_admissible_height_operator_chart h
  obtain ⟨U, _, hSU, hg, hz, hD, _, hyy, _⟩ := h
  have hOU : modelOpenSquare ⊆ U := modelOpenSquare_subset.trans hSU
  have hgo : SmoothPositiveOn g modelOpenSquare :=
    ⟨fun i j => (hg.1 i j).mono hOU, fun p hp => hg.2 p (hOU hp)⟩
  have hzo : ContDiffOn ℝ ∞ z modelOpenSquare := hz.mono hOU
  have hDo : ∀ p ∈ modelOpenSquare,
      (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p :=
    fun p hp => hD p (modelOpenSquare_subset hp)
  have hyyo : ∀ p ∈ modelOpenSquare, covHessian g z p 1 1 ≠ 0 :=
    fun p hp => hyy p (modelOpenSquare_subset hp)
  refine ⟨Y, hY, hmap, hpos, hcoef, ?_⟩
  intro m p hp
  have hu := verticalJet_contDiffOn modelOpenSquare_isOpen hzo (m + 3)
  rw [← (htransport (verticalJet z (m + 3)) hu p hp).2.2.2 (m + 3)]
  exact actual_differentiated_drift hgo modelOpenSquare_isOpen hzo hDo hyyo m (hmap hp)

end SmoothLocal.HighEquation

end

end OAI
