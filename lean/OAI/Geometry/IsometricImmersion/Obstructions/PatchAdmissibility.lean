import OAI.Geometry.IsometricImmersion.Darboux.ActualDriftEquation
import OAI.Geometry.IsometricImmersion.Darboux.DarbouxEquation
import OAI.Geometry.IsometricImmersion.Flows.FlowJointSmooth

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry
open SmoothLocal.Flow SmoothLocal.ODE

def PatchAdmissibleHeight (g : MetricField) (z : Coord → ℝ) : Prop :=
  ∃ U : Set Coord, IsOpen U ∧ modelSquare ⊆ U ∧ SmoothPositiveOn g U ∧
    ContDiffOn ℝ ∞ z U ∧
    (∀ p ∈ modelSquare,
      (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) ∧
    (∀ p ∈ modelSquare, 0 < heightEnergy g z p) ∧
    (∀ p ∈ modelSquare, covHessian g z p 1 1 ≠ 0) ∧
    (∀ p ∈ modelSquare, |hessianQuotient g z p| ≤ (1 : ℝ) / 100)

theorem exists_open_hessianQuotient_domain
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hSU : modelSquare ⊆ U)
    (hyy : ∀ p ∈ modelSquare, covHessian g z p 1 1 ≠ 0) :
    ∃ V : Set Coord, IsOpen V ∧ modelSquare ⊆ V ∧ V ⊆ U ∧
      (∀ p ∈ V, covHessian g z p 1 1 ≠ 0) ∧
      ContDiffOn ℝ ∞ (hessianQuotient g z) V := by
  let V := U ∩ (fun p => covHessian g z p 1 1) ⁻¹' ({0} : Set ℝ)ᶜ
  have hV : IsOpen V :=
    (covHessian_contDiffOn hg hU hz 1 1).continuousOn.isOpen_inter_preimage
      hU isClosed_singleton.isOpen_compl
  have hVU : V ⊆ U := fun _ hp => hp.1
  have hSV : modelSquare ⊆ V := fun p hp => ⟨hSU hp, hyy p hp⟩
  have hnonzero : ∀ p ∈ V, covHessian g z p 1 1 ≠ 0 := fun _ hp => hp.2
  have hgv : SmoothPositiveOn g V :=
    ⟨fun i j => (hg.1 i j).mono hVU, fun p hp => hg.2 p (hVU hp)⟩
  exact ⟨V, hV, hSV, hVU, hnonzero,
    hessianQuotient_contDiffOn hgv hV (hz.mono hVU) hnonzero⟩

theorem patchAdmissibleHeight_exists_smooth_flow
    {g : MetricField} {z : Coord → ℝ} (h : PatchAdmissibleHeight g z) :
    ∃ Y : ℝ → ℝ → ℝ,
      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
        HasDerivWithinAt (Y s) (-hessianQuotient g z (coordinatePoint t (Y s t)))
          (Icc (-2 : ℝ) 2) t) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
        |Y s t - s| ≤ (1 : ℝ) / 50) ∧
      (∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2,
        HasDerivAt (fun u => Y u t)
          (Real.exp (-(∫ r in 0..t,
            coordPartial 1 (hessianQuotient g z) (coordinatePoint r (Y s r))))) s ∧
        0 < deriv (fun u => Y u t) s) := by
  obtain ⟨U, hU, hSU, hg, hz, _, _, hyy, hsmall⟩ := h
  obtain ⟨V, hV, hSV, _, _, hq⟩ := exists_open_hessianQuotient_domain hg hU hz hSU hyy
  exact exists_smooth_cap_flow hq hV hSV hsmall

end SmoothLocal.Geometry

end

end OAI
