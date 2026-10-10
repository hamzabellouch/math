import OAI.Analysis.CircleDomains.Topology.CutoffCore
import OAI.Analysis.CircleDomains.Topology.RealCircleRepresentative
import OAI.Analysis.CircleDomains.Sobolev.SmoothMeanPhysicalBranches

namespace OAI

/-! Apply real-plane coordinate transport to the
smooth mean. The original quantitative partial norms are
retained and the physical circle values are unchanged in the domain. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem SmoothMeanPeriodData.euclidean_smooth
    (hsch : PlanarSchoenflies) (K : Set C(PathTime, ℂ)) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (F : C(Sphere, ℂ))
    {G U S M : Set Sphere} {b : Sphere} {π : Sphere → Sphere}
    (Q : SmoothMeanPeriodData hsch K hKS η F G U S M b π) :
    SmoothCircleOn Q.euclidean (planeSphere ⁻¹' (G ∩ π ⁻¹' S)) := by
  have heq : Q.physical ∘ complexPlaneCoordinates = Q.euclidean := by
    funext x
    rw [Q.physical_eq]
    simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  rw [← heq]
  intro x hx a ha
  exact (Q.physical_smooth (complexPlaneCoordinates x) hx a ha).comp x
    complexPlaneCoordinates.contDiff.contDiffAt

 theorem SmoothMeanPeriodData.exists_real_representative
    (hsch : PlanarSchoenflies) (K : Set C(PathTime, ℂ)) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (F : C(Sphere, ℂ))
    {G U S M : Set Sphere} (hG : IsOpen G) (hS : IsOpen S) {b : Sphere}
    {π : Sphere → Sphere} (hπ : Continuous π)
    (Q : SmoothMeanPeriodData hsch K hKS η F G U S M b π)
    (henergy : ∀ i : Fin 2, MemLp (fun x => circleFDeriv Q.euclidean x (EuclideanSpace.single i 1))
      2 (volume.restrict (planeSphere ⁻¹' (G ∩ π ⁻¹' S)))) :
    ∃ f : (ℝ × ℝ) → UnitAddCircle, Measurable f ∧ Measurable (circleGradient f) ∧
      SmoothCircleOn f (realChartDomain (G ∩ π ⁻¹' S)) ∧
      MemLp (circleGradient f) 2 (volume.restrict (realChartDomain (G ∩ π ⁻¹' S))) ∧
      (∀ i : Fin 2, eLpNorm (fun p => circleFDeriv f p
          (if i = 0 then (1, 0) else (0, 1))) 2
          (volume.restrict (realChartDomain (G ∩ π ⁻¹' S))) =
        eLpNorm (fun x => circleFDeriv Q.euclidean x (EuclideanSpace.single i 1))
          2 (volume.restrict (planeSphere ⁻¹' (G ∩ π ⁻¹' S)))) ∧
      ∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ S →
        f (Complex.equivRealProdCLM z) = Q.physical z := by
  let D := realChartDomain (G ∩ π ⁻¹' S)
  have hD : IsOpen D := isOpen_realChartDomain (hG.inter (hS.preimage hπ))
  have hΩ : euclideanPlaneCoordinates ⁻¹' D = planeSphere ⁻¹' (G ∩ π ⁻¹' S) := rfl
  obtain ⟨f, hm, hdm, hs, hE, hn, hv⟩ := exists_real_circle_representative hD Q.euclidean
    (by rw [hΩ]; exact Q.euclidean_smooth hsch K hKS η F)
    (by rw [hΩ]; exact henergy)
  refine ⟨f, hm, hdm, hs, hE, ?_, ?_⟩
  · simpa only [hΩ] using hn
  · intro z hzG hzS
    have hzD : Complex.equivRealProdCLM z ∈ D := by
      simpa only [D, realChartDomain, mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using
        (show (z : Sphere) ∈ G ∩ π ⁻¹' S from ⟨hzG, hzS⟩)
    rw [hv _ hzD, Q.physical_eq]
    rfl


 theorem SmoothMeanPeriodData.real_branch_smooth
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (F : C(Sphere, ℂ))
    {G U S M : Set Sphere} (hG : IsOpen G) {b : Sphere}
    {π : Sphere → Sphere} (hπ : Continuous π)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (Q : SmoothMeanPeriodData hsch K hKS η F G U S M b π) (i : Q.Index) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => Q.branch i (π (Complex.equivRealProdCLM.symm p : Sphere)))
      (realChartDomain G ∩ realChartDomain (π ⁻¹' Q.patch i)) := by
  exact (Q.branch_physical_smooth hsch hsep K hK hKS η F hG hπ h0 h1 i).comp
    Complex.equivRealProdCLM.symm.contDiff.contDiffOn (fun _ hp => hp)

end CircleDomainRigidity

end

end OAI
