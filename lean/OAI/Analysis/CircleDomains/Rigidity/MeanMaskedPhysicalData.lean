import OAI.Analysis.CircleDomains.Sobolev.SmoothMeanRealRepresentative
import OAI.Analysis.CircleDomains.Topology.GraphBoundaryBranches
import OAI.Analysis.CircleDomains.Rigidity.AssembledMaskedModel

namespace OAI

/-! The selected smooth mean supplies the actual physical inputs to
masked finite transfer. Its closed-mask energy is obtained by restricting
the original open-mask energy, without enlarging any norm. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem SmoothMeanPeriodData.exists_masked_physical_data
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (F : C(Sphere, ℂ))
    {G U S M : Set Sphere} (hG : IsOpen G) (hS : IsOpen S) (hM : IsClosed M)
    {b : Sphere} (hbU : b ∉ U) (hMS : M \ {b} ⊆ S)
    {π : Sphere → Sphere} (hπ : Continuous π)
    (hPU : ∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ U)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (Q : SmoothMeanPeriodData hsch K hKS η F G U S M b π)
    (henergy : ∀ i : Fin 2, MemLp (fun x => circleFDeriv Q.euclidean x (EuclideanSpace.single i 1))
      2 (volume.restrict (planeSphere ⁻¹' (G ∩ π ⁻¹' S)))) :
    ∃ f : (ℝ × ℝ) → UnitAddCircle, Measurable f ∧ Measurable (circleGradient f) ∧
      SmoothCircleOn f (realChartDomain G ∩ interior (physicalMask π M)) ∧
      MemLp (circleGradient f) 2 ((volume.restrict (realChartDomain G)).restrict (physicalMask π M)) ∧
      (∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ S →
        f (Complex.equivRealProdCLM z) = Q.physical z) ∧
      (∀ x ∈ realChartDomain G ∩ interior (physicalMask π M),
        (π (Complex.equivRealProdCLM.symm x : Sphere), f x) ∈
          periodBandGraph U M b Q.patch Q.branch) ∧
      (∀ i, ContDiffOn ℝ ∞
        (fun x : ℝ × ℝ => Q.branch i (π (Complex.equivRealProdCLM.symm x : Sphere)))
        (realChartDomain G ∩ realChartDomain (π ⁻¹' Q.patch i))) ∧
      (∀ i x, x ∈ realChartDomain G ∩ realChartDomain (π ⁻¹' Q.patch i) →
        (Q.branch i (π (Complex.equivRealProdCLM.symm x : Sphere)) : UnitAddCircle) = f x) ∧
      (∀ i : Fin 2, eLpNorm (fun p => circleFDeriv f p
          (if i = 0 then (1, 0) else (0, 1))) 2
          (volume.restrict (realChartDomain (G ∩ π ⁻¹' S))) =
        eLpNorm (fun x => circleFDeriv Q.euclidean x (EuclideanSpace.single i 1))
          2 (volume.restrict (planeSphere ⁻¹' (G ∩ π ⁻¹' S)))) := by
  obtain ⟨f, hmf, hdf, hsf, hEf, hn, hval⟩ :=
    Q.exists_real_representative hsch K hKS η F hG hS hπ henergy
  have hMSphysical (z : ℂ) (hzG : (z : Sphere) ∈ G) (hzM : π (z : Sphere) ∈ M) :
      π (z : Sphere) ∈ S := by
    apply hMS
    refine ⟨hzM, ?_⟩
    intro heq
    exact hbU (heq ▸ hPU z hzG)
  have hsub : realChartDomain G ∩ physicalMask π M ⊆ realChartDomain (G ∩ π ⁻¹' S) := by
    intro x hx
    exact ⟨hx.1, hMSphysical _ hx.1 hx.2⟩
  have hMm : MeasurableSet (physicalMask π M) :=
    ((hM.preimage hπ).preimage
      (OnePoint.continuous_coe.comp Complex.equivRealProdCLM.symm.continuous)).measurableSet
  have hE : MemLp (circleGradient f) 2
      ((volume.restrict (realChartDomain G)).restrict (physicalMask π M)) := by
    rw [Measure.restrict_restrict hMm, inter_comm]
    exact hEf.mono_measure (Measure.restrict_mono_set volume hsub)
  refine ⟨f, hmf, hdf, (fun x hx => hsf x (hsub ⟨hx.1, interior_subset hx.2⟩)),
    hE, hval, ?_, ?_, ?_, hn⟩
  · intro x hx
    have hzG : (Complex.equivRealProdCLM.symm x : Sphere) ∈ G := hx.1
    have hzM : π (Complex.equivRealProdCLM.symm x : Sphere) ∈ M :=
      (show x ∈ physicalMask π M from interior_subset hx.2)
    have hzS := hMSphysical _ hzG hzM
    have hv := hval _ hzG hzS
    simp only [ContinuousLinearEquiv.apply_symm_apply] at hv
    rw [hv]
    exact Q.physical_mem_graph hsch K hKS η F hzG (hPU _ hzG) hzM hzS
  · exact fun i => Q.real_branch_smooth hsch hsep K hK hKS η F hG hπ h0 h1 i
  · intro i x hx
    have hzS := Q.patch_closure i (subset_closure hx.2)
    have hv := hval _ hx.1 hzS
    simp only [ContinuousLinearEquiv.apply_symm_apply] at hv
    exact (Q.branch_physical_projection hsch hsep K hK hKS η F h0 h1 i hx.1 hx.2).trans hv.symm

end CircleDomainRigidity

end

end OAI
