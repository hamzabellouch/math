import OAI.Analysis.CircleDomains.Topology.OpenDomainRepresentative
import OAI.Analysis.CircleDomains.Sobolev.RealGradientNorm
import OAI.Analysis.CircleDomains.Topology.PlaneQuotientRepresentative
import OAI.Analysis.CircleDomains.Topology.CutoffCore

namespace OAI

/-! A measurable, smooth finite-plane representative with the constructed
Sobolev energy and the actual quotient pullback identity. -/

open Set Function MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable {X : Type*} [MetricSpace X] [MeasurableSpace C(PathTime, X)]

theorem exists_real_physical_representative
    (d : PathCodeData X Sphere) (hG : IsOpen d.physicalDomain)
    (π : Sphere → X) (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (w : EuclideanPlane → ℝ) (hw : ContDiffOn ℝ (⊤ : ℕ∞) w (physicalPlaneDomain d.physicalDomain))
    (henergy : ∀i : Fin 2, MemLp (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1))
      2 (volume.restrict (physicalPlaneDomain d.physicalDomain))) :
    ∃v : (ℝ × ℝ) → ℝ,
      Measurable v ∧ ContDiffOn ℝ (⊤ : ℕ∞) v (FiniteTransfer.realChartDomain d.physicalDomain) ∧
      MemLp (FiniteTransfer.planarGradient v) 2
        (volume.restrict (FiniteTransfer.realChartDomain d.physicalDomain)) ∧
      (∀i : Fin 2, eLpNorm (fun p => (fderiv ℝ v p)
        (if i = 0 then (1, 0) else (0, 1))) 2
          (volume.restrict (FiniteTransfer.realChartDomain d.physicalDomain)) =
        eLpNorm (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) 2
          (volume.restrict (physicalPlaneDomain d.physicalDomain))) ∧
      ∀z : ℂ, (z : Sphere) ∈ d.physicalDomain →
        v (Complex.equivRealProdCLM z) = quotientPlaneRepresentative d w (π z) := by
  let Ω := physicalPlaneDomain d.physicalDomain
  let D := FiniteTransfer.realChartDomain d.physicalDomain
  have hΩ : IsOpen Ω := isOpen_physicalPlaneDomain hG
  have hD : IsOpen D := FiniteTransfer.isOpen_realChartDomain hG
  let w₀ := openZeroExtension Ω w
  let v : (ℝ × ℝ) → ℝ := w₀ ∘ euclideanPlaneCoordinates.symm
  have hmeas : Measurable w₀ := openZeroExtension_measurable hΩ hw.continuousOn
  have hs : ContDiffOn ℝ (⊤ : ℕ∞) w₀ (euclideanPlaneCoordinates ⁻¹' D) :=
    openZeroExtension_contDiffOn hw
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞) v D := by
    apply hs.comp euclideanPlaneCoordinates.symm.contDiff.contDiffOn
    intro p hp
    simpa only [mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using hp
  have hgrad : ∀i : Fin 2, MemLp (fun x => (fderiv ℝ w₀ x) (EuclideanSpace.single i 1))
      2 (volume.restrict (euclideanPlaneCoordinates ⁻¹' D)) :=
    fun i => openZeroExtension_gradient_memLp hΩ (henergy i)
  refine ⟨v, hmeas.comp euclideanPlaneCoordinates.symm.continuous.measurable, hsm,
    real_chart_gradient_memLp hD hs hgrad, ?_, ?_⟩
  · intro i
    exact real_chart_zeroExtension_partial_eLpNorm hD hw i (henergy i)
  intro z hz
  let x := euclideanPlaneCoordinates.symm (Complex.equivRealProdCLM z)
  have heq : planeSphere x = (z : Sphere) := by
    apply congrArg ((↑) : ℂ → Sphere)
    change Complex.equivRealProdCLM.symm
      (euclideanPlaneCoordinates (euclideanPlaneCoordinates.symm (Complex.equivRealProdCLM z))) = z
    simp only [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
  have hx : x ∈ Ω := by
    change planeSphere x ∈ d.physicalDomain
    rwa [heq]
  change openZeroExtension Ω w x = quotientPlaneRepresentative d w (π z)
  rw [openZeroExtension_eq hx, ← heq]
  exact (quotientPlaneRepresentative_plane d w π he hx).symm

end CircleDomainRigidity

end

end OAI
