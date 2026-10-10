import OAI.Analysis.CircleDomains.Sobolev.SmoothPlaneEnergyTransport

namespace OAI

/-! The conformal energy identity applied to differences of the actual
smooth transports, for the Cauchy argument below. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

 theorem smooth_transport_difference_energy
    {f fi : Sphere → Sphere} {U V : Set Sphere}
    (heq : IsSmoothSphereEquivalence f fi U V) (hU : IsOpen U) (hV : IsOpen V)
    (hinf : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty)
    (hf : IsConformalOn f U) {u v : EuclideanPlane → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (physicalPlaneDomain U))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v (physicalPlaneDomain U))
    (hgu : ∀ i : Fin 2, MemLp (fun x => fderiv ℝ u x (EuclideanSpace.single i 1))
      2 (volume.restrict (physicalPlaneDomain U)))
    (hgv : ∀ i : Fin 2, MemLp (fun x => fderiv ℝ v x (EuclideanSpace.single i 1))
      2 (volume.restrict (physicalPlaneDomain U))) :
    (∫ x in physicalPlaneDomain V,
      (fderiv ℝ (planeInverseTransport fi u) x (EuclideanSpace.single 0 1)-
        fderiv ℝ (planeInverseTransport fi v) x (EuclideanSpace.single 0 1))^2+
      (fderiv ℝ (planeInverseTransport fi u) x (EuclideanSpace.single 1 1)-
        fderiv ℝ (planeInverseTransport fi v) x (EuclideanSpace.single 1 1))^2) =
    ∫ x in physicalPlaneDomain U,
      (fderiv ℝ u x (EuclideanSpace.single 0 1)-fderiv ℝ v x (EuclideanSpace.single 0 1))^2+
      (fderiv ℝ u x (EuclideanSpace.single 1 1)-fderiv ℝ v x (EuclideanSpace.single 1 1))^2 := by
  have hPU := isOpen_physicalPlaneDomain hU
  have hPV := isOpen_physicalPlaneDomain hV
  have hdu (x) (hx : x ∈ physicalPlaneDomain U) : DifferentiableAt ℝ u x :=
    (hu.contDiffAt (hPU.mem_nhds hx)).differentiableAt (by norm_num)
  have hdv (x) (hx : x ∈ physicalPlaneDomain U) : DifferentiableAt ℝ v x :=
    (hv.contDiffAt (hPU.mem_nhds hx)).differentiableAt (by norm_num)
  have hgs (i : Fin 2) : MemLp (fun x => fderiv ℝ (fun x => u x-v x) x
      (EuclideanSpace.single i 1)) 2 (volume.restrict (physicalPlaneDomain U)) := by
    apply MemLp.ae_eq (hf_Lp := (hgu i).sub (hgv i))
    filter_upwards [ae_restrict_mem hPU.measurableSet] with x hx
    simp only [Pi.sub_apply,fderiv_fun_sub (hdu x hx) (hdv x hx),sub_apply]
  have hs := smooth_plane_energy_transport heq hU hV hinf hfix hf (hu.sub hv) hgs
  have htu := (smooth_plane_energy_transport heq hU hV hinf hfix hf hu hgu).1
  have htv := (smooth_plane_energy_transport heq hU hV hinf hfix hf hv hgv).1
  have hsub : planeInverseTransport fi (fun x => u x-v x) =
      (fun x => planeInverseTransport fi u x-planeInverseTransport fi v x) := rfl
  rw [hsub] at hs
  calc
    _ = ∫ x in physicalPlaneDomain V,
        (fderiv ℝ (fun x => planeInverseTransport fi u x-planeInverseTransport fi v x) x
          (EuclideanSpace.single 0 1))^2+
        (fderiv ℝ (fun x => planeInverseTransport fi u x-planeInverseTransport fi v x) x
          (EuclideanSpace.single 1 1))^2 := by
      apply setIntegral_congr_fun hPV.measurableSet
      intro x hx
      have h₀ := (htu.contDiffAt (hPV.mem_nhds hx)).differentiableAt (by norm_num)
      have h₁ := (htv.contDiffAt (hPV.mem_nhds hx)).differentiableAt (by norm_num)
      simp only [fderiv_fun_sub h₀ h₁,sub_apply]
    _ = _ := hs.2.2
    _ = _ := by
      apply setIntegral_congr_fun hPU.measurableSet
      intro x hx
      simp only [fderiv_fun_sub (hdu x hx) (hdv x hx),sub_apply]

end CircleDomainRigidity

end

end OAI
