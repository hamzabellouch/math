import OAI.Analysis.CircleDomains.Reflection.ConformalBoundaryChart

namespace OAI

/-! Explicit Möbius normalization of a finite circular exterior to the
unit disk. This converts the actual circularization maps to the target
used by the boundary-continuation argument. -/
open Set Function Filter Metric
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity

def exteriorDiskNormalization (c : ℂ) (r : ℝ) (hr : 0<r) : Sphere ≃ₜ Sphere :=
  (affineSphere (r:ℂ) c (by exact_mod_cast hr.ne')).symm.trans CannonMobius.inversion

lemma affineSphere_image_unit_closedBall (c : ℂ) {r : ℝ} (hr : 0<r) :
    affineSphere (r:ℂ) c (by exact_mod_cast hr.ne') ''
      (((↑) : ℂ → Sphere) '' closedBall 0 1) =
      ((↑) : ℂ → Sphere) '' closedBall c r := by
  rw [closedBall_eq_affine_image hr.le c,image_image,image_image]
  congr 1
  funext z
  rw [affineSphere_coe]
  congr 1
  simp only [Complex.real_smul,mul_comm,add_comm]

lemma exteriorDiskNormalization_image (c : ℂ) {r : ℝ} (hr : 0<r) :
    exteriorDiskNormalization c r hr ''
      ((((↑) : ℂ → Sphere) '' closedBall c r)ᶜ) =
      ((↑) : ℂ → Sphere) '' ball 0 1 := by
  let A := affineSphere (r:ℂ) c (by exact_mod_cast hr.ne')
  have hA : A '' (((↑) : ℂ → Sphere) '' closedBall 0 1)=
      ((↑) : ℂ → Sphere) '' closedBall c r := affineSphere_image_unit_closedBall c hr
  have hAi : A.symm '' ((((↑) : ℂ → Sphere) '' closedBall c r)ᶜ)=
      ((((↑) : ℂ → Sphere) '' closedBall 0 1)ᶜ) := by
    rw [←hA,←A.image_compl,image_image]
    simp only [A.symm_apply_apply, image_id']
  change (CannonMobius.inversion ∘ A.symm) '' _ = _
  rw [image_comp,hAi,←inversion_preimage_unitDisk,
    image_preimage_eq _ CannonMobius.inversion.surjective]

lemma isConformalEquivalence_exteriorDiskNormalization (c : ℂ) {r : ℝ} (hr : 0<r) :
    IsConformalEquivalence (exteriorDiskNormalization c r hr)
      ((((↑) : ℂ → Sphere) '' closedBall c r)ᶜ)
      (((↑) : ℂ → Sphere) '' ball 0 1) := by
  have he := isConformalEquivalence_of_homeomorph (exteriorDiskNormalization c r hr)
    ((((↑) : ℂ → Sphere) '' closedBall c r)ᶜ)
    (fun p _ => (isConformalAt_inversion _).comp
      (isConformalAt_affineSphere_symm (r:ℂ) c (by exact_mod_cast hr.ne') p))
    (fun p _ => (isConformalAt_affineSphere (r:ℂ) c (by exact_mod_cast hr.ne') _).comp
      (isConformalAt_inversion p))
  rwa [exteriorDiskNormalization_image c hr] at he

lemma circular_exterior_boundary_chart_continuation {U : Set Sphere}
    {f : Sphere → Sphere} {κ : ℂ → ℂ} {R r : ℝ} {c : ℂ}
    (hU : IsOpen U)
    (hf : IsConformalEquivalence f U ((((↑) : ℂ → Sphere) '' closedBall c r)ᶜ))
    (hr : 0<r) (hR : 0<R) (hκ : DifferentiableOn ℂ κ (upperSemidisk R))
    (hm : ∀z∈upperSemidisk R,(κ z : Sphere)∈U)
    (hc : ∀p:ℂ,‖p‖≤R → p.im=0 → ContinuousAt κ p)
    (hb : ∀p:ℂ,‖p‖≤R → p.im=0 → (κ p : Sphere)∉U) :
    ∃ (V : Set ℂ) (F : ℂ → ℂ), IsOpen V ∧ (0:ℂ)∈V ∧ V⊆ball 0 R ∧
      DifferentiableOn ℂ F V ∧
      EqOn F (fun z => finiteCoord (exteriorDiskNormalization c r hr (f (κ z : Sphere))))
        (V∩{z : ℂ | 0<z.im}) :=
  conformal_disk_boundary_chart_continuation hU
    (hf.trans (isConformalEquivalence_exteriorDiskNormalization c hr)) hR hκ hm hc hb

end CircleDomainRigidity

end

end OAI
