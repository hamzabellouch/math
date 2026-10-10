import OAI.Analysis.CircleDomains.Uniformization.ExteriorDiskNormalization
import OAI.Analysis.CircleDomains.Reflection.ReflectionTiles

namespace OAI

/-! Exact spherical reflections in the assigned finite round disks. -/
open Set Function Metric
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity

lemma affineSphere_image_unit_ball (c : ℂ) {r : ℝ} (hr : 0<r) :
    affineSphere (r:ℂ) c (by exact_mod_cast hr.ne') ''
      (((↑) : ℂ → Sphere) '' ball 0 1)=((↑) : ℂ → Sphere) '' ball c r := by
  have hb : ball c r=(fun z : ℂ => c+r • z) '' ball 0 1 := by
    rw [←affinity_unitBall hr c]
    change (fun z : ℂ => c+z) '' ((fun z : ℂ => r • z) '' ball 0 1)=_
    rw [image_image]
  rw [hb,image_image,image_image]
  congr 1
  funext z
  rw [affineSphere_coe]
  congr 1
  simp only [Complex.real_smul,mul_comm,add_comm]

def roundDiskReflection (c : ℂ) (r : ℝ) (hr : 0<r) : Sphere ≃ₜ Sphere :=
  let A := affineSphere (r:ℂ) c (by exact_mod_cast hr.ne')
  A.symm.trans (CannonSphereReflection.reflection.trans A)

lemma roundDiskReflection_involutive (c : ℂ) {r : ℝ} (hr : 0<r) :
    Involutive (roundDiskReflection c r hr) := by
  intro z
  dsimp [roundDiskReflection]
  rw [Homeomorph.symm_apply_apply,CannonSphereReflection.reflection_involutive,
    Homeomorph.apply_symm_apply]

lemma roundDiskReflection_closed_image (c : ℂ) {r : ℝ} (hr : 0<r) :
    roundDiskReflection c r hr '' (((↑) : ℂ → Sphere) '' closedBall c r)=
      (((↑) : ℂ → Sphere) '' ball c r)ᶜ := by
  let A := affineSphere (r:ℂ) c (by exact_mod_cast hr.ne')
  have hc : A '' (((↑) : ℂ → Sphere) '' closedBall 0 1)=
      ((↑) : ℂ → Sphere) '' closedBall c r := affineSphere_image_unit_closedBall c hr
  have ho : A '' (((↑) : ℂ → Sphere) '' ball 0 1)=
      ((↑) : ℂ → Sphere) '' ball c r := affineSphere_image_unit_ball c hr
  have hai : A.symm '' (((↑) : ℂ → Sphere) '' closedBall c r)=
      ((↑) : ℂ → Sphere) '' closedBall 0 1 := by
    rw [←hc,image_image]
    simp only [A.symm_apply_apply,image_id']
  calc
    _ = A '' (CannonSphereReflection.reflection ''
        (A.symm '' (((↑) : ℂ → Sphere) '' closedBall c r))) := by
      simp only [image_image]
      rfl
    _ = _ := by rw [hai,CannonSphereReflection.reflection_image_closedBall,A.image_compl,ho]

lemma roundDiskReflection_outer_image (c : ℂ) {r : ℝ} (hr : 0<r) :
    roundDiskReflection c r hr '' ((((↑) : ℂ → Sphere) '' closedBall c r)ᶜ)=
      ((↑) : ℂ → Sphere) '' ball c r := by
  rw [(roundDiskReflection c r hr).image_compl,roundDiskReflection_closed_image c hr,compl_compl]

lemma roundDiskReflection_coe (c : ℂ) {r : ℝ} (hr : 0<r) {z : ℂ} (hz : z≠c) :
    roundDiskReflection c r hr (z : Sphere)=
      ((c+(r:ℂ)^2/(starRingEnd ℂ (z-c)) : ℂ) : Sphere) := by
  have hrC : (r:ℂ)≠0 := by exact_mod_cast hr.ne'
  have hn : (z-c)/(r:ℂ)≠0 := div_ne_zero (sub_ne_zero.mpr hz) hrC
  change affineSphere (r:ℂ) c hrC
    (CannonSphereReflection.reflection ((((z-c)/(r:ℂ) : ℂ) : Sphere)))=_
  rw [CannonSphereReflection.reflection_coe hn,affineSphere_coe]
  congr 1
  simp only [map_div₀,Complex.conj_ofReal]
  field_simp
  ring

lemma roundDiskReflection_fixed (c : ℂ) {r : ℝ} (hr : 0<r) {z : ℂ}
    (hz : z∈sphere c r) : roundDiskReflection c r hr (z : Sphere)=(z : Sphere) := by
  have hrC : (r:ℂ)≠0 := by exact_mod_cast hr.ne'
  have hn : (z-c)/(r:ℂ)∈sphere (0:ℂ) 1 := by
    rw [mem_sphere,dist_zero_right,norm_div,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos hr]
    rw [mem_sphere,dist_eq_norm] at hz
    rw [hz,div_self hr.ne']
  change affineSphere (r:ℂ) c hrC
    (CannonSphereReflection.reflection ((((z-c)/(r:ℂ) : ℂ) : Sphere)))=_
  rw [CannonSphereReflection.reflection_fix hn,affineSphere_coe]
  congr 1
  field_simp
  ring

end CircleDomainRigidity

end

end OAI
