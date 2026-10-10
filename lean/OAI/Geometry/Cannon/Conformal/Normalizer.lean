import Mathlib
import OAI.Geometry.Cannon.Conformal.LinearZ
import OAI.Geometry.Cannon.Conformal.BoundedCrossRatios
import OAI.Geometry.Cannon.Conformal.PlaneWeakQSBounded
import OAI.Geometry.Cannon.Actions.Height

namespace OAI

section
section
section
section
section
noncomputable section
noncomputable section
open Set Filter Topology
open scoped OnePoint

noncomputable section
open Set Filter Topology

namespace CannonMobius
open Set Filter Topology
open scoped OnePoint

lemma biholomorphic_stabilizer {f : Sphere ≃ₜ Sphere} (hf : f ∈ biholomorphic)
    (ht : tripleMap f standard=standard) : f=1 := by
  have hi (i : Fin 3) : f (std i)=std i := congrFun (congrArg Subtype.val ht) i
  obtain ⟨a,b,ha,he⟩ := analytic_fix_infty_eq_affine f (hi 0) hf
  have h0 := hi 1
  have h1 := hi 2
  rw [he] at h0 h1
  change affine a b ha (0:ℂ)=((0:ℂ):Sphere) at h0
  change affine a b ha (1:ℂ)=((1:ℂ):Sphere) at h1
  rw [affine_coe] at h0 h1
  have hb : b=0 := by simpa using h0
  have ha1 : a=1 := by simpa [hb] using h1
  rw [he]
  apply Homeomorph.ext
  intro p
  induction p using OnePoint.rec with
  | infty => rfl
  | coe z => simp [affine,affinePlane,ha1,hb]

lemma triple_normalizer_unique {f g : Sphere ≃ₜ Sphere} (hf : f ∈ biholomorphic)
    (hg : g ∈ biholomorphic) (he : tripleMap f standard=tripleMap g standard) : f=g := by
  have h : tripleMap (g⁻¹*f) standard=standard := by
    rw [tripleMap_mul,he]
    apply Subtype.ext
    funext i
    exact g.symm_apply_apply _
  have hh := biholomorphic_stabilizer (biholomorphic.mul_mem (biholomorphic.inv_mem hg) hf) h
  exact (inv_mul_eq_one.mp hh).symm
end CannonMobius

namespace CannonMobius
open Set Filter Topology CannonH3
open scoped OnePoint

lemma reflection_inv : boundaryReflection⁻¹=boundaryReflection :=
  inv_eq_of_mul_eq_one_left boundaryReflection_sq
lemma reflection_affine (a b : ℂ) (ha : a ≠ 0) :
    boundaryReflection*affine a b ha*boundaryReflection=affine (star a) (star b) (star_ne_zero.mpr ha) := by
  apply Homeomorph.ext
  intro p
  induction p using OnePoint.rec with
  | infty => rfl
  | coe z =>
    change ((star (a*star z+b):ℂ):Sphere)=((star a*z+star b:ℂ):Sphere)
    rw [star_add,star_mul,star_star,mul_comm z]
lemma reflection_inversion : boundaryReflection*inversion*boundaryReflection=inversion := by
  apply Homeomorph.ext
  intro p
  induction p using OnePoint.rec with
  | infty =>
    change boundaryReflection (inv ∞)=inv ∞
    rw [inv_infty]
    change ((star (0:ℂ):ℂ):Sphere)=((0:ℂ):Sphere)
    simp
  | coe z =>
    by_cases hz : z=0
    · subst z
      change boundaryReflection (inv ((star (0:ℂ):ℂ):Sphere))=inv ((0:ℂ):Sphere)
      simp only [star_zero,inv_zero]
      rfl
    · change boundaryReflection (inv ((star z:ℂ):Sphere))=inv (z:Sphere)
      rw [inv_coe (star_ne_zero.mpr hz),inv_coe hz]
      change ((star ((star z)⁻¹):ℂ):Sphere)=((z⁻¹:ℂ):Sphere)
      rw [star_inv₀,star_star]

lemma reflection_conjugate_biholomorphic {f : Sphere ≃ₜ Sphere} (hf : f ∈ biholomorphic) :
    boundaryReflection*f*boundaryReflection ∈ biholomorphic := by
  let C : MulAut (Sphere ≃ₜ Sphere) := MulAut.conj boundaryReflection
  have he (g : Sphere ≃ₜ Sphere) : C g=boundaryReflection*g*boundaryReflection := by
    simp [C,MulAut.conj_apply,reflection_inv]
  have ha (a b : ℂ) (h : a ≠ 0) : C (affine a b h) ∈ biholomorphic := by
    rw [he,reflection_affine]
    exact affine_biholomorphic _ _ _
  have hi : C inversion ∈ biholomorphic := by rw [he,reflection_inversion]; exact inversion_biholomorphic
  rw [← he]
  rcases biholomorphic_normal_form f hf with ⟨a,b,h,rfl⟩|⟨p,a,b,h,rfl⟩
  · exact ha a b h
  · rw [map_mul,map_mul]
    exact biholomorphic.mul_mem (biholomorphic.mul_mem (ha 1 p one_ne_zero) hi) (ha a b h)

lemma reflection_standard : tripleMap boundaryReflection standard=standard := by
  apply Subtype.ext
  funext i
  fin_cases i <;> simp [tripleMap,standard,std,boundaryReflection]

def normalizer (t : Triple) : biholomorphic :=
  ⟨(exists_triple_normalizer t).choose,(exists_triple_normalizer t).choose_spec.1⟩
lemma normalizer_spec (t : Triple) : tripleMap (normalizer t).val standard=t :=
  (exists_triple_normalizer t).choose_spec.2

def center (t : Triple) : Half :=
  interior ⟨(normalizer t).val,biholomorphic_mem_boundaryGroup (normalizer t).property⟩ basepoint

lemma center_orbit (f : Sphere ≃ₜ Sphere) (hf : f ∈ biholomorphic) :
    center (tripleMap f standard)=interior ⟨f,biholomorphic_mem_boundaryGroup hf⟩ basepoint := by
  have he : (normalizer (tripleMap f standard)).val=f :=
    triple_normalizer_unique (normalizer _).property hf (normalizer_spec _)
  unfold center
  congr 2
  exact Subtype.ext he

lemma center_biholomorphic (f : Sphere ≃ₜ Sphere) (hf : f ∈ biholomorphic) (t : Triple) :
    center (tripleMap f t)=interior ⟨f,biholomorphic_mem_boundaryGroup hf⟩ (center t) := by
  have he : tripleMap (f*(normalizer t).val) standard=tripleMap f t := by
    rw [tripleMap_mul,normalizer_spec]
  rw [← he,center_orbit _ (biholomorphic.mul_mem hf (normalizer t).property)]
  change CannonH3.interior (⟨f,biholomorphic_mem_boundaryGroup hf⟩*
    ⟨(normalizer t).val,biholomorphic_mem_boundaryGroup (normalizer t).property⟩) basepoint=_
  rw [interior_mul]
  rfl

lemma center_reflection (t : Triple) : center (tripleMap boundaryReflection t)=reflection (center t) := by
  let f := (normalizer t).val
  have hf : f ∈ biholomorphic := (normalizer t).property
  have hfc := reflection_conjugate_biholomorphic hf
  have he : tripleMap (boundaryReflection*f*boundaryReflection) standard=tripleMap boundaryReflection t := by
    rw [tripleMap_mul,tripleMap_mul,reflection_standard,normalizer_spec]
  rw [← he,center_orbit _ hfc]
  change CannonH3.interior (⟨boundaryReflection,reflection_mem_boundaryGroup⟩*
    ⟨f,biholomorphic_mem_boundaryGroup hf⟩*⟨boundaryReflection,reflection_mem_boundaryGroup⟩) basepoint=_
  rw [interior_mul,interior_mul,interior_reflection]
  have hb : reflection basepoint=basepoint := by
    apply Prod.ext
    · change star (0:ℂ)=0
      exact star_zero _
    · rfl
  change reflection (CannonH3.interior ⟨f,biholomorphic_mem_boundaryGroup hf⟩ (reflection basepoint))=_
  rw [hb]
  rfl

lemma center_conformal (f : Sphere ≃ₜ Sphere)
    (hf : f ∈ biholomorphic ∨ boundaryReflection*f ∈ biholomorphic) (t : Triple) :
    center (tripleMap f t)=interior ⟨f,conformal_or_anticonformal_mem hf⟩ (center t) := by
  rcases hf with hf|hf
  · exact center_biholomorphic f hf t
  · have he : boundaryReflection*(boundaryReflection*f)=f := by rw [← mul_assoc,boundaryReflection_sq,one_mul]
    have hs : (⟨f,conformal_or_anticonformal_mem (Or.inr hf)⟩ : boundaryGroup)=
        ⟨boundaryReflection,reflection_mem_boundaryGroup⟩*
        ⟨boundaryReflection*f,biholomorphic_mem_boundaryGroup hf⟩ := Subtype.ext he.symm
    rw [hs,interior_mul,interior_reflection]
    conv_lhs => rw [← he,tripleMap_mul,center_reflection,center_biholomorphic _ hf]
    rfl

lemma center_surjective : Function.Surjective center := by
  intro x
  have ht : (x.2.val:ℂ) ≠ 0 := by exact_mod_cast x.2.property.ne'
  refine ⟨tripleMap (affine (x.2.val:ℂ) x.1 ht) standard,?_⟩
  rw [center_orbit _ (affine_biholomorphic _ _ _),interior_affine]
  apply Prod.ext
  · change (x.2.val:ℂ)*0+x.1=x.1
    simp
  · apply Subtype.ext
    change ‖(x.2.val:ℂ)‖*1=x.2.val
    simp [Complex.norm_real,abs_of_pos x.2.property]
end CannonMobius

end
end
end
end
noncomputable section
namespace CannonMobius
open Set Filter Topology MeasureTheory CannonMetricQC CannonConformal CannonQM CannonH3
open scoped OnePoint ComplexConjugate

lemma sendToInfty_biholomorphic (p : Sphere) : sendToInfty p ∈ biholomorphic := by
  by_cases hp : p=∞
  · simp [sendToInfty,hp]
  · rw [sendToInfty,ite_eq_right hp]
    exact biholomorphic.mul_mem inversion_biholomorphic (affine_biholomorphic 1 (-coordinate p) one_ne_zero)

lemma ae_conformal_post_biholomorphic (f M : Sphere ≃ₜ Sphere) (hM : M ∈ biholomorphic)
    (hf : ∀ᵐ z : ℂ, DifferentiableAt ℝ (inChart false false f) z ∧
      IsConformalMap (fderiv ℝ (inChart false false f) z)) :
    ∀ᵐ z : ℂ, DifferentiableAt ℝ (inChart false false (M*f)) z ∧
      IsConformalMap (fderiv ℝ (inChart false false (M*f)) z) := by
  filter_upwards [hf,chartDomain_ae f false false,chartDomain_ae (M*f) false false]
    with z hz hzdom hMz
  have hMd : inChart false false f z ∈ chartDomain false false M := by
    change M (coordinate (f (z:Sphere)):Sphere) ≠ ∞
    have hzfinite : f (z:Sphere) ≠ ∞ := hzdom
    rw [coe_coordinate hzfinite]
    exact hMz
  have hdM := (analytic_differentiableAt hM.1 false false hMd).restrictScalars ℝ
  have hm := analytic_chart_conformal M hM hMd
  have hc := (hdM.hasFDerivAt.comp z hz.1.hasFDerivAt).congr_of_eventuallyEq
    (chart_mul_eventually M f hzdom)
  exact ⟨hc.differentiableAt,hc.fderiv ▸ hm.comp hz.2⟩

lemma restriction_affine_or_anti (f : Sphere ≃ₜ Sphere) (hi : f ∞=∞)
    (h : (∃ a b : ℂ, a ≠ 0 ∧ ∀ z, finiteRestriction f hi z=a*z+b) ∨
      (∃ a b : ℂ, a ≠ 0 ∧ ∀ z, finiteRestriction f hi z=a*conj z+b)) :
    f ∈ biholomorphic ∨ boundaryReflection*f ∈ biholomorphic := by
  rcases h with ⟨a,b,ha,he⟩ | ⟨a,b,ha,he⟩
  · left
    have hEq : f=affine a b ha := by
      apply Homeomorph.ext
      intro p
      induction p using OnePoint.rec with
      | infty => exact hi
      | coe z =>
        have hz := congrArg (fun w : ℂ => (w:Sphere)) (he z)
        exact (coe_coordinate (coe_map_ne_infty f hi z)).symm.trans hz
    rw [hEq]
    exact affine_biholomorphic a b ha
  · right
    have hEq : f=affine a b ha*boundaryReflection := by
      apply Homeomorph.ext
      intro p
      induction p using OnePoint.rec with
      | infty => exact hi
      | coe z =>
        have hz := congrArg (fun w : ℂ => (w:Sphere)) (he z)
        exact (coe_coordinate (coe_map_ne_infty f hi z)).symm.trans hz
    rw [hEq,← mul_assoc,reflection_affine]
    exact affine_biholomorphic _ _ _

theorem sphere_ae_conformal_rigidity (f : Sphere ≃ₜ Sphere)
    (hf : BoundedCrossRatios f) (hi : BoundedCrossRatios f.symm)
    (hd : ∀ᵐ z : ℂ, DifferentiableAt ℝ (inChart false false f) z ∧
      IsConformalMap (fderiv ℝ (inChart false false f) z)) :
    f ∈ biholomorphic ∨ boundaryReflection*f ∈ biholomorphic := by
  let M := sendToInfty (f ∞)
  have hM : M ∈ biholomorphic := sendToInfty_biholomorphic _
  have hMc : Controlled M (OrderIso.refl _) := sendToInfty_controlled _
  have hInf : (M*f) ∞=∞ := sendToInfty_apply _
  have hC : BoundedCrossRatios (M*f) := hMc.boundedCrossRatios.comp hf f.injective
  have hCi : BoundedCrossRatios (M*f).symm :=
    hi.comp (hMc.inverse M).boundedCrossRatios M.symm.injective
  let P := finiteRestriction (M*f) hInf
  obtain ⟨H,hH,hP⟩ := BoundedCrossRatios.plane_weakQS P
    (boundedCrossRatios_restriction (M*f) hInf hC)
  obtain ⟨J,hJ,hPi⟩ := BoundedCrossRatios.plane_weakQS P.symm
    (boundedCrossRatios_restriction (M*f).symm (symm_infty _ hInf) hCi)
  have hpconf : ∀ᵐ z : ℂ, IsConformalMap (fderiv ℝ (P : ℂ → ℂ) z) := by
    filter_upwards [ae_conformal_post_biholomorphic f M hM hd] with z hz
    exact hz.2
  have hclass := weakQS_ae_conformal_affine_or_anti P hH hJ hP hPi hpconf
  rcases restriction_affine_or_anti (M*f) hInf hclass with hleft|hright
  · left
    have hh := biholomorphic.mul_mem (biholomorphic.inv_mem hM) hleft
    simpa only [← mul_assoc,inv_mul_cancel,one_mul] using hh
  · right
    have hm := reflection_conjugate_biholomorphic (biholomorphic.inv_mem hM)
    have hh := biholomorphic.mul_mem hm hright
    simp only [mul_assoc] at hh
    rw [← mul_assoc boundaryReflection boundaryReflection, boundaryReflection_sq, one_mul,
      ← mul_assoc M⁻¹ M, inv_mul_cancel, one_mul] at hh
    exact hh

end CannonMobius

end
end
noncomputable section
namespace CannonMobius
open Set Filter Topology MeasureTheory CannonMetricQC CannonConformal CannonQM CannonH3
open scoped OnePoint

variable {Γ : Type*} [Group Γ] [Countable Γ]

theorem sphere_action_straightening (A : Γ →* (Sphere ≃ₜ Sphere))
    {η : Distortion} (hA : ∀ g, Controlled (A g) η) :
    ∃ F : Sphere ≃ₜ Sphere, ∀ g : Γ,
      F*A g*F.symm ∈ biholomorphic ∨ boundaryReflection*(F*A g*F.symm) ∈ biholomorphic := by
  obtain ⟨q,hqm,hqb,hqi,C,hC,F,hF0,hF1,hF,hFi,hD⟩ := controlled_action_structure_integration A hA
  refine ⟨F.onePointCongr,fun g => ?_⟩
  have hcr := weakQS_sphere_boundedCrossRatios F hC hF
  have hcri : BoundedCrossRatios F.onePointCongr.symm := weakQS_sphere_boundedCrossRatios F.symm hC hFi
  have hB : BoundedCrossRatios (F.onePointCongr*A g*F.onePointCongr.symm) :=
    (hcr.comp (hA g).boundedCrossRatios (A g).injective).comp hcri F.onePointCongr.symm.injective
  have hBi : BoundedCrossRatios (F.onePointCongr*A g*F.onePointCongr.symm).symm :=
    (hcr.comp ((hA g).inverse (A g)).boundedCrossRatios (A g).symm.injective).comp
      hcri F.onePointCongr.symm.injective
  apply sphere_ae_conformal_rigidity _ hB hBi
  exact integrated_conjugate_ae_conformal (A g) (hA g) q ((hqi g).mono (fun _ h => h.2))
    F hF0 hC hF hFi hD

end CannonMobius

end
end
section
noncomputable section

section

open Set Topology

namespace CannonRelease

open Set Topology

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G)

variable (hthin : D.ThinTriangles)

local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open Set Topology

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) (hthin : D.ThinTriangles)

local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology Set

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology Set

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Set

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Set

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Set

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

end

end
end
end
end

end OAI
