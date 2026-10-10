import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.ClosedInsideSegment
import OAI.Geometry.Cannon.PlaneTopology.Crossing
import OAI.Geometry.Cannon.PlaneTopology.CompactifiedFace
import OAI.Geometry.Cannon.Conformal.Sphere
import OAI.Geometry.Cannon.Modulus.ClosedCoverReflTrans

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology CannonFaceIncidence CannonTriangleWinding
open scoped OnePoint

attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : ι → Arc ℂ} [Fintype (Faces F)] {out : Faces F}

def sphereTile (F : ι → Arc ℂ) (z : ℂ → ℂ) (out d : Faces F) : Set (OnePoint ℂ) :=
  if d=out then ((↑) '' interior (faceHull F z out))ᶜ else (↑) '' faceHull F z d

omit [DecidableEq ι] [Nonempty ι] [Fintype (Faces F)] in
lemma sphereTile_closed (z : ℂ → ℂ) (out d : Faces F) : IsClosed (sphereTile F z out d) := by
  classical
  unfold sphereTile
  split_ifs
  · exact (OnePoint.isOpenMap_coe _ isOpen_interior).isClosed_compl
  · exact ((((faceVertices F d).finite_toSet.image z).isCompact_convexHull ℝ).image OnePoint.continuous_coe).isClosed

omit [DecidableEq ι] [Nonempty ι] [Fintype (Faces F)] in
lemma sphereTile_cover (z : ℂ → ℂ)
    (hfill : (⋃ d : {d : Faces F // d≠out},faceHull F z d.val)=faceHull F z out) :
    ∀ p : OnePoint ℂ,∃ d : Faces F,p∈sphereTile F z out d := by
  classical
  intro p
  by_cases hp : p∈((↑) '' interior (faceHull F z out):Set (OnePoint ℂ))
  · obtain ⟨q,hq,rfl⟩:=hp
    have hq':=interior_subset hq
    rw [←hfill] at hq'
    obtain ⟨d,hd⟩:=mem_iUnion.mp hq'
    exact ⟨d.val,by simp only [sphereTile,ite_eq_right d.property]; exact ⟨q,hd,rfl⟩⟩
  · exact ⟨out,by simpa [sphereTile] using hp⟩

omit [DecidableEq ι] [Nonempty ι] [Fintype (Faces F)] in
theorem sphereTile_inter_common_vertex (z : ℂ → ℂ) (ρ : ℂ → ℝ) (hρ : ∀ v,0<ρ v)
    (hlen : ∀ i,dist (z (F i 0)) (z (F i 1))=ρ (F i 0)+ρ (F i 1))
    (hdis : ∀ u,Vertex F u → ∀ v,Vertex F v → u≠v → ρ u+ρ v≤dist (z u) (z v))
    (hcycles : ∀ d : Faces F,∃ C : FacialCycle F d,0<area (z C.a) (z C.b) (z C.c))
    (hI : ∀ d e : Faces F,d≠out → e≠out → d≠e →
      Disjoint (interior (faceHull F z d)) (interior (faceHull F z e)))
    (hfill : (⋃ d : {d : Faces F // d≠out},faceHull F z d.val)=faceHull F z out)
    (d e : Faces F) (hmeet : (sphereTile F z out d∩sphereTile F z out e).Nonempty) :
    ∃ v,v∈faceVertices F d ∧ v∈faceVertices F e := by
  classical
  by_cases hde : d=e
  · subst e
    obtain ⟨C,hC⟩:=hcycles d
    exact ⟨C.a,C.mem_a,C.mem_a⟩
  have outer (d : Faces F) (hd : d≠out)
      (hm : (sphereTile F z out d∩sphereTile F z out out).Nonempty) :
      ∃ v,v∈faceVertices F d ∧ v∈faceVertices F out := by
    obtain ⟨p,hpd,hpo⟩:=hm
    simp only [sphereTile,ite_eq_right hd] at hpd
    obtain ⟨q,hq,rfl⟩:=hpd
    simp only [sphereTile] at hpo
    have hqo : q∉interior (faceHull F z out) := by
      intro h
      apply hpo
      exact ⟨q,h,rfl⟩
    have hsub : faceHull F z d⊆faceHull F z out := by
      rw [←hfill]
      exact subset_iUnion (fun d : {d : Faces F // d≠out}=>faceHull F z d.val) ⟨d,hd⟩
    obtain ⟨C,hC⟩:=hcycles d
    obtain ⟨O,hO⟩:=hcycles out
    apply C.common_vertex_of_frontier_inter O z ρ hρ hlen hdis hC hO
    refine ⟨q,⟨subset_closure hq,fun hi=>hqo (interior_mono hsub hi)⟩,
      subset_closure (hsub hq),hqo⟩
  by_cases hd : d=out
  · subst d
    obtain ⟨v,hve,hvo⟩:=outer e (Ne.symm hde) (by simpa only [inter_comm] using hmeet)
    exact ⟨v,hvo,hve⟩
  by_cases he : e=out
  · subst e
    exact outer d hd hmeet
  obtain ⟨C,hC⟩:=hcycles d
  obtain ⟨E,hE⟩:=hcycles e
  apply C.common_vertex_of_hull_inter E z ρ hρ hlen hdis hC hE (hI d e hd he hde)
  obtain ⟨p,hpd,hpe⟩:=hmeet
  simp only [sphereTile,ite_eq_right hd,ite_eq_right he] at hpd hpe
  obtain ⟨q,hq,rfl⟩:=hpd
  obtain ⟨w,hw,hew⟩:=hpe
  have hew' : w=q:=OnePoint.coe_injective hew
  subst w
  exact ⟨q,hq,hw⟩

variable {X : Type*} [TopologicalSpace X] [T2Space X]
omit [DecidableEq ι] [Nonempty ι] [Fintype (Faces F)] [T2Space X] in
lemma compactifiedFace_vertex (e : ℂ → X) (he : Continuous e)
    {d : Faces F} {v : ℂ} (hv : v∈faceVertices F d) : e v∈compactifiedFace F e d :=
  image_closure_subset_closure_image he ⟨v,((mem_faceVertices F d v).mp hv).2,rfl⟩

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype (Faces F)] [T2Space X] in
lemma compactifiedFace_preconnected (e : ℂ → X) (he : Continuous e) (d : Faces F) :
    IsPreconnected (compactifiedFace F e d) :=
  ((component_region_connected _ d).isPreconnected.image e he.continuousOn).closure

omit [DecidableEq ι] [Nonempty ι] [T2Space X] in
theorem sphere_carrier_preconnected (e : ℂ → X) (he : Continuous e)
    (z : ℂ → ℂ) (ρ : ℂ → ℝ) (hρ : ∀ v,0<ρ v)
    (hlen : ∀ i,dist (z (F i 0)) (z (F i 1))=ρ (F i 0)+ρ (F i 1))
    (hdis : ∀ u,Vertex F u → ∀ v,Vertex F v → u≠v → ρ u+ρ v≤dist (z u) (z v))
    (hcycles : ∀ d : Faces F,∃ C : FacialCycle F d,0<area (z C.a) (z C.b) (z C.c))
    (hI : ∀ d e : Faces F,d≠out → e≠out → d≠e →
      Disjoint (interior (faceHull F z d)) (interior (faceHull F z e)))
    (hfill : (⋃ d : {d : Faces F // d≠out},faceHull F z d.val)=faceHull F z out)
    (S : Set (OnePoint ℂ)) (hS : IsPreconnected S) :
    IsPreconnected (⋃ (d : {d : Faces F // (S∩sphereTile F z out d).Nonempty}),
      compactifiedFace F e d.val) := by
  apply CannonFiniteCarrier.connected_carrier _ _ (compactifiedFace_preconnected e he)
    (sphereTile_closed z out) S hS
  · intro y hy
    exact mem_iUnion.mpr (sphereTile_cover z hfill y)
  · intro d k hdk
    obtain ⟨v,hvd,hvk⟩:=sphereTile_inter_common_vertex z ρ hρ hlen hdis hcycles hI hfill d k
      (by obtain ⟨x,⟨_,hx⟩,hk⟩:=hdk; exact ⟨x,hx,hk⟩)
    exact ⟨e v,compactifiedFace_vertex e he hvd,compactifiedFace_vertex e he hvk⟩

omit [DecidableEq ι] [Nonempty ι] [Fintype (Faces F)] in
theorem sphere_realization_fiber_bound {X : Type*} [PseudoMetricSpace X]
    (e : ℂ → X) (he : Continuous e) (f : X → OnePoint ℂ)
    (hcover : ∀ x,∃ d : Faces F,x∈compactifiedFace F e d)
    (z : ℂ → ℂ) (ρ : ℂ → ℝ) (hρ : ∀ v,0<ρ v)
    (hlen : ∀ i,dist (z (F i 0)) (z (F i 1))=ρ (F i 0)+ρ (F i 1))
    (hdis : ∀ u,Vertex F u → ∀ v,Vertex F v → u≠v → ρ u+ρ v≤dist (z u) (z v))
    (hcycles : ∀ d : Faces F,∃ C : FacialCycle F d,0<area (z C.a) (z C.b) (z C.c))
    (hI : ∀ d e : Faces F,d≠out → e≠out → d≠e →
      Disjoint (interior (faceHull F z d)) (interior (faceHull F z e)))
    (hfill : (⋃ d : {d : Faces F // d≠out},faceHull F z d.val)=faceHull F z out)
    (hf : ∀ d,MapsTo f (compactifiedFace F e d) (sphereTile F z out d))
    (R : ℝ) (hR : ∀ d,∀ x∈compactifiedFace F e d,∀ y∈compactifiedFace F e d,dist x y≤R)
    (x y : X) (hxy : f x=f y) : dist x y≤2*R := by
  obtain ⟨d,hd⟩:=hcover x
  obtain ⟨k,hk⟩:=hcover y
  obtain ⟨v,hvd,hvk⟩:=sphereTile_inter_common_vertex z ρ hρ hlen hdis hcycles hI hfill d k
    ⟨f x,hf d hd,hxy.symm ▸ hf k hk⟩
  have hvd' := image_closure_subset_closure_image he ⟨v,((mem_faceVertices F d v).mp hvd).2,rfl⟩
  have hvk' := image_closure_subset_closure_image he ⟨v,((mem_faceVertices F k v).mp hvk).2,rfl⟩
  calc dist x y ≤ dist x (e v)+dist (e v) y := dist_triangle _ _ _
       _ ≤ R+R := add_le_add (hR d x hd (e v) hvd') (hR k (e v) hvk' y hk)
       _ = 2*R := by ring
end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonMobius
open Set Topology
open scoped OnePoint

@[simp] lemma inv_inv_apply (p : Sphere) : inv (inv p)=p := inv_involutive p

lemma inv_scalar_differentiable :
    DifferentiableOn ℂ (fun z : ℂ => coordinate (inv (z:Sphere))) {z | inv (z:Sphere) ≠ ∞} := by
  intro z hz
  have hn : z ≠ 0 := by intro hh; subst z; exact hz inv_zero
  simpa only [coordinate_inv_coe] using (differentiableAt_inv hn).differentiableWithinAt

lemma isAnalytic_one : IsAnalytic 1 := by
  intro s t
  cases s <;> cases t
  · change DifferentiableOn ℂ (fun z : ℂ => z) _
    exact differentiable_id.differentiableOn
  · exact inv_scalar_differentiable
  · exact inv_scalar_differentiable
  · change DifferentiableOn ℂ (fun z : ℂ => coordinate (inv (inv (z:Sphere)))) _
    simp_rw [inv_inv_apply,coordinate_coe]
    exact differentiable_id.differentiableOn

lemma isAnalytic_inversion : IsAnalytic inversion := by
  intro s t
  cases s <;> cases t
  · exact inv_scalar_differentiable
  · change DifferentiableOn ℂ (fun z : ℂ => coordinate (inv (inv (z:Sphere)))) _
    simp_rw [inv_inv_apply,coordinate_coe]
    exact differentiable_id.differentiableOn
  · change DifferentiableOn ℂ (fun z : ℂ => coordinate (inv (inv (z:Sphere)))) _
    simp_rw [inv_inv_apply,coordinate_coe]
    exact differentiable_id.differentiableOn
  · change DifferentiableOn ℂ (fun z : ℂ => coordinate (inv (inv (inv (z:Sphere)))))
      {z | inv (inv (inv (z:Sphere))) ≠ ∞}
    simpa only [inv_inv_apply] using inv_scalar_differentiable

def affinePlane (a b : ℂ) (ha : a ≠ 0) : ℂ ≃ₜ ℂ where
  toFun z := a*z+b
  invFun z := (z-b)/a
  left_inv z := by simp [ha]
  right_inv z := by field_simp; ring
  continuous_toFun := (continuous_const.mul continuous_id).add continuous_const
  continuous_invFun := (continuous_id.sub continuous_const).div_const a

def affine (a b : ℂ) (ha : a ≠ 0) : Sphere ≃ₜ Sphere := (affinePlane a b ha).onePointCongr
@[simp] lemma affine_infty (a b : ℂ) (ha : a ≠ 0) : affine a b ha ∞=∞ := rfl
@[simp] lemma affine_coe (a b : ℂ) (ha : a ≠ 0) (z : ℂ) :
    affine a b ha (z:Sphere)=(a*z+b:ℂ) := rfl

lemma affine_symm (a b : ℂ) (ha : a ≠ 0) :
    (affine a b ha).symm=affine a⁻¹ (-b/a) (inv_ne_zero ha) := by
  apply Homeomorph.ext
  intro p
  induction p using OnePoint.rec with
  | infty => rfl
  | coe z =>
    change (((z-b)/a:ℂ):Sphere)=((a⁻¹*z+(-b/a):ℂ):Sphere)
    congr 1
    ring

lemma inChart_affine_tt (a b : ℂ) (ha : a ≠ 0) (z : ℂ) :
    inChart true true (affine a b ha) z=z/(a+b*z) := by
  change coordinate (inv (affine a b ha (inv (z:Sphere))))=_
  by_cases hz : z=0
  · subst z
    rw [inv_zero,affine_infty,inv_infty,coordinate_coe]
    simp
  · rw [inv_coe hz,affine_coe,coordinate_inv_coe]
    have he : a*z⁻¹+b=(a+b*z)/z := by field_simp
    rw [he,inv_div]

lemma isAnalytic_affine (a b : ℂ) (ha : a ≠ 0) : IsAnalytic (affine a b ha) := by
  intro s t
  cases s <;> cases t
  · change DifferentiableOn ℂ (fun z : ℂ => a*z+b) _
    exact ((differentiable_const a).mul differentiable_id |>.add_const b).differentiableOn
  · intro z hz
    change inv ((a*z+b:ℂ):Sphere) ≠ ∞ at hz
    have hn : a*z+b ≠ 0 := by
      intro hh
      rw [hh,inv_zero] at hz
      exact hz rfl
    change DifferentiableWithinAt ℂ (fun z : ℂ => coordinate (inv ((a*z+b:ℂ):Sphere))) _ z
    simp_rw [coordinate_inv_coe]
    exact (((differentiable_const a).mul differentiable_id |>.add_const b) z).inv hn |>.differentiableWithinAt
  · intro z hz
    have hn : z ≠ 0 := by
      intro hh
      subst z
      change affine a b ha (inv ((0:ℂ):Sphere)) ≠ ∞ at hz
      rw [inv_zero,affine_infty] at hz
      exact hz rfl
    have hd : DifferentiableAt ℂ (fun z : ℂ => a*z⁻¹+b) z :=
      ((differentiableAt_const a).mul (differentiableAt_inv hn)).add_const b
    apply (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [eventually_ne_nhds hn] with w hw
    change coordinate (affine a b ha (inv (w:Sphere)))=a*w⁻¹+b
    rw [inv_coe hw,affine_coe,coordinate_coe]
  · intro z hz
    have hn : a+b*z ≠ 0 := by
      intro hh
      by_cases hz0 : z=0
      · exact ha (by simpa [hz0] using hh)
      · have he : a*z⁻¹+b=0 := by
          have he' : a*z⁻¹+b=(a+b*z)/z := by field_simp
          rw [he',hh,zero_div]
        change inv (affine a b ha (inv (z:Sphere))) ≠ ∞ at hz
        rw [inv_coe hz0,affine_coe,he,inv_zero] at hz
        exact hz rfl
    have hd : DifferentiableAt ℂ (fun z : ℂ => z/(a+b*z)) z :=
      differentiableAt_id.div ((differentiableAt_const a).add
        ((differentiableAt_const b).mul differentiableAt_id)) hn
    rw [show inChart true true (affine a b ha)=(fun z : ℂ => z/(a+b*z)) from funext (inChart_affine_tt a b ha)]
    exact hd.differentiableWithinAt

def biholomorphic : Subgroup (Sphere ≃ₜ Sphere) where
  carrier := {f | IsAnalytic f ∧ IsAnalytic f.symm}
  one_mem' := ⟨isAnalytic_one,isAnalytic_one⟩
  mul_mem' := by
    intro f g hf hg
    exact ⟨isAnalytic_mul hf.1 hg.1,isAnalytic_mul hg.2 hf.2⟩
  inv_mem' := by intro f hf; exact ⟨hf.2,hf.1⟩

lemma affine_biholomorphic (a b : ℂ) (ha : a ≠ 0) : affine a b ha ∈ biholomorphic := by
  refine ⟨isAnalytic_affine a b ha,?_⟩
  rw [affine_symm]
  exact isAnalytic_affine _ _ _

lemma inversion_biholomorphic : inversion ∈ biholomorphic :=
  ⟨isAnalytic_inversion,isAnalytic_inversion⟩
end CannonMobius

namespace CannonMobius
open Set Filter Topology
open scoped OnePoint

def std (i : Fin 3) : Sphere := ![∞,((0:ℂ):Sphere),((1:ℂ):Sphere)] i
lemma std_injective : Function.Injective std := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [std]

abbrev Triple := {t : Fin 3 → Sphere // Function.Injective t}
def standard : Triple := ⟨std,std_injective⟩
def tripleMap (f : Sphere ≃ₜ Sphere) (t : Triple) : Triple := ⟨f ∘ t.val,f.injective.comp t.property⟩
lemma continuous_tripleMap (f : Sphere ≃ₜ Sphere) : Continuous (tripleMap f) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact f.continuous.comp ((continuous_apply i).comp continuous_subtype_val)
def tripleHomeomorph (f : Sphere ≃ₜ Sphere) : Triple ≃ₜ Triple where
  toFun := tripleMap f
  invFun := tripleMap f.symm
  left_inv t := by apply Subtype.ext; funext i; exact f.symm_apply_apply _
  right_inv t := by apply Subtype.ext; funext i; exact f.apply_symm_apply _
  continuous_toFun := continuous_tripleMap f
  continuous_invFun := continuous_tripleMap f.symm
@[simp] lemma tripleMap_mul (f g : Sphere ≃ₜ Sphere) (t : Triple) :
    tripleMap (f*g) t=tripleMap f (tripleMap g t) := rfl

lemma exists_finite_normalizer (t : Triple) (ht : ∀ i, t.val i ≠ ∞) :
    ∃ f : Sphere ≃ₜ Sphere, f ∈ biholomorphic ∧ tripleMap f standard=t := by
  let p : Fin 3 → ℂ := fun i => coordinate (t.val i)
  have hp (i : Fin 3) : (p i:Sphere)=t.val i := coe_coordinate (ht i)
  have hinj : Function.Injective p := by
    intro i j h
    apply t.property
    rw [← hp i,← hp j,h]
  have h10 : p 1-p 0 ≠ 0 := sub_ne_zero.mpr (fun h => (by decide : (1:Fin 3) ≠ 0) (hinj h))
  have h20 : p 2-p 0 ≠ 0 := sub_ne_zero.mpr (fun h => (by decide : (2:Fin 3) ≠ 0) (hinj h))
  let b := (p 1-p 0)⁻¹
  let a := (p 2-p 0)⁻¹-b
  have ha : a ≠ 0 := by
    intro h
    have he : (p 2-p 0)⁻¹=(p 1-p 0)⁻¹ := sub_eq_zero.mp h
    have he' := inv_injective he
    exact (by decide : (2:Fin 3) ≠ 1) (hinj (sub_left_injective he'))
  refine ⟨affine 1 (p 0) one_ne_zero*inversion*affine a b ha,
    biholomorphic.mul_mem (biholomorphic.mul_mem (affine_biholomorphic _ _ _) inversion_biholomorphic)
      (affine_biholomorphic _ _ _),?_⟩
  apply Subtype.ext
  funext i
  fin_cases i
  · change affine 1 (p 0) one_ne_zero (inv ∞)=t.val 0
    rw [inv_infty,affine_coe]
    simpa using hp 0
  · change affine 1 (p 0) one_ne_zero (inv (affine a b ha (0:ℂ)))=t.val 1
    rw [affine_coe]
    simp only [mul_zero,zero_add]
    rw [inv_coe (inv_ne_zero h10),affine_coe]
    simpa [b] using hp 1
  · change affine 1 (p 0) one_ne_zero (inv (affine a b ha (1:ℂ)))=t.val 2
    rw [affine_coe]
    have he : a*1+b=(p 2-p 0)⁻¹ := by dsimp [a]; ring
    rw [he,inv_coe (inv_ne_zero h20),affine_coe]
    simpa using hp 2

lemma exists_pole_avoiding (t : Triple) : ∃ p : ℂ, ∀ i, t.val i ≠ (p:Sphere) := by
  obtain ⟨p,hp⟩ := (Set.finite_range (fun i : Fin 3 => coordinate (t.val i))).exists_notMem
  refine ⟨p,?_⟩
  intro i hi
  apply hp
  refine ⟨i,?_⟩
  change coordinate (t.val i)=p
  rw [hi,coordinate_coe]

lemma exists_triple_normalizer (t : Triple) :
    ∃ f : Sphere ≃ₜ Sphere, f ∈ biholomorphic ∧ tripleMap f standard=t := by
  obtain ⟨p,hp⟩ := exists_pole_avoiding t
  let N : Sphere ≃ₜ Sphere := inversion*affine 1 (-p) one_ne_zero
  have hN : N ∈ biholomorphic := biholomorphic.mul_mem inversion_biholomorphic
    (affine_biholomorphic _ _ _)
  have hNp : N (p:Sphere)=∞ := by
    change inv (affine 1 (-p) one_ne_zero p)=∞
    rw [affine_coe]
    simp only [one_mul,add_neg_cancel,inv_zero]
  have hfin (i : Fin 3) : (tripleMap N t).val i ≠ ∞ :=
    fun he => hp i (N.injective (he.trans hNp.symm))
  obtain ⟨f,hf,he⟩ := exists_finite_normalizer (tripleMap N t) hfin
  refine ⟨N⁻¹*f,biholomorphic.mul_mem (biholomorphic.inv_mem hN) hf,?_⟩
  rw [tripleMap_mul,he]
  apply Subtype.ext
  funext i
  exact N.symm_apply_apply _

end CannonMobius

end
end
section
noncomputable section
namespace CannonMobius
open Set Metric Topology
open scoped OnePoint

lemma sphere_locallyPathConnected : LocallyPathConnectedSpace Sphere := by
  let f : ℂ ⊕ ℂ → Sphere := Sum.elim ((↑):ℂ → Sphere) (inversion ∘ ((↑):ℂ → Sphere))
  have hc : Continuous f := OnePoint.continuous_coe.sumElim
    (inversion.continuous.comp OnePoint.continuous_coe)
  have ho : IsOpenMap f := OnePoint.isOpenMap_coe.sumElim
    (inversion.isOpenMap.comp OnePoint.isOpenMap_coe)
  have hs : Function.Surjective f := by
    intro p
    induction p using OnePoint.rec with
    | infty => exact ⟨Sum.inr 0,inv_zero⟩
    | coe z => exact ⟨Sum.inl z,rfl⟩
  exact (ho.isQuotientMap hc hs).locallyPathConnectedSpace

theorem normalize_finite_realization {X : Type*} [PseudoMetricSpace X]
    (f : C(X,Sphere)) (hf : Function.Surjective f) (R : ℝ)
    (hsmall : ∀ x y,f x=f y → dist x y≤R)
    (a : Fin 3 → X) (ha : ∀ i j,i≠j → R<dist (a i) (a j)) :
    ∃ N : Sphere ≃ₜ Sphere,N∈biholomorphic ∧
      ∃ g : C(X,Sphere),(∀ x,g x=N (f x)) ∧ Function.Surjective g ∧
        (∀ i,g (a i)=std i) ∧ (∀ x y,g x=g y → dist x y≤R) := by
  have hinj : Function.Injective (fun i=>f (a i)) := by
    intro i j hij
    by_contra hn
    exact (not_le_of_gt (ha i j hn)) (hsmall _ _ hij)
  let t : Triple := ⟨fun i=>f (a i),hinj⟩
  obtain ⟨M,hM,hMt⟩ := exists_triple_normalizer t
  let g : C(X,Sphere) := ⟨M.symm ∘ f,M.symm.continuous.comp f.continuous⟩
  refine ⟨M.symm,biholomorphic.inv_mem hM,g,(fun _=>rfl),M.symm.surjective.comp hf,?_,?_⟩
  · intro i
    have H : M (std i)=f (a i) := congrArg (fun t : Triple=>t.val i) hMt
    change M.symm (f (a i))=std i
    rw [←H,M.symm_apply_apply]
  · intro x y hxy
    exact hsmall x y (M.symm.injective hxy)

theorem normalized_carrier {X ι : Type*} [TopologicalSpace X]
    (A : ι → Set X) (K : ι → Set Sphere)
    (hc : ∀ S : Set Sphere,IsPreconnected S →
      IsPreconnected (⋃ (i : {i : ι // (S∩K i).Nonempty}),A i.val))
    (N : Sphere ≃ₜ Sphere) (S : Set Sphere) (hS : IsPreconnected S) :
    IsPreconnected (⋃ (i : {i : ι // (S∩N '' K i).Nonempty}),A i.val) := by
  have he (i : ι) : (S∩N '' K i).Nonempty ↔ (N ⁻¹' S∩K i).Nonempty := by
    constructor
    · rintro ⟨_,hs,⟨x,hx,rfl⟩⟩
      exact ⟨x,hs,hx⟩
    · rintro ⟨x,hx,hk⟩
      exact ⟨N x,hx,⟨x,hk,rfl⟩⟩
  have hpre : IsPreconnected (N ⁻¹' S) := by
    rw [←Homeomorph.image_symm]
    exact hS.image N.symm N.symm.continuous.continuousOn
  have hu : (⋃ (i : {i : ι // (S∩N '' K i).Nonempty}),A i.val)=
      (⋃ (i : {i : ι // (N ⁻¹' S∩K i).Nonempty}),A i.val) := by
    ext x
    simp only [mem_iUnion,Subtype.exists]
    constructor <;> rintro ⟨i,hi,hx⟩
    · exact ⟨i,(he i).mp hi,hx⟩
    · exact ⟨i,(he i).mpr hi,hx⟩
  rw [hu]
  exact hc _ hpre
end CannonMobius

end
end
end
end

end OAI
