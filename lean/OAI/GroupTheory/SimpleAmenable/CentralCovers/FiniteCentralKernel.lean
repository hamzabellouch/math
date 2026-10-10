import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PerfectCalculus

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FiniteCentralKernel

open scoped commutatorElement

variable {G H Q : Type*} [Group G] [Group H] [Group Q]

theorem subgroup_fg_map (f : G →* H) {K : Subgroup G} (hK : K.FG) : (K.map f).FG := by
  obtain ⟨S,hS,hSf⟩ := (Subgroup.fg_iff K).mp hK
  apply (Subgroup.fg_iff _).mpr
  exact ⟨f '' S, by rw [← MonoidHom.map_closure, hS], hSf.image f⟩

theorem group_fg_of_kernel_quotient (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker.FG) [Group.FG H] : Group.FG G := by
  classical
  obtain ⟨S,hS,hSf⟩ := Group.fg_iff.mp (inferInstance : Group.FG H)
  let a : H → G := fun y => (hf y).choose
  have ha (y : H) : f (a y) = y := (hf y).choose_spec
  let T := Subgroup.closure (a '' S)
  have hTf : T.FG := (Subgroup.fg_iff T).mpr ⟨a '' S,rfl,hSf.image a⟩
  have hm : T.map f = ⊤ := by
    change (Subgroup.closure (a '' S)).map f = ⊤
    rw [MonoidHom.map_closure,Set.image_image]
    have he : (fun y => f (a y)) = id := funext ha
    rw [he,Set.image_id,hS]
  have htop : T ⊔ f.ker = ⊤ := by
    apply (Subgroup.eq_top_iff' _).mpr
    intro x
    obtain ⟨y,hy,hyx⟩ := Subgroup.mem_map.mp (hm.symm ▸ Subgroup.mem_top (f x))
    have hd : y⁻¹*x ∈ f.ker := by
      change f (y⁻¹*x) = 1
      simp [hyx]
    have hh := (T ⊔ f.ker).mul_mem ((show T ≤ T ⊔ f.ker from le_sup_left) hy)
      ((show f.ker ≤ T ⊔ f.ker from le_sup_right) hd)
    simpa using hh
  exact Group.fg_def.mpr (htop ▸ hTf.sup hker)

theorem subgroup_fg_of_comm {A : Type*} [CommGroup A] [Group.FG A] (K : Subgroup A) : K.FG := by
  let : Module.Finite ℤ (Additive A) :=
    Module.Finite.iff_addGroup_fg.mpr (inferInstance : AddGroup.FG (Additive A))
  apply (Subgroup.fg_iff_add_fg K).mpr
  exact (Submodule.fg_iff_addSubgroup_fg (AddSubgroup.toIntSubmodule K.toAddSubgroup)).mp
    (IsNoetherian.noetherian _)

theorem perfect_lift_range [Group.IsPerfect G] (l : G →* H) (q : H →* Q)
    (hq : Function.Surjective (q.comp l)) (hc : q.ker ≤ Subgroup.center H) :
    l.range = commutator H := by
  apply le_antisymm
  · have he : l.range = ⁅l.range,l.range⁆ := by
      rw [← map_commutator_eq,Group.IsPerfect.commutator_eq_top,← MonoidHom.range_eq_map]
    rw [he,commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  · rw [commutator_def]
    apply Subgroup.commutator_le.mpr
    intro x _ y _
    obtain ⟨u,hu⟩ := hq (q x)
    obtain ⟨v,hv⟩ := hq (q y)
    change q (l u) = q x at hu
    change q (l v) = q y at hv
    have hx : (l u)⁻¹*x ∈ Subgroup.center H := hc (by
      change q ((l u)⁻¹*x) = 1
      simpa only [map_mul,map_inv,MonoidHom.comp_apply] using
        (show (q (l u))⁻¹*q x = 1 by rw [hu]; simp))
    have hy : (l v)⁻¹*y ∈ Subgroup.center H := hc (by
      change q ((l v)⁻¹*y) = 1
      simpa only [map_mul,map_inv,MonoidHom.comp_apply] using
        (show (q (l v))⁻¹*q y = 1 by rw [hv]; simp))
    have hex : x = l u*((l u)⁻¹*x) := by simp
    have hey : y = l v*((l v)⁻¹*y) := by simp
    have hz (a : H) : ⁅(l u)⁻¹*x,a⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr ((Subgroup.mem_center_iff.mp hx a).symm)
    have hw (a : H) : ⁅a,(l v)⁻¹*y⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hy a)
    have he : ⁅x,y⁆ = ⁅l u,l v⁆ := by
      conv_lhs => rw [hex,hey]
      rw [commutatorElement_mul_left_eq_conj_mul,hz]
      simp only [mul_one,mul_inv_cancel,one_mul]
      rw [commutatorElement_mul_right_eq_mul_conj,hw]
      simp only [mul_one,mul_inv_cancel_right]
    rw [he]
    exact ⟨⁅u,v⁆,map_commutatorElement l u v⟩

theorem central_kernel_fg_of_universal [Group.IsPerfect Q] [Group.FG H]
    [Group.FG (universalProjection Q).ker] (q : H →* Q)
    (hq : Function.Surjective q) (hc : q.ker ≤ Subgroup.center H) : Group.FG q.ker := by
  let l := universalLift q hq hc (MonoidHom.id Q)
  have hl : q.comp l = universalProjection Q := by
    simpa only [l,MonoidHom.id_comp] using universalLift_spec q hq hc (MonoidHom.id Q)
  have hls : Function.Surjective (q.comp l) := hl ▸ universalProjection_surjective Q
  have hr : l.range = commutator H := perfect_lift_range l q hls hc
  let f : q.ker →* Abelianization H := Abelianization.of.comp q.ker.subtype
  let t : (universalProjection Q).ker →* f.ker :=
    { toFun := fun u => ⟨⟨l u.val, by
        change q (l u.val) = 1
        rw [← MonoidHom.comp_apply,hl]
        exact u.property⟩, by
        change Abelianization.of (l u.val) = 1
        apply MonoidHom.mem_ker.mp
        rw [Abelianization.ker_of]
        exact hr ▸ (show l u.val ∈ l.range from ⟨u.val,rfl⟩)⟩
      map_one' := by apply Subtype.ext; apply Subtype.ext; exact map_one l
      map_mul' := by intro u v; apply Subtype.ext; apply Subtype.ext; exact map_mul l u.val v.val }
  have ht : Function.Surjective t := by
    intro x
    have hx : x.val.val ∈ commutator H := by
      rw [← Abelianization.ker_of]
      exact x.property
    obtain ⟨u,hu⟩ := hr.symm ▸ hx
    have hup : u ∈ (universalProjection Q).ker := by
      change universalProjection Q u = 1
      rw [← hl]
      change q (l u) = 1
      rw [hu]
      exact x.val.property
    refine ⟨⟨u,hup⟩,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hu
  have : Group.FG f.ker := Group.fg_of_surjective ht
  have : Group.FG (Abelianization H) := by
    change Group.FG (H ⧸ commutator H)
    infer_instance
  have : Group.FG f.range := (Group.fg_iff_subgroup_fg _).mpr (subgroup_fg_of_comm f.range)
  apply group_fg_of_kernel_quotient f.rangeRestrict f.rangeRestrict_surjective
  rw [MonoidHom.ker_rangeRestrict]
  exact (Group.fg_iff_subgroup_fg _).mp inferInstance

theorem finitelyPresented_of_central_cover [Group.IsPerfect Q] [Group.IsFinitelyPresented H]
    [Group.FG (universalProjection Q).ker] (q : H →* Q)
    (hq : Function.Surjective q) (hc : q.ker ≤ Subgroup.center H) : Group.IsFinitelyPresented Q := by
  have : Group.FG H := by
    obtain ⟨n,p,hp,_⟩ := (inferInstance : Group.IsFinitelyPresented H).out
    exact Group.fg_of_surjective hp
  have := central_kernel_fg_of_universal q hq hc
  exact Group.IsFinitelyPresented.of_surjective q hq (Subgroup.IsFinitelyNormallyGenerated.of_FG _)

end FiniteCentralKernel

end SimpleAmenable
end
end

end OAI
