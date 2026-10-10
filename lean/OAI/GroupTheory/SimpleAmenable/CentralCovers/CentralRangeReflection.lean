import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.NestedCutCalculus
import OAI.GroupTheory.SimpleAmenable.CentralCovers.AssignmentGeneration

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section CentralRangeReflection
open scoped commutatorElement

theorem perfect_range_le_of_central_image {G H Q : Type*} [Group G] [Group H]
    [Group Q] [Group.IsPerfect G] (f : G →* H) (q : H →* Q)
    (hc : q.ker ≤ Subgroup.center H) (K : Subgroup H)
    (himage : (q.comp f).range ≤ K.map q) : f.range ≤ K := by
  have he : f.range = ⁅f.range,f.range⁆ := by
    rw [← map_commutator_eq,Group.IsPerfect.commutator_eq_top,← MonoidHom.range_eq_map]
  rw [he]
  apply Subgroup.commutator_le.mpr
  intro x hx y hy
  obtain ⟨u,hu⟩ := hx
  obtain ⟨v,hv⟩ := hy
  obtain ⟨k,hk,hkx⟩ := Subgroup.mem_map.mp (himage ⟨u,by simpa using congrArg q hu⟩)
  obtain ⟨l,hl,hly⟩ := Subgroup.mem_map.mp (himage ⟨v,by simpa using congrArg q hv⟩)
  have hz : k⁻¹*x ∈ Subgroup.center H := hc (by
    change q (k⁻¹*x) = 1
    simp only [map_mul,map_inv,hkx,inv_mul_cancel])
  have hw : l⁻¹*y ∈ Subgroup.center H := hc (by
    change q (l⁻¹*y) = 1
    simp only [map_mul,map_inv,hly,inv_mul_cancel])
  have hz' (a : H) : ⁅k⁻¹*x,a⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr ((Subgroup.mem_center_iff.mp hz a).symm)
  have hw' (a : H) : ⁅a,l⁻¹*y⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hw a)
  have hxy : ⁅x,y⁆ = ⁅k,l⁆ := by
    have hex : x=k*(k⁻¹*x) := by simp
    have hey : y=l*(l⁻¹*y) := by simp
    conv_lhs => rw [hex,hey]
    rw [commutatorElement_mul_left_eq_conj_mul,hz']
    simp only [mul_one,mul_inv_cancel,one_mul]
    rw [commutatorElement_mul_right_eq_mul_conj,hw']
    simp only [mul_one,mul_inv_cancel_right]
  rw [hxy]
  exact K.mul_mem (K.mul_mem (K.mul_mem hk hl) (K.inv_mem hk)) (K.inv_mem hl)

end CentralRangeReflection

section FormalSectorSupport
variable {E E' H Ω ι : Type*} [Group E] [Group E'] [Group H]

def assignmentPost (ψ : E' →* E) : (Ω → E') →* (Ω → E) where
  toFun f ω := ψ (f ω)
  map_one' := by ext ω; exact map_one ψ
  map_mul' f g := by ext ω; exact map_mul ψ (f ω) (g ω)

theorem assignmentPost_mask (ψ : E' →* E) (U : Set Ω) (s : E') :
    assignmentPost ψ (sectorMask U s) = sectorMask U (ψ s) := by
  classical
  ext ω
  by_cases h : ω ∈ U <;> simp [assignmentPost,sectorMask,h]

theorem centralSector_supported [Group.IsPerfect E] [Group.IsPerfect E']
    [Finite Ω] [Finite ι] (φ : (Ω → E) →* H ⧸ Subgroup.center H)
    (U : ι → Set Ω) (hsep : ∀ ω ν, (∀ i, ω ∈ U i ↔ ν ∈ U i) → ω=ν)
    (ψ : E' →* E) (K : Subgroup H)
    (hwhole : ∀ s, φ (sectorMask Set.univ (ψ s)) ∈ K.map (QuotientGroup.mk' _))
    (hU : ∀ i s, φ (sectorMask (U i) (ψ s)) ∈ K.map (QuotientGroup.mk' _))
    (V : Set Ω) :
    ((centralSector φ V).comp (universalMap ψ)).range ≤ K := by
  let q := QuotientGroup.mk' (Subgroup.center H)
  let J := (K.map q).comap (φ.comp (assignmentPost ψ))
  have hJ : J=⊤ := assignment_group_generated U hsep J
    (fun s => by change φ (assignmentPost ψ (sectorMask Set.univ s)) ∈ K.map q
                 rw [assignmentPost_mask]; exact hwhole s)
    (fun i s => by change φ (assignmentPost ψ (sectorMask (U i) s)) ∈ K.map q
                   rw [assignmentPost_mask]; exact hU i s)
  apply perfect_range_le_of_central_image _ q (by rw [QuotientGroup.ker_mk']) K
  rintro y ⟨s,rfl⟩
  change q (centralSector φ V (universalMap ψ s)) ∈ K.map q
  rw [centralSector_spec]
  have hs := DFunLike.congr_fun (universalMap_spec ψ) s
  change universalProjection E (universalMap ψ s)=ψ (universalProjection E' s) at hs
  rw [hs,← assignmentPost_mask]
  have hmem : sectorMask V (universalProjection E' s) ∈ J := by rw [hJ]; trivial
  exact hmem

theorem centralSector_whole_eq [Group.IsPerfect E]
    (φ : (Ω → E) →* H ⧸ Subgroup.center H) (c : E →* H)
    (hc : φ.comp (sectorMask Set.univ)=(QuotientGroup.mk' _).comp c) :
    centralSector φ Set.univ=c.comp (universalProjection E) := by
  apply perfect_lift_unique (QuotientGroup.mk' (Subgroup.center H))
    (by rw [QuotientGroup.ker_mk'])
  ext s
  simp only [MonoidHom.comp_apply,centralSector_spec]
  exact DFunLike.congr_fun hc (universalProjection E s)

theorem centralSector_control [Group.IsPerfect E]
    (φ : (Ω → E) →* H ⧸ Subgroup.center H) {U V : Set Ω} (hUV : U ⊆ V) :
    SameActionOn (centralSector φ V) (centralSector φ Set.univ) (centralSector φ U).range := by
  intro s x hx
  obtain ⟨t,rfl⟩ := hx
  have hd : Disjoint V Vᶜ := disjoint_compl_right_iff.mpr le_rfl
  have he := centralSector_union φ hd s
  rw [Set.union_compl_self] at he
  rw [he]
  exact (conj_mul_of_commute _ _ _
    (centralSector_commute φ (disjoint_compl_left_iff.mpr hUV) s t)).symm

end FormalSectorSupport

end SimpleAmenable
end
end

end OAI
