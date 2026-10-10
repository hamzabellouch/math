import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.AssignmentGeneration
import OAI.GroupTheory.SimpleAmenable.CentralCovers.AlphabetAlignedGeneration

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ConditionalFamilyLaws

variable {ι E H Ω : Type*} [Group E] [Group H]

noncomputable def copyFamilyEval (F : ι → E →* H) : FreeGroup (ι × E) →* H :=
  FreeGroup.lift (fun p => F p.1 p.2)

@[simp] theorem copyFamilyEval_of (F : ι → E →* H) (i : ι) (x : E) :
    copyFamilyEval F (FreeGroup.of (i,x)) = F i x := FreeGroup.lift_apply_of

theorem copyFamilyEval_range (F : ι → E →* H) :
    (copyFamilyEval F).range = ⨆ i, (F i).range := by
  rw [copyFamilyEval,FreeGroup.range_lift_eq_closure]
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨⟨i,x⟩,rfl⟩
    exact (le_iSup (fun i => (F i).range) i) ⟨x,rfl⟩
  · apply iSup_le
    intro i x hx
    obtain ⟨x,rfl⟩ := hx
    exact Subgroup.subset_closure ⟨(i,x),rfl⟩

theorem copyFamilyEval_perfect [Group.IsPerfect E] (F : ι → E →* H) :
    Group.IsPerfect (copyFamilyEval F).range := by
  rw [copyFamilyEval_range]
  let (i : ι) : Group.IsPerfect (F i).range := Group.IsPerfect.range (F i)
  exact perfect_iSup (fun i => (F i).range)

noncomputable def maskFamily (U : ι → Set Ω) : Option ι → E →* (Ω → E)
  | none => sectorMask Set.univ
  | some i => sectorMask (U i)

noncomputable def assignmentEval (U : ι → Set Ω) :
    FreeGroup (Option ι × E) →* (Ω → E) := copyFamilyEval (maskFamily U)

theorem assignmentEval_surjective [Group.IsPerfect E] [Finite ι] [Finite Ω]
    (U : ι → Set Ω) (hsep : ∀ ω ν, (∀ i, ω ∈ U i ↔ ν ∈ U i) → ω = ν) :
    Function.Surjective (assignmentEval (E := E) U) := by
  apply MonoidHom.range_eq_top.mp
  apply assignment_group_generated U hsep
  · intro s
    exact ⟨FreeGroup.of (none,s),copyFamilyEval_of _ _ _⟩
  · intro i s
    exact ⟨FreeGroup.of (some i,s),copyFamilyEval_of _ _ _⟩

def CopyFamilyLaw (U : ι → Set Ω) (F : Option ι → E →* H) : Prop :=
  HasCentralLaw (assignmentEval U) (copyFamilyEval F).rangeRestrict

theorem copyFamilyLaw_iff (U : ι → Set Ω) (F : Option ι → E →* H) :
    CopyFamilyLaw U F ↔ ∀ w, assignmentEval U w = 1 →
      ∀ i x, Commute (copyFamilyEval F w) (F i x) := by
  rw [CopyFamilyLaw,hasCentralLaw_iff]
  constructor
  · intro h w hw i x
    have ht := Subgroup.mem_center_iff.mp (h w hw)
      ⟨F i x,⟨FreeGroup.of (i,x),copyFamilyEval_of _ _ _⟩⟩
    exact (show Commute (F i x) (copyFamilyEval F w) from
      congrArg Subtype.val ht).symm
  · intro h w hw
    apply Subgroup.mem_center_iff.mpr
    intro x
    apply Subtype.ext
    have hx : x.val ∈ Subgroup.centralizer {copyFamilyEval F w} := by
      have hc : (copyFamilyEval F).range ≤ Subgroup.centralizer {copyFamilyEval F w} := by
        rw [copyFamilyEval_range]
        apply iSup_le
        rintro i y ⟨s,rfl⟩
        exact Subgroup.mem_centralizer_singleton_iff.mpr (h w hw i s).symm.eq
      exact hc x.property
    exact Subgroup.mem_centralizer_singleton_iff.mp hx

theorem copyFamilyLaw_of_table (U : ι → Set Ω) (F : Option ι → E →* H)
    (ρ : (Ω → E) →* H) (hρ : ∀ i, ρ.comp (maskFamily U i) = F i) :
    CopyFamilyLaw U F := by
  have he : ρ.comp (assignmentEval U) = copyFamilyEval F := by
    apply FreeGroup.ext_hom
    rintro ⟨i,s⟩
    simpa only [MonoidHom.comp_apply,assignmentEval,copyFamilyEval_of] using
      DFunLike.congr_fun (hρ i) s
  rw [copyFamilyLaw_iff]
  intro w hw i s
  have hf : copyFamilyEval F w = 1 := by
    rw [← DFunLike.congr_fun he w,MonoidHom.comp_apply,hw,map_one]
  rw [hf]
  exact Commute.one_left _

end ConditionalFamilyLaws

section ActualFamilyLaws

variable {ι E H Q : Type*} [Group E] [Group H] [Group Q]

def CentralOn (q : H →* Q) (S : Subgroup H) : Prop :=
  (q.comp S.subtype).ker ≤ Subgroup.center S

theorem centralOn_iff (q : H →* Q) (S : Subgroup H) :
    CentralOn q S ↔ ∀ x ∈ S, q x = 1 → ∀ y ∈ S, Commute x y := by
  constructor
  · intro h x hx hqx y hy
    exact (show Commute y x from congrArg Subtype.val
      (Subgroup.mem_center_iff.mp (h (show ⟨x,hx⟩ ∈ (q.comp S.subtype).ker from hqx))
        ⟨y,hy⟩)).symm
  · intro h x hx
    apply Subgroup.mem_center_iff.mpr
    intro y
    exact Subtype.ext (h x.val x.property hx y.val y.property).symm.eq

theorem CentralOn.mono {q : H →* Q} {S T : Subgroup H}
    (h : CentralOn q T) (hst : S ≤ T) : CentralOn q S := by
  rw [centralOn_iff] at h ⊢
  intro x hx hqx y hy
  exact h x (hst hx) hqx y (hst hy)

theorem centralOn_of_table (q : H →* Q) {T : Type*} [Group T]
    (ρ : T →* H) (hρ : Function.Injective (q.comp ρ)) : CentralOn q ρ.range := by
  rw [centralOn_iff]
  rintro x ⟨t,rfl⟩ hx y hy
  have ht : t = 1 := hρ (hx.trans (map_one (q.comp ρ)).symm)
  rw [ht,map_one]
  exact Commute.one_left y

theorem copyFamilyLaw_iff_centralOn {Ω : Type*} (U : ι → Set Ω)
    (F : Option ι → E →* H) (q : H →* Q) (v : (Ω → E) →* Q)
    (hv : Function.Injective v)
    (hcompat : ∀ i, q.comp (F i) = v.comp (maskFamily U i)) :
    CopyFamilyLaw U F ↔ CentralOn q (copyFamilyEval F).range := by
  have he : q.comp (copyFamilyEval F) = v.comp (assignmentEval U) := by
    apply FreeGroup.ext_hom
    rintro ⟨i,s⟩
    simpa only [MonoidHom.comp_apply,assignmentEval,copyFamilyEval_of] using
      DFunLike.congr_fun (hcompat i) s
  have hk (w : FreeGroup (Option ι × E)) :
      q (copyFamilyEval F w) = 1 ↔ assignmentEval U w = 1 := by
    have hw := DFunLike.congr_fun he w
    change q (copyFamilyEval F w) = v (assignmentEval U w) at hw
    rw [hw,← map_one v]
    exact hv.eq_iff
  rw [CopyFamilyLaw,hasCentralLaw_iff]
  constructor
  · intro h x hx
    obtain ⟨w,hw⟩ := x.property
    have hx' : q (copyFamilyEval F w) = 1 := by
      change q x.val = 1 at hx
      simpa only [hw] using hx
    have ht := h w ((hk w).mp hx')
    have heq : (copyFamilyEval F).rangeRestrict w = x := Subtype.ext hw
    rwa [heq] at ht
  · intro h w hw
    exact h ((hk w).mpr hw)

theorem centralOn_conjugate (q : H →* Q) (S : Subgroup H) (z : H)
    (h : CentralOn q S) : CentralOn q (S.map (MulAut.conj z).toMonoidHom) := by
  rw [centralOn_iff] at h ⊢
  rintro x ⟨x,hx,rfl⟩ hqx y ⟨y,hy,rfl⟩
  have hqx' : q x = 1 := by
    have he : MulAut.conj (q z) (q x) = 1 := by simpa using hqx
    exact (MulAut.conj (q z)).injective (he.trans (map_one _).symm)
  exact (h x hx hqx' y hy).map (MulAut.conj z).toMonoidHom

end ActualFamilyLaws

end SimpleAmenable
end
end

end OAI
