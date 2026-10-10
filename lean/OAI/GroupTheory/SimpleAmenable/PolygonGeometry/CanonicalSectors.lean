import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FiniteCentralKernel

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section CanonicalSectors
open scoped commutatorElement

variable {E H Q : Type*} [Group E] [Group H] [Group Q]

theorem perfect_maps_commute_of_central [Group.IsPerfect E]
    {P : Type*} [Group P] (q : H →* Q) (hc : q.ker ≤ Subgroup.center H)
    (f : E →* H) (g : P →* H)
    (hfg : ∀ x y, Commute (q (f x)) (q (g y))) :
    ∀ x y, Commute (f x) (g y) := by
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hh : ⁅f.range,g.range⁆ ≤ Subgroup.center H := by
    apply Subgroup.commutator_le.mpr
    rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩
    apply hc
    change q ⁅f x,g y⁆ = 1
    rw [map_commutatorElement]
    exact (hfg x y).commutator_eq
  have hzero := perfect_commutator_central_trivial f.range g.range hh
  intro x y
  apply commutatorElement_eq_one_iff_mul_comm.mp
  have hh' := Subgroup.commutator_mem_commutator
    (show f x ∈ f.range from ⟨x,rfl⟩) (show g y ∈ g.range from ⟨y,rfl⟩)
  simpa [hzero] using hh'

theorem perfect_finite_pi {ι : Type*} [Finite ι] {F : ι → Type*}
    [∀ i, Group (F i)] [∀ i, Group.IsPerfect (F i)] : Group.IsPerfect (∀ i, F i) := by
  classical
  have he : (Abelianization.of : (∀ i, F i) →* Abelianization (∀ i, F i)) = 1 := by
    apply MonoidHom.pi_ext
    intro i x
    exact perfect_hom_to_commGroup
      (Abelianization.of.comp (MonoidHom.mulSingle F i)) x
  constructor
  rw [← Abelianization.ker_of, he, MonoidHom.ker_one]

variable {Ω : Type*}

noncomputable def sectorMask (U : Set Ω) : E →* (Ω → E) := by
  classical
  exact { toFun := fun s ω => if ω ∈ U then s else 1
          map_one' := by funext ω; simp
          map_mul' := by intro s t; funext ω; by_cases h : ω ∈ U <;> simp [h] }

@[simp] theorem sectorMask_of_mem (U : Set Ω) (s : E) (ω : Ω) (h : ω ∈ U) :
    sectorMask U s ω = s := by
  classical
  simp [sectorMask, h]

@[simp] theorem sectorMask_of_not_mem (U : Set Ω) (s : E) (ω : Ω) (h : ω ∉ U) :
    sectorMask U s ω = 1 := by
  classical
  simp [sectorMask, h]

theorem sectorMask_commute {U V : Set Ω} (huv : Disjoint U V) (s t : E) :
    Commute (sectorMask U s) (sectorMask V t) := by
  classical
  funext ω
  change sectorMask U s ω * sectorMask V t ω = sectorMask V t ω * sectorMask U s ω
  have hd := Set.disjoint_left.mp huv
  by_cases hu : ω ∈ U <;> by_cases hv : ω ∈ V <;> simp_all [sectorMask]

theorem sectorMask_disjoint_union {U V : Set Ω} (huv : Disjoint U V) (s : E) :
    sectorMask (U ∪ V) s = sectorMask U s * sectorMask V s := by
  classical
  funext ω
  have hd := Set.disjoint_left.mp huv
  by_cases hu : ω ∈ U <;> by_cases hv : ω ∈ V <;> simp_all [sectorMask, Pi.mul_apply]

variable [Group.IsPerfect E]

noncomputable def centralSector (φ : (Ω → E) →* H ⧸ Subgroup.center H) (U : Set Ω) :
    UniversalExtension E →* H :=
  universalLift (QuotientGroup.mk' (Subgroup.center H))
    (QuotientGroup.mk'_surjective (Subgroup.center H))
    (by rw [QuotientGroup.ker_mk']) (φ.comp (sectorMask U))

theorem centralSector_spec (φ : (Ω → E) →* H ⧸ Subgroup.center H) (U : Set Ω)
    (s : UniversalExtension E) :
    QuotientGroup.mk' (Subgroup.center H) (centralSector φ U s) =
      φ (sectorMask U (universalProjection E s)) :=
  DFunLike.congr_fun (universalLift_spec (QuotientGroup.mk' (Subgroup.center H))
    (QuotientGroup.mk'_surjective (Subgroup.center H))
    (by rw [QuotientGroup.ker_mk']) (φ.comp (sectorMask U))) s

theorem centralSector_commute (φ : (Ω → E) →* H ⧸ Subgroup.center H)
    {U V : Set Ω} (huv : Disjoint U V) (s t : UniversalExtension E) :
    Commute (centralSector φ U s) (centralSector φ V t) := by
  apply perfect_maps_commute_of_central (QuotientGroup.mk' (Subgroup.center H))
    (by rw [QuotientGroup.ker_mk']) (centralSector φ U) (centralSector φ V) ?_ s t
  intro x y
  rw [centralSector_spec, centralSector_spec]
  exact (sectorMask_commute huv _ _).map φ

def commutingProduct (f g : E →* H) (hc : ∀ s t, Commute (f s) (g t)) : E →* H :=
  (f.noncommCoprod g hc).comp ((MonoidHom.id E).prod (MonoidHom.id E))

omit [Group.IsPerfect E] in
@[simp] theorem commutingProduct_apply (f g : E →* H)
    (hc : ∀ s t, Commute (f s) (g t)) (s : E) :
    commutingProduct f g hc s = f s * g s := rfl

theorem centralSector_union (φ : (Ω → E) →* H ⧸ Subgroup.center H)
    {U V : Set Ω} (huv : Disjoint U V) (s : UniversalExtension E) :
    centralSector φ (U ∪ V) s = centralSector φ U s * centralSector φ V s := by
  let p := commutingProduct (centralSector φ U) (centralSector φ V)
    (centralSector_commute φ huv)
  have hp : centralSector φ (U ∪ V) = p := by
    apply perfect_lift_unique (QuotientGroup.mk' (Subgroup.center H))
      (by rw [QuotientGroup.ker_mk'])
    ext t
    simp only [MonoidHom.comp_apply, p, commutingProduct_apply, map_mul, centralSector_spec]
    rw [sectorMask_disjoint_union huv, map_mul]
  exact DFunLike.congr_fun hp s

@[simp] theorem centralSector_empty (φ : (Ω → E) →* H ⧸ Subgroup.center H) :
    centralSector φ ∅ = 1 := by
  apply perfect_lift_unique (QuotientGroup.mk' (Subgroup.center H))
    (by rw [QuotientGroup.ker_mk'])
  ext s
  simp only [MonoidHom.comp_apply, centralSector_spec, MonoidHom.one_apply, map_one]
  have h : sectorMask (∅ : Set Ω) (universalProjection E s) = 1 := by ext ω; simp
  rw [h, map_one]

theorem centralSector_trivial (φ : (Ω → E) →* H ⧸ Subgroup.center H)
    (U : Set Ω) (hU : φ.comp (sectorMask U) = 1) : centralSector φ U = 1 := by
  apply perfect_lift_unique (QuotientGroup.mk' (Subgroup.center H))
    (by rw [QuotientGroup.ker_mk'])
  ext s
  rw [MonoidHom.comp_apply, centralSector_spec]
  have ht := DFunLike.congr_fun hU (universalProjection E s)
  simpa only [MonoidHom.comp_apply, MonoidHom.one_apply, map_one] using ht

def assignmentPullback {Ω' : Type*} (r : Ω' → Ω) : (Ω → E) →* (Ω' → E) where
  toFun f := f ∘ r
  map_one' := rfl
  map_mul' _ _ := rfl

theorem centralSector_refine {Ω' : Type*} (r : Ω' → Ω)
    (φ : (Ω' → E) →* H ⧸ Subgroup.center H) (U : Set Ω) :
    centralSector (φ.comp (assignmentPullback r)) U = centralSector φ (r ⁻¹' U) := by
  apply perfect_lift_unique (QuotientGroup.mk' (Subgroup.center H))
    (by rw [QuotientGroup.ker_mk'])
  ext s
  simp only [MonoidHom.comp_apply, centralSector_spec]
  congr 1

noncomputable def centralSectorProduct [Fintype Ω]
    (φ : (Ω → E) →* H ⧸ Subgroup.center H) : (Ω → UniversalExtension E) →* H :=
  MonoidHom.noncommPiCoprod (fun ω => centralSector φ {ω})
    (fun _ _ h => centralSector_commute φ (Set.disjoint_singleton.mpr h))

@[simp] theorem centralSectorProduct_single [Fintype Ω] [DecidableEq Ω]
    (φ : (Ω → E) →* H ⧸ Subgroup.center H) (ω : Ω) (s : UniversalExtension E) :
    centralSectorProduct φ (Pi.mulSingle ω s) = centralSector φ {ω} s := by
  classical
  exact MonoidHom.noncommPiCoprod_mulSingle _ _ _

def assignmentProjection : (Ω → UniversalExtension E) →* (Ω → E) where
  toFun s ω := universalProjection E (s ω)
  map_one' := by ext ω; exact map_one _
  map_mul' s t := by ext ω; exact map_mul _ _ _

theorem assignmentProjection_surjective :
    Function.Surjective (assignmentProjection (E := E) (Ω := Ω)) := by
  intro f
  choose s hs using fun ω => universalProjection_surjective E (f ω)
  exact ⟨s, funext hs⟩

theorem centralSectorProduct_spec [Fintype Ω]
    (φ : (Ω → E) →* H ⧸ Subgroup.center H) :
    (QuotientGroup.mk' (Subgroup.center H)).comp (centralSectorProduct φ) =
      φ.comp assignmentProjection := by
  classical
  apply MonoidHom.pi_ext
  intro ω s
  simp only [MonoidHom.comp_apply, centralSectorProduct_single, centralSector_spec]
  congr 1
  ext ν
  by_cases h : ν = ω
  · subst ν
    simp [assignmentProjection]
  · simp [sectorMask, assignmentProjection, h]

theorem centralSectorProduct_surjective [Fintype Ω] [Group.IsPerfect H]
    (φ : (Ω → E) →* H ⧸ Subgroup.center H) (hφ : Function.Surjective φ) :
    Function.Surjective (centralSectorProduct φ) := by
  let : Group.IsPerfect (Ω → UniversalExtension E) := perfect_finite_pi
  have hs : Function.Surjective
      ((QuotientGroup.mk' (Subgroup.center H)).comp (centralSectorProduct φ)) := by
    rw [centralSectorProduct_spec]
    exact hφ.comp assignmentProjection_surjective
  apply MonoidHom.range_eq_top.mp
  rw [perfect_lift_range (centralSectorProduct φ) (QuotientGroup.mk' (Subgroup.center H))
    hs (by rw [QuotientGroup.ker_mk']), Group.IsPerfect.commutator_eq_top]

theorem centralSector_generate [Fintype Ω] [Group.IsPerfect H]
    (φ : (Ω → E) →* H ⧸ Subgroup.center H) (hφ : Function.Surjective φ) :
    (⨆ ω : Ω, (centralSector φ {ω}).range) = ⊤ := by
  have hr := MonoidHom.range_eq_top.mpr (centralSectorProduct_surjective φ hφ)
  calc
    _ = (centralSectorProduct φ).range := by
      unfold centralSectorProduct
      exact (MonoidHom.noncommPiCoprod_range _).symm
    _ = ⊤ := hr

end CanonicalSectors

end SimpleAmenable
end
end

end OAI
