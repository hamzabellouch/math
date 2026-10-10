import Mathlib

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
section PerfectCalculus

open scoped commutatorElement

variable {P H Q : Type*} [Group P] [Group H] [Group Q]

theorem perfect_hom_to_commGroup {A : Type*} [Group A] [IsMulCommutative A] [Group.IsPerfect P]
    (f : P →* A) (x : P) : f x = 1 := by
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  have : Subsingleton f.range := inferInstance
  exact congrArg Subtype.val
    (Subsingleton.elim (⟨f x, x, rfl⟩ : f.range) 1)

theorem perfect_lift_unique [Group.IsPerfect P] (q : H →* Q)
    (hq : q.ker ≤ Subgroup.center H) (f g : P →* H)
    (hfg : q.comp f = q.comp g) : f = g := by
  have hpoint (x : P) : q (f x) = q (g x) := DFunLike.congr_fun hfg x
  have hc (x : P) : f x * (g x)⁻¹ ∈ Subgroup.center H := by
    apply hq
    change q (f x * (g x)⁻¹) = 1
    simp [hpoint]
  let d : P →* Subgroup.center H :=
    { toFun := fun x => ⟨f x * (g x)⁻¹, hc x⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        change f (x * y) * (g (x * y))⁻¹ =
          (f x * (g x)⁻¹) * (f y * (g y)⁻¹)
        rw [map_mul, map_mul, mul_inv_rev]
        have hcomm := Subgroup.mem_center_iff.mp (hc y) ((g x)⁻¹)
        calc
          f x * f y * ((g y)⁻¹ * (g x)⁻¹) =
              f x * ((f y * (g y)⁻¹) * (g x)⁻¹) := by simp only [mul_assoc]
          _ = f x * ((g x)⁻¹ * (f y * (g y)⁻¹)) := by rw [hcomm]
          _ = (f x * (g x)⁻¹) * (f y * (g y)⁻¹) := by simp only [mul_assoc] }
  ext x
  have heq := congrArg Subtype.val (perfect_hom_to_commGroup d x)
  exact mul_inv_eq_one.mp heq

theorem perfect_commutator_central_trivial (A B : Subgroup H) [Group.IsPerfect A]
    (h : ⁅A, B⁆ ≤ Subgroup.center H) : ⁅A, B⁆ = ⊥ := by
  have hz : ⁅⁅A, B⁆, (⊤ : Subgroup H)⁆ = ⊥ :=
    Subgroup.commutator_top_right_eq_bot_iff_le_center.mpr h
  have ha : ⁅⁅A, B⁆, A⁆ = ⊥ :=
    bot_unique ((Subgroup.commutator_mono le_rfl le_top).trans hz.le)
  have hb : ⁅⁅B, A⁆, A⁆ = ⊥ := by simpa only [Subgroup.commutator_comm B A] using ha
  have hc : ⁅⁅A, A⁆, B⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate ha hb
  simpa only [Subgroup.commutator_eq_self] using hc

theorem perfect_center_quotient [Group.IsPerfect H] :
    Subgroup.center (H ⧸ Subgroup.center H) = ⊥ :=
  Group.IsPerfect.center_quotient_center_eq_bot H

theorem central_extension_decomposition [Group.IsPerfect Q] (q : H →* Q)
    (hq : Function.Surjective q) (hcentral : q.ker ≤ Subgroup.center H) (x : H) :
    ∃ d ∈ commutator H, ∃ z ∈ Subgroup.center H, x = d * z := by
  have hmap : (commutator H).map q = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hq,
      ← commutator_def, Group.IsPerfect.commutator_eq_top]
  obtain ⟨d, hd, hdx⟩ := Subgroup.mem_map.mp (hmap.symm ▸ Subgroup.mem_top (q x))
  refine ⟨d, hd, d⁻¹ * x, hcentral ?_, by simp⟩
  change q (d⁻¹ * x) = 1
  simp [hdx]

theorem central_extension_commutator_perfect [Group.IsPerfect Q] (q : H →* Q)
    (hq : Function.Surjective q) (hcentral : q.ker ≤ Subgroup.center H) :
    Group.IsPerfect (commutator H) := by
  apply Subgroup.isPerfect_iff.mpr
  apply le_antisymm (Subgroup.commutator_le_self _)
  rw [commutator_def]
  apply Subgroup.commutator_le.mpr
  intro x _ y _
  obtain ⟨d, hd, z, hz, rfl⟩ := central_extension_decomposition q hq hcentral x
  obtain ⟨e, he, w, hw, rfl⟩ := central_extension_decomposition q hq hcentral y
  have hzcomm : ⁅z, e * w⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr
      ((Subgroup.mem_center_iff.mp hz (e * w)).symm)
  have hwcomm : ⁅d, w⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hw d)
  rw [commutatorElement_mul_left_eq_conj_mul, hzcomm]
  simp only [mul_one, mul_inv_cancel, one_mul]
  rw [commutatorElement_mul_right_eq_mul_conj, hwcomm]
  simpa only [mul_one, mul_inv_cancel_right, commutator_def] using Subgroup.commutator_mem_commutator hd he

theorem central_extension_commutator_surjective [Group.IsPerfect Q] (q : H →* Q)
    (hq : Function.Surjective q) :
    Function.Surjective (q.comp (commutator H).subtype) := by
  intro x
  have hmap : (commutator H).map q = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hq,
      ← commutator_def, Group.IsPerfect.commutator_eq_top]
  obtain ⟨d, hd, hdx⟩ := Subgroup.mem_map.mp (hmap.symm ▸ Subgroup.mem_top x)
  exact ⟨⟨d, hd⟩, hdx⟩

end PerfectCalculus

open scoped commutatorElement
section FiniteCentralCovers
variable {H Q : Type*} [Group H] [Group Q]

theorem commutator_eq_of_central_kernel (q : H →* Q)
    (hc : q.ker ≤ Subgroup.center H) {x x' : H} (hx : q x = q x') (y : H) :
    ⁅x,y⁆ = ⁅x',y⁆ := by
  have hz : x'⁻¹*x ∈ q.ker := by simp [hx]
  have hzy : Commute (x'⁻¹*x) y := (Subgroup.mem_center_iff.mp (hc hz) y).symm
  calc
    _ = ⁅x'*(x'⁻¹*x),y⁆ := by simp
    _ = ⁅x',y⁆ := by rw [commutatorElement_mul_left_eq_conj_mul,hzy.commutator_eq]; simp

theorem finite_of_perfect_central_cover [Finite Q] [Group.IsPerfect H]
    (q : H →* Q) (hq : Function.Surjective q) (hc : q.ker ≤ Subgroup.center H) : Finite H := by
  classical
  let s : Q → H := fun x => (hq x).choose
  have hs (x : Q) : q (s x) = x := (hq x).choose_spec
  let r : Q × Q → commutatorSet H := fun p =>
    ⟨⁅s p.1,s p.2⁆,commutator_mem_commutatorSet _ _⟩
  have hr : Function.Surjective r := by
    rintro ⟨z,hz⟩
    obtain ⟨x,y,rfl⟩ := mem_commutatorSet_iff.mp hz
    refine ⟨(q x,q y),Subtype.ext ?_⟩
    change ⁅s (q x),s (q y)⁆ = ⁅x,y⁆
    rw [commutator_eq_of_central_kernel q hc (hs (q x))]
    rw [← commutatorElement_inv,commutator_eq_of_central_kernel q hc (hs (q y)),
      commutatorElement_inv]
  have : Finite (commutatorSet H) := Finite.of_surjective r hr
  have : Finite (commutator H) := inferInstance
  exact Finite.of_surjective (commutator H).subtype (by
    intro x
    refine ⟨⟨x,?_⟩,rfl⟩
    rw [Group.IsPerfect.commutator_eq_top]
    trivial)
end FiniteCentralCovers

section UniversalCentralExtension

open scoped commutatorElement

variable (E : Type*) [Group E]

def freeEvaluation : FreeGroup E →* E := FreeGroup.lift id

@[simp] theorem freeEvaluation_of (x : E) : freeEvaluation E (FreeGroup.of x) = x :=
  FreeGroup.lift_apply_of

theorem freeEvaluation_surjective : Function.Surjective (freeEvaluation E) :=
  fun x => ⟨FreeGroup.of x, freeEvaluation_of E x⟩

def centralizingRelations : Subgroup (FreeGroup E) :=
  ⁅(⊤ : Subgroup (FreeGroup E)), (freeEvaluation E).ker⁆

instance : (centralizingRelations E).Normal := by
  unfold centralizingRelations
  infer_instance

abbrev CentralizedFree := FreeGroup E ⧸ centralizingRelations E

def centralFreeMap : CentralizedFree E →* E :=
  QuotientGroup.lift (centralizingRelations E) (freeEvaluation E)
    (fun _ h => Subgroup.commutator_le_right (⊤ : Subgroup (FreeGroup E))
      (freeEvaluation E).ker h)

@[simp] theorem centralFreeMap_mk (x : FreeGroup E) :
    centralFreeMap E (QuotientGroup.mk' (centralizingRelations E) x) =
      freeEvaluation E x := rfl

theorem centralFreeMap_surjective : Function.Surjective (centralFreeMap E) := by
  intro x
  exact ⟨QuotientGroup.mk' (centralizingRelations E) (FreeGroup.of x), freeEvaluation_of E x⟩

theorem centralFreeMap_central : (centralFreeMap E).ker ≤ Subgroup.center (CentralizedFree E) := by
  intro x
  refine QuotientGroup.induction_on x ?_
  intro w hw
  apply Subgroup.mem_center_iff.mpr
  intro y
  refine QuotientGroup.induction_on y ?_
  intro v
  apply commutatorElement_eq_one_iff_mul_comm.mp
  change ⁅QuotientGroup.mk' (centralizingRelations E) v,
    QuotientGroup.mk' (centralizingRelations E) w⁆ = 1
  rw [← map_commutatorElement]
  apply (QuotientGroup.eq_one_iff _).mpr
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top v) hw

abbrev UniversalExtension := commutator (CentralizedFree E)

def universalProjection : UniversalExtension E →* E :=
  (centralFreeMap E).comp (commutator (CentralizedFree E)).subtype

instance [Group.IsPerfect E] : Group.IsPerfect (UniversalExtension E) :=
  central_extension_commutator_perfect (centralFreeMap E)
    (centralFreeMap_surjective E) (centralFreeMap_central E)

theorem universalProjection_surjective [Group.IsPerfect E] :
    Function.Surjective (universalProjection E) :=
  central_extension_commutator_surjective (centralFreeMap E) (centralFreeMap_surjective E)

theorem universalProjection_central :
    (universalProjection E).ker ≤ Subgroup.center (UniversalExtension E) := by
  intro x hx
  apply Subgroup.mem_center_iff.mpr
  intro y
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (centralFreeMap_central E hx) y.val

variable {E} {H Q : Type*} [Group H] [Group Q]

theorem universal_lift_exists (q : H →* Q) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center H) (f : E →* Q) :
    ∃ l : UniversalExtension E →* H, q.comp l = f.comp (universalProjection E) := by
  classical
  let a : E → H := fun x => (hq (f x)).choose
  have ha (x : E) : q (a x) = f x := (hq (f x)).choose_spec
  let F : FreeGroup E →* H := FreeGroup.lift a
  have hF : q.comp F = f.comp (freeEvaluation E) := by
    ext x
    simpa [F, freeEvaluation] using ha x
  have hrel : centralizingRelations E ≤ F.ker := by
    apply Subgroup.commutator_le.mpr
    intro x _ r hr
    change F ⁅x, r⁆ = 1
    rw [map_commutatorElement]
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    apply Subgroup.mem_center_iff.mp
    apply hcentral
    change q (F r) = 1
    have hpoint := DFunLike.congr_fun hF r
    simpa only [MonoidHom.comp_apply, MonoidHom.mem_ker.mp hr, map_one] using hpoint
  let Fbar : CentralizedFree E →* H :=
    QuotientGroup.lift (centralizingRelations E) F (fun _ hr => hrel hr)
  refine ⟨Fbar.comp (commutator (CentralizedFree E)).subtype, ?_⟩
  ext x
  change q (Fbar x.val) = f (centralFreeMap E x.val)
  have hpoint (y : CentralizedFree E) : q (Fbar y) = f (centralFreeMap E y) := by
    refine QuotientGroup.induction_on y ?_
    intro w
    exact DFunLike.congr_fun hF w
  exact hpoint x.val

theorem universal_lift_exists_unique [Group.IsPerfect E] (q : H →* Q)
    (hq : Function.Surjective q) (hcentral : q.ker ≤ Subgroup.center H) (f : E →* Q) :
    ∃! l : UniversalExtension E →* H, q.comp l = f.comp (universalProjection E) := by
  obtain ⟨l, hl⟩ := universal_lift_exists q hq hcentral f
  refine ⟨l, hl, ?_⟩
  intro l' hl'
  exact perfect_lift_unique q hcentral l' l (hl'.trans hl.symm)

noncomputable def universalLift [Group.IsPerfect E] (q : H →* Q)
    (hq : Function.Surjective q) (hcentral : q.ker ≤ Subgroup.center H) (f : E →* Q) :
    UniversalExtension E →* H :=
  (universal_lift_exists_unique q hq hcentral f).choose

theorem universalLift_spec [Group.IsPerfect E] (q : H →* Q)
    (hq : Function.Surjective q) (hcentral : q.ker ≤ Subgroup.center H) (f : E →* Q) :
    q.comp (universalLift q hq hcentral f) = f.comp (universalProjection E) :=
  (universal_lift_exists_unique q hq hcentral f).choose_spec.1

variable [Group.IsPerfect E] [Group.IsPerfect H] [Group.IsPerfect Q]

noncomputable def universalMap (f : E →* H) : UniversalExtension E →* UniversalExtension H :=
  universalLift (universalProjection H) (universalProjection_surjective H)
    (universalProjection_central H) f

theorem universalMap_spec (f : E →* H) :
    (universalProjection H).comp (universalMap f) = f.comp (universalProjection E) :=
  universalLift_spec _ _ _ _

@[simp] theorem universalMap_id : universalMap (MonoidHom.id E) =
    MonoidHom.id (UniversalExtension E) := by
  apply perfect_lift_unique (universalProjection E) (universalProjection_central E)
  simpa using universalMap_spec (MonoidHom.id E)

@[simp] theorem universalMap_comp (g : H →* Q) (f : E →* H) :
    universalMap (g.comp f) = (universalMap g).comp (universalMap f) := by
  apply perfect_lift_unique (universalProjection Q) (universalProjection_central Q)
  rw [universalMap_spec, ← MonoidHom.comp_assoc, universalMap_spec]
  simp only [MonoidHom.comp_assoc, universalMap_spec]

noncomputable def universalEquiv (f : E ≃* H) : UniversalExtension E ≃* UniversalExtension H :=
  MonoidHom.toMulEquiv (universalMap f.toMonoidHom) (universalMap f.symm.toMonoidHom)
    (by rw [← universalMap_comp]; simp)
    (by rw [← universalMap_comp]; simp)

instance universalExtension_finite [Finite E] : Finite (UniversalExtension E) :=
  finite_of_perfect_central_cover (universalProjection E) (universalProjection_surjective E)
    (universalProjection_central E)

end UniversalCentralExtension

end SimpleAmenable
end
end

end OAI
