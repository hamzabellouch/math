import Mathlib

namespace OAI

namespace SourceBurnside.Stability
noncomputable section
open Classical

abbrev QGroup := Multiplicative ℚ

structure RationalExtension (E G : Type*) [Group E] [Group G]
    extends GroupExtension QGroup E G where
  central : inl.range ≤ Subgroup.center E

namespace RationalExtension
variable {E G : Type*} [Group E] [Group G] (S : RationalExtension E G)

lemma inl_central (q : QGroup) : S.inl q ∈ Subgroup.center E :=
  S.central ⟨q, rfl⟩

def kernelHom : QGroup →* S.rightHom.ker where
  toFun q := ⟨S.inl q, S.toGroupExtension.rightHom_inl q⟩
  map_one' := Subtype.ext (map_one S.inl)
  map_mul' q r := Subtype.ext (map_mul S.inl q r)

def kernelEquiv : QGroup ≃* S.rightHom.ker :=
  MulEquiv.ofBijective S.kernelHom
    ⟨fun q r h => S.inl_injective (congrArg Subtype.val h), by
      rintro ⟨x, hx⟩
      have : x ∈ S.inl.range := S.range_inl_eq_ker_rightHom ▸ hx
      obtain ⟨q, hq⟩ := this
      exact ⟨q, Subtype.ext hq⟩⟩

@[simp] lemma kernelEquiv_val (q : QGroup) : (S.kernelEquiv q).val = S.inl q := rfl

section Finite
variable [Finite G]

def finiteRetraction : E →* QGroup :=
  haveI : S.rightHom.ker.FiniteIndex := Subgroup.finiteIndex_ker S.rightHom
  let divide : QGroup →* QGroup :=
    { toFun := fun q => Multiplicative.ofAdd (q.toAdd / (S.rightHom.ker.index : ℚ))
      map_one' := by change (0 : ℚ) / _ = 0; simp
      map_mul' := fun q r => by
        change (q.toAdd + r.toAdd) / _ = q.toAdd / _ + r.toAdd / _
        exact add_div _ _ _ }
  divide.comp (MonoidHom.transfer S.kernelEquiv.symm.toMonoidHom)

@[simp] theorem finiteRetraction_inl (q : QGroup) :
    S.finiteRetraction (S.inl q) = q := by
  let : S.rightHom.ker.FiniteIndex := Subgroup.finiteIndex_ker S.rightHom
  have hi : (S.rightHom.ker.index : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Subgroup.FiniteIndex.index_ne_zero
  have hp (k : ℕ) (x : E) (_ : x⁻¹ * S.inl q ^ k * x ∈ S.rightHom.ker) :
      x⁻¹ * S.inl q ^ k * x = S.inl q ^ k := by
    have h := (Subgroup.center E).pow_mem (S.inl_central q) k
    rw [← h.comm]
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  unfold finiteRetraction
  dsimp only [MonoidHom.comp_apply]
  rw [MonoidHom.transfer_eq_pow _ _ hp]
  have he : (⟨S.inl q ^ S.rightHom.ker.index,
      MonoidHom.transfer_eq_pow_aux (S.inl q) hp⟩ : S.rightHom.ker) =
      S.kernelEquiv (q ^ S.rightHom.ker.index) := by
    apply Subtype.ext
    exact (map_pow S.inl q _).symm
  rw [he]
  simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, MonoidHom.coe_mk, OneHom.coe_mk]
  change ((S.rightHom.ker.index : ℚ) * q.toAdd) / (S.rightHom.ker.index : ℚ) = q.toAdd
  exact mul_div_cancel_left₀ _ hi

def finiteComplementMap : S.finiteRetraction.ker →* G :=
  S.rightHom.comp S.finiteRetraction.ker.subtype

lemma finiteComplementMap_bijective : Function.Bijective S.finiteComplementMap := by
  constructor
  · apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    rintro ⟨x, hx⟩ h
    have hg : S.rightHom x = 1 := h
    have hr : x ∈ S.inl.range := S.range_inl_eq_ker_rightHom ▸ hg
    obtain ⟨q, rfl⟩ := hr
    have hq : q = 1 := (S.finiteRetraction_inl q).symm.trans hx
    apply Subtype.ext
    simp [hq]
  · intro g
    obtain ⟨x, hx⟩ := S.rightHom_surjective g
    refine ⟨⟨x * (S.inl (S.finiteRetraction x))⁻¹, ?_⟩, ?_⟩
    · change S.finiteRetraction (x * (S.inl (S.finiteRetraction x))⁻¹) = 1
      simp only [map_mul, map_inv, finiteRetraction_inl, mul_inv_cancel]
    · change S.rightHom (x * (S.inl (S.finiteRetraction x))⁻¹) = g
      simp only [map_mul, map_inv, S.toGroupExtension.rightHom_inl, inv_one, mul_one, hx]

def finiteSplitting : S.toGroupExtension.Splitting where
  toMonoidHom := S.finiteRetraction.ker.subtype.comp
    (MulEquiv.ofBijective S.finiteComplementMap S.finiteComplementMap_bijective).symm.toMonoidHom
  rightInverse_rightHom g :=
    (MulEquiv.ofBijective S.finiteComplementMap S.finiteComplementMap_bijective).apply_symm_apply g

end Finite

lemma inl_eq_one_of_finite_order (q : QGroup) (hq : IsOfFinOrder (S.inl q)) : q = 1 := by
  obtain ⟨m, hm, he⟩ := hq.exists_pow_eq_one
  have hq : q ^ m = 1 := S.inl_injective (by simpa only [map_pow, map_one] using he)
  have ha : (m : ℚ) * q.toAdd = 0 := congrArg Multiplicative.toAdd hq
  have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  have : q.toAdd = 0 := (mul_eq_zero.mp ha).resolve_left hm'
  exact this

theorem torsion_lift_unique {x y : E} (hx : IsOfFinOrder x) (hy : IsOfFinOrder y)
    (hxy : S.rightHom x = S.rightHom y) : x = y := by
  have hr : x * y⁻¹ ∈ S.inl.range := by
    rw [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv, hxy,
      mul_inv_cancel]
  obtain ⟨q, hq⟩ := hr
  have hc : Commute x y := by
    have ht := (S.inl_central q).comm y
    rw [hq] at ht
    have : x * y = y * x := by
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using
        congrArg (fun z : E => z * y) ht.eq
    exact this
  have hf : IsOfFinOrder (S.inl q) := hq.symm ▸ hc.inv_right.isOfFinOrder_mul hx hy.inv
  have he := S.inl_eq_one_of_finite_order q hf
  rw [he, map_one] at hq
  exact mul_inv_eq_one.mp hq.symm

def restrict (H : Subgroup G) : RationalExtension (H.comap S.rightHom) H where
  inl :=
    { toFun := fun q => ⟨S.inl q, by
        change S.rightHom (S.inl q) ∈ H
        rw [S.toGroupExtension.rightHom_inl]
        exact H.one_mem⟩
      map_one' := Subtype.ext (map_one S.inl)
      map_mul' := fun q r => Subtype.ext (map_mul S.inl q r) }
  rightHom :=
    { toFun := fun x => ⟨S.rightHom x, x.property⟩
      map_one' := Subtype.ext (map_one S.rightHom)
      map_mul' := fun q r => Subtype.ext (map_mul S.rightHom (q : E) (r : E)) }
  inl_injective := fun q r h => S.inl_injective (congrArg Subtype.val h)
  rightHom_surjective := by
    rintro ⟨g, hg⟩
    obtain ⟨x, hx⟩ := S.rightHom_surjective g
    exact ⟨⟨x, by change S.rightHom x ∈ H; rwa [hx]⟩, Subtype.ext hx⟩
  range_inl_eq_ker_rightHom := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      exact Subtype.ext (S.toGroupExtension.rightHom_inl q)
    · intro hx
      have h : x.val ∈ S.inl.range := by
        rw [S.range_inl_eq_ker_rightHom]
        exact congrArg Subtype.val hx
      obtain ⟨q, hq⟩ := h
      exact ⟨q, Subtype.ext hq⟩
  central := by
    rintro x ⟨q, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro y
    exact Subtype.ext ((S.inl_central q).comm y.val).eq.symm

def liftFinite (H : Subgroup G) [Finite H] : H →* E :=
  (H.comap S.rightHom).subtype.comp (S.restrict H).finiteSplitting.toMonoidHom

@[simp] lemma rightHom_liftFinite (H : Subgroup G) [Finite H] (g : H) :
    S.rightHom (S.liftFinite H g) = g.val :=
  congrArg Subtype.val ((S.restrict H).finiteSplitting.rightInverse_rightHom g)

lemma liftFinite_finite_order (H : Subgroup G) [Finite H] (g : H) :
    IsOfFinOrder (S.liftFinite H g) := by
  obtain ⟨m, hm, he⟩ := (isOfFinOrder_of_finite g).exists_pow_eq_one
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, by rw [← map_pow, he, map_one]⟩

def LocallyFinite (G : Type*) [Group G] : Prop :=
  ∀ s : Finset G, ∃ H : Subgroup G, (∀ g ∈ s, g ∈ H) ∧ Finite H

variable (hG : LocallyFinite G)
include hG

lemma exists_torsion_lift (g : G) : ∃ x : E, S.rightHom x = g ∧ IsOfFinOrder x := by
  obtain ⟨H, hH, hf⟩ := hG {g}
  let := hf
  exact ⟨S.liftFinite H ⟨g, hH g (Finset.mem_singleton_self g)⟩,
    S.rightHom_liftFinite H _, S.liftFinite_finite_order H _⟩

def torsionLift (g : G) : E := (S.exists_torsion_lift hG g).choose

@[simp] lemma rightHom_torsionLift (g : G) : S.rightHom (S.torsionLift hG g) = g :=
  (S.exists_torsion_lift hG g).choose_spec.1

lemma torsionLift_finite_order (g : G) : IsOfFinOrder (S.torsionLift hG g) :=
  (S.exists_torsion_lift hG g).choose_spec.2

def locallyFiniteSplitting : S.toGroupExtension.Splitting where
  toFun := S.torsionLift hG
  map_one' := S.torsion_lift_unique (S.torsionLift_finite_order hG 1)
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨1, by decide, one_pow 1⟩) (by rw [S.rightHom_torsionLift, map_one])
  map_mul' g h := by
    obtain ⟨H, hH, hf⟩ := hG {g, h}
    let := hf
    let g' : H := ⟨g, hH g (by simp)⟩
    let h' : H := ⟨h, hH h (by simp)⟩
    have he (x : H) : S.torsionLift hG x.val = S.liftFinite H x :=
      S.torsion_lift_unique (S.torsionLift_finite_order hG _) (S.liftFinite_finite_order H x)
        (by rw [S.rightHom_torsionLift, S.rightHom_liftFinite])
    exact (he (g' * h')).trans ((map_mul (S.liftFinite H) g' h').trans
      (congrArg₂ (· * ·) (he g').symm (he h').symm))
  rightInverse_rightHom := S.rightHom_torsionLift hG

theorem locallyFiniteSplitting_unique (σ : S.toGroupExtension.Splitting) :
    σ = S.locallyFiniteSplitting hG := by
  apply DFunLike.ext
  intro g
  have hg : IsOfFinOrder g := by
    obtain ⟨H, hH, hf⟩ := hG {g}
    let := hf
    obtain ⟨m, hm, he⟩ := (isOfFinOrder_of_finite (⟨g, hH g (by simp)⟩ : H)).exists_pow_eq_one
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, congrArg Subtype.val he⟩
  have hσ : IsOfFinOrder (σ g) := by
    obtain ⟨m, hm, he⟩ := hg.exists_pow_eq_one
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, by rw [← map_pow, he, map_one]⟩
  exact S.torsion_lift_unique hσ (S.torsionLift_finite_order hG g)
    ((σ.rightInverse_rightHom g).trans (S.rightHom_torsionLift hG g).symm)

end RationalExtension
end
end SourceBurnside.Stability

namespace SourceBurnside.Stability.CentralPushout
noncomputable section
open Classical
variable {P G : Type} [Group P] [Group G]

def graphHom (p : P →* G) (φ : p.ker →* QGroup) : p.ker →* P×QGroup where
  toFun j := (j.val,(φ j)⁻¹)
  map_one' := Prod.ext rfl (by simp)
  map_mul' j k := Prod.ext rfl (by simp [mul_comm])

def relation (p : P →* G) (_hc : p.ker ≤ Subgroup.center P) (φ : p.ker →* QGroup) : Subgroup (P×QGroup) :=
  (graphHom p φ).range

lemma relation_central (p : P →* G) (hc : p.ker ≤ Subgroup.center P) (φ : p.ker →* QGroup) :
    relation p hc φ ≤ Subgroup.center (P×QGroup) := by
  rintro x ⟨j,rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro y
  apply Prod.ext
  · exact ((hc j.property).comm y.1).eq.symm
  · exact mul_comm _ _

instance relation_normal (p : P →* G) (hc : p.ker ≤ Subgroup.center P) (φ : p.ker →* QGroup) :
    (relation p hc φ).Normal where
  conj_mem x hx y := by
    have he := ((relation_central p hc φ hx).comm y).eq
    rw [←he,mul_assoc,mul_inv_cancel,mul_one]
    exact hx

def Extension (p : P →* G) (hc : p.ker ≤ Subgroup.center P) (φ : p.ker →* QGroup) :=
  (P×QGroup) ⧸ relation p hc φ
instance extensionGroup (p : P →* G) (hc : p.ker ≤ Subgroup.center P) (φ : p.ker →* QGroup) :
    Group (Extension p hc φ) := inferInstanceAs (Group ((P×QGroup) ⧸ relation p hc φ))

variable (p : P →* G) (hc : p.ker ≤ Subgroup.center P) (φ : p.ker →* QGroup)

def canonical : P →* Extension p hc φ := (QuotientGroup.mk' (relation p hc φ)).comp ((MonoidHom.id P).prod 1)
def inclusion : QGroup →* Extension p hc φ := (QuotientGroup.mk' (relation p hc φ)).comp ((1 : QGroup →* P).prod (MonoidHom.id QGroup))

def projection : Extension p hc φ →* G := QuotientGroup.lift (relation p hc φ)
  (p.comp (MonoidHom.fst P QGroup)) (by
    rintro x ⟨j,rfl⟩
    exact j.property)

lemma projection_mk (s : P) (q : QGroup) : projection p hc φ (QuotientGroup.mk' (relation p hc φ) (s,q))=p s := rfl
lemma projection_canonical (s : P) : projection p hc φ (canonical p hc φ s)=p s := rfl
lemma projection_inclusion (q : QGroup) : projection p hc φ (inclusion p hc φ q)=1 := map_one p

lemma canonical_kernel (j : p.ker) : canonical p hc φ j.val=inclusion p hc φ (φ j) := by
  apply (QuotientGroup.mk'_eq_mk' (relation p hc φ)).mpr
  refine ⟨graphHom p φ j⁻¹,⟨j⁻¹,rfl⟩,?_⟩
  apply Prod.ext
  · exact mul_inv_cancel _
  · change 1*(φ j⁻¹)⁻¹=φ j
    rw [map_inv,inv_inv,one_mul]

lemma mk_pair (s : P) (q : QGroup) : QuotientGroup.mk' (relation p hc φ) (s,q)=canonical p hc φ s*inclusion p hc φ q := by
  change _=QuotientGroup.mk' _ (s,1)*QuotientGroup.mk' _ (1,q)
  erw [←map_mul]
  congr 1
  exact Prod.ext (mul_one _).symm (one_mul _).symm

lemma inclusion_injective : Function.Injective (inclusion p hc φ) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro q hq
  change inclusion p hc φ q=1 at hq
  have h : (1,q)∈relation p hc φ := (QuotientGroup.eq_one_iff (1,q)).mp hq
  obtain ⟨j,hj⟩ := h
  have hj1 : j=1 := Subtype.ext (congrArg Prod.fst hj)
  have he := congrArg Prod.snd hj
  change (φ j)⁻¹=q at he
  change q=1
  simpa only [hj1,map_one,inv_one] using he.symm

lemma exactness : (inclusion p hc φ).range=(projection p hc φ).ker := by
  ext x
  constructor
  · rintro ⟨q,rfl⟩
    exact projection_inclusion p hc φ q
  · intro hx
    obtain ⟨⟨s,q⟩,rfl⟩ := QuotientGroup.mk'_surjective (relation p hc φ) x
    have hs : s∈p.ker := hx
    refine ⟨φ ⟨s,hs⟩*q,?_⟩
    rw [map_mul,←canonical_kernel p hc φ ⟨s,hs⟩,mk_pair]

lemma inclusion_central : (inclusion p hc φ).range ≤ Subgroup.center (Extension p hc φ) := by
  rintro x ⟨q,rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro y
  obtain ⟨⟨s,r⟩,rfl⟩ := QuotientGroup.mk'_surjective (relation p hc φ) y
  change QuotientGroup.mk' _ (s,r)*QuotientGroup.mk' _ (1,q)=QuotientGroup.mk' _ (1,q)*QuotientGroup.mk' _ (s,r)
  erw [←map_mul,←map_mul]
  congr 1
  exact Prod.ext ((mul_one _).trans (one_mul _).symm) (mul_comm _ _)

def extension (hp : Function.Surjective p) : RationalExtension (Extension p hc φ) G where
  inl := inclusion p hc φ
  rightHom := projection p hc φ
  inl_injective := inclusion_injective p hc φ
  rightHom_surjective := by
    intro g
    obtain ⟨s,rfl⟩ := hp g
    exact ⟨canonical p hc φ s,rfl⟩
  range_inl_eq_ker_rightHom := exactness p hc φ
  central := inclusion_central p hc φ

end
end SourceBurnside.Stability.CentralPushout

namespace SourceBurnside.Stability
noncomputable section
open Classical Representation

variable {G V W : Type*} [Group G] [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W]

abbrev LocallyFinite := RationalExtension.LocallyFinite

namespace FiniteAverage
variable [Fintype G] (ρ : Representation ℚ G V)

def average : V →ₗ[ℚ] V := (Fintype.card G : ℚ)⁻¹ • ∑ g : G, ρ g

lemma average_apply (v : V) : average ρ v =
    (Fintype.card G : ℚ)⁻¹ • ∑ g : G, ρ g v := by
  simp [average]

lemma average_action (g : G) (v : V) : average ρ (ρ g v) = average ρ v := by
  simp only [average_apply]
  congr 1
  simp only [← Module.End.mul_apply, ← map_mul]
  exact Fintype.sum_equiv (Equiv.mulRight g) (fun h => ρ (h * g) v)
    (fun h => ρ h v) (fun _ => rfl)

lemma average_ker (v : V) (hv : v ∈ Coinvariants.ker ρ) : average ρ v = 0 := by
  apply (show Coinvariants.ker ρ ≤ (average ρ).ker from ?_) hv
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨g, x⟩, rfl⟩
  change average ρ (ρ g x - x) = 0
  rw [map_sub, average_action, sub_self]

lemma mk_average (v : V) : Coinvariants.mk ρ (average ρ v) = Coinvariants.mk ρ v := by
  rw [average_apply, map_smul, map_sum]
  simp only [Coinvariants.mk_self_apply, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀, one_smul]
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

lemma intertwining (τ : Representation ℚ G W) (f : ρ.IntertwiningMap τ) (v : V) :
    f (average ρ v) = average τ (f v) := by
  simp only [average_apply, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  exact DFunLike.congr_fun (f.isIntertwining' g) v

lemma map_injective (τ : Representation ℚ G W) (f : ρ.IntertwiningMap τ)
    (hf : Function.Injective f) : Function.Injective (Coinvariants.map ρ τ f) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨v, rfl⟩ := Coinvariants.mk_surjective ρ x
  have hz : average τ (f v) = 0 := average_ker τ _ ((Coinvariants.mk_eq_zero τ).mp hx)
  have hv : average ρ v = 0 := hf (by rw [intertwining ρ τ f, hz, map_zero])
  rw [← mk_average ρ v, hv, map_zero]
end FiniteAverage

lemma coinvariant_finite_witness (hG : LocallyFinite G) (ρ : Representation ℚ G V)
    {v : V} (hv : v ∈ Coinvariants.ker ρ) :
    ∃ H : Subgroup G, Finite H ∧ v ∈ Coinvariants.ker (ρ.comp H.subtype) := by
  obtain ⟨s, hs, hvs⟩ := Submodule.mem_span_finite_of_mem_span hv
  let pick (x : s) : G × V := (hs x.property).choose
  have hp (x : s) : ρ (pick x).1 (pick x).2 - (pick x).2 = x.val :=
    (hs x.property).choose_spec
  obtain ⟨H, hH, hfin⟩ := hG (Finset.univ.image fun x : s => (pick x).1)
  refine ⟨H, hfin, (show Submodule.span ℚ (s : Set V) ≤
    Coinvariants.ker (ρ.comp H.subtype) from ?_) hvs⟩
  apply Submodule.span_le.mpr
  intro x hx
  let y : s := ⟨x, hx⟩
  have hg : (pick y).1 ∈ H := hH _ (Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩)
  change y.val ∈ Coinvariants.ker (ρ.comp H.subtype)
  rw [← hp y]
  exact Coinvariants.sub_mem_ker (ρ := ρ.comp H.subtype) ⟨(pick y).1, hg⟩ (pick y).2

lemma locallyFinite_coinvariants_injective (hG : LocallyFinite G)
    (ρ : Representation ℚ G V) (τ : Representation ℚ G W)
    (f : ρ.IntertwiningMap τ) (hf : Function.Injective f) :
    Function.Injective (Coinvariants.map ρ τ f) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨v, rfl⟩ := Coinvariants.mk_surjective ρ x
  obtain ⟨H, hfin, hv⟩ := coinvariant_finite_witness hG τ
    ((Coinvariants.mk_eq_zero τ).mp hx)
  let : Finite H := hfin
  let : Fintype H := Fintype.ofFinite H
  let fH : Representation.IntertwiningMap (ρ.comp H.subtype) (τ.comp H.subtype) :=
    { f with isIntertwining' := fun h => f.isIntertwining' h.val }
  have hzero : Coinvariants.map _ _ fH (Coinvariants.mk _ v) = 0 :=
    (Coinvariants.mk_eq_zero _).mpr hv
  have hk : v ∈ Coinvariants.ker (ρ.comp H.subtype) :=
    (Coinvariants.mk_eq_zero _).mp
      ((injective_iff_map_eq_zero _).mp (FiniteAverage.map_injective _ _ fH hf) _ hzero)
  apply (Coinvariants.mk_eq_zero ρ).mpr
  apply (show Coinvariants.ker (ρ.comp H.subtype) ≤ Coinvariants.ker ρ from ?_) hk
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨h, w⟩, rfl⟩
  exact Coinvariants.sub_mem_ker (ρ := ρ) h.val w

end

noncomputable section
open Classical CategoryTheory CategoryTheory.Limits Representation
universe u
variable {G : Type u} [Group G] (N : Subgroup G) [N.Normal]

namespace RelativeCoinvariants

abbrev functor : Rep.{u} ℚ G ⥤ Rep ℚ (G ⧸ N) :=
  Rep.quotientToCoinvariantsFunctor ℚ N

@[simp] lemma map_mk {A B : Rep.{u} ℚ G} (f : A ⟶ B) (x : A) :
    ((functor N).map f).hom (Coinvariants.mk _ x) = Coinvariants.mk _ (f.hom x) := rfl

instance : (functor N).Additive where
  map_add {A B} f g := by
    ext x
    induction x using Coinvariants.induction_on with | h x =>
    change Coinvariants.mk (B.ρ.comp N.subtype) (f.hom x + g.hom x) = _
    exact map_add _ _ _

def unit (A : Rep.{u} ℚ G) :
    A ⟶ Rep.res (QuotientGroup.mk' N) ((functor N).obj A) :=
  Rep.toCoinvariantsMkQ A N

def counit (B : Rep.{u} ℚ (G ⧸ N)) :
    (functor N).obj (Rep.res (QuotientGroup.mk' N) B) ⟶ B :=
  Rep.ofHom
    { toLinearMap := Coinvariants.lift _ LinearMap.id (by
        intro g
        ext x
        change B.ρ (QuotientGroup.mk' N g.val) x = x
        have hg : QuotientGroup.mk' N g.val = 1 := (QuotientGroup.eq_one_iff _).mpr g.property
        rw [hg, map_one]
        rfl)
      isIntertwining' := by
        intro g
        induction g using QuotientGroup.induction_on with | H g =>
        ext x
        rfl }

@[simp] lemma unit_apply (A : Rep.{u} ℚ G) (x : A) :
    (unit N A).hom x = Coinvariants.mk _ x := rfl
@[simp] lemma counit_mk (B : Rep.{u} ℚ (G ⧸ N)) (x : B) :
    (counit N B).hom (Coinvariants.mk _ x) = x := rfl

def adjunction : functor N ⊣ Rep.resFunctor (QuotientGroup.mk' N) where
  unit :=
    { app := unit N
      naturality := by intros; ext x; rfl }
  counit :=
    { app := counit N
      naturality := by
        intro A B f
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        apply LinearMap.ext
        intro x
        induction x using Coinvariants.induction_on with | h x => rfl }
  left_triangle_components A := by
    ext x
    induction x using Coinvariants.induction_on with | h x => rfl
  right_triangle_components B := by ext x; rfl

instance : (functor N).IsLeftAdjoint := (adjunction N).isLeftAdjoint
instance : (functor N).PreservesProjectiveObjects :=
  Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms (adjunction N)

lemma preservesMonomorphisms (hN : LocallyFinite N) :
    (functor N).PreservesMonomorphisms where
  preserves {A B} f hf := by
    apply (Rep.mono_iff_injective _).mpr
    exact locallyFinite_coinvariants_injective hN (A.ρ.comp N.subtype)
      (B.ρ.comp N.subtype) (Rep.resMap N.subtype f).hom
      ((Rep.mono_iff_injective f).mp hf)

lemma preservesHomology (hN : LocallyFinite N) :
    (functor N).PreservesHomology := by
  let := preservesMonomorphisms N hN
  exact Functor.preservesHomology_of_preservesMonos_and_cokernels _

end RelativeCoinvariants
end

noncomputable section
open Classical CategoryTheory CategoryTheory.Limits Representation Rep
open MonoidalCategory BraidedCategory

namespace RelativeCoinvariants
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

def inductionIso : Rep.indFunctor ℚ (QuotientGroup.mk' N) ≅ functor N :=
  (Rep.indResAdjunction ℚ (QuotientGroup.mk' N)).leftAdjointUniq (adjunction N)

variable {H : Type} [Group H] (q : G →* H) (A : Rep ℚ H)

def projectionRight :
    Rep.indFunctor ℚ q ⋙ (Rep.coinvariantsTensor ℚ H).flip.obj A ≅
      (Rep.coinvariantsTensor ℚ G).flip.obj (Rep.res q A) :=
  NatIso.ofComponents (fun B => Rep.coinvariantsTensorIndIso q B A) (by
    intro B C f
    apply Rep.coinvariantsTensor_hom_ext
    apply Representation.IndV.hom_ext
    intro h
    ext b a
    simp [Rep.coinvariantsTensorIndHom, Rep.coinvariantsTensorMk,
      Rep.indMap])

def tensorSymmetry {K : Type} [Group K] (B : Rep ℚ K) :
    (Rep.coinvariantsTensor ℚ K).obj B ≅
      (Rep.coinvariantsTensor ℚ K).flip.obj B :=
  Functor.isoWhiskerRight (tensorLeftIsoTensorRight B) (Rep.coinvariantsFunctor ℚ K)

def projection :
    (Rep.coinvariantsTensor ℚ G).obj (Rep.res q A) ≅
      Rep.indFunctor ℚ q ⋙ (Rep.coinvariantsTensor ℚ H).obj A :=
  tensorSymmetry (Rep.res q A) ≪≫ (projectionRight q A).symm ≪≫
    Functor.isoWhiskerLeft (Rep.indFunctor ℚ q) (tensorSymmetry A).symm

def quotientProjection (B : Rep ℚ (G ⧸ N)) :
    (Rep.coinvariantsTensor ℚ G).obj (Rep.res (QuotientGroup.mk' N) B) ≅
      functor N ⋙ (Rep.coinvariantsTensor ℚ (G ⧸ N)).obj B :=
  projection (QuotientGroup.mk' N) B ≪≫
    Functor.isoWhiskerRight (inductionIso N) ((Rep.coinvariantsTensor ℚ (G ⧸ N)).obj B)

def trivialIso : (functor N).obj (Rep.trivial ℚ G ℚ) ≅ Rep.trivial ℚ (G ⧸ N) ℚ where
  hom := counit N (Rep.trivial ℚ (G ⧸ N) ℚ)
  inv := Rep.ofHom
    { toLinearMap := Coinvariants.mk _
      isIntertwining' := by
        intro g
        induction g using QuotientGroup.induction_on with | H g => rfl }
  hom_inv_id := by
    ext x
    induction x using Coinvariants.induction_on with | h x => rfl
  inv_hom_id := by ext; rfl

end RelativeCoinvariants
end
end SourceBurnside.Stability

end OAI
