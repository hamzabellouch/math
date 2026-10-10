import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.PolygonAction

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
section PolygonFullGroup

attribute [local instance] Classical.propDecidable

abbrev TrackPoint (a m : ℕ) := Fin m × GenericSquare a

structure TableChart (a m : ℕ) where
  source : Fin m
  target : Fin m
  shift : CutRing × CutRing
  domain : polygonAlgebra a

def TableChart.Holds {a m : ℕ} (c : TableChart a m) (f : TrackPoint a m → TrackPoint a m) : Prop :=
  ∀ x ∈ c.domain.val, f (c.source, x) = (c.target, translate a c.shift x)

def TableChart.Contains {a m : ℕ} (c : TableChart a m) (p : TrackPoint a m) : Prop :=
  p.1 = c.source ∧ p.2 ∈ c.domain.val

def HasTranslationTable {a m : ℕ} (f : TrackPoint a m → TrackPoint a m) : Prop :=
  ∃ s : Finset (TableChart a m),
    (∀ c ∈ s, c.Holds f) ∧ (∀ p, ∃ c ∈ s, c.Contains p)

private def identityChart (a m : ℕ) (i : Fin m) : TableChart a m :=
  ⟨i, i, 0, ⟨Set.univ, BooleanSubalgebra.top_mem⟩⟩

theorem identity_hasTable (a m : ℕ) : HasTranslationTable (id : TrackPoint a m → TrackPoint a m) := by
  classical
  refine ⟨Finset.univ.image (identityChart a m), ?_, ?_⟩
  · intro c hc
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
    intro x _
    simp [identityChart]
  · intro p
    exact ⟨identityChart a m p.1, Finset.mem_image.mpr ⟨p.1, Finset.mem_univ _, rfl⟩,
      rfl, Set.mem_univ _⟩

noncomputable def TableChart.comp {a m : ℕ} (c d : TableChart a m) : TableChart a m :=
  ⟨d.source, c.target, c.shift + d.shift,
    ⟨d.domain.val ∩ translate a d.shift ⁻¹' c.domain.val,
      BooleanSubalgebra.inf_mem d.domain.property (polygon_preimage_translate _ c.domain.property)⟩⟩

theorem TableChart.comp_holds {a m : ℕ} {c d : TableChart a m}
    {f g : TrackPoint a m → TrackPoint a m}
    (hc : c.Holds f) (hd : d.Holds g) (hcd : c.source = d.target) :
    (c.comp d).Holds (f ∘ g) := by
  intro x hx
  change f (g (d.source, x)) = (c.target, translate a (c.shift + d.shift) x)
  rw [hd x hx.1, ← hcd, hc _ hx.2, translate_add]

theorem comp_hasTable {a m : ℕ} {f g : TrackPoint a m → TrackPoint a m}
    (hf : HasTranslationTable f) (hg : HasTranslationTable g) : HasTranslationTable (f ∘ g) := by
  classical
  obtain ⟨s, hs, hscover⟩ := hf
  obtain ⟨t, ht, htcover⟩ := hg
  let pairs := (s ×ˢ t).filter (fun cd => cd.1.source = cd.2.target)
  refine ⟨pairs.image (fun cd => cd.1.comp cd.2), ?_, ?_⟩
  · intro e he
    obtain ⟨⟨c, d⟩, hcd, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hmem, hmatch⟩ := Finset.mem_filter.mp hcd
    obtain ⟨hc, hd⟩ := Finset.mem_product.mp hmem
    exact TableChart.comp_holds (hs c hc) (ht d hd) hmatch
  · intro p
    obtain ⟨d, hd, hp⟩ := htcover p
    obtain ⟨c, hc, hgp⟩ := hscover (g p)
    have hdvalue : g p = (d.target, translate a d.shift p.2) := by
      convert ht d hd p.2 hp.2 using 1
      exact congrArg g (Prod.ext hp.1 rfl : p = (d.source, p.2))
    have hmatch : c.source = d.target := by
      rw [hdvalue] at hgp
      exact hgp.1.symm
    refine ⟨c.comp d, Finset.mem_image.mpr ⟨(c,d), ?_, rfl⟩, hp.1, hp.2, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hc,hd⟩, hmatch⟩
    · change translate a d.shift p.2 ∈ c.domain.val
      simpa only [hdvalue] using hgp.2

noncomputable def TableChart.inverse {a m : ℕ} (c : TableChart a m) : TableChart a m :=
  ⟨c.target, c.source, -c.shift,
    ⟨translation a c.shift '' c.domain.val, polygon_image_translation _ c.domain.property⟩⟩

theorem inverse_hasTable {a m : ℕ} (f : Equiv.Perm (TrackPoint a m))
    (hf : HasTranslationTable f) : HasTranslationTable f.symm := by
  classical
  obtain ⟨s, hs, hcover⟩ := hf
  refine ⟨s.image TableChart.inverse, ?_, ?_⟩
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    change f.symm (d.target, translate a d.shift x) =
      (d.source, translate a (-d.shift) (translate a d.shift x))
    rw [← hs d hd x hx, f.symm_apply_apply, ← translate_add, neg_add_cancel, translate_zero]
  · intro p
    obtain ⟨c, hc, hp⟩ := hcover (f.symm p)
    have hvalue : f (c.source, (f.symm p).2) =
        (c.target, translate a c.shift (f.symm p).2) := hs c hc _ hp.2
    have hpair : (c.source, (f.symm p).2) = f.symm p := Prod.ext hp.1.symm rfl
    rw [hpair, f.apply_symm_apply] at hvalue
    refine ⟨c.inverse, Finset.mem_image.mpr ⟨c,hc,rfl⟩, ?_, ?_⟩
    · exact congrArg Prod.fst hvalue
    · exact ⟨(f.symm p).2, hp.2, (congrArg Prod.snd hvalue).symm⟩

noncomputable def polygonFullGroup (a m : ℕ) : Subgroup (Equiv.Perm (TrackPoint a m)) where
  carrier := {f | HasTranslationTable f}
  one_mem' := identity_hasTable a m
  mul_mem' := comp_hasTable
  inv_mem' := fun {f} h => inverse_hasTable f h

noncomputable def SlotMap (a m : ℕ) (U : polygonAlgebra a) {n : ℕ}
    (slots : Fin n → Fin m × (CutRing × CutRing)) :
    Fin n × U.val → TrackPoint a m :=
  fun ix => ((slots ix.1).1, translate a (slots ix.1).2 ix.2.val)

def IsThreeSlotCycle {a m : ℕ} (g : polygonFullGroup a m) : Prop :=
  ∃ (U : polygonAlgebra a) (slots : Fin 3 → Fin m × (CutRing × CutRing)),
    U.val.Nonempty ∧ Function.Injective (SlotMap a m U slots) ∧
    (∀ (i : Fin 3) (x : U.val),
      g.val (SlotMap a m U slots (i,x)) = SlotMap a m U slots (i+1,x)) ∧
    (∀ p ∉ Set.range (SlotMap a m U slots), g.val p = p)

noncomputable def polygonAlternatingGroup (a m : ℕ) : Subgroup (polygonFullGroup a m) :=
  Subgroup.closure {g | IsThreeSlotCycle g}

noncomputable def conditionalPerm {a m : ℕ} (U : polygonAlgebra a)
    (σ : Equiv.Perm (Fin m)) : Equiv.Perm (TrackPoint a m) := by
  classical
  exact {
    toFun := fun p => (if p.2 ∈ U.val then σ p.1 else p.1, p.2)
    invFun := fun p => (if p.2 ∈ U.val then σ.symm p.1 else p.1, p.2)
    left_inv := by intro p; by_cases h : p.2 ∈ U.val <;> simp [h]
    right_inv := by intro p; by_cases h : p.2 ∈ U.val <;> simp [h] }

@[simp] theorem conditionalPerm_apply {a m : ℕ} (U : polygonAlgebra a)
    (σ : Equiv.Perm (Fin m)) (p : TrackPoint a m) :
    conditionalPerm U σ p = (if p.2 ∈ U.val then σ p.1 else p.1, p.2) := by
  classical
  rfl

private noncomputable def conditionalChart {a m : ℕ} (U : polygonAlgebra a)
    (σ : Equiv.Perm (Fin m)) (b : Bool) (i : Fin m) : TableChart a m :=
  ⟨i, if b then σ i else i, 0,
    if b then U else ⟨U.valᶜ, BooleanSubalgebra.compl_mem U.property⟩⟩

theorem conditional_hasTable {a m : ℕ} (U : polygonAlgebra a)
    (σ : Equiv.Perm (Fin m)) : HasTranslationTable (conditionalPerm U σ) := by
  classical
  refine ⟨Finset.univ.image (fun bi : Bool × Fin m => conditionalChart U σ bi.1 bi.2), ?_, ?_⟩
  · intro c hc
    obtain ⟨⟨b,i⟩, _, rfl⟩ := Finset.mem_image.mp hc
    cases b <;> intro x hx
    · change x ∉ U.val at hx
      simp [conditionalChart, hx]
    · change x ∈ U.val at hx
      simp [conditionalChart, hx]
  · intro p
    by_cases hp : p.2 ∈ U.val
    · refine ⟨conditionalChart U σ true p.1, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨(true,p.1), Finset.mem_univ _,rfl⟩
      · exact ⟨rfl,hp⟩
    · refine ⟨conditionalChart U σ false p.1, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨(false,p.1), Finset.mem_univ _,rfl⟩
      · exact ⟨rfl,hp⟩

noncomputable def conditionalHom {a m : ℕ} (U : polygonAlgebra a) :
    Equiv.Perm (Fin m) →* polygonFullGroup a m where
  toFun σ := ⟨conditionalPerm U σ, conditional_hasTable U σ⟩
  map_one' := by
    apply Subtype.ext
    apply Equiv.ext
    intro p
    change conditionalPerm U 1 p = p
    simp
  map_mul' σ ρ := by
    apply Subtype.ext
    apply Equiv.ext
    intro p
    change conditionalPerm U (σ * ρ) p = conditionalPerm U σ (conditionalPerm U ρ p)
    by_cases hp : p.2 ∈ U.val <;> simp [hp]

noncomputable def slotPerm {a m n : ℕ} (U : polygonAlgebra a)
    (slots : Fin n → Fin m × (CutRing × CutRing))
    (hinj : Function.Injective (SlotMap a m U slots))
    (σ : Equiv.Perm (Fin n)) : Equiv.Perm (TrackPoint a m) :=
  Equiv.Perm.viaEmbedding (Equiv.prodCongr σ (Equiv.refl U.val)) ⟨SlotMap a m U slots, hinj⟩

theorem slotPerm_apply {a m n : ℕ} (U : polygonAlgebra a)
    (slots : Fin n → Fin m × (CutRing × CutRing))
    (hinj : Function.Injective (SlotMap a m U slots)) (σ : Equiv.Perm (Fin n))
    (i : Fin n) (x : U.val) :
    slotPerm U slots hinj σ (SlotMap a m U slots (i,x)) =
      SlotMap a m U slots (σ i,x) :=
  Equiv.Perm.viaEmbedding_apply _ _ _

theorem slotPerm_apply_of_notMem {a m n : ℕ} (U : polygonAlgebra a)
    (slots : Fin n → Fin m × (CutRing × CutRing))
    (hinj : Function.Injective (SlotMap a m U slots)) (σ : Equiv.Perm (Fin n))
    {p : TrackPoint a m} (hp : p ∉ Set.range (SlotMap a m U slots)) :
    slotPerm U slots hinj σ p = p :=
  Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hp

private noncomputable def slotChart {a m n : ℕ} (U : polygonAlgebra a)
    (slots : Fin n → Fin m × (CutRing × CutRing)) (σ : Equiv.Perm (Fin n))
    (i : Fin n) : TableChart a m :=
  ⟨(slots i).1, (slots (σ i)).1, (slots (σ i)).2 - (slots i).2,
    ⟨translate a (slots i).2 '' U.val, polygon_image_translation _ U.property⟩⟩

private def slotVoid {a m n : ℕ} (U : polygonAlgebra a)
    (slots : Fin n → Fin m × (CutRing × CutRing)) (i : Fin m) :
    Set (GenericSquare a) :=
  (⋃ j : Fin n, ⋃ (_ : (slots j).1 = i), translate a (slots j).2 '' U.val)ᶜ

private theorem slotVoid_mem {a m n : ℕ} (U : polygonAlgebra a)
    (slots : Fin n → Fin m × (CutRing × CutRing)) (i : Fin m) :
    slotVoid U slots i ∈ polygonAlgebra a := by
  apply BooleanSubalgebra.compl_mem
  apply BooleanSubalgebra.iSup_mem
  intro j
  apply BooleanSubalgebra.iSup_mem
  intro _
  exact polygon_image_translation _ U.property

private theorem mem_slotVoid {a m n : ℕ} (U : polygonAlgebra a)
    (slots : Fin n → Fin m × (CutRing × CutRing)) (p : TrackPoint a m) :
    p.2 ∈ slotVoid U slots p.1 ↔ p ∉ Set.range (SlotMap a m U slots) := by
  simp only [slotVoid, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_image, Set.mem_range]
  constructor
  · rintro h ⟨⟨i,x⟩, he⟩
    apply h
    exact ⟨i, congrArg Prod.fst he, x.val, x.property, congrArg Prod.snd he⟩
  · rintro h ⟨i, hi, x, hx, he⟩
    apply h
    exact ⟨(i,⟨x,hx⟩), Prod.ext hi he⟩

private noncomputable def slotVoidChart {a m n : ℕ} (U : polygonAlgebra a)
    (slots : Fin n → Fin m × (CutRing × CutRing)) (i : Fin m) : TableChart a m :=
  ⟨i,i,0,⟨slotVoid U slots i, slotVoid_mem U slots i⟩⟩

theorem slotPerm_hasTable {a m n : ℕ} (U : polygonAlgebra a)
    (slots : Fin n → Fin m × (CutRing × CutRing))
    (hinj : Function.Injective (SlotMap a m U slots)) (σ : Equiv.Perm (Fin n)) :
    HasTranslationTable (slotPerm U slots hinj σ) := by
  classical
  refine ⟨(Finset.univ.image (slotChart U slots σ)) ∪
    (Finset.univ.image (slotVoidChart U slots)), ?_, ?_⟩
  · intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      change slotPerm U slots hinj σ (SlotMap a m U slots (i,⟨y,hy⟩)) = _
      rw [slotPerm_apply]
      change ((slots (σ i)).1, translate a (slots (σ i)).2 y) =
        ((slots (σ i)).1, translate a ((slots (σ i)).2 - (slots i).2)
          (translate a (slots i).2 y))
      rw [← translate_add]
      simp
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
      intro x hx
      change slotPerm U slots hinj σ (i,x) = (i,translate a 0 x)
      rw [translate_zero]
      exact slotPerm_apply_of_notMem U slots hinj σ ((mem_slotVoid U slots (i,x)).mp hx)
  · intro p
    by_cases hp : p ∈ Set.range (SlotMap a m U slots)
    · obtain ⟨⟨i,x⟩, rfl⟩ := hp
      refine ⟨slotChart U slots σ i, Finset.mem_union_left _ ?_, rfl, ?_⟩
      · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      · exact ⟨x.val, x.property, rfl⟩
    · refine ⟨slotVoidChart U slots p.1, Finset.mem_union_right _ ?_, rfl, ?_⟩
      · exact Finset.mem_image.mpr ⟨p.1, Finset.mem_univ _, rfl⟩
      · exact (mem_slotVoid U slots p).mpr hp

noncomputable def slotHom {a m n : ℕ} (U : polygonAlgebra a)
    (slots : Fin n → Fin m × (CutRing × CutRing))
    (hinj : Function.Injective (SlotMap a m U slots)) :
    Equiv.Perm (Fin n) →* polygonFullGroup a m where
  toFun σ := ⟨slotPerm U slots hinj σ, slotPerm_hasTable U slots hinj σ⟩
  map_one' := by
    apply Subtype.ext
    apply Equiv.ext
    intro p
    by_cases hp : p ∈ Set.range (SlotMap a m U slots)
    · obtain ⟨⟨i,x⟩, rfl⟩ := hp
      exact slotPerm_apply U slots hinj 1 i x
    · exact slotPerm_apply_of_notMem U slots hinj 1 hp
  map_mul' σ ρ := by
    apply Subtype.ext
    apply Equiv.ext
    intro p
    change slotPerm U slots hinj (σ * ρ) p =
      slotPerm U slots hinj σ (slotPerm U slots hinj ρ p)
    by_cases hp : p ∈ Set.range (SlotMap a m U slots)
    · obtain ⟨⟨i,x⟩, rfl⟩ := hp
      simp only [slotPerm_apply, Equiv.Perm.mul_apply]
    · simp only [slotPerm_apply_of_notMem U slots hinj _ hp]

theorem SlotMap_injective_mono {a m n : ℕ} {U V : polygonAlgebra a}
    (slots : Fin n → Fin m × (CutRing × CutRing)) (hVU : V.val ⊆ U.val)
    (hU : Function.Injective (SlotMap a m U slots)) :
    Function.Injective (SlotMap a m V slots) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ he
  have ht := hU (show SlotMap a m U slots (i,⟨x.val,hVU x.property⟩) =
    SlotMap a m U slots (j,⟨y.val,hVU y.property⟩) from he)
  exact Prod.ext (congrArg (fun p : Fin n × U.val => p.1) ht)
    (Subtype.ext (congrArg (fun p => p.2.val) ht))

private noncomputable def polygonInter {a : ℕ} (U V : polygonAlgebra a) : polygonAlgebra a :=
  ⟨U.val ∩ V.val, BooleanSubalgebra.inf_mem U.property V.property⟩

private noncomputable def polygonDiff {a : ℕ} (U V : polygonAlgebra a) : polygonAlgebra a :=
  ⟨U.val \ V.val, BooleanSubalgebra.inf_mem U.property (BooleanSubalgebra.compl_mem V.property)⟩

private theorem slotPerm_restrict_apply {a m n : ℕ} {U V : polygonAlgebra a}
    (slots : Fin n → Fin m × (CutRing × CutRing)) (hVU : V.val ⊆ U.val)
    (hU : Function.Injective (SlotMap a m U slots)) (σ : Equiv.Perm (Fin n))
    (i : Fin n) (x : U.val) :
    slotPerm V slots (SlotMap_injective_mono slots hVU hU) σ (SlotMap a m U slots (i,x)) =
      if x.val ∈ V.val then SlotMap a m U slots (σ i,x) else SlotMap a m U slots (i,x) := by
  classical
  split_ifs with hx
  · exact slotPerm_apply V slots _ σ i ⟨x.val,hx⟩
  · apply slotPerm_apply_of_notMem
    rintro ⟨⟨j,y⟩,he⟩
    have ht := hU (show SlotMap a m U slots (j,⟨y.val,hVU y.property⟩) =
      SlotMap a m U slots (i,x) from he)
    have hyx : y.val = x.val := congrArg (fun p => p.2.val) ht
    exact hx (hyx ▸ y.property)

theorem slotHom_split {a m n : ℕ} (U V : polygonAlgebra a)
    (slots : Fin n → Fin m × (CutRing × CutRing))
    (hU : Function.Injective (SlotMap a m U slots)) (σ : Equiv.Perm (Fin n)) :
    slotHom U slots hU σ =
      slotHom (polygonInter U V) slots (SlotMap_injective_mono slots (fun _ h => h.1) hU) σ *
      slotHom (polygonDiff U V) slots (SlotMap_injective_mono slots (fun _ h => h.1) hU) σ := by
  classical
  apply Subtype.ext
  apply Equiv.ext
  intro p
  change slotPerm U slots hU σ p =
    slotPerm (polygonInter U V) slots _ σ (slotPerm (polygonDiff U V) slots _ σ p)
  by_cases hp : p ∈ Set.range (SlotMap a m U slots)
  · obtain ⟨⟨i,x⟩,rfl⟩ := hp
    rw [slotPerm_apply, slotPerm_restrict_apply slots (V := polygonDiff U V) (fun _ h => h.1) hU σ]
    by_cases hx : x.val ∈ V.val
    · simp only [polygonDiff, Set.mem_sdiff, x.property, hx, not_true_eq_false, and_false,
        ↓reduceIte]
      rw [slotPerm_restrict_apply slots (V := polygonInter U V) (fun _ h => h.1) hU σ]
      simp [polygonInter, x.property, hx]
    · simp only [polygonDiff, Set.mem_sdiff, x.property, hx, not_false_eq_true, and_self,
        ↓reduceIte]
      rw [slotPerm_restrict_apply slots (V := polygonInter U V) (fun _ h => h.1) hU σ]
      simp [polygonInter, x.property, hx]
  · have hout (W : polygonAlgebra a) (hW : W.val ⊆ U.val) : p ∉ Set.range (SlotMap a m W slots) := by
      rintro ⟨⟨i,x⟩,he⟩
      exact hp ⟨(i,⟨x.val,hW x.property⟩),he⟩
    rw [slotPerm_apply_of_notMem _ _ _ _ hp,
      slotPerm_apply_of_notMem _ _ _ _ (hout (polygonDiff U V) (fun _ h => h.1)),
      slotPerm_apply_of_notMem _ _ _ _ (hout (polygonInter U V) (fun _ h => h.1))]

theorem slotHom_empty {a m n : ℕ} (U : polygonAlgebra a)
    (slots : Fin n → Fin m × (CutRing × CutRing))
    (hU : Function.Injective (SlotMap a m U slots)) (σ : Equiv.Perm (Fin n))
    (h_empty : U.val = ∅) : slotHom U slots hU σ = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro p
  apply slotPerm_apply_of_notMem
  rintro ⟨⟨i,x⟩,_⟩
  simpa [h_empty] using x.property

theorem slotHom_of_finite_cover {a m n : ℕ} {β : Type*}
    (s : Finset β) (cover : β → polygonAlgebra a) (U : polygonAlgebra a)
    (slots : Fin n → Fin m × (CutRing × CutRing))
    (hU : Function.Injective (SlotMap a m U slots)) (σ : Equiv.Perm (Fin n))
    (N : Subgroup (polygonFullGroup a m))
    (hcover : ∀ x ∈ U.val, ∃ b ∈ s, x ∈ (cover b).val)
    (hlocal : ∀ b ∈ s, ∀ V : polygonAlgebra a, ∀ hV : V.val ⊆ U.val,
      V.val ⊆ (cover b).val →
      slotHom V slots (SlotMap_injective_mono slots hV hU) σ ∈ N) :
    slotHom U slots hU σ ∈ N := by
  classical
  induction s using Finset.induction_on generalizing U with
  | empty =>
      have hu : U.val = ∅ := Set.eq_empty_iff_forall_notMem.mpr (by
        intro x hx
        obtain ⟨b,hb,_⟩ := hcover x hx
        simp at hb)
      rw [slotHom_empty U slots hU σ hu]
      exact N.one_mem
  | @insert b s hb ih =>
      rw [slotHom_split U (cover b) slots hU σ]
      apply N.mul_mem
      · exact hlocal b (Finset.mem_insert_self ..) (polygonInter U (cover b)) (fun _ h => h.1) (fun _ h => h.2)
      · apply ih
        · intro x hx
          obtain ⟨c,hc,hxc⟩ := hcover x hx.1
          rcases Finset.mem_insert.mp hc with rfl | hc
          · exact (hx.2 hxc).elim
          · exact ⟨c,hc,hxc⟩
        · intro c hc V hV hVc
          exact hlocal c (Finset.mem_insert_of_mem hc) V (fun x hx => (hV hx).1) hVc

theorem slotHom_conjugate {a m n : ℕ} (U : polygonAlgebra a)
    (slots targets : Fin n → Fin m × (CutRing × CutRing))
    (hU : Function.Injective (SlotMap a m U slots))
    (hT : Function.Injective (SlotMap a m U targets))
    (g : polygonFullGroup a m)
    (htransport : ∀ (i : Fin n) (x : U.val),
      g.val (SlotMap a m U slots (i,x)) = SlotMap a m U targets (i,x))
    (σ : Equiv.Perm (Fin n)) :
    g * slotHom U slots hU σ * g⁻¹ = slotHom U targets hT σ := by
  apply Subtype.ext
  apply Equiv.ext
  intro y
  obtain ⟨p,rfl⟩ := g.val.surjective y
  change g.val (slotPerm U slots hU σ (g.val.symm (g.val p))) =
    slotPerm U targets hT σ (g.val p)
  rw [g.val.symm_apply_apply]
  by_cases hp : p ∈ Set.range (SlotMap a m U slots)
  · obtain ⟨⟨i,x⟩,rfl⟩ := hp
    rw [slotPerm_apply, htransport, htransport, slotPerm_apply]
  · have hout : g.val p ∉ Set.range (SlotMap a m U targets) := by
      rintro ⟨⟨i,x⟩,he⟩
      rw [← htransport] at he
      exact hp ⟨(i,x),g.val.injective he⟩
    rw [slotPerm_apply_of_notMem U slots hU σ hp,
      slotPerm_apply_of_notMem U targets hT σ hout]

end PolygonFullGroup
end SimpleAmenable
end
end

end OAI
