import Mathlib
import OAI.CategoryTheory.Thomason.AlexanderWhitney

namespace OAI

/-! Linearization. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

def op (C : OmegaCategory.{u}) : OmegaCategory.{u} where
  Cell := C.Cell
  source := C.target
  target := C.source
  source_source := C.target_target
  target_target := C.source_source
  source_target := C.target_source
  target_source := C.source_target
  comp k x y h := C.comp k y x h.symm
  source_comp_le i k hik x y h := C.target_comp_le i k hik y x h.symm
  target_comp_le i k hik x y h := C.source_comp_le i k hik y x h.symm
  source_comp_gt i k hki x y h hs :=
    C.target_comp_gt i k hki y x h.symm hs.symm
  target_comp_gt i k hki x y h ht :=
    C.source_comp_gt i k hki y x h.symm ht.symm
  unit_left k x h := C.unit_right k x h.symm
  unit_right k x h := C.unit_left k x h.symm
  assoc k x y z hxy hyz hxy_z hx_yz :=
    (C.assoc k z y x hyz.symm hxy.symm hx_yz.symm hxy_z.symm).symm
  interchange k l hkl a b c d hab hcd hac hbd hab_cd hac_bd :=
    C.interchange k l hkl d c b a hcd.symm hab.symm hbd.symm hac.symm
      hab_cd.symm hac_bd.symm
  finite_dimension x := by
    obtain ⟨k, hk⟩ := C.finite_dimension x
    exact ⟨k, C.target_eq_self_of_source_eq_self hk⟩

@[simp] lemma op_op (C : OmegaCategory.{u}) : C.op.op = C := rfl

def Functor.op {C : OmegaCategory.{u}} {D : OmegaCategory.{v}} (F : Functor C D) :
    Functor C.op D.op where
  map := F.map
  map_source := F.map_target
  map_target := F.map_source
  map_comp k x y h h' := F.map_comp k y x h.symm h'.symm

@[simp] lemma Functor.op_op {C : OmegaCategory.{u}} {D : OmegaCategory.{v}}
    (F : Functor C D) : F.op.op = F := rfl

@[simp] lemma Functor.op_id (C : OmegaCategory.{u}) : (Functor.id C).op = Functor.id C.op := rfl

@[simp] lemma Functor.op_comp {C : OmegaCategory.{u}} {D : OmegaCategory.{v}}
    {E : OmegaCategory.{w}} (F : Functor C D) (G : Functor D E) :
    (Functor.comp F G).op = Functor.comp F.op G.op := rfl

lemma op_truncated {C : OmegaCategory.{u}} {n : ℕ} (h : C.IsTruncated n) :
    C.op.IsTruncated n := fun x => C.target_eq_self_of_source_eq_self (h x)

def opFunctor : CategoryTheory.Functor OmegaCategory.{u} OmegaCategory.{u} where
  obj := op
  map := Functor.op

def opEquivalence : CategoryTheory.Equivalence OmegaCategory.{u} OmegaCategory.{u} where
  functor := opFunctor
  inverse := opFunctor
  unitIso := CategoryTheory.Iso.refl _
  counitIso := CategoryTheory.Iso.refl _

def intervalReflect : Functor interval.{u}.op interval.{u} where
  map x := ⟨⟨x.right.down.rev⟩, ⟨x.left.down.rev⟩, by
    exact Fin.rev_le_rev.mpr x.related⟩
  map_source k x := by cases k <;> rfl
  map_target k x := by cases k <;> rfl
  map_comp k x y h h' := by
    cases k with
    | zero => rfl
    | succ k =>
      have he : x = y := h
      subst y
      rfl

@[simp] lemma intervalReflect_vertex (a : Fin 2) :
    intervalReflect.map (intervalVertex a).val = (intervalVertex a.rev).val := rfl

@[simp] lemma intervalReflect_arrow : intervalReflect.map intervalArrow = intervalArrow := rfl

@[simp] lemma intervalReflect_involutive (x : interval.{u}.Cell) :
    intervalReflect.map (intervalReflect.map x) = x := by
  rcases x with ⟨⟨a⟩, ⟨b⟩, h⟩
  simp only [intervalReflect, Fin.rev_rev]
  rfl

lemma intervalReflect_injective : Function.Injective intervalReflect.{u}.map :=
  Function.LeftInverse.injective intervalReflect_involutive

def reverseLabel {C : OmegaCategory.{u}} (p : Functor C interval.{u}) :
    Functor C.op interval.{u} := Functor.comp p.op intervalReflect

@[simp] lemma reverseLabel_reverseLabel {C : OmegaCategory.{u}} (p : Functor C interval.{u}) :
    reverseLabel (reverseLabel p) = p := by
  apply Functor.ext
  funext x
  exact intervalReflect_involutive (p.map x)

open CategoryTheory

def reverseLabelFunctor : CategoryTheory.Functor (Over interval.{u}) (Over interval.{u}) where
  obj p := Over.mk (reverseLabel p.hom)
  map {p q} F := Over.homMk (Thomason.OmegaCategory.Functor.op F.left) (by
    apply Functor.ext
    funext x
    have he := congrArg (fun f : Thomason.OmegaCategory.Functor p.left interval => f.map x) (Over.w F)
    exact congrArg intervalReflect.map he)
  map_id p := by apply Over.OverMorphism.ext; rfl
  map_comp F G := by apply Over.OverMorphism.ext; rfl

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory

def reverseLabelTwiceIso : reverseLabelFunctor.{u} ⋙ reverseLabelFunctor ≅ 𝟭 _ :=
  NatIso.ofComponents (fun p => Over.isoMk (Iso.refl p.left) (by
    change p.hom = reverseLabel (reverseLabel p.hom)
    exact (reverseLabel_reverseLabel p.hom).symm)) (by
      intro p q F
      apply Over.OverMorphism.ext
      rfl)

def reverseLabelEquivalence : (Over interval.{u}) ≌ (Over interval.{u}) where
  functor := reverseLabelFunctor
  inverse := reverseLabelFunctor
  unitIso := reverseLabelTwiceIso.symm
  counitIso := reverseLabelTwiceIso
  functor_unitIso_comp p := by
    apply Over.OverMorphism.ext
    rfl

instance reverseLabelFunctor_isEquivalence : reverseLabelFunctor.{u}.IsEquivalence :=
  reverseLabelEquivalence.isEquivalence_functor

instance opFunctor_isEquivalence : opFunctor.{u}.IsEquivalence :=
  opEquivalence.isEquivalence_functor

def reversedZeroFiberIso (p : Over interval.{u}) :
    ((fiberFunctor (intervalVertex 0)).obj (reverseLabelFunctor.obj p)).op ≅
      (fiberFunctor (intervalVertex 1)).obj p where
  hom := {
    map := fun x => ⟨x.val, by
      apply intervalReflect_injective
      exact x.property⟩
    map_source := fun _ _ => rfl
    map_target := fun _ _ => rfl
    map_comp := fun _ _ _ _ _ => rfl }
  inv := {
    map := fun x => ⟨x.val, by
      change intervalReflect.map (p.hom.map x.val) = (intervalVertex 0).val
      rw [x.property]
      rfl⟩
    map_source := fun _ _ => rfl
    map_target := fun _ _ => rfl
    map_comp := fun _ _ _ _ _ => rfl }
  hom_inv_id := by apply Functor.ext; rfl
  inv_hom_id := by apply Functor.ext; rfl

def reversedZeroFiberNatIso :
    (reverseLabelFunctor.{u} ⋙ fiberFunctor (intervalVertex 0)) ⋙ opFunctor ≅
      fiberFunctor (intervalVertex 1) :=
  NatIso.ofComponents reversedZeroFiberIso (by
    intro p q F
    apply Functor.ext
    rfl)

noncomputable instance oneFiber_preservesColimits :
    Limits.PreservesColimitsOfSize.{v,w} (fiberFunctor.{u} (intervalVertex 1)) :=
  Limits.preservesColimits_of_natIso reversedZeroFiberNatIso

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open DirectedComplex

variable {E : Type u} [PartialOrder E]

def edgeTable (a b : E) (hab : a ≤ b) : Table (complex E) where
  row p e := match p with
    | 0 => if e then ⟨bracket [b], bracket_mem_grade [b]⟩
      else ⟨bracket [a], bracket_mem_grade [a]⟩
    | 1 => ⟨bracket [a,b], bracket_mem_grade [a,b]⟩
    | _+2 => 0
  positive p e := by
    cases p with
    | zero =>
      cases e
      · change Positive (bracket [a]); exact bracket_positive _
      · change Positive (bracket [b]); exact bracket_positive _
    | succ p => cases p with
      | zero => exact bracket_positive _
      | succ p => exact (complex E).positive (p+2) |>.zero_mem
  boundary p e := by
    cases p with
    | zero =>
      apply Subtype.ext
      change boundary (bracket [a,b]) = bracket [b] - bracket [a]
      rw [boundary_bracket (by simpa using hab)]
      simp [wordBoundary_cons, wordBoundary_nil, prepend_bracket]
    | succ p =>
      cases p with
      | zero => exact (map_zero _).trans (sub_self _).symm
      | succ p => exact (map_zero _).trans (sub_self _).symm
  augmentation e := by
    cases e <;>
      change emptyCoefficient (boundary (bracket [_])) = 1 <;>
      rw [boundary_bracket (by simp)] <;>
      simp [wordBoundary_cons, wordBoundary_nil, emptyCoefficient_bracket]
  bounded := ⟨1, by
    intro p hp e
    cases p with
    | zero => omega
    | succ p => cases p with
      | zero => omega
      | succ p => rfl⟩

lemma edgeTable_source (a b : E) (hab : a ≤ b) :
    Table.truncate 0 false (edgeTable a b hab) = vertexTable a := by
  ext p e
  cases p with
  | zero => rfl
  | succ p => simp [Table.truncate_row, vertexTable_row_pos a (by omega : 0 < p+1)]

lemma edgeTable_target (a b : E) (hab : a ≤ b) :
    Table.truncate 0 true (edgeTable a b hab) = vertexTable b := by
  ext p e
  cases p with
  | zero => rfl
  | succ p => simp [Table.truncate_row, vertexTable_row_pos b (by omega : 0 < p+1)]

lemma edgeTable_sourceObject (a b : E) (hab : a ≤ b) :
    (complex E).nu.sourceObject (edgeTable a b hab) = tableObjectsEquiv.symm a :=
  Subtype.ext (edgeTable_source a b hab)

lemma edgeTable_targetObject (a b : E) (hab : a ≤ b) :
    (complex E).nu.targetObject (edgeTable a b hab) = tableObjectsEquiv.symm b :=
  Subtype.ext (edgeTable_target a b hab)

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

def IsObjectSieve (C : OmegaCategory.{u}) (S : Set C.Objects) : Prop :=
  ∀ x : C.Cell, C.targetObject x ∈ S → C.sourceObject x ∈ S

def IsObjectCosieve (C : OmegaCategory.{u}) (S : Set C.Objects) : Prop :=
  ∀ x : C.Cell, C.sourceObject x ∈ S → C.targetObject x ∈ S

lemma isObjectSieve_iff_oneCells (C : OmegaCategory.{u}) (S : Set C.Objects) :
    C.IsObjectSieve S ↔
      ∀ x : C.Cells 1, C.targetObject x.val ∈ S → C.sourceObject x.val ∈ S := by
  constructor
  · intro h x; exact h x.val
  · intro h x hx
    simpa only [sourceObject_source_succ, targetObject_source_succ] using
      h ⟨C.source 1 x, C.source_source_self 1 x⟩ (by simpa using hx)

lemma isObjectCosieve_iff_oneCells (C : OmegaCategory.{u}) (S : Set C.Objects) :
    C.IsObjectCosieve S ↔
      ∀ x : C.Cells 1, C.sourceObject x.val ∈ S → C.targetObject x.val ∈ S := by
  constructor
  · intro h x; exact h x.val
  · intro h x hx
    simpa only [sourceObject_source_succ, targetObject_source_succ] using
      h ⟨C.source 1 x, C.source_source_self 1 x⟩ (by simpa using hx)

open NormalizedChains

lemma simplex_objects_mem_sieve {C : OmegaCategory.{u}} {m : ℕ}
    (F : Functor (Oriental m) C) {S : Set C.Objects} (hS : C.IsObjectSieve S)
    (hm : F.objects (tableObjectsEquiv.symm (Fin.last m)) ∈ S) :
    ∀ a : (Oriental m).Objects, F.objects a ∈ S := by
  intro a
  let i := tableObjectsEquiv a
  have h := hS (F.map (edgeTable i (Fin.last m) (Fin.le_last i)))
  have hs := (F.objects_source (edgeTable i (Fin.last m) (Fin.le_last i))).symm
  have ht := (F.objects_target (edgeTable i (Fin.last m) (Fin.le_last i))).symm
  have es : (Oriental m).sourceObject (edgeTable i (Fin.last m) (Fin.le_last i)) =
      tableObjectsEquiv.symm i := edgeTable_sourceObject _ _ _
  have et : (Oriental m).targetObject (edgeTable i (Fin.last m) (Fin.le_last i)) =
      tableObjectsEquiv.symm (Fin.last m) := edgeTable_targetObject _ _ _
  rw [es] at hs
  rw [et] at ht
  rw [hs, ht] at h
  have hi := h hm
  have he : tableObjectsEquiv.symm i = a :=
    (tableObjectsEquiv (E := Fin (m+1))).symm_apply_apply a
  exact he ▸ hi

lemma simplex_objects_mem_cosieve {C : OmegaCategory.{u}} {m : ℕ}
    (F : Functor (Oriental m) C) {S : Set C.Objects} (hS : C.IsObjectCosieve S)
    (h0 : F.objects (tableObjectsEquiv.symm (0 : Fin (m+1))) ∈ S) :
    ∀ a : (Oriental m).Objects, F.objects a ∈ S := by
  intro a
  let i := tableObjectsEquiv a
  have h := hS (F.map (edgeTable (0 : Fin (m+1)) i (Fin.zero_le i)))
  have hs := (F.objects_source (edgeTable (0 : Fin (m+1)) i (Fin.zero_le i))).symm
  have ht := (F.objects_target (edgeTable (0 : Fin (m+1)) i (Fin.zero_le i))).symm
  have es : (Oriental m).sourceObject (edgeTable (0 : Fin (m+1)) i (Fin.zero_le i)) =
      tableObjectsEquiv.symm (0 : Fin (m+1)) := edgeTable_sourceObject _ _ _
  have et : (Oriental m).targetObject (edgeTable (0 : Fin (m+1)) i (Fin.zero_le i)) =
      tableObjectsEquiv.symm i := edgeTable_targetObject _ _ _
  rw [es] at hs
  rw [et] at ht
  rw [hs, ht] at h
  have hi := h h0
  have he : tableObjectsEquiv.symm i = a :=
    (tableObjectsEquiv (E := Fin (m+1))).symm_apply_apply a
  exact he ▸ hi

def Functor.liftFullOn {C : OmegaCategory.{u}} {D : OmegaCategory.{v}}
    (F : Functor C D) (S : Set D.Objects)
    (h : ∀ a : C.Objects, F.objects a ∈ S) : Functor C (D.fullOn S).category :=
  (D.fullOn S).lift F (fun x => ⟨by simpa using h (C.sourceObject x),
    by simpa using h (C.targetObject x)⟩)

lemma Functor.liftFullOn_inclusion {C : OmegaCategory.{u}} {D : OmegaCategory.{v}}
    (F : Functor C D) (S : Set D.Objects) (h : ∀ a : C.Objects, F.objects a ∈ S) :
    Functor.comp (F.liftFullOn S h) (D.fullOn S).inclusion = F := rfl

lemma simplex_sieve_cover {C : OmegaCategory.{u}} {S T : Set C.Objects}
    (hS : C.IsObjectSieve S) (hT : C.IsObjectSieve T)
    (hcover : ∀ a : C.Objects, a ∈ S ∨ a ∈ T) {m : ℕ} (F : Functor (Oriental m) C) :
    (∃ G : Functor (Oriental m) (C.fullOn S).category,
      Functor.comp G (C.fullOn S).inclusion = F) ∨
    (∃ G : Functor (Oriental m) (C.fullOn T).category,
      Functor.comp G (C.fullOn T).inclusion = F) := by
  rcases hcover (F.objects (tableObjectsEquiv.symm (Fin.last m))) with h | h
  · exact Or.inl ⟨F.liftFullOn S (simplex_objects_mem_sieve F hS h), rfl⟩
  · exact Or.inr ⟨F.liftFullOn T (simplex_objects_mem_sieve F hT h), rfl⟩

lemma simplex_cosieve_cover {C : OmegaCategory.{u}} {S T : Set C.Objects}
    (hS : C.IsObjectCosieve S) (hT : C.IsObjectCosieve T)
    (hcover : ∀ a : C.Objects, a ∈ S ∨ a ∈ T) {m : ℕ} (F : Functor (Oriental m) C) :
    (∃ G : Functor (Oriental m) (C.fullOn S).category,
      Functor.comp G (C.fullOn S).inclusion = F) ∨
    (∃ G : Functor (Oriental m) (C.fullOn T).category,
      Functor.comp G (C.fullOn T).inclusion = F) := by
  rcases hcover (F.objects (tableObjectsEquiv.symm (0 : Fin (m+1)))) with h | h
  · exact Or.inl ⟨F.liftFullOn S (simplex_objects_mem_cosieve F hS h), rfl⟩
  · exact Or.inr ⟨F.liftFullOn T (simplex_objects_mem_cosieve F hT h), rfl⟩

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory Limits

def fullOnMap {C : OmegaCategory.{u}} {S T : Set C.Objects} (h : S ⊆ T) :
    Functor (C.fullOn S).category (C.fullOn T).category where
  map x := ⟨x.val, h x.property.1, h x.property.2⟩
  map_source _ _ := rfl
  map_target _ _ := rfl
  map_comp _ _ _ _ _ := rfl

@[simp] lemma fullOnMap_inclusion {C : OmegaCategory.{u}} {S T : Set C.Objects}
    (h : S ⊆ T) :
    Functor.comp (fullOnMap h) (C.fullOn T).inclusion = (C.fullOn S).inclusion := rfl

def fullNerve (C : OmegaCategory.{u}) (S : Set C.Objects) : (streetNerve C).Subcomplex where
  obj _ := {F | ∀ a, F.objects a ∈ S}
  map f _ h a := h ((orientals.map f.unop).objects a)

def fullNerveIso (C : OmegaCategory.{u}) (S : Set C.Objects) :
    streetNerve (C.fullOn S).category ≅ (C.fullNerve S : SSet.{u}) where
  hom := {
    app := fun _ => ↾fun F => ⟨Functor.comp F (C.fullOn S).inclusion,
      fun a => by
        have h := (F.map a.val).property.1
        change C.sourceObject ((Functor.comp F (C.fullOn S).inclusion).objects a).val ∈ S at h
        rwa [C.sourceObject_object] at h⟩
    naturality := fun _ _ _ => rfl }
  inv := {
    app := fun _ => ↾fun F => F.val.liftFullOn S F.property
    naturality := fun _ _ _ => rfl }
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro F
    apply Functor.ext
    rfl
  inv_hom_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro F
    apply Subtype.ext
    rfl

lemma fullNerveIso_hom_ι (C : OmegaCategory.{u}) (S : Set C.Objects) :
    (C.fullNerveIso S).hom ≫ (C.fullNerve S).ι =
      streetNerveMap (C.fullOn S).inclusion := rfl

instance fullInclusion_nerve_mono (C : OmegaCategory.{u}) (S : Set C.Objects) :
    Mono (streetNerveMap (C.fullOn S).inclusion) := by
  rw [← fullNerveIso_hom_ι]
  infer_instance

instance fullOnMap_nerve_mono {C : OmegaCategory.{u}} {S T : Set C.Objects} (h : S ⊆ T) :
    Mono (streetNerveMap (fullOnMap h)) := by
  exact mono_of_mono_fac (show streetNerveMap (fullOnMap h) ≫ streetNerveMap (C.fullOn T).inclusion =
    streetNerveMap (C.fullOn S).inclusion from rfl)

lemma fullNerve_inf (C : OmegaCategory.{u}) (S T : Set C.Objects) :
    C.fullNerve (S ∩ T) = C.fullNerve S ⊓ C.fullNerve T := by
  ext n F
  exact forall_and

lemma fullNerve_sieve_sup {C : OmegaCategory.{u}} {S T : Set C.Objects}
    (hS : C.IsObjectSieve S) (hT : C.IsObjectSieve T)
    (hcover : ∀ a : C.Objects, a ∈ S ∨ a ∈ T) :
    C.fullNerve S ⊔ C.fullNerve T = ⊤ := by
  apply top_unique
  intro n F _
  rcases hcover (F.objects (NormalizedChains.tableObjectsEquiv.symm
      (Fin.last n.unop.len))) with h | h
  · exact Or.inl (simplex_objects_mem_sieve F hS h)
  · exact Or.inr (simplex_objects_mem_sieve F hT h)

lemma fullNerve_cosieve_sup {C : OmegaCategory.{u}} {S T : Set C.Objects}
    (hS : C.IsObjectCosieve S) (hT : C.IsObjectCosieve T)
    (hcover : ∀ a : C.Objects, a ∈ S ∨ a ∈ T) :
    C.fullNerve S ⊔ C.fullNerve T = ⊤ := by
  apply top_unique
  intro n F _
  rcases hcover (F.objects (NormalizedChains.tableObjectsEquiv.symm
      (0 : Fin (n.unop.len+1)))) with h | h
  · exact Or.inl (simplex_objects_mem_cosieve F hS h)
  · exact Or.inr (simplex_objects_mem_cosieve F hT h)

lemma fullNerve_isPushout {C : OmegaCategory.{u}} {S T : Set C.Objects}
    (h : C.fullNerve S ⊔ C.fullNerve T = ⊤) :
    IsPushout (streetNerveMap (fullOnMap (Set.inter_subset_left (s := S) (t := T))))
      (streetNerveMap (fullOnMap (Set.inter_subset_right (s := S) (t := T))))
      (streetNerveMap (C.fullOn S).inclusion) (streetNerveMap (C.fullOn T).inclusion) := by
  let sq : SSet.Subcomplex.BicartSq (C.fullNerve (S ∩ T))
      (C.fullNerve S) (C.fullNerve T) ⊤ := ⟨h, (C.fullNerve_inf S T).symm⟩
  exact sq.isPushout.of_iso (C.fullNerveIso (S ∩ T)).symm
    (C.fullNerveIso S).symm (C.fullNerveIso T).symm
    (SSet.Subcomplex.topIso (streetNerve C)) rfl rfl rfl rfl

lemma sieve_cover_nerve_isPushout {C : OmegaCategory.{u}} {S T : Set C.Objects}
    (hS : C.IsObjectSieve S) (hT : C.IsObjectSieve T)
    (hcover : ∀ a : C.Objects, a ∈ S ∨ a ∈ T) :
    IsPushout (streetNerveMap (fullOnMap (Set.inter_subset_left (s := S) (t := T))))
      (streetNerveMap (fullOnMap (Set.inter_subset_right (s := S) (t := T))))
      (streetNerveMap (C.fullOn S).inclusion) (streetNerveMap (C.fullOn T).inclusion) :=
  fullNerve_isPushout (fullNerve_sieve_sup hS hT hcover)

lemma cosieve_cover_nerve_isPushout {C : OmegaCategory.{u}} {S T : Set C.Objects}
    (hS : C.IsObjectCosieve S) (hT : C.IsObjectCosieve T)
    (hcover : ∀ a : C.Objects, a ∈ S ∨ a ∈ T) :
    IsPushout (streetNerveMap (fullOnMap (Set.inter_subset_left (s := S) (t := T))))
      (streetNerveMap (fullOnMap (Set.inter_subset_right (s := S) (t := T))))
      (streetNerveMap (C.fullOn S).inclusion) (streetNerveMap (C.fullOn T).inclusion) :=
  fullNerve_isPushout (fullNerve_cosieve_sup hS hT hcover)

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

def sourceCell (C : OmegaCategory.{u}) (p : ℕ) (x : C.Cell) : C.Cells p :=
  ⟨C.source p x, C.source_source_self p x⟩

def targetCell (C : OmegaCategory.{u}) (p : ℕ) (x : C.Cell) : C.Cells p :=
  ⟨C.target p x, C.source_target_self p x⟩

@[simp] lemma sourceCell_source_lt (C : OmegaCategory.{u}) {p q : ℕ}
    (h : p < q) (x : C.Cell) : C.sourceCell p (C.source q x) = C.sourceCell p x := by
  apply Subtype.ext
  exact (C.source_source p q x).trans (congrArg (fun t => C.source t x) (Nat.min_eq_left (le_of_lt h)))

@[simp] lemma targetCell_target_lt (C : OmegaCategory.{u}) {p q : ℕ}
    (h : p < q) (x : C.Cell) : C.targetCell p (C.target q x) = C.targetCell p x := by
  apply Subtype.ext
  exact (C.target_target p q x).trans (congrArg (fun t => C.target t x) (Nat.min_eq_left (le_of_lt h)))

@[simp] lemma sourceCell_target_lt (C : OmegaCategory.{u}) {p q : ℕ}
    (h : p < q) (x : C.Cell) : C.sourceCell p (C.target q x) = C.sourceCell p x := by
  apply Subtype.ext
  simpa only [sourceCell, ite_eq_left h] using C.source_target p q x

@[simp] lemma targetCell_source_lt (C : OmegaCategory.{u}) {p q : ℕ}
    (h : p < q) (x : C.Cell) : C.targetCell p (C.source q x) = C.targetCell p x := by
  apply Subtype.ext
  simpa only [targetCell, ite_eq_left h] using C.target_source p q x

def gradedComp (C : OmegaCategory.{u}) {n k : ℕ} (hkn : k < n)
    (x y : C.Cells n) (h : C.target k x.val = C.source k y.val) : C.Cells n :=
  ⟨C.comp k x.val y.val h, by
    rw [C.source_comp_gt n k hkn x.val y.val h (C.source_composable hkn h)]
    simp only [x.property, y.property]⟩

@[simp] lemma sourceCell_comp_lt (C : OmegaCategory.{u}) {n k : ℕ} (hkn : k < n)
    (x y : C.Cell) (h : C.target k x = C.source k y) :
    C.sourceCell n (C.comp k x y h) =
      C.gradedComp hkn (C.sourceCell n x) (C.sourceCell n y) (C.source_composable hkn h) :=
  Subtype.ext (C.source_comp_gt n k hkn x y h _)

@[simp] lemma targetCell_comp_lt (C : OmegaCategory.{u}) {n k : ℕ} (hkn : k < n)
    (x y : C.Cell) (h : C.target k x = C.source k y) :
    C.targetCell n (C.comp k x y h) =
      C.gradedComp hkn (C.targetCell n x) (C.targetCell n y) (C.target_composable hkn h) :=
  Subtype.ext (C.target_comp_gt n k hkn x y h _)

abbrev LambdaRaw (C : OmegaCategory.{u}) (n : ℕ) := C.Cells n →₀ ℤ

def lambdaRelations (C : OmegaCategory.{u}) (n : ℕ) : Submodule ℤ (C.LambdaRaw n) :=
  Submodule.span ℤ ({z | ∃ (x : C.Cells n) (k : ℕ), k < n ∧ C.source k x.val = x.val ∧
      z = Finsupp.single x 1} ∪
    {z | ∃ (k : ℕ) (hk : k < n) (x y : C.Cells n)
      (h : C.target k x.val = C.source k y.val),
      z = Finsupp.single (C.gradedComp hk x y h) 1 - Finsupp.single x 1 - Finsupp.single y 1})

abbrev LambdaChain (C : OmegaCategory.{u}) (n : ℕ) := C.LambdaRaw n ⧸ C.lambdaRelations n

def lambdaGen (C : OmegaCategory.{u}) {n : ℕ} (x : C.Cells n) : C.LambdaChain n :=
  (C.lambdaRelations n).mkQ (Finsupp.single x 1)

lemma lambdaGen_degenerate (C : OmegaCategory.{u}) {n k : ℕ} (hkn : k < n)
    (x : C.Cells n) (hx : C.source k x.val = x.val) : C.lambdaGen x = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact Submodule.subset_span (Or.inl ⟨x, k, hkn, hx, rfl⟩)

lemma lambdaGen_comp (C : OmegaCategory.{u}) {n k : ℕ} (hkn : k < n)
    (x y : C.Cells n) (h : C.target k x.val = C.source k y.val) :
    C.lambdaGen (C.gradedComp hkn x y h) = C.lambdaGen x + C.lambdaGen y := by
  have hz : (C.lambdaRelations n).mkQ
      (Finsupp.single (C.gradedComp hkn x y h) 1 - Finsupp.single x 1 - Finsupp.single y 1) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact Submodule.subset_span (Or.inr ⟨k, hkn, x, y, h, rfl⟩)
  change C.lambdaGen (C.gradedComp hkn x y h) - C.lambdaGen x - C.lambdaGen y = 0 at hz
  exact sub_eq_zero.mp (by simpa only [sub_add_eq_sub_sub] using hz)

lemma lambda_linear_ext (C : OmegaCategory.{u}) {n : ℕ} {M : Type v}
    [AddCommGroup M] [Module ℤ M] (f g : C.LambdaChain n →ₗ[ℤ] M)
    (h : ∀ x : C.Cells n, f (C.lambdaGen x) = g (C.lambdaGen x)) : f = g := by
  apply Submodule.linearMap_qext
  apply Finsupp.lhom_ext
  intro x z
  have hz : (Finsupp.single x z : C.LambdaRaw n) = z • Finsupp.single x 1 := by simp
  rw [hz]
  exact (map_zsmul (f.comp (C.lambdaRelations n).mkQ) z _).trans
    ((congrArg (fun t => z • t) (h x)).trans
      (map_zsmul (g.comp (C.lambdaRelations n).mkQ) z _).symm)

def lambdaRawD (C : OmegaCategory.{u}) (n : ℕ) : C.LambdaRaw (n+1) →ₗ[ℤ] C.LambdaChain n :=
  Finsupp.linearCombination ℤ (fun x =>
    C.lambdaGen (C.targetCell n x.val) - C.lambdaGen (C.sourceCell n x.val))

@[simp] lemma lambdaRawD_single (C : OmegaCategory.{u}) (n : ℕ) (x : C.Cells (n+1)) :
    C.lambdaRawD n (Finsupp.single x 1) =
      C.lambdaGen (C.targetCell n x.val) - C.lambdaGen (C.sourceCell n x.val) := by
  exact (Finsupp.linearCombination_single _ _ _).trans (one_smul ℤ _)

lemma lambdaRawD_relations (C : OmegaCategory.{u}) (n : ℕ) :
    C.lambdaRelations (n+1) ≤ LinearMap.ker (C.lambdaRawD n) := by
  apply Submodule.span_le.mpr
  intro z hz
  change C.lambdaRawD n z = 0
  rcases hz with ⟨x, k, hk, hx, rfl⟩ | ⟨k, hk, x, y, h, rfl⟩
  · rw [C.lambdaRawD_single]
    have hs : C.source n x.val = x.val := C.source_fixed_upwards (by omega) hx
    have he : C.targetCell n x.val = C.sourceCell n x.val :=
      Subtype.ext ((C.target_eq_self_of_source_eq_self hs).trans hs.symm)
    rw [he, sub_self]
  · simp only [map_sub, lambdaRawD_single]
    by_cases hkn : k < n
    · rw [show (C.gradedComp hk x y h).val = C.comp k x.val y.val h from rfl,
        C.targetCell_comp_lt hkn, C.sourceCell_comp_lt hkn]
      erw [C.lambdaGen_comp hkn, C.lambdaGen_comp hkn]
      abel
    · have he : k = n := by omega
      subst k
      have hs : C.sourceCell n (C.gradedComp hk x y h).val = C.sourceCell n x.val :=
        Subtype.ext (C.source_comp_le n n le_rfl x.val y.val h)
      have ht : C.targetCell n (C.gradedComp hk x y h).val = C.targetCell n y.val :=
        Subtype.ext (C.target_comp_le n n le_rfl x.val y.val h)
      have hh : C.targetCell n x.val = C.sourceCell n y.val := Subtype.ext h
      rw [hs, ht, hh]
      abel

def lambdaD (C : OmegaCategory.{u}) (n : ℕ) : C.LambdaChain (n+1) →ₗ[ℤ] C.LambdaChain n :=
  (C.lambdaRelations (n+1)).liftQ (C.lambdaRawD n) (C.lambdaRawD_relations n)

@[simp] lemma lambdaD_gen (C : OmegaCategory.{u}) (n : ℕ) (x : C.Cells (n+1)) :
    C.lambdaD n (C.lambdaGen x) =
      C.lambdaGen (C.targetCell n x.val) - C.lambdaGen (C.sourceCell n x.val) :=
  C.lambdaRawD_single n x

lemma lambdaD_square (C : OmegaCategory.{u}) (n : ℕ) :
    (C.lambdaD n).comp (C.lambdaD (n+1)) = 0 := by
  apply C.lambda_linear_ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  erw [lambdaD_gen, map_sub, lambdaD_gen, lambdaD_gen]
  have hss : C.sourceCell n (C.source (n+1) x.val) = C.sourceCell n x.val :=
    C.sourceCell_source_lt (by omega) x.val
  have hst : C.sourceCell n (C.target (n+1) x.val) = C.sourceCell n x.val :=
    C.sourceCell_target_lt (by omega) x.val
  have hts : C.targetCell n (C.source (n+1) x.val) = C.targetCell n x.val :=
    C.targetCell_source_lt (by omega) x.val
  have htt : C.targetCell n (C.target (n+1) x.val) = C.targetCell n x.val :=
    C.targetCell_target_lt (by omega) x.val
  change (C.lambdaGen (C.targetCell n (C.target (n+1) x.val)) -
      C.lambdaGen (C.sourceCell n (C.target (n+1) x.val))) -
    (C.lambdaGen (C.targetCell n (C.source (n+1) x.val)) -
      C.lambdaGen (C.sourceCell n (C.source (n+1) x.val))) = 0
  rw [hss, hst, hts, htt, sub_self]

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

def lambdaRawAug (C : OmegaCategory.{u}) : C.LambdaRaw 0 →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (fun _ => 1)

lemma lambdaRawAug_relations (C : OmegaCategory.{u}) :
    C.lambdaRelations 0 ≤ LinearMap.ker C.lambdaRawAug := by
  apply Submodule.span_le.mpr
  intro z hz
  rcases hz with ⟨x, k, hk, _, _⟩ | ⟨k, hk, x, y, h, _⟩ <;> omega

def lambdaAug (C : OmegaCategory.{u}) : C.LambdaChain 0 →ₗ[ℤ] ℤ :=
  (C.lambdaRelations 0).liftQ C.lambdaRawAug C.lambdaRawAug_relations

@[simp] lemma lambdaAug_gen (C : OmegaCategory.{u}) (x : C.Cells 0) :
    C.lambdaAug (C.lambdaGen x) = 1 := by
  change C.lambdaRawAug (Finsupp.single x 1) = 1
  exact (Finsupp.linearCombination_single _ _ _).trans (one_smul ℤ _)

lemma lambdaAug_d (C : OmegaCategory.{u}) : C.lambdaAug.comp (C.lambdaD 0) = 0 := by
  apply C.lambda_linear_ext
  intro x
  change C.lambdaAug (C.lambdaD 0 (C.lambdaGen x)) = 0
  erw [lambdaD_gen, map_sub, lambdaAug_gen, lambdaAug_gen, sub_self]

def lambdaPositive (C : OmegaCategory.{u}) (n : ℕ) : AddSubmonoid (C.LambdaChain n) :=
  AddSubmonoid.closure (Set.range (C.lambdaGen (n := n)))

lemma lambdaGen_positive (C : OmegaCategory.{u}) {n : ℕ} (x : C.Cells n) :
    C.lambdaGen x ∈ C.lambdaPositive n :=
  AddSubmonoid.subset_closure ⟨x, rfl⟩

def linearization (C : OmegaCategory.{u}) : DirectedComplex.{u} where
  Chain := C.LambdaChain
  group _ := inferInstance
  d n := (C.lambdaD n).toAddMonoidHom
  d_d n x := LinearMap.congr_fun (C.lambdaD_square n) x
  augmentation := C.lambdaAug.toAddMonoidHom
  augmentation_d x := LinearMap.congr_fun C.lambdaAug_d x
  positive := C.lambdaPositive

lemma lambdaGen_source_above (C : OmegaCategory.{u}) {p k : ℕ} (h : k < p)
    (x : C.Cell) : C.lambdaGen (C.sourceCell p (C.source k x)) = 0 := by
  apply C.lambdaGen_degenerate h
  change C.source k (C.source p (C.source k x)) = C.source p (C.source k x)
  have he := C.source_fixed_upwards (le_of_lt h) (C.source_source_self k x)
  rw [he, C.source_source_self]

lemma lambdaGen_target_above (C : OmegaCategory.{u}) {p k : ℕ} (h : k < p)
    (x : C.Cell) : C.lambdaGen (C.targetCell p (C.source k x)) = 0 := by
  apply C.lambdaGen_degenerate h
  change C.source k (C.target p (C.source k x)) = C.target p (C.source k x)
  have he := C.target_eq_self_of_source_eq_self
    (C.source_fixed_upwards (le_of_lt h) (C.source_source_self k x))
  rw [he, C.source_source_self]

def lambdaUnitTable (C : OmegaCategory.{u}) (x : C.Cell) :
    DirectedComplex.Table C.linearization where
  row p b := if b then C.lambdaGen (C.targetCell p x) else C.lambdaGen (C.sourceCell p x)
  positive p b := by
    cases b <;> exact C.lambdaGen_positive _
  boundary p b := by
    change C.lambdaD p (if b then _ else _) = _
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · erw [lambdaD_gen]
      erw [C.targetCell_source_lt (Nat.lt_succ_self p), C.sourceCell_source_lt (Nat.lt_succ_self p)]
      rfl
    · erw [lambdaD_gen]
      erw [C.targetCell_target_lt (Nat.lt_succ_self p), C.sourceCell_target_lt (Nat.lt_succ_self p)]
      rfl
  augmentation b := by
    change C.lambdaAug (if b then _ else _) = 1
    cases b <;> exact C.lambdaAug_gen _
  bounded := by
    obtain ⟨k, hk⟩ := C.finite_dimension x
    refine ⟨k, fun p hp b => ?_⟩
    rw [← hk]
    cases b <;> first
      | exact C.lambdaGen_source_above hp x
      | exact C.lambdaGen_target_above hp x

@[simp] lemma lambdaUnitTable_row (C : OmegaCategory.{u}) (x : C.Cell) (p : ℕ) (b : Bool) :
    (C.lambdaUnitTable x).row p b =
      if b then C.lambdaGen (C.targetCell p x) else C.lambdaGen (C.sourceCell p x) := rfl

lemma lambdaUnitTable_source (C : OmegaCategory.{u}) (k : ℕ) (x : C.Cell) :
    C.lambdaUnitTable (C.source k x) =
      DirectedComplex.Table.truncate k false (C.lambdaUnitTable x) := by
  ext p b
  simp only [lambdaUnitTable_row, DirectedComplex.Table.truncate_row]
  by_cases hpk : p < k
  · simp only [hpk]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · rw [C.sourceCell_source_lt hpk]
    · rw [C.targetCell_source_lt hpk]
  · by_cases he : p = k
    · subst p
      simp only [lt_self_iff_false, ite_false, Bool.false_eq_true]
      have hs : C.sourceCell k (C.source k x) = C.sourceCell k x :=
        Subtype.ext (C.source_source_self k x)
      have ht : C.targetCell k (C.source k x) = C.sourceCell k x :=
        Subtype.ext (C.target_source_self k x)
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, hs, ht] <;> rfl
    · have hkp : k < p := by omega
      simp only [hpk, he]
      cases b <;> first
        | exact C.lambdaGen_source_above hkp x
        | exact C.lambdaGen_target_above hkp x

lemma lambdaUnitTable_target (C : OmegaCategory.{u}) (k : ℕ) (x : C.Cell) :
    C.lambdaUnitTable (C.target k x) =
      DirectedComplex.Table.truncate k true (C.lambdaUnitTable x) := by
  ext p b
  simp only [lambdaUnitTable_row, DirectedComplex.Table.truncate_row]
  by_cases hpk : p < k
  · simp only [hpk]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · rw [C.sourceCell_target_lt hpk]
    · rw [C.targetCell_target_lt hpk]
  · by_cases he : p = k
    · subst p
      simp only [lt_self_iff_false, ite_true]
      have hs : C.sourceCell k (C.target k x) = C.targetCell k x :=
        Subtype.ext (C.source_target_self k x)
      have ht : C.targetCell k (C.target k x) = C.targetCell k x :=
        Subtype.ext (C.target_target_self k x)
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, hs, ht] <;> rfl
    · have hkp : k < p := by omega
      simp only [hpk, he]
      have hk : C.source k (C.target k x) = C.target k x := C.source_target_self k x
      rw [← hk]
      cases b <;> first
        | exact C.lambdaGen_source_above hkp (C.target k x)
        | exact C.lambdaGen_target_above hkp (C.target k x)

lemma lambdaUnitTable_comp (C : OmegaCategory.{u}) (k : ℕ) (x y : C.Cell)
    (h : C.target k x = C.source k y)
    (h' : DirectedComplex.Table.truncate k true (C.lambdaUnitTable x) =
      DirectedComplex.Table.truncate k false (C.lambdaUnitTable y)) :
    C.lambdaUnitTable (C.comp k x y h) =
      DirectedComplex.Table.comp k (C.lambdaUnitTable x) (C.lambdaUnitTable y) h' := by
  ext p b
  simp only [lambdaUnitTable_row, DirectedComplex.Table.comp_row]
  by_cases hpk : p < k
  · have he : C.target p y = C.target p x := by
      have hh := congrArg (C.target p) h
      simpa only [C.target_target, Nat.min_eq_left (le_of_lt hpk),
        C.target_source, ite_eq_left hpk] using hh.symm
    simp only [hpk]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · congr 1
      exact Subtype.ext (C.source_comp_le p k (le_of_lt hpk) x y h)
    · congr 1
      exact Subtype.ext ((C.target_comp_le p k (le_of_lt hpk) x y h).trans he)
  · by_cases he : p = k
    · subst p
      simp only [lt_self_iff_false, ite_true]
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · congr 1
        exact Subtype.ext (C.source_comp_le k k le_rfl x y h)
      · congr 1
        exact Subtype.ext (C.target_comp_le k k le_rfl x y h)
    · have hkp : k < p := by omega
      simp only [hpk, he]
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · rw [C.sourceCell_comp_lt hkp]
        exact C.lambdaGen_comp hkp _ _ _
      · rw [C.targetCell_comp_lt hkp]
        exact C.lambdaGen_comp hkp _ _ _

def lambdaUnit (C : OmegaCategory.{u}) : Functor C C.linearization.nu where
  map := C.lambdaUnitTable
  map_source := C.lambdaUnitTable_source
  map_target := C.lambdaUnitTable_target
  map_comp := C.lambdaUnitTable_comp

end Thomason.OmegaCategory

end

end OAI
