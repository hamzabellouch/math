import OAI.GroupTheory.UniversalGroup.HigmanEmbedding

namespace OAI

section UniversalFinitelyPresentedProof
universe u v w x
noncomputable section

namespace UniversalFInfinity.UniversalGroup

abbrev PresentationCode := Σ n : ℕ, Finset (FreeGroup (Fin n))
abbrev Presented (p : PresentationCode) := PresentedGroup (p.2 : Set (FreeGroup (Fin p.1)))
abbrev CountableUniversal := Monoid.CoprodI Presented

instance : Countable PresentationCode := inferInstance
instance (p : PresentationCode) : Countable (Presented p) := by
  exact (QuotientGroup.mk'_surjective
    (Subgroup.normalClosure (p.2 : Set (FreeGroup (Fin p.1))))).countable

instance : Countable CountableUniversal := by
  exact (Con.mk'_surjective (c := conGen (Monoid.CoprodI.Rel Presented))).countable

theorem countable_universal {G : Type*} [Group G] [Group.IsFinitelyPresented G] :
    ∃ φ : G →* CountableUniversal, Function.Injective φ := by
  classical
  obtain ⟨n,s,hs,⟨e⟩⟩ := Group.IsFinitelyPresented.exists_mulEquiv_presentedGroup (G := G)
  let p : PresentationCode := ⟨n,hs.toFinset⟩
  have heq : (p.2 : Set (FreeGroup (Fin p.1))) = s := hs.coe_toFinset
  let a : G ≃* Presented p := e.trans (QuotientGroup.quotientMulEquivOfEq
    (congrArg Subgroup.normalClosure heq.symm))
  exact ⟨(Monoid.CoprodI.of (i := p)).comp a.toMonoidHom,
    (Monoid.CoprodI.of_injective p).comp a.injective⟩

end UniversalFInfinity.UniversalGroup

namespace UniversalFInfinity.FreeConjugates

def shift (n : ℤ) : MulAut (FreeGroup ℤ) :=
  FreeGroup.freeGroupCongr (Equiv.addLeft n)

@[simp] lemma shift_of (n k : ℤ) : shift n (FreeGroup.of k) = FreeGroup.of (n+k) := rfl

def shifts : Multiplicative ℤ →* MulAut (FreeGroup ℤ) where
  toFun n := shift n.toAdd
  map_one' := by
    apply MulEquiv.toMonoidHom_injective
    ext k
    simp [shift]
  map_mul' n m := by
    apply MulEquiv.toMonoidHom_injective
    ext k
    simp [shift, add_assoc]

abbrev ShiftGroup := (FreeGroup ℤ) ⋊[shifts] (Multiplicative ℤ)
abbrev Two := FreeGroup Bool
def a : Two := FreeGroup.of false
def p : Two := FreeGroup.of true
def word (i : ℕ) : Two := a ^ i * p * (a ^ i)⁻¹

def test : Two →* ShiftGroup :=
  FreeGroup.lift (fun b => if b then SemidirectProduct.inl (FreeGroup.of 0)
    else SemidirectProduct.inr (Multiplicative.ofAdd 1))

@[simp] lemma test_a : test a = SemidirectProduct.inr (Multiplicative.ofAdd 1) := by
  simp [test,a]
@[simp] lemma test_p : test p = SemidirectProduct.inl (FreeGroup.of 0) := by
  simp [test,p]

lemma test_word (i : ℕ) : test (word i) =
    SemidirectProduct.inl (FreeGroup.of (i : ℤ)) := by
  simp only [word,map_mul,map_pow,map_inv,test_a,test_p]
  rw [← map_pow,← map_inv,← SemidirectProduct.inl_aut]
  congr 1
  change shift ((Multiplicative.ofAdd (1 : ℤ)) ^ i).toAdd (FreeGroup.of 0) = _
  simp

def inclusion : FreeGroup ℕ →* Two := FreeGroup.lift word

lemma test_comp : test.comp inclusion =
    (SemidirectProduct.inl : FreeGroup ℤ →* ShiftGroup).comp (FreeGroup.map Int.ofNat) := by
  apply FreeGroup.ext_hom
  intro i
  simpa only [MonoidHom.comp_apply, inclusion, FreeGroup.lift_apply_of, FreeGroup.map.of]
    using (test_word i).trans (congrArg SemidirectProduct.inl
      (congrArg FreeGroup.of (show (i : ℤ) = Int.ofNat i from rfl)))

lemma inclusion_injective : Function.Injective inclusion := by
  apply Function.Injective.of_comp (f := test)
  rw [← MonoidHom.coe_comp,test_comp]
  exact SemidirectProduct.inl_injective.comp (FreeGroup.map_injective Int.ofNat_injective)

end UniversalFInfinity.FreeConjugates

namespace UniversalFInfinity.CountableOvergroup
open Monoid
variable {C : Type u} [Group C] (c : ℕ → C)

abbrev Base := Coprod C FreeConjugates.Two

def left : FreeGroup ℕ →* Base (C := C) :=
  Coprod.inr.comp FreeConjugates.inclusion

def right : FreeGroup ℕ →* Base (C := C) :=
  FreeGroup.lift (fun i => Coprod.inl (c i) * Coprod.inr (FreeConjugates.word i))

@[simp] lemma left_of (i : ℕ) : left (C := C) (FreeGroup.of i) =
    Coprod.inr (FreeConjugates.word i) := by
  simp only [left,MonoidHom.comp_apply,FreeConjugates.inclusion,FreeGroup.lift_apply_of]

@[simp] lemma right_of (i : ℕ) : right c (FreeGroup.of i) =
    Coprod.inl (c i) * Coprod.inr (FreeConjugates.word i) := by
  simp only [right,FreeGroup.lift_apply_of]

def projection : Base (C := C) →* FreeConjugates.Two :=
  Coprod.lift 1 (MonoidHom.id _)

lemma left_injective : Function.Injective (left (C := C)) :=
  Coprod.inr_injective.comp FreeConjugates.inclusion_injective

lemma projection_right : (projection (C := C)).comp (right c) = FreeConjugates.inclusion := by
  apply FreeGroup.ext_hom
  intro i
  simp [projection,right,FreeConjugates.inclusion]

lemma right_injective : Function.Injective (right c) := by
  apply Function.Injective.of_comp (f := projection)
  rw [← MonoidHom.coe_comp,projection_right]
  exact FreeConjugates.inclusion_injective

noncomputable def associated : (left (C := C)).range ≃* (right c).range :=
  (MonoidHom.ofInjective (left_injective (C := C))).symm.trans
    (MonoidHom.ofInjective (right_injective c))

abbrev Overgroup := HNNExtension (Base (C := C)) (left (C := C)).range (right c).range
  (associated c)

noncomputable def embed : C →* Overgroup c := HNNExtension.of.comp Coprod.inl

lemma embed_injective : Function.Injective (embed c) :=
  (HNNExtension.of_injective (φ := associated c)).comp Coprod.inl_injective

noncomputable def a : Overgroup c := HNNExtension.of (Coprod.inr FreeConjugates.a)
noncomputable def p : Overgroup c := HNNExtension.of (Coprod.inr FreeConjugates.p)
noncomputable def t : Overgroup c := HNNExtension.t

lemma associated_left (g : FreeGroup ℕ) : associated c ⟨left g,⟨g,rfl⟩⟩ =
    ⟨right c g,⟨g,rfl⟩⟩ := by
  change (MonoidHom.ofInjective (right_injective c))
    ((MonoidHom.ofInjective (left_injective (C := C))).symm
      ((MonoidHom.ofInjective (left_injective (C := C))) g)) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

lemma generator_formula (i : ℕ) : embed c (c i) =
    t c * (a c ^ i * p c * (a c ^ i)⁻¹) * (t c)⁻¹ *
      (a c ^ i * p c * (a c ^ i)⁻¹)⁻¹ := by
  have h := HNNExtension.equiv_eq_conj (φ := associated c)
    (⟨left (FreeGroup.of i),⟨FreeGroup.of i,rfl⟩⟩ : (left (C := C)).range)
  rw [associated_left] at h
  change HNNExtension.of (right c (FreeGroup.of i)) = _ at h
  simp only [right_of,left_of,map_mul] at h
  have hw : (HNNExtension.of (Coprod.inr (FreeConjugates.word i)) : Overgroup c) =
      a c ^ i * p c * (a c ^ i)⁻¹ := by
    simp only [FreeConjugates.word,map_mul,map_inv,map_pow,a,p]
  rw [hw] at h
  change embed c (c i) * _ = t c * _ * (t c)⁻¹ at h
  rw [← h]
  group

lemma closure_three_of_generates (hc : Subgroup.closure (Set.range c) = ⊤) :
    Subgroup.closure ({a c,p c,t c} : Set (Overgroup c)) = ⊤ := by
  let S := Subgroup.closure ({a c,p c,t c} : Set (Overgroup c))
  have ha : a c ∈ S := Subgroup.subset_closure (by simp)
  have hp : p c ∈ S := Subgroup.subset_closure (by simp)
  have ht : t c ∈ S := Subgroup.subset_closure (by simp)
  have hgen : Set.range c ⊆ S.comap (embed c) := by
    rintro _ ⟨i,rfl⟩
    change embed c (c i) ∈ S
    rw [generator_formula]
    have hv := S.mul_mem (S.mul_mem (S.pow_mem ha i) hp) (S.inv_mem (S.pow_mem ha i))
    exact S.mul_mem (S.mul_mem (S.mul_mem ht hv) (S.inv_mem ht)) (S.inv_mem hv)
  have htop : ⊤ ≤ S.comap (embed c) := by
    rw [← hc]
    exact (Subgroup.closure_le _).mpr hgen
  have hcS (g : C) : embed c g ∈ S := htop (Subgroup.mem_top g)
  have hfS (g : FreeConjugates.Two) :
      (HNNExtension.of (Coprod.inr g) : Overgroup c) ∈ S := by
    induction g using FreeGroup.induction_on with
    | one => simp
    | of b => cases b <;> assumption
    | inv_of g hg => simpa only [map_inv] using S.inv_mem hg
    | mul g h hg hh => simpa only [map_mul] using S.mul_mem hg hh
  apply top_unique
  intro g hg
  clear hg
  change g ∈ S
  induction g using HNNExtension.induction_on with
  | of g =>
    induction g using Coprod.induction_on with
    | inl g => exact hcS g
    | inr g => exact hfS g
    | mul g h hg hh => simpa only [map_mul] using S.mul_mem hg hh
  | t => exact ht
  | mul g h hg hh => exact S.mul_mem hg hh
  | inv g hg => exact S.inv_mem hg

lemma closure_three (hc : Function.Surjective c) :
    Subgroup.closure ({a c,p c,t c} : Set (Overgroup c)) = ⊤ :=
  closure_three_of_generates c (by rw [Set.range_eq_univ.mpr hc,Subgroup.closure_univ])

lemma finitely_generated (hc : Function.Surjective c) : Group.FG (Overgroup c) :=
  Group.fg_iff.mpr ⟨{a c,p c,t c},closure_three c hc,by simp⟩

theorem countable_embeds_three_generated [Countable C] :
    ∃ (V : Type u) (_ : Group V) (_ : Group.FG V),
      ∃ e : C →* V, Function.Injective e := by
  obtain ⟨c,hc⟩ := exists_surjective_nat C
  exact ⟨Overgroup c,inferInstance,finitely_generated c hc,embed c,embed_injective c⟩

end UniversalFInfinity.CountableOvergroup

namespace UniversalFInfinity.ThreePresentation
open Monoid

abbrev Alphabet := Bool ⊕ Unit
abbrev Words := FreeGroup Alphabet

def A : Words := FreeGroup.of (Sum.inl false)
def P : Words := FreeGroup.of (Sum.inl true)
def T : Words := FreeGroup.of (Sum.inr ())
def conjugate (i : ℕ) : Words := A ^ i * P * (A ^ i)⁻¹
def substitute : FreeGroup ℕ →* Words :=
  FreeGroup.lift (fun i => T * conjugate i * T⁻¹ * (conjugate i)⁻¹)

variable (rels : Set (FreeGroup ℕ))
abbrev C := PresentedGroup rels
abbrev V := CountableOvergroup.Overgroup (PresentedGroup.of (rels := rels))
abbrev Q := PresentedGroup (substitute '' rels)

noncomputable def generator : Alphabet → V rels
  | Sum.inl false => CountableOvergroup.a _
  | Sum.inl true => CountableOvergroup.p _
  | Sum.inr _ => CountableOvergroup.t _

lemma lift_substitute : (FreeGroup.lift (generator rels)).comp substitute =
    (CountableOvergroup.embed (PresentedGroup.of (rels := rels))).comp
      (PresentedGroup.mk rels) := by
  apply FreeGroup.ext_hom
  intro i
  simp only [MonoidHom.comp_apply,substitute,FreeGroup.lift_apply_of,
    map_mul,map_inv,conjugate,map_pow,A,P,T,generator]
  exact (CountableOvergroup.generator_formula _ i).symm

lemma substituted_relation (r : Words) (hr : r ∈ substitute '' rels) :
    FreeGroup.lift (generator rels) r = 1 := by
  obtain ⟨r,hr,rfl⟩ := hr
  change ((FreeGroup.lift (generator rels)).comp substitute) r = 1
  rw [lift_substitute,MonoidHom.comp_apply,PresentedGroup.one_of_mem hr,map_one]

noncomputable def toV : Q rels →* V rels :=
  PresentedGroup.toGroup (substituted_relation rels)

def fromC : C rels →* Q rels :=
  PresentedGroup.map substitute (fun _ hr => ⟨_,hr,rfl⟩)

lemma fromC_of (i : ℕ) : fromC rels (PresentedGroup.of i) =
    (PresentedGroup.mk (substitute '' rels))
      (T * conjugate i * T⁻¹ * (conjugate i)⁻¹) := by
  change (PresentedGroup.mk _) (substitute (FreeGroup.of i)) = _
  rw [substitute,FreeGroup.lift_apply_of]

lemma toV_comp_fromC : (toV rels).comp (fromC rels) =
    CountableOvergroup.embed (PresentedGroup.of (rels := rels)) := by
  apply PresentedGroup.ext
  intro i
  rw [MonoidHom.comp_apply,fromC_of]
  change (FreeGroup.lift (generator rels))
    (T * conjugate i * T⁻¹ * (conjugate i)⁻¹) = _
  simp only [map_mul,map_inv,conjugate,map_pow,T,A,P,FreeGroup.lift_apply_of,generator]
  exact (CountableOvergroup.generator_formula _ i).symm

theorem fromC_injective : Function.Injective (fromC rels) := by
  apply Function.Injective.of_comp (f := toV rels)
  rw [← MonoidHom.coe_comp,toV_comp_fromC]
  exact CountableOvergroup.embed_injective _

end UniversalFInfinity.ThreePresentation

namespace UniversalFInfinity.RecursiveUniversal

abbrev Word := List (ℕ × Bool)
abbrev Code := List Word

def relations (P : Code) : Set (FreeGroup ℕ) := FreeGroup.mk '' {w | w ∈ P}
def rawAt (m j : ℕ) : Word := ((Encodable.decode (α := Code) m).getD []).getD j []
def colour (m : ℕ) (w : Word) : Word := w.map (fun x => (Nat.pair m x.1,x.2))
def relator (k : ℕ) : Word := colour k.unpair.1 (rawAt k.unpair.1 k.unpair.2)
def allRelations : Set (FreeGroup ℕ) := Set.range (fun k => FreeGroup.mk (relator k))
abbrev Universal := PresentedGroup allRelations

lemma rawAt_encode (P : Code) (j : ℕ) : rawAt (Encodable.encode P) j = P.getD j [] := by
  simp [rawAt]

lemma coloured_relation (P : Code) (w : Word) (hw : w ∈ P) :
    FreeGroup.map (Nat.pair (Encodable.encode P)) (FreeGroup.mk w) ∈ allRelations := by
  obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hw
  refine ⟨Nat.pair (Encodable.encode P) j,?_⟩
  simp only [relator,Nat.unpair_pair,rawAt_encode,List.getD_eq_getElem?_getD,hj,
    Option.getD_some,colour,FreeGroup.map.mk]

def embed (P : Code) : PresentedGroup (relations P) →* Universal :=
  PresentedGroup.map (FreeGroup.map (Nat.pair (Encodable.encode P))) (by
    rintro _ ⟨w,hw,rfl⟩
    exact coloured_relation P w hw)

def project (P : Code) (k : ℕ) : PresentedGroup (relations P) :=
  if k.unpair.1 = Encodable.encode P then PresentedGroup.of k.unpair.2 else 1

lemma eval_colour (P : Code) (m : ℕ) :
    (FreeGroup.lift (project P)).comp (FreeGroup.map (Nat.pair m)) =
      if m = Encodable.encode P then PresentedGroup.mk (relations P) else 1 := by
  apply FreeGroup.ext_hom
  intro i
  simp only [MonoidHom.comp_apply,FreeGroup.map.of,FreeGroup.lift_apply_of,project,
    Nat.unpair_pair]
  split_ifs <;> rfl

lemma raw_relation (P : Code) (j : ℕ) :
    PresentedGroup.mk (relations P) (FreeGroup.mk (P.getD j [])) = 1 := by
  simp only [List.getD_eq_getElem?_getD]
  cases hj : P[j]? with
  | none => change (PresentedGroup.mk (relations P)) 1 = 1; exact map_one _
  | some w =>
    simp only [Option.getD_some]
    exact PresentedGroup.one_of_mem ⟨w,List.mem_of_getElem? hj,rfl⟩

lemma project_relator (P : Code) (k : ℕ) :
    FreeGroup.lift (project P) (FreeGroup.mk (relator k)) = 1 := by
  change FreeGroup.lift (project P)
    (FreeGroup.mk ((rawAt k.unpair.1 k.unpair.2).map
      (fun x => (Nat.pair k.unpair.1 x.1,x.2)))) = 1
  rw [← FreeGroup.map.mk]
  rw [← MonoidHom.comp_apply]
  rw [eval_colour]
  split_ifs with h
  · rw [h,rawAt_encode]
    exact raw_relation P _
  · rfl

def retract (P : Code) : Universal →* PresentedGroup (relations P) :=
  PresentedGroup.toGroup (by rintro _ ⟨k,rfl⟩; exact project_relator P k)

lemma retract_embed (P : Code) : (retract P).comp (embed P) = MonoidHom.id _ := by
  apply PresentedGroup.ext
  intro i
  change FreeGroup.lift (project P) (FreeGroup.map (Nat.pair (Encodable.encode P))
    (FreeGroup.of i)) = PresentedGroup.of i
  simp [project]

lemma embed_injective (P : Code) : Function.Injective (embed P) := by
  apply Function.Injective.of_comp (f := retract P)
  rw [← MonoidHom.coe_comp,retract_embed]
  exact Function.injective_id

def rename {α β : Type*} (i : α ↪ β) (s : Set (FreeGroup α)) :
    PresentedGroup s →* PresentedGroup (FreeGroup.map i '' s) :=
  PresentedGroup.map (FreeGroup.map i) (fun _ hr => ⟨_,hr,rfl⟩)

noncomputable def renameValues {α β : Type*} (i : α ↪ β) (s : Set (FreeGroup α)) :
    β → PresentedGroup s := Function.extend i PresentedGroup.of (fun _ => 1)

lemma renameValues_comp {α β : Type*} (i : α ↪ β) (s : Set (FreeGroup α)) :
    (FreeGroup.lift (renameValues i s)).comp (FreeGroup.map i) = PresentedGroup.mk s := by
  apply FreeGroup.ext_hom
  intro a
  simp [renameValues,i.injective.extend_apply,PresentedGroup.of]

noncomputable def renameRetract {α β : Type*} (i : α ↪ β) (s : Set (FreeGroup α)) :
    PresentedGroup (FreeGroup.map i '' s) →* PresentedGroup s :=
  PresentedGroup.toGroup (by
    rintro _ ⟨r,hr,rfl⟩
    change ((FreeGroup.lift (renameValues i s)).comp (FreeGroup.map i)) r = 1
    rw [renameValues_comp]
    exact PresentedGroup.one_of_mem hr)

lemma renameRetract_comp {α β : Type*} (i : α ↪ β) (s : Set (FreeGroup α)) :
    (renameRetract i s).comp (rename i s) = MonoidHom.id _ := by
  apply PresentedGroup.ext
  intro a
  change FreeGroup.lift (renameValues i s) (FreeGroup.map i (FreeGroup.of a)) =
    PresentedGroup.of a
  simp [renameValues,i.injective.extend_apply]

lemma rename_injective {α β : Type*} (i : α ↪ β) (s : Set (FreeGroup α)) :
    Function.Injective (rename i s) := by
  apply Function.Injective.of_comp (f := renameRetract i s)
  rw [← MonoidHom.coe_comp,renameRetract_comp]
  exact Function.injective_id

lemma code_exists (s : Set (FreeGroup ℕ)) (hs : s.Finite) : ∃ P : Code, relations P = s := by
  classical
  refine ⟨hs.toFinset.toList.map FreeGroup.toWord,?_⟩
  ext r
  constructor
  · rintro ⟨w,hw,rfl⟩
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hw
    rw [FreeGroup.mk_toWord]
    exact hs.mem_toFinset.mp (Finset.mem_toList.mp hq)
  · intro hr
    refine ⟨r.toWord,?_,FreeGroup.mk_toWord⟩
    exact List.mem_map.mpr ⟨r,Finset.mem_toList.mpr (hs.mem_toFinset.mpr hr),rfl⟩

theorem universal {G : Type*} [Group G] [Group.IsFinitelyPresented G] :
    ∃ h : G →* Universal, Function.Injective h := by
  classical
  obtain ⟨n,s,hs,⟨e⟩⟩ := Group.IsFinitelyPresented.exists_mulEquiv_presentedGroup (G := G)
  let i : Fin n ↪ ℕ := ⟨Fin.val,Fin.val_injective⟩
  obtain ⟨P,hP⟩ := code_exists (FreeGroup.map i '' s) (hs.image _)
  let eP : PresentedGroup (FreeGroup.map i '' s) ≃* PresentedGroup (relations P) :=
    QuotientGroup.quotientMulEquivOfEq (congrArg Subgroup.normalClosure hP.symm)
  exact ⟨(embed P).comp (eP.toMonoidHom.comp ((rename i s).comp e.toMonoidHom)),
    (embed_injective P).comp (eP.injective.comp ((rename_injective i s).comp e.injective))⟩

lemma rawAt_primrec : Primrec₂ rawAt := by
  unfold rawAt
  exact (Primrec.list_getD []).comp
    (Primrec.option_getD.comp (Primrec.decode.comp Primrec.fst) (Primrec.const [])) Primrec.snd

lemma colour_primrec : Primrec₂ colour := by
  unfold Primrec₂ colour
  apply Primrec.list_map Primrec.snd
  exact (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.fst)
    (Primrec.fst.comp Primrec.snd)).pair (Primrec.snd.comp Primrec.snd)

theorem relator_primrec : Primrec relator := by
  unfold relator
  exact colour_primrec.comp (Primrec.fst.comp Primrec.unpair)
    (rawAt_primrec.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair))

end UniversalFInfinity.RecursiveUniversal

namespace UniversalFInfinity.RecursiveUniversalThree
open ThreePresentation
abbrev Raw := List (Alphabet × Bool)

def positive (i : ℕ) : Raw := List.replicate i (Sum.inl false,true)
def v (i : ℕ) : Raw := positive i ++ [(Sum.inl true,true)] ++ FreeGroup.invRev (positive i)
def replacement (i : ℕ) : Raw :=
  [(Sum.inr (),true)] ++ v i ++ [(Sum.inr (),false)] ++ FreeGroup.invRev (v i)
def substituteRaw (w : RecursiveUniversal.Word) : Raw :=
  w.flatMap (fun x => if x.2 then replacement x.1 else FreeGroup.invRev (replacement x.1))
def enumerator (k : ℕ) : Raw := substituteRaw (RecursiveUniversal.relator k)

lemma mk_positive (i : ℕ) : FreeGroup.mk (positive i) = A ^ i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [positive,List.replicate_succ]
    change A * FreeGroup.mk (positive i) = A ^ (i+1)
    rw [ih,pow_succ']

lemma mk_v (i : ℕ) : FreeGroup.mk (v i) = conjugate i := by
  simp only [v,← FreeGroup.mul_mk,← FreeGroup.inv_mk,mk_positive,conjugate]
  rfl

lemma mk_replacement (i : ℕ) : FreeGroup.mk (replacement i) =
    substitute (FreeGroup.of i) := by
  simp only [replacement,← FreeGroup.mul_mk,← FreeGroup.inv_mk,mk_v,
    substitute,FreeGroup.lift_apply_of]
  rfl

lemma mk_substituteRaw (w : RecursiveUniversal.Word) : FreeGroup.mk (substituteRaw w) =
    substitute (FreeGroup.mk w) := by
  induction w with
  | nil => exact (map_one substitute).symm
  | cons x w ih =>
    rcases x with ⟨i,b⟩
    cases b with
    | false =>
      change FreeGroup.mk (FreeGroup.invRev (replacement i) ++ substituteRaw w) =
        substitute ((FreeGroup.of i)⁻¹ * FreeGroup.mk w)
      rw [← FreeGroup.mul_mk,← FreeGroup.inv_mk,mk_replacement,map_mul,map_inv,ih]
    | true =>
      change FreeGroup.mk (replacement i ++ substituteRaw w) =
        substitute (FreeGroup.of i * FreeGroup.mk w)
      rw [← FreeGroup.mul_mk,mk_replacement,map_mul,ih]

lemma enumerated_relations : Set.range (fun k => FreeGroup.mk (enumerator k)) =
    substitute '' RecursiveUniversal.allRelations := by
  ext r
  constructor
  · rintro ⟨k,rfl⟩
    exact ⟨FreeGroup.mk (RecursiveUniversal.relator k),⟨k,rfl⟩,(mk_substituteRaw _).symm⟩
  · rintro ⟨_,⟨k,rfl⟩,rfl⟩
    exact ⟨k,mk_substituteRaw _⟩

lemma invRev_primrec : Primrec (@FreeGroup.invRev Alphabet) := by
  unfold FreeGroup.invRev
  apply Primrec.list_reverse.comp
  apply Primrec.list_map Primrec.id
  exact (Primrec.fst.comp Primrec.snd).pair
    ((Primrec.dom_bool Bool.not).comp (Primrec.snd.comp Primrec.snd))

lemma positive_primrec : Primrec positive := by
  have h : Primrec (fun i : ℕ => (List.range i).map (fun _ => ((Sum.inl false,true) : Alphabet × Bool))) :=
    Primrec.list_map Primrec.list_range (Primrec₂.const _)
  apply h.of_eq
  intro i
  simp only [List.map_const',List.length_range,positive]

lemma v_primrec : Primrec v :=
  Primrec.list_append.comp
    (Primrec.list_append.comp positive_primrec (Primrec.const _))
    (invRev_primrec.comp positive_primrec)

lemma replacement_primrec : Primrec replacement :=
  Primrec.list_append.comp
    (Primrec.list_append.comp (Primrec.list_append.comp (Primrec.const _) v_primrec) (Primrec.const _))
    (invRev_primrec.comp v_primrec)

lemma substituteRaw_primrec : Primrec substituteRaw := by
  have h : Primrec (fun x : ℕ × Bool =>
      if x.2 then replacement x.1 else FreeGroup.invRev (replacement x.1)) := by
    apply (Primrec.cond Primrec.snd (replacement_primrec.comp Primrec.fst)
      (invRev_primrec.comp (replacement_primrec.comp Primrec.fst))).of_eq
    intro x
    cases x.2 <;> rfl
  exact Primrec.list_flatMap Primrec.id (h.comp Primrec.snd)

theorem enumerator_primrec : Primrec enumerator :=
  substituteRaw_primrec.comp RecursiveUniversal.relator_primrec

abbrev Universal := PresentedGroup (Set.range (fun k => FreeGroup.mk (enumerator k)))

theorem universal {G : Type*} [Group G] [Group.IsFinitelyPresented G] :
    ∃ h : G →* Universal, Function.Injective h := by
  obtain ⟨e,he⟩ := RecursiveUniversal.universal (G := G)
  let q := QuotientGroup.quotientMulEquivOfEq
    (congrArg Subgroup.normalClosure enumerated_relations.symm)
  exact ⟨q.toMonoidHom.comp ((ThreePresentation.fromC _).comp e),
    q.injective.comp ((ThreePresentation.fromC_injective _).comp he)⟩

end UniversalFInfinity.RecursiveUniversalThree

namespace UniversalFInfinity
universe z

theorem exists_universal_finitely_presented :
    ∃ (U : Type) (_ : Group U) (_ : Group.IsFinitelyPresented U),
      ∀ (G : Type z) [Group G] [Group.IsFinitelyPresented G],
        ∃ i : G →* U, Function.Injective i := by
  obtain ⟨U,gU,fpU,i,hi⟩ := Higman.NormalWords.embeds_presentation
    RecursiveUniversalThree.enumerator RecursiveUniversalThree.enumerator_primrec.to_comp
  refine ⟨U,gU,fpU,?_⟩
  intro G _ _
  obtain ⟨j,hj⟩ := RecursiveUniversalThree.universal (G := G)
  exact ⟨i.comp j,hi.comp hj⟩

end UniversalFInfinity

end
end UniversalFinitelyPresentedProof

end OAI
