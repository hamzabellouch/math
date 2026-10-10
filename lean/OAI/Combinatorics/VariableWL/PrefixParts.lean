import OAI.Combinatorics.VariableWL.PortGame

namespace OAI

namespace VariableWL.PrefixParts
open VariableWL.Affine
open scoped CharTwo
attribute [local instance] Classical.propDecidable

structure Data where
  dimension : ℕ
  channels : ℕ
  positive : 0 < channels
  root : Fin channels → ℕ
  root_le : ∀ c, root c ≤ dimension
  zero_root : root ⟨0,positive⟩ = 0
  order : Fin channels → Equiv.Perm (Fin dimension)
  legal : Bit → Set (Vec dimension)
  nonempty : ∀ ε, (legal ε).Nonempty
  coset : ∀ (ξ : Vec dimension), ξ ∈ legal 1 →
    ∀ z, z ∈ legal 0 ↔ z+ξ ∈ legal 1

namespace Data
@[simp] theorem vec_add_self {a : ℕ} (v : Vec a) : v+v=0 := by
  ext i; simp

variable (D : Data)
abbrev Valuation (ε : Bit) := {z : Vec D.dimension // z ∈ D.legal ε}

noncomputable def translate (ξ : D.Valuation 1) : D.Valuation 0 ≃ D.Valuation 1 where
  toFun z := ⟨z.val+ξ.val,(D.coset _ ξ.property _).mp z.property⟩
  invFun z := ⟨z.val+ξ.val,(D.coset _ ξ.property _).mpr (by rw [add_assoc,vec_add_self,add_zero]; exact z.property)⟩
  left_inv z := by ext i; simp
  right_inv z := by ext i; simp

def truncate {a : ℕ} (h : ℕ) (u : Vec a) : Vec a := fun i => if i.val<h then u i else 0

theorem truncate_add {a h : ℕ} (u v : Vec a) : truncate h (u+v)=truncate h u+truncate h v := by
  ext i; simp only [truncate,Pi.add_apply]; split_ifs <;> simp

theorem truncate_truncate {a h k : ℕ} (hk : h ≤ k) (u : Vec a) :
    truncate h (truncate k u)=truncate h u := by
  ext i; simp only [truncate]; split_ifs <;> (first | rfl | omega)

@[simp] theorem truncate_zero {a : ℕ} (u : Vec a) : truncate 0 u=0 := by
  ext i; simp [truncate]

@[simp] theorem truncate_full {a : ℕ} (u : Vec a) : truncate a u=u := by
  ext i; simp [truncate,i.isLt]

abbrev RawTree := Fin D.channels × Fin (D.dimension+1) × Vec D.dimension

def TreeLegal (ε : Bit) (t : D.RawTree) : Prop :=
  D.root t.1 ≤ t.2.1.val ∧ ∃ z : D.Valuation ε,
    truncate t.2.1.val (z.val ∘ D.order t.1)=t.2.2

abbrev Tree (ε : Bit) := {t : D.RawTree // D.TreeLegal ε t}
abbrev Vertex (ε : Bit) := Unit ⊕ ((Fin D.channels × D.Valuation ε) ⊕ D.Tree ε)

namespace Tree
variable {D} {ε : Bit}
abbrev channel (t : D.Tree ε) := t.val.1
abbrev height (t : D.Tree ε) := t.val.2.1.val
abbrev bits (t : D.Tree ε) := t.val.2.2

def ofValuation (c : Fin D.channels) (h : ℕ) (hqa : D.root c ≤ h) (ha : h ≤ D.dimension)
    (z : D.Valuation ε) : D.Tree ε :=
  ⟨(c,⟨h,by omega⟩,truncate h (z.val ∘ D.order c)),hqa,z,rfl⟩

@[ext] theorem ext {t u : D.Tree ε} (hc : t.channel=u.channel)
    (hh : t.height=u.height) (hb : t.bits=u.bits) : t=u := by
  apply Subtype.ext
  exact Prod.ext hc (Prod.ext (Fin.ext hh) hb)

theorem truncated (t : D.Tree ε) : truncate t.height t.bits=t.bits := by
  obtain ⟨_,z,hz⟩ := t.property
  change truncate t.height (z.val ∘ D.order t.channel)=t.bits at hz
  rw [← hz,truncate_truncate le_rfl]

theorem above_zero (t : D.Tree ε) (i : Fin D.dimension) (hi : t.height ≤ i.val) : t.bits i=0 := by
  have h := congrFun t.truncated i
  simpa [truncate,show ¬i.val<t.height by omega] using h.symm

theorem height_zero (t : D.Tree ε) (hh : t.height=0) : t.bits=0 := by
  rw [← t.truncated,hh,truncate_zero]

end Tree

variable {D}
def TreeStep {ε : Bit} (t u : D.Tree ε) : Prop :=
  t.channel=u.channel ∧ t.height+1=u.height ∧ truncate t.height u.bits=t.bits

def Forward {ε : Bit} : D.Vertex ε → D.Vertex ε → Prop
  | .inl _, .inr (.inr t) => t.channel.val=0 ∧ t.height=0
  | .inr (.inl (c,z)), .inr (.inl (d,w)) => c.val+1=d.val ∧ z=w
  | .inr (.inr t), .inr (.inr u) => TreeStep t u
  | .inr (.inr t), .inr (.inl (c,z)) =>
      t.channel=c ∧ t.height=D.dimension ∧ t.bits=z.val ∘ D.order c
  | _, _ => False

variable (D)
def graph (ε : Bit) : SimpleGraph (D.Vertex ε) where
  Adj x y := Forward x y ∨ Forward y x
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨by
    intro x
    cases x with
    | inl u => simp [Forward]
    | inr v =>
      cases v with
      | inl v => simp only [Forward,or_self]; omega
      | inr t => simp only [Forward,TreeStep,or_self]; omega⟩

noncomputable def treeTranslation (ξ : D.Valuation 1) : D.Tree 0 ≃ D.Tree 1 where
  toFun t := ⟨(t.channel,t.val.2.1,t.bits+truncate t.height (ξ.val ∘ D.order t.channel)),by
    refine ⟨t.property.1,?_⟩
    obtain ⟨z,hz⟩ := t.property.2
    refine ⟨D.translate ξ z,?_⟩
    change truncate t.height ((z.val+ξ.val) ∘ D.order t.channel)=_
    have he : (z.val+ξ.val) ∘ D.order t.channel = z.val ∘ D.order t.channel+ξ.val ∘ D.order t.channel := rfl
    rw [he,truncate_add,hz]⟩
  invFun t := ⟨(t.channel,t.val.2.1,t.bits+truncate t.height (ξ.val ∘ D.order t.channel)),by
    refine ⟨t.property.1,?_⟩
    obtain ⟨z,hz⟩ := t.property.2
    refine ⟨(D.translate ξ).symm z,?_⟩
    change truncate t.height ((z.val+ξ.val) ∘ D.order t.channel)=_
    have he : (z.val+ξ.val) ∘ D.order t.channel = z.val ∘ D.order t.channel+ξ.val ∘ D.order t.channel := rfl
    rw [he,truncate_add,hz]⟩
  left_inv t := by
    apply Tree.ext
    · rfl
    · rfl
    · change (t.bits+truncate t.height (ξ.val ∘ D.order t.channel))+truncate t.height (ξ.val ∘ D.order t.channel)=t.bits
      rw [add_assoc,vec_add_self,add_zero]
  right_inv t := by
    apply Tree.ext
    · rfl
    · rfl
    · change (t.bits+truncate t.height (ξ.val ∘ D.order t.channel))+truncate t.height (ξ.val ∘ D.order t.channel)=t.bits
      rw [add_assoc,vec_add_self,add_zero]

noncomputable def vertexTranslation (ξ : D.Valuation 1) : D.Vertex 0 ≃ D.Vertex 1 :=
  Equiv.sumCongr (Equiv.refl Unit) (Equiv.sumCongr
    (Equiv.prodCongr (Equiv.refl _) (D.translate ξ)) (D.treeTranslation ξ))

theorem treeTranslation_step (ξ : D.Valuation 1) (t u : D.Tree 0) :
    TreeStep (D.treeTranslation ξ t) (D.treeTranslation ξ u) ↔ TreeStep t u := by
  change (t.channel=u.channel ∧ t.height+1=u.height ∧
    truncate t.height (u.bits+truncate u.height (ξ.val ∘ D.order u.channel))=
      t.bits+truncate t.height (ξ.val ∘ D.order t.channel)) ↔ _
  constructor
  · rintro ⟨hc,hh,hb⟩
    refine ⟨hc,hh,?_⟩
    rw [truncate_add,truncate_truncate (by omega),← hc] at hb
    exact add_right_cancel hb
  · rintro ⟨hc,hh,hb⟩
    refine ⟨hc,hh,?_⟩
    rw [truncate_add,truncate_truncate (by omega),← hc,hb]

theorem vertexTranslation_forward (ξ : D.Valuation 1) (x y : D.Vertex 0) :
    Forward (D.vertexTranslation ξ x) (D.vertexTranslation ξ y) ↔ Forward x y := by
  cases x with
  | inl x => cases y with
    | inl y => rfl
    | inr y => cases y <;> rfl
  | inr x =>
    cases x with
    | inl x =>
      cases y with
      | inl y => rfl
      | inr y => cases y with
        | inl y => exact and_congr Iff.rfl (D.translate ξ).injective.eq_iff
        | inr y => rfl
    | inr x =>
      cases y with
      | inl y => rfl
      | inr y => cases y with
        | inr y => exact D.treeTranslation_step ξ x y
        | inl y =>
          rcases y with ⟨c,z⟩
          change (x.channel=c ∧ x.height=D.dimension ∧
            x.bits+truncate x.height (ξ.val ∘ D.order x.channel)=
              (z.val+ξ.val) ∘ D.order c) ↔ _
          constructor
          · rintro ⟨hc,hh,hb⟩
            refine ⟨hc,hh,?_⟩
            rw [hc,hh,truncate_full] at hb
            exact add_right_cancel (show x.bits+ξ.val ∘ D.order c=(z.val ∘ D.order c)+ξ.val ∘ D.order c from hb)
          · rintro ⟨hc,hh,hb⟩
            refine ⟨hc,hh,?_⟩
            rw [hc,hh,truncate_full,hb]
            rfl

noncomputable def translationIso (ξ : D.Valuation 1) : D.graph 0 ≃g D.graph 1 where
  toEquiv := D.vertexTranslation ξ
  map_rel_iff' := by intro x y; exact or_congr (D.vertexTranslation_forward ξ x y) (D.vertexTranslation_forward ξ y x)

theorem tree_to_leaf {ε : Bit} (c : Fin D.channels) (z : D.Valuation ε) :
    ∀ h (hq : D.root c ≤ h) (ha : h ≤ D.dimension),
    (D.graph ε).Reachable (.inr (.inr (Tree.ofValuation c h hq ha z)))
      (.inr (.inr (Tree.ofValuation c D.dimension (D.root_le c) le_rfl z))) := by
  intro h hq ha
  induction hd : D.dimension-h generalizing h with
  | zero => have he : h=D.dimension := by omega
            subst h
            exact SimpleGraph.Reachable.refl _
  | succ d ih =>
    have hlt : h < D.dimension := by omega
    have hs : (D.graph ε).Adj (.inr (.inr (Tree.ofValuation c h hq ha z)))
        (.inr (.inr (Tree.ofValuation c (h+1) (by omega) (by omega) z))) := by
      refine Or.inl ⟨rfl,rfl,?_⟩
      change truncate h (truncate (h+1) (z.val ∘ D.order c))=truncate h (z.val ∘ D.order c)
      exact truncate_truncate (by omega) _
    exact hs.reachable.trans (ih (h+1) (by omega) (by omega) (by omega))

theorem spine_to_zero {ε : Bit} (c : Fin D.channels) (z : D.Valuation ε) :
    (D.graph ε).Reachable (.inr (.inl (c,z))) (.inr (.inl (⟨0,D.positive⟩,z))) := by
  induction hc : c.val generalizing c with
  | zero => have he : c=⟨0,D.positive⟩ := Fin.ext hc
            subst c; exact SimpleGraph.Reachable.refl _
  | succ k ih =>
    let d : Fin D.channels := ⟨k,by omega⟩
    have hs : (D.graph ε).Adj (.inr (.inl (c,z))) (.inr (.inl (d,z))) := Or.inr ⟨hc.symm,rfl⟩
    exact hs.reachable.trans (ih d rfl)

theorem leaf_spine {ε : Bit} (c : Fin D.channels) (z : D.Valuation ε) :
    (D.graph ε).Adj (.inr (.inr (Tree.ofValuation c D.dimension (D.root_le c) le_rfl z)))
      (.inr (.inl (c,z))) := Or.inl ⟨rfl,rfl,truncate_full _⟩

theorem connected (ε : Bit) : (D.graph ε).Connected := by
  have hp : ∀ x : D.Vertex ε, (D.graph ε).Reachable x (.inl ()) := by
    have hs : ∀ (c : Fin D.channels) (z : D.Valuation ε),
        (D.graph ε).Reachable (.inr (.inl (c,z))) (.inl ()) := by
      intro c z
      have hr : D.root ⟨0,D.positive⟩ ≤ 0 := by rw [D.zero_root]
      have hroot : (D.graph ε).Adj (.inl ())
          (.inr (.inr (Tree.ofValuation ⟨0,D.positive⟩ 0 hr (Nat.zero_le _) z))) := Or.inl ⟨rfl,rfl⟩
      exact (D.spine_to_zero c z).trans ((D.leaf_spine ⟨0,D.positive⟩ z).reachable.symm.trans
        ((D.tree_to_leaf ⟨0,D.positive⟩ z 0 hr (Nat.zero_le _)).symm.trans hroot.reachable.symm))
    intro x
    rcases x with x | (⟨c,z⟩ | t)
    · cases x; exact SimpleGraph.Reachable.refl _
    · exact hs c z
    · obtain ⟨z,hz⟩ := t.property.2
      have he : t=Tree.ofValuation t.channel t.height t.property.1 (by have ht : t.height < D.dimension+1 := t.val.2.1.isLt; omega) z :=
        Tree.ext rfl rfl hz.symm
      rw [he]
      exact (D.tree_to_leaf _ _ _ _ _).trans ((D.leaf_spine _ _).reachable.trans (hs _ _))
  exact ⟨fun x y => (hp x).trans (hp y).symm⟩

end Data
end VariableWL.PrefixParts

namespace VariableWL.PrefixParts.Data
open VariableWL.Affine
open scoped CharTwo
attribute [local instance] Classical.propDecidable
variable {D : Data} {ε : Bit}

theorem Tree.height_le (t : D.Tree ε) : t.height ≤ D.dimension := Nat.le_of_lt_succ t.val.2.1.isLt

theorem TreeStep.lower_lt {t u : D.Tree ε} (h : TreeStep t u) : t.height < D.dimension := by
  have hu := u.height_le
  have hh := h.2.1
  omega

theorem TreeStep.parent_unique {t u v : D.Tree ε} (h : TreeStep u t) (h' : TreeStep v t) : u=v := by
  have hh := h.2.1
  have hh' := h'.2.1
  apply Tree.ext (h.1.trans h'.1.symm)
  · omega
  · have hh : u.height=v.height := by omega
    rw [← h.2.2,hh,h'.2.2]

theorem TreeStep.child_unique {t u v : D.Tree ε} (h : TreeStep t u) (h' : TreeStep t v)
    (hb : u.bits ⟨t.height,h.lower_lt⟩=v.bits ⟨t.height,h'.lower_lt⟩) : u=v := by
  have hh := h.2.1
  have hh' := h'.2.1
  apply Tree.ext (h.1.symm.trans h'.1)
  · omega
  · ext i
    rcases lt_trichotomy i.val t.height with hi | hi | hi
    · have hu := congrFun h.2.2 i
      have hv := congrFun h'.2.2 i
      simpa [truncate,hi] using hu.trans hv.symm
    · have he : i=⟨t.height,h.lower_lt⟩ := Fin.ext hi
      simpa only [he] using hb
    · rw [u.above_zero i (by omega),v.above_zero i (by omega)]

theorem Tree.root_unique {t u : D.Tree ε} (hc : t.channel=u.channel)
    (ht : t.height=0) (hu : u.height=0) : t=u :=
  Tree.ext hc (ht.trans hu.symm) ((t.height_zero ht).trans (u.height_zero hu).symm)

def bitPort (b : Bit) : Fin 3 := ⟨b.val+1,by have := ZMod.val_lt b; omega⟩

theorem bitPort_ne_zero (b : Bit) : bitPort b ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp only [bitPort,Fin.val_zero] at this
  omega

theorem bitPort_injective : Function.Injective bitPort := by
  intro a b h
  apply ZMod.val_injective 2
  have he := congrArg Fin.val h
  change a.val+1=b.val+1 at he
  omega

noncomputable def slot {ε : Bit} : D.Vertex ε → D.Vertex ε → Fin 3
  | .inl _, _ => 0
  | .inr (.inl (c,_)), .inr (.inl (d,_)) => if d.val<c.val then 0 else 1
  | .inr (.inl _), _ => 2
  | .inr (.inr _), .inl _ => 0
  | .inr (.inr _), .inr (.inl _) => 1
  | .inr (.inr t), .inr (.inr u) =>
      if u.height<t.height then 0 else
        if ht : t.height<D.dimension then bitPort (u.bits ⟨t.height,ht⟩) else 1

theorem slot_parent {t u : D.Tree ε} (h : TreeStep t u) :
    slot (.inr (.inr u)) (.inr (.inr t))=0 := by
  have hh := h.2.1
  simp only [slot,ite_eq_left (show t.height<u.height by omega)]

theorem slot_child {t u : D.Tree ε} (h : TreeStep t u) :
    slot (.inr (.inr t)) (.inr (.inr u))=bitPort (u.bits ⟨t.height,h.lower_lt⟩) := by
  have hh := h.2.1
  simp only [slot,ite_eq_right (show ¬u.height<t.height by omega),dite_eq_left h.lower_lt]

theorem leaf_unique (t : D.Tree ε) {c d : Fin D.channels} {z w : D.Valuation ε}
    (h : t.channel=c ∧ t.height=D.dimension ∧ t.bits=z.val ∘ D.order c)
    (h' : t.channel=d ∧ t.height=D.dimension ∧ t.bits=w.val ∘ D.order d) : (c,z)=(d,w) := by
  have hc : c=d := h.1.symm.trans h'.1
  subst d
  apply Prod.ext
  · rfl
  apply Subtype.ext
  ext i
  have he := congrFun (h.2.2.symm.trans h'.2.2) ((D.order c).symm i)
  simpa only [Function.comp_apply,Equiv.apply_symm_apply] using he

theorem leaf_node_unique {t u : D.Tree ε} {c : Fin D.channels} {z : D.Valuation ε}
    (h : t.channel=c ∧ t.height=D.dimension ∧ t.bits=z.val ∘ D.order c)
    (h' : u.channel=c ∧ u.height=D.dimension ∧ u.bits=z.val ∘ D.order c) : t=u :=
  Tree.ext (h.1.trans h'.1.symm) (h.2.1.trans h'.2.1.symm) (h.2.2.trans h'.2.2.symm)

theorem slot_injective (x : D.Vertex ε) :
    Function.Injective (fun y : (D.graph ε).neighborSet x => slot x y.val) := by
  rintro ⟨y,hy⟩ ⟨z,hz⟩ he
  change slot x y=slot x z at he
  apply Subtype.ext
  change y=z
  have hy' : Forward x y ∨ Forward y x := hy
  have hz' : Forward x z ∨ Forward z x := hz
  rcases x with x | (⟨c,v⟩ | t)
  · rcases y with y | (y | u) <;> rcases z with z | (z | w) <;>
      simp only [Forward,or_false] at hy' hz'; try contradiction
    obtain ⟨huc,hu⟩ := hy'
    obtain ⟨hwc,hw⟩ := hz'
    exact congrArg (fun a => Sum.inr (Sum.inr a)) (Tree.root_unique (Fin.ext (huc.trans hwc.symm)) hu hw)
  · rcases y with y | (⟨d,w⟩ | u) <;> rcases z with z | (⟨e,v'⟩ | t') <;>
      simp only [Forward,false_or,or_false] at hy' hz' <;> try contradiction
    · have hd : w=v := by rcases hy' with h | h; exact h.2.symm; exact h.2
      have he' : v'=v := by rcases hz' with h | h; exact h.2.symm; exact h.2
      subst w; subst v'
      have hc : d=e := by
        apply Fin.ext
        simp only [slot] at he
        split_ifs at he <;> (rcases hy' with h | h) <;> (rcases hz' with h' | h') <;>
          omega
      subst e; rfl
    · simp only [slot] at he
      split_ifs at he <;> have := congrArg Fin.val he <;> norm_num at this
    · simp only [slot] at he
      split_ifs at he <;> have := congrArg Fin.val he <;> norm_num at this
    · exact congrArg (fun a => Sum.inr (Sum.inr a)) (leaf_node_unique hy' hz')
  · rcases y with y | (⟨d,w⟩ | u) <;> rcases z with z | (⟨e,v'⟩ | t') <;>
      simp only [Forward,false_or,or_false] at hy' hz'
    · cases y; cases z; rfl
    · have := congrArg Fin.val he; norm_num [slot] at this
    · rcases hz' with h | h
      · rw [slot_child h] at he
        exact (bitPort_ne_zero _ he.symm).elim
      · have ht := hy'.2
        have hh := h.2.1
        omega
    · have := congrArg Fin.val he; norm_num [slot] at this
    · exact congrArg (fun a => Sum.inr (Sum.inl a)) (leaf_unique t hy' hz')
    · rcases hz' with h | h
      · have hh := h.lower_lt; omega
      · rw [slot_parent h] at he
        have := congrArg Fin.val he; norm_num [slot] at this
    · rcases hy' with h | h
      · rw [slot_child h] at he
        exact (bitPort_ne_zero _ he).elim
      · have ht := hz'.2
        have hh := h.2.1
        omega
    · rcases hy' with h | h
      · have hh := h.lower_lt; omega
      · rw [slot_parent h] at he
        have := congrArg Fin.val he; norm_num [slot] at this
    · rcases hy' with h | h <;> rcases hz' with h' | h'
      · rw [slot_child h,slot_child h'] at he
        exact congrArg (fun a => Sum.inr (Sum.inr a)) (h.child_unique h' (bitPort_injective he))
      · rw [slot_child h,slot_parent h'] at he
        exact (bitPort_ne_zero _ he).elim
      · rw [slot_parent h,slot_child h'] at he
        exact (bitPort_ne_zero _ he.symm).elim
      · exact congrArg (fun a => Sum.inr (Sum.inr a)) (h.parent_unique h')

theorem degree_le_three (x : D.Vertex ε) : (D.graph ε).degree x ≤ 3 := by
  have hc := Fintype.card_le_of_injective _ (slot_injective x)
  simpa only [SimpleGraph.card_neighborSet_eq_degree,Fintype.card_fin] using hc

end VariableWL.PrefixParts.Data

namespace VariableWL.PrefixParts.Data
open VariableWL.Affine
attribute [local instance] Classical.propDecidable
variable {D : Data}

def portAlphabet : Fin 3 ≃ Option Bit := finSuccEquiv 2

@[simp] theorem portAlphabet_zero : portAlphabet 0=none := rfl

@[simp] theorem portAlphabet_bitPort (b : Bit) : portAlphabet (bitPort b)=some b := by
  exact finSuccEquiv_succ b

def shiftPorts (b : Bit) : Equiv.Perm (Fin 3) :=
  portAlphabet.trans ((Equiv.optionCongr (Equiv.addRight b)).trans portAlphabet.symm)

@[simp] theorem shiftPorts_zero (b : Bit) : shiftPorts b 0=0 := by
  apply portAlphabet.injective
  simp [shiftPorts]

@[simp] theorem shiftPorts_bitPort (a b : Bit) : shiftPorts b (bitPort a)=bitPort (a+b) := by
  apply portAlphabet.injective
  simp [shiftPorts]

noncomputable def localPorts (ξ : D.Valuation 1) : D.Vertex 0 → Equiv.Perm (Fin 3)
  | .inr (.inr t) => if h : t.height<D.dimension then
      shiftPorts (ξ.val (D.order t.channel ⟨t.height,h⟩)) else Equiv.refl _
  | _ => Equiv.refl _

@[simp] theorem localPorts_zero (ξ : D.Valuation 1) (x : D.Vertex 0) : localPorts ξ x 0=0 := by
  rcases x with x | (x | t) <;> simp only [localPorts,Equiv.refl_apply]
  split_ifs <;> simp

theorem slot_translation (ξ : D.Valuation 1) (x y : D.Vertex 0)
    (ha : (D.graph 0).Adj x y) :
    slot (D.vertexTranslation ξ x) (D.vertexTranslation ξ y)=localPorts ξ x (slot x y) := by
  have h : Forward x y ∨ Forward y x := ha
  rcases x with x | (⟨c,z⟩ | t)
  · rcases y with y | (y | u) <;> rfl
  · rcases y with y | (y | u) <;> rfl
  · rcases y with y | (⟨c,z⟩ | u)
    · change 0=localPorts ξ (.inr (.inr t)) 0
      exact (localPorts_zero ξ _).symm
    · have hl : t.channel=c ∧ t.height=D.dimension ∧ t.bits=z.val ∘ D.order c := by
        simpa only [Forward,or_false] using h
      change 1=(if ht : t.height<D.dimension then _ else Equiv.refl (Fin 3)) 1
      simp only [hl.2.1,lt_self_iff_false,dite_false,Equiv.refl_apply]
    · rcases h with h | h
      · have h' := (D.treeTranslation_step ξ t u).mpr h
        change slot (.inr (.inr (D.treeTranslation ξ t))) (.inr (.inr (D.treeTranslation ξ u)))=_
        rw [slot_child h',slot_child h]
        have hh := h.2.1
        change bitPort ((u.bits+truncate u.height (ξ.val ∘ D.order u.channel)) ⟨t.height,h.lower_lt⟩)=_
        rw [show localPorts ξ (.inr (.inr t))=shiftPorts (ξ.val (D.order t.channel ⟨t.height,h.lower_lt⟩)) by
          simp only [localPorts,dite_eq_left h.lower_lt],shiftPorts_bitPort]
        congr 1
        simp only [Pi.add_apply,truncate,ite_eq_left (show t.height<u.height by omega),Function.comp_apply,h.1]
      · have h' := (D.treeTranslation_step ξ u t).mpr h
        change slot (.inr (.inr (D.treeTranslation ξ t))) (.inr (.inr (D.treeTranslation ξ u)))=_
        rw [slot_parent h',slot_parent h,localPorts_zero]

theorem proper_root_reserved {ε : Bit} (t : D.Tree ε)
    (hc : t.channel.val ≠ 0) (hh : t.height=D.root t.channel)
    {y : D.Vertex ε} (hy : (D.graph ε).Adj (.inr (.inr t)) y) :
    slot (.inr (.inr t)) y ≠ 0 := by
  have hy' : Forward (.inr (.inr t)) y ∨ Forward y (.inr (.inr t)) := hy
  rcases y with y | (⟨c,z⟩ | u)
  · simp only [Forward,false_or] at hy'
    exact (hc hy'.1).elim
  · change (1 : Fin 3) ≠ 0
    decide
  · rcases hy' with h | h
    · rw [slot_child h]
      exact bitPort_ne_zero _
    · have hroot := u.property.1
      change D.root u.channel ≤ u.height at hroot
      have hch := h.1
      have hht := h.2.1
      rw [hch] at hroot
      omega

end VariableWL.PrefixParts.Data

end OAI
