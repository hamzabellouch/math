import OAI.Combinatorics.VariableWL.PrefixListing

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8

namespace VariableWL.PrefixDescriptor
open VariableWL.Affine Descriptor PrefixParts
attribute [local instance] Classical.propDecidable
variable {B : Type uVariable1} [Fintype B] (P : Presentation B) (F : B → PrefixParts.Data)
variable (hDim : ∀b,(F b).dimension≤6) (ε : Bit)

 theorem raw_anchors {D : Data} (h : Good P F hDim ε D) (x y : Wiring.Vertex F ε) (i j : Fin 3) :
    let _ : FiniteNumbering B := P.numbering
    D.anchors (raw P F hDim ε x) (raw P F hDim ε y) i.val j.val=true ↔
      (Wiring.anchorPorts F ε).edge (x,i) (y,j) := by
  let _ : FiniteNumbering B := P.numbering
  rcases x with ⟨b,x | (x | t)⟩ <;> rcases y with ⟨d,y | (y | u)⟩
  all_goals try {
    simp only [Data.anchors,raw,one_ne_zero,show (2:ℕ)≠0 by omega,false_and,and_false,decide_false,Bool.false_eq_true]
    constructor
    · exact False.elim
    · rintro (⟨a,b,ha,hb,_⟩ | ⟨a,b,hb,ha,_⟩)
      all_goals first
      | have hx := congrArg (fun z : Wiring.Vertex F ε => (raw P F hDim ε z).kind) (congrArg Prod.fst ha)
        simp only [Wiring.anchor,raw] at hx
        omega
      | have hy := congrArg (fun z : Wiring.Vertex F ε => (raw P F hDim ε z).kind) (congrArg Prod.fst hb)
        simp only [Wiring.anchor,raw] at hy
        omega }
  cases x; cases y
  simp only [Data.anchors,raw,h.validBlock,true_and,decide_eq_true_eq]
  constructor
  · rintro (⟨hi,hj,he⟩ | ⟨hi,hj,he⟩)
    · left; exact ⟨b,d,by congr; exact Fin.ext hi,by congr; exact Fin.ext hj,by simpa only [Presentation.enumeration_val] using he⟩
    · right; exact ⟨d,b,by congr; exact Fin.ext hj,by congr; exact Fin.ext hi,by simpa only [Presentation.enumeration_val] using he⟩
  · rintro (⟨a,c,ha,hc,he⟩ | ⟨a,c,hc,ha,he⟩)
    · have hb : b=a := congrArg (fun z : Wiring.Vertex F ε × Fin 3=>z.1.1) ha
      have hd : d=c := congrArg (fun z : Wiring.Vertex F ε × Fin 3=>z.1.1) hc
      subst a; subst c
      exact Or.inl ⟨congrArg (fun z : Wiring.Vertex F ε × Fin 3=>z.2.val) ha,
        congrArg (fun z : Wiring.Vertex F ε × Fin 3=>z.2.val) hc,by simpa only [Presentation.enumeration_val] using he⟩
    · have hb : b=c := congrArg (fun z : Wiring.Vertex F ε × Fin 3=>z.1.1) ha
      have hd : d=a := congrArg (fun z : Wiring.Vertex F ε × Fin 3=>z.1.1) hc
      subst a; subst c
      exact Or.inr ⟨congrArg (fun z : Wiring.Vertex F ε × Fin 3=>z.2.val) ha,
        congrArg (fun z : Wiring.Vertex F ε × Fin 3=>z.2.val) hc,by simpa only [Presentation.enumeration_val] using he⟩

 theorem raw_incidence {D : Data} (h : Good P F hDim ε D) (W : Wiring F) (hm : MatchingGood P F D W)
    (x y : Wiring.Vertex F ε) (i j : Fin 3) :
    let _ : FiniteNumbering B := P.numbering
    D.incidence (3*D.pack (raw P F hDim ε x)+i.val) (3*D.pack (raw P F hDim ε y)+j.val)=true ↔
      (W.ports F ε).edge (x,i) (y,j) := by
  let _ : FiniteNumbering B := P.numbering
  have hi : i.val<3 := i.isLt
  have hj : j.val<3 := j.isLt
  have hx := raw_bounds P F hDim ε h x
  have hy := raw_bounds P F hDim ε h y
  simp only [Data.incidence,Nat.mul_add_div (by omega : 0<3),Nat.mul_add_mod,Nat.mod_eq_of_lt hi,
    Nat.mod_eq_of_lt hj,Nat.div_eq_of_lt hi,Nat.div_eq_of_lt hj,Nat.add_zero,
    D.unpack_pack _ hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2,
    D.unpack_pack _ hy.2.1 hy.2.2.1 hy.2.2.2.1 hy.2.2.2.2,
    Bool.or_eq_true,raw_internal P F hDim ε h,raw_roots P F hDim ε h W hm,raw_anchors P F hDim ε h,
    Wiring.ports,SubcubicRealization.PortGraph.union,or_assoc]

 omit [Fintype B] in
 theorem tag_sort {D : Data} (x : Wiring.Vertex F ε) :
    D.tag (raw P F hDim ε x)=D.tag (sortRaw P F (Wiring.sort F x)) := by
  rcases x with ⟨b,x | (x | x)⟩ <;> rfl

 theorem raw_color {D : Data} (h : Good P F hDim ε D) (Q : Presentation (Wiring.SortTag F))
    (hq : Q.valid=D.sortPredicate) (he : ∀s,Q.encode s=D.tag (sortRaw P F s))
    (x : Wiring.Vertex F ε) :
    let _ : FiniteNumbering (Wiring.SortTag F) := Q.numbering
    D.color (D.pack (raw P F hDim ε x))=Wiring.color F x := by
  let _ : FiniteNumbering (Wiring.SortTag F) := Q.numbering
  have hx := raw_bounds P F hDim ε h x
  rw [Data.color,D.unpack_pack _ hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2,tag_sort P F hDim ε]
  simp only [Wiring.color,Presentation.enumeration_val,hq,he,Nat.add_comm]

 omit [Fintype B] in
 theorem color_le {D : Data} (h : Good P F hDim ε D) (x : Wiring.Vertex F ε) :
    D.color (D.pack (raw P F hDim ε x))≤D.colorBound := by
  have hx := raw_bounds P F hDim ε h x
  rw [Data.color,D.unpack_pack _ hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2,Data.colorBound]
  apply Nat.add_le_add_left
  exact Descriptor.rank_mono D.sortPredicate (D.tag_lt _ hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1).le

end VariableWL.PrefixDescriptor

namespace VariableWL.Descriptor.Presentation
attribute [local instance] Classical.propDecidable
variable {A : Type uVariable2} {B : Type uVariable3}

noncomputable def product (P : Presentation A) (Q : Presentation B) : Presentation (A × B) :=
  ofEncoding (P.bound*Q.bound) (fun i=>P.valid (i/Q.bound) && Q.valid (i%Q.bound))
    (fun x=>P.encode x.1*Q.bound+Q.encode x.2)
    (fun x=>by have hp := P.encode_lt x.1; have hq := Q.encode_lt x.2; nlinarith)
    (fun x=>by
      have hq := Q.encode_lt x.2
      simp only [PrefixDescriptor.Data.join_div _ _ _ (by omega : 0<Q.bound) hq,
        PrefixDescriptor.Data.join_mod _ _ _ hq,P.encode_valid,Q.encode_valid,Bool.and_self])
    (by
      intro x y he
      have hx := Q.encode_lt x.2
      have hy := Q.encode_lt y.2
      have hm := congrArg (fun i=>i%Q.bound) he
      have hd := congrArg (fun i=>i/Q.bound) he
      dsimp only at hm hd
      rw [PrefixDescriptor.Data.join_mod _ _ _ hx,PrefixDescriptor.Data.join_mod _ _ _ hy] at hm
      rw [PrefixDescriptor.Data.join_div _ _ _ (by omega : 0<Q.bound) hx,
        PrefixDescriptor.Data.join_div _ _ _ (by omega : 0<Q.bound) hy] at hd
      exact Prod.ext (P.encode_injective hd) (Q.encode_injective hm))
    (by
      intro i hi hv
      have hq : 0<Q.bound := by nlinarith
      obtain ⟨hpv,hqv⟩ := Bool.and_eq_true_iff.mp hv
      let a : Valid P.bound P.valid := ⟨⟨i/Q.bound,(Nat.div_lt_iff_lt_mul hq).mpr hi⟩,hpv⟩
      let b : Valid Q.bound Q.valid := ⟨⟨i%Q.bound,Nat.mod_lt _ hq⟩,hqv⟩
      refine ⟨(P.equiv a,Q.equiv b),?_⟩
      simp only [encode,Equiv.symm_apply_apply]
      change (i/Q.bound)*Q.bound+i%Q.bound=i
      rw [Nat.mul_comm,Nat.div_add_mod])

@[simp] theorem product_encode (P : Presentation A) (Q : Presentation B) (x : A × B) :
    (P.product Q).encode x=P.encode x.1*Q.bound+Q.encode x.2 := rfl

noncomputable def sum (P : Presentation A) (Q : Presentation B) : Presentation (A ⊕ B) :=
  ofEncoding (P.bound+Q.bound) (fun i=>if i<P.bound then P.valid i else Q.valid (i-P.bound))
    (Sum.elim P.encode (fun b=>P.bound+Q.encode b))
    (fun x=>by cases x with
      | inl a => exact (P.encode_lt a).trans_le (Nat.le_add_right _ _)
      | inr b => have := Q.encode_lt b; dsimp; omega)
    (fun x=>by cases x with
      | inl a => exact (ite_eq_left (P.encode_lt a)).trans (P.encode_valid a)
      | inr b => simpa only [Sum.elim_inr,not_lt.mpr (Nat.le_add_right _ _),ite_false,Nat.add_sub_cancel_left] using Q.encode_valid b)
    (by
      rintro (a|a) (b|b) he
      · exact congrArg Sum.inl (P.encode_injective he)
      · have := P.encode_lt a; dsimp at he; omega
      · have := P.encode_lt b; dsimp at he; omega
      · exact congrArg Sum.inr (Q.encode_injective (Nat.add_left_cancel he)))
    (by
      intro i hi hv
      by_cases h : i<P.bound
      · rw [ite_eq_left h] at hv
        let a : Valid P.bound P.valid := ⟨⟨i,h⟩,hv⟩
        exact ⟨.inl (P.equiv a),by simp only [Sum.elim_inl,encode,Equiv.symm_apply_apply]; rfl⟩
      · rw [ite_eq_right h] at hv
        let b : Valid Q.bound Q.valid := ⟨⟨i-P.bound,by omega⟩,hv⟩
        exact ⟨.inr (Q.equiv b),by simp only [Sum.elim_inr,encode,Equiv.symm_apply_apply]; change P.bound+(i-P.bound)=i; omega⟩)

@[simp] theorem sum_inl (P : Presentation A) (Q : Presentation B) (a : A) :
    (P.sum Q).encode (.inl a)=P.encode a := rfl
@[simp] theorem sum_inr (P : Presentation A) (Q : Presentation B) (b : B) :
    (P.sum Q).encode (.inr b)=P.bound+Q.encode b := rfl

noncomputable def filter (P : Presentation A) (Q : ℕ → Bool) (T : A → Prop)
    (h : ∀a,Q (P.encode a)=true ↔ T a) : Presentation {a // T a} :=
  ofEncoding P.bound (fun i=>P.valid i && Q i) (fun a=>P.encode a.val)
    (fun a=>P.encode_lt a.val)
    (fun a=>Bool.and_eq_true_iff.mpr ⟨P.encode_valid a.val,(h a.val).mpr a.property⟩)
    (by intro a b he; exact Subtype.ext (P.encode_injective he))
    (by
      intro i hi hv
      obtain ⟨hp,hq⟩ := Bool.and_eq_true_iff.mp hv
      let a : Valid P.bound P.valid := ⟨⟨i,hi⟩,hp⟩
      have ha : P.encode (P.equiv a)=i := by simp only [encode,Equiv.symm_apply_apply]; rfl
      exact ⟨⟨P.equiv a,(h _).mp (ha ▸ hq)⟩,ha⟩)

@[simp] theorem filter_encode (P : Presentation A) (Q : ℕ → Bool) (T : A → Prop) (h) (a : {a // T a}) :
    (P.filter Q T h).encode a=P.encode a.val := rfl

end VariableWL.Descriptor.Presentation

namespace VariableWL.PrefixDescriptor
open VariableWL.Affine Descriptor PrefixParts SubcubicRealization
attribute [local instance] Classical.propDecidable
variable {B : Type uVariable4} [Fintype B] (P : Presentation B) (F : B → PrefixParts.Data)
variable (hDim : ∀b,(F b).dimension≤6) (ε : Bit)

 omit [Fintype B] in
 theorem presentation_inverse_val {D : Data} (h : Good P F hDim ε D) (x : Wiring.Vertex F ε) :
    ((presentation P F hDim ε h).equiv.symm x).val.val=D.pack (raw P F hDim ε x) := rfl

 theorem port_sound {D : Data} (h : Good P F hDim ε D) (W : Wiring F) (hm : MatchingGood P F D W) :
    D.portData.Sound := by
  let _ : FiniteNumbering B := P.numbering
  let Q := presentation P F hDim ε h
  apply PortData.sound_of_encoding D.portData Q.equiv.symm Q.equiv.symm.bijective (W.ports F ε)
  · intro x
    exact color_le P F hDim ε h x
  · intro x y i j
    exact raw_incidence P F hDim ε h W hm x y i j

noncomputable def uncoloredIso {D : Data} (h : Good P F hDim ε D) (W : Wiring F)
    (hm : MatchingGood P F D W) (S : Presentation (Wiring.SortTag F))
    (hs : S.valid=D.sortPredicate) (he : ∀s,S.encode s=D.tag (sortRaw P F s)) :
    let _ : FiniteNumbering B := P.numbering
    let _ : FiniteNumbering (Wiring.SortTag F) := S.numbering
    (D.portData.expanded.graph (D.portData.sound_expanded (port_sound P F hDim ε h W hm))).graph ≃g
      Wiring.uncolored F W ε := by
  let _ : FiniteNumbering B := P.numbering
  let _ : FiniteNumbering (Wiring.SortTag F) := S.numbering
  let Q := presentation P F hDim ε h
  have hc (a : D.portData.Owners) : Wiring.color F (Q.equiv a)=D.color a.val.val := by
    obtain ⟨x,rfl⟩ := Q.equiv.symm.surjective a
    simpa only [Equiv.apply_symm_apply,Q,presentation_inverse_val] using (raw_color P F hDim ε h S hs he x).symm
  let E := vertexEquiv Q.equiv (fun _=>Equiv.refl (Fin 3)) hc
  let T : SubcubicRealization.graph (D.portData.ports (port_sound P F hDim ε h W hm))
      (fun a=>D.color a.val.val) ≃g Wiring.uncolored F W ε := {
    toEquiv := E
    map_rel_iff' := by
      intro x y
      apply vertexEquiv_adj
      obtain ⟨a,ha⟩ := Q.equiv.symm.surjective x.owner
      obtain ⟨b,hb⟩ := Q.equiv.symm.surjective y.owner
      change D.incidence (3*x.owner.val.val+x.port.val) (3*y.owner.val.val+y.port.val)=true ↔ _
      rw [←ha,←hb]
      simpa only [Equiv.apply_symm_apply,Equiv.refl_apply,Q,presentation_inverse_val] using raw_incidence P F hDim ε h W hm a b x.port y.port }
  exact (D.portData.graphIso (port_sound P F hDim ε h W hm)).trans T
end VariableWL.PrefixDescriptor

namespace VariableWL.Descriptor.Presentation
variable {A : Type uVariable5} {B : Type uVariable6}
def transport (P : Presentation A) (e : A ≃ B) : Presentation B := ⟨P.bound,P.valid,P.equiv.trans e⟩
@[simp] theorem transport_encode (P : Presentation A) (e : A ≃ B) (a : A) :
    (P.transport e).encode (e a)=P.encode a := by
  change ((P.equiv.symm (e.symm (e a))).val.val)=_
  rw [Equiv.symm_apply_apply]
  rfl

def fin (n : ℕ) : Presentation (Fin n) where
  bound := n
  valid _ := true
  equiv := { toFun a:=a.val, invFun a:=⟨a,rfl⟩,left_inv _:=rfl,right_inv _:=rfl }
@[simp] theorem fin_encode (n : ℕ) (a : Fin n) : (fin n).encode a=a.val := rfl

theorem count_eq_card [Fintype A] (P : Presentation A) : Descriptor.rank P.valid P.bound=Fintype.card A := by
  simpa only [Fintype.card_fin] using (Fintype.card_congr (Descriptor.rankEquiv P.bound P.valid)).symm.trans
    (Fintype.card_congr P.equiv)

theorem pick_enumeration [Fintype A] (P : Presentation A) (a : A) :
    Descriptor.pick P.bound P.valid ((@VariableWL.enumeration A _ P.numbering) a).val=P.encode a :=
  Descriptor.pick_rank _ _ _ (P.encode_lt a) (P.encode_valid a)
end VariableWL.Descriptor.Presentation

namespace VariableWL.BlockDescriptor
open Blocks BlockCoordinates Descriptor
attribute [local instance] Classical.propDecidable
variable {r n : ℕ} {P : Type uVariable7} {E : Type uVariable8} [Fintype P] [Fintype E]
variable (J : ProductImages.Instance r P E)
variable (PB : Presentation (Block (n := n) J)) (PR : Presentation (Readout r n P E))
variable (H : ℕ → ℕ → Bool)
variable (hH : ∀b : Block (n := n) J,∀a,H (PB.encode b) (PR.encode a)=true ↔ HasReadout J b.val a)

noncomputable def properEquiv (b : Block (n := n) J) : Proper J b ≃
    {x : Block (n := n) J × Readout r n P E // x.1≠b ∧ HasReadout J b.val x.2 ∧ HasReadout J x.1.val x.2} where
  toFun p := ⟨(p.1.val,p.2.val),p.1.property,p.2.property⟩
  invFun x := ⟨⟨x.val.1,x.property.1⟩,x.val.2,x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def ProperPredicate (b i : ℕ) : Bool :=
  decide (i/PR.bound≠b) && (H b (i%PR.bound) && H (i/PR.bound) (i%PR.bound))

 omit [Fintype P] [Fintype E] in
 include hH in
 theorem properPredicate_code (b c : Block (n := n) J) (a : Readout r n P E) :
    ProperPredicate PR H (PB.encode b) (PB.encode c*PR.bound+PR.encode a)=true ↔
      c≠b ∧ HasReadout J b.val a ∧ HasReadout J c.val a := by
  have ha := PR.encode_lt a
  simp only [ProperPredicate,PrefixDescriptor.Data.join_div _ _ _ (by omega : 0<PR.bound) ha,
    PrefixDescriptor.Data.join_mod _ _ _ ha,Bool.and_eq_true,decide_eq_true_eq,
    hH]
  exact and_congr_left (fun _=>not_congr PB.encode_injective.eq_iff)

noncomputable def properPresentation (b : Block (n := n) J) : Presentation (Proper J b) :=
  ((PB.product PR).filter (ProperPredicate PR H (PB.encode b))
    (fun x=>x.1≠b ∧ HasReadout J b.val x.2 ∧ HasReadout J x.1.val x.2)
    (fun x=>properPredicate_code J PB PR H hH b x.1 x.2)).transport (properEquiv J b).symm

 omit [Fintype P] [Fintype E] in
 theorem properPresentation_encode (b : Block (n := n) J) (p : Proper J b) :
    (properPresentation J PB PR H hH b).encode p=PB.encode p.1.val*PR.bound+PR.encode p.2.val := rfl

 omit [Fintype P] [Fintype E] in
 theorem properPresentation_valid (b : Block (n := n) J) (i : ℕ) :
    (properPresentation J PB PR H hH b).valid i=
      ((PB.valid (i/PR.bound) && PR.valid (i%PR.bound)) && ProperPredicate PR H (PB.encode b) i) := rfl

 theorem properNumber_val (b : Block (n := n) J) (p : Proper J b) :
    let _ : ∀b : Block (n := n) J, FiniteNumbering (Proper J b) := fun b=>(properPresentation J PB PR H hH b).numbering
    (properNumber J b p).val.val=Descriptor.rank (properPresentation J PB PR H hH b).valid
      (PB.encode p.1.val*PR.bound+PR.encode p.2.val)+1 := rfl

 theorem properNumber_pick (b : Block (n := n) J) (p : Proper J b) :
    let _ : ∀b : Block (n := n) J, FiniteNumbering (Proper J b) := fun b=>(properPresentation J PB PR H hH b).numbering
    Descriptor.pick (PB.bound*PR.bound) (properPresentation J PB PR H hH b).valid
      ((properNumber J b p).val.val-1)=PB.encode p.1.val*PR.bound+PR.encode p.2.val := by
  let _ : ∀b : Block (n := n) J, FiniteNumbering (Proper J b) := fun b=>(properPresentation J PB PR H hH b).numbering
  dsimp only
  change Descriptor.pick _ _ (Descriptor.rank _ _ + 1 - 1)=_
  rw [Nat.add_sub_cancel]
  exact Descriptor.pick_rank _ _ _ ((properPresentation J PB PR H hH b).encode_lt p)
    ((properPresentation J PB PR H hH b).encode_valid p)
end VariableWL.BlockDescriptor

namespace VariableWL.BlockDescriptor
structure Core where
  blocks : ℕ
  validBlock : ℕ → Bool
  reads : ℕ
  validRead : ℕ → Bool
  has : ℕ → ℕ → Bool
  dimension : ℕ → ℕ
  readDimension : ℕ → ℕ
  zeroOrder : ℕ → ℕ
  readOrder : ℕ → ℕ → ℕ
  legal : ℕ → ℕ → Bool
namespace Core
variable (D : Core)
def properBound : ℕ := D.blocks*D.reads
def channelBound : ℕ := D.properBound+1
def proper (b i : ℕ) : Bool :=
  (D.validBlock (i/D.reads) && D.validRead (i%D.reads)) &&
    (decide (i/D.reads≠b) && (D.has b (i%D.reads) && D.has (i/D.reads) (i%D.reads)))
def channels (b : ℕ) : ℕ := Descriptor.rank (D.proper b) D.properBound+1
def select (b c : ℕ) : ℕ := Descriptor.pick D.properBound (D.proper b) (c-1)
def other (b c : ℕ) : ℕ := D.select b c/D.reads
def readout (b c : ℕ) : ℕ := D.select b c%D.reads
def root (b c : ℕ) : ℕ := if c=0 then 0 else D.readDimension (D.readout b c)
def order (b c : ℕ) : ℕ := if c=0 then D.zeroOrder b else D.readOrder b (D.readout b c)
def matching (i j : ℕ) : Bool :=
  decide (D.other (i/D.channelBound) (i%D.channelBound)=j/D.channelBound ∧
    D.other (j/D.channelBound) (j%D.channelBound)=i/D.channelBound ∧
    D.readout (i/D.channelBound) (i%D.channelBound)=D.readout (j/D.channelBound) (j%D.channelBound))
def toPrefix : PrefixDescriptor.Data where
  blocks := D.blocks
  validBlock := D.validBlock
  channelBound := D.channelBound
  dimension := D.dimension
  channels := D.channels
  root := D.root
  order := D.order
  legal := D.legal
  matching := D.matching
 theorem channelBound_pos : 0<D.channelBound := Nat.zero_lt_succ _
 theorem channels_le (b : ℕ) : D.channels b≤D.channelBound := by
  apply Nat.add_le_add_right
  exact List.countP_le_length.trans_eq List.length_range
end Core
end VariableWL.BlockDescriptor

namespace VariableWL.BlockDescriptor.Program
open Computation.Stack.PolyRecipe Computation.Stack.Recipe
variable {n : ℕ}
structure Listing (n : ℕ) where
  blocks : Expr n
  validBlock : Expr (n+1)
  reads : Expr n
  validRead : Expr (n+1)
  has : Expr (n+2)
  dimension : Expr (n+1)
  readDimension : Expr (n+1)
  zeroOrder : Expr (n+1)
  readOrder : Expr (n+2)
  legal : Expr (n+2)
namespace Listing
variable (D : Listing n)
def eval (v : Env n) : Core where
  blocks := D.blocks.number v
  validBlock i := D.validBlock.bit (cons (List.replicate i true) v)
  reads := D.reads.number v
  validRead i := D.validRead.bit (cons (List.replicate i true) v)
  has i j := D.has.bit (cons (List.replicate i true) (cons (List.replicate j true) v))
  dimension i := D.dimension.number (cons (List.replicate i true) v)
  readDimension i := D.readDimension.number (cons (List.replicate i true) v)
  zeroOrder i := D.zeroOrder.number (cons (List.replicate i true) v)
  readOrder i j := D.readOrder.number (cons (List.replicate i true) (cons (List.replicate j true) v))
  legal i j := D.legal.bit (cons (List.replicate i true) (cons (List.replicate j true) v))
def up : Listing (n+1) where
  blocks := D.blocks.up
  validBlock := underOne D.validBlock
  reads := D.reads.up
  validRead := underOne D.validRead
  has := underTwo D.has
  dimension := underOne D.dimension
  readDimension := underOne D.readDimension
  zeroOrder := underOne D.zeroOrder
  readOrder := underTwo D.readOrder
  legal := underTwo D.legal
 theorem eval_up (v : Env n) (a : Word) : D.up.eval (cons a v)=D.eval v := by
  unfold eval up
  congr 1
  · funext i; exact underOne_bit ..
  · funext i; exact underOne_bit ..
  · funext i j; exact underTwo_bit ..
  · funext i; exact underOne_number ..
  · funext i; exact underOne_number ..
  · funext i; exact underOne_number ..
  · funext i j; exact underTwo_number ..
  · funext i j; exact underTwo_bit ..

def properBound : Expr n := mul D.blocks D.reads
def channelBound : Expr n := add D.properBound (numeral 1)
def proper (B I : Expr n) : Expr n :=
  conj (conj (applyNat D.validBlock (div I D.reads)) (applyNat D.validRead (mod I D.reads)))
    (conj (neg (eq (div I D.reads) B))
      (conj (applyNat₂ D.has B (mod I D.reads)) (applyNat₂ D.has (div I D.reads) (mod I D.reads))))
def channels (B : Expr n) : Expr n := add (count D.properBound (D.up.proper B.up (input 0))) (numeral 1)
def select (B C : Expr n) : Expr n := Computation.Stack.PolyRecipe.select D.properBound (D.up.proper B.up (input 0)) (sub C (numeral 1))
def other (B C : Expr n) : Expr n := div (D.select B C) D.reads
def readout (B C : Expr n) : Expr n := mod (D.select B C) D.reads
def root (B C : Expr n) : Expr n := choose (eq C (numeral 0)) (numeral 0) (applyNat D.readDimension (D.readout B C))
def order (B C : Expr n) : Expr n := choose (eq C (numeral 0)) (applyNat D.zeroOrder B) (applyNat₂ D.readOrder B (D.readout B C))
def matching (I J : Expr n) : Expr n :=
  conj (eq (D.other (div I D.channelBound) (mod I D.channelBound)) (div J D.channelBound))
    (conj (eq (D.other (div J D.channelBound) (mod J D.channelBound)) (div I D.channelBound))
      (eq (D.readout (div I D.channelBound) (mod I D.channelBound)) (D.readout (div J D.channelBound) (mod J D.channelBound))))
 theorem properBound_number (v : Env n) : D.properBound.number v=(D.eval v).properBound := by
  simp only [properBound,mul_number,Core.properBound,eval]
 theorem channelBound_number (v : Env n) : D.channelBound.number v=(D.eval v).channelBound := by
  simp only [channelBound,add_number,numeral_number,properBound_number,Core.channelBound]
 theorem proper_bit (B I : Expr n) (v : Env n) : (D.proper B I).bit v=(D.eval v).proper (B.number v) (I.number v) := by
  simp only [proper,conj_bit,neg_bit,eq_bit,div_number,mod_number,applyNat_bit,applyNat₂_bit,Core.proper,eval]
  rw [←decide_not]
  rfl
 theorem channels_number (B : Expr n) (v : Env n) : (D.channels B).number v=(D.eval v).channels (B.number v) := by
  simp only [channels,add_number,count_number,properBound_number,proper_bit,eval_up,up_number,input_number,
    cons_zero,List.length_replicate,numeral_number,Core.channels,Descriptor.rank]
 theorem select_number (B C : Expr n) (v : Env n) : (D.select B C).number v=(D.eval v).select (B.number v) (C.number v) := by
  simp only [select,Computation.Stack.PolyRecipe.select_number,properBound_number,proper_bit,eval_up,up_number,input_number,
    cons_zero,List.length_replicate,sub_number,numeral_number,Core.select]
 theorem other_number (B C : Expr n) (v : Env n) : (D.other B C).number v=(D.eval v).other (B.number v) (C.number v) := by
  simp only [other,div_number,select_number,Core.other,eval]
 theorem readout_number (B C : Expr n) (v : Env n) : (D.readout B C).number v=(D.eval v).readout (B.number v) (C.number v) := by
  simp only [readout,mod_number,select_number,Core.readout,eval]
 theorem root_number (B C : Expr n) (v : Env n) : (D.root B C).number v=(D.eval v).root (B.number v) (C.number v) := by
  simp only [root,NumericProgram.choose_number,eq_bit,numeral_number,applyNat_number,readout_number,
    decide_eq_true_eq,Core.root,eval]
 theorem order_number (B C : Expr n) (v : Env n) : (D.order B C).number v=(D.eval v).order (B.number v) (C.number v) := by
  simp only [order,NumericProgram.choose_number,eq_bit,numeral_number,applyNat_number,applyNat₂_number,readout_number,
    decide_eq_true_eq,Core.order,eval]
 theorem matching_bit (I J : Expr n) (v : Env n) : (D.matching I J).bit v=(D.eval v).matching (I.number v) (J.number v) := by
  apply Bool.eq_iff_iff.mpr
  simp only [matching,conj_bit,eq_bit,other_number,readout_number,div_number,mod_number,channelBound_number,
    Core.matching,Bool.and_eq_true,decide_eq_true_eq]

def toPrefix : PrefixDescriptor.Program.Listing n where
  blocks := D.blocks
  validBlock := D.validBlock
  channelBound := D.channelBound
  dimension := D.dimension
  channels := D.up.channels (input 0)
  root := D.up.up.root (input 0) (input 1)
  order := D.up.up.order (input 0) (input 1)
  legal := D.legal
  matching := D.up.up.matching (input 0) (input 1)
 theorem prefix_eval (v : Env n) : D.toPrefix.eval v=(D.eval v).toPrefix := by
  unfold toPrefix PrefixDescriptor.Program.Listing.eval Core.toPrefix
  congr 1
  · exact D.channelBound_number v
  · funext i; simp only [channels_number,eval_up,input_number,cons_zero,List.length_replicate]
  · funext i j; simp only [root_number,eval_up,input_number,cons_zero,NumericProgram.cons_one,List.length_replicate]
  · funext i j; simp only [order_number,eval_up,input_number,cons_zero,NumericProgram.cons_one,List.length_replicate]
  · funext i j; simp only [matching_bit,eval_up,input_number,cons_zero,NumericProgram.cons_one,List.length_replicate]
end Listing
end VariableWL.BlockDescriptor.Program

end OAI
