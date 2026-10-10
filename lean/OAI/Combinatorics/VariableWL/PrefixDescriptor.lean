import OAI.Combinatorics.VariableWL.PrefixAlphabet

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4

namespace VariableWL.PrefixDescriptor
open VariableWL.Affine Descriptor PrefixParts
attribute [local instance] Classical.propDecidable
variable {B : Type uVariable1} (P : Presentation B) (F : B → PrefixParts.Data)
variable (hDim : ∀b,(F b).dimension≤6) (ε : Bit)

 theorem raw_injective : Function.Injective (raw P F hDim ε) := by
  rintro ⟨b,x⟩ ⟨d,y⟩ he
  have hb : b=d := P.encode_injective (by simpa only [raw_block] using congrArg Raw.block he)
  subst d
  apply congrArg (Sigma.mk b)
  cases x with
  | inl x =>
    cases y with
    | inl y => congr
    | inr y => cases y <;> have hk := congrArg Raw.kind he <;> cases hk
  | inr x =>
    cases y with
    | inl y => cases x <;> have hk := congrArg Raw.kind he <;> cases hk
    | inr y =>
      congr 1
      cases x with
      | inl x =>
        cases y with
        | inr y => have hk := congrArg Raw.kind he; cases hk
        | inl y =>
          congr 1
          apply Prod.ext
          · exact Fin.ext (congrArg Raw.channel he)
          · exact Subtype.ext (PrefixAlphabet.encode_injective (hDim b) (congrArg Raw.vector he))
      | inr x =>
        cases y with
        | inl y => have hk := congrArg Raw.kind he; cases hk
        | inr y =>
          congr 1
          exact Data.Tree.ext (Fin.ext (congrArg Raw.channel he)) (congrArg Raw.height he)
            (PrefixAlphabet.encode_injective (hDim b) (congrArg Raw.vector he))

 theorem raw_surjective {D : Data} (h : Good P F hDim ε D) (x : Raw)
    (hb : x.block<D.blocks) (hv : D.validRaw x=true) :
    ∃v : Wiring.Vertex F ε,raw P F hDim ε v=x := by
  obtain ⟨hbv,hv⟩ := Bool.and_eq_true_iff.mp hv
  let u : Valid P.bound P.valid := ⟨⟨x.block,h.blocks ▸ hb⟩,h.validBlock ▸ hbv⟩
  let b := P.equiv u
  have eb : P.encode b=x.block := by
    change (P.equiv.symm (P.equiv u)).val.val=_
    rw [Equiv.symm_apply_apply]
  rcases Bool.or_eq_true_iff.mp hv with hv | hv
  · rcases Bool.or_eq_true_iff.mp hv with hv | hv
    · obtain ⟨hk,hc,hh,hu⟩ := of_decide_eq_true hv
      refine ⟨⟨b,.inl ()⟩,?_⟩
      apply Raw.ext <;> simp only [raw,eb,hk,hc,hh,hu]
    · obtain ⟨hv,hl⟩ := Bool.and_eq_true_iff.mp hv
      obtain ⟨hk,hc,hh⟩ := of_decide_eq_true hv
      rw [←eb,h.channels] at hc
      rw [←eb] at hl
      obtain ⟨z,hz⟩ := (h.legal b x.vector).mp hl
      refine ⟨⟨b,.inr (.inl (⟨x.channel,hc⟩,z))⟩,?_⟩
      apply Raw.ext <;> simp only [raw,eb,hk,hh,hz]
  · obtain ⟨hv,ht⟩ := Bool.and_eq_true_iff.mp hv
    obtain ⟨hk,hc⟩ := of_decide_eq_true hv
    rw [←eb,h.channels] at hc
    let c : Fin (F b).channels := ⟨x.channel,hc⟩
    obtain ⟨ht,hz⟩ := Bool.and_eq_true_iff.mp ht
    obtain ⟨hr,hd⟩ := of_decide_eq_true ht
    rw [←eb,h.dimension] at hd
    have hr' : (F b).root c≤x.height := by
      rw [←eb] at hr
      change D.root (P.encode b) c.val≤x.height at hr
      rwa [h.root] at hr
    obtain ⟨j,_,hj⟩ := List.any_eq_true.mp hz
    obtain ⟨hl,hp⟩ := Bool.and_eq_true_iff.mp hj
    rw [←eb] at hl
    obtain ⟨z,ez⟩ := (h.legal b j).mp hl
    have hp' : PrefixAlphabet.encode (hDim b) (PrefixParts.Data.truncate x.height (z.val ∘ (F b).order c))=x.vector := by
      have hop := h.order b c
      rw [←ez,←eb,hop,PrefixAlphabet.prefix_encode] at hp
      exact of_decide_eq_true hp
    refine ⟨⟨b,.inr (.inr (PrefixParts.Data.Tree.ofValuation c x.height hr' hd z))⟩,?_⟩
    apply Raw.ext <;> simp only [raw,PrefixParts.Data.Tree.ofValuation,eb,hk,hp',c]

noncomputable def presentation {D : Data} (h : Good P F hDim ε D) : Presentation (Wiring.Vertex F ε) :=
  Presentation.ofEncoding D.bound D.valid (fun x=>D.pack (raw P F hDim ε x))
    (fun x=>D.pack_lt _ (raw_bounds P F hDim ε h x).1 (raw_bounds P F hDim ε h x).2.1
      (raw_bounds P F hDim ε h x).2.2.1 (raw_bounds P F hDim ε h x).2.2.2.1
      (raw_bounds P F hDim ε h x).2.2.2.2)
    (fun x=>by
      rw [Data.valid,D.unpack_pack _ (raw_bounds P F hDim ε h x).2.1
        (raw_bounds P F hDim ε h x).2.2.1 (raw_bounds P F hDim ε h x).2.2.2.1
        (raw_bounds P F hDim ε h x).2.2.2.2]
      exact raw_valid P F hDim ε h x)
    (by
      intro x y he
      have hb := raw_bounds P F hDim ε h x
      have hc := raw_bounds P F hDim ε h y
      have he' := congrArg D.unpack he
      rw [D.unpack_pack _ hb.2.1 hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2,
        D.unpack_pack _ hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2] at he'
      exact raw_injective P F hDim ε he')
    (by
      intro i hi hv
      obtain ⟨x,hx⟩ := raw_surjective P F hDim ε h (D.unpack i) (D.unpack_bounds h.positive hi).1 hv
      exact ⟨x,by rw [hx,D.pack_unpack]⟩)

@[simp] theorem presentation_encode {D : Data} (h : Good P F hDim ε D) (x : Wiring.Vertex F ε) :
    (presentation P F hDim ε h).encode x=D.pack (raw P F hDim ε x) := rfl

end VariableWL.PrefixDescriptor

namespace VariableWL.PrefixAlphabet
open VariableWL.Affine
noncomputable def trim (h i : ℕ) : ℕ :=
  if hi : i<vectorCount then (vectorNumber (truncated h (vectorNumber.symm ⟨i,hi⟩))).val else 0
@[simp] theorem trim_encode {a : ℕ} (ha : a≤6) (z : Vec a) (h : ℕ) :
    trim h (encode ha z)=encode ha (PrefixParts.Data.truncate h z) := by
  simp only [trim,dite_eq_left (encode_lt ha z)]
  change (vectorNumber (truncated h (vectorNumber.symm (vectorNumber ⟨⟨a,by omega⟩,z⟩)))).val=_
  rw [Equiv.symm_apply_apply]
  rfl
end VariableWL.PrefixAlphabet

namespace VariableWL.PrefixDescriptor
open VariableWL.Affine Descriptor PrefixParts
attribute [local instance] Classical.propDecidable
namespace Data
variable (D : Data)
noncomputable def forward (x y : Raw) : Bool :=
  (decide (x.kind=0 ∧ y.kind=2 ∧ y.channel=0 ∧ y.height=0)) ||
  (decide (x.kind=1 ∧ y.kind=1 ∧ x.channel+1=y.channel ∧ x.vector=y.vector)) ||
  (decide (x.kind=2 ∧ y.kind=2 ∧ x.channel=y.channel ∧ x.height+1=y.height ∧
    PrefixAlphabet.trim x.height y.vector=x.vector)) ||
  (decide (x.kind=2 ∧ y.kind=1 ∧ x.channel=y.channel ∧ x.height=D.dimension x.block ∧
    x.vector=PrefixAlphabet.prefixCode (D.order x.block y.channel) (D.dimension x.block) y.vector))
noncomputable def slot (x y : Raw) : ℕ :=
  if x.kind=0 then 0 else if x.kind=1 then
    if y.kind=1 then if y.channel<x.channel then 0 else 1 else 2
  else if y.kind=0 then 0 else if y.kind=1 then 1 else
    if y.height<x.height then 0 else
      if x.height<D.dimension x.block then PrefixAlphabet.bit y.vector x.height+1 else 1
noncomputable def internal (x y : Raw) (i j : ℕ) : Bool :=
  decide (x.block=y.block) && (D.forward x y || D.forward y x) &&
    decide (i=D.slot x y ∧ j=D.slot y x)
end Data

variable {B : Type uVariable2} (P : Presentation B) (F : B → PrefixParts.Data)
variable (hDim : ∀b,(F b).dimension≤6) (ε : Bit)

 theorem raw_forward {D : Data} (h : Good P F hDim ε D) (b : B) (x y : (F b).Vertex ε) :
    D.forward (raw P F hDim ε ⟨b,x⟩) (raw P F hDim ε ⟨b,y⟩)=true ↔ PrefixParts.Data.Forward x y := by
  have hinj (z w : Vec (F b).dimension) : PrefixAlphabet.encode (hDim b) z=PrefixAlphabet.encode (hDim b) w ↔ z=w :=
    (PrefixAlphabet.encode_injective (hDim b)).eq_iff
  rcases x with x | (⟨c,z⟩ | t) <;> rcases y with y | (⟨d,w⟩ | u) <;>
    simp only [raw,Data.forward,PrefixParts.Data.Forward,PrefixParts.Data.TreeStep,
      h.dimension,h.order,PrefixAlphabet.prefix_encode,PrefixAlphabet.trim_encode,
      PrefixParts.Data.truncate_full,Bool.or_eq_true,decide_eq_true_eq,hinj,
      Fin.ext_iff,Subtype.ext_iff]
  all_goals norm_num only
  all_goals simp only [true_and,false_and,and_true,and_false,false_or,or_false,decide_false,Bool.false_eq_true]

 theorem fin_val_ite (p : Prop) [Decidable p] (a b : Fin 3) :
    (if p then a else b).val=if p then a.val else b.val := by split_ifs <;> rfl
 theorem fin_val_dite (p : Prop) [Decidable p] (a : p → Fin 3) (b : ¬p → Fin 3) :
    (dite p a b).val=dite p (fun h => (a h).val) (fun h => (b h).val) := by split_ifs <;> rfl
 theorem raw_slot {D : Data} (h : Good P F hDim ε D) (b : B) (x y : (F b).Vertex ε) :
    D.slot (raw P F hDim ε ⟨b,x⟩) (raw P F hDim ε ⟨b,y⟩)=(PrefixParts.Data.slot x y).val := by
  rcases x with x | (⟨c,z⟩ | t) <;> rcases y with y | (⟨d,w⟩ | u) <;>
    simp only [Data.slot,raw,PrefixParts.Data.slot,h.dimension,one_ne_zero,show (2:ℕ)≠0 by omega,show (2:ℕ)≠1 by omega,
      ite_true,ite_false,show (0:ℕ)≠1 by omega,Fin.val_zero,Fin.val_one,fin_val_ite,fin_val_dite,PrefixParts.Data.bitPort]
  · rfl
  · rfl
  · rfl
  · split_ifs with h1 h2
    · rfl
    · rw [PrefixAlphabet.bit_encode (hDim b) u.bits ⟨t.height,h2⟩]
    · rfl

 theorem raw_internal [Fintype B] {D : Data} (h : Good P F hDim ε D)
    (x y : Wiring.Vertex F ε) (i j : Fin 3) :
    D.internal (raw P F hDim ε x) (raw P F hDim ε y) i.val j.val=true ↔
      (Wiring.internal F ε).edge (x,i) (y,j) := by
  rcases x with ⟨b,x⟩
  rcases y with ⟨d,y⟩
  by_cases hbd : b=d
  · subst d
    simp only [Data.internal,raw_block,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,
      true_and,raw_forward P F hDim ε h,raw_slot P F hDim ε h]
    simp only [Wiring.internal,SubcubicRealization.PortGraph.sigma,PrefixParts.Data.ports,
      PrefixParts.Data.graph,SubcubicRealization.PortGraph.ofSlots,exists_true_left,Fin.ext_iff]
  · have he : P.encode b≠P.encode d := P.encode_injective.ne hbd
    simp only [Data.internal,raw_block,he,decide_false,Bool.false_and,Bool.false_eq_true,
      Wiring.internal,SubcubicRealization.PortGraph.sigma,hbd]
    exact ⟨False.elim,fun ⟨h,_⟩=>h⟩

end VariableWL.PrefixDescriptor

namespace VariableWL.PrefixDescriptor
open VariableWL.Affine Descriptor PrefixParts
attribute [local instance] Classical.propDecidable
variable {B : Type uVariable3} (P : Presentation B) (F : B → PrefixParts.Data)

noncomputable def sortRaw (s : Wiring.SortTag F) : Raw := match s.2 with
  | .inl _ => ⟨P.encode s.1,0,0,0,0⟩
  | .inr (.inl c) => ⟨P.encode s.1,1,c.val,0,0⟩
  | .inr (.inr ⟨c,h⟩) => ⟨P.encode s.1,2,c.val,h.val.val,0⟩

@[simp] theorem sortRaw_block (s : Wiring.SortTag F) : (sortRaw P F s).block=P.encode s.1 := by
  rcases s with ⟨b,x| (x|x)⟩ <;> rfl

 theorem sortRaw_injective : Function.Injective (sortRaw P F) := by
  rintro ⟨b,x⟩ ⟨d,y⟩ he
  have hb := P.encode_injective (by simpa only [sortRaw_block] using congrArg Raw.block he)
  subst d
  apply congrArg (Sigma.mk b)
  cases x with
  | inl x =>
    cases y with
    | inl y => congr
    | inr y => cases y <;> have hk := congrArg Raw.kind he <;> cases hk
  | inr x =>
    cases y with
    | inl y => cases x <;> have hk := congrArg Raw.kind he <;> cases hk
    | inr y =>
      congr 1
      cases x with
      | inl x =>
        cases y with
        | inr y => have hk := congrArg Raw.kind he; cases hk
        | inl y => exact congrArg Sum.inl (Fin.ext (congrArg Raw.channel he))
      | inr x =>
        cases y with
        | inl y => have hk := congrArg Raw.kind he; cases hk
        | inr y =>
          congr 1
          rcases x with ⟨c,u⟩
          rcases y with ⟨d,v⟩
          have hc : c=d := Fin.ext (congrArg Raw.channel he)
          subst d
          apply congrArg (Sigma.mk c)
          exact Subtype.ext (Fin.ext (congrArg Raw.height he))

variable (hDim : ∀b,(F b).dimension≤6) (ε : Bit)
 theorem sortRaw_bounds {D : Data} (h : Good P F hDim ε D) (x : Wiring.SortTag F) :
    (sortRaw P F x).block<D.blocks ∧ (sortRaw P F x).kind<3 ∧
      (sortRaw P F x).channel<D.channelBound ∧ (sortRaw P F x).height<7 ∧
      (sortRaw P F x).vector<PrefixAlphabet.vectorCount := by
  have hb := P.encode_lt x.1
  rw [←h.blocks] at hb
  rcases x with ⟨b,x | (c | ⟨c,t⟩)⟩
  · exact ⟨hb,by change 0<3; omega,h.positive,by change 0<7; omega,PrefixAlphabet.vectorCount_pos⟩
  · exact ⟨hb,by change 1<3; omega,c.isLt.trans_le (h.channelBound b),by change 0<7; omega,PrefixAlphabet.vectorCount_pos⟩
  · have ht := t.val.isLt
    have hd := hDim b
    exact ⟨hb,by change 2<3; omega,c.isLt.trans_le (h.channelBound b),by dsimp [sortRaw]; omega,
      PrefixAlphabet.vectorCount_pos⟩

 theorem sortRaw_valid {D : Data} (h : Good P F hDim ε D) (x : Wiring.SortTag F) :
    D.sortValid (sortRaw P F x)=true := by
  have hb : D.validBlock (P.encode x.1)=true := h.validBlock ▸ P.encode_valid x.1
  rcases x with ⟨b,x | (c | ⟨c,t⟩)⟩
  · simp only [sortRaw,Data.sortValid,hb,Bool.true_and,and_self,true_or,decide_true]
  · have hc := c.isLt
    simp only [sortRaw,Data.sortValid,hb,Bool.true_and,h.channels,decide_eq_true_eq]
    exact Or.inr (Or.inl ⟨True.intro,hc,True.intro⟩)
  · simp only [sortRaw,Data.sortValid,hb,Bool.true_and,h.channels,h.root,h.dimension,decide_eq_true_eq]
    exact Or.inr (Or.inr ⟨True.intro,c.isLt,t.property,Nat.le_of_lt_succ t.val.isLt⟩)

namespace Data
variable (D : Data)
noncomputable def sortPredicate (i : ℕ) : Bool := D.sortValid (D.unpack (i*PrefixAlphabet.vectorCount))
noncomputable def color (i : ℕ) : ℕ := 1+Descriptor.rank D.sortPredicate (D.tag (D.unpack i))
noncomputable def colorBound : ℕ := 1+Descriptor.rank D.sortPredicate D.sortBound
end Data

 theorem sortPresentation {D : Data} (h : Good P F hDim ε D) :
    ∃Q : Presentation (Wiring.SortTag F),Q.bound=D.sortBound ∧ Q.valid=D.sortPredicate ∧
      ∀s,Q.encode s=D.tag (sortRaw P F s) := by
  let f := fun s : Wiring.SortTag F=>D.tag (sortRaw P F s)
  have hf (s) : f s<D.sortBound := by
    have hb := sortRaw_bounds P F hDim ε h s
    exact D.tag_lt _ hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1
  have helper (s) : D.unpack (f s*PrefixAlphabet.vectorCount)=sortRaw P F s := by
    have hb := sortRaw_bounds P F hDim ε h s
    have hv : (sortRaw P F s).vector=0 := by rcases s with ⟨b,x | (x|x)⟩ <;> rfl
    have he : f s*PrefixAlphabet.vectorCount=D.pack (sortRaw P F s) := by simp only [Data.pack,hv,Nat.add_zero]; rfl
    rw [he,D.unpack_pack _ hb.2.1 hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2]
  have hp (s) : D.sortPredicate (f s)=true := by
    rw [Data.sortPredicate,helper]
    exact sortRaw_valid P F hDim ε h s
  have hi : Function.Injective f := by
    intro s t he
    apply sortRaw_injective P F
    rw [←helper s,←helper t,he]
  have hs (i : ℕ) (hi : i<D.sortBound) (hv : D.sortPredicate i=true) : ∃s,f s=i := by
    let x := D.unpack (i*PrefixAlphabet.vectorCount)
    have hx : i*PrefixAlphabet.vectorCount<D.bound := Nat.mul_lt_mul_of_pos_right hi PrefixAlphabet.vectorCount_pos
    have hb := (D.unpack_bounds h.positive hx).1
    obtain ⟨hbv,hv⟩ := Bool.and_eq_true_iff.mp hv
    let u : Valid P.bound P.valid := ⟨⟨x.block,h.blocks ▸ hb⟩,h.validBlock ▸ hbv⟩
    let b := P.equiv u
    have eb : P.encode b=x.block := by
      change (P.equiv.symm (P.equiv u)).val.val=_
      rw [Equiv.symm_apply_apply]
    have hxv : x.vector=0 := by simp [x,Data.unpack]
    have target (s : Wiring.SortTag F) (hh : sortRaw P F s=x) : f s=i := by
      have he := congrArg D.pack hh
      rw [D.pack_unpack] at he
      have hv : (sortRaw P F s).vector=0 := by rcases s with ⟨b,x | (x|x)⟩ <;> rfl
      simp only [Data.pack,hv,Nat.add_zero] at he
      exact Nat.eq_of_mul_eq_mul_right PrefixAlphabet.vectorCount_pos he
    change decide ((x.kind=0 ∧ x.channel=0 ∧ x.height=0) ∨
      (x.kind=1 ∧ x.channel<D.channels x.block ∧ x.height=0) ∨
      (x.kind=2 ∧ x.channel<D.channels x.block ∧ D.root x.block x.channel≤x.height ∧
        x.height≤D.dimension x.block))=true at hv
    rcases of_decide_eq_true hv with hh | hh | hh
    · obtain ⟨hk,hc,hh⟩ := hh
      exact ⟨⟨b,.inl ()⟩,target _ (by apply Raw.ext <;> simp only [sortRaw,eb,hk,hc,hh,hxv])⟩
    · obtain ⟨hk,hc,hh⟩ := hh
      rw [←eb,h.channels] at hc
      exact ⟨⟨b,.inr (.inl ⟨x.channel,hc⟩)⟩,target _ (by apply Raw.ext <;> simp only [sortRaw,eb,hk,hh,hxv])⟩
    · obtain ⟨hk,hc,hr,hd⟩ := hh
      rw [←eb,h.channels] at hc
      rw [←eb,h.dimension] at hd
      let c : Fin (F b).channels := ⟨x.channel,hc⟩
      have hr' : (F b).root c≤x.height := by
        rw [←eb] at hr
        change D.root (P.encode b) c.val≤x.height at hr
        rwa [h.root] at hr
      exact ⟨⟨b,.inr (.inr ⟨c,⟨x.height,by omega⟩,hr'⟩)⟩,
        target _ (by apply Raw.ext <;> simp only [sortRaw,eb,hk,hxv,c])⟩
  exact ⟨Presentation.ofEncoding _ _ f hf hp hi hs,rfl,rfl,fun s=>rfl⟩

end VariableWL.PrefixDescriptor

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}
def table₂ (N M : ℕ) (f : ℕ → ℕ → ℕ) (I J : Expr n) : Expr n :=
  choose (conj (lt I (numeral N)) (lt J (numeral M))) (fixedNat₂ N M f I J) (numeral 0)
theorem table₂_number (N M : ℕ) (f : ℕ → ℕ → ℕ) (I J : Expr n) (v : Env n) :
    (table₂ N M f I J).number v=if I.number v<N ∧ J.number v<M then f (I.number v) (J.number v) else 0 := by
  simp only [table₂,NumericProgram.choose_number,conj_bit,lt_bit,numeral_number,Bool.and_eq_true,decide_eq_true_eq]
  split_ifs with h
  · exact fixedNat₂_number _ _ _ _ _ _ h.1 h.2
  · rfl

def table₃ (N M K : ℕ) (f : ℕ → ℕ → ℕ → ℕ) (I J L : Expr n) : Expr n :=
  choose (conj (conj (lt I (numeral N)) (lt J (numeral M))) (lt L (numeral K)))
    (fixedNat₃ N M K f I J L) (numeral 0)
theorem table₃_number (N M K : ℕ) (f : ℕ → ℕ → ℕ → ℕ) (I J L : Expr n) (v : Env n) :
    (table₃ N M K f I J L).number v=if I.number v<N ∧ J.number v<M ∧ L.number v<K then f (I.number v) (J.number v) (L.number v) else 0 := by
  simp only [table₃,NumericProgram.choose_number,conj_bit,lt_bit,numeral_number,Bool.and_eq_true,decide_eq_true_eq]
  by_cases h : I.number v<N ∧ J.number v<M ∧ L.number v<K
  · rw [ite_eq_left ⟨⟨h.1,h.2.1⟩,h.2.2⟩,ite_eq_left h]
    exact fixedNat₃_number _ _ _ _ _ _ _ _ h.1 h.2.1 h.2.2
  · rw [ite_eq_right (by tauto),ite_eq_right h]

end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.PrefixAlphabet
open VariableWL.Affine
 theorem truncate_cap {a : ℕ} (ha : a≤6) (z : Vec a) (h : ℕ) :
    PrefixParts.Data.truncate (min h 7) z=PrefixParts.Data.truncate h z := by
  ext i
  have hi := i.isLt
  simp only [PrefixParts.Data.truncate]
  split_ifs <;> first | rfl | omega
 theorem prefixCode_cap (p h i : ℕ) : prefixCode p (min h 7) i=prefixCode p h i := by
  unfold prefixCode
  split_ifs with hp hi
  · congr 2
    apply congrArg (Sigma.mk _)
    exact truncate_cap (by have := (permuted (orderNumber.symm ⟨p,hp⟩) (vectorNumber.symm ⟨i,hi⟩)).1.isLt; omega) _ h
  all_goals rfl
 theorem trim_cap (h i : ℕ) : trim (min h 7) i=trim h i := by
  unfold trim
  split_ifs with hi
  · congr 2
    apply congrArg (Sigma.mk _)
    exact truncate_cap (by have := (vectorNumber.symm ⟨i,hi⟩).1.isLt; omega) _ h
  · rfl
 theorem prefixCode_zero {p h i : ℕ} (hp : ¬p<orderCount ∨ ¬i<vectorCount) : prefixCode p h i=0 := by
  unfold prefixCode
  rcases hp with hp | hi
  · rw [dite_eq_right hp]
  · split_ifs <;> omega
 theorem trim_zero {h i : ℕ} (hi : ¬i<vectorCount) : trim h i=0 := dite_eq_right hi
 theorem bit_zero {i h : ℕ} (hp : ¬i<vectorCount ∨ ¬h<7) : bit i h=0 := by
  unfold bit
  rcases hp with hi | hh
  · rw [dite_eq_right hi]
  · split_ifs with hi
    · dsimp only
      rw [dite_eq_right (by have hbound := (vectorNumber.symm ⟨i,hi⟩).1.isLt; omega)]
    · rfl

namespace TotalProgram
open Computation.Stack.PolyRecipe Computation.Stack.Recipe
variable {n : ℕ}
noncomputable def prefixCode (P H I : Expr n) : Expr n :=
  table₃ orderCount 8 vectorCount PrefixAlphabet.prefixCode P (minimum H (numeral 7)) I
noncomputable def trim (H I : Expr n) : Expr n :=
  table₂ 8 vectorCount PrefixAlphabet.trim (minimum H (numeral 7)) I
noncomputable def bit (I H : Expr n) : Expr n :=
  table₂ vectorCount 7 PrefixAlphabet.bit I H
 theorem prefixCode_number (P H I : Expr n) (v : Env n) :
    (prefixCode P H I).number v=PrefixAlphabet.prefixCode (P.number v) (H.number v) (I.number v) := by
  simp only [prefixCode,table₃_number,minimum_number,numeral_number]
  split_ifs with h
  · exact prefixCode_cap _ _ _
  · apply Eq.symm
    exact prefixCode_zero (by have := Nat.min_le_right (H.number v) 7; omega)
 theorem trim_number (H I : Expr n) (v : Env n) :
    (trim H I).number v=PrefixAlphabet.trim (H.number v) (I.number v) := by
  simp only [trim,table₂_number,minimum_number,numeral_number]
  split_ifs with h
  · exact trim_cap _ _
  · exact (trim_zero (by have := Nat.min_le_right (H.number v) 7; omega)).symm
 theorem bit_number (I H : Expr n) (v : Env n) :
    (bit I H).number v=PrefixAlphabet.bit (I.number v) (H.number v) := by
  simp only [bit,table₂_number]
  split_ifs with h
  · rfl
  · exact (bit_zero (by tauto)).symm
end TotalProgram
end VariableWL.PrefixAlphabet

namespace VariableWL.PrefixDescriptor
open VariableWL.Affine Descriptor PrefixParts
attribute [local instance] Classical.propDecidable
namespace Data
variable (D : Data)
noncomputable def roots (x y : Raw) (i j : ℕ) : Bool :=
  decide (x.kind=2 ∧ y.kind=2 ∧ i=0 ∧ j=0 ∧ x.channel≠0 ∧ y.channel≠0 ∧
    x.height=D.root x.block x.channel ∧ y.height=D.root y.block y.channel) &&
  D.matching (x.block*D.channelBound+x.channel) (y.block*D.channelBound+y.channel) &&
  PrefixAlphabet.paddedEqual x.vector y.vector
noncomputable def anchors (x y : Raw) (i j : ℕ) : Bool :=
  decide (x.kind=0 ∧ y.kind=0 ∧
    ((i=2 ∧ j=1 ∧ Descriptor.rank D.validBlock x.block+1=Descriptor.rank D.validBlock y.block) ∨
      (i=1 ∧ j=2 ∧ Descriptor.rank D.validBlock y.block+1=Descriptor.rank D.validBlock x.block)))
noncomputable def incidence (a b : ℕ) : Bool :=
  let x := D.unpack (a/3)
  let y := D.unpack (b/3)
  D.internal x y (a%3) (b%3) || D.roots x y (a%3) (b%3) || D.anchors x y (a%3) (b%3)
noncomputable def portData : Descriptor.PortData where
  bound := D.bound
  valid := D.valid
  color := D.color
  colorBound := D.colorBound
  incidence := D.incidence
end Data

variable {B : Type uVariable4} (P : Presentation B) (F : B → PrefixParts.Data)
variable (hDim : ∀b,(F b).dimension≤6) (ε : Bit)

def MatchingGood (D : Data) (W : Wiring F) : Prop :=
  ∀c d : Channel F,D.matching (P.encode c.1*D.channelBound+c.2.val.val)
    (P.encode d.1*D.channelBound+d.2.val.val)=true ↔ W.mate c=d

 theorem rootPorts_tree [Fintype B] (W : Wiring F) (b d : B) (t : (F b).Tree ε) (u : (F d).Tree ε)
    (i j : Fin 3) :
    (W.rootPorts F ε).edge ((⟨b,.inr (.inr t)⟩ : Wiring.Vertex F ε),i) (⟨d,.inr (.inr u)⟩,j) ↔
    i=0 ∧ j=0 ∧ ∃hc : t.channel.val≠0,∃hd : u.channel.val≠0,
      t.height=(F b).root t.channel ∧ u.height=(F d).root u.channel ∧
      W.mate ⟨b,t.channel,hc⟩=⟨d,u.channel,hd⟩ ∧ Wiring.pad t.bits=Wiring.pad u.bits := by
  constructor
  · rintro ⟨⟨⟨b',c⟩,t'⟩,⟨⟨d',e⟩,u'⟩,hx,hy,hm,hp⟩
    have hi := congrArg Prod.snd hx
    have hj := congrArg Prod.snd hy
    have hb := congrArg (fun a : Wiring.Vertex F ε × Fin 3=>a.1.1) hx
    have hd := congrArg (fun a : Wiring.Vertex F ε × Fin 3=>a.1.1) hy
    dsimp only [Wiring.rootVertex] at hb hd
    subst b'; subst d'
    have ht : t=t'.val := Sum.inr_injective (Sum.inr_injective
      (eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Prod.fst hx)).2))
    have hu : u=u'.val := Sum.inr_injective (Sum.inr_injective
      (eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Prod.fst hy)).2))
    subst t; subst u
    have hc := t'.property.1
    have he := u'.property.1
    refine ⟨hi,hj,by rw [hc]; exact c.property,by rw [he]; exact e.property,?_,?_,?_,hp⟩
    · rw [hc]; exact t'.property.2
    · rw [he]; exact u'.property.2
    · simpa only [hc,he] using hm
  · rintro ⟨rfl,rfl,hc,hd,ht,hu,hm,hp⟩
    exact ⟨⟨⟨b,t.channel,hc⟩,t,rfl,ht⟩,⟨⟨d,u.channel,hd⟩,u,rfl,hu⟩,rfl,rfl,hm,hp⟩

 theorem raw_roots [Fintype B] {D : Data} (h : Good P F hDim ε D) (W : Wiring F)
    (hm : MatchingGood P F D W) (x y : Wiring.Vertex F ε) (i j : Fin 3) :
    D.roots (raw P F hDim ε x) (raw P F hDim ε y) i.val j.val=true ↔
      (W.rootPorts F ε).edge (x,i) (y,j) := by
  rcases x with ⟨b,x | (x | t)⟩ <;> rcases y with ⟨d,y | (y | u)⟩
  all_goals try {
    simp only [Data.roots,raw,show (0:ℕ)≠2 by omega,show (1:ℕ)≠2 by omega,false_and,and_false,
      decide_false,Bool.false_and,Bool.false_eq_true]
    constructor
    · exact False.elim
    · rintro ⟨a,b,ha,hb,_,_⟩
      first
      | have hx := congrArg (fun z : Wiring.Vertex F ε => (raw P F hDim ε z).kind) (congrArg Prod.fst ha)
        simp only [Wiring.rootVertex,raw] at hx
        omega
      | have hy := congrArg (fun z : Wiring.Vertex F ε => (raw P F hDim ε z).kind) (congrArg Prod.fst hb)
        simp only [Wiring.rootVertex,raw] at hy
        omega }
  rw [rootPorts_tree F ε W]
  simp only [Data.roots,raw,h.root,Bool.and_eq_true,decide_eq_true_eq,
    PrefixAlphabet.paddedEqual_encode,true_and]
  constructor
  · rintro ⟨⟨⟨hi,hj,hc,hd,ht,hu⟩,hmatch⟩,hp⟩
    exact ⟨Fin.ext hi,Fin.ext hj,hc,hd,ht,hu,(hm ⟨b,t.channel,hc⟩ ⟨d,u.channel,hd⟩).mp hmatch,hp⟩
  · rintro ⟨hi,hj,hc,hd,ht,hu,hmatch,hp⟩
    exact ⟨⟨⟨congrArg Fin.val hi,congrArg Fin.val hj,hc,hd,ht,hu⟩,
      (hm ⟨b,t.channel,hc⟩ ⟨d,u.channel,hd⟩).mpr hmatch⟩,hp⟩

end VariableWL.PrefixDescriptor

end OAI
