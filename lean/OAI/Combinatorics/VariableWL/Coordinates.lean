import OAI.Combinatorics.VariableWL.PrefixGame

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7

namespace VariableWL.BlockCoordinates
open VariableWL.Affine VariableWL.Blocks Subdivision
attribute [local instance] Classical.propDecidable
variable {r n : ℕ} {P : Type uVariable1} {E : Type uVariable2} (J : ProductImages.Instance r P E)

def Coordinate : RawBlock r n P E → Type
  | .inl h => Fin (dimension J h.type)
  | .inr s => (Fin (dimension J (left J.source s.link)) ⊕
      Fin (dimension J (right J.target s.link))) ⊕ Bool

instance coordinateFintype (b : RawBlock r n P E) : Fintype (Coordinate J b) := by
  cases b <;> dsimp only [Coordinate] <;> infer_instance

def coordinateEquiv (b : RawBlock r n P E) : RawValue J b ≃+ (Coordinate J b → Bit) := by
  cases b with
  | inl h => exact AddEquiv.refl _
  | inr s =>
    exact {
      toFun := fun z => Sum.elim (Sum.elim z.1.1 z.1.2) (fun t => if t then z.2.2 else z.2.1)
      invFun := fun f => ((fun i => f (.inl (.inl i)),fun i => f (.inl (.inr i))),
        (f (.inr false),f (.inr true)))
      left_inv := fun z => by cases z; rfl
      right_inv := fun f => by
        funext i
        rcases i with (i | i) | t
        · rfl
        · rfl
        · cases t <;> rfl
      map_add' := fun z w => by
        funext i
        rcases i with (i | i) | t
        · rfl
        · rfl
        · cases t <;> rfl }

noncomputable def numbering (b : RawBlock r n P E) : Coordinate J b ≃ Fin (Fintype.card (Coordinate J b)) :=
  Fintype.equivFin _

noncomputable def encode (b : RawBlock r n P E) : RawValue J b ≃+ Vec (Fintype.card (Coordinate J b)) where
  toFun z := coordinateEquiv J b z ∘ (numbering J b).symm
  invFun f := (coordinateEquiv J b).symm (f ∘ numbering J b)
  left_inv z := by simp only [Function.comp_def,Equiv.symm_apply_apply]; exact (coordinateEquiv J b).symm_apply_apply z
  right_inv f := by funext i; simp
  map_add' z w := by funext i; exact congrFun ((coordinateEquiv J b).map_add z w) _

def readoutDimension : Readout r n P E → ℕ
  | .inl h => dimension J h.type
  | .inr _ => 1

def readoutEquiv (a : Readout r n P E) : ReadoutValue J a ≃+ Vec (readoutDimension J a) := by
  cases a with
  | inl h => exact AddEquiv.refl _
  | inr v =>
    change Bit ≃+ Vec 1
    exact { toFun := fun z _ => z
            invFun := fun f => f 0
            left_inv := fun _ => rfl
            right_inv := fun f => by funext i; have : i=0 := Subsingleton.elim _ _; subst i; rfl
            map_add' := fun _ _ => rfl }

theorem coordinate_lift (hr : 2 ≤ r) (hn : 0 < n) {b : RawBlock r n P E}
    {a : Readout r n P E} (ha : HasReadout J b a) :
    ∃ e : Fin (readoutDimension J a) ↪ Coordinate J b,
      ∀ z i, coordinateEquiv J b z (e i)=readoutEquiv J a (readout J z ha) i := by
  cases b with
  | inl h =>
    cases ha
    refine ⟨Function.Embedding.refl _,?_⟩
    intro z i
    rw [readout_eq J hr hn (b := .inl h) (z := z) (a := .inl h) rfl ⟨rfl,HEq.rfl⟩]
    rfl
  | inr s =>
    rcases ha with rfl | rfl | rfl | rfl
    · refine ⟨⟨fun i => .inl (.inl i),fun i j h => Sum.inl.inj (Sum.inl.inj h)⟩,?_⟩
      intro z i
      rw [readout_eq J hr hn (b := .inr s) (z := z) (a := (.inl (squareLeft J s))) (Or.inl rfl) (Or.inl ⟨rfl,HEq.rfl⟩)]
      rfl
    · refine ⟨⟨fun i => .inl (.inr i),fun i j h => Sum.inr.inj (Sum.inl.inj h)⟩,?_⟩
      intro z i
      rw [readout_eq J hr hn (b := .inr s) (z := z) (a := (.inl (squareRight J s))) (Or.inr (Or.inl rfl)) (Or.inr (Or.inl ⟨rfl,HEq.rfl⟩))]
      rfl
    · refine ⟨⟨fun _ => .inr false,by intro i j _; apply Fin.ext; have hi : i.val<1 := i.isLt; have hj : j.val<1 := j.isLt; omega⟩,?_⟩
      intro z i
      rw [readout_eq J hr hn (b := .inr s) (z := z) (a := (.inr (squareBottom s))) (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inl ⟨rfl,HEq.rfl⟩)))]
      rfl
    · refine ⟨⟨fun _ => .inr true,by intro i j _; apply Fin.ext; have hi : i.val<1 := i.isLt; have hj : j.val<1 := j.isLt; omega⟩,?_⟩
      intro z i
      rw [readout_eq J hr hn (b := .inr s) (z := z) (a := (.inr (squareTop s))) (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (Or.inr (Or.inr ⟨rfl,HEq.rfl⟩)))]
      rfl

noncomputable def readoutEmbedding (hr : 2 ≤ r) (hn : 0 < n) {b : RawBlock r n P E}
    {a : Readout r n P E} (ha : HasReadout J b a) :
    Fin (readoutDimension J a) ↪ Fin (Fintype.card (Coordinate J b)) :=
  (coordinate_lift J hr hn ha).choose.trans (numbering J b).toEmbedding

theorem readoutEmbedding_spec (hr : 2 ≤ r) (hn : 0 < n) {b : RawBlock r n P E}
    {a : Readout r n P E} (ha : HasReadout J b a) (z : RawValue J b) (i : Fin (readoutDimension J a)) :
    encode J b z (readoutEmbedding J hr hn ha i)=readoutEquiv J a (readout J z ha) i := by
  simpa only [encode,AddEquiv.coe_mk,Equiv.coe_fn_mk,Function.comp_apply,readoutEmbedding,
    Function.Embedding.trans_apply,Equiv.toEmbedding_apply,Equiv.symm_apply_apply] using
    (coordinate_lift J hr hn ha).choose_spec z i

theorem readoutDimension_le (hr : 2 ≤ r) (hn : 0 < n) {b : RawBlock r n P E}
    {a : Readout r n P E} (ha : HasReadout J b a) :
    readoutDimension J a ≤ Fintype.card (Coordinate J b) := by
  simpa using Fintype.card_le_of_injective _ (readoutEmbedding J hr hn ha).injective

theorem exists_readout_order (hr : 2 ≤ r) (hn : 0 < n) {b : RawBlock r n P E}
    {a : Readout r n P E} (ha : HasReadout J b a) :
    ∃ e : Equiv.Perm (Fin (Fintype.card (Coordinate J b))),
      ∀ i : Fin (readoutDimension J a),
      e ⟨i.val,lt_of_lt_of_le i.isLt (readoutDimension_le J hr hn ha)⟩=readoutEmbedding J hr hn ha i := by
  exact Equiv.Perm.exists_extending_pair
    (fun i : Fin (readoutDimension J a) => (⟨i.val,lt_of_lt_of_le i.isLt (readoutDimension_le J hr hn ha)⟩ :
      Fin (Fintype.card (Coordinate J b)))) (readoutEmbedding J hr hn ha)
    (fun _ _ h => Fin.ext (congrArg (fun x : Fin (Fintype.card (Coordinate J b)) => x.val) h)) (readoutEmbedding J hr hn ha).injective

end VariableWL.BlockCoordinates

namespace VariableWL.BlockCoordinates
open VariableWL.Affine VariableWL.Blocks Subdivision VariableWL.PrefixParts
attribute [local instance] Classical.propDecidable
variable {r n : ℕ} {P : Type uVariable3} {E : Type uVariable4} [Fintype P] [Fintype E]
  (J : ProductImages.Instance r P E)

abbrev Proper (b : Block (n := n) J) :=
  Σ c : {c : Block (n := n) J // c≠b}, {a : Readout r n P E // HasReadout J b.val a ∧ HasReadout J c.val.val a}

noncomputable instance (priority := 10) defaultProperNumberings :
    (b : Block (n := n) J) → FiniteNumbering (Proper J b) :=
  fun b=>defaultFiniteNumbering (Proper J b)
variable [∀ b : Block (n := n) J, FiniteNumbering (Proper J b)]

noncomputable def properNumber (b : Block (n := n) J) :
    Proper J b ≃ {c : Fin (Fintype.card (Proper J b)+1) // c.val≠0} where
  toFun p := ⟨(enumeration (Proper J b) p).succ,by simp⟩
  invFun c := (enumeration (Proper J b)).symm ⟨c.val.val-1,by have := c.val.isLt; have := c.property; omega⟩
  left_inv p := by simp
  right_inv c := by apply Subtype.ext; apply Fin.ext; simp; have := c.property; omega

noncomputable def channelRoot (b : Block (n := n) J)
    (c : Fin (Fintype.card (Proper J b)+1)) : ℕ :=
  if h : c.val=0 then 0 else readoutDimension J ((properNumber J b).symm ⟨c,h⟩).2.val

noncomputable def channelOrder (hr : 2 ≤ r) (hn : 0 < n) (b : Block (n := n) J)
    (c : Fin (Fintype.card (Proper J b)+1)) : Equiv.Perm (Fin (Fintype.card (Coordinate J b.val))) :=
  if h : c.val=0 then Equiv.refl _ else
    (exists_readout_order J hr hn ((properNumber J b).symm ⟨c,h⟩).2.property.1).choose

noncomputable def data (hr : 2 ≤ r) (hn : 0 < n) (marked : Fin r) (b : Block (n := n) J) : Data where
  dimension := Fintype.card (Coordinate J b.val)
  channels := Fintype.card (Proper J b)+1
  positive := Nat.zero_lt_succ _
  root := channelRoot J b
  root_le c := by
    unfold channelRoot
    split_ifs with h
    · exact Nat.zero_le _
    · exact readoutDimension_le J hr hn ((properNumber J b).symm ⟨c,h⟩).2.property.1
  zero_root := by simp [channelRoot]
  order := channelOrder J hr hn b
  legal ε := {z | LegalValue J marked ε b.val ((encode J b.val).symm z)}
  nonempty ε := by
    obtain ⟨z,hz⟩ := legal_nonempty J marked ε b.val
    exact ⟨encode J b.val z,by simpa using hz⟩
  coset ξ hξ z := by
    change boundaryMap J b.val ((encode J b.val).symm z) = 0 * inhomogeneity J marked b.val ↔
      boundaryMap J b.val ((encode J b.val).symm (z+ξ)) = 1 * inhomogeneity J marked b.val
    change boundaryMap J b.val ((encode J b.val).symm ξ) = 1 * inhomogeneity J marked b.val at hξ
    rw [map_add,map_add,hξ,zero_mul]
    exact add_eq_right.symm

noncomputable def valuationEquiv (hr : 2 ≤ r) (hn : 0 < n) (marked : Fin r) (b : Block (n := n) J) (ε : Bit) :
    Valuation J marked ε b ≃ (data J hr hn marked b).Valuation ε where
  toFun z := ⟨encode J b.val z.val,by
    change LegalValue J marked ε b.val ((encode J b.val).symm (encode J b.val z.val))
    rw [AddEquiv.symm_apply_apply]
    exact z.property⟩
  invFun z := ⟨(encode J b.val).symm z.val,z.property⟩
  left_inv z := Subtype.ext ((encode J b.val).symm_apply_apply _)
  right_inv z := Subtype.ext ((encode J b.val).apply_symm_apply _)

def properSwap : (Σ b : Block (n := n) J, Proper J b) ≃ (Σ b : Block (n := n) J, Proper J b) where
  toFun x := ⟨x.2.1.val,⟨x.1,Ne.symm x.2.1.property⟩,x.2.2.val,x.2.2.property.symm⟩
  invFun x := ⟨x.2.1.val,⟨x.1,Ne.symm x.2.1.property⟩,x.2.2.val,x.2.2.property.symm⟩
  left_inv x := by rfl
  right_inv x := by rfl

noncomputable def channelEquiv (hr : 2 ≤ r) (hn : 0 < n) (marked : Fin r) :
    (Σ b : Block (n := n) J, Proper J b) ≃ Channel (data J hr hn marked) where
  toFun x := ⟨x.1,properNumber J x.1 x.2⟩
  invFun x := ⟨x.1,(properNumber J x.1).symm x.2⟩
  left_inv x := by simp
  right_inv x := by
    rcases x with ⟨b,c⟩
    change (⟨b,properNumber J b ((properNumber J b).symm c)⟩ : Channel (data J hr hn marked))=⟨b,c⟩
    exact congrArg (fun d : {c : Fin (Fintype.card (Proper J b)+1) // c.val ≠ 0} =>
      (⟨b,d⟩ : Channel (data J hr hn marked))) ((properNumber J b).apply_symm_apply c)

theorem channelRoot_number (b : Block (n := n) J) (p : Proper J b) :
    channelRoot J b (properNumber J b p).val=readoutDimension J p.2.val := by
  rw [channelRoot,dite_eq_right (properNumber J b p).property]
  change readoutDimension J ((properNumber J b).symm (properNumber J b p)).2.val=_
  rw [Equiv.symm_apply_apply]

noncomputable def wiring (hr : 2 ≤ r) (hn : 0 < n) (marked : Fin r) : Wiring (data J hr hn marked) where
  mate := (channelEquiv J hr hn marked).symm.trans ((properSwap J).trans (channelEquiv J hr hn marked))
  involutive c := by
    change (channelEquiv J hr hn marked) ((properSwap J) ((channelEquiv J hr hn marked).symm
      ((channelEquiv J hr hn marked) ((properSwap J) ((channelEquiv J hr hn marked).symm c)))))=c
    rw [Equiv.symm_apply_apply]
    change (channelEquiv J hr hn marked) ((channelEquiv J hr hn marked).symm c)=c
    exact Equiv.apply_symm_apply _ _
  different c := by
    obtain ⟨⟨b,p⟩,rfl⟩ := (channelEquiv J hr hn marked).surjective c
    change ((channelEquiv J hr hn marked) ((properSwap J) ((channelEquiv J hr hn marked).symm
      ((channelEquiv J hr hn marked) ⟨b,p⟩)))).1≠b
    rw [Equiv.symm_apply_apply]
    exact p.1.property
  root_eq c := by
    obtain ⟨⟨b,p⟩,rfl⟩ := (channelEquiv J hr hn marked).surjective c
    change (data J hr hn marked
      ((channelEquiv J hr hn marked) ((properSwap J) ((channelEquiv J hr hn marked).symm
        ((channelEquiv J hr hn marked) ⟨b,p⟩)))).1).root
      ((channelEquiv J hr hn marked) ((properSwap J) ((channelEquiv J hr hn marked).symm
        ((channelEquiv J hr hn marked) ⟨b,p⟩)))).2.val = _
    rw [Equiv.symm_apply_apply]
    change channelRoot J p.1.val
      (properNumber J p.1.val ⟨⟨b,Ne.symm p.1.property⟩,p.2.val,p.2.property.symm⟩).val =
      channelRoot J b (properNumber J b p).val
    rw [channelRoot_number,channelRoot_number]

end VariableWL.BlockCoordinates

namespace VariableWL.BlockCoordinates
open VariableWL.Affine VariableWL.Blocks Subdivision VariableWL.PrefixParts
open VariableWL.PrefixParts.Wiring
attribute [local instance] Classical.propDecidable
variable {r n : ℕ} {P : Type uVariable5} {E : Type uVariable6} (J : ProductImages.Instance r P E)

theorem readout_prefix (hr : 2 ≤ r) (hn : 0 < n) {b : RawBlock r n P E}
    {a : Readout r n P E} (ha : HasReadout J b a) (z : RawValue J b) :
    pad (Data.truncate (readoutDimension J a)
      (encode J b z ∘ (exists_readout_order J hr hn ha).choose)) =
    pad (readoutEquiv J a (readout J z ha)) := by
  funext j
  by_cases hj : j<readoutDimension J a
  · have hja : j<Fintype.card (Coordinate J b) := lt_of_lt_of_le hj (readoutDimension_le J hr hn ha)
    simp only [pad,dite_eq_left hja,dite_eq_left hj,Data.truncate,ite_eq_left hj,Function.comp_apply]
    rw [(exists_readout_order J hr hn ha).choose_spec ⟨j,hj⟩]
    exact readoutEmbedding_spec J hr hn ha z ⟨j,hj⟩
  · simp only [pad,dite_eq_right hj]
    split_ifs with hja
    · simp only [Data.truncate,ite_eq_right hj]
    · rfl

variable [Fintype P] [Fintype E] [∀ b : Block (n := n) J, FiniteNumbering (Proper J b)]

theorem channelOrder_number (hr : 2 ≤ r) (hn : 0 < n) (b : Block (n := n) J) (p : Proper J b) :
    channelOrder J hr hn b (properNumber J b p).val=
      (exists_readout_order J hr hn p.2.property.1).choose := by
  rw [channelOrder,dite_eq_right (properNumber J b p).property]
  change (exists_readout_order J hr hn
    ((properNumber J b).symm (properNumber J b p)).2.property.1).choose=_
  rw [Equiv.symm_apply_apply]

theorem data_prefix (hr : 2 ≤ r) (hn : 0 < n) (marked : Fin r) (b : Block (n := n) J)
    (p : Proper J b) {ε : Bit} (z : Valuation J marked ε b) :
    pad (Data.truncate ((data J hr hn marked b).root (properNumber J b p).val)
      (((valuationEquiv J hr hn marked b ε) z).val ∘
        (data J hr hn marked b).order (properNumber J b p).val)) =
    pad (readoutEquiv J p.2.val (readout J z.val p.2.property.1)) := by
  change pad (Data.truncate (channelRoot J b (properNumber J b p).val)
    (encode J b.val z.val ∘ channelOrder J hr hn b (properNumber J b p).val))=_
  rw [channelRoot_number,channelOrder_number]
  exact readout_prefix J hr hn p.2.property.1 z.val

@[simp] theorem mate_channel (hr : 2 ≤ r) (hn : 0 < n) (marked : Fin r)
    (x : Σ b : Block (n := n) J, Proper J b) :
    (wiring J hr hn marked).mate (channelEquiv J hr hn marked x)=
      channelEquiv J hr hn marked (properSwap J x) := by
  change (channelEquiv J hr hn marked) ((properSwap J)
    ((channelEquiv J hr hn marked).symm ((channelEquiv J hr hn marked) x)))=_
  rw [Equiv.symm_apply_apply]

noncomputable def encodeList (hr : 2 ≤ r) (hn : 0 < n) (marked : Fin r)
    (ξ : ∀ b : Block (n := n) J, Valuation J marked 1 b) :
    ∀ b, (data J hr hn marked b).Valuation 1 := fun b => valuationEquiv J hr hn marked b 1 (ξ b)

theorem rootShift_encode (hr : 2 ≤ r) (hn : 0 < n) (marked : Fin r)
    (ξ : ∀ b : Block (n := n) J, Valuation J marked 1 b) (b : Block (n := n) J) (p : Proper J b) :
    rootShift (data J hr hn marked) (encodeList J hr hn marked ξ) (channelEquiv J hr hn marked ⟨b,p⟩)=
      pad (readoutEquiv J p.2.val (readout J (ξ b).val p.2.property.1)) :=
  data_prefix J hr hn marked b p (ξ b)

theorem compatible_of_agree (hr : 2 ≤ r) (hn : 0 < n) (marked : Fin r)
    (ξ : ∀ b : Block (n := n) J, Valuation J marked 1 b) {b c : Block (n := n) J}
    (h : General.Agree J marked ⟨b,ξ b⟩ ⟨c,ξ c⟩) :
    CompatiblePair (data J hr hn marked) (wiring J hr hn marked) (encodeList J hr hn marked ξ) b c := by
  intro d hd hc
  obtain ⟨⟨e,p⟩,rfl⟩ := (channelEquiv J hr hn marked).surjective d
  change e=b at hd
  subst e
  rw [mate_channel] at hc ⊢
  change p.1.val=c at hc
  rw [rootShift_encode,rootShift_encode]
  change pad (readoutEquiv J p.2.val (readout J (ξ b).val p.2.property.1))=
    pad (readoutEquiv J p.2.val (readout J (ξ p.1.val).val p.2.property.2))
  have hag : General.Agree J marked ⟨b,ξ b⟩ ⟨p.1.val,ξ p.1.val⟩ := hc.symm ▸ h
  rw [hag p.2.val p.2.property.1 p.2.property.2]

end VariableWL.BlockCoordinates

namespace VariableWL.PrefixParts.Wiring
open VariableWL.Affine VariableWL.SubcubicRealization
variable {B : Type uVariable7} [Fintype B] [FiniteNumbering B] (D : B → Data) [FiniteNumbering (SortTag D)]

omit [FiniteNumbering B] in
theorem uncoloredTranslation_local (ξ η : ∀ b, (D b).Valuation 1)
    (x : UncoloredVertex D 0) (h : ξ x.owner.1=η x.owner.1) :
    uncoloredTranslation D ξ x=uncoloredTranslation D η x := by
  apply SubcubicRealization.Vertex.ext
  · change (⟨x.owner.1,(D x.owner.1).vertexTranslation (ξ x.owner.1) x.owner.2⟩ : Vertex D 1)=
      ⟨x.owner.1,(D x.owner.1).vertexTranslation (η x.owner.1) x.owner.2⟩
    rw [h]
  · change Data.localPorts (ξ x.owner.1) x.owner.2 x.port=Data.localPorts (η x.owner.1) x.owner.2 x.port
    rw [h]
  · rfl
end VariableWL.PrefixParts.Wiring

end OAI
