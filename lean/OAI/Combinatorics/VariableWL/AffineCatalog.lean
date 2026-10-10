import OAI.Combinatorics.VariableWL.BlockListing

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4

namespace VariableWL.AffineCatalog
open Blocks Subdivision Descriptor VariableWL.Affine
attribute [local instance] Classical.propDecidable
structure Data extends BlockCatalog.Data where
  realDimension : ℕ → ℕ
  leftForm : ℕ → ℕ
  rightForm : ℕ → ℕ
  leftConstant : ℕ → ℕ
  rightConstant : ℕ → ℕ
  marked : ℕ
  epsilon : ℕ
namespace Data
variable (D : Data)
def vertexDimension (t : ℕ) : ℕ := if t<D.reals then D.realDimension t else 1
def horizontalDimension (h : ℕ) : ℕ := D.vertexDimension (D.htype h)
def squareLeftDimension (s : ℕ) : ℕ := D.vertexDimension (D.left (D.slink s))
def squareRightDimension (s : ℕ) : ℕ := D.vertexDimension (D.right (D.slink s))
def dimension (b : ℕ) : ℕ := if b<D.horizontals then D.horizontalDimension b else
  D.squareLeftDimension (b-D.horizontals)+D.squareRightDimension (b-D.horizontals)+2
def readDimension (a : ℕ) : ℕ := if a<D.horizontals then D.horizontalDimension a else 1
noncomputable def linkLeft (l : ℕ) : ℕ := if l%(D.internal+1)=0 then D.leftForm (l/(D.internal+1)) else
  AffineAlphabet.encodeForm (by decide : 1≤2) (LinearMap.proj (0 : Fin 1))
noncomputable def linkRight (l : ℕ) : ℕ := if l%(D.internal+1)=D.internal then D.rightForm (l/(D.internal+1)) else
  AffineAlphabet.encodeForm (by decide : 1≤2) (LinearMap.proj (0 : Fin 1))
def linkLeftConstant (l : ℕ) : ℕ := if l%(D.internal+1)=0 then D.leftConstant (l/(D.internal+1)) else 0
def linkRightConstant (l : ℕ) : ℕ := if l%(D.internal+1)=D.internal then D.rightConstant (l/(D.internal+1)) else 0
def constant (s : ℕ) : ℕ := (D.epsilon*(if D.srow s=D.marked then
  D.linkLeftConstant (D.slink s)+D.linkRightConstant (D.slink s) else 0))%2
noncomputable def zeroOrder (b : ℕ) : ℕ := AffineAlphabet.zeroOrder (D.dimension b)
noncomputable def readOrder (b a : ℕ) : ℕ := if b<D.horizontals then AffineAlphabet.horizontalOrder (D.horizontalDimension b) else
  let s:=b-D.horizontals
  AffineAlphabet.squareOrder (D.squareLeftDimension s) (D.squareRightDimension s)
    (if a=D.squareLeft s then 0 else if a=D.squareRight s then 1 else if a=D.squareBottom s then 2 else 3)
noncomputable def legal (b i : ℕ) : Bool := if b<D.horizontals then AffineAlphabet.horizontalLegal (D.horizontalDimension b) i else
  let s:=b-D.horizontals
  AffineAlphabet.squareLegal (D.linkLeft (D.slink s)) (D.linkRight (D.slink s)) (D.constant s) i
noncomputable def core : BlockDescriptor.Core where
  blocks := D.blocks
  validBlock := D.validBlock
  reads := D.reads
  validRead := D.readValid
  has := D.has
  dimension := D.dimension
  readDimension := D.readDimension
  zeroOrder := D.zeroOrder
  readOrder := D.readOrder
  legal := D.legal
end Data
variable {r n : ℕ} {P : Type uVariable1} {E : Type uVariable2} (PP : Presentation P) (PE : Presentation E)
variable (J : ProductImages.Instance r P E) (marked : Fin r) (ε : Bit)
structure Good (D : Data) : Prop extends BlockCatalog.Good (n := n) PP PE J D.toData where
  realDimension : ∀p,D.realDimension (PP.encode p)=J.dimension p
  leftForm : ∀e,D.leftForm (PE.encode e)=AffineAlphabet.encodeForm
    (RealizationSize.dimension_le_two J (n := n) (.inl (J.source e))) (J.linearLeft e)
  rightForm : ∀e,D.rightForm (PE.encode e)=AffineAlphabet.encodeForm
    (RealizationSize.dimension_le_two J (n := n) (.inl (J.target e))) (J.linearRight e)
  leftConstant : ∀e,D.leftConstant (PE.encode e)=(J.constantLeft e).val
  rightConstant : ∀e,D.rightConstant (PE.encode e)=(J.constantRight e).val
  marked : D.marked=marked.val
  epsilon : D.epsilon=ε.val
variable {D : Data} (h : Good (n := n) PP PE J marked ε D)
include h
 theorem vertex_dimension (t : Vertex P E n) : D.vertexDimension ((BlockCatalog.vertex PP PE).encode t)=Blocks.dimension J t := by
  cases t with
  | inl p =>
    rw [Data.vertexDimension,BlockCatalog.vertex_inl,h.reals,ite_eq_left (PP.encode_lt p),h.realDimension]
    rfl
  | inr q =>
    rcases q with ⟨e,j⟩
    rw [Data.vertexDimension,BlockCatalog.vertex_inr,h.reals,ite_eq_right (by omega)]
    rfl
 theorem horizontal_dimension (x : Horizontal r n P E) : D.horizontalDimension ((BlockCatalog.horizontal PP PE).encode x)=dimension J x.type := by
  rw [Data.horizontalDimension,(BlockCatalog.horizontal_parts PP PE J h.toGood x).2.1]
  exact vertex_dimension PP PE J marked ε h x.type
 theorem square_dimensions (s : Square r n E) :
    D.squareLeftDimension ((BlockCatalog.square PE).encode s)=dimension J (left J.source s.link) ∧
    D.squareRightDimension ((BlockCatalog.square PE).encode s)=dimension J (right J.target s.link) := by
  obtain ⟨_,hl,_,_⟩ := BlockCatalog.square_parts PP PE J h.toGood s
  simp only [Data.squareLeftDimension,Data.squareRightDimension,hl,
    BlockCatalog.left_code PP PE J h.toGood,BlockCatalog.right_code PP PE J h.toGood,
    vertex_dimension PP PE J marked ε h]
  exact ⟨trivial,trivial⟩
 theorem dimension_code (b : RawBlock r n P E) : D.dimension ((BlockCatalog.raw PP PE).encode b)=Fintype.card (BlockCoordinates.Coordinate J b) := by
  cases b with
  | inl x =>
    change (if (BlockCatalog.horizontal PP PE).encode x<D.horizontals then _ else _)=_
    rw [ite_eq_left (by rw [BlockCatalog.horizontals_eq PP PE J h.toGood]; exact (BlockCatalog.horizontal PP PE).encode_lt x)]
    change D.horizontalDimension ((BlockCatalog.horizontal PP PE).encode x)=_
    rw [horizontal_dimension PP PE J marked ε h]
    simp only [BlockCoordinates.Coordinate,Fintype.card_fin]
  | inr s =>
    change (if (BlockCatalog.horizontal (r := r) (n := n) PP PE).bound+(BlockCatalog.square PE).encode s<D.horizontals then _ else _)=_
    rw [BlockCatalog.horizontals_eq PP PE J h.toGood,ite_eq_right (by omega)]
    have hs : (BlockCatalog.horizontal (r := r) (n := n) PP PE).bound+(BlockCatalog.square (r := r) (n := n) PE).encode s-
        (BlockCatalog.horizontal (r := r) (n := n) PP PE).bound=(BlockCatalog.square PE).encode s := by omega
    change (BlockCatalog.horizontal (r := r) (n := n) PP PE).bound+(BlockCatalog.square PE).encode s-
      (BlockCatalog.horizontal (r := r) (n := n) PP PE).bound=(BlockCatalog.square PE).encode s at hs
    simp only [BlockCatalog.raw,Presentation.sum_inr,Nat.add_sub_cancel_left] at *
    obtain ⟨hl,hr⟩ := square_dimensions PP PE J marked ε h s
    rw [hl,hr]
    simp only [BlockCoordinates.Coordinate,Fintype.card_sum,Fintype.card_fin,Fintype.card_bool]
 theorem read_dimension (a : Readout r n P E) : D.readDimension ((BlockCatalog.readout PP PE).encode a)=BlockCoordinates.readoutDimension J a := by
  cases a with
  | inl x =>
    change (if (BlockCatalog.horizontal PP PE).encode x<D.horizontals then _ else _)=_
    rw [ite_eq_left (by rw [BlockCatalog.horizontals_eq PP PE J h.toGood]; exact (BlockCatalog.horizontal PP PE).encode_lt x)]
    change D.horizontalDimension ((BlockCatalog.horizontal PP PE).encode x)=_
    rw [horizontal_dimension PP PE J marked ε h]
    rfl
  | inr x =>
    change (if (BlockCatalog.horizontal (r := r) (n := n) PP PE).bound+(BlockCatalog.vertical PE).encode x<D.horizontals then _ else _)=_
    rw [BlockCatalog.horizontals_eq PP PE J h.toGood,ite_eq_right (by omega)]
    rfl
 theorem link_left (l : Link E n) : D.linkLeft ((BlockCatalog.link PE).encode l)=AffineAlphabet.encodeForm
    (RealizationSize.dimension_le_two J (left J.source l)) (Blocks.linkLeft J l) := by
  rcases l with ⟨e,j⟩
  simp only [Data.linkLeft,h.internal,BlockCatalog.link_encode,
    PrefixDescriptor.Data.join_div _ _ _ (by omega : 0<n+1) j.isLt,PrefixDescriptor.Data.join_mod _ _ _ j.isLt]
  by_cases hz : j.val=0
  · simp only [ite_eq_left hz,h.leftForm,Blocks.linkLeft,Subdivision.left,dite_eq_left hz]
    apply AffineAlphabet.encodeForm_heq
    · simp [dimension,hz]
    · exact (cast_heq _ _).symm
  · simp only [ite_eq_right hz,Blocks.linkLeft,Subdivision.left,dite_eq_right hz,Blocks.dimension]
    apply AffineAlphabet.encodeForm_heq
    · simp [hz]
    · exact (cast_heq _ _).symm
 theorem link_right (l : Link E n) : D.linkRight ((BlockCatalog.link PE).encode l)=AffineAlphabet.encodeForm
    (RealizationSize.dimension_le_two J (right J.target l)) (Blocks.linkRight J l) := by
  rcases l with ⟨e,j⟩
  simp only [Data.linkRight,h.internal,BlockCatalog.link_encode,
    PrefixDescriptor.Data.join_div _ _ _ (by omega : 0<n+1) j.isLt,PrefixDescriptor.Data.join_mod _ _ _ j.isLt]
  by_cases hz : j.val=n
  · simp only [ite_eq_left hz,h.rightForm,Blocks.linkRight,Subdivision.right,dite_eq_left hz]
    apply AffineAlphabet.encodeForm_heq
    · simp [dimension,hz]
    · exact (cast_heq _ _).symm
  · simp only [ite_eq_right hz,Blocks.linkRight,Subdivision.right,dite_eq_right hz,Blocks.dimension]
    apply AffineAlphabet.encodeForm_heq
    · simp [hz]
    · exact (cast_heq _ _).symm
 theorem link_left_constant (l : Link E n) : (D.linkLeftConstant ((BlockCatalog.link PE).encode l) : Bit)=Blocks.leftConstant J l := by
  rcases l with ⟨e,j⟩
  simp only [Data.linkLeftConstant,h.internal,BlockCatalog.link_encode,
    PrefixDescriptor.Data.join_div _ _ _ (by omega : 0<n+1) j.isLt,PrefixDescriptor.Data.join_mod _ _ _ j.isLt,
    Blocks.leftConstant,h.leftConstant]
  split_ifs <;> simp only [ZMod.natCast_zmod_val,Nat.cast_zero]
 theorem link_right_constant (l : Link E n) : (D.linkRightConstant ((BlockCatalog.link PE).encode l) : Bit)=Blocks.rightConstant J l := by
  rcases l with ⟨e,j⟩
  simp only [Data.linkRightConstant,h.internal,BlockCatalog.link_encode,
    PrefixDescriptor.Data.join_div _ _ _ (by omega : 0<n+1) j.isLt,PrefixDescriptor.Data.join_mod _ _ _ j.isLt,
    Blocks.rightConstant,h.rightConstant]
  split_ifs <;> simp only [ZMod.natCast_zmod_val,Nat.cast_zero]
 theorem constant_code (s : Square r n E) : (D.constant ((BlockCatalog.square PE).encode s) : Bit)=ε*inhomogeneity J marked (.inr s) := by
  obtain ⟨hrw,hl,_,_⟩ := BlockCatalog.square_parts PP PE J h.toGood s
  rw [Data.constant]
  simp only [hrw,hl,h.marked,h.epsilon,Blocks.inhomogeneity,Blocks.linkConstant]
  rw [ZMod.natCast_mod, Nat.cast_mul,ZMod.natCast_zmod_val]
  by_cases hi : s.row=marked
  · subst marked
    rw [ite_eq_left rfl,Nat.cast_add,link_left_constant PP PE J _ ε h,link_right_constant PP PE J _ ε h]
    simp only [marker,ite_true,one_mul]
  · rw [ite_eq_right (fun he=>hi (Fin.ext he)),Nat.cast_zero,mul_zero]
    simp only [marker,ite_eq_right hi,zero_mul,mul_zero]
end VariableWL.AffineCatalog

namespace VariableWL.AffineCatalog
open Blocks Subdivision Descriptor VariableWL.Affine
attribute [local instance] Classical.propDecidable
variable {r n : ℕ} {P : Type uVariable3} {E : Type uVariable4} (PP : Presentation P) (PE : Presentation E)
variable (J : ProductImages.Instance r P E) (marked : Fin r) (ε : Bit)
variable {D : Data} (h : Good (n := n) PP PE J marked ε D)
include h
 theorem zero_order (b : RawBlock r n P E) : D.zeroOrder ((BlockCatalog.raw PP PE).encode b)=
    PrefixAlphabet.encodeOrder (RealizationSize.coordinate_card J b) (Equiv.refl _) := by
  rw [Data.zeroOrder,dimension_code PP PE J marked ε h,AffineAlphabet.zeroOrder,
    dite_eq_left (RealizationSize.coordinate_card J b)]
 theorem read_order (hr : 2≤r) (hn : 0<n) (b : RawBlock r n P E) (a : Readout r n P E)
    (ha : HasReadout J b a) : D.readOrder ((BlockCatalog.raw PP PE).encode b) ((BlockCatalog.readout PP PE).encode a)=
      PrefixAlphabet.encodeOrder (RealizationSize.coordinate_card J b) (BlockCoordinates.exists_readout_order J hr hn ha).choose := by
  cases b with
  | inl x =>
    have he : a=.inl x := ha
    subst a
    change (if (BlockCatalog.horizontal PP PE).encode x<D.horizontals then _ else _)=_
    rw [ite_eq_left (by rw [BlockCatalog.horizontals_eq PP PE J h.toGood]; exact (BlockCatalog.horizontal PP PE).encode_lt x)]
    change AffineAlphabet.horizontalOrder (D.horizontalDimension ((BlockCatalog.horizontal PP PE).encode x))=_
    rw [horizontal_dimension PP PE J marked ε h]
    have ho := BlockCoordinates.order_eq_extend J hr hn (b := .inl x) (a := .inl x) rfl
    have hb := BlockCoordinates.embedding_horizontal J hr hn x
    rw [ho,hb]
    rw [AffineAlphabet.horizontalOrder,dite_eq_left (RealizationSize.dimension_le_two J x.type)]
    rfl
  | inr s =>
    change (if (BlockCatalog.horizontal (r := r) (n := n) PP PE).bound+(BlockCatalog.square PE).encode s<D.horizontals then _ else _)=_
    rw [BlockCatalog.horizontals_eq PP PE J h.toGood,ite_eq_right (by omega)]
    have hs : (BlockCatalog.horizontal (r := r) (n := n) PP PE).bound+(BlockCatalog.square (r := r) (n := n) PE).encode s-
        (BlockCatalog.horizontal (r := r) (n := n) PP PE).bound=(BlockCatalog.square PE).encode s := by omega
    dsimp only
    change (BlockCatalog.horizontal (r := r) (n := n) PP PE).bound+(BlockCatalog.square PE).encode s-
      (BlockCatalog.horizontal (r := r) (n := n) PP PE).bound=(BlockCatalog.square PE).encode s at hs
    simp only [BlockCatalog.raw,Presentation.sum_inr,Nat.add_sub_cancel_left] at *
    obtain ⟨hl,he⟩ := square_dimensions PP PE J marked ε h s
    obtain ⟨fl,fr,fb,ft⟩ := BlockCatalog.square_faces PP PE J h.toGood s
    rw [hl,he,fl,fr,fb]
    have hi := (BlockCatalog.readout (r := r) (n := n) PP PE).encode_injective
    change a=.inl (squareLeft J s) ∨ a=.inl (squareRight J s) ∨ a=.inr (squareBottom s) ∨ a=.inr (squareTop s) at ha
    rcases ha with ha | ha | ha | ha
    all_goals subst a
    · simp only [ite_true]
      rw [AffineAlphabet.squareOrder,dite_eq_left (RealizationSize.dimension_le_two J (left J.source s.link)),
        dite_eq_left (RealizationSize.dimension_le_two J (right J.target s.link)),ite_eq_left rfl]
      have hh := (BlockCoordinates.order_eq_extend J hr hn (b := .inr s) (a := .inl (squareLeft J s)) (Or.inl rfl)).trans
        (congrArg AffineAlphabet.extend (BlockCoordinates.embedding_left J hr hn s))
      exact (congrArg (PrefixAlphabet.encodeOrder (RealizationSize.coordinate_card J (.inr s))) hh).symm
    · have hnL : (BlockCatalog.readout PP PE).encode (.inl (squareRight J s)) ≠ (BlockCatalog.readout PP PE).encode (.inl (squareLeft J s)) :=
        fun hh=>squareLeft_ne_right J hn s (Sum.inl.inj (hi hh)).symm
      simp only [hnL,ite_false,ite_true]
      rw [AffineAlphabet.squareOrder,dite_eq_left (RealizationSize.dimension_le_two J (left J.source s.link)),
        dite_eq_left (RealizationSize.dimension_le_two J (right J.target s.link)),ite_eq_right (by decide : ¬(1 : ℕ)=0),ite_eq_left rfl]
      have hh := (BlockCoordinates.order_eq_extend J hr hn (b := .inr s) (a := .inl (squareRight J s)) (Or.inr (Or.inl rfl))).trans
        (congrArg AffineAlphabet.extend (BlockCoordinates.embedding_right J hr hn s))
      exact (congrArg (PrefixAlphabet.encodeOrder (RealizationSize.coordinate_card J (.inr s))) hh).symm
    · have hnL : (BlockCatalog.readout PP PE).encode (.inr (squareBottom s)) ≠ (BlockCatalog.readout PP PE).encode (.inl (squareLeft J s)) := fun hh=>Sum.inr_ne_inl (hi hh)
      have hnR : (BlockCatalog.readout PP PE).encode (.inr (squareBottom s)) ≠ (BlockCatalog.readout PP PE).encode (.inl (squareRight J s)) := fun hh=>Sum.inr_ne_inl (hi hh)
      simp only [hnL,hnR,ite_false,ite_true]
      rw [AffineAlphabet.squareOrder,dite_eq_left (RealizationSize.dimension_le_two J (left J.source s.link)),
        dite_eq_left (RealizationSize.dimension_le_two J (right J.target s.link)),ite_eq_right (by decide : ¬(2 : ℕ)=0),ite_eq_right (by decide : ¬(2 : ℕ)=1)]
      have hh := (BlockCoordinates.order_eq_extend J hr hn (b := .inr s) (a := .inr (squareBottom s)) (Or.inr (Or.inr (Or.inl rfl)))).trans
        (congrArg AffineAlphabet.extend (BlockCoordinates.embedding_bottom J hr hn s))
      exact (congrArg (PrefixAlphabet.encodeOrder (RealizationSize.coordinate_card J (.inr s))) hh).symm
    · have hnL : (BlockCatalog.readout PP PE).encode (.inr (squareTop s)) ≠ (BlockCatalog.readout PP PE).encode (.inl (squareLeft J s)) := fun hh=>Sum.inr_ne_inl (hi hh)
      have hnR : (BlockCatalog.readout PP PE).encode (.inr (squareTop s)) ≠ (BlockCatalog.readout PP PE).encode (.inl (squareRight J s)) := fun hh=>Sum.inr_ne_inl (hi hh)
      have hnB : (BlockCatalog.readout PP PE).encode (.inr (squareTop s)) ≠ (BlockCatalog.readout PP PE).encode (.inr (squareBottom s)) := fun hh=>squareBottom_ne_top hr s (Sum.inr.inj (hi hh)).symm
      simp only [hnL,hnR,hnB,ite_false]
      rw [AffineAlphabet.squareOrder,dite_eq_left (RealizationSize.dimension_le_two J (left J.source s.link)),
        dite_eq_left (RealizationSize.dimension_le_two J (right J.target s.link)),ite_eq_right (by decide : ¬(3 : ℕ)=0),ite_eq_right (by decide : ¬(3 : ℕ)=1)]
      have hh := (BlockCoordinates.order_eq_extend J hr hn (b := .inr s) (a := .inr (squareTop s)) (Or.inr (Or.inr (Or.inr rfl)))).trans
        (congrArg AffineAlphabet.extend (BlockCoordinates.embedding_top J hr hn s))
      exact (congrArg (PrefixAlphabet.encodeOrder (RealizationSize.coordinate_card J (.inr s))) hh).symm
 theorem legal_code (b : RawBlock r n P E) (i : ℕ) : D.legal ((BlockCatalog.raw PP PE).encode b) i=true ↔
    ∃z : RawValue J b,LegalValue J marked ε b z ∧
      PrefixAlphabet.encode (RealizationSize.coordinate_card J b) (BlockCoordinates.encode J b z)=i := by
  cases b with
  | inl x =>
    change (if (BlockCatalog.horizontal PP PE).encode x<D.horizontals then _ else _)=true ↔ _
    rw [ite_eq_left (by rw [BlockCatalog.horizontals_eq PP PE J h.toGood]; exact (BlockCatalog.horizontal PP PE).encode_lt x)]
    change AffineAlphabet.horizontalLegal (D.horizontalDimension ((BlockCatalog.horizontal PP PE).encode x)) i=true ↔ _
    rw [horizontal_dimension PP PE J marked ε h,
      AffineAlphabet.horizontalLegal_eq (RealizationSize.dimension_le_two J x.type)]
    simp only [LegalValue,boundaryMap,inhomogeneity,mul_zero,AddMonoidHom.zero_apply,true_and]
    rfl
  | inr s =>
    change (if (BlockCatalog.horizontal (r := r) (n := n) PP PE).bound+(BlockCatalog.square PE).encode s<D.horizontals then _ else _)=true ↔ _
    rw [BlockCatalog.horizontals_eq PP PE J h.toGood,ite_eq_right (by omega)]
    have hs : (BlockCatalog.horizontal (r := r) (n := n) PP PE).bound+(BlockCatalog.square (r := r) (n := n) PE).encode s-
        (BlockCatalog.horizontal (r := r) (n := n) PP PE).bound=(BlockCatalog.square PE).encode s := by omega
    dsimp only
    change (BlockCatalog.horizontal (r := r) (n := n) PP PE).bound+(BlockCatalog.square PE).encode s-
      (BlockCatalog.horizontal (r := r) (n := n) PP PE).bound=(BlockCatalog.square PE).encode s at hs
    simp only [BlockCatalog.raw,Presentation.sum_inr,Nat.add_sub_cancel_left] at *
    rw [(BlockCatalog.square_parts PP PE J h.toGood s).2.1,link_left PP PE J marked ε h,link_right PP PE J marked ε h]
    have hc : D.constant ((BlockCatalog.square PE).encode s)=(ε*inhomogeneity J marked (.inr s)).val := by
      have hh := congrArg ZMod.val (constant_code PP PE J marked ε h s)
      rw [ZMod.val_natCast] at hh
      have hm : D.constant ((BlockCatalog.square PE).encode s)<2 := Nat.mod_lt _ (by decide)
      rwa [Nat.mod_eq_of_lt hm] at hh
    rw [hc,AffineAlphabet.squareLegal_eq]
    rfl
 theorem core_good (hr : 2≤r) (hn : 0<n) : BlockDescriptor.Good J hr hn marked
    (BlockCatalog.block PP PE J h.toGood) (BlockCatalog.readout PP PE)
      (fun b=>RealizationSize.coordinate_card J b.val) ε D.core := by
  refine ⟨(BlockCatalog.block_bound PP PE J h.toGood).symm,BlockCatalog.reads_eq PP PE J h.toGood,
    (BlockCatalog.block_valid PP PE J h.toGood).symm,BlockCatalog.readValid_eq PP PE J h.toGood,
    BlockCatalog.has_code PP PE J h.toGood,?_,read_dimension PP PE J marked ε h,?_,?_,?_⟩
  · intro b; exact dimension_code PP PE J marked ε h b.val
  · intro b; exact zero_order PP PE J marked ε h b.val
  · intro b a ha; exact read_order PP PE J marked ε h hr hn b.val a ha
  · intro b i
    rw [show D.core.legal (BlockCatalog.block PP PE J h.toGood |>.encode b) i=D.legal ((BlockCatalog.raw PP PE).encode b.val) i from rfl,
      legal_code PP PE J marked ε h]
    exact ⟨fun ⟨z,hz,he⟩=>⟨⟨z,hz⟩,he⟩,fun ⟨z,he⟩=>⟨z.val,z.property,he⟩⟩
end VariableWL.AffineCatalog

namespace VariableWL.AffineAlphabet
open VariableWL.Affine
attribute [local instance] Classical.propDecidable
 theorem horizontalLegal_false {d i : ℕ} (h : ¬(d<3 ∧ i<PrefixAlphabet.vectorCount)) : horizontalLegal d i=false := by
  apply Bool.eq_false_iff.mpr
  intro he
  obtain ⟨hd,z,hz⟩ := of_decide_eq_true he
  have hi := PrefixAlphabet.encode_lt (by simp only [Fintype.card_fin]; omega) (horizontalEncode d z)
  exact h ⟨by omega,hz ▸ hi⟩
 theorem squareLegal_false {l r c i : ℕ} (h : ¬(l<formCount ∧ r<formCount ∧ i<PrefixAlphabet.vectorCount)) : squareLegal l r c i=false := by
  unfold squareLegal
  split_ifs with hl hr
  · apply Bool.eq_false_iff.mpr
    intro he
    obtain ⟨z,_,hz⟩ := of_decide_eq_true he
    have hi := PrefixAlphabet.encode_lt (square_count_le (formNumber.symm ⟨l,hl⟩).1 (formNumber.symm ⟨r,hr⟩).1)
      (squareEncode _ _ z)
    exact h ⟨hl,hr,hz ▸ hi⟩
  all_goals rfl
 theorem squareLegal_mod (l r c i : ℕ) : squareLegal l r (c%2) i=squareLegal l r c i := by
  unfold squareLegal
  split_ifs <;> simp only [ZMod.natCast_mod]
 theorem horizontalOrder_false {d : ℕ} (h : ¬d<3) : horizontalOrder d=0 := dite_eq_right (by omega)
 theorem squareOrder_false {d e a : ℕ} (h : ¬(d<3 ∧ e<3)) : squareOrder d e a=0 := by
  unfold squareOrder
  split_ifs <;> omega
 theorem squareOrder_cap (d e a : ℕ) : squareOrder d e (min a 3)=squareOrder d e a := by
  by_cases ha : a≤3
  · rw [Nat.min_eq_left ha]
  · have h3 : 3≤a := by omega
    rw [Nat.min_eq_right h3]
    unfold squareOrder
    simp only [show ¬a=0 by omega,show ¬a=1 by omega,ite_false]
    split_ifs <;> simp_all [show a≠2 by omega]
 theorem zeroOrder_false {d : ℕ} (h : ¬d<7) : zeroOrder d=0 := dite_eq_right (by omega)
end VariableWL.AffineAlphabet

namespace VariableWL.AffineAlphabet.Program
open Computation.Stack.PolyRecipe Computation.Stack.Recipe
variable {n : ℕ}
noncomputable def horizontalLegal (D I : Expr n) : Expr n :=
  eq (table₂ 3 PrefixAlphabet.vectorCount (fun d i=>if AffineAlphabet.horizontalLegal d i then 1 else 0) D I) (numeral 1)
noncomputable def squareLegalBody (L R C I : Expr n) : Expr n :=
  eq (table₃ formCount formCount (2*PrefixAlphabet.vectorCount)
    (fun l r q=>if AffineAlphabet.squareLegal l r (q/PrefixAlphabet.vectorCount) (q%PrefixAlphabet.vectorCount) then 1 else 0)
    L R (add (mul (mod C (numeral 2)) (numeral PrefixAlphabet.vectorCount)) I)) (numeral 1)
noncomputable def horizontalOrder (D : Expr n) : Expr n := fixedNat 3 (fun d=>AffineAlphabet.horizontalOrder d.val) D
noncomputable def squareOrder (D E A : Expr n) : Expr n := table₃ 3 3 4 AffineAlphabet.squareOrder D E (minimum A (numeral 3))
noncomputable def zeroOrder (D : Expr n) : Expr n := fixedNat 7 (fun d=>AffineAlphabet.zeroOrder d.val) D
 theorem horizontalOrder_number (D : Expr n) (v : Env n) : (horizontalOrder D).number v=AffineAlphabet.horizontalOrder (D.number v) := by
  rw [horizontalOrder,fixedNat_total]
  unfold tableLookup
  split_ifs with h
  · rfl
  · exact (horizontalOrder_false h).symm
 theorem zeroOrder_number (D : Expr n) (v : Env n) : (zeroOrder D).number v=AffineAlphabet.zeroOrder (D.number v) := by
  rw [zeroOrder,fixedNat_total]
  unfold tableLookup
  split_ifs with h
  · rfl
  · exact (zeroOrder_false h).symm
 theorem squareOrder_number (D E A : Expr n) (v : Env n) :
    (squareOrder D E A).number v=AffineAlphabet.squareOrder (D.number v) (E.number v) (A.number v) := by
  simp only [squareOrder,table₃_number,minimum_number,numeral_number]
  split_ifs with h
  · exact squareOrder_cap _ _ _
  · exact (squareOrder_false (by have := Nat.min_le_right (A.number v) 3; omega)).symm
 theorem horizontalLegal_bit (D I : Expr n) (v : Env n) :
    (horizontalLegal D I).bit v=AffineAlphabet.horizontalLegal (D.number v) (I.number v) := by
  simp only [horizontalLegal,eq_bit,table₂_number,numeral_number]
  by_cases h : D.number v<3 ∧ I.number v<PrefixAlphabet.vectorCount
  · rw [ite_eq_left h]
    cases AffineAlphabet.horizontalLegal (D.number v) (I.number v) <;> rfl
  · rw [ite_eq_right h,horizontalLegal_false h]
    rfl
 theorem squareLegal_bit_bounded (L R C I : Expr n) (v : Env n) (hi : I.number v<PrefixAlphabet.vectorCount) :
    (squareLegalBody L R C I).bit v=AffineAlphabet.squareLegal (L.number v) (R.number v) (C.number v) (I.number v) := by
  have hc : C.number v%2<2 := Nat.mod_lt _ (by decide)
  have hp : 0<PrefixAlphabet.vectorCount := by omega
  have hq : C.number v%2*PrefixAlphabet.vectorCount+I.number v<2*PrefixAlphabet.vectorCount := by
    nlinarith
  simp only [squareLegalBody,eq_bit,table₃_number,add_number,mul_number,mod_number,numeral_number]
  by_cases h : L.number v<formCount ∧ R.number v<formCount ∧ C.number v%2*PrefixAlphabet.vectorCount+I.number v<2*PrefixAlphabet.vectorCount
  · rw [ite_eq_left h,PrefixDescriptor.Data.join_div _ _ _ hp hi,PrefixDescriptor.Data.join_mod _ _ _ hi,squareLegal_mod]
    cases AffineAlphabet.squareLegal (L.number v) (R.number v) (C.number v) (I.number v) <;> rfl
  · have hh : ¬(L.number v<formCount ∧ R.number v<formCount ∧ I.number v<PrefixAlphabet.vectorCount) := by
      intro ht; exact h ⟨ht.1,ht.2.1,hq⟩
    rw [ite_eq_right h,squareLegal_false hh]
    rfl
noncomputable def squareLegal (L R C I : Expr n) : Expr n :=
  choose (lt I (numeral PrefixAlphabet.vectorCount)) (squareLegalBody L R C I) (literal [false])
 theorem squareLegal_bit (L R C I : Expr n) (v : Env n) :
    (squareLegal L R C I).bit v=AffineAlphabet.squareLegal (L.number v) (R.number v) (C.number v) (I.number v) := by
  simp only [squareLegal,choose_bit,lt_bit,numeral_number,decide_eq_true_eq]
  split_ifs with hi
  · exact squareLegal_bit_bounded _ _ _ _ _ hi
  · rw [squareLegal_false (by tauto)]
    rfl
end VariableWL.AffineAlphabet.Program

namespace VariableWL.BlockDescriptor.Program.Listing
open Computation.Stack.PolyRecipe Computation.Stack.Recipe
 theorem eval_blocks {n : ℕ} (B : Listing n) (v : Env n) : (B.eval v).blocks=B.blocks.number v := rfl
 theorem eval_reads {n : ℕ} (B : Listing n) (v : Env n) : (B.eval v).reads=B.reads.number v := rfl
 theorem eval_validBlock {n : ℕ} (B : Listing n) (v : Env n) : (B.eval v).validBlock=(fun i=>B.validBlock.bit (cons (List.replicate i true) v)) := rfl
 theorem eval_validRead {n : ℕ} (B : Listing n) (v : Env n) : (B.eval v).validRead=(fun i=>B.validRead.bit (cons (List.replicate i true) v)) := rfl
end VariableWL.BlockDescriptor.Program.Listing
namespace VariableWL.AffineCatalog.Data
 theorem core_blocks_eq (D : Data) : D.core.blocks=D.toData.blocks := rfl
 theorem core_reads_eq (D : Data) : D.core.reads=D.toData.reads := rfl
 theorem core_validBlock_eq (D : Data) : D.core.validBlock=D.validBlock := rfl
 theorem core_validRead_eq (D : Data) : D.core.validRead=D.readValid := rfl
end VariableWL.AffineCatalog.Data
namespace VariableWL.BlockDescriptor.Core
theorem ext_fields {X Y : Core} (hb : X.blocks=Y.blocks) (hv : X.validBlock=Y.validBlock)
    (hr : X.reads=Y.reads) (hvr : X.validRead=Y.validRead) (hh : X.has=Y.has)
    (hd : X.dimension=Y.dimension) (hrd : X.readDimension=Y.readDimension)
    (hz : X.zeroOrder=Y.zeroOrder) (ho : X.readOrder=Y.readOrder) (hl : X.legal=Y.legal) : X=Y := by
  cases X; cases Y; simp_all
end VariableWL.BlockDescriptor.Core

end OAI
