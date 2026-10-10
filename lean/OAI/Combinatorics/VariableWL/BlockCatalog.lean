import OAI.Combinatorics.VariableWL.BlockDescriptor

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6

namespace VariableWL.BlockDescriptor
open Blocks BlockCoordinates Descriptor VariableWL.Affine
attribute [local instance] Classical.propDecidable
variable {r n : ℕ} {P : Type uVariable1} {E : Type uVariable2} [Fintype P] [Fintype E]
variable (J : ProductImages.Instance r P E) (hr : 2≤r) (hn : 0<n) (marked : Fin r)
variable (PB : Presentation (Block (n := n) J)) (PR : Presentation (Readout r n P E))
variable (hDim : ∀b : Block (n := n) J,Fintype.card (Coordinate J b.val)≤6) (ε : Bit)

structure Good (D : Core) : Prop where
  blocks : D.blocks=PB.bound
  reads : D.reads=PR.bound
  validBlock : D.validBlock=PB.valid
  validRead : D.validRead=PR.valid
  has : ∀b a,D.has (PB.encode b) (PR.encode a)=true ↔ HasReadout J b.val a
  dimension : ∀b,D.dimension (PB.encode b)=Fintype.card (Coordinate J b.val)
  readDimension : ∀a,D.readDimension (PR.encode a)=readoutDimension J a
  zeroOrder : ∀b,D.zeroOrder (PB.encode b)=PrefixAlphabet.encodeOrder (hDim b) (Equiv.refl _)
  readOrder : ∀b a (ha : HasReadout J b.val a),D.readOrder (PB.encode b) (PR.encode a)=
    PrefixAlphabet.encodeOrder (hDim b) (exists_readout_order J hr hn ha).choose
  legal : ∀b i,D.legal (PB.encode b) i=true ↔ ∃z : Valuation J marked ε b,
    PrefixAlphabet.encode (hDim b) (BlockCoordinates.encode J b.val z.val)=i

variable {D : Core} (h : Good J hr hn marked PB PR hDim ε D)
@[instance_reducible] noncomputable def properNumberings : (b : Block (n := n) J) → FiniteNumbering (Proper J b) :=
  fun b=>(properPresentation J PB PR D.has h.has b).numbering

 omit [Fintype P] [Fintype E] in
 theorem proper_eq (b : Block (n := n) J) :
    D.proper (PB.encode b)=(properPresentation J PB PR D.has h.has b).valid := by
  funext i
  simp only [Core.proper,h.reads,h.validBlock,h.validRead,properPresentation_valid,ProperPredicate]
 include h in
 theorem channels_eq (b : Block (n := n) J) : D.channels (PB.encode b)=Fintype.card (Proper J b)+1 := by
  rw [Core.channels,proper_eq J hr hn marked PB PR hDim ε h]
  have he : D.properBound=(properPresentation J PB PR D.has h.has b).bound := by
    change D.blocks*D.reads=PB.bound*PR.bound
    rw [h.blocks,h.reads]
  rw [he,Presentation.count_eq_card]

 theorem select_number (b : Block (n := n) J) (p : Proper J b) :
    let _ : (b : Block (n := n) J) → FiniteNumbering (Proper J b) := properNumberings J hr hn marked PB PR hDim ε h
    D.select (PB.encode b) (properNumber J b p).val.val=PB.encode p.1.val*PR.bound+PR.encode p.2.val := by
  let _ : (b : Block (n := n) J) → FiniteNumbering (Proper J b) := properNumberings J hr hn marked PB PR hDim ε h
  dsimp only
  rw [Core.select,proper_eq J hr hn marked PB PR hDim ε h]
  change Descriptor.pick (D.blocks*D.reads) _ _=_
  rw [h.blocks,h.reads]
  exact properNumber_pick J PB PR D.has h.has b p

 theorem other_number (b : Block (n := n) J) (p : Proper J b) :
    let _ : (b : Block (n := n) J) → FiniteNumbering (Proper J b) := properNumberings J hr hn marked PB PR hDim ε h
    D.other (PB.encode b) (properNumber J b p).val.val=PB.encode p.1.val := by
  let _ : (b : Block (n := n) J) → FiniteNumbering (Proper J b) := properNumberings J hr hn marked PB PR hDim ε h
  dsimp only
  rw [Core.other,select_number J hr hn marked PB PR hDim ε h,h.reads]
  have ha := PR.encode_lt p.2.val
  exact PrefixDescriptor.Data.join_div _ _ _ (by omega) ha

 theorem readout_number (b : Block (n := n) J) (p : Proper J b) :
    let _ : (b : Block (n := n) J) → FiniteNumbering (Proper J b) := properNumberings J hr hn marked PB PR hDim ε h
    D.readout (PB.encode b) (properNumber J b p).val.val=PR.encode p.2.val := by
  let _ : (b : Block (n := n) J) → FiniteNumbering (Proper J b) := properNumberings J hr hn marked PB PR hDim ε h
  dsimp only
  rw [Core.readout,select_number J hr hn marked PB PR hDim ε h,h.reads]
  exact PrefixDescriptor.Data.join_mod _ _ _ (PR.encode_lt p.2.val)

 theorem prefix_good :
    let _ : (b : Block (n := n) J) → FiniteNumbering (Proper J b) := properNumberings J hr hn marked PB PR hDim ε h
    PrefixDescriptor.Good PB (data J hr hn marked) hDim ε D.toPrefix := by
  let _ : (b : Block (n := n) J) → FiniteNumbering (Proper J b) := properNumberings J hr hn marked PB PR hDim ε h
  dsimp only
  refine ⟨h.blocks,h.validBlock,D.channelBound_pos,?_,h.dimension,channels_eq J hr hn marked PB PR hDim ε h,?_,?_,?_⟩
  · intro b
    change Fintype.card (Proper J b)+1≤D.channelBound
    rw [←channels_eq J hr hn marked PB PR hDim ε h]
    exact D.channels_le _
  · intro b c
    change D.root (PB.encode b) c.val=channelRoot J b c
    by_cases hc : c.val=0
    · simp only [Core.root,ite_eq_left hc,channelRoot,dite_eq_left hc]
    · obtain ⟨p,hp⟩ := (properNumber J b).surjective ⟨c,hc⟩
      have hc' : (properNumber J b p).val=c := congrArg Subtype.val hp
      rw [←hc']
      change D.root (PB.encode b) (properNumber J b p).val.val=channelRoot J b (properNumber J b p).val
      rw [channelRoot_number,Core.root,ite_eq_right (properNumber J b p).property,
        readout_number J hr hn marked PB PR hDim ε h,h.readDimension]
  · intro b c
    change D.order (PB.encode b) c.val=PrefixAlphabet.encodeOrder (hDim b) (channelOrder J hr hn b c)
    by_cases hc : c.val=0
    · simp only [Core.order,ite_eq_left hc,channelOrder,dite_eq_left hc,h.zeroOrder]
    · obtain ⟨p,hp⟩ := (properNumber J b).surjective ⟨c,hc⟩
      have hc' : (properNumber J b p).val=c := congrArg Subtype.val hp
      rw [←hc']
      change D.order (PB.encode b) (properNumber J b p).val.val=
        PrefixAlphabet.encodeOrder (hDim b) (channelOrder J hr hn b (properNumber J b p).val)
      rw [channelOrder_number,Core.order,ite_eq_right (properNumber J b p).property,
        readout_number J hr hn marked PB PR hDim ε h,h.readOrder b p.2.val p.2.property.1]
  · intro b i
    constructor
    · intro hi
      obtain ⟨z,hz⟩ := (h.legal b i).mp hi
      exact ⟨valuationEquiv J hr hn marked b ε z,hz⟩
    · rintro ⟨z,hz⟩
      obtain ⟨y,rfl⟩ := (valuationEquiv J hr hn marked b ε).surjective z
      exact (h.legal b i).mpr ⟨y,hz⟩

 theorem matching_good :
    let _ : (b : Block (n := n) J) → FiniteNumbering (Proper J b) := properNumberings J hr hn marked PB PR hDim ε h
    PrefixDescriptor.MatchingGood PB (data J hr hn marked) D.toPrefix (wiring J hr hn marked) := by
  let _ : (b : Block (n := n) J) → FiniteNumbering (Proper J b) := properNumberings J hr hn marked PB PR hDim ε h
  dsimp only
  intro c d
  obtain ⟨⟨b,p⟩,rfl⟩ := (channelEquiv J hr hn marked).surjective c
  obtain ⟨⟨e,q⟩,rfl⟩ := (channelEquiv J hr hn marked).surjective d
  rw [mate_channel]
  have hp : (properNumber J b p).val.val<D.channelBound :=
    (properNumber J b p).val.isLt.trans_le (by rw [←channels_eq J hr hn marked PB PR hDim ε h]; exact D.channels_le _)
  have hq : (properNumber J e q).val.val<D.channelBound :=
    (properNumber J e q).val.isLt.trans_le (by rw [←channels_eq J hr hn marked PB PR hDim ε h]; exact D.channels_le _)
  change D.matching (PB.encode b*D.channelBound+(properNumber J b p).val.val)
    (PB.encode e*D.channelBound+(properNumber J e q).val.val)=true ↔ _
  simp only [Core.matching,PrefixDescriptor.Data.join_div _ _ _ D.channelBound_pos hp,
    PrefixDescriptor.Data.join_div _ _ _ D.channelBound_pos hq,
    PrefixDescriptor.Data.join_mod _ _ _ hp,PrefixDescriptor.Data.join_mod _ _ _ hq,
    other_number J hr hn marked PB PR hDim ε h,readout_number J hr hn marked PB PR hDim ε h,decide_eq_true_eq]
  rw [PB.encode_injective.eq_iff,PB.encode_injective.eq_iff,PR.encode_injective.eq_iff]
  rw [(channelEquiv J hr hn marked).injective.eq_iff]
  constructor
  · rintro ⟨he,hb,ha⟩
    subst e
    rcases q with ⟨⟨c,hc⟩,⟨a,haq⟩⟩
    dsimp only at hb ha
    subst c
    subst a
    rfl
  · intro he
    have he' := congrArg Sigma.fst he
    have hb' := congrArg (fun x : Σ b : Block (n := n) J,Proper J b=>x.2.1.val) he
    have ha' := congrArg (fun x : Σ b : Block (n := n) J,Proper J b=>x.2.2.val) he
    exact ⟨he',hb'.symm,ha'⟩
end VariableWL.BlockDescriptor

namespace VariableWL.Descriptor.Presentation
attribute [local instance] Classical.propDecidable
noncomputable def boolean : Presentation Bool :=
  ofEncoding 2 (fun _=>true) Bool.toNat (by intro b; cases b <;> decide) (fun _=>rfl)
    (by intro a b h; cases a <;> cases b <;> simp_all)
    (by intro i hi _; interval_cases i; exact ⟨false,rfl⟩; exact ⟨true,rfl⟩)
@[simp] theorem boolean_encode (b : Bool) : boolean.encode b=b.toNat := rfl
 theorem boolean_bound : boolean.bound=2 := rfl
 theorem boolean_valid (i : ℕ) : boolean.valid i=true := rfl
end VariableWL.Descriptor.Presentation

namespace VariableWL.BlockCatalog
open Blocks Subdivision Descriptor
attribute [local instance] Classical.propDecidable
variable {r n : ℕ} {P : Type uVariable3} {E : Type uVariable4}
variable (PP : Presentation P) (PE : Presentation E)
noncomputable def vertex : Presentation (Vertex P E n) := PP.sum (PE.product (Presentation.fin n))
noncomputable def link : Presentation (Link E n) := PE.product (Presentation.fin (n+1))

def horizontalEquiv : ((Fin r × Vertex P E n) × (Bool × Bool)) ≃ Horizontal r n P E where
  toFun a := ⟨a.1.1,a.1.2,a.2.1,a.2.2⟩
  invFun h := ((h.row,h.type),(h.first,h.last))
  left_inv _ := rfl
  right_inv _ := rfl

def squareEquiv : ((Fin r × Link E n) × (Bool × Bool)) ≃ Square r n E where
  toFun a := ⟨a.1.1,a.1.2,a.2.1,a.2.2⟩
  invFun h := ((h.row,h.link),(h.first,h.last))
  left_inv _ := rfl
  right_inv _ := rfl

def verticalEquiv : ((Fin r × Link E n) × Bool) ≃ Vertical r n E where
  toFun a := ⟨a.1.1,a.1.2,a.2⟩
  invFun h := ((h.row,h.link),h.label)
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def horizontal : Presentation (Horizontal r n P E) :=
  (((Presentation.fin r).product (vertex (n := n) PP PE)).product
    (Presentation.boolean.product Presentation.boolean)).transport horizontalEquiv
noncomputable def square : Presentation (Square r n E) :=
  (((Presentation.fin r).product (link (n := n) PE)).product
    (Presentation.boolean.product Presentation.boolean)).transport squareEquiv
noncomputable def vertical : Presentation (Vertical r n E) :=
  (((Presentation.fin r).product (link (n := n) PE)).product Presentation.boolean).transport verticalEquiv
noncomputable def raw : Presentation (RawBlock r n P E) := (horizontal PP PE).sum (square PE)
noncomputable def readout : Presentation (Readout r n P E) := (horizontal PP PE).sum (vertical PE)

 theorem horizontal_encode (h : Horizontal r n P E) :
    (horizontal PP PE).encode h=(h.row.val*(PP.bound+PE.bound*n)+(vertex PP PE).encode h.type)*4+
      h.first.toNat*2+h.last.toNat := by
  change (h.row.val*(PP.bound+PE.bound*n)+(vertex PP PE).encode h.type)*(2*2)+
    (h.first.toNat*2+h.last.toNat)=_
  omega
 theorem square_encode (s : Square r n E) :
    (square PE).encode s=(s.row.val*(PE.bound*(n+1))+(link PE).encode s.link)*4+
      s.first.toNat*2+s.last.toNat := by
  change (s.row.val*(PE.bound*(n+1))+(link PE).encode s.link)*(2*2)+
    (s.first.toNat*2+s.last.toNat)=_
  omega
 theorem vertical_encode (v : Vertical r n E) :
    (vertical PE).encode v=(v.row.val*(PE.bound*(n+1))+(link PE).encode v.link)*2+v.label.toNat := rfl
 theorem vertex_inl (p : P) : (vertex (n := n) PP PE).encode (.inl p)=PP.encode p := rfl
 theorem vertex_inr (e : E) (j : Fin n) :
    (vertex PP PE).encode (.inr (e,j))=PP.bound+PE.encode e*n+j.val := by
  change PP.bound+(PE.encode e*n+j.val)=_; omega
 theorem link_encode (e : E) (j : Fin (n+1)) : (link PE).encode (e,j)=PE.encode e*(n+1)+j.val := rfl

structure Data where
  rows : ℕ
  internal : ℕ
  reals : ℕ
  comparisons : ℕ
  validReal : ℕ → Bool
  validComparison : ℕ → Bool
  source : ℕ → ℕ
  target : ℕ → ℕ
  domain : ℕ → ℕ → ℕ → Bool
  map : ℕ → ℕ → ℕ → ℕ

namespace Data
variable (D : Data)
def vertices : ℕ := D.reals+D.comparisons*D.internal
def links : ℕ := D.comparisons*(D.internal+1)
def horizontals : ℕ := D.rows*D.vertices*4
def squares : ℕ := D.rows*D.links*4
def verticals : ℕ := D.rows*D.links*2
def blocks : ℕ := D.horizontals+D.squares
def reads : ℕ := D.horizontals+D.verticals
def validVertex (i : ℕ) : Bool := if i<D.reals then D.validReal i else D.validComparison ((i-D.reals)/D.internal)
def validLink (i : ℕ) : Bool := D.validComparison (i/(D.internal+1))
def validH (i : ℕ) : Bool := D.validVertex (i/4%D.vertices)
def validS (i : ℕ) : Bool := D.validLink (i/4%D.links)
def validV (i : ℕ) : Bool := D.validLink (i/2%D.links)
def rawValid (i : ℕ) : Bool := if i<D.horizontals then D.validH i else D.validS (i-D.horizontals)
def readValid (i : ℕ) : Bool := if i<D.horizontals then D.validH i else D.validV (i-D.horizontals)
def hrow (i : ℕ) : ℕ := i/4/D.vertices
def htype (i : ℕ) : ℕ := i/4%D.vertices
def srow (i : ℕ) : ℕ := i/4/D.links
def slink (i : ℕ) : ℕ := i/4%D.links
def first (i : ℕ) : ℕ := i%4/2
def last (i : ℕ) : ℕ := i%2
def next (i : ℕ) : ℕ := (i+1)%D.rows
def labels (t i a : ℕ) : Bool := if t<D.reals then true else D.domain ((t-D.reals)/D.internal) i a
def horizontalValid (i : ℕ) : Bool := D.labels (D.htype i) (D.hrow i) (first i) && D.labels (D.htype i) (D.next (D.hrow i)) (last i)
def squareValid (i : ℕ) : Bool := D.domain (D.slink i/(D.internal+1)) (D.srow i) (first i) &&
  D.domain (D.slink i/(D.internal+1)) (D.next (D.srow i)) (last i)
def validBlock (i : ℕ) : Bool := D.rawValid i &&
  (if i<D.horizontals then D.horizontalValid i else D.squareValid (i-D.horizontals))
def left (l : ℕ) : ℕ := if l%(D.internal+1)=0 then D.source (l/(D.internal+1)) else
  D.reals+(l/(D.internal+1))*D.internal+(l%(D.internal+1)-1)
def right (l : ℕ) : ℕ := if l%(D.internal+1)=D.internal then D.target (l/(D.internal+1)) else
  D.reals+(l/(D.internal+1))*D.internal+l%(D.internal+1)
def output (l i a : ℕ) : ℕ := if l%(D.internal+1)=D.internal then D.map (l/(D.internal+1)) i a else a
def horizontalCode (i t a b : ℕ) : ℕ := (i*D.vertices+t)*4+a*2+b
def verticalCode (i l a : ℕ) : ℕ := D.horizontals+(i*D.links+l)*2+a
def squareLeft (s : ℕ) : ℕ := D.horizontalCode (D.srow s) (D.left (D.slink s)) (first s) (last s)
def squareRight (s : ℕ) : ℕ := D.horizontalCode (D.srow s) (D.right (D.slink s))
  (D.output (D.slink s) (D.srow s) (first s)) (D.output (D.slink s) (D.next (D.srow s)) (last s))
def squareBottom (s : ℕ) : ℕ := D.verticalCode (D.srow s) (D.slink s) (first s)
def squareTop (s : ℕ) : ℕ := D.verticalCode (D.next (D.srow s)) (D.slink s) (last s)
def has (b a : ℕ) : Bool := if b<D.horizontals then decide (a=b) else
  let s:=b-D.horizontals
  decide (a=D.squareLeft s ∨ a=D.squareRight s ∨ a=D.squareBottom s ∨ a=D.squareTop s)
end Data

structure Good (J : ProductImages.Instance r P E) (D : Data) : Prop where
  rows : D.rows=r
  internal : D.internal=n
  reals : D.reals=PP.bound
  comparisons : D.comparisons=PE.bound
  validReal : D.validReal=PP.valid
  validComparison : D.validComparison=PE.valid
  source : ∀e,D.source (PE.encode e)=PP.encode (J.source e)
  target : ∀e,D.target (PE.encode e)=PP.encode (J.target e)
  domain : ∀e i a,D.domain (PE.encode e) i.val a.toNat=true ↔ a ∈ J.domain e i
  map : ∀e i a,D.map (PE.encode e) i.val a.toNat=(J.map e i a).toNat
end VariableWL.BlockCatalog

namespace VariableWL.BlockCatalog
open Blocks Subdivision Descriptor
attribute [local instance] Classical.propDecidable
variable {r n : ℕ} {P : Type uVariable5} {E : Type uVariable6}
variable (PP : Presentation P) (PE : Presentation E) (J : ProductImages.Instance r P E)
variable {D : Data} (h : Good (n := n) PP PE J D)
include h

 theorem vertices_eq : D.vertices=(vertex (n := n) PP PE).bound := by
  change D.reals+D.comparisons*D.internal=PP.bound+PE.bound*n
  rw [h.reals,h.comparisons,h.internal]
 theorem links_eq : D.links=(link (n := n) PE).bound := by
  change D.comparisons*(D.internal+1)=PE.bound*(n+1)
  rw [h.comparisons,h.internal]
 theorem horizontals_eq : D.horizontals=(horizontal (r := r) (n := n) PP PE).bound := by
  change D.rows*D.vertices*4=r*(PP.bound+PE.bound*n)*(2*2)
  rw [h.rows,vertices_eq PP PE J h]
  rfl
 theorem squares_eq : D.squares=(square (r := r) (n := n) PE).bound := by
  change D.rows*D.links*4=r*(PE.bound*(n+1))*(2*2)
  rw [h.rows,links_eq PP PE J h]
  rfl
 theorem verticals_eq : D.verticals=(vertical (r := r) (n := n) PE).bound := by
  change D.rows*D.links*2=r*(PE.bound*(n+1))*2
  rw [h.rows,links_eq PP PE J h]
  rfl
 theorem blocks_eq : D.blocks=(raw (r := r) (n := n) PP PE).bound := by
  change D.horizontals+D.squares=_
  rw [horizontals_eq PP PE J h,squares_eq PP PE J h]
  rfl
 theorem reads_eq : D.reads=(readout (r := r) (n := n) PP PE).bound := by
  change D.horizontals+D.verticals=_
  rw [horizontals_eq PP PE J h,verticals_eq PP PE J h]
  rfl

 theorem validVertex_eq : D.validVertex=(vertex (n := n) PP PE).valid := by
  funext i
  change (if i<D.reals then D.validReal i else D.validComparison ((i-D.reals)/D.internal))=
    (if i<PP.bound then PP.valid i else (PE.valid ((i-PP.bound)/n) && true))
  simp only [h.reals,h.validReal,h.validComparison,h.internal,Bool.and_true]
 theorem validLink_eq : D.validLink=(link (n := n) PE).valid := by
  funext i
  change D.validComparison (i/(D.internal+1))= (PE.valid (i/(n+1)) && true)
  simp only [h.validComparison,h.internal,Bool.and_true]
 theorem validH_eq : D.validH=(horizontal (r := r) (n := n) PP PE).valid := by
  funext i
  change D.validVertex (i/4%D.vertices)=
    ((true && (vertex PP PE).valid (i/4%(vertex (n := n) PP PE).bound)) && (true && true))
  simp only [validVertex_eq PP PE J h,vertices_eq PP PE J h,Bool.true_and,Bool.and_true]
 theorem validS_eq : D.validS=(square (r := r) (n := n) PE).valid := by
  funext i
  change D.validLink (i/4%D.links)=
    ((true && (link PE).valid (i/4%(link (n := n) PE).bound)) && (true && true))
  simp only [validLink_eq PP PE J h,links_eq PP PE J h,Bool.true_and,Bool.and_true]
 theorem validV_eq : D.validV=(vertical (r := r) (n := n) PE).valid := by
  funext i
  change D.validLink (i/2%D.links)=
    ((true && (link PE).valid (i/2%(link (n := n) PE).bound)) && true)
  simp only [validLink_eq PP PE J h,links_eq PP PE J h,Bool.true_and,Bool.and_true]
 theorem rawValid_eq : D.rawValid=(raw (r := r) (n := n) PP PE).valid := by
  funext i
  change (if i<D.horizontals then D.validH i else D.validS (i-D.horizontals))=_
  simp only [horizontals_eq PP PE J h,validH_eq PP PE J h,validS_eq PP PE J h]
  rfl
 theorem readValid_eq : D.readValid=(readout (r := r) (n := n) PP PE).valid := by
  funext i
  change (if i<D.horizontals then D.validH i else D.validV (i-D.horizontals))=_
  simp only [horizontals_eq PP PE J h,validH_eq PP PE J h,validV_eq PP PE J h]
  rfl

 omit h in
 theorem boolPair_lt (a b : Bool) : a.toNat*2+b.toNat<4 := by cases a <;> cases b <;> decide
 omit h in
 theorem boolPair_first (a b : Bool) : (a.toNat*2+b.toNat)/2=a.toNat := by cases a <;> cases b <;> decide
 omit h in
 theorem boolPair_last (a b : Bool) : (a.toNat*2+b.toNat)%2=b.toNat := by cases a <;> cases b <;> decide
 omit h in
 theorem packed_div (q : ℕ) (a b : Bool) : (q*4+a.toNat*2+b.toNat)/4=q := by
  rw [Nat.add_assoc]
  exact PrefixDescriptor.Data.join_div _ _ _ (by decide) (boolPair_lt a b)
 omit h in
 theorem packed_first (q : ℕ) (a b : Bool) : Data.first (q*4+a.toNat*2+b.toNat)=a.toNat := by
  unfold Data.first
  rw [Nat.add_assoc,PrefixDescriptor.Data.join_mod _ _ _ (boolPair_lt a b),boolPair_first]
 omit h in
 theorem packed_last (q : ℕ) (a b : Bool) : Data.last (q*4+a.toNat*2+b.toNat)=b.toNat := by
  unfold Data.last
  cases a <;> cases b <;> simp only [Bool.toNat_false,Bool.toNat_true] <;> omega

 theorem horizontal_parts (x : Horizontal r n P E) :
    D.hrow ((horizontal PP PE).encode x)=x.row.val ∧
    D.htype ((horizontal PP PE).encode x)=(vertex PP PE).encode x.type ∧
    Data.first ((horizontal PP PE).encode x)=x.first.toNat ∧
    Data.last ((horizontal PP PE).encode x)=x.last.toNat := by
  have hx := (vertex (n := n) PP PE).encode_lt x.type
  have hv := vertices_eq PP PE J h
  have hp : 0<(vertex (n := n) PP PE).bound := by omega
  simp only [horizontal_encode,Data.hrow,Data.htype,packed_div,packed_first,packed_last,hv]
  change (x.row.val*(vertex (n := n) PP PE).bound+(vertex PP PE).encode x.type)/(vertex PP PE).bound=x.row.val ∧
    (x.row.val*(vertex (n := n) PP PE).bound+(vertex PP PE).encode x.type)%(vertex PP PE).bound=_ ∧ _
  simp only [PrefixDescriptor.Data.join_div _ _ _ hp hx,PrefixDescriptor.Data.join_mod _ _ _ hx,and_self]

 theorem square_parts (x : Square r n E) :
    D.srow ((square PE).encode x)=x.row.val ∧ D.slink ((square PE).encode x)=(link PE).encode x.link ∧
    Data.first ((square PE).encode x)=x.first.toNat ∧ Data.last ((square PE).encode x)=x.last.toNat := by
  have hx := (link (n := n) PE).encode_lt x.link
  have hv := links_eq PP PE J h
  have hp : 0<(link (n := n) PE).bound := by omega
  simp only [square_encode,Data.srow,Data.slink,packed_div,packed_first,packed_last,hv]
  change (x.row.val*(link (n := n) PE).bound+(link PE).encode x.link)/(link PE).bound=x.row.val ∧
    (x.row.val*(link (n := n) PE).bound+(link PE).encode x.link)%(link PE).bound=_ ∧ _
  simp only [PrefixDescriptor.Data.join_div _ _ _ hp hx,PrefixDescriptor.Data.join_mod _ _ _ hx,and_self]

 theorem next_eq (i : Fin r) : D.next i.val=(finRotate r i).val := by
  have : NeZero r := i.neZero
  rw [Data.next,h.rows,finRotate_apply,Fin.val_add]
  simp only [Fin.val_one',Nat.add_mod_mod]

 theorem labels_code (t : Vertex P E n) (i : Fin r) (a : Bool) :
    D.labels ((vertex PP PE).encode t) i.val a.toNat=true ↔ a ∈ J.labels t i := by
  cases t with
  | inl p => simp only [Data.labels,vertex_inl,h.reals,ite_eq_left (PP.encode_lt p),ProductImages.Instance.labels,Finset.mem_univ]
  | inr q =>
    rcases q with ⟨e,j⟩
    simp only [Data.labels,vertex_inr,h.reals,not_lt.mpr (by omega : PP.bound≤PP.bound+PE.encode e*n+j.val),ite_false]
    have he : PP.bound+PE.encode e*n+j.val-PP.bound=PE.encode e*n+j.val := by omega
    rw [he,h.internal,PrefixDescriptor.Data.join_div _ _ _ (by omega : 0<n) j.isLt]
    exact h.domain e i a

 theorem horizontal_valid (x : Horizontal r n P E) :
    D.horizontalValid ((horizontal PP PE).encode x)=true ↔ ValidHorizontal J x := by
  obtain ⟨hrw,ht,hf,hl⟩ := horizontal_parts PP PE J h x
  rw [Data.horizontalValid,hrw,ht,hf,hl,next_eq PP PE J h,Bool.and_eq_true]
  exact and_congr (labels_code PP PE J h x.type x.row x.first)
    (labels_code PP PE J h x.type (finRotate r x.row) x.last)

 theorem square_valid (x : Square r n E) :
    D.squareValid ((square PE).encode x)=true ↔ ValidSquare J x := by
  obtain ⟨hrw,ht,hf,hl⟩ := square_parts PP PE J h x
  rw [Data.squareValid,hrw,ht,hf,hl,next_eq PP PE J h,h.internal,link_encode,
    PrefixDescriptor.Data.join_div _ _ _ (by omega : 0<n+1) x.link.2.isLt,Bool.and_eq_true]
  exact and_congr (h.domain x.link.1 x.row x.first) (h.domain x.link.1 (finRotate r x.row) x.last)

 theorem block_predicate (b : RawBlock r n P E) :
    (if (raw PP PE).encode b<D.horizontals then D.horizontalValid ((raw PP PE).encode b)
      else D.squareValid ((raw PP PE).encode b-D.horizontals))=true ↔ Valid J b := by
  cases b with
  | inl x =>
    change (if (horizontal PP PE).encode x<D.horizontals then _ else _)=true ↔ _
    rw [ite_eq_left (by rw [horizontals_eq PP PE J h]; exact (horizontal PP PE).encode_lt x)]
    exact horizontal_valid PP PE J h x
  | inr x =>
    change (if (horizontal PP PE).bound+(square PE).encode x<D.horizontals then _ else _)=true ↔ _
    rw [horizontals_eq PP PE J h,ite_eq_right (by omega)]
    change D.squareValid ((horizontal PP PE).bound+(square PE).encode x-(horizontal PP PE).bound)=true ↔ _
    rw [Nat.add_sub_cancel_left]
    exact square_valid PP PE J h x

noncomputable def block : Presentation (Block (n := n) J) :=
  (raw PP PE).filter (fun i=>if i<D.horizontals then D.horizontalValid i else D.squareValid (i-D.horizontals))
    (Valid J) (block_predicate PP PE J h)
 theorem block_encode (b : Block (n := n) J) : (block PP PE J h).encode b=(raw PP PE).encode b.val := rfl
 theorem block_bound : (block PP PE J h).bound=D.blocks := (blocks_eq PP PE J h).symm
 theorem block_valid : (block PP PE J h).valid=D.validBlock := by
  funext i
  change ((raw PP PE).valid i && _) = (D.rawValid i && _)
  rw [rawValid_eq PP PE J h]

 theorem left_code (l : Link E n) : D.left ((link PE).encode l)=(vertex PP PE).encode (Subdivision.left J.source l) := by
  rcases l with ⟨e,j⟩
  have hj := j.isLt
  simp only [Data.left,h.internal,link_encode,PrefixDescriptor.Data.join_div _ _ _ (by omega : 0<n+1) hj,
    PrefixDescriptor.Data.join_mod _ _ _ hj]
  by_cases hz : j.val=0
  · rw [ite_eq_left hz,Subdivision.left,dite_eq_left hz,vertex_inl,h.source]
  · rw [ite_eq_right hz,Subdivision.left,dite_eq_right hz,vertex_inr,h.reals]

 theorem right_code (l : Link E n) : D.right ((link PE).encode l)=(vertex PP PE).encode (Subdivision.right J.target l) := by
  rcases l with ⟨e,j⟩
  have hj := j.isLt
  simp only [Data.right,h.internal,link_encode,PrefixDescriptor.Data.join_div _ _ _ (by omega : 0<n+1) hj,
    PrefixDescriptor.Data.join_mod _ _ _ hj]
  by_cases hz : j.val=n
  · rw [ite_eq_left hz,Subdivision.right,dite_eq_left hz,vertex_inl,h.target]
  · rw [ite_eq_right hz,Subdivision.right,dite_eq_right hz,vertex_inr,h.reals]

 theorem output_code (l : Link E n) (i : Fin r) (a : Bool) :
    D.output ((link PE).encode l) i.val a.toNat=(matchOutput J l i a).toNat := by
  rcases l with ⟨e,j⟩
  have hj := j.isLt
  simp only [Data.output,h.internal,link_encode,PrefixDescriptor.Data.join_div _ _ _ (by omega : 0<n+1) hj,
    PrefixDescriptor.Data.join_mod _ _ _ hj,matchOutput]
  split_ifs <;> first | exact h.map e i a | rfl

 theorem horizontalCode_eq (x : Horizontal r n P E) :
    D.horizontalCode x.row.val ((vertex PP PE).encode x.type) x.first.toNat x.last.toNat=(horizontal PP PE).encode x := by
  rw [Data.horizontalCode,horizontal_encode,vertices_eq PP PE J h]
  rfl
 theorem verticalCode_eq (x : Vertical r n E) :
    D.verticalCode x.row.val ((link PE).encode x.link) x.label.toNat=(readout PP PE).encode (.inr x) := by
  rw [Data.verticalCode,links_eq PP PE J h,horizontals_eq PP PE J h]
  change _=(horizontal PP PE).bound+((x.row.val*(link (n := n) PE).bound+(link PE).encode x.link)*2+x.label.toNat)
  omega
 theorem square_faces (s : Square r n E) :
    D.squareLeft ((square PE).encode s)=(readout PP PE).encode (.inl (Blocks.squareLeft J s)) ∧
    D.squareRight ((square PE).encode s)=(readout PP PE).encode (.inl (Blocks.squareRight J s)) ∧
    D.squareBottom ((square PE).encode s)=(readout PP PE).encode (.inr (Blocks.squareBottom s)) ∧
    D.squareTop ((square PE).encode s)=(readout PP PE).encode (.inr (Blocks.squareTop s)) := by
  obtain ⟨hrw,ht,hf,hl⟩ := square_parts PP PE J h s
  simp only [Data.squareLeft,Data.squareRight,Data.squareBottom,Data.squareTop,hrw,ht,hf,hl,
    next_eq PP PE J h,left_code PP PE J h,right_code PP PE J h,output_code PP PE J h]
  exact ⟨horizontalCode_eq PP PE J h (Blocks.squareLeft J s),
    horizontalCode_eq PP PE J h (Blocks.squareRight J s),
    verticalCode_eq PP PE J h (Blocks.squareBottom s),verticalCode_eq PP PE J h (Blocks.squareTop s)⟩

 theorem has_code (b : Block (n := n) J) (a : Readout r n P E) :
    D.has ((block PP PE J h).encode b) ((readout PP PE).encode a)=true ↔ HasReadout J b.val a := by
  rw [block_encode,Data.has]
  cases he : b.val with
  | inl x =>
    change (if (horizontal PP PE).encode x<D.horizontals then _ else _)=true ↔ _
    rw [ite_eq_left (by rw [horizontals_eq PP PE J h]; exact (horizontal PP PE).encode_lt x),decide_eq_true_eq]
    change (readout PP PE).encode a=(readout PP PE).encode (.inl x) ↔ a=.inl x
    exact (readout PP PE).encode_injective.eq_iff
  | inr s =>
    change (if (horizontal PP PE).bound+(square PE).encode s<D.horizontals then _ else _)=true ↔ _
    rw [horizontals_eq PP PE J h,ite_eq_right (by omega)]
    have hs : (raw PP PE).encode (.inr s)-(horizontal (r := r) (n := n) PP PE).bound=(square PE).encode s := by
      change (horizontal PP PE).bound+(square PE).encode s-(horizontal PP PE).bound=_
      omega
    dsimp only
    rw [hs]
    obtain ⟨hl,hr,hb,ht⟩ := square_faces PP PE J h s
    simp only [hl,hr,hb,ht,decide_eq_true_eq,(readout PP PE).encode_injective.eq_iff,HasReadout]
end VariableWL.BlockCatalog

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}
def underThree (P : Expr (n+3)) : Expr (n+4) :=
  P.reindex (Fin.cons 0 (Fin.cons 1 (Fin.cons 2 (fun i=>i.succ.succ.succ.succ))))
theorem underThree_value (P : Expr (n+3)) (v : Env n) (a b c d : Word) :
    (underThree P).value (cons a (cons b (cons c (cons d v))))=P.value (cons a (cons b (cons c v))) := by
  apply congrArg P.program.value
  funext i
  exact Fin.cases rfl (fun i=>Fin.cases rfl (fun i=>Fin.cases rfl (fun _=>rfl) i) i) i
theorem underThree_number (P : Expr (n+3)) (v : Env n) (a b c d : Word) :
    (underThree P).number (cons a (cons b (cons c (cons d v))))=P.number (cons a (cons b (cons c v))) := by
  unfold Expr.number
  rw [underThree_value]
theorem underThree_bit (P : Expr (n+3)) (v : Env n) (a b c d : Word) :
    (underThree P).bit (cons a (cons b (cons c (cons d v))))=P.bit (cons a (cons b (cons c v))) := by
  unfold Expr.bit
  rw [underThree_value]
end VariableWL.Computation.Stack.PolyRecipe

end OAI
