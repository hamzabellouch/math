import OAI.Combinatorics.VariableWL.ProductImages

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10 uVariable11 uVariable12 uVariable13 uVariable14 uVariable15 uVariable16 uVariable17 uVariable18

namespace VariableWL.Blocks
open Subdivision
variable {r n : ℕ} {P : Type uVariable1} {E : Type uVariable2}

structure Horizontal (r n : ℕ) (P : Type uVariable3) (E : Type uVariable4) where
  row : Fin r
  type : Vertex P E n
  first : Bool
  last : Bool
  deriving DecidableEq

structure Vertical (r n : ℕ) (E : Type uVariable5) where
  row : Fin r
  link : Link E n
  label : Bool
  deriving DecidableEq

structure Square (r n : ℕ) (E : Type uVariable6) where
  row : Fin r
  link : Link E n
  first : Bool
  last : Bool
  deriving DecidableEq

abbrev Corner (r n : ℕ) (P : Type uVariable7) (E : Type uVariable8) := Fin r × Vertex P E n × Bool
abbrev Readout (r n : ℕ) (P : Type uVariable9) (E : Type uVariable10) := Horizontal r n P E ⊕ Vertical r n E
abbrev RawBlock (r n : ℕ) (P : Type uVariable11) (E : Type uVariable12) := Horizontal r n P E ⊕ Square r n E

variable (J : ProductImages.Instance r P E)

def matchOutput (l : Link E n) (i : Fin r) (a : Bool) : Bool :=
  if l.2.val = n then J.map l.1 i a else a

def ValidHorizontal (h : Horizontal r n P E) : Prop :=
  h.first ∈ J.labels h.type h.row ∧ h.last ∈ J.labels h.type (finRotate r h.row)

def ValidSquare (s : Square r n E) : Prop :=
  s.first ∈ J.domain s.link.1 s.row ∧ s.last ∈ J.domain s.link.1 (finRotate r s.row)

def Valid : RawBlock r n P E → Prop
  | .inl h => ValidHorizontal J h
  | .inr s => ValidSquare J s

abbrev Block := { b : RawBlock r n P E // Valid J b }

def row : RawBlock r n P E → Fin r
  | .inl h => h.row
  | .inr s => s.row

def squareLeft (s : Square r n E) : Horizontal r n P E :=
  ⟨s.row, left J.source s.link, s.first, s.last⟩

def squareRight (s : Square r n E) : Horizontal r n P E :=
  ⟨s.row, right J.target s.link, matchOutput J s.link s.row s.first,
    matchOutput J s.link (finRotate r s.row) s.last⟩

def squareBottom (s : Square r n E) : Vertical r n E := ⟨s.row, s.link, s.first⟩
def squareTop (s : Square r n E) : Vertical r n E := ⟨finRotate r s.row, s.link, s.last⟩

def HasReadout : RawBlock r n P E → Readout r n P E → Prop
  | .inl h, a => a = .inl h
  | .inr s, a => a = .inl (squareLeft J s) ∨ a = .inl (squareRight J s) ∨
      a = .inr (squareBottom s) ∨ a = .inr (squareTop s)

def end0 : Readout r n P E → Corner r n P E
  | .inl h => (h.row, h.type, h.first)
  | .inr v => (v.row, left J.source v.link, v.label)

def end1 : Readout r n P E → Corner r n P E
  | .inl h => (finRotate r h.row, h.type, h.last)
  | .inr v => (v.row, right J.target v.link, matchOutput J v.link v.row v.label)

theorem readout_ne (hr : 2 ≤ r) (hn : 0 < n) (a : Readout r n P E) :
    end0 J a ≠ end1 J a := by
  cases a with
  | inl h =>
    intro he
    exact Wrapping.finRotate_no_fixed hr h.row (congrArg Prod.fst he).symm
  | inr v =>
    intro he
    exact endpoints_ne hn J.source J.target v.link (congrArg (fun c => c.2.1) he)

def diagram (hr : 2 ≤ r) (hn : 0 < n) (U : Set (Block (n := n) J)) :
    SimpleGraph (Corner r n P E) where
  Adj v w := ∃ b ∈ U, ∃ a, HasReadout J b.val a ∧
    ((v = end0 J a ∧ w = end1 J a) ∨ (v = end1 J a ∧ w = end0 J a))
  symm := ⟨by
    rintro v w ⟨b,hb,a,ha,h⟩
    exact ⟨b,hb,a,ha,h.elim (fun h => Or.inr h.symm) (fun h => Or.inl h.symm)⟩⟩
  loopless := ⟨by
    rintro v ⟨b,hb,a,ha,h⟩
    exact readout_ne J hr hn a (h.elim (fun h => h.1.symm.trans h.2)
      (fun h => h.2.symm.trans h.1))⟩

theorem finRotate_twice_ne (hr : 3 ≤ r) (i : Fin r) : finRotate r (finRotate r i) ≠ i := by
  have : NeZero r := ⟨by omega⟩
  intro he
  have hh : (1 : Fin r) + 1 = 0 := by
    apply add_left_cancel (a := i)
    simpa only [finRotate_apply, add_assoc, add_zero] using he
  have hval := congrArg Fin.val hh
  have h1 : 1 % r = 1 := Nat.mod_eq_of_lt (by omega)
  have h2 : 2 % r = 2 := Nat.mod_eq_of_lt (by omega)
  norm_num [Fin.val_add, Fin.val_one, h1, h2] at hval

def horizontalTag (v w : Corner r n P E) : Option (Fin r) :=
  if w.1 = finRotate r v.1 then some v.1
  else if v.1 = finRotate r w.1 then some w.1 else none

theorem horizontalTag_readout (hr : 3 ≤ r) (a : Readout r n P E) :
    horizontalTag (end0 J a) (end1 J a) =
      (match a with | .inl h => some h.row | .inr _ => none) ∧
    horizontalTag (end1 J a) (end0 J a) =
      (match a with | .inl h => some h.row | .inr _ => none) := by
  cases a with
  | inl h =>
    dsimp only [horizontalTag, end0, end1]
    simp only [ite_eq_right (finRotate_twice_ne hr h.row).symm]
    exact ⟨rfl,rfl⟩
  | inr v =>
    have hne := (Wrapping.finRotate_no_fixed (by omega) v.row).symm
    dsimp only [horizontalTag, end0, end1]
    simp only [ite_eq_right hne, and_self]

def rowDiagram (hr : 3 ≤ r) (hn : 0 < n) (U : Set (Block (n := n) J)) :
    Wrapping.RowDiagram (diagram J (by omega) hn U) (finRotate r) where
  boundary := Prod.fst
  horizontal := horizontalTag
  symmetric := by
    rintro v w ⟨b,hb,a,ha,h⟩
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact (horizontalTag_readout J hr a).1.trans (horizontalTag_readout J hr a).2.symm
    · exact (horizontalTag_readout J hr a).2.trans (horizontalTag_readout J hr a).1.symm
  shape := by
    rintro v w ⟨b,hb,a,ha,h⟩
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · rw [(horizontalTag_readout J hr a).1]
      cases a with
      | inl h => exact Or.inl ⟨rfl,rfl⟩
      | inr v => rfl
    · rw [(horizontalTag_readout J hr a).2]
      cases a with
      | inl h => exact Or.inr ⟨rfl,rfl⟩
      | inr v => rfl

end VariableWL.Blocks

namespace VariableWL.Blocks
open Subdivision
variable {r n : ℕ} {P : Type uVariable13} {E : Type uVariable14} (J : ProductImages.Instance r P E)

def linksOf : RawBlock r n P E → Finset (Link E n)
  | .inl _ => ∅
  | .inr s => {s.link}

noncomputable def supportLinks (U : Finset (Block (n := n) J)) : Finset (Link E n) :=
  by classical exact U.biUnion (fun b => linksOf b.val)

theorem supportLinks_card (U : Finset (Block (n := n) J)) :
    (supportLinks J U).card ≤ U.card := by
  classical
  calc
    _ ≤ ∑ b ∈ U, (linksOf b.val).card := Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ U, 1 := Finset.sum_le_sum fun b _ => by
      cases b.val <;> simp [linksOf]
    _ = U.card := by simp

theorem square_link_mem (U : Finset (Block (n := n) J)) {b : Block (n := n) J}
    (hb : b ∈ U) {s : Square r n E} (hs : b.val = .inr s) :
    s.link ∈ supportLinks J U := by
  classical
  apply Finset.mem_biUnion.mpr
  exact ⟨b,hb,by simp [hs, linksOf]⟩

theorem hasReadout_horizontal_row {b : RawBlock r n P E} {h : Horizontal r n P E}
    (hh : HasReadout J b (.inl h)) : h.row = row b := by
  classical
  cases b with
  | inl h' => cases hh; rfl
  | inr s =>
    rcases hh with hh | hh | hh | hh
    · cases hh; rfl
    · cases hh; rfl
    · cases hh
    · cases hh

theorem hasReadout_vertical_link {b : RawBlock r n P E} {v : Vertical r n E}
    (hh : HasReadout J b (.inr v)) : v.link ∈ linksOf b := by
  classical
  cases b with
  | inl h => cases hh
  | inr s =>
    rcases hh with hh | hh | hh | hh
    · cases hh
    · cases hh
    · cases hh; simp [linksOf, squareBottom]
    · cases hh; simp [linksOf, squareTop]

theorem projection_adj (hr : 2 ≤ r) (hn : 0 < n) (U : Finset (Block (n := n) J))
    {v w : Corner r n P E} (h : (diagram J hr hn U).Adj v w) :
    v.2.1 = w.2.1 ∨ (supportGraph hn J.source J.target (supportLinks J U)).Adj v.2.1 w.2.1 := by
  classical
  obtain ⟨b,hb,a,ha,h⟩ := h
  have hv {a : Vertical r n E} (ha : HasReadout J b.val (.inr a)) :
      a.link ∈ supportLinks J U := Finset.mem_biUnion.mpr
        ⟨b,hb,hasReadout_vertical_link J ha⟩
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> cases a with
  | inl h => exact Or.inl rfl
  | inr v =>
    apply Or.inr
    first
    | exact ⟨v.link, hv ha, Or.inl ⟨rfl,rfl⟩⟩
    | exact ⟨v.link, hv ha, Or.inr ⟨rfl,rfl⟩⟩

theorem projection_reachable (hr : 2 ≤ r) (hn : 0 < n) (U : Finset (Block (n := n) J))
    {v w : Corner r n P E} (h : (diagram J hr hn U).Reachable v w) :
    (supportGraph hn J.source J.target (supportLinks J U)).Reachable v.2.1 w.2.1 := by
  classical
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons h p ih =>
    rcases projection_adj J hr hn U h with h | h
    · exact h ▸ ih
    · exact h.reachable.trans ih

theorem row_cover (hr : 3 ≤ r) (hn : 0 < n) (U : Finset (Block (n := n) J))
    {v w : Corner r n P E} (h : (diagram J (by omega) hn U).Adj v w)
    {i : Fin r} (hi : (rowDiagram J hr hn U).horizontal v w = some i) :
    i ∈ U.image (fun b => row b.val) := by
  classical
  obtain ⟨b,hb,a,ha,h⟩ := h
  have he : (Sum.elim (fun h => some h.row) (fun _ => none) a) = some i := by
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · have ht := (horizontalTag_readout J hr a).1.symm.trans hi
      cases a <;> exact ht
    · have ht := (horizontalTag_readout J hr a).2.symm.trans hi
      cases a <;> exact ht
  cases a with
  | inr v => cases he
  | inl h =>
    have he' := Option.some.inj he
    exact Finset.mem_image.mpr ⟨b,hb,(hasReadout_horizontal_row J ha).symm.trans he'⟩

theorem wrapping_card_ge (hr : 3 ≤ r) (hn : 0 < n) (U : Finset (Block (n := n) J))
    {marked : Fin r} (hw : (rowDiagram J hr hn U).Wraps marked) : r ≤ U.card := by
  classical
  have : NeZero r := ⟨by omega⟩
  simpa only [Fintype.card_fin] using (rowDiagram J hr hn U).blocks_card_ge U
    (fun b => row b.val) (fun _ _ h _ hi => row_cover J hr hn U h hi)
    Wrapping.RowDiagram.finRotate_orbit hw

theorem wrapping_row_injective (hr : 3 ≤ r) (hn : 0 < n) (U : Finset (Block (n := n) J))
    {marked : Fin r} (hw : (rowDiagram J hr hn U).Wraps marked) (hc : U.card = r) :
    Set.InjOn (fun b : Block (n := n) J => row b.val) (↑U : Set (Block (n := n) J)) := by
  classical
  have : NeZero r := ⟨by omega⟩
  exact (rowDiagram J hr hn U).row_injective U (fun b => row b.val)
    (fun _ _ h _ hi => row_cover J hr hn U h hi)
    Wrapping.RowDiagram.finRotate_orbit hw (by simpa only [Fintype.card_fin] using hc)

noncomputable def aligned (cut : E → Fin (n+1)) (v : Corner r n P E) : Bool :=
  J.alignment cut v.2.1 v.1 v.2.2

noncomputable def firstLabel (cut : E → Fin (n+1)) : RawBlock r n P E → Bool
  | .inl h => J.alignment cut h.type h.row h.first
  | .inr s => J.alignment cut (left J.source s.link) s.row s.first

noncomputable def lastLabel (cut : E → Fin (n+1)) : RawBlock r n P E → Bool
  | .inl h => J.alignment cut h.type (finRotate r h.row) h.last
  | .inr s => J.alignment cut (left J.source s.link) (finRotate r s.row) s.last

theorem square_alignment (hn : 0 < n) (cut : E → Fin (n+1))
    (s : Square r n E) (hs : ValidSquare J s) (hc : s.link.2 ≠ cut s.link.1) :
    aligned J cut (end0 J (.inl (squareRight J s))) = firstLabel J cut (.inr s) ∧
    aligned J cut (end1 J (.inl (squareRight J s))) = lastLabel J cut (.inr s) := by
  classical
  constructor
  · exact (J.alignment_match hn cut s.link hc s.row ⟨hs.1,rfl⟩).symm
  · exact (J.alignment_match hn cut s.link hc (finRotate r s.row) ⟨hs.2,rfl⟩).symm

theorem horizontal_labels (hn : 0 < n) (cut : E → Fin (n+1))
    (b : Block (n := n) J) (hc : ∀ l ∈ linksOf b.val, l.2 ≠ cut l.1)
    {h : Horizontal r n P E} (hh : HasReadout J b.val (.inl h)) :
    aligned J cut (end0 J (.inl h)) = firstLabel J cut b.val ∧
    aligned J cut (end1 J (.inl h)) = lastLabel J cut b.val := by
  classical
  obtain ⟨b,hb⟩ := b
  cases b with
  | inl h' => cases hh; exact ⟨rfl,rfl⟩
  | inr s =>
    rcases hh with hh | hh | hh | hh
    · cases hh; exact ⟨rfl,rfl⟩
    · cases hh; exact square_alignment J hn cut s hb (hc s.link (by simp [linksOf]))
    · cases hh
    · cases hh

theorem vertical_labels (hn : 0 < n) (cut : E → Fin (n+1))
    (b : Block (n := n) J) (hc : ∀ l ∈ linksOf b.val, l.2 ≠ cut l.1)
    {v : Vertical r n E} (hv : HasReadout J b.val (.inr v)) :
    aligned J cut (end0 J (.inr v)) = aligned J cut (end1 J (.inr v)) := by
  classical
  obtain ⟨b,hb⟩ := b
  cases b with
  | inl h => cases hv
  | inr s =>
    have hcut := hc s.link (by simp [linksOf])
    rcases hv with hv | hv | hv | hv
    · cases hv
    · cases hv
    · cases hv; exact J.alignment_match hn cut s.link hcut s.row ⟨hb.1,rfl⟩
    · cases hv; exact J.alignment_match hn cut s.link hcut (finRotate r s.row) ⟨hb.2,rfl⟩

end VariableWL.Blocks

namespace VariableWL.Blocks
open Subdivision
variable {r n : ℕ} {P : Type uVariable15} {E : Type uVariable16} (J : ProductImages.Instance r P E)

theorem recovered_address (hr : 3 ≤ r) (hn : 0 < n)
    (U : Finset (Block (n := n) J)) (cut : E → Fin (n+1))
    (hcut : ∀ l ∈ supportLinks J U, l.2 ≠ cut l.1)
    {marked : Fin r} (hw : (rowDiagram J hr hn U).Wraps marked) (hc : U.card = r) :
    ∃ a : Fin r → Bool, ∀ b ∈ U,
      firstLabel J cut b.val = a (row b.val) ∧
        lastLabel J cut b.val = a (finRotate r (row b.val)) := by
  classical
  have : NeZero r := ⟨by omega⟩
  have hrows := (rowDiagram J hr hn U).covers_rows U (fun b => row b.val)
    (fun _ _ h _ hi => row_cover J hr hn U h hi)
    Wrapping.RowDiagram.finRotate_orbit hw
  have hi := wrapping_row_injective J hr hn U hw hc
  choose chosen hat using fun i => Finset.mem_image.mp (hrows i)
  have hatmem (i) : chosen i ∈ U := (hat i).1
  have hatrow (i) : row (chosen i).val = i := (hat i).2
  have hateq (b : Block (n := n) J) (hb : b ∈ U) : chosen (row b.val) = b :=
    hi (hatmem _) hb (hatrow _)
  let first := fun i => firstLabel J cut (chosen i).val
  let last := fun i => lastLabel J cut (chosen i).val
  have hl : (rowDiagram J hr hn U).Labeled (aligned J cut) first last := by
    rintro v w ⟨b,hb,c,hc,h⟩
    have hc' : ∀ l ∈ linksOf b.val, l.2 ≠ cut l.1 := fun l hl =>
      hcut l (Finset.mem_biUnion.mpr ⟨b,hb,hl⟩)
    have hfirst : first (row b.val) = firstLabel J cut b.val := by
      dsimp only [first]; rw [hateq b hb]
    have hlast : last (row b.val) = lastLabel J cut b.val := by
      dsimp only [last]; rw [hateq b hb]
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · dsimp only [rowDiagram]
      rw [(horizontalTag_readout J hr c).1]
      cases c with
      | inl h =>
        have hrow := hasReadout_horizontal_row J hc
        obtain ⟨hf,hl⟩ := horizontal_labels J hn cut b hc' hc
        rw [← hrow] at hfirst hlast
        exact Or.inl ⟨Prod.ext rfl (hf.trans hfirst.symm),
          Prod.ext rfl (hl.trans hlast.symm)⟩
      | inr v => exact Prod.ext rfl (vertical_labels J hn cut b hc' hc)
    · dsimp only [rowDiagram]
      rw [(horizontalTag_readout J hr c).2]
      cases c with
      | inl h =>
        have hrow := hasReadout_horizontal_row J hc
        obtain ⟨hf,hl⟩ := horizontal_labels J hn cut b hc' hc
        rw [← hrow] at hfirst hlast
        exact Or.inr ⟨Prod.ext rfl (hf.trans hfirst.symm),
          Prod.ext rfl (hl.trans hlast.symm)⟩
      | inr v => exact Prod.ext rfl (vertical_labels J hn cut b hc' hc).symm
  have hcoherent := (rowDiagram J hr hn U).label_coherence (aligned J cut) first last
    hl Wrapping.RowDiagram.finRotate_orbit hw
  refine ⟨first, fun b hb => ⟨?_, ?_⟩⟩
  · dsimp only [first]; rw [hateq b hb]
  · rw [← hcoherent (row b.val)]
    dsimp only [last]; rw [hateq b hb]

end VariableWL.Blocks

namespace VariableWL.ProductImages.Instance
open VariableWL.Affine Subdivision
variable {r n : ℕ} {P : Type uVariable17} {E : Type uVariable18} (J : ProductImages.Instance r P E)

def AgreeAt (h g : J.Shifts n) : Vertex P E n → Prop
  | .inl p => h.1 p = g.1 p
  | .inr q => h.2 q = g.2 q

theorem shiftLeft_agree {h g : J.Shifts n} (l : Link E n)
    (ha : J.AgreeAt h g (left J.source l)) : J.shiftLeft h l = J.shiftLeft g l := by
  unfold left at ha
  unfold shiftLeft
  split_ifs at ha ⊢ with hl
  · exact congrArg (J.leftForm l.1) ha
  · exact ha

theorem shiftRight_agree {h g : J.Shifts n} (l : Link E n)
    (ha : J.AgreeAt h g (right J.target l)) : J.shiftRight h l = J.shiftRight g l := by
  unfold right at ha
  unfold shiftRight
  split_ifs at ha ⊢ with hr
  · exact congrArg (J.rightForm l.1) ha
  · exact ha

theorem shiftLeft_eq_internal (h : J.Shifts n) (l : Link E n) {q : E × Fin n}
    (hq : left J.source l = .inr q) : J.shiftLeft h l = h.2 q := by
  unfold left at hq
  split at hq
  · cases hq
  · rename_i hl
    simp only [shiftLeft, dite_eq_right hl, Sum.inr.inj hq]

theorem shiftRight_eq_internal (h : J.Shifts n) (l : Link E n) {q : E × Fin n}
    (hq : right J.target l = .inr q) : J.shiftRight h l = h.2 q := by
  unfold right at hq
  split at hq
  · cases hq
  · rename_i hr
    simp only [shiftRight, dite_eq_right hr, Sum.inr.inj hq]

theorem agree_adj (hn : 0 < n) (S : Set (Link E n)) {h g : J.Shifts n}
    (hh : J.ShiftSystem S h) (hg : J.ShiftSystem S g)
    {v w : Vertex P E n} (he : (supportGraph hn J.source J.target S).Adj v w)
    (hv : J.AgreeAt h g v) (hw : ∀ p, w = .inl p → h.1 p = g.1 p) :
    J.AgreeAt h g w := by
  cases w with
  | inl p => exact hw p rfl
  | inr q =>
    obtain ⟨l,hl,(⟨hvl,hwr⟩ | ⟨hvr,hwl⟩)⟩ := he
    · have ha := J.shiftLeft_agree l (hvl ▸ hv)
      have hb := (hh l hl).symm.trans (ha.trans (hg l hl))
      rw [J.shiftRight_eq_internal h l hwr.symm,
        J.shiftRight_eq_internal g l hwr.symm] at hb
      exact hb
    · have ha := J.shiftRight_agree l (hvr ▸ hv)
      have hb := (hh l hl).trans (ha.trans (hg l hl).symm)
      rw [J.shiftLeft_eq_internal h l hwl.symm,
        J.shiftLeft_eq_internal g l hwl.symm] at hb
      exact hb

theorem agree_reachable (hn : 0 < n) (S : Set (Link E n)) {h g : J.Shifts n}
    (hh : J.ShiftSystem S h) (hg : J.ShiftSystem S g) (root : Vertex P E n)
    (hroot : J.AgreeAt h g root)
    (hreals : ∀ p, (supportGraph hn J.source J.target S).Reachable root (.inl p) →
      h.1 p = g.1 p) {w : Vertex P E n}
    (hw : (supportGraph hn J.source J.target S).Reachable root w) : J.AgreeAt h g w := by
  obtain ⟨path⟩ := hw
  have walk_prop {v w : Vertex P E n} (p : (supportGraph hn J.source J.target S).Walk v w)
      (hv : J.AgreeAt h g v)
      (hr : (supportGraph hn J.source J.target S).Reachable root v) : J.AgreeAt h g w := by
    induction p with
    | nil => exact hv
    | @cons v u w h p ih =>
      have hu := hr.trans h.reachable
      exact ih (J.agree_adj hn S hh hg h hv (fun p he => hreals p (he ▸ hu))) hu
  exact walk_prop path hroot (.refl _)

end VariableWL.ProductImages.Instance

end OAI
