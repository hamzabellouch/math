import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.PortPatches
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Order.ModularLattice

namespace OAI

noncomputable section
open scoped Classical Matrix

namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
open scoped Classical
variable {F : Type}

theorem equivalence_chain (parent : F) {m n : ℕ} (e : Fin m ≃ Fin n)
    (f : Fin m → F) : Nonempty (OrderedChain parent (List.ofFn f)
      (List.ofFn (f ∘ e.symm))) := by
  have h : m=n := by simpa using Fintype.card_congr e
  subst n
  exact permutation_chain parent e f

lemma matrix_list {m n : ℕ} (f : Fin m → Fin n → F) :
    List.ofFn (fun k : Fin (m*n) =>
      f (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)=
      (List.ofFn fun i => List.ofFn (f i)).flatten := by
  rw [List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have h : (⟨i.val*n+j.val,by nlinarith [Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt), j.isLt]⟩ : Fin (m*n))=finProdFinEquiv (i,j) := by
    apply Fin.ext
    change i.val*n+j.val=j.val+n*i.val
    ac_rfl
  rw [h,Equiv.symm_apply_apply]

/-- The row/column enumeration of the same intersection blocks. -/
def gridTranspose (m n : ℕ) : Fin (m*n) ≃ Fin (n*m) :=
  finProdFinEquiv.symm.trans ((Equiv.prodComm _ _).trans finProdFinEquiv)

lemma gridTranspose_colors {m n : ℕ} (f : Fin m → Fin n → F) :
    (fun k : Fin (m*n) => f (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2) ∘
      (gridTranspose m n).symm =
      (fun k : Fin (n*m) => f (finProdFinEquiv.symm k).2 (finProdFinEquiv.symm k).1) := by
  funext k
  change f (finProdFinEquiv.symm (finProdFinEquiv
    ((finProdFinEquiv.symm k).2,(finProdFinEquiv.symm k).1))).1
      (finProdFinEquiv.symm (finProdFinEquiv
    ((finProdFinEquiv.symm k).2,(finProdFinEquiv.symm k).1))).2 = _
  rw [Equiv.symm_apply_apply]

/-- Row-by-row to column-by-column uses only adjacent vertices. -/
theorem rectangular_permutation (parent : F) {m n : ℕ} (f : Fin m → Fin n → F) :
    Nonempty (OrderedChain parent ((List.ofFn fun i => List.ofFn (f i)).flatten)
      ((List.ofFn fun j => List.ofFn fun i => f i j).flatten)) := by
  have h := equivalence_chain parent (gridTranspose m n)
    (fun k => f (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
  rw [gridTranspose_colors,matrix_list] at h
  have hc := matrix_list (fun j i => f i j)
  exact hc ▸ h

/-- The finite band recipe for the band reduction: split every old left grade into its common intersection pieces, interchange adjacent pieces, then coarsen into all right grades. Every split/merge branch is retained by OrderedStep.kind. -/
theorem two_flag_gallery (parent : F) {m n : ℕ} (row : Fin m → F) (col : Fin n → F)
    (grid : Fin m → Fin n → F) :
    Nonempty (OrderedChain parent (List.ofFn row) (List.ofFn col)) := by
  have hr := (refine_rows parent (List.ofFn fun i => (row i,List.ofFn (grid i))) [] []).1
  have hc := (refine_rows parent (List.ofFn fun j => (col j,List.ofFn fun i => grid i j)) [] []).2
  simp only [List.nil_append,List.append_nil,List.flatMap_def,List.map_ofFn] at hr hc
  obtain ⟨p⟩ := hr
  obtain ⟨q⟩ := rectangular_permutation parent grid
  obtain ⟨r⟩ := hc
  exact ⟨p.trans (q.trans r)⟩

end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
open scoped Classical
variable {F : Type}

/-- Finite sequence of states and vertex tables. States do not impose extra conditions on solutions: they are the ordered facet names computed by the split/permutation/merge recipe. -/
structure OrderedWalk (parent : F) (a b : List F) where
  length : ℕ
  state : Fin (length+1) → List F
  vertex : (i : Fin length) → OrderedStep parent (state i.castSucc) (state i.succ)
  first : state 0=a
  last : state (Fin.last length)=b

namespace OrderedWalk
variable {parent : F} {a b c : List F}
def refl (a : List F) : OrderedWalk parent a a where
  length := 0
  state _ := a
  vertex i := Fin.elim0 i
  first := rfl
  last := rfl

def cons (s : OrderedStep parent a b) (w : OrderedWalk parent b c) :
    OrderedWalk parent a c where
  length := w.length+1
  state := Fin.cases a w.state
  vertex := Fin.cases
    (by change OrderedStep parent a (w.state 0); rw [w.first]; exact s)
    (fun j => by simpa using w.vertex j)
  first := rfl
  last := by change w.state (Fin.last w.length)=c; exact w.last
end OrderedWalk

namespace OrderedChain
variable {parent : F}
def walk : {a b : List F} → OrderedChain parent a b → OrderedWalk parent a b
  | _,_,.refl a => .refl a
  | _,_,.step s p => (walk p).cons s
end OrderedChain

lemma children_ext {k h : Kind} (d : Decoration k F) (e : Decoration h F)
    (p : k.table.Port) (q : h.table.Port) (he : d.children p=e.children q)
    (hc : k.arity p=h.arity q) (i : Fin (k.arity p)) :
    d.portColor p (some i)=e.portColor q (some (finCongr hc i)) := by
  have hh := congrArg (fun l : List F => l[i.val]?) he
  have hiq : i.val<h.arity q := hc ▸ i.isLt
  simp only [Decoration.children,List.getElem?_ofFn,dite_eq_left i.isLt,dite_eq_left hiq] at hh
  exact Option.some.inj hh

end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
open scoped Classical
variable {F : Type}

/-- Entire finite band, including all split branch ports. The exposed ports are the complement of the internal sewing, not chosen subsets. -/
structure RealizedBand (parent : F) (a b : List F) where
  length : ℕ
  kind : Fin (length+1) → Kind
  decoration : (v : Fin (length+1)) → Decoration (kind v) F
  arity_match : ∀ j : Fin length, (kind j.castSucc).arity (kind j.castSucc).output=
    (kind j.succ).arity (kind j.succ).input
  color_match : VariableGallery.ColorChain kind arity_match decoration
  input_parent : (decoration 0).portColor (kind 0).input none=parent
  output_parent : (decoration (Fin.last length)).portColor (kind (Fin.last length)).output none=parent
  input_children : (decoration 0).children (kind 0).input=a
  output_children : (decoration (Fin.last length)).children (kind (Fin.last length)).output=b

namespace RealizedBand
variable {parent : F} {a b : List F}
noncomputable def patch (B : RealizedBand parent a b) :=
  VariableGallery.patch B.kind B.arity_match
end RealizedBand

namespace OrderedWalk
variable {parent : F} {a b : List F}
/-- An identity vertex is retained even for an empty walk, so the resulting band always has two exposed main ports and loses no branch occurrence. -/
def headIdentity (w : OrderedWalk parent a b) : OrderedWalk parent a b :=
  w.cons {
    kind := .passage a.length .continuation
    decoration := passageDecoration .continuation parent a.get
    input_parent := rfl
    output_parent := rfl
    input_children := by change List.ofFn a.get=a; exact List.ofFn_get a
    output_children := by change List.ofFn a.get=a; exact List.ofFn_get a }

noncomputable def realize (w : OrderedWalk parent a b) : RealizedBand parent a b := by
  let v := w.headIdentity
  let k : Fin (w.length+1) → Kind := fun j => (v.vertex j).kind
  let d : (j : Fin (w.length+1)) → Decoration (k j) F := fun j => (v.vertex j).decoration
  have he (j : Fin w.length) :
      (d j.castSucc).children (k j.castSucc).output = (d j.succ).children (k j.succ).input := by
    rw [(v.vertex j.castSucc).output_children,(v.vertex j.succ).input_children]
    rfl
  have ha (j : Fin w.length) : (k j.castSucc).arity (k j.castSucc).output =
      (k j.succ).arity (k j.succ).input := by
    simpa only [Decoration.children_length] using congrArg List.length (he j)
  refine ⟨w.length,k,d,ha,?_,(v.vertex (0 : Fin (w.length+1))).input_parent,
    (v.vertex (Fin.last w.length)).output_parent,?_,?_⟩
  · intro j i
    cases i with
    | none => exact (v.vertex j.castSucc).output_parent.trans (v.vertex j.succ).input_parent.symm
    | some i => exact children_ext (d j.castSucc) (d j.succ) _ _ (he j) (ha j) i
  · exact (v.vertex (0 : Fin (w.length+1))).input_children.trans v.first
  · exact (v.vertex (Fin.last w.length)).output_children.trans v.last
end OrderedWalk

/-- Finite two-flag band producer: every row branch, column branch, and every intersection-block passage occurs in an allowed finite port patch. -/
theorem produced_two_flag_band (parent : F) {m n : ℕ} (row : Fin m → F)
    (col : Fin n → F) (grid : Fin m → Fin n → F) :
    Nonempty (RealizedBand parent (List.ofFn row) (List.ofFn col)) := by
  obtain ⟨p⟩ := two_flag_gallery parent row col grid
  exact ⟨p.walk.realize⟩
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
open scoped Classical
variable {F : Type} (r : F → ℕ)

def listRank (l : List F) : ℕ := (l.map r).sum
@[simp] lemma listRank_nil : listRank r []=0 := rfl
@[simp] lemma listRank_cons (f : F) (l : List F) : listRank r (f::l)=r f+listRank r l := rfl
@[simp] lemma listRank_append (l k : List F) : listRank r (l++k)=listRank r l+listRank r k := by
  simp [listRank]
@[simp] lemma listRank_ofFn {n : ℕ} (f : Fin n → F) : listRank r (List.ofFn f)=∑ i,r (f i) := by
  simp [listRank,List.sum_ofFn]

/-- Rank conservation on every ordered port (including side branches). -/
def Decoration.Conservative {k : Kind} (d : Decoration k F) : Prop :=
  ∀ p, r (d.portColor p none)=listRank r (d.children p)

lemma Decoration.conservative_iff {k : Kind} (d : Decoration k F) :
    d.Conservative r ↔ ∀ p, r (d.color ⟨p,none⟩)=∑ j,r (d.color ⟨p,some j⟩) := by
  have h (p : k.table.Port) : listRank r (d.children p)=∑ j,r (d.color ⟨p,some j⟩) := by
    rw [Decoration.children,listRank_ofFn]
    symm
    apply Fintype.sum_equiv (k.childEnumeration p)
    intro j
    exact congrArg r (d.portColor_child p j).symm
  simp only [Decoration.Conservative,h]
  rfl

lemma splitLists_conservative (rev : Bool) (parent big : F) (left mid right : List F)
    (hp : r parent=listRank r (left++big::right)) (hm : r big=listRank r mid) :
    (splitLists rev parent big left mid right).Conservative r := by
  cases rev <;> intro p <;> cases p
  all_goals simp only [splitLists, splitting_after_children_false,
    splitting_before_children_false,splitting_branch_children_false,
    splitting_after_children_true,splitting_before_children_true,
    splitting_branch_children_true,List.ofFn_get]
  all_goals first
    | exact hp
    | exact hm
    | (change r parent=listRank r (left++(mid++right));
       simpa only [listRank_append,listRank_cons,hm] using hp)

lemma passage_conservative (parent : F) {n : ℕ} (t : Passage n) (f : Fin n → F)
    (h : r parent=listRank r (List.ofFn f)) : (passageDecoration t parent f).Conservative r := by
  intro p
  cases p
  · exact h
  · change r parent=listRank r (List.ofFn (f ∘ t.permutation.symm))
    simp only [listRank_ofFn] at *
    exact h.trans (Equiv.sum_comp t.permutation.symm (fun i => r (f i))).symm

/-- A finite ranked gallery. The constructor stores a verified vertex, not a geometric bundle hypothesis; lengths and unused ports remain explicit. -/
inductive RankedChain (parent : F) : List F → List F → Type
  | refl (a : List F) : RankedChain parent a a
  | step {a b c : List F} (s : OrderedStep parent a b)
      (hs : s.decoration.Conservative r) (p : RankedChain parent b c) : RankedChain parent a c

namespace RankedChain
variable {r} {parent : F}
def forget : {a b : List F} → RankedChain r parent a b → OrderedChain parent a b
  | _,_,.refl a => .refl a
  | _,_,.step s _ p => .step s p.forget

def trans : {a b c : List F} → RankedChain r parent a b → RankedChain r parent b c → RankedChain r parent a c
  | _,_,_,.refl _,q => q
  | _,_,_,.step s hs p,q => .step s hs (p.trans q)

def single {a b : List F} (s : OrderedStep parent a b) (hs : s.decoration.Conservative r) :
    RankedChain r parent a b := .step s hs (.refl _)

def split (big : F) (left mid right : List F)
    (hp : r parent=listRank r (left++big::right)) (hm : r big=listRank r mid) :
    RankedChain r parent (left++big::right) (left++(mid++right)) :=
  single (OrderedStep.split parent big left mid right)
    (splitLists_conservative r false parent big left mid right hp hm)

def merge (big : F) (left mid right : List F)
    (hp : r parent=listRank r (left++big::right)) (hm : r big=listRank r mid) :
    RankedChain r parent (left++(mid++right)) (left++big::right) :=
  single (OrderedStep.merge parent big left mid right)
    (splitLists_conservative r true parent big left mid right hp hm)

def passage {n : ℕ} (t : Passage n) (f : Fin n → F)
    (hp : r parent=listRank r (List.ofFn f)) :
    RankedChain r parent (List.ofFn f) (List.ofFn (f ∘ t.permutation.symm)) :=
  single (OrderedStep.passage parent t f) (passage_conservative r parent t f hp)
end RankedChain
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
open scoped Classical
variable {F : Type} (r : F → ℕ)

lemma row_rank_sum (rows : List (F × List F))
    (hr : ∀ x∈rows, r x.1=listRank r x.2) :
    listRank r (rows.map Prod.fst)=listRank r (rows.flatMap Prod.snd) := by
  induction rows with
  | nil => rfl
  | cons x rows ih =>
    simp only [List.map_cons,List.flatMap_cons,listRank_cons,listRank_append]
    rw [hr x (by simp),ih (fun y hy => hr y (by simp [hy]))]

/-- Rank conservation is verified on every refinement branch, not merely on the parent at the ends of a band. -/
theorem ranked_refine_rows (parent : F) (rows : List (F × List F)) (left right : List F)
    (hp : r parent=listRank r (left++(rows.map Prod.fst++right)))
    (hr : ∀ x∈rows, r x.1=listRank r x.2) :
    Nonempty (RankedChain r parent (left++(rows.map Prod.fst++right))
      (left++(rows.flatMap Prod.snd++right))) ∧
    Nonempty (RankedChain r parent (left++(rows.flatMap Prod.snd++right))
      (left++(rows.map Prod.fst++right))) := by
  induction rows generalizing left with
  | nil => exact ⟨⟨.refl _⟩,⟨.refl _⟩⟩
  | cons x rows ih =>
    have hx := hr x (by simp)
    have ht : ∀ y∈rows,r y.1=listRank r y.2 := fun y hy => hr y (by simp [hy])
    have hp' : r parent=listRank r ((left++x.2)++(rows.map Prod.fst++right)) := by
      simpa only [List.map_cons,listRank_append,listRank_cons,hx,add_assoc] using hp
    obtain ⟨⟨p⟩,⟨q⟩⟩ := ih (left++x.2) hp' ht
    constructor
    · have h := (RankedChain.split x.1 left x.2 (rows.map Prod.fst++right) hp hx).trans
        (by simpa [List.append_assoc] using p)
      exact ⟨by simpa [List.append_assoc] using h⟩
    · have h := q.trans (by simpa [List.append_assoc] using
        (RankedChain.merge x.1 left x.2 (rows.map Prod.fst++right) hp hx))
      exact ⟨by simpa [List.append_assoc] using h⟩

/-- Adjacent interchanges preserve the numerical rank of the parent, including zero blocks; this is the ranked version of the permutation producer. -/
theorem ranked_permutation_chain (parent : F) {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    ∀ (f : Fin m → F), r parent=listRank r (List.ofFn f) →
    Nonempty (RankedChain r parent (List.ofFn f) (List.ofFn (f ∘ σ.symm))) := by
  cases m with
  | zero =>
    intro f _
    simpa using (show Nonempty (RankedChain r parent ([] : List F) []) from ⟨.refl _⟩)
  | succ n =>
    have hs : σ∈Submonoid.closure (Set.range (fun i : Fin n => Equiv.swap i.castSucc i.succ)) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      trivial
    induction hs using Submonoid.closure_induction with
    | mem x hx =>
      rcases hx with ⟨i,rfl⟩
      intro f hf
      exact ⟨RankedChain.passage (.interchange (m:=n+1) i) f hf⟩
    | one => intro f _; exact ⟨.refl _⟩
    | mul x y hx hy ihx ihy =>
      intro f hf
      obtain ⟨p⟩ := ihy f hf
      have hf' : r parent=listRank r (List.ofFn (f ∘ y.symm)) := by
        simp only [listRank_ofFn] at hf ⊢
        exact hf.trans (Equiv.sum_comp y.symm (fun i => r (f i))).symm
      obtain ⟨q⟩ := ihx (f ∘ y.symm) hf'
      exact ⟨p.trans q⟩

theorem ranked_equivalence_chain (parent : F) {m n : ℕ} (e : Fin m ≃ Fin n)
    (f : Fin m → F) (hf : r parent=listRank r (List.ofFn f)) :
    Nonempty (RankedChain r parent (List.ofFn f) (List.ofFn (f ∘ e.symm))) := by
  have h : m=n := by simpa using Fintype.card_congr e
  subst n
  exact ranked_permutation_chain r parent e f hf

theorem ranked_rectangular_permutation (parent : F) {m n : ℕ} (f : Fin m → Fin n → F)
    (hf : r parent=listRank r ((List.ofFn fun i => List.ofFn (f i)).flatten)) :
    Nonempty (RankedChain r parent ((List.ofFn fun i => List.ofFn (f i)).flatten)
      ((List.ofFn fun j => List.ofFn fun i => f i j).flatten)) := by
  have h := ranked_equivalence_chain r parent (gridTranspose m n)
    (fun k => f (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
    (by simpa only [matrix_list] using hf)
  rw [gridTranspose_colors,matrix_list] at h
  have hc := matrix_list (fun j i => f i j)
  exact hc ▸ h

lemma listRank_flatten (rows : List (List F)) :
    listRank r rows.flatten=(rows.map (listRank r)).sum := by
  induction rows with
  | nil => rfl
  | cons l rows ih => simp only [List.flatten_cons,listRank_append,List.map_cons,List.sum_cons,ih]

/-- Finite ranked two-flag band under the exact intersection-rank identities. No properness or positivity is required until later zero-block normalization. -/
theorem ranked_two_flag_gallery (parent : F) {m n : ℕ} (row : Fin m → F) (col : Fin n → F)
    (grid : Fin m → Fin n → F) (hp : r parent=∑ i,r (row i))
    (hr : ∀ i,r (row i)=∑ j,r (grid i j)) (hc : ∀ j,r (col j)=∑ i,r (grid i j)) :
    Nonempty (RankedChain r parent (List.ofFn row) (List.ofFn col)) := by
  have hpc : r parent=∑ j,r (col j) := by
    rw [hp]
    simp_rw [hr,hc]
    exact Finset.sum_comm
  have Hrows : ∀ x∈(List.ofFn fun i => (row i,List.ofFn (grid i))),r x.1=listRank r x.2 := by
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    simpa only [listRank_ofFn] using hr i
  have Hcols : ∀ x∈(List.ofFn fun j => (col j,List.ofFn fun i => grid i j)),r x.1=listRank r x.2 := by
    intro x hx
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
    simpa only [listRank_ofFn] using hc j
  have hrow := (ranked_refine_rows r parent (List.ofFn fun i => (row i,List.ofFn (grid i))) [] []
    (by simpa only [List.nil_append,List.append_nil,List.map_ofFn,Function.comp_apply,listRank_ofFn] using hp) Hrows).1
  have hcol := (ranked_refine_rows r parent (List.ofFn fun j => (col j,List.ofFn fun i => grid i j)) [] []
    (by simpa only [List.nil_append,List.append_nil,List.map_ofFn,Function.comp_apply,listRank_ofFn] using hpc) Hcols).2
  simp only [List.nil_append,List.append_nil,List.flatMap_def,List.map_ofFn] at hrow hcol
  have hgrid : r parent=listRank r ((List.ofFn fun i => List.ofFn (grid i)).flatten) := by
    simp only [listRank_flatten,List.map_ofFn,List.sum_ofFn,Function.comp_apply,listRank_ofFn]
    simpa only [hr] using hp
  obtain ⟨p⟩ := hrow
  obtain ⟨q⟩ := ranked_rectangular_permutation r parent grid hgrid
  obtain ⟨s⟩ := hcol
  exact ⟨p.trans (q.trans s)⟩
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
open scoped Classical
variable {F : Type} {r : F → ℕ} {parent : F}
namespace OrderedWalk
variable {a b c : List F}
def Conservative (w : OrderedWalk parent a b) : Prop := ∀ j,(w.vertex j).decoration.Conservative r

lemma conservative_cons (s : OrderedStep parent a b) (w : OrderedWalk parent b c)
    (hs : s.decoration.Conservative r) (hw : w.Conservative (r:=r)) :
    (w.cons s).Conservative (r:=r) := by
  rcases w with ⟨l,state,vertex,first,last⟩
  subst b
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · exact hs
  · exact hw i

lemma conservative_headIdentity (w : OrderedWalk parent a b)
    (hw : w.Conservative (r:=r)) (hp : r parent=listRank r a) :
    w.headIdentity.Conservative (r:=r) := by
  apply conservative_cons _ _ ?_ hw
  exact passage_conservative r parent (.continuation (m:=a.length)) a.get
    (by simpa only [List.ofFn_get] using hp)

lemma realize_conservative (w : OrderedWalk parent a b)
    (hw : w.Conservative (r:=r)) (hp : r parent=listRank r a) :
    ∀ v,(w.realize.decoration v).Conservative r :=
  w.conservative_headIdentity hw hp
end OrderedWalk

namespace RankedChain
lemma walk_conservative {a b : List F} (p : RankedChain r parent a b) :
    p.forget.walk.Conservative (r:=r) := by
  induction p with
  | refl a => intro j; exact Fin.elim0 j
  | step s hs p ih => exact OrderedWalk.conservative_cons s p.forget.walk hs ih
end RankedChain

/-- The finite band is an allowed incidence patch with the full rank identity at every port. Rank conservation is produced, not an extra interface. -/
theorem produced_ranked_two_flag_band {m n : ℕ} (row : Fin m → F) (col : Fin n → F)
    (grid : Fin m → Fin n → F) (hp : r parent=∑ i,r (row i))
    (hr : ∀ i,r (row i)=∑ j,r (grid i j)) (hc : ∀ j,r (col j)=∑ i,r (grid i j)) :
    ∃ B : RealizedBand parent (List.ofFn row) (List.ofFn col),
      ∀ v,(B.decoration v).Conservative r := by
  obtain ⟨p⟩ := ranked_two_flag_gallery r parent row col grid hp hr hc
  exact ⟨p.forget.walk.realize,p.forget.walk.realize_conservative p.walk_conservative
    (by simpa only [listRank_ofFn] using hp)⟩
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable

namespace IntegralCharacterVarieties
open scoped Classical

/-- All blocks in a rectangular lower-left prefix. -/
def flagGridSum {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (W : ℕ → ℕ → Submodule K V) (i j : ℕ) : Submodule K V :=
  ⨆ (x : Fin i) (y : Fin j), W x.val y.val


lemma fin_iSup_castSucc {L : Type*} [CompleteLattice L] {n : ℕ}
    (f : Fin (n+1) → L) : (⨆ x, f x)=(⨆ x : Fin n, f x.castSucc) ⊔ f (Fin.last n) := by
  apply le_antisymm
  · apply iSup_le
    intro x
    refine Fin.lastCases ?_ (fun y => ?_) x
    · exact le_sup_right
    · exact (le_iSup (fun y : Fin n => f y.castSucc) y).trans le_sup_left
  · apply sup_le
    · exact iSup_le fun x => le_iSup f x.castSucc
    · exact le_iSup f (Fin.last n)

lemma flagGridSum_corner {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (W : ℕ → ℕ → Submodule K V) (i j : ℕ) :
    flagGridSum W (i+1) (j+1)=
      flagGridSum W i (j+1) ⊔ flagGridSum W (i+1) j ⊔ W i j := by
  simp only [flagGridSum,fin_iSup_castSucc,Fin.val_castSucc,Fin.val_last,iSup_sup_eq]
  simp [sup_assoc,sup_left_comm,sup_comm]

lemma twoFlagGrid_choose {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (F H : ℕ → Submodule K V) (hF : Monotone F) (hH : Monotone H) :
    ∃ W : ℕ → ℕ → Submodule K V, ∀ i j,
      Disjoint ((F i ⊓ H (j+1)) ⊔ (F (i+1) ⊓ H j)) (W i j) ∧
      ((F i ⊓ H (j+1)) ⊔ (F (i+1) ⊓ H j)) ⊔ W i j=F (i+1) ⊓ H (j+1) := by
  have h i j : ∃ P : Submodule K V,
      Disjoint ((F i ⊓ H (j+1)) ⊔ (F (i+1) ⊓ H j)) P ∧
      ((F i ⊓ H (j+1)) ⊔ (F (i+1) ⊓ H j)) ⊔ P=F (i+1) ⊓ H (j+1) := by
    apply IsModularLattice.exists_disjoint_and_sup_eq
    exact sup_le (inf_le_inf (hF (by omega)) le_rfl) (inf_le_inf le_rfl (hH (by omega)))
  choose W hW using h
  exact ⟨W,hW⟩

lemma twoFlagGrid_spans {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (F H : ℕ → Submodule K V) (hF0 : F 0=⊥) (hH0 : H 0=⊥)
    (W : ℕ → ℕ → Submodule K V)
    (hW : ∀ i j, ((F i ⊓ H (j+1)) ⊔ (F (i+1) ⊓ H j)) ⊔ W i j=F (i+1) ⊓ H (j+1)) :
    ∀ i j, F i ⊓ H j=flagGridSum W i j := by
  intro i
  induction i with
  | zero => intro j; simp [hF0,flagGridSum]
  | succ i ih =>
    intro j
    induction j with
    | zero => simp [hH0,flagGridSum]
    | succ j ihj =>
      rw [← hW i j,ih (j+1),ihj,← flagGridSum_corner]

lemma twoFlagGrid_dim_corner {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (F H : ℕ → Submodule K V) (hF : Monotone F) (hH : Monotone H)
    (W : ℕ → ℕ → Submodule K V)
    (hW : ∀ i j, Disjoint ((F i ⊓ H (j+1)) ⊔ (F (i+1) ⊓ H j)) (W i j) ∧
      ((F i ⊓ H (j+1)) ⊔ (F (i+1) ⊓ H j)) ⊔ W i j=F (i+1) ⊓ H (j+1)) (i j : ℕ) :
    Module.finrank K ↥(F (i+1) ⊓ H (j+1)) + Module.finrank K ↥(F i ⊓ H j) =
      Module.finrank K ↥(F i ⊓ H (j+1))+Module.finrank K ↥(F (i+1) ⊓ H j)+
        Module.finrank K (W i j) := by
  have hi : (F i ⊓ H (j+1)) ⊓ (F (i+1) ⊓ H j)=F i ⊓ H j := by
    rw [inf_inf_inf_comm,inf_eq_left.mpr (hF (by omega)),inf_eq_right.mpr (hH (by omega))]
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq
    ((F i ⊓ H (j+1)) ⊔ (F (i+1) ⊓ H j)) (W i j)
  rw [(hW i j).1.eq_bot,(hW i j).2] at h1
  simp only [finrank_bot,add_zero] at h1
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (F i ⊓ H (j+1)) (F (i+1) ⊓ H j)
  rw [hi] at h2
  omega

lemma grid_sum_corner (d : ℕ → ℕ → ℕ) (i j : ℕ) :
    (∑ x : Fin (i+1), ∑ y : Fin (j+1), d x.val y.val) +
      (∑ x : Fin i, ∑ y : Fin j, d x.val y.val) =
    (∑ x : Fin i, ∑ y : Fin (j+1), d x.val y.val) +
      (∑ x : Fin (i+1), ∑ y : Fin j, d x.val y.val)+d i j := by
  simp only [Fin.sum_univ_castSucc,Fin.val_castSucc,Fin.val_last,Finset.sum_add_distrib]
  omega

lemma grid_sum_unique (d w : ℕ → ℕ → ℕ) (hd0 : ∀ j, d 0 j=0) (hd1 : ∀ i, d i 0=0)
    (hw : ∀ i j, d (i+1) (j+1)+ d i j=d i (j+1)+d (i+1) j+w i j) :
    ∀ i j, (∑ x : Fin i, ∑ y : Fin j, w x.val y.val)=d i j := by
  intro i
  induction i with
  | zero => intro j; simp [hd0]
  | succ i ih =>
    intro j
    induction j with
    | zero => simp [hd1]
    | succ j ihj =>
      have hs := grid_sum_corner w i j
      rw [ih j,ih (j+1),ihj] at hs
      have hc := hw i j
      omega

def finiteSubmoduleSum {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {ι : Type*} [Fintype ι] (P : ι → Submodule K V) : ((i:ι) → P i) →ₗ[K] V where
  toFun v := ∑ i, (v i : V)
  map_add' v w := by simp [Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.smul_sum]

lemma finiteSubmoduleSum_surjective {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {ι : Type*} [Fintype ι] (P : ι → Submodule K V) (hP : iSup P=⊤) :
    Function.Surjective (finiteSubmoduleSum P) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← hP]
  refine iSup_le fun i => ?_
  intro v hv
  refine ⟨Pi.single i ⟨v,hv⟩,?_⟩
  change (∑ j, ((Pi.single i ⟨v,hv⟩ : (k:ι) → P k) j : V))=v
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji]
    rfl
  · simp


/-- Every pair of finite flags has one simultaneous free splitting, including flags with repeated terms/zero blocks. -/
theorem two_flag_common_splitting
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (F H : ℕ → Submodule K V) (hF : Monotone F) (hH : Monotone H)
    (hF0 : F 0=⊥) (hH0 : H 0=⊥) (n m : ℕ) (hFn : F n=⊤) (hHm : H m=⊤) :
    ∃ W : ℕ → ℕ → Submodule K V,
      (∀ i j, F i ⊓ H j=flagGridSum W i j) ∧
      Function.Bijective (fun v : (p : Fin n × Fin m) → W p.1.val p.2.val =>
        ∑ p, (v p : V)) := by
  obtain ⟨W,hW⟩ := twoFlagGrid_choose F H hF hH
  have hspan := twoFlagGrid_spans F H hF0 hH0 W (fun i j => (hW i j).2)
  refine ⟨W,hspan,?_⟩
  let P : Fin n × Fin m → Submodule K V := fun p => W p.1.val p.2.val
  have hP : iSup P=⊤ := by
    change (⨆ p : Fin n × Fin m, W p.1.val p.2.val)=⊤
    rw [iSup_prod]
    change flagGridSum W n m=⊤
    rw [← hspan,hFn,hHm,inf_top_eq]
  have hsurj := finiteSubmoduleSum_surjective P hP
  have hdim : Module.finrank K ((p : Fin n × Fin m) → P p)=Module.finrank K V := by
    rw [Module.finrank_pi_fintype]
    change (∑ p : Fin n × Fin m, Module.finrank K (W p.1.val p.2.val))=_
    rw [Fintype.sum_prod_type]
    have hsum := grid_sum_unique
      (fun i j => Module.finrank K ↥(F i ⊓ H j))
      (fun i j => Module.finrank K (W i j))
      (by intro j; simp [hF0]) (by intro i; simp [hH0])
      (twoFlagGrid_dim_corner F H hF hH W hW) n m
    change (∑ x : Fin n, ∑ y : Fin m, Module.finrank K (W x.val y.val)) =
      Module.finrank K ↥(F n ⊓ H m) at hsum
    rw [hFn,hHm,inf_top_eq] at hsum
    simpa using hsum
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj
  exact ⟨hinj,hsurj⟩
end IntegralCharacterVarieties

end

end OAI
