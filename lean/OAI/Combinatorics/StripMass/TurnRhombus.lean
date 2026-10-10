import Mathlib
import OAI.Combinatorics.StripMass.GraphPath
import OAI.Combinatorics.StripMass.TurnWideGate

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

namespace TurnDisk
lemma sew_edge {n : ℕ} (D : TurnDisk (n+2)) (k : ℕ) (hk : k≤n)
    {v w : D.Vertex} (h : D.wiring v w) : (D.sew k hk).wiring v w := Or.inl h
lemma sew_edgeTurn {n : ℕ} (D : TurnDisk (n+2)) (k : ℕ) (hk : k≤n)
    {v w : D.Vertex} (h : D.wiring v w) : (D.sew k hk).edgeTurn v w=D.edgeTurn v w := by
  change (if D.wiring v w then _ else _)=_
  rw [ite_eq_left h]
lemma sew_zeroTurn {n : ℕ} (D : TurnDisk (n+2)) (k : ℕ) (hk : k≤n)
    {v w : D.Vertex} (h : D.edgeTurn v w=0) : (D.sew k hk).edgeTurn v w=0 := by
  change (if D.wiring v w then _ else _)=_
  split_ifs <;> first | exact h | rfl

namespace Gate4
variable {n : ℕ} (D : TurnDisk n) (k : ℕ) (hk : k+4≤n) (E : TurnDisk 8)
lemma old_edge {v w : D.Vertex} (h : D.wiring v w) :
    (D.gate4 k hk E).wiring (.inl v) (.inl w) :=
  Or.inl (Or.inl (Or.inl (Or.inl h)))
lemma new_edge {v w : E.Vertex} (h : E.wiring v w) :
    (D.gate4 k hk E).wiring (.inr v) (.inr w) :=
  Or.inl (Or.inl (Or.inl (Or.inl h)))
lemma old_edgeTurn {v w : D.Vertex} (h : D.wiring v w) :
    (D.gate4 k hk E).edgeTurn (.inl v) (.inl w)=D.edgeTurn v w := by
  change (((stage0 D k hk E).sew _ _).sew _ _ |>.sew _ _ |>.sew _ _).edgeTurn _ _=_
  rw [sew_edgeTurn (stage3 D k hk E) k (by omega) (v:=Sum.inl v) (w:=Sum.inl w) (Or.inl (Or.inl (Or.inl h))),
    sew_edgeTurn (stage2 D k hk E) (k+1) (by omega) (v:=Sum.inl v) (w:=Sum.inl w) (Or.inl (Or.inl h)),
    sew_edgeTurn (stage1 D k hk E) (k+2) (by omega) (v:=Sum.inl v) (w:=Sum.inl w) (Or.inl h),
    sew_edgeTurn (stage0 D k hk E) (k+3) (by omega) (v:=Sum.inl v) (w:=Sum.inl w) h]
  rfl
lemma new_edgeTurn {v w : E.Vertex} (h : E.wiring v w) :
    (D.gate4 k hk E).edgeTurn (.inr v) (.inr w)=E.edgeTurn v w := by
  change (((stage0 D k hk E).sew _ _).sew _ _ |>.sew _ _ |>.sew _ _).edgeTurn _ _=_
  rw [sew_edgeTurn (stage3 D k hk E) k (by omega) (v:=Sum.inr v) (w:=Sum.inr w) (Or.inl (Or.inl (Or.inl h))),
    sew_edgeTurn (stage2 D k hk E) (k+1) (by omega) (v:=Sum.inr v) (w:=Sum.inr w) (Or.inl (Or.inl h)),
    sew_edgeTurn (stage1 D k hk E) (k+2) (by omega) (v:=Sum.inr v) (w:=Sum.inr w) (Or.inl h),
    sew_edgeTurn (stage0 D k hk E) (k+3) (by omega) (v:=Sum.inr v) (w:=Sum.inr w) h]
  rfl
lemma cross_edgeTurn (v : D.Vertex) (w : E.Vertex) :
    (D.gate4 k hk E).edgeTurn (.inl v) (.inr w)=0 :=
  sew_zeroTurn _ _ _ (sew_zeroTurn _ _ _ (sew_zeroTurn _ _ _ (sew_zeroTurn _ _ _ rfl)))
lemma cross_edgeTurn_reverse (v : E.Vertex) (w : D.Vertex) :
    (D.gate4 k hk E).edgeTurn (.inr v) (.inl w)=0 :=
  sew_zeroTurn _ _ _ (sew_zeroTurn _ _ _ (sew_zeroTurn _ _ _ (sew_zeroTurn _ _ _ rfl)))
end Gate4

 

namespace Rhombus

def upGauge (i : Fin 6) : ℤ := -5+2*(i.val/2 : ℕ)
def downGauge (i : Fin 6) : ℤ := -4+2*(i.val/2 : ℕ)

def disk (p q : Pairing 6) : TurnDisk 8 :=
  (((TurnDisk.atom p upGauge).insert 6 (by omega) q downGauge).sew 5 (by omega)).sew 4 (by omega)

variable (p q : Pairing 6)

lemma boundary_left (i : Fin 4) : (disk p q).boundary ⟨i.val,by omega⟩=
    .inl ⟨i.val,by omega⟩ := by
  change BoundaryInsert.boundary (n:=6) (m:=6) 6 (by omega) id id
    (BoundaryErase.keep 5 (by omega) (BoundaryErase.keep 4 (by omega) ⟨i.val,by omega⟩))=_
  have he : BoundaryErase.keep 5 (by omega) (BoundaryErase.keep 4 (by omega)
      (⟨i.val,by omega⟩:Fin 8))=(⟨i.val,by omega⟩:Fin 12) := by
    apply Fin.ext
    change Gate4.skip 5 (Gate4.skip 4 i.val)=i.val
    simp (disch := omega) only [Gate4.skip,ite_eq_left]
  rw [he]
  exact BoundaryInsert.boundary_before 6 (by omega) id id _ (by change i.val<6; omega)

lemma boundary_right (i : Fin 4) : (disk p q).boundary ⟨4+i.val,by omega⟩=
    .inr ⟨2+i.val,by omega⟩ := by
  change BoundaryInsert.boundary (n:=6) (m:=6) 6 (by omega) id id
    (BoundaryErase.keep 5 (by omega) (BoundaryErase.keep 4 (by omega) ⟨4+i.val,by omega⟩))=_
  have he : BoundaryErase.keep 5 (by omega) (BoundaryErase.keep 4 (by omega)
      (⟨4+i.val,by omega⟩:Fin 8))=(⟨8+i.val,by omega⟩:Fin 12) := by
    apply Fin.ext
    change Gate4.skip 5 (Gate4.skip 4 (4+i.val))=8+i.val
    simp (disch := omega) only [Gate4.skip,ite_eq_right]
    omega
  rw [he,BoundaryInsert.boundary_between 6 (by omega) id id _
    (by change 6≤8+i.val; omega) (by change 8+i.val<6+6; omega)]
  apply congrArg Sum.inr
  apply Fin.ext
  change (8+i.val)-6=2+i.val
  omega

lemma input_boundary (i : Fin 4) : (disk p q).boundary (Gate4.input i)=
    .inl ⟨3-i.val,by omega⟩ := boundary_left p q ⟨3-i.val,by omega⟩
lemma output_boundary (i : Fin 4) : (disk p q).boundary (Gate4.output i)=
    .inr ⟨2+i.val,by omega⟩ := boundary_right p q i

lemma gauge_input (i : Fin 4) : (disk p q).gauge (Gate4.input i)=
    (if i.val<2 then -3 else -5) := by
  rw [←vertexGauge_boundary,input_boundary]
  change upGauge ⟨3-i.val,_⟩=_
  fin_cases i <;> decide
lemma gauge_output (i : Fin 4) : (disk p q).gauge (Gate4.output i)=
    (if i.val<2 then -2 else 0) := by
  rw [←vertexGauge_boundary,output_boundary]
  change downGauge ⟨2+i.val,_⟩=_
  fin_cases i <;> decide

abbrev stage : TurnDisk 12 := (TurnDisk.atom p upGauge).insert 6 (by omega) q downGauge
lemma first_left : (stage p q).boundary (BoundaryErase.left 5 (by omega))=.inl (5:Fin 6) := by
  exact BoundaryInsert.boundary_before (n:=6) (m:=6) 6 (by omega) id id _ (by decide)
lemma first_right : (stage p q).boundary (BoundaryErase.right 5 (by omega))=.inr (0:Fin 6) := by
  exact BoundaryInsert.boundary_between (n:=6) (m:=6) 6 (by omega) id id _ (by decide) (by decide)
abbrev joined : TurnDisk 10 := (stage p q).sew 5 (by omega)
lemma second_left : (joined p q).boundary
    (BoundaryErase.left 4 (by omega))=.inl (4:Fin 6) := by
  change BoundaryInsert.boundary (n:=6) (m:=6) 6 (by omega) id id (4:Fin 12)=_
  exact BoundaryInsert.boundary_before (n:=6) (m:=6) 6 (by omega) id id _ (by decide)
lemma second_right : (joined p q).boundary
    (BoundaryErase.right 4 (by omega))=.inr (1:Fin 6) := by
  change BoundaryInsert.boundary (n:=6) (m:=6) 6 (by omega) id id (7:Fin 12)=_
  exact BoundaryInsert.boundary_between (n:=6) (m:=6) 6 (by omega) id id _ (by decide) (by decide)

variable (hm : ∀ i : Fin 2,p.Occupied ⟨4+i.val,by omega⟩ ↔ q.Occupied ⟨1-i.val,by omega⟩)
include hm
lemma match1 : Graph.Used (stage p q).wiring ((stage p q).boundary (BoundaryErase.left 5 (by omega))) ↔
    Graph.Used (stage p q).wiring ((stage p q).boundary (BoundaryErase.right 5 (by omega))) := by
  rw [first_left,first_right]
  change Graph.Used (BoundaryInsert.unionGraph p.Adj q.Adj) (.inl 5) ↔
    Graph.Used (BoundaryInsert.unionGraph p.Adj q.Adj) (.inr 0)
  rw [BoundaryInsert.used_left,BoundaryInsert.used_right]
  exact hm 1
lemma stage_used (v : Fin 6⊕Fin 6) :
    Graph.Used (joined p q).wiring v ↔ Graph.Used (stage p q).wiring v :=
  sew_used _ _ _ (match1 p q hm) v
lemma match2 : Graph.Used (joined p q).wiring
    ((joined p q).boundary (BoundaryErase.left 4 (by omega))) ↔
    Graph.Used (joined p q).wiring
    ((joined p q).boundary (BoundaryErase.right 4 (by omega))) := by
  erw [second_left,second_right,stage_used p q hm,stage_used p q hm]
  change Graph.Used (BoundaryInsert.unionGraph p.Adj q.Adj) (.inl 4) ↔
    Graph.Used (BoundaryInsert.unionGraph p.Adj q.Adj) (.inr 1)
  rw [BoundaryInsert.used_left,BoundaryInsert.used_right]
  exact hm 0
lemma used (v : Fin 6⊕Fin 6) : Graph.Used (disk p q).wiring v ↔
    Graph.Used (stage p q).wiring v :=
  (sew_used _ _ _ (match2 p q hm) v).trans (stage_used p q hm v)
lemma compatible : (disk p q).Compatible := by
  refine ⟨⟨True.intro,match1 p q hm,?_⟩,match2 p q hm,?_⟩
  · rw [←vertexGauge_boundary,←vertexGauge_boundary,first_right,first_left]
    change downGauge 0=upGauge 5-3
    decide
  · rw [←vertexGauge_boundary,←vertexGauge_boundary,second_right,second_left]
    change downGauge 1=upGauge 4-3
    decide

lemma wiring (v w : Fin 6⊕Fin 6) : (disk p q).wiring v w ↔
    BoundaryInsert.unionGraph p.Adj q.Adj v w ∨ ∃ i : Fin 2,p.Occupied ⟨4+i.val,by omega⟩ ∧
      ((v=.inl ⟨4+i.val,by omega⟩ ∧ w=.inr ⟨1-i.val,by omega⟩) ∨
        (w=.inl ⟨4+i.val,by omega⟩ ∧ v=.inr ⟨1-i.val,by omega⟩)) := by
  change BoundarySew.graph (joined p q).wiring _ _ _ v w ↔ _
  simp only [BoundarySew.graph]
  erw [second_left,second_right,stage_used p q hm]
  change (BoundarySew.graph (stage p q).wiring _ _ _ v w ∨ _) ↔ _
  simp only [BoundarySew.graph]
  rw [first_left,first_right]
  change ((_ ∨ (Graph.Used (BoundaryInsert.unionGraph p.Adj q.Adj) (.inl 5) ∧ _)) ∨
    (Graph.Used (BoundaryInsert.unionGraph p.Adj q.Adj) (.inl 4) ∧ _)) ↔ _
  rw [BoundaryInsert.used_left,BoundaryInsert.used_left]
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false]
  change ((BoundaryInsert.unionGraph p.Adj q.Adj v w ∨ (p.Occupied 5 ∧ _)) ∨ (p.Occupied 4 ∧ _)) ↔ _
  tauto

omit hm
lemma up_edge {v w : Fin 6} (h : p.Adj v w) : (disk p q).wiring (.inl v) (.inl w) :=
  Or.inl (Or.inl h)
lemma down_edge {v w : Fin 6} (h : q.Adj v w) : (disk p q).wiring (.inr v) (.inr w) :=
  Or.inl (Or.inl h)
lemma up_turn {v w : Fin 6} (h : p.Adj v w) :
    (disk p q).edgeTurn (.inl v) (.inl w)=Pairing.arcTurn upGauge v w := by
  change ((joined p q).sew 4 (by omega)).edgeTurn _ _=_
  rw [sew_edgeTurn (joined p q) 4 (by omega) (v:=Sum.inl v) (w:=Sum.inl w) (Or.inl h),
    sew_edgeTurn (stage p q) 5 (by omega) (v:=Sum.inl v) (w:=Sum.inl w) h]
  rfl
lemma down_turn {v w : Fin 6} (h : q.Adj v w) :
    (disk p q).edgeTurn (.inr v) (.inr w)=Pairing.arcTurn downGauge v w := by
  change ((joined p q).sew 4 (by omega)).edgeTurn _ _=_
  rw [sew_edgeTurn (joined p q) 4 (by omega) (v:=Sum.inr v) (w:=Sum.inr w) (Or.inl h),
    sew_edgeTurn (stage p q) 5 (by omega) (v:=Sum.inr v) (w:=Sum.inr w) h]
  rfl
lemma cross_turn (v w : Fin 6) : (disk p q).edgeTurn (.inl v) (.inr w)=0 :=
  sew_zeroTurn _ _ _ (sew_zeroTurn _ _ _ rfl)
lemma cross_turn_reverse (v w : Fin 6) : (disk p q).edgeTurn (.inr v) (.inl w)=0 :=
  sew_zeroTurn _ _ _ (sew_zeroTurn _ _ _ rfl)
end Rhombus
end TurnDisk

 

 


namespace TurnNetwork
open TurnDisk
abbrev Local := Fin 6 ⊕ Fin 6
abbrev Node (n t : ℕ) := Fin n ⊕ (Fin t × Local)

def old {n t : ℕ} : Node n t → Node n (t+1)
  | .inl i => .inl i
  | .inr (i,v) => .inr (i.castSucc,v)
def fresh {n t : ℕ} (v : Local) : Node n (t+1) := .inr (Fin.last t,v)

lemma old_injective {n t : ℕ} : Function.Injective (old (n:=n) (t:=t)) := by
  rintro (i|⟨i,v⟩) (j|⟨j,w⟩) h <;> simp only [old,Sum.inl.injEq,Sum.inr.injEq,Prod.mk.injEq] at h
  · exact congrArg Sum.inl h
  · cases h
  · cases h
  · obtain ⟨h,rfl⟩:=h
    have h' : i=j := Fin.ext (congrArg (fun i : Fin (t+1)=>i.val) h)
    subst j
    rfl
lemma fresh_injective {n t : ℕ} : Function.Injective (fresh (n:=n) (t:=t)) := by
  intro v w h
  simpa only [fresh,Sum.inr.injEq,Prod.mk.injEq,true_and] using h
lemma old_ne_fresh {n t : ℕ} (v : Node n t) (w : Local) : old v≠fresh w := by
  cases v with
  | inl i => simp only [old,fresh,ne_eq,reduceCtorEq,not_false_eq_true]
  | inr x =>
    intro h
    have hz := congrArg (fun z : Node n (t+1)=> match z with
      | .inl _ => 0
      | .inr x => x.1.val) h
    change x.1.val=t at hz
    omega
lemma cover {n t : ℕ} (v : Node n (t+1)) :
    (∃ w : Node n t,v=old w) ∨ (∃ w : Local,v=fresh w) := by
  cases v with
  | inl i => exact Or.inl ⟨.inl i,rfl⟩
  | inr x =>
    obtain ⟨i,v⟩:=x
    by_cases h : i.val<t
    · exact Or.inl ⟨.inr (⟨i.val,h⟩,v),by rfl⟩
    · right
      refine ⟨v,?_⟩
      have he : i=Fin.last t := Fin.ext (by change i.val=t; omega)
      rw [he]
      rfl

variable {n : ℕ} (p₀ : Pairing n) (g₀ : Fin n → ℤ)
  (p q : ℕ → Pairing 6) (k : ℕ → ℕ) (hk : ∀ t,k t+4≤n)

def disk : ℕ → TurnDisk n
  | 0 => .atom p₀ g₀
  | t+1 => (disk t).gate4 (k t) (hk t) (Rhombus.disk (p t) (q t))

 

def names : (t : ℕ) → (disk p₀ g₀ p q k hk t).Vertex ≃ Node n t
  | 0 =>
    { toFun := Sum.inl
      invFun := fun v=> match v with
        | .inl i=>i
        | .inr x=>Fin.elim0 x.1
      left_inv := fun _=>rfl
      right_inv := by rintro (i|⟨i,v⟩); rfl; exact Fin.elim0 i }
  | t+1 =>
    Equiv.ofBijective (fun v=> match v with
      | .inl w=>old (names t w)
      | .inr w=>fresh w) ⟨by
        rintro (v|v) (w|w) h
        · exact congrArg Sum.inl ((names t).injective (old_injective h))
        · exact (old_ne_fresh (names t v) w h).elim
        · exact (old_ne_fresh (names t w) v h.symm).elim
        · exact congrArg Sum.inr (fresh_injective h),by
        intro v
        obtain ⟨w,rfl⟩|⟨w,rfl⟩:=cover v
        · exact ⟨.inl ((names t).symm w),by simp only [Equiv.apply_symm_apply]⟩
        · exact ⟨.inr w,rfl⟩⟩

lemma names_old (t : ℕ) (v : (disk p₀ g₀ p q k hk t).Vertex) :
    names p₀ g₀ p q k hk (t+1) (.inl v)=old (names p₀ g₀ p q k hk t v) := rfl
lemma names_fresh (t : ℕ) (v : Local) :
    names p₀ g₀ p q k hk (t+1) (.inr v)=fresh v := rfl
lemma inv_old (t : ℕ) (v : Node n t) :
    (names p₀ g₀ p q k hk (t+1)).symm (old v)=.inl ((names p₀ g₀ p q k hk t).symm v) := by
  apply (names p₀ g₀ p q k hk (t+1)).injective
  rw [Equiv.apply_symm_apply,names_old,Equiv.apply_symm_apply]
lemma inv_fresh (t : ℕ) (v : Local) :
    (names p₀ g₀ p q k hk (t+1)).symm (fresh v)=.inr v := by
  apply (names p₀ g₀ p q k hk (t+1)).injective
  rw [Equiv.apply_symm_apply,names_fresh]

def graph (t : ℕ) (v w : Node n t) : Prop :=
  (disk p₀ g₀ p q k hk t).wiring ((names p₀ g₀ p q k hk t).symm v)
    ((names p₀ g₀ p q k hk t).symm w)
def edgeTurn (t : ℕ) (v w : Node n t) : ℤ :=
  (disk p₀ g₀ p q k hk t).edgeTurn ((names p₀ g₀ p q k hk t).symm v)
    ((names p₀ g₀ p q k hk t).symm w)
def boundary (t : ℕ) (i : Fin n) : Node n t :=
  names p₀ g₀ p q k hk t ((disk p₀ g₀ p q k hk t).boundary i)

instance (t : ℕ) : Std.Symm (graph p₀ g₀ p q k hk t) :=
  ⟨by intro v w h; exact (symm h : (disk p₀ g₀ p q k hk t).wiring _ _)⟩
lemma boundary_zero (i : Fin n) : boundary p₀ g₀ p q k hk 0 i=.inl i := rfl
lemma boundary_slot (t : ℕ) (i : Fin 4) :
    boundary p₀ g₀ p q k hk (t+1) (Gate4.slot (k t) (hk t) i)=
      fresh (.inr ⟨2+i.val,by omega⟩) := by
  unfold boundary
  change names p₀ g₀ p q k hk (t+1)
    (((disk p₀ g₀ p q k hk t).gate4 (k t) (hk t) (Rhombus.disk (p t) (q t))).boundary _) = _
  erw [Gate4.boundary_slot,Rhombus.output_boundary]
  rfl
lemma boundary_outside (t : ℕ) (i : Fin n) (hi : i.val<k t ∨ k t+4 ≤ i.val) :
    boundary p₀ g₀ p q k hk (t+1) i=old (boundary p₀ g₀ p q k hk t i) := by
  unfold boundary
  change names p₀ g₀ p q k hk (t+1)
    (((disk p₀ g₀ p q k hk t).gate4 (k t) (hk t) (Rhombus.disk (p t) (q t))).boundary _) = _
  erw [Gate4.boundary_outside _ _ _ _ i hi]
  rfl

lemma old_edge (t : ℕ) {v w : Node n t} (h : graph p₀ g₀ p q k hk t v w) :
    graph p₀ g₀ p q k hk (t+1) (old v) (old w) := by
  unfold graph
  rw [inv_old,inv_old]
  exact Gate4.old_edge _ _ _ _ h
lemma old_turn (t : ℕ) {v w : Node n t} (h : graph p₀ g₀ p q k hk t v w) :
    edgeTurn p₀ g₀ p q k hk (t+1) (old v) (old w)=edgeTurn p₀ g₀ p q k hk t v w := by
  unfold edgeTurn
  rw [inv_old,inv_old]
  exact Gate4.old_edgeTurn _ _ _ _ h
lemma fresh_edge (t : ℕ) {v w : Local} (h : (Rhombus.disk (p t) (q t)).wiring v w) :
    graph p₀ g₀ p q k hk (t+1) (fresh v) (fresh w) := by
  unfold graph
  rw [inv_fresh,inv_fresh]
  exact Gate4.new_edge _ _ _ _ h
lemma fresh_turn (t : ℕ) {v w : Local} (h : (Rhombus.disk (p t) (q t)).wiring v w) :
    edgeTurn p₀ g₀ p q k hk (t+1) (fresh v) (fresh w)=(Rhombus.disk (p t) (q t)).edgeTurn v w := by
  unfold edgeTurn
  rw [inv_fresh,inv_fresh]
  exact Gate4.new_edgeTurn _ _ _ _ h
lemma wire_turn (t : ℕ) (v : Node n t) (w : Local) :
    edgeTurn p₀ g₀ p q k hk (t+1) (old v) (fresh w)=0 := by
  unfold edgeTurn
  rw [inv_old,inv_fresh]
  exact Gate4.cross_edgeTurn _ _ _ _ _ _
lemma wire_turn_reverse (t : ℕ) (v : Local) (w : Node n t) :
    edgeTurn p₀ g₀ p q k hk (t+1) (fresh v) (old w)=0 := by
  unfold edgeTurn
  rw [inv_old,inv_fresh]
  exact Gate4.cross_edgeTurn_reverse _ _ _ _ _ _

 

def Occupied (t : ℕ) : Node n t → Prop
  | .inl i=>p₀.Occupied i
  | .inr (i,.inl v)=>(p i.val).Occupied v
  | .inr (i,.inr v)=>(q i.val).Occupied v

omit g₀ k hk
lemma occupied_old (t : ℕ) (v : Node n t) : Occupied p₀ p q (t+1) (old v) ↔ Occupied p₀ p q t v := by
  cases v with
  | inl i=>rfl
  | inr x=>obtain ⟨i,(v|v)⟩:=x <;> rfl
lemma occupied_fresh (t : ℕ) (v : Local) :
    Occupied p₀ p q (t+1) (fresh v) ↔ match v with
      | .inl i=>(p t).Occupied i
      | .inr i=>(q t).Occupied i := by cases v <;> rfl

include g₀ k hk
lemma used_equiv (t : ℕ) (v : Node n t) :
    Graph.Used (graph p₀ g₀ p q k hk t) v ↔
      Graph.Used (disk p₀ g₀ p q k hk t).wiring ((names p₀ g₀ p q k hk t).symm v) := by
  constructor
  · rintro ⟨w,hw⟩
    exact ⟨(names p₀ g₀ p q k hk t).symm w,hw⟩
  · rintro ⟨w,hw⟩
    exact ⟨names p₀ g₀ p q k hk t w,by simpa only [graph,Equiv.symm_apply_apply] using hw⟩

 

theorem potential (t : ℕ) (hc : (disk p₀ g₀ p q k hk t).Compatible)
    (hd : Graph.DrainsBoundary (graph p₀ g₀ p q k hk t) (boundary p₀ g₀ p q k hk t)) :
    ∃ (a : Pairing n) (P : Node n t → ℤ),
      (∀ i j,Relation.ReflTransGen (graph p₀ g₀ p q k hk t)
        (boundary p₀ g₀ p q k hk t i) (boundary p₀ g₀ p q k hk t j) ↔ i=j ∨ a.Adj i j) ∧
      (∀ i j,a.Adj i j → P (boundary p₀ g₀ p q k hk t j)-P (boundary p₀ g₀ p q k hk t i)=
        Pairing.arcTurn (disk p₀ g₀ p q k hk t).gauge i j) ∧
      ∀ v w,graph p₀ g₀ p q k hk t v w → P w-P v=edgeTurn p₀ g₀ p q k hk t v w := by
  have hd' : Graph.DrainsBoundary (disk p₀ g₀ p q k hk t).wiring (disk p₀ g₀ p q k hk t).boundary := by
    intro v w hvw
    have he : graph p₀ g₀ p q k hk t (names p₀ g₀ p q k hk t v) (names p₀ g₀ p q k hk t w) := by
      simpa only [graph,Equiv.symm_apply_apply] using hvw
    obtain ⟨i,hi⟩:=hd _ _ he
    refine ⟨i,?_⟩
    have h:=Graph.map_reach (names p₀ g₀ p q k hk t).symm (fun _ _ h=>.single h) hi
    simpa only [boundary,Equiv.symm_apply_apply] using h
  obtain ⟨a,P,hr,ha,he⟩:=(disk p₀ g₀ p q k hk t).potential hc hd'
  refine ⟨a,P ∘ (names p₀ g₀ p q k hk t).symm,?_,?_,fun v w h=>he _ _ h⟩
  · intro i j
    rw [←hr.reach]
    constructor
    · intro h
      have hh:=Graph.map_reach (names p₀ g₀ p q k hk t).symm (fun _ _ h=>.single h) h
      simpa only [boundary,Equiv.symm_apply_apply] using hh
    · intro h
      exact Graph.map_reach (names p₀ g₀ p q k hk t) (fun _ _ h=>by
        apply Relation.ReflTransGen.single
        simpa only [graph,Equiv.symm_apply_apply] using h) h
  · intro i j hij
    simpa only [Function.comp_apply,boundary,Equiv.symm_apply_apply] using ha i j hij

end TurnNetwork
end
end CriticalStrip.Diagram

end OAI
