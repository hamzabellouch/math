import Mathlib
import OAI.Combinatorics.StripMass.ColumnSweep
import OAI.Combinatorics.StripMass.TripleCircuit

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

 
def BareColumn {n : ℕ} (t : Configuration n) (v w : Vertex n) : Prop :=
  (v.1=w.1 ∧ (t v.1).Adj v.2 w.2) ∨
  (v.2=3 ∧ w.2=0 ∧ v.1.val+1=w.1.val ∧ (t v.1).Occupied 3) ∨
  (w.2=3 ∧ v.2=0 ∧ w.1.val+1=v.1.val ∧ (t w.1).Occupied 3)

namespace ColumnSew
variable {n : ℕ} (p : Pairing n) (t : Configuration n)

def graph : Sum (Fin n) (Vertex n) → Sum (Fin n) (Vertex n) → Prop :=
  Patch.glued p.Adj (BareColumn t) id (fun i=>(i,1)) p.Occupied

def project : Sum (Fin n) (Vertex n) → Vertex n
  | .inl i => (i,1)
  | .inr v => v

lemma bare_sub {v w : Vertex n} (h : BareColumn t v w) : Wiring p t v w := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

lemma west (i : Fin n) (hi : p.Occupied i) :
    graph p t (.inl i) (.inr (i,1)) := ⟨i,hi,rfl,rfl⟩

lemma west' (i : Fin n) (hi : p.Occupied i) :
    graph p t (.inr (i,1)) (.inl i) := ⟨i,hi,rfl,rfl⟩

lemma project_edge {v w} (h : graph p t v w) :
    Relation.ReflTransGen (Wiring p t) (project v) (project w) := by
  cases v with
  | inl i =>
    cases w with
    | inl j => exact .single (Or.inr (Or.inl ⟨rfl,rfl,h⟩))
    | inr w => obtain ⟨i,hi,rfl,rfl⟩ := h; exact .refl
  | inr v =>
    cases w with
    | inl j => obtain ⟨i,hi,rfl,rfl⟩ := h; exact .refl
    | inr w => exact .single (bare_sub p t h)

lemma include_edge {v w} (h : Wiring p t v w) :
    Relation.ReflTransGen (graph p t) (.inr v) (.inr w) := by
  rcases h with h | h | h | h
  · exact .single (Or.inl h)
  · rcases v with ⟨i,a⟩; rcases w with ⟨j,b⟩
    obtain ⟨rfl,rfl,hij⟩ := h
    exact ((Relation.ReflTransGen.single (west' p t i ⟨j,hij⟩)).tail (show graph p t (.inl i) (.inl j) from hij)).tail
      (west p t j ⟨i,Pairing.adj_symm hij⟩)
  · exact .single (Or.inr (Or.inl h))
  · exact .single (Or.inr (Or.inr h))

lemma old_used (i : Fin n) (hi : Graph.Used (graph p t) (.inl i)) : p.Occupied i := by
  obtain ⟨j,hj⟩ := hi
  cases j with
  | inl j => exact ⟨j,hj⟩
  | inr j => obtain ⟨i,hi,rfl,rfl⟩ := hj; exact hi

lemma wiring_west_used (i : Fin n) (hi : p.Occupied i) :
    Graph.Used (Wiring p t) (i,1) := by
  obtain ⟨j,hj⟩ := hi
  exact ⟨(j,1),Or.inr (Or.inl ⟨rfl,rfl,hj⟩)⟩

lemma project_used (v) (hv : Graph.Used (graph p t) v) :
    Graph.Used (Wiring p t) (project v) := by
  cases v with
  | inl i => exact wiring_west_used p t i (old_used p t i hv)
  | inr v =>
    obtain ⟨w,hw⟩ := hv
    cases w with
    | inl i => obtain ⟨i,hi,rfl,rfl⟩ := hw; exact wiring_west_used p t i hi
    | inr w => exact ⟨w,bare_sub p t hw⟩

lemma include_used (v : Vertex n) (hv : Graph.Used (Wiring p t) v) :
    Graph.Used (graph p t) (.inr v) := by
  obtain ⟨w,h⟩ := hv
  rcases h with h | h | h | h
  · exact ⟨.inr w,Or.inl h⟩
  · rcases v with ⟨i,a⟩; rcases w with ⟨j,b⟩
    obtain ⟨rfl,rfl,hij⟩ := h
    exact ⟨.inl i,west' p t i ⟨j,hij⟩⟩
  · exact ⟨.inr w,Or.inr (Or.inl h)⟩
  · exact ⟨.inr w,Or.inr (Or.inr h)⟩

 

def equivalence : Graph.BoundaryEquiv (graph p t) (Wiring p t)
    (fun i=>.inr (i,2)) (fun i=>(i,2)) where
  toFun := project
  invFun := Sum.inr
  map_edge := fun _ _ => project_edge p t
  inv_edge := fun _ _ => include_edge p t
  map_boundary := fun _=>rfl
  inv_boundary := fun _=>rfl
  map_used := project_used p t
  inv_used := include_used p t
  retract := by
    intro v hv
    cases v with
    | inl i => exact .single (west p t i (old_used p t i hv))
    | inr v => exact .refl
  inv_retract := fun _ _=>.refl

end ColumnSew

 
structure ColumnCompatible {n : ℕ} (west : Fin n → Prop) (t : Configuration n) : Prop where
  west : ∀ i, (t i).Occupied 1 ↔ west i
  south : ∀ i, i.val=0 → ¬(t i).Occupied 0
  north : ∀ i, i.val+1=n → ¬(t i).Occupied 3
  glued : ∀ i j, i.val+1=j.val → ((t i).Occupied 3 ↔ (t j).Occupied 0)

lemma realizes_iff_column_graph {n : ℕ} (p q : Pairing n) (t : Configuration n) :
    Realizes p q t ↔ ColumnCompatible p.Occupied t ∧
      GraphRealizes (Wiring p t) (fun i=>(i,2)) q := by
  constructor
  · intro h
    refine ⟨⟨h.west,h.south,h.north,h.glued⟩,h.no_loop,?_⟩
    intro i j
    by_cases hij : i=j
    · subst j; exact ⟨fun _=>Or.inl rfl,fun _=>.refl⟩
    · simpa only [Reach,hij,false_or] using (h.output i j hij).symm
  · rintro ⟨hc,h⟩
    refine ⟨hc.west,?_,hc.south,hc.north,hc.glued,h.no_loop,?_⟩
    · intro i
      exact (PartialColumn.east_used p t i).symm.trans
        (h.boundary_used_iff (fun _ _ he=>congrArg Prod.fst he) i)
    · intro i j hij
      simpa only [Reach,hij,false_or] using (h.reach i j).symm

lemma realizes_unique {n : ℕ} {p q r : Pairing n} {t : Configuration n}
    (hq : Realizes p q t) (hr : Realizes p r t) : q=r :=
  ((realizes_iff_column_graph p q t).mp hq).2.unique
    ((realizes_iff_column_graph p r t).mp hr).2

 

lemma realizes_exists_of_drains {n : ℕ} (hn : 0<n) (p : Pairing n) (t : Configuration n)
    (hc : ColumnCompatible p.Occupied t)
    (hd : Graph.DrainsBoundary (Wiring p t) (fun i=>(i,2))) :
    ∃ q, Realizes p q t := by
  have hd' : Graph.DrainsBoundary (Wiring p t) (PartialColumn.fullBoundary hn) := by
    intro v w hvw
    obtain ⟨i,hi⟩ := hd v w hvw
    exact ⟨i.castSucc,by simpa only [PartialColumn.fullBoundary,Fin.lastCases_castSucc] using hi⟩
  have hc' := (PartialColumn.full_compatible_iff p t).mpr
    (show PartialColumn.InputConditions p t from ⟨hc.west,hc.south,hc.glued⟩)
  obtain ⟨q,hq⟩ := PartialColumn.circuit_exists p t n le_rfl hc'
    ((PartialColumn.fullEquiv hn p t).symm.drains hd')
  have hs := (Circuit.eval_sound p.padBottom (PartialColumn.circuit t n le_rfl) q hq).2.2
  have hlast : ¬q.Occupied (Fin.last n) := by
    rw [←hs,PartialColumn.circuit_support]
    simp only [PartialColumn.support,Fin.val_last,lt_self_iff_false,dite_false,
      true_and,dite_eq_left hn]
    exact hc.north _ (by dsimp; omega)
  let q' := q.restrict Fin.castSuccOrderEmb
  refine ⟨q',(PartialColumn.column_eval_iff hn p q' t).mp ?_⟩
  rw [Pairing.padTop_restrict q hlast]
  exact hq

end

 

 

noncomputable section
open scoped Classical BigOperators

 

namespace ColumnChain
variable {n : ℕ}

def Vertices : List (Configuration n) → Type
  | [] => Fin n
  | _::ts => Sum (Vertices ts) (Vertex n)

def boundary : (ts : List (Configuration n)) → Fin n → Vertices ts
  | [] => id
  | _::_ => fun i => .inr (i,2)

def support (p : Pairing n) : List (Configuration n) → Fin n → Prop
  | [] => p.Occupied
  | t::_ => fun i => (t i).Occupied 2

def wiring (p : Pairing n) : (ts : List (Configuration n)) → Vertices ts → Vertices ts → Prop
  | [] => p.Adj
  | t::ts => Patch.glued (wiring p ts) (BareColumn t) (boundary ts)
      (fun i=>(i,1)) (support p ts)

def Compatible (p : Pairing n) : List (Configuration n) → Prop
  | [] => True
  | t::ts => Compatible p ts ∧ ColumnCompatible (support p ts) t

def Runs (p : Pairing n) : List (Configuration n) → Pairing n → Prop
  | [],q => p=q
  | t::ts,q => ∃ r, Runs p ts r ∧ Realizes r q t

lemma runs_sound (p : Pairing n) (ts : List (Configuration n)) (q : Pairing n)
    (h : Runs p ts q) : Compatible p ts ∧
      GraphRealizes (wiring p ts) (boundary ts) q ∧ support p ts=q.Occupied := by
  induction ts generalizing q with
  | nil =>
    have he : p=q := h
    subst q
    exact ⟨trivial,p.graphRealizes,rfl⟩
  | cons t ts ih =>
    obtain ⟨r,hr,hq⟩ := h
    obtain ⟨hc,hg,hs⟩ := ih r hr
    obtain ⟨hct,hgt⟩ := (realizes_iff_column_graph r q t).mp hq
    refine ⟨⟨hc,by simpa only [hs] using hct⟩,?_,?_⟩
    · change GraphRealizes (Patch.glued (wiring p ts) (BareColumn t) (boundary ts)
        (fun i=>(i,1)) (support p ts)) (fun i=>.inr (i,2)) q
      rw [hs,hg.substitute_iff]
      exact (ColumnSew.equivalence r t).symm.realizes hgt
    · funext i
      exact propext (hq.east i)

lemma runs_unique {p q r : Pairing n} {ts : List (Configuration n)}
    (hq : Runs p ts q) (hr : Runs p ts r) : q=r :=
  (runs_sound p ts q hq).2.1.unique (runs_sound p ts r hr).2.1

lemma runs_exists (hn : 0<n) (p : Pairing n) (ts : List (Configuration n))
    (hc : Compatible p ts) (hd : Graph.DrainsBoundary (wiring p ts) (boundary ts)) :
    ∃ q, Runs p ts q := by
  induction ts with
  | nil => exact ⟨p,rfl⟩
  | cons t ts ih =>
    obtain ⟨hc,ht⟩ := hc
    have hd' : Graph.DrainsBoundary (wiring p ts) (boundary ts) :=
      Graph.glued_drains_local (wiring p ts) (BareColumn t) (boundary ts)
        (fun i=>(i,1)) (support p ts) (fun i=>(i,2)) hd
    obtain ⟨r,hr⟩ := ih hc hd'
    obtain ⟨_,hg,hs⟩ := runs_sound p ts r hr
    change Graph.DrainsBoundary (Patch.glued (wiring p ts) (BareColumn t) (boundary ts)
      (fun i=>(i,1)) (support p ts)) (fun i=>.inr (i,2)) at hd
    rw [hs] at ht hd
    have hdr := (hg.substitute_drains_iff (BareColumn t) (fun i=>(i,1)) (fun i=>(i,2))).mp hd
    obtain ⟨q,hq⟩ := realizes_exists_of_drains hn r t ht ((ColumnSew.equivalence r t).drains hdr)
    exact ⟨q,r,hr,hq⟩

 

lemma runs_iff (hn : 0<n) (p : Pairing n) (ts : List (Configuration n)) (q : Pairing n) :
    Runs p ts q ↔ Compatible p ts ∧ GraphRealizes (wiring p ts) (boundary ts) q := by
  constructor
  · intro h
    have hh:=runs_sound p ts q h
    exact ⟨hh.1,hh.2.1⟩
  · rintro ⟨hc,hg⟩
    obtain ⟨r,hr⟩:=runs_exists hn p ts hc hg.drainsBoundary
    exact (runs_sound p ts r hr).2.1.unique hg ▸ hr

end ColumnChain
end

 

 

noncomputable section
open scoped Classical

namespace ColumnRectangle
variable {n m : ℕ}

abbrev V (n m : ℕ) := Sum (Fin n) (Fin m × Vertex n)

 

def wiring (p : Pairing n) (h : Fin m → Configuration n) : V n m → V n m → Prop
  | .inl i, .inl j => p.Adj i j
  | .inl i, .inr (k,j,a) | .inr (k,j,a), .inl i =>
      k.val+1=m ∧ i=j ∧ a=1 ∧ p.Occupied i
  | .inr (k,i,a), .inr (l,j,b) =>
      (k=l ∧ BareColumn (h k) (i,a) (j,b)) ∨
      (i=j ∧ a=2 ∧ b=1 ∧ l.val+1=k.val ∧ (h k i).Occupied 2) ∨
      (i=j ∧ a=1 ∧ b=2 ∧ k.val+1=l.val ∧ (h l j).Occupied 2)

def boundary : (m : ℕ) → Fin n → V n m
  | 0 => Sum.inl
  | _+1 => fun i=>.inr (0,i,2)

def active (p : Pairing n) : {m : ℕ} → (Fin m → Configuration n) → Fin n → Prop
  | 0,_ => p.Occupied
  | _+1,h => fun i=>(h 0 i).Occupied 2

 
def addColumn (n m : ℕ) : Sum (V n m) (Vertex n) ≃ V n (m+1) where
  toFun
    | .inl (.inl i) => .inl i
    | .inl (.inr (k,v)) => .inr (k.succ,v)
    | .inr v => .inr (0,v)
  invFun
    | .inl i => .inl (.inl i)
    | .inr (k,v) => Fin.cases (.inr v) (fun k=>.inl (.inr (k,v))) k
  left_inv := by
    rintro ((i|⟨k,v⟩)|v) <;> simp
  right_inv := by
    rintro (i|⟨k,v⟩)
    · rfl
    · induction k using Fin.cases <;> simp

@[simp] lemma addColumn_old (i : Fin n) : addColumn n m (.inl (.inl i))=.inl i := rfl
@[simp] lemma addColumn_cell (k : Fin m) (v : Vertex n) :
    addColumn n m (.inl (.inr (k,v)))=.inr (k.succ,v) := rfl
@[simp] lemma addColumn_new (v : Vertex n) : addColumn n m (.inr v)=.inr (0,v) := rfl

lemma wiring_step (p : Pairing n) (t : Configuration n) (h : Fin m → Configuration n)
    (v w : Sum (V n m) (Vertex n)) :
    Patch.glued (wiring p h) (BareColumn t) (boundary m) (fun i=>(i,1)) (active p h) v w ↔
      wiring p (Fin.cons t h) (addColumn n m v) (addColumn n m w) := by
  cases v with
  | inl v =>
    cases w with
    | inl w =>
      cases v with
      | inl i =>
        cases w with
        | inl j => rfl
        | inr w =>
          rcases w with ⟨l,j,b⟩
          simp [Patch.glued,wiring]
      | inr v =>
        rcases v with ⟨k,i,a⟩
        cases w with
        | inl j => simp [Patch.glued,wiring]
        | inr w =>
          rcases w with ⟨l,j,b⟩
          simp [Patch.glued,wiring]
    | inr w =>
      rcases w with ⟨j,b⟩
      cases m with
      | zero =>
        cases v with
        | inl i =>
          by_cases hij : i=j
          · subst j; simp [Patch.glued,wiring,boundary,active,and_assoc,and_comm]
          · simp [Patch.glued,wiring,boundary,active,hij,and_assoc,and_left_comm,and_comm]
        | inr v => exact Fin.elim0 v.1
      | succ m =>
        cases v with
        | inl i => simp [Patch.glued,wiring,boundary,active]
        | inr v =>
          rcases v with ⟨k,i,a⟩
          induction k using Fin.cases with
          | zero =>
            by_cases hij : i=j
            · subst j; simp [Patch.glued,wiring,boundary,active,and_assoc,and_left_comm,and_comm]
            · simp [Patch.glued,wiring,boundary,active,hij,and_assoc,and_left_comm,and_comm]
          | succ k => simp [Patch.glued,wiring,boundary,active]
  | inr v =>
    rcases v with ⟨i,a⟩
    cases w with
    | inl w =>
      cases m with
      | zero =>
        cases w with
        | inl j =>
          by_cases hij : i=j
          · subst j; simp [Patch.glued,wiring,boundary,active,and_assoc,and_comm]
          · simp [Patch.glued,wiring,boundary,active,Ne.symm hij,and_assoc,and_left_comm,and_comm]
        | inr w => exact Fin.elim0 w.1
      | succ m =>
        cases w with
        | inl j => simp [Patch.glued,wiring,boundary,active]
        | inr w =>
          rcases w with ⟨l,j,b⟩
          induction l using Fin.cases with
          | zero =>
            by_cases hij : i=j
            · subst j; simp [Patch.glued,wiring,boundary,active,and_assoc,and_left_comm,and_comm]
            · simp [Patch.glued,wiring,boundary,active,hij,Ne.symm hij,and_assoc,and_left_comm,and_comm]
          | succ l =>
            have hh : (0 : Fin (m+2))≠l.succ.succ := Ne.symm (Fin.succ_ne_zero _)
            simp [Patch.glued,wiring,boundary,active,hh]
    | inr w =>
      rcases w with ⟨j,b⟩
      simp [Patch.glued,wiring,addColumn,BareColumn]

 

def flatten : (ts : List (Configuration n)) → ColumnChain.Vertices ts ≃ V n ts.length
  | [] => (Equiv.sumEmpty (Fin n) (Fin 0 × Vertex n)).symm
  | _::ts => (Equiv.sumCongr (flatten ts) (Equiv.refl (Vertex n))).trans
      (addColumn n ts.length)

def entries : (ts : List (Configuration n)) → Fin ts.length → Configuration n
  | [] => Fin.elim0
  | t::ts => Fin.cons t (entries ts)

lemma ofFn_entries (ts : List (Configuration n)) : List.ofFn (entries ts)=ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [entries,List.ofFn_cons,ih]

lemma flatten_boundary (ts : List (Configuration n)) (i : Fin n) :
    flatten ts (ColumnChain.boundary ts i)=boundary ts.length i := by
  cases ts <;> rfl

lemma active_entries (p : Pairing n) (ts : List (Configuration n)) :
    active p (entries ts)=ColumnChain.support p ts := by
  cases ts <;> rfl

lemma flatten_wiring (p : Pairing n) (ts : List (Configuration n))
    (v w : ColumnChain.Vertices ts) : ColumnChain.wiring p ts v w ↔
      wiring p (entries ts) (flatten ts v) (flatten ts w) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    change Patch.glued (ColumnChain.wiring p ts) (BareColumn t) (ColumnChain.boundary ts)
        (fun i=>(i,1)) (ColumnChain.support p ts) v w ↔ _
    change _ ↔ wiring p (Fin.cons t (entries ts))
      (addColumn n ts.length ((Equiv.sumCongr (flatten ts) (Equiv.refl (Vertex n))) v))
      (addColumn n ts.length ((Equiv.sumCongr (flatten ts) (Equiv.refl (Vertex n))) w))
    rw [←wiring_step]
    cases v with
    | inl v =>
      cases w with
      | inl w => exact ih v w
      | inr w =>
        simp only [Patch.glued,Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr,
          Equiv.refl_apply,active_entries,←flatten_boundary,Equiv.apply_eq_iff_eq]
    | inr v =>
      cases w with
      | inl w =>
        simp only [Patch.glued,Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr,
          Equiv.refl_apply,active_entries,←flatten_boundary,Equiv.apply_eq_iff_eq]
      | inr w => rfl

def boundaryEquiv (p : Pairing n) (ts : List (Configuration n)) :
    Graph.BoundaryEquiv (ColumnChain.wiring p ts) (wiring p (entries ts))
      (ColumnChain.boundary ts) (boundary ts.length) :=
  Graph.BoundaryEquiv.ofEquiv (flatten ts) (flatten_wiring p ts) (flatten_boundary ts)

lemma runs_iff (hn : 0<n) (p : Pairing n) (ts : List (Configuration n)) (q : Pairing n) :
    ColumnChain.Runs p ts q ↔ ColumnChain.Compatible p ts ∧
      GraphRealizes (wiring p (entries ts)) (boundary ts.length) q := by
  rw [ColumnChain.runs_iff hn,(boundaryEquiv p ts).realizes_iff]

end ColumnRectangle
end
end CriticalStrip.Diagram

end OAI
