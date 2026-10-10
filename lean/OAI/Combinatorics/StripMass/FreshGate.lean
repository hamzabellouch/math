import Mathlib
import OAI.Combinatorics.StripMass.WireContraction

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical
namespace FreshGate
variable {V : Type*} {n : ℕ}

 
structure Ports (r : V → V → Prop) (old : Fin n → V) where
  port : Fin 4 → V
  select : V → Option (Fin 4)
  select_port : ∀ k, select (port k)=some k
  of_some : ∀ v k, select v=some k → v=port k
  old_none : ∀ i, select (old i)=none
  edge_none : ∀ v w, r v w → select v=none

namespace Ports
variable {r : V → V → Prop} {old : Fin n → V} (f : Ports r old)

def project : Sum V (Fin 4) → V
  | .inl v => v
  | .inr k => f.port k

def core (v : V) : Sum V (Fin 4) :=
  match f.select v with | none => .inl v | some k => .inr k

@[simp] theorem project_core (v : V) : f.project (f.core v)=v := by
  cases h : f.select v with
  | none => simp [core,h,project]
  | some k => simpa [core,h,project] using (f.of_some v k h).symm

@[simp] theorem core_port (k : Fin 4) : f.core (f.port k)=.inr k := by simp [core,f.select_port]
@[simp] theorem core_old (i : Fin n) : f.core (old i)=.inl (old i) := by simp [core,f.old_none]

def boundary (a b : Fin n) (i : Fin n) : V := f.project (CompactGate.boundary old a b i)

def wiring (active : Fin n → Prop) (a b : Fin n) (t : Tile) (v w : V) : Prop :=
  CompactGate.wiring r old active a b t (f.core v) (f.core w)

lemma core_boundary (a b i : Fin n) : f.core (f.boundary a b i)=CompactGate.boundary old a b i := by
  by_cases hia : i=a <;> by_cases hib : i=b <;>
    simp_all [boundary,CompactGate.boundary,project]

lemma core_project_used (active : Fin n → Prop) (a b : Fin n) (t : Tile)
    (v : Sum V (Fin 4)) (hv : Graph.Used (CompactGate.wiring r old active a b t) v) :
    f.core (f.project v)=v := by
  cases v with
  | inr k => exact f.core_port k
  | inl v =>
    have hn : f.select v=none := by
      obtain ⟨w,hw⟩ := hv
      cases w with
      | inl w => exact f.edge_none v w hw
      | inr k =>
        rcases hw with ⟨rfl,_,_⟩ | ⟨rfl,_,_⟩ <;> exact f.old_none _
    simp [project,core,hn]

instance wiring_symm [Std.Symm r] (active : Fin n → Prop) (a b : Fin n) (t : Tile) :
    Std.Symm (f.wiring active a b t) := by
  constructor
  intro v w h
  change CompactGate.wiring r old active a b t (f.core v) (f.core w) at h
  change CompactGate.wiring r old active a b t (f.core w) (f.core v)
  exact symm h

 def contraction [Std.Symm r] (hinj : Function.Injective old)
    (active : Fin n → Prop) (a b : Fin n) (t : Tile) :
    Graph.WireContraction (CompactGate.wiring r old active a b t)
      (f.wiring active a b t) (CompactGate.boundary old a b) (f.boundary a b) where
  project := f.project
  core := f.core
  section_eq := f.project_core
  map_edge := by
    intro v w h
    apply Relation.ReflTransGen.single
    change CompactGate.wiring r old active a b t (f.core (f.project v)) (f.core (f.project w))
    rw [f.core_project_used active a b t v ⟨w,h⟩,
      f.core_project_used active a b t w ⟨v,symm h⟩]
    exact h
  core_edge := fun _ _ h => h
  map_boundary := fun _ => rfl
  boundary_injective := by
    intro i j hij
    apply CompactGate.boundary_injective old hinj a b
    have he := congrArg f.core hij
    simpa only [f.core_boundary] using he
  map_used := by
    intro v ⟨w,h⟩
    refine ⟨f.project w,?_⟩
    change CompactGate.wiring r old active a b t (f.core (f.project v)) (f.core (f.project w))
    rw [f.core_project_used active a b t v ⟨w,h⟩,
      f.core_project_used active a b t w ⟨v,symm h⟩]
    exact h
  retract := by
    intro v hv
    rw [f.core_project_used active a b t v hv]
  boundary_retract := by
    intro i _
    rw [f.core_boundary]

 theorem realizes_iff [Std.Symm r] (hinj : Function.Injective old)
    (active : Fin n → Prop) (a b : Fin n) (t : Tile) (q : Pairing n) :
    GraphRealizes (CompactGate.wiring r old active a b t) (CompactGate.boundary old a b) q ↔
      GraphRealizes (f.wiring active a b t) (f.boundary a b) q :=
  (f.contraction hinj active a b t).realizes_iff

end Ports
end FreshGate
namespace PartialColumn

abbrev V (n : ℕ) := Sum (Fin (n+1)) (Vertex n)

def wiring {n : ℕ} (p : Pairing n) (t : Configuration n) (k : ℕ) : V n → V n → Prop
  | .inl i, .inl j => p.padBottom.Adj i j
  | .inl i, .inr (j,a) | .inr (j,a), .inl i =>
      j.val<k ∧ i=j.succ ∧ a=1 ∧ p.Occupied j
  | .inr (i,a), .inr (j,b) =>
      (i=j ∧ i.val<k ∧ (t i).Adj a b) ∨
      (a=3 ∧ b=0 ∧ i.val+1=j.val ∧ j.val<k ∧ (t i).Occupied 3) ∨
      (b=3 ∧ a=0 ∧ j.val+1=i.val ∧ i.val<k ∧ (t j).Occupied 3)

def boundary {n : ℕ} (k : ℕ) (hk : k≤n) (i : Fin (n+1)) : V n :=
  if hi : i.val<k then .inr (⟨i.val,lt_of_lt_of_le hi hk⟩,2)
  else if h : i.val=k ∧ 0<k then .inr (⟨k-1,by omega⟩,3)
  else .inl i

def support {n : ℕ} (p : Pairing n) (t : Configuration n) (k : ℕ) (hk : k≤n)
    (i : Fin (n+1)) : Prop :=
  if hi : i.val<k then (t ⟨i.val,lt_of_lt_of_le hi hk⟩).Occupied 2
  else if h : i.val=k ∧ 0<k then (t ⟨k-1,by omega⟩).Occupied 3
  else p.padBottom.Occupied i

@[simp] theorem boundary_zero {n : ℕ} (i : Fin (n+1)) : boundary 0 (Nat.zero_le n) i=.inl i := by
  simp [boundary]
@[simp] theorem support_zero {n : ℕ} (p : Pairing n) (t : Configuration n) (i : Fin (n+1)) :
    support p t 0 (Nat.zero_le n) i ↔ p.padBottom.Occupied i := by simp [support]

instance wiring_symm {n : ℕ} (p : Pairing n) (t : Configuration n) (k : ℕ) :
    Std.Symm (wiring p t k) := by
  constructor
  rintro (i|⟨i,a⟩) (j|⟨j,b⟩) h
  · exact Pairing.adj_symm h
  · exact h
  · exact h
  · rcases h with ⟨rfl,hi,hab⟩ | h | h
    · exact Or.inl ⟨rfl,hi,hab.elim Or.inr Or.inl⟩
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)

 theorem boundary_injective {n : ℕ} (k : ℕ) (hk : k≤n) : Function.Injective (boundary k hk) := by
  intro i j hij
  apply Fin.ext
  by_cases hi : i.val<k <;> by_cases hj : j.val<k <;>
    by_cases hi' : i.val=k ∧ 0<k <;> by_cases hj' : j.val=k ∧ 0<k <;>
    simp_all [boundary]

 def select {n : ℕ} (row : Fin n) : V n → Option (Fin 4)
  | .inl _ => none
  | .inr (i,a) => if i=row then some a else none

 def ports {n : ℕ} (p : Pairing n) (t : Configuration n) (row : Fin n) :
    FreshGate.Ports (wiring p t row.val) (boundary row.val (Nat.le_of_lt row.isLt)) where
  port := fun a => .inr (row,a)
  select := select row
  select_port := fun a => by simp [select]
  of_some := by
    rintro (i|⟨i,a⟩) b h
    · simp [select] at h
    · by_cases hi : i=row
      · subst i; simpa [select] using h
      · simp [select,hi] at h
  old_none := by
    intro i
    by_cases hi : i.val<row.val
    · simp only [boundary,dite_eq_left hi,select]
      apply ite_eq_right
      intro he
      have hh := congrArg Fin.val he
      dsimp at hh
      omega
    · by_cases hh : i.val=row.val ∧ 0<row.val
      · simp only [boundary,dite_eq_right hi,dite_eq_left hh,select]
        apply ite_eq_right
        intro he
        have hh := congrArg Fin.val he
        dsimp at hh
        omega
      · simp [boundary,hi,hh,select]
  edge_none := by
    rintro (i|⟨i,a⟩) (j|⟨j,b⟩) h
    · rfl
    · rfl
    · have hi := h.1
      simp only [select]
      apply ite_eq_right
      intro he; subst i; omega
    · have hi : i.val<row.val := by
        rcases h with ⟨_,hi,_⟩ | ⟨_,_,hij,hj,_⟩ | ⟨_,_,_,hi,_⟩ <;> omega
      simp only [select]
      apply ite_eq_right
      intro he; subst i; omega

section RowTransitions
variable {n : ℕ} (p : Pairing n) (t : Configuration n) (row : Fin n)

 def prev (h : 0<row.val) : Fin n := ⟨row.val-1,by omega⟩

@[simp] lemma right_boundary : boundary row.val (Nat.le_of_lt row.isLt) row.succ = .inl row.succ := by
  simp [boundary]

lemma left_boundary_zero (h : row.val=0) :
    boundary row.val (Nat.le_of_lt row.isLt) row.castSucc = .inl row.castSucc := by
  simp [boundary,h]

lemma left_boundary_pos (h : 0<row.val) :
    boundary row.val (Nat.le_of_lt row.isLt) row.castSucc = .inr (prev row h,3) := by
  simp [boundary,h,prev]

@[simp] lemma right_support : support p t row.val (Nat.le_of_lt row.isLt) row.succ ↔ p.Occupied row := by
  simp [support]

lemma left_support_zero (h : row.val=0) :
    ¬support p t row.val (Nat.le_of_lt row.isLt) row.castSucc := by
  have hh : row.castSucc=(0:Fin (n+1)) := Fin.ext h
  simp [support,h,hh]

lemma left_support_pos (h : 0<row.val) :
    support p t row.val (Nat.le_of_lt row.isLt) row.castSucc ↔ (t (prev row h)).Occupied 3 := by
  simp [support,h,prev]

lemma boundary_step (i : Fin (n+1)) :
    (ports p t row).boundary row.castSucc row.succ i = boundary (row.val+1) row.isLt i := by
  have ha : row.castSucc≠row.succ := by intro hh; have he := congrArg Fin.val hh; dsimp at he; omega
  by_cases hia : i=row.castSucc
  · subst i
    simp [FreshGate.Ports.boundary,CompactGate.boundary,FreshGate.Ports.project,ports,boundary]
  · by_cases hib : i=row.succ
    · subst i
      simp [FreshGate.Ports.boundary,CompactGate.boundary,FreshGate.Ports.project,ports,boundary,ha.symm]
    · have hia' : i.val≠row.val := fun h => hia (Fin.ext h)
      have hib' : i.val≠row.val+1 := fun h => hib (Fin.ext h)
      have hlt : i.val<row.val+1 ↔ i.val<row.val := by omega
      have hp : ¬(i.val=row.val ∧ 0<row.val) := by omega
      have hp' : ¬(i.val=row.val+1 ∧ 0<row.val+1) := by omega
      simp only [FreshGate.Ports.boundary,CompactGate.boundary,ite_eq_right hia,ite_eq_right hib,
        FreshGate.Ports.project,boundary,hlt]
      by_cases hi : i.val<row.val <;> simp [hi,hia',hib']

lemma support_step (i : Fin (n+1)) :
    (if i=row.castSucc then (t row).Occupied 2 else
       if i=row.succ then (t row).Occupied 3 else support p t row.val (Nat.le_of_lt row.isLt) i) ↔
      support p t (row.val+1) row.isLt i := by
  have ha : row.castSucc≠row.succ := by intro hh; have he := congrArg Fin.val hh; dsimp at he; omega
  by_cases hia : i=row.castSucc
  · subst i; simp [support]
  · by_cases hib : i=row.succ
    · subst i; simp [support,ha.symm]
    · have hia' : i.val≠row.val := fun h => hia (Fin.ext h)
      have hib' : i.val≠row.val+1 := fun h => hib (Fin.ext h)
      have hlt : i.val<row.val+1 ↔ i.val<row.val := by omega
      have hp : ¬(i.val=row.val ∧ 0<row.val) := by omega
      have hp' : ¬(i.val=row.val+1 ∧ 0<row.val+1) := by omega
      simp only [ite_eq_right hia,ite_eq_right hib,support,hlt]
      by_cases hi : i.val<row.val <;> simp [hi,hia',hib']

lemma core_initial (i : Fin (n+1)) : (ports p t row).core (.inl i)=.inl (.inl i) := rfl
lemma core_box (i : Fin n) (a : Fin 4) : (ports p t row).core (.inr (i,a))=
    if i=row then .inr a else .inl (.inr (i,a)) := by
  by_cases hi : i=row <;> simp [FreshGate.Ports.core,ports,select,hi]

 abbrev nextWiring := (ports p t row).wiring (support p t row.val (Nat.le_of_lt row.isLt))
  row.castSucc row.succ (t row)

lemma next_initial (i j : Fin (n+1)) :
    nextWiring p t row (.inl i) (.inl j) ↔ wiring p t (row.val+1) (.inl i) (.inl j) := by
  rfl

lemma next_mixed (i : Fin (n+1)) (j : Fin n) (b : Fin 4) :
    nextWiring p t row (.inl i) (.inr (j,b)) ↔ wiring p t (row.val+1) (.inl i) (.inr (j,b)) := by
  by_cases hj : j=row
  · subst j
    simp only [nextWiring,FreshGate.Ports.wiring,core_initial,core_box,CompactGate.wiring]
    rw [right_boundary,right_support]
    by_cases hrow : row.val=0
    · rw [left_boundary_zero row hrow]
      simp [left_support_zero p t row hrow,wiring]
    · rw [left_boundary_pos row (by omega),left_support_pos p t row (by omega)]
      simp [wiring]
  · have hlt : j.val<row.val+1 ↔ j.val<row.val := by
      have hne : j.val≠row.val := fun he => hj (Fin.ext he)
      omega
    simp [nextWiring,FreshGate.Ports.wiring,core_initial,core_box,hj,CompactGate.wiring,wiring,hlt]

lemma prev_val_add (h : 0<row.val) : (prev row h).val+1=row.val := by
  simp only [prev]
  omega

lemma next_new_new (a b : Fin 4) :
    nextWiring p t row (.inr (row,a)) (.inr (row,b)) ↔
      wiring p t (row.val+1) (.inr (row,a)) (.inr (row,b)) := by
  simp [nextWiring,FreshGate.Ports.wiring,core_box,CompactGate.wiring,wiring]

lemma next_new_old (j : Fin n) (hj : j≠row) (a b : Fin 4) :
    nextWiring p t row (.inr (row,a)) (.inr (j,b)) ↔
      wiring p t (row.val+1) (.inr (row,a)) (.inr (j,b)) := by
  simp only [nextWiring,FreshGate.Ports.wiring,core_box,ite_eq_right hj,CompactGate.wiring]
  rw [right_boundary]
  have hforward : ¬(row.val+1=j.val ∧ j.val<row.val+1) := by omega
  by_cases hrow : row.val=0
  · rw [left_boundary_zero row hrow]
    simp [wiring,hj.symm,hrow]
    omega
  · have hpos : 0<row.val := by omega
    rw [left_boundary_pos row hpos,left_support_pos p t row hpos]
    by_cases he : j=prev row hpos
    · subst j
      have hback := prev_val_add row hpos
      have hf : ¬(row.val+1=(prev row hpos).val) := by omega
      simp [wiring,hj.symm,hback,hf,and_comm,and_left_comm]
    · have hb : ¬(j.val+1=row.val) := by
        intro hh
        apply he
        apply Fin.ext
        simp only [prev]
        omega
      simp [wiring,hj.symm,hb]
      omega

lemma next_old_old (i j : Fin n) (hi : i≠row) (hj : j≠row) (a b : Fin 4) :
    nextWiring p t row (.inr (i,a)) (.inr (j,b)) ↔
      wiring p t (row.val+1) (.inr (i,a)) (.inr (j,b)) := by
  have hi' : i.val≠row.val := fun he => hi (Fin.ext he)
  have hj' : j.val≠row.val := fun he => hj (Fin.ext he)
  have hli : i.val<row.val+1 ↔ i.val<row.val := by omega
  have hlj : j.val<row.val+1 ↔ j.val<row.val := by omega
  simp [nextWiring,FreshGate.Ports.wiring,core_box,hi,hj,CompactGate.wiring,wiring,hli,hlj]

lemma next_iff (v w : V n) : nextWiring p t row v w ↔ wiring p t (row.val+1) v w := by
  rcases v with i | ⟨i,a⟩ <;> rcases w with j | ⟨j,b⟩
  · exact next_initial p t row i j
  · exact next_mixed p t row i j b
  · constructor
    · intro h; exact symm ((next_mixed p t row j i a).mp (symm h))
    · intro h; exact symm ((next_mixed p t row j i a).mpr (symm h))
  · by_cases hi : i=row
    · subst i
      by_cases hj : j=row
      · subst j; exact next_new_new p t row a b
      · exact next_new_old p t row j hj a b
    · by_cases hj : j=row
      · subst j
        constructor
        · intro h; exact symm ((next_new_old p t row i hi b a).mp (symm h))
        · intro h; exact symm ((next_new_old p t row i hi b a).mpr (symm h))
      · exact next_old_old p t row i j hi hj a b

lemma next_eq : nextWiring p t row = wiring p t (row.val+1) := by
  funext v w
  exact propext (next_iff p t row v w)

end RowTransitions

variable {n : ℕ} (hn : 0<n) (p : Pairing n) (t : Configuration n)

def fullBoundary : Fin (n+1) → Vertex n :=
  Fin.lastCases (⟨n-1,by omega⟩,3) (fun i => (i,2))

def fullProject : V n → Vertex n
  | .inr v => v
  | .inl i => Fin.cases (⟨0,hn⟩,0) (fun j => (j,1)) i

lemma full_box {i j : Fin n} {a b : Fin 4}
    (h : wiring p t n (.inr (i,a)) (.inr (j,b))) : Wiring p t (i,a) (j,b) := by
  rcases h with ⟨hij,_,hab⟩ | ⟨ha,hb,hij,_,ht⟩ | ⟨hb,ha,hij,_,ht⟩
  · exact Or.inl ⟨hij,hab⟩
  · exact Or.inr (Or.inr (Or.inl ⟨ha,hb,hij,ht⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hb,ha,hij,ht⟩))

lemma full_initial_zero (v : V n) : ¬ wiring p t n (.inl 0) v := by
  rcases v with i | ⟨j,a⟩
  · exact p.padBottom_not_adj_zero i
  · rintro ⟨_,he,_,_⟩
    have hh := congrArg Fin.val he
    simp at hh

lemma full_mixed {i : Fin (n+1)} {j : Fin n} {a : Fin 4}
    (h : wiring p t n (.inl i) (.inr (j,a))) :
    fullProject hn (.inl i)=(j,a) ∧ p.Occupied j := by
  obtain ⟨_,rfl,rfl,hp⟩ := h
  exact ⟨rfl,hp⟩

lemma full_map_edge (v w : V n) (h : wiring p t n v w) :
    Reach p t (fullProject hn v) (fullProject hn w) := by
  rcases v with i | ⟨i,a⟩ <;> rcases w with j | ⟨j,b⟩
  · induction i using Fin.cases with
    | zero => exact (p.padBottom_not_adj_zero j h).elim
    | succ i =>
      induction j using Fin.cases with
      | zero => exact (p.padBottom_not_adj_zero' i.succ h).elim
      | succ j => exact .single (Or.inr (Or.inl ⟨rfl,rfl,(p.padBottom_adj_succ i j).mp h⟩))
  · rw [(full_mixed hn p t h).1]; exact .refl
  · have hh := (full_mixed hn p t (symm h)).1
    change Reach p t (i,a) (fullProject hn (.inl j))
    rw [hh]; exact .refl
  · exact .single (full_box p t h)

lemma full_inv_edge (v w : Vertex n) (h : Wiring p t v w) :
    Relation.ReflTransGen (wiring p t n) (.inr v) (.inr w) := by
  rcases v with ⟨i,a⟩; rcases w with ⟨j,b⟩
  rcases h with ⟨hij,hab⟩ | ⟨rfl,rfl,hp⟩ | ⟨ha,hb,hij,ht⟩ | ⟨hb,ha,hij,ht⟩
  · exact .single (Or.inl ⟨hij,i.isLt,hab⟩)
  · have hi : wiring p t n (.inr (i,1)) (.inl i.succ) := ⟨i.isLt,rfl,rfl,⟨j,hp⟩⟩
    have hij : wiring p t n (.inl i.succ) (.inl j.succ) := (p.padBottom_adj_succ i j).mpr hp
    have hj : wiring p t n (.inl j.succ) (.inr (j,1)) := ⟨j.isLt,rfl,rfl,⟨i,Pairing.adj_symm hp⟩⟩
    exact ((Relation.ReflTransGen.single hi).tail hij).tail hj
  · exact .single (Or.inr (Or.inl ⟨ha,hb,hij,j.isLt,ht⟩))
  · exact .single (Or.inr (Or.inr ⟨hb,ha,hij,i.isLt,ht⟩))

lemma full_map_used (v : V n) (h : Graph.Used (wiring p t n) v) :
    Graph.Used (Wiring p t) (fullProject hn v) := by
  obtain ⟨w,hw⟩ := h
  rcases v with i | ⟨i,a⟩ <;> rcases w with j | ⟨j,b⟩
  · induction i using Fin.cases with
    | zero => exact (p.padBottom_not_adj_zero j hw).elim
    | succ i =>
      induction j using Fin.cases with
      | zero => exact (p.padBottom_not_adj_zero' i.succ hw).elim
      | succ j => exact ⟨(j,1),Or.inr (Or.inl ⟨rfl,rfl,(p.padBottom_adj_succ i j).mp hw⟩)⟩
  · obtain ⟨he,k,hpk⟩ := full_mixed hn p t hw
    rw [he]
    obtain ⟨_,rfl,rfl,_⟩ := hw
    exact ⟨(k,1),Or.inr (Or.inl ⟨rfl,rfl,hpk⟩)⟩
  · obtain ⟨_,rfl,rfl,⟨k,hpk⟩⟩ := hw
    exact ⟨(k,1),Or.inr (Or.inl ⟨rfl,rfl,hpk⟩)⟩
  · exact ⟨(j,b),full_box p t hw⟩

lemma full_inv_used (v : Vertex n) (h : Graph.Used (Wiring p t) v) :
    Graph.Used (wiring p t n) (.inr v) := by
  obtain ⟨⟨j,b⟩,hw⟩ := h
  rcases v with ⟨i,a⟩
  rcases hw with ⟨hij,hab⟩ | ⟨rfl,rfl,hp⟩ | ⟨ha,hb,hij,ht⟩ | ⟨hb,ha,hij,ht⟩
  · exact ⟨.inr (j,b),Or.inl ⟨hij,i.isLt,hab⟩⟩
  · exact ⟨.inl i.succ,i.isLt,rfl,rfl,⟨j,hp⟩⟩
  · exact ⟨.inr (j,b),Or.inr (Or.inl ⟨ha,hb,hij,j.isLt,ht⟩)⟩
  · exact ⟨.inr (j,b),Or.inr (Or.inr ⟨hb,ha,hij,i.isLt,ht⟩)⟩

lemma full_boundary (i : Fin (n+1)) : boundary n le_rfl i=.inr (fullBoundary hn i) := by
  induction i using Fin.lastCases with
  | last => simp [boundary,fullBoundary,hn]
  | cast i => simp [boundary,fullBoundary,i.isLt]

lemma full_retract (v : V n) (h : Graph.Used (wiring p t n) v) :
    Relation.ReflTransGen (wiring p t n) v (.inr (fullProject hn v)) := by
  cases v with
  | inr v => exact .refl
  | inl i =>
    induction i using Fin.cases with
    | zero => obtain ⟨w,hw⟩ := h; exact (full_initial_zero p t w hw).elim
    | succ i =>
      have hp : p.Occupied i := by
        obtain ⟨w,hw⟩ := h
        rcases w with j | ⟨j,b⟩
        · exact (p.padBottom_occupied_succ i).mp ⟨j,hw⟩
        · obtain ⟨_,he,rfl,hp⟩ := hw
          have hij : i=j := Fin.succ_injective _ he
          exact hij ▸ hp
      exact .single ⟨i.isLt,rfl,rfl,hp⟩

def fullEquiv : Graph.BoundaryEquiv (wiring p t n) (Wiring p t) (boundary n le_rfl) (fullBoundary hn) where
  toFun := fullProject hn
  invFun := Sum.inr
  map_edge := full_map_edge hn p t
  inv_edge := full_inv_edge p t
  map_boundary := fun i => by rw [full_boundary hn]; rfl
  inv_boundary := fun i => (full_boundary hn i).symm
  map_used := full_map_used hn p t
  inv_used := full_inv_used p t
  retract := full_retract hn p t
  inv_retract := fun _ _ => .refl

end PartialColumn
end
end CriticalStrip.Diagram

end OAI
