import Mathlib
import OAI.Probability.CriticalPercolation.Model

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation

inductive SearchTree (E R : Type*) where
  | done (r : R)
  | ask (e : E) (left right : SearchTree E R)

namespace SearchTree
variable {E R : Type*}
def run : SearchTree E R → (E → Bool) → R
  | .done r, _ => r
  | .ask e l r, ω => if ω e then run r ω else run l ω

def reads : SearchTree E R → (E → Bool) → List E
  | .done _, _ => []
  | .ask e l r, ω => e :: if ω e then reads r ω else reads l ω

def Valid [DecidableEq E] : SearchTree E R → Finset E → Prop
  | .done _, _ => True
  | .ask e l r, used => e ∉ used ∧ l.Valid (insert e used) ∧ r.Valid (insert e used)

lemma reads_disjoint [DecidableEq E] (t : SearchTree E R) (used : Finset E) (h : t.Valid used)
    (ω : E → Bool) : ∀ e ∈ t.reads ω, e ∉ used := by
  induction t generalizing used with
  | done r => simp [reads]
  | ask e l r hl hr =>
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact h.1
    · by_cases he : ω e = true
      · have hm : f ∈ r.reads ω := by simpa [reads,he] using hf
        exact fun hx => hr _ h.2.2 _ hm (Finset.mem_insert_of_mem hx)
      · have hm : f ∈ l.reads ω := by simpa [reads,he] using hf
        exact fun hx => hl _ h.2.1 _ hm (Finset.mem_insert_of_mem hx)

lemma reads_nodup [DecidableEq E] (t : SearchTree E R) (used : Finset E) (h : t.Valid used)
    (ω : E → Bool) : (t.reads ω).Nodup := by
  induction t generalizing used with
  | done r => simp [reads]
  | ask e l r hl hr =>
    rw [reads,List.nodup_cons]
    by_cases he : ω e = true
    · simp only [he,↓reduceIte]
      exact ⟨fun hm => reads_disjoint r _ h.2.2 ω e hm (Finset.mem_insert_self _ _), hr _ h.2.2⟩
    · simp only [he]
      exact ⟨fun hm => reads_disjoint l _ h.2.1 ω e hm (Finset.mem_insert_self _ _), hl _ h.2.1⟩
end SearchTree

namespace LazyDFS
variable {V E : Type*} [DecidableEq V] [DecidableEq E]

abbrev Dart (V E : Type*) := V × E × V

structure State (V E : Type*) where
  reached : Finset V
  read : Finset E

def State.closed (s : State V E) (e : E) : State V E := ⟨s.reached,insert e s.read⟩
def State.opened (s : State V E) (e : E) (v : V) : State V E :=
  ⟨insert v s.reached,insert e s.read⟩

def push (G : BondGraph V E) (order : List (Dart V E)) (v : V) : List (Dart V E) :=
  order.filter fun d => d.1 = v ∧ G.ends d.2.1 = s(d.1,d.2.2)

omit [DecidableEq E] in
lemma push_length (G : BondGraph V E) (order : List (Dart V E)) (v : V) :
    (push G order v).length ≤ order.length := List.length_filter_le _ _

noncomputable def compile (G : BondGraph V E) (order : List (Dart V E)) (B : Set V) :
    ℕ → State V E → List (Dart V E) → SearchTree E (State V E)
  | 0, st, _ => .done st
  | n+1, st, stack =>
    if ∃ v ∈ st.reached, v ∈ B then .done st else
    match stack with
    | [] => .done st
    | d :: rest =>
      if d.2.2 ∈ st.reached ∨ d.2.1 ∈ st.read ∨ d.1 ∉ st.reached ∨
        G.ends d.2.1 ≠ s(d.1,d.2.2) then compile G order B n st rest else
      .ask d.2.1 (compile G order B n (st.closed d.2.1) rest)
        (compile G order B n (st.opened d.2.1 d.2.2) (push G order d.2.2 ++ rest))

lemma compile_valid (G : BondGraph V E) (order : List (Dart V E)) (B : Set V)
    (fuel : ℕ) (st : State V E) (stack : List (Dart V E)) :
    (compile G order B fuel st stack).Valid st.read := by
  induction fuel generalizing st stack with
  | zero => trivial
  | succ n ih =>
    rw [compile.eq_def]
    dsimp only
    split_ifs with hh
    · trivial
    · cases stack with
      | nil => trivial
      | cons d rest =>
        dsimp only
        split_ifs with hd
        · exact ih st rest
        · exact ⟨fun he => hd (Or.inr (Or.inl he)), ih _ _, ih _ _⟩

variable [Fintype V]

def rank (order : List (Dart V E)) (st : State V E) (stack : List (Dart V E)) : ℕ :=
  (Fintype.card V - st.reached.card)*(order.length+1)+stack.length

omit [DecidableEq V] [DecidableEq E] in
lemma rank_pop (order : List (Dart V E)) (st : State V E) (d : Dart V E) (rest : List (Dart V E)) :
    rank order st rest < rank order st (d::rest) := by simp [rank]

omit [DecidableEq V] in
lemma rank_closed (order : List (Dart V E)) (st : State V E) (d : Dart V E) (rest : List (Dart V E)) :
    rank order (st.closed d.2.1) rest < rank order st (d::rest) := by simp [rank,State.closed]

lemma rank_opened (G : BondGraph V E) (order : List (Dart V E)) (st : State V E)
    (d : Dart V E) (rest : List (Dart V E)) (h : d.2.2 ∉ st.reached) :
    rank order (st.opened d.2.1 d.2.2) (push G order d.2.2 ++ rest) <
      rank order st (d::rest) := by
  have hc : st.reached.card < Fintype.card V := by
    have hh := Finset.card_le_univ (s := insert d.2.2 st.reached)
    rw [Finset.card_insert_of_notMem h] at hh
    omega
  have hp := push_length G order d.2.2
  simp only [rank,State.opened,Finset.card_insert_of_notMem h,List.length_append,List.length_cons]
  have he : Fintype.card V - (st.reached.card+1) + 1 = Fintype.card V-st.reached.card := by omega
  have hm := congrArg (fun n => n*(order.length+1)) he
  simp only [Nat.add_mul,Nat.one_mul] at hm
  omega

omit [Fintype V] in

lemma compile_mono (G : BondGraph V E) (order : List (Dart V E)) (B : Set V)
    (fuel : ℕ) (st : State V E) (stack : List (Dart V E)) (ω : E → Bool) :
    st.reached ⊆ ((compile G order B fuel st stack).run ω).reached ∧
    st.read ⊆ ((compile G order B fuel st stack).run ω).read := by
  induction fuel generalizing st stack with
  | zero => exact ⟨Finset.Subset.refl _,Finset.Subset.refl _⟩
  | succ n ih =>
    rw [compile.eq_def]
    dsimp only
    split_ifs with hh
    · exact ⟨Finset.Subset.refl _,Finset.Subset.refl _⟩
    · cases stack with
      | nil => exact ⟨Finset.Subset.refl _,Finset.Subset.refl _⟩
      | cons d rest =>
        dsimp only
        split_ifs with hd
        · exact ih _ _
        · rw [SearchTree.run]
          split_ifs with he
          · exact ⟨(Finset.subset_insert _ _).trans (ih (st.opened d.2.1 d.2.2) _).1,
              (Finset.subset_insert d.2.1 _).trans (ih (st.opened d.2.1 d.2.2) _).2⟩
          · exact ⟨(ih (st.closed d.2.1) rest).1,
              (Finset.subset_insert d.2.1 _).trans (ih (st.closed d.2.1) rest).2⟩

end LazyDFS
end CriticalPercolation

end
end

end OAI
