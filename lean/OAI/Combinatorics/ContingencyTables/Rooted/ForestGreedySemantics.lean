import OAI.Combinatorics.ContingencyTables.Rooted.ForestGreedyProgram
import OAI.Combinatorics.ContingencyTables.Rooted.MaximumForestExchange

namespace OAI

/-! # Correctness of the actual binary forest loop

The invariant refers to the adjacency list produced by the program.
The final graph is decoded directly from that list. Optimal forests
occur only as proof witnesses for the safe-edge invariant.
-/

namespace ContingencyTables.ForestGreedySemantics

open SimpleGraph MaximumForest MaximumForestExchange
open ForestGreedyProgram ForestEdgeChoiceProgram FiniteGraphRootProgram WeightedArgmaxProgram
open scoped Classical

variable {n : ℕ}

/-- Every stored edge is valid, and every graph edge is stored in at least
one orientation with its exact capacity. -/
def Catalog (G : SimpleGraph (Fin n)) (b : Sym2 (Fin n)→ℕ) (es : List Edge) : Prop :=
  (∀ e∈es,∃ u v : Fin n,G.Adj u v ∧ e=((u.val,v.val),b s(u,v))) ∧
  (∀ u v,G.Adj u v →
    ((u.val,v.val),b s(u,v))∈es ∨ ((v.val,u.val),b s(u,v))∈es)

lemma chosen_spec {G T : SimpleGraph (Fin n)} {b : Sym2 (Fin n)→ℕ} {es : List Edge}
    (hC : Catalog G b es) {e : Edge} (he : choice (graphCode T,es)=some e) :
    ∃ u v : Fin n,e=((u.val,v.val),b s(u,v)) ∧ G.Adj u v ∧ ¬T.Reachable u v ∧
      ∀ a d,G.Adj a d → ¬T.Reachable a d → b s(a,d)≤b s(u,v) := by
  have hm := choice_mem he
  obtain ⟨u,v,hG,heq⟩ := hC.1 e hm.1
  subst e
  have hnu : ¬T.Reachable u v := (eligible_code T es u v _).mp hm.2
  refine ⟨u,v,rfl,hG,hnu,?_⟩
  intro a d had hn
  rcases hC.2 a d had with hmem|hmem
  · exact choice_max he hmem ((eligible_code T es a d _).mpr hn)
  · exact choice_max he hmem ((eligible_code T es d a _).mpr (fun hd=>hn hd.symm))

lemma none_spec {G T : SimpleGraph (Fin n)} {b : Sym2 (Fin n)→ℕ} {es : List Edge}
    (hC : Catalog G b es) (he : choice (graphCode T,es)=none) :
    ∀ u v,G.Adj u v → T.Reachable u v := by
  intro u v hG
  by_contra hn
  rcases hC.2 u v hG with hmem|hmem
  · have hfalse := choice_none he _ hmem
    have htrue := (eligible_code T es u v (b s(u,v))).mpr hn
    exact Bool.noConfusion (hfalse.symm.trans htrue)
  · have hfalse := choice_none he _ hmem
    have htrue := (eligible_code T es v u (b s(u,v))).mpr (fun hr=>hn hr.symm)
    exact Bool.noConfusion (hfalse.symm.trans htrue)

def iterate : ℕ→State→State
  | 0,s=>s
  | k+1,s=>iterate k (ForestGreedyProgram.advance (0,s))

lemma fold_eq_iterate (xs : List ℕ) (s : State) :
    xs.foldl (fun s a=>ForestGreedyProgram.advance (a,s)) s=iterate xs.length s := by
  induction xs generalizing s with
  | nil=>rfl
  | cons a xs ih=>simpa only [List.foldl_cons,List.length_cons,iterate,ForestGreedyProgram.advance] using ih (ForestGreedyProgram.advance (a,s))

lemma execute_iterate (s : State) : execute s=iterate (s.1.length*s.1.length) s := by
  simpa only [execute,slots,List.length_range] using fold_eq_iterate (slots s) s

lemma advance_none {s : State} (he : choice s=none) : ForestGreedyProgram.advance (0,s)=s := by
  simp only [ForestGreedyProgram.advance,update,he,Option.elim_none]

lemma iterate_none {s : State} (he : choice s=none) (k : ℕ) : iterate k s=s := by
  induction k with
  | zero=>rfl
  | succ k ih=>simpa only [iterate,advance_none he] using ih

lemma advance_code (T : SimpleGraph (Fin n)) (es : List Edge) (u v : Fin n)
    (w : ℕ) (hne : u≠v)
    (he : choice (graphCode T,es)=some ((u.val,v.val),w)) :
    ForestGreedyProgram.advance (0,(graphCode T,es))=(graphCode (T⊔edge u v),es) := by
  simp only [ForestGreedyProgram.advance,update,he,Option.elim_some]
  change (ForestJoinProgram.join (graphCode T,(u.val,v.val)),es)=_
  rw [ForestJoinProgram.join_code T u v hne]

private noncomputable def edgeCount (G : SimpleGraph (Fin n)) : ℕ := G.edgeFinset.card

private lemma edgeCount_le (G : SimpleGraph (Fin n)) :
    edgeCount G≤Fintype.card (Sym2 (Fin n)) := Finset.card_le_univ _

private lemma card_add (T : SimpleGraph (Fin n)) {u v : Fin n}
    (hn : ¬T.Reachable u v) (huv : u≠v) :
    edgeCount (T⊔edge u v)=edgeCount T+1 := by
  have h := T.card_edgeFinset_sup_edge (fun ht=>hn ht.reachable) huv
  unfold edgeCount
  convert h using 1
  congr 1
  ext a
  simp only [mem_edgeFinset]

/-- A fuel count at least the number of missing unordered edges suffices
for the executed loop, without any tie-breaking assumption. -/
theorem iterate_optimal (G T : SimpleGraph (Fin n)) (b : Sym2 (Fin n)→ℕ)
    (es : List Edge) (hC : Catalog G b es) (hb : ∀ e∈G.edgeSet,0<b e)
    (hT : Extendible G T b) (k : ℕ)
    (hbudget : Fintype.card (Sym2 (Fin n))≤edgeCount T+k) :
    ∃ F : SimpleGraph (Fin n),iterate k (graphCode T,es)=(graphCode F,es) ∧
      F≤G ∧ F.IsAcyclic ∧
        ∀ H : SimpleGraph (Fin n),H≤G → H.IsAcyclic → weight H b≤weight F b := by
  induction k generalizing T with
  | zero=>
    have hnone : choice (graphCode T,es)=none := by
      cases he : choice (graphCode T,es) with
      | none=>rfl
      | some e=>
        obtain ⟨u,v,_,hg,hn,_⟩ := chosen_spec hC he
        have hc := card_add T hn hg.ne
        have hle := edgeCount_le (T⊔edge u v)
        omega
    exact ⟨T,rfl,finished G T b hT (none_spec hC hnone)⟩
  | succ k ih=>
    cases he : choice (graphCode T,es) with
    | none=>exact ⟨T,iterate_none he _,finished G T b hT (none_spec hC he)⟩
    | some e=>
      obtain ⟨u,v,rfl,hg,hn,hbest⟩ := chosen_spec hC he
      have hnext := safe_edge G T b hb hT hg hn hbest
      have hc := card_add T hn hg.ne
      obtain ⟨F,hF,hopt⟩ := ih (T⊔edge u v) hnext (by omega)
      refine ⟨F,?_,hopt⟩
      rw [iterate,advance_code T es u v _ hg.ne he]
      convert hF using 1
      congr 3

def decoded (g : GraphCode) : SimpleGraph (Fin n) where
  Adj u v := u≠v ∧ u.val∈g.getD v.val [] ∧ v.val∈g.getD u.val []
  symm := ⟨by intro u v h; exact ⟨Ne.symm h.1,h.2.2,h.2.1⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

lemma decoded_graphCode (G : SimpleGraph (Fin n)) : decoded (graphCode G)=G := by
  ext u v
  simp only [decoded,graphCode_getD,adjacencyRow_mem]
  constructor
  · rintro ⟨_,⟨a,ha,haG⟩,_⟩
    exact (Fin.ext ha) ▸ haG
  · intro h
    exact ⟨h.ne,⟨u,rfl,h⟩,⟨v,rfl,h.symm⟩⟩

lemma unordered_pair_budget : Fintype.card (Sym2 (Fin n))≤n*n := by
  have hs : Function.Surjective (fun p : Fin n×Fin n=>s(p.1,p.2)) := by
    intro e
    induction e using Sym2.inductionOn with
    | _ u v=>exact ⟨(u,v),rfl⟩
  simpa only [Fintype.card_prod,Fintype.card_fin] using Fintype.card_le_of_surjective _ hs

/-- The graph is decoded from the literal result list, not selected from
an existence proof. -/
theorem execute_optimal (G T : SimpleGraph (Fin n)) (b : Sym2 (Fin n)→ℕ)
    (es : List Edge) (hC : Catalog G b es) (hb : ∀ e∈G.edgeSet,0<b e)
    (hT : Extendible G T b) :
    let F := decoded (execute (graphCode T,es)).1
    F≤G ∧ F.IsAcyclic ∧
      ∀ H : SimpleGraph (Fin n),H≤G → H.IsAcyclic → weight H b≤weight F b := by
  obtain ⟨F,hF,hopt⟩ := iterate_optimal G T b es hC hb hT (n*n)
    (by have h := unordered_pair_budget (n:=n); omega)
  rw [execute_iterate,graphCode_length,hF]
  simpa only [decoded_graphCode] using hopt

end ContingencyTables.ForestGreedySemantics

end OAI
