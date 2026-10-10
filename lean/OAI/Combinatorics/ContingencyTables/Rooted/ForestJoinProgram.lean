import OAI.Combinatorics.ContingencyTables.Rooted.ForestEdgeChoiceProgram
import OAI.Combinatorics.ContingencyTables.Transport.DirectedBFSCode

namespace OAI

/-! # Canonical adjacency-list insertion of a forest edge

Every row is rebuilt from the stored vertex range. This keeps the graph
encoding canonical and bounds all intermediate lists by the vertex count.
-/

namespace ContingencyTables.ForestJoinProgram

open MatchingFPRAS.TreeTyped Polynomial FiniteGraphRootProgram SimpleGraph

abbrev Input := GraphCode×(ℕ×ℕ)
abbrev RowInput := Input×ℕ
abbrev TestInput := RowInput×ℕ

def keep (z : TestInput) : Bool :=
  decide (z.2∈z.1.1.1.getD z.1.2 []) ||
    ((decide (z.1.2=z.1.1.2.1) && decide (z.2=z.1.1.2.2)) ||
     (decide (z.1.2=z.1.1.2.2) && decide (z.2=z.1.1.2.1)))

def keepRealizer : Realizer keep := by
  let row : Realizer (fun z : TestInput=>z.1.2) := composition first second
  let u : Realizer (fun z : TestInput=>z.1.1.2.1) :=
    composition (composition (composition first first) second) first
  let v : Realizer (fun z : TestInput=>z.1.1.2.2) :=
    composition (composition (composition first first) second) second
  let old : Realizer (fun z : TestInput=>decide (z.2∈z.1.1.1.getD z.1.2 [])) :=
    composition (pair
      (composition (pair (composition (composition first first) first) row) (getDFast []))
      second) membership
  exact composition (pair old
    (composition (pair
      (composition (pair (composition (pair row u) natEqual)
        (composition (pair second v) natEqual)) boolAnd)
      (composition (pair (composition (pair row v) natEqual)
        (composition (pair second u) natEqual)) boolAnd)) boolOr)) boolOr

lemma polynomial_keep : PolynomialTime keepRealizer := by
  unfold keepRealizer
  have hr : PolynomialTime (composition (first (A:=RowInput) (B:=ℕ)) second) :=
    polynomial_composition polynomial_first polynomial_second
  have hu : PolynomialTime (composition (composition
      (composition (first (A:=RowInput) (B:=ℕ)) first) second) first) :=
    polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_first
  have hv : PolynomialTime (composition (composition
      (composition (first (A:=RowInput) (B:=ℕ)) first) second) second) :=
    polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_second
  apply polynomial_composition _ polynomial_boolOr
  apply polynomial_pair
  · exact polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair
        (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
          polynomial_first) hr) (polynomial_getDFast [])) polynomial_second) polynomial_membership
  · apply polynomial_composition _ polynomial_boolOr
    apply polynomial_pair
    · exact polynomial_composition (polynomial_pair
        (polynomial_composition (polynomial_pair hr hu) polynomial_natEqual)
        (polynomial_composition (polynomial_pair polynomial_second hv) polynomial_natEqual))
        polynomial_boolAnd
    · exact polynomial_composition (polynomial_pair
        (polynomial_composition (polynomial_pair hr hv) polynomial_natEqual)
        (polynomial_composition (polynomial_pair polynomial_second hu) polynomial_natEqual))
        polynomial_boolAnd

def vertices (z : RowInput) : List ℕ := indices z.1.1
def verticesRealizer : Realizer vertices :=
  composition (composition first first) indicesRealizer
lemma polynomial_vertices : PolynomialTime verticesRealizer :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_indices

def row (z : RowInput) : List ℕ := (vertices z).filter (fun a=>keep (z,a))
def rowRealizer : Realizer row :=
  composition (pair identity verticesRealizer) (filterWith keepRealizer)
lemma polynomial_row : PolynomialTime rowRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_vertices)
    (polynomial_filterWith polynomial_keep)

def join (z : Input) : GraphCode := (indices z.1).map (fun i=>row (z,i))
def joinRealizer : Realizer join :=
  composition (pair identity (composition first indicesRealizer)) (mapWith rowRealizer)
lemma polynomial_join : PolynomialTime joinRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition polynomial_first polynomial_indices))
    (polynomial_mapWith polynomial_row)

lemma join_length (z : Input) : (join z).length=z.1.length := by
  simp only [join,List.length_map,indices,List.length_range]

lemma row_weight (z : RowInput) : weight (row z)≤weight (indices z.1.1) :=
  weight_sublist (List.filter_sublist (p:=fun a=>keep (z,a)) (l:=vertices z))

lemma join_weight (z : Input) :
    weight (join z)≤z.1.length*(4*z.1.length^2+2*z.1.length+2)+1 := by
  have hi := indices_weight z.1
  have hs : ∀ i∈indices z.1,weight (row (z,i))≤4*z.1.length^2+2*z.1.length+1 := by
    intro i _
    exact (row_weight (z,i)).trans (by nlinarith [hi])
  have h := weight_map_bound (as:=indices z.1) (f:=fun i=>row (z,i))
    (N:=4*z.1.length^2+2*z.1.length+1) hs
  simpa only [join,indices,List.length_range,Nat.add_assoc] using h

lemma keep_code {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v r a : Fin n) (hne : u≠v) :
    keep (((graphCode G,(u.val,v.val)),r.val),a.val)=true ↔
      (G⊔edge u v).Adj a r := by
  simp only [keep,graphCode_getD,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq]
  rw [adjacencyRow_mem]
  have he : (∃ w : Fin n,w.val=a.val ∧ G.Adj w r) ↔ G.Adj a r := by
    constructor
    · rintro ⟨w,hw,hwr⟩
      exact (Fin.ext hw) ▸ hwr
    · intro har
      exact ⟨a,rfl,har⟩
  rw [he]
  simp only [Fin.val_inj,SimpleGraph.sup_adj,SimpleGraph.edge_adj]
  constructor
  · rintro (h|(⟨hr,ha⟩|⟨hr,ha⟩))
    · exact Or.inl h
    · subst r; subst a; exact Or.inr ⟨Or.inr ⟨rfl,rfl⟩,Ne.symm hne⟩
    · subst r; subst a; exact Or.inr ⟨Or.inl ⟨rfl,rfl⟩,hne⟩
  · rintro (h|⟨(⟨ha,hr⟩|⟨ha,hr⟩),_⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨hr,ha⟩)
    · exact Or.inr (Or.inl ⟨hr,ha⟩)

lemma join_code {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) (hne : u≠v) :
    join (graphCode G,(u.val,v.val))=graphCode (G⊔edge u v) := by
  simp only [join,indices,graphCode_length,DirectedBFSCode.range_eq_map,←List.ofFn_eq_map,
    List.map_ofFn]
  change List.ofFn (fun r : Fin n=>row ((graphCode G,(u.val,v.val)),r.val)) =
    List.ofFn (adjacencyRow (G⊔edge u v))
  apply congrArg List.ofFn
  funext r
  simp only [row,vertices,indices,graphCode_length,
    DirectedBFSCode.range_eq_map,List.filter_map,adjacencyRow]
  apply congrArg (List.map Fin.val)
  apply List.filter_congr
  intro a _
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq,Function.comp_apply] using keep_code G u v r a hne

end ContingencyTables.ForestJoinProgram

end OAI
