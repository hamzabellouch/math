import Mathlib
import OAI.Geometry.HyperbolicGroups.FinitePolyhedronVoltage
import OAI.Geometry.HyperbolicGroups.FinitePolygonModel
import OAI.Geometry.HyperbolicGroups.IntegralCellularBoundary
import OAI.Geometry.HyperbolicGroups.FiniteFlatFacets

namespace OAI

/-! Literal source voltages on the mapping-cylinder triangulation. -/
noncomputable section

namespace HyperbolicObstruction.FinitePolygonModel.Data
open FinitePolyhedron
variable {V E C G : Type*} [Group G]
variable (P : Data V E C) (v : E → G)

def signed (e : E × Bool) : G := if e.2 then v e.1 else (v e.1)⁻¹

def segment (q : P.Position) : G := if q.2.2.val = 1 then signed v (P.side q.1 q.2.1) else 1

def cornerOffset (q : P.Position) : G :=
  ((List.ofFn (fun i => signed v (P.side q.1 i))).take q.2.1.val).prod *
    (if q.2.2.val = 2 then signed v (P.side q.1 q.2.1) else 1)

lemma cornerOffset_next (h : ∀ c, (List.ofFn (fun i => signed v (P.side c i))).prod = 1)
    (q : P.Position) : P.cornerOffset v (P.next q) = P.cornerOffset v q * P.segment v q := by
  rcases q with ⟨c,i,j⟩
  fin_cases j
  · simp [next,cornerOffset,segment]
  · simp [next,cornerOffset,segment]
  · simpa [next,cornerOffset,segment] using IntegralIncidence.group_prefix_rotate
      (fun i => signed v (P.side c i)) (h c) i

lemma next_next_ne (q : P.Position) : P.next (P.next q) ≠ q := by
  rcases q with ⟨c,i,j⟩
  intro h
  have hh := congrArg (fun a : P.Position => a.2.2.val) h
  fin_cases j <;> simp [next] at hh

lemma base_next (q : P.Position) : P.base (P.next q) =
    if q.2.2.val = 2 then P.old (P.start ((P.side q.1 q.2.1).1, !(P.side q.1 q.2.1).2))
    else if q.2.2.val = 0 then P.mid (P.side q.1 q.2.1).1 (P.side q.1 q.2.1).2
    else P.mid (P.side q.1 q.2.1).1 (!(P.side q.1 q.2.1).2) := by
  rcases q with ⟨c,i,j⟩
  fin_cases j
  · simp [base,next,dartStart]
  · simp [base,next,dartStart]
  · simpa [base,next,dartStart] using congrArg P.old (P.closed c i)

lemma base_ne_next (q : P.Position) : P.base q ≠ P.base (P.next q) := by
  rw [base_next]
  rcases q with ⟨c,i,j⟩
  rcases he : P.side c i with ⟨e,b⟩
  fin_cases j <;> cases b <;> simp [base,dartStart,he]

variable [DecidableEq E]

/-- Only the middle third of each graph edge carries its original voltage. -/
def graphValue : (V ⊕ (E × Bool)) → (V ⊕ (E × Bool)) → G
  | .inr (e,a), .inr (f,b) => if e = f ∧ a ≠ b then signed v (e,a) else 1
  | _,_ => 1

lemma graphValue_self (a : (V ⊕ (E × Bool))) : graphValue (V := V) v a a = 1 := by
  rcases a with a|⟨e,b⟩ <;> simp [graphValue]

lemma graphValue_reverse (a b : (V ⊕ (E × Bool))) : graphValue (V := V) v b a = (graphValue (V := V) v a b)⁻¹ := by
  rcases a with a|⟨e,a⟩ <;> rcases b with b|⟨f,b⟩ <;> try simp [graphValue]
  by_cases h : e = f
  · subst f; cases a <;> cases b <;> simp [signed]
  · simp [h,Ne.symm h]

variable [DecidableEq V] [DecidableEq C]

/-- The collar and cap formulas retain each occurrence's independent cornerOffset. -/
def value : P.Vertex → P.Vertex → G
  | .inl a, .inl b => graphValue (V := V) v a b
  | .inr (.inr q), .inl b => if P.graph b = P.base (P.next q) then P.segment v q else 1
  | .inl a, .inr (.inr q) => (if P.graph a = P.base (P.next q) then P.segment v q else 1)⁻¹
  | .inr (.inr q), .inr (.inr r) =>
      if r = P.next q then P.segment v q else if q = P.next r then (P.segment v r)⁻¹ else 1
  | .inr (.inl c), .inr (.inr q) => if c = q.1 then P.cornerOffset v q else 1
  | .inr (.inr q), .inr (.inl c) => (if c = q.1 then P.cornerOffset v q else 1)⁻¹
  | _,_ => 1

lemma value_self (a : P.Vertex) : P.value v a a = 1 := by
  rcases a with a|(c|q)
  · exact graphValue_self (V := V) v a
  · rfl
  · simp [value,Ne.symm (P.next_ne q)]

lemma value_reverse (a b : P.Vertex) : P.value v b a = (P.value v a b)⁻¹ := by
  rcases a with a|(c|q) <;> rcases b with b|(d|r) <;> first | exact graphValue_reverse v _ _ | simp only [value,inv_inv,inv_one]
  by_cases h : r = P.next q
  · subst r
    simp [Ne.symm (P.next_next_ne q)]
  · by_cases h' : q = P.next r
    · subst q; simp [h]
    · simp [h,h']

omit [DecidableEq V] [DecidableEq E] [DecidableEq C] in
lemma base_graph (q : P.Position) : ∃ b : V ⊕ (E × Bool), P.base q = P.graph b := by
  dsimp [base,dartStart]
  split_ifs <;> exact ⟨_,rfl⟩

lemma value_outer_base (q : P.Position) : P.value v (P.outer q) (P.base q) = 1 := by
  obtain ⟨b,hb⟩ := P.base_graph q
  have hn := P.base_ne_next q
  rw [hb] at hn ⊢
  simp [value,hn]

lemma value_outer_nextbase (q : P.Position) :
    P.value v (P.outer q) (P.base (P.next q)) = P.segment v q := by
  obtain ⟨b,hb⟩ := P.base_graph (P.next q)
  rw [hb]
  simp [value,hb]

lemma value_outer_next (q : P.Position) :
    P.value v (P.outer q) (P.outer (P.next q)) = P.segment v q := by simp [value]

lemma value_apex_outer (q : P.Position) :
    P.value v (P.apex q.1) (P.outer q) = P.cornerOffset v q := by simp [value]

lemma value_base_next (q : P.Position) :
    P.value v (P.base q) (P.base (P.next q)) = P.segment v q := by
  rw [base_next]
  rcases q with ⟨c,i,j⟩
  fin_cases j <;> simp [base,dartStart,value,graphValue,segment]

lemma collar_ordered (h : ∀ c, (List.ofFn (fun i => signed v (P.side c i))).prod = 1)
    (q : P.Position) :
    P.value v (P.outer q) (P.base q) * P.value v (P.base q) (P.base (P.next q)) =
      P.value v (P.outer q) (P.base (P.next q)) ∧
    P.value v (P.outer q) (P.outer (P.next q)) * P.value v (P.outer (P.next q)) (P.base (P.next q)) =
      P.value v (P.outer q) (P.base (P.next q)) ∧
    P.value v (P.outer q) (P.outer (P.next q)) * P.value v (P.outer (P.next q)) (P.apex q.1) =
      P.value v (P.outer q) (P.apex q.1) := by
  refine ⟨by simp [value_outer_base,value_base_next,value_outer_nextbase],
    by simp [value_outer_next,value_outer_base,value_outer_nextbase],?_⟩
  have hc : (P.next q).1 = q.1 := rfl
  rw [value_outer_next,P.value_reverse v (P.apex q.1) (P.outer (P.next q)),
    P.value_reverse v (P.apex q.1) (P.outer q)]
  rw [← hc, value_apex_outer,hc,value_apex_outer,cornerOffset_next P v h]
  simp

lemma facet_flat (h : ∀ c, (List.ofFn (fun i => signed v (P.side c i))).prod = 1)
    (f : P.Facet) {a b c : P.Vertex} (ha : a ∈ P.facet f) (hb : b ∈ P.facet f)
    (hc : c ∈ P.facet f) : P.value v a b * P.value v b c = P.value v a c := by
  cases f with
  | inl e =>
    dsimp [facet,graphFace] at ha hb hc
    split_ifs at ha hb hc <;> exact flat_two (P.value v) (P.value_self v) (P.value_reverse v) ha hb hc
  | inr q =>
    obtain ⟨h0,h1,h2⟩ := P.collar_ordered v h q.1
    dsimp [facet,collarFace] at ha hb hc
    split_ifs at ha hb hc
    · exact flat_three (P.value v) (P.value_self v) (P.value_reverse v) h0 ha hb hc
    · exact flat_three (P.value v) (P.value_self v) (P.value_reverse v) h1 ha hb hc
    · exact flat_three (P.value v) (P.value_self v) (P.value_reverse v) h2 ha hb hc

/-- Every literal source relation gives a genuine topological voltage cover of
its finite simplicial mapping-cylinder realization. -/
def voltage (h : ∀ c, (List.ofFn (fun i => signed v (P.side c i))).prod = 1) :
    Voltage P.complex G where
  value := P.value v
  self := P.value_self v
  triangle a b c ht := by
    rcases ht.2 with hsmall|⟨f,hf⟩
    · have hab : a = b := Finset.card_le_one.mp hsmall a (by simp) b (by simp)
      have hbc : b = c := Finset.card_le_one.mp hsmall b (by simp) c (by simp)
      subst b; subst c
      simp [value_self]
    · exact P.facet_flat v h f (hf (by simp)) (hf (by simp)) (hf (by simp))

end HyperbolicObstruction.FinitePolygonModel.Data
end

end OAI
