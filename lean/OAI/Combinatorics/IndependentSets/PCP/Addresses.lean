import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.Queries
import OAI.Combinatorics.IndependentSets.PCP.Emitter

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.Addresses

open IndependentSetsGames.Foundations.Hastad
open Enumeration

abbrev Terms := List (Fin 5 × Nat)

structure Field (bound : Nat) where
  terms : Terms
  offset : Fin bound

def values (n m edge tail head : Nat) : Fin 5 → Nat := ![n, m, edge, tail, head]

def eval {bound : Nat} (field : Field bound) (inputs : Fin 5 → Nat) : Nat :=
  Emitter.affineValue field.terms inputs field.offset.val

def fieldBound (q : Nat) : Nat :=
  12 * localCount q + tapeCount q + pairTapeCount q + 1

theorem fieldBound_pos (q : Nat) : 0 < fieldBound q := by
  unfold fieldBound
  omega

theorem tapeCount_lt_bound (q : Nat) : tapeCount q < fieldBound q := by
  unfold fieldBound
  omega

theorem pairTapeCount_lt_bound (q : Nat) : pairTapeCount q < fieldBound q := by
  unfold fieldBound
  omega

theorem localCount_lt_bound (q : Nat) : localCount q < fieldBound q := by
  unfold fieldBound
  omega

theorem local_add_pair_lt_bound (q : Nat) : localCount q + pairTapeCount q < fieldBound q := by
  unfold fieldBound
  omega

theorem twelve_local_lt_bound (q : Nat) : 12 * localCount q < fieldBound q := by
  unfold fieldBound
  omega

def zeroOffset (q : Nat) : Fin (fieldBound q) := ⟨0, fieldBound_pos q⟩

def eventOffset (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q)) : Fin (fieldBound q) :=
  ⟨(localEventEquiv q event).val,
    (localEventEquiv q event).isLt.trans (localCount_lt_bound q)⟩

def rawQueryOffset (q : Nat) : Queries.RawQuery q → Fin (fieldBound q)
  | .inl (_, tape) =>
    ⟨(cubeEquiv q tape).val, (cubeEquiv q tape).isLt.trans (tapeCount_lt_bound q)⟩
  | .inr tape =>
    ⟨(pairCubeEquiv q tape).val, (pairCubeEquiv q tape).isLt.trans (pairTapeCount_lt_bound q)⟩

def reverseOffset (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) : Fin (fieldBound q) :=
  ⟨(localEventEquiv q event).val * 12 + slot.val * 2 + bitValue (!orientation), by
    have he := (localEventEquiv q event).isLt
    have hs := slot.isLt
    have hb : bitValue (!orientation) < 2 := by
      simpa only [boolEquiv_val] using (boolEquiv (!orientation)).isLt
    have hbound := twelve_local_lt_bound q
    omega⟩

def headerVertices (q : Nat) : Field (fieldBound q) :=
  ⟨[(0, tapeCount q), (1, localCount q + pairTapeCount q)], zeroOffset q⟩

def headerDarts (q : Nat) : Field (fieldBound q) :=
  ⟨[(1, 12 * localCount q)], zeroOffset q⟩

def eventVertexField (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q)) :
    Field (fieldBound q) :=
  ⟨[(2, localCount q)], eventOffset q event⟩

def vertexQueryTerms (q : Nat) (side : Bool) : Terms :=
  [(1, localCount q), (if side then 4 else 3, tapeCount q)]

def edgeQueryTerms (q : Nat) : Terms :=
  [(1, localCount q), (0, tapeCount q), (2, pairTapeCount q)]

def rawQueryTerms (q : Nat) : Queries.RawQuery q → Terms
  | .inl (side, _) => vertexQueryTerms q side
  | .inr _ => edgeQueryTerms q

def rawQueryField (q : Nat) (query : Queries.RawQuery q) : Field (fieldBound q) :=
  ⟨rawQueryTerms q query, rawQueryOffset q query⟩

def reverseDartField (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) : Field (fieldBound q) :=
  ⟨[(2, 12 * localCount q)], reverseOffset q event slot orientation⟩

theorem headerVertices_eval (q n m edge tail head : Nat) :
    eval (headerVertices q) (values n m edge tail head) = vertexCount n m q := by
  simp [eval, headerVertices, values, zeroOffset, Emitter.affineValue,
    vertexCount, eventCount, addressCount, Nat.mul_add,
    Nat.mul_comm, Nat.add_comm, Nat.add_assoc]

theorem headerDarts_eval (q n m edge tail head : Nat) :
    eval (headerDarts q) (values n m edge tail head) = dartCount m q := by
  simp [eval, headerDarts, values, zeroOffset, Emitter.affineValue,
    dartCount, eventCount, Nat.mul_comm, Nat.mul_assoc]

theorem eventVertexField_eval (n m q : Nat) (edge : Fin m)
    (event : AlphabetGraph.LocalEvent (Fin q)) (tail head : Nat) :
    eval (eventVertexField q event) (values n m edge.val tail head) =
      (vertexEquiv n m q (.inl (edge, event))).val := by
  rw [vertexEquiv_event_val, eventEquiv_val]
  simp [eval, eventVertexField, eventOffset, values, Emitter.affineValue, Nat.mul_comm]

theorem rawQueryField_eval (n m q : Nat) (edge : Fin m) (tail head : Fin n)
    (query : Queries.RawQuery q) :
    eval (rawQueryField q query) (values n m edge.val tail.val head.val) =
      (vertexEquiv n m q (.inr (Queries.globalize tail head edge query))).val := by
  cases query with
  | inl query =>
    rcases query with ⟨side, tape⟩
    cases side <;>
      simp [eval, rawQueryField, rawQueryTerms, vertexQueryTerms, rawQueryOffset,
        values, Emitter.affineValue, Queries.globalize, eventCount,
        Nat.mul_comm, Nat.add_assoc]
  | inr tape =>
    simp [eval, rawQueryField, rawQueryTerms, edgeQueryTerms, rawQueryOffset,
      values, Emitter.affineValue, Queries.globalize, eventCount,
      Nat.mul_comm, Nat.add_assoc]

theorem reverseDartField_eval (n m q : Nat) (edge : Fin m)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) (orientation : Bool)
    (tail head : Nat) :
    eval (reverseDartField q event slot orientation) (values n m edge.val tail head) =
      (dartEquiv m q (QueryIncidence.reverse (((edge, event), slot), orientation))).val := by
  rw [dartEquiv_reverse_val, eventEquiv_val]
  simp [eval, reverseDartField, reverseOffset, values, Emitter.affineValue,
    Nat.mul_add, Nat.mul_comm, Nat.mul_assoc,
    Nat.add_assoc]

def queryEventTerms (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) : Terms :=
  rawQueryTerms q (Queries.query (fun _ _ => false) event slot)

theorem rawQueryTerms_query (q : Nat) (P : Fin q → Fin q → Bool)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) :
    rawQueryTerms q (Queries.query P event slot) = queryEventTerms q event slot := by
  rcases event with ⟨kind, ⟨side, tape⟩, f, g, r₀, r₁, r₂⟩
  by_cases hk₀ : kind = 0 <;> by_cases hk₁ : kind = 1 <;> by_cases hk₂ : kind = 2 <;>
    simp only [queryEventTerms, Queries.query, hk₀, hk₁, hk₂, ite_true, ite_false]
  all_goals split_ifs <;> rfl

def queryEventOffset (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (P : Fin q → Fin q → Bool) : Fin (fieldBound q) :=
  rawQueryOffset q (Queries.query P event slot)

def fieldForQueryEvent (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (P : Fin q → Fin q → Bool) : Field (fieldBound q) :=
  ⟨queryEventTerms q event slot, queryEventOffset q event slot P⟩

theorem fieldForQueryEvent_eq_rawQueryField (q : Nat)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6)
    (P : Fin q → Fin q → Bool) :
    fieldForQueryEvent q event slot P = rawQueryField q (Queries.query P event slot) := by
  unfold fieldForQueryEvent queryEventOffset rawQueryField
  rw [rawQueryTerms_query]

theorem fieldForQueryEvent_eval (n m q : Nat) (edge : Fin m) (tail head : Fin n)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6)
    (P : Fin q → Fin q → Bool) :
    eval (fieldForQueryEvent q event slot P) (values n m edge.val tail.val head.val) =
      (vertexEquiv n m q
        (.inr (Queries.globalize tail head edge (Queries.query P event slot)))).val := by
  rw [fieldForQueryEvent_eq_rawQueryField]
  exact rawQueryField_eval n m q edge tail head _

theorem fieldForQueryEvent_eval_verifier (n m q : Nat)
    (G : ConstraintGraph (Fin n) (Fin m) (Fin q)) (edge : Fin m)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) :
    eval (fieldForQueryEvent q event slot (G.accepts edge))
      (values n m edge.val (G.tail edge).val (G.head edge).val) =
      (vertexEquiv n m q (.inr ((AlphabetGraph.verifier G).query (edge, event) slot))).val := by
  rw [← Queries.globalize_query G edge event slot]
  exact fieldForQueryEvent_eval n m q edge (G.tail edge) (G.head edge) event slot _

def dartTailTerms (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) : Terms :=
  if orientation then queryEventTerms q event slot else [(2, localCount q)]

def dartTailOffset (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) (P : Fin q → Fin q → Bool) : Fin (fieldBound q) :=
  if orientation then queryEventOffset q event slot P else eventOffset q event

def fieldForDartTail (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) (P : Fin q → Fin q → Bool) : Field (fieldBound q) :=
  ⟨dartTailTerms q event slot orientation, dartTailOffset q event slot orientation P⟩

theorem fieldForDartTail_eval (n m q : Nat) (edge : Fin m) (tail head : Fin n)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) (orientation : Bool)
    (P : Fin q → Fin q → Bool) :
    eval (fieldForDartTail q event slot orientation P)
      (values n m edge.val tail.val head.val) =
      (vertexEquiv n m q (if orientation then
        .inr (Queries.globalize tail head edge (Queries.query P event slot))
        else .inl (edge, event))).val := by
  cases orientation with
  | false => exact eventVertexField_eval n m q edge event tail.val head.val
  | true => exact fieldForQueryEvent_eval n m q edge tail head event slot P

def CoefficientsBounded (q : Nat) (terms : Terms) : Prop :=
  ∀ term ∈ terms, term.2 < fieldBound q

theorem headerVertices_coefficients (q : Nat) : CoefficientsBounded q (headerVertices q).terms := by
  simp only [CoefficientsBounded, headerVertices, List.mem_cons, List.not_mem_nil, or_false]
  intro term h
  rcases h with rfl | rfl
  · exact tapeCount_lt_bound q
  · exact local_add_pair_lt_bound q

theorem headerDarts_coefficients (q : Nat) : CoefficientsBounded q (headerDarts q).terms := by
  intro term h
  have heq : term = (1, 12 * localCount q) := by simpa [headerDarts] using h
  subst term
  exact twelve_local_lt_bound q

theorem eventVertexField_coefficients (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q)) :
    CoefficientsBounded q (eventVertexField q event).terms := by
  intro term h
  have heq : term = (2, localCount q) := by simpa [eventVertexField] using h
  subst term
  exact localCount_lt_bound q

theorem rawQueryTerms_coefficients (q : Nat) (query : Queries.RawQuery q) :
    CoefficientsBounded q (rawQueryTerms q query) := by
  cases query with
  | inl query =>
    rcases query with ⟨side, tape⟩
    intro term h
    simp only [rawQueryTerms, vertexQueryTerms, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact localCount_lt_bound q
    · exact tapeCount_lt_bound q
  | inr tape =>
    intro term h
    simp only [rawQueryTerms, edgeQueryTerms, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · exact localCount_lt_bound q
    · exact tapeCount_lt_bound q
    · exact pairTapeCount_lt_bound q

theorem queryEventTerms_coefficients (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) : CoefficientsBounded q (queryEventTerms q event slot) :=
  rawQueryTerms_coefficients q _

theorem reverseDartField_coefficients (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) :
    CoefficientsBounded q (reverseDartField q event slot orientation).terms := by
  intro term h
  have heq : term = (2, 12 * localCount q) := by simpa [reverseDartField] using h
  subst term
  exact twelve_local_lt_bound q

theorem rawQueryTerms_length_le (q : Nat) (query : Queries.RawQuery q) :
    (rawQueryTerms q query).length ≤ 3 := by
  cases query with
  | inl query => rcases query with ⟨side, tape⟩; simp [rawQueryTerms, vertexQueryTerms]
  | inr tape => simp [rawQueryTerms, edgeQueryTerms]

theorem queryEventTerms_length_le (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) : (queryEventTerms q event slot).length ≤ 3 :=
  rawQueryTerms_length_le q _

theorem dartTailTerms_coefficients (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) :
    CoefficientsBounded q (dartTailTerms q event slot orientation) := by
  cases orientation with
  | false => exact eventVertexField_coefficients q event
  | true => exact queryEventTerms_coefficients q event slot

theorem dartTailTerms_length_le (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) :
    (dartTailTerms q event slot orientation).length ≤ 3 := by
  cases orientation with
  | false => simp [dartTailTerms]
  | true => exact queryEventTerms_length_le q event slot

theorem offset_lt {bound : Nat} (field : Field bound) : field.offset.val < bound :=
  field.offset.isLt

end IndependentSetsGames.Foundations.PCP.AlphabetTable.Addresses

end OAI
