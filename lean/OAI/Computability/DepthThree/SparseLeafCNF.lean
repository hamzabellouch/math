import OAI.Computability.DepthThree.SparseNormalize
import OAI.Computability.DepthThree.SparsePrefix

namespace OAI

universe uDepth1

noncomputable section

namespace DepthThreeLowerBound

open scoped BigOperators

variable {V : Type uDepth1} [instDecidableEqV : DecidableEq V]

namespace SparseNormalization

def toState {H : CNF V} {b : ℕ} (N : SparseNormalization H b) : SparseState V where
  active := N.active
  side := ∅
  added := ∅

theorem toState_valid
    {V : Type uDepth1}
    [DecidableEq V]
    {H : CNF V} {b : ℕ} (N : SparseNormalization H b) :
    N.toState.Valid b where
  normalized := N.normalized
  nonempty := N.nonempty
  antichain := N.antichain
  width_le := N.width_le
  added_subset := Finset.empty_subset _

@[simp] theorem toState_added
    {V : Type uDepth1}
    [DecidableEq V]
    {H : CNF V} {b : ℕ} (N : SparseNormalization H b) :
    N.toState.added = ∅ := rfl

theorem toState_eval
    {V : Type uDepth1}
    [DecidableEq V]
    {H : CNF V} {b : ℕ} (N : SparseNormalization H b)
    (x : Cube V) : N.toState.eval x = H.eval x := by
  simpa only [SparseState.eval, SparseState.toCNF, toState, Finset.toList_empty,
    List.map_nil, List.append_nil] using N.eval_eq x

end SparseNormalization

namespace SparseState

theorem toCNF_normalized
    {V : Type uDepth1}
    [DecidableEq V]
    (s : SparseState V) {b : ℕ}
    (hs : s.Valid b) : s.toCNF.Normalized := by
  intro C hC
  rcases List.mem_append.mp hC with hactive | hside
  · exact hs.normalized C (Finset.mem_toList.mp hactive)
  · obtain ⟨l, _, rfl⟩ := List.mem_map.mp hside
    intro v hf ht
    have heq := (Finset.mem_singleton.mp hf).trans (Finset.mem_singleton.mp ht).symm
    have hfalse : (false : Bool) = true := congrArg Prod.snd heq
    cases hfalse

theorem toCNF_widthAtMost
    {V : Type uDepth1}
    [DecidableEq V]
    (s : SparseState V) {b : ℕ}
    (hs : s.Valid b) (hb : 1 ≤ b) : s.toCNF.WidthAtMost b := by
  intro C hC
  rcases List.mem_append.mp hC with hactive | hside
  · exact hs.width_le C (Finset.mem_toList.mp hactive)
  · obtain ⟨l, _, rfl⟩ := List.mem_map.mp hside
    simpa [Clause.width, Clause.scope] using hb

@[simp] theorem toCNF_length
    {V : Type uDepth1}
    [DecidableEq V]
    (s : SparseState V) :
    s.toCNF.length = s.active.card + s.side.card := by
  simp [toCNF]

theorem active_card_eq_sum_sizes
    {V : Type uDepth1}
    [DecidableEq V]
    (s : SparseState V) {b : ℕ} (hs : s.Valid b) :
    s.active.card = ∑ u ∈ Finset.Icc 1 b, (clausesOfSize s.active u).card := by
  apply Finset.card_eq_sum_card_fiberwise
  intro C hC
  apply Finset.mem_Icc.mpr
  constructor
  · exact (hs.nonempty C hC).card_pos
  · rw [(hs.normalized C hC).card_eq_width]
    exact hs.width_le C hC

theorem active_card_le_of_terminal [Fintype V] (s : SparseState V)
    {r e D : ℕ → ℕ} {b : ℕ} (hs : s.Valid b)
    (hnum : SparseNumerics r e D b)
    (hterminal : ∀ i, ¬ Nonempty (SignedSunflower s i (r i))) :
    s.active.card ≤ (2 * Fintype.card V) * ∑ u ∈ Finset.Icc 1 b, e u := by
  rw [s.active_card_eq_sum_sizes hs, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u hu
  obtain ⟨hu1, hub⟩ := Finset.mem_Icc.mp hu
  apply clausesOfSize_card_le
  · intro C hC
    exact hs.nonempty C (mem_clausesOfSize.mp hC).1
  · intro l
    exact sparse_occurrence_le_of_no_sunflower hnum s u hu1 hub (hterminal u) l

theorem toCNF_length_le_of_terminal [Fintype V] (s : SparseState V)
    {r e D : ℕ → ℕ} {b : ℕ} (hs : s.Valid b)
    (hnum : SparseNumerics r e D b)
    (hterminal : ∀ i, ¬ Nonempty (SignedSunflower s i (r i))) :
    s.toCNF.length ≤
      (2 + 2 * ∑ u ∈ Finset.Icc 1 b, e u) * Fintype.card V := by
  have hside : s.side.card ≤ 2 * Fintype.card V := by
    have h := Finset.card_le_univ s.side
    simpa only [Literal, Fintype.card_prod, Fintype.card_bool, Nat.mul_comm] using h
  rw [s.toCNF_length]
  calc
    s.active.card + s.side.card ≤
        (2 * Fintype.card V) * (∑ u ∈ Finset.Icc 1 b, e u) +
          2 * Fintype.card V :=
      Nat.add_le_add (s.active_card_le_of_terminal hs hnum hterminal) hside
    _ = _ := by ring

end SparseState

end DepthThreeLowerBound

end

end OAI
