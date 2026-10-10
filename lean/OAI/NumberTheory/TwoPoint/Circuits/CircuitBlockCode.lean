import OAI.NumberTheory.TwoPoint.Circuits.CircuitQueryWalk

namespace OAI

/-! A query block is encoded by positions within its term, the path answers,
and one separator. Term indices are recovered from the modified restriction,
so the code alphabet is independent of the number of terms. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def CubeTerm.slot {n : ℕ} (C : CubeTerm n) (i : Fin n) : ℕ :=
  if hi : i ∈ C.support then (C.support.equivFin ⟨i, hi⟩).val
  else C.support.card

lemma CubeTerm.slot_le {n : ℕ} (C : CubeTerm n) (i : Fin n) :
    C.slot i ≤ C.support.card := by
  unfold slot
  split_ifs with hi
  · exact Nat.le_of_lt (Fin.isLt _)
  · exact le_rfl

lemma CubeTerm.slot_injective {n : ℕ} (C : CubeTerm n) {i j : Fin n}
    (hi : i ∈ C.support) (hj : j ∈ C.support) (h : C.slot i = C.slot j) : i = j := by
  have he : C.support.equivFin ⟨i, hi⟩ = C.support.equivFin ⟨j, hj⟩ := by
    apply Fin.ext
    simpa only [slot, dite_eq_left hi, dite_eq_left hj] using h
  exact congrArg Subtype.val (C.support.equivFin.injective he)

namespace DNFQueryBlock

noncomputable def literalCode {n : ℕ} (b : DNFQueryBlock n) : List (ℕ × Bool) :=
  (b.queried.sort (· ≤ ·)).map (fun i => (b.term.slot i, b.answer i))

noncomputable def code {n : ℕ} (b : DNFQueryBlock n) : List (Option (ℕ × Bool)) :=
  b.literalCode.map some ++ [none]

noncomputable def codes {n : ℕ} (bs : List (DNFQueryBlock n)) : List (Option (ℕ × Bool)) :=
  bs.flatMap code

lemma code_length {n : ℕ} (b : DNFQueryBlock n) : b.code.length = b.queried.card + 1 := by
  simp [code, literalCode, Finset.length_sort]

lemma literalCode_injective {n : ℕ} (C : CubeTerm n) (S T : Finset (Fin n))
    (hS : S ⊆ C.support) (hT : T ⊆ C.support) (x y : BooleanCube n)
    (h : literalCode ⟨C, S, x⟩ = literalCode ⟨C, T, y⟩) :
    S = T ∧ ∀ i ∈ S, x i = y i := by
  have hmem (i : Fin n) (hi : i ∈ S) : i ∈ T ∧ x i = y i := by
    have hc : (C.slot i, x i) ∈ literalCode ⟨C, S, x⟩ := by
      apply List.mem_map.mpr
      exact ⟨i, (Finset.mem_sort _).mpr hi, rfl⟩
    rw [h] at hc
    obtain ⟨j, hj, he⟩ := List.mem_map.mp hc
    have hjT : j ∈ T := (Finset.mem_sort _).mp hj
    have hji : j = i := C.slot_injective (hT hjT) (hS hi) (congrArg Prod.fst he)
    subst j
    exact ⟨hjT, (congrArg Prod.snd he).symm⟩
  refine ⟨?_, fun i hi => (hmem i hi).2⟩
  apply Finset.Subset.antisymm (fun i hi => (hmem i hi).1)
  intro i hi
  have hc : (C.slot i, y i) ∈ literalCode ⟨C, T, y⟩ := by
    apply List.mem_map.mpr
    exact ⟨i, (Finset.mem_sort _).mpr hi, rfl⟩
  rw [← h] at hc
  obtain ⟨j, hj, he⟩ := List.mem_map.mp hc
  have hjS : j ∈ S := (Finset.mem_sort _).mp hj
  have hji : j = i := C.slot_injective (hS hjS) (hT hi) (congrArg Prod.fst he)
  exact hji ▸ hjS

end DNFQueryBlock

lemma separated_option_lists_injective {α : Type*} (xs ys : List α)
    (u v : List (Option α))
    (h : xs.map some ++ none :: u = ys.map some ++ none :: v) : xs = ys ∧ u = v := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact ⟨rfl, List.cons.inj h |>.2⟩
    | cons y ys => simp at h
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      have hp := List.cons.inj h
      have hxy : x = y := Option.some.inj hp.1
      obtain ⟨hxs, huv⟩ := ih ys hp.2
      exact ⟨by rw [hxy, hxs], huv⟩

end TwoPointCorrelations

end OAI
