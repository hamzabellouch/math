import Mathlib.Data.List.Pairwise
import Mathlib.Data.Nat.Prime.Basic
import OAI.NumberTheory.Ostmann.Arithmetic.MovingRegularSlots

namespace OAI

/-! # Keep nonbulk coprimalities when bulk collisions are removed -/

namespace Ostmann
open scoped Classical

theorem pairwise_split_bulk {α : Type*} (R : α → α → Prop)
    (bulk : α → Bool) (L : List α)
    (hcross : ∀ a ∈ L, ∀ b ∈ L, bulk a ≠ bulk b → R a b) :
    L.Pairwise R ↔ (L.filter bulk).Pairwise R ∧ (L.filter fun a => !(bulk a)).Pairwise R := by
  constructor
  · intro h
    exact ⟨h.filter bulk, h.filter (fun a => !(bulk a))⟩
  · induction L with
    | nil => simp
    | cons a L ih =>
      rintro ⟨hb, hs⟩
      have htail := ih (fun b hb c hc => hcross b (List.mem_cons_of_mem a hb)
        c (List.mem_cons_of_mem a hc))
      cases ha : bulk a with
      | false =>
        simp only [List.filter_cons, ha, Bool.not_false, Bool.false_eq_true, ite_false,
          ite_true, List.pairwise_cons] at hb hs
        refine List.pairwise_cons.mpr ⟨?_, htail ⟨hb, hs.2⟩⟩
        intro b hbL
        cases hbB : bulk b with
        | false => exact hs.1 b (List.mem_filter.mpr ⟨hbL, by simp [hbB]⟩)
        | true => exact hcross a List.mem_cons_self b (List.mem_cons_of_mem a hbL) (by simp [ha, hbB])
      | true =>
        simp only [List.filter_cons, ha, Bool.not_true, Bool.false_eq_true, ite_false,
          ite_true, List.pairwise_cons] at hb hs
        refine List.pairwise_cons.mpr ⟨?_, htail ⟨hb.2, hs⟩⟩
        intro b hbL
        cases hbB : bulk b with
        | false => exact hcross a List.mem_cons_self b (List.mem_cons_of_mem a hbL) (by simp [ha, hbB])
        | true => exact hb.1 b (List.mem_filter.mpr ⟨hbL, hbB⟩)

/-- Under the original distinct-bulk event, all bulk coprimality tests are
automatic. The nonbulk tests are retained exactly. -/
theorem prime_list_pairwise_iff_nonbulk {σ : Type*} (value : σ → ℕ)
    (bulk : σ → Bool) (L : List σ)
    (hprime : ∀ i ∈ L, (value i).Prime)
    (hnodup : (L.filter bulk).Nodup)
    (hinj : ∀ i j, bulk i = true → bulk j = true → value i = value j → i = j)
    (hcross : ∀ i ∈ L, ∀ j ∈ L, bulk i ≠ bulk j → value i ≠ value j) :
    (L.map value).Pairwise Nat.Coprime ↔
      ((L.filter fun i => !(bulk i)).map value).Pairwise Nat.Coprime := by
  rw [List.pairwise_map, List.pairwise_map]
  have hb : (L.filter bulk).Pairwise (fun i j => (value i).Coprime (value j)) := by
    apply hnodup.imp_of_mem
    intro i j hi hj hij
    obtain ⟨hiL, hiB⟩ := List.mem_filter.mp hi
    obtain ⟨hjL, hjB⟩ := List.mem_filter.mp hj
    exact (Nat.coprime_primes (hprime i hiL) (hprime j hjL)).mpr
      (fun h => hij (hinj i j hiB hjB h))
  rw [pairwise_split_bulk _ bulk L (fun i hi j hj h =>
    (Nat.coprime_primes (hprime i hi) (hprime j hj)).mpr (hcross i hi j hj h))]
  exact and_iff_right hb

end Ostmann

end OAI
