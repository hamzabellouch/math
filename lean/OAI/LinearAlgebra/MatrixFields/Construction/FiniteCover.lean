import Mathlib

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

open scoped BigOperators

namespace MatrixMultiplication.FiniteCover

variable {Ω M G : Type*}

theorem exists_avoiding [Fintype Ω] [DecidableEq Ω] [DecidableEq M]
    (s : Finset M) (bad : M → Finset Ω) (t : ℕ)
    (hbad : ∀ m ∈ s, (bad m).card ≤ t)
    (hbudget : s.card * t < Fintype.card Ω) :
    ∃ ω : Ω, ∀ m ∈ s, ω ∉ bad m := by
  classical
  have hcard : (s.biUnion bad).card ≤ s.card * t := by
    calc
      (s.biUnion bad).card ≤ ∑ m ∈ s, (bad m).card := Finset.card_biUnion_le
      _ ≤ ∑ _m ∈ s, t := Finset.sum_le_sum fun m hm => hbad m hm
      _ = s.card * t := by simp
  by_contra hn
  have hsub : (Finset.univ : Finset Ω) ⊆ s.biUnion bad := by
    intro ω hω
    by_contra hout
    apply hn
    refine ⟨ω, ?_⟩
    intro m hm hmem
    exact hout (Finset.mem_biUnion.mpr ⟨m, hm, hmem⟩)
  have := Finset.card_le_card hsub
  simp only [Finset.card_univ] at this
  exact (not_lt_of_ge (this.trans hcard)) hbudget

def avoidingWords [Fintype G] [DecidableEq G] (bad : Finset G) (L : ℕ) :
    Finset (Fin L → G) := Finset.univ.filter fun f => ∀ i, f i ∈ bad

theorem card_avoidingWords [Fintype G] [DecidableEq G] (bad : Finset G) (L : ℕ) :
    (avoidingWords bad L).card = bad.card ^ L := by
  classical
  let e : {f : Fin L → G // f ∈ avoidingWords bad L} ≃ (Fin L → {g // g ∈ bad}) :=
    { toFun := fun f i => ⟨f.1 i, (Finset.mem_filter.mp f.2).2 i⟩
      invFun := fun f => ⟨fun i => (f i).1, by simp [avoidingWords]⟩
      left_inv := by intro f; rfl
      right_inv := by intro f; rfl }
  calc
    (avoidingWords bad L).card = Fintype.card {f : Fin L → G // f ∈ avoidingWords bad L} := by simp
    _ = Fintype.card (Fin L → {g // g ∈ bad}) := Fintype.card_congr e
    _ = bad.card ^ L := by simp

theorem exists_cover [Fintype G] [DecidableEq G] [DecidableEq M]
    (s : Finset M) (good : G → M → Prop) [∀ g, DecidablePred (good g)]
    (t L : ℕ)
    (hbad : ∀ m ∈ s, (Finset.univ.filter fun g => ¬good g m).card ≤ t)
    (hbudget : s.card * t ^ L < Fintype.card G ^ L) :
    ∃ f : Fin L → G, ∀ m ∈ s, ∃ i, good (f i) m := by
  classical
  let bad : M → Finset G := fun m => Finset.univ.filter fun g => ¬good g m
  have hb : ∀ m ∈ s, (avoidingWords (bad m) L).card ≤ t ^ L := by
    intro m hm
    rw [card_avoidingWords]
    exact Nat.pow_le_pow_left (hbad m hm) L
  obtain ⟨f, hf⟩ := exists_avoiding s (fun m => avoidingWords (bad m) L) (t ^ L) hb
    (by simpa using hbudget)
  refine ⟨f, ?_⟩
  intro m hm
  by_contra hn
  apply hf m hm
  simp only [avoidingWords, Finset.mem_filter, Finset.mem_univ, true_and]
  intro i
  simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
  exact fun hi => hn ⟨i, hi⟩

end MatrixMultiplication.FiniteCover

end MatrixAllFields

end OAI
