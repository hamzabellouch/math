import OAI.Algebra.DepthFive.Basic
import Mathlib.Data.List.SplitLengths

namespace OAI

namespace Problem335

/-- Full blocks followed by one possible shorter final block. -/
def blockLengths (n t : ℕ) : List ℕ :=
  List.replicate (n / t) t ++ if n % t = 0 then [] else [n % t]

theorem blockLengths_sum (n t : ℕ) : (blockLengths n t).sum = n := by
  simp only [blockLengths, List.sum_append, List.sum_replicate]
  split_ifs with h
  · simp only [List.sum_nil, add_zero]
    simpa [h, Nat.mul_comm] using Nat.div_add_mod n t
  · simpa [Nat.mul_comm] using Nat.div_add_mod n t

theorem blockLengths_pos {n t : ℕ} (ht : 0 < t) :
    ∀ d ∈ blockLengths n t, 0 < d := by
  intro d hd
  simp only [blockLengths, List.mem_append] at hd
  rcases hd with hd | hd
  · have : d = t := (List.mem_replicate.mp hd).2
    simpa [this] using ht
  · split_ifs at hd with h
    · simp at hd
    · have : d = n % t := by simpa using hd
      simpa [this] using (show 0 < n % t from Nat.pos_of_ne_zero h)

theorem blockLengths_le {n t : ℕ} (ht : 0 < t) :
    ∀ d ∈ blockLengths n t, d ≤ t := by
  intro d hd
  simp only [blockLengths, List.mem_append] at hd
  rcases hd with hd | hd
  · exact le_of_eq (List.mem_replicate.mp hd).2
  · split_ifs at hd with h
    · simp at hd
    · have : d = n % t := by simpa using hd
      simpa [this] using (Nat.mod_lt n ht).le

theorem blockLengths_length {n t : ℕ} (ht : 0 < t) :
    (blockLengths n t).length = ceilDiv n t := by
  simp only [blockLengths, List.length_append, List.length_replicate]
  have hm := Nat.mod_lt n ht
  have hd := Nat.div_add_mod n t
  have hs : n + t - 1 + 1 = n + t := by omega
  unfold ceilDiv
  split_ifs with h
  · simp only [List.length_nil, add_zero]
    symm
    apply Nat.div_eq_of_lt_le
    · nlinarith
    · nlinarith
  · simp only [List.length_singleton]
    have hp : 0 < n % t := Nat.pos_of_ne_zero h
    symm
    apply Nat.div_eq_of_lt_le
    · nlinarith
    · nlinarith

/-- Consecutive blocks, with their lengths prescribed explicitly. -/
def consecutiveBlocks {α : Type*} (t : ℕ) (l : List α) : List (List α) :=
  (blockLengths l.length t).splitLengths l

@[simp] theorem consecutiveBlocks_flatten {α : Type*} (t : ℕ) (l : List α) :
    (consecutiveBlocks t l).flatten = l := by
  apply List.flatten_splitLengths
  simp [blockLengths_sum]

@[simp] theorem consecutiveBlocks_map_length {α : Type*} (t : ℕ) (l : List α) :
    (consecutiveBlocks t l).map List.length = blockLengths l.length t := by
  apply List.map_splitLengths_length
  simp [blockLengths_sum]

theorem consecutiveBlocks_length {α : Type*} {t : ℕ} (ht : 0 < t) (l : List α) :
    (consecutiveBlocks t l).length = ceilDiv l.length t := by
  simpa only [consecutiveBlocks, List.length_splitLengths] using
    (blockLengths_length (n := l.length) ht)

theorem consecutiveBlocks_length_pos {α : Type*} {t : ℕ} (ht : 0 < t)
    (l : List α) {b : List α} (hb : b ∈ consecutiveBlocks t l) : 0 < b.length := by
  apply blockLengths_pos ht b.length
  rw [← consecutiveBlocks_map_length t l]
  exact List.mem_map_of_mem hb

theorem consecutiveBlocks_length_le {α : Type*} {t : ℕ} (ht : 0 < t)
    (l : List α) {b : List α} (hb : b ∈ consecutiveBlocks t l) : b.length ≤ t := by
  apply blockLengths_le ht b.length
  rw [← consecutiveBlocks_map_length t l]
  exact List.mem_map_of_mem hb

theorem consecutiveBlocks_nonempty {α : Type*} {t : ℕ} (ht : 0 < t)
    (l : List α) {b : List α} (hb : b ∈ consecutiveBlocks t l) : b ≠ [] := by
  have := consecutiveBlocks_length_pos ht l hb
  intro he
  simp [he] at this

theorem consecutiveBlocks_prod {M : Type*} [Monoid M] (t : ℕ) (l : List M) :
    ((consecutiveBlocks t l).map List.prod).prod = l.prod := by
  rw [← List.prod_flatten, consecutiveBlocks_flatten]

theorem consecutiveBlocks_map_prod {α M : Type*} [Monoid M]
    (f : α → M) (t : ℕ) (l : List α) :
    ((consecutiveBlocks t l).map (fun b => (b.map f).prod)).prod = (l.map f).prod := by
  calc
    _ = (((consecutiveBlocks t l).map (List.map f)).map List.prod).prod := by
      simp only [List.map_map, Function.comp_def]
    _ = (l.map f).prod := by
      rw [← List.prod_flatten, ← List.map_flatten, consecutiveBlocks_flatten]

/-- The consecutive blocks of the matrix-layer index list. -/
def layerBlocks (n t : ℕ) : List (List (Fin n)) :=
  consecutiveBlocks t (List.finRange n)

@[simp] theorem layerBlocks_flatten (n t : ℕ) :
    (layerBlocks n t).flatten = List.finRange n :=
  consecutiveBlocks_flatten t _

theorem layerBlocks_length {n t : ℕ} (ht : 0 < t) :
    (layerBlocks n t).length = ceilDiv n t := by
  simpa [layerBlocks] using consecutiveBlocks_length ht (List.finRange n)

end Problem335

namespace Problem335

theorem layerBlocks_length_pos {n t : ℕ} (ht : 0 < t)
    {b : List (Fin n)} (hb : b ∈ layerBlocks n t) : 0 < b.length :=
  consecutiveBlocks_length_pos ht _ hb

theorem layerBlocks_length_le {n t : ℕ} (ht : 0 < t)
    {b : List (Fin n)} (hb : b ∈ layerBlocks n t) : b.length ≤ t :=
  consecutiveBlocks_length_le ht _ hb

theorem layerBlocks_nonempty {n t : ℕ} (ht : 0 < t)
    {b : List (Fin n)} (hb : b ∈ layerBlocks n t) : b ≠ [] :=
  consecutiveBlocks_nonempty ht _ hb

theorem layerBlocks_get_length_pos {n t : ℕ} (ht : 0 < t)
    (i : Fin (layerBlocks n t).length) : 0 < ((layerBlocks n t).get i).length :=
  layerBlocks_length_pos ht (List.get_mem ..)

theorem layerBlocks_get_length_le {n t : ℕ} (ht : 0 < t)
    (i : Fin (layerBlocks n t).length) : ((layerBlocks n t).get i).length ≤ t :=
  layerBlocks_length_le ht (List.get_mem ..)

@[simp] theorem layerBlocks_sum_lengths (n t : ℕ) :
    ((layerBlocks n t).map List.length).sum = n := by
  simp [layerBlocks, blockLengths_sum]

theorem layerBlocks_map_prod {M : Type*} [Monoid M] (n t : ℕ) (f : Fin n → M) :
    ((layerBlocks n t).map (fun b => (b.map f).prod)).prod = (List.ofFn f).prod := by
  simpa only [layerBlocks, List.ofFn_eq_map] using consecutiveBlocks_map_prod f t (List.finRange n)

/-- The entry defining IMM can be computed from the consecutive block products. -/
theorem imm_eq_layerBlocks (K : Type*) [CommSemiring K] {n : ℕ} (hn : 0 < n) (t : ℕ) :
    imm K n =
      (((layerBlocks n t).map (fun b : List (Fin n) => (b.map (immLayer K n)).prod)).prod)
        ⟨0, hn⟩ ⟨0, hn⟩ := by
  rw [layerBlocks_map_prod]
  simp only [imm, dite_eq_left hn]

/-- The block-expansion lower-product gate budget. -/
theorem layerBlocks_power_sum_le {n t : ℕ} (hn : 0 < n) (ht : 0 < t) :
    ((layerBlocks n t).map (fun b => n ^ (b.length + 1))).sum ≤
      ceilDiv n t * n ^ (t + 1) := by
  have h := List.sum_le_length_nsmul
    ((layerBlocks n t).map (fun b => n ^ (b.length + 1))) (n ^ (t + 1)) (by
      intro x hx
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
      exact Nat.pow_le_pow_right hn (Nat.add_le_add_right (layerBlocks_length_le ht hb) 1))
  simpa only [List.length_map, layerBlocks_length ht, nsmul_eq_mul, Nat.cast_id] using h

end Problem335

end OAI
