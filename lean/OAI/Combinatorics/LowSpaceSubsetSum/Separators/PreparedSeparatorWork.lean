import OAI.Combinatorics.LowSpaceSubsetSum.Separators.PreparedSeparatorRefinement
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.Magnitudes

namespace OAI

/-! # Polynomial work per source scan for the prepared checker

The incidence tables are built once. Each subsequent checker call is the
stored-list execution, with its cost bounded by the same source scan ledger
that occurs in the separator expectation theorem.
-/

namespace LowSpaceSubsetSum.PreparedSeparatorWork

open StoredSeparatorCheck

variable {n g : ℕ}

theorem queryBound (b : Block n g) (hg : g ≤ n) (hs : b.steps ≤ n + 4) :
    b.queryBound ≤ 128 * (n + 1) ^ 3 := by
  have hp : (g + 1) ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hm := Nat.mul_le_mul (show n + 7 ≤ 7 * (n + 1) by omega) hp
  have he : 7 * (n + 1) * (n + 1) ^ 2 = 7 * (n + 1) ^ 3 := by ring
  rw [he] at hm
  have hlin : n + 1 ≤ (n + 1) ^ 3 := Nat.le_self_pow (by decide) (n + 1)
  have hone : 1 ≤ (n + 1) ^ 3 := by
    simpa using (Nat.pow_le_pow_left (show 1 ≤ n + 1 by omega) 3)
  unfold Block.queryBound
  nlinarith only [hm, hs, hlin, hone]

theorem factor (blocks : List (Block n g)) (hlen : blocks.length = 4)
    (hg : g ≤ n) (hs : ∀ b ∈ blocks, b.steps ≤ n + 4) :
    StoredSeparatorCheck.factor n blocks ≤ 8192 * (n + 1) ^ 3 := by
  have hf := four_factor blocks (128 * (n + 1) ^ 3) hlen
    (fun b hb => queryBound b hg (hs b hb))
  have hlin : n + 1 ≤ (n + 1) ^ 3 := Nat.le_self_pow (by decide) (n + 1)
  have hone : 1 ≤ (n + 1) ^ 3 := by
    simpa using (Nat.pow_le_pow_left (show 1 ≤ n + 1 by omega) 3)
  nlinarith only [hf, hlin, hone]

theorem factor_scale (I : Instance n) (hn : 10000 ≤ n)
    (blocks : List (Block n g)) (hlen : blocks.length = 4)
    (hg : g ≤ n) (hs : ∀ b ∈ blocks, b.steps ≤ n + 4) :
    StoredSeparatorCheck.factor n blocks ≤ inputScale I ^ 4 := by
  have hu : n + 1 ≤ inputScale I := by unfold inputScale; omega
  have hp : (n + 1) ^ 3 ≤ inputScale I ^ 3 := Nat.pow_le_pow_left hu 3
  calc
    StoredSeparatorCheck.factor n blocks ≤ 8192 * (n + 1) ^ 3 :=
      factor blocks hlen hg hs
    _ ≤ inputScale I * inputScale I ^ 3 := Nat.mul_le_mul (by omega) hp
    _ = inputScale I ^ 4 := by ring

theorem prepared_steps (rows : Fin 4 → Vector (Fin n) g)
    (families : Fin 4 → Array (Fin (2 ^ g))) (depths steps : Fin 4 → ℕ)
    (hd : ∀ i, depths i = Nat.clog 2 (families i).size)
    (hs : ∀ i, (families i).size < 2 ^ steps i)
    (hsteps : ∀ i, steps i ≤ n + 4) :
    ∀ b ∈ (prepareFour rows families depths steps hd hs).1, b.steps ≤ n + 4 := by
  intro b hb
  rw [prepareFour_value] at hb
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
  exact hsteps i

theorem run_work (I : Instance n) (hn : 10000 ≤ n) (C : TopCoordinates n g)
    (rows : Fin 4 → Vector (Fin n) g) (hrows : ∀ i j, (rows i)[j] = C.index (i, j))
    (families : Fin 4 → Array (Fin (2 ^ g))) (depths steps : Fin 4 → ℕ)
    (hd : ∀ i, depths i = Nat.clog 2 (families i).size)
    (hs : ∀ i, (families i).size < 2 ^ steps i)
    (hg : g ≤ n) (hsteps : ∀ i, steps i ≤ n + 4)
    (capacity : ℕ) (hcap : capacity = 2 ^ n) (target : ℤ)
    (xs ys : List (StoredEntry n)) :
    (run capacity target (prepareFour rows families depths steps hd hs).1 xs ys).2 ≤
      inputScale I ^ 4 *
        ((C.check (fun i => (families i).map SeparatorStoredMasks.decode) target
          (xs.map StoredEntry.semantic) (ys.map StoredEntry.semantic)).scans +
          xs.length + ys.length + 1) := by
  have hw := StoredSeparatorCheck.run_work capacity hcap target
    (prepareFour rows families depths steps hd hs).1 xs ys
  rw [PreparedSeparatorRefinement.source_result C rows hrows families depths steps hd hs] at hw
  exact hw.trans (Nat.mul_le_mul_right _ (factor_scale I hn _
    (prepareFour_length rows families depths steps hd hs) hg
    (prepared_steps rows families depths steps hd hs hsteps)))

/-- A fixed integer number of binary-search steps suffices for every table
row; it depends only on the local universe size. -/
theorem family_search_bound (family : Array (Fin (2 ^ g)))
    (hsize : family.size ≤ 11 * 2 ^ g) : family.size < 2 ^ (g + 4) := by
  calc
    family.size ≤ 11 * 2 ^ g := hsize
    _ < 16 * 2 ^ g := Nat.mul_lt_mul_of_pos_right (by decide) (by positivity)
    _ = 2 ^ (g + 4) := by rw [pow_add]; ring

end LowSpaceSubsetSum.PreparedSeparatorWork

end OAI
