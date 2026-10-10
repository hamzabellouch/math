import OAI.Combinatorics.LowSpaceSubsetSum.Separators.PreparedSeparatorWork
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.CountedCeilLog

namespace OAI

/-! # Preparing the shared checker context with computed depths

The four ceiling logarithms are computed by bounded doubling loops. The
resulting blocks retain the explicit coordinate vectors and incidence
arrays; later checks reuse them without rebuilding the tables.
-/

namespace LowSpaceSubsetSum.PreparedSeparatorContext

open StoredSeparatorCheck

variable {n g : ℕ}

def depths (families : Fin 4 → Array (Fin (2 ^ g))) : Fin 4 → ℕ :=
  ![(CountedCeilLog.run (families 0).size (g + 4)).1,
    (CountedCeilLog.run (families 1).size (g + 4)).1,
    (CountedCeilLog.run (families 2).size (g + 4)).1,
    (CountedCeilLog.run (families 3).size (g + 4)).1]

theorem depths_value (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g) (i : Fin 4) :
    depths families i = Nat.clog 2 (families i).size := by
  have h j := CountedCeilLog.run_value (families j).size (g + 4)
    (PreparedSeparatorWork.family_search_bound (families j) (hsize j)).le
  fin_cases i <;> exact h _

def prepare (rows : Fin 4 → Vector (Fin n) g)
    (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g) : List (Block n g) × ℕ :=
  let a := CountedCeilLog.run (families 0).size (g + 4)
  let b := CountedCeilLog.run (families 1).size (g + 4)
  let c := CountedCeilLog.run (families 2).size (g + 4)
  let d := CountedCeilLog.run (families 3).size (g + 4)
  let ds := ![a.1, b.1, c.1, d.1]
  let out := prepareFour rows families ds (fun _ => g + 4)
    (depths_value families hsize)
    (fun i => PreparedSeparatorWork.family_search_bound (families i) (hsize i))
  (out.1, out.2 + a.2 + b.2 + c.2 + d.2 + 5)

theorem prepare_value (rows : Fin 4 → Vector (Fin n) g)
    (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g) :
    (prepare rows families hsize).1 =
      (prepareFour rows families (depths families) (fun _ => g + 4)
        (depths_value families hsize)
        (fun i => PreparedSeparatorWork.family_search_bound (families i) (hsize i))).1 := rfl

theorem prepare_work (rows : Fin 4 → Vector (Fin n) g)
    (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g) :
    (prepare rows families hsize).2 ≤ 880 * 2 ^ (2 * g) + 16 * (g + 4) + 70 := by
  have ht := prepareFour_work rows families (depths families) (fun _ => g + 4)
    (depths_value families hsize)
    (fun i => PreparedSeparatorWork.family_search_bound (families i) (hsize i)) hsize
  have h₀ := CountedCeilLog.run_work (families 0).size (g + 4)
  have h₁ := CountedCeilLog.run_work (families 1).size (g + 4)
  have h₂ := CountedCeilLog.run_work (families 2).size (g + 4)
  have h₃ := CountedCeilLog.run_work (families 3).size (g + 4)
  change _ + _ + _ + _ + _ + 5 ≤ _
  change (prepareFour rows families (depths families) (fun _ => g + 4)
    (depths_value families hsize)
    (fun i => PreparedSeparatorWork.family_search_bound (families i) (hsize i))).2 ≤ _ at ht
  dsimp only [depths] at ht
  omega

theorem prepare_work_scale (I : Instance n) (hn : 10000 ≤ n) (hg : g ≤ n)
    (C : ℕ) (hC : 2 ^ (2 * g) ≤ C)
    (rows : Fin 4 → Vector (Fin n) g) (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g) :
    (prepare rows families hsize).2 ≤ inputScale I ^ 2 * C := by
  have hCpos : 1 ≤ C := (Nat.one_le_two_pow).trans hC
  have hu : n + 1 ≤ inputScale I := by unfold inputScale; omega
  have hcoef : 880 + 16 * (g + 4) + 70 ≤ inputScale I ^ 2 := by
    nlinarith only [hu, hg, hn]
  have hm := Nat.mul_le_mul_left (16 * (g + 4) + 70) hCpos
  have hp := Nat.mul_le_mul_left 880 hC
  have hw := prepare_work rows families hsize
  calc
    (prepare rows families hsize).2 ≤ (880 + 16 * (g + 4) + 70) * C := by
      nlinarith only [hw, hm, hp]
    _ ≤ inputScale I ^ 2 * C := Nat.mul_le_mul_right C hcoef

theorem acceptance (C : TopCoordinates n g)
    (rows : Fin 4 → Vector (Fin n) g) (hrows : ∀ i j, (rows i)[j] = C.index (i, j))
    (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g)
    (capacity : ℕ) (hcap : capacity = 2 ^ n) (target : ℤ)
    (xs ys : List (StoredEntry n)) :
    (run capacity target (prepare rows families hsize).1 xs ys).1 =
      (C.check (fun i => (families i).map SeparatorStoredMasks.decode) target
        (xs.map StoredEntry.semantic) (ys.map StoredEntry.semantic)).accepted := by
  rw [prepare_value]
  exact PreparedSeparatorRefinement.acceptance C rows hrows families (depths families)
    (fun _ => g + 4) (depths_value families hsize)
    (fun i => PreparedSeparatorWork.family_search_bound (families i) (hsize i))
    capacity hcap target xs ys

theorem run_work (I : Instance n) (hn : 10000 ≤ n) (hg : g ≤ n)
    (C : TopCoordinates n g)
    (rows : Fin 4 → Vector (Fin n) g) (hrows : ∀ i j, (rows i)[j] = C.index (i, j))
    (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g)
    (capacity : ℕ) (hcap : capacity = 2 ^ n) (target : ℤ)
    (xs ys : List (StoredEntry n)) :
    (run capacity target (prepare rows families hsize).1 xs ys).2 ≤ inputScale I ^ 4 *
      ((C.check (fun i => (families i).map SeparatorStoredMasks.decode) target
        (xs.map StoredEntry.semantic) (ys.map StoredEntry.semantic)).scans +
        xs.length + ys.length + 1) := by
  rw [prepare_value]
  exact PreparedSeparatorWork.run_work I hn C rows hrows families (depths families)
    (fun _ => g + 4) (depths_value families hsize)
    (fun i => PreparedSeparatorWork.family_search_bound (families i) (hsize i)) hg
    (fun _ => by omega) capacity hcap target xs ys

end LowSpaceSubsetSum.PreparedSeparatorContext

end OAI
