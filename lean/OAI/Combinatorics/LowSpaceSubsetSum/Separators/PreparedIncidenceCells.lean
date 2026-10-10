import OAI.Combinatorics.LowSpaceSubsetSum.Separators.IncidenceBuildCells
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.PreparedSeparatorContext

namespace OAI

/-! # Preparing the checker tables with a live-cell trace

The actual arrays produced by the row-at-a-time builder are placed directly
in the block. The original preparation occurs only in erased proof fields.
The four-block trace includes previously completed blocks while the next
pair of tables is constructed.
-/

namespace LowSpaceSubsetSum.PreparedIncidenceCells

open StoredSeparatorCheck

variable {n g : ℕ}

private def blockOfTables (row : Vector (Fin n) g)
    (family : Array (Fin (2 ^ g))) (depth steps : ℕ)
    (hd : depth = Nat.clog 2 family.size) (hs : family.size < 2 ^ steps)
    (tables : Array (Array ℕ) × Array (Array ℕ))
    (ht : tables = (StoredIncidenceBuild.tables family).1) : Block n g where
  row := row
  familySize := family.size
  depth := depth
  steps := steps
  leftStore := tables.1
  rightStore := tables.2
  leftSize := by
    rw [ht]
    exact StoredIncidenceBuild.preprocess_size _ _
  rightSize := by
    rw [ht]
    exact StoredIncidenceBuild.preprocess_size _ _
  depth_eq := hd
  leftSorted := by
    subst tables
    exact (StoredSeparatorCheck.prepareBlock row family depth steps hd hs).1.leftSorted
  rightSorted := by
    subst tables
    exact (StoredSeparatorCheck.prepareBlock row family depth steps hd hs).1.rightSorted
  leftBound := by
    subst tables
    exact (StoredSeparatorCheck.prepareBlock row family depth steps hd hs).1.leftBound
  rightBound := by
    subst tables
    exact (StoredSeparatorCheck.prepareBlock row family depth steps hd hs).1.rightBound

private theorem blockOfTables_value (row : Vector (Fin n) g)
    (family : Array (Fin (2 ^ g))) (depth steps : ℕ)
    (hd : depth = Nat.clog 2 family.size) (hs : family.size < 2 ^ steps)
    (tables : Array (Array ℕ) × Array (Array ℕ))
    (ht : tables = (StoredIncidenceBuild.tables family).1) :
    blockOfTables row family depth steps hd hs tables ht =
      (StoredSeparatorCheck.prepareBlock row family depth steps hd hs).1 := by
  subst tables
  rfl

def prepareBlock (row : Vector (Fin n) g) (family : Array (Fin (2 ^ g)))
    (depth steps : ℕ) (hd : depth = Nat.clog 2 family.size)
    (hs : family.size < 2 ^ steps) : (Block n g × ℕ) × ℕ :=
  let out := IncidenceBuildCells.tables family
  ((blockOfTables row family depth steps hd hs out.1.1
    (IncidenceBuildCells.tables_value family), out.1.2 + 12), out.2 + g + 12)

theorem prepareBlock_value (row : Vector (Fin n) g) (family : Array (Fin (2 ^ g)))
    (depth steps : ℕ) (hd : depth = Nat.clog 2 family.size)
    (hs : family.size < 2 ^ steps) :
    (prepareBlock row family depth steps hd hs).1.1 =
      (StoredSeparatorCheck.prepareBlock row family depth steps hd hs).1 :=
  blockOfTables_value row family depth steps hd hs _ (IncidenceBuildCells.tables_value family)

theorem prepareBlock_work (row : Vector (Fin n) g) (family : Array (Fin (2 ^ g)))
    (depth steps : ℕ) (hd : depth = Nat.clog 2 family.size)
    (hs : family.size < 2 ^ steps) (hsize : family.size ≤ 11 * 2 ^ g) :
    (prepareBlock row family depth steps hd hs).1.2 ≤ 220 * 2 ^ (2 * g) + 12 := by
  have h := IncidenceBuildCells.tables_work family
  have hm := Nat.mul_le_mul_right (2 ^ g) hsize
  have hM : 1 ≤ 2 ^ g := Nat.one_le_two_pow
  have hpow : 2 ^ (2 * g) = (2 ^ g) ^ 2 := by rw [two_mul, pow_add]; ring
  have hsq : 2 ^ g ≤ (2 ^ g) ^ 2 := by nlinarith only [hM]
  change (IncidenceBuildCells.tables family).1.2 + 12 ≤ _
  rw [hpow]
  nlinarith only [h, hm, hM, hsq]

theorem prepareBlock_cells (row : Vector (Fin n) g) (family : Array (Fin (2 ^ g)))
    (depth steps : ℕ) (hd : depth = Nat.clog 2 family.size)
    (hs : family.size < 2 ^ steps) (hsize : family.size ≤ 11 * 2 ^ g) :
    (prepareBlock row family depth steps hd hs).2 ≤ 160 * 2 ^ (2 * g) + g + 12 := by
  exact Nat.add_le_add_right (Nat.add_le_add_right
    (IncidenceBuildCells.tables_cells family hsize) g) 12

def payload (b : Block n g) : ℕ :=
  IncidenceBuildCells.arrayCells b.leftStore +
    IncidenceBuildCells.arrayCells b.rightStore + g + 8

/-- Scalar capacity; computing it does not scan either completed table. -/
def blockAllowance (family : Array (Fin (2 ^ g))) : ℕ :=
  2 * (2 ^ g * (family.size + 1) + 1) + g + 8

theorem prepareBlock_payload_allowance (row : Vector (Fin n) g)
    (family : Array (Fin (2 ^ g))) (depth steps : ℕ)
    (hd : depth = Nat.clog 2 family.size) (hs : family.size < 2 ^ steps) :
    payload (prepareBlock row family depth steps hd hs).1.1 ≤ blockAllowance family := by
  have ha := IncidenceBuildCells.preprocess_payload IncidenceBuildCells.contains family
  have hb := IncidenceBuildCells.preprocess_payload IncidenceBuildCells.avoids family
  change IncidenceBuildCells.arrayCells
      (IncidenceBuildCells.preprocess IncidenceBuildCells.contains family).1.1 +
    IncidenceBuildCells.arrayCells
      (IncidenceBuildCells.preprocess IncidenceBuildCells.avoids family).1.1 + g + 8 ≤ _
  unfold blockAllowance
  omega

theorem blockAllowance_le (family : Array (Fin (2 ^ g)))
    (hsize : family.size ≤ 11 * 2 ^ g) :
    blockAllowance family ≤ 26 * 2 ^ (2 * g) + g + 8 := by
  have hm := Nat.mul_le_mul_right (2 ^ g) hsize
  have hM : 1 ≤ 2 ^ g := Nat.one_le_two_pow
  have hpow : 2 ^ (2 * g) = (2 ^ g) ^ 2 := by rw [two_mul, pow_add]; ring
  have hsq : 2 ^ g ≤ (2 ^ g) ^ 2 := by nlinarith only [hM]
  unfold blockAllowance
  rw [hpow]
  nlinarith only [hm, hM, hsq]

theorem prepareBlock_payload (row : Vector (Fin n) g) (family : Array (Fin (2 ^ g)))
    (depth steps : ℕ) (hd : depth = Nat.clog 2 family.size)
    (hs : family.size < 2 ^ steps) (hsize : family.size ≤ 11 * 2 ^ g) :
    payload (prepareBlock row family depth steps hd hs).1.1 ≤
      26 * 2 ^ (2 * g) + g + 8 :=
  (prepareBlock_payload_allowance row family depth steps hd hs).trans
    (blockAllowance_le family hsize)

def prepareFour (rows : Fin 4 → Vector (Fin n) g)
    (families : Fin 4 → Array (Fin (2 ^ g))) (depths steps : Fin 4 → ℕ)
    (hd : ∀ i, depths i = Nat.clog 2 (families i).size)
    (hs : ∀ i, (families i).size < 2 ^ steps i) : (List (Block n g) × ℕ) × ℕ :=
  let a := prepareBlock (rows 0) (families 0) (depths 0) (steps 0) (hd 0) (hs 0)
  let b := prepareBlock (rows 1) (families 1) (depths 1) (steps 1) (hd 1) (hs 1)
  let c := prepareBlock (rows 2) (families 2) (depths 2) (steps 2) (hd 2) (hs 2)
  let d := prepareBlock (rows 3) (families 3) (depths 3) (steps 3) (hd 3) (hs 3)
  (([a.1.1, b.1.1, c.1.1, d.1.1], a.1.2 + b.1.2 + c.1.2 + d.1.2 + 5),
    max a.2 (max (blockAllowance (families 0) + b.2)
      (max (blockAllowance (families 0) + blockAllowance (families 1) + c.2)
        (blockAllowance (families 0) + blockAllowance (families 1) +
          blockAllowance (families 2) + d.2))) + 20)

theorem prepareFour_value (rows : Fin 4 → Vector (Fin n) g)
    (families : Fin 4 → Array (Fin (2 ^ g))) (depths steps : Fin 4 → ℕ)
    (hd : ∀ i, depths i = Nat.clog 2 (families i).size)
    (hs : ∀ i, (families i).size < 2 ^ steps i) :
    (prepareFour rows families depths steps hd hs).1.1 =
      (StoredSeparatorCheck.prepareFour rows families depths steps hd hs).1 := by
  simp only [prepareFour, StoredSeparatorCheck.prepareFour, prepareBlock_value]

theorem prepareFour_work (rows : Fin 4 → Vector (Fin n) g)
    (families : Fin 4 → Array (Fin (2 ^ g))) (depths steps : Fin 4 → ℕ)
    (hd : ∀ i, depths i = Nat.clog 2 (families i).size)
    (hs : ∀ i, (families i).size < 2 ^ steps i)
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g) :
    (prepareFour rows families depths steps hd hs).1.2 ≤ 880 * 2 ^ (2 * g) + 53 := by
  have h i := prepareBlock_work (rows i) (families i) (depths i) (steps i) (hd i) (hs i) (hsize i)
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  change _ + _ + _ + _ + 5 ≤ _
  omega

theorem prepareFour_cells (rows : Fin 4 → Vector (Fin n) g)
    (families : Fin 4 → Array (Fin (2 ^ g))) (depths steps : Fin 4 → ℕ)
    (hd : ∀ i, depths i = Nat.clog 2 (families i).size)
    (hs : ∀ i, (families i).size < 2 ^ steps i)
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g) :
    (prepareFour rows families depths steps hd hs).2 ≤ 256 * 2 ^ (2 * g) + 4 * g + 80 := by
  have hc i := prepareBlock_cells (rows i) (families i) (depths i) (steps i) (hd i) (hs i) (hsize i)
  have hp i := blockAllowance_le (families i) (hsize i)
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  change max _ (max _ (max _ _)) + 20 ≤ _
  omega

/-- The ceiling logs are computed once before the shared tables. -/
def prepare (rows : Fin 4 → Vector (Fin n) g)
    (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g) : (List (Block n g) × ℕ) × ℕ :=
  let a := CountedCeilLog.run (families 0).size (g + 4)
  let b := CountedCeilLog.run (families 1).size (g + 4)
  let c := CountedCeilLog.run (families 2).size (g + 4)
  let d := CountedCeilLog.run (families 3).size (g + 4)
  let ds := ![a.1, b.1, c.1, d.1]
  let out := prepareFour rows families ds (fun _ => g + 4)
    (PreparedSeparatorContext.depths_value families hsize)
    (fun i => PreparedSeparatorWork.family_search_bound (families i) (hsize i))
  ((out.1.1, out.1.2 + a.2 + b.2 + c.2 + d.2 + 5), out.2 + 32 * (g + 5))

theorem prepare_value (rows : Fin 4 → Vector (Fin n) g)
    (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g) :
    (prepare rows families hsize).1.1 =
      (PreparedSeparatorContext.prepare rows families hsize).1 := by
  exact prepareFour_value rows families (PreparedSeparatorContext.depths families)
    (fun _ => g + 4) (PreparedSeparatorContext.depths_value families hsize)
    (fun i => PreparedSeparatorWork.family_search_bound (families i) (hsize i))

theorem prepare_work (rows : Fin 4 → Vector (Fin n) g)
    (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g) :
    (prepare rows families hsize).1.2 ≤ 880 * 2 ^ (2 * g) + 16 * (g + 4) + 70 := by
  have ht := prepareFour_work rows families (PreparedSeparatorContext.depths families)
    (fun _ => g + 4) (PreparedSeparatorContext.depths_value families hsize)
    (fun i => PreparedSeparatorWork.family_search_bound (families i) (hsize i)) hsize
  have h0 := CountedCeilLog.run_work (families 0).size (g + 4)
  have h1 := CountedCeilLog.run_work (families 1).size (g + 4)
  have h2 := CountedCeilLog.run_work (families 2).size (g + 4)
  have h3 := CountedCeilLog.run_work (families 3).size (g + 4)
  change _ + _ + _ + _ + _ + 5 ≤ _
  dsimp only [PreparedSeparatorContext.depths] at ht
  omega

theorem prepare_cells (rows : Fin 4 → Vector (Fin n) g)
    (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g) :
    (prepare rows families hsize).2 ≤ 512 * 2 ^ (2 * g) + 64 * (g + 5) := by
  have ht := prepareFour_cells rows families (PreparedSeparatorContext.depths families)
    (fun _ => g + 4) (PreparedSeparatorContext.depths_value families hsize)
    (fun i => PreparedSeparatorWork.family_search_bound (families i) (hsize i)) hsize
  change _ + 32 * (g + 5) ≤ _
  dsimp only [PreparedSeparatorContext.depths] at ht
  omega

theorem prepare_work_scale (I : Instance n) (hn : 10000 ≤ n) (hg : g ≤ n)
    (C : ℕ) (hC : 2 ^ (2 * g) ≤ C)
    (rows : Fin 4 → Vector (Fin n) g) (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g) :
    (prepare rows families hsize).1.2 ≤ inputScale I ^ 2 * C := by
  have hCpos : 1 ≤ C := (Nat.one_le_two_pow).trans hC
  have hu : n + 1 ≤ inputScale I := by unfold inputScale; omega
  have hcoef : 880 + 16 * (g + 4) + 70 ≤ inputScale I ^ 2 := by
    nlinarith only [hu, hg, hn]
  have hm := Nat.mul_le_mul_left (16 * (g + 4) + 70) hCpos
  have hp := Nat.mul_le_mul_left 880 hC
  have hw := prepare_work rows families hsize
  calc
    (prepare rows families hsize).1.2 ≤ (880 + 16 * (g + 4) + 70) * C := by
      nlinarith only [hw, hm, hp]
    _ ≤ inputScale I ^ 2 * C := Nat.mul_le_mul_right C hcoef

theorem prepare_cells_scale (I : Instance n) (hn : 10000 ≤ n) (hg : g ≤ n)
    (C : ℕ) (hC : 2 ^ (2 * g) ≤ C)
    (rows : Fin 4 → Vector (Fin n) g) (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g) :
    (prepare rows families hsize).2 ≤ inputScale I ^ 2 * C := by
  have hCpos : 1 ≤ C := (Nat.one_le_two_pow).trans hC
  have hu : n + 1 ≤ inputScale I := by unfold inputScale; omega
  have hcoef : 512 + 64 * (g + 5) ≤ inputScale I ^ 2 := by
    nlinarith only [hu, hg, hn]
  have hm := Nat.mul_le_mul_left (64 * (g + 5)) hCpos
  have hp := Nat.mul_le_mul_left 512 hC
  have hw := prepare_cells rows families hsize
  calc
    (prepare rows families hsize).2 ≤ (512 + 64 * (g + 5)) * C := by
      nlinarith only [hw, hm, hp]
    _ ≤ inputScale I ^ 2 * C := Nat.mul_le_mul_right C hcoef

/-- Four shared coordinate vectors and four sampled arrays remain resident. -/
def retainedInputs (families : Fin 4 → Array (Fin (2 ^ g))) : ℕ :=
  (families 0).size + (families 1).size + (families 2).size + (families 3).size + 4 * g + 12

theorem retainedInputs_le (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g) :
    retainedInputs families ≤ 44 * 2 ^ (2 * g) + 4 * g + 12 := by
  have h0 := hsize 0
  have h1 := hsize 1
  have h2 := hsize 2
  have h3 := hsize 3
  have hm : 2 ^ g ≤ 2 ^ (2 * g) := Nat.pow_le_pow_right (by decide) (by omega)
  unfold retainedInputs
  omega

theorem prepare_cells_with_inputs (I : Instance n) (hn : 10000 ≤ n) (hg : g ≤ n)
    (C : ℕ) (hC : 2 ^ (2 * g) ≤ C)
    (rows : Fin 4 → Vector (Fin n) g) (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g) :
    (prepare rows families hsize).2 + retainedInputs families ≤ inputScale I ^ 2 * C := by
  have ht := prepare_cells rows families hsize
  have hi := retainedInputs_le families hsize
  have hCpos : 1 ≤ C := (Nat.one_le_two_pow).trans hC
  have hu : n + 1 ≤ inputScale I := by unfold inputScale; omega
  have hcoef : 556 + 68 * g + 332 ≤ inputScale I ^ 2 := by
    nlinarith only [hu, hg, hn]
  have hm := Nat.mul_le_mul_left (68 * g + 332) hCpos
  have hp := Nat.mul_le_mul_left 556 hC
  calc
    _ ≤ (556 + 68 * g + 332) * C := by nlinarith only [ht, hi, hm, hp]
    _ ≤ inputScale I ^ 2 * C := Nat.mul_le_mul_right C hcoef

end LowSpaceSubsetSum.PreparedIncidenceCells

end OAI
