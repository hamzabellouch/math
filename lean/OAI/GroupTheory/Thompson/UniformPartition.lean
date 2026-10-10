import OAI.GroupTheory.Thompson.BasicPartition
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace OAI

/-!
# Uniform dyadic partitions

The depth-`n` partition consists of all `2^n` basic intervals at that depth.
Coverage includes both endpoints of the unit interval.  Distinct cells have
disjoint open interiors; their closed carriers may share an endpoint.
-/

noncomputable section

namespace ThompsonNonamenability.BasicPartition

open Set

/-- The cell with index `k` in the depth-`n` uniform dyadic partition. -/
def uniformCell (n : ℕ) (k : Fin (2 ^ n)) : BasicInterval :=
  ⟨n, k⟩

@[simp] theorem uniformCell_depth (n : ℕ) (k : Fin (2 ^ n)) :
    (uniformCell n k).depth = n := rfl

@[simp] theorem uniformCell_index (n : ℕ) (k : Fin (2 ^ n)) :
    (uniformCell n k).index = k := rfl

theorem uniformCell_injective (n : ℕ) : Function.Injective (uniformCell n) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun I : BasicInterval => I.index.val) h

/-- All cells at depth `n`, with no repeated intervals. -/
def uniformCells (n : ℕ) : Finset BasicInterval :=
  Finset.univ.map ⟨uniformCell n, uniformCell_injective n⟩

theorem mem_uniformCells {n : ℕ} {I : BasicInterval} :
    I ∈ uniformCells n ↔ ∃ k : Fin (2 ^ n), uniformCell n k = I := by
  simp [uniformCells]

@[simp] theorem uniformCell_mem_uniformCells (n : ℕ) (k : Fin (2 ^ n)) :
    uniformCell n k ∈ uniformCells n :=
  mem_uniformCells.mpr ⟨k, rfl⟩

@[simp] theorem card_uniformCells (n : ℕ) : (uniformCells n).card = 2 ^ n := by
  simp [uniformCells]

/-- At a fixed depth, the interiors of distinct cells are disjoint. -/
theorem uniformCell_disjoint {n : ℕ} {i j : Fin (2 ^ n)} (hij : i ≠ j) :
    Disjoint (uniformCell n i).interior (uniformCell n j).interior := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  change (i.val : ℝ) / (2 : ℝ) ^ n < x ∧
    x < ((i.val : ℝ) + 1) / (2 : ℝ) ^ n at hx
  change (j.val : ℝ) / (2 : ℝ) ^ n < x ∧
    x < ((j.val : ℝ) + 1) / (2 : ℝ) ^ n at hy
  have hd : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hlt | hlt
  · have hstep : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hlt
    have hsep : ((i.val : ℝ) + 1) / (2 : ℝ) ^ n ≤
        (j.val : ℝ) / (2 : ℝ) ^ n :=
      (div_le_div_iff_of_pos_right hd).mpr hstep
    exact (not_lt_of_ge hsep) (lt_trans hy.1 hx.2)
  · have hstep : (j.val : ℝ) + 1 ≤ (i.val : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hlt
    have hsep : ((j.val : ℝ) + 1) / (2 : ℝ) ^ n ≤
        (i.val : ℝ) / (2 : ℝ) ^ n :=
      (div_le_div_iff_of_pos_right hd).mpr hstep
    exact (not_lt_of_ge hsep) (lt_trans hx.1 hy.2)

/-- Every point of `[0,1]` lies in one of the closed depth-`n` cells. -/
theorem uniformCells_cover (n : ℕ) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    ∃ I ∈ uniformCells n, x ∈ I.carrier := by
  have hnat : 0 < (2 : ℕ) ^ n := pow_pos (by decide) n
  have hd : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  by_cases hx1 : x = 1
  · subst x
    have hk : 2 ^ n - 1 < 2 ^ n := Nat.sub_lt hnat (by decide)
    let k : Fin (2 ^ n) := ⟨2 ^ n - 1, hk⟩
    refine ⟨uniformCell n k, uniformCell_mem_uniformCells n k, ?_⟩
    change ((2 ^ n - 1 : ℕ) : ℝ) / (2 : ℝ) ^ n ≤ 1 ∧
      1 ≤ (((2 ^ n - 1 : ℕ) : ℝ) + 1) / (2 : ℝ) ^ n
    have hsucc : (2 ^ n - 1 : ℕ) + 1 = 2 ^ n :=
      Nat.sub_add_cancel hnat
    have hcast : (((2 ^ n - 1 : ℕ) : ℝ) + 1) = (2 : ℝ) ^ n := by
      exact_mod_cast hsucc
    constructor
    · apply (div_le_iff₀ hd).mpr
      linarith
    · rw [hcast, div_self (ne_of_gt hd)]
  · have hlt : x < 1 := lt_of_le_of_ne hx.2 hx1
    have hxD : 0 ≤ x * (2 : ℝ) ^ n := mul_nonneg hx.1 hd.le
    have hbound : x * (2 : ℝ) ^ n < ((2 ^ n : ℕ) : ℝ) := by
      simpa using (mul_lt_mul_of_pos_right hlt hd)
    have hk : ⌊x * (2 : ℝ) ^ n⌋₊ < 2 ^ n :=
      (Nat.floor_lt hxD).mpr hbound
    let k : Fin (2 ^ n) := ⟨⌊x * (2 : ℝ) ^ n⌋₊, hk⟩
    refine ⟨uniformCell n k, uniformCell_mem_uniformCells n k, ?_⟩
    change (⌊x * (2 : ℝ) ^ n⌋₊ : ℝ) / (2 : ℝ) ^ n ≤ x ∧
      x ≤ ((⌊x * (2 : ℝ) ^ n⌋₊ : ℝ) + 1) / (2 : ℝ) ^ n
    constructor
    · exact (div_le_iff₀ hd).mpr (Nat.floor_le hxD)
    · exact (le_div_iff₀ hd).mpr (Nat.lt_floor_add_one _).le

/-- The genuine partition into all depth-`n` dyadic cells. -/
def uniform (n : ℕ) : BasicPartition where
  cells := uniformCells n
  cover := uniformCells_cover n
  disjoint := by
    intro I hI J hJ hIJ
    obtain ⟨i, rfl⟩ := mem_uniformCells.mp hI
    obtain ⟨j, rfl⟩ := mem_uniformCells.mp hJ
    apply uniformCell_disjoint
    intro hij
    exact hIJ (congrArg (uniformCell n) hij)

@[simp] theorem uniform_cells (n : ℕ) : (uniform n).cells = uniformCells n := rfl

@[simp] theorem uniform_cellCount (n : ℕ) : (uniform n).cellCount = 2 ^ n := by
  exact card_uniformCells n

@[simp] theorem uniformCell_length (n : ℕ) (k : Fin (2 ^ n)) :
    (uniformCell n k).length = ((2 : ℝ) ^ n)⁻¹ := rfl

theorem uniform_depth {n : ℕ} {I : BasicInterval} (hI : I ∈ (uniform n).cells) :
    I.depth = n := by
  obtain ⟨k, rfl⟩ := mem_uniformCells.mp hI
  rfl

/-- All cells in the uniform partition have the same positive length. -/
theorem uniform_length {n : ℕ} {I : BasicInterval} (hI : I ∈ (uniform n).cells) :
    I.length = ((2 : ℝ) ^ n)⁻¹ := by
  obtain ⟨k, rfl⟩ := mem_uniformCells.mp hI
  rfl

/-- A uniform grid respects every basic interval resolved at its depth. -/
theorem uniform_respects_of_depth_le (n : ℕ) (I : BasicInterval)
    (hI : I.depth ≤ n) : (uniform n).Respects I := by
  apply ((uniform n).respects_iff I).mpr
  intro K hK hmeet
  apply BasicInterval.contained_of_overlap_of_depth_le
  · rw [uniform_depth hK]
    exact hI
  · simpa only [Set.inter_comm] using hmeet

end ThompsonNonamenability.BasicPartition

end

end OAI
