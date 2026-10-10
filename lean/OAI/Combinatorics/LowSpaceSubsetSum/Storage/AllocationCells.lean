import OAI.Combinatorics.LowSpaceSubsetSum.Storage.ComputedFuelCells
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationAllocationExecution

namespace OAI

/-! # Constant-state integer allocation and its six stored widths -/

namespace LowSpaceSubsetSum.AllocationCells

open scoped BigOperators

def logarithm : ℕ → ℕ → ℕ → ℕ → (ℕ × ℕ) × ℕ
  | 0, _, value, work => ((value, work+1), 8)
  | fuel+1, x, value, work =>
    if 2 ≤ x then logarithm fuel (x/2) (value+1) (work+3)
    else ((value, work+1), 8)

theorem logarithm_value (fuel x value work : ℕ) :
    (logarithm fuel x value work).1 = MeasuredLog2.loop fuel x value work := by
  induction fuel generalizing x value work with
  | zero => rfl
  | succ fuel ih => simp only [logarithm, MeasuredLog2.loop]; split <;> simp_all only

theorem logarithm_cells (fuel x value work : ℕ) : (logarithm fuel x value work).2 ≤ 8 := by
  induction fuel generalizing x value work with
  | zero => exact le_rfl
  | succ fuel ih => simp only [logarithm]; split <;> simp_all only [le_refl]

def bits (m k : ℕ) : (ℕ × ℕ) × ℕ :=
  let choose := ComputedFuelCells.choose m k
  let log := logarithm m choose.1.value 0 0
  ((log.1.1, 8*choose.1.steps+log.1.2+8), choose.2+log.2+16)

theorem bits_value (m k : ℕ) : (bits m k).1 = RepresentationAllocationExecution.bits m k := by
  simp only [bits, ComputedFuelCells.choose_value, logarithm_value,
    RepresentationAllocationExecution.bits, MeasuredLog2.run]

theorem bits_cells (m k : ℕ) : (bits m k).2 ≤ 40 := by
  have hc := ComputedFuelCells.choose_cells m k
  have hl := logarithm_cells m (ComputedFuelCells.choose m k).1.value 0 0
  change _+_+16 ≤ _
  omega

def run (n : ℕ) (guesses : Vector ℕ 3) : (Vector ℕ 8 × ℕ) × ℕ :=
  let bs := Vector.ofFn (fun side : Fin 2 => Vector.ofFn (fun j : Fin 3 =>
    bits (mixerSize n) (if side = 0 then guesses[j.val] else mixerSize n/2-guesses[j.val])))
  let counts := computedLeafCounts (representationBackgroundSize n)
    bs[0][0].1.1 bs[1][0].1.1 bs[0][1].1.1 bs[1][1].1.1 bs[0][2].1.1 bs[1][2].1.1
  ((Vector.ofFn counts, (∑ side : Fin 2, ∑ j : Fin 3, bs[side.val][j.val].1.2)+100),
    (∑ side : Fin 2, ∑ j : Fin 3, bs[side.val][j.val].2)+64)

theorem value (n : ℕ) (guesses : Vector ℕ 3) :
    (run n guesses).1 = RepresentationAllocationExecution.run n guesses := by
  simp only [run, RepresentationAllocationExecution.run, Vector.getElem_ofFn, bits_value]

theorem cells (n : ℕ) (guesses : Vector ℕ 3) : (run n guesses).2 ≤ 304 := by
  have h := Finset.sum_le_sum (fun side (_ : side ∈ (Finset.univ : Finset (Fin 2))) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) =>
      bits_cells (mixerSize n) (if side = 0 then guesses[j.val] else mixerSize n/2-guesses[j.val])))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  simp only [run, Vector.getElem_ofFn, Fin.eta]
  omega

end LowSpaceSubsetSum.AllocationCells

end OAI
