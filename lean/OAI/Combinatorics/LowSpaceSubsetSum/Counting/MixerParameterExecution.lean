import OAI.Combinatorics.LowSpaceSubsetSum.Streams.MeasuredLog2
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.MixerOrderExecution

namespace OAI

/-! # Integer mixer parameter arithmetic after the measured counts

The count logarithms are computed by bounded division loops. Sorting and
all four prime-width formulas then use only stored integers.
-/

namespace LowSpaceSubsetSum.MixerParameterExecution

open scoped BigOperators

def low (n half count : ℕ) : ℕ × ℕ :=
  let bits := MeasuredLog2.run n count
  (max (rationalLowParameter n half) (bits.1 / 2), bits.2 + 12)

theorem low_value (n half count : ℕ) (hc : count ≤ 2 ^ n) :
    (low n half count).1 = lowParameterFromCount n half count := by
  simp only [low, MeasuredLog2.run_value n count hc, lowParameterFromCount]

theorem low_work (n half count : ℕ) : (low n half count).2 ≤ 3 * n + 13 := by
  have h := MeasuredLog2.run_work n count
  change _ + 12 ≤ _
  omega

structure Parameters where
  order : Vector (Fin 3) 3
  low : Vector ℕ 3
  widths : Vector ℕ 4

def run (n : ℕ) (counts : Vector ℕ 3) : Parameters × ℕ :=
  let order := MixerOrderExecution.run counts
  let lows := Vector.ofFn (fun i : Fin 3 => low n (mixerSize n / 2) counts[order.1[i.val].val])
  let lowValues := lows.map Prod.fst
  let widths : Vector ℕ 4 := #v[lowValues[2], lowValues[1] - lowValues[2],
    lowValues[0] - lowValues[1], extraParameterFromLow n (mixerSize n) (fun i => lowValues[i.val])]
  (⟨order.1, lowValues, widths⟩, order.2 + (∑ i : Fin 3, lows[i.val].2) + 30)

theorem order_value (n : ℕ) (counts : Vector ℕ 3) (i : Fin 3) :
    (run n counts).1.order[i.val] = mixerOrderFromCounts (fun j => counts[j.val]) i :=
  MixerOrderExecution.run_value counts i

theorem low_values (n : ℕ) (counts : Vector ℕ 3) (hc : ∀ i : Fin 3, counts[i.val] ≤ 2 ^ n)
    (i : Fin 3) :
    (run n counts).1.low[i.val] = lowParameterFromCount n (mixerSize n / 2)
      counts[(mixerOrderFromCounts (fun j => counts[j.val]) i).val] := by
  simp only [run, Vector.getElem_map, Vector.getElem_ofFn,
    low_value n _ _ (hc _), MixerOrderExecution.run_value]

theorem low_values_of_counts (n : ℕ) (counts : Vector ℕ 3)
    (hc : ∀ i : Fin 3, counts[i.val] ≤ 2 ^ n) (f : Fin 3 → ℕ)
    (hf : ∀ i : Fin 3, counts[i.val] = f i) (i : Fin 3) :
    (run n counts).1.low[i.val] = lowParameterFromCount n (mixerSize n / 2)
      (f (mixerOrderFromCounts f i)) := by
  rw [low_values n counts hc]
  have he : (fun j : Fin 3 => counts[j.val]) = f := funext hf
  change lowParameterFromCount n (mixerSize n / 2)
    ((fun j : Fin 3 => counts[j.val]) (mixerOrderFromCounts (fun j => counts[j.val]) i)) = _
  rw [he]

theorem widths_value (n : ℕ) (counts : Vector ℕ 3) :
    (run n counts).1.widths = #v[(run n counts).1.low[2],
      (run n counts).1.low[1] - (run n counts).1.low[2],
      (run n counts).1.low[0] - (run n counts).1.low[1],
      extraParameterFromLow n (mixerSize n) (fun i => (run n counts).1.low[i.val])] := rfl

theorem work (n : ℕ) (counts : Vector ℕ 3) : (run n counts).2 ≤ 9 * n + 120 := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
    low_work n (mixerSize n / 2) counts[(MixerOrderExecution.run counts).1[i.val].val])
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  change 40 + (∑ i : Fin 3,
    (low n (mixerSize n / 2) counts[(MixerOrderExecution.run counts).1[i.val].val]).2) + 30 ≤ _
  omega

end LowSpaceSubsetSum.MixerParameterExecution

end OAI
