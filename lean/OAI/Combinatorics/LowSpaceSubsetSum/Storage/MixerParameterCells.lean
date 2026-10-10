import OAI.Combinatorics.LowSpaceSubsetSum.Counting.MixerParameterExecution

namespace OAI

/-! # Constant-state integer mixer parameter preparation

The logarithm is evaluated by its actual bounded division loop. Sorting
three counts and building the seven scalar parameter fields retain only
fixed-size vectors. The input counts are shared throughout.
-/

namespace LowSpaceSubsetSum.MixerParameterCells

open scoped BigOperators

def logLoop : ℕ → ℕ → ℕ → ℕ → ℕ → (ℕ × ℕ) × ℕ
  | 0, _, value, work, peak => ((value, work+1), max peak 16)
  | fuel+1, x, value, work, peak =>
    if 2 ≤ x then logLoop fuel (x/2) (value+1) (work+3) (max peak 16)
    else ((value, work+1), max peak 16)

theorem logLoop_value (fuel x value work peak : ℕ) :
    (logLoop fuel x value work peak).1 = MeasuredLog2.loop fuel x value work := by
  induction fuel generalizing x value work peak with
  | zero => rfl
  | succ fuel ih =>
    simp only [logLoop, MeasuredLog2.loop]
    split <;> simp only [ih]

theorem logLoop_cells (fuel x value work peak : ℕ) :
    (logLoop fuel x value work peak).2 ≤ max peak 16 := by
  induction fuel generalizing x value work peak with
  | zero => exact le_rfl
  | succ fuel ih =>
    simp only [logLoop]
    split
    · simpa only [max_assoc, max_self] using ih (x/2) (value+1) (work+3) (max peak 16)
    · exact le_rfl

def low (n half count : ℕ) : (ℕ × ℕ) × ℕ :=
  let bits := logLoop n count 0 0 0
  ((max (rationalLowParameter n half) (bits.1.1/2), bits.1.2+12), bits.2+16)

theorem low_value (n half count : ℕ) :
    (low n half count).1 = MixerParameterExecution.low n half count := by
  simp only [low, logLoop_value, MixerParameterExecution.low, MeasuredLog2.run]

theorem low_cells (n half count : ℕ) : (low n half count).2 ≤ 32 := by
  have h := logLoop_cells n count 0 0 0
  simp only [Nat.zero_max] at h
  change _+16 ≤ _
  omega

def run (n : ℕ) (counts : Vector ℕ 3) : (MixerParameterExecution.Parameters × ℕ) × ℕ :=
  let order := MixerOrderExecution.run counts
  let lows := Vector.ofFn (fun i : Fin 3 => low n (mixerSize n/2) counts[order.1[i.val].val])
  let lowValues := lows.map (fun x => x.1.1)
  let widths : Vector ℕ 4 := #v[lowValues[2], lowValues[1]-lowValues[2],
    lowValues[0]-lowValues[1], extraParameterFromLow n (mixerSize n) (fun i => lowValues[i.val])]
  ((⟨order.1, lowValues, widths⟩, order.2+(∑ i : Fin 3, lows[i.val].1.2)+30),
    (∑ i : Fin 3, lows[i.val].2)+32)

theorem run_value (n : ℕ) (counts : Vector ℕ 3) :
    (run n counts).1 = MixerParameterExecution.run n counts := by
  have hmap : (Vector.ofFn (fun i : Fin 3 => low n (mixerSize n/2)
      counts[(MixerOrderExecution.run counts).1[i.val].val])).map (fun x => x.1.1) =
      (Vector.ofFn (fun i : Fin 3 => MixerParameterExecution.low n (mixerSize n/2)
      counts[(MixerOrderExecution.run counts).1[i.val].val])).map Prod.fst := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_ofFn, low_value]
  simp only [run, MixerParameterExecution.run, hmap, Vector.getElem_ofFn, low_value]

theorem run_cells (n : ℕ) (counts : Vector ℕ 3) : (run n counts).2 ≤ 128 := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
    low_cells n (mixerSize n/2) counts[(MixerOrderExecution.run counts).1[i.val].val])
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  change (∑ i : Fin 3,
    (low n (mixerSize n/2) counts[(MixerOrderExecution.run counts).1[i.val].val]).2)+32 ≤ _
  omega

end LowSpaceSubsetSum.MixerParameterCells

end OAI
