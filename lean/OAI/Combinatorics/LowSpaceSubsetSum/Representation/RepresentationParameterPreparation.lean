import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationMixerPreparation
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.MixerParameterExecution
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationSamplerWork

namespace OAI

/-! # Actual mixer preparation supplies all four prime widths

Only the stored input and permutation are computational arguments. The sign
set is needed solely to identify the result with the sampling experiment.
-/

namespace LowSpaceSubsetSum.RepresentationParameterPreparation

variable {n : ℕ}

def run (D : RepresentationData n) (v : Vector (Fin n) n) :
    (Vector (List (Fin n)) 3 × MixerParameterExecution.Parameters) × ℕ :=
  let mixers := RepresentationMixerPreparation.run D v
  let out := MixerParameterExecution.run n mixers.1.counts
  ((mixers.1.domains, out.1), mixers.2 + out.2 + 3)

theorem counts_bound (D : RepresentationData n) (v : Vector (Fin n) n)
    (e : Equiv.Perm (Fin n)) (hv : ∀ i : Fin n, v[i.val] = e i) (j : Fin 3) :
    (RepresentationMixerPreparation.run D v).1.counts[j.val] ≤ 2 ^ n := by
  rw [RepresentationMixerPreparation.counts_value D v e hv]
  exact (distinctSumCount_le_pow _ _).trans
    (Nat.pow_le_pow_right (by decide) (by
      simpa only [Fintype.card_fin] using Finset.card_le_univ (permuteSubset e (D.mixers j))))

theorem order_formula (D : RepresentationData n) (v : Vector (Fin n) n)
    (e : Equiv.Perm (Fin n)) (hv : ∀ i : Fin n, v[i.val] = e i) (signs : Finset (Fin n)) :
    mixerOrderFromCounts (fun j => (RepresentationMixerPreparation.run D v).1.counts[j.val]) =
      D.zeroSetup.mixerOrder (e, signs) := by
  rw [D.zeroSetup.mixerOrder_eq_integer]
  congr 1
  funext j
  exact RepresentationMixerPreparation.counts_value D v e hv j

theorem order_value (D : RepresentationData n) (v : Vector (Fin n) n)
    (e : Equiv.Perm (Fin n)) (hv : ∀ i : Fin n, v[i.val] = e i)
    (signs : Finset (Fin n)) (i : Fin 3) :
    (run D v).1.2.order[i.val] = D.zeroSetup.mixerOrder (e, signs) i := by
  change (MixerParameterExecution.run n (RepresentationMixerPreparation.run D v).1.counts).1.order[i.val] = _
  rw [MixerParameterExecution.order_value, order_formula D v e hv signs]

theorem low_value (D : RepresentationData n) (v : Vector (Fin n) n)
    (e : Equiv.Perm (Fin n)) (hv : ∀ i : Fin n, v[i.val] = e i)
    (signs : Finset (Fin n)) (i : Fin 3) :
    (run D v).1.2.low[i.val] = ⌊D.zeroSetup.lowExponent (e, signs) i⌋₊ := by
  change (MixerParameterExecution.run n (RepresentationMixerPreparation.run D v).1.counts).1.low[i.val] = _
  let f := fun j => distinctSumCount D.zeroSetup.originalWeights (D.zeroSetup.rawMixers (e, signs) j)
  have hf (j : Fin 3) : (RepresentationMixerPreparation.run D v).1.counts[j.val] = f j :=
    RepresentationMixerPreparation.counts_value D v e hv j
  have h := MixerParameterExecution.low_values_of_counts n
    (RepresentationMixerPreparation.run D v).1.counts (counts_bound D v e hv) f hf i
  have ho : mixerOrderFromCounts f i = D.zeroSetup.mixerOrder (e, signs) i :=
    congrArg (fun order : Equiv.Perm (Fin 3) => order i)
      (D.zeroSetup.mixerOrder_eq_integer (e, signs)).symm
  calc
    _ = lowParameterFromCount n (mixerSize n / 2) (f (mixerOrderFromCounts f i)) := h
    _ = lowParameterFromCount n (mixerSize n / 2) (f (D.zeroSetup.mixerOrder (e, signs) i)) :=
      congrArg (fun j => lowParameterFromCount n (mixerSize n / 2) (f j)) ho
    _ = _ := (D.zeroSetup.floor_lowExponent_eq_integer (e, signs) i).symm

theorem widths_value (D : RepresentationData n) (v : Vector (Fin n) n)
    (e : Equiv.Perm (Fin n)) (hv : ∀ i : Fin n, v[i.val] = e i)
    (signs : Finset (Fin n)) (i : Fin 4) :
    (run D v).1.2.widths[i.val] = D.zeroSetup.samplerPrimeWidths (e, signs) i := by
  have hw := MixerParameterExecution.widths_value n (RepresentationMixerPreparation.run D v).1.counts
  change (MixerParameterExecution.run n (RepresentationMixerPreparation.run D v).1.counts).1.widths[i.val] = _
  rw [hw]
  fin_cases i
  · exact low_value D v e hv signs 2
  · exact congrArg₂ Nat.sub (low_value D v e hv signs 1) (low_value D v e hv signs 2)
  · exact congrArg₂ Nat.sub (low_value D v e hv signs 0) (low_value D v e hv signs 1)
  · change extraParameterFromLow n (mixerSize n) (fun j => (run D v).1.2.low[j.val]) = _
    change extraParameterFromLow n (mixerSize n) (fun j => (run D v).1.2.low[j.val]) =
      D.zeroSetup.extraPrimeParameter (e, signs)
    rw [D.zeroSetup.extraPrimeParameter_eq_integer]
    congr 1
    funext j
    rw [low_value D v e hv signs, D.zeroSetup.floor_lowExponent_eq_integer]

theorem work (D : RepresentationData n) (hn : 10000 ≤ n) (v : Vector (Fin n) n)
    (e : Equiv.Perm (Fin n)) (hv : ∀ i : Fin n, v[i.val] = e i) :
    (run D v).2 ≤ inputScale D.input ^ 6 * 2 ^ mixerSize n := by
  let u := inputScale D.input
  have hu : n + 1 ≤ u := by dsimp [u, inputScale]; omega
  have hu0 : 10000 ≤ u := by omega
  have hp := RepresentationMixerPreparation.work D hn v e hv
  have hw := MixerParameterExecution.work n (RepresentationMixerPreparation.run D v).1.counts
  have hu2 : 1 ≤ u ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h25 : u ^ 2 ≤ u ^ 5 := pow_le_pow_right' (by omega) (by decide)
  have hsmall : 9 * n + 123 ≤ u ^ 5 := by nlinarith only [hu, hu0, hu2, h25]
  have hT : 1 ≤ 2 ^ mixerSize n := Nat.one_le_two_pow
  have hsmallT := hsmall.trans (Nat.le_mul_of_pos_right _ hT)
  have hf : 2 * u ^ 5 ≤ u ^ 6 := by
    calc
      _ ≤ u * u ^ 5 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  have hfT := Nat.mul_le_mul_right (2 ^ mixerSize n) hf
  change _ + _ + 3 ≤ _
  change (RepresentationMixerPreparation.run D v).2 +
    (MixerParameterExecution.run n (RepresentationMixerPreparation.run D v).1.counts).2 + 3 ≤
      u ^ 6 * 2 ^ mixerSize n
  change (RepresentationMixerPreparation.run D v).2 ≤ u ^ 5 * 2 ^ mixerSize n at hp
  nlinarith only [hp, hw, hsmallT, hfT]

end LowSpaceSubsetSum.RepresentationParameterPreparation

end OAI
