import OAI.Combinatorics.LowSpaceSubsetSum.Storage.PermutationSubsetCode
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.PermutationDigitsExecution
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationSamplerExecution

namespace OAI

/-! # Executed fixed-size samples as bounded integer mask codes -/

noncomputable section

namespace LowSpaceSubsetSum.FixedSizeCodeExecution

def run (n g k : ℕ) (s : (permutationCoupling n g).Seed) : Option (Fin (2 ^ g)) × ℕ :=
  let digits := PermutationDigitsExecution.run n g s
  match digits.value with
  | none => (none, digits.reads + 1)
  | some d =>
    let v := PermutationArray.build g d
    let out := PermutationSubsetCode.pack v.1 k
    (some out.1, digits.reads + v.2 + out.2 + 2)

theorem value (n g k : ℕ) (hk : k ≤ g) (s : (permutationCoupling n g).Seed) :
    (run n g k s).1 = ((SamplerExecution.fixedSize n g k hk).run s).value.map
      (fun x => SeparatorStoredMasks.code x.val) := by
  have hp := PermutationDigitsExecution.value n g s
  simp only [SamplerExecution.fixedSize, SamplerExecution.subset, SamplerExecution.map,
    Option.map_map]
  rw [← hp]
  cases hd : (PermutationDigitsExecution.run n g s).value with
  | none => simp only [run, hd, Option.map_none]
  | some d =>
    simp only [run, hd, Option.map_some]
    congr 1
    exact PermutationSubsetCode.pack_value _ _ (PermutationArray.build_value g d) k hk

theorem work (n g k : ℕ) (s : (permutationCoupling n g).Seed) :
    (run n g k s).2 ≤ g * n ^ 3 + 32 * (g + 1) ^ 3 := by
  have hd := PermutationDigitsExecution.counts n g s
  simp only [run]
  split
  · dsimp only; nlinarith only [hd.1, Nat.zero_le (g ^ 2), Nat.zero_le (g ^ 3)]
  next d _ =>
    have hv := PermutationArray.build_work g d
    have hp := PermutationSubsetCode.pack_work (PermutationArray.build g d).1 k
    change _ + _ + _ + 2 ≤ _
    nlinarith only [hd.1, hv, hp, Nat.zero_le (g ^ 2), Nat.zero_le (g ^ 3)]

end LowSpaceSubsetSum.FixedSizeCodeExecution

end

end OAI
