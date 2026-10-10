import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationKeys
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationSamplerCoupling

namespace OAI

/-! # Reading the sampled sign bits into a bounded stored mask -/

namespace LowSpaceSubsetSum.SignMaskExecution

def run (n : ℕ) (bits : Fin n → Bool) : IndexedMask n × ℕ :=
  let indices := (List.finRange n).filter bits
  (⟨indices, by
    simpa only [List.length_finRange] using List.length_filter_le bits (List.finRange n)⟩,
    4 * n + 2)

theorem value (n : ℕ) (bits : Fin n → Bool) :
    (run n bits).1.semantic = bitsSubsetEquiv n bits := by
  ext i
  simp only [run, IndexedMask.semantic, List.mem_toFinset, List.mem_filter,
    List.mem_finRange, true_and, bitsSubsetEquiv, Equiv.coe_fn_mk, Finset.mem_filter,
    Finset.mem_univ]

theorem work (n : ℕ) (bits : Fin n → Bool) : (run n bits).2 = 4 * n + 2 := rfl

def cells (n : ℕ) (bits : Fin n → Bool) : ℕ :=
  n + (run n bits).1.indices.length + 4

theorem cells_le (n : ℕ) (bits : Fin n → Bool) : cells n bits ≤ 2 * n + 4 := by
  have h := (run n bits).1.length_le
  unfold cells
  omega

end LowSpaceSubsetSum.SignMaskExecution

end OAI
