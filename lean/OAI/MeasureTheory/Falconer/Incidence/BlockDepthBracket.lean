import OAI.MeasureTheory.Falconer.Incidence.BlockRegularization

namespace OAI

/-! Bracket any intermediate integer depth by an actual selected block.
The loss is at most the original block size, including truncated end blocks. -/
namespace Falconer.Regularization

theorem blockDepth_bracket {N B i j n : ℕ} (hji : j ≤ i)
    (hlo : blockDepth N B i ≤ n) (hhi : n ≤ blockDepth N B j) :
    ∃ k, j ≤ k ∧ k ≤ i ∧ blockDepth N B k ≤ n ∧ n ≤ blockDepth N B k+B := by
  have hex : ∃ k, j ≤ k ∧ k ≤ i ∧ blockDepth N B k ≤ n := ⟨i,hji,le_rfl,hlo⟩
  let k := Nat.find hex
  have hk : j ≤ k ∧ k ≤ i ∧ blockDepth N B k ≤ n := Nat.find_spec hex
  refine ⟨k,hk.1,hk.2.1,hk.2.2,?_⟩
  by_cases he : k = j
  · rw [he]
    omega
  · have hk0 : 0 < k := by omega
    have hp : n < blockDepth N B (k-1) := by
      by_contra hn
      have hm := Nat.find_min hex (show k-1 < k by omega)
      exact hm ⟨by omega,by omega,by omega⟩
    have hgap := blockDepth_gap N B (k-1)
    have horder := blockDepth_antitone N B (show k-1 ≤ k by omega)
    rw [Nat.sub_add_cancel hk0] at hgap
    omega

end Falconer.Regularization

end OAI
