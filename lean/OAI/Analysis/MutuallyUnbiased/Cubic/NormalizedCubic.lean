import OAI.Analysis.MutuallyUnbiased.Cubic.CubicGraph
import OAI.Analysis.MutuallyUnbiased.Cubic.NormalizedCodes

namespace OAI

noncomputable section

namespace MUB6

theorem normalized_cubic_equivalent_tao {H : CMatrix} (hH : IsHadamard H)
    (hcube : ∀ i j, H i j ^ 3 = 1)
    (h0row : ∀ j, H 0 j = 1) (h0col : ∀ i, H i 0 = 1)
    (hdiag : ∀ i j : Fin 5, H i.succ j.succ = 1 ↔ i = j) : Equivalent H tao := by
  classical
  have hchoice (i : Fin 5) : ∃ a, ∀ j, fiveRowChoice i a j = cubicGraph H i j := by
    apply rowChoice_complete i (cubicGraph H i) ?_ (cubic_graph_degree hH hcube h0row h0col i)
    simp [cubicGraph, (hdiag i i).mpr rfl, Ne.symm omega_ne_one]
  choose a ha using hchoice
  have hagree : ∀ i j, normalizedCodeGraph a i j = cubicGraph H i j := ha
  have horth : normalizedCodeOrthogonal a := by
    intro i j hij
    simpa only [hagree] using cubic_graph_orthogonal hH hcube h0col hdiag i j hij
  obtain ⟨c, hc⟩ := normalizedCodes_classified a horth
  let q := fiveCyclePermutation c
  have hq (i j : Fin 5) : cubicGraph H (q i) (q j) = canonicalFiveCycle i j := by
    simpa only [q, fiveCyclePermutation, Equiv.ofBijective_apply, hagree] using hc i j
  have heq (i j : Coord) : H (fixZeroPermutation q i) (fixZeroPermutation q j) = tao i j := by
    cases i using Fin.cases with
    | zero => fin_cases j <;> simp [h0row, tao, taoExponent]
    | succ i =>
      cases j using Fin.cases with
      | zero => fin_cases i <;> simp [h0col, tao, taoExponent]
      | succ j =>
        simp only [fixZeroPermutation_succ, cubic_graph_entry hcube hdiag, hq,
          Equiv.apply_eq_iff_eq, tao_noninitial]
  refine ⟨fixZeroPermutation q, fixZeroPermutation q, fun _ => 1, fun _ => 1,
    by simp, by simp, ?_⟩
  intro i j
  simpa using (heq i j).symm

end MUB6

end

end OAI
