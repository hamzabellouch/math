import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block0
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block0Reindex
import OAI.Analysis.MutuallyUnbiased.GramEntries.Block0
import OAI.Analysis.MutuallyUnbiased.Certificate.GramNonnegative

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6.Certificate.GramAssembly.Block0

theorem indexed_entry_eval (i j : Fin 5) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries i j) (fun k => GramNormalization.eval B (key k)) =
      (GramFunctions.Block0.forms i).mixedGram (GramFunctions.Block0.forms j) B := by
  have he := Integer.Sparse.eval_reindex key (entries i j) (GramNormalization.eval B)
  rw [entries_reindex] at he
  exact he.symm.trans (GramEntries.Block0.entryEval i j B hB)

theorem weights_real (i j : Fin 5) :
    (weights i j : ℝ) = realMatrix GramData.Block0.Z i j := by
  change (weights i j : ℝ) = (GramData.Block0.Z i j : ℝ)
  exact_mod_cast weights_cast i j

theorem polynomial_interpretation (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval polynomial (fun k => GramNormalization.eval B (key k)) =
      GramNonnegative.quadratic0 B := by
  rw [polynomial_eval]
  unfold GramNonnegative.quadratic0
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [indexed_entry_eval i j B hB, weights_real]

end MUB6.Certificate.GramAssembly.Block0

end

end OAI
