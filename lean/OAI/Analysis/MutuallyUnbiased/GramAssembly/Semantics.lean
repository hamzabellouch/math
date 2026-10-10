import OAI.Analysis.MutuallyUnbiased.GramAssembly.Combined
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block0Semantics
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block1Semantics
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block2Semantics
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Semantics
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block4Semantics
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block5Semantics

namespace OAI

noncomputable section

namespace MUB6.Certificate.GramAssembly

theorem interpretation (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * Integer.Sparse.eval polynomial (fun k => GramNormalization.eval B (key k)) =
      GramNonnegative.sourceGram B := by
  rw [polynomial, combined4_eval]
  rw [Block0.polynomial_interpretation B hB, Block1.polynomial_interpretation B hB, Block2.polynomial_interpretation B hB, Block3.polynomial_interpretation B hB, Block4.polynomial_interpretation B hB, Block5.polynomial_interpretation B hB]
  norm_num only [GramNonnegative.sourceGram, GramFunctions.Block0.decimalExponent, GramFunctions.Block1.decimalExponent, GramFunctions.Block2.decimalExponent, GramFunctions.Block3.decimalExponent, GramFunctions.Block4.decimalExponent, GramFunctions.Block5.decimalExponent]
  all_goals ring

end MUB6.Certificate.GramAssembly

end

end OAI
