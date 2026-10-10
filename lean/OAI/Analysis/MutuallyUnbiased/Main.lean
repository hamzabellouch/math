import OAI.Analysis.MutuallyUnbiased.Certificate.Comparison
import OAI.Analysis.MutuallyUnbiased.MixedData.Main
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical296
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical299
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical300
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical301
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical302
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical303
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical304
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical305
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical306
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical307
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.GroupedColumns4
import OAI.Analysis.MutuallyUnbiased.PairData.Main
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Boundaries
import OAI.Analysis.MutuallyUnbiased.Results.Bounds

namespace OAI

namespace MUB6

theorem fourier_and_family_bound :
    (∀ H : CMatrix, IsHadamard H → ¬Equivalent H tao →
      ∀ π : Equiv.Perm Coord, g H (permuteCharge π alpha) = 0) ∧
    (∀ n : ℕ, Attainable n → n ≤ 5) := by
  constructor
  · intro H hH hTao π
    exact fourier_vanishing hH hTao π
  · exact family_size_le_five

end MUB6

end OAI
