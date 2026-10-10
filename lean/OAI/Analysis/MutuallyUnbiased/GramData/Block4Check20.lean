import OAI.Analysis.MutuallyUnbiased.GramData.Block4Data

namespace OAI

namespace MUB6.Certificate.GramData.Block4

open Matrix
open scoped BigOperators

theorem entry_21_18 : Z 21 18 =
    ∑ k : Fin 22, lowerUnit entries k 21 * D k * lowerUnit entries k 18 := by
  decide +kernel

theorem entry_21_19 : Z 21 19 =
    ∑ k : Fin 22, lowerUnit entries k 21 * D k * lowerUnit entries k 19 := by
  decide +kernel

theorem entry_21_20 : Z 21 20 =
    ∑ k : Fin 22, lowerUnit entries k 21 * D k * lowerUnit entries k 20 := by
  decide +kernel

theorem entry_21_21 : Z 21 21 =
    ∑ k : Fin 22, lowerUnit entries k 21 * D k * lowerUnit entries k 21 := by
  decide +kernel

end MUB6.Certificate.GramData.Block4

end OAI
