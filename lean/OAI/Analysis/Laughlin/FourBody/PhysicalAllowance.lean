import OAI.Analysis.Laughlin.FourBody.LocalNormalization
import OAI.Analysis.Laughlin.FourBody.TransferConjugation
import OAI.Analysis.Laughlin.Operators.WeightedOccupationNorm

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators
open Spin

theorem source_fourBody_normalized_allowance (Q r D : ℕ) (hr : r ≤ D) (hor : Odd r)
    (hQ : D+2 ≤ Q) (x : Space Q) :
    occupationNormSq Q (physicalFourCopyEnd Q r D (by omega) x) ≤
      ∑ b : LocalFourIndex D, occupationNormSq Q (sourcePairEnd Q b.val.1.val x) := by
  simp only [physicalFourCopyEnd,LinearMap.sum_apply,LinearMap.smul_apply]
  apply (normalized_occupation_sum_bound Q
    (fun b : LocalFourIndex D => fourBodyCoefficient Q r D D b.val.1.val b.val.2.1.val b.val.2.2.val)
    (fun b => sourceFourEnd Q b.val.1.val ⟨b.val.2.1.val,by omega⟩ ⟨b.val.2.2.val,by omega⟩ x)
    (source_fourBody_local_normalization Q r D hr hor hQ)).trans
  apply Finset.sum_le_sum
  intro b hb
  exact sourceFour_normSq_le_pair Q b.val.1.val _ _ x

end Laughlin.Fock

end OAI
