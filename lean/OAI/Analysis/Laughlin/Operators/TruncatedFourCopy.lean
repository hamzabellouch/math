import OAI.Analysis.Laughlin.FourBody.TransferConjugation
import OAI.Analysis.Laughlin.Operators.TruncatedConjugation

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators
open Spin

noncomputable def localFourOperators (Q D : ℕ) (hDQ : D ≤ Q) (b : LocalFourIndex D) : Module.End ℂ (Space Q) :=
  limitFourEnd Q b.val.1.val ⟨b.val.2.1.val,by omega⟩ ⟨b.val.2.2.val,by omega⟩

theorem physicalFourCopyEnd_truncated (Q r D : ℕ) (hDQ : D ≤ Q) (hQ : 24 ≤ Q)
    (hD : D ≤ 23) (x : Space Q) :
    physicalFourCopyEnd Q r D hDQ x = truncatedScalingInv 24 Q
      (∑ b : LocalFourIndex D, (physicalFourBeta Q r D b : ℂ) •
        localFourOperators Q D hDQ b (truncatedScaling 24 Q x)) := by
  simp only [physicalFourCopyEnd,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul,localFourOperators]
  apply Finset.sum_congr rfl
  intro b hb
  rw [truncated_sourceFour_conjugation 24 Q b.val.1.val (by omega) (by omega) (by omega)
    _ _ (by change b.val.2.1.val ≤ 24; omega) (by change b.val.2.2.val ≤ 24; omega)]
  rw [smul_smul]
  congr 1
  simp only [physicalFourBeta]
  push_cast
  ring

theorem localFourOperators_bound (Q D : ℕ) (hDQ : D ≤ Q) (hD : D ≤ 23) (x : Space Q) :
    (∑ b : LocalFourIndex D, occupationNormSq Q (localFourOperators Q D hDQ b x)) ≤
      (Fintype.card (LocalFourIndex D) : ℝ) * limitPairWindow Q x := by
  exact collection_limit_annihilator_bound Q (fun b : LocalFourIndex D => b.val.1.val)
    (fun b => ⟨b.val.2.1.val,by omega⟩) (fun b => ⟨b.val.2.2.val,by omega⟩)
    (fun b => by have := b.val.1.isLt; omega) x

end Laughlin.Fock

end OAI
