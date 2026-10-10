import OAI.Analysis.Laughlin.Exterior.FourConjugation
import OAI.Analysis.Laughlin.FourBody.CoefficientLimit
import OAI.Analysis.Laughlin.Pair.FactorLimit

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Topology
open Filter

abbrev LocalFourIndex (D : ℕ) :=
  {b : Fin (D+1) × Fin (D+1) × Fin (D+1) // b.1.val+b.2.1.val+b.2.2.val=D ∧ b.2.1 < b.2.2}

noncomputable def physicalFourBeta (Q r D : ℕ) (b : LocalFourIndex D) : ℝ :=
  fourBodyCoefficient Q r D D b.val.1.val b.val.2.1.val b.val.2.2.val *
    pairFactor Q b.val.1.val / (modeFactor Q b.val.2.1.val * modeFactor Q b.val.2.2.val)

theorem physicalFourBeta_tendsto (r D : ℕ) (hrD : r ≤ D) (b : LocalFourIndex D) :
    Tendsto (fun Q => physicalFourBeta Q r D b) atTop
      (𝓝 (fourBodyLimitCoefficient r D D b.val.1.val b.val.2.1.val b.val.2.2.val)) := by
  have hs := source_fourBody_coefficient_tendsto r D D b.val.1.val b.val.2.1.val b.val.2.2.val
    hrD (le_refl _) b.property.1
  have hp := pairFactor_tendsto b.val.1.val
  have hj := modeFactor_tendsto b.val.2.1.val
  have hk := modeFactor_tendsto b.val.2.2.val
  have hh := (hs.mul hp).div (hj.mul hk) (by norm_num)
  simp only [mul_one,div_one] at hh
  apply hh.congr
  intro Q
  rfl

end Laughlin.Spin

namespace Laughlin.Fock
open scoped BigOperators
open Spin

noncomputable def physicalFourCopyEnd (Q r D : ℕ) (hDQ : D ≤ Q) : Module.End ℂ (Space Q) :=
  ∑ b : LocalFourIndex D,
    (fourBodyCoefficient Q r D D b.val.1.val b.val.2.1.val b.val.2.2.val : ℂ) •
    sourceFourEnd Q b.val.1.val ⟨b.val.2.1.val,by omega⟩ ⟨b.val.2.2.val,by omega⟩

theorem physicalFourCopyEnd_conjugation (Q r D : ℕ) (hDQ : D ≤ Q) (hQ : 2 ≤ Q)
    (x : Space Q) :
    physicalFourCopyEnd Q r D hDQ x = physicalScalingInv Q
      (∑ b : LocalFourIndex D, (physicalFourBeta Q r D b : ℂ) •
        limitFourEnd Q b.val.1.val ⟨b.val.2.1.val,by omega⟩ ⟨b.val.2.2.val,by omega⟩
          (physicalScaling Q x)) := by
  simp only [physicalFourCopyEnd,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro b hb
  rw [sourceFour_conjugation Q b.val.1.val (by omega) (by omega)]
  rw [smul_smul]
  congr 1
  simp only [physicalFourBeta]
  push_cast
  ring

end Laughlin.Fock

end OAI
