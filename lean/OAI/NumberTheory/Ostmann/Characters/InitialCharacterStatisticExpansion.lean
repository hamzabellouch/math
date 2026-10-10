import OAI.NumberTheory.Ostmann.Characters.CharacterRepeatedTuplesPoisson
import OAI.NumberTheory.Ostmann.Characters.CharacterRepeatedTuplesSeries
import OAI.NumberTheory.Ostmann.Characters.InitialCharacterStatisticDouble

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters
open Construction Preliminaries

theorem initialCharacterStatistic_eq_physical_mean {Q b : ℕ}
    (E : Fin b → Finset (PrimeUpTo Q)) (hE : ∀ i, 0 < primeShellMass (E i))
    (χ : Fin b → (q : ℕ) → MulChar (ZMod q) ℂ)
    (a : Fin b → (q : ℕ) → ZMod q) (z : Fin b → ℕ → ℂ)
    (B : (Fin b → PrimeUpTo Q) → ℝ) {X : ℝ} (hX : 0 < X) :
    (initialCharacterStatistic X (initialCharacterMean E hE χ a z B) : ℂ)/(Real.sqrt X : ℂ) =
      (characterTuplePrior (characterDoubleShell E) (characterDoubleShell_positive E hE)).cmean
        (fun w => (characterDoubleMask B w : ℂ)*characterTuplePhysical
          (characterDoubleChar χ) (characterDoubleCenter a) (characterDoublePhase z) X w) := by
  rw [character_physical_mean_eq_sum _ _ _ _ _ _ hX]
  change _ = (∑' n : ℤ, initialCharacterMean (characterDoubleShell E)
    (characterDoubleShell_positive E hE) (characterDoubleChar χ) (characterDoubleCenter a)
    (characterDoublePhase z) (characterDoubleMask B) n *
      SchwartzCutoff.psi ((n : ℝ)/X))/(Real.sqrt X : ℂ)
  have hd (n : ℤ) := characterDoubleMean_eq_norm_sq E hE χ a z B n
  simp_rw [hd]
  congr 1
  unfold initialCharacterStatistic
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  have hreal : ((SchwartzCutoff.psi ((n : ℝ)/X)).re : ℂ) =
      SchwartzCutoff.psi ((n : ℝ)/X) := by
    apply Complex.ext <;> simp [SchwartzCutoff.psi_im]
  rw [Complex.ofReal_mul, hreal, mul_comm]

theorem initialCharacterStatistic_eq_distinct_add_repeated {Q b : ℕ}
    (E : Fin b → Finset (PrimeUpTo Q)) (hE : ∀ i, 0 < primeShellMass (E i))
    (χ : Fin b → (q : ℕ) → MulChar (ZMod q) ℂ)
    (a : Fin b → (q : ℕ) → ZMod q) (z : Fin b → ℕ → ℂ)
    (B : (Fin b → PrimeUpTo Q) → ℝ) {X : ℝ} (hX : 0 < X) :
    (initialCharacterStatistic X (initialCharacterMean E hE χ a z B) : ℂ)/(Real.sqrt X : ℂ) =
      characterDistinctContribution (characterDoubleShell E) (characterDoubleShell_positive E hE)
        (characterDoubleChar χ) (characterDoubleCenter a) (characterDoublePhase z)
        (characterDoubleMask B) X +
      characterRepeatedContribution (characterDoubleShell E) (characterDoubleShell_positive E hE)
        (characterDoubleChar χ) (characterDoubleCenter a) (characterDoublePhase z)
        (characterDoubleMask B) X := by
  rw [initialCharacterStatistic_eq_physical_mean E hE χ a z B hX,
    character_physical_mean_eq_distinct_add_repeated]

end Ostmann.Characters

end

end OAI
