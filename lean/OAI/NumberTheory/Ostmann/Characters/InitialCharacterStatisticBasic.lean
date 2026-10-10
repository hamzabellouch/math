import OAI.NumberTheory.Ostmann.Characters.CharacterRepeatedTuplesDefs
import OAI.NumberTheory.Ostmann.Construction.SmoothedStatistic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters
open Construction Preliminaries

def initialCharacterMean {Q b : ℕ} (E : Fin b → Finset (PrimeUpTo Q))
    (hE : ∀ i, 0 < primeShellMass (E i))
    (χ : Fin b → (q : ℕ) → MulChar (ZMod q) ℂ)
    (a : Fin b → (q : ℕ) → ZMod q) (z : Fin b → ℕ → ℂ)
    (B : (Fin b → PrimeUpTo Q) → ℝ) (n : ℤ) : ℂ :=
  (characterTuplePrior E hE).cmean (fun w => (B w : ℂ)*characterTupleTest χ a z w n)

def initialCharacterStatistic (X : ℝ) (F : ℤ → ℂ) : ℝ :=
  ∑' n : ℤ, (SchwartzCutoff.psi ((n : ℝ)/X)).re*‖F n‖^2

theorem characterTupleTest_norm_le_one {Q b : ℕ}
    (χ : Fin b → (q : ℕ) → MulChar (ZMod q) ℂ)
    (a : Fin b → (q : ℕ) → ZMod q) (z : Fin b → ℕ → ℂ)
    (w : Fin b → PrimeUpTo Q) (hz : ∀ i, ‖z i (w i).val‖ ≤ 1) (n : ℤ) :
    ‖characterTupleTest χ a z w n‖ ≤ 1 := by
  rw [characterTupleTest, norm_prod]
  apply Finset.prod_le_one₀ (fun i _ => norm_nonneg _)
  intro i hi
  let : Fact (w i).val.Prime := ⟨primeUpTo_prime (w i)⟩
  exact phasedCharacter_norm_le_one _ _ (hz i) _

theorem initialCharacterMean_norm_le_one {Q b : ℕ}
    (E : Fin b → Finset (PrimeUpTo Q)) (hE : ∀ i, 0 < primeShellMass (E i))
    (χ : Fin b → (q : ℕ) → MulChar (ZMod q) ℂ)
    (a : Fin b → (q : ℕ) → ZMod q) (z : Fin b → ℕ → ℂ)
    (hz : ∀ i, ∀ p ∈ E i, ‖z i p.val‖ ≤ 1)
    (B : (Fin b → PrimeUpTo Q) → ℝ) (hB : ∀ w, |B w| ≤ 1) (n : ℤ) :
    ‖initialCharacterMean E hE χ a z B n‖ ≤ 1 := by
  classical
  let μ := characterTuplePrior E hE
  apply (μ.norm_cmean_le _).trans
  change (∑ w, μ.mass w*‖(B w : ℂ)*characterTupleTest χ a z w n‖) ≤ 1
  rw [← μ.mass_total]
  apply Finset.sum_le_sum
  intro w hw
  by_cases hs : ∀ i, w i ∈ E i
  · have hn := characterTupleTest_norm_le_one χ a z w (fun i => hz i (w i) (hs i)) n
    have hb : ‖(B w : ℂ)*characterTupleTest χ a z w n‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_mul (hB w) hn (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    exact mul_le_of_le_one_right (μ.mass_nonneg w) hb
  · have hm := characterTuplePrior_mass_eq_zero E hE w hs
    change μ.mass w = 0 at hm
    simp [hm]

theorem initialCharacterStatistic_summable {X M : ℝ} (hX : 0 < X) (hM : 0 ≤ M)
    (F : ℤ → ℂ) (hF : ∀ n, ‖F n‖ ≤ M) :
    Summable (fun n : ℤ => (SchwartzCutoff.psi ((n : ℝ)/X)).re*‖F n‖^2) :=
  smoothedStatistic_summable hX hM (fun n => ‖F n‖)
    (fun n => by simpa only [abs_of_nonneg (norm_nonneg _)] using hF n)

theorem exists_initialCharacterStatistic_constant : ∃ cψ : ℝ, 0 < cψ ∧
    ∀ {Q b : ℕ} (E : Fin b → Finset (PrimeUpTo Q)) (hE : ∀ i, 0 < primeShellMass (E i))
      (χ : Fin b → (q : ℕ) → MulChar (ZMod q) ℂ)
      (a : Fin b → (q : ℕ) → ZMod q) (z : Fin b → ℕ → ℂ)
      (B : (Fin b → PrimeUpTo Q) → ℝ) (H : Finset ℤ) (X α : ℝ),
      (∀ i, ∀ p ∈ E i, ‖z i p.val‖ ≤ 1) → (∀ w, |B w| ≤ 1) →
      0 < X → 0 ≤ α → (∀ n ∈ H, |(n : ℝ)/X| ≤ 1) →
      (∀ n ∈ H, α ≤ ‖initialCharacterMean E hE χ a z B n‖) →
      cψ*(H.card : ℝ)*α^2 ≤ initialCharacterStatistic X (initialCharacterMean E hE χ a z B) := by
  obtain ⟨cψ,hc,hstat⟩ := exists_cutoff_statistic_constant
  refine ⟨cψ,hc,?_⟩
  intro Q b E hE χ a z B H X α hz hB hX hα hH hgood
  apply hstat X 1 α (fun n => ‖initialCharacterMean E hE χ a z B n‖) H hX zero_le_one
    (fun n => by simpa only [abs_of_nonneg (norm_nonneg _)] using
      initialCharacterMean_norm_le_one E hE χ a z hz B hB n) hα hH
  simpa only [Finset.sum_const, nsmul_eq_mul] using
    Finset.sum_le_sum (s := H) (fun n hn => hgood n hn)

end Ostmann.Characters

end

end OAI
