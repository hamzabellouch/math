import OAI.NumberTheory.Ostmann.Characters.CharacterRepeatedTuplesDefs

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters
open Construction Preliminaries

theorem characterTuplePhysical_summable {Q b : ℕ}
    (χ : Fin b → (q : ℕ) → MulChar (ZMod q) ℂ)
    (a : Fin b → (q : ℕ) → ZMod q) (z : Fin b → ℕ → ℂ)
    (w : Fin b → PrimeUpTo Q) {X : ℝ} (hX : 0 < X) :
    Summable (fun n : ℤ => characterTupleTest χ a z w n*SchwartzCutoff.psi ((n : ℝ)/X)) := by
  have hpsi : Summable (fun n : ℤ => ‖SchwartzCutoff.psi ((n : ℝ)/X)‖) := by
    simpa only [schwartzScale_apply, div_eq_mul_inv] using
      schwartz_int_norm_summable (schwartzScale SchwartzCutoff.psi X⁻¹ (inv_ne_zero hX.ne'))
  have hbound (n : ℤ) : ‖characterTupleTest χ a z w n‖ ≤ ∏ i, ‖z i (w i).val‖ := by
    rw [characterTupleTest, norm_prod]
    apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
    intro i hi
    let : Fact (w i).val.Prime := ⟨primeUpTo_prime (w i)⟩
    rw [phasedCharacter, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_character_le_one _ _)
  apply (hpsi.mul_left (∏ i, ‖z i (w i).val‖)).of_norm_bounded
  intro n
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg _)

theorem character_physical_mean_eq_sum {Q b : ℕ}
    (E : Fin b → Finset (PrimeUpTo Q)) (hE : ∀ i, 0 < primeShellMass (E i))
    (χ : Fin b → (q : ℕ) → MulChar (ZMod q) ℂ)
    (a : Fin b → (q : ℕ) → ZMod q) (z : Fin b → ℕ → ℂ)
    (B : (Fin b → PrimeUpTo Q) → ℝ) {X : ℝ} (hX : 0 < X) :
    (characterTuplePrior E hE).cmean (fun w => (B w : ℂ)*characterTuplePhysical χ a z X w) =
      (∑' n : ℤ, (characterTuplePrior E hE).cmean
        (fun w => (B w : ℂ)*characterTupleTest χ a z w n)*
        SchwartzCutoff.psi ((n : ℝ)/X))/(Real.sqrt X : ℂ) := by
  let μ := characterTuplePrior E hE
  let f := fun (w : Fin b → PrimeUpTo Q) (n : ℤ) =>
    (B w : ℂ)*(characterTupleTest χ a z w n*SchwartzCutoff.psi ((n : ℝ)/X))
  have hs : ∀ w, Summable (f w) := fun w =>
    (characterTuplePhysical_summable χ a z w hX).mul_left _
  have he := Summable.tsum_finsetSum (s := Finset.univ)
    (f := fun w n => (μ.mass w : ℂ)*f w n) (fun w _ => (hs w).mul_left _)
  simp only [tsum_mul_left] at he
  unfold FinitePrior.cmean characterTuplePhysical
  simp only [← mul_div_assoc, ← Finset.sum_div]
  congr 1
  calc
    _ = ∑' n : ℤ, ∑ w, (μ.mass w : ℂ)*f w n := by
      rw [he]
      simp only [f, tsum_mul_left]
      rfl
    _ = _ := by
      apply tsum_congr
      intro n
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro w hw
      dsimp only [f, μ]
      ring

end Ostmann.Characters

end

end OAI
