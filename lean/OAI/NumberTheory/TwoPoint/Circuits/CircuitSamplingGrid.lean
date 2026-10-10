import OAI.NumberTheory.TwoPoint.Circuits.CircuitIsolation
import OAI.NumberTheory.TwoPoint.Bounds.IndependentSampling

namespace OAI

/-! A logarithmic grid of repeated Bernoulli samplers isolates a member of
every nonempty marked set, with failure at most `(7/8)^s`. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def dyadicCubeLaw (n a : ℕ) : FiniteLaw (BooleanCube n) :=
  bernoulliCubeLaw n (1 / (2 : ℝ) ^ a) (by positivity)
    (by
      have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ a := one_le_pow₀ (by norm_num)
      simpa only [div_one] using
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hpow)

abbrev GateSamplingChoices (n k s : ℕ) := Fin (Nat.log 2 k + 3) → Fin s → BooleanCube n

noncomputable def gateSamplingLaw (n k s : ℕ) : FiniteLaw (GateSamplingChoices n k s) :=
  FiniteLaw.independent (fun a : Fin (Nat.log 2 k + 3) =>
    FiniteLaw.independent (fun _ : Fin s => dyadicCubeLaw n a.val))

theorem gateSamplingLaw_failure (n k s : ℕ) (S : Finset (Fin n))
    (hS : S.Nonempty) (hSk : S.card ≤ k) :
    (gateSamplingLaw n k s).probability
      (fun x => ∀ a i, ¬isolatesOne S (x a i)) ≤ (7 / 8 : ℝ) ^ s := by
  obtain ⟨a, ha, hhit⟩ := exists_dyadic_single_hit k S.card hS.card_pos hSk
  let a₀ : Fin (Nat.log 2 k + 3) := ⟨a, by omega⟩
  have hsingle : (1 / 8 : ℝ) ≤ (dyadicCubeLaw n a).probability (isolatesOne S) := by
    simpa only [dyadicCubeLaw, bernoulliCubeLaw_isolatesOne] using hhit
  calc
    _ = ∏ b : Fin (Nat.log 2 k + 3),
      (FiniteLaw.independent (fun _ : Fin s => dyadicCubeLaw n b.val)).probability
        (fun x => ∀ i, ¬isolatesOne S (x i)) :=
      FiniteLaw.independent_probability_all _ _
    (∏ b : Fin (Nat.log 2 k + 3),
      (FiniteLaw.independent (fun _ : Fin s => dyadicCubeLaw n b.val)).probability
        (fun x => ∀ i, ¬isolatesOne S (x i))) ≤
        ∏ b : Fin (Nat.log 2 k + 3), if b = a₀ then (7 / 8 : ℝ) ^ s else 1 := by
      apply prod_le_prod₀
      · intro b _
        exact FiniteLaw.probability_nonneg _ _
      · intro b _
        by_cases hb : b = a₀
        · subst b
          rw [ite_eq_left rfl]
          exact (dyadicCubeLaw n a).independent_failure_le (isolatesOne S) s hsingle
        · rw [ite_eq_right hb]
          exact FiniteLaw.probability_le_one _ _
    _ = (7 / 8 : ℝ) ^ s := by simp

end TwoPointCorrelations

end OAI
