import OAI.Probability.SATComputability.SignLaw

namespace OAI

namespace FixedClauseThreshold.Computability
open DilutedSpinGlass
open scoped BigOperators

noncomputable def signFeature {n : ℕ} (P : FiniteLaw (Fin n → Spin)) : ℝ :=
  (FiniteLaw.uniform : FiniteLaw Bool).expect fun J =>
    P.expect (fun s => ∏ a, literalFactor J (s a))

theorem signFeature_nonneg {n : ℕ} (P : FiniteLaw (Fin n → Spin)) :
    0 ≤ signFeature P := by
  apply FiniteLaw.expect_nonneg
  intro J
  apply FiniteLaw.expect_nonneg
  intro s
  exact Finset.prod_nonneg (fun _ _ => literalFactor_nonneg _ _)

theorem signFeature_cubic_nonnegative {n : ℕ} {β : ℝ} (hβ : 0 ≤ β)
    (j : Fin 3) (P B : FiniteLaw (Fin n → Spin)) :
    0 ≤ (1 - Real.exp (-β))^n * (∏ _ : Fin 3, signFeature P) -
      3 * ((1 - Real.exp (-β))^n *
        ∏ l : Fin 3, signFeature (if l = j then P else B)) +
      2 * ((1 - Real.exp (-β))^n * ∏ _ : Fin 3, signFeature B) := by
  have he : 0 ≤ 1 - Real.exp (-β) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have hp := signFeature_nonneg P
  have hb := signFeature_nonneg B
  have hid : (1 - Real.exp (-β))^n * (∏ _ : Fin 3, signFeature P) -
      3 * ((1 - Real.exp (-β))^n *
        ∏ l : Fin 3, signFeature (if l = j then P else B)) +
      2 * ((1 - Real.exp (-β))^n * ∏ _ : Fin 3, signFeature B) =
      (1 - Real.exp (-β))^n * (signFeature P - signFeature B)^2 *
        (signFeature P + 2 * signFeature B) := by
    fin_cases j <;> simp [Fin.prod_univ_three] <;> ring
  rw [hid]
  positivity

end FixedClauseThreshold.Computability

end OAI
