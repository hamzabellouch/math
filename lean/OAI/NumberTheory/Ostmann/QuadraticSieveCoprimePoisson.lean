import OAI.NumberTheory.Ostmann.QuadraticSieveCoprimePoissonExact

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped SchwartzMap FourierTransform

theorem coprime_poisson_truncated (ψ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (X X₁ X₂ J L : ℝ),
      2 ≤ k → 0 < X₁ → X₁ ≤ X → X ≤ X₂ → 0 < J →
      J ≤ min (X / X₁) (X₂ / X) → (X₂ / X) ^ 2 ≤ L →
      ‖(∑' n : ℤ, if Nat.Coprime n.natAbs k then ψ ((n : ℝ) / X) else 0) -
        coprimePoissonMain ψ k X X₁ X₂ L‖ ≤ C * X / J ^ A := by
  obtain ⟨C₁, hC₁, hlarge⟩ := largeDivisorError_bound ψ A
  obtain ⟨C₂, hC₂, hsmall⟩ := smallDivisorError_bound ψ A
  obtain ⟨C₃, hC₃, hmiddle⟩ := middleDivisorError_bound ψ A
  refine ⟨C₁ + C₂ + C₃, by positivity, ?_⟩
  intro k X X₁ X₂ J L hk hX₁ hX₁X hXX₂ hJ hJmin hL
  have hX : 0 < X := hX₁.trans_le hX₁X
  have hX₂ : 0 < X₂ := hX.trans_le hXX₂
  have hLp : 0 < L := (sq_pos_of_pos (div_pos hX₂ hX)).trans_le hL
  have heq := coprime_lattice_eq_approx_add_errors ψ k (by omega) X X₁ X₂ L
    hX (hX₁X.trans hXX₂) hLp.le
  rw [coprimePoissonApprox_eq_main ψ k hk X X₁ X₂ L] at heq
  have hdiff : (∑' n : ℤ, if Nat.Coprime n.natAbs k then ψ ((n : ℝ) / X) else 0) -
      coprimePoissonMain ψ k X X₁ X₂ L =
        largeDivisorError ψ k X X₂ + smallDivisorError ψ k X X₁ +
          middleDivisorError ψ k X X₁ X₂ L := by
    linear_combination heq
  rw [hdiff]
  calc
    _ ≤ ‖largeDivisorError ψ k X X₂‖ + ‖smallDivisorError ψ k X X₁‖ +
        ‖middleDivisorError ψ k X X₁ X₂ L‖ := norm_add₃_le
    _ ≤ C₁ * X / J ^ A + C₂ * X / J ^ A + C₃ * X / J ^ A :=
      add_le_add (add_le_add
        (hlarge k X X₂ J hX hXX₂ hJ (hJmin.trans (min_le_right _ _)))
        (hsmall k X X₁ J hX₁ hX₁X hJ (hJmin.trans (min_le_left _ _))))
        (hmiddle k X X₁ X₂ J L hX hXX₂ hJ (hJmin.trans (min_le_right _ _)) hL)
    _ = _ := by ring

end Ostmann.QuadraticSieve

end OAI
