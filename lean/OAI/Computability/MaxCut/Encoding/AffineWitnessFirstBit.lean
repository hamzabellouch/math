import Mathlib
import OAI.Computability.MaxCut.Games.MatrixGap
import OAI.Computability.MaxCut.Games.AffineWitness

namespace OAI

namespace MaxCutGames.Inverse.AffineWitness

theorem first_bit_witness {m ℓ r : ℕ}
    (e : (Fin m → F2) →ₗ[F2] F2)
    (A : (Fin ℓ → F2) →ₗ[F2] (Fin r → F2))
    (Z : Submodule F2 (Fin m → F2))
    (M₀ : (Fin m → F2) →ₗ[F2] (Fin ℓ → F2))
    (z : Fin m → F2) (u : Fin ℓ → F2)
    (F : ((Fin m → F2) →ₗ[F2] (Fin ℓ → F2)) → (Fin ℓ → F2))
    (hfold : ∀ (h : A.ker) M, F (shift e h M) = F M + h)
    (α : ℝ) (hα : 0 < α)
    (hgood : α / 2 ≤
      (Nat.card {M : Slice A Z M₀ // F M = M.val z + u} : ℝ) /
        (Nat.card (Slice A Z M₀) : ℝ))
    (hsmall : 1 / (2 : ℝ) ^ (ℓ - r) < α / 8) :
    ∃ z' : Fin m → F2, ∃ u' : Fin ℓ → F2, e z' = 1 ∧
      ∀ M, InSlice A Z M₀ M → M z' + u' = M z + u := by
  have hpow : (0 : ℝ) < 2 ^ (ℓ - r) := pow_pos (by norm_num) _
  have hsep := (div_lt_iff₀ hpow).mp hsmall
  have hk : (2 : ℝ) ^ (ℓ - r) ≤ (Nat.card A.ker : ℝ) := by
    exact_mod_cast binary_kernel_card_lower A
  have hscale := mul_le_mul_of_nonneg_left hk hα.le
  have hsize : 1 < (α / 2) * (Nat.card A.ker : ℝ) := by
    nlinarith only [hsep, hscale]
  exact normalize_of_density e A Z M₀ z u F hfold (α / 2) hgood hsize

end MaxCutGames.Inverse.AffineWitness

end OAI
