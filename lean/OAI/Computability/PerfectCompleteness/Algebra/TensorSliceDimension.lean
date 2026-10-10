import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.Tactic.NormNum
import OAI.Computability.PerfectCompleteness.Algebra.BilinearGramCompressionLemmas

namespace OAI


namespace PerfectCompleteness.TensorSliceDimension

noncomputable section

open UniqueGamesTheorem.Integration.BinaryLinear (F2)

theorem mask_card (n : Nat) : Fintype.card (Fin n → Bool) = 2 ^ n := by
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

theorem mask_card_le {n N : Nat} (h : n ≤ N) :
    Fintype.card (Fin n → Bool) ≤ 2 ^ N := by
  rw [mask_card]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) h

theorem reciprocal_mask_card_ge {n N : Nat} (h : n ≤ N) :
    1 / (2 ^ N : ℝ) ≤ 1 / (Fintype.card (Fin n → Bool) : ℝ) := by
  simpa only [mask_card, Nat.cast_pow, Nat.cast_ofNat] using
    (one_div_pow_le_one_div_pow_of_le (by norm_num : (1 : ℝ) ≤ 2) h)

section GeneralEquationSpace

variable {Q W : Type*} [AddCommGroup Q] [Module F2 Q]
  [AddCommGroup W] [Module F2 W]
  [FiniteDimensional F2 Q] [FiniteDimensional F2 W]

theorem linearMap_finrank_le {r ℓ : Nat}
    (hQ : Module.finrank F2 Q ≤ r) (hW : Module.finrank F2 W ≤ ℓ) :
    Module.finrank F2 (Q →ₗ[F2] W) ≤ r * ℓ := by
  rw [Module.finrank_linearMap]
  exact Nat.mul_le_mul hQ hW

theorem reciprocal_linearMap_masks_ge {r ℓ : Nat}
    (hQ : Module.finrank F2 Q ≤ r) (hW : Module.finrank F2 W ≤ ℓ) :
    1 / (2 ^ (r * ℓ) : ℝ) ≤
      1 / (Fintype.card (Fin (Module.finrank F2 (Q →ₗ[F2] W)) → Bool) : ℝ) :=
  reciprocal_mask_card_ge (linearMap_finrank_le hQ hW)

end GeneralEquationSpace

variable {H : Type*} [AddCommGroup H] [Module F2 H] [FiniteDimensional F2 H]
  {ℓ : Nat} (W : Submodule F2 (Fin ℓ → F2))
  (Q : Submodule F2 (Module.Dual F2 H))

theorem row_finrank_le : Module.finrank F2 W ≤ ℓ := by
  simpa only [Module.finrank_fin_fun] using (Submodule.finrank_le W)

theorem equation_finrank_le {r : Nat} (hQ : Module.finrank F2 Q ≤ r) :
    Module.finrank F2 (Q →ₗ[F2] W) ≤ r * ℓ :=
  linearMap_finrank_le (Q := Q) (W := W) hQ (row_finrank_le W)

theorem equation_mask_card :
    Fintype.card (Fin (Module.finrank F2 (Q →ₗ[F2] W)) → Bool) =
      2 ^ (Module.finrank F2 Q * Module.finrank F2 W) := by
  let : Module.Free F2 Q := Module.Free.of_divisionRing F2 Q
  let : Module.Free F2 W := Module.Free.of_divisionRing F2 W
  rw [mask_card, Module.finrank_linearMap F2 F2 Q W]

theorem equation_mask_card_le {r : Nat} (hQ : Module.finrank F2 Q ≤ r) :
    Fintype.card (Fin (Module.finrank F2 (Q →ₗ[F2] W)) → Bool) ≤ 2 ^ (r * ℓ) :=
  mask_card_le (equation_finrank_le W Q hQ)

theorem reciprocal_equation_mask_card_ge {r : Nat} (hQ : Module.finrank F2 Q ≤ r) :
    1 / (2 ^ (r * ℓ) : ℝ) ≤
      1 / (Fintype.card (Fin (Module.finrank F2 (Q →ₗ[F2] W)) → Bool) : ℝ) :=
  reciprocal_mask_card_ge (equation_finrank_le W Q hQ)

theorem restriction_finrank_le {r : Nat} (hQ : Module.finrank F2 Q ≤ r) :
    Module.finrank F2 (LinearMap.range (TensorRestriction.restrictionMap (W := W) Q)) ≤
      r * ℓ := by
  rw [TensorRestriction.finrank_range, Nat.mul_comm]
  exact Nat.mul_le_mul hQ (row_finrank_le W)

end
end PerfectCompleteness.TensorSliceDimension

end OAI
