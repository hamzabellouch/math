import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalStatistic
import OAI.NumberTheory.Ostmann.Construction.PhaseGiantTest

namespace OAI

/-! # The two original giant Fourier phases on a fixed product fibre -/

namespace Ostmann
open scoped Classical BigOperators

/-- The two cofactor phases before inserting the logarithmic coordinates. -/
noncomputable def giantPairPhase (g : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (D H XL XR : ℕ) (s : ℤ) : ℂ :=
  (if favorable XL then complexUnitPhase
    (g XL ((s : ZMod XL) * ((D * XR * H : ℕ) : ZMod XL)⁻¹)) else 0) *
  (if favorable XR then complexUnitPhase
    (g XR ((s : ZMod XR) * ((D * XL * H : ℕ) : ZMod XR)⁻¹)) else 0)

/-- The two giant factors of Section 7.4, evaluated at their exact cofactors.
The definition also applies to the integer giant in a transfer diagonal. -/
noncomputable def movingGiantPhase {σ B : Type*} {n : ℕ}
    (value : σ → ℕ) (outside : List ℕ) (small bulk : TreeLeafTuple (List B) n)
    (g : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (s : ℤ) (y : B → σ) (x z : ℝ) : ℂ :=
  giantPairPhase g favorable outside.prod
    (MovingSlotReversal.naturalProduct (value ∘ y)
      (flattenMovingSlots n small ++ flattenMovingSlots n bulk))
    ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊ s

theorem movingGiantPhase_norm_le {σ B : Type*} {n : ℕ}
    (value : σ → ℕ) (outside : List ℕ) (small bulk : TreeLeafTuple (List B) n)
    (g : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (s : ℤ) (y : B → σ) (x z : ℝ) :
    ‖movingGiantPhase value outside small bulk g favorable s y x z‖ ≤ 1 := by
  unfold movingGiantPhase giantPairPhase
  rw [norm_mul]
  apply (mul_le_mul _ _ (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  all_goals split_ifs <;> first | exact complexUnitPhase_norm_le _ | simp

theorem movingGiantPhase_selectedBulkSample {σ B : Type*} [Fintype B]
    (value : σ → ℕ) (outside : List ℕ) (n m : ℕ)
    (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (e : Equiv.Perm (TreeLeafIndex n × Fin m)) (y : B → σ)
    (hsmall : ∀ i ∈ flattenMovingSlots n small, i ∉ Set.range slot)
    (g : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) (s : ℤ) (x z : ℝ) :
    movingGiantPhase value outside small (bulkSlotLeaves n m slot) g favorable s
      (selectedBulkSample slot e y) x z =
    movingGiantPhase value outside small (bulkSlotLeaves n m slot) g favorable s y x z := by
  unfold movingGiantPhase
  rw [MovingSlotReversal.naturalProduct_selected_bulk value n m small slot e y hsmall]

end Ostmann

end OAI
