import OAI.NumberTheory.Ostmann.Arithmetic.MovingSampleCoordinates
import OAI.NumberTheory.Ostmann.Arithmetic.MovingScalarWindows
import OAI.NumberTheory.Ostmann.Arithmetic.InternalPatternWeight

namespace OAI

/-! # The exact compensation factors in the original history weight

Every sampled prime occurs once in the factor `u` at the node where it is
sampled. Its subsequent appearances in descendants do not add factors of `u`.
-/

namespace Ostmann
open scoped Classical BigOperators

def movingSampleProduct {A : Type*} (value : A → ℕ) :
    {n : ℕ} → MovingSampleSlots A n → ℕ
  | _, .leaf => 1
  | n + 1, .node u l r =>
      MovingSlotReversal.naturalProduct value (flattenMovingSlots n (movingCompensationSlots n u)) *
        movingSampleProduct value l * movingSampleProduct value r

theorem movingCompensationProduct_indexed {A : Type*} (value : A → ℕ) (n : ℕ)
    (a : TreeLeafTuple (Fin 4 → A) n) :
    MovingSlotReversal.naturalProduct value (flattenMovingSlots n (movingCompensationSlots n a)) =
      ∏ t : TreeLeafIndex n, ∏ j : Fin 4, value (treeLeafTupleEquiv (Fin 4 → A) n a t j) := by
  induction n with
  | zero =>
      simp only [flattenMovingSlots, movingCompensationSlots, MovingSlotReversal.naturalProduct,
        List.map_ofFn, List.prod_ofFn]
      change (∏ j : Fin 4, value (a j)) = ∏ _t : Unit, ∏ j : Fin 4, value (a j)
      simp only [Fintype.prod_unique]
  | succ n ih =>
      simp only [movingCompensationSlots, flattenMovingSlots, movingNaturalProduct_append, ih]
      change _ = ∏ t : TreeLeafIndex n ⊕ TreeLeafIndex n,
        ∏ j : Fin 4, value (treeLeafTupleEquiv (Fin 4 → A) (n + 1) a t j)
      rw [Fintype.prod_sum_type]
      rfl

theorem movingSampleProduct_coordinates {A : Type*} (value : A → ℕ) {n : ℕ}
    (a : MovingSampleSlots A n) :
    movingSampleProduct value a =
      ∏ i : MovingSampleIndex n, value (movingSampleCoordinates A n a i) := by
  induction a with
  | leaf => rfl
  | @node n u l r hl hr =>
      change _ = ∏ i : (TreeLeafIndex n × Fin 4) ⊕ (Bool × MovingSampleIndex n), _
      rw [Fintype.prod_sum_type, Fintype.prod_prod_type, Fintype.prod_prod_type, Fintype.prod_bool]
      rw [movingSampleProduct, movingCompensationProduct_indexed, hl, hr]
      simp only [movingSampleCoordinates, Equiv.coe_fn_mk]
      ring

noncomputable def movingCompensationExtra {σ : Type*} (value : σ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ
  | _, .leaf _ _, _, _, _ => 1
  | _, .node _ _ _ u _ _, _, _, _ => MovingSlotReversal.naturalProduct value u

/-- Factor all the actual `u` multipliers out of the scalar history
coefficient. Leaf weights and right-branch conjugations are retained. -/
theorem movingDataWeight_compensations {σ : Type*} (value : σ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (a : MovingSampleSlots σ n) :
    movingDataWeight F (movingCompensationExtra value) (buildMovingSlotData n t small bulk a) =
      (movingSampleProduct value a : ℂ) *
        movingDataWeight F (fun _ _ _ _ => 1) (buildMovingSlotData n t small bulk a) := by
  induction a with
  | leaf => simp only [buildMovingSlotData, movingDataWeight, movingSampleProduct, Nat.cast_one, one_mul]
  | @node n u l r hl hr =>
      simp only [buildMovingSlotData, movingDataWeight, movingCompensationExtra,
        hl, hr, movingSampleProduct, Nat.cast_mul, Complex.ofReal_natCast,
        Complex.ofReal_one, one_mul, star_mul, star_natCast]
      ring

/-- Prior times compensation is precisely the dependent pattern weight
used in the internal-line comparison, before any coincidences are collapsed. -/
theorem movingSamples_compensated_prior {A : Type*} (μ : ℕ → A → ℝ)
    (value : A → ℕ) {n : ℕ} (a : MovingSampleSlots A n) :
    (movingSampleProduct value a : ℝ) * movingSamplesPrior μ a =
      ∏ i : MovingSampleIndex n,
        (value (movingSampleCoordinates A n a i) : ℝ) *
          μ (movingSampleTier i) (movingSampleCoordinates A n a i) := by
  rw [movingSampleProduct_coordinates, movingSamplesPrior_coordinates,
    Nat.cast_prod, Finset.prod_mul_distrib]

theorem movingSamples_compensated_pattern {A C : Type*} (μ : ℕ → A → ℝ)
    (value : A → ℕ) (n : ℕ) (pattern : MovingSampleIndex n → C) (x : C → A) :
    let a := (movingSampleCoordinates A n).symm (x ∘ pattern)
    (movingSampleProduct value a : ℝ) * movingSamplesPrior μ a =
      internalPatternWeight pattern (fun i => μ (movingSampleTier i)) value x := by
  dsimp only
  rw [movingSamples_compensated_prior, Equiv.apply_symm_apply]
  rfl

end Ostmann

end OAI
