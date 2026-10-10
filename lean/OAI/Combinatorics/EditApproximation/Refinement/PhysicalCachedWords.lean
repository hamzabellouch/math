import OAI.Combinatorics.EditApproximation.Binary.BinaryPowerStorage
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalLocalDenominator

namespace OAI

/-! The cache normalization algorithm applied to the actual all-seed local
table invariants. These word bounds require neither a good-seed event nor a
bound on the temporary numerator and denominator before normalization. -/

namespace EditApproximation

theorem physicalLocalRefinement_cached_word {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F exponent Q : ℕ) (A tau : ℚ) (hsize : source.length + target.length ≤ N)
    (T ell : ℕ) (hell : 0 < ell)
    (draw : PhysicalInternalNode M J → ℕ → CellGroupDraws M F Q)
    (online : PhysicalNode M J → PhysicalChildTables M target.length → ℕ →
      TargetInterval target.length → List (PhysicalRationalAction M target.length))
    (honline : ∀ node children t q action, action ∈ online node children t q → action.connection.den = 1)
    (node : PhysicalNode M J) (t : ℕ) (q : TargetInterval target.length)
    (raw : BinaryFraction) (hraw : raw.value =
      physicalLocalRefinement source target U N P F exponent Q A tau
        (1 / (ell : ℚ) ^ 10) T draw online node t q)
    (base : List Bool) (hbase : bitWordValue base = ell ^ 10 + 1) :
    let result := BinaryFraction.powerDenominatorWithWork raw base
      (by rw [hbase]; omega) (J - node.1.val)
    result.1.value = raw.value ∧ result.1.width ≤
      Nat.size ((32 * F + 1) * N) + 2 * (J - node.1.val) * base.length + 3 := by
  dsimp only
  have hd : raw.value.den ∣ bitWordValue base ^ (J - node.1.val) := by
    rw [hraw, hbase]
    exact physicalLocalRefinement_den_dvd source target U N P F exponent Q A tau T ell hell
      draw online honline node t q
  have hb := physicalLocalRefinement_bounds source target U N P F exponent Q A tau
    (1 / (ell : ℚ) ^ 10) T (by positivity) draw online node t q
  have hv : |raw.value| ≤ (((32 * F + 1) * N : ℕ) : ℚ) := by
    rw [hraw, abs_of_nonneg hb.1]
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
      hb.2.trans (stageInitial_upper_all_seeds source target U N P F A hsize (node, q))
  refine ⟨BinaryFraction.powerDenominatorWithWork_value raw base _ _ hd, ?_⟩
  have hw := BinaryFraction.powerDenominatorWithWork_width raw base (by rw [hbase]; omega)
    (J - node.1.val) ((32 * F + 1) * N) base.length le_rfl hd hv
  simpa only [Nat.mul_add, Nat.mul_one, Nat.mul_assoc, Nat.add_assoc] using hw

theorem physicalLocalOnlineRefinement_cached_word {α : Type*} [DecidableEq α]
    {M J R : ℕ} [NeZero R]
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F exponent H Q : ℕ) (A tau eta kappa : ℚ)
    (hsize : source.length + target.length ≤ N) (T ell : ℕ) (hell : 0 < ell)
    (draw : PhysicalInternalNode M J → ℕ → CellGroupDraws M F Q)
    (integer : PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
    (node : PhysicalNode M J) (t : ℕ) (q : TargetInterval target.length)
    (raw : BinaryFraction) (hraw : raw.value =
      physicalLocalRefinement source target U N P F exponent Q A tau (1 / (ell : ℚ) ^ 10)
        T draw (physicalLocalOnline source target U N P F exponent H T A tau eta kappa integer) node t q)
    (base : List Bool) (hbase : bitWordValue base = ell ^ 10 + 1) :
    let result := BinaryFraction.powerDenominatorWithWork raw base
      (by rw [hbase]; omega) (J - node.1.val)
    result.1.value = raw.value ∧ result.1.width ≤
      Nat.size ((32 * F + 1) * N) + 2 * (J - node.1.val) * base.length + 3 :=
  physicalLocalRefinement_cached_word source target U N P F exponent Q A tau hsize T ell hell
    draw _ (physicalLocalOnline_connection_den source target U N P F exponent H T A tau eta kappa integer)
    node t q raw hraw base hbase

theorem physicalLocalWarmup_cached_word {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (hsize : source.length + target.length ≤ N)
    (t : ℕ) (state : PhysicalEntry M J target.length)
    (raw : BinaryFraction) (hraw : raw.value = physicalLocalWarmup source target U N P F A t state) :
    let result := BinaryFraction.fixedDenominatorWithWork raw [true] (by decide)
    result.1.value = raw.value ∧ result.1.width ≤ Nat.size ((32 * F + 1) * N) + 3 := by
  dsimp only
  have hd : raw.value.den ∣ bitWordValue [true] := by
    rw [hraw, physicalLocalWarmup_den_one]
    exact one_dvd _
  have hb := physicalLocalWarmup_bounds source target U N P F A t state
  have hv : |raw.value| ≤ (((32 * F + 1) * N : ℕ) : ℚ) := by
    rw [hraw, abs_of_nonneg hb.1]
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
      hb.2.trans (stageInitial_upper_all_seeds source target U N P F A hsize state)
  exact ⟨BinaryFraction.fixedDenominatorWithWork_value raw [true] (by decide) hd,
    BinaryFraction.fixedDenominatorWithWork_width raw [true] (by decide) hd
      ((32 * F + 1) * N) 1 hv (by decide)⟩

end EditApproximation

end OAI
