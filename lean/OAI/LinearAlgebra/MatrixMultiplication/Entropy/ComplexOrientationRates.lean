import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

namespace MatrixMultiplication.Foundation
namespace OrientationRates

open scoped BigOperators

abbrev Orientation := Equiv.Perm (Fin 3)

@[simp] theorem orientation_card : Fintype.card Orientation = 6 := by
  rw [Fintype.card_perm]
  decide

def relativeOrientation (relative : Orientation) : Orientation ≃ Orientation where
  toFun outer := outer * relative
  invFun original := original * relative⁻¹
  left_inv outer := by simp [mul_assoc]
  right_inv original := by simp [mul_assoc]

@[simp] theorem relativeOrientation_apply (relative outer : Orientation) :
    relativeOrientation relative outer = outer * relative := rfl

theorem unique_outer_orientation (relative original : Orientation) :
    ∃! outer : Orientation, outer * relative = original :=
  (relativeOrientation relative).bijective.existsUnique original

theorem sum_relative_orientation {M : Type*} [AddCommMonoid M]
    (relative : Orientation) (value : Orientation → M) :
    (∑ outer, value (outer * relative)) = ∑ original, value original :=
  (relativeOrientation relative).sum_comp value

theorem prod_relative_orientation {M : Type*} [CommMonoid M]
    (relative : Orientation) (value : Orientation → M) :
    (∏ outer, value (outer * relative)) = ∏ original, value original :=
  (relativeOrientation relative).prod_comp value

theorem site_population_in_orientation {M : Type*} [AddCommMonoid M]
    (relative original : Orientation) (population : M) :
    (∑ outer : Orientation,
      if outer * relative = original then population else 0) = population := by
  classical
  rw [sum_relative_orientation relative
    (fun orientation => if orientation = original then population else 0)]
  simp

theorem histogram_in_original_orientation {Site M : Type*}
    [Fintype Site] [AddCommMonoid M]
    (relative : Site → Orientation) (population : Site → M)
    (original : Orientation) :
    (∑ site, ∑ outer : Orientation,
      if outer * relative site = original then population site else 0) =
      ∑ site, population site := by
  classical
  apply Finset.sum_congr rfl
  intro site _
  exact site_population_in_orientation (relative site) original (population site)

theorem target_multiplicity (targetCount : ℕ) :
    (∏ _ : Orientation, targetCount) = targetCount ^ 6 := by
  simp

section FiniteRates

variable {Node Grade : Type*} [Fintype Node] [Fintype Grade]

def outputLaw (n : ℕ) (population : Node → ℝ) (law : Node → Grade → ℝ)
    (grade : Grade) : ℝ :=
  (∑ node, population node * law node grade) / n

def affineScore (offset : ℝ) (coefficient law : Grade → ℝ) : ℝ :=
  offset + ∑ grade, coefficient grade * law grade

def totalNodeUtility (population utility : Node → ℝ) : ℝ :=
  ∑ node, population node * utility node

def totalCost (population : Node → ℝ) (law : Node → Grade → ℝ)
    (offset : ℝ) (coefficient : Grade → ℝ) (utility : Node → ℝ) : ℝ :=
  ∑ node, population node * (affineScore offset coefficient (law node) - utility node)

omit [Fintype Grade] in
theorem outputLaw_nonnegative (n : ℕ) (population : Node → ℝ)
    (law : Node → Grade → ℝ)
    (hp : ∀ node, 0 ≤ population node) (hq : ∀ node grade, 0 ≤ law node grade)
    (grade : Grade) : 0 ≤ outputLaw n population law grade := by
  apply div_nonneg
  · exact Finset.sum_nonneg fun node _ => mul_nonneg (hp node) (hq node grade)
  · exact Nat.cast_nonneg n

theorem outputLaw_total (n : ℕ) (hn : n ≠ 0) (population : Node → ℝ)
    (law : Node → Grade → ℝ)
    (hp : ∑ node, population node = (n : ℝ))
    (hq : ∀ node, ∑ grade, law node grade = 1) :
    ∑ grade, outputLaw n population law grade = 1 := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp only [outputLaw, ← Finset.sum_div]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, hq, mul_one, hp, div_self hn']

theorem weighted_affineScore (population : Node → ℝ) (law : Node → Grade → ℝ)
    (offset : ℝ) (coefficient : Grade → ℝ) :
    (∑ node, population node * affineScore offset coefficient (law node)) =
      (∑ node, population node) * offset +
        ∑ grade, coefficient grade * (∑ node, population node * law node grade) := by
  simp only [affineScore, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
  congr 1
  calc
    (∑ node, population node * ∑ grade, coefficient grade * law node grade) =
        ∑ node, ∑ grade, coefficient grade * (population node * law node grade) := by
      apply Finset.sum_congr rfl
      intro node _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro grade _
      ring
    _ = ∑ grade, coefficient grade * ∑ node, population node * law node grade := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]

theorem weighted_affineScore_eq (n : ℕ) (hn : n ≠ 0)
    (population : Node → ℝ) (law : Node → Grade → ℝ)
    (hp : ∑ node, population node = (n : ℝ))
    (offset : ℝ) (coefficient : Grade → ℝ) :
    (∑ node, population node * affineScore offset coefficient (law node)) =
      (n : ℝ) * affineScore offset coefficient (outputLaw n population law) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [weighted_affineScore, hp]
  simp only [affineScore, outputLaw]
  conv_rhs => rw [mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro grade _
  field_simp [hn']

theorem totalCost_eq (n : ℕ) (hn : n ≠ 0)
    (population : Node → ℝ) (law : Node → Grade → ℝ)
    (hp : ∑ node, population node = (n : ℝ))
    (offset : ℝ) (coefficient : Grade → ℝ) (utility : Node → ℝ) :
    totalCost population law offset coefficient utility =
      (n : ℝ) * affineScore offset coefficient (outputLaw n population law) -
        totalNodeUtility population utility := by
  simp only [totalCost, mul_sub, Finset.sum_sub_distrib, totalNodeUtility]
  rw [weighted_affineScore_eq n hn population law hp]

theorem utility_rate_identity (n : ℕ) (hn : n ≠ 0)
    (population : Node → ℝ) (law : Node → Grade → ℝ)
    (hp : ∑ node, population node = (n : ℝ))
    (offset targetRate : ℝ) (coefficient : Grade → ℝ) (utility : Node → ℝ) :
    (targetRate + totalNodeUtility population utility) / n =
      affineScore offset coefficient (outputLaw n population law) +
        (targetRate - totalCost population law offset coefficient utility) / n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [totalCost_eq n hn population law hp]
  field_simp [hn']
  ring

theorem finite_utility_bound (n : ℕ) (hn : n ≠ 0)
    (population : Node → ℝ) (law : Node → Grade → ℝ)
    (hp : ∑ node, population node = (n : ℝ))
    (offset targetRate error actualUtility : ℝ)
    (coefficient : Grade → ℝ) (utility : Node → ℝ)
    (construction : (targetRate + totalNodeUtility population utility) / n - error ≤
      actualUtility) :
    affineScore offset coefficient (outputLaw n population law) +
      (targetRate - totalCost population law offset coefficient utility) / n - error ≤
        actualUtility := by
  rwa [utility_rate_identity n hn population law hp offset targetRate coefficient utility]
    at construction

end FiniteRates

section PhysicalNormalization

variable {Node : Type*} [Fintype Node]

theorem log_resource_product (copies : Node → ℕ) (resource : Node → ℝ)
    (hresource : ∀ node, resource node ≠ 0) :
    Real.log (∏ node, resource node ^ copies node) =
      ∑ node, (copies node : ℝ) * Real.log (resource node) := by
  rw [Real.log_prod (s := Finset.univ) (f := fun node => resource node ^ copies node)
    (fun node _ => pow_ne_zero _ (hresource node))]
  simp only [Real.log_pow]

theorem log_direct_multiplicity (targetCount : ℝ) (htarget : targetCount ≠ 0)
    (copies : Node → ℕ) (labels : Node → ℝ) (hlabels : ∀ node, labels node ≠ 0) :
    Real.log (targetCount ^ 6 * ∏ node, labels node ^ copies node) =
      6 * Real.log targetCount + ∑ node, (copies node : ℝ) * Real.log (labels node) := by
  have hprod : (∏ node, labels node ^ copies node) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun node _ => pow_ne_zero _ (hlabels node))
  rw [Real.log_mul (pow_ne_zero _ htarget) hprod, Real.log_pow,
    log_resource_product copies labels hlabels]
  norm_num

theorem raw_utility_accounting (targetCount : ℝ) (htarget : targetCount ≠ 0)
    (copies : Node → ℕ) (labels rank volume : Node → ℝ)
    (hlabels : ∀ node, labels node ≠ 0) (hrank : ∀ node, rank node ≠ 0)
    (hvolume : ∀ node, volume node ≠ 0) (volumeWeight : ℝ) :
    Real.log (targetCount ^ 6 * ∏ node, labels node ^ copies node) -
      Real.log (∏ node, rank node ^ copies node) +
      volumeWeight * Real.log (∏ node, volume node ^ copies node) =
      6 * Real.log targetCount +
        ∑ node, (copies node : ℝ) *
          (Real.log (labels node) - Real.log (rank node) +
            volumeWeight * Real.log (volume node)) := by
  rw [log_direct_multiplicity targetCount htarget copies labels hlabels,
    log_resource_product copies rank hrank, log_resource_product copies volume hvolume]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  have hvolumeSum :
      (∑ node, volumeWeight * ((copies node : ℝ) * Real.log (volume node))) =
        ∑ node, (copies node : ℝ) * (volumeWeight * Real.log (volume node)) := by
    apply Finset.sum_congr rfl
    intro node _
    ring
  rw [hvolumeSum]
  ring

theorem physical_rate_normalization (bank horizon : ℕ)
    (hbank : bank ≠ 0) (hhorizon : horizon ≠ 0)
    (blockSize copies : Node → ℕ) (hsize : ∀ node, blockSize node ≠ 0)
    (population rawNodeUtility : Node → ℝ) (targetLog : ℝ)
    (tiling : ∀ node, (bank : ℝ) * population node =
      (copies node : ℝ) * blockSize node) :
    (6 * targetLog + ∑ node, (copies node : ℝ) * rawNodeUtility node) /
        (6 * bank * horizon) =
      (targetLog / bank + totalNodeUtility population
        (fun node => rawNodeUtility node / (6 * blockSize node))) / horizon := by
  have hbank' : (bank : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hbank
  have hhorizon' : (horizon : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hhorizon
  have hnode (node : Node) :
      population node * (rawNodeUtility node / (6 * blockSize node)) =
        (copies node : ℝ) * rawNodeUtility node / (6 * bank) := by
    have hsize' : (blockSize node : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hsize node)
    have hp : population node = (copies node : ℝ) * blockSize node / bank := by
      apply (eq_div_iff hbank').mpr
      simpa only [mul_comm] using tiling node
    rw [hp]
    field_simp [hbank', hsize']
  simp only [totalNodeUtility, hnode, ← Finset.sum_div]
  field_simp [hbank', hhorizon']

theorem physical_cost_rate_identity {Grade : Type*} [Fintype Grade]
    (bank horizon : ℕ) (hbank : bank ≠ 0) (hhorizon : horizon ≠ 0)
    (blockSize copies : Node → ℕ) (hsize : ∀ node, blockSize node ≠ 0)
    (population rawNodeUtility : Node → ℝ) (law : Node → Grade → ℝ)
    (targetLog offset : ℝ) (coefficient : Grade → ℝ)
    (tiling : ∀ node, (bank : ℝ) * population node =
      (copies node : ℝ) * blockSize node)
    (total : ∑ node, population node = (horizon : ℝ)) :
    (6 * targetLog + ∑ node, (copies node : ℝ) * rawNodeUtility node) /
        (6 * bank * horizon) =
      affineScore offset coefficient (outputLaw horizon population law) +
        (targetLog / bank - totalCost population law offset coefficient
          (fun node => rawNodeUtility node / (6 * blockSize node))) / horizon := by
  rw [physical_rate_normalization bank horizon hbank hhorizon blockSize copies
    hsize population rawNodeUtility targetLog tiling]
  exact utility_rate_identity horizon hhorizon population law total offset
    (targetLog / bank) coefficient (fun node => rawNodeUtility node / (6 * blockSize node))

end PhysicalNormalization

end OrientationRates
end MatrixMultiplication.Foundation

end

end OAI
