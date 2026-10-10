import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.StageCLaw
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.PopulationCounts
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.Population
import OAI.LinearAlgebra.MatrixMultiplication.Recovery.FiniteSchedule
import OAI.LinearAlgebra.MatrixMultiplication.Recovery.PhysicalOrders
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sets

namespace OAI

/-! Finite extraction histories, inherited masks and recovery bounds. -/

noncomputable section

namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

structure Allocation where
  mass : Fin 3 → ℚ
  positive : ∀ i, 0 < mass i
  total : ∑ i, mass i = 1

abbrev Placement := PhysicalOrders.PhysicalOrder
abbrev Initial (K : ℕ) := Fin K × Fin sortedInitial.length

def initialShape {K : ℕ} (h : Initial K) : Shape := sortedInitial.get h.2

theorem initialShape_mem {K : ℕ} (h : Initial K) : initialShape h ∈ sortedInitial :=
  List.get_mem _ _

abbrev InitialPositive (K : ℕ) := {h : Initial K // initialShape h ∈ positiveInitial}

abbrev ASplit {K : ℕ} (h : InitialPositive K) := Fin (below (initialShape h.val)).length
abbrev AfterA (K : ℕ) := Σ h : InitialPositive K, ASplit h × Bool

def aSplit {K : ℕ} (h : AfterA K) : Shape :=
  (below (initialShape h.1.val)).get h.2.1

def halfShape (parent left : Shape) (right : Bool) : Shape :=
  if right then complement parent left else left

def aShape {K : ℕ} (h : AfterA K) : Shape :=
  halfShape (initialShape h.1.val) (aSplit h) h.2.2

theorem aSplit_mem {K : ℕ} (h : AfterA K) : aSplit h ∈ below (initialShape h.1.val) :=
  List.get_mem _ _

theorem aShape_mem {K : ℕ} (h : AfterA K) : aShape h ∈ below (initialShape h.1.val) := by
  have hc := (stageA_support_complement _ h.1.property _ (aSplit_mem h)).1
  cases hh : h.2.2 <;> simp [aShape, halfShape, hh, aSplit_mem h, hc]

theorem stageA_children_size : ∀ g ∈ positiveInitial, ∀ t ∈ below g, t ∈ shapes 8 := by
  decide +kernel

theorem aShape_size {K : ℕ} (h : AfterA K) : aShape h ∈ shapes 8 :=
  stageA_children_size _ h.1.property _ (aShape_mem h)

abbrev APositive (K : ℕ) := {h : AfterA K // aShape h ∈ positiveSecond}
abbrev BSplit {K : ℕ} (h : APositive K) := Fin (below (aShape h.val)).length
abbrev AfterB (K : ℕ) := Σ h : APositive K, BSplit h × Bool

def bSplit {K : ℕ} (h : AfterB K) : Shape :=
  (below (aShape h.1.val)).get h.2.1

def bShape {K : ℕ} (h : AfterB K) : Shape :=
  halfShape (aShape h.1.val) (bSplit h) h.2.2

theorem bSplit_mem {K : ℕ} (h : AfterB K) : bSplit h ∈ below (aShape h.1.val) :=
  List.get_mem _ _

theorem bShape_mem {K : ℕ} (h : AfterB K) : bShape h ∈ below (aShape h.1.val) := by
  have hc := (stageB_support_complement _ h.1.property _ (bSplit_mem h)).1
  cases hh : h.2.2 <;> simp [bShape, halfShape, hh, bSplit_mem h, hc]

theorem stageB_children_size : ∀ t ∈ positiveSecond, ∀ u ∈ below t, u ∈ shapes 4 := by
  decide +kernel

theorem bShape_size {K : ℕ} (h : AfterB K) : bShape h ∈ shapes 4 :=
  stageB_children_size _ h.1.property _ (bShape_mem h)

abbrev BPositive (K : ℕ) := {h : AfterB K // positive (bShape h) = true}
abbrev PartC (K : ℕ) := BPositive K × Fin 3
abbrev AfterC (K : ℕ) := PartC K × Fin 4 × Bool

def cParameterParent {K : ℕ} (h : PartC K) : Shape := aShape h.1.val.1.val
def cShapeParent {K : ℕ} (h : PartC K) : Shape := bShape h.1.val

def cSplit {K : ℕ} (h : AfterC K) : Shape := stageCAtom (cShapeParent h.1) h.2.1

def cShape {K : ℕ} (h : AfterC K) : Shape :=
  halfShape (cShapeParent h.1) (cSplit h) h.2.2

theorem cShape_zero {K : ℕ} (h : AfterC K) : ∃ i, cShape h i = 0 := by
  have hg := stageC_children_geometry (cShapeParent h.1)
    (bShape_size h.1.1.val) h.1.1.property (cSplit h)
    (stageCAtom_mem _ (bShape_size h.1.1.val) h.1.1.property h.2.1)
  cases hh : h.2.2 with
  | false => simpa [cShape, halfShape, hh] using hg.2.2.1
  | true => simpa [cShape, halfShape, hh] using hg.2.2.2

instance initialPositiveFintype (K : ℕ) : Fintype (InitialPositive K) :=
  Fintype.ofFinite _

instance aPositiveFintype (K : ℕ) : Fintype (APositive K) :=
  Fintype.ofFinite _

instance bPositiveFintype (K : ℕ) : Fintype (BPositive K) :=
  Fintype.ofFinite _

inductive CanonicalHistory (K : ℕ) where
  | initial (h : Initial K)
  | afterA (h : AfterA K)
  | afterB (h : AfterB K)
  | partC (h : PartC K)
  | afterC (h : AfterC K)
  deriving Fintype

abbrev History (K : ℕ) := CanonicalHistory K × Placement

def initialAmount {K : ℕ} (h : Initial K) : ℚ := initialLaw (initialShape h)
def aAmount {K : ℕ} (h : AfterA K) : ℚ :=
  initialAmount h.1.val * stageALaw (initialShape h.1.val) (aSplit h)
def bAmount {K : ℕ} (h : AfterB K) : ℚ :=
  aAmount h.1.val * stageBLaw (aShape h.1.val) (bSplit h)
def partAmount {K : ℕ} (allocation : Allocation) (h : PartC K) : ℚ :=
  bAmount h.1.val * allocation.mass h.2
def cAmount {K : ℕ} (allocation : Allocation) (h : AfterC K) : ℚ :=
  partAmount allocation h.1 * stageCWeight (cParameterParent h.1) (cShapeParent h.1) h.2.1

def canonicalAmount {K : ℕ} (allocation : Allocation) : CanonicalHistory K → ℚ
  | .initial h => initialAmount h
  | .afterA h => aAmount h
  | .afterB h => bAmount h
  | .partC h => partAmount allocation h
  | .afterC h => cAmount allocation h

def amount {K : ℕ} (allocation : Allocation) (h : History K) : ℚ :=
  canonicalAmount allocation h.1 / 6

theorem initialAmount_pos {K : ℕ} (h : Initial K) : 0 < initialAmount h :=
  initialLaw_positive _ (initialShape_mem h)

theorem aAmount_pos {K : ℕ} (h : AfterA K) : 0 < aAmount h :=
  mul_pos (initialAmount_pos _) (stageALaw_positive _ _ (aSplit_mem h))

theorem bAmount_pos {K : ℕ} (h : AfterB K) : 0 < bAmount h :=
  mul_pos (aAmount_pos _) (stageBLaw_positive _ _ (bSplit_mem h))

theorem partAmount_pos {K : ℕ} (allocation : Allocation) (h : PartC K) :
    0 < partAmount allocation h := mul_pos (bAmount_pos _) (allocation.positive _)

theorem cAmount_nonneg {K : ℕ} (allocation : Allocation) (h : AfterC K) :
    0 ≤ cAmount allocation h :=
  mul_nonneg (partAmount_pos allocation _).le (stageCWeight_nonnegative _ _ _)

theorem amount_nonneg {K : ℕ} (allocation : Allocation) (h : History K) :
    0 ≤ amount allocation h := by
  apply div_nonneg _ (by norm_num)
  cases h.1 with
  | initial h => exact (initialAmount_pos h).le
  | afterA h => exact (aAmount_pos h).le
  | afterB h => exact (bAmount_pos h).le
  | partC h => exact (partAmount_pos allocation h).le
  | afterC h => exact cAmount_nonneg allocation h

theorem placement_amount_eq {K : ℕ} (allocation : Allocation)
    (h : CanonicalHistory K) (phi psi : Placement) :
    amount allocation (h, phi) = amount allocation (h, psi) := rfl

theorem sum_placement_amount {K : ℕ} (allocation : Allocation) (h : CanonicalHistory K) :
    ∑ phi : Placement, amount allocation (h, phi) = canonicalAmount allocation h := by
  simp only [amount, Finset.sum_const, Finset.card_univ,
    PhysicalOrders.card_physical_orders, nsmul_eq_mul]
  norm_num
  ring

theorem initial_amount_sum (K : ℕ) (j : Fin K) :
    ∑ g : Fin sortedInitial.length, initialAmount (j, g) = 1 := by
  change (∑ g : Fin sortedInitial.length, initialLaw sortedInitial[g.val]) = 1
  rw [Fin.sum_univ_fun_getElem]
  exact initialLaw_normalized

theorem root_mass_sum_lot {K : ℕ} (allocation : Allocation) (j : Fin K) :
    (∑ g : Fin sortedInitial.length, ∑ phi : Placement,
      amount allocation (.initial (j, g), phi)) = 1 := by
  simp only [sum_placement_amount, canonicalAmount]
  exact initial_amount_sum K j

theorem a_transition {K : ℕ} (h : InitialPositive K) (right : Bool) :
    ∑ k : ASplit h, aAmount ⟨h, k, right⟩ = initialAmount h.val := by
  change (∑ k : ASplit h, initialAmount h.val *
    stageALaw (initialShape h.val) (below (initialShape h.val))[k.val]) = _
  rw [← Finset.mul_sum, Fin.sum_univ_fun_getElem,
    stageALaw_normalized _ h.property, mul_one]

theorem b_transition {K : ℕ} (h : APositive K) (right : Bool) :
    ∑ k : BSplit h, bAmount ⟨h, k, right⟩ = aAmount h.val := by
  change (∑ k : BSplit h, aAmount h.val *
    stageBLaw (aShape h.val) (below (aShape h.val))[k.val]) = _
  rw [← Finset.mul_sum, Fin.sum_univ_fun_getElem,
    stageBLaw_normalized _ h.property, mul_one]

theorem part_transition {K : ℕ} (allocation : Allocation) (h : BPositive K) :
    ∑ i : Fin 3, partAmount allocation (h, i) = bAmount h.val := by
  simp only [partAmount, ← Finset.mul_sum, allocation.total, mul_one]

theorem c_transition {K : ℕ} (allocation : Allocation) (h : PartC K) (right : Bool) :
    ∑ k : Fin 4, cAmount allocation (h, k, right) = partAmount allocation h := by
  simp only [cAmount, ← Finset.mul_sum, stageCWeight_normalized, mul_one]

def population {K : ℕ} (allocation : Allocation) (dilation : ℕ) : History K → ℕ :=
  AllFieldPopulationCounts.count (amount allocation) dilation

def populationLength {K : ℕ} (allocation : Allocation) (dilation : ℕ) : ℕ :=
  AllFieldPopulationCounts.blockLength (amount (K := K) allocation) dilation

theorem population_cast {K : ℕ} (allocation : Allocation) (dilation : ℕ) (h : History K) :
    (population allocation dilation h : ℚ) =
      (populationLength (K := K) allocation dilation : ℚ) * amount allocation h :=
  AllFieldPopulationCounts.count_cast_blockLength _ (amount_nonneg allocation) dilation h

theorem population_zero_iff {K : ℕ} (allocation : Allocation) {dilation : ℕ}
    (hd : 0 < dilation) (h : History K) :
    population allocation dilation h = 0 ↔ amount allocation h = 0 :=
  AllFieldPopulationCounts.count_zero_iff _ (amount_nonneg allocation) hd h

theorem initial_population_sum {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (j : Fin K) :
    (∑ g : Fin sortedInitial.length, ∑ phi : Placement,
      population allocation dilation (.initial (j, g), phi)) =
        populationLength (K := K) allocation dilation := by
  apply Nat.cast_injective (R := ℚ)
  simp only [Nat.cast_sum, population_cast, ← Finset.mul_sum,
    root_mass_sum_lot allocation j, mul_one]

theorem a_population_transition {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : InitialPositive K) (right : Bool) (phi : Placement) :
    (∑ k : ASplit h, population allocation dilation (.afterA ⟨h, k, right⟩, phi)) =
      population allocation dilation (.initial h.val, phi) := by
  apply Nat.cast_injective (R := ℚ)
  simp only [Nat.cast_sum, population_cast, amount, canonicalAmount,
    ← Finset.mul_sum, ← Finset.sum_div, a_transition]

theorem b_population_transition {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : APositive K) (right : Bool) (phi : Placement) :
    (∑ k : BSplit h, population allocation dilation (.afterB ⟨h, k, right⟩, phi)) =
      population allocation dilation (.afterA h.val, phi) := by
  apply Nat.cast_injective (R := ℚ)
  simp only [Nat.cast_sum, population_cast, amount, canonicalAmount,
    ← Finset.mul_sum, ← Finset.sum_div, b_transition]

theorem part_population_transition {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : BPositive K) (phi : Placement) :
    (∑ i : Fin 3, population allocation dilation (.partC (h, i), phi)) =
      population allocation dilation (.afterB h.val, phi) := by
  apply Nat.cast_injective (R := ℚ)
  simp only [Nat.cast_sum, population_cast, amount, canonicalAmount,
    ← Finset.mul_sum, ← Finset.sum_div, part_transition]

theorem c_population_transition {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : PartC K) (right : Bool) (phi : Placement) :
    (∑ k : Fin 4, population allocation dilation (.afterC (h, k, right), phi)) =
      population allocation dilation (.partC h, phi) := by
  apply Nat.cast_injective (R := ℚ)
  simp only [Nat.cast_sum, population_cast, amount, canonicalAmount,
    ← Finset.mul_sum, ← Finset.sum_div, c_transition]

theorem a_half_counts_eq {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : InitialPositive K) (k : ASplit h) (phi : Placement) :
    population allocation dilation (.afterA ⟨h, k, false⟩, phi) =
      population allocation dilation (.afterA ⟨h, k, true⟩, phi) :=
  AllFieldPopulationCounts.count_eq_of_mass_eq _ (amount_nonneg allocation) dilation rfl

theorem b_half_counts_eq {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : APositive K) (k : BSplit h) (phi : Placement) :
    population allocation dilation (.afterB ⟨h, k, false⟩, phi) =
      population allocation dilation (.afterB ⟨h, k, true⟩, phi) :=
  AllFieldPopulationCounts.count_eq_of_mass_eq _ (amount_nonneg allocation) dilation rfl

theorem c_half_counts_eq {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : PartC K) (k : Fin 4) (phi : Placement) :
    population allocation dilation (.afterC (h, k, false), phi) =
      population allocation dilation (.afterC (h, k, true), phi) :=
  AllFieldPopulationCounts.count_eq_of_mass_eq _ (amount_nonneg allocation) dilation rfl

end MatrixMultiplication.AllFieldHistory

end

end OAI
