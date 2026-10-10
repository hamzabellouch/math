import Mathlib
import OAI.LinearAlgebra.MatrixFields.Entropy.ConditionalRateBridge

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldTerminalPopulations

open AllFieldHistory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K : ℕ} {H : Type*} [Fintype H]
  {A : H → Type*} [∀ h, Fintype (A h)]

def law (ν : ∀ h, A h → ℚ) (x : Sigma A) : ℚ := ν x.1 x.2

def denominator (ν : ∀ h, A h → ℚ) : ℕ :=
  AllFieldPopulationCounts.denominator (law ν)

def dilation (ν : ∀ h, A h → ℚ) (m : ℕ) : ℕ := m * denominator ν

def count (allocation : Allocation) (history : H → History K)
    (ν : ∀ h, A h → ℚ) (m : ℕ) (h : H) (a : A h) : ℕ :=
  population allocation m (history h) *
    AllFieldPopulationCounts.baseCount (law ν) ⟨h, a⟩

theorem denominator_pos (ν : ∀ h, A h → ℚ) : 0 < denominator ν :=
  AllFieldPopulationCounts.denominator_pos (law ν)

theorem dilation_pos (ν : ∀ h, A h → ℚ) {m : ℕ} (hm : 0 < m) :
    0 < dilation ν m := Nat.mul_pos hm (denominator_pos ν)

theorem baseCount_cast (ν : ∀ h, A h → ℚ) (hν : ∀ h a, 0 ≤ ν h a)
    (h : H) (a : A h) :
    (AllFieldPopulationCounts.baseCount (law ν) ⟨h, a⟩ : ℚ) =
      (denominator ν : ℚ) * ν h a :=
  AllFieldPopulationCounts.baseCount_cast (law ν) (fun x => hν x.1 x.2) ⟨h, a⟩

theorem sum_baseCount (ν : ∀ h, A h → ℚ) (hν : ∀ h a, 0 ≤ ν h a)
    (htotal : ∀ h, ∑ a, ν h a = 1) (h : H) :
    (∑ a, AllFieldPopulationCounts.baseCount (law ν) ⟨h, a⟩) = denominator ν := by
  apply Nat.cast_injective (R := ℚ)
  simp only [Nat.cast_sum, baseCount_cast ν hν, ← Finset.mul_sum, htotal, mul_one]

theorem population_dilation (allocation : Allocation) (ν : ∀ h, A h → ℚ)
    (m : ℕ) (h : History K) :
    population allocation (dilation ν m) h =
      population allocation m h * denominator ν := by
  simp only [population, AllFieldPopulationCounts.count, dilation]
  ac_rfl

theorem populationLength_dilation (allocation : Allocation) (ν : ∀ h, A h → ℚ)
    (m : ℕ) :
    populationLength (K := K) allocation (dilation ν m) =
      populationLength (K := K) allocation m * denominator ν := by
  simp only [populationLength, AllFieldPopulationCounts.blockLength, dilation]
  ac_rfl

theorem sum_count (allocation : Allocation) (history : H → History K)
    (ν : ∀ h, A h → ℚ) (hν : ∀ h a, 0 ≤ ν h a)
    (htotal : ∀ h, ∑ a, ν h a = 1) (m : ℕ) (h : H) :
    (∑ a, count allocation history ν m h a) =
      population allocation (dilation ν m) (history h) := by
  simp only [count, ← Finset.mul_sum, sum_baseCount ν hν htotal,
    population_dilation]

theorem count_cast (allocation : Allocation) (history : H → History K)
    (ν : ∀ h, A h → ℚ) (hν : ∀ h a, 0 ≤ ν h a)
    (m : ℕ) (h : H) (a : A h) :
    (count allocation history ν m h a : ℚ) =
      (populationLength (K := K) allocation (dilation ν m) : ℚ) *
        amount allocation (history h) * ν h a := by
  rw [count, Nat.cast_mul, population_cast, baseCount_cast ν hν,
    populationLength_dilation, Nat.cast_mul]
  ring

theorem count_cast_real (allocation : Allocation) (history : H → History K)
    (ν : ∀ h, A h → ℚ) (hν : ∀ h a, 0 ≤ ν h a)
    (m : ℕ) (h : H) (a : A h) :
    (count allocation history ν m h a : ℝ) =
      (populationLength (K := K) allocation (dilation ν m) : ℝ) *
        (amount allocation (history h) : ℝ) * (ν h a : ℝ) := by
  exact_mod_cast count_cast allocation history ν hν m h a

theorem count_dilate (allocation : Allocation) (history : H → History K)
    (ν : ∀ h, A h → ℚ) (m n : ℕ) (h : H) (a : A h) :
    count allocation history ν (m * n) h a =
      m * count allocation history ν n h a := by
  simp only [count, population, AllFieldPopulationCounts.count]
  ac_rfl

theorem count_mul_one (allocation : Allocation) (history : H → History K)
    (ν : ∀ h, A h → ℚ) (m : ℕ) (h : H) (a : A h) :
    count allocation history ν m h a = m * count allocation history ν 1 h a := by
  simpa only [Nat.mul_one] using count_dilate allocation history ν m 1 h a

theorem source_population_pos (allocation : Allocation) (ν : ∀ h, A h → ℚ)
    {m : ℕ} (hm : 0 < m) (h : History K) (hh : 0 < amount allocation h) :
    0 < population allocation (dilation ν m) h :=
  (AllFieldPopulationCounts.count_pos_iff (amount allocation)
    (amount_nonneg allocation) (dilation_pos ν hm) h).2 hh

theorem sum_count_pos (allocation : Allocation) (history : H → History K)
    (ν : ∀ h, A h → ℚ) (hν : ∀ h a, 0 ≤ ν h a)
    (htotal : ∀ h, ∑ a, ν h a = 1) {m : ℕ} (hm : 0 < m)
    (h : H) (hh : 0 < amount allocation (history h)) :
    0 < ∑ a, count allocation history ν m h a := by
  rw [sum_count allocation history ν hν htotal]
  exact source_population_pos allocation ν hm (history h) hh

theorem count_positive_law_positive (allocation : Allocation) (history : H → History K)
    (ν : ∀ h, A h → ℚ) (hν : ∀ h a, 0 ≤ ν h a)
    (m : ℕ) (h : H) (a : A h) (ha : 0 < count allocation history ν m h a) :
    0 < ν h a := by
  have hb : 0 < AllFieldPopulationCounts.baseCount (law ν) ⟨h, a⟩ :=
    Nat.pos_of_mul_pos_left ha
  have hbq : (0 : ℚ) < AllFieldPopulationCounts.baseCount (law ν) ⟨h, a⟩ := by
    exact_mod_cast hb
  rw [baseCount_cast ν hν] at hbq
  have hD : (0 : ℚ) < denominator ν := by exact_mod_cast denominator_pos ν
  exact (mul_pos_iff_of_pos_left hD).mp hbq

theorem count_pos_iff (allocation : Allocation) (history : H → History K)
    (ν : ∀ h, A h → ℚ) (hν : ∀ h a, 0 ≤ ν h a)
    {m : ℕ} (hm : 0 < m) (h : H) (hh : 0 < amount allocation (history h))
    (a : A h) : 0 < count allocation history ν m h a ↔ 0 < ν h a := by
  constructor
  · exact count_positive_law_positive allocation history ν hν m h a
  · intro ha
    apply Nat.mul_pos
    · exact (AllFieldPopulationCounts.count_pos_iff (amount allocation)
        (amount_nonneg allocation) hm (history h)).2 hh
    · have hb := (AllFieldPopulationCounts.count_pos_iff (law ν)
        (fun x => hν x.1 x.2) (m := 1) (by decide) ⟨h, a⟩).2 ha
      simpa only [AllFieldPopulationCounts.count, one_mul] using hb

theorem count_eq_zero_of_law_eq_zero (allocation : Allocation) (history : H → History K)
    (ν : ∀ h, A h → ℚ) (hν : ∀ h a, 0 ≤ ν h a)
    (m : ℕ) (h : H) (a : A h) (ha : ν h a = 0) :
    count allocation history ν m h a = 0 := by
  apply Nat.cast_injective (R := ℚ)
  simp only [count_cast allocation history ν hν, ha, mul_zero, Nat.cast_zero]

theorem count_ratio (allocation : Allocation) (history : H → History K)
    (ν : ∀ h, A h → ℚ) (hν : ∀ h a, 0 ≤ ν h a)
    (htotal : ∀ h, ∑ a, ν h a = 1) {m : ℕ} (hm : 0 < m)
    (h : H) (hh : 0 < amount allocation (history h)) (a : A h) :
    (count allocation history ν m h a : ℚ) /
      (∑ b, count allocation history ν m h b : ℕ) = ν h a := by
  rw [sum_count allocation history ν hν htotal, count_cast allocation history ν hν,
    population_cast]
  have hp : (populationLength (K := K) allocation (dilation ν m) : ℚ) *
      amount allocation (history h) ≠ 0 := by
    rw [← population_cast]
    exact_mod_cast (Nat.ne_of_gt (source_population_pos allocation ν hm (history h) hh))
  exact mul_div_cancel_left₀ _ hp

theorem count_ratio_real (allocation : Allocation) (history : H → History K)
    (ν : ∀ h, A h → ℚ) (hν : ∀ h a, 0 ≤ ν h a)
    (htotal : ∀ h, ∑ a, ν h a = 1) {m : ℕ} (hm : 0 < m)
    (h : H) (hh : 0 < amount allocation (history h)) (a : A h) :
    (count allocation history ν m h a : ℝ) /
      (∑ b, count allocation history ν m h b : ℕ) = (ν h a : ℝ) := by
  have hq := congrArg (fun q : ℚ => (q : ℝ))
    (count_ratio allocation history ν hν htotal hm h hh a)
  simpa only [Rat.cast_div, Rat.cast_natCast] using hq

theorem normalizedCountLaw_mass (allocation : Allocation) (history : H → History K)
    (ν : ∀ h, A h → ℚ) (hν : ∀ h a, 0 ≤ ν h a)
    (htotal : ∀ h, ∑ a, ν h a = 1) {m : ℕ} (hm : 0 < m)
    (h : H) (hh : 0 < amount allocation (history h)) (a : A h) :
    (ConditionalLabels.normalizedCountLaw (count allocation history ν m h)
      (sum_count_pos allocation history ν hν htotal hm h hh)).mass a = (ν h a : ℝ) :=
  count_ratio_real allocation history ν hν htotal hm h hh a

theorem normalizedCountLaw_mass_eq (allocation : Allocation) (history : H → History K)
    (ν : ∀ h, A h → ℚ) (hν : ∀ h a, 0 ≤ ν h a)
    (htotal : ∀ h, ∑ a, ν h a = 1) {m : ℕ} (hm : 0 < m)
    (h : H) (hh : 0 < amount allocation (history h)) :
    (ConditionalLabels.normalizedCountLaw (count allocation history ν m h)
      (sum_count_pos allocation history ν hν htotal hm h hh)).mass =
        fun a => (ν h a : ℝ) :=
  funext (normalizedCountLaw_mass allocation history ν hν htotal hm h hh)

end MatrixMultiplication.AllFieldTerminalPopulations

end

end MatrixAllFields

end OAI
