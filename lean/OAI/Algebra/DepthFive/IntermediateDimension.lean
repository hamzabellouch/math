import OAI.Algebra.DepthFive.DimensionCorrection
import OAI.Algebra.DepthFive.DegreeDiscrepancy

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- Factors applied first in the intermediate-space argument. -/
def positiveBidegreeSet {ι : Type*} (s : Finset ι) (e i : ι → ℕ) (lam : ℝ) : Finset ι := by
  classical
  exact s.filter (fun j => 0 < (i j : ℝ) - lam * e j)

/-- Total differentiation degree of the first group of factors. -/
def positiveBidegreeV {ι : Type*} (s : Finset ι) (e i : ι → ℕ) (lam : ℝ) : ℕ :=
  ∑ j ∈ positiveBidegreeSet s e i lam, i j

/-- Total multiplication degree of the first group of factors. -/
def positiveBidegreeU {ι : Type*} (s : Finset ι) (e i : ι → ℕ) (lam : ℝ) : ℕ :=
  ∑ j ∈ positiveBidegreeSet s e i lam, (e j - i j)

theorem positiveBidegreeV_le {ι : Type*} (s : Finset ι) (e i : ι → ℕ) (lam : ℝ) :
    positiveBidegreeV s e i lam ≤ ∑ j ∈ s, i j := by
  classical
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ => Nat.zero_le _)

theorem positiveBidegreeU_le {ι : Type*} (s : Finset ι) (e i : ι → ℕ) (lam : ℝ)
    (hie : ∀ j ∈ s, i j ≤ e j) :
    positiveBidegreeU s e i lam ≤ (∑ j ∈ s, e j) - ∑ j ∈ s, i j := by
  classical
  calc
    _ ≤ ∑ j ∈ s, (e j - i j) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => Nat.zero_le _)
    _ = _ := Finset.sum_tsub_distrib s hie

/-- Natural bidegree assignments give exactly the discrepancy-weight product. -/
theorem positiveBidegree_rpow {ι : Type*} (s : Finset ι) (e i : ι → ℕ)
    (ρ lam α : ℝ) (hα : 0 < α) (hie : ∀ j ∈ s, i j ≤ e j)
    (hlam : (1 + ρ) * lam = ρ)
    (hbalance : lam * (∑ j ∈ s, e j : ℕ) = (∑ j ∈ s, i j : ℕ)) :
    α ^ ((positiveBidegreeV s e i lam : ℝ) - ρ * positiveBidegreeU s e i lam) =
      ∏ j ∈ s, (α ^ ((1 + ρ) / 2)) ^ |(i j : ℝ) - lam * e j| := by
  classical
  have hzero : ∑ j ∈ s, ((i j : ℝ) - lam * e j) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    norm_cast at hbalance ⊢
    exact sub_eq_zero.mpr hbalance.symm
  have hcast : (positiveBidegreeU s e i lam : ℝ) =
      ∑ j ∈ s.filter (fun j => 0 < (i j : ℝ) - lam * e j), ((e j : ℝ) - i j) := by
    unfold positiveBidegreeU positiveBidegreeSet
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    exact Nat.cast_sub (hie j (Finset.mem_filter.mp hj).1)
  rw [hcast]
  simp only [positiveBidegreeV, positiveBidegreeSet, Nat.cast_sum]
  exact positive_bidegree_rpow s (fun j => (e j : ℝ)) (fun j => (i j : ℝ))
    ρ lam α hα hlam hzero

/-- The intermediate space associated to an admissible natural bidegree
assignment is bounded by its product of discrepancy weights. -/
theorem intermediate_dimension_le_weight_product {ι : Type*} (s : Finset ι)
    (e i : ι → ℕ) (k n v u a b : ℕ) (ρ lam : ℝ)
    (hie : ∀ j ∈ s, i j ≤ e j)
    (he : ∑ j ∈ s, e j = n) (hi : ∑ j ∈ s, i j = k)
    (hproportion : lam * n = k) (hlam : (1 + ρ) * lam = ρ)
    (hv : 1 ≤ v) (hu : 1 ≤ u) (ha : 0 < a) (hb : 0 < b)
    (hka : k ≤ a) (hbudget : 2 * k ≤ a + v)
    (hbalance : ((a : ℝ) / ((a : ℝ) + v)) ^ ρ ≤
      (b : ℝ) / ((b : ℝ) + u)) :
    (homogeneousDim v (a - positiveBidegreeV s e i lam) : ℝ) *
        homogeneousDim u (b + positiveBidegreeU s e i lam) ≤
      2 * ((homogeneousDim v a : ℝ) * homogeneousDim u b) *
        ∏ j ∈ s, (((a : ℝ) / ((a : ℝ) + v)) ^ ((1 + ρ) / 2)) ^
          |(i j : ℝ) - lam * e j| := by
  have hVk : positiveBidegreeV s e i lam ≤ k := by
    simpa only [hi] using positiveBidegreeV_le s e i lam
  have hVa : positiveBidegreeV s e i lam ≤ a := hVk.trans hka
  have hVbudget : 2 * positiveBidegreeV s e i lam ≤ a + v := by omega
  have hα : 0 < (a : ℝ) / ((a : ℝ) + v) := by positivity
  have hprop : lam * (∑ j ∈ s, e j : ℕ) = (∑ j ∈ s, i j : ℕ) := by
    rw [he, hi]
    exact hproportion
  have h := intermediate_dimension_le_balanced
    (I := positiveBidegreeV s e i lam) (J := positiveBidegreeU s e i lam)
    hv hu ha hb hVa hVbudget ρ hbalance
  rw [positiveBidegree_rpow s e i ρ lam _ hα hie hlam hprop] at h
  exact h

/-- Summing intermediate dimensions over the admissible bidegrees gives the
numerical product bound used after rank subadditivity. -/
theorem sum_intermediate_dimensions_le_weight_product {ι : Type*}
    [Fintype ι] [DecidableEq ι] (e : ι → ℕ) (k n v u a b : ℕ) (ρ lam : ℝ)
    (he : ∑ j, e j = n) (hproportion : lam * n = k)
    (hlam : (1 + ρ) * lam = ρ)
    (hv : 1 ≤ v) (hu : 1 ≤ u) (ha : 0 < a) (hb : 0 < b)
    (hka : k ≤ a) (hbudget : 2 * k ≤ a + v)
    (hbalance : ((a : ℝ) / ((a : ℝ) + v)) ^ ρ ≤
      (b : ℝ) / ((b : ℝ) + u)) :
    (∑ i ∈ (Fintype.piFinset (fun j => Finset.range (e j + 1))).filter
        (fun i => ∑ j, i j = k),
      (homogeneousDim v (a - positiveBidegreeV Finset.univ e i lam) : ℝ) *
        homogeneousDim u (b + positiveBidegreeU Finset.univ e i lam)) ≤
      2 * ((homogeneousDim v a : ℝ) * homogeneousDim u b) *
        ∏ j, degreeWeight (((a : ℝ) / ((a : ℝ) + v)) ^ ((1 + ρ) / 2)) lam (e j) := by
  classical
  let α : ℝ := (a : ℝ) / ((a : ℝ) + v)
  let q : ℝ := α ^ ((1 + ρ) / 2)
  let D : ℝ := (homogeneousDim v a : ℝ) * homogeneousDim u b
  let A := (Fintype.piFinset (fun j => Finset.range (e j + 1))).filter
    (fun i => ∑ j, i j = k)
  have hα : 0 ≤ α := by dsimp [α]; positivity
  change (∑ i ∈ A, _) ≤ 2 * D * ∏ j, degreeWeight q lam (e j)
  calc
    _ ≤ ∑ i ∈ A, 2 * D * ∏ j, q ^ |(i j : ℝ) - lam * e j| := by
      apply Finset.sum_le_sum
      intro i hi
      have hiA := Finset.mem_filter.mp hi
      have hie : ∀ j ∈ (Finset.univ : Finset ι), i j ≤ e j := by
        intro j _
        have hj := Fintype.mem_piFinset.mp hiA.1 j
        exact Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      exact intermediate_dimension_le_weight_product Finset.univ e i k n v u a b ρ lam
        hie he hiA.2 hproportion hlam hv hu ha hb hka hbudget hbalance
    _ = 2 * D * ∑ i ∈ A, ∏ j, q ^ |(i j : ℝ) - lam * e j| := by
      rw [Finset.mul_sum]
    _ ≤ 2 * D * ∏ j, degreeWeight q lam (e j) := by
      apply mul_le_mul_of_nonneg_left
      · exact bidegree_weight_sum_le e k q lam (Real.rpow_nonneg hα _)
      · dsimp [D]
        positivity

end Problem335

end

end OAI
