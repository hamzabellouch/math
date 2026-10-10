import OAI.Probability.FreeIsing.Trees.Shells

namespace OAI

noncomputable section

namespace Problem367

def componentPairWeight {d : ℕ} (r : ℝ) : List (Fin d) → List (Fin d) → ℝ
  | [], v => r ^ v.length
  | _ :: u, [] => r ^ (u.length + 1)
  | a :: u, b :: v =>
      if a = b then r * componentPairWeight r u v else r ^ (u.length + v.length + 2)

def componentPairSum {d : ℕ} (r : ℝ) (c : Fin d) (k l : ℕ) : ℝ :=
  ∑ u : ReducedTail c k, ∑ v : ReducedTail c l, componentPairWeight r u.1 v.1

private theorem tail_length {d : ℕ} {c : Fin d} {n : ℕ} (w : ReducedTail c n) :
    w.1.length = n := w.2.1

@[simp] theorem componentPairSum_zero_left {d : ℕ} (r : ℝ) (c : Fin d) (l : ℕ) :
    componentPairSum r c 0 l = (((d - 1 : ℕ) : ℝ) * r) ^ l := by
  unfold componentPairSum
  rw [sum_reducedTail_zero c (fun u =>
    ∑ v : ReducedTail c l, componentPairWeight r u v.1)]
  simp only [componentPairWeight, tail_length, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, card_reducedTail, Nat.cast_pow, mul_pow]

@[simp] theorem componentPairSum_zero_right {d : ℕ} (r : ℝ) (c : Fin d) (k : ℕ) :
    componentPairSum r c k 0 = (((d - 1 : ℕ) : ℝ) * r) ^ k := by
  unfold componentPairSum
  simp_rw [sum_reducedTail_zero]
  have hnil (u : List (Fin d)) : componentPairWeight r u [] = r ^ u.length := by
    cases u <;> simp [componentPairWeight]
  simp only [hnil, tail_length, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, card_reducedTail, Nat.cast_pow, mul_pow]

private theorem sum_diagonal_constant {A : Type*} [Fintype A] [DecidableEq A] (F : A → ℝ) (C : ℝ) :
    (∑ a : A, ∑ b : A, if a = b then F a else C) =
      (∑ a : A, F a) + (Fintype.card A : ℝ) * (Fintype.card A - 1 : ℕ) * C := by
  classical
  have hrow (a : A) : (∑ b : A, if a = b then F a else C) =
      F a + (Fintype.card A - 1 : ℕ) * C := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a)]
    simp only [ite_true]
    rw [Finset.sum_congr rfl (fun b hb =>
      ite_eq_right (Ne.symm (Finset.mem_erase.mp hb).1))]
    simp
  simp_rw [hrow]
  simp [Finset.sum_add_distrib, mul_assoc]

theorem componentPairSum_succ {d : ℕ} (r : ℝ) (c : Fin d) (k l : ℕ) :
    componentPairSum r c (k + 1) (l + 1) =
      r * (∑ a : {a : Fin d // c ≠ a}, componentPairSum r a.1 k l) +
      ((d - 1 : ℕ) : ℝ) * ((d - 1 : ℕ) - 1 : ℕ) *
        (((d - 1 : ℕ) : ℝ) ^ k * ((d - 1 : ℕ) : ℝ) ^ l * r ^ (k + l + 2)) := by
  classical
  have hc : Fintype.card {a : Fin d // c ≠ a} = d - 1 := by
    simp
  have hinner (a b : {a : Fin d // c ≠ a}) :
      (∑ u : ReducedTail a.1 k, ∑ v : ReducedTail b.1 l,
        componentPairWeight r (a.1 :: u.1) (b.1 :: v.1)) =
      if a = b then r * componentPairSum r a.1 k l else
        ((d - 1 : ℕ) : ℝ) ^ k * ((d - 1 : ℕ) : ℝ) ^ l * r ^ (k + l + 2) := by
    by_cases hab : a = b
    · subst b
      simp only [componentPairWeight, ite_true, componentPairSum]
      simp_rw [← Finset.mul_sum]
    · have hab' : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
      simp only [ite_eq_right hab, componentPairWeight, ite_eq_right hab', tail_length,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_reducedTail, Nat.cast_pow]
      ring
  change (∑ u : ReducedTail c (k + 1), ∑ v : ReducedTail c (l + 1),
    componentPairWeight r u.1 v.1) = _
  rw [sum_reducedTail_succ c k (fun u =>
    ∑ v : ReducedTail c (l + 1), componentPairWeight r u v.1)]
  simp_rw [sum_reducedTail_succ c l]
  have hcomm :
      (∑ a : {a : Fin d // c ≠ a}, ∑ u : ReducedTail a.1 k,
        ∑ b : {a : Fin d // c ≠ a}, ∑ v : ReducedTail b.1 l,
          componentPairWeight r (a.1 :: u.1) (b.1 :: v.1)) =
      ∑ a : {a : Fin d // c ≠ a}, ∑ b : {a : Fin d // c ≠ a},
        ∑ u : ReducedTail a.1 k, ∑ v : ReducedTail b.1 l,
          componentPairWeight r (a.1 :: u.1) (b.1 :: v.1) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
  rw [hcomm]
  simp_rw [hinner]
  rw [sum_diagonal_constant]
  simp only [hc, ← Finset.mul_sum]

theorem componentPairSum_critical {d : ℕ} (r : ℝ) (c : Fin d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * r = 1) (k l : ℕ) :
    componentPairSum r c k l = 1 + (min k l : ℕ) * (1 - r) := by
  have hb : 1 ≤ d - 1 := by
    by_contra h
    have hz : d - 1 = 0 := by omega
    norm_num [hz] at hcritical
  have hc (a : Fin d) : Fintype.card {b : Fin d // a ≠ b} = d - 1 := by
    simp
  induction k generalizing c l with
  | zero => simp [hcritical]
  | succ k ih =>
    cases l with
    | zero => simp [hcritical]
    | succ l =>
      rw [componentPairSum_succ]
      simp_rw [ih]
      have hcross :
          ((d - 1 : ℕ) : ℝ) * ((d - 1 : ℕ) - 1 : ℕ) *
              (((d - 1 : ℕ) : ℝ) ^ k * ((d - 1 : ℕ) : ℝ) ^ l * r ^ (k + l + 2)) =
            1 - r := by
        rw [Nat.cast_sub hb]
        calc
          _ = ((((d - 1 : ℕ) : ℝ) * r) - r) *
              ((((d - 1 : ℕ) : ℝ) * r) ^ (k + l + 1)) := by
            simp only [pow_add, pow_one, pow_two, mul_pow]
            ring
          _ = 1 - r := by simp [hcritical]
      rw [hcross]
      simp only [Finset.sum_const, Finset.card_univ, hc, nsmul_eq_mul]
      rw [← mul_assoc, mul_comm r, hcritical, one_mul]
      have hmin : min (k + 1) (l + 1) = min k l + 1 := by omega
      simp only [hmin, Nat.cast_add, Nat.cast_one]
      ring

theorem componentPairSum_critical_le {d : ℕ} (r : ℝ) (c : Fin d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * r = 1) (k l : ℕ) :
    componentPairSum r c k l ≤ (min k l : ℕ) + 1 := by
  have hr : 0 ≤ r := by
    by_contra h
    have hp := mul_nonpos_of_nonneg_of_nonpos
      (Nat.cast_nonneg (d - 1) : (0 : ℝ) ≤ _) (le_of_lt (lt_of_not_ge h))
    linarith
  rw [componentPairSum_critical r c hcritical]
  have hm : (0 : ℝ) ≤ (min k l : ℕ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg hm hr]

theorem sum_componentPairSum_critical_le {d : ℕ} (r : ℝ) (c : Fin d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * r = 1) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1), componentPairSum r c k l) ≤
      (n + 1 : ℝ) ^ 3 := by
  calc
    _ ≤ ∑ _k ∈ Finset.range (n + 1), ∑ _l ∈ Finset.range (n + 1), (n + 1 : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro l hl
      have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hmin : (min k l : ℕ) ≤ n := (Nat.min_le_left _ _).trans hk'
      have hmin' : ((min k l : ℕ) : ℝ) ≤ n := by exact_mod_cast hmin
      exact (componentPairSum_critical_le r c hcritical k l).trans (by linarith)
    _ = _ := by simp; ring

def componentWordDistance {α : Type*} [DecidableEq α] : List α → List α → ℕ
  | [], v => v.length
  | _ :: u, [] => u.length + 1
  | a :: u, b :: v =>
      if a = b then componentWordDistance u v else u.length + v.length + 2

theorem componentPairWeight_eq_pow_distance {d : ℕ} (theta : ℝ)
    (u v : List (Fin d)) :
    componentPairWeight (theta ^ 2) u v =
      theta ^ (u.length + v.length + componentWordDistance u v) := by
  induction u generalizing v with
  | nil =>
    simp only [componentPairWeight, componentWordDistance, List.length_nil, zero_add]
    rw [← pow_mul]
    congr 1
    omega
  | cons a u ih =>
    cases v with
    | nil =>
      simp only [componentPairWeight, componentWordDistance, List.length_nil,
        List.length_cons, add_zero]
      rw [← pow_mul]
      congr 1
      omega
    | cons b v =>
      by_cases hab : a = b
      · simp only [componentPairWeight, componentWordDistance, ite_eq_left hab, List.length_cons]
        rw [ih, ← pow_add]
        congr 1
        omega
      · simp only [componentPairWeight, componentWordDistance, ite_eq_right hab, List.length_cons]
        rw [← pow_mul]
        congr 1
        omega

theorem componentPairWeight_eq_weighted_correlation {d : ℕ} (theta : ℝ)
    (u v : List (Fin d)) :
    componentPairWeight (theta ^ 2) u v =
      theta ^ u.length * theta ^ v.length * theta ^ componentWordDistance u v := by
  rw [componentPairWeight_eq_pow_distance, pow_add, pow_add]

theorem sum_component_weighted_correlation_critical {d : ℕ} (theta : ℝ) (c : Fin d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * theta ^ 2 = 1) (k l : ℕ) :
    (∑ u : ReducedTail c k, ∑ v : ReducedTail c l,
      theta ^ k * theta ^ l * theta ^ componentWordDistance u.1 v.1) =
      1 + (min k l : ℕ) * (1 - theta ^ 2) := by
  simpa only [componentPairSum, componentPairWeight_eq_weighted_correlation, tail_length]
    using componentPairSum_critical (theta ^ 2) c hcritical k l

theorem sum_component_weighted_correlation_critical_le {d : ℕ} (theta : ℝ) (c : Fin d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * theta ^ 2 = 1) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
      ∑ u : ReducedTail c k, ∑ v : ReducedTail c l,
        theta ^ k * theta ^ l * theta ^ componentWordDistance u.1 v.1) ≤
      (n + 1 : ℝ) ^ 3 := by
  simpa only [componentPairSum, componentPairWeight_eq_weighted_correlation, tail_length]
    using sum_componentPairSum_critical_le (theta ^ 2) c hcritical n

theorem sum_component_radial_sq_critical {d : ℕ} (theta : ℝ) (c : Fin d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * theta ^ 2 = 1) (k : ℕ) :
    (∑ u : ReducedTail c k, (theta ^ u.1.length) ^ 2) = 1 := by
  simp only [tail_length, Finset.sum_const, Finset.card_univ, card_reducedTail,
    nsmul_eq_mul, Nat.cast_pow]
  rw [← pow_mul, Nat.mul_comm k 2, pow_mul, ← mul_pow, hcritical, one_pow]

theorem sum_component_radial_sq_levels_critical {d : ℕ} (theta : ℝ) (c : Fin d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * theta ^ 2 = 1) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), ∑ u : ReducedTail c k, (theta ^ u.1.length) ^ 2) =
      (n + 1 : ℝ) := by
  simp [sum_component_radial_sq_critical theta c hcritical]

end Problem367

end

end OAI
