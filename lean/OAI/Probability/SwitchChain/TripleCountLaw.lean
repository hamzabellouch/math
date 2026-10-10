import OAI.Probability.SwitchChain.CountCoupling

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.TripleCountLaw

abbrev Triple (m : ℕ) :=
  {x : Fin 3 → Fin (m + 1) // ∑ i : Fin 3, (x i).val = m}

def weight (a : Fin 3 → ℕ) {m : ℕ} (x : Triple m) : ℝ :=
  ∏ i : Fin 3, CountCoupling.countWeight (a i) (x.val i).val

abbrev Fiber (m : ℕ) (σ : Equiv.Perm (Fin 3)) (t : ℕ) :=
  {x : Triple m // (x.val (σ 0)).val = t}

def fiberEquiv (m : ℕ) (σ : Equiv.Perm (Fin 3)) (t : ℕ) (ht : t ≤ m) :
    Fin (m - t + 1) ≃ Fiber m σ t where
  toFun y :=
    ⟨⟨fun i => (![⟨t, by omega⟩, ⟨y.val, by omega⟩,
      ⟨m - t - y.val, by omega⟩] : Fin 3 → Fin (m + 1)) (σ.symm i), by
      rw [← Equiv.sum_comp σ]
      simp only [Equiv.symm_apply_apply]
      simp only [Fin.sum_univ_three]
      dsimp
      omega⟩, by simp⟩
  invFun x := ⟨(x.val.val (σ 1)).val, by
    have hs := x.val.property
    rw [← Equiv.sum_comp σ] at hs
    simp only [Fin.sum_univ_three] at hs
    have hx := x.property
    omega⟩
  left_inv y := by simp
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    obtain ⟨j, rfl⟩ := σ.surjective i
    apply Fin.ext
    have hs := x.val.property
    rw [← Equiv.sum_comp σ] at hs
    simp only [Fin.sum_univ_three] at hs
    have hx := x.property
    fin_cases j <;> simp at * <;> omega

@[simp] theorem fiberEquiv_coordinate_zero (m : ℕ) (σ : Equiv.Perm (Fin 3))
    (t : ℕ) (ht : t ≤ m) (y : Fin (m - t + 1)) :
    (((fiberEquiv m σ t ht y).val.val (σ 0)).val) = t := by
  simp [fiberEquiv]

@[simp] theorem fiberEquiv_coordinate_one (m : ℕ) (σ : Equiv.Perm (Fin 3))
    (t : ℕ) (ht : t ≤ m) (y : Fin (m - t + 1)) :
    (((fiberEquiv m σ t ht y).val.val (σ 1)).val) = y.val := by
  simp [fiberEquiv]

@[simp] theorem fiberEquiv_coordinate_two (m : ℕ) (σ : Equiv.Perm (Fin 3))
    (t : ℕ) (ht : t ≤ m) (y : Fin (m - t + 1)) :
    (((fiberEquiv m σ t ht y).val.val (σ 2)).val) = m - t - y.val := by
  simp [fiberEquiv]

theorem weight_pos (a : Fin 3 → ℕ) {m : ℕ} (x : Triple m) : 0 < weight a x := by
  exact Finset.prod_pos (fun i _ => CountCoupling.countWeight_pos _ _)

theorem weight_fiberEquiv (a : Fin 3 → ℕ) (m : ℕ) (σ : Equiv.Perm (Fin 3))
    (t : ℕ) (ht : t ≤ m) (y : Fin (m - t + 1)) :
    weight a (fiberEquiv m σ t ht y).val =
      CountCoupling.countWeight (a (σ 0)) t *
        CountCoupling.pairWeight (a (σ 1)) (a (σ 2)) (m - t) y.val := by
  unfold weight
  rw [← Equiv.prod_comp σ]
  simp [Fin.prod_univ_three, CountCoupling.pairWeight, mul_assoc]

def conditionalAverage (a : Fin 3 → ℕ) {m : ℕ} (f : Triple m → ℝ)
    (σ : Equiv.Perm (Fin 3)) (t : ℕ) : ℝ :=
  (∑ x : Fiber m σ t, weight a x.val * f x.val) /
    (∑ x : Fiber m σ t, weight a x.val)

theorem conditionalAverage_reindex (a : Fin 3 → ℕ) {m : ℕ}
    (f : Triple m → ℝ) (σ : Equiv.Perm (Fin 3)) (t : ℕ) (ht : t ≤ m) :
    conditionalAverage a f σ t =
      (∑ y : Fin (m - t + 1),
        CountCoupling.pairWeight (a (σ 1)) (a (σ 2)) (m - t) y.val *
          f (fiberEquiv m σ t ht y).val) /
      (∑ y : Fin (m - t + 1),
        CountCoupling.pairWeight (a (σ 1)) (a (σ 2)) (m - t) y.val) := by
  unfold conditionalAverage
  rw [← Equiv.sum_comp (fiberEquiv m σ t ht) (fun x => weight a x.val * f x.val),
    ← Equiv.sum_comp (fiberEquiv m σ t ht) (fun x => weight a x.val)]
  simp_rw [weight_fiberEquiv, mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ (ne_of_gt (CountCoupling.countWeight_pos _ _))

def rowSum {m : ℕ} (b : Fin 3 → ℕ → ℝ) (x : Triple m) : ℝ :=
  ∑ i : Fin 3, b i (x.val i).val

theorem rowSum_fiberEquiv (b : Fin 3 → ℕ → ℝ) (m : ℕ)
    (σ : Equiv.Perm (Fin 3)) (t : ℕ) (ht : t ≤ m) (y : Fin (m - t + 1)) :
    rowSum b (fiberEquiv m σ t ht y).val =
      b (σ 0) t + (b (σ 1) y.val + b (σ 2) (m - t - y.val)) := by
  unfold rowSum
  rw [← Equiv.sum_comp σ]
  simp [Fin.sum_univ_three, add_assoc]

theorem conditionalAverage_rowSum (a : Fin 3 → ℕ) (m : ℕ)
    (b : Fin 3 → ℕ → ℝ) (σ : Equiv.Perm (Fin 3)) (t : ℕ) (ht : t ≤ m) :
    conditionalAverage a (rowSum b : Triple m → ℝ) σ t =
      b (σ 0) t + CountCoupling.pairExpectation (a (σ 1)) (a (σ 2)) (m - t)
        (fun y => b (σ 1) y + b (σ 2) (m - t - y)) := by
  rw [conditionalAverage_reindex a (rowSum b) σ t ht]
  simp_rw [rowSum_fiberEquiv]
  rw [Fin.sum_univ_eq_sum_range
    (fun y => CountCoupling.pairWeight (a (σ 1)) (a (σ 2)) (m - t) y *
      (b (σ 0) t + (b (σ 1) y + b (σ 2) (m - t - y)))) (m - t + 1),
    Fin.sum_univ_eq_sum_range]
  unfold CountCoupling.pairExpectation
  have hpos : 0 < ∑ y ∈ Finset.range (m - t + 1),
      CountCoupling.pairWeight (a (σ 1)) (a (σ 2)) (m - t) y := by
    apply Finset.sum_pos
    · intro y hy
      exact CountCoupling.pairWeight_pos _ _ _ _
    · exact ⟨0, Finset.mem_range.mpr (by omega)⟩
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul]
  field_simp [ne_of_gt hpos]

theorem fiber_nonempty (m : ℕ) (σ : Equiv.Perm (Fin 3)) (t : ℕ) (ht : t ≤ m) :
    Nonempty (Fiber m σ t) :=
  ⟨fiberEquiv m σ t ht ⟨0, by omega⟩⟩

theorem fiber_weight_sum_pos (a : Fin 3 → ℕ) (m : ℕ)
    (σ : Equiv.Perm (Fin 3)) (t : ℕ) (ht : t ≤ m) :
    0 < ∑ x : Fiber m σ t, weight a x.val := by
  have := fiber_nonempty m σ t ht
  exact Finset.sum_pos (fun x _ => weight_pos a x.val) Finset.univ_nonempty

def totalWeight (a : Fin 3 → ℕ) (m : ℕ) : ℝ := ∑ x : Triple m, weight a x

theorem totalWeight_pos (a : Fin 3 → ℕ) (m : ℕ) : 0 < totalWeight a m := by
  obtain ⟨x⟩ := fiber_nonempty m (Equiv.refl _) 0 (Nat.zero_le _)
  have : Nonempty (Triple m) := ⟨x.val⟩
  exact Finset.sum_pos (fun x _ => weight_pos a x) Finset.univ_nonempty

def probability (a : Fin 3 → ℕ) {m : ℕ} (x : Triple m) : ℝ :=
  weight a x / totalWeight a m

theorem probability_pos (a : Fin 3 → ℕ) {m : ℕ} (x : Triple m) :
    0 < probability a x := div_pos (weight_pos a x) (totalWeight_pos a m)

theorem probability_sum (a : Fin 3 → ℕ) (m : ℕ) :
    ∑ x : Triple m, probability a x = 1 := by
  simp only [probability, ← Finset.sum_div]
  exact div_self (ne_of_gt (totalWeight_pos a m))

theorem sum_fiber_eq_indicator (m : ℕ) (σ : Equiv.Perm (Fin 3)) (t : ℕ)
    (f : Triple m → ℝ) :
    (∑ x : Fiber m σ t, f x.val) =
      ∑ x : Triple m, if (x.val (σ 0)).val = t then f x else 0 := by
  classical
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (fun x => by simp) f).symm

theorem normalized_conditionalAverage (a : Fin 3 → ℕ) {m : ℕ}
    (f : Triple m → ℝ) (σ : Equiv.Perm (Fin 3)) (t : ℕ) :
    ((∑ x : Triple m, if (x.val (σ 0)).val = t then probability a x * f x else 0) /
      (∑ x : Triple m, if (x.val (σ 0)).val = t then probability a x else 0)) =
      conditionalAverage a f σ t := by
  rw [← sum_fiber_eq_indicator, ← sum_fiber_eq_indicator]
  unfold probability conditionalAverage
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, ← Finset.sum_div]
  exact div_div_div_cancel_right₀ (ne_of_gt (totalWeight_pos a m)) _ _

theorem marginal_pos (a : Fin 3 → ℕ) (m : ℕ) (σ : Equiv.Perm (Fin 3))
    (t : ℕ) (ht : t ≤ m) :
    0 < ∑ x : Triple m, if (x.val (σ 0)).val = t then probability a x else 0 := by
  rw [← sum_fiber_eq_indicator]
  have := fiber_nonempty m σ t ht
  exact Finset.sum_pos (fun x _ => probability_pos a x.val) Finset.univ_nonempty

theorem normalized_conditional_rowSum (a : Fin 3 → ℕ) (m : ℕ)
    (b : Fin 3 → ℕ → ℝ) (σ : Equiv.Perm (Fin 3)) (t : ℕ) (ht : t ≤ m) :
    ((∑ x : Triple m, if (x.val (σ 0)).val = t then
        probability a x * rowSum b x else 0) /
      (∑ x : Triple m, if (x.val (σ 0)).val = t then probability a x else 0)) =
      b (σ 0) t + CountCoupling.pairExpectation (a (σ 1)) (a (σ 2)) (m - t)
        (fun y => b (σ 1) y + b (σ 2) (m - t - y)) := by
  rw [normalized_conditionalAverage]
  exact conditionalAverage_rowSum a m b σ t ht

end Problem315.TripleCountLaw

end

end OAI
