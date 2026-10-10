import OAI.Algebra.DepthFive.Basic

namespace OAI

noncomputable section

namespace Problem335
universe u
variable {K : Type u} [CommSemiring K] {n : ℕ}

omit [CommSemiring K] in
/-- Every input leaf has formal degree at most one. -/
theorem d5LeafDegree_le_one (x : D5Leaf K n) : d5LeafDegree x ≤ 1 := by
  cases x <;> simp [d5LeafDegree]

/-- Bottom sums have degree zero or one, including empty bottom sums. -/
theorem bottomDegree_le_one (c : Depth5Circuit K n) (i : Fin c.bottomCount) :
    c.bottomDegree i ≤ 1 := by
  by_cases h : c.bottomInputs i = []
  · rw [c.bottomEmpty i h]
    omega
  · obtain ⟨entry, hentry⟩ := List.exists_mem_of_ne_nil _ h
    rw [← c.bottomHomogeneous i entry hentry]
    exact d5LeafDegree_le_one _

omit [CommSemiring K] in
/-- A zero-degree leaf is a scalar, syntactically, even if its value is zero. -/
theorem leaf_scalar_of_degree_zero (x : D5Leaf K n) (h : d5LeafDegree x = 0) :
    ∃ a : K, x = D5Leaf.scalar a := by
  cases x with
  | scalar a => exact ⟨a, rfl⟩
  | «variable» v => simp [d5LeafDegree] at h

omit [CommSemiring K] in
/-- A positive-degree leaf is a variable. -/
theorem leaf_variable_of_degree_pos (x : D5Leaf K n) (h : 0 < d5LeafDegree x) :
    ∃ v, x = D5Leaf.variable v := by
  cases x with
  | scalar a => simp [d5LeafDegree] at h
  | «variable» v => exact ⟨v, rfl⟩

/-- For a list of zeros and ones, the formal degree is the number of one inputs. -/
theorem sum_map_eq_length_filter_one {α : Type*} (d : α → ℕ) (l : List α)
    (hd : ∀ a ∈ l, d a ≤ 1) :
    (l.map d).sum = (l.filter fun a => d a = 1).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha : d a ≤ 1 := hd a (by simp)
      have hl : ∀ b ∈ l, d b ≤ 1 := fun b hb => hd b (by simp [hb])
      have hcases : d a = 0 ∨ d a = 1 := by omega
      rcases hcases with ha | ha <;> simp [ha, ih hl, Nat.add_comm]

/-- Repeated lower-product inputs count separately in their formal degree. -/
theorem lowerDegree_eq_linear_count (c : Depth5Circuit K n) (i : Fin c.lowerCount) :
    ((c.lowerInputs i).map c.bottomDegree).sum =
      ((c.lowerInputs i).filter fun j => c.bottomDegree j = 1).length := by
  apply sum_map_eq_length_filter_one
  intro j _
  exact bottomDegree_le_one c j

/-- The number of positive-degree input occurrences is bounded by their total degree. -/
theorem length_filter_pos_le_sum_map {α : Type*} (d : α → ℕ) (l : List α) :
    (l.filter fun a => 0 < d a).length ≤ (l.map d).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      by_cases ha : 0 < d a
      · simp [ha]
        omega
      · have hz : d a = 0 := by omega
        simpa [ha, hz] using ih

/-- The number of positive-degree middle factors is bounded by an upper product's degree. -/
theorem upper_positive_count_le_degree (c : Depth5Circuit K n) (i : Fin c.upperCount) :
    ((c.upperInputs i).filter fun j => 0 < c.middleDegree j).length ≤
      ((c.upperInputs i).map c.middleDegree).sum :=
  length_filter_pos_le_sum_map _ _

/-- An upper term that occurs at the output has at most outputDegree positive factors. -/
theorem output_term_positive_count_le_degree (c : Depth5Circuit K n)
    (entry : K × Fin c.upperCount) (hentry : entry ∈ c.outputInputs) :
    ((c.upperInputs entry.2).filter fun j => 0 < c.middleDegree j).length ≤
      c.outputDegree := by
  rw [← c.outputHomogeneous entry hentry]
  exact upper_positive_count_le_degree c entry.2

/-- A finite sum of scalar polynomials is a scalar polynomial. -/
theorem sum_eq_C_of_mem {σ : Type*} (l : List (MvPolynomial σ K))
    (h : ∀ p ∈ l, ∃ a : K, p = MvPolynomial.C a) :
    ∃ a : K, l.sum = MvPolynomial.C a := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons p l ih =>
      obtain ⟨a, ha⟩ := h p (by simp)
      obtain ⟨b, hb⟩ := ih (fun q hq => h q (by simp [hq]))
      exact ⟨a + b, by simp [ha, hb]⟩

/-- Zero-degree bottom sums really compute scalars; cancellation is harmless. -/
theorem bottomValue_eq_C_of_degree_zero (c : Depth5Circuit K n)
    (i : Fin c.bottomCount) (hdeg : c.bottomDegree i = 0) :
    ∃ a : K, bottomValue c i = MvPolynomial.C a := by
  unfold bottomValue
  apply sum_eq_C_of_mem
  intro p hp
  obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hp
  obtain ⟨a, ha⟩ := leaf_scalar_of_degree_zero (c.leaves entry.2)
    ((c.bottomHomogeneous i entry hentry).trans hdeg)
  exact ⟨entry.1 * a, by simp [ha, d5LeafValue]⟩

/-- Large-degree occurrences are bounded using their total formal degree. -/
theorem threshold_mul_length_filter_le_sum {α : Type*} (d : α → ℕ)
    (l : List α) (t : ℕ) :
    t * (l.filter fun a => t ≤ d a).length ≤ (l.map d).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      by_cases ha : t ≤ d a
      · simp [ha, Nat.mul_add]
        omega
      · simpa [ha] using le_trans ih (Nat.le_add_left _ _)

/-- The manuscript's number of high-degree occurrences bound for an upper term. -/
theorem output_term_high_count_bound (c : Depth5Circuit K n)
    (entry : K × Fin c.upperCount) (hentry : entry ∈ c.outputInputs) (t : ℕ) :
    t * ((c.upperInputs entry.2).filter fun j => t ≤ c.middleDegree j).length ≤
      c.outputDegree := by
  rw [← c.outputHomogeneous entry hentry]
  exact threshold_mul_length_filter_le_sum _ _ _

/-- Real thresholds need not be rounded to bound the number of large factors. -/
theorem real_threshold_mul_length_filter_le_sum {α : Type*} (d : α → ℕ)
    (l : List α) (t : ℝ) :
    t * ((l.filter fun a => t ≤ (d a : ℝ)).length : ℝ) ≤ (l.map d).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [Nat.cast_list_sum, List.map_map] at ih
      by_cases ha : t ≤ (d a : ℝ)
      · simp [ha, Nat.cast_add, mul_add]
        linarith
      · have hnonneg : (0 : ℝ) ≤ d a := Nat.cast_nonneg _
        simp [ha, Nat.cast_add]
        linarith

/-- The number of high middle-factor occurrences is at most output degree / threshold. -/
theorem output_term_high_count_le_div (c : Depth5Circuit K n)
    (entry : K × Fin c.upperCount) (hentry : entry ∈ c.outputInputs)
    (t : ℝ) (ht : 0 < t) :
    (((c.upperInputs entry.2).filter fun j => t ≤ (c.middleDegree j : ℝ)).length : ℝ) ≤
      (c.outputDegree : ℝ) / t := by
  apply (le_div_iff₀ ht).mpr
  rw [mul_comm, ← c.outputHomogeneous entry hentry]
  exact real_threshold_mul_length_filter_le_sum _ _ _

end Problem335

end

end OAI
