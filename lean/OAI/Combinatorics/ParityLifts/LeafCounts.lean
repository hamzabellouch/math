import OAI.Combinatorics.ParityLifts.SparseStates

namespace OAI

namespace Sparsification

variable {α : Type} [DecidableEq α] [Fintype α]

lemma weighted_split (b : ℝ) (hb : 0 < b) (s x y K l t : ℕ)
    (hl : (l : ℝ) * b ^ (s + x) ≤ b ^ K)
    (ht : (t : ℝ) * b ^ (s + y) ≤ b ^ K)
    (hs : 1 / b ^ x + 1 / b ^ y ≤ 1) :
    ((l + t : ℕ) : ℝ) * b ^ s ≤ b ^ K := by
  have hx : 0 < b ^ x := pow_pos hb _
  have hy : 0 < b ^ y := pow_pos hb _
  have hl' : (l : ℝ) * b ^ s ≤ b ^ K / b ^ x := by
    apply (le_div_iff₀ hx).mpr
    simpa [pow_add, mul_assoc] using hl
  have ht' : (t : ℝ) * b ^ s ≤ b ^ K / b ^ y := by
    apply (le_div_iff₀ hy).mpr
    simpa [pow_add, mul_assoc] using ht
  calc
    _ = (l : ℝ) * b ^ s + (t : ℝ) * b ^ s := by push_cast; ring
    _ ≤ b ^ K / b ^ x + b ^ K / b ^ y := add_le_add hl' ht'
    _ = b ^ K * (1 / b ^ x + 1 / b ^ y) := by ring
    _ ≤ b ^ K * 1 := mul_le_mul_of_nonneg_left hs (le_of_lt (pow_pos hb _))
    _ = _ := mul_one _

lemma state_leaves {r : ℕ} (hr : 0 < r) (s : State α (r ^ 2)) :
    ∃ L : List (CNF α),
      (∀ F ∈ L, Reduced F ∧ (∀ C ∈ F, C.card ≤ 3) ∧ Terminal F r) ∧
      (∀ v : α → Prop, Holds s.formula v ↔ ∃ F ∈ L, Holds F v) ∧
      (L.length : ℝ) * branchBase r ^ s.spent ≤
        branchBase r ^ (3 * Fintype.card α * r ^ 2) := by
  let K := 3 * Fintype.card α * r ^ 2
  have hb : 1 ≤ branchBase r := (branchBase_gt_one hr).le
  have hp : 0 < branchBase r := lt_of_lt_of_le zero_lt_one hb
  suffices ∀ n : ℕ, ∀ s : State α (r ^ 2), K - s.spent = n →
      ∃ L : List (CNF α),
        (∀ F ∈ L, Reduced F ∧ (∀ C ∈ F, C.card ≤ 3) ∧ Terminal F r) ∧
        (∀ v : α → Prop, Holds s.formula v ↔ ∃ F ∈ L, Holds F v) ∧
        (L.length : ℝ) * branchBase r ^ s.spent ≤ branchBase r ^ K by
    exact this _ s rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro s hn
    rcases state_terminal_or_split hr s with ht | hf
    · refine ⟨[s.formula], ?_, ?_, ?_⟩
      · intro F hF
        obtain rfl := List.mem_singleton.mp hF
        exact ⟨s.reduced, s.width, ht⟩
      · intro v
        simp
      · simp only [List.length_singleton, Nat.cast_one, one_mul]
        exact pow_le_pow_right₀ hb s.spent_bound
    · obtain ⟨f⟩ := hf
      have hl : K - f.left.spent < n := by
        have hK : f.left.spent ≤ K := f.left.spent_bound
        have he := f.left_spent
        have hx := f.x_pos
        omega
      have ht : K - f.right.spent < n := by
        have hK : f.right.spent ≤ K := f.right.spent_bound
        have he := f.right_spent
        have hy := f.y_pos
        omega
      obtain ⟨L, hL, hLv, hLc⟩ := ih _ hl f.left rfl
      obtain ⟨T, hT, hTv, hTc⟩ := ih _ ht f.right rfl
      refine ⟨L ++ T, ?_, ?_, ?_⟩
      · intro F hF
        rcases List.mem_append.mp hF with hF | hF
        · exact hL F hF
        · exact hT F hF
      · intro v
        rw [f.holds v, hLv v, hTv v]
        simp only [List.mem_append, or_and_right, exists_or]
      · rw [List.length_append]
        rw [f.left_spent] at hLc
        rw [f.right_spent] at hTc
        exact weighted_split _ hp s.spent f.x f.y K L.length T.length hLc hTc f.split_bound

/-- Width-three sparsification, with the explicit branching base and linear
leaf density. No sparsification theorem is imported or presumed. -/
theorem sparsification_parameter (F : CNF α) (hw : ∀ C ∈ F, C.card ≤ 3)
    (r : ℕ) (hr : 0 < r) : ∃ L : List (CNF α),
      (∀ H ∈ L, Reduced H ∧ (∀ C ∈ H, C.card ≤ 3) ∧
        H.card ≤ 1 + Fintype.card α * (1 + r ^ 2 + 2 * r ^ 8)) ∧
      (∀ v : α → Prop, Holds F v ↔ ∃ H ∈ L, Holds H v) ∧
      (L.length : ℝ) ≤ branchBase r ^ (3 * Fintype.card α * r ^ 2) := by
  obtain ⟨L, hL, hv, hc⟩ := state_leaves hr (initialState F hw (r ^ 2))
  refine ⟨L, ?_, ?_, ?_⟩
  · intro H hH
    obtain ⟨hred, hwidth, hn2, hn31, hn32⟩ := hL H hH
    refine ⟨hred, hwidth, ?_⟩
    have he : (r ^ 4) ^ 2 = r ^ 8 := by ring
    simpa [he] using sparse_leaf_density H (r ^ 2) (r ^ 4) (pow_pos hr _) hwidth hn2 hn31 hn32
  · intro v
    exact (minimize_holds F v).symm.trans (hv v)
  · have hp : 1 ≤ branchBase r ^ (initialState F hw (r ^ 2)).spent :=
      one_le_pow₀ (branchBase_gt_one hr).le
    exact (le_mul_of_one_le_right (Nat.cast_nonneg _) hp).trans hc

end Sparsification


namespace Sparsification

lemma branch_base_exponential (r n : ℕ) (hr : 0 < r) :
    branchBase r ^ (3 * n * r ^ 2) ≤ Real.exp (3 * (n : ℝ) / r) := by
  have hp : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have he : branchBase r ≤ Real.exp (1 / (r : ℝ) ^ 3) := by
    dsimp [branchBase]
    linarith [Real.add_one_le_exp (1 / (r : ℝ) ^ 3)]
  calc
    _ ≤ Real.exp (1 / (r : ℝ) ^ 3) ^ (3 * n * r ^ 2) := by
      exact pow_le_pow_left₀ (le_of_lt (lt_trans zero_lt_one (branchBase_gt_one hr))) he _
    _ = Real.exp ((3 * n * r ^ 2 : ℕ) * (1 / (r : ℝ) ^ 3)) := (Real.exp_nat_mul _ _).symm
    _ = _ := by congr 1; push_cast; field_simp

lemma indexed_rate_bound (j N : ℕ) (hj : 0 < j) :
    branchBase (12 * j) ^ (3 * (2 * N) * (12 * j) ^ 2) ≤
      (2 : ℝ) ^ ((N : ℝ) / j) := by
  have hp : (0 : ℝ) < j := Nat.cast_pos.mpr hj
  have hl : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  calc
    _ ≤ Real.exp (3 * (2 * N : ℕ) / (12 * j : ℕ)) :=
      branch_base_exponential _ _ (by omega)
    _ ≤ Real.exp (Real.log 2 * ((N : ℝ) / j)) := by
      apply Real.exp_le_exp.mpr
      have hm := mul_le_mul_of_nonneg_right hl
        (div_nonneg (Nat.cast_nonneg N) hp.le)
      push_cast
      calc
        3 * (2 * (N : ℝ)) / (12 * j) = (1 / 2 : ℝ) * (N / j) := by ring
        _ ≤ _ := hm
    _ = _ := (Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) _).symm

theorem indexed_sparsification {α : Type} [DecidableEq α] [Fintype α]
    (N : ℕ) (hα : Fintype.card α = 2 * N) (F : CNF α)
    (hw : ∀ C ∈ F, C.card ≤ 3) (j : ℕ) (hj : 0 < j) :
    ∃ L : List (CNF α),
      (∀ H ∈ L, Reduced H ∧ (∀ C ∈ H, C.card ≤ 3) ∧
        H.card ≤ 1 + 2 * N * (1 + (12 * j) ^ 2 + 2 * (12 * j) ^ 8)) ∧
      (∀ v : α → Prop, Holds F v ↔ ∃ H ∈ L, Holds H v) ∧
      (L.length : ℝ) ≤ (2 : ℝ) ^ ((N : ℝ) / j) := by
  obtain ⟨L, hL, hv, hc⟩ := sparsification_parameter F hw (12 * j) (by omega)
  refine ⟨L, ?_, hv, ?_⟩
  · simpa only [hα] using hL
  · exact (by simpa only [hα] using hc :
      (L.length : ℝ) ≤ branchBase (12 * j) ^ (3 * (2 * N) * (12 * j) ^ 2)).trans
      (indexed_rate_bound j N hj)

end Sparsification

end OAI
