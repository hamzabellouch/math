import OAI.Combinatorics.ParityLifts.Flowers

namespace OAI

namespace Sparsification

lemma bernoulli_split (S : ℝ) (hS : 0 < S) (x y : ℕ)
    (hxy : S ^ 2 ≤ (x : ℝ) * y) :
    (1 / (1 + 1 / S) ^ x) + (1 / (1 + 1 / S) ^ y) ≤ 1 := by
  have hi : 0 ≤ 1 / S := le_of_lt (one_div_pos.mpr hS)
  have hx := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ 1 / S) x
  have hy := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ 1 / S) y
  have hax : (0 : ℝ) < (1 + 1 / S) ^ x := pow_pos (by linarith) _
  have hay : (0 : ℝ) < (1 + 1 / S) ^ y := pow_pos (by linarith) _
  have hab : 1 ≤ ((x : ℝ) * (1 / S)) * ((y : ℝ) * (1 / S)) := by
    have he : ((x : ℝ) * (1 / S)) * ((y : ℝ) * (1 / S)) = (x * y : ℝ) / S ^ 2 := by ring
    rw [he]
    exact (le_div_iff₀ (sq_pos_of_pos hS)).mpr (by simpa using hxy)
  have hm := mul_le_mul (show (x : ℝ) * (1 / S) ≤ (1 + 1 / S) ^ x - 1 by linarith)
    (show (y : ℝ) * (1 / S) ≤ (1 + 1 / S) ^ y - 1 by linarith)
    (mul_nonneg (Nat.cast_nonneg _) hi)
    (show 0 ≤ (1 + 1 / S) ^ x - 1 by nlinarith [mul_nonneg (Nat.cast_nonneg x) hi])
  have he : (1 / (1 + 1 / S) ^ x + 1 / (1 + 1 / S) ^ y) =
      ((1 + 1 / S) ^ y + (1 + 1 / S) ^ x) /
        ((1 + 1 / S) ^ x * (1 + 1 / S) ^ y) := by field_simp
  rw [he]
  apply (div_le_iff₀ (mul_pos hax hay)).mpr
  nlinarith

noncomputable def branchBase (r : ℕ) : ℝ := 1 + 1 / (r : ℝ) ^ 3

lemma branchBase_gt_one {r : ℕ} (hr : 0 < r) : 1 < branchBase r := by
  have hr' : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  dsimp [branchBase]
  have hi := one_div_pos.mpr (pow_pos hr' 3)
  linarith

lemma split_units {r : ℕ} (hr : 0 < r) :
    1 / branchBase r ^ (r ^ 2) + 1 / branchBase r ^ (r ^ 4) ≤ 1 := by
  apply bernoulli_split ((r : ℝ) ^ 3) (pow_pos (Nat.cast_pos.mpr hr) _) (r ^ 2) (r ^ 4)
  push_cast
  ring_nf
  rfl

lemma split_binary {r : ℕ} (hr : 0 < r) :
    1 / branchBase r ^ 1 + 1 / branchBase r ^ (r ^ 6) ≤ 1 := by
  apply bernoulli_split ((r : ℝ) ^ 3) (pow_pos (Nat.cast_pos.mpr hr) _) 1 (r ^ 6)
  push_cast
  ring_nf
  rfl

end Sparsification


namespace Sparsification

variable {α : Type} [DecidableEq α] [Fintype α]

structure State (α : Type) [DecidableEq α] [Fintype α] (h : ℕ) where
  formula : CNF α
  marked : CNF α
  created : ℕ
  reduced : Reduced formula
  width : ∀ C ∈ formula, C.card ≤ 3
  marked_sub : marked ⊆ binaries formula
  marked_degree : ∀ x, degree marked x ≤ h
  resource : created ≤ marked.card + h * (units formula).card

def State.spent {h : ℕ} (s : State α h) : ℕ := h * (units s.formula).card + s.created

lemma State.spent_bound {h : ℕ} (s : State α h) : s.spent ≤ 3 * Fintype.card α * h := by
  have hm := marked_card_bound s.marked h (fun C hC => Finset.card_pos.mp (by
    rw [(Finset.mem_filter.mp (s.marked_sub hC)).2]; omega)) s.marked_degree
  have hu : (units s.formula).card ≤ Fintype.card α := Finset.card_le_univ _
  have hr := s.resource
  unfold State.spent
  nlinarith

omit [Fintype α] in
lemma minimize_subset (F : CNF α) : minimize F ⊆ F := Finset.filter_subset _ _

def initialState (F : CNF α) (hw : ∀ C ∈ F, C.card ≤ 3) (h : ℕ) : State α h where
  formula := minimize F
  marked := ∅
  created := 0
  reduced := minimize_reduced F
  width := by
    intro C hC
    exact hw C (minimize_subset F hC)
  marked_sub := Finset.empty_subset _
  marked_degree := by intro x; simp [degree]
  resource := Nat.zero_le _

omit [DecidableEq α] [Fintype α] in
lemma singleton_reduced (C : Finset α) : Reduced {C} := by
  intro D hD E hE _
  exact (Finset.mem_singleton.mp hD).trans (Finset.mem_singleton.mp hE).symm

omit [Fintype α] in
lemma prune_width {F A : CNF α} (hF : ∀ C ∈ F, C.card ≤ 3)
    (hA : ∀ C ∈ A, C.card ≤ 3) : ∀ C ∈ prune F A, C.card ≤ 3 := by
  intro C hC
  rcases Finset.mem_union.mp hC with hC | hC
  · exact hF C (Finset.mem_filter.mp hC).1
  · exact hA C hC

omit [Fintype α] in
lemma survived_sub_binaries {F M A : CNF α} (hm : M ⊆ binaries F) :
    survived M A ⊆ binaries (prune F A) := by
  intro C hC
  have hC' := Finset.mem_filter.mp hC
  have hc := Finset.mem_filter.mp (hm hC'.1)
  exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _ (Finset.mem_filter.mpr
    ⟨hc.1, hC'.2⟩), hc.2⟩

def State.addUnits {h : ℕ} (s : State α h) (A : CNF α)
    (ha : ∀ C ∈ A, C.card = 1) (hf : Fresh s.formula A) : State α h where
  formula := prune s.formula A
  marked := survived s.marked A
  created := s.created
  reduced := prune_reduced s.reduced (by
    intro C hC D hD hCD
    exact Finset.eq_of_subset_of_card_le hCD (by rw [ha C hC, ha D hD])) hf
  width := prune_width s.width (by intro C hC; rw [ha C hC]; omega)
  marked_sub := survived_sub_binaries s.marked_sub
  marked_degree := fun x => (degree_survived_le _ _ x).trans (s.marked_degree x)
  resource := unit_resource hf ha s.marked_degree s.resource

lemma State.spent_addUnits {h : ℕ} (s : State α h) (A : CNF α)
    (ha : ∀ C ∈ A, C.card = 1) (hf : Fresh s.formula A) :
    (s.addUnits A ha hf).spent = s.spent + h * A.card := by
  simp only [State.spent, State.addUnits, units_prune_card _ _ hf ha]
  ring

def State.addBinaries {h : ℕ} (s : State α h) (A : CNF α)
    (ha : ∀ C ∈ A, C.card = 2) (hf : Fresh s.formula A)
    (hdeg : ∀ x, degree A x ≤ 1)
    (hn : ¬ Nonempty (Flower s.formula 1 1 h)) : State α h where
  formula := prune s.formula A
  marked := s.marked ∪ A
  created := s.created + A.card
  reduced := prune_reduced s.reduced (by
    intro C hC D hD hCD
    exact Finset.eq_of_subset_of_card_le hCD (by rw [ha C hC, ha D hD])) hf
  width := prune_width s.width (by intro C hC; rw [ha C hC]; omega)
  marked_sub := by
    intro C hC
    rcases Finset.mem_union.mp hC with hC | hC
    · apply survived_sub_binaries s.marked_sub
      rw [survived_binary_eq hf s.marked_sub ha]
      exact hC
    · exact Finset.mem_filter.mpr ⟨Finset.mem_union_right _ hC, ha C hC⟩
  marked_degree := binary_degree_invariant s.marked_sub (no_two_flower_degree hn) hdeg
  resource := binary_resource hf s.marked_sub ha s.resource

lemma State.spent_addBinaries {h : ℕ} (s : State α h) (A : CNF α)
    (ha : ∀ C ∈ A, C.card = 2) (hf : Fresh s.formula A)
    (hdeg : ∀ x, degree A x ≤ 1) (hn : ¬ Nonempty (Flower s.formula 1 1 h)) :
    (s.addBinaries A ha hf hdeg hn).spent = s.spent + A.card := by
  have hne : ∀ C ∈ A, C.Nonempty := by
    intro C hC; exact Finset.card_pos.mp (by rw [ha C hC]; omega)
  simp only [State.spent, State.addBinaries, units_prune _ _ hne,
    units_empty_of_binaries A ha, Finset.union_empty]
  ring

/-- A split stores its actual successor states, progress and the exact semantic
branching equation. Its numerical inequality is proved for the three cases. -/
structure Split {r : ℕ} (s : State α (r ^ 2)) where
  left : State α (r ^ 2)
  right : State α (r ^ 2)
  x : ℕ
  y : ℕ
  x_pos : 0 < x
  y_pos : 0 < y
  left_spent : left.spent = s.spent + x
  right_spent : right.spent = s.spent + y
  split_bound : 1 / branchBase r ^ x + 1 / branchBase r ^ y ≤ 1
  holds : ∀ v : α → Prop, Holds s.formula v ↔ Holds left.formula v ∨ Holds right.formula v

def Terminal (F : CNF α) (r : ℕ) : Prop :=
  ¬ Nonempty (Flower F 1 1 (r ^ 2)) ∧
  ¬ Nonempty (Flower F 1 2 (r ^ 4)) ∧ ¬ Nonempty (Flower F 2 1 (r ^ 4))

lemma state_terminal_or_split {r : ℕ} (hr : 0 < r) (s : State α (r ^ 2)) :
    Terminal s.formula r ∨ Nonempty (Split s) := by
  classical
  have hr2 : 0 < r ^ 2 := pow_pos hr _
  have hr4 : 0 < r ^ 4 := pow_pos hr _
  by_cases h2 : Nonempty (Flower s.formula 1 1 (r ^ 2))
  · obtain ⟨f⟩ := h2
    have hc : ∀ C ∈ ({f.core} : CNF α), C.card = 1 := by
      intro C hC; obtain rfl := Finset.mem_singleton.mp hC; exact f.core_card
    let l := s.addUnits {f.core} hc (f.core_fresh s.reduced (by omega) hr2)
    let t := s.addUnits f.petals f.petal_card (f.petals_fresh s.reduced (by omega))
    right
    refine ⟨⟨l, t, r ^ 2, r ^ 4, hr2, hr4, ?_, ?_, split_units hr, ?_⟩⟩
    · simpa [l] using s.spent_addUnits {f.core} hc (f.core_fresh s.reduced (by omega) hr2)
    · have he : r ^ 2 * r ^ 2 = r ^ 4 := by ring
      simpa [t, f.petals_card, he] using
        s.spent_addUnits f.petals f.petal_card (f.petals_fresh s.reduced (by omega))
    · exact f.branch_holds
  by_cases h32 : Nonempty (Flower s.formula 2 1 (r ^ 4))
  · obtain ⟨f⟩ := h32
    have hc : ∀ C ∈ ({f.core} : CNF α), C.card = 2 := by
      intro C hC; obtain rfl := Finset.mem_singleton.mp hC; exact f.core_card
    let l := s.addBinaries {f.core} hc (f.core_fresh s.reduced (by omega) hr4)
      (singleton_degree_le_one f.core) h2
    let t := s.addUnits f.petals f.petal_card (f.petals_fresh s.reduced (by omega))
    right
    refine ⟨⟨l, t, 1, r ^ 6, by omega, pow_pos hr _, ?_, ?_, split_binary hr, ?_⟩⟩
    · simpa [l] using s.spent_addBinaries {f.core} hc
        (f.core_fresh s.reduced (by omega) hr4) (singleton_degree_le_one f.core) h2
    · have he : r ^ 2 * r ^ 4 = r ^ 6 := by ring
      simpa [t, f.petals_card, he] using
        s.spent_addUnits f.petals f.petal_card (f.petals_fresh s.reduced (by omega))
    · exact f.branch_holds
  by_cases h31 : Nonempty (Flower s.formula 1 2 (r ^ 4))
  · obtain ⟨f⟩ := h31
    have hc : ∀ C ∈ ({f.core} : CNF α), C.card = 1 := by
      intro C hC; obtain rfl := Finset.mem_singleton.mp hC; exact f.core_card
    let l := s.addUnits {f.core} hc (f.core_fresh s.reduced (by omega) hr4)
    let t := s.addBinaries f.petals f.petal_card (f.petals_fresh s.reduced (by omega))
      (pairwise_degree_le_one f.petals f.pairwise) h2
    right
    refine ⟨⟨l, t, r ^ 2, r ^ 4, hr2, hr4, ?_, ?_, split_units hr, ?_⟩⟩
    · simpa [l] using s.spent_addUnits {f.core} hc (f.core_fresh s.reduced (by omega) hr4)
    · simpa [t, f.petals_card] using s.spent_addBinaries f.petals f.petal_card
        (f.petals_fresh s.reduced (by omega)) (pairwise_degree_le_one f.petals f.pairwise) h2
    · exact f.branch_holds
  exact Or.inl ⟨h2, h31, h32⟩

end Sparsification

end OAI
