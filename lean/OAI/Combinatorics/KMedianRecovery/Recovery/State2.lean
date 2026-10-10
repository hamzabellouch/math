import Mathlib

namespace OAI

namespace MetricKMedianRecovery.Sampling

structure State (V : Type*) where
  deleted : Finset V
  leaves : List (V × ℝ)

namespace State
variable {V : Type*}
def initial : State V := ⟨∅, []⟩
noncomputable def remove (s : State V) (v : V) : State V := by
  classical
  exact ⟨insert v s.deleted, s.leaves⟩
def add (s : State V) (w : V) (R : ℝ) : State V :=
  ⟨s.deleted, s.leaves ++ [(w,R)]⟩
end State

variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]
abbrev Tag (V : Type*) := V ⊕ₗ ℕ

def realTag (v : V) : Tag V := toLex (Sum.inl v)
def leafTag (j : ℕ) : Tag V := toLex (Sum.inr j)

noncomputable def tags (S : Finset V) (s : State V) : Finset (Tag V) :=
  (S \ s.deleted).image realTag ∪ (Finset.range (s.leaves.length+1)).image leafTag

omit [PseudoMetricSpace V] in
lemma tags_nonempty (S : Finset V) (s : State V) : (tags S s).Nonempty := by
  refine ⟨leafTag 0,?_⟩
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨0,by simp, rfl⟩)

omit [PseudoMetricSpace V] in
lemma real_mem_tags (S : Finset V) (s : State V) (v : V) :
    realTag v ∈ tags S s ↔ v ∈ S \ s.deleted := by
  simp [tags, realTag, leafTag]

omit [PseudoMetricSpace V] in
lemma leaf_mem_tags (S : Finset V) (s : State V) (j : ℕ) :
    leafTag j ∈ tags S s ↔ j ≤ s.leaves.length := by
  simp [tags, realTag, leafTag]

noncomputable def tagDistance (Δ : ℝ) (s : State V) (x : V) (t : Tag V) : ℝ :=
  match ofLex t with
  | .inl v => dist x v
  | .inr 0 => Δ
  | .inr (j+1) => match s.leaves[j]? with
    | some z => dist x z.1 + z.2
    | none => Δ

noncomputable def chosen (S : Finset V) (Δ : ℝ) (s : State V) (x : V) : Tag V :=
  Classical.choose (Finset.exists_min_image (tags S s)
    (fun t => toLex (tagDistance Δ s x t,t)) (tags_nonempty S s))

lemma chosen_mem (S : Finset V) (Δ : ℝ) (s : State V) (x : V) :
    chosen S Δ s x ∈ tags S s :=
  (Classical.choose_spec (Finset.exists_min_image (tags S s)
    (fun t => toLex (tagDistance Δ s x t,t)) (tags_nonempty S s))).1

lemma chosen_key_le (S : Finset V) (Δ : ℝ) (s : State V) (x : V) {t : Tag V}
    (ht : t ∈ tags S s) :
    toLex (tagDistance Δ s x (chosen S Δ s x),chosen S Δ s x) ≤
      toLex (tagDistance Δ s x t,t) :=
  (Classical.choose_spec (Finset.exists_min_image (tags S s)
    (fun t => toLex (tagDistance Δ s x t,t)) (tags_nonempty S s))).2 t ht

noncomputable def reference (S : Finset V) (Δ : ℝ) (s : State V) (x : V) : ℝ :=
  tagDistance Δ s x (chosen S Δ s x)

lemma reference_le (S : Finset V) (Δ : ℝ) (s : State V) (x : V) {t : Tag V}
    (ht : t ∈ tags S s) : reference S Δ s x ≤ tagDistance Δ s x t :=
  Prod.Lex.monotone_fst _ _ (chosen_key_le S Δ s x ht)

lemma reference_le_real (S : Finset V) (Δ : ℝ) (s : State V) (x v : V)
    (hv : v ∈ S \ s.deleted) : reference S Δ s x ≤ dist x v :=
  reference_le S Δ s x ((real_mem_tags S s v).mpr hv)

lemma reference_le_diameter (S : Finset V) (Δ : ℝ) (s : State V) (x : V) :
    reference S Δ s x ≤ Δ :=
  reference_le S Δ s x ((leaf_mem_tags S s 0).mpr (Nat.zero_le _))

lemma reference_le_leaf (S : Finset V) (Δ : ℝ) (s : State V) (x : V)
    (j : ℕ) (z : V × ℝ) (hz : s.leaves[j]? = some z) :
    reference S Δ s x ≤ dist x z.1 + z.2 := by
  have hj : j < s.leaves.length := List.getElem?_eq_some_iff.mp hz |>.1
  have hh := reference_le S Δ s x ((leaf_mem_tags S s (j+1)).mpr (by omega))
  simpa only [tagDistance, leafTag, ofLex_toLex, hz] using hh

omit [LinearOrder V] in
lemma tagDistance_triangle (Δ : ℝ) (s : State V) (x y : V) (t : Tag V) :
    tagDistance Δ s x t ≤ dist x y + tagDistance Δ s y t := by
  cases ht : ofLex t with
  | inl v => simpa only [tagDistance, ht] using dist_triangle x y v
  | inr j =>
    cases j with
    | zero => simp only [tagDistance, ht]; linarith [dist_nonneg (x := x) (y := y)]
    | succ j =>
      cases hz : s.leaves[j]? with
      | none => simp only [tagDistance, ht, hz]; linarith [dist_nonneg (x := x) (y := y)]
      | some z =>
        simp only [tagDistance, ht, hz]
        linarith [dist_triangle x y z.1]

lemma reference_triangle (S : Finset V) (Δ : ℝ) (s : State V) (x y : V) :
    reference S Δ s x ≤ dist x y + reference S Δ s y :=
  (reference_le S Δ s x (chosen_mem S Δ s y)).trans
    (tagDistance_triangle Δ s x y (chosen S Δ s y))

lemma reference_nonneg (S : Finset V) (Δ : ℝ) (s : State V) (x : V)
    (hΔ : 0 ≤ Δ) (hr : ∀ z ∈ s.leaves, 0 ≤ z.2) : 0 ≤ reference S Δ s x := by
  unfold reference
  generalize chosen S Δ s x = t
  cases ht : ofLex t with
  | inl v => simpa only [tagDistance, ht] using (dist_nonneg (x := x) (y := v))
  | inr j =>
    cases j with
    | zero => simpa only [tagDistance, ht] using hΔ
    | succ j =>
      cases hz : s.leaves[j]? with
      | none => simpa only [tagDistance, ht, hz] using hΔ
      | some z =>
        simp only [tagDistance, ht, hz]
        exact add_nonneg dist_nonneg (hr z (List.mem_of_getElem? hz))

omit [PseudoMetricSpace V] in
lemma tags_add_mono (S : Finset V) (s : State V) (w : V) (R : ℝ) :
    tags S s ⊆ tags S (s.add w R) := by
  unfold tags
  apply Finset.union_subset_union_right
  exact Finset.image_subset_image (Finset.range_mono (by simp [State.add]))

lemma tagDistance_add_old (S : Finset V) (Δ : ℝ) (s : State V) (w : V) (R : ℝ)
    (x : V) {t : Tag V} (ht : t ∈ tags S s) :
    tagDistance Δ (s.add w R) x t = tagDistance Δ s x t := by
  cases he : ofLex t with
  | inl v => simp only [tagDistance, he]
  | inr j =>
    have htag : t = leafTag j := by exact congrArg toLex he
    have hj := (leaf_mem_tags S s j).mp (htag ▸ ht)
    cases j with
    | zero => simp only [tagDistance, he]
    | succ j =>
      have hj' : j < s.leaves.length := by omega
      simp only [tagDistance, he, State.add, List.getElem?_append, hj', ↓reduceIte]

lemma reference_add_le (S : Finset V) (Δ : ℝ) (s : State V) (w : V) (R : ℝ) (x : V) :
    reference S Δ (s.add w R) x ≤ reference S Δ s x := by
  have hh := reference_le S Δ (s.add w R) x (tags_add_mono S s w R (chosen_mem S Δ s x))
  exact hh.trans_eq (tagDistance_add_old S Δ s w R x (chosen_mem S Δ s x))

lemma chosen_add_consistent (S : Finset V) (Δ : ℝ) (s : State V) (w : V) (R : ℝ) (x : V)
    (hold : chosen S Δ (s.add w R) x ∈ tags S s) :
    chosen S Δ (s.add w R) x = chosen S Δ s x := by
  have h₁ := chosen_key_le S Δ s x hold
  have h₂ := chosen_key_le S Δ (s.add w R) x (tags_add_mono S s w R (chosen_mem S Δ s x))
  rw [tagDistance_add_old S Δ s w R x hold,
    tagDistance_add_old S Δ s w R x (chosen_mem S Δ s x)] at h₂
  exact congrArg (fun z : ℝ ×ₗ Tag V => (ofLex z).2) (le_antisymm h₂ h₁)

end MetricKMedianRecovery.Sampling

end OAI
