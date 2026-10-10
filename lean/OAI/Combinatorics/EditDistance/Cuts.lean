import OAI.Combinatorics.EditDistance.Model

namespace OAI

/-!
# Finite scalar and absolutely summable cut decompositions
-/

namespace EditCuts
open scoped BigOperators
open Finset

lemma top_clipping_distance (a b x y : ℝ) (hba : b < a)
    (hx : x = a ∨ x ≤ b) (hy : y = a ∨ y ≤ b) :
    |x - y| = |min x b - min y b| +
      (a - b) * |(if x = a then (1 : ℝ) else 0) - (if y = a then (1 : ℝ) else 0)| := by
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · subst x; subst y; simp
  · subst x
    have hya : y < a := hy.trans_lt hba
    simp [min_eq_right hba.le, min_eq_left hy, hya.ne,
      abs_of_nonneg (sub_nonneg.mpr hya.le), abs_of_nonneg (sub_nonneg.mpr hy)]
  · subst y
    have hxa : x < a := hx.trans_lt hba
    simp [min_eq_right hba.le, min_eq_left hx, hxa.ne,
      abs_of_nonpos (sub_nonpos.mpr hxa.le), abs_of_nonpos (sub_nonpos.mpr hx)]
  · have hxa : x < a := hx.trans_lt hba
    have hya : y < a := hy.trans_lt hba
    simp [min_eq_left hx, min_eq_left hy, hxa.ne, hya.ne]

section Finite
variable {X : Type*} [Fintype X] [DecidableEq X]

def cut (A : Finset X) (x : X) : ℝ := if x ∈ A then 1 else 0

theorem scalar_decomposition_aux (s : Finset ℝ) :
    ∀ (f : X → ℝ), (∀ x, f x ∈ s) →
      ∃ w : Finset X → ℝ, (∀ A, 0 ≤ w A) ∧
        ∀ x y, |f x - f y| = ∑ A : Finset X, w A * |cut A x - cut A y| := by
  classical
  induction s using Finset.induction_on_max with
  | empty =>
    intro f hf
    refine ⟨fun _ => 0, fun _ => le_rfl, ?_⟩
    intro x
    simpa using hf x
  | insert a s hmax ih =>
    intro f hf
    by_cases hse : s = ∅
    · have hfconst (x : X) : f x = a := by simpa [hse] using hf x
      refine ⟨fun _ => 0, fun _ => le_rfl, ?_⟩
      intro x y
      simp [hfconst]
    have hsn : s.Nonempty := nonempty_iff_ne_empty.mpr hse
    let b : ℝ := s.max' hsn
    have hb : b ∈ s := max'_mem s hsn
    have hba : b < a := hmax b hb
    have hfb (x : X) (hx : f x ≠ a) : f x ≤ b := by
      exact le_max' s (f x) ((mem_insert.mp (hf x)).resolve_left hx)
    let f' : X → ℝ := fun x => min (f x) b
    have hf' (x : X) : f' x ∈ s := by
      by_cases hx : f x = a
      · simpa only [f', hx, min_eq_right hba.le] using hb
      · simpa only [f', min_eq_left (hfb x hx)] using
          ((mem_insert.mp (hf x)).resolve_left hx)
    obtain ⟨w, hw, hwd⟩ := ih f' hf'
    let A : Finset X := univ.filter (fun x => f x = a)
    have hcut (x : X) : cut A x = if f x = a then 1 else 0 := by simp [cut, A]
    have hcase (x : X) : f x = a ∨ f x ≤ b := by
      by_cases hx : f x = a
      · exact Or.inl hx
      · exact Or.inr (hfb x hx)
    have heq (x y : X) : |f x - f y| = |f' x - f' y| +
        (a - b) * |cut A x - cut A y| := by
      simpa only [f', hcut] using top_clipping_distance a b (f x) (f y) hba (hcase x) (hcase y)
    refine ⟨fun B => w B + if B = A then a - b else 0, ?_, ?_⟩
    · intro B
      apply add_nonneg (hw B)
      split_ifs
      · exact sub_nonneg.mpr hba.le
      · exact le_rfl
    · intro x y
      rw [heq, hwd]
      simp only [add_mul, sum_add_distrib, ite_mul, zero_mul, sum_ite_eq', mem_univ, ite_true]

theorem scalar_decomposition (f : X → ℝ) :
    ∃ w : Finset X → ℝ, (∀ A, 0 ≤ w A) ∧
      ∀ x y, |f x - f y| = ∑ A : Finset X, w A * |cut A x - cut A y| :=
  scalar_decomposition_aux (univ.image f) f (fun x => mem_image.mpr ⟨x, mem_univ x, rfl⟩)

end Finite
end EditCuts

namespace EditCuts
open scoped BigOperators
open Finset

abbrev RealL1 := lp (fun _ : ℕ => ℝ) 1

lemma l1_norm (f : RealL1) : ‖f‖ = ∑' n, |f n| := by
  simpa using lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ENNReal).toReal) f

lemma l1_summable (f : RealL1) : Summable (fun n => |f n|) := by
  simpa using (lp.memℓp f).summable (by norm_num : 0 < (1 : ENNReal).toReal)

lemma l1_norm_sub (f g : RealL1) : ‖f - g‖ = ∑' n, |f n - g n| :=
  l1_norm (f - g)

section Finite
variable {X : Type*} [Fintype X] [DecidableEq X]

omit [Fintype X] in
lemma cut_empty (x : X) : cut ∅ x = 0 := by simp [cut]
lemma cut_univ (x : X) : cut univ x = 1 := by simp [cut]

theorem scalar_decomposition_nontrivial (f : X → ℝ) :
    ∃ w : Finset X → ℝ, (∀ A, 0 ≤ w A) ∧ w ∅ = 0 ∧ w univ = 0 ∧
      ∀ x y, |f x - f y| = ∑ A : Finset X, w A * |cut A x - cut A y| := by
  classical
  obtain ⟨w, hw, hd⟩ := scalar_decomposition f
  refine ⟨fun A => if A = ∅ ∨ A = univ then 0 else w A, ?_, by simp, by simp, ?_⟩
  · intro A
    dsimp only
    split_ifs <;> simp_all
  · intro x y
    rw [hd]
    apply sum_congr rfl
    intro A _
    by_cases hac : A = ∅ ∨ A = univ
    · rcases hac with rfl | rfl <;> simp [cut_empty, cut_univ]
    · simp [hac]

lemma weight_le_distance (f : X → ℝ) (w : Finset X → ℝ)
    (hw : ∀ A, 0 ≤ w A)
    (hd : ∀ x y, |f x - f y| = ∑ A : Finset X, w A * |cut A x - cut A y|)
    (A : Finset X) (x y : X) (hx : x ∈ A) (hy : y ∉ A) :
    w A ≤ |f x - f y| := by
  rw [hd]
  calc
    w A = w A * |cut A x - cut A y| := by simp [cut, hx, hy]
    _ ≤ _ := single_le_sum (fun B _ => mul_nonneg (hw B) (abs_nonneg (cut B x - cut B y))) (mem_univ A)

theorem l1_decomposition (H : X → RealL1) :
    ∃ c : Finset X → ℝ, (∀ A, 0 ≤ c A) ∧ c ∅ = 0 ∧ c univ = 0 ∧
      ∀ x y, ‖H x - H y‖ = ∑ A : Finset X, c A * |cut A x - cut A y| := by
  classical
  choose w hw he hu hd using fun n => scalar_decomposition_nontrivial (fun x => H x n)
  have hs (A : Finset X) : Summable (fun n => w n A) := by
    by_cases ha : A = ∅ ∨ A = univ
    · rcases ha with rfl | rfl <;> simpa only [he, hu] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
    obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr (not_or.mp ha).1
    obtain ⟨y, hy⟩ : ∃ y, y ∉ A := by
      by_contra! hn
      exact (not_or.mp ha).2 (eq_univ_iff_forall.mpr hn)
    exact Summable.of_nonneg_of_le (fun n => hw n A)
      (fun n => weight_le_distance _ _ (hw n) (hd n) A x y hx hy)
      (l1_summable (H x - H y))
  refine ⟨fun A => ∑' n, w n A, fun A => tsum_nonneg (fun n => hw n A),
    by simp [he], by simp [hu], ?_⟩
  intro x y
  rw [l1_norm_sub]
  simp_rw [hd]
  rw [Summable.tsum_finsetSum]
  · apply sum_congr rfl
    intro A _
    exact (hs A).tsum_mul_right _
  · intro A _
    exact (hs A).mul_right _

end Finite
end EditCuts

end OAI
