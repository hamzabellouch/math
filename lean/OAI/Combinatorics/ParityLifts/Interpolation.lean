import OAI.Combinatorics.ParityLifts.TestAlgebra

namespace OAI

namespace ParityWL

open scoped BigOperators

section FiniteInterpolation

open scoped Classical

lemma color_indicator_mem_of_separation {X D : Type} [Fintype X] [DecidableEq D]
    (A : Subalgebra ℚ (X → ℚ)) (c : X → D)
    (hsep : ∀ x y, c x ≠ c y → ∃ f ∈ A,
      (∀ z w, c z = c w → f z = f w) ∧ f x ≠ f y) (d : D) :
    (fun x => if c x = d then (1 : ℚ) else 0) ∈ A := by
  by_cases hex : ∃ x, c x = d
  · obtain ⟨x₀, hx₀⟩ := hex
    let Y := {y : X // c x₀ ≠ c y}
    choose f hf hinv hne using (fun y : Y => hsep x₀ y.1 y.2)
    let p : X → ℚ := ∏ y : Y, (f y x₀ - f y y.1)⁻¹ • (f y - (f y y.1) • 1)
    have hp : p ∈ A := A.prod_mem (fun y _ =>
      A.smul_mem (A.sub_mem (hf y) (A.smul_mem A.one_mem (f y y.1))) _)
    have he : p = fun x => if c x = d then (1 : ℚ) else 0 := by
      funext x
      dsimp only [p]
      rw [Finset.prod_apply]
      by_cases hx : c x = d
      · rw [ite_eq_left hx]
        apply Finset.prod_eq_one
        intro y _
        simp only [Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul, mul_one]
        rw [hinv y x x₀ (hx.trans hx₀.symm)]
        exact inv_mul_cancel₀ (sub_ne_zero.mpr (hne y))
      · rw [ite_eq_right hx]
        let y : Y := ⟨x, fun he => hx (he.symm.trans hx₀)⟩
        apply Finset.prod_eq_zero (Finset.mem_univ y)
        simp only [Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul, mul_one]
        change _ * (f y x - f y x) = 0
        rw [sub_self, mul_zero]
    rwa [he] at hp
  · have he : (fun x => if c x = d then (1 : ℚ) else 0) = 0 := by
      funext x
      exact ite_eq_right (fun h => hex ⟨x, h⟩)
    rw [he]
    exact A.zero_mem

lemma count_map_as_sum {X D : Type} [Fintype X] [DecidableEq D] (c : X → D) (d : D) :
    (Multiset.count d (Finset.univ.val.map c) : ℚ) =
      ∑ x : X, if c x = d then (1 : ℚ) else 0 := by
  rw [Multiset.count_map, Finset.sum_boole]
  congr 1
  exact congrArg Multiset.card (by
    apply Multiset.filter_congr
    intro x _
    exact eq_comm)

end FiniteInterpolation

section RefinementOperators

open scoped Classical

variable {V W : Type} [Fintype V] [Fintype W]
variable (G : SimpleGraph V) (H : SimpleGraph W)

noncomputable def replacementSum {k : ℕ} (i : Fin k) (f : TuplePair V W k → ℚ) :
    TuplePair V W k → ℚ :=
  Sum.elim (fun x => ∑ y : V, f (.inl (Function.update x i y)))
    (fun x => ∑ y : W, f (.inr (Function.update x i y)))

lemma insertNth_comp_succAbove {k : ℕ} {A : Type} (i : Fin (k + 1)) (y : A)
    (x : Fin (k + 1) → A) :
    i.insertNth y (x ∘ i.succAbove) = Function.update x i y :=
  Fin.insertNth_removeNth i y x

lemma testSpan_replacementSum {k t : ℕ} (hkt : k ≤ t) (i : Fin k)
    {f : TuplePair V W k → ℚ} (hf : f ∈ testSpan G H k t) :
    replacementSum i f ∈ testSpan G H k t := by
  cases k with
  | zero => exact i.elim0
  | succ k =>
    have hmem := testSpan_reindex G H hkt i.succAbove
      (testSpan_sumInsert G H (by omega) i hf)
    have he : replacementSum i f = reindexLinear i.succAbove (sumInsertLinear i f) := by
      funext a
      cases a with
      | inl x =>
        change (∑ y : V, f (.inl (Function.update x i y))) =
          ∑ y : V, f (.inl (i.insertNth y (x ∘ i.succAbove)))
        simp only [insertNth_comp_succAbove]
      | inr x =>
        change (∑ y : W, f (.inr (Function.update x i y))) =
          ∑ y : W, f (.inr (i.insertNth y (x ∘ i.succAbove)))
        simp only [insertNth_comp_succAbove]
    rwa [← he] at hmem

def replaceEmbedding {k : ℕ} (i j : Fin k) : Fin (k + 1) :=
  if j = i then Fin.last k else j.castSucc

lemma insertNth_replaceEmbedding {k : ℕ} {A : Type} (i : Fin k) (y : A) (x : Fin k → A) :
    ((Fin.last k).insertNth y x) ∘ replaceEmbedding i = Function.update x i y := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [replaceEmbedding]
  · simp only [Function.comp_apply, replaceEmbedding, ite_eq_right hj, Function.update_of_ne hj]
    rw [← Fin.succAbove_last_apply j, Fin.insertNth_apply_succAbove]

noncomputable def jointReplacementSum {k : ℕ} (f : Fin k → TuplePair V W k → ℚ) :
    TuplePair V W k → ℚ :=
  Sum.elim (fun x => ∑ y : V, ∏ i : Fin k, f i (.inl (Function.update x i y)))
    (fun x => ∑ y : W, ∏ i : Fin k, f i (.inr (Function.update x i y)))

lemma testSpan_jointReplacementSum {k t : ℕ} (hkt : k + 1 ≤ t)
    {f : Fin k → TuplePair V W k → ℚ} (hf : ∀ i, f i ∈ testSpan G H k t) :
    jointReplacementSum f ∈ testSpan G H k t := by
  have hp : (∏ i : Fin k, reindexLinear (replaceEmbedding i) (f i)) ∈
      testSpan G H (k + 1) t :=
    (testAlgebra G H (k + 1) t hkt).prod_mem
      (fun i _ => testSpan_reindex G H hkt (replaceEmbedding i) (hf i))
  have hs := testSpan_sumInsert G H (by omega) (Fin.last k) hp
  have he : jointReplacementSum f = sumInsertLinear (Fin.last k)
      (∏ i : Fin k, reindexLinear (replaceEmbedding i) (f i)) := by
    funext a
    cases a with
    | inl x =>
      change (∑ y : V, ∏ i : Fin k, f i (.inl (Function.update x i y))) =
        ∑ y : V, (∏ i : Fin k, reindexLinear (replaceEmbedding i) (f i))
          (.inl ((Fin.last k).insertNth y x))
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.prod_apply]
      apply Finset.prod_congr rfl
      intro i _
      change f i (.inl (Function.update x i y)) =
        f i (.inl (((Fin.last k).insertNth y x) ∘ replaceEmbedding i))
      rw [insertNth_replaceEmbedding]
    | inr x =>
      change (∑ y : W, ∏ i : Fin k, f i (.inr (Function.update x i y))) =
        ∑ y : W, (∏ i : Fin k, reindexLinear (replaceEmbedding i) (f i))
          (.inr ((Fin.last k).insertNth y x))
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.prod_apply]
      apply Finset.prod_congr rfl
      intro i _
      change f i (.inr (Function.update x i y)) =
        f i (.inr (((Fin.last k).insertNth y x) ∘ replaceEmbedding i))
      rw [insertNth_replaceEmbedding]
  rwa [← he] at hs

end RefinementOperators

end ParityWL

end OAI
