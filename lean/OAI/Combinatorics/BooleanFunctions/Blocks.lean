import OAI.Combinatorics.BooleanFunctions.Conditioning

namespace OAI

open scoped BigOperators

noncomputable section

namespace SquareRootDegree

/-! ## Disjoint blocks and finite observation degree calculus -/

attribute [local instance] Classical.propDecidable

def blockCurry (κ ι α : Type*) : ((κ × ι) → α) ≃ (κ → ι → α) where
  toFun x j i := x (j,i)
  invFun x ji := x ji.1 ji.2
  left_inv _ := rfl
  right_inv _ := rfl

theorem average_pi_prod {κ α : Type*} [Fintype κ] [Fintype α] (f : κ → α → ℝ) :
    average (fun x : κ → α => ∏ i, f i (x i)) = ∏ i, average (f i) := by
  simp only [average, Fintype.card_fun, Nat.cast_pow, inv_pow, ← Fintype.prod_sum,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

theorem average_pi_eval {κ α : Type*} [Fintype κ] [Fintype α] [Nonempty α]
    (j : κ) (f : α → ℝ) : average (fun x : κ → α => f (x j)) = average f := by
  have he := average_pi_prod (fun i a => if i = j then f a else 1)
  have hif (i : κ) : average (fun a : α => if i = j then f a else 1) =
      if i = j then average f else 1 := by
    split_ifs <;> simp_all [average_const]
  simpa [Finset.prod_ite_eq, hif] using he

theorem fourierDegree_comp_coordinates_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : Cube ι → ℝ) (e : ι → κ) :
    fourierDegree (fun x : Cube κ => f (fun i => x (e i))) ≤ fourierDegree f := by
  have he : (fun x : Cube κ => f (fun i => x (e i))) = fun x =>
      ∑ s : Finset ι, fourierCoeff f s * character s (fun i => x (e i)) := by
    funext x
    exact fourier_inversion f _
  rw [he]
  apply fourierDegree_sum_le
  intro s _
  by_cases hs : fourierCoeff f s = 0
  · simp [hs, fourierDegree_const]
  apply (fourierDegree_const_mul_le _ _).trans
  apply (fourierDegree_le_card_of_dependsOn (t := s.image e) ?_).trans
  · exact (Finset.card_image_le).trans
      (Finset.le_sup (f := Finset.card) (by simp [hs]))
  · intro x y hxy
    apply Finset.prod_congr rfl
    intro i hi
    exact congrArg sign (hxy (e i) (Finset.mem_image.mpr ⟨i,hi,rfl⟩))

theorem fourierDegree_comp_observation_le {ι α : Type*} [Fintype ι] [Fintype α]
    (F : Cube ι → α) (D : ℕ) (hF : ∀ a, fourierDegree (cell F a) ≤ D) (g : α → ℝ) :
    fourierDegree (fun x => g (F x)) ≤ D := by
  have he : (fun x => g (F x)) = fun x => ∑ a, g a * cell F a x := by
    funext x
    simp [cell]
  rw [he]
  apply fourierDegree_sum_le
  intro a _
  exact (fourierDegree_const_mul_le _ _).trans (hF a)

theorem cell_tuple {α β κ : Type*} [Fintype κ] (F : κ → α → β) (b : κ → β) (x : α) :
    cell (fun x i => F i x) b x = ∏ i, cell (F i) (b i) x := by
  by_cases h : (fun i => F i x) = b
  · simp only [cell, h, ite_true]
    apply Eq.symm
    apply Finset.prod_eq_one
    intro i _
    rw [show F i x = b i from congrFun h i]
    simp
  · have hi : ∃ i, F i x ≠ b i := by
      by_contra hn
      push Not at hn
      exact h (funext hn)
    obtain ⟨i, hi⟩ := hi
    simp only [cell, h, ite_false]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem fourierDegree_comp_tuple_le {ι α κ : Type*}
    [Fintype ι] [Fintype α] [Fintype κ]
    (F : κ → Cube ι → α) (D : κ → ℕ)
    (hF : ∀ i a, fourierDegree (cell (F i) a) ≤ D i) (g : (κ → α) → ℝ) :
    fourierDegree (fun x => g (fun i => F i x)) ≤ ∑ i, D i := by
  apply fourierDegree_comp_observation_le
  intro a
  have he : cell (fun x i => F i x) a = fun x => ∏ i, cell (F i) (a i) x := by
    funext x
    exact cell_tuple F a x
  rw [he]
  apply (fourierDegree_prod_le _ _).trans
  exact Finset.sum_le_sum (fun i _ => hF i (a i))

theorem fourierDegree_block_cell_le {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (F : Cube ι → α) (D : ℕ) (hF : ∀ a, fourierDegree (cell F a) ≤ D) (j : κ) (a : α) :
    fourierDegree (cell (fun x : Cube (κ × ι) => F (blockCurry κ ι Bool x j)) a) ≤ D := by
  exact (fourierDegree_comp_coordinates_le (cell F a) (fun i => (j,i))).trans (hF a)

end SquareRootDegree

end

end OAI
