import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundaryHeight

namespace OAI

/-!
# From ray bounds to a leafwise height bound

On each generator orbit the boundary argument controls all ray characters
except one. The positive relation recovers that character, uniformly over the
finite ray set. A bounded product of generator orbits then controls the whole
nilpotent leaf. These are the two algebraic steps in the leaf-height lemma.
-/

namespace PolycyclicRecognition

open scoped BigOperators

variable {W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [DecidableEq I]

omit [FiniteDimensional ℝ W] in
/-- Deleting one character from a positive balanced separating family still
leaves a separating family. -/
theorem separates_after_deleting_one
    (α : I → Module.Dual ℝ W) (c : I → ℝ) (hc : ∀ i, 0 < c i)
    (hrel : ∀ w, ∑ i, c i * α i w = 0)
    (hsep : ∀ w, (∀ i, α i w = 0) → w = 0)
    (i₀ : I) (w : W) (hw : ∀ i, i ≠ i₀ → α i w = 0) : w = 0 := by
  apply hsep w
  intro i
  by_cases hi : i = i₀
  · subst i
    have hs : (∑ j, c j * α j w) = c i₀ * α i₀ w := by
      apply Finset.sum_eq_single i₀
      · intro j _ hj
        rw [hw j hj, mul_zero]
      · simp
    have hz : c i₀ * α i₀ w = 0 := hs.symm.trans (hrel w)
    exact (mul_eq_zero.mp hz).resolve_left (hc i₀).ne'
  · exact hw i hi

/-- The bound can be chosen uniformly in the omitted ray. -/
theorem exists_bound_of_all_but_one_form
    (α : I → Module.Dual ℝ W) (c : I → ℝ) (hc : ∀ i, 0 < c i)
    (hrel : ∀ w, ∑ i, c i * α i w = 0)
    (hsep : ∀ w, (∀ i, α i w = 0) → w = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i₀ : I) (w : W) (B : ℝ), 0 ≤ B →
      (∀ i, i ≠ i₀ → |α i w| ≤ B) → ‖w‖ ≤ C * B := by
  have hlocal (i₀ : I) : ∃ C : ℝ, 0 < C ∧ ∀ (w : W) (B : ℝ), 0 ≤ B →
      (∀ i, i ≠ i₀ → |α i w| ≤ B) → ‖w‖ ≤ C * B := by
    obtain ⟨C, hC, hbound⟩ := exists_bound_of_separating_forms
      (fun i : {i : I // i ≠ i₀} => α i)
      (fun w hw => separates_after_deleting_one α c hc hrel hsep i₀ w
        (fun i hi => hw ⟨i, hi⟩))
    exact ⟨C, hC, fun w B hB hw => hbound w B hB (fun i => hw i i.property)⟩
  choose C hC hbound using hlocal
  have hs : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ => (hC i).le
  refine ⟨(∑ i, C i) + 1, by linarith, ?_⟩
  intro i₀ w B hB hw
  apply (hbound i₀ w B hB hw).trans
  apply mul_le_mul_of_nonneg_right _ hB
  have hi : C i₀ ≤ ∑ i, C i :=
    Finset.single_le_sum (fun i _ => (hC i).le) (Finset.mem_univ i₀)
  linarith

omit [NormedSpace ℝ W] [FiniteDimensional ℝ W] [Fintype I] [DecidableEq I] in
/-- Uniform control for elementary right increments adds along a word. -/
theorem norm_increment_list_prod {G : Type*} [Group G]
    (f : G → W) (S : Set G) {B : ℝ}
    (hstep : ∀ g ∈ S, ∀ x, ‖f (x * g) - f x‖ ≤ B)
    (l : List G) (hl : ∀ g ∈ l, g ∈ S) (x : G) :
    ‖f (x * l.prod) - f x‖ ≤ (l.length : ℝ) * B := by
  induction l generalizing x with
  | nil => simp
  | cons g l ih =>
    have htail : ∀ a ∈ l, a ∈ S := fun a ha => hl a (by simp [ha])
    have hg : g ∈ S := hl g (by simp)
    calc
      ‖f (x * (g :: l).prod) - f x‖ = ‖f ((x * g) * l.prod) - f x‖ := by
        rw [List.prod_cons, mul_assoc]
      _ ≤ ‖f ((x * g) * l.prod) - f (x * g)‖ + ‖f (x * g) - f x‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (l.length : ℝ) * B + B := add_le_add (ih htail (x * g)) (hstep g hg x)
      _ = ((g :: l).length : ℝ) * B := by simp [add_mul]

omit [NormedSpace ℝ W] [FiniteDimensional ℝ W] [Fintype I] [DecidableEq I] in
/-- A uniform bound on word length in generator orbits makes the entire leaf
height variation uniformly bounded. Parameters inside each orbit are unrestricted. -/
theorem norm_increment_of_bounded_word_width {G : Type*} [Group G]
    (f : G → W) (S : Set G) (N : Subgroup G) (M : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hstep : ∀ g ∈ S, ∀ x, ‖f (x * g) - f x‖ ≤ B)
    (hwidth : ∀ n : N, ∃ l : List G,
      l.length ≤ M ∧ l.prod = n ∧ ∀ g ∈ l, g ∈ S) :
    ∀ (x : G) (n : N), ‖f (x * n) - f x‖ ≤ (M : ℝ) * B := by
  intro x n
  obtain ⟨l, hlen, hprod, hl⟩ := hwidth n
  rw [← hprod]
  exact (norm_increment_list_prod f S hstep l hl x).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) hB)

end PolycyclicRecognition

end OAI
