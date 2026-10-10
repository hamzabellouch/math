import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularMatrixHeight

namespace OAI

/-!
# Polynomial coordinate bounds for bounded-height triangular words

We use the actual prefix diagonals of a word in positive triangular matrices.
Every normalized increment is unipotent. Thus bounded heights at every prefix,
with bounded step matrices, imply a polynomial endpoint bound. No endpoint-only
height assumption is substituted for the path condition.
-/

namespace PolycyclicRecognition.PositiveTriangular

open scoped Matrix.Norms.Operator

variable {n : ℕ}

/-- The increments seen in the diagonal frame at each prefix. -/
noncomputable def framedSteps (g : positiveTriangular n) :
    List (positiveTriangular n) → List (Matrix (Fin n) (Fin n) ℝ)
  | [] => []
  | a :: l => ((frame g : Matrix (Fin n) (Fin n) ℝ) * matrix a *
      (↑(frame (g * a))⁻¹ : Matrix (Fin n) (Fin n) ℝ)) :: framedSteps (g * a) l

@[simp] theorem framedSteps_length (g : positiveTriangular n) (l : List (positiveTriangular n)) :
    (framedSteps g l).length = l.length := by
  induction l generalizing g with
  | nil => rfl
  | cons a l ih => simp [framedSteps, ih]

/-- Prefix frames cancel without any commutativity of the step matrices. -/
theorem framedSteps_prod (g : positiveTriangular n) (l : List (positiveTriangular n)) :
    (framedSteps g l).prod = (frame g : Matrix (Fin n) (Fin n) ℝ) *
      (l.map matrix).prod * (↑(frame (g * l.prod))⁻¹ : Matrix (Fin n) (Fin n) ℝ) := by
  induction l generalizing g with
  | nil => simp [framedSteps]
  | cons a l ih =>
    simp only [framedSteps, List.prod_cons, List.map_cons, ih, mul_assoc,
      Units.inv_mul_cancel_left]

/-- For the actual prefix diagonal, the normalized step has diagonal one. -/
theorem framedSteps_strict (g : positiveTriangular n) (l : List (positiveTriangular n)) :
    ∀ a ∈ framedSteps g l, StrictUpper (a - 1) := by
  induction l generalizing g with
  | nil => simp [framedSteps]
  | cons a l ih =>
    intro x hx
    rcases List.mem_cons.mp hx with hxa | hxl
    · subst x
      apply strictUpper_diagonal_gauge (matrix a) (upper a) (diagonal g) (diagonal (g * a))
      intro i
      simp only [diagonal_val]
      exact (triangular_mul_diag (matrix g) (matrix a) (upper g) (upper a) i).symm
    · exact ih (g * a) x hxl

/-- Uniform height control is required at every prefix, not only at the end. -/
theorem framedSteps_norm (g : positiveTriangular n) (l : List (positiveTriangular n))
    {H M : ℝ} (hM : 0 ≤ M) (hl : ∀ a ∈ l, ‖matrix a‖ ≤ M)
    (hpath : ∀ p q : List (positiveTriangular n), p ++ q = l →
      ‖(height (g * p.prod)).toAdd‖ ≤ H) :
    ∀ a ∈ framedSteps g l, ‖a‖ ≤ Real.exp H * M * Real.exp H := by
  induction l generalizing g with
  | nil => simp [framedSteps]
  | cons a l ih =>
    have hg : ‖(height g).toAdd‖ ≤ H := by simpa using hpath [] (a :: l) rfl
    have hga : ‖(height (g * a)).toAdd‖ ≤ H := by simpa using hpath [a] l rfl
    have ht : ∀ p q : List (positiveTriangular n), p ++ q = l →
        ‖(height ((g * a) * p.prod)).toAdd‖ ≤ H := by
      intro p q hpq
      simpa only [List.prod_cons, mul_assoc] using
        hpath (a :: p) q (by simp only [List.cons_append, hpq])
    intro x hx
    rcases List.mem_cons.mp hx with hxa | hxl
    · subst x
      exact (norm_mul_le _ _).trans
        (mul_le_mul ((norm_mul_le _ _).trans
          (mul_le_mul (frame_norm_le_exp g hg).1 (hl a (by simp)) (norm_nonneg _)
            (Real.exp_pos H).le))
          (frame_norm_le_exp (g * a) hga).2 (norm_nonneg _)
          (mul_nonneg (Real.exp_pos H).le hM))
    · exact ih (g * a) (fun a ha => hl a (by simp [ha])) ht x hxl

@[simp] theorem frame_one : frame (1 : positiveTriangular n) = 1 := by
  apply Units.ext
  ext i j
  simp [frame, diagonalUnit, Matrix.diagonal, Matrix.one_apply]

theorem matrix_prod (l : List (positiveTriangular n)) : matrix l.prod = (l.map matrix).prod := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change matrix a * matrix l.prod = matrix a * (l.map matrix).prod
    rw [ih]

variable [NeZero n]

/-- Concrete bounded-height words have polynomially bounded endpoint matrices.
The degree is fixed by the matrix dimension and is independent of the word. -/
theorem norm_word_prod_le (l : List (positiveTriangular n))
    {H M : ℝ} (hM : 0 ≤ M) (hl : ∀ a ∈ l, ‖matrix a‖ ≤ M)
    (hpath : ∀ p q : List (positiveTriangular n), p ++ q = l →
      ‖(height p.prod).toAdd‖ ≤ H) :
    ‖matrix l.prod‖ ≤ ((n : ℝ) * (1 + (Real.exp H * M * Real.exp H + 1)) ^ n *
      (1 + (l.length : ℝ)) ^ n) * Real.exp H := by
  let fs := framedSteps 1 l
  let xs := fs.map (fun a => a - 1)
  have hs : ∀ a ∈ xs, StrictUpper a := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact framedSteps_strict 1 l b hb
  have hf : ∀ a ∈ fs, ‖a‖ ≤ Real.exp H * M * Real.exp H :=
    framedSteps_norm 1 l hM hl (by simpa only [one_mul] using hpath)
  have hnorm : ∀ a ∈ xs, ‖a‖ ≤ Real.exp H * M * Real.exp H + 1 := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact (norm_sub_le _ _).trans (by simpa only [norm_one] using add_le_add (hf b hb) le_rfl)
  have hp := norm_unipotent_prod_le xs hs (by positivity : 0 ≤ Real.exp H * M * Real.exp H + 1) hnorm
  have heq : (xs.map (fun a => 1 + a)).prod = fs.prod := by
    simp [xs, List.map_map, Function.comp_def]
  rw [heq] at hp
  have hprod : matrix l.prod = fs.prod * (frame l.prod : Matrix (Fin n) (Fin n) ℝ) := by
    dsimp [fs]
    rw [framedSteps_prod, frame_one, one_mul, matrix_prod]
    simp [mul_assoc]
  rw [hprod]
  apply (norm_mul_le _ _).trans
  apply mul_le_mul _ (frame_norm_le_exp l.prod (by simpa using hpath l [] (by simp))).1
    (norm_nonneg _) _
  · simpa [xs, fs] using hp
  · positivity

/-- The word estimate also applies to a concrete triangular representation of
another group, preserving every prefix-height hypothesis. -/
theorem norm_mapped_word_prod_le {G : Type*} [Group G]
    (ρ : G →* positiveTriangular n) (l : List G)
    {H M : ℝ} (hM : 0 ≤ M) (hl : ∀ a ∈ l, ‖matrix (ρ a)‖ ≤ M)
    (hpath : ∀ p q : List G, p ++ q = l → ‖(height (ρ p.prod)).toAdd‖ ≤ H) :
    ‖matrix (ρ l.prod)‖ ≤ ((n : ℝ) * (1 + (Real.exp H * M * Real.exp H + 1)) ^ n *
      (1 + (l.length : ℝ)) ^ n) * Real.exp H := by
  have h := norm_word_prod_le (l.map ρ) hM (by
    intro a ha
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp ha
    exact hl g hg) (by
      intro p q hpq
      obtain ⟨p', q', hl', hp', _⟩ := List.append_eq_map_iff.mp hpq
      rw [← hp', ← map_list_prod]
      exact hpath p' q' hl'.symm)
  simpa only [← map_list_prod, List.length_map] using h

end PolycyclicRecognition.PositiveTriangular

end OAI
