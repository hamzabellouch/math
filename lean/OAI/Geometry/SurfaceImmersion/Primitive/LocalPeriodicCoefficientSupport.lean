import OAI.Geometry.SurfaceImmersion.Primitive.LocalPeriodicMetricCoefficients

namespace OAI

/-! Differentiating and forming metric coefficients preserves local zero support. -/

noncomputable section
open scoped BigOperators

namespace ClosedSurfaceR4.LocalPeriodicExpansion

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  {O : TopologicalSpace.Opens A}

variable {Z : Set A} (hO : IsOpen Z) (hZO : Z ⊆ O) (U : ℕ → Family O E)
  (hU : ∀ i p, p ∈ Z → (U i).val p = 0)

include hO hU hZO

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma xCoefficient_zero_on (dx : A) (i : ℕ) {p : A} (hp : p ∈ Z) :
    (xCoefficient dx U i).val p = 0 := by
  have hs := (U (i - 1)).slow_zero_on hO (hU (i - 1)) dx (hZO hp) hp
  have ha := (U i).angle_zero_at (hZO hp) (hU i p hp)
  ext t
  change ((U (i - 1)).slow dx).val p t + (U i).angle.val p t = 0
  rw [hs, ha]
  simp only [ContinuousMap.zero_apply, add_zero]

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma yCoefficient_zero_on (dy : A) (i : ℕ) {p : A} (hp : p ∈ Z) :
    (yCoefficient dy U i).val p = 0 :=
  (U (i - 1)).slow_zero_on hO (hU (i - 1)) dy (hZO hp) hp

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma xxQuadratic_zero_on (dx : A) (r : ℕ) {p : A} (hp : p ∈ Z) :
    (xxQuadratic dx U r).val p = 0 := by
  ext t
  simp only [xxQuadratic, Family.sum_apply, Family.inner_apply]
  apply Finset.sum_eq_zero
  intro i hi
  rw [xCoefficient_zero_on hO hZO U hU dx i hp]
  exact inner_zero_left _

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma xyQuadratic_zero_on (dx dy : A) (r : ℕ) {p : A} (hp : p ∈ Z) :
    (xyQuadratic dx dy U r).val p = 0 := by
  ext t
  simp only [xyQuadratic, Family.sum_apply, Family.inner_apply]
  apply Finset.sum_eq_zero
  intro i hi
  rw [xCoefficient_zero_on hO hZO U hU dx i hp]
  exact inner_zero_left _

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma yyQuadratic_zero_on (dy : A) (r : ℕ) {p : A} (hp : p ∈ Z) :
    (yyQuadratic dy U r).val p = 0 := by
  ext t
  simp only [yyQuadratic, Family.sum_apply, Family.inner_apply]
  apply Finset.sum_eq_zero
  intro i hi
  rw [yCoefficient_zero_on hO hZO U hU dy i hp]
  exact inner_zero_left _

end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
