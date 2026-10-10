import OAI.Analysis.MetricEntropy.SupportPolar
import OAI.Analysis.MetricEntropy.CoveringNumber
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Linarith

namespace OAI

universe uX uY

/-!
# Polar covers from arbitrary uniform approximation lists

The functions on the approximation list need not be column combinations.
For every nonempty coefficient fiber we choose an actual vector in the
coefficient ball; empty fibers receive zero. The resulting list has exactly
the original number of slots, with no factor depending on the dimension.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped BigOperators Pointwise

variable {X : Type uX} {Y : Type uY} [Fintype Y]

/-- An actual coefficient vector in the fiber of a list function, or zero
when this fiber is empty. No inverse of the column-combination map is used. -/
def coefficientRepresentative (g : Y → X → ℝ) (ε : ℝ) (f : RealSpace X) :
    RealSpace Y := by
  classical
  exact if h : ∃ lam ∈ l1Ball Y, UniformClose ε (columnCombination g lam) f then
    Classical.choose h else 0

theorem coefficientRepresentative_mem (g : Y → X → ℝ) (ε : ℝ) (f : RealSpace X) :
    coefficientRepresentative g ε f ∈ l1Ball Y := by
  classical
  by_cases h : ∃ lam ∈ l1Ball Y, UniformClose ε (columnCombination g lam) f
  · simpa only [coefficientRepresentative, dite_eq_left h] using (Classical.choose_spec h).1
  · simpa only [coefficientRepresentative, dite_eq_right h] using
      (zero_mem_l1Ball : (0 : RealSpace Y) ∈ l1Ball Y)

theorem coefficientRepresentative_close (g : Y → X → ℝ) (ε : ℝ) (f : RealSpace X)
    (h : ∃ lam ∈ l1Ball Y, UniformClose ε (columnCombination g lam) f) :
    UniformClose ε (columnCombination g (coefficientRepresentative g ε f)) f := by
  classical
  simpa only [coefficientRepresentative, dite_eq_left h] using (Classical.choose_spec h).2

/-- Two functions within the same error of one arbitrary center are within
twice that error of each other. -/
theorem UniformClose.of_same_center {ε : ℝ} {f h r : RealSpace X}
    (hf : UniformClose ε f h) (hr : UniformClose ε r h) :
    UniformClose (2 * ε) f r := by
  intro x
  have htriangle := abs_sub_le (f x) (h x) (r x)
  have hfx := hf x
  have hrx := hr.symm x
  linarith

/-- The approximation hypothesis itself rules out an empty list, since
the coefficient ball always contains zero. -/
theorem UniformApproximation.nonempty {g : Y → X → ℝ} {ε : ℝ}
    {A : Finset (RealSpace X)} (hA : UniformApproximation g ε A) : A.Nonempty := by
  obtain ⟨f, hf, _⟩ := hA 0 zero_mem_l1Ball
  exact ⟨f, hf⟩

/-- Choose one actual coefficient-ball representative for each original
list slot. Every coefficient vector is close to one such representative
both after the column map and in the coefficient ℓ¹ norm. -/
theorem exists_coefficient_representatives (g : Y → X → ℝ) (ε : ℝ)
    (A : Finset (RealSpace X)) (hA : UniformApproximation g ε A) :
    ∃ centers : Fin A.card → RealSpace Y,
      (∀ j, centers j ∈ l1Ball Y) ∧
      ∀ lam ∈ l1Ball Y, ∃ j,
        UniformClose (2 * ε) (columnCombination g lam) (columnCombination g (centers j)) ∧
        l1Norm (lam - centers j) ≤ 2 := by
  classical
  let centers : Fin A.card → RealSpace Y := fun j =>
    coefficientRepresentative g ε ((A.equivFin).symm j).val
  refine ⟨centers, ?_, ?_⟩
  · intro j
    exact coefficientRepresentative_mem g ε _
  · intro lam hLam
    obtain ⟨f, hf, hclose⟩ := hA lam hLam
    let j : Fin A.card := A.equivFin ⟨f, hf⟩
    have hj : centers j = coefficientRepresentative g ε f := by
      simp [centers, j]
    have hrep := coefficientRepresentative_close g ε f ⟨lam, hLam, hclose⟩
    have hrepMem := coefficientRepresentative_mem g ε f
    refine ⟨j, ?_, ?_⟩
    · rw [hj]
      exact hclose.of_same_center hrep
    · rw [hj]
      have hLamNorm : l1Norm lam ≤ 1 := hLam
      have hrepNorm : l1Norm (coefficientRepresentative g ε f) ≤ 1 := hrepMem
      have hsub := l1Norm_sub_le lam (coefficientRepresentative g ε f)
      linarith

/-- The selected coefficient vectors give an actual ambient translate cover
of the whole coefficient ball at the specified polar scale. -/
theorem exists_l1Ball_polar_cover (g : Y → X → ℝ) {ε t : ℝ}
    (hε : 0 ≤ ε) (ht : 0 < t) (A : Finset (RealSpace X))
    (hA : UniformApproximation g ε A) :
    ∃ centers : Fin A.card → RealSpace Y,
      (∀ j, centers j ∈ l1Ball Y) ∧
      Covers (l1Ball Y) ((6 * ε + 2 * t) • polar (matrixBody g t)) centers := by
  obtain ⟨centers, hmem, hrep⟩ := exists_coefficient_representatives g ε A hA
  refine ⟨centers, hmem, ?_⟩
  intro lam hLam
  obtain ⟨j, hclose, hnorm⟩ := hrep lam hLam
  refine ⟨j, mem_smul_polar_matrixBody_of_bounds g (lam - centers j)
    ht.le (by linarith) (M := 2 * ε) (L := 2) ?_ hnorm (by linarith)⟩
  intro x
  simpa only [pairing_row_eq_columnCombination, columnCombination_sub, Pi.sub_apply] using
    hclose x

/-- The same explicit finite list covers the literal polar of the cube. -/
theorem exists_cube_polar_cover (g : Y → X → ℝ) {ε t : ℝ}
    (hε : 0 ≤ ε) (ht : 0 < t) (A : Finset (RealSpace X))
    (hA : UniformApproximation g ε A) :
    ∃ centers : Fin A.card → RealSpace Y,
      (∀ j, centers j ∈ l1Ball Y) ∧
      Covers (polar (cube Y)) ((6 * ε + 2 * t) • polar (matrixBody g t)) centers := by
  simpa only [polar_cube] using exists_l1Ball_polar_cover g hε ht A hA

/-- Finiteness is supplied by an actual list, independently of the convention
used for an empty natural infimum in the covering-number definition. -/
theorem cube_polar_coverable (g : Y → X → ℝ) {ε t : ℝ}
    (hε : 0 ≤ ε) (ht : 0 < t) (A : Finset (RealSpace X))
    (hA : UniformApproximation g ε A) :
    Coverable (polar (cube Y)) ((6 * ε + 2 * t) • polar (matrixBody g t)) := by
  obtain ⟨centers, _, hcover⟩ := exists_cube_polar_cover g hε ht A hA
  exact ⟨A.card, centers, hcover⟩

/-- The least number of arbitrary ambient translates is bounded by the
original approximation-list cardinal, without a dimension or center factor. -/
theorem polar_coveringNumber_le (g : Y → X → ℝ) {ε t : ℝ}
    (hε : 0 ≤ ε) (ht : 0 < t) (A : Finset (RealSpace X))
    (hA : UniformApproximation g ε A) :
    coveringNumber (polar (cube Y)) ((6 * ε + 2 * t) • polar (matrixBody g t)) ≤ A.card := by
  obtain ⟨centers, _, hcover⟩ := exists_cube_polar_cover g hε ht A hA
  exact coveringNumber_le_of_covers hcover

end MetricEntropyDuality

end

end OAI
