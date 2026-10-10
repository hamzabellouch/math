import Mathlib

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section SymmetricCoordinates
variable {ν : Type*} [Fintype ν] [LinearOrder ν]

abbrev UpperTriangle (ν : Type*) [LE ν] := {p : ν × ν // p.1 ≤ p.2}

noncomputable def symmetricCoordinates :
    EuclideanSpace ℝ (UpperTriangle ν) →ₗ[ℝ] Matrix ν ν ℝ where
  toFun x i j := if h : i ≤ j then x ⟨(i,j),h⟩ else x ⟨(j,i),le_of_not_ge h⟩
  map_add' x y := by
    ext i j
    change (if h : i ≤ j then (x+y) ⟨(i,j),h⟩ else (x+y) ⟨(j,i),le_of_not_ge h⟩) =
      (if h : i ≤ j then x ⟨(i,j),h⟩ else x ⟨(j,i),le_of_not_ge h⟩) +
      (if h : i ≤ j then y ⟨(i,j),h⟩ else y ⟨(j,i),le_of_not_ge h⟩)
    split_ifs <;> rfl
  map_smul' t x := by
    ext i j
    change (if h : i ≤ j then (t • x) ⟨(i,j),h⟩ else (t • x) ⟨(j,i),le_of_not_ge h⟩) =
      t * (if h : i ≤ j then x ⟨(i,j),h⟩ else x ⟨(j,i),le_of_not_ge h⟩)
    split_ifs <;> rfl

omit [Fintype ν] in
lemma symmetricCoordinates_upper (x : EuclideanSpace ℝ (UpperTriangle ν))
    (i j : ν) (hij : i ≤ j) : symmetricCoordinates x i j = x ⟨(i,j), hij⟩ := by
  change (if h : i ≤ j then x ⟨(i,j),h⟩ else x ⟨(j,i),le_of_not_ge h⟩) = _
  exact dite_eq_left hij

omit [Fintype ν] in
lemma symmetricCoordinates_selfAdjoint (x : EuclideanSpace ℝ (UpperTriangle ν)) :
    IsSelfAdjoint (symmetricCoordinates x) := by
  change (symmetricCoordinates x)ᴴ = symmetricCoordinates x
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial]
  change (if h : j ≤ i then x ⟨(j,i),h⟩ else x ⟨(i,j),le_of_not_ge h⟩) =
    (if h : i ≤ j then x ⟨(i,j),h⟩ else x ⟨(j,i),le_of_not_ge h⟩)
  by_cases hij : i ≤ j
  · by_cases hji : j ≤ i
    · have he := le_antisymm hij hji
      subst j
      rfl
    · simp [hij, hji]
  · have hji : j ≤ i := le_of_not_ge hij
    simp [hij, hji]

omit [Fintype ν] in
lemma symmetricCoordinates_injective : Function.Injective (symmetricCoordinates (ν := ν)) := by
  intro x y hxy
  apply PiLp.ext
  intro p
  have h := congrArg (fun A : Matrix ν ν ℝ => A p.val.1 p.val.2) hxy
  simpa only [symmetricCoordinates_upper _ _ _ p.property] using h

lemma upperTriangle_four_card : Fintype.card (UpperTriangle (Fin 4)) = 10 := by decide

end SymmetricCoordinates

end BorsukNine

end OAI
