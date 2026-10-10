import OAI.Geometry.ProjectionBody.GraphChart
import OAI.Geometry.ProjectionBody.SimplexFacets

namespace OAI

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace ProjectionCounterexample

def allOnes (n : ℕ) : E n := WithLp.toLp 2 (fun _ => 1)

@[simp] theorem allOnes_apply {n : ℕ} (i : Fin n) : allOnes n i = 1 := rfl

@[simp] theorem inner_allOnes {n : ℕ} (x : E n) : ⟪allOnes n, x⟫ = ∑ i, x i := by
  simp [PiLp.inner_apply, allOnes]

/-- Linear part of each simplex facet chart. -/
def simplexFacetLinear (n : ℕ) : Option (Fin (n + 1)) → E n →ₗ[ℝ] E (n + 1)
  | none => graphLinear (Fin.last n) (allOnes n)
  | some i => (insertZero i).toLinearMap

def simplexFacetCenter (n : ℕ) : Option (Fin (n + 1)) → E (n + 1)
  | none => EuclideanSpace.single (Fin.last n) 1
  | some _ => 0

theorem simplexFacetChart_none (n : ℕ) (x : E n) :
    simplexFacetCenter n none + simplexFacetLinear n none x = sumFacetMap n x := by
  ext j
  induction j using Fin.lastCases
  · simp [simplexFacetCenter, simplexFacetLinear, graphLinear, sub_eq_add_neg]
  · simp [simplexFacetCenter, simplexFacetLinear, graphLinear, insertZero,
      Fin.insertNth_last']

theorem simplex_facet_eq_affine_image (n : ℕ) (i : Option (Fin (n + 1))) :
    boundingFace (simplexFunctional (n + 1)) simplexLevel i =
      (fun x => simplexFacetCenter n i + simplexFacetLinear n i x) '' simplex n := by
  cases i with
  | none =>
    simp_rw [simplex_boundingFace_sum, simplexFacetChart_none]
    exact sum_facet_eq_image n
  | some i =>
    rw [simplex_boundingFace_coordinate, coordinate_facet_eq_image]
    simp [simplexFacetCenter, simplexFacetLinear]

/-- Every defining hyperplane other than the chart's own hyperplane is transverse.
The positive dimension excludes the degenerate segment-endpoint case. -/
theorem simplex_facet_transverse {n : ℕ} (hn : 0 < n)
    (i j : Option (Fin (n + 1))) (hij : i ≠ j) :
    (simplexFunctional (n + 1) j).comp (simplexFacetLinear n i) ≠ 0 := by
  intro heq
  let k : Fin n := ⟨0, hn⟩
  cases i with
  | none =>
    cases j with
    | none => exact hij rfl
    | some j =>
      induction j using Fin.lastCases with
      | last =>
        have h := LinearMap.congr_fun heq (EuclideanSpace.single k 1)
        simp [simplexFacetLinear, graphLinear] at h
      | cast j =>
        have h := LinearMap.congr_fun heq (EuclideanSpace.single j 1)
        simp [simplexFacetLinear, graphLinear, insertZero, Fin.insertNth_last'] at h
  | some i =>
    cases j with
    | none =>
      have h := LinearMap.congr_fun heq (EuclideanSpace.single k 1)
      simp [simplexFacetLinear, sum_insertZero] at h
    | some j =>
      have hji : j ≠ i := fun h => hij (congrArg some h.symm)
      obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
      have h := LinearMap.congr_fun heq (EuclideanSpace.single k 1)
      simp [simplexFacetLinear] at h

end ProjectionCounterexample

end

end OAI
