import OAI.Combinatorics.EuclideanRamsey.TensorDescent
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace OAI

/-! Nonsingular tensor evaluation matrices obstruct the Euclidean Ramsey property. -/

noncomputable section
open scoped TensorProduct BigOperators

namespace EuclideanRamsey.NineLinearObstruction

theorem vector_eq_zero_of_det_ne_zero {J K : Type*} [Fintype J]
    [DecidableEq J] [Field K] (M : Matrix J J K) (hM : M.det ≠ 0)
    (v : J → K) (hv : M.mulVec v = 0) : v = 0 := by
  have hu : IsUnit M := M.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hM)
  apply (Matrix.mulVec_injective_iff_isUnit.mpr hu)
  simpa using hv

abbrev Column (d : ℕ) := Option (Fin d) × Option (Fin d)

/-- Rows are reindexed by an actual equivalence; entries are the exact
images of the two augmented-coordinate tensor factors in FieldCriterion. -/
def evaluationMatrix {s d : ℕ} (a : Fin s → Space d)
    {K : Type*} [Field K] [Algebra ℚ K]
    (f : TensorRing a →ₐ[ℚ] K) (e : Column d ≃ Fin s) :
    Matrix (Column d) (Column d) K := fun i q =>
  f ((augmented a (e i) q.1) ⊗ₜ[ℚ] (1 : Coeff a)) *
    f ((1 : Coeff a) ⊗ₜ[ℚ] (augmented a (e i) q.2))

theorem not_fieldCriterion_of_det_ne_zero {s d : ℕ} (a : Fin s → Space d)
    (hd : 0 < d) {K : Type*} [Field K] [Algebra ℚ K]
    (f : TensorRing a →ₐ[ℚ] K) (hf : Function.Injective f)
    (e : Column d ≃ Fin s) (hdet : (evaluationMatrix a f e).det ≠ 0) :
    ¬ FieldCriterion a := by
  classical
  rintro ⟨P, hP, hspatial⟩
  let v : Column d → K := fun q => f (P q.1 q.2)
  have hv : (evaluationMatrix a f e).mulVec v = 0 := by
    funext i
    have h := congrArg f (hP (e i))
    simp only [map_sum, map_mul, map_zero] at h
    change (∑ q : Column d, evaluationMatrix a f e i q * v q) = 0
    rw [Fintype.sum_prod_type]
    convert h using 1
    apply Finset.sum_congr rfl
    intro α hα
    apply Finset.sum_congr rfl
    intro β hβ
    dsimp [evaluationMatrix, v]
    ring
  have hvzero := vector_eq_zero_of_det_ne_zero (evaluationMatrix a f e) hdet v hv
  have hPzero (α β : Option (Fin d)) : P α β = 0 := by
    apply hf
    have h := congrFun hvzero (α, β)
    simpa only [v, Pi.zero_apply, map_zero] using h
  let j : Fin d := ⟨0, hd⟩
  have hbad := hspatial j j
  rw [hPzero, map_zero, ite_eq_left rfl] at hbad
  exact zero_ne_one hbad

/-- Ramsey configurations cannot have a nonsingular tensor evaluation matrix. -/
theorem not_ramsey_of_det_ne_zero {s d : ℕ} (a : Fin s → Space d)
    (hs : 0 < s) (hd : 0 < d)
    (hspan : affineSpan ℝ (Set.range a) = ⊤)
    {K : Type*} [Field K] [Algebra ℚ K]
    (f : TensorRing a →ₐ[ℚ] K) (hf : Function.Injective f)
    (e : Column d ≃ Fin s) (hdet : (evaluationMatrix a f e).det ≠ 0) :
    ¬ Ramsey a := by
  intro hR
  exact not_fieldCriterion_of_det_ne_zero a hd f hf e hdet
    (ramsey_fieldCriterion a hs hspan hR)

end EuclideanRamsey.NineLinearObstruction

end

end OAI
