import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace OAI

noncomputable section
open scoped BigOperators

namespace DiagonalZonotope
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]

/-- Replacing one identity column by the all-ones vector leaves determinant one. -/
theorem det_identity_updateCol_ones (i : ι) :
    ((1 : Matrix ι ι R).updateCol i (fun _ => 1)).det = 1 := by
  have h := Matrix.det_updateCol_sum (1 : Matrix ι ι R) i (fun _ => (1 : R))
  have hc : (fun k : ι => ∑ j : ι, (1 : R) • (1 : Matrix ι ι R) k j) =
      (fun _ : ι => (1 : R)) := by
    funext k
    simp [Matrix.one_apply]
  rw [hc] at h
  simpa using h

end DiagonalZonotope

end

end OAI
