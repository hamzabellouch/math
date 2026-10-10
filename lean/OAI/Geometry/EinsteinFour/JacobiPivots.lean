import OAI.Geometry.EinsteinFour.DirichletFactorization

namespace OAI

/-! The finite Dirichlet determinant is the determinant of the discrete
Jacobi solution, on the nonsingular range used before conjugacy. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix

noncomputable section

def jacobiPivot (D : ℕ → NormalMatrix) : ℕ → NormalMatrix
  | 0 => D 0
  | n + 1 => D (n + 1) - (jacobiPivot D n)⁻¹

theorem jacobiPivot_symmetric (D : ℕ → NormalMatrix)
    (hD : ∀ i, (D i).transpose = D i) (i : ℕ) :
    (jacobiPivot D i).transpose = jacobiPivot D i := by
  induction i with
  | zero => exact hD 0
  | succ i hi => simp only [jacobiPivot, Matrix.transpose_sub,
      Matrix.transpose_nonsing_inv, hD, hi]

theorem jacobiPivot_eq_ratio (D Y : ℕ → NormalMatrix)
    (h0 : Y 0 = 0) (h1 : Y 1 = 1)
    (hrec : ∀ i, Y (i + 2) = D i * Y (i + 1) - Y i)
    (n : ℕ) (hunit : ∀ i, 1 ≤ i → i ≤ n + 1 → IsUnit (Y i).det) :
    jacobiPivot D n = Y (n + 2) * (Y (n + 1))⁻¹ := by
  induction n with
  | zero => simp [jacobiPivot, hrec 0, h0, h1]
  | succ n ih =>
      have hn := ih (fun i hi hin => hunit i hi (by omega))
      rw [jacobiPivot, hn]
      exact (jacobi_pivot_recurrence (hunit (n + 1) (by omega) (by omega))
        (hunit (n + 2) (by omega) (by omega)) (hrec (n + 1))).symm

private theorem predecessor_sum_zero {N : ℕ} (S : Fin N → NormalMatrix) :
    (∑ k, if k.val + 1 = 0 then (S k)⁻¹ else 0) = 0 := by simp

private theorem predecessor_sum_succ {N m : ℕ} (hm : m + 1 < N)
    (S : Fin N → NormalMatrix) :
    (∑ k, if k.val + 1 = m + 1 then (S k)⁻¹ else 0) =
      (S ⟨m, by omega⟩)⁻¹ := by
  let p : Fin N := ⟨m, by omega⟩
  rw [Finset.sum_eq_single p]
  · simp [p]
  · intro k _ hkp
    have hne : k.val ≠ m := by
      intro heq
      apply hkp
      apply Fin.ext
      dsimp [p]
      omega
    simp [hne]
  · simp

theorem pivotDiagonal_jacobiPivot (D : ℕ → NormalMatrix) {N : ℕ} (i : Fin N) :
    pivotDiagonal (fun k : Fin N => jacobiPivot D k.val) i = D i.val := by
  rcases i with ⟨m, hm⟩
  cases m with
  | zero => simp [pivotDiagonal, jacobiPivot]
  | succ m =>
      change jacobiPivot D (m + 1) +
        (∑ k : Fin N, if k.val + 1 = m + 1 then (jacobiPivot D k.val)⁻¹ else 0) = D (m + 1)
      rw [predecessor_sum_succ hm, jacobiPivot]
      exact sub_add_cancel _ _

/-- The determinant identity required for the preconjugate comparison.
The hypotheses on `Y` are its recurrence and nonsingularity. -/
theorem dirichlet_determinant_eq_jacobi (D Y : ℕ → NormalMatrix) (N : ℕ)
    (hD : ∀ i, (D i).transpose = D i)
    (h0 : Y 0 = 0) (h1 : Y 1 = 1)
    (hrec : ∀ i, Y (i + 2) = D i * Y (i + 1) - Y i)
    (hunit : ∀ i, 1 ≤ i → i ≤ N + 1 → IsUnit (Y i).det) :
    (dirichletMatrix (fun i : Fin N => D i.val)).det = (Y (N + 1)).det := by
  let S : Fin N → NormalMatrix := fun i => jacobiPivot D i.val
  have hratio (i : Fin N) : S i = Y (i.val + 2) * (Y (i.val + 1))⁻¹ :=
    jacobiPivot_eq_ratio D Y h0 h1 hrec i.val (fun k hk hki => hunit k hk (by omega))
  have hSunit (i : Fin N) : IsUnit (S i).det := by
    apply isUnit_iff_ne_zero.mpr
    rw [hratio, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    exact mul_ne_zero (hunit (i.val + 2) (by omega) (by omega)).ne_zero
      (inv_ne_zero (hunit (i.val + 1) (by omega) (by omega)).ne_zero)
  have hSsym (i : Fin N) : (S i).transpose = S i := jacobiPivot_symmetric D hD i.val
  have hdiag : (fun i : Fin N => D i.val) = pivotDiagonal S := by
    funext i
    exact (pivotDiagonal_jacobiPivot D i).symm
  rw [hdiag, det_dirichlet_pivots S hSunit hSsym]
  have hp := determinant_pivot_product (fun i => Y (i + 1)) N
    (fun i hi => (hunit (i + 1) (by omega) (by omega)).ne_zero)
  rw [← Fin.prod_univ_eq_prod_range] at hp
  calc
    (∏ i : Fin N, (S i).det) =
        ∏ i : Fin N, (Y (i.val + 2) * (Y (i.val + 1))⁻¹).det := by
      apply Finset.prod_congr rfl
      intro i _
      rw [hratio]
    _ = (Y (N + 1)).det := by
      simpa only [Nat.add_assoc, h1, Matrix.det_one, div_one] using hp

end

end PositiveEinsteinFour.Jacobi

end OAI
