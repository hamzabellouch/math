import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import OAI.NumberTheory.Catalan.Analysis.RealPairedIntegral

namespace OAI

noncomputable section

open scoped BigOperators

namespace InternalCatalan

private theorem det_succ_schur {m : ℕ}
    (M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (h00 : M 0 0 ≠ 0) :
    M.det = M 0 0 *
      Matrix.det (Matrix.of (fun i j : Fin m =>
        M i.succ j.succ - M i.succ 0 * M 0 j.succ / M 0 0)) := by
  classical
  let c : Fin (m + 1) → ℝ := fun i => if i = 0 then 0 else -(M i 0 / M 0 0)
  let E : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
    Matrix.of (fun i j => M i j + c i * M 0 j)
  have hdet : E.det = M.det :=
    Matrix.det_eq_of_forall_row_eq_smul_add_const c 0
      (by simp only [c, ite_eq_left rfl]) (fun _ _ => rfl)
  have hE00 : E 0 0 = M 0 0 := by simp [E, c]
  have hEi0 (i : Fin (m + 1)) (hi : i ≠ 0) : E i 0 = 0 := by
    simp only [E, Matrix.of_apply, c, ite_eq_right hi]
    field_simp [h00]
    ring
  have htail : E.submatrix Fin.succ Fin.succ =
      Matrix.of (fun i j : Fin m =>
        M i.succ j.succ - M i.succ 0 * M 0 j.succ / M 0 0) := by
    ext i j
    simp only [Matrix.submatrix_apply, E, Matrix.of_apply, c,
      Fin.succ_ne_zero, ite_false]
    ring
  calc
    M.det = E.det := hdet.symm
    _ = _ := by
      rw [Matrix.det_succ_column_zero, Finset.sum_eq_single 0]
      · rw [Fin.val_zero, pow_zero, one_mul, hE00, Fin.succAbove_zero, htail]
      · intro i _ hi
        rw [hEi0 i hi, mul_zero, zero_mul]
      · simp

theorem cauchy_schur_entry (t0 ti s0 sj : ℝ)
    (h00 : 1 - t0 * s0 ≠ 0) (hi0 : 1 - ti * s0 ≠ 0)
    (h0j : 1 - t0 * sj ≠ 0) (hij : 1 - ti * sj ≠ 0) :
    (1 : ℝ) / (1 - ti * sj) -
        ((1 / (1 - ti * s0)) * (1 / (1 - t0 * sj))) / (1 / (1 - t0 * s0)) =
      ((ti - t0) / (1 - ti * s0)) *
        (((sj - s0) / (1 - t0 * sj)) * (1 / (1 - ti * sj))) := by
  have hi0' : 1 - s0 * ti ≠ 0 := by simpa only [mul_comm] using hi0
  have h0j' : 1 - sj * t0 ≠ 0 := by simpa only [mul_comm] using h0j
  apply mul_left_cancel₀ h00
  field_simp [hi0, hi0', h0j, h0j', hij]
  ring

theorem cauchy_det_succ {m : ℕ} (t s : Fin (m + 1) → ℝ)
    (hden : ∀ i j, 1 - t i * s j ≠ 0) :
    Matrix.det (Matrix.of (fun i j : Fin (m + 1) => (1 : ℝ) / (1 - t i * s j))) =
      (1 / (1 - t 0 * s 0)) *
        (∏ i : Fin m, (t i.succ - t 0) / (1 - t i.succ * s 0)) *
        (∏ j : Fin m, (s j.succ - s 0) / (1 - t 0 * s j.succ)) *
        Matrix.det (Matrix.of (fun i j : Fin m => (1 : ℝ) / (1 - t i.succ * s j.succ))) := by
  classical
  let C : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
    Matrix.of (fun i j => (1 : ℝ) / (1 - t i * s j))
  let T : Matrix (Fin m) (Fin m) ℝ :=
    Matrix.of (fun i j => (1 : ℝ) / (1 - t i.succ * s j.succ))
  let rowFactor : Fin m → ℝ := fun i => (t i.succ - t 0) / (1 - t i.succ * s 0)
  let colFactor : Fin m → ℝ := fun j => (s j.succ - s 0) / (1 - t 0 * s j.succ)
  let B : Matrix (Fin m) (Fin m) ℝ := Matrix.of (fun i j => colFactor j * T i j)
  have hpivot : C 0 0 ≠ 0 := div_ne_zero one_ne_zero (hden 0 0)
  have htail :
      Matrix.of (fun i j : Fin m =>
        C i.succ j.succ - C i.succ 0 * C 0 j.succ / C 0 0) =
      Matrix.of (fun i j : Fin m => rowFactor i * B i j) := by
    ext i j
    simp only [C, T, B, rowFactor, colFactor, Matrix.of_apply]
    exact cauchy_schur_entry (t 0) (t i.succ) (s 0) (s j.succ)
      (hden 0 0) (hden i.succ 0) (hden 0 j.succ) (hden i.succ j.succ)
  have hB : B.det = (∏ j : Fin m, colFactor j) * T.det :=
    Matrix.det_mul_row colFactor T
  change C.det = C 0 0 * (∏ i : Fin m, rowFactor i) *
    (∏ j : Fin m, colFactor j) * T.det
  rw [det_succ_schur C hpivot, htail, Matrix.det_mul_column, hB]
  ring

end InternalCatalan

end

end OAI
