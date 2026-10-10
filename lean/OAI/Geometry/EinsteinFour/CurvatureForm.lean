import OAI.Geometry.EinsteinFour.FrameCurvature
import Mathlib.LinearAlgebra.Multilinear.Basic

namespace OAI

/-! The actual coordinate curvature is a four-linear form. This supplies
the multilinearity used to change normal frames without an independent
curvature-transformation assumption. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

private def fourIndicesEquiv : (Fin 4 → Fin 4) ≃ Fin 4 × (Fin 4 × (Fin 4 × Fin 4)) where
  toFun a := (a 0, a 1, a 2, a 3)
  invFun a := ![a.1, a.2.1, a.2.2.1, a.2.2.2]
  left_inv a := by funext i; fin_cases i <;> rfl
  right_inv := by rintro ⟨a, b, c, d⟩; rfl

private theorem sum_four_indices (F : (Fin 4 → Fin 4) → ℝ) :
    (∑ a, F a) = ∑ a, ∑ b, ∑ c, ∑ d, F ![a, b, c, d] := by
  calc
    _ = ∑ a : Fin 4 × (Fin 4 × (Fin 4 × Fin 4)), F (fourIndicesEquiv.symm a) :=
      (fourIndicesEquiv.symm.sum_comp F).symm
    _ = _ := by simp only [Fintype.sum_prod_type]; rfl

theorem multilinear_combinations
    (f : MultilinearMap ℝ (fun _ : Fin 4 => FourSpace) ℝ)
    (A : Mat4) (e : Fin 4 → FourSpace) (v : Fin 4 → Fin 4) :
    f (fun s => ∑ a, A a (v s) • e a) =
      ∑ a, ∑ b, ∑ c, ∑ d,
        (A a (v 0) * A b (v 1) * A c (v 2) * A d (v 3)) *
          f ![e a, e b, e c, e d] := by
  rw [f.map_sum]
  simp_rw [f.map_smul_univ, smul_eq_mul]
  rw [sum_four_indices]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  congr 1
  funext a
  congr 1
  funext b
  congr 1
  funext c
  congr 1
  funext d
  congr 1
  · change A a (v 0) * (A b (v 1) * (A c (v 2) * A d (v 3))) = _
    ring
  · congr 1
    funext i
    fin_cases i <;> rfl

def curvatureForm (g : SmoothMetric M) (c : M) :
    MultilinearMap ℝ (fun _ : Fin 4 => FourSpace) ℝ :=
  MultilinearMap.mk'
    (fun v => ∑ a, ∑ b, ∑ p, ∑ q, ∑ r,
      chartMetric g c a b * curvatureComponent g c (chartAt FourSpace c c) a p q r *
        v 0 p * v 1 q * v 2 r * v 3 b)
    (by
      intro v i x y
      fin_cases i <;>
        simp [Function.update, add_mul, mul_add, Finset.sum_add_distrib])
    (by
      intro v i k x
      fin_cases i <;> simp [Function.update, Finset.mul_sum]
      all_goals
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro p _
        apply Finset.sum_congr rfl
        intro q _
        apply Finset.sum_congr rfl
        intro r _
        ring)

theorem frameCurvature_eq_form (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) (i j k l : Fin 4) :
    frameCurvature g c e i j k l =
      curvatureForm g c ![e.vector i, e.vector j, e.vector k, e.vector l] := rfl

theorem OrthonormalFrame.turn_vector {g : SmoothMetric M} {c : M}
    (e : OrthonormalFrame g c) (q : Angular.Directions) (j : Fin 4) :
    (e.turn q).vector j = ∑ a, directionFrameMatrix q a j • e.vector a := by
  ext i
  simp [OrthonormalFrame.vector, OrthonormalFrame.turn, Matrix.mul_apply, mul_comm]

theorem frameCurvature_turn (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) (q : Angular.Directions) (i j k l : Fin 4) :
    frameCurvature g c (e.turn q) i j k l =
      ∑ a, ∑ b, ∑ p, ∑ r,
        (directionFrameMatrix q a i * directionFrameMatrix q b j *
          directionFrameMatrix q p k * directionFrameMatrix q r l) *
            frameCurvature g c e a b p r := by
  have h := multilinear_combinations (curvatureForm g c)
    (directionFrameMatrix q) e.vector ![i, j, k, l]
  have he : (fun s : Fin 4 => ∑ a, directionFrameMatrix q a (![i, j, k, l] s) •
      e.vector a) = ![(e.turn q).vector i, (e.turn q).vector j,
        (e.turn q).vector k, (e.turn q).vector l] := by
    funext s
    fin_cases s <;> simp [OrthonormalFrame.turn_vector]
  rw [he] at h
  simpa [← frameCurvature_eq_form] using h

theorem frameCurvatureField_turn (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) (q : Angular.Directions) :
    frameCurvatureField g (frameTurn e q) = normalCurvatureDeviation g c e q := by
  ext i j
  rw [frameCurvatureField_apply]
  change frameCurvature g c (e.turn q) i.succ 0 0 j.succ -
    (if i = j then 1 else 0) = _
  rw [frameCurvature_turn]
  simp only [directionFrameMatrix_zero, directionFrameMatrix_succ]
  change (∑ a, ∑ b, ∑ p, ∑ r,
    (Angular.normalVector q i a * q.val b * q.val p * Angular.normalVector q j r) *
      frameCurvature g c e a b p r) - (if i = j then 1 else 0) =
    (∑ a, ∑ b, ∑ p, ∑ r, frameCurvature g c e a b p r *
      Angular.normalVector q i a * q.val b * q.val p * Angular.normalVector q j r) -
        (if i = j then 1 else 0)
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro r _
  ring

end

end PositiveEinsteinFour.Geometry

end OAI
