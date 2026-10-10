import OAI.Geometry.EinsteinFour.JacobiSchemeRatios
import OAI.Geometry.EinsteinFour.MatrixRatioPositivity

namespace OAI

/-! Positive Jacobi pivot ratios give the actual finite curvature matrix. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix

noncomputable section

/-- The positive ratios are the ordered Schur pivots of the concrete
curvature Dirichlet matrix. No commutation between time samples is used. -/
theorem curvatureDirichlet_posDef_of_ratios {N : ℕ} {t : ℝ} (ht : t ≠ 0)
    (R : ℕ → NormalMatrix)
    (hunit : ∀ i, 1 ≤ i → i ≤ N + 1 →
      IsUnit (normalizedDiscrete R (t / (N + 1)) i).det)
    (hpos : ∀ i, 1 ≤ i → i ≤ N →
      (normalizedDiscrete R (t / (N + 1)) (i + 1) *
        (normalizedDiscrete R (t / (N + 1)) i)⁻¹).PosDef) :
    (curvatureDirichlet t (fun i : Fin N => R (i.val + 1) - 1)).PosDef := by
  let h : ℝ := t / (N + 1)
  let D : ℕ → NormalMatrix := fun i => (2 : ℝ) • 1 - h ^ 2 • R (i + 1)
  let Y : ℕ → NormalMatrix := normalizedDiscrete R h
  let S : Fin N → NormalMatrix := fun i => jacobiPivot D i.val
  have hh : h ≠ 0 := div_ne_zero ht (by positivity)
  have hY0 : Y 0 = 0 := normalizedDiscrete_zero R h
  have hY1 : Y 1 = 1 := normalizedDiscrete_one R hh
  have hrec : ∀ i, Y (i + 2) = D i * Y (i + 1) - Y i :=
    normalizedDiscrete_recurrence R h
  have hp (i : Fin N) : (S i).PosDef := by
    have hr : S i = Y (i.val + 2) * (Y (i.val + 1))⁻¹ :=
      jacobiPivot_eq_ratio D Y hY0 hY1 hrec i.val
        (fun k hk hki => hunit k hk (by omega))
    rw [hr]
    exact hpos (i.val + 1) (by omega) (by omega)
  have hdiag : (fun i : Fin N => D i.val) = pivotDiagonal S := by
    funext i
    exact (pivotDiagonal_jacobiPivot D i).symm
  rw [curvatureDirichlet_eq]
  simp only [add_sub_cancel]
  change (dirichletMatrix (fun i : Fin N => D i.val)).PosDef
  rw [hdiag]
  exact dirichlet_pivots_posDef S hp

end

end PositiveEinsteinFour.Jacobi

end OAI
