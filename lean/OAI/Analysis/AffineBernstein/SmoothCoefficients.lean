import Mathlib
import OAI.Analysis.AffineBernstein.HessianDivergence

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/-- The frozen coordinate Hessian has smooth entries at every interior smooth point. -/
theorem contDiffAt_hessian_entry {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (i j : Fin n) :
    ContDiffAt ℝ ∞ (fun y => hessian u y i j) x := by
  exact (((hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).fderiv_right
    (m := ∞) (by simp)).clm_apply contDiffAt_const

/-- Determinants of the actual Hessian are smooth, by row multilinearity. -/
theorem contDiffAt_det_hessian {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) : ContDiffAt ℝ ∞ (fun y => (hessian u y).det) x := by
  have hH : ContDiffAt ℝ ∞ (fun y i j => hessian u y i j) x :=
    contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j => contDiffAt_hessian_entry hu i j
  exact continuousDetRows.contDiff.contDiffAt.comp x hH

/-- Polynomial cofactor entries are smooth even before invertibility is used. -/
theorem contDiffAt_adjugate_hessian_entry {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (i j : Fin n) :
    ContDiffAt ℝ ∞ (fun y => (hessian u y).adjugate i j) x := by
  have hM : ContDiffAt ℝ ∞
      (fun (y : Space n) (l m : Fin n) => if l = j then (Pi.single i (1 : ℝ) : Fin n → ℝ) m else hessian u y l m) x := by
    apply contDiffAt_pi.mpr
    intro l
    apply contDiffAt_pi.mpr
    intro m
    by_cases hlj : l = j
    · simp only [ite_eq_left hlj]
      exact contDiffAt_const
    · simp only [ite_eq_right hlj]
      exact contDiffAt_hessian_entry hu l m
  have hc := continuousDetRows.contDiff.contDiffAt.comp x hM
  convert hc using 1
  funext y
  rw [Matrix.adjugate_apply]
  change ((hessian u y).updateRow j (Pi.single i 1)).det =
    (Matrix.of fun l m => if l = j then Pi.single i 1 m else hessian u y l m).det
  congr 1
  ext l m
  exact Matrix.updateRow_apply

/-- Smoothness of U on its actual open domain, with no extension hypothesis. -/
theorem contDiffAt_cofactorHessian_entry {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hpos : ∀ y ∈ Ω, (hessian u y).PosDef) {x : Space n} (hx : x ∈ Ω) (i j : Fin n) :
    ContDiffAt ℝ ∞ (fun y => cofactorHessian u y i j) x := by
  apply (contDiffAt_adjugate_hessian_entry (hu.contDiffAt (hΩ.mem_nhds hx)) i j).congr_of_eventuallyEq
  filter_upwards [hΩ.mem_nhds hx] with y hy
  rw [cofactorHessian_eq_adjugate u y (ne_of_gt (hpos y hy).det_pos)]

/-- The real determinant weight has its original exponent throughout the proof. -/
theorem contDiffAt_affineWeight {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hpos : (hessian u x).PosDef) :
    ContDiffAt ℝ ∞ (affineWeight u) x :=
  (contDiffAt_det_hessian hu).rpow_const_of_ne (ne_of_gt hpos.det_pos)

end AffineBernstein
end

end OAI
