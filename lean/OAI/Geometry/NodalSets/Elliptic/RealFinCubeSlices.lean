import Mathlib.Analysis.Calculus.Deriv.Pi
import OAI.Geometry.NodalSets.Elliptic.RealCoordinateEllipticLemmas

namespace OAI

namespace Yau.Geometry
open Function
open scoped ContDiff
noncomputable section

lemma real_finCons_smooth (n : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℝ) ↦ (Fin.cons p.1 p.2 : Fin (n+1) → ℝ)) := by
  apply contDiff_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa using (contDiff_fst : ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℝ) ↦ p.1))
  · simpa [Function.comp_def] using (contDiff_apply ℝ ℝ j).comp
      (contDiff_snd : ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℝ) ↦ p.2))

lemma real_finCube_slice_smooth (n : ℕ) (W : (Fin (n+1) → ℝ) → ℝ)
    (hW : ContDiff ℝ ∞ W) (t : ℝ) :
    ContDiff ℝ ∞ (fun z ↦ W (Fin.cons t z)) :=
  hW.comp ((real_finCons_smooth n).comp (contDiff_const.prodMk contDiff_id))

lemma real_finCube_line_smooth (n : ℕ) (W : (Fin (n+1) → ℝ) → ℝ)
    (hW : ContDiff ℝ ∞ W) (z : Fin n → ℝ) :
    ContDiff ℝ ∞ (fun t ↦ W (Fin.cons t z)) :=
  hW.comp ((real_finCons_smooth n).comp (contDiff_id.prodMk contDiff_const))

lemma real_coordPartial_eq_deriv_update (n : ℕ) (W : (Fin n → ℝ) → ℝ)
    (hW : ContDiff ℝ ∞ W) (z : Fin n → ℝ) (i : Fin n) :
    Yau.coordPartial W z i = deriv (fun t ↦ W (update z i t)) (z i) := by
  have hd := (hW.differentiable (by simp) (update z i (z i))).hasFDerivAt.comp_hasDerivAt
    (z i) (hasDerivAt_update z i (z i))
  simpa [Yau.coordPartial,Function.comp_def] using hd.deriv.symm

lemma real_finCube_slice_partial (n : ℕ) (W : (Fin (n+1) → ℝ) → ℝ)
    (hW : ContDiff ℝ ∞ W) (t : ℝ) (z : Fin n → ℝ) (i : Fin n) :
    Yau.coordPartial (fun y ↦ W (Fin.cons t y)) z i =
      Yau.coordPartial W (Fin.cons t z) i.succ := by
  rw [real_coordPartial_eq_deriv_update n _ (real_finCube_slice_smooth n W hW t),
    real_coordPartial_eq_deriv_update (n+1) W hW]
  have he (s : ℝ) : (Fin.cons t (update z i s) : Fin (n+1) → ℝ) =
      update (Fin.cons t z : Fin (n+1) → ℝ) i.succ s := by
    ext j
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · simp [Ne.symm (Fin.succ_ne_zero i)]
    · by_cases h : k=i
      · subst k; simp
      · simp [h]
  simp only [he,Fin.cons_succ]

lemma real_finCube_line_deriv (n : ℕ) (W : (Fin (n+1) → ℝ) → ℝ)
    (hW : ContDiff ℝ ∞ W) (t : ℝ) (z : Fin n → ℝ) :
    deriv (fun s ↦ W (Fin.cons s z)) t = Yau.coordPartial W (Fin.cons t z) 0 := by
  rw [real_coordPartial_eq_deriv_update (n+1) W hW]
  have he (s : ℝ) : update (Fin.cons t z : Fin (n+1) → ℝ) 0 s = Fin.cons s z := by
    ext j
    refine Fin.cases ?_ (fun k ↦ ?_) j <;> simp
  simp only [he,Fin.cons_zero]

end
end Yau.Geometry

end OAI
