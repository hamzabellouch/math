import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Data.List.FinRange
import OAI.Geometry.NodalSets.Elliptic.SmoothJet

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section

def directionalList (l : List Coord) (f : Coord → ℂ) : Coord → ℂ :=
  match l with
  | [] => f
  | v :: l => fun x ↦ fderiv ℝ (directionalList l f) x v

lemma directionalList_contDiff (l : List Coord) {f : Coord → ℂ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (directionalList l f) := by
  induction l with
  | nil => exact hf
  | cons v l ih => exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

lemma directionalList_perm {l r : List Coord} (h : l.Perm r) {f : Coord → ℂ}
    (hf : ContDiff ℝ ∞ f) : directionalList l f = directionalList r f := by
  induction h with
  | nil => rfl
  | cons v h ih => simp only [directionalList, ih]
  | swap v w l =>
    funext x
    have hs : IsSymmSndFDerivAt ℝ (directionalList l f) x :=
      (directionalList_contDiff l hf).contDiffAt.isSymmSndFDerivAt (by simp)
    dsimp [directionalList]
    rw [fderiv_clm_apply, fderiv_clm_apply]
    · simpa using hs w v
    all_goals first | exact differentiableAt_const _ | exact
      ((directionalList_contDiff l hf).fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  | trans h h' ih ih' => exact ih.trans ih'

theorem iteratedFDeriv_eq_directionalList {f : Coord → ℂ} (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (v : Fin n → Coord) (x : Coord) :
    iteratedFDeriv ℝ n f x v = directionalList (List.ofFn v) f x := by
  induction n generalizing x with
  | zero => simp [directionalList]
  | succ n ih =>
    rw [iteratedFDeriv_succ_apply_left]
    have he : (fun y ↦ iteratedFDeriv ℝ n f y (Fin.tail v)) =
        directionalList (List.ofFn (Fin.tail v)) f := funext (fun y ↦ ih _ y)
    rw [← fderiv_continuousMultilinear_apply_const_apply
      ((hf.differentiable_iteratedFDeriv (m := n) (by exact_mod_cast (show (n : ℕ∞) < ⊤ by simp))) x)]
    rw [he]
    simp only [List.ofFn_succ, directionalList]
    rfl

theorem smooth_iteratedFDeriv_perm {f : Coord → ℂ} (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (v : Fin n → Coord) (x : Coord) (σ : Equiv.Perm (Fin n)) :
    iteratedFDeriv ℝ n f x (v ∘ σ) = iteratedFDeriv ℝ n f x v := by
  rw [iteratedFDeriv_eq_directionalList hf, iteratedFDeriv_eq_directionalList hf,
    directionalList_perm (σ.ofFn_comp_perm v) hf]

end
end Yau.Jets

end OAI
