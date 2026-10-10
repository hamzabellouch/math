import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FiniteDifferenceError
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.MoserChargeBounds

namespace OAI

/-! First and second coordinate differences approximate the actual
gradient and Laplacian of the manufactured C6 field. -/

noncomputable section
namespace ContinuumCoulomb.MoserCoordinateDifferences
open NeutralAtom (dirPartial axis)

private theorem partial_C5 (V : Position → ℝ) (hV : ContDiff ℝ 6 V) (a : Fin 3) :
    ContDiff ℝ 5 (dirPartial V (axis a)) :=
  (hV.fderiv_right (by norm_num)).clm_apply contDiff_const

private theorem second_C4 (V : Position → ℝ) (hV : ContDiff ℝ 6 V) (a : Fin 3) :
    ContDiff ℝ 4 (dirPartial (dirPartial V (axis a)) (axis a)) :=
  ((partial_C5 V hV a).fderiv_right (by norm_num)).clm_apply contDiff_const

private theorem partial_fderiv_bound (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    {B : ℝ} (hb : ∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k V x‖ ≤ B) (a : Fin 3) (x : Position) :
    ‖fderiv ℝ (dirPartial V (axis a)) x‖ ≤ B := by
  have h := dirPartial_iterated_norm_bound V hV (axis a) (k := 1) (by norm_num) x
  rw [show ‖axis a‖ = 1 by simp [axis],one_mul,norm_iteratedFDeriv_one] at h
  exact h.trans (hb 2 (by norm_num) x)

private theorem second_fderiv_bound (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    {B : ℝ} (hb : ∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k V x‖ ≤ B) (a : Fin 3) (x : Position) :
    ‖fderiv ℝ (dirPartial (dirPartial V (axis a)) (axis a)) x‖ ≤ B := by
  have hp := (partial_C5 V hV a).fderiv_right (by norm_num : (4:WithTop ℕ∞)+1 ≤ 5)
  have h := norm_iteratedFDeriv_clm_apply_const (x := x) (c := axis a) hp.contDiffAt
    (by norm_num : (1:WithTop ℕ∞) ≤ 4)
  rw [norm_iteratedFDeriv_fderiv] at h
  have h' := dirPartial_iterated_norm_bound V hV (axis a) (k := 2) (by norm_num) x
  rw [show ‖axis a‖ = 1 by simp [axis],one_mul] at h h'
  rw [norm_iteratedFDeriv_one] at h
  exact h.trans (h'.trans (hb 3 (by norm_num) x))

theorem along_axis_hasDerivAt (V : Position → ℝ) (hV : Differentiable ℝ V)
    (x : Position) (a : Fin 3) (t : ℝ) :
    HasDerivAt (fun s : ℝ => V (x+s • axis a)) (dirPartial V (axis a) (x+t • axis a)) t := by
  have hline : HasDerivAt (fun s : ℝ => x+s • axis a) (axis a) t := by
    simpa only [id_eq,one_smul] using ((hasDerivAt_id t).smul_const (axis a)).const_add x
  exact (hV _).hasFDerivAt.comp_hasDerivAt t hline

private theorem partial_axis_lipschitz (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    {B : ℝ} (hb : ∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k V x‖ ≤ B)
    (x : Position) (a : Fin 3) (t : ℝ) :
    |dirPartial V (axis a) (x+t • axis a)-dirPartial V (axis a) x| ≤ B*|t| := by
  have h := (convex_univ : Convex ℝ (Set.univ : Set Position)).norm_image_sub_le_of_norm_fderiv_le
    (fun y _ => (partial_C5 V hV a).differentiable (by norm_num) y)
    (fun y _ => partial_fderiv_bound V hV hb a y) (Set.mem_univ x) (Set.mem_univ (x+t • axis a))
  simpa only [Real.norm_eq_abs,add_sub_cancel_left,norm_smul,show ‖axis a‖ = 1 by simp [axis],mul_one] using h

private theorem second_axis_lipschitz (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    {B : ℝ} (hb : ∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k V x‖ ≤ B)
    (x : Position) (a : Fin 3) (t : ℝ) :
    |dirPartial (dirPartial V (axis a)) (axis a) (x+t • axis a)-
      dirPartial (dirPartial V (axis a)) (axis a) x| ≤ B*|t| := by
  have h := (convex_univ : Convex ℝ (Set.univ : Set Position)).norm_image_sub_le_of_norm_fderiv_le
    (fun y _ => (second_C4 V hV a).differentiable (by norm_num) y)
    (fun y _ => second_fderiv_bound V hV hb a y) (Set.mem_univ x) (Set.mem_univ (x+t • axis a))
  simpa only [Real.norm_eq_abs,add_sub_cancel_left,norm_smul,show ‖axis a‖ = 1 by simp [axis],mul_one] using h

theorem first_error (V evaluate : Position → ℝ) (hV : ContDiff ℝ 6 V)
    {B ε h : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε) (hh : 0 < h)
    (hb : ∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k V x‖ ≤ B)
    (he : ∀ y, |evaluate y-V y| ≤ ε) (x : Position) (a : Fin 3) :
    |(evaluate (x+h • axis a)-evaluate x)/h-dirPartial V (axis a) x| ≤ B*h+2*ε/h := by
  have ht := FiniteDifferenceError.forward_difference
    (fun s => V (x+s • axis a)) (fun s => dirPartial V (axis a) (x+s • axis a))
    (fun s => evaluate (x+s • axis a)) hh hB hε
    (fun s _ => along_axis_hasDerivAt V (hV.differentiable (by norm_num)) x a s)
    (x := 0) (fun s _ => by simpa using partial_axis_lipschitz V hV hb x a s)
    (he _) (he _)
  simpa only [zero_add,zero_smul,add_zero] using ht

theorem second_error (V evaluate : Position → ℝ) (hV : ContDiff ℝ 6 V)
    {B ε h : ℝ} (hB : 0 ≤ B) (hh : 0 < h)
    (hb : ∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k V x‖ ≤ B)
    (he : ∀ y, |evaluate y-V y| ≤ ε) (x : Position) (a : Fin 3) :
    |(evaluate (x+h • axis a)+evaluate (x-h • axis a)-2*evaluate x)/h^2-
      dirPartial (dirPartial V (axis a)) (axis a) x| ≤ B*h+4*ε/h^2 := by
  have ht := FiniteDifferenceError.centered_difference
    (fun s => V (x+s • axis a)) (fun s => dirPartial V (axis a) (x+s • axis a))
    (fun s => dirPartial (dirPartial V (axis a)) (axis a) (x+s • axis a))
    (fun s => evaluate (x+s • axis a)) hh hB
    (fun s => along_axis_hasDerivAt V (hV.differentiable (by norm_num)) x a s)
    (fun s => along_axis_hasDerivAt _ ((partial_C5 V hV a).differentiable (by norm_num)) x a s)
    (x := 0) (fun s _ => by simpa using second_axis_lipschitz V hV hb x a s)
    (he _) (he _) (he _)
  simpa only [zero_add,zero_sub,zero_smul,add_zero,neg_smul,← sub_eq_add_neg] using ht

end ContinuumCoulomb.MoserCoordinateDifferences

end

end OAI
