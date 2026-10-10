import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialRectangleIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.TangentCone.Prod

namespace OAI

/-! Finite-order smoothness of the regular origin integral, including its one-sided boundary. -/

open Set
namespace DefocusingNLS

theorem radial_rectangle_integral_contDiffOn (R : ℝ) (hR : 0 < R) (n : ℕ)
    (F : ℝ × ℝ → ℂ) (hF : ContDiffOn ℝ n F (Icc 0 R ×ˢ Icc 0 1)) :
    ContDiffOn ℝ n (fun x => ∫ t in Icc (0 : ℝ) 1, F (x,t)) (Icc 0 R) := by
  induction n generalizing F with
  | zero =>
    rw [Nat.cast_zero,contDiffOn_zero]
    exact radial_rectangle_integral_continuousOn R hR.le F hF.continuousOn
  | succ n ih =>
    rw [Nat.cast_succ] at hF ⊢
    let S : Set (ℝ × ℝ) := Icc 0 R ×ˢ Icc 0 1
    have hU : UniqueDiffOn ℝ (Icc 0 R) := uniqueDiffOn_Icc hR
    have hS : UniqueDiffOn ℝ S := hU.prod (uniqueDiffOn_Icc (by norm_num))
    let D : ℝ × ℝ → ℂ := fun p => fderivWithin ℝ F S p (1,0)
    have hDC : ContDiffOn ℝ n D S :=
      (hF.fderivWithin hS (by simp)).clm_apply contDiffOn_const
    have hDF : DifferentiableOn ℝ F S := hF.differentiableOn (by simp)
    have hd (x : ℝ) (hx : x ∈ Icc 0 R) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        HasDerivWithinAt (fun y => F (y,t)) (D (x,t)) (Icc 0 R) x := by
      have hp : HasDerivWithinAt (fun y : ℝ => (y,t)) (1,0) (Icc 0 R) x :=
        (hasDerivWithinAt_id x _).prodMk (hasDerivWithinAt_const x _ t)
      have hpt : (x,t) ∈ S := ⟨hx,ht⟩
      have hm : MapsTo (fun y : ℝ => (y,t)) (Icc 0 R) S := fun _ hy => ⟨hy,ht⟩
      exact (hDF (x,t) hpt).hasFDerivWithinAt.comp_hasDerivWithinAt x hp hm
    have hI := ih D hDC
    have hId (x : ℝ) (hx : x ∈ Icc 0 R) :=
      radial_rectangle_integral_hasDerivWithinAt R hR.le F D hF.continuousOn hDC.continuousOn hd x hx
    apply (contDiffOn_succ_iff_derivWithin hU).2
    refine ⟨fun x hx => (hId x hx).differentiableWithinAt,by simp,?_⟩
    apply hI.congr
    intro x hx
    exact (hId x hx).derivWithin (hU x hx)

end DefocusingNLS

end OAI
