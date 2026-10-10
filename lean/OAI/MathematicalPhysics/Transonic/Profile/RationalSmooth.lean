import OAI.MathematicalPhysics.Transonic.Profile.FiniteExterior

namespace OAI

section
noncomputable section
namespace SepticProfile.PhysicalExterior
open Set
open scoped ContDiff

lemma source_solution_smooth {beta : ℝ} {s : Set ℝ} (hs : IsOpen s) {u : ℝ → ℝ}
    (hne : ∀ y∈s, profileDenom ell y (u y)≠0)
    (hd : ∀ y∈s, HasDerivAt u (field ell beta (y,u y)) y) :
    ContDiffOn ℝ ∞ u s := by
  rw [contDiffOn_infty]
  intro n
  induction n with
  | zero =>
    rw [Nat.cast_zero,contDiffOn_zero]
    exact fun y hy => (hd y hy).continuousAt.continuousWithinAt
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,contDiffOn_succ_iff_deriv_of_isOpen hs]
    refine ⟨fun y hy => (hd y hy).differentiableAt.differentiableWithinAt,by simp,?_⟩
    have hf : ContDiffOn ℝ n (fun y => field ell beta (y,u y)) s := by
      intro y hy
      have hu := ih y hy
      have hn := hne y hy
      unfold field profileNumer profileDenom at *
      fun_prop
    exact hf.congr (fun y hy => (hd y hy).deriv)

end SepticProfile.PhysicalExterior

end
end

end OAI
